import DecoderTransformer.ModernIncremental
import DecoderTransformer.Autoregressive
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# End-to-end modern autoregressive generation

This module is the Lean counterpart of `Modern_Generation.thy`.  A generation
state stores the complete token history and a cache for all but its final
token.  The final token is evaluated on demand; the cache theorem therefore
connects the incremental evaluator with the last row of the full model.
-/

def modernGenerationCacheMatches (embedding : Nat → Vector ℝ)
    (layers : List ModernDecoderLayerParameters) (start : Nat)
    (tokens : List Nat) (caches : ModernTransformerCache) : Prop :=
  tokens ≠ [] ∧
    validModernStack layers ∧
    modernTransformerCacheMatches layers start
      (tokens.dropLast.map embedding) caches

abbrev ModernGenerationState := List Nat × ModernTransformerCache

def cachedModernGenerationEvaluate
    (layers : List ModernDecoderLayerParameters) (embedding : Nat → Vector ℝ)
    (start vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (tokens : List Nat) (caches : ModernTransformerCache) :
    Vector ℝ × ModernTransformerCache :=
  if tokens = [] then ([], caches)
  else
    let pref := tokens.dropLast.map embedding
    let step := cachedModernDecoderStackStep layers
      (start + pref.length) (embedding (lastNat tokens)) caches
    (nextTokenDistribution vocabularySize vocabularyWeights step.1, step.2)

theorem cachedModernGenerationEvaluate_correct
    {embedding : Nat → Vector ℝ}
    {layers : List ModernDecoderLayerParameters} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {tokens : List Nat}
    {caches : ModernTransformerCache}
    (hmatch : modernGenerationCacheMatches embedding layers start tokens caches) :
    (cachedModernGenerationEvaluate layers embedding start vocabularySize
      vocabularyWeights tokens caches).1 =
        nextTokenDistribution vocabularySize vocabularyWeights
          ((fullModernDecoderStack layers start
            (tokens.map embedding)).getLast?.getD ([] : Vector ℝ)) ∧
      modernTransformerCacheMatches layers start (tokens.map embedding)
        (cachedModernGenerationEvaluate layers embedding start vocabularySize
          vocabularyWeights tokens caches).2 := by
  have hne : tokens ≠ [] := hmatch.1
  have hvalid : validModernStack layers := hmatch.2.1
  have hcache : modernTransformerCacheMatches layers start
      (tokens.dropLast.map embedding) caches := hmatch.2.2
  have hlast : lastNat tokens = tokens.getLast hne := by
    simp [lastNat, List.getLast?_eq_getLast_of_ne_nil hne]
  have hsplit : tokens = tokens.dropLast ++ [lastNat tokens] := by
    rw [hlast]
    exact (List.dropLast_append_getLast hne).symm
  have hemb : tokens.map embedding =
      tokens.dropLast.map embedding ++ [embedding (lastNat tokens)] := by
    calc
      tokens.map embedding =
          (tokens.dropLast ++ [lastNat tokens]).map embedding :=
        congrArg (List.map embedding) hsplit
      _ = tokens.dropLast.map embedding ++ [embedding (lastNat tokens)] := by
        simp
  have hstep := cachedModernDecoderStackStep_correct
    (layers := layers) (start := start)
    (pref := tokens.dropLast.map embedding) (caches := caches)
    (x := embedding (lastNat tokens)) hvalid hcache
  have hout :
      (cachedModernDecoderStackStep layers
        (start + (tokens.dropLast.map embedding).length)
        (embedding (lastNat tokens)) caches).1 =
        (fullModernDecoderStack layers start
          (tokens.map embedding)).getLast?.getD ([] : Vector ℝ) := by
    have hlastout := congrArg
      (fun z : Matrix ℝ => z.getLast?.getD ([] : Vector ℝ)) hstep.1
    rw [hemb]
    simpa using hlastout.symm
  have hcache' : modernTransformerCacheMatches layers start
      (tokens.map embedding)
      (cachedModernDecoderStackStep layers
        (start + (tokens.dropLast.map embedding).length)
        (embedding (lastNat tokens)) caches).2 := by
    rw [hemb]
    exact hstep.2
  constructor
  · simpa [cachedModernGenerationEvaluate, hne] using
      congrArg (nextTokenDistribution vocabularySize vocabularyWeights) hout
  · simpa [cachedModernGenerationEvaluate, hne] using hcache'

theorem cachedModernNextTokenDistributionCorrect
    {embedding : Nat → Vector ℝ}
    {layers : List ModernDecoderLayerParameters} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {tokens : List Nat}
    {caches : ModernTransformerCache}
    (hmatch : modernGenerationCacheMatches embedding layers start tokens caches) :
    (cachedModernGenerationEvaluate layers embedding start vocabularySize
      vocabularyWeights tokens caches).1 =
        nextTokenDistribution vocabularySize vocabularyWeights
          ((fullModernDecoderStack layers start
            (tokens.map embedding)).getLast?.getD ([] : Vector ℝ)) :=
  (cachedModernGenerationEvaluate_correct hmatch).1

def initializeModernGenerationState (layers : List ModernDecoderLayerParameters)
    (embedding : Nat → Vector ℝ) (start : Nat) (tokens : List Nat) :
    ModernGenerationState :=
  (tokens,
    (cachedModernDecoderStackRun layers start
      (emptyModernTransformerCache layers)
      (tokens.dropLast.map embedding)).2)

theorem initializeModernGenerationState_correct
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start : Nat} {tokens : List Nat}
    (hvalid : validModernStack layers) (hne : tokens ≠ []) :
    modernGenerationCacheMatches embedding layers start
      (initializeModernGenerationState layers embedding start tokens).1
      (initializeModernGenerationState layers embedding start tokens).2 := by
  refine ⟨by simpa [initializeModernGenerationState], hvalid, ?_⟩
  simpa [initializeModernGenerationState] using
    (initializedModernCachedRun_cacheInvariant (layers := layers) hvalid start
      (tokens.dropLast.map embedding))

def modernGenerationTransition (select : Vector ℝ → Nat)
    (layers : List ModernDecoderLayerParameters) (embedding : Nat → Vector ℝ)
    (start vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (state : ModernGenerationState) : ModernGenerationState :=
  let tokens := state.1
  let evaluation := cachedModernGenerationEvaluate layers embedding start
    vocabularySize vocabularyWeights tokens state.2
  let next := deterministicNextToken select evaluation.1
  (tokens ++ [next], evaluation.2)

theorem modernGenerationTransitionCacheInvariant
    {select : Vector ℝ → Nat}
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    modernGenerationCacheMatches embedding layers start
      (modernGenerationTransition select layers embedding start vocabularySize
        vocabularyWeights state).1
      (modernGenerationTransition select layers embedding start vocabularySize
        vocabularyWeights state).2 := by
  have heval := cachedModernGenerationEvaluate_correct
    (vocabularySize := vocabularySize) (vocabularyWeights := vocabularyWeights)
    hmatch
  have hcache := heval.2
  have hvalid : validModernStack layers := hmatch.2.1
  refine ⟨?_, hvalid, ?_⟩
  · simp [modernGenerationTransition, hmatch.1]
  · simpa [modernGenerationTransition, deterministicNextToken] using hcache

def modernGenerateSteps : Nat → (Vector ℝ → Nat) →
    List ModernDecoderLayerParameters → (Nat → Vector ℝ) → Nat → Nat →
    Matrix ℝ → ModernGenerationState → ModernGenerationState
  | 0, _, _, _, _, _, _, state => state
  | n + 1, select, layers, embedding, start, vocabularySize,
      vocabularyWeights, state =>
      modernGenerateSteps n select layers embedding start vocabularySize
        vocabularyWeights
        (modernGenerationTransition select layers embedding start vocabularySize
          vocabularyWeights state)

theorem modernGenerateStepsCacheInvariant {n : Nat}
    {select : Vector ℝ → Nat}
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    modernGenerationCacheMatches embedding layers start
      (modernGenerateSteps n select layers embedding start vocabularySize
        vocabularyWeights state).1
      (modernGenerateSteps n select layers embedding start vocabularySize
        vocabularyWeights state).2 := by
  induction n generalizing state with
  | zero => exact hmatch
  | succ n ih =>
      apply ih
      exact modernGenerationTransitionCacheInvariant hmatch

def modernFullNextToken (layers : List ModernDecoderLayerParameters)
    (embedding : Nat → Vector ℝ) (start vocabularySize : Nat)
    (vocabularyWeights : Matrix ℝ) (tokens : List Nat) : Nat :=
  firstArgmax (nextTokenDistribution vocabularySize vocabularyWeights
    ((fullModernDecoderStack layers start
      (tokens.map embedding)).getLast?.getD ([] : Vector ℝ)))

def modernFullGenerateSteps : Nat → List ModernDecoderLayerParameters →
    (Nat → Vector ℝ) → Nat → Nat → Matrix ℝ → List Nat → List Nat
  | 0, _, _, _, _, _, tokens => tokens
  | n + 1, layers, embedding, start, vocabularySize, vocabularyWeights, tokens =>
      modernFullGenerateSteps n layers embedding start vocabularySize
        vocabularyWeights
        (tokens ++ [modernFullNextToken layers embedding start vocabularySize
          vocabularyWeights tokens])

theorem modernGenerationTransitionFull
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    (modernGenerationTransition firstArgmax layers embedding start
      vocabularySize vocabularyWeights state).1 =
      state.1 ++ [modernFullNextToken layers embedding start vocabularySize
        vocabularyWeights state.1] := by
  have heval := cachedModernNextTokenDistributionCorrect
    (vocabularySize := vocabularySize) (vocabularyWeights := vocabularyWeights)
    hmatch
  simp [modernGenerationTransition, deterministicNextToken,
    modernFullNextToken, heval]

theorem modernGreedyGenerateStepsEqFull {n : Nat}
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    (modernGenerateSteps n firstArgmax layers embedding start vocabularySize
      vocabularyWeights state).1 =
      modernFullGenerateSteps n layers embedding start vocabularySize
        vocabularyWeights state.1 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      have hnext := modernGenerationTransitionCacheInvariant
        (select := firstArgmax) (vocabularySize := vocabularySize)
        (vocabularyWeights := vocabularyWeights) hmatch
      have hrec := ih hnext
      have hfull := modernGenerationTransitionFull
        (vocabularySize := vocabularySize)
        (vocabularyWeights := vocabularyWeights) hmatch
      simp only [modernGenerateSteps]
      simpa [modernFullGenerateSteps, hfull] using hrec

theorem initializedModernGreedyGenerateStepsEqFull {n : Nat}
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {tokens : List Nat}
    (hvalid : validModernStack layers) (hne : tokens ≠ []) :
    (modernGenerateSteps n firstArgmax layers embedding start vocabularySize
      vocabularyWeights
      (initializeModernGenerationState layers embedding start tokens)).1 =
      modernFullGenerateSteps n layers embedding start vocabularySize
        vocabularyWeights tokens := by
  have hmatch := initializeModernGenerationState_correct
    (layers := layers) (embedding := embedding) (start := start)
    (tokens := tokens) hvalid hne
  have h := modernGreedyGenerateStepsEqFull (n := n)
    (vocabularySize := vocabularySize) (vocabularyWeights := vocabularyWeights)
    hmatch
  simpa [initializeModernGenerationState] using h

theorem modernGenerateStepsPreservesVocabulary {n : Nat}
    {select : Vector ℝ → Nat} {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hselector : validTokenSelector vocabularySize select)
    (htokens : tokensInVocabulary vocabularySize state.1)
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    tokensInVocabulary vocabularySize
      (modernGenerateSteps n select layers embedding start vocabularySize
        vocabularyWeights state).1 := by
  induction n generalizing state with
  | zero => exact htokens
  | succ n ih =>
      have hne : state.1 ≠ [] := hmatch.1
      have hlength :
          (cachedModernGenerationEvaluate layers embedding start vocabularySize
            vocabularyWeights state.1 state.2).1.length = vocabularySize := by
        simp [cachedModernGenerationEvaluate, hne]
      have hselected := hselector
        (cachedModernGenerationEvaluate layers embedding start vocabularySize
          vocabularyWeights state.1 state.2).1 hlength
      let next := modernGenerationTransition select layers embedding start
        vocabularySize vocabularyWeights state
      have hnext : tokensInVocabulary vocabularySize next.1 := by
        intro token htoken
        simp only [next, modernGenerationTransition, List.mem_append,
          List.mem_singleton] at htoken ⊢
        rcases htoken with htoken | rfl
        · exact htokens token htoken
        · simpa [deterministicNextToken] using hselected
      have hnextMatch : modernGenerationCacheMatches embedding layers start
          next.1 next.2 := by
        exact modernGenerationTransitionCacheInvariant hmatch
      exact ih hnext hnextMatch

theorem greedyModernGenerationIsSafe {n : Nat}
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hvocab : 0 < vocabularySize)
    (htokens : tokensInVocabulary vocabularySize state.1)
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    tokensInVocabulary vocabularySize
      (modernGenerateSteps n firstArgmax layers embedding start vocabularySize
        vocabularyWeights state).1 := by
  exact modernGenerateStepsPreservesVocabulary
    (firstArgmax_is_valid_selector hvocab) htokens hmatch

end
end DecoderTransformer
