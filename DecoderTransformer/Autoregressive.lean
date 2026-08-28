import DecoderTransformer.Incremental
import Mathlib.Data.List.GetD

namespace DecoderTransformer

noncomputable section

/-!
# Autoregressive generation
-/

def nextTokenLogits (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (hidden : Vector ℝ) : Vector ℝ :=
  linearProject vocabularySize vocabularyWeights hidden

def nextTokenDistribution (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (hidden : Vector ℝ) : Vector ℝ :=
  listSoftmax (nextTokenLogits vocabularySize vocabularyWeights hidden)

@[simp] theorem length_nextTokenLogits (vocabularySize : Nat)
    (vocabularyWeights : Matrix ℝ) (hidden : Vector ℝ) :
    (nextTokenLogits vocabularySize vocabularyWeights hidden).length = vocabularySize := by
  simp [nextTokenLogits, linearProject, matrixColumns]

@[simp] theorem nextTokenLogits_zero_vocabulary
    (vocabularyWeights : Matrix ℝ) (hidden : Vector ℝ) :
    nextTokenLogits 0 vocabularyWeights hidden = [] := by
  simp [nextTokenLogits, linearProject, matrixColumns]

@[simp] theorem length_nextTokenDistribution (vocabularySize : Nat)
    (vocabularyWeights : Matrix ℝ) (hidden : Vector ℝ) :
    (nextTokenDistribution vocabularySize vocabularyWeights hidden).length = vocabularySize := by
  simp [nextTokenDistribution]

@[simp] theorem nextTokenDistribution_zero_vocabulary
    (vocabularyWeights : Matrix ℝ) (hidden : Vector ℝ) :
    nextTokenDistribution 0 vocabularyWeights hidden = [] := by
  simp [nextTokenDistribution]

theorem nextTokenLogits_nonempty {vocabularySize : Nat}
    (hvocab : 0 < vocabularySize) (vocabularyWeights : Matrix ℝ)
    (hidden : Vector ℝ) :
    nextTokenLogits vocabularySize vocabularyWeights hidden ≠ [] := by
  intro h
  have hlen := length_nextTokenLogits vocabularySize vocabularyWeights hidden
  rw [h] at hlen
  have hvzero : vocabularySize = 0 := by
    simpa using hlen.symm
  exact (Nat.ne_of_gt hvocab) hvzero

theorem nextTokenDistribution_normalized {vocabularySize : Nat}
    (hvocab : 0 < vocabularySize) (vocabularyWeights : Matrix ℝ)
    (hidden : Vector ℝ) :
    (nextTokenDistribution vocabularySize vocabularyWeights hidden).sum = 1 := by
  apply listSoftmax_normalized
  exact nextTokenLogits_nonempty hvocab _ _

def sampleSupported (distribution : Vector ℝ) (token : Nat) : Prop :=
  token < distribution.length ∧ 0 < distribution.getD token 0

theorem sampleSupported_bound {distribution : Vector ℝ} {token : Nat}
    (h : sampleSupported distribution token) : token < distribution.length := h.1

theorem nextTokenDistribution_support {vocabularySize token : Nat}
    (hvocab : 0 < vocabularySize) (htoken : token < vocabularySize)
    (vocabularyWeights : Matrix ℝ) (hidden : Vector ℝ) :
    sampleSupported (nextTokenDistribution vocabularySize vocabularyWeights hidden) token := by
  have hlen : token <
      (nextTokenDistribution vocabularySize vocabularyWeights hidden).length := by
    simpa using htoken
  have hlogits := nextTokenLogits_nonempty hvocab vocabularyWeights hidden
  have hpos : 0 <
      (nextTokenDistribution vocabularySize vocabularyWeights hidden)[token]'hlen := by
    apply listSoftmax_positive hlogits
    exact List.getElem_mem hlen
  refine ⟨hlen, ?_⟩
  rw [List.getD_eq_getElem _ _ hlen]
  exact hpos

def deterministicNextToken (select : Vector ℝ → Nat) (distribution : Vector ℝ) : Nat :=
  select distribution

def generationCacheMatches (embedding : Nat → Vector ℝ)
    (layers : List DecoderLayerParameters) (tokens : List Nat)
    (caches : TransformerKVCache) : Prop :=
  tokens ≠ [] ∧
    transformerCacheMatches layers (tokens.dropLast.map embedding) caches

def lastNat (tokens : List Nat) : Nat := tokens.getLast?.getD 0

def cachedGenerationEvaluate (layers : List DecoderLayerParameters)
    (embedding : Nat → Vector ℝ) (vocabularySize : Nat)
    (vocabularyWeights : Matrix ℝ) (tokens : List Nat)
    (caches : TransformerKVCache) : Vector ℝ × TransformerKVCache :=
  if tokens = [] then ([], caches) else
    let step := cachedDecoderStackStep layers (embedding (lastNat tokens)) caches
    (nextTokenDistribution vocabularySize vocabularyWeights step.1, step.2)

theorem cachedGenerationEvaluate_correct
    {layers : List DecoderLayerParameters} {embedding : Nat → Vector ℝ}
    {tokens : List Nat} {caches : TransformerKVCache}
    (hmatch : generationCacheMatches embedding layers tokens caches)
    (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ) :
    (cachedGenerationEvaluate layers embedding vocabularySize vocabularyWeights
      tokens caches).1 =
        nextTokenDistribution vocabularySize vocabularyWeights
          ((fullDecoderStack layers (tokens.map embedding)).getLast?.getD
            ([] : Vector ℝ)) ∧
    transformerCacheMatches layers (tokens.map embedding)
      (cachedGenerationEvaluate layers embedding vocabularySize vocabularyWeights
        tokens caches).2 := by
  have hne : tokens ≠ [] := hmatch.1
  have hsplit : tokens = tokens.dropLast ++ [lastNat tokens] := by
    have hlast : lastNat tokens = tokens.getLast hne := by
      simp [lastNat, List.getLast?_eq_getLast_of_ne_nil hne]
    rw [hlast]
    exact (List.dropLast_append_getLast hne).symm
  have hcache : transformerCacheMatches layers
      (tokens.dropLast.map embedding) caches := hmatch.2
  have hstep := cachedDecoderStackStep_correct (x := embedding (lastNat tokens)) hcache
  have hemb : tokens.map embedding = tokens.dropLast.map embedding ++
      [embedding (lastNat tokens)] := by
    calc
      tokens.map embedding =
          (tokens.dropLast ++ [lastNat tokens]).map embedding :=
        congrArg (List.map embedding) hsplit
      _ = tokens.dropLast.map embedding ++ [embedding (lastNat tokens)] := by
        simp
  have hout : (cachedDecoderStackStep layers (embedding (lastNat tokens)) caches).1 =
      ((fullDecoderStack layers (tokens.map embedding)).getLast?.getD
        ([] : Vector ℝ)) := by
    have happ := hstep.1
    rw [hemb]
    simpa using (congrArg (fun z => z.getLast?.getD ([] : Vector ℝ)) happ).symm
  have hcache' : transformerCacheMatches layers (tokens.map embedding)
      (cachedDecoderStackStep layers (embedding (lastNat tokens)) caches).2 := by
    rw [hemb]
    exact hstep.2
  constructor
  · simpa [cachedGenerationEvaluate, hne] using
      congrArg (nextTokenDistribution vocabularySize vocabularyWeights) hout
  · simp [cachedGenerationEvaluate, hne, hcache']

abbrev GenerationState := List Nat × TransformerKVCache

def generationTransition (select : Vector ℝ → Nat)
    (layers : List DecoderLayerParameters) (embedding : Nat → Vector ℝ)
    (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (state : GenerationState) : GenerationState :=
  let tokens := state.1
  let evaluation := cachedGenerationEvaluate layers embedding vocabularySize
    vocabularyWeights tokens state.2
  let next := deterministicNextToken select evaluation.1
  (tokens ++ [next], evaluation.2)

theorem generationTransition_cache_invariant
    {select : Vector ℝ → Nat} {layers : List DecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : GenerationState}
    (hmatch : generationCacheMatches embedding layers state.1 state.2) :
    generationCacheMatches embedding layers
      (generationTransition select layers embedding vocabularySize vocabularyWeights state).1
      (generationTransition select layers embedding vocabularySize vocabularyWeights state).2 := by
  have heval := cachedGenerationEvaluate_correct hmatch vocabularySize vocabularyWeights
  have hcache := heval.2
  refine ⟨by simp [generationTransition, hmatch.1], ?_⟩
  simpa [generationCacheMatches, generationTransition, deterministicNextToken] using hcache

def generateSteps : Nat → (Vector ℝ → Nat) → List DecoderLayerParameters →
    (Nat → Vector ℝ) → Nat → Matrix ℝ → GenerationState → GenerationState
  | 0, select, layers, embedding, vocabularySize, vocabularyWeights, state => state
  | n + 1, select, layers, embedding, vocabularySize, vocabularyWeights, state =>
      generateSteps n select layers embedding vocabularySize vocabularyWeights
        (generationTransition select layers embedding vocabularySize vocabularyWeights state)

theorem generateSteps_cache_invariant {n : Nat}
    {select : Vector ℝ → Nat} {layers : List DecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : GenerationState}
    (hmatch : generationCacheMatches embedding layers state.1 state.2) :
    generationCacheMatches embedding layers
      (generateSteps n select layers embedding vocabularySize vocabularyWeights state).1
      (generateSteps n select layers embedding vocabularySize vocabularyWeights state).2 := by
  induction n generalizing state with
  | zero => exact hmatch
  | succ n ih =>
      apply ih
      exact generationTransition_cache_invariant hmatch

end
end DecoderTransformer
