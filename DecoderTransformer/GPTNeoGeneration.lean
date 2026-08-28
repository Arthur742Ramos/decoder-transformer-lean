import DecoderTransformer.GPTNeoModel
import DecoderTransformer.Decoding
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# GPT-Neo autoregressive generation

This is the Lean counterpart of `GPT_Neo_Generation.thy`.  It keeps the
unbounded and sliding-window evaluators separate, including their state
validity, room bounds, greedy/full refinement, and initialized-state results.
-/

abbrev GPTNeoGenerationState := List Nat × GPTNeoTransformerCache

def gptNeoGenerationStateValid (m : GPTNeoModelParameters) (position : Nat)
    (state : GPTNeoGenerationState) : Prop :=
  validGPTNeoModel m ∧
  state.1 ≠ [] ∧
  tokensInVocabulary m.vocabularySize state.1 ∧
  position + state.1.length ≤ m.maxPosition ∧
  gptNeoGenerationCacheMatches m position state.1 state.2

def gptNeoGenerationTransition (select : Vector ℝ → Nat)
    (m : GPTNeoModelParameters) (position : Nat)
    (state : GPTNeoGenerationState) : GPTNeoGenerationState :=
  let tokens := state.1
  let evaluation := gptNeoCachedModelEvaluate m position tokens state.2
  let next := select evaluation.1
  (tokens ++ [next], evaluation.2)

theorem gptNeoGenerationTransitionTokens
    (select : Vector ℝ → Nat) (m : GPTNeoModelParameters) (position : Nat)
    (state : GPTNeoGenerationState) :
    (gptNeoGenerationTransition select m position state).1 =
      state.1 ++ [select (gptNeoCachedModelEvaluate m position
        state.1 state.2).1] := by
  simp [gptNeoGenerationTransition]

theorem gptNeoGenerationTransitionCache
    (select : Vector ℝ → Nat) (m : GPTNeoModelParameters) (position : Nat)
    (state : GPTNeoGenerationState) :
    (gptNeoGenerationTransition select m position state).2 =
      (gptNeoCachedModelEvaluate m position state.1 state.2).2 := by
  simp [gptNeoGenerationTransition]

def gptNeoFullNextToken (m : GPTNeoModelParameters) (position : Nat)
    (tokens : List Nat) : Nat :=
  firstArgmax ((gptNeoFullModelLogits m position tokens).getLast?.getD
    ([] : Vector ℝ))

def gptNeoFullGenerateSteps : Nat → GPTNeoModelParameters → Nat →
    List Nat → List Nat
  | 0, _, _, tokens => tokens
  | n + 1, m, position, tokens =>
      gptNeoFullGenerateSteps n m position
        (tokens ++ [gptNeoFullNextToken m position tokens])

theorem gptNeoCachedModelEvaluateLogitsLength
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoGenerationCacheMatches m position tokens caches) :
    (gptNeoCachedModelEvaluate m position tokens caches).1.length =
      m.vocabularySize := by
  have hshape := validGPTNeoFullModelLogitsShape hvalid htokenBounds hposition
  have hnonempty : gptNeoFullModelLogits m position tokens ≠ [] := by
    intro hnil
    have hlength :
        (gptNeoFullModelLogits m position tokens).length = tokens.length := by
      simp [gptNeoFullModelLogits, gptNeoFullHidden, length_gptNeoFullStack]
    have hzero : tokens.length = 0 := by
      rw [← hlength, hnil]
      rfl
    exact htokens (List.eq_nil_of_length_eq_zero hzero)
  have hlast : vectorShape m.vocabularySize
      ((gptNeoFullModelLogits m position tokens).getLast?.getD
        ([] : Vector ℝ)) := by
    have hmem := List.getLast_mem hnonempty
    have hrow := hshape.2 _ hmem
    simpa [List.getLast?_eq_getLast_of_ne_nil hnonempty, vectorShape] using hrow
  have heq := gptNeoCachedModelEvaluate_logits_correct
    hvalid htokens htokenBounds hposition hmatch
  rw [heq]
  exact hlast

theorem gptNeoGenerationTransitionValid
    {select : Vector ℝ → Nat} {m : GPTNeoModelParameters}
    {position : Nat} {state : GPTNeoGenerationState}
    (hstate : gptNeoGenerationStateValid m position state)
    (hselector : validTokenSelector m.vocabularySize select)
    (hroom : position + (state.1.length + 1) ≤ m.maxPosition) :
    gptNeoGenerationStateValid m position
      (gptNeoGenerationTransition select m position state) := by
  rcases hstate with ⟨hvalid, hne, htokens, hposition, hcache⟩
  have htokenBounds : ∀ token ∈ state.1, token < m.vocabularySize := htokens
  have hlength :
      (gptNeoCachedModelEvaluate m position state.1 state.2).1.length =
        m.vocabularySize :=
    gptNeoCachedModelEvaluateLogitsLength hvalid hne htokenBounds hposition
      hcache
  have hselected := hselector
    (gptNeoCachedModelEvaluate m position state.1 state.2).1 hlength
  have hevalCache := gptNeoCachedModelEvaluate_cache_correct
    hvalid hne htokenBounds hposition hcache
  have hnewTokens : tokensInVocabulary m.vocabularySize
      (gptNeoGenerationTransition select m position state).1 := by
    intro token htoken
    rw [gptNeoGenerationTransitionTokens] at htoken
    simp only [List.mem_append, List.mem_singleton] at htoken
    rcases htoken with htoken | rfl
    · exact htokens token htoken
    · exact hselected
  have hnewNonempty :
      (gptNeoGenerationTransition select m position state).1 ≠ [] := by
    rw [gptNeoGenerationTransitionTokens]
    simp [hne]
  have hnewPosition : position +
      (gptNeoGenerationTransition select m position state).1.length ≤
        m.maxPosition := by
    rw [gptNeoGenerationTransitionTokens]
    simpa [List.length_append] using hroom
  have hnewCache : gptNeoGenerationCacheMatches m position
      (gptNeoGenerationTransition select m position state).1
      (gptNeoGenerationTransition select m position state).2 := by
    rw [gptNeoGenerationTransitionTokens, gptNeoGenerationTransitionCache]
    simpa [gptNeoGenerationCacheMatches, hne] using hevalCache
  exact ⟨hvalid, hnewNonempty, hnewTokens, hnewPosition, hnewCache⟩

def gptNeoGenerateSteps : Nat → (Vector ℝ → Nat) → GPTNeoModelParameters →
    Nat → GPTNeoGenerationState → GPTNeoGenerationState
  | 0, _, _, _, state => state
  | n + 1, select, m, position, state =>
      gptNeoGenerateSteps n select m position
        (gptNeoGenerationTransition select m position state)

theorem gptNeoGenerateStepsValid {n : Nat}
    {select : Vector ℝ → Nat} {m : GPTNeoModelParameters}
    {position : Nat} {state : GPTNeoGenerationState}
    (hstate : gptNeoGenerationStateValid m position state)
    (hselector : validTokenSelector m.vocabularySize select)
    (hroom : position + state.1.length + n ≤ m.maxPosition) :
    gptNeoGenerationStateValid m position
      (gptNeoGenerateSteps n select m position state) := by
  induction n generalizing state with
  | zero => exact hstate
  | succ n ih =>
      have htransitionRoom : position + (state.1.length + 1) ≤ m.maxPosition := by
        omega
      have hnext := gptNeoGenerationTransitionValid hstate hselector
        htransitionRoom
      have hnextRoom : position +
          (gptNeoGenerationTransition select m position state).1.length + n ≤
            m.maxPosition := by
        rw [gptNeoGenerationTransitionTokens]
        simp only [List.length_append, List.length_singleton]
        omega
      exact ih hnext hnextRoom

theorem gptNeoGreedyGenerateStepsValid {n : Nat}
    {m : GPTNeoModelParameters} {position : Nat}
    {state : GPTNeoGenerationState}
    (hstate : gptNeoGenerationStateValid m position state)
    (hroom : position + state.1.length + n ≤ m.maxPosition) :
    gptNeoGenerationStateValid m position
      (gptNeoGenerateSteps n firstArgmax m position state) := by
  exact gptNeoGenerateStepsValid hstate
    (firstArgmax_is_valid_selector
      (validGPTNeoModel_dimensions hstate.1).2.1) hroom

theorem gptNeoGenerationTransitionFull
    {m : GPTNeoModelParameters} {position : Nat}
    {state : GPTNeoGenerationState}
    (hstate : gptNeoGenerationStateValid m position state) :
    (gptNeoGenerationTransition firstArgmax m position state).1 =
      state.1 ++ [gptNeoFullNextToken m position state.1] := by
  have heval := gptNeoCachedModelEvaluate_logits_correct
    hstate.1 hstate.2.1 hstate.2.2.1 hstate.2.2.2.1 hstate.2.2.2.2
  simp [gptNeoGenerationTransition, gptNeoFullNextToken, heval]

theorem gptNeoGreedyGenerateStepsEqFull {n : Nat}
    {m : GPTNeoModelParameters} {position : Nat}
    {state : GPTNeoGenerationState}
    (hstate : gptNeoGenerationStateValid m position state)
    (hroom : position + state.1.length + n ≤ m.maxPosition) :
    (gptNeoGenerateSteps n firstArgmax m position state).1 =
      gptNeoFullGenerateSteps n m position state.1 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      have htransitionRoom : position + (state.1.length + 1) ≤ m.maxPosition := by
        omega
      have hnext := gptNeoGenerationTransitionValid hstate
        (firstArgmax_is_valid_selector
          (validGPTNeoModel_dimensions hstate.1).2.1) htransitionRoom
      have hnextRoom : position +
          (gptNeoGenerationTransition firstArgmax m position state).1.length + n ≤
            m.maxPosition := by
        rw [gptNeoGenerationTransitionTokens]
        simp only [List.length_append, List.length_singleton]
        omega
      have hrec := ih hnext hnextRoom
      have hfull := gptNeoGenerationTransitionFull hstate
      simp only [gptNeoGenerateSteps]
      simpa [gptNeoFullGenerateSteps, hfull] using hrec

def gptNeoInitializedGenerationState (m : GPTNeoModelParameters)
    (position : Nat) (tokens : List Nat) : GPTNeoGenerationState :=
  (tokens,
    (gptNeoCachedPrompt m position tokens.dropLast).2)

theorem gptNeoInitializedGenerationStateValid
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    (hvalid : validGPTNeoModel m) (hne : tokens ≠ [])
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition) :
    gptNeoGenerationStateValid m position
      (gptNeoInitializedGenerationState m position tokens) := by
  have hprefTokens : ∀ token ∈ tokens.dropLast, token < m.vocabularySize := by
    intro token htoken
    exact htokens token (List.mem_of_mem_dropLast htoken)
  have hprefPosition : position + tokens.dropLast.length ≤ m.maxPosition := by
    simp only [List.length_dropLast]
    omega
  have hcache := gptNeoCachedPrompt_correct hvalid hprefTokens hprefPosition
  have hcacheMatch : gptNeoGenerationCacheMatches m position tokens
      (gptNeoInitializedGenerationState m position tokens).2 := by
    refine ⟨hne, ?_⟩
    simpa [gptNeoInitializedGenerationState] using hcache.2
  have hvocab : tokensInVocabulary m.vocabularySize tokens := htokens
  change validGPTNeoModel m ∧ tokens ≠ [] ∧
    tokensInVocabulary m.vocabularySize tokens ∧
    position + tokens.length ≤ m.maxPosition ∧
    gptNeoGenerationCacheMatches m position tokens
      (gptNeoInitializedGenerationState m position tokens).2
  exact ⟨hvalid, hne, hvocab, hposition, hcacheMatch⟩

def gptNeoBoundedGenerationStateValid (m : GPTNeoModelParameters)
    (position : Nat) (state : GPTNeoGenerationState) : Prop :=
  validGPTNeoModel m ∧
  state.1 ≠ [] ∧
  tokensInVocabulary m.vocabularySize state.1 ∧
  position + state.1.length ≤ m.maxPosition ∧
  gptNeoBoundedGenerationCacheMatches m position state.1 state.2

def gptNeoBoundedGenerationTransition (select : Vector ℝ → Nat)
    (m : GPTNeoModelParameters) (position : Nat)
    (state : GPTNeoGenerationState) : GPTNeoGenerationState :=
  let tokens := state.1
  let evaluation := gptNeoBoundedCachedModelEvaluate m position tokens state.2
  let next := select evaluation.1
  (tokens ++ [next], evaluation.2)

theorem gptNeoBoundedGenerationTransitionTokens
    (select : Vector ℝ → Nat) (m : GPTNeoModelParameters) (position : Nat)
    (state : GPTNeoGenerationState) :
    (gptNeoBoundedGenerationTransition select m position state).1 =
      state.1 ++ [select (gptNeoBoundedCachedModelEvaluate m position
        state.1 state.2).1] := by
  simp [gptNeoBoundedGenerationTransition]

theorem gptNeoBoundedGenerationTransitionCache
    (select : Vector ℝ → Nat) (m : GPTNeoModelParameters) (position : Nat)
    (state : GPTNeoGenerationState) :
    (gptNeoBoundedGenerationTransition select m position state).2 =
      (gptNeoBoundedCachedModelEvaluate m position state.1 state.2).2 := by
  simp [gptNeoBoundedGenerationTransition]

theorem gptNeoBoundedGenerationTransitionValid
    {select : Vector ℝ → Nat} {m : GPTNeoModelParameters}
    {position : Nat} {state : GPTNeoGenerationState}
    (hstate : gptNeoBoundedGenerationStateValid m position state)
    (hselector : validTokenSelector m.vocabularySize select)
    (hroom : position + (state.1.length + 1) ≤ m.maxPosition) :
    gptNeoBoundedGenerationStateValid m position
      (gptNeoBoundedGenerationTransition select m position state) := by
  rcases hstate with ⟨hvalid, hne, htokens, hposition, hcache⟩
  have hlength :
      (gptNeoBoundedCachedModelEvaluate m position state.1 state.2).1.length =
        m.vocabularySize :=
    gptNeoBoundedCachedModelEvaluate_logits_length hvalid hne htokens
      hposition hcache
  have hselected := hselector
    (gptNeoBoundedCachedModelEvaluate m position state.1 state.2).1 hlength
  have hevalCache := gptNeoBoundedCachedModelEvaluate_cache_correct
    hvalid hne htokens hposition hcache
  have hnewTokens : tokensInVocabulary m.vocabularySize
      (gptNeoBoundedGenerationTransition select m position state).1 := by
    intro token htoken
    rw [gptNeoBoundedGenerationTransitionTokens] at htoken
    simp only [List.mem_append, List.mem_singleton] at htoken
    rcases htoken with htoken | rfl
    · exact htokens token htoken
    · exact hselected
  have hnewNonempty :
      (gptNeoBoundedGenerationTransition select m position state).1 ≠ [] := by
    rw [gptNeoBoundedGenerationTransitionTokens]
    simp [hne]
  have hnewPosition : position +
      (gptNeoBoundedGenerationTransition select m position state).1.length ≤
        m.maxPosition := by
    rw [gptNeoBoundedGenerationTransitionTokens]
    simpa [List.length_append] using hroom
  have hnewCache : gptNeoBoundedGenerationCacheMatches m position
      (gptNeoBoundedGenerationTransition select m position state).1
      (gptNeoBoundedGenerationTransition select m position state).2 := by
    rw [gptNeoBoundedGenerationTransitionTokens,
      gptNeoBoundedGenerationTransitionCache]
    simpa [gptNeoBoundedGenerationCacheMatches, hne] using hevalCache
  exact ⟨hvalid, hnewNonempty, hnewTokens, hnewPosition, hnewCache⟩

def gptNeoBoundedGenerateSteps : Nat → (Vector ℝ → Nat) →
    GPTNeoModelParameters → Nat → GPTNeoGenerationState → GPTNeoGenerationState
  | 0, _, _, _, state => state
  | n + 1, select, m, position, state =>
      gptNeoBoundedGenerateSteps n select m position
        (gptNeoBoundedGenerationTransition select m position state)

theorem gptNeoBoundedGenerateStepsValid {n : Nat}
    {select : Vector ℝ → Nat} {m : GPTNeoModelParameters}
    {position : Nat} {state : GPTNeoGenerationState}
    (hstate : gptNeoBoundedGenerationStateValid m position state)
    (hselector : validTokenSelector m.vocabularySize select)
    (hroom : position + state.1.length + n ≤ m.maxPosition) :
    gptNeoBoundedGenerationStateValid m position
      (gptNeoBoundedGenerateSteps n select m position state) := by
  induction n generalizing state with
  | zero => exact hstate
  | succ n ih =>
      have htransitionRoom : position + (state.1.length + 1) ≤ m.maxPosition := by
        omega
      have hnext := gptNeoBoundedGenerationTransitionValid hstate hselector
        htransitionRoom
      have hnextRoom : position +
          (gptNeoBoundedGenerationTransition select m position state).1.length + n ≤
            m.maxPosition := by
        rw [gptNeoBoundedGenerationTransitionTokens]
        simp only [List.length_append, List.length_singleton]
        omega
      exact ih hnext hnextRoom

theorem gptNeoBoundedGreedyGenerateStepsValid {n : Nat}
    {m : GPTNeoModelParameters} {position : Nat}
    {state : GPTNeoGenerationState}
    (hstate : gptNeoBoundedGenerationStateValid m position state)
    (hroom : position + state.1.length + n ≤ m.maxPosition) :
    gptNeoBoundedGenerationStateValid m position
      (gptNeoBoundedGenerateSteps n firstArgmax m position state) := by
  exact gptNeoBoundedGenerateStepsValid hstate
    (firstArgmax_is_valid_selector
      (validGPTNeoModel_dimensions hstate.1).2.1) hroom

theorem gptNeoBoundedGenerationTransitionFull
    {m : GPTNeoModelParameters} {position : Nat}
    {state : GPTNeoGenerationState}
    (hstate : gptNeoBoundedGenerationStateValid m position state) :
    (gptNeoBoundedGenerationTransition firstArgmax m position state).1 =
      state.1 ++ [gptNeoFullNextToken m position state.1] := by
  have heval := gptNeoBoundedCachedModelEvaluate_logits_correct
    hstate.1 hstate.2.1 hstate.2.2.1 hstate.2.2.2.1 hstate.2.2.2.2
  simp [gptNeoBoundedGenerationTransition, gptNeoFullNextToken, heval]

theorem gptNeoBoundedGreedyGenerateStepsEqFull {n : Nat}
    {m : GPTNeoModelParameters} {position : Nat}
    {state : GPTNeoGenerationState}
    (hstate : gptNeoBoundedGenerationStateValid m position state)
    (hroom : position + state.1.length + n ≤ m.maxPosition) :
    (gptNeoBoundedGenerateSteps n firstArgmax m position state).1 =
      gptNeoFullGenerateSteps n m position state.1 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      have htransitionRoom : position + (state.1.length + 1) ≤ m.maxPosition := by
        omega
      have hnext := gptNeoBoundedGenerationTransitionValid hstate
        (firstArgmax_is_valid_selector
          (validGPTNeoModel_dimensions hstate.1).2.1) htransitionRoom
      have hnextRoom : position +
          (gptNeoBoundedGenerationTransition firstArgmax m position state).1.length + n ≤
            m.maxPosition := by
        rw [gptNeoBoundedGenerationTransitionTokens]
        simp only [List.length_append, List.length_singleton]
        omega
      have hrec := ih hnext hnextRoom
      have hfull := gptNeoBoundedGenerationTransitionFull hstate
      simp only [gptNeoBoundedGenerateSteps]
      simpa [gptNeoFullGenerateSteps, hfull] using hrec

def gptNeoBoundedInitializedGenerationState (m : GPTNeoModelParameters)
    (position : Nat) (tokens : List Nat) : GPTNeoGenerationState :=
  (tokens,
    (gptNeoBoundedCachedPrompt m position tokens.dropLast).2)

theorem gptNeoBoundedInitializedGenerationStateValid
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    (hvalid : validGPTNeoModel m) (hne : tokens ≠ [])
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition) :
    gptNeoBoundedGenerationStateValid m position
      (gptNeoBoundedInitializedGenerationState m position tokens) := by
  have hprefTokens : ∀ token ∈ tokens.dropLast, token < m.vocabularySize := by
    intro token htoken
    exact htokens token (List.mem_of_mem_dropLast htoken)
  have hprefPosition : position + tokens.dropLast.length ≤ m.maxPosition := by
    simp only [List.length_dropLast]
    omega
  have hcache := gptNeoBoundedCachedPrompt_correct hvalid hprefTokens
    hprefPosition
  have hcacheMatch : gptNeoBoundedGenerationCacheMatches m position tokens
      (gptNeoBoundedInitializedGenerationState m position tokens).2 := by
    refine ⟨hne, ?_⟩
    simpa [gptNeoBoundedInitializedGenerationState] using hcache.2
  change validGPTNeoModel m ∧ tokens ≠ [] ∧
    tokensInVocabulary m.vocabularySize tokens ∧
    position + tokens.length ≤ m.maxPosition ∧
    gptNeoBoundedGenerationCacheMatches m position tokens
      (gptNeoBoundedInitializedGenerationState m position tokens).2
  exact ⟨hvalid, hne, htokens, hposition, hcacheMatch⟩

theorem gptNeoInitializedGreedyGenerateStepsEqFull {n : Nat}
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    (hvalid : validGPTNeoModel m) (hne : tokens ≠ [])
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hroom : position + tokens.length + n ≤ m.maxPosition) :
    (gptNeoGenerateSteps n firstArgmax m position
      (gptNeoInitializedGenerationState m position tokens)).1 =
      gptNeoFullGenerateSteps n m position tokens := by
  have hstate := gptNeoInitializedGenerationStateValid hvalid hne htokens
    hposition
  have h := gptNeoGreedyGenerateStepsEqFull hstate
    (by simpa [gptNeoInitializedGenerationState] using hroom)
  simpa [gptNeoInitializedGenerationState] using h

theorem gptNeoBoundedInitializedGreedyGenerateStepsEqFull {n : Nat}
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    (hvalid : validGPTNeoModel m) (hne : tokens ≠ [])
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hroom : position + tokens.length + n ≤ m.maxPosition) :
    (gptNeoBoundedGenerateSteps n firstArgmax m position
      (gptNeoBoundedInitializedGenerationState m position tokens)).1 =
      gptNeoFullGenerateSteps n m position tokens := by
  have hstate := gptNeoBoundedInitializedGenerationStateValid hvalid hne
    htokens hposition
  have h := gptNeoBoundedGreedyGenerateStepsEqFull hstate
    (by simpa [gptNeoBoundedInitializedGenerationState] using hroom)
  simpa [gptNeoBoundedInitializedGenerationState] using h

end
end DecoderTransformer
