import DecoderTransformer.GPTNeoWindowedStack
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# GPT-Neo model-level semantics

This module lifts the exact GPT-Neo block and cache semantics to a language
model with learned token/position embeddings, final normalization, and a
vocabulary projection.  The bounded and unbounded prompt/evaluation paths are
kept side by side so their cache invariants remain explicit.
-/

structure GPTNeoModelParameters where
  layers : List GPTNeoLayerParameters
  hiddenSize : Nat
  vocabularySize : Nat
  maxPosition : Nat
  normEpsilon : ℝ
  tokenEmbeddings : Matrix ℝ
  positionEmbeddings : Matrix ℝ
  finalGain : Vector ℝ
  finalBias : Vector ℝ
  vocabularyWeights : Matrix ℝ

def validGPTNeoModel (m : GPTNeoModelParameters) : Prop :=
  m.layers ≠ [] ∧
  0 < m.hiddenSize ∧
  0 < m.vocabularySize ∧
  0 < m.maxPosition ∧
  0 < m.normEpsilon ∧
  matrixShape m.vocabularySize m.hiddenSize m.tokenEmbeddings ∧
  matrixShape m.maxPosition m.hiddenSize m.positionEmbeddings ∧
  vectorShape m.hiddenSize m.finalGain ∧
  vectorShape m.hiddenSize m.finalBias ∧
  matrixShape m.hiddenSize m.vocabularySize m.vocabularyWeights ∧
  gptNeoStackCompatible m.hiddenSize m.layers

theorem validGPTNeoModel_dimensions {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) :
    0 < m.hiddenSize ∧ 0 < m.vocabularySize ∧ 0 < m.maxPosition ∧
      0 < m.normEpsilon := by
  rcases h with ⟨_, hhidden, hvocab, hposition, hepsilon, _⟩
  exact ⟨hhidden, hvocab, hposition, hepsilon⟩

theorem validGPTNeoModel_layers_nonempty {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) : m.layers ≠ [] := h.1

theorem validGPTNeoModel_shapes {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) :
    matrixShape m.vocabularySize m.hiddenSize m.tokenEmbeddings ∧
    matrixShape m.maxPosition m.hiddenSize m.positionEmbeddings ∧
    vectorShape m.hiddenSize m.finalGain ∧
    vectorShape m.hiddenSize m.finalBias ∧
    matrixShape m.hiddenSize m.vocabularySize m.vocabularyWeights ∧
    gptNeoStackCompatible m.hiddenSize m.layers := by
  rcases h with ⟨_, _, _, _, _, htokens, hpositions, hgain, hbias,
    hvocab, hstack⟩
  exact ⟨htokens, hpositions, hgain, hbias, hvocab, hstack⟩

theorem validGPTNeoModel_tokenEmbeddingShape {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) :
    matrixShape m.vocabularySize m.hiddenSize m.tokenEmbeddings :=
  (validGPTNeoModel_shapes h).1

theorem validGPTNeoModel_positionEmbeddingShape {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) :
    matrixShape m.maxPosition m.hiddenSize m.positionEmbeddings :=
  (validGPTNeoModel_shapes h).2.1

theorem validGPTNeoModel_finalGainShape {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) : vectorShape m.hiddenSize m.finalGain :=
  (validGPTNeoModel_shapes h).2.2.1

theorem validGPTNeoModel_finalBiasShape {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) : vectorShape m.hiddenSize m.finalBias :=
  (validGPTNeoModel_shapes h).2.2.2.1

theorem validGPTNeoModel_vocabularyShape {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) :
    matrixShape m.hiddenSize m.vocabularySize m.vocabularyWeights :=
  (validGPTNeoModel_shapes h).2.2.2.2.1

theorem validGPTNeoModel_stackCompatible {m : GPTNeoModelParameters}
    (h : validGPTNeoModel m) :
    gptNeoStackCompatible m.hiddenSize m.layers :=
  (validGPTNeoModel_shapes h).2.2.2.2.2

def gptNeoModelInput (m : GPTNeoModelParameters)
    (position token : Nat) : Vector ℝ :=
  gptNeoInputEmbedding m.tokenEmbeddings m.positionEmbeddings token position

def gptNeoModelInputSequence (m : GPTNeoModelParameters) (position : Nat) :
    List Nat → Matrix ℝ
  | [] => []
  | token :: tokens =>
      gptNeoModelInput m position token ::
        gptNeoModelInputSequence m (position + 1) tokens

@[simp] theorem length_gptNeoModelInputSequence
    (m : GPTNeoModelParameters) (position : Nat) (tokens : List Nat) :
    (gptNeoModelInputSequence m position tokens).length = tokens.length := by
  induction tokens generalizing position with
  | nil => rfl
  | cons token tokens ih => simp [gptNeoModelInputSequence, ih]

theorem gptNeoModelInputSequence_append_singleton
    (m : GPTNeoModelParameters) (position : Nat) (tokens : List Nat)
    (token : Nat) :
    gptNeoModelInputSequence m position (tokens ++ [token]) =
      gptNeoModelInputSequence m position tokens ++
        [gptNeoModelInput m (position + tokens.length) token] := by
  induction tokens generalizing position with
  | nil => simp [gptNeoModelInputSequence]
  | cons head tokens ih =>
      simp only [gptNeoModelInputSequence, List.cons_append,
        List.length_cons]
      rw [ih (position := position + 1)]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem gptNeoModelInput_shape {m : GPTNeoModelParameters}
    {position token : Nat} (htoken : token < m.vocabularySize)
    (hposition : position < m.maxPosition) (hvalid : validGPTNeoModel m) :
    vectorShape m.hiddenSize (gptNeoModelInput m position token) := by
  exact gptNeoInputEmbedding_shape htoken hposition
    (validGPTNeoModel_tokenEmbeddingShape hvalid)
    (validGPTNeoModel_positionEmbeddingShape hvalid)

theorem gptNeoModelInputSequence_shape {m : GPTNeoModelParameters}
    {position : Nat} {tokens : List Nat} (hvalid : validGPTNeoModel m)
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition) :
    matrixShape tokens.length m.hiddenSize
      (gptNeoModelInputSequence m position tokens) := by
  induction tokens generalizing position with
  | nil =>
      change ([] : Matrix ℝ).length = 0 ∧
        ∀ row : Vector ℝ, row ∈ ([] : Matrix ℝ) → row.length = m.hiddenSize
      exact ⟨rfl, by intro row hrow; cases hrow⟩
  | cons token tokens ih =>
      have htoken : token < m.vocabularySize := htokens token (by simp)
      have hposition' : position < m.maxPosition := by
        simp only [List.length_cons] at hposition
        omega
      have hhead : vectorShape m.hiddenSize
          (gptNeoModelInput m position token) :=
        gptNeoModelInput_shape htoken hposition' hvalid
      have htailTokens : ∀ t ∈ tokens, t < m.vocabularySize := by
        intro t ht
        exact htokens t (by simp [ht])
      have htailPosition : (position + 1) + tokens.length ≤ m.maxPosition := by
        simp only [List.length_cons] at hposition
        omega
      have htail := ih (position := position + 1) htailTokens htailPosition
      refine ⟨?_, ?_⟩
      · simp [htail.1]
      · intro row hrow
        simp only [gptNeoModelInputSequence, List.mem_cons] at hrow
        rcases hrow with rfl | hrow
        · exact vectorShape_length hhead
        · exact htail.2 row hrow

def gptNeoFullHidden (m : GPTNeoModelParameters) (position : Nat)
    (tokens : List Nat) : Matrix ℝ :=
  gptNeoFullStack m.layers (gptNeoModelInputSequence m position tokens)

theorem validGPTNeoFullHiddenShape {m : GPTNeoModelParameters}
    {position : Nat} {tokens : List Nat} (hvalid : validGPTNeoModel m)
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition) :
    matrixShape tokens.length m.hiddenSize
      (gptNeoFullHidden m position tokens) := by
  apply compatibleGPTNeoFullStackShape
    (validGPTNeoModel_stackCompatible hvalid)
  exact gptNeoModelInputSequence_shape hvalid htokens hposition

def gptNeoFinalNormalize (m : GPTNeoModelParameters) (x : Vector ℝ) :
    Vector ℝ :=
  gptNeoLayerNorm m.normEpsilon m.finalGain m.finalBias x

def gptNeoModelLogits (m : GPTNeoModelParameters) (x : Vector ℝ) :
    Vector ℝ :=
  gptNeoLogits m.vocabularySize m.vocabularyWeights
    (gptNeoFinalNormalize m x)

def gptNeoFullModelLogits (m : GPTNeoModelParameters) (position : Nat)
    (tokens : List Nat) : Matrix ℝ :=
  (gptNeoFullHidden m position tokens).map (gptNeoModelLogits m)

theorem gptNeoFinalNormalize_shape {m : GPTNeoModelParameters}
    (hvalid : validGPTNeoModel m) {x : Vector ℝ}
    (hx : vectorShape m.hiddenSize x) :
    vectorShape m.hiddenSize (gptNeoFinalNormalize m x) := by
  exact gptNeoLayerNorm_shape (validGPTNeoModel_finalGainShape hvalid)
    (validGPTNeoModel_finalBiasShape hvalid) hx

theorem gptNeoModelLogits_shape {m : GPTNeoModelParameters}
    (hvalid : validGPTNeoModel m) {x : Vector ℝ}
    (hx : vectorShape m.hiddenSize x) :
    vectorShape m.vocabularySize (gptNeoModelLogits m x) := by
  exact gptNeoLogits_shape (validGPTNeoModel_vocabularyShape hvalid)
    (gptNeoFinalNormalize_shape hvalid hx)

theorem validGPTNeoFullModelLogitsShape {m : GPTNeoModelParameters}
    {position : Nat} {tokens : List Nat} (hvalid : validGPTNeoModel m)
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition) :
    matrixShape tokens.length m.vocabularySize
      (gptNeoFullModelLogits m position tokens) := by
  have hhidden := validGPTNeoFullHiddenShape hvalid htokens hposition
  refine ⟨by simp [gptNeoFullModelLogits, hhidden.1], ?_⟩
  intro row hrow
  rcases List.mem_map.1 hrow with ⟨source, hsource, rfl⟩
  exact gptNeoModelLogits_shape hvalid (hhidden.2 source hsource)

def gptNeoModelCacheMatches (m : GPTNeoModelParameters) (position : Nat)
    (tokens : List Nat) (caches : GPTNeoTransformerCache) : Prop :=
  gptNeoTransformerCacheMatches m.layers
    (gptNeoModelInputSequence m position tokens) caches

def gptNeoCachedPrompt (m : GPTNeoModelParameters) (position : Nat)
    (tokens : List Nat) : Matrix ℝ × GPTNeoTransformerCache :=
  gptNeoCachedStackRun m.layers
    (emptyGPTNeoTransformerCache m.layers)
    (gptNeoModelInputSequence m position tokens)

theorem gptNeoCachedPrompt_correct {m : GPTNeoModelParameters}
    {position : Nat} {tokens : List Nat} (hvalid : validGPTNeoModel m)
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition) :
    (gptNeoCachedPrompt m position tokens).1 =
        gptNeoFullHidden m position tokens ∧
      gptNeoModelCacheMatches m position tokens
        (gptNeoCachedPrompt m position tokens).2 := by
  have hstack : validGPTNeoStack m.layers := by
    intro p hp
    exact (validGPTNeoModel_stackCompatible hvalid p hp).1
  have hrun := gptNeoCachedStackRun_correct (layers := m.layers)
    (pref := []) (caches := emptyGPTNeoTransformerCache m.layers)
    (xs := gptNeoModelInputSequence m position tokens) hstack
    (emptyGPTNeoTransformerCache_matches m.layers)
  constructor
  · simpa [gptNeoCachedPrompt, gptNeoFullHidden, gptNeoFullStack_empty]
      using hrun.1.symm
  · simpa [gptNeoCachedPrompt, gptNeoModelCacheMatches] using hrun.2

def gptNeoGenerationCacheMatches (m : GPTNeoModelParameters)
    (position : Nat) (tokens : List Nat)
    (caches : GPTNeoTransformerCache) : Prop :=
  tokens ≠ [] ∧
    gptNeoModelCacheMatches m position tokens.dropLast caches

def gptNeoLastNat (tokens : List Nat) : Nat :=
  tokens.getLast?.getD 0

def gptNeoCachedModelEvaluate (m : GPTNeoModelParameters) (position : Nat)
    (tokens : List Nat) (caches : GPTNeoTransformerCache) :
    Vector ℝ × GPTNeoTransformerCache :=
  if tokens = [] then ([], caches) else
    let pref := tokens.dropLast
    let token := gptNeoLastNat tokens
    let x := gptNeoModelInput m (position + pref.length) token
    let step := gptNeoCachedStackStep m.layers x caches
    (gptNeoModelLogits m step.1, step.2)

theorem gptNeoInputSequence_token_split {m : GPTNeoModelParameters}
    {position : Nat} {tokens : List Nat} (htokens : tokens ≠ []) :
    gptNeoModelInputSequence m position tokens =
      gptNeoModelInputSequence m position tokens.dropLast ++
        [gptNeoModelInput m (position + tokens.dropLast.length)
          (gptNeoLastNat tokens)] := by
  have hlast : gptNeoLastNat tokens = tokens.getLast htokens := by
    simp [gptNeoLastNat, List.getLast?_eq_getLast_of_ne_nil htokens]
  have hsplit : tokens = tokens.dropLast ++ [gptNeoLastNat tokens] := by
    rw [hlast]
    exact (List.dropLast_append_getLast htokens).symm
  calc
    gptNeoModelInputSequence m position tokens =
        gptNeoModelInputSequence m position
          (tokens.dropLast ++ [gptNeoLastNat tokens]) :=
      congrArg (gptNeoModelInputSequence m position) hsplit
    _ = gptNeoModelInputSequence m position tokens.dropLast ++
        [gptNeoModelInput m (position + tokens.dropLast.length)
          (gptNeoLastNat tokens)] :=
      gptNeoModelInputSequence_append_singleton m position tokens.dropLast
        (gptNeoLastNat tokens)

theorem gptNeoCachedModelEvaluate_correct
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoGenerationCacheMatches m position tokens caches) :
    (gptNeoCachedModelEvaluate m position tokens caches).1 =
        (gptNeoFullModelLogits m position tokens).getLast?.getD [] ∧
      gptNeoModelCacheMatches m position tokens
        (gptNeoCachedModelEvaluate m position tokens caches).2 := by
  have hcache : gptNeoModelCacheMatches m position tokens.dropLast caches :=
    hmatch.2
  let x := gptNeoModelInput m (position + tokens.dropLast.length)
    (gptNeoLastNat tokens)
  have hsplit := gptNeoInputSequence_token_split
    (m := m) (position := position) htokens
  have hstack : validGPTNeoStack m.layers := by
    intro p hp
    exact (validGPTNeoModel_stackCompatible hvalid p hp).1
  have hstackMatch : gptNeoTransformerCacheMatches m.layers
      (gptNeoModelInputSequence m position tokens.dropLast) caches := hcache
  have hone := gptNeoCachedStackStep_correct (layers := m.layers)
    (pref := gptNeoModelInputSequence m position tokens.dropLast)
    (caches := caches) (x := x) hstack hstackMatch
  have hcache' : gptNeoTransformerCacheMatches m.layers
      (gptNeoModelInputSequence m position tokens)
      (gptNeoCachedStackStep m.layers x caches).2 := by
    rw [hsplit]
    exact hone.2
  have hhiddenLast :
      (gptNeoFullHidden m position tokens).getLast?.getD [] =
        (gptNeoCachedStackStep m.layers x caches).1 := by
    have hlast := congrArg
      (fun z : Matrix ℝ => z.getLast?.getD ([] : Vector ℝ)) hone.1
    simpa [gptNeoFullHidden, hsplit, x] using hlast
  have hhiddenNonempty : gptNeoFullHidden m position tokens ≠ [] := by
    intro hnil
    have hlength :
        (gptNeoFullHidden m position tokens).length = tokens.length := by
      simp [gptNeoFullHidden, length_gptNeoFullStack]
    have hzero : tokens.length = 0 := by
      rw [← hlength, hnil]
      rfl
    exact htokens (List.eq_nil_of_length_eq_zero hzero)
  have hhiddenLast' :
      (gptNeoFullHidden m position tokens).getLast hhiddenNonempty =
        (gptNeoCachedStackStep m.layers x caches).1 := by
    simpa [List.getLast?_eq_getLast_of_ne_nil hhiddenNonempty] using
      hhiddenLast
  have hlogitsLast :
      (gptNeoFullModelLogits m position tokens).getLast?.getD [] =
        gptNeoModelLogits m (gptNeoCachedStackStep m.layers x caches).1 := by
    rw [gptNeoFullModelLogits, List.getLast?_map,
      List.getLast?_eq_getLast_of_ne_nil hhiddenNonempty]
    simp [hhiddenLast']
  have heval :
      (gptNeoCachedModelEvaluate m position tokens caches).1 =
        gptNeoModelLogits m (gptNeoCachedStackStep m.layers x caches).1 := by
    simp [gptNeoCachedModelEvaluate, htokens, x]
  have hcacheEval :
      (gptNeoCachedModelEvaluate m position tokens caches).2 =
        (gptNeoCachedStackStep m.layers x caches).2 := by
    simp [gptNeoCachedModelEvaluate, htokens, x]
  constructor
  · rw [heval, ← hlogitsLast]
  · rw [hcacheEval]
    exact hcache'

theorem gptNeoCachedModelEvaluate_logits_correct
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoGenerationCacheMatches m position tokens caches) :
    (gptNeoCachedModelEvaluate m position tokens caches).1 =
      (gptNeoFullModelLogits m position tokens).getLast?.getD [] :=
  (gptNeoCachedModelEvaluate_correct hvalid htokens htokenBounds
    hposition hmatch).1

theorem gptNeoCachedModelEvaluate_cache_correct
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoGenerationCacheMatches m position tokens caches) :
    gptNeoModelCacheMatches m position tokens
      (gptNeoCachedModelEvaluate m position tokens caches).2 :=
  (gptNeoCachedModelEvaluate_correct hvalid htokens htokenBounds
    hposition hmatch).2

def gptNeoBoundedModelCacheMatches (m : GPTNeoModelParameters)
    (position : Nat) (tokens : List Nat)
    (caches : GPTNeoTransformerCache) : Prop :=
  gptNeoBoundedTransformerCacheMatches m.layers
    (gptNeoModelInputSequence m position tokens) caches

def gptNeoBoundedCachedPrompt (m : GPTNeoModelParameters) (position : Nat)
    (tokens : List Nat) : Matrix ℝ × GPTNeoTransformerCache :=
  gptNeoBoundedCachedStackRun m.layers
    (emptyGPTNeoBoundedTransformerCache m.layers)
    (gptNeoModelInputSequence m position tokens)

theorem gptNeoBoundedCachedPrompt_correct {m : GPTNeoModelParameters}
    {position : Nat} {tokens : List Nat} (hvalid : validGPTNeoModel m)
    (htokens : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition) :
    (gptNeoBoundedCachedPrompt m position tokens).1 =
        gptNeoFullHidden m position tokens ∧
      gptNeoBoundedModelCacheMatches m position tokens
        (gptNeoBoundedCachedPrompt m position tokens).2 := by
  have hstack : validGPTNeoStack m.layers := by
    intro p hp
    exact (validGPTNeoModel_stackCompatible hvalid p hp).1
  have hrun := gptNeoBoundedCachedStackRun_correct (layers := m.layers)
    (pref := []) (caches := emptyGPTNeoBoundedTransformerCache m.layers)
    (xs := gptNeoModelInputSequence m position tokens) hstack
    (emptyGPTNeoBoundedTransformerCache_matches m.layers)
  constructor
  · simpa [gptNeoBoundedCachedPrompt, gptNeoFullHidden,
      gptNeoFullStack_empty] using hrun.1.symm
  · simpa [gptNeoBoundedCachedPrompt, gptNeoBoundedModelCacheMatches]
      using hrun.2

def gptNeoBoundedGenerationCacheMatches (m : GPTNeoModelParameters)
    (position : Nat) (tokens : List Nat)
    (caches : GPTNeoTransformerCache) : Prop :=
  tokens ≠ [] ∧
    gptNeoBoundedModelCacheMatches m position tokens.dropLast caches

def gptNeoBoundedCachedModelEvaluate (m : GPTNeoModelParameters)
    (position : Nat) (tokens : List Nat)
    (caches : GPTNeoTransformerCache) :
    Vector ℝ × GPTNeoTransformerCache :=
  if tokens = [] then ([], caches) else
    let pref := tokens.dropLast
    let token := gptNeoLastNat tokens
    let x := gptNeoModelInput m (position + pref.length) token
    let step := gptNeoBoundedCachedStackStep m.layers x caches
    (gptNeoModelLogits m step.1, step.2)

theorem gptNeoBoundedCachedModelEvaluate_correct
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoBoundedGenerationCacheMatches m position tokens caches) :
    (gptNeoBoundedCachedModelEvaluate m position tokens caches).1 =
        (gptNeoFullModelLogits m position tokens).getLast?.getD [] ∧
      gptNeoBoundedModelCacheMatches m position tokens
        (gptNeoBoundedCachedModelEvaluate m position tokens caches).2 := by
  have hcache : gptNeoBoundedModelCacheMatches m position
      tokens.dropLast caches := hmatch.2
  let x := gptNeoModelInput m (position + tokens.dropLast.length)
    (gptNeoLastNat tokens)
  have hsplit := gptNeoInputSequence_token_split
    (m := m) (position := position) htokens
  have hstack : validGPTNeoStack m.layers := by
    intro p hp
    exact (validGPTNeoModel_stackCompatible hvalid p hp).1
  have hone := gptNeoBoundedCachedStackStep_correct (layers := m.layers)
    (pref := gptNeoModelInputSequence m position tokens.dropLast)
    (caches := caches) (x := x) hstack hcache
  have hcache' : gptNeoBoundedTransformerCacheMatches m.layers
      (gptNeoModelInputSequence m position tokens)
      (gptNeoBoundedCachedStackStep m.layers x caches).2 := by
    rw [hsplit]
    exact hone.2
  have hhiddenLast :
      (gptNeoFullHidden m position tokens).getLast?.getD [] =
        (gptNeoBoundedCachedStackStep m.layers x caches).1 := by
    have hlast := congrArg
      (fun z : Matrix ℝ => z.getLast?.getD ([] : Vector ℝ)) hone.1
    simpa [gptNeoFullHidden, hsplit, x] using hlast
  have hhiddenNonempty : gptNeoFullHidden m position tokens ≠ [] := by
    intro hnil
    have hlength :
        (gptNeoFullHidden m position tokens).length = tokens.length := by
      simp [gptNeoFullHidden, length_gptNeoFullStack]
    have hzero : tokens.length = 0 := by
      rw [← hlength, hnil]
      rfl
    exact htokens (List.eq_nil_of_length_eq_zero hzero)
  have hhiddenLast' :
      (gptNeoFullHidden m position tokens).getLast hhiddenNonempty =
        (gptNeoBoundedCachedStackStep m.layers x caches).1 := by
    simpa [List.getLast?_eq_getLast_of_ne_nil hhiddenNonempty] using
      hhiddenLast
  have hlogitsLast :
      (gptNeoFullModelLogits m position tokens).getLast?.getD [] =
        gptNeoModelLogits m (gptNeoBoundedCachedStackStep m.layers x caches).1 := by
    rw [gptNeoFullModelLogits, List.getLast?_map,
      List.getLast?_eq_getLast_of_ne_nil hhiddenNonempty]
    simp [hhiddenLast']
  have heval :
      (gptNeoBoundedCachedModelEvaluate m position tokens caches).1 =
        gptNeoModelLogits m
          (gptNeoBoundedCachedStackStep m.layers x caches).1 := by
    simp [gptNeoBoundedCachedModelEvaluate, htokens, x]
  have hcacheEval :
      (gptNeoBoundedCachedModelEvaluate m position tokens caches).2 =
        (gptNeoBoundedCachedStackStep m.layers x caches).2 := by
    simp [gptNeoBoundedCachedModelEvaluate, htokens, x]
  constructor
  · rw [heval, ← hlogitsLast]
  · rw [hcacheEval]
    exact hcache'

theorem gptNeoBoundedCachedModelEvaluate_logits_correct
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoBoundedGenerationCacheMatches m position tokens caches) :
    (gptNeoBoundedCachedModelEvaluate m position tokens caches).1 =
      (gptNeoFullModelLogits m position tokens).getLast?.getD [] :=
  (gptNeoBoundedCachedModelEvaluate_correct hvalid htokens htokenBounds
    hposition hmatch).1

theorem gptNeoBoundedCachedModelEvaluate_cache_correct
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoBoundedGenerationCacheMatches m position tokens caches) :
    gptNeoBoundedModelCacheMatches m position tokens
      (gptNeoBoundedCachedModelEvaluate m position tokens caches).2 :=
  (gptNeoBoundedCachedModelEvaluate_correct hvalid htokens htokenBounds
    hposition hmatch).2

theorem gptNeoBoundedCachedModelEvaluate_logits_length
    {m : GPTNeoModelParameters} {position : Nat} {tokens : List Nat}
    {caches : GPTNeoTransformerCache} (hvalid : validGPTNeoModel m)
    (htokens : tokens ≠ [])
    (htokenBounds : ∀ token ∈ tokens, token < m.vocabularySize)
    (hposition : position + tokens.length ≤ m.maxPosition)
    (hmatch : gptNeoBoundedGenerationCacheMatches m position tokens caches) :
    ((gptNeoBoundedCachedModelEvaluate m position tokens caches).1).length =
      m.vocabularySize := by
  have hshape := validGPTNeoFullModelLogitsShape hvalid htokenBounds hposition
  have hnonempty : gptNeoFullModelLogits m position tokens ≠ [] := by
    intro h
    have hlength : (gptNeoFullModelLogits m position tokens).length =
        tokens.length := by
      simp [gptNeoFullModelLogits, gptNeoFullHidden,
        length_gptNeoFullStack]
    have hzero : tokens.length = 0 := by
      rw [← hlength, h]
      rfl
    exact htokens (List.eq_nil_of_length_eq_zero hzero)
  have hlast : vectorShape m.vocabularySize
      ((gptNeoFullModelLogits m position tokens).getLast?.getD
        ([] : Vector ℝ)) := by
    have hmem : (gptNeoFullModelLogits m position tokens).getLast
        hnonempty ∈ gptNeoFullModelLogits m position tokens :=
      List.getLast_mem hnonempty
    have hrow := hshape.2 _ hmem
    simpa [List.getLast?_eq_getLast_of_ne_nil hnonempty,
      vectorShape] using hrow
  have heq := gptNeoBoundedCachedModelEvaluate_logits_correct
    hvalid htokens htokenBounds hposition hmatch
  have hlength := congrArg List.length heq
  rw [hlast] at hlength
  exact hlength

end
end DecoderTransformer
