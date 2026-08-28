import DecoderTransformer.Numerical
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Globally well-formed decoder models

The semantic operators are total list functions.  These predicates make the
nondegeneracy and tensor-shape obligations of an actual decoder explicit.
-/

def validDecoderLayer (p : DecoderLayerParameters) : Prop :=
  0 < p.headCount ∧
  0 < p.modelDim ∧
  0 < p.headDim ∧
  0 < p.hiddenDim ∧
  p.modelDim = p.headCount * p.headDim ∧
  0 < p.normEpsilon ∧
  vectorShape p.modelDim p.attentionGain ∧
  vectorShape p.modelDim p.mlpGain ∧
  multiHeadParametersShape p.headCount p.modelDim p.headDim
    p.queryWeights p.keyWeights p.valueWeights p.outputWeights ∧
  matrixShape p.modelDim p.hiddenDim p.upWeights ∧
  matrixShape p.hiddenDim p.modelDim p.downWeights

def decoderLayersWellFormed (modelDim : Nat)
    (layers : List DecoderLayerParameters) : Prop :=
  ∀ p ∈ layers, validDecoderLayer p ∧ p.modelDim = modelDim

def validTransformer (modelDim : Nat)
    (layers : List DecoderLayerParameters) : Prop :=
  0 < modelDim ∧ layers ≠ [] ∧ decoderLayersWellFormed modelDim layers

def validVocabulary (modelDim vocabularySize : Nat)
    (embedding : Nat → Vector ℝ) (vocabularyWeights : Matrix ℝ) : Prop :=
  0 < vocabularySize ∧
  (∀ token, token < vocabularySize → vectorShape modelDim (embedding token)) ∧
  matrixShape modelDim vocabularySize vocabularyWeights

def validTokenSelector (vocabularySize : Nat)
    (select : Vector ℝ → Nat) : Prop :=
  ∀ distribution, distribution.length = vocabularySize →
    select distribution < vocabularySize

def tokensInVocabulary (vocabularySize : Nat) (tokens : List Nat) : Prop :=
  ∀ token ∈ tokens, token < vocabularySize

theorem validDecoderLayer_dimensions {p : DecoderLayerParameters}
    (h : validDecoderLayer p) :
    0 < p.headCount ∧ 0 < p.modelDim ∧ 0 < p.headDim ∧
      0 < p.hiddenDim ∧ p.modelDim = p.headCount * p.headDim ∧
      0 < p.normEpsilon := by
  rcases h with ⟨hhead, hmodel, hheadDim, hhidden, hdim, hepsilon,
    hattentionGain, hmlpGain, hparams, hup, hdown⟩
  exact ⟨hhead, hmodel, hheadDim, hhidden, hdim, hepsilon⟩

theorem validDecoderLayer_shapes {p : DecoderLayerParameters}
    (h : validDecoderLayer p) :
    vectorShape p.modelDim p.attentionGain ∧
    vectorShape p.modelDim p.mlpGain ∧
    multiHeadParametersShape p.headCount p.modelDim p.headDim
      p.queryWeights p.keyWeights p.valueWeights p.outputWeights ∧
      matrixShape p.modelDim p.hiddenDim p.upWeights ∧
    matrixShape p.hiddenDim p.modelDim p.downWeights := by
  rcases h with ⟨hhead, hmodel, hheadDim, hhidden, hdim, hepsilon,
    hattentionGain, hmlpGain, hparams, hup, hdown⟩
  exact ⟨hattentionGain, hmlpGain, hparams, hup, hdown⟩

theorem rmsDenominator_positive {epsilon : ℝ} {x : Vector ℝ}
    (hepsilon : 0 < epsilon) : 0 < rmsDenominator epsilon x := by
  have hsquares : 0 ≤ (x.map (fun v => v * v)).sum := by
    induction x with
    | nil => simp
    | cons a x ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_nonneg (mul_self_nonneg a) ih
  have hquotient : 0 ≤ (x.map (fun v => v * v)).sum / x.length := by
    exact div_nonneg hsquares (by positivity)
  unfold rmsDenominator
  apply Real.sqrt_pos.2
  exact add_pos_of_nonneg_of_pos hquotient hepsilon

theorem validLayer_rmsDenominator_ne_zero {p : DecoderLayerParameters}
    (hp : validDecoderLayer p) (x : Vector ℝ) :
    rmsDenominator p.normEpsilon x ≠ 0 := by
  exact ne_of_gt (rmsDenominator_positive
    (validDecoderLayer_dimensions hp).2.2.2.2.2)

theorem validLayer_attentionScale_positive {p : DecoderLayerParameters}
    (hp : validDecoderLayer p) : 0 < Real.sqrt p.headDim := by
  have hhead : 0 < p.headDim := (validDecoderLayer_dimensions hp).2.2.1
  exact Real.sqrt_pos.2 (by exact_mod_cast hhead)

theorem validDecoderLayer_preservesShape {p : DecoderLayerParameters}
    {seqLen : Nat} {X : Matrix ℝ}
    (hp : validDecoderLayer p) (hX : matrixShape seqLen p.modelDim X) :
    matrixShape seqLen p.modelDim (fullDecoderLayer p X) := by
  rcases validDecoderLayer_shapes hp with
    ⟨hattentionGain, hmlpGain, hparams, hup, hdown⟩
  exact decoderBlock_shape hparams hattentionGain hmlpGain hup hdown hX

theorem wellFormedDecoderStack_preservesShape {modelDim : Nat}
    {layers : List DecoderLayerParameters} {seqLen : Nat} {X : Matrix ℝ}
    (hvalid : decoderLayersWellFormed modelDim layers)
    (hX : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim (fullDecoderStack layers X) := by
  induction layers generalizing X with
  | nil => simpa [fullDecoderStack] using hX
  | cons p ps ih =>
      have hp := hvalid p (by simp)
      have htail : decoderLayersWellFormed modelDim ps := by
        intro q hq
        exact hvalid q (by simp [hq])
      have hX' : matrixShape seqLen p.modelDim X := by
        simpa [hp.2] using hX
      have hlayer := validDecoderLayer_preservesShape hp.1 hX'
      have hlayer' : matrixShape seqLen modelDim (fullDecoderLayer p X) := by
        simpa [hp.2] using hlayer
      exact ih htail hlayer'

theorem validTransformer_preservesShape {modelDim : Nat}
    {layers : List DecoderLayerParameters} {seqLen : Nat} {X : Matrix ℝ}
    (hvalid : validTransformer modelDim layers)
    (hX : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim (fullDecoderStack layers X) := by
  exact wellFormedDecoderStack_preservesShape hvalid.2.2 hX

theorem cachedGeneration_distribution_length
    {tokens : List Nat} (htokens : tokens ≠ [])
    (layers : List DecoderLayerParameters) (embedding : Nat → Vector ℝ)
    (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (caches : TransformerKVCache) :
    (cachedGenerationEvaluate layers embedding vocabularySize vocabularyWeights
      tokens caches).1.length = vocabularySize := by
  simp [cachedGenerationEvaluate, htokens]

theorem generationTransition_preservesVocabulary
    {vocabularySize : Nat} {select : Vector ℝ → Nat}
    {layers : List DecoderLayerParameters} {embedding : Nat → Vector ℝ}
    {vocabularyWeights : Matrix ℝ} {state : GenerationState}
    (hselector : validTokenSelector vocabularySize select)
    (htokens : tokensInVocabulary vocabularySize state.1)
    (hne : state.1 ≠ []) :
    tokensInVocabulary vocabularySize
      (generationTransition select layers embedding vocabularySize
        vocabularyWeights state).1 := by
  have hlength := cachedGeneration_distribution_length hne layers embedding
    vocabularySize vocabularyWeights state.2
  have hselected := hselector
    (cachedGenerationEvaluate layers embedding vocabularySize vocabularyWeights
      state.1 state.2).1 hlength
  intro token htoken
  simp only [generationTransition, List.mem_append, List.mem_singleton] at htoken ⊢
  rcases htoken with htoken | rfl
  · exact htokens token htoken
  · exact hselected

theorem generateSteps_preservesVocabulary {n vocabularySize : Nat}
    {select : Vector ℝ → Nat} {layers : List DecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {vocabularyWeights : Matrix ℝ}
    {state : GenerationState}
    (hselector : validTokenSelector vocabularySize select)
    (htokens : tokensInVocabulary vocabularySize state.1)
    (hne : state.1 ≠ []) :
    tokensInVocabulary vocabularySize
      (generateSteps n select layers embedding vocabularySize
        vocabularyWeights state).1 := by
  induction n generalizing state with
  | zero => exact htokens
  | succ n ih =>
      have hnext := generationTransition_preservesVocabulary
        (layers := layers) (embedding := embedding)
        (vocabularyWeights := vocabularyWeights) (state := state)
        hselector htokens hne
      have hnextNonempty :
          (generationTransition select layers embedding vocabularySize
            vocabularyWeights state).1 ≠ [] := by
        simp [generationTransition, hne]
      exact ih hnext hnextNonempty

end
end DecoderTransformer
