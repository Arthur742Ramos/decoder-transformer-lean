import DecoderTransformer.DecoderBlock
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace DecoderTransformer

noncomputable section

/-!
# GPT-Neo components

This module keeps the GPT-Neo path separate from the modern grouped-query
path: learned position embeddings, LayerNorm, GELU, affine biases, and
optional sliding-window attention are all explicit.
-/

def matrixRowAt (M : Matrix ℝ) (i : Nat) : Vector ℝ := M.getD i []

def affineProject (outDim : Nat) (W : Matrix ℝ) (bias x : Vector ℝ) : Vector ℝ :=
  vectorAdd (linearProject outDim W x) bias

theorem affineProject_shape {inDim outDim : Nat} {W : Matrix ℝ}
    {bias x : Vector ℝ} (hW : matrixShape inDim outDim W)
    (hbias : vectorShape outDim bias) (hx : vectorShape inDim x) :
    vectorShape outDim (affineProject outDim W bias x) := by
  exact vectorAdd_shape (linearProject_shape hW hx) hbias

def gptNeoInputEmbedding (tokenEmbeddings positionEmbeddings : Matrix ℝ)
    (token position : Nat) : Vector ℝ :=
  vectorAdd (matrixRowAt tokenEmbeddings token) (matrixRowAt positionEmbeddings position)

theorem gptNeoInputEmbedding_shape {vocabSize maxPosition modelDim : Nat}
    {tokenEmbeddings positionEmbeddings : Matrix ℝ} {token position : Nat}
    (htoken : token < vocabSize) (hposition : position < maxPosition)
    (htokens : matrixShape vocabSize modelDim tokenEmbeddings)
    (hpositions : matrixShape maxPosition modelDim positionEmbeddings) :
    vectorShape modelDim
      (gptNeoInputEmbedding tokenEmbeddings positionEmbeddings token position) := by
  have ht : token < tokenEmbeddings.length := by simpa [htokens.1] using htoken
  have hp : position < positionEmbeddings.length := by simpa [hpositions.1] using hposition
  have hte : matrixRowAt tokenEmbeddings token = tokenEmbeddings[token]'ht := by
    simp [matrixRowAt, List.getD, ht]
  have hpe : matrixRowAt positionEmbeddings position = positionEmbeddings[position]'hp := by
    simp [matrixRowAt, List.getD, hp]
  have hts : vectorShape modelDim (tokenEmbeddings[token]'ht) := by
    simpa [vectorShape] using
      (matrixShape_nth htokens htoken)
  have hps : vectorShape modelDim (positionEmbeddings[position]'hp) := by
    simpa [vectorShape] using
      (matrixShape_nth hpositions hposition)
  rw [gptNeoInputEmbedding, hte, hpe]
  exact vectorAdd_shape hts hps

def gptNeoLogits (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (hidden : Vector ℝ) : Vector ℝ :=
  linearProject vocabularySize vocabularyWeights hidden

theorem gptNeoLogits_shape {modelDim vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {hidden : Vector ℝ}
    (hweights : matrixShape modelDim vocabularySize vocabularyWeights)
    (hhidden : vectorShape modelDim hidden) :
    vectorShape vocabularySize (gptNeoLogits vocabularySize vocabularyWeights hidden) := by
  exact linearProject_shape hweights hhidden

def gptNeoMean (x : Vector ℝ) : ℝ :=
  if x = [] then 0 else x.sum / x.length

def gptNeoVariance (x : Vector ℝ) : ℝ :=
  if x = [] then 0 else
    (x.map (fun v => (v - gptNeoMean x) * (v - gptNeoMean x))).sum / x.length

def gptNeoNormalized (x : Vector ℝ) (epsilon : ℝ) : Vector ℝ :=
  x.map (fun v => (v - gptNeoMean x) /
    Real.sqrt (gptNeoVariance x + epsilon))

def gptNeoLayerNorm (epsilon : ℝ) (gain bias x : Vector ℝ) : Vector ℝ :=
  List.zipWith (fun gb z => gb.1 * z + gb.2)
    (gain.zip bias) (gptNeoNormalized x epsilon)

theorem gptNeoLayerNorm_shape {n : Nat} {epsilon : ℝ}
    {gain bias x : Vector ℝ} (hgain : vectorShape n gain)
    (hbias : vectorShape n bias) (hx : vectorShape n x) :
    vectorShape n (gptNeoLayerNorm epsilon gain bias x) := by
  have hnorm : (gptNeoNormalized x epsilon).length = n := by
    simp only [gptNeoNormalized, List.length_map]
    exact vectorShape_length hx
  have hgb : (gain.zip bias).length = n := by
    rw [List.length_zip, hgain, hbias]
    simp
  change (List.zipWith (fun gb z => gb.1 * z + gb.2)
      (gain.zip bias) (gptNeoNormalized x epsilon)).length = n
  rw [List.length_zipWith, hgb, hnorm]
  simp

def gptNeoGeluNew (x : ℝ) : ℝ :=
  (1 / 2) * x * (1 + Real.tanh (Real.sqrt (2 / Real.pi) *
    (x + 0.044715 * x * x * x)))

@[simp] theorem gptNeoGeluNew_zero : gptNeoGeluNew 0 = 0 := by
  simp [gptNeoGeluNew]

def gptNeoLocalContext (window : Nat) (xs : List α) : List α :=
  xs.drop (xs.length - min window xs.length)

@[simp] theorem length_gptNeoLocalContext (window : Nat) (xs : List α) :
    (gptNeoLocalContext window xs).length = min window xs.length := by
  simp [gptNeoLocalContext]
  omega

theorem gptNeoLocalContext_short {window : Nat} {xs : List α}
    (hshort : xs.length ≤ window) : gptNeoLocalContext window xs = xs := by
  simp [gptNeoLocalContext, Nat.min_eq_right hshort]

def gptNeoAttentionContext (window : Nat) (xs : List α) : List α :=
  if window = 0 then xs else gptNeoLocalContext window xs

@[simp] theorem gptNeoAttentionContext_global (xs : List α) :
    gptNeoAttentionContext 0 xs = xs := by
  simp [gptNeoAttentionContext]

theorem length_gptNeoAttentionContext (window : Nat) (xs : List α) :
    (gptNeoAttentionContext window xs).length =
      if window = 0 then xs.length else min window xs.length := by
  by_cases h : window = 0 <;> simp [gptNeoAttentionContext, h,
    length_gptNeoLocalContext]

def gptNeoWindowedHeadAttention (headDim window : Nat)
    (WQ WK WV : Matrix ℝ) (x : Vector ℝ) (pref : Matrix ℝ) : Vector ℝ :=
  exactAttention headDim headDim
    (linearProject headDim WQ x)
    ((gptNeoAttentionContext window pref).map (linearProject headDim WK))
    ((gptNeoAttentionContext window pref).map (linearProject headDim WV))

theorem gptNeoWindowedHeadAttention_shape (headDim window : Nat)
    (WQ WK WV : Matrix ℝ) (x : Vector ℝ) (pref : Matrix ℝ) :
    vectorShape headDim
      (gptNeoWindowedHeadAttention headDim window WQ WK WV x pref) := by
  exact exactAttention_shape _ _ _ _ _

def gptNeoWindowedMultiHeadAtPrefix (heads modelDim headDim window : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) (outBias : Vector ℝ) (x : Vector ℝ)
    (pref : Matrix ℝ) : Vector ℝ :=
  affineProject modelDim WO outBias
    ((List.range heads).map (fun h =>
      gptNeoWindowedHeadAttention headDim window
        (tensorMatrixAt WQ h) (tensorMatrixAt WK h) (tensorMatrixAt WV h) x pref)).flatten

theorem gptNeoWindowedMultiHeadAtPrefix_shape
    {heads modelDim headDim window : Nat}
    {WQ WK WV : Tensor3 ℝ} {WO : Matrix ℝ} {outBias x : Vector ℝ}
    {pref : Matrix ℝ}
    (hparams : multiHeadParametersShape heads modelDim headDim WQ WK WV WO)
    (houtBias : vectorShape modelDim outBias) (hx : vectorShape modelDim x) :
    vectorShape modelDim
      (gptNeoWindowedMultiHeadAtPrefix heads modelDim headDim window
        WQ WK WV WO outBias x pref) := by
  apply affineProject_shape hparams.2.2.2 houtBias
  have hrows : ∀ row ∈ (List.range heads).map (fun h =>
      gptNeoWindowedHeadAttention headDim window
        (tensorMatrixAt WQ h) (tensorMatrixAt WK h) (tensorMatrixAt WV h) x pref),
      row.length = headDim := by
    intro row hrow
    rcases List.mem_map.1 hrow with ⟨h, hh, rfl⟩
    exact vectorShape_length (gptNeoWindowedHeadAttention_shape _ _ _ _ _ _ _)
  exact (concat_rows_length hrows).trans (by simp)

def gptNeoMlp (modelDim hiddenDim : Nat) (Wfc : Matrix ℝ) (bfc : Vector ℝ)
    (Wproj : Matrix ℝ) (bproj x : Vector ℝ) : Vector ℝ :=
  affineProject modelDim Wproj bproj
    ((affineProject hiddenDim Wfc bfc x).map gptNeoGeluNew)

theorem gptNeoMlp_shape {modelDim hiddenDim : Nat} {Wfc Wproj : Matrix ℝ}
    {bfc : Vector ℝ} {bproj x : Vector ℝ}
    (hx : vectorShape modelDim x) (hfc : matrixShape modelDim hiddenDim Wfc)
    (hfcBias : vectorShape hiddenDim bfc)
    (hproj : matrixShape hiddenDim modelDim Wproj)
    (hprojBias : vectorShape modelDim bproj) :
    vectorShape modelDim
      (gptNeoMlp modelDim hiddenDim Wfc bfc Wproj bproj x) := by
  have hhidden := affineProject_shape hfc hfcBias hx
  have hactivated : vectorShape hiddenDim
      ((affineProject hiddenDim Wfc bfc x).map gptNeoGeluNew) := by
    simpa [vectorShape] using hhidden
  exact affineProject_shape hproj hprojBias hactivated

structure GPTNeoLayerParameters where
  headCount : Nat
  modelDim : Nat
  headDim : Nat
  hiddenDim : Nat
  attentionWindow : Nat
  normEpsilon : ℝ
  ln1Gain : Vector ℝ
  ln1Bias : Vector ℝ
  ln2Gain : Vector ℝ
  ln2Bias : Vector ℝ
  queryWeights : Tensor3 ℝ
  keyWeights : Tensor3 ℝ
  valueWeights : Tensor3 ℝ
  outputWeights : Matrix ℝ
  outputBias : Vector ℝ
  fcWeights : Matrix ℝ
  fcBias : Vector ℝ
  projectionWeights : Matrix ℝ
  projectionBias : Vector ℝ

def gptNeoNormalizedPrefix (p : GPTNeoLayerParameters) (pref : Matrix ℝ) : Matrix ℝ :=
  pref.map (gptNeoLayerNorm p.normEpsilon p.ln1Gain p.ln1Bias)

def validGPTNeoLayer (p : GPTNeoLayerParameters) : Prop :=
  0 < p.headCount ∧ 0 < p.modelDim ∧ 0 < p.headDim ∧ 0 < p.hiddenDim ∧
  p.modelDim = p.headCount * p.headDim ∧ 0 < p.normEpsilon ∧
  vectorShape p.modelDim p.ln1Gain ∧ vectorShape p.modelDim p.ln1Bias ∧
  vectorShape p.modelDim p.ln2Gain ∧ vectorShape p.modelDim p.ln2Bias ∧
  multiHeadParametersShape p.headCount p.modelDim p.headDim
    p.queryWeights p.keyWeights p.valueWeights p.outputWeights ∧
  vectorShape p.modelDim p.outputBias ∧
  matrixShape p.modelDim p.hiddenDim p.fcWeights ∧
  vectorShape p.hiddenDim p.fcBias ∧
  matrixShape p.hiddenDim p.modelDim p.projectionWeights ∧
  vectorShape p.modelDim p.projectionBias

def gptNeoBlockAtPrefix (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (pref : Matrix ℝ) : Vector ℝ :=
  let normalizedAttention :=
    gptNeoLayerNorm p.normEpsilon p.ln1Gain p.ln1Bias x
  let attention :=
    gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
      p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
      p.outputWeights p.outputBias normalizedAttention
      (gptNeoNormalizedPrefix p pref)
  let attentionResidual := vectorAdd x attention
  let normalizedMlp :=
    gptNeoLayerNorm p.normEpsilon p.ln2Gain p.ln2Bias attentionResidual
  let mlp :=
    gptNeoMlp p.modelDim p.hiddenDim p.fcWeights p.fcBias
      p.projectionWeights p.projectionBias normalizedMlp
  vectorAdd attentionResidual mlp

theorem validGPTNeoBlock_shape {p : GPTNeoLayerParameters} {x : Vector ℝ}
    {pref : Matrix ℝ} (hp : validGPTNeoLayer p)
    (hx : vectorShape p.modelDim x) :
    vectorShape p.modelDim (gptNeoBlockAtPrefix p x pref) := by
  rcases hp with ⟨hhead, hmodel, hheaddim, hhidden, hdim, heps,
    hln1gain, hln1bias, hln2gain, hln2bias, hparams, houtbias,
    hfc, hfcBias, hproj, hprojBias⟩
  have hln1 := gptNeoLayerNorm_shape (epsilon := p.normEpsilon)
    hln1gain hln1bias hx
  have hatt := gptNeoWindowedMultiHeadAtPrefix_shape
    (window := p.attentionWindow)
    (pref := gptNeoNormalizedPrefix p pref)
    (hparams := hparams) (houtBias := houtbias) hln1
  have hres := vectorAdd_shape hx hatt
  have hln2 := gptNeoLayerNorm_shape (epsilon := p.normEpsilon)
    hln2gain hln2bias hres
  have hmlp := gptNeoMlp_shape hln2 hfc hfcBias hproj hprojBias
  simpa [gptNeoBlockAtPrefix] using vectorAdd_shape hres hmlp

def gptNeoFullLayer (p : GPTNeoLayerParameters) : Matrix ℝ → Matrix ℝ :=
  causalAttention id id id (fun x pref _ => gptNeoBlockAtPrefix p x pref)

theorem gptNeoFullLayer_is_causal (p : GPTNeoLayerParameters) :
    causal (gptNeoFullLayer p) := by
  exact causalAttention_is_causal _ _ _ _

theorem validGPTNeoFullLayer_shape {p : GPTNeoLayerParameters} {seqLen : Nat}
    {X : Matrix ℝ} (hp : validGPTNeoLayer p)
    (hX : matrixShape seqLen p.modelDim X) :
    matrixShape seqLen p.modelDim (gptNeoFullLayer p X) := by
  have from_shape : ∀ (Y : Matrix ℝ) (pref : Matrix ℝ),
      matrixShape Y.length p.modelDim Y →
      matrixShape Y.length p.modelDim
        (causalAttentionFrom id id id
          (fun x pref _ => gptNeoBlockAtPrefix p x pref) pref Y) := by
    intro Y
    induction Y with
    | nil =>
        intro pref hY
        simp [causalAttentionFrom, matrixShape]
    | cons y ys ih =>
        intro pref hY
        have hy : vectorShape p.modelDim y := hY.2 y (by simp)
        have hhead :
            (gptNeoBlockAtPrefix p y (pref ++ [y])).length = p.modelDim :=
          vectorShape_length (validGPTNeoBlock_shape hp hy)
        have htailY : matrixShape ys.length p.modelDim ys := by
          refine ⟨rfl, ?_⟩
          intro row hr
          exact hY.2 row (by simp [hr])
        have htail := ih (pref := pref ++ [y]) htailY
        refine ⟨by simp [causalAttentionFrom, length_causalAttentionFrom], ?_⟩
        intro row hrow
        simp only [causalAttentionFrom, List.mem_cons] at hrow
        rcases hrow with rfl | hrow
        · simpa using hhead
        · exact htail.2 row hrow
  have hX' : matrixShape X.length p.modelDim X := by
    refine ⟨rfl, ?_⟩
    exact hX.2
  have hfull := from_shape X [] hX'
  simpa [gptNeoFullLayer, causalAttention, hX.1] using hfull

def gptNeoWindowedCausalAttention (heads modelDim headDim window : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) (outBias : Vector ℝ) :
    Matrix ℝ → Matrix ℝ :=
  causalAttention id id id (fun x pref _ =>
    gptNeoWindowedMultiHeadAtPrefix heads modelDim headDim window
      WQ WK WV WO outBias x pref)

theorem gptNeoWindowedCausalAttention_is_causal (heads modelDim headDim window : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) (outBias : Vector ℝ) :
    causal (gptNeoWindowedCausalAttention heads modelDim headDim window
      WQ WK WV WO outBias) := by
  exact causalAttention_is_causal _ _ _ _

end
end DecoderTransformer
