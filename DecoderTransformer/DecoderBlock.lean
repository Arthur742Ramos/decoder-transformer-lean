import DecoderTransformer.MultiHead

namespace DecoderTransformer

noncomputable section

/-!
# Normalization, residuals, and decoder blocks

This module is the direct Lean counterpart of `Decoder_Block.thy`.  The
sequence residual is totalized with `List.zipWith`; its shape hypotheses are
what guarantee that no row is silently dropped.
-/

def rmsDenominator (epsilon : ℝ) (x : Vector ℝ) : ℝ :=
  Real.sqrt ((x.map (fun v => v * v)).sum / x.length + epsilon)

def rmsNorm (epsilon : ℝ) (gain x : Vector ℝ) : Vector ℝ :=
  List.zipWith (fun g v => g * (v / rmsDenominator epsilon x)) gain x

theorem rmsNorm_shape {modelDim : Nat} {epsilon : ℝ} {gain x : Vector ℝ}
    (hgain : vectorShape modelDim gain) (hx : vectorShape modelDim x) :
    vectorShape modelDim (rmsNorm epsilon gain x) := by
  change (List.zipWith (fun g v => g * (v / rmsDenominator epsilon x)) gain x).length =
    modelDim
  rw [List.length_zipWith, hgain, hx]
  simp

def rmsNormSequence (epsilon : ℝ) (gain : Vector ℝ) (X : Matrix ℝ) : Matrix ℝ :=
  X.map (rmsNorm epsilon gain)

theorem rmsNormSequence_shape {modelDim seqLen : Nat} {epsilon : ℝ}
    {gain : Vector ℝ} {X : Matrix ℝ}
    (hgain : vectorShape modelDim gain) (hX : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim (rmsNormSequence epsilon gain X) := by
  refine ⟨by simp [rmsNormSequence, hX.1], ?_⟩
  intro row hrow
  rcases List.mem_map.1 hrow with ⟨source, hsource, rfl⟩
  exact vectorShape_length (rmsNorm_shape hgain (hX.2 source hsource))

theorem rmsNormSequence_is_causal (epsilon : ℝ) (gain : Vector ℝ) :
    causal (rmsNormSequence epsilon gain) := by
  exact causal_map _

@[simp] theorem length_rmsNormSequence (epsilon : ℝ) (gain : Vector ℝ)
    (X : Matrix ℝ) : (rmsNormSequence epsilon gain X).length = X.length := by
  simp [rmsNormSequence]

def feedForward (modelDim hiddenDim : Nat) (activation : ℝ → ℝ)
    (Wup Wdown : Matrix ℝ) (x : Vector ℝ) : Vector ℝ :=
  linearProject modelDim Wdown
    ((linearProject hiddenDim Wup x).map activation)

theorem feedForward_shape {modelDim hiddenDim : Nat} {activation : ℝ → ℝ}
    {Wup Wdown : Matrix ℝ} {x : Vector ℝ}
    (hx : vectorShape modelDim x) (hup : matrixShape modelDim hiddenDim Wup)
    (hdown : matrixShape hiddenDim modelDim Wdown) :
    vectorShape modelDim (feedForward modelDim hiddenDim activation Wup Wdown x) := by
  apply linearProject_shape hdown
  have hhidden : vectorShape hiddenDim (linearProject hiddenDim Wup x) :=
    linearProject_shape hup hx
  simpa [vectorShape] using hhidden

def feedForwardSequence (modelDim hiddenDim : Nat) (activation : ℝ → ℝ)
    (Wup Wdown : Matrix ℝ) (X : Matrix ℝ) : Matrix ℝ :=
  X.map (feedForward modelDim hiddenDim activation Wup Wdown)

theorem feedForwardSequence_shape {modelDim hiddenDim seqLen : Nat}
    {activation : ℝ → ℝ} {Wup Wdown X : Matrix ℝ}
    (hX : matrixShape seqLen modelDim X)
    (hup : matrixShape modelDim hiddenDim Wup)
    (hdown : matrixShape hiddenDim modelDim Wdown) :
    matrixShape seqLen modelDim
      (feedForwardSequence modelDim hiddenDim activation Wup Wdown X) := by
  refine ⟨by simp [feedForwardSequence, hX.1], ?_⟩
  intro row hrow
  rcases List.mem_map.1 hrow with ⟨source, hsource, rfl⟩
  exact vectorShape_length (feedForward_shape (hX.2 source hsource) hup hdown)

theorem feedForwardSequence_is_causal (modelDim hiddenDim : Nat)
    (activation : ℝ → ℝ) (Wup Wdown : Matrix ℝ) :
    causal (feedForwardSequence modelDim hiddenDim activation Wup Wdown) := by
  exact causal_map _

@[simp] theorem length_feedForwardSequence (modelDim hiddenDim : Nat)
    (activation : ℝ → ℝ) (Wup Wdown X : Matrix ℝ) :
    (feedForwardSequence modelDim hiddenDim activation Wup Wdown X).length = X.length := by
  simp [feedForwardSequence]

def sequenceResidual (X Y : Matrix ℝ) : Matrix ℝ :=
  List.zipWith vectorAdd X Y

theorem sequenceResidual_take (n : Nat) (X Y : Matrix ℝ) :
    (sequenceResidual X Y).take n = sequenceResidual (X.take n) (Y.take n) := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
      cases X with
      | nil => simp [sequenceResidual]
      | cons x X =>
          cases Y with
          | nil => simp [sequenceResidual]
          | cons y Y =>
              simp only [sequenceResidual, List.zipWith_cons_cons,
                List.take_succ_cons]
              congr 1
              simpa [sequenceResidual] using ih X Y

theorem sequenceResidual_shape {seqLen modelDim : Nat} {X Y : Matrix ℝ}
    (hX : matrixShape seqLen modelDim X) (hY : matrixShape seqLen modelDim Y) :
    matrixShape seqLen modelDim (sequenceResidual X Y) := by
  induction X generalizing Y seqLen with
  | nil =>
      cases Y <;> simp_all [sequenceResidual, matrixShape]
  | cons x X ih =>
      cases Y with
      | nil =>
          have hxlen := hX.1
          have hylen := hY.1
          simp at hxlen hylen
          omega
      | cons y Y =>
          have hlen : (y :: Y).length = (x :: X).length := hY.1.trans hX.1.symm
          have htailLen : Y.length = X.length := by simpa using hlen
          have hx : x.length = modelDim := hX.2 x (by simp)
          have hy : y.length = modelDim := hY.2 y (by simp)
          have hXt : matrixShape X.length modelDim X := by
            refine ⟨rfl, ?_⟩
            intro row hr
            exact hX.2 row (by simp [hr])
          have hYt : matrixShape Y.length modelDim Y := by
            refine ⟨rfl, ?_⟩
            intro row hr
            exact hY.2 row (by simp [hr])
          have ht : matrixShape X.length modelDim (sequenceResidual X Y) :=
            ih hXt (by simpa [htailLen] using hYt)
          refine ⟨?_, ?_⟩
          · simp only [sequenceResidual, List.length_cons, List.length_zipWith]
            rw [htailLen, min_self]
            exact hX.1
          · intro row hrow
            simp only [sequenceResidual, List.zipWith_cons_cons, List.mem_cons] at hrow
            rcases hrow with rfl | hrow
            · exact vectorShape_length (vectorAdd_shape
                (by simpa [vectorShape] using hx)
                (by simpa [vectorShape] using hy))
            · exact ht.2 row hrow

theorem length_sequenceResidual {X Y : Matrix ℝ} (hXY : X.length = Y.length) :
    (sequenceResidual X Y).length = X.length := by
  simp [sequenceResidual, List.length_zipWith, hXY]

theorem sequenceResidual_append {X Y : Matrix ℝ} {x y : Vector ℝ}
    (hXY : X.length = Y.length) :
    sequenceResidual (X ++ [x]) (Y ++ [y]) =
      sequenceResidual X Y ++ [vectorAdd x y] := by
  induction X generalizing Y with
  | nil =>
      cases Y <;> simp [sequenceResidual] at hXY ⊢
  | cons a X ih =>
      cases Y with
      | nil => simp_all [sequenceResidual]
      | cons b Y =>
          simp only [sequenceResidual, List.zipWith_cons_cons, List.append_assoc,
            List.cons_append]
          have htail : X.length = Y.length := by simpa using hXY
          congr 1
          simpa [sequenceResidual] using ih htail

def residualBlock (F : Matrix ℝ → Matrix ℝ) (X : Matrix ℝ) : Matrix ℝ :=
  sequenceResidual X (F X)

theorem residualBlock_shape {seqLen modelDim : Nat} {F : Matrix ℝ → Matrix ℝ}
    {X : Matrix ℝ} (hX : matrixShape seqLen modelDim X)
    (hFX : matrixShape seqLen modelDim (F X)) :
    matrixShape seqLen modelDim (residualBlock F X) := by
  exact sequenceResidual_shape hX hFX

theorem residualBlock_is_causal {F : Matrix ℝ → Matrix ℝ}
    (hF : causal F) : causal (residualBlock F) := by
  intro n X Y hXY
  simp only [prefixEq] at hXY ⊢
  simp only [residualBlock]
  rw [sequenceResidual_take, sequenceResidual_take]
  exact congrArg₂ sequenceResidual hXY (hF n X Y hXY)

def attentionResidualBlock (heads modelDim headDim : Nat) (epsilon : ℝ)
    (attentionGain : Vector ℝ) (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) :
    Matrix ℝ → Matrix ℝ := fun X =>
  residualBlock
    (fun Z => multiHeadCausalAttention heads modelDim headDim WQ WK WV WO
      (rmsNormSequence epsilon attentionGain Z)) X

theorem attentionResidualBlock_shape {heads modelDim headDim seqLen : Nat}
    {epsilon : ℝ} {attentionGain : Vector ℝ} {WQ WK WV : Tensor3 ℝ}
    {WO X : Matrix ℝ}
    (hparams : multiHeadParametersShape heads modelDim headDim WQ WK WV WO)
    (hgain : vectorShape modelDim attentionGain)
    (hX : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim
      (attentionResidualBlock heads modelDim headDim epsilon attentionGain
        WQ WK WV WO X) := by
  apply residualBlock_shape hX
  apply multiHeadCausalAttention_shape hparams
  exact rmsNormSequence_shape hgain hX

theorem attentionResidualBlock_is_causal (heads modelDim headDim : Nat)
    (epsilon : ℝ) (attentionGain : Vector ℝ) (WQ WK WV : Tensor3 ℝ)
    (WO : Matrix ℝ) :
    causal (attentionResidualBlock heads modelDim headDim epsilon attentionGain
      WQ WK WV WO) := by
  apply residualBlock_is_causal
  apply causal_comp
  · exact rmsNormSequence_is_causal _ _
  · exact multiHeadCausalAttention_is_causal _ _ _ _ _ _ _

theorem attentionResidualBlock_append (heads modelDim headDim : Nat)
    (epsilon : ℝ) (attentionGain : Vector ℝ) (WQ WK WV : Tensor3 ℝ)
    (WO : Matrix ℝ) (X : Matrix ℝ) (x : Vector ℝ) :
    attentionResidualBlock heads modelDim headDim epsilon attentionGain
        WQ WK WV WO (X ++ [x]) =
      attentionResidualBlock heads modelDim headDim epsilon attentionGain
        WQ WK WV WO X ++
      [vectorAdd x
        (multiHeadAtPrefix heads modelDim headDim WQ WK WV WO
          (rmsNorm epsilon attentionGain x)
          (rmsNormSequence epsilon attentionGain X ++
            [rmsNorm epsilon attentionGain x]))] := by
  simp only [attentionResidualBlock, residualBlock]
  have hnorm : rmsNormSequence epsilon attentionGain (X ++ [x]) =
      rmsNormSequence epsilon attentionGain X ++
        [rmsNorm epsilon attentionGain x] := by
    simp [rmsNormSequence]
  rw [hnorm, multiHeadCausalAttention_append]
  apply sequenceResidual_append
  simp

@[simp] theorem length_attentionResidualBlock (heads modelDim headDim : Nat)
    (epsilon : ℝ) (attentionGain : Vector ℝ) (WQ WK WV : Tensor3 ℝ)
    (WO : Matrix ℝ) (X : Matrix ℝ) :
    (attentionResidualBlock heads modelDim headDim epsilon attentionGain
      WQ WK WV WO X).length = X.length := by
  apply length_sequenceResidual
  simp [attentionResidualBlock, length_rmsNormSequence,
    length_multiHeadCausalAttention]

def mlpResidualBlock (modelDim hiddenDim : Nat) (epsilon : ℝ)
    (activation : ℝ → ℝ) (mlpGain : Vector ℝ) (Wup Wdown : Matrix ℝ) :
    Matrix ℝ → Matrix ℝ := fun X =>
  residualBlock
    (fun Z => feedForwardSequence modelDim hiddenDim activation Wup Wdown
      (rmsNormSequence epsilon mlpGain Z)) X

theorem mlpResidualBlock_shape {modelDim hiddenDim seqLen : Nat}
    {epsilon : ℝ} {activation : ℝ → ℝ} {mlpGain : Vector ℝ}
    {Wup Wdown X : Matrix ℝ}
    (hgain : vectorShape modelDim mlpGain)
    (hup : matrixShape modelDim hiddenDim Wup)
    (hdown : matrixShape hiddenDim modelDim Wdown)
    (hX : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim
      (mlpResidualBlock modelDim hiddenDim epsilon activation mlpGain Wup Wdown X) := by
  apply residualBlock_shape hX
  apply feedForwardSequence_shape
  · exact rmsNormSequence_shape hgain hX
  · exact hup
  · exact hdown

theorem mlpResidualBlock_is_causal (modelDim hiddenDim : Nat) (epsilon : ℝ)
    (activation : ℝ → ℝ) (mlpGain : Vector ℝ) (Wup Wdown : Matrix ℝ) :
    causal (mlpResidualBlock modelDim hiddenDim epsilon activation mlpGain Wup Wdown) := by
  apply residualBlock_is_causal
  apply causal_comp
  · exact rmsNormSequence_is_causal _ _
  · exact feedForwardSequence_is_causal _ _ _ _ _

theorem mlpResidualBlock_append (modelDim hiddenDim : Nat) (epsilon : ℝ)
    (activation : ℝ → ℝ) (mlpGain : Vector ℝ) (Wup Wdown X : Matrix ℝ)
    (x : Vector ℝ) :
    mlpResidualBlock modelDim hiddenDim epsilon activation mlpGain Wup Wdown (X ++ [x]) =
      mlpResidualBlock modelDim hiddenDim epsilon activation mlpGain Wup Wdown X ++
      [vectorAdd x (feedForward modelDim hiddenDim activation Wup Wdown
        (rmsNorm epsilon mlpGain x))] := by
  simp only [mlpResidualBlock, residualBlock]
  have hnorm : rmsNormSequence epsilon mlpGain (X ++ [x]) =
      rmsNormSequence epsilon mlpGain X ++ [rmsNorm epsilon mlpGain x] := by
    simp [rmsNormSequence]
  rw [hnorm]
  have hff : feedForwardSequence modelDim hiddenDim activation Wup Wdown
      (rmsNormSequence epsilon mlpGain X ++ [rmsNorm epsilon mlpGain x]) =
      feedForwardSequence modelDim hiddenDim activation Wup Wdown
        (rmsNormSequence epsilon mlpGain X) ++
        [feedForward modelDim hiddenDim activation Wup Wdown
          (rmsNorm epsilon mlpGain x)] := by
    simp [feedForwardSequence]
  rw [hff]
  apply sequenceResidual_append
  simp

@[simp] theorem length_mlpResidualBlock (modelDim hiddenDim : Nat) (epsilon : ℝ)
    (activation : ℝ → ℝ) (mlpGain : Vector ℝ) (Wup Wdown X : Matrix ℝ) :
    (mlpResidualBlock modelDim hiddenDim epsilon activation mlpGain Wup Wdown X).length =
      X.length := by
  apply length_sequenceResidual
  simp [mlpResidualBlock, length_rmsNormSequence,
    length_feedForwardSequence]

def decoderBlock (heads modelDim headDim hiddenDim : Nat) (epsilon : ℝ)
    (activation : ℝ → ℝ) (attentionGain mlpGain : Vector ℝ)
    (WQ WK WV : Tensor3 ℝ) (WO Wup Wdown : Matrix ℝ) : Matrix ℝ → Matrix ℝ :=
  mlpResidualBlock modelDim hiddenDim epsilon activation mlpGain Wup Wdown ∘
    attentionResidualBlock heads modelDim headDim epsilon attentionGain WQ WK WV WO

theorem decoderBlock_shape {heads modelDim headDim hiddenDim seqLen : Nat}
    {epsilon : ℝ} {activation : ℝ → ℝ} {attentionGain mlpGain : Vector ℝ}
    {WQ WK WV : Tensor3 ℝ} {WO Wup Wdown X : Matrix ℝ}
    (hparams : multiHeadParametersShape heads modelDim headDim WQ WK WV WO)
    (hattentionGain : vectorShape modelDim attentionGain)
    (hmlpGain : vectorShape modelDim mlpGain)
    (hup : matrixShape modelDim hiddenDim Wup)
    (hdown : matrixShape hiddenDim modelDim Wdown)
    (hX : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim
      (decoderBlock heads modelDim headDim hiddenDim epsilon activation
        attentionGain mlpGain WQ WK WV WO Wup Wdown X) := by
  apply mlpResidualBlock_shape hmlpGain hup hdown
  exact attentionResidualBlock_shape hparams hattentionGain hX

theorem decoderBlock_is_causal (heads modelDim headDim hiddenDim : Nat)
    (epsilon : ℝ) (activation : ℝ → ℝ) (attentionGain mlpGain : Vector ℝ)
    (WQ WK WV : Tensor3 ℝ) (WO Wup Wdown : Matrix ℝ) :
    causal (decoderBlock heads modelDim headDim hiddenDim epsilon activation
      attentionGain mlpGain WQ WK WV WO Wup Wdown) := by
  exact causal_comp
    (attentionResidualBlock_is_causal heads modelDim headDim epsilon
      attentionGain WQ WK WV WO)
    (mlpResidualBlock_is_causal _ _ _ _ _ _ _)

@[simp] theorem length_decoderBlock (heads modelDim headDim hiddenDim : Nat)
    (epsilon : ℝ) (activation : ℝ → ℝ) (attentionGain mlpGain : Vector ℝ)
    (WQ WK WV : Tensor3 ℝ) (WO Wup Wdown X : Matrix ℝ) :
    (decoderBlock heads modelDim headDim hiddenDim epsilon activation
      attentionGain mlpGain WQ WK WV WO Wup Wdown X).length = X.length := by
  simp [decoderBlock, length_attentionResidualBlock, length_mlpResidualBlock]

end
end DecoderTransformer
