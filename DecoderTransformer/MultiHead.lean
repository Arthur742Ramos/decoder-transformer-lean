import DecoderTransformer.ExactAttention

namespace DecoderTransformer

noncomputable section

/-!
# Exact multi-head causal attention

Tensor lookup is totalized with `List.getD`; the shape theorems below establish
the intended results on every well-formed parameter tensor.
-/

def tensorMatrixAt (T : Tensor3 ℝ) (h : Nat) : Matrix ℝ := T.getD h []

def multiHeadParametersShape (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) : Prop :=
  tensor3Shape heads modelDim headDim WQ ∧
  tensor3Shape heads modelDim headDim WK ∧
  tensor3Shape heads modelDim headDim WV ∧
  matrixShape (heads * headDim) modelDim WO

theorem multiHeadParameter_nth {heads modelDim headDim : Nat}
    {WQ WK WV : Tensor3 ℝ} {WO : Matrix ℝ}
    (hparams : multiHeadParametersShape heads modelDim headDim WQ WK WV WO)
    {h : Nat} (hh : h < heads) :
    matrixShape modelDim headDim (tensorMatrixAt WQ h) ∧
    matrixShape modelDim headDim (tensorMatrixAt WK h) ∧
    matrixShape modelDim headDim (tensorMatrixAt WV h) := by
  have hq := hparams.1.2 (WQ[h]'(by simpa [hparams.1.1] using hh))
    (by exact List.getElem_mem (by simpa [hparams.1.1] using hh))
  have hk := hparams.2.1.2 (WK[h]'(by simpa [hparams.2.1.1] using hh))
    (by exact List.getElem_mem (by simpa [hparams.2.1.1] using hh))
  have hv := hparams.2.2.1.2 (WV[h]'(by simpa [hparams.2.2.1.1] using hh))
    (by exact List.getElem_mem (by simpa [hparams.2.2.1.1] using hh))
  have hq' : tensorMatrixAt WQ h = WQ[h]'(by simpa [hparams.1.1] using hh) := by
    simp [tensorMatrixAt, List.getD, hh, hparams.1.1]
  have hk' : tensorMatrixAt WK h = WK[h]'(by simpa [hparams.2.1.1] using hh) := by
    simp [tensorMatrixAt, List.getD, hh, hparams.2.1.1]
  have hv' : tensorMatrixAt WV h = WV[h]'(by simpa [hparams.2.2.1.1] using hh) := by
    simp [tensorMatrixAt, List.getD, hh, hparams.2.2.1.1]
  exact ⟨hq' ▸ hq, hk' ▸ hk, hv' ▸ hv⟩

def projectedHeadAttention (modelDim headDim : Nat)
    (WQ WK WV : Matrix ℝ) (x : Vector ℝ) (pref : Matrix ℝ) : Vector ℝ :=
  exactAttention headDim headDim
    (linearProject headDim WQ x)
    (pref.map (linearProject headDim WK))
    (pref.map (linearProject headDim WV))

theorem projectedHeadAttention_shape (modelDim headDim : Nat)
    (WQ WK WV : Matrix ℝ) (x : Vector ℝ) (pref : Matrix ℝ) :
    vectorShape headDim
      (projectedHeadAttention modelDim headDim WQ WK WV x pref) := by
  exact exactAttention_shape _ _ _ _ _

def concatenatedHeadAttention (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (x : Vector ℝ) (pref : Matrix ℝ) : Vector ℝ :=
  (List.range heads).map (fun h =>
    projectedHeadAttention modelDim headDim
      (tensorMatrixAt WQ h) (tensorMatrixAt WK h) (tensorMatrixAt WV h) x pref) |>.flatten

theorem concatenatedHeadAttention_shape (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (x : Vector ℝ) (pref : Matrix ℝ) :
    vectorShape (heads * headDim)
      (concatenatedHeadAttention heads modelDim headDim WQ WK WV x pref) := by
  have hrows : ∀ row ∈ (List.range heads).map (fun h =>
      projectedHeadAttention modelDim headDim
        (tensorMatrixAt WQ h) (tensorMatrixAt WK h) (tensorMatrixAt WV h) x pref),
      row.length = headDim := by
    intro row hrow
    rcases List.mem_map.1 hrow with ⟨h, hh, rfl⟩
    exact vectorShape_length
      (projectedHeadAttention_shape modelDim headDim
        (tensorMatrixAt WQ h) (tensorMatrixAt WK h) (tensorMatrixAt WV h) x pref)
  exact (concat_rows_length hrows).trans (by simp)

def multiHeadAtPrefix (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) (x : Vector ℝ)
    (pref : Matrix ℝ) : Vector ℝ :=
  linearProject modelDim WO
    (concatenatedHeadAttention heads modelDim headDim WQ WK WV x pref)

theorem multiHeadAtPrefix_shape {heads modelDim headDim : Nat}
    {WQ WK WV : Tensor3 ℝ} {WO : Matrix ℝ} {x : Vector ℝ} {pref : Matrix ℝ}
    (hparams : multiHeadParametersShape heads modelDim headDim WQ WK WV WO) :
    vectorShape modelDim
      (multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x pref) := by
  apply linearProject_shape hparams.2.2.2
  exact concatenatedHeadAttention_shape heads modelDim headDim WQ WK WV x pref

def multiHeadCausalAttention (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) : Matrix ℝ → Matrix ℝ :=
  causalAttention id id id (fun x pref _ =>
    multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x pref)

@[simp] theorem length_multiHeadCausalAttention (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) (xs : Matrix ℝ) :
    (multiHeadCausalAttention heads modelDim headDim WQ WK WV WO xs).length = xs.length := by
  simpa [multiHeadCausalAttention, causalAttentionFrom] using
    (length_causalAttention id id id
      (fun x pref _ => multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x pref)
      xs)

theorem multiHeadCausalAttention_from_rows
    {heads modelDim headDim : Nat} {WQ WK WV : Tensor3 ℝ} {WO : Matrix ℝ}
    (hparams : multiHeadParametersShape heads modelDim headDim WQ WK WV WO)
    (pref xs : Matrix ℝ) :
    ∀ row ∈ causalAttentionFrom id id id
      (fun x pref _ => multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x pref)
      pref xs, row.length = modelDim := by
  induction xs generalizing pref with
  | nil =>
      intro row hrow
      simp [causalAttentionFrom] at hrow
  | cons x xs ih =>
      have hhead :
          (multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x (pref ++ [x])).length =
            modelDim := by
        exact vectorShape_length (multiHeadAtPrefix_shape hparams)
      have htail := ih (pref := pref ++ [x])
      intro row hrow
      simp only [causalAttentionFrom, List.mem_cons] at hrow
      rcases hrow with rfl | hrow
      · simpa using hhead
      · exact htail row hrow

theorem multiHeadCausalAttention_shape
    {heads modelDim headDim seqLen : Nat}
    {WQ WK WV : Tensor3 ℝ} {WO : Matrix ℝ} {xs : Matrix ℝ}
    (hparams : multiHeadParametersShape heads modelDim headDim WQ WK WV WO)
    (hinput : matrixShape seqLen modelDim xs) :
    matrixShape seqLen modelDim
      (multiHeadCausalAttention heads modelDim headDim WQ WK WV WO xs) := by
  refine ⟨by simpa [multiHeadCausalAttention] using
      (length_causalAttention id id id
        (fun x pref _ => multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x pref) xs)
      |>.trans hinput.1, ?_⟩
  intro row hrow
  exact multiHeadCausalAttention_from_rows hparams [] xs row hrow

theorem multiHeadCausalAttention_is_causal (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) :
    causal (multiHeadCausalAttention heads modelDim headDim WQ WK WV WO) := by
  exact causalAttention_is_causal _ _ _ _

theorem multiHeadCausalAttention_independence (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) {i : Nat} {xs ys : Matrix ℝ}
    (hiₓ : i < xs.length) (hiᵧ : i < ys.length)
    (hprefix : xs.take (i + 1) = ys.take (i + 1)) :
    (multiHeadCausalAttention heads modelDim headDim WQ WK WV WO xs)[i]? =
      (multiHeadCausalAttention heads modelDim headDim WQ WK WV WO ys)[i]? := by
  exact causalAttention_independence _ _ _ _ hiₓ hiᵧ hprefix

theorem multiHeadCausalAttention_append (heads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) (xs : Matrix ℝ) (x : Vector ℝ) :
    multiHeadCausalAttention heads modelDim headDim WQ WK WV WO (xs ++ [x]) =
      multiHeadCausalAttention heads modelDim headDim WQ WK WV WO xs ++
        [multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x (xs ++ [x])] := by
  let F : Vector ℝ → Matrix ℝ → Matrix ℝ → Vector ℝ := fun x pref _ =>
    multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x pref
  have h := causalAttention_append id id id F xs [x]
  have hsingle : causalAttentionFrom id id id F xs [x] =
      [multiHeadAtPrefix heads modelDim headDim WQ WK WV WO x (xs ++ [x])] := by
    simp [causalAttentionFrom, F]
  rw [hsingle] at h
  simpa [multiHeadCausalAttention, F] using h

end
end DecoderTransformer
