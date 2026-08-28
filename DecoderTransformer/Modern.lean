import DecoderTransformer.Rotary
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Grouped-query attention and SwiGLU
-/

def groupedQueryParametersShape (queryHeads kvHeads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) : Prop :=
  0 < queryHeads ∧
  0 < kvHeads ∧
  kvHeads ∣ queryHeads ∧
  tensor3Shape queryHeads modelDim headDim WQ ∧
  tensor3Shape kvHeads modelDim headDim WK ∧
  tensor3Shape kvHeads modelDim headDim WV ∧
  matrixShape (queryHeads * headDim) modelDim WO

def groupedQueryHeadIndex (queryHeads kvHeads queryHead : Nat) : Nat :=
  queryHead / (queryHeads / kvHeads)

theorem groupedQueryHeadIndex_bound
    {queryHeads kvHeads queryHead : Nat}
    (hquery : 0 < queryHeads) (hkv : 0 < kvHeads)
    (hgroups : kvHeads ∣ queryHeads) (hhead : queryHead < queryHeads) :
    groupedQueryHeadIndex queryHeads kvHeads queryHead < kvHeads := by
  have hle : kvHeads ≤ queryHeads := Nat.le_of_dvd
    (Nat.zero_lt_of_lt hquery) hgroups
  have hquot : 0 < queryHeads / kvHeads := Nat.div_pos hle hkv
  have hmul : queryHeads / kvHeads * kvHeads = queryHeads :=
    Nat.div_mul_cancel hgroups
  unfold groupedQueryHeadIndex
  apply (Nat.div_lt_iff_lt_mul hquot).2
  calc
    queryHead < queryHeads := hhead
    _ = (queryHeads / kvHeads) * kvHeads := hmul.symm
    _ = kvHeads * (queryHeads / kvHeads) := by ac_rfl

def groupedQueryAtPrefix (queryHeads kvHeads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) (x : Vector ℝ)
    (pref : Matrix ℝ) : Vector ℝ :=
  linearProject modelDim WO
    (List.flatten ((List.range queryHeads).map (fun h =>
      let g := groupedQueryHeadIndex queryHeads kvHeads h
      exactAttention headDim headDim
        (linearProject headDim (tensorMatrixAt WQ h) x)
        (pref.map (linearProject headDim (tensorMatrixAt WK g)))
        (pref.map (linearProject headDim (tensorMatrixAt WV g))))))

theorem groupedQueryAtPrefix_shape
    {queryHeads kvHeads modelDim headDim : Nat}
    {WQ WK WV : Tensor3 ℝ} {WO : Matrix ℝ}
    {x : Vector ℝ} {pref : Matrix ℝ}
    (hparams : groupedQueryParametersShape queryHeads kvHeads modelDim headDim
      WQ WK WV WO) :
    vectorShape modelDim
      (groupedQueryAtPrefix queryHeads kvHeads modelDim headDim
        WQ WK WV WO x pref) := by
  rcases hparams with ⟨hquery, hkv, hgroups, hWQ, hWK, hWV, hWO⟩
  have hrows : ∀ row ∈ (List.range queryHeads).map (fun h =>
      let g := groupedQueryHeadIndex queryHeads kvHeads h
      exactAttention headDim headDim
        (linearProject headDim (tensorMatrixAt WQ h) x)
        (pref.map (linearProject headDim (tensorMatrixAt WK g)))
        (pref.map (linearProject headDim (tensorMatrixAt WV g)))),
      row.length = headDim := by
    intro row hrow
    rcases List.mem_map.1 hrow with ⟨h, hh, rfl⟩
    exact vectorShape_length (exactAttention_shape _ _ _ _ _)
  apply linearProject_shape hWO
  exact (concat_rows_length hrows).trans (by simp)

def groupedQueryCausalAttention (queryHeads kvHeads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) : Matrix ℝ → Matrix ℝ :=
  causalAttention id id id (fun x pref _ =>
    groupedQueryAtPrefix queryHeads kvHeads modelDim headDim WQ WK WV WO x pref)

theorem groupedQueryCausalAttention_is_causal
    (queryHeads kvHeads modelDim headDim : Nat)
    (WQ WK WV : Tensor3 ℝ) (WO : Matrix ℝ) :
    causal (groupedQueryCausalAttention queryHeads kvHeads modelDim headDim
      WQ WK WV WO) := by
  exact causalAttention_is_causal _ _ _ _

theorem groupedQueryCausalAttention_shape
    {queryHeads kvHeads modelDim headDim seqLen : Nat}
    {WQ WK WV : Tensor3 ℝ} {WO : Matrix ℝ} {xs : Matrix ℝ}
    (hparams : groupedQueryParametersShape queryHeads kvHeads modelDim headDim
      WQ WK WV WO) (hinput : matrixShape seqLen modelDim xs) :
    matrixShape seqLen modelDim
      (groupedQueryCausalAttention queryHeads kvHeads modelDim headDim
        WQ WK WV WO xs) := by
  have hrowsFrom : ∀ (pref ys : Matrix ℝ), ∀ row ∈ causalAttentionFrom id id id
      (fun x pref _ => groupedQueryAtPrefix queryHeads kvHeads modelDim headDim
        WQ WK WV WO x pref) pref ys, row.length = modelDim := by
    intro pref ys
    induction ys generalizing pref with
    | nil =>
        intro row hrow
        simp [causalAttentionFrom] at hrow
    | cons x xs ih =>
        intro row hrow
        simp only [causalAttentionFrom, List.mem_cons] at hrow
        rcases hrow with rfl | hrow
        · exact vectorShape_length (groupedQueryAtPrefix_shape hparams)
        · exact ih (pref := pref ++ [x]) row hrow
  have hrows := hrowsFrom [] xs
  refine ⟨?_, hrows⟩
  change (causalAttentionFrom id id id
      (fun x pref _ => groupedQueryAtPrefix queryHeads kvHeads modelDim headDim
        WQ WK WV WO x pref) [] xs).length = seqLen
  exact (length_causalAttention id id id
      (fun x pref _ => groupedQueryAtPrefix queryHeads kvHeads modelDim headDim
        WQ WK WV WO x pref) xs).trans hinput.1

def vectorHadamard (xs ys : Vector ℝ) : Vector ℝ :=
  List.zipWith (· * ·) xs ys

theorem vectorHadamard_shape {n : Nat} {xs ys : Vector ℝ}
    (hxs : vectorShape n xs) (hys : vectorShape n ys) :
    vectorShape n (vectorHadamard xs ys) := by
  change (List.zipWith (· * ·) xs ys).length = n
  rw [List.length_zipWith, hxs, hys]
  simp

def silu (x : ℝ) : ℝ := x / (1 + Real.exp (-x))

def gatedFeedForward (modelDim hiddenDim : Nat) (activation : ℝ → ℝ)
    (Wgate Wup Wdown : Matrix ℝ) (x : Vector ℝ) : Vector ℝ :=
  linearProject modelDim Wdown
    (vectorHadamard
      ((linearProject hiddenDim Wgate x).map activation)
      (linearProject hiddenDim Wup x))

def swiglu (modelDim hiddenDim : Nat)
    (Wgate Wup Wdown : Matrix ℝ) : Vector ℝ → Vector ℝ :=
  gatedFeedForward modelDim hiddenDim silu Wgate Wup Wdown

theorem gatedFeedForward_shape
    {modelDim hiddenDim : Nat} {activation : ℝ → ℝ}
    {Wgate Wup Wdown : Matrix ℝ} {x : Vector ℝ}
    (hx : vectorShape modelDim x)
    (hgate : matrixShape modelDim hiddenDim Wgate)
    (hup : matrixShape modelDim hiddenDim Wup)
    (hdown : matrixShape hiddenDim modelDim Wdown) :
    vectorShape modelDim
      (gatedFeedForward modelDim hiddenDim activation Wgate Wup Wdown x) := by
  apply linearProject_shape hdown
  apply vectorHadamard_shape
  · simpa [vectorShape] using
      (linearProject_shape hgate hx :
        vectorShape hiddenDim (linearProject hiddenDim Wgate x))
  · exact linearProject_shape hup hx

theorem swiglu_shape {modelDim hiddenDim : Nat}
    {Wgate Wup Wdown : Matrix ℝ} {x : Vector ℝ}
    (hx : vectorShape modelDim x)
    (hgate : matrixShape modelDim hiddenDim Wgate)
    (hup : matrixShape modelDim hiddenDim Wup)
    (hdown : matrixShape hiddenDim modelDim Wdown) :
    vectorShape modelDim (swiglu modelDim hiddenDim Wgate Wup Wdown x) := by
  exact gatedFeedForward_shape hx hgate hup hdown

def gatedFeedForwardSequence (modelDim hiddenDim : Nat)
    (activation : ℝ → ℝ) (Wgate Wup Wdown : Matrix ℝ) :
    Matrix ℝ → Matrix ℝ :=
  List.map (gatedFeedForward modelDim hiddenDim activation Wgate Wup Wdown)

theorem gatedFeedForwardSequence_is_causal
    (modelDim hiddenDim : Nat) (activation : ℝ → ℝ)
    (Wgate Wup Wdown : Matrix ℝ) :
    causal (gatedFeedForwardSequence modelDim hiddenDim activation
      Wgate Wup Wdown) := by
  exact causal_map _

end
end DecoderTransformer
