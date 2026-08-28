import DecoderTransformer.Shaped
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Exact scaled dot-product attention

This is the real-valued attention layer from `Exact_Attention.thy`.  The
softmax is total, while its normalization and positivity facts correctly
require a nonempty key history.  Out-of-range value coordinates are read as
zero; all well-shaped uses therefore agree with Isabelle's totalized list
lookup.
-/

def softmaxDenominator (xs : List ℝ) : ℝ :=
  (xs.map Real.exp).sum

def listSoftmax (xs : List ℝ) : List ℝ :=
  xs.map (fun x => Real.exp x / softmaxDenominator xs)

@[simp] theorem length_listSoftmax (xs : List ℝ) :
    (listSoftmax xs).length = xs.length := by
  simp [listSoftmax]

@[simp] theorem listSoftmax_empty : listSoftmax ([] : List ℝ) = [] := by
  simp [listSoftmax]

theorem softmaxDenominator_pos {xs : List ℝ} (hxs : xs ≠ []) :
    0 < softmaxDenominator xs := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simp only [softmaxDenominator, List.map, List.sum_cons]
      have htail : ∀ ys : List ℝ, 0 ≤ (ys.map Real.exp).sum := by
        intro ys
        induction ys with
        | nil => simp
        | cons y ys ih =>
            simp only [List.map, List.sum_cons]
            exact add_nonneg (le_of_lt (Real.exp_pos y)) ih
      exact add_pos_of_pos_of_nonneg (Real.exp_pos x) (htail xs)

theorem sumListMapDivide (f : α → ℝ) (c : ℝ) (xs : List α) :
    (xs.map (fun x => f x / c)).sum = (xs.map f).sum / c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map, List.sum_cons]
      rw [ih, add_div]

theorem listSoftmax_normalized {xs : List ℝ} (hxs : xs ≠ []) :
    (listSoftmax xs).sum = 1 := by
  have hpos := softmaxDenominator_pos hxs
  have hne : softmaxDenominator xs ≠ 0 := ne_of_gt hpos
  rw [listSoftmax, sumListMapDivide]
  change (xs.map Real.exp).sum / softmaxDenominator xs = 1
  exact div_self hne

theorem listSoftmax_positive {xs : List ℝ} {w : ℝ}
    (hxs : xs ≠ []) (hw : w ∈ listSoftmax xs) : 0 < w := by
  have hden : 0 < softmaxDenominator xs := softmaxDenominator_pos hxs
  rcases (List.mem_map.1 hw) with ⟨x, hx, rfl⟩
  exact div_pos (Real.exp_pos x) hden

def scaledDotScore (headDim : Nat) (q k : Vector ℝ) : ℝ :=
  dotProduct q k / Real.sqrt (headDim : ℝ)

def attentionWeights (headDim : Nat) (q : Vector ℝ) (keys : Matrix ℝ) :
    Vector ℝ :=
  listSoftmax (keys.map (scaledDotScore headDim q))

@[simp] theorem length_attentionWeights (headDim : Nat) (q : Vector ℝ)
    (keys : Matrix ℝ) : (attentionWeights headDim q keys).length = keys.length := by
  simp [attentionWeights]

@[simp] theorem attention_weights_length (headDim : Nat) (q : Vector ℝ)
    (keys : Matrix ℝ) : (attentionWeights headDim q keys).length = keys.length :=
  length_attentionWeights headDim q keys

theorem attentionWeights_normalized {headDim : Nat} {q : Vector ℝ}
    {keys : Matrix ℝ} (hkeys : keys ≠ []) :
    (attentionWeights headDim q keys).sum = 1 := by
  exact listSoftmax_normalized (by simpa [attentionWeights] using hkeys)

theorem attentionWeights_positive {headDim : Nat} {q : Vector ℝ}
    {keys : Matrix ℝ} {w : ℝ} (hkeys : keys ≠ [])
    (hw : w ∈ attentionWeights headDim q keys) : 0 < w := by
  exact listSoftmax_positive (by simpa [attentionWeights] using hkeys) hw

theorem prefix_attentionWeights_normalized (headDim : Nat) (q : Vector ℝ)
    (K : α → Vector ℝ) (pref : List α) (x : α) :
    (attentionWeights headDim q (pref.map K ++ [x].map K)).sum = 1 := by
  apply attentionWeights_normalized
  simp

def weightedValueSum (valueDim : Nat) (weights : Vector ℝ)
    (values : Matrix ℝ) : Vector ℝ :=
  (List.range valueDim).map (fun j =>
    (List.zipWith (fun w v => w * nthOrZero v j) weights values).sum)

theorem weightedValueSum_shape (valueDim : Nat) (weights : Vector ℝ)
    (values : Matrix ℝ) :
    vectorShape valueDim (weightedValueSum valueDim weights values) := by
  simp [vectorShape, weightedValueSum]

def exactAttention (headDim valueDim : Nat) (q : Vector ℝ)
    (keys values : Matrix ℝ) : Vector ℝ :=
  weightedValueSum valueDim (attentionWeights headDim q keys) values

theorem exactAttention_shape (headDim valueDim : Nat) (q : Vector ℝ)
    (keys values : Matrix ℝ) :
    vectorShape valueDim (exactAttention headDim valueDim q keys values) := by
  exact weightedValueSum_shape valueDim _ _

theorem mapZeroUpt (n : Nat) :
    (List.range n).map (fun _ => (0 : ℝ)) = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, ih]
      simp only [List.map_cons, List.map_nil]
      rw [← List.replicate_one (a := (0 : ℝ)), ← List.replicate_add]

theorem weightedValueSum_emptyWeights (valueDim : Nat) (values : Matrix ℝ) :
    weightedValueSum valueDim [] values = List.replicate valueDim 0 := by
  simp [weightedValueSum, mapZeroUpt]

@[simp] theorem exactAttention_emptyKeys (headDim valueDim : Nat)
    (q : Vector ℝ) (values : Matrix ℝ) :
    exactAttention headDim valueDim q [] values = List.replicate valueDim 0 := by
  simp [exactAttention, attentionWeights, weightedValueSum_emptyWeights]

def exactCausalAttention (headDim valueDim : Nat)
    (Q K V : α → Vector ℝ) : List α → Matrix ℝ :=
  causalAttention Q K V (exactAttention headDim valueDim)

theorem exactCausalAttentionFrom_shape (headDim valueDim : Nat)
    (Q K V : α → Vector ℝ) (pref xs : List α) :
    matrixShape xs.length valueDim
      (causalAttentionFrom Q K V (exactAttention headDim valueDim) pref xs) := by
  induction xs generalizing pref with
  | nil => simp [matrixShape, causalAttentionFrom]
  | cons x xs ih =>
      have hhead :
          (exactAttention headDim valueDim (Q x)
            (List.map K (pref ++ [x])) (List.map V (pref ++ [x]))).length =
            valueDim := by
        exact exactAttention_shape _ _ _ _ _
      have htail := ih (pref := pref ++ [x])
      refine ⟨by simp [causalAttentionFrom, length_causalAttentionFrom], ?_⟩
      intro row hrow
      simp only [causalAttentionFrom, List.mem_cons] at hrow
      rcases hrow with rfl | hrow
      · exact hhead
      · exact htail.2 row hrow

theorem exactCausalAttention_shape (headDim valueDim : Nat)
    (Q K V : α → Vector ℝ) (xs : List α) :
    matrixShape xs.length valueDim
      (exactCausalAttention headDim valueDim Q K V xs) := by
  exact exactCausalAttentionFrom_shape headDim valueDim Q K V [] xs

theorem exactCausalAttention_independence (headDim valueDim : Nat)
    (Q K V : α → Vector ℝ) {i : Nat} {xs ys : List α}
    (hiₓ : i < xs.length) (hiᵧ : i < ys.length)
    (hprefix : xs.take (i + 1) = ys.take (i + 1)) :
    (exactCausalAttention headDim valueDim Q K V xs)[i]? =
      (exactCausalAttention headDim valueDim Q K V ys)[i]? := by
  exact causalAttention_independence Q K V (exactAttention headDim valueDim)
    hiₓ hiᵧ hprefix

def exactCachedAttention (headDim valueDim : Nat)
    (Q K V : α → Vector ℝ) : List α → Matrix ℝ :=
  cachedAttention Q K V (exactAttention headDim valueDim)

theorem exactCachedAttention_eq_full (headDim valueDim : Nat)
    (Q K V : α → Vector ℝ) (xs : List α) :
    exactCachedAttention headDim valueDim Q K V xs =
      exactCausalAttention headDim valueDim Q K V xs := by
  exact cachedAttention_eq_causalAttention Q K V (exactAttention headDim valueDim) xs

end
end DecoderTransformer
