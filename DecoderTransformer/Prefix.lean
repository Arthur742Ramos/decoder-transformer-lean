import Mathlib.Data.List.Basic

namespace DecoderTransformer

/-!
# Prefix-local sequence operators

The first translation unit isolates causality from tensor arithmetic.  A
sequence operator is causal when equal input prefixes produce equal output
prefixes of the same length.  This is the structural property used by the
cached/full refinement theorem below.
-/

def prefixEq (n : Nat) (xs ys : List α) : Prop :=
  xs.take n = ys.take n

def causal (F : List α → List β) : Prop :=
  ∀ n xs ys, prefixEq n xs ys → prefixEq n (F xs) (F ys)

theorem prefixEq_refl (n : Nat) (xs : List α) : prefixEq n xs xs := by
  simp [prefixEq]

theorem prefixEq_sym {n : Nat} {xs ys : List α} :
    prefixEq n xs ys → prefixEq n ys xs := by
  intro h
  exact h.symm

theorem prefixEq_trans {n : Nat} {xs ys zs : List α} :
    prefixEq n xs ys → prefixEq n ys zs → prefixEq n xs zs := by
  intro h₁ h₂
  exact h₁.trans h₂

theorem prefixEq_mono {m n : Nat} {xs ys : List α} (h : prefixEq n xs ys)
    (hmn : m ≤ n) : prefixEq m xs ys := by
  simp only [prefixEq] at h ⊢
  rw [show xs.take m = (xs.take n).take m by simp [List.take_take, Nat.min_eq_left hmn]]
  rw [h]
  simp [List.take_take, Nat.min_eq_left hmn]

theorem causal_id : causal (id : List α → List α) := by
  intro n xs ys h
  exact h

theorem causal_map (f : α → β) : causal (List.map f) := by
  intro n xs ys h
  simp only [prefixEq] at h ⊢
  simpa using congrArg (List.map f) h

theorem causal_comp {F : List α → List β} {G : List β → List γ}
    (hF : causal F) (hG : causal G) : causal (G ∘ F) := by
  intro n xs ys hxy
  exact hG n (F xs) (F ys) (hF n xs ys hxy)

def applyBlocks : List (List α → List α) → List α → List α
  | [], xs => xs
  | F :: Fs, xs => applyBlocks Fs (F xs)

theorem causal_applyBlocks {Fs : List (List α → List α)}
    (hFs : ∀ F ∈ Fs, causal F) : causal (applyBlocks Fs) := by
  induction Fs with
  | nil => exact causal_id
  | cons F Fs ih =>
      have hF : causal F := hFs F (by simp)
      have htail : ∀ G ∈ Fs, causal G := by
        intro G hG
        exact hFs G (by simp [hG])
      have hrest : causal (applyBlocks Fs) := ih htail
      intro n xs ys hxy
      exact hrest n (F xs) (F ys) (hF n xs ys hxy)

theorem causalI {F : List α → List β}
    (hF : ∀ n xs ys, xs.take n = ys.take n →
      (F xs).take n = (F ys).take n) : causal F := by
  intro n xs ys hxy
  exact hF n xs ys hxy

theorem causalD {F : List α → List β} {n : Nat}
    {xs ys : List α} (hF : causal F) (hxy : xs.take n = ys.take n) :
    (F xs).take n = (F ys).take n := by
  exact hF n xs ys hxy

end DecoderTransformer
