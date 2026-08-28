import DecoderTransformer.Prefix

namespace DecoderTransformer

/-!
# Parametric causal attention

Queries, keys, values, and the attention aggregator remain abstract.  The
theorems therefore cover exact attention independently of a scalar field,
softmax implementation, number of heads, or tensor representation.
-/

def causalAttentionFrom (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (pref : List x) : List x → List o
  | [] => []
  | y :: ys =>
      A (Q y) (List.map K (pref ++ [y])) (List.map V (pref ++ [y])) ::
        causalAttentionFrom Q K V A (pref ++ [y]) ys

def causalAttention (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) : List x → List o :=
  causalAttentionFrom Q K V A []

theorem length_causalAttentionFrom (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (pref xs) :
    (causalAttentionFrom Q K V A pref xs).length = xs.length := by
  induction xs generalizing pref with
  | nil => simp [causalAttentionFrom]
  | cons y ys ih => simp [causalAttentionFrom, ih]

theorem length_causalAttention (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (xs) :
    (causalAttention Q K V A xs).length = xs.length := by
  exact length_causalAttentionFrom Q K V A [] xs

theorem causalAttentionFrom_append (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (pref xs ys) :
    causalAttentionFrom Q K V A pref (xs ++ ys) =
      causalAttentionFrom Q K V A pref xs ++
        causalAttentionFrom Q K V A (pref ++ xs) ys := by
  induction xs generalizing pref ys with
  | nil => simp [causalAttentionFrom]
  | cons y ys ih =>
      simp only [List.cons_append, causalAttentionFrom]
      rw [ih (pref := pref ++ [y]) (ys := ys)]
      simp [List.append_assoc]

theorem causalAttention_append (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (xs ys) :
    causalAttention Q K V A (xs ++ ys) =
      causalAttention Q K V A xs ++ causalAttentionFrom Q K V A xs ys := by
  exact causalAttentionFrom_append Q K V A [] xs ys

theorem causalAttentionFrom_take (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (pref : List x) (n : Nat) (xs : List x) :
    (causalAttentionFrom Q K V A pref xs).take n =
      causalAttentionFrom Q K V A pref (xs.take n) := by
  induction xs generalizing pref n with
  | nil => simp [causalAttentionFrom]
  | cons y ys ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.take_succ_cons, causalAttentionFrom]
          rw [ih (pref := pref ++ [y]) (n := n)]

theorem causalAttention_take (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (n : Nat) (xs : List x) :
    (causalAttention Q K V A xs).take n =
      causalAttention Q K V A (xs.take n) := by
  simpa [causalAttention] using
    (causalAttentionFrom_take Q K V A [] n xs)

theorem causalAttention_is_causal (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) :
    causal (causalAttention Q K V A) := by
  intro n xs ys hxy
  simp only [prefixEq] at hxy ⊢
  rw [causalAttention_take Q K V A n xs,
    causalAttention_take Q K V A n ys, hxy]

theorem causalAttention_independence (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) {i : Nat} {xs ys : List x}
    (hiₓ : i < xs.length) (hiᵧ : i < ys.length)
    (hprefix : xs.take (i + 1) = ys.take (i + 1)) :
    (causalAttention Q K V A xs)[i]? =
      (causalAttention Q K V A ys)[i]? := by
  have hcausal := causalAttention_is_causal Q K V A (n := i + 1) xs ys
  have hout :
      (causalAttention Q K V A xs).take (i + 1) =
        (causalAttention Q K V A ys).take (i + 1) :=
    hcausal hprefix
  have hxout : (causalAttention Q K V A xs)[i]? =
      ((causalAttention Q K V A xs).take (i + 1))[i]? := by
    simp [hiₓ, length_causalAttention Q K V A]
  have hyout : (causalAttention Q K V A ys)[i]? =
      ((causalAttention Q K V A ys).take (i + 1))[i]? := by
    simp [hiᵧ, length_causalAttention Q K V A]
  rw [hxout, hyout, hout]

end DecoderTransformer
