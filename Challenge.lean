import Mathlib.Data.List.Basic

/-!
# Palomar challenge surface

This file intentionally contains only the auditable statement surface.  The
definitions are repeated here so that Palomar can compare them with the
proved development imported by `Solution.lean` without trusting project
implementation modules.
-/

namespace DecoderTransformer

def prefixEq (n : Nat) (xs ys : List α) : Prop :=
  xs.take n = ys.take n

def causal (F : List α → List β) : Prop :=
  ∀ n xs ys, prefixEq n xs ys → prefixEq n (F xs) (F ys)

def causalAttentionFrom (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (pref : List α) : List α → List o
  | [] => []
  | y :: ys =>
      A (Q y) (List.map K (pref ++ [y])) (List.map V (pref ++ [y])) ::
        causalAttentionFrom Q K V A (pref ++ [y]) ys

def causalAttention (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) : List α → List o :=
  causalAttentionFrom Q K V A []

structure KVCache (k v : Type*) where
  keys : List k
  values : List v

def emptyCache : KVCache k v := ⟨[], []⟩

def cacheOf (K : α → k) (V : α → v) (xs : List α) : KVCache k v :=
  ⟨xs.map K, xs.map V⟩

def cacheMatches (K : α → k) (V : α → v) (xs : List α) (C : KVCache k v) : Prop :=
  C = cacheOf K V xs

def cachedStep (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (C : KVCache k v) (token : α) :
    KVCache k v × o :=
  let ks := C.keys ++ [K token]
  let vs := C.values ++ [V token]
  (⟨ks, vs⟩, A (Q token) ks vs)

def cachedRun (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) : KVCache k v → List α → KVCache k v × List o
  | C, [] => (C, [])
  | C, token :: xs =>
      let (C', y) := cachedStep Q K V A C token
      let (C'', ys) := cachedRun Q K V A C' xs
      (C'', y :: ys)

def cachedAttention (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (xs : List α) : List o :=
  (cachedRun Q K V A (emptyCache) xs).2

/-! The generic causal and cache-refinement results. -/

lemma causalAttentionFrom_take (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (pref : List α) (n : Nat) (xs : List α) :
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

lemma cachedRun_refinesFull (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) {pref : List α} {C : KVCache k v}
    (xs : List α) (hC : cacheMatches K V pref C) :
    cachedRun Q K V A C xs =
      (cacheOf K V (pref ++ xs),
        causalAttentionFrom Q K V A pref xs) := by
  induction xs generalizing pref C with
  | nil =>
      subst C
      simp [cachedRun, causalAttentionFrom, cacheOf]
  | cons token xs ih =>
      have hC' : C = cacheOf K V pref := hC
      subst C
      have hstep :
          cachedStep Q K V A (cacheOf K V pref) token =
            (cacheOf K V (pref ++ [token]),
              A (Q token) (List.map K (pref ++ [token]))
                (List.map V (pref ++ [token]))) := by
        simp [cachedStep, cacheOf, List.map_append]
      have hmatch : cacheMatches K V (pref ++ [token])
          (cacheOf K V (pref ++ [token])) := by
        rfl
      have htail := ih (pref := pref ++ [token])
        (C := cacheOf K V (pref ++ [token])) hmatch
      simp only [cachedRun, hstep, htail, causalAttentionFrom]
      simp [List.append_assoc]

theorem causalAttention_is_causal (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) :
    causal (causalAttention Q K V A) := by
  intro n xs ys hxy
  simp only [prefixEq] at hxy ⊢
  rw [show (causalAttention Q K V A xs).take n =
      causalAttention Q K V A (xs.take n) by
        simpa [causalAttention] using
          causalAttentionFrom_take Q K V A [] n xs,
    show (causalAttention Q K V A ys).take n =
      causalAttention Q K V A (ys.take n) by
        simpa [causalAttention] using
          causalAttentionFrom_take Q K V A [] n ys,
    hxy]

theorem cachedAttention_eq_causalAttention (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (xs : List α) :
    cachedAttention Q K V A xs = causalAttention Q K V A xs := by
  have h := cachedRun_refinesFull Q K V A (xs := xs)
      (pref := []) (C := emptyCache) (by rfl)
  simpa [cachedAttention, causalAttention] using congrArg Prod.snd h

theorem finalCache_eq_fullProjections (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (xs : List α) :
    (cachedRun Q K V A emptyCache xs).1 = cacheOf K V xs := by
  have h := cachedRun_refinesFull Q K V A (xs := xs)
      (pref := []) (C := emptyCache) (by rfl)
  simpa using congrArg Prod.fst h

end DecoderTransformer
