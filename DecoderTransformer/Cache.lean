import DecoderTransformer.Attention

namespace DecoderTransformer

/-!
# Exact key-value cache refinement

The cache stores the projections of the processed prefix.  A cache step
appends the current key and value, then applies the same abstract aggregator
to the resulting histories.  The main theorem proves equality with the
full-prefix causal attention run.
-/

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

theorem emptyCache_eq_cacheOf (K : α → k) (V : α → v) :
    emptyCache = cacheOf K V [] := by
  rfl

@[simp] theorem empty_cache_is_cache_of (K : α → k) (V : α → v) :
    emptyCache = cacheOf K V [] :=
  emptyCache_eq_cacheOf K V

theorem cachedStep_refinesFull (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) {pref : List α} {C : KVCache k v} {token : α}
    (hC : cacheMatches K V pref C) :
    cachedStep Q K V A C token =
      (cacheOf K V (pref ++ [token]),
        A (Q token) (List.map K (pref ++ [token])) (List.map V (pref ++ [token]))) := by
  subst C
  simp [cachedStep, cacheOf, List.map_append]

theorem cachedRun_refinesFull (Q : α → q) (K : α → k) (V : α → v)
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
      have hstep := cachedStep_refinesFull Q K V A hC (token := token)
      have hmatch : cacheMatches K V (pref ++ [token])
          (cacheOf K V (pref ++ [token])) := by
        rfl
      have htail := ih (pref := pref ++ [token])
        (C := cacheOf K V (pref ++ [token])) hmatch
      simp only [cachedRun, hstep, htail, causalAttentionFrom]
      simp [List.append_assoc]

theorem cachedAttention_eq_causalAttention (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (xs : List α) :
    cachedAttention Q K V A xs = causalAttention Q K V A xs := by
  have h := cachedRun_refinesFull Q K V A (xs := xs)
      (pref := []) (C := emptyCache) (by rfl)
  simpa [cachedAttention, causalAttention] using congrArg Prod.snd h

theorem cached_attention_eq_full_attention (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (xs : List α) :
    cachedAttention Q K V A xs = causalAttention Q K V A xs :=
  cachedAttention_eq_causalAttention Q K V A xs

theorem finalCache_eq_fullProjections (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) (xs : List α) :
    (cachedRun Q K V A emptyCache xs).1 = cacheOf K V xs := by
  have h := cachedRun_refinesFull Q K V A (xs := xs)
      (pref := []) (C := emptyCache) (by rfl)
  simpa using congrArg Prod.fst h

theorem cachedAttention_is_causal (Q : α → q) (K : α → k) (V : α → v)
    (A : q → List k → List v → o) :
    causal (cachedAttention Q K V A) := by
  rw [show cachedAttention Q K V A = causalAttention Q K V A from by
    funext xs
    exact cachedAttention_eq_causalAttention Q K V A xs]
  exact causalAttention_is_causal Q K V A

end DecoderTransformer
