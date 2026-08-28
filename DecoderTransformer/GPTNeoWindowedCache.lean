import DecoderTransformer.GPTNeoIncremental
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# GPT-Neo sliding-window caches

`gptNeoAttentionContext 0` is global attention.  For a positive window the
context is the final window-sized tail, and the append theorem below is the
key fact that permits a bounded cache to be updated one token at a time.
-/

theorem gptNeoLocalContext_appendTrim (window : Nat) (xs : List α) (x : α) :
    gptNeoLocalContext window
        (gptNeoLocalContext window xs ++ [x]) =
      gptNeoLocalContext window (xs ++ [x]) := by
  by_cases hwindow : window = 0
  · simp [gptNeoLocalContext, hwindow]
  · by_cases hshort : xs.length ≤ window
    · rw [gptNeoLocalContext_short hshort]
    · have hpos : 0 < window := Nat.pos_of_ne_zero hwindow
      have hlt : window < xs.length := Nat.lt_of_not_ge hshort
      have hle : window ≤ xs.length := Nat.le_of_lt hlt
      let n := xs.length - window
      let trimmed := xs.drop n
      have hn : n + 1 ≤ xs.length := by
        dsimp [n]
        omega
      have htrimmed_length : trimmed.length = window := by
        dsimp [trimmed, n]
        rw [List.length_drop]
        omega
      have hleft :
          gptNeoLocalContext window
              (gptNeoLocalContext window xs ++ [x]) = trimmed.drop 1 ++ [x] := by
        have hinner : gptNeoLocalContext window xs = trimmed := by
          simp [gptNeoLocalContext, n, trimmed, Nat.min_eq_left hle]
        rw [hinner]
        unfold gptNeoLocalContext
        have hmin : min window (trimmed ++ [x]).length = window := by
          apply Nat.min_eq_left
          simp [htrimmed_length]
        rw [hmin]
        have hamt : (trimmed ++ [x]).length - window = 1 := by
          simp [htrimmed_length]
        rw [hamt]
        apply List.drop_append_of_le_length
        simp [htrimmed_length]
        omega
      have hright :
          gptNeoLocalContext window (xs ++ [x]) =
            xs.drop (n + 1) ++ [x] := by
        unfold gptNeoLocalContext
        have hmin : min window (xs ++ [x]).length = window := by
          apply Nat.min_eq_left
          simp
          omega
        rw [hmin]
        have hamt : (xs ++ [x]).length - window = n + 1 := by
          simpa [n] using (Nat.sub_add_comm hle)
        rw [hamt]
        exact List.drop_append_of_le_length hn
      rw [hleft, hright]
      simp [trimmed, List.drop_drop]

theorem gptNeoAttentionContext_appendTrim (window : Nat) (xs : List α) (x : α) :
    gptNeoAttentionContext window
        (gptNeoAttentionContext window xs ++ [x]) =
      gptNeoAttentionContext window (xs ++ [x]) := by
  by_cases hwindow : window = 0
  · simp [gptNeoAttentionContext, hwindow]
  · simp [gptNeoAttentionContext, hwindow,
      gptNeoLocalContext_appendTrim]

theorem gptNeoAttentionContext_idempotent (window : Nat) (xs : List α) :
    gptNeoAttentionContext window
        (gptNeoAttentionContext window xs) =
      gptNeoAttentionContext window xs := by
  by_cases hwindow : window = 0
  · simp [gptNeoAttentionContext, hwindow]
  · by_cases hshort : xs.length ≤ window
    · simp [gptNeoAttentionContext, hwindow, gptNeoLocalContext_short hshort]
    · have hle : window ≤ xs.length := Nat.le_of_not_ge hshort
      have htrim :
          (gptNeoLocalContext window xs).length = window := by
        simp [gptNeoLocalContext, Nat.min_eq_left hle]
        omega
      simp only [gptNeoAttentionContext, hwindow, ↓reduceIte]
      rw [gptNeoLocalContext_short htrim.le]

@[simp] theorem gptNeoAttentionContext_empty (window : Nat) :
    gptNeoAttentionContext window ([] : List α) = [] := by
  by_cases hwindow : window = 0 <;>
    simp [gptNeoAttentionContext, gptNeoLocalContext, hwindow]

def gptNeoTrimCache (window : Nat) (cache : KVCache k v) : KVCache k v :=
  ⟨gptNeoAttentionContext window cache.keys,
   gptNeoAttentionContext window cache.values⟩

@[simp] theorem gptNeoTrimCache_keys (window : Nat) (cache : KVCache k v) :
    (gptNeoTrimCache window cache).keys =
      gptNeoAttentionContext window cache.keys := by
  rfl

@[simp] theorem gptNeoTrimCache_values (window : Nat) (cache : KVCache k v) :
    (gptNeoTrimCache window cache).values =
      gptNeoAttentionContext window cache.values := by
  rfl

theorem gptNeoTrimCache_of (window : Nat) (K : α → k) (V : α → v)
    (xs : List α) :
    gptNeoTrimCache window (cacheOf K V xs) =
      cacheOf K V (gptNeoAttentionContext window xs) := by
  simp [gptNeoTrimCache, cacheOf, gptNeoAttentionContext_map]

def gptNeoBoundedCacheMatches (p : GPTNeoLayerParameters) (pref : Matrix ℝ)
    (cache : KVCache (Vector ℝ) (Vector ℝ)) : Prop :=
  cache = gptNeoTrimCache p.attentionWindow
    (cacheOf (gptNeoNormalizedInput p) (gptNeoNormalizedInput p) pref)

def gptNeoBoundedCacheExtend (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : KVCache (Vector ℝ) (Vector ℝ)) : KVCache (Vector ℝ) (Vector ℝ) :=
  gptNeoTrimCache p.attentionWindow
    ⟨cache.keys ++ [gptNeoNormalizedInput p x],
     cache.values ++ [gptNeoNormalizedInput p x]⟩

theorem gptNeoBoundedCacheExtendMatches
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hcache : gptNeoBoundedCacheMatches p pref cache) :
    gptNeoBoundedCacheMatches p (pref ++ [x])
      (gptNeoBoundedCacheExtend p x cache) := by
  subst cache
  unfold gptNeoBoundedCacheMatches gptNeoBoundedCacheExtend
  apply congrArg₂ KVCache.mk <;>
    simp [gptNeoTrimCache, cacheOf, gptNeoAttentionContext_map]
  all_goals
    rw [← gptNeoAttentionContext_map]
    rw [gptNeoAttentionContext_appendTrim]

def gptNeoBoundedCachedAttention (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : KVCache (Vector ℝ) (Vector ℝ)) : Vector ℝ :=
  gptNeoAttentionAggregator p x
    (gptNeoBoundedCacheExtend p x cache).keys
    (gptNeoBoundedCacheExtend p x cache).values

theorem gptNeoBoundedCachedAttention_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hcache : gptNeoBoundedCacheMatches p pref cache) :
    gptNeoBoundedCachedAttention p x cache =
      gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
        p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
        ((pref ++ [x]).map (gptNeoNormalizedInput p)) := by
  have hext := gptNeoBoundedCacheExtendMatches (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  have hcache' : gptNeoBoundedCacheExtend p x cache =
      gptNeoTrimCache p.attentionWindow
        (cacheOf (gptNeoNormalizedInput p) (gptNeoNormalizedInput p)
          (pref ++ [x])) := by
    simpa [gptNeoBoundedCacheMatches, gptNeoBoundedCacheExtend] using hext
  unfold gptNeoBoundedCachedAttention
  rw [hcache']
  simp [gptNeoTrimCache, cacheOf, gptNeoAttentionAggregator,
    gptNeoWindowedMultiHeadAtPrefix, gptNeoWindowedHeadAttention,
    gptNeoAttentionContext_idempotent]

def gptNeoBoundedCachedBlockStep (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : KVCache (Vector ℝ) (Vector ℝ)) :
    Vector ℝ × KVCache (Vector ℝ) (Vector ℝ) :=
  (gptNeoBlockFromAttention p x (gptNeoBoundedCachedAttention p x cache),
   gptNeoBoundedCacheExtend p x cache)

theorem gptNeoBoundedCachedBlockStep_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoBoundedCacheMatches p pref cache) :
    (gptNeoBoundedCachedBlockStep p x cache).1 =
        gptNeoBlockAtPrefix p x (pref ++ [x]) ∧
    gptNeoBoundedCacheMatches p (pref ++ [x])
      (gptNeoBoundedCachedBlockStep p x cache).2 := by
  have hatt := gptNeoBoundedCachedAttention_correct (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  have hcache' := gptNeoBoundedCacheExtendMatches (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  constructor
  · simpa [gptNeoBoundedCachedBlockStep,
      gptNeoBlockAtPrefix_fromAttention] using
      congrArg (gptNeoBlockFromAttention p x) hatt
  · simpa [gptNeoBoundedCachedBlockStep] using hcache'

theorem gptNeoBoundedCachedBlockStep_output
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoBoundedCacheMatches p pref cache) :
    (gptNeoBoundedCachedBlockStep p x cache).1 =
      gptNeoBlockAtPrefix p x (pref ++ [x]) :=
  (gptNeoBoundedCachedBlockStep_correct hvalid hcache).1

theorem gptNeoBoundedCachedBlockStep_cache
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoBoundedCacheMatches p pref cache) :
    gptNeoBoundedCacheMatches p (pref ++ [x])
      (gptNeoBoundedCachedBlockStep p x cache).2 :=
  (gptNeoBoundedCachedBlockStep_correct hvalid hcache).2

/-! Bounded projected caches. -/

def gptNeoProjectedBoundedHeadCacheOf (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) (h : Nat) : GPTNeoProjectedHeadCache :=
  cacheOf (gptNeoProjectedKey p h) (gptNeoProjectedValue p h)
    (gptNeoAttentionContext p.attentionWindow
      (pref.map (gptNeoNormalizedInput p)))

def gptNeoProjectedBoundedCacheOf (p : GPTNeoLayerParameters) (pref : Matrix ℝ) :
    GPTNeoProjectedLayerCache :=
  (List.range p.headCount).map (gptNeoProjectedBoundedHeadCacheOf p pref)

def gptNeoProjectedBoundedEmptyCache (p : GPTNeoLayerParameters) :
    GPTNeoProjectedLayerCache :=
  gptNeoProjectedBoundedCacheOf p []

def gptNeoProjectedBoundedCacheMatches (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) (cache : GPTNeoProjectedLayerCache) : Prop :=
  cache = gptNeoProjectedBoundedCacheOf p pref

theorem gptNeoProjectedBoundedEmptyCache_matches (p : GPTNeoLayerParameters) :
    gptNeoProjectedBoundedCacheMatches p []
      (gptNeoProjectedBoundedEmptyCache p) := by
  rfl

def gptNeoProjectedBoundedHeadCacheAppend (p : GPTNeoLayerParameters) (h : Nat)
    (x : Vector ℝ) (cache : GPTNeoProjectedHeadCache) :
    GPTNeoProjectedHeadCache :=
  gptNeoTrimCache p.attentionWindow
    ⟨cache.keys ++ [gptNeoProjectedKey p h (gptNeoNormalizedInput p x)],
     cache.values ++ [gptNeoProjectedValue p h (gptNeoNormalizedInput p x)]⟩

def gptNeoProjectedBoundedCacheExtendOnHeads (p : GPTNeoLayerParameters)
    (x : Vector ℝ) :
    List Nat → GPTNeoProjectedLayerCache → GPTNeoProjectedLayerCache
  | [], _ => []
  | _, [] => []
  | h :: hs, cache :: caches =>
      gptNeoProjectedBoundedHeadCacheAppend p h x cache ::
        gptNeoProjectedBoundedCacheExtendOnHeads p x hs caches

def gptNeoProjectedBoundedCacheExtend (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : GPTNeoProjectedLayerCache) : GPTNeoProjectedLayerCache :=
  gptNeoProjectedBoundedCacheExtendOnHeads p x (List.range p.headCount) cache

theorem gptNeoProjectedBoundedHeadCacheAppendOf
    (p : GPTNeoLayerParameters) (pref : Matrix ℝ) (h : Nat) (x : Vector ℝ) :
    gptNeoProjectedBoundedHeadCacheAppend p h x
        (gptNeoProjectedBoundedHeadCacheOf p pref h) =
      gptNeoProjectedBoundedHeadCacheOf p (pref ++ [x]) h := by
  have happend (f : Vector ℝ → Vector ℝ) :
      gptNeoAttentionContext p.attentionWindow
          ((gptNeoAttentionContext p.attentionWindow
              (pref.map (gptNeoNormalizedInput p))).map f ++
            [f (gptNeoNormalizedInput p x)]) =
        (gptNeoAttentionContext p.attentionWindow
            ((pref ++ [x]).map (gptNeoNormalizedInput p))).map f := by
    rw [← gptNeoAttentionContext_map p.attentionWindow f
      (pref.map (gptNeoNormalizedInput p))]
    rw [gptNeoAttentionContext_appendTrim]
    conv_rhs =>
      rw [← gptNeoAttentionContext_map p.attentionWindow f
        ((pref ++ [x]).map (gptNeoNormalizedInput p))]
    simp [List.map_append, Function.comp_def]
  apply congrArg₂ KVCache.mk <;>
    simp [gptNeoProjectedBoundedHeadCacheAppend,
    gptNeoProjectedBoundedHeadCacheOf, gptNeoTrimCache, cacheOf,
    gptNeoProjectedKey, gptNeoProjectedValue,
    gptNeoAttentionContext_map]
  · simpa [Function.comp_def, gptNeoProjectedKey,
      gptNeoAttentionContext_map] using
      happend (gptNeoProjectedKey p h)
  · simpa [Function.comp_def, gptNeoProjectedValue,
      gptNeoAttentionContext_map] using
      happend (gptNeoProjectedValue p h)

theorem gptNeoProjectedBoundedCacheExtendOnHeadsMap
    (p : GPTNeoLayerParameters) (pref : Matrix ℝ) (x : Vector ℝ) (hs : List Nat) :
    gptNeoProjectedBoundedCacheExtendOnHeads p x hs
        (hs.map (gptNeoProjectedBoundedHeadCacheOf p pref)) =
      hs.map (gptNeoProjectedBoundedHeadCacheOf p (pref ++ [x])) := by
  induction hs with
  | nil => simp [gptNeoProjectedBoundedCacheExtendOnHeads]
  | cons h hs ih =>
      simp [gptNeoProjectedBoundedCacheExtendOnHeads,
        gptNeoProjectedBoundedHeadCacheAppendOf, ih]

theorem gptNeoProjectedBoundedCacheExtendOf
    (p : GPTNeoLayerParameters) (pref : Matrix ℝ) (x : Vector ℝ) :
    gptNeoProjectedBoundedCacheExtend p x
        (gptNeoProjectedBoundedCacheOf p pref) =
      gptNeoProjectedBoundedCacheOf p (pref ++ [x]) := by
  simp [gptNeoProjectedBoundedCacheExtend,
    gptNeoProjectedBoundedCacheOf,
    gptNeoProjectedBoundedCacheExtendOnHeadsMap]

theorem gptNeoProjectedBoundedCacheExtendMatches
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hcache : gptNeoProjectedBoundedCacheMatches p pref cache) :
    gptNeoProjectedBoundedCacheMatches p (pref ++ [x])
      (gptNeoProjectedBoundedCacheExtend p x cache) := by
  subst cache
  simp [gptNeoProjectedBoundedCacheMatches,
    gptNeoProjectedBoundedCacheExtendOf]

theorem gptNeoProjectedAttentionHeadsBounded
    (p : GPTNeoLayerParameters) (pref : Matrix ℝ) (x : Vector ℝ) (hs : List Nat) :
    gptNeoProjectedAttentionHeads p x hs
        (hs.map (gptNeoProjectedBoundedHeadCacheOf p pref)) =
      hs.map (fun h =>
        exactAttention p.headDim p.headDim (gptNeoProjectedQuery p h x)
          (gptNeoAttentionContext p.attentionWindow
            ((pref.map (gptNeoNormalizedInput p)).map
              (gptNeoProjectedKey p h)))
          (gptNeoAttentionContext p.attentionWindow
            ((pref.map (gptNeoNormalizedInput p)).map
              (gptNeoProjectedValue p h)))) := by
  induction hs with
  | nil => simp [gptNeoProjectedAttentionHeads]
  | cons h hs ih =>
      simp [gptNeoProjectedAttentionHeads,
        gptNeoProjectedBoundedHeadCacheOf, cacheOf,
        gptNeoProjectedQuery, gptNeoProjectedKey,
        gptNeoProjectedValue, Function.comp_def,
        gptNeoAttentionContext_map, gptNeoAttentionContext_idempotent, ih]

theorem gptNeoProjectedAttentionAggregatorBounded
    (p : GPTNeoLayerParameters) (pref : Matrix ℝ) (x : Vector ℝ) :
    gptNeoProjectedAttentionAggregator p x
        (gptNeoProjectedBoundedCacheOf p pref) =
      gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
        p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
        (pref.map (gptNeoNormalizedInput p)) := by
  simp [gptNeoProjectedAttentionAggregator,
    gptNeoProjectedBoundedCacheOf, gptNeoProjectedAttentionHeadsBounded,
    gptNeoWindowedMultiHeadAtPrefix, gptNeoWindowedHeadAttention,
    gptNeoProjectedQuery, gptNeoProjectedKey, gptNeoProjectedValue,
    Function.comp_def, gptNeoAttentionContext_map,
    gptNeoAttentionContext_idempotent]

def gptNeoProjectedBoundedCachedAttention (p : GPTNeoLayerParameters)
    (x : Vector ℝ) (cache : GPTNeoProjectedLayerCache) : Vector ℝ :=
  gptNeoProjectedAttentionAggregator p x
    (gptNeoProjectedBoundedCacheExtend p x cache)

theorem gptNeoProjectedBoundedCachedAttention_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hcache : gptNeoProjectedBoundedCacheMatches p pref cache) :
    gptNeoProjectedBoundedCachedAttention p x cache =
      gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
        p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
        ((pref ++ [x]).map (gptNeoNormalizedInput p)) := by
  subst cache
  simp [gptNeoProjectedBoundedCachedAttention,
    gptNeoProjectedBoundedCacheExtendOf,
    gptNeoProjectedAttentionAggregatorBounded]

def gptNeoProjectedBoundedCachedBlockStep (p : GPTNeoLayerParameters)
    (x : Vector ℝ) (cache : GPTNeoProjectedLayerCache) :
    Vector ℝ × GPTNeoProjectedLayerCache :=
  (gptNeoBlockFromAttention p x
      (gptNeoProjectedBoundedCachedAttention p x cache),
   gptNeoProjectedBoundedCacheExtend p x cache)

theorem gptNeoProjectedBoundedCachedBlockStep_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoProjectedBoundedCacheMatches p pref cache) :
    (gptNeoProjectedBoundedCachedBlockStep p x cache).1 =
        gptNeoBlockAtPrefix p x (pref ++ [x]) ∧
    gptNeoProjectedBoundedCacheMatches p (pref ++ [x])
      (gptNeoProjectedBoundedCachedBlockStep p x cache).2 := by
  have hatt := gptNeoProjectedBoundedCachedAttention_correct
    (p := p) (pref := pref) (cache := cache) (x := x) hcache
  have hcache' := gptNeoProjectedBoundedCacheExtendMatches
    (p := p) (pref := pref) (cache := cache) (x := x) hcache
  constructor
  · simpa [gptNeoProjectedBoundedCachedBlockStep,
      gptNeoBlockAtPrefix_fromAttention] using
      congrArg (gptNeoBlockFromAttention p x) hatt
  · simpa [gptNeoProjectedBoundedCachedBlockStep] using hcache'

theorem gptNeoProjectedBoundedCachedBlockStep_output
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoProjectedBoundedCacheMatches p pref cache) :
    (gptNeoProjectedBoundedCachedBlockStep p x cache).1 =
      gptNeoBlockAtPrefix p x (pref ++ [x]) :=
  (gptNeoProjectedBoundedCachedBlockStep_correct hvalid hcache).1

theorem gptNeoProjectedBoundedCachedBlockStep_cache
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoProjectedBoundedCacheMatches p pref cache) :
    gptNeoProjectedBoundedCacheMatches p (pref ++ [x])
      (gptNeoProjectedBoundedCachedBlockStep p x cache).2 :=
  (gptNeoProjectedBoundedCachedBlockStep_correct hvalid hcache).2

end
end DecoderTransformer
