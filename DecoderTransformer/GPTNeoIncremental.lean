import DecoderTransformer.GPTNeoComponents
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# GPT-Neo exact cache refinement

The first cache in this file is a semantic bridge: it stores the normalized
input vectors used by LayerNorm.  The projected cache below is the
implementation boundary used by the stack, and appends only the newly
projected key and value for each head.
-/

def gptNeoNormalizedInput (p : GPTNeoLayerParameters) (x : Vector ℝ) : Vector ℝ :=
  gptNeoLayerNorm p.normEpsilon p.ln1Gain p.ln1Bias x

def gptNeoCacheMatches (p : GPTNeoLayerParameters) (pref : Matrix ℝ)
    (cache : KVCache (Vector ℝ) (Vector ℝ)) : Prop :=
  cacheMatches (gptNeoNormalizedInput p) (gptNeoNormalizedInput p) pref cache

def gptNeoAttentionAggregator (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (keys values : Matrix ℝ) : Vector ℝ :=
  affineProject p.modelDim p.outputWeights p.outputBias
    ((List.range p.headCount).map (fun h =>
      exactAttention p.headDim p.headDim
        (linearProject p.headDim (tensorMatrixAt p.queryWeights h)
          (gptNeoNormalizedInput p x))
        ((gptNeoAttentionContext p.attentionWindow keys).map
          (linearProject p.headDim (tensorMatrixAt p.keyWeights h)))
        ((gptNeoAttentionContext p.attentionWindow values).map
          (linearProject p.headDim (tensorMatrixAt p.valueWeights h))))).flatten

theorem gptNeoLocalContext_map (window : Nat) (f : α → β) (xs : List α) :
    gptNeoLocalContext window (xs.map f) =
      (gptNeoLocalContext window xs).map f := by
  simp [gptNeoLocalContext]

theorem gptNeoAttentionContext_map (window : Nat) (f : α → β) (xs : List α) :
    gptNeoAttentionContext window (xs.map f) =
      (gptNeoAttentionContext window xs).map f := by
  by_cases hwindow : window = 0
  · simp [gptNeoAttentionContext, hwindow]
  · simp [gptNeoAttentionContext, hwindow, gptNeoLocalContext_map]

theorem gptNeoAttentionAggregator_full (p : GPTNeoLayerParameters)
    (x : Vector ℝ) (pref : Matrix ℝ) :
    gptNeoAttentionAggregator p x
        (pref.map (gptNeoNormalizedInput p))
        (pref.map (gptNeoNormalizedInput p)) =
      gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
        p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
        (pref.map (gptNeoNormalizedInput p)) := by
  simp [gptNeoAttentionAggregator, gptNeoWindowedMultiHeadAtPrefix,
    gptNeoWindowedHeadAttention]

theorem gptNeoNormalizedPrefix_asInput (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) :
    gptNeoNormalizedPrefix p pref = pref.map (gptNeoNormalizedInput p) := by
  rfl

def gptNeoCachedAttention (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : KVCache (Vector ℝ) (Vector ℝ)) : Vector ℝ :=
  (cachedStep id (gptNeoNormalizedInput p) (gptNeoNormalizedInput p)
    (gptNeoAttentionAggregator p) cache x).2

theorem gptNeoCachedAttention_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hcache : gptNeoCacheMatches p pref cache) :
    gptNeoCachedAttention p x cache =
      gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
        p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
        ((pref ++ [x]).map (gptNeoNormalizedInput p)) := by
  have hcache' : cacheMatches (gptNeoNormalizedInput p)
      (gptNeoNormalizedInput p) pref cache := hcache
  have hstep := cachedStep_refinesFull id (gptNeoNormalizedInput p)
    (gptNeoNormalizedInput p) (gptNeoAttentionAggregator p)
    (pref := pref) (C := cache) (token := x) hcache'
  unfold gptNeoCachedAttention
  rw [hstep]
  exact gptNeoAttentionAggregator_full p x (pref ++ [x])

theorem gptNeoCachedAttention_cacheMatches
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hcache : gptNeoCacheMatches p pref cache) :
    gptNeoCacheMatches p (pref ++ [x])
      (cachedStep id (gptNeoNormalizedInput p) (gptNeoNormalizedInput p)
        (gptNeoAttentionAggregator p) cache x).1 := by
  have hcache' : cacheMatches (gptNeoNormalizedInput p)
      (gptNeoNormalizedInput p) pref cache := hcache
  have hstep := cachedStep_refinesFull id (gptNeoNormalizedInput p)
    (gptNeoNormalizedInput p) (gptNeoAttentionAggregator p)
    (pref := pref) (C := cache) (token := x) hcache'
  have hfst := congrArg Prod.fst hstep
  simpa [gptNeoCacheMatches, cacheMatches] using hfst

def gptNeoBlockFromAttention (p : GPTNeoLayerParameters) (x attention : Vector ℝ) :
    Vector ℝ :=
  let attentionResidual := vectorAdd x attention
  let normalizedMlp :=
    gptNeoLayerNorm p.normEpsilon p.ln2Gain p.ln2Bias attentionResidual
  let mlp := gptNeoMlp p.modelDim p.hiddenDim p.fcWeights p.fcBias
    p.projectionWeights p.projectionBias normalizedMlp
  vectorAdd attentionResidual mlp

theorem gptNeoBlockAtPrefix_fromAttention (p : GPTNeoLayerParameters)
    (x : Vector ℝ) (pref : Matrix ℝ) :
    gptNeoBlockAtPrefix p x pref =
      gptNeoBlockFromAttention p x
        (gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
          p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
          p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
          (pref.map (gptNeoNormalizedInput p))) := by
  rfl

def gptNeoCachedBlockStep (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : KVCache (Vector ℝ) (Vector ℝ)) :
    Vector ℝ × KVCache (Vector ℝ) (Vector ℝ) :=
  let step := cachedStep id (gptNeoNormalizedInput p) (gptNeoNormalizedInput p)
    (gptNeoAttentionAggregator p) cache x
  (gptNeoBlockFromAttention p x step.2, step.1)

theorem gptNeoCachedBlockStep_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p) (hcache : gptNeoCacheMatches p pref cache) :
    (gptNeoCachedBlockStep p x cache).1 =
        gptNeoBlockAtPrefix p x (pref ++ [x]) ∧
    gptNeoCacheMatches p (pref ++ [x])
      (gptNeoCachedBlockStep p x cache).2 := by
  have hatt := gptNeoCachedAttention_correct (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  have hcache' := gptNeoCachedAttention_cacheMatches (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  constructor
  · simpa [gptNeoCachedBlockStep, gptNeoCachedAttention,
      gptNeoBlockAtPrefix_fromAttention] using
      congrArg (gptNeoBlockFromAttention p x) hatt
  · simpa [gptNeoCachedBlockStep] using hcache'

theorem gptNeoCachedBlockStep_output
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p) (hcache : gptNeoCacheMatches p pref cache) :
    (gptNeoCachedBlockStep p x cache).1 =
      gptNeoBlockAtPrefix p x (pref ++ [x]) :=
  (gptNeoCachedBlockStep_correct hvalid hcache).1

theorem gptNeoCachedBlockStep_cache
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p) (hcache : gptNeoCacheMatches p pref cache) :
    gptNeoCacheMatches p (pref ++ [x])
      (gptNeoCachedBlockStep p x cache).2 :=
  (gptNeoCachedBlockStep_correct hvalid hcache).2

theorem gptNeoFullLayer_append (p : GPTNeoLayerParameters) (pref : Matrix ℝ)
    (x : Vector ℝ) :
    gptNeoFullLayer p (pref ++ [x]) =
      gptNeoFullLayer p pref ++
        [gptNeoBlockAtPrefix p x (pref ++ [x])] := by
  have h := causalAttention_append id id id
    (fun x pref _ => gptNeoBlockAtPrefix p x pref) pref [x]
  simpa [gptNeoFullLayer, causalAttentionFrom] using h

theorem gptNeoCachedBlockStep_full
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : KVCache (Vector ℝ) (Vector ℝ)} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p) (hcache : gptNeoCacheMatches p pref cache) :
    gptNeoFullLayer p (pref ++ [x]) =
      gptNeoFullLayer p pref ++
        [(gptNeoCachedBlockStep p x cache).1] := by
  rw [gptNeoFullLayer_append]
  rw [gptNeoCachedBlockStep_output hvalid hcache]

/-! The projected per-head cache used by the GPT-Neo stack. -/

abbrev GPTNeoProjectedHeadCache := KVCache (Vector ℝ) (Vector ℝ)
abbrev GPTNeoProjectedLayerCache := List GPTNeoProjectedHeadCache

def gptNeoProjectedQuery (p : GPTNeoLayerParameters) (h : Nat) (x : Vector ℝ) :
    Vector ℝ :=
  linearProject p.headDim (tensorMatrixAt p.queryWeights h)
    (gptNeoNormalizedInput p x)

def gptNeoProjectedKey (p : GPTNeoLayerParameters) (h : Nat) (x : Vector ℝ) :
    Vector ℝ :=
  linearProject p.headDim (tensorMatrixAt p.keyWeights h) x

def gptNeoProjectedValue (p : GPTNeoLayerParameters) (h : Nat) (x : Vector ℝ) :
    Vector ℝ :=
  linearProject p.headDim (tensorMatrixAt p.valueWeights h) x

def gptNeoProjectedHeadCacheOf (p : GPTNeoLayerParameters) (pref : Matrix ℝ)
    (h : Nat) : GPTNeoProjectedHeadCache :=
  cacheOf (gptNeoProjectedKey p h) (gptNeoProjectedValue p h)
    (pref.map (gptNeoNormalizedInput p))

def gptNeoProjectedCacheOf (p : GPTNeoLayerParameters) (pref : Matrix ℝ) :
    GPTNeoProjectedLayerCache :=
  (List.range p.headCount).map (gptNeoProjectedHeadCacheOf p pref)

def gptNeoProjectedCacheMatches (p : GPTNeoLayerParameters) (pref : Matrix ℝ)
    (cache : GPTNeoProjectedLayerCache) : Prop :=
  cache = gptNeoProjectedCacheOf p pref

def gptNeoProjectedHeadCacheAppend (p : GPTNeoLayerParameters) (h : Nat)
    (x : Vector ℝ) (cache : GPTNeoProjectedHeadCache) : GPTNeoProjectedHeadCache :=
  ⟨cache.keys ++ [gptNeoProjectedKey p h (gptNeoNormalizedInput p x)],
   cache.values ++ [gptNeoProjectedValue p h (gptNeoNormalizedInput p x)]⟩

def gptNeoProjectedCacheExtendOnHeads (p : GPTNeoLayerParameters) (x : Vector ℝ) :
    List Nat → GPTNeoProjectedLayerCache → GPTNeoProjectedLayerCache
  | [], _ => []
  | _, [] => []
  | h :: hs, cache :: caches =>
      gptNeoProjectedHeadCacheAppend p h x cache ::
        gptNeoProjectedCacheExtendOnHeads p x hs caches

def gptNeoProjectedCacheExtend (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : GPTNeoProjectedLayerCache) : GPTNeoProjectedLayerCache :=
  gptNeoProjectedCacheExtendOnHeads p x (List.range p.headCount) cache

theorem gptNeoProjectedHeadCacheAppendOf (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) (h : Nat) (x : Vector ℝ) :
    gptNeoProjectedHeadCacheAppend p h x
        (gptNeoProjectedHeadCacheOf p pref h) =
      gptNeoProjectedHeadCacheOf p (pref ++ [x]) h := by
  simp [gptNeoProjectedHeadCacheAppend, gptNeoProjectedHeadCacheOf,
    gptNeoProjectedKey, gptNeoProjectedValue, cacheOf, List.map_append]

theorem gptNeoProjectedCacheExtendOnHeadsMap (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) (x : Vector ℝ) (hs : List Nat) :
    gptNeoProjectedCacheExtendOnHeads p x hs
        (hs.map (gptNeoProjectedHeadCacheOf p pref)) =
      hs.map (gptNeoProjectedHeadCacheOf p (pref ++ [x])) := by
  induction hs with
  | nil => simp [gptNeoProjectedCacheExtendOnHeads]
  | cons h hs ih =>
      simp [gptNeoProjectedCacheExtendOnHeads,
        gptNeoProjectedHeadCacheAppendOf, ih]

theorem gptNeoProjectedCacheExtendOf (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) (x : Vector ℝ) :
    gptNeoProjectedCacheExtend p x (gptNeoProjectedCacheOf p pref) =
      gptNeoProjectedCacheOf p (pref ++ [x]) := by
  simp [gptNeoProjectedCacheExtend, gptNeoProjectedCacheOf,
    gptNeoProjectedCacheExtendOnHeadsMap]

theorem gptNeoProjectedCacheExtendMatches
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hcache : gptNeoProjectedCacheMatches p pref cache) :
    gptNeoProjectedCacheMatches p (pref ++ [x])
      (gptNeoProjectedCacheExtend p x cache) := by
  subst cache
  simp [gptNeoProjectedCacheMatches, gptNeoProjectedCacheExtendOf]

def gptNeoProjectedAttentionHeads (p : GPTNeoLayerParameters) (x : Vector ℝ) :
    List Nat → GPTNeoProjectedLayerCache → Matrix ℝ
  | [], _ => []
  | _, [] => []
  | h :: hs, cache :: caches =>
      exactAttention p.headDim p.headDim (gptNeoProjectedQuery p h x)
        ((gptNeoAttentionContext p.attentionWindow cache.keys))
        ((gptNeoAttentionContext p.attentionWindow cache.values) ) ::
        gptNeoProjectedAttentionHeads p x hs caches

def gptNeoProjectedAttentionAggregator (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : GPTNeoProjectedLayerCache) : Vector ℝ :=
  affineProject p.modelDim p.outputWeights p.outputBias
    (gptNeoProjectedAttentionHeads p x (List.range p.headCount) cache).flatten

theorem gptNeoProjectedAttentionHeadsOf (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) (x : Vector ℝ) (hs : List Nat) :
    gptNeoProjectedAttentionHeads p x hs
        (hs.map (gptNeoProjectedHeadCacheOf p pref)) =
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
      simp [gptNeoProjectedAttentionHeads, gptNeoProjectedHeadCacheOf,
        gptNeoProjectedQuery, gptNeoProjectedKey, gptNeoProjectedValue,
        cacheOf, ih]

theorem gptNeoProjectedAttentionAggregatorFull (p : GPTNeoLayerParameters)
    (pref : Matrix ℝ) (x : Vector ℝ) :
    gptNeoProjectedAttentionAggregator p x (gptNeoProjectedCacheOf p pref) =
      gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
        p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
        (pref.map (gptNeoNormalizedInput p)) := by
  simp [gptNeoProjectedAttentionAggregator, gptNeoProjectedCacheOf,
    gptNeoProjectedAttentionHeadsOf, gptNeoWindowedMultiHeadAtPrefix,
    gptNeoWindowedHeadAttention, gptNeoProjectedQuery,
    gptNeoProjectedKey, gptNeoProjectedValue, Function.comp_def,
    gptNeoAttentionContext_map]

def gptNeoProjectedCachedAttention (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : GPTNeoProjectedLayerCache) : Vector ℝ :=
  gptNeoProjectedAttentionAggregator p x (gptNeoProjectedCacheExtend p x cache)

theorem gptNeoProjectedCachedAttention_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hcache : gptNeoProjectedCacheMatches p pref cache) :
    gptNeoProjectedCachedAttention p x cache =
      gptNeoWindowedMultiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.attentionWindow p.queryWeights p.keyWeights p.valueWeights
        p.outputWeights p.outputBias (gptNeoNormalizedInput p x)
        ((pref ++ [x]).map (gptNeoNormalizedInput p)) := by
  subst cache
  simp [gptNeoProjectedCachedAttention, gptNeoProjectedCacheExtendOf,
    gptNeoProjectedAttentionAggregatorFull]

def gptNeoProjectedCachedBlockStep (p : GPTNeoLayerParameters) (x : Vector ℝ)
    (cache : GPTNeoProjectedLayerCache) :
    Vector ℝ × GPTNeoProjectedLayerCache :=
  (gptNeoBlockFromAttention p x (gptNeoProjectedCachedAttention p x cache),
   gptNeoProjectedCacheExtend p x cache)

theorem gptNeoProjectedCachedBlockStep_correct
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoProjectedCacheMatches p pref cache) :
    (gptNeoProjectedCachedBlockStep p x cache).1 =
        gptNeoBlockAtPrefix p x (pref ++ [x]) ∧
    gptNeoProjectedCacheMatches p (pref ++ [x])
      (gptNeoProjectedCachedBlockStep p x cache).2 := by
  have hatt := gptNeoProjectedCachedAttention_correct (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  have hcache' := gptNeoProjectedCacheExtendMatches (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  constructor
  · simpa [gptNeoProjectedCachedBlockStep, gptNeoProjectedCachedAttention,
      gptNeoBlockAtPrefix_fromAttention] using
      congrArg (gptNeoBlockFromAttention p x) hatt
  · simpa [gptNeoProjectedCachedBlockStep] using hcache'

theorem gptNeoProjectedCachedBlockStep_output
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoProjectedCacheMatches p pref cache) :
    (gptNeoProjectedCachedBlockStep p x cache).1 =
      gptNeoBlockAtPrefix p x (pref ++ [x]) :=
  (gptNeoProjectedCachedBlockStep_correct hvalid hcache).1

theorem gptNeoProjectedCachedBlockStep_cache
    {p : GPTNeoLayerParameters} {pref : Matrix ℝ}
    {cache : GPTNeoProjectedLayerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoLayer p)
    (hcache : gptNeoProjectedCacheMatches p pref cache) :
    gptNeoProjectedCacheMatches p (pref ++ [x])
      (gptNeoProjectedCachedBlockStep p x cache).2 :=
  (gptNeoProjectedCachedBlockStep_correct hvalid hcache).2

def gptNeoProjectedEmptyCache (p : GPTNeoLayerParameters) :
    GPTNeoProjectedLayerCache :=
  (List.range p.headCount).map (fun _ => emptyCache)

theorem gptNeoProjectedEmptyCache_matches (p : GPTNeoLayerParameters) :
    gptNeoProjectedCacheMatches p [] (gptNeoProjectedEmptyCache p) := by
  have hconst : ∀ n : Nat,
      (List.range n).map (fun _ => (emptyCache : GPTNeoProjectedHeadCache)) =
        List.replicate n emptyCache := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [ih]
  unfold gptNeoProjectedCacheMatches gptNeoProjectedEmptyCache
    gptNeoProjectedCacheOf gptNeoProjectedHeadCacheOf
  apply List.map_congr_left
  intro h hh
  simp [cacheOf, emptyCache]

end
end DecoderTransformer
