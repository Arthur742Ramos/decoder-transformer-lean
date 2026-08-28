import DecoderTransformer.DecoderBlock

namespace DecoderTransformer

noncomputable section

/-!
# Incremental decoder stacks

This is the generic per-head cache refinement.  Cache lookup is totalized by
`List.getD`, while `layerCacheMatches` records the exact projected prefix, so
all uses at a valid head index reduce to the intended list entry.
-/

structure DecoderLayerParameters where
  headCount : Nat
  modelDim : Nat
  headDim : Nat
  hiddenDim : Nat
  normEpsilon : ℝ
  activation : ℝ → ℝ
  attentionGain : Vector ℝ
  mlpGain : Vector ℝ
  queryWeights : Tensor3 ℝ
  keyWeights : Tensor3 ℝ
  valueWeights : Tensor3 ℝ
  outputWeights : Matrix ℝ
  upWeights : Matrix ℝ
  downWeights : Matrix ℝ

def fullDecoderLayer (p : DecoderLayerParameters) : Matrix ℝ → Matrix ℝ :=
  decoderBlock p.headCount p.modelDim p.headDim p.hiddenDim p.normEpsilon
    p.activation p.attentionGain p.mlpGain p.queryWeights p.keyWeights
    p.valueWeights p.outputWeights p.upWeights p.downWeights

def decoderLayerAtPrefix (p : DecoderLayerParameters) (pref : Matrix ℝ)
    (x : Vector ℝ) : Vector ℝ :=
  let normalizedX := rmsNorm p.normEpsilon p.attentionGain x
  let attention := multiHeadAtPrefix p.headCount p.modelDim p.headDim
    p.queryWeights p.keyWeights p.valueWeights p.outputWeights normalizedX
    (rmsNormSequence p.normEpsilon p.attentionGain pref ++ [normalizedX])
  let attentionResidual := vectorAdd x attention
  vectorAdd attentionResidual
    (feedForward p.modelDim p.hiddenDim p.activation p.upWeights p.downWeights
      (rmsNorm p.normEpsilon p.mlpGain attentionResidual))

theorem fullDecoderLayer_append (p : DecoderLayerParameters) (pref : Matrix ℝ)
    (x : Vector ℝ) :
    fullDecoderLayer p (pref ++ [x]) = fullDecoderLayer p pref ++
      [decoderLayerAtPrefix p pref x] := by
  unfold fullDecoderLayer decoderBlock Function.comp
  rw [attentionResidualBlock_append, mlpResidualBlock_append]
  rfl

@[simp] theorem length_fullDecoderLayer (p : DecoderLayerParameters) (X : Matrix ℝ) :
    (fullDecoderLayer p X).length = X.length := by
  simp [fullDecoderLayer, length_decoderBlock]

abbrev HeadKVCache := Matrix ℝ × Matrix ℝ
abbrev LayerKVCache := List HeadKVCache
abbrev TransformerKVCache := List LayerKVCache

def layerCacheOf (p : DecoderLayerParameters) (pref : Matrix ℝ) : LayerKVCache :=
  (List.range p.headCount).map (fun h =>
    ((rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.keyWeights h)),
     (rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.valueWeights h))))

def layerCacheMatches (p : DecoderLayerParameters) (pref : Matrix ℝ)
    (cache : LayerKVCache) : Prop := cache = layerCacheOf p pref

def extendHeadCache (p : DecoderLayerParameters) (h : Nat) (normalizedX : Vector ℝ)
    (cache : HeadKVCache) : HeadKVCache :=
  (cache.1 ++ [linearProject p.headDim (tensorMatrixAt p.keyWeights h) normalizedX],
   cache.2 ++ [linearProject p.headDim (tensorMatrixAt p.valueWeights h) normalizedX])

def layerCacheAt (cache : LayerKVCache) (h : Nat) : HeadKVCache :=
  cache.getD h ([], [])

def extendLayerCache (p : DecoderLayerParameters) (normalizedX : Vector ℝ)
    (cache : LayerKVCache) : LayerKVCache :=
  (List.range p.headCount).map (fun h =>
    extendHeadCache p h normalizedX (layerCacheAt cache h))

theorem getD_map_range {β : Type*} (f : Nat → β) (d : β)
    {n i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD, List.getElem?_map]
  have hget : (List.range n)[i]? = some i := by
    rw [List.getElem?_eq_getElem (by simp [hi]), List.getElem_range]
  rw [hget]
  rfl

theorem extend_layer_cache_nth (p : DecoderLayerParameters)
    (normalizedX : Vector ℝ) (cache : LayerKVCache) {h : Nat}
    (hh : h < p.headCount) :
    (extendLayerCache p normalizedX cache).getD h ([], []) =
      extendHeadCache p h normalizedX (layerCacheAt cache h) := by
  unfold extendLayerCache
  exact getD_map_range _ _ hh

theorem extendLayerCache_matches {p : DecoderLayerParameters}
    {pref : Matrix ℝ} {cache : LayerKVCache} {x : Vector ℝ}
    (hcache : layerCacheMatches p pref cache) :
    layerCacheMatches p (pref ++ [x])
      (extendLayerCache p (rmsNorm p.normEpsilon p.attentionGain x) cache) := by
  subst cache
  apply Eq.symm
  unfold extendLayerCache
  apply List.map_congr_left
  intro h hh
  have hlt : h < p.headCount := List.mem_range.1 hh
  have hget : layerCacheAt (layerCacheOf p pref) h =
      ((rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.keyWeights h)),
       (rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.valueWeights h))) := by
    exact getD_map_range _ _ hlt
  rw [hget]
  simp [extendHeadCache, rmsNormSequence, List.map_append]

def cachedMultiHeadOutput (p : DecoderLayerParameters) (normalizedX : Vector ℝ)
    (cache : LayerKVCache) : Vector ℝ :=
  linearProject p.modelDim p.outputWeights
    ((List.range p.headCount).map (fun h =>
      exactAttention p.headDim p.headDim
        (linearProject p.headDim (tensorMatrixAt p.queryWeights h) normalizedX)
        (layerCacheAt cache h).1 (layerCacheAt cache h).2) |>.flatten)

theorem cachedMultiHeadOutput_correct {p : DecoderLayerParameters}
    {pref : Matrix ℝ} {cache : LayerKVCache} {x normalizedX : Vector ℝ}
    (hcache : layerCacheMatches p pref cache) :
    cachedMultiHeadOutput p normalizedX
        (extendLayerCache p normalizedX cache) =
      multiHeadAtPrefix p.headCount p.modelDim p.headDim
        p.queryWeights p.keyWeights p.valueWeights p.outputWeights normalizedX
        (rmsNormSequence p.normEpsilon p.attentionGain pref ++ [normalizedX]) := by
  subst cache
  unfold cachedMultiHeadOutput multiHeadAtPrefix concatenatedHeadAttention
  apply congrArg (linearProject p.modelDim p.outputWeights)
  apply congrArg List.flatten
  apply List.map_congr_left
  intro h hh
  have hlt : h < p.headCount := List.mem_range.1 hh
  have hget : layerCacheAt (layerCacheOf p pref) h =
      ((rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.keyWeights h)),
       (rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.valueWeights h))) := by
    exact getD_map_range _ _ hlt
  have hext : layerCacheAt (extendLayerCache p normalizedX
      (layerCacheOf p pref)) h =
      ((rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.keyWeights h)) ++
          [linearProject p.headDim (tensorMatrixAt p.keyWeights h) normalizedX],
       (rmsNormSequence p.normEpsilon p.attentionGain pref).map
        (linearProject p.headDim (tensorMatrixAt p.valueWeights h)) ++
          [linearProject p.headDim (tensorMatrixAt p.valueWeights h) normalizedX]) := by
    have hget' : (layerCacheOf p pref).getD h ([], []) =
        ((rmsNormSequence p.normEpsilon p.attentionGain pref).map
          (linearProject p.headDim (tensorMatrixAt p.keyWeights h)),
         (rmsNormSequence p.normEpsilon p.attentionGain pref).map
          (linearProject p.headDim (tensorMatrixAt p.valueWeights h))) := by
      simpa [layerCacheAt] using hget
    unfold extendLayerCache layerCacheAt
    rw [getD_map_range _ _ hlt, hget']
    rfl
  rw [hext]
  simp [extendLayerCache, layerCacheOf, layerCacheAt,
    getD_map_range _ _ hlt, hget, extendHeadCache, rmsNormSequence,
    List.map_append, projectedHeadAttention]

def cachedDecoderLayerStep (p : DecoderLayerParameters) (x : Vector ℝ)
    (cache : LayerKVCache) : Vector ℝ × LayerKVCache :=
  let normalizedX := rmsNorm p.normEpsilon p.attentionGain x
  let cache' := extendLayerCache p normalizedX cache
  let attention := cachedMultiHeadOutput p normalizedX cache'
  let attentionResidual := vectorAdd x attention
  let output := vectorAdd attentionResidual
    (feedForward p.modelDim p.hiddenDim p.activation p.upWeights p.downWeights
      (rmsNorm p.normEpsilon p.mlpGain attentionResidual))
  (output, cache')

theorem cachedDecoderLayerStep_correct {p : DecoderLayerParameters}
    {pref : Matrix ℝ} {cache : LayerKVCache} {x : Vector ℝ}
    (hcache : layerCacheMatches p pref cache) :
    (cachedDecoderLayerStep p x cache).1 = decoderLayerAtPrefix p pref x ∧
    layerCacheMatches p (pref ++ [x]) (cachedDecoderLayerStep p x cache).2 := by
  have hout := cachedMultiHeadOutput_correct (p := p) (pref := pref)
    (cache := cache) (x := x)
    (normalizedX := rmsNorm p.normEpsilon p.attentionGain x) hcache
  have hcache' := extendLayerCache_matches (p := p) (pref := pref)
    (cache := cache) (x := x) hcache
  constructor
  · simp [cachedDecoderLayerStep, decoderLayerAtPrefix, hout]
  · simpa [cachedDecoderLayerStep] using hcache'

theorem cachedDecoderLayerStep_full {p : DecoderLayerParameters}
    {pref : Matrix ℝ} {cache : LayerKVCache} {x : Vector ℝ}
    (hcache : layerCacheMatches p pref cache) :
    fullDecoderLayer p (pref ++ [x]) = fullDecoderLayer p pref ++
      [(cachedDecoderLayerStep p x cache).1] := by
  rw [fullDecoderLayer_append]
  simpa using congrArg (fun z => fullDecoderLayer p pref ++ [z])
    (cachedDecoderLayerStep_correct (p := p) (pref := pref)
      (cache := cache) (x := x) hcache).1.symm

def fullDecoderStack : List DecoderLayerParameters → Matrix ℝ → Matrix ℝ
  | [], X => X
  | p :: ps, X => fullDecoderStack ps (fullDecoderLayer p X)

def transformerCacheMatches : List DecoderLayerParameters → Matrix ℝ →
    TransformerKVCache → Prop
  | [], pref, caches => caches = []
  | p :: ps, pref, [] => False
  | p :: ps, pref, cache :: caches =>
      layerCacheMatches p pref cache ∧
        transformerCacheMatches ps (fullDecoderLayer p pref) caches

def cachedDecoderStackStep : List DecoderLayerParameters → Vector ℝ →
    TransformerKVCache → Vector ℝ × TransformerKVCache
  | [], x, caches => (x, [])
  | p :: ps, x, [] => (x, [])
  | p :: ps, x, cache :: caches =>
      let layerStep := cachedDecoderLayerStep p x cache
      let stackStep := cachedDecoderStackStep ps layerStep.1 caches
      (stackStep.1, layerStep.2 :: stackStep.2)

theorem cachedDecoderStackStep_correct {layers : List DecoderLayerParameters}
    {pref : Matrix ℝ} {caches : TransformerKVCache} {x : Vector ℝ}
    (hmatch : transformerCacheMatches layers pref caches) :
    fullDecoderStack layers (pref ++ [x]) =
        fullDecoderStack layers pref ++
          [cachedDecoderStackStep layers x caches |>.1] ∧
    transformerCacheMatches layers (pref ++ [x])
      (cachedDecoderStackStep layers x caches |>.2) := by
  induction layers generalizing pref caches x with
  | nil => simp [fullDecoderStack, cachedDecoderStackStep, transformerCacheMatches]
  | cons p ps ih =>
      cases caches with
      | nil => simp [transformerCacheMatches] at hmatch
      | cons cache caches =>
          have hp : layerCacheMatches p pref cache := hmatch.1
          have hps : transformerCacheMatches ps (fullDecoderLayer p pref) caches :=
            hmatch.2
          have hstep := cachedDecoderLayerStep_correct (p := p)
            (pref := pref) (cache := cache) (x := x) hp
          have hstack := ih (pref := fullDecoderLayer p pref)
            (caches := caches)
            (x := (cachedDecoderLayerStep p x cache).1) hps
          have hfull : fullDecoderLayer p (pref ++ [x]) =
              fullDecoderLayer p pref ++
                [(cachedDecoderLayerStep p x cache).1] := by
            exact cachedDecoderLayerStep_full hp
          constructor
          · simpa [fullDecoderStack, cachedDecoderStackStep, hfull] using hstack.1
          · have htail : transformerCacheMatches ps
                (fullDecoderLayer p (pref ++ [x]))
                (cachedDecoderStackStep ps
                  (cachedDecoderLayerStep p x cache).1 caches).2 := by
              simpa [hfull] using hstack.2
            change layerCacheMatches p (pref ++ [x])
                (cachedDecoderLayerStep p x cache).2 ∧
              transformerCacheMatches ps (fullDecoderLayer p (pref ++ [x]))
                (cachedDecoderStackStep ps
                  (cachedDecoderLayerStep p x cache).1 caches).2
            exact ⟨hstep.2, htail⟩

theorem incrementalDecoderEqualsFull {layers : List DecoderLayerParameters}
    {pref : Matrix ℝ} {caches : TransformerKVCache} {x : Vector ℝ}
    (hmatch : transformerCacheMatches layers pref caches) :
    (fullDecoderStack layers (pref ++ [x])).getLast? =
      some (cachedDecoderStackStep layers x caches |>.1) := by
  have h := (cachedDecoderStackStep_correct (layers := layers)
    (pref := pref) (caches := caches) (x := x) hmatch).1
  rw [h]
  simp

end
end DecoderTransformer
