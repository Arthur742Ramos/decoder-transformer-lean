import DecoderTransformer.GPTNeoStack
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# GPT-Neo bounded/windowed cache stacks

The bounded stack has the same layer-to-layer cache relation as the full
stack, but each layer retains only its active local-attention context.
-/

def gptNeoBoundedTransformerCacheMatches
    (layers : List GPTNeoLayerParameters) (pref : Matrix ℝ)
    (caches : GPTNeoTransformerCache) : Prop :=
  match layers, caches with
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | p :: ps, cache :: rest =>
      gptNeoProjectedBoundedCacheMatches p pref cache ∧
        gptNeoBoundedTransformerCacheMatches ps (gptNeoFullLayer p pref) rest

def gptNeoBoundedCachedStackStep :
    List GPTNeoLayerParameters → Vector ℝ → GPTNeoTransformerCache →
      Vector ℝ × GPTNeoTransformerCache
  | [], x, _ => (x, [])
  | _ :: _, x, [] => (x, [])
  | p :: ps, x, cache :: rest =>
      let layerStep := gptNeoProjectedBoundedCachedBlockStep p x cache
      let stackStep := gptNeoBoundedCachedStackStep ps layerStep.1 rest
      (stackStep.1, layerStep.2 :: stackStep.2)

theorem gptNeoBoundedCachedStackStep_correct
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoBoundedTransformerCacheMatches layers pref caches) :
    gptNeoFullStack layers (pref ++ [x]) =
        gptNeoFullStack layers pref ++
          [(gptNeoBoundedCachedStackStep layers x caches).1] ∧
      gptNeoBoundedTransformerCacheMatches layers (pref ++ [x])
        (gptNeoBoundedCachedStackStep layers x caches).2 := by
  induction layers generalizing pref caches x with
  | nil =>
      simp [gptNeoBoundedTransformerCacheMatches,
        gptNeoBoundedCachedStackStep]
  | cons p ps ih =>
      cases caches with
      | nil =>
          simp [gptNeoBoundedTransformerCacheMatches] at hmatch
      | cons cache rest =>
          have hp : validGPTNeoLayer p := hvalid p (by simp)
          have hps : validGPTNeoStack ps := by
            intro q hq
            exact hvalid q (by simp [hq])
          have hpcache : gptNeoProjectedBoundedCacheMatches p pref cache :=
            hmatch.1
          have hrest : gptNeoBoundedTransformerCacheMatches ps
              (gptNeoFullLayer p pref) rest := hmatch.2
          let layerStep :=
            gptNeoProjectedBoundedCachedBlockStep p x cache
          have hlayer := gptNeoProjectedBoundedCachedBlockStep_correct
            (p := p) (pref := pref) (cache := cache) (x := x) hp hpcache
          have hstack := ih (pref := gptNeoFullLayer p pref)
              (caches := rest) (x := layerStep.1) hps hrest
          have hout : layerStep.1 =
              gptNeoBlockAtPrefix p x (pref ++ [x]) := hlayer.1
          have hfull := gptNeoFullLayer_append p pref x
          constructor
          · change gptNeoFullStack ps (gptNeoFullLayer p (pref ++ [x])) =
              gptNeoFullStack ps (gptNeoFullLayer p pref) ++
                [(gptNeoBoundedCachedStackStep ps layerStep.1 rest).1]
            rw [hfull, ← hout]
            exact hstack.1
          · change gptNeoProjectedBoundedCacheMatches p (pref ++ [x])
                layerStep.2 ∧
              gptNeoBoundedTransformerCacheMatches ps
                (gptNeoFullLayer p (pref ++ [x]))
                (gptNeoBoundedCachedStackStep ps layerStep.1 rest).2
            constructor
            · exact hlayer.2
            · rw [hfull, ← hout]
              exact hstack.2

theorem gptNeoBoundedCachedStackStep_output
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoBoundedTransformerCacheMatches layers pref caches) :
    (gptNeoBoundedCachedStackStep layers x caches).1 =
      (gptNeoFullStack layers (pref ++ [x])).getLast? := by
  have h := (gptNeoBoundedCachedStackStep_correct (layers := layers)
    (pref := pref) (caches := caches) (x := x) hvalid hmatch).1
  rw [h]
  simp

theorem gpt_neo_bounded_incremental_equals_full
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoBoundedTransformerCacheMatches layers pref caches) :
    (gptNeoBoundedCachedStackStep layers x caches).1 =
      (gptNeoFullStack layers (pref ++ [x])).getLast? :=
  gptNeoBoundedCachedStackStep_output hvalid hmatch

theorem gptNeoBoundedCachedStackStep_cache
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoBoundedTransformerCacheMatches layers pref caches) :
    gptNeoBoundedTransformerCacheMatches layers (pref ++ [x])
      (gptNeoBoundedCachedStackStep layers x caches).2 :=
  (gptNeoBoundedCachedStackStep_correct hvalid hmatch).2

def gptNeoBoundedCachedStackRun (layers : List GPTNeoLayerParameters)
    (caches : GPTNeoTransformerCache) (xs : Matrix ℝ) :
    Matrix ℝ × GPTNeoTransformerCache :=
  match xs with
  | [] => ([], caches)
  | x :: rest =>
      let step := gptNeoBoundedCachedStackStep layers x caches
      let tail := gptNeoBoundedCachedStackRun layers step.2 rest
      (step.1 :: tail.1, tail.2)

theorem gptNeoBoundedCachedStackRun_correct
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {xs : Matrix ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoBoundedTransformerCacheMatches layers pref caches) :
    gptNeoFullStack layers (pref ++ xs) =
        gptNeoFullStack layers pref ++
          (gptNeoBoundedCachedStackRun layers caches xs).1 ∧
      gptNeoBoundedTransformerCacheMatches layers (pref ++ xs)
        (gptNeoBoundedCachedStackRun layers caches xs).2 := by
  induction xs generalizing pref caches with
  | nil =>
      constructor
      · simp [gptNeoBoundedCachedStackRun]
      · simpa [gptNeoBoundedCachedStackRun] using hmatch
  | cons x xs ih =>
      let step := gptNeoBoundedCachedStackStep layers x caches
      have hone := gptNeoBoundedCachedStackStep_correct (layers := layers)
        (pref := pref) (caches := caches) (x := x) hvalid hmatch
      have htail := ih (pref := pref ++ [x]) (caches := step.2) hone.2
      dsimp [step] at htail
      simp only [gptNeoBoundedCachedStackRun]
      constructor
      · rw [show pref ++ x :: xs = (pref ++ [x]) ++ xs by simp,
          htail.1, hone.1]
        simp [List.append_assoc]
      · simpa [List.append_assoc] using htail.2

def emptyGPTNeoBoundedTransformerCache
    (layers : List GPTNeoLayerParameters) : GPTNeoTransformerCache :=
  layers.map gptNeoProjectedBoundedEmptyCache

theorem emptyGPTNeoBoundedTransformerCache_matches
    (layers : List GPTNeoLayerParameters) :
    gptNeoBoundedTransformerCacheMatches layers []
      (emptyGPTNeoBoundedTransformerCache layers) := by
  induction layers with
  | nil =>
      simp [emptyGPTNeoBoundedTransformerCache,
        gptNeoBoundedTransformerCacheMatches]
  | cons p ps ih =>
      change gptNeoProjectedBoundedCacheMatches p []
          (gptNeoProjectedBoundedEmptyCache p) ∧
        gptNeoBoundedTransformerCacheMatches ps (gptNeoFullLayer p [])
          (emptyGPTNeoBoundedTransformerCache ps)
      constructor
      · exact gptNeoProjectedBoundedEmptyCache_matches p
      · simpa using ih

theorem gpt_neo_bounded_cache_matches_empty (p : GPTNeoLayerParameters) :
    gptNeoProjectedBoundedCacheMatches p []
      (gptNeoProjectedBoundedEmptyCache p) :=
  gptNeoProjectedBoundedEmptyCache_matches p

theorem initializedGPTNeoBoundedCachedRun_equalsFull
    {layers : List GPTNeoLayerParameters} (hvalid : validGPTNeoStack layers)
    (xs : Matrix ℝ) :
    (gptNeoBoundedCachedStackRun layers
      (emptyGPTNeoBoundedTransformerCache layers) xs).1 =
      gptNeoFullStack layers xs := by
  have h := gptNeoBoundedCachedStackRun_correct (layers := layers)
    (pref := []) (caches := emptyGPTNeoBoundedTransformerCache layers)
    (xs := xs) hvalid (emptyGPTNeoBoundedTransformerCache_matches layers)
  simpa [gptNeoFullStack_empty] using h.1.symm

theorem initializedGPTNeoBoundedCachedRun_cacheInvariant
    {layers : List GPTNeoLayerParameters} (hvalid : validGPTNeoStack layers)
    (xs : Matrix ℝ) :
    gptNeoBoundedTransformerCacheMatches layers xs
      (gptNeoBoundedCachedStackRun layers
        (emptyGPTNeoBoundedTransformerCache layers) xs).2 := by
  have h := gptNeoBoundedCachedStackRun_correct (layers := layers)
    (pref := []) (caches := emptyGPTNeoBoundedTransformerCache layers)
    (xs := xs) hvalid (emptyGPTNeoBoundedTransformerCache_matches layers)
  simpa using h.2

end
end DecoderTransformer
