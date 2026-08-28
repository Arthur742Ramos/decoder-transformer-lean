import DecoderTransformer.GPTNeoWindowedCache
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# GPT-Neo layer stacks and prompt caches

The cache for each layer is indexed by the sequence produced by all lower
layers.  This is the architecture-level refinement theorem: a projected
per-head cache run produces exactly the same stack outputs as the full
causal stack.
-/

abbrev GPTNeoLayerCache := GPTNeoProjectedLayerCache
abbrev GPTNeoTransformerCache := List GPTNeoLayerCache

def gptNeoFullStack : List GPTNeoLayerParameters → Matrix ℝ → Matrix ℝ
  | [], X => X
  | p :: ps, X => gptNeoFullStack ps (gptNeoFullLayer p X)

@[simp] theorem gptNeoFullStack_nil (X : Matrix ℝ) :
    gptNeoFullStack [] X = X := by
  rfl

@[simp] theorem gptNeoFullStack_cons (p : GPTNeoLayerParameters)
    (ps : List GPTNeoLayerParameters) (X : Matrix ℝ) :
    gptNeoFullStack (p :: ps) X =
      gptNeoFullStack ps (gptNeoFullLayer p X) := by
  rfl

theorem length_gptNeoFullStack (layers : List GPTNeoLayerParameters)
    (X : Matrix ℝ) :
    (gptNeoFullStack layers X).length = X.length := by
  induction layers generalizing X with
  | nil => rfl
  | cons p ps ih =>
      have hlayer : (gptNeoFullLayer p X).length = X.length := by
        simpa [gptNeoFullLayer] using
          length_causalAttention id id id
            (fun x pref _ => gptNeoBlockAtPrefix p x pref) X
      exact (ih (gptNeoFullLayer p X)).trans hlayer

def validGPTNeoStack (layers : List GPTNeoLayerParameters) : Prop :=
  ∀ p ∈ layers, validGPTNeoLayer p

def gptNeoStackCompatible (modelDim : Nat)
    (layers : List GPTNeoLayerParameters) : Prop :=
  ∀ p ∈ layers, validGPTNeoLayer p ∧ p.modelDim = modelDim

theorem compatibleGPTNeoFullStackShape
    {modelDim seqLen : Nat} {layers : List GPTNeoLayerParameters}
    {X : Matrix ℝ}
    (hcompatible : gptNeoStackCompatible modelDim layers)
    (hinput : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim (gptNeoFullStack layers X) := by
  induction layers generalizing X with
  | nil =>
      simpa using hinput
  | cons p ps ih =>
      have hp := hcompatible p (by simp)
      have hps : gptNeoStackCompatible modelDim ps := by
        intro q hq
        exact hcompatible q (by simp [hq])
      have hinput' : matrixShape seqLen p.modelDim X := by
        simpa [hp.2] using hinput
      have hlayer : matrixShape seqLen modelDim
          (gptNeoFullLayer p X) := by
        simpa [hp.2] using validGPTNeoFullLayer_shape hp.1 hinput'
      exact ih hps hlayer

def gptNeoTransformerCacheMatches
    (layers : List GPTNeoLayerParameters) (pref : Matrix ℝ)
    (caches : GPTNeoTransformerCache) : Prop :=
  match layers, caches with
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | p :: ps, cache :: rest =>
      gptNeoProjectedCacheMatches p pref cache ∧
        gptNeoTransformerCacheMatches ps (gptNeoFullLayer p pref) rest

def gptNeoCachedStackStep : List GPTNeoLayerParameters → Vector ℝ →
    GPTNeoTransformerCache → Vector ℝ × GPTNeoTransformerCache
  | [], x, _ => (x, [])
  | _ :: _, x, [] => (x, [])
  | p :: ps, x, cache :: rest =>
      let layerStep := gptNeoProjectedCachedBlockStep p x cache
      let stackStep := gptNeoCachedStackStep ps layerStep.1 rest
      (stackStep.1, layerStep.2 :: stackStep.2)

theorem gptNeoCachedStackStep_correct
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoTransformerCacheMatches layers pref caches) :
    gptNeoFullStack layers (pref ++ [x]) =
        gptNeoFullStack layers pref ++
          [(gptNeoCachedStackStep layers x caches).1] ∧
      gptNeoTransformerCacheMatches layers (pref ++ [x])
        (gptNeoCachedStackStep layers x caches).2 := by
  induction layers generalizing pref caches x with
  | nil =>
      simp [gptNeoTransformerCacheMatches, gptNeoCachedStackStep]
  | cons p ps ih =>
      cases caches with
      | nil =>
          simp [gptNeoTransformerCacheMatches] at hmatch
      | cons cache rest =>
          have hp : validGPTNeoLayer p := hvalid p (by simp)
          have hps : validGPTNeoStack ps := by
            intro q hq
            exact hvalid q (by simp [hq])
          have hpcache : gptNeoProjectedCacheMatches p pref cache := by
            exact hmatch.1
          have hrest : gptNeoTransformerCacheMatches ps
              (gptNeoFullLayer p pref) rest := hmatch.2
          let layerStep := gptNeoProjectedCachedBlockStep p x cache
          have hlayer := gptNeoProjectedCachedBlockStep_correct
            (p := p) (pref := pref) (cache := cache) (x := x) hp hpcache
          have hstack := ih (pref := gptNeoFullLayer p pref)
              (caches := rest) (x := layerStep.1) hps hrest
          have hout : layerStep.1 =
              gptNeoBlockAtPrefix p x (pref ++ [x]) := by
            exact hlayer.1
          have hfull := gptNeoFullLayer_append p pref x
          constructor
          · change gptNeoFullStack ps (gptNeoFullLayer p (pref ++ [x])) =
              gptNeoFullStack ps (gptNeoFullLayer p pref) ++
                [(gptNeoCachedStackStep ps layerStep.1 rest).1]
            rw [hfull, ← hout]
            exact hstack.1
          · change gptNeoProjectedCacheMatches p (pref ++ [x]) layerStep.2 ∧
              gptNeoTransformerCacheMatches ps
                (gptNeoFullLayer p (pref ++ [x]))
                (gptNeoCachedStackStep ps layerStep.1 rest).2
            constructor
            · exact hlayer.2
            · rw [hfull, ← hout]
              exact hstack.2

theorem gptNeoCachedStackStep_output
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoTransformerCacheMatches layers pref caches) :
    (gptNeoCachedStackStep layers x caches).1 =
      (gptNeoFullStack layers (pref ++ [x])).getLast? := by
  have h := (gptNeoCachedStackStep_correct (layers := layers)
    (pref := pref) (caches := caches) (x := x) hvalid hmatch).1
  rw [h]
  simp

theorem gptNeoCachedStackStep_cache
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {x : Vector ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoTransformerCacheMatches layers pref caches) :
    gptNeoTransformerCacheMatches layers (pref ++ [x])
      (gptNeoCachedStackStep layers x caches).2 :=
  (gptNeoCachedStackStep_correct hvalid hmatch).2

def gptNeoCachedStackRun (layers : List GPTNeoLayerParameters)
    (caches : GPTNeoTransformerCache) (xs : Matrix ℝ) :
    Matrix ℝ × GPTNeoTransformerCache :=
  match xs with
  | [] => ([], caches)
  | x :: rest =>
      let step := gptNeoCachedStackStep layers x caches
      let tail := gptNeoCachedStackRun layers step.2 rest
      (step.1 :: tail.1, tail.2)

theorem gptNeoCachedStackRun_correct
    {layers : List GPTNeoLayerParameters} {pref : Matrix ℝ}
    {caches : GPTNeoTransformerCache} {xs : Matrix ℝ}
    (hvalid : validGPTNeoStack layers)
    (hmatch : gptNeoTransformerCacheMatches layers pref caches) :
    gptNeoFullStack layers (pref ++ xs) =
        gptNeoFullStack layers pref ++
          (gptNeoCachedStackRun layers caches xs).1 ∧
      gptNeoTransformerCacheMatches layers (pref ++ xs)
        (gptNeoCachedStackRun layers caches xs).2 := by
  induction xs generalizing pref caches with
  | nil =>
      constructor
      · simp [gptNeoCachedStackRun]
      · simpa [gptNeoCachedStackRun] using hmatch
  | cons x xs ih =>
      let step := gptNeoCachedStackStep layers x caches
      have hone := gptNeoCachedStackStep_correct (layers := layers)
        (pref := pref) (caches := caches) (x := x) hvalid hmatch
      have htail := ih (pref := pref ++ [x]) (caches := step.2)
        hone.2
      dsimp [step] at htail
      simp only [gptNeoCachedStackRun, step, ↓reduceIte]
      constructor
      · rw [show pref ++ x :: xs = (pref ++ [x]) ++ xs by simp,
          htail.1, hone.1]
        simp [List.append_assoc]
      · simpa [List.append_assoc] using htail.2

def emptyGPTNeoTransformerCache
    (layers : List GPTNeoLayerParameters) : GPTNeoTransformerCache :=
  layers.map gptNeoProjectedEmptyCache

@[simp] theorem gptNeoFullLayer_empty (p : GPTNeoLayerParameters) :
    gptNeoFullLayer p [] = [] := by
  have h := length_causalAttention id id id
    (fun x pref _ => gptNeoBlockAtPrefix p x pref) ([] : Matrix ℝ)
  simpa [gptNeoFullLayer] using h

@[simp] theorem gptNeoFullStack_empty
    (layers : List GPTNeoLayerParameters) :
    gptNeoFullStack layers [] = [] := by
  induction layers with
  | nil => simp [gptNeoFullStack]
  | cons p ps ih => simp [gptNeoFullStack, ih]

@[simp] theorem length_gpt_neo_full_layer (p : GPTNeoLayerParameters)
    (X : Matrix ℝ) : (gptNeoFullLayer p X).length = X.length := by
  simpa [gptNeoFullLayer] using
    (length_causalAttention id id id
      (fun x pref _ => gptNeoBlockAtPrefix p x pref) X)

theorem gpt_neo_full_stack_def (layers : List GPTNeoLayerParameters)
    (X : Matrix ℝ) :
    gptNeoFullStack layers X =
      match layers with
      | [] => X
      | p :: ps => gptNeoFullStack ps (gptNeoFullLayer p X) := by
  cases layers <;> rfl

theorem emptyGPTNeoTransformerCache_matches
    (layers : List GPTNeoLayerParameters) :
    gptNeoTransformerCacheMatches layers []
      (emptyGPTNeoTransformerCache layers) := by
  induction layers with
  | nil => simp [emptyGPTNeoTransformerCache, gptNeoTransformerCacheMatches]
  | cons p ps ih =>
      change gptNeoProjectedCacheMatches p [] (gptNeoProjectedEmptyCache p) ∧
        gptNeoTransformerCacheMatches ps (gptNeoFullLayer p [])
          (emptyGPTNeoTransformerCache ps)
      constructor
      · exact gptNeoProjectedEmptyCache_matches p
      · simpa using ih

theorem initializedGPTNeoCachedRun_equalsFull
    {layers : List GPTNeoLayerParameters} (hvalid : validGPTNeoStack layers)
    (xs : Matrix ℝ) :
    (gptNeoCachedStackRun layers (emptyGPTNeoTransformerCache layers) xs).1 =
      gptNeoFullStack layers xs := by
  have h := gptNeoCachedStackRun_correct (layers := layers) (pref := [])
    (caches := emptyGPTNeoTransformerCache layers) (xs := xs) hvalid
    (emptyGPTNeoTransformerCache_matches layers)
  simpa [gptNeoFullStack_empty] using h.1.symm

theorem initializedGPTNeoCachedRun_cacheInvariant
    {layers : List GPTNeoLayerParameters} (hvalid : validGPTNeoStack layers)
    (xs : Matrix ℝ) :
    gptNeoTransformerCacheMatches layers xs
      (gptNeoCachedStackRun layers (emptyGPTNeoTransformerCache layers) xs).2 := by
  have h := gptNeoCachedStackRun_correct (layers := layers) (pref := [])
    (caches := emptyGPTNeoTransformerCache layers) (xs := xs) hvalid
    (emptyGPTNeoTransformerCache_matches layers)
  simpa using h.2

end

end DecoderTransformer
