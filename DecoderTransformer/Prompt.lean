import DecoderTransformer.ModelValidity
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Cache initialization and whole-prompt refinement
-/

def emptyLayerCache (p : DecoderLayerParameters) : LayerKVCache :=
  List.replicate p.headCount ([], [])

def emptyTransformerCache (layers : List DecoderLayerParameters) :
    TransformerKVCache := layers.map emptyLayerCache

@[simp] theorem length_emptyLayerCache (p : DecoderLayerParameters) :
    (emptyLayerCache p).length = p.headCount := by
  simp [emptyLayerCache]

@[simp] theorem length_emptyTransformerCache
    (layers : List DecoderLayerParameters) :
    (emptyTransformerCache layers).length = layers.length := by
  simp [emptyTransformerCache]

theorem emptyLayerCache_matches (p : DecoderLayerParameters) :
    layerCacheMatches p [] (emptyLayerCache p) := by
  have hconst : ∀ n : Nat,
      (List.range n).map (fun _ : Nat => (([] : Matrix ℝ), ([] : Matrix ℝ))) =
        List.replicate n (([], []) : HeadKVCache) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [ih]
  change List.replicate p.headCount (([], []) : HeadKVCache) =
    (List.range p.headCount).map (fun h =>
      ((rmsNormSequence p.normEpsilon p.attentionGain []).map
          (linearProject p.headDim (tensorMatrixAt p.keyWeights h)),
       (rmsNormSequence p.normEpsilon p.attentionGain []).map
          (linearProject p.headDim (tensorMatrixAt p.valueWeights h))))
  simpa [rmsNormSequence] using (hconst p.headCount).symm

@[simp] theorem fullDecoderLayer_empty (p : DecoderLayerParameters) :
    fullDecoderLayer p [] = [] := by
  have hlen := length_fullDecoderLayer p ([] : Matrix ℝ)
  exact List.eq_nil_of_length_eq_zero (by simpa using hlen)

@[simp] theorem fullDecoderStack_empty
    (layers : List DecoderLayerParameters) :
    fullDecoderStack layers [] = [] := by
  induction layers with
  | nil => simp [fullDecoderStack]
  | cons p ps ih => simp [fullDecoderStack, ih]

theorem emptyTransformerCache_matches
    (layers : List DecoderLayerParameters) :
    transformerCacheMatches layers [] (emptyTransformerCache layers) := by
  induction layers with
  | nil => simp [emptyTransformerCache, transformerCacheMatches]
  | cons p ps ih =>
      simp only [emptyTransformerCache, List.map_cons, transformerCacheMatches,
        fullDecoderLayer_empty]
      exact ⟨emptyLayerCache_matches p, ih⟩

def cachedDecoderStackRun (layers : List DecoderLayerParameters)
    (caches : TransformerKVCache) (xs : Matrix ℝ) :
    TransformerKVCache × Matrix ℝ :=
  match xs with
  | [] => (caches, [])
  | x :: rest =>
      let step := cachedDecoderStackStep layers x caches
      let tail := cachedDecoderStackRun layers step.2 rest
      (tail.1, step.1 :: tail.2)

@[simp] theorem length_cachedDecoderStackRun
    (layers : List DecoderLayerParameters) (caches : TransformerKVCache)
    (xs : Matrix ℝ) :
    (cachedDecoderStackRun layers caches xs).2.length = xs.length := by
  induction xs generalizing caches with
  | nil => simp [cachedDecoderStackRun]
  | cons x xs ih =>
      simp [cachedDecoderStackRun, ih]

theorem cachedDecoderStackRun_correct
    {layers : List DecoderLayerParameters}
    {pref : Matrix ℝ} {caches : TransformerKVCache}
    (xs : Matrix ℝ)
    (hmatch : transformerCacheMatches layers pref caches) :
    fullDecoderStack layers (pref ++ xs) =
        fullDecoderStack layers pref ++
          (cachedDecoderStackRun layers caches xs).2 ∧
    transformerCacheMatches layers (pref ++ xs)
      (cachedDecoderStackRun layers caches xs).1 := by
  induction xs generalizing pref caches with
  | nil =>
      constructor
      · simp [cachedDecoderStackRun]
      · simpa [cachedDecoderStackRun] using hmatch
  | cons x xs ih =>
      have hstep := cachedDecoderStackStep_correct
        (layers := layers) (pref := pref) (caches := caches) (x := x) hmatch
      have htail := ih (pref := pref ++ [x])
        (caches := (cachedDecoderStackStep layers x caches).2) (by exact hstep.2)
      constructor
      · change fullDecoderStack layers (pref ++ x :: xs) =
          fullDecoderStack layers pref ++
            (cachedDecoderStackStep layers x caches).1 ::
              (cachedDecoderStackRun layers
                (cachedDecoderStackStep layers x caches).2 xs).2
        calc
          fullDecoderStack layers (pref ++ x :: xs) =
              fullDecoderStack layers ((pref ++ [x]) ++ xs) := by
            simp [List.append_assoc]
          _ = fullDecoderStack layers (pref ++ [x]) ++
                (cachedDecoderStackRun layers
                  (cachedDecoderStackStep layers x caches).2 xs).2 := htail.1
          _ = (fullDecoderStack layers pref ++
                [(cachedDecoderStackStep layers x caches).1]) ++
                (cachedDecoderStackRun layers
                  (cachedDecoderStackStep layers x caches).2 xs).2 := by
            rw [hstep.1]
          _ = fullDecoderStack layers pref ++
                (cachedDecoderStackStep layers x caches).1 ::
                (cachedDecoderStackRun layers
                  (cachedDecoderStackStep layers x caches).2 xs).2 := by
            simp [List.append_assoc]
      · simp only [cachedDecoderStackRun]
        simpa [List.append_assoc] using htail.2

theorem initializedCachedRun_equalsFull
    (layers : List DecoderLayerParameters) (xs : Matrix ℝ) :
    (cachedDecoderStackRun layers (emptyTransformerCache layers) xs).2 =
      fullDecoderStack layers xs := by
  have h := cachedDecoderStackRun_correct (layers := layers)
    (pref := []) (caches := emptyTransformerCache layers) xs
    (emptyTransformerCache_matches layers)
  simpa using h.1.symm

theorem initializedCachedRun_cacheInvariant
    (layers : List DecoderLayerParameters) (xs : Matrix ℝ) :
    transformerCacheMatches layers xs
      (cachedDecoderStackRun layers (emptyTransformerCache layers) xs).1 := by
  have h := cachedDecoderStackRun_correct (layers := layers)
    (pref := []) (caches := emptyTransformerCache layers) xs
    (emptyTransformerCache_matches layers)
  simpa using h.2

def initializeGenerationState (layers : List DecoderLayerParameters)
    (embedding : Nat → Vector ℝ) (tokens : List Nat) : GenerationState :=
  (tokens,
    (cachedDecoderStackRun layers (emptyTransformerCache layers)
      (tokens.dropLast.map embedding)).1)

theorem initializeGenerationState_correct
    {layers : List DecoderLayerParameters} {embedding : Nat → Vector ℝ}
    {tokens : List Nat} (htokens : tokens ≠ []) :
    generationCacheMatches embedding layers
      (initializeGenerationState layers embedding tokens).1
      (initializeGenerationState layers embedding tokens).2 := by
  refine ⟨?_, ?_⟩
  · simpa [initializeGenerationState] using htokens
  · simpa [initializeGenerationState] using
      (initializedCachedRun_cacheInvariant layers (tokens.dropLast.map embedding))

theorem initializedGenerationEvaluate_correct
    {layers : List DecoderLayerParameters} {embedding : Nat → Vector ℝ}
    {tokens : List Nat} (htokens : tokens ≠ [])
    (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ) :
    (cachedGenerationEvaluate layers embedding vocabularySize vocabularyWeights
      tokens (initializeGenerationState layers embedding tokens).2).1 =
      nextTokenDistribution vocabularySize vocabularyWeights
        ((fullDecoderStack layers (tokens.map embedding)).getLast?.getD
          ([] : Vector ℝ)) := by
  exact (cachedGenerationEvaluate_correct
    (initializeGenerationState_correct htokens) vocabularySize vocabularyWeights).1

end
end DecoderTransformer
