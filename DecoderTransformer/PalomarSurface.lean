import DecoderTransformer.DyadicFinitePrecision

namespace DecoderTransformer

noncomputable section

/-!
# Palomar theorem surface

These wrappers state the public contracts with their semantic side
conditions.  The underlying library remains total on arbitrary lists, but
the advertised refinement results are about nonempty, dimension-compatible
modern stacks; generation and next-token error additionally use a positive
vocabulary.
-/

def palomarModernStackWellFormed (modelDim : Nat)
    (layers : List ModernDecoderLayerParameters) : Prop :=
  layers ≠ [] ∧ validModernStack layers ∧
    modernStackCompatible modelDim layers

theorem palomarIncrementalModernDecoderRefinesFull
    {modelDim : Nat} {layers : List ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {caches : ModernTransformerCache} {x : Vector ℝ}
    (hwellformed : palomarModernStackWellFormed modelDim layers)
    (hmatch : modernTransformerCacheMatches layers start pref caches) :
    (cachedModernDecoderStackStep layers (start + pref.length) x caches).1 =
      (fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD
        ([] : Vector ℝ) := by
  exact incremental_modern_decoder_equals_full hwellformed.2.1 hmatch

theorem palomarModernGreedyGenerateStepsRefinesFull {modelDim n : Nat}
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hwellformed : palomarModernStackWellFormed modelDim layers)
    (hvocabulary : 0 < vocabularySize)
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    (modernGenerateSteps n firstArgmax layers embedding start vocabularySize
      vocabularyWeights state).1 =
      modernFullGenerateSteps n layers embedding start vocabularySize
        vocabularyWeights state.1 := by
  exact modernGreedyGenerateStepsEqFull hmatch

theorem palomarCachedModernDyadicNextTokenLogitError
    {modelDim vocabularySize p start : Nat}
    {layers : List ModernDecoderLayerParameters}
    {pref : Matrix ℝ} {x : Vector ℝ}
    {caches : ModernTransformerCache} {W : Matrix ℝ}
    (hwellformed : palomarModernStackWellFormed modelDim layers)
    (hvocabulary : 0 < vocabularySize)
    (hcache : modernTransformerCacheMatches layers start pref caches)
    (hmatrix : matrixShape modelDim vocabularySize W) :
    vectorErrorBound (modelDim * dyadicUnitRoundoff p)
      (nextTokenLogits vocabularySize W
        ((fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD
          ([] : Vector ℝ)))
      (dyadicNextTokenLogits p vocabularySize W
        (cachedModernDecoderStackStep layers (start + pref.length) x caches).1) := by
  exact cached_modern_dyadic_next_token_logit_error
    hwellformed.2.1 hcache hmatrix

end
end DecoderTransformer
