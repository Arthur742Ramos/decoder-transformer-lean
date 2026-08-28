import DecoderTransformer.TinyDecoderCheckpoint
import Mathlib.Tactic

namespace DecoderTransformer
namespace ImportedDecoderCheckpoint

noncomputable section

/-!
# Imported nonzero checkpoint

This is the Lean counterpart of the generated `Imported_Decoder_Checkpoint`
fixture.  The values are synthetic, shape checked, and intentionally use
identity RoPE rather than claiming to be trained-model parameters.
-/

def imported_query_weights : Tensor3 ℝ := [[[1, 0], [0, 1]]]

def imported_key_weights : Tensor3 ℝ := [[[1, 0], [0, 1]]]

def imported_value_weights : Tensor3 ℝ := [[[1, 0], [0, 1]]]

def imported_output_weights : Matrix ℝ := [[1, 0], [0, 1]]

def imported_gate_weights : Matrix ℝ := [[1, 0], [0, 1]]

def imported_up_weights : Matrix ℝ := [[1, 0], [0, 1]]

def imported_down_weights : Matrix ℝ := [[1, 0], [0, 1]]

def imported_attention_gain : Vector ℝ := [1, 1]

def imported_mlp_gain : Vector ℝ := [1, 1]

def imported_embedding_rows : Matrix ℝ := [[1, 0], [0, 1]]

def imported_embedding (token : Nat) : Vector ℝ :=
  imported_embedding_rows.getD token []

def imported_vocabulary_weights : Matrix ℝ := [[1, 0], [0, 1]]

def imported_modern_layer : ModernDecoderLayerParameters where
  queryHeadCount := 1
  kvHeadCount := 1
  modelDim := 2
  headDim := 2
  hiddenDim := 2
  normEpsilon := 1
  rope := fun _ x => x
  attentionGain := imported_attention_gain
  mlpGain := imported_mlp_gain
  queryWeights := imported_query_weights
  keyWeights := imported_key_weights
  valueWeights := imported_value_weights
  outputWeights := imported_output_weights
  gateWeights := imported_gate_weights
  upWeights := imported_up_weights
  downWeights := imported_down_weights

def imported_modern_layers : List ModernDecoderLayerParameters :=
  [imported_modern_layer]

lemma imported_modern_layer_valid :
    validModernDecoderLayer imported_modern_layer := by
  simp [validModernDecoderLayer, imported_modern_layer,
    imported_attention_gain, imported_mlp_gain, imported_query_weights,
    imported_key_weights, imported_value_weights, imported_output_weights,
    imported_gate_weights, imported_up_weights, imported_down_weights,
    vectorShape, matrixShape, tensor3Shape, groupedQueryParametersShape]

lemma imported_modern_stack_valid : validModernStack imported_modern_layers := by
  intro p hp
  simp only [imported_modern_layers, List.mem_singleton] at hp
  simpa [hp] using imported_modern_layer_valid

lemma imported_embedding_rows_shape :
    matrixShape 2 2 imported_embedding_rows := by
  simp [imported_embedding_rows, matrixShape]

lemma imported_embedding_zero : imported_embedding 0 = [1, 0] := by
  simp [imported_embedding, imported_embedding_rows]

lemma imported_embedding_one : imported_embedding 1 = [0, 1] := by
  simp [imported_embedding, imported_embedding_rows]

lemma imported_vocabulary_weights_shape :
    matrixShape 2 2 imported_vocabulary_weights := by
  simp [imported_vocabulary_weights, matrixShape]

lemma imported_checkpoint_has_nonzero_weights :
    imported_query_weights ≠ [[[0, 0], [0, 0]]] ∧
    imported_key_weights ≠ [[[0, 0], [0, 0]]] ∧
    imported_value_weights ≠ [[[0, 0], [0, 0]]] ∧
    imported_output_weights ≠ [[0, 0], [0, 0]] ∧
    imported_gate_weights ≠ [[0, 0], [0, 0]] ∧
    imported_up_weights ≠ [[0, 0], [0, 0]] ∧
    imported_down_weights ≠ [[0, 0], [0, 0]] := by
  simp [imported_query_weights, imported_key_weights,
    imported_value_weights, imported_output_weights,
    imported_gate_weights, imported_up_weights, imported_down_weights]

theorem imported_cached_prompt_refinement (start : Nat) (tokens : List Nat) :
    (cachedModernDecoderStackRun imported_modern_layers start
      (emptyModernTransformerCache imported_modern_layers)
      (tokens.map imported_embedding)).1 =
      fullModernDecoderStack imported_modern_layers start
        (tokens.map imported_embedding) := by
  exact initializedModernCachedRun_equalsFull imported_modern_stack_valid start
    (tokens.map imported_embedding)

theorem imported_cached_prompt_cache (start : Nat) (tokens : List Nat) :
    modernTransformerCacheMatches imported_modern_layers start
      (tokens.map imported_embedding)
      (cachedModernDecoderStackRun imported_modern_layers start
        (emptyModernTransformerCache imported_modern_layers)
        (tokens.map imported_embedding)).2 := by
  exact initializedModernCachedRun_cacheInvariant imported_modern_stack_valid
    start (tokens.map imported_embedding)

theorem imported_cached_next_token_refinement {start : Nat} {tokens : List Nat}
    {caches : ModernTransformerCache}
    (hcache : modernGenerationCacheMatches imported_embedding
      imported_modern_layers start tokens caches) :
    (cachedModernGenerationEvaluate imported_modern_layers imported_embedding
      start 2 imported_vocabulary_weights tokens caches).1 =
      nextTokenDistribution 2 imported_vocabulary_weights
        ((fullModernDecoderStack imported_modern_layers start
          (tokens.map imported_embedding)).getLast?.getD ([] : Vector ℝ)) := by
  exact cachedModernNextTokenDistributionCorrect
    (vocabularySize := 2) (vocabularyWeights := imported_vocabulary_weights)
    hcache

theorem imported_initialized_generation_state_valid {start : Nat}
    {tokens : List Nat} (hne : tokens ≠ []) :
    modernGenerationCacheMatches imported_embedding imported_modern_layers start
      (initializeModernGenerationState imported_modern_layers imported_embedding
        start tokens).1
      (initializeModernGenerationState imported_modern_layers imported_embedding
        start tokens).2 := by
  exact initializeModernGenerationState_correct imported_modern_stack_valid hne

end
end ImportedDecoderCheckpoint
end DecoderTransformer
