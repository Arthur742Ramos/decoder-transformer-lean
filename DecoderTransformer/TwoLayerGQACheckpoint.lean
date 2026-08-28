import DecoderTransformer.TinyDecoderCheckpoint
import Mathlib.Tactic

namespace DecoderTransformer
namespace TwoLayerGQACheckpoint

noncomputable section

/-!
# Two-layer GQA, RoPE, and SwiGLU checkpoint

This is the Lean counterpart of the generated
`Two_Layer_GQA_Checkpoint.thy` fixture.  It keeps the concrete two-layer,
two-query-head/one-KV-head parameters and the nonzero pairwise rotation
angles, while retaining the exact cache/generation certificates from the
parametric development.
-/

def imported_embedding_rows : Matrix ℝ := [[1, 0, 0, 0], [0, 1, 1, 0]]

def imported_embedding (token : Nat) : Vector ℝ :=
  imported_embedding_rows.getD token []

def imported_vocabulary_weights : Matrix ℝ :=
  [[1, 0], [0, 1], [0, 1], [1, 0]]

def imported_layer0_query_weights : Tensor3 ℝ :=
  [[[1, 0], [0, 1], [1, 1], [1, -1]],
   [[1, 1], [1, -1], [0, 1], [1, 0]]]

def imported_layer0_key_weights : Tensor3 ℝ :=
  [[[1, 0], [0, 1], [1, 0], [0, 1]]]

def imported_layer0_value_weights : Tensor3 ℝ :=
  [[[1, 0], [0, 1], [1, 1], [1, -1]]]

def imported_layer0_output_weights : Matrix ℝ :=
  [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

def imported_layer0_gate_weights : Matrix ℝ :=
  [[1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1], [1, 0, 0, 1]]

def imported_layer0_up_weights : Matrix ℝ :=
  [[1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1]]

def imported_layer0_down_weights : Matrix ℝ :=
  [[1, 0, 0, 1], [0, 1, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1]]

def imported_layer0_attention_gain : Vector ℝ := [1, 1, 1, 1]

def imported_layer0_mlp_gain : Vector ℝ := [1, 1, 1, 1]

def imported_layer0_rope_angle_table : Vector ℝ := [0.5]

def imported_layer0_angles (_pair _position : Nat) : ℝ :=
  imported_layer0_rope_angle_table.getD 0 0

def imported_layer0 : ModernDecoderLayerParameters where
  queryHeadCount := 2
  kvHeadCount := 1
  modelDim := 4
  headDim := 2
  hiddenDim := 4
  normEpsilon := 1
  rope := ropeRotate imported_layer0_angles
  attentionGain := imported_layer0_attention_gain
  mlpGain := imported_layer0_mlp_gain
  queryWeights := imported_layer0_query_weights
  keyWeights := imported_layer0_key_weights
  valueWeights := imported_layer0_value_weights
  outputWeights := imported_layer0_output_weights
  gateWeights := imported_layer0_gate_weights
  upWeights := imported_layer0_up_weights
  downWeights := imported_layer0_down_weights

def imported_layer1_query_weights : Tensor3 ℝ :=
  [[[1, -1], [1, 1], [0, 1], [1, 0]],
   [[1, 0], [0, 1], [1, -1], [1, 1]]]

def imported_layer1_key_weights : Tensor3 ℝ :=
  [[[1, 1], [1, -1], [0, 1], [1, 0]]]

def imported_layer1_value_weights : Tensor3 ℝ :=
  [[[1, 1], [1, -1], [1, 0], [0, 1]]]

def imported_layer1_output_weights : Matrix ℝ :=
  [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

def imported_layer1_gate_weights : Matrix ℝ :=
  [[1, 0, 1, 0], [0, 1, 0, 1], [1, 1, 0, 0], [0, 0, 1, 1]]

def imported_layer1_up_weights : Matrix ℝ :=
  [[1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1], [1, 0, 0, 1]]

def imported_layer1_down_weights : Matrix ℝ :=
  [[1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1]]

def imported_layer1_attention_gain : Vector ℝ := [1, 1, 1, 1]

def imported_layer1_mlp_gain : Vector ℝ := [1, 1, 1, 1]

def imported_layer1_rope_angle_table : Vector ℝ := [-0.3333333333333333]

def imported_layer1_angles (_pair _position : Nat) : ℝ :=
  imported_layer1_rope_angle_table.getD 0 0

def imported_layer1 : ModernDecoderLayerParameters where
  queryHeadCount := 2
  kvHeadCount := 1
  modelDim := 4
  headDim := 2
  hiddenDim := 4
  normEpsilon := 1
  rope := ropeRotate imported_layer1_angles
  attentionGain := imported_layer1_attention_gain
  mlpGain := imported_layer1_mlp_gain
  queryWeights := imported_layer1_query_weights
  keyWeights := imported_layer1_key_weights
  valueWeights := imported_layer1_value_weights
  outputWeights := imported_layer1_output_weights
  gateWeights := imported_layer1_gate_weights
  upWeights := imported_layer1_up_weights
  downWeights := imported_layer1_down_weights

def imported_modern_layers : List ModernDecoderLayerParameters :=
  [imported_layer0, imported_layer1]

lemma imported_layer0_valid : validModernDecoderLayer imported_layer0 := by
  have hrope : ∀ position x, vectorShape 2 x →
      vectorShape 2 (ropeRotate imported_layer0_angles position x) := by
    intro position x hx
    exact ropeRotate_preservesShape hx
  simp [validModernDecoderLayer, imported_layer0, imported_layer0_attention_gain,
    imported_layer0_mlp_gain, imported_layer0_query_weights,
    imported_layer0_key_weights, imported_layer0_value_weights,
    imported_layer0_output_weights, imported_layer0_gate_weights,
    imported_layer0_up_weights, imported_layer0_down_weights, vectorShape,
    matrixShape, tensor3Shape, groupedQueryParametersShape]
  intro position x hx
  simpa [vectorShape] using ropeRotate_preservesShape hx

lemma imported_layer1_valid : validModernDecoderLayer imported_layer1 := by
  have hrope : ∀ position x, vectorShape 2 x →
      vectorShape 2 (ropeRotate imported_layer1_angles position x) := by
    intro position x hx
    exact ropeRotate_preservesShape hx
  simp [validModernDecoderLayer, imported_layer1, imported_layer1_attention_gain,
    imported_layer1_mlp_gain, imported_layer1_query_weights,
    imported_layer1_key_weights, imported_layer1_value_weights,
    imported_layer1_output_weights, imported_layer1_gate_weights,
    imported_layer1_up_weights, imported_layer1_down_weights, vectorShape,
    matrixShape, tensor3Shape, groupedQueryParametersShape]
  intro position x hx
  simpa [vectorShape] using ropeRotate_preservesShape hx

lemma imported_modern_stack_valid : validModernStack imported_modern_layers := by
  intro p hp
  simp [imported_modern_layers] at hp
  rcases hp with rfl | rfl
  · exact imported_layer0_valid
  · exact imported_layer1_valid

lemma imported_gqa_grouping :
    groupedQueryHeadIndex 4 2 0 = 0 ∧
    groupedQueryHeadIndex 4 2 1 = 0 ∧
    groupedQueryHeadIndex 4 2 2 = 1 ∧
    groupedQueryHeadIndex 4 2 3 = 1 := by
  norm_num [groupedQueryHeadIndex]

lemma imported_embedding_shape :
    matrixShape 2 4 imported_embedding_rows := by
  simp [imported_embedding_rows, matrixShape]

lemma imported_vocabulary_shape :
    matrixShape 4 2 imported_vocabulary_weights := by
  simp [imported_vocabulary_weights, matrixShape]

lemma imported_layer0_rope_angle :
    imported_layer0_angles 0 0 = 1 / 2 := by
  norm_num [imported_layer0_angles, imported_layer0_rope_angle_table]

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
end TwoLayerGQACheckpoint
end DecoderTransformer
