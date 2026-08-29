(* Generated deterministically by tools/import_multilayer_checkpoint.py. *)
(* Source: two_layer_gqa_rope_swiglu.json; provenance: synthetic deterministic two-layer integration fixture *)

theory Two_Layer_GQA_Checkpoint
  imports Tiny_Decoder_Checkpoint
begin

section \<open>Two-layer GQA, RoPE, and SwiGLU checkpoint\<close>

text \<open>
  This generated theory is a deterministic integration fixture.  It
  has two modern layers, two query heads sharing one key-value head,
  explicit nonzero SwiGLU matrices, and nonzero pairwise RoPE angles.
  The fixture is synthetic and carries no trained-model provenance.
\<close>

definition imported_embedding_rows :: "real matrix" where
  "imported_embedding_rows = [[1, 0, 0, 0], [0, 1, 1, 0]]"
definition imported_embedding :: "nat \<Rightarrow> real vector" where
  "imported_embedding = (\<lambda>token. if token < length imported_embedding_rows then
      imported_embedding_rows ! token else [])"
definition imported_vocabulary_weights :: "real matrix" where
  "imported_vocabulary_weights = [[1, 0], [0, 1], [0, 1], [1, 0]]"
definition imported_layer0_query_weights :: "real tensor3" where
  "imported_layer0_query_weights = [[[1, 0], [0, 1], [1, 1], [1, -1]], [[1, 1], [1, -1], [0, 1], [1, 0]]]"

definition imported_layer0_key_weights :: "real tensor3" where
  "imported_layer0_key_weights = [[[1, 0], [0, 1], [1, 0], [0, 1]]]"

definition imported_layer0_value_weights :: "real tensor3" where
  "imported_layer0_value_weights = [[[1, 0], [0, 1], [1, 1], [1, -1]]]"

definition imported_layer0_output_weights :: "real matrix" where
  "imported_layer0_output_weights = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]"

definition imported_layer0_gate_weights :: "real matrix" where
  "imported_layer0_gate_weights = [[1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1], [1, 0, 0, 1]]"

definition imported_layer0_up_weights :: "real matrix" where
  "imported_layer0_up_weights = [[1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1]]"

definition imported_layer0_down_weights :: "real matrix" where
  "imported_layer0_down_weights = [[1, 0, 0, 1], [0, 1, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1]]"

definition imported_layer0_attention_gain :: "real vector" where
  "imported_layer0_attention_gain = [1, 1, 1, 1]"

definition imported_layer0_mlp_gain :: "real vector" where
  "imported_layer0_mlp_gain = [1, 1, 1, 1]"

definition imported_layer0_rope_angle_table :: "real vector" where
  "imported_layer0_rope_angle_table = [0.5]"

definition imported_layer0_angles :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "imported_layer0_angles pair position =
    (if pair < length imported_layer0_rope_angle_table
     then imported_layer0_rope_angle_table ! pair else 0)"

definition imported_layer0 :: modern_decoder_layer_parameters where
  "imported_layer0 =
    \<lparr>modern_query_head_count = 2,
      modern_kv_head_count = 1,
      modern_model_dimension = 4,
      modern_head_dimension = 2,
      modern_hidden_dimension = 4,
      modern_norm_epsilon = 1,
      modern_rope = rope_rotate imported_layer0_angles,
      modern_attention_gain = imported_layer0_attention_gain,
      modern_mlp_gain = imported_layer0_mlp_gain,
      modern_query_weights = imported_layer0_query_weights,
      modern_key_weights = imported_layer0_key_weights,
      modern_value_weights = imported_layer0_value_weights,
      modern_output_weights = imported_layer0_output_weights,
      modern_gate_weights = imported_layer0_gate_weights,
      modern_up_weights = imported_layer0_up_weights,
      modern_down_weights = imported_layer0_down_weights\<rparr>"

definition imported_layer1_query_weights :: "real tensor3" where
  "imported_layer1_query_weights = [[[1, -1], [1, 1], [0, 1], [1, 0]], [[1, 0], [0, 1], [1, -1], [1, 1]]]"

definition imported_layer1_key_weights :: "real tensor3" where
  "imported_layer1_key_weights = [[[1, 1], [1, -1], [0, 1], [1, 0]]]"

definition imported_layer1_value_weights :: "real tensor3" where
  "imported_layer1_value_weights = [[[1, 1], [1, -1], [1, 0], [0, 1]]]"

definition imported_layer1_output_weights :: "real matrix" where
  "imported_layer1_output_weights = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]"

definition imported_layer1_gate_weights :: "real matrix" where
  "imported_layer1_gate_weights = [[1, 0, 1, 0], [0, 1, 0, 1], [1, 1, 0, 0], [0, 0, 1, 1]]"

definition imported_layer1_up_weights :: "real matrix" where
  "imported_layer1_up_weights = [[1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1], [1, 0, 0, 1]]"

definition imported_layer1_down_weights :: "real matrix" where
  "imported_layer1_down_weights = [[1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1]]"

definition imported_layer1_attention_gain :: "real vector" where
  "imported_layer1_attention_gain = [1, 1, 1, 1]"

definition imported_layer1_mlp_gain :: "real vector" where
  "imported_layer1_mlp_gain = [1, 1, 1, 1]"

definition imported_layer1_rope_angle_table :: "real vector" where
  "imported_layer1_rope_angle_table = [-0.3333333333333333]"

definition imported_layer1_angles :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "imported_layer1_angles pair position =
    (if pair < length imported_layer1_rope_angle_table
     then imported_layer1_rope_angle_table ! pair else 0)"

definition imported_layer1 :: modern_decoder_layer_parameters where
  "imported_layer1 =
    \<lparr>modern_query_head_count = 2,
      modern_kv_head_count = 1,
      modern_model_dimension = 4,
      modern_head_dimension = 2,
      modern_hidden_dimension = 4,
      modern_norm_epsilon = 1,
      modern_rope = rope_rotate imported_layer1_angles,
      modern_attention_gain = imported_layer1_attention_gain,
      modern_mlp_gain = imported_layer1_mlp_gain,
      modern_query_weights = imported_layer1_query_weights,
      modern_key_weights = imported_layer1_key_weights,
      modern_value_weights = imported_layer1_value_weights,
      modern_output_weights = imported_layer1_output_weights,
      modern_gate_weights = imported_layer1_gate_weights,
      modern_up_weights = imported_layer1_up_weights,
      modern_down_weights = imported_layer1_down_weights\<rparr>"
definition imported_modern_layers :: "modern_decoder_layer_parameters list" where
  "imported_modern_layers = [imported_layer0, imported_layer1]"

lemma imported_layer0_valid:
  "valid_modern_decoder_layer imported_layer0"
proof -
  have rope_shape:
    "\<forall>position x. vector_shape 2 x \<longrightarrow>
      vector_shape 2
        (rope_rotate imported_layer0_angles position x)"
    by (intro allI impI; rule rope_rotate_preserves_shape)
  show ?thesis
    unfolding valid_modern_decoder_layer_def imported_layer0_def
      imported_layer0_attention_gain_def imported_layer0_mlp_gain_def imported_layer0_query_weights_def imported_layer0_key_weights_def imported_layer0_value_weights_def imported_layer0_output_weights_def imported_layer0_gate_weights_def imported_layer0_up_weights_def imported_layer0_down_weights_def
    using rope_shape
    by (simp add: vector_shape_def matrix_shape_def tensor3_shape_def)
qed

lemma imported_layer1_valid:
  "valid_modern_decoder_layer imported_layer1"
proof -
  have rope_shape:
    "\<forall>position x. vector_shape 2 x \<longrightarrow>
      vector_shape 2
        (rope_rotate imported_layer1_angles position x)"
    by (intro allI impI; rule rope_rotate_preserves_shape)
  show ?thesis
    unfolding valid_modern_decoder_layer_def imported_layer1_def
      imported_layer1_attention_gain_def imported_layer1_mlp_gain_def imported_layer1_query_weights_def imported_layer1_key_weights_def imported_layer1_value_weights_def imported_layer1_output_weights_def imported_layer1_gate_weights_def imported_layer1_up_weights_def imported_layer1_down_weights_def
    using rope_shape
    by (simp add: vector_shape_def matrix_shape_def tensor3_shape_def)
qed

lemma imported_modern_stack_valid:
  "valid_modern_decoder_stack imported_modern_layers"
  using imported_layer0_valid imported_layer1_valid
  by (simp add: imported_modern_layers_def valid_modern_decoder_stack_def)

lemma imported_gqa_grouping:
  "grouped_query_head_index 4 2 0 = 0 \<and>
   grouped_query_head_index 4 2 1 = 0 \<and>
   grouped_query_head_index 4 2 2 = 1 \<and>
   grouped_query_head_index 4 2 3 = 1"
  by (simp add: grouped_query_head_index_def)

lemma imported_embedding_shape:
  "matrix_shape 2 4 imported_embedding_rows"
  by (simp add: imported_embedding_rows_def matrix_shape_def)

lemma imported_vocabulary_shape:
  "matrix_shape 4 2 imported_vocabulary_weights"
  by (simp add: imported_vocabulary_weights_def matrix_shape_def)

lemma imported_layer0_rope_angle:
  "imported_layer0_angles 0 0 = 1 / 2"
  by (simp add: imported_layer0_angles_def imported_layer0_rope_angle_table_def)

theorem imported_cached_prompt_refinement:
  "fst (cached_modern_decoder_stack_run imported_modern_layers start
      (empty_modern_transformer_cache imported_modern_layers)
      (map imported_embedding tokens)) =
    full_modern_decoder_stack imported_modern_layers start
      (map imported_embedding tokens)"
  by (rule initialized_modern_cached_run_equals_full
      [OF imported_modern_stack_valid])

theorem imported_cached_prompt_cache:
  "modern_transformer_cache_matches imported_modern_layers start
      (map imported_embedding tokens)
      (snd (cached_modern_decoder_stack_run imported_modern_layers start
        (empty_modern_transformer_cache imported_modern_layers)
        (map imported_embedding tokens)))"
  by (rule initialized_modern_cached_run_cache_invariant
      [OF imported_modern_stack_valid])

theorem imported_cached_next_token_refinement:
  assumes cache:
    "modern_generation_cache_matches imported_embedding
      imported_modern_layers start tokens caches"
  shows "fst (cached_modern_generation_evaluate imported_modern_layers
      imported_embedding start 2 imported_vocabulary_weights tokens caches) =
    next_token_distribution 2 imported_vocabulary_weights
      (last (full_modern_decoder_stack imported_modern_layers start
        (map imported_embedding tokens)))"
  by (rule cached_modern_next_token_distribution_correct[OF cache])

theorem imported_initialized_generation_state_valid:
  assumes nonempty: "tokens \<noteq> []"
  shows "modern_generation_cache_matches imported_embedding
      imported_modern_layers start
      (fst (initialize_modern_generation_state imported_modern_layers
        imported_embedding start tokens))
      (snd (initialize_modern_generation_state imported_modern_layers
        imported_embedding start tokens))"
  by (rule initialize_modern_generation_state_correct
      [OF imported_modern_stack_valid nonempty])

end
