theory GPT_Neo_Tiny_Checkpoint
  imports GPT_Neo_Generation
begin

section \<open>Concrete GPT-Neo Model Fixture\<close>

text \<open>
  This is a deliberately small, fully shape-checked GPT-Neo fixture.  It is
  not trained-model data: the one-head, one-dimensional block has zero
  projections and a positive LayerNorm epsilon.  Its purpose is to exercise
  the model, bounded prompt-cache, and finite-generation interfaces with a
  concrete record rather than only abstract parameters.
\<close>

definition gpt_neo_tiny_zero_matrix :: "real matrix" where
  "gpt_neo_tiny_zero_matrix = [[0]]"

definition gpt_neo_tiny_zero_tensor :: "real tensor3" where
  "gpt_neo_tiny_zero_tensor = [[[0]]]"

definition gpt_neo_tiny_layer :: gpt_neo_layer_parameters where
  "gpt_neo_tiny_layer =
    \<lparr>gpt_neo_head_count = 1,
     gpt_neo_model_dimension = 1,
     gpt_neo_head_dimension = 1,
     gpt_neo_hidden_dimension = 1,
     gpt_neo_attention_window = 1,
     gpt_neo_norm_epsilon = 1,
     gpt_neo_ln1_gain = [1],
     gpt_neo_ln1_bias = [0],
     gpt_neo_ln2_gain = [1],
     gpt_neo_ln2_bias = [0],
     gpt_neo_query_weights = gpt_neo_tiny_zero_tensor,
     gpt_neo_key_weights = gpt_neo_tiny_zero_tensor,
     gpt_neo_value_weights = gpt_neo_tiny_zero_tensor,
     gpt_neo_output_weights = gpt_neo_tiny_zero_matrix,
     gpt_neo_output_bias = [0],
     gpt_neo_fc_weights = gpt_neo_tiny_zero_matrix,
     gpt_neo_fc_bias = [0],
     gpt_neo_projection_weights = gpt_neo_tiny_zero_matrix,
     gpt_neo_projection_bias = [0]\<rparr>"

definition gpt_neo_tiny_model :: gpt_neo_model_parameters where
  "gpt_neo_tiny_model =
    \<lparr>gpt_neo_model_layers = [gpt_neo_tiny_layer],
     gpt_neo_model_hidden_size = 1,
     gpt_neo_model_vocabulary_size = 2,
     gpt_neo_model_max_position = 4,
     gpt_neo_model_norm_epsilon = 1,
     gpt_neo_model_token_embeddings = [[0], [1]],
     gpt_neo_model_position_embeddings = [[0], [0], [0], [0]],
     gpt_neo_model_final_gain = [1],
     gpt_neo_model_final_bias = [0],
     gpt_neo_model_vocabulary_weights = [[0, 1]]\<rparr>"

lemma gpt_neo_tiny_layer_valid:
  "valid_gpt_neo_layer gpt_neo_tiny_layer"
  by (simp add: valid_gpt_neo_layer_def gpt_neo_tiny_layer_def
      gpt_neo_tiny_zero_tensor_def gpt_neo_tiny_zero_matrix_def
      vector_shape_def matrix_shape_def tensor3_shape_def
      multi_head_parameters_shape_def)

lemma gpt_neo_tiny_model_valid:
  "valid_gpt_neo_model gpt_neo_tiny_model"
  using gpt_neo_tiny_layer_valid
  by (simp add: valid_gpt_neo_model_def gpt_neo_tiny_model_def
      gpt_neo_tiny_layer_def gpt_neo_tiny_zero_tensor_def
      gpt_neo_tiny_zero_matrix_def vector_shape_def matrix_shape_def
      tensor3_shape_def multi_head_parameters_shape_def
      gpt_neo_stack_compatible_def valid_gpt_neo_stack_def)

lemma gpt_neo_tiny_token_bounds:
  "\<forall>token \<in> set [1]. token <
    gpt_neo_model_vocabulary_size gpt_neo_tiny_model"
  by (simp add: gpt_neo_tiny_model_def)

lemma gpt_neo_tiny_position_bound:
  "0 + length [1] \<le> gpt_neo_model_max_position gpt_neo_tiny_model"
  by (simp add: gpt_neo_tiny_model_def)

theorem gpt_neo_tiny_prompt_cache_refinement:
  "fst (gpt_neo_cached_prompt gpt_neo_tiny_model 0 [1]) =
      gpt_neo_full_hidden gpt_neo_tiny_model 0 [1] \<and>
   gpt_neo_model_cache_matches gpt_neo_tiny_model 0 [1]
      (snd (gpt_neo_cached_prompt gpt_neo_tiny_model 0 [1]))"
  by (rule conjI;
    rule gpt_neo_cached_prompt_correct[
      OF gpt_neo_tiny_model_valid gpt_neo_tiny_token_bounds
        gpt_neo_tiny_position_bound])

theorem gpt_neo_tiny_bounded_prompt_cache_refinement:
  "fst (gpt_neo_bounded_cached_prompt gpt_neo_tiny_model 0 [1]) =
      gpt_neo_full_hidden gpt_neo_tiny_model 0 [1] \<and>
   gpt_neo_bounded_model_cache_matches gpt_neo_tiny_model 0 [1]
      (snd (gpt_neo_bounded_cached_prompt gpt_neo_tiny_model 0 [1]))"
  by (rule conjI;
    rule gpt_neo_bounded_cached_prompt_correct[
      OF gpt_neo_tiny_model_valid gpt_neo_tiny_token_bounds
        gpt_neo_tiny_position_bound])

theorem gpt_neo_tiny_bounded_generation_initialization:
  "gpt_neo_bounded_generation_state_valid gpt_neo_tiny_model 0
    (gpt_neo_bounded_initialized_generation_state
      gpt_neo_tiny_model 0 [1])"
  by (rule gpt_neo_bounded_initialized_generation_state_valid[
    OF gpt_neo_tiny_model_valid])
    (simp_all add: gpt_neo_tiny_model_def)

theorem gpt_neo_tiny_bounded_one_step:
  "gpt_neo_bounded_generation_state_valid gpt_neo_tiny_model 0
    (gpt_neo_bounded_generate_steps 1 first_argmax
      gpt_neo_tiny_model 0
      (gpt_neo_bounded_initialized_generation_state
        gpt_neo_tiny_model 0 [1]))"
  by (rule gpt_neo_bounded_greedy_generate_steps_valid[
    OF gpt_neo_tiny_bounded_generation_initialization])
    (simp add: gpt_neo_tiny_model_def
      gpt_neo_bounded_initialized_generation_state_def)

end
