(* Generated deterministically by tools/import_decoder_checkpoint.py. *)
(* Source: nonzero_tiny_decoder.json; provenance: synthetic deterministic fixture for importer validation *)

theory Imported_Decoder_Checkpoint
  imports Tiny_Decoder_Checkpoint
begin

section \<open>Imported nonzero checkpoint\<close>

text \<open>
  This theory is generated from a shape-checked JSON fixture.  The
  fixture is intentionally synthetic rather than a claim about a
  trained model; every listed projection is nonzero and RoPE is the
  explicit identity convention of this importer format.
\<close>

definition imported_query_weights :: "real tensor3" where
  "imported_query_weights = [[[1, 0], [0, 1]]]"

definition imported_key_weights :: "real tensor3" where
  "imported_key_weights = [[[1, 0], [0, 1]]]"

definition imported_value_weights :: "real tensor3" where
  "imported_value_weights = [[[1, 0], [0, 1]]]"

definition imported_output_weights :: "real matrix" where
  "imported_output_weights = [[1, 0], [0, 1]]"

definition imported_gate_weights :: "real matrix" where
  "imported_gate_weights = [[1, 0], [0, 1]]"

definition imported_up_weights :: "real matrix" where
  "imported_up_weights = [[1, 0], [0, 1]]"

definition imported_down_weights :: "real matrix" where
  "imported_down_weights = [[1, 0], [0, 1]]"

definition imported_attention_gain :: "real vector" where
  "imported_attention_gain = [1, 1]"

definition imported_mlp_gain :: "real vector" where
  "imported_mlp_gain = [1, 1]"

definition imported_embedding_rows :: "real matrix" where
  "imported_embedding_rows = [[1, 0], [0, 1]]"

definition imported_embedding :: "nat \<Rightarrow> real vector" where
  "imported_embedding token =
    (if token < length imported_embedding_rows
     then imported_embedding_rows ! token else [])"

definition imported_vocabulary_weights :: "real matrix" where
  "imported_vocabulary_weights = [[1, 0], [0, 1]]"

definition imported_modern_layer :: modern_decoder_layer_parameters where
  "imported_modern_layer =
    \<lparr>modern_query_head_count = 1,
      modern_kv_head_count = 1,
      modern_model_dimension = 2,
      modern_head_dimension = 2,
      modern_hidden_dimension = 2,
      modern_norm_epsilon = 1,
      modern_rope = (\<lambda>position x. x),
      modern_attention_gain = imported_attention_gain,
      modern_mlp_gain = imported_mlp_gain,
      modern_query_weights = imported_query_weights,
      modern_key_weights = imported_key_weights,
      modern_value_weights = imported_value_weights,
      modern_output_weights = imported_output_weights,
      modern_gate_weights = imported_gate_weights,
      modern_up_weights = imported_up_weights,
      modern_down_weights = imported_down_weights\<rparr>"

definition imported_modern_layers :: "modern_decoder_layer_parameters list" where
  "imported_modern_layers = [imported_modern_layer]"

lemma imported_modern_layer_valid:
  "valid_modern_decoder_layer imported_modern_layer"
  by (simp add: valid_modern_decoder_layer_def imported_modern_layer_def
      imported_attention_gain_def imported_mlp_gain_def
      imported_query_weights_def imported_key_weights_def
      imported_value_weights_def imported_output_weights_def
      imported_gate_weights_def imported_up_weights_def
      imported_down_weights_def vector_shape_def matrix_shape_def
      tensor3_shape_def)

lemma imported_modern_stack_valid:
  "valid_modern_decoder_stack imported_modern_layers"
  using imported_modern_layer_valid
  by (simp add: imported_modern_layers_def valid_modern_decoder_stack_def)

lemma imported_embedding_rows_shape:
  "matrix_shape 2 2 imported_embedding_rows"
  by (simp add: imported_embedding_rows_def matrix_shape_def)

lemma imported_embedding_zero [simp]:
  "imported_embedding 0 = [1, 0]"
  by (simp add: imported_embedding_def imported_embedding_rows_def)

lemma imported_embedding_one [simp]:
  "imported_embedding 1 = [0, 1]"
  by (simp add: imported_embedding_def imported_embedding_rows_def)

lemma imported_vocabulary_weights_shape:
  "matrix_shape 2 2 imported_vocabulary_weights"
  by (simp add: imported_vocabulary_weights_def matrix_shape_def)

lemma imported_checkpoint_has_nonzero_weights:
  "imported_query_weights \<noteq> [[[0, 0], [0, 0]]] \<and>
   imported_key_weights \<noteq> [[[0, 0], [0, 0]]] \<and>
   imported_value_weights \<noteq> [[[0, 0], [0, 0]]] \<and>
   imported_output_weights \<noteq> [[0, 0], [0, 0]] \<and>
   imported_gate_weights \<noteq> [[0, 0], [0, 0]] \<and>
   imported_up_weights \<noteq> [[0, 0], [0, 0]] \<and>
   imported_down_weights \<noteq> [[0, 0], [0, 0]]"
  by (simp add: imported_query_weights_def imported_key_weights_def
      imported_value_weights_def imported_output_weights_def
      imported_gate_weights_def imported_up_weights_def
      imported_down_weights_def)

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
