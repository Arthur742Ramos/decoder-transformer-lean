theory Tiny_Decoder_Checkpoint
  imports IEEE_754_Projection
begin

section \<open>A Concrete Executable Decoder Checkpoint\<close>

text \<open>
  This theory instantiates the parametric modern decoder with a deliberately
  small but complete checkpoint: one query head, one key-value head, model and
  head dimension two, hidden dimension two, identity RoPE, and zero attention
  and SwiGLU weights.  Residual connections therefore make the decoder layer
  exactly the identity.  A two-token embedding and vocabulary projection turn
  the development into an executable end-to-end inference example.
\<close>

definition tiny_zero_matrix :: "real matrix" where
  "tiny_zero_matrix = [[0, 0], [0, 0]]"

definition tiny_zero_tensor :: "real tensor3" where
  "tiny_zero_tensor = [tiny_zero_matrix]"

definition tiny_identity_matrix :: "real matrix" where
  "tiny_identity_matrix = [[1, 0], [0, 1]]"

definition tiny_embedding :: "nat \<Rightarrow> real vector" where
  "tiny_embedding token = (if token = 0 then [1, 0] else [0, 1])"

definition tiny_modern_layer :: modern_decoder_layer_parameters where
  "tiny_modern_layer =
    \<lparr>modern_query_head_count = 1,
     modern_kv_head_count = 1,
     modern_model_dimension = 2,
     modern_head_dimension = 2,
     modern_hidden_dimension = 2,
     modern_norm_epsilon = 1,
     modern_rope = (\<lambda>position x. x),
     modern_attention_gain = [1, 1],
     modern_mlp_gain = [1, 1],
     modern_query_weights = tiny_zero_tensor,
     modern_key_weights = tiny_zero_tensor,
     modern_value_weights = tiny_zero_tensor,
     modern_output_weights = tiny_zero_matrix,
     modern_gate_weights = tiny_zero_matrix,
     modern_up_weights = tiny_zero_matrix,
     modern_down_weights = tiny_zero_matrix\<rparr>"

definition tiny_modern_layers :: "modern_decoder_layer_parameters list" where
  "tiny_modern_layers = [tiny_modern_layer]"

lemma tiny_modern_layer_valid:
  "valid_modern_decoder_layer tiny_modern_layer"
  by (simp add: valid_modern_decoder_layer_def tiny_modern_layer_def
      tiny_zero_tensor_def tiny_zero_matrix_def vector_shape_def
      matrix_shape_def tensor3_shape_def)

lemma tiny_modern_stack_valid:
  "valid_modern_decoder_stack tiny_modern_layers"
  using tiny_modern_layer_valid
  by (simp add: tiny_modern_layers_def valid_modern_decoder_stack_def)

lemma tiny_dot_product_zero_two [simp]:
  "dot_product (x :: real vector) [0, 0] = 0"
proof (cases x)
  case Nil
  then show ?thesis by (simp add: dot_product_def)
next
  case (Cons a xs)
  have x: "x = a # xs" using Cons by simp
  then show ?thesis
  proof (cases xs)
    case Nil
    then show ?thesis using x by (simp add: dot_product_def)
  next
    case (Cons b ys)
    then show ?thesis using x by (simp add: dot_product_def)
  qed
qed

lemma tiny_zero_projection [simp]:
  "linear_project 2 tiny_zero_matrix (x :: real vector) = [0, 0]"
proof -
  have range: "[0..<2] = [0, 1]" by (simp add: upt_rec)
  show ?thesis
    by (simp add: linear_project_def matrix_columns_def
        tiny_zero_matrix_def range)
qed

lemma tiny_identity_projection [simp]:
  "linear_project 2 tiny_identity_matrix [a, b] = [a, b]"
proof -
  have range: "[0..<2] = [0, 1]" by (simp add: upt_rec)
  show ?thesis
    by (simp add: linear_project_def matrix_columns_def dot_product_def
        tiny_identity_matrix_def range)
qed

lemma tiny_grouped_attention_zero [simp]:
  "modern_grouped_attention_at_prefix tiny_modern_layer ix prefix = [0, 0]"
  by (simp add: modern_grouped_attention_at_prefix_def tiny_modern_layer_def)

lemma tiny_swiglu_zero [simp]:
  "swiglu 2 2 tiny_zero_matrix tiny_zero_matrix tiny_zero_matrix x = [0, 0]"
  by (simp add: swiglu_def gated_feed_forward_def)

theorem tiny_modern_decoder_identity:
  assumes "vector_shape 2 x"
  shows "modern_decoder_at_indexed_prefix tiny_modern_layer (position, x)
    prefix = x"
proof -
  have length: "length x = 2"
    using assms by (simp add: vector_shape_def)
  then obtain a xs where x_cons: "x = a # xs"
    by (cases x) auto
  then obtain b ys where xs_cons: "xs = b # ys"
    using length by (cases xs) auto
  have ys_empty: "ys = []"
    using length x_cons xs_cons by simp
  have x: "x = [a, b]"
    using x_cons xs_cons ys_empty by simp
  have attention:
    "modern_grouped_attention_at_prefix tiny_modern_layer (position, x)
      prefix = [0, 0]"
    by (rule tiny_grouped_attention_zero)
  show ?thesis
    unfolding modern_decoder_at_indexed_prefix_def Let_def
    using attention
    by (simp add: x tiny_modern_layer_def vector_add_def)
qed

theorem tiny_full_layer_identity:
  assumes shape: "matrix_shape seq_len 2 X"
  shows "full_modern_decoder_layer tiny_modern_layer start X = X"
proof -
  have rows: "\<forall>x \<in> set X. vector_shape 2 x"
    using shape by (auto simp: matrix_shape_def vector_shape_def)
  have identity:
    "\<And>Y. \<forall>y \<in> set Y. vector_shape 2 y \<Longrightarrow>
      full_modern_decoder_layer tiny_modern_layer start Y = Y"
  proof -
    fix Y :: "real matrix"
    assume Y: "\<forall>y \<in> set Y. vector_shape 2 y"
    show "full_modern_decoder_layer tiny_modern_layer start Y = Y"
      using Y
    proof (induction Y rule: rev_induct)
      case Nil
      then show ?case by simp
    next
      case (snoc y ys)
      have prefix: "full_modern_decoder_layer tiny_modern_layer start ys = ys"
        by (rule snoc.IH) (use snoc.prems in auto)
      have y_shape: "vector_shape 2 y"
        using snoc.prems by simp
      show ?case
        using prefix tiny_modern_decoder_identity[OF y_shape]
        by (simp add: full_modern_decoder_layer_append)
    qed
  qed
  show ?thesis by (rule identity[OF rows])
qed

theorem tiny_full_stack_identity:
  assumes "matrix_shape seq_len 2 X"
  shows "full_modern_decoder_stack tiny_modern_layers start X = X"
  using tiny_full_layer_identity[OF assms]
  by (simp add: tiny_modern_layers_def)

lemma tiny_embedding_shape [simp]:
  "vector_shape 2 (tiny_embedding token)"
  by (simp add: tiny_embedding_def vector_shape_def)

lemma tiny_vocabulary_shape:
  "matrix_shape 2 2 tiny_identity_matrix"
  by (simp add: tiny_identity_matrix_def matrix_shape_def)

theorem tiny_checkpoint_logits:
  "next_token_logits 2 tiny_identity_matrix
      (last (full_modern_decoder_stack tiny_modern_layers start
        (map tiny_embedding (tokens @ [token])))) = tiny_embedding token"
proof -
  have input_shape:
    "matrix_shape (length (tokens @ [token])) 2
      (map tiny_embedding (tokens @ [token]))"
    by (auto simp: matrix_shape_def tiny_embedding_def)
  have stack:
    "full_modern_decoder_stack tiny_modern_layers start
      (map tiny_embedding (tokens @ [token])) =
      map tiny_embedding (tokens @ [token])"
    by (rule tiny_full_stack_identity[OF input_shape])
  show ?thesis
    unfolding next_token_logits_def
    unfolding stack
    by (cases token) (simp_all add: tiny_embedding_def)
qed

theorem tiny_cached_prompt_outputs:
  "fst (cached_modern_decoder_stack_run tiny_modern_layers start
      (empty_modern_transformer_cache tiny_modern_layers)
      (map tiny_embedding tokens)) = map tiny_embedding tokens"
proof -
  have input_shape:
    "matrix_shape (length tokens) 2 (map tiny_embedding tokens)"
    by (auto simp: matrix_shape_def tiny_embedding_def)
  have exact:
    "full_modern_decoder_stack tiny_modern_layers start
        ([] @ map tiny_embedding tokens) =
      full_modern_decoder_stack tiny_modern_layers start [] @
        fst (cached_modern_decoder_stack_run tiny_modern_layers start
          (empty_modern_transformer_cache tiny_modern_layers)
          (map tiny_embedding tokens))"
    by (rule cached_modern_decoder_stack_run_correct(1)
        [OF tiny_modern_stack_valid
          empty_modern_transformer_cache_matches]) simp
  have full:
    "full_modern_decoder_stack tiny_modern_layers start
      (map tiny_embedding tokens) = map tiny_embedding tokens"
    by (rule tiny_full_stack_identity[OF input_shape])
  show ?thesis using exact full by simp
qed

theorem tiny_cached_prompt_certificate:
  "modern_transformer_cache_matches tiny_modern_layers start
    (map tiny_embedding tokens)
    (snd (cached_modern_decoder_stack_run tiny_modern_layers start
      (empty_modern_transformer_cache tiny_modern_layers)
      (map tiny_embedding tokens)))"
proof -
  have result:
    "modern_transformer_cache_matches tiny_modern_layers start
      ([] @ map tiny_embedding tokens)
      (snd (cached_modern_decoder_stack_run tiny_modern_layers start
        (empty_modern_transformer_cache tiny_modern_layers)
        (map tiny_embedding tokens)))"
    by (rule cached_modern_decoder_stack_run_correct(2)
        [where layers=tiny_modern_layers and start=start and prefix="[]"
          and caches="empty_modern_transformer_cache tiny_modern_layers"
          and position=start and xs="map tiny_embedding tokens",
          OF tiny_modern_stack_valid empty_modern_transformer_cache_matches])
       simp
  show ?thesis using result by simp
qed

theorem tiny_cached_prompt_execution:
  "fst (cached_modern_decoder_stack_run tiny_modern_layers start
      (empty_modern_transformer_cache tiny_modern_layers)
      (map tiny_embedding tokens)) = map tiny_embedding tokens \<and>
   modern_transformer_cache_matches tiny_modern_layers start
      (map tiny_embedding tokens)
      (snd (cached_modern_decoder_stack_run tiny_modern_layers start
        (empty_modern_transformer_cache tiny_modern_layers)
        (map tiny_embedding tokens)))"
  using tiny_cached_prompt_outputs tiny_cached_prompt_certificate by blast

theorem tiny_uniform_generation_distribution:
  "next_token_distribution 2 tiny_zero_matrix hidden = [1 / 2, 1 / 2]"
  by (simp add: next_token_distribution_def list_softmax_def
      softmax_denominator_def next_token_logits_def)

corollary tiny_uniform_generation_selects_zero:
  "first_argmax (next_token_distribution 2 tiny_zero_matrix hidden) = 0"
  by (simp add: tiny_uniform_generation_distribution)

theorem tiny_cached_next_token:
  assumes cache:
    "modern_generation_cache_matches tiny_embedding tiny_modern_layers start
      tokens caches"
  shows "first_argmax
    (fst (cached_modern_generation_evaluate tiny_modern_layers tiny_embedding
      start 2 tiny_zero_matrix tokens caches)) = 0"
proof -
  have nonempty: "tokens \<noteq> []"
    using cache by (simp add: modern_generation_cache_matches_def)
  show ?thesis
    using nonempty
    by (simp add: cached_modern_generation_evaluate_def Let_def
        tiny_uniform_generation_selects_zero)
qed

theorem tiny_generation_transition_appends_zero:
  assumes cache:
    "modern_generation_cache_matches tiny_embedding tiny_modern_layers start
      (fst state) (snd state)"
  shows "fst (modern_generation_transition first_argmax tiny_modern_layers
    tiny_embedding start 2 tiny_zero_matrix state) = fst state @ [0]"
proof -
  have selected:
    "first_argmax
      (fst (cached_modern_generation_evaluate tiny_modern_layers tiny_embedding
        start 2 tiny_zero_matrix (fst state) (snd state))) = 0"
    by (rule tiny_cached_next_token[OF cache])
  show ?thesis
    using selected
    by (simp add: modern_generation_transition_def deterministic_next_token_def
        Let_def)
qed

theorem tiny_generate_steps_tokens:
  assumes cache:
    "modern_generation_cache_matches tiny_embedding tiny_modern_layers start
      (fst state) (snd state)"
  shows "fst (modern_generate_steps n first_argmax tiny_modern_layers
    tiny_embedding start 2 tiny_zero_matrix state) =
    fst state @ replicate n 0"
  using cache
proof (induction n arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?next = "modern_generation_transition first_argmax tiny_modern_layers
    tiny_embedding start 2 tiny_zero_matrix state"
  have next_tokens: "fst ?next = fst state @ [0]"
    by (rule tiny_generation_transition_appends_zero[OF Suc.prems])
  have next_cache:
    "modern_generation_cache_matches tiny_embedding tiny_modern_layers start
      (fst ?next) (snd ?next)"
    by (rule modern_generation_transition_cache_invariant[OF Suc.prems])
  have tail:
    "fst (modern_generate_steps n first_argmax tiny_modern_layers tiny_embedding
      start 2 tiny_zero_matrix ?next) = fst ?next @ replicate n 0"
    by (rule Suc.IH[OF next_cache])
  show ?case
    using tail next_tokens by simp
qed

corollary tiny_initialized_generation_trace:
  assumes nonempty: "tokens \<noteq> []"
  shows "fst (modern_generate_steps n first_argmax tiny_modern_layers
      tiny_embedding start 2 tiny_zero_matrix
      (initialize_modern_generation_state tiny_modern_layers tiny_embedding
        start tokens)) = tokens @ replicate n 0"
proof -
  have cache:
    "modern_generation_cache_matches tiny_embedding tiny_modern_layers start
      (fst (initialize_modern_generation_state tiny_modern_layers tiny_embedding
        start tokens))
      (snd (initialize_modern_generation_state tiny_modern_layers tiny_embedding
        start tokens))"
    by (rule initialize_modern_generation_state_correct
        [OF tiny_modern_stack_valid nonempty])
  have trace:
    "fst (modern_generate_steps n first_argmax tiny_modern_layers
        tiny_embedding start 2 tiny_zero_matrix
        (initialize_modern_generation_state tiny_modern_layers tiny_embedding
          start tokens)) =
      fst (initialize_modern_generation_state tiny_modern_layers tiny_embedding
        start tokens) @ replicate n 0"
    by (rule tiny_generate_steps_tokens[OF cache])
  show ?thesis
    using trace by (simp add: initialize_modern_generation_state_def)
qed

corollary tiny_three_step_demo:
  "fst (modern_generate_steps 3 first_argmax tiny_modern_layers
      tiny_embedding 0 2 tiny_zero_matrix
      (initialize_modern_generation_state tiny_modern_layers tiny_embedding
        0 [1])) = [1, 0, 0, 0]"
proof -
  have trace:
    "fst (modern_generate_steps 3 first_argmax tiny_modern_layers
        tiny_embedding 0 2 tiny_zero_matrix
        (initialize_modern_generation_state tiny_modern_layers tiny_embedding
          0 [1])) = [1] @ replicate 3 0"
    by (rule tiny_initialized_generation_trace) simp
  have replicate: "replicate 3 (0 :: nat) = [0, 0, 0]"
  proof -
    have three: "(3 :: nat) = Suc (Suc (Suc 0))" by simp
    show ?thesis unfolding three by simp
  qed
  show ?thesis using trace replicate by simp
qed

end
