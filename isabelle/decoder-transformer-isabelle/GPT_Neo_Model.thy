theory GPT_Neo_Model
  imports GPT_Neo_Windowed_Stack
begin

section \<open>GPT-Neo Model-Level Semantics\<close>

text \<open>
  The block theory is lifted to a complete causal language model here.  The
  input sequence carries absolute positions through learned position
  embeddings; the transformer stack then operates on those hidden vectors,
  followed by the final LayerNorm and vocabulary projection used for logits.
\<close>

record gpt_neo_model_parameters =
  gpt_neo_model_layers :: "gpt_neo_layer_parameters list"
  gpt_neo_model_hidden_size :: nat
  gpt_neo_model_vocabulary_size :: nat
  gpt_neo_model_max_position :: nat
  gpt_neo_model_norm_epsilon :: real
  gpt_neo_model_token_embeddings :: "real matrix"
  gpt_neo_model_position_embeddings :: "real matrix"
  gpt_neo_model_final_gain :: "real vector"
  gpt_neo_model_final_bias :: "real vector"
  gpt_neo_model_vocabulary_weights :: "real matrix"

definition valid_gpt_neo_model :: "gpt_neo_model_parameters \<Rightarrow> bool" where
  "valid_gpt_neo_model m \<longleftrightarrow>
    gpt_neo_model_layers m \<noteq> [] \<and>
    0 < gpt_neo_model_hidden_size m \<and>
    0 < gpt_neo_model_vocabulary_size m \<and>
    0 < gpt_neo_model_max_position m \<and>
    0 < gpt_neo_model_norm_epsilon m \<and>
    matrix_shape (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_token_embeddings m) \<and>
    matrix_shape (gpt_neo_model_max_position m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_position_embeddings m) \<and>
    vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_gain m) \<and>
    vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_bias m) \<and>
    matrix_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_vocabulary_weights m) \<and>
    gpt_neo_stack_compatible (gpt_neo_model_hidden_size m)
      (gpt_neo_model_layers m)"

lemma valid_gpt_neo_model_dimensions:
  assumes "valid_gpt_neo_model m"
  shows "0 < gpt_neo_model_hidden_size m"
    and "0 < gpt_neo_model_vocabulary_size m"
    and "0 < gpt_neo_model_max_position m"
    and "0 < gpt_neo_model_norm_epsilon m"
  using assms unfolding valid_gpt_neo_model_def by blast+

lemma valid_gpt_neo_model_layers_nonempty:
  assumes "valid_gpt_neo_model m"
  shows "gpt_neo_model_layers m \<noteq> []"
  using assms unfolding valid_gpt_neo_model_def by blast

lemma valid_gpt_neo_model_shapes:
  assumes "valid_gpt_neo_model m"
  shows "matrix_shape (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_token_embeddings m)"
    and "matrix_shape (gpt_neo_model_max_position m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_position_embeddings m)"
    and "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_gain m)"
    and "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_bias m)"
    and "matrix_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_vocabulary_weights m)"
    and "gpt_neo_stack_compatible (gpt_neo_model_hidden_size m)
      (gpt_neo_model_layers m)"
  using assms unfolding valid_gpt_neo_model_def by blast+

lemma valid_gpt_neo_model_token_embedding_shape:
  assumes "valid_gpt_neo_model m"
  shows "matrix_shape (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_token_embeddings m)"
  using assms unfolding valid_gpt_neo_model_def by blast

lemma valid_gpt_neo_model_position_embedding_shape:
  assumes "valid_gpt_neo_model m"
  shows "matrix_shape (gpt_neo_model_max_position m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_position_embeddings m)"
  using assms unfolding valid_gpt_neo_model_def by blast

lemma valid_gpt_neo_model_final_gain_shape:
  assumes "valid_gpt_neo_model m"
  shows "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_gain m)"
  using assms unfolding valid_gpt_neo_model_def by blast

lemma valid_gpt_neo_model_final_bias_shape:
  assumes "valid_gpt_neo_model m"
  shows "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_bias m)"
  using assms unfolding valid_gpt_neo_model_def by blast

lemma valid_gpt_neo_model_vocabulary_shape:
  assumes "valid_gpt_neo_model m"
  shows "matrix_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_vocabulary_weights m)"
  using assms unfolding valid_gpt_neo_model_def by blast

lemma valid_gpt_neo_model_stack_compatible:
  assumes "valid_gpt_neo_model m"
  shows "gpt_neo_stack_compatible (gpt_neo_model_hidden_size m)
      (gpt_neo_model_layers m)"
  using assms unfolding valid_gpt_neo_model_def by blast

definition gpt_neo_model_input ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real vector" where
  "gpt_neo_model_input m position token =
    gpt_neo_input_embedding
      (gpt_neo_model_token_embeddings m)
      (gpt_neo_model_position_embeddings m) token position"

fun gpt_neo_model_input_sequence ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real matrix" where
  "gpt_neo_model_input_sequence m position [] = []"
| "gpt_neo_model_input_sequence m position (token # tokens) =
    gpt_neo_model_input m position token #
      gpt_neo_model_input_sequence m (Suc position) tokens"

lemma length_gpt_neo_model_input_sequence [simp]:
  "length (gpt_neo_model_input_sequence m position tokens) = length tokens"
  by (induction tokens arbitrary: position) simp_all

lemma gpt_neo_model_input_sequence_append_singleton:
  "gpt_neo_model_input_sequence m position (tokens @ [token]) =
    gpt_neo_model_input_sequence m position tokens @
      [gpt_neo_model_input m (position + length tokens) token]"
proof (induction tokens arbitrary: position)
  case Nil
  then show ?case by simp
next
  case (Cons head tokens)
  then show ?case by (simp add: add.assoc)
qed

lemma gpt_neo_model_input_shape:
  assumes token_bound: "token < gpt_neo_model_vocabulary_size m"
    and position_bound: "position < gpt_neo_model_max_position m"
    and valid: "valid_gpt_neo_model m"
  shows "vector_shape (gpt_neo_model_hidden_size m)
    (gpt_neo_model_input m position token)"
proof -
  have token_embeddings:
    "matrix_shape (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_token_embeddings m)"
    by (rule valid_gpt_neo_model_token_embedding_shape[OF valid])
  have position_embeddings:
    "matrix_shape (gpt_neo_model_max_position m)
      (gpt_neo_model_hidden_size m)
      (gpt_neo_model_position_embeddings m)"
    by (rule valid_gpt_neo_model_position_embedding_shape[OF valid])
  show ?thesis
    unfolding gpt_neo_model_input_def
    by (rule gpt_neo_input_embedding_shape[
      OF token_bound position_bound token_embeddings position_embeddings])
qed

lemma gpt_neo_model_input_sequence_shape:
  assumes valid: "valid_gpt_neo_model m"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
  shows "matrix_shape (length tokens) (gpt_neo_model_hidden_size m)
    (gpt_neo_model_input_sequence m position tokens)"
  using token_bounds position_bound
proof (induction tokens arbitrary: position)
  case Nil
  then show ?case by (simp add: matrix_shape_def)
next
  case (Cons token tokens)
  have token_bound:
    "token < gpt_neo_model_vocabulary_size m"
    using Cons.prems(1) by simp
  have head_position:
    "position < gpt_neo_model_max_position m"
    using Cons.prems(2) by simp
  have head:
    "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_input m position token)"
    by (rule gpt_neo_model_input_shape[
      OF token_bound head_position valid])
  have tail_tokens:
    "\<forall>t \<in> set tokens.
      t < gpt_neo_model_vocabulary_size m"
    using Cons.prems(1) by simp
  have tail_position:
    "Suc position + length tokens \<le>
      gpt_neo_model_max_position m"
  proof -
    have source:
      "position + Suc (length tokens) \<le>
        gpt_neo_model_max_position m"
      using Cons.prems(2) by simp
    then show ?thesis by (simp add: add.assoc)
  qed
  have tail:
    "matrix_shape (length tokens) (gpt_neo_model_hidden_size m)
      (gpt_neo_model_input_sequence m (Suc position) tokens)"
    by (rule Cons.IH[OF tail_tokens tail_position])
  show ?case
    using head tail
    by (simp add: matrix_shape_def vector_shape_def)
qed

definition gpt_neo_full_hidden ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real matrix" where
  "gpt_neo_full_hidden m position tokens =
    gpt_neo_full_stack (gpt_neo_model_layers m)
      (gpt_neo_model_input_sequence m position tokens)"

theorem valid_gpt_neo_full_hidden_shape:
  assumes valid: "valid_gpt_neo_model m"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
  shows "matrix_shape (length tokens) (gpt_neo_model_hidden_size m)
    (gpt_neo_full_hidden m position tokens)"
proof -
  have input:
    "matrix_shape (length tokens) (gpt_neo_model_hidden_size m)
      (gpt_neo_model_input_sequence m position tokens)"
    by (rule gpt_neo_model_input_sequence_shape[
      OF valid token_bounds position_bound])
  have compatible:
    "gpt_neo_stack_compatible (gpt_neo_model_hidden_size m)
      (gpt_neo_model_layers m)"
    by (rule valid_gpt_neo_model_stack_compatible[OF valid])
  show ?thesis
    unfolding gpt_neo_full_hidden_def
    by (rule compatible_gpt_neo_full_stack_shape[OF compatible input])
qed

definition gpt_neo_final_normalize ::
  "gpt_neo_model_parameters \<Rightarrow> real vector \<Rightarrow> real vector" where
  "gpt_neo_final_normalize m x =
    gpt_neo_layer_norm (gpt_neo_model_norm_epsilon m)
      (gpt_neo_model_final_gain m)
      (gpt_neo_model_final_bias m) x"

definition gpt_neo_model_logits ::
  "gpt_neo_model_parameters \<Rightarrow> real vector \<Rightarrow> real vector" where
  "gpt_neo_model_logits m x =
    gpt_neo_logits (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_vocabulary_weights m)
      (gpt_neo_final_normalize m x)"

definition gpt_neo_full_model_logits ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real matrix" where
  "gpt_neo_full_model_logits m position tokens =
    map (gpt_neo_model_logits m)
      (gpt_neo_full_hidden m position tokens)"

lemma gpt_neo_final_normalize_shape:
  assumes valid: "valid_gpt_neo_model m"
    and x: "vector_shape (gpt_neo_model_hidden_size m) x"
  shows "vector_shape (gpt_neo_model_hidden_size m)
    (gpt_neo_final_normalize m x)"
proof -
  have gain:
    "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_gain m)"
    by (rule valid_gpt_neo_model_final_gain_shape[OF valid])
  have bias:
    "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_final_bias m)"
    by (rule valid_gpt_neo_model_final_bias_shape[OF valid])
  show ?thesis
    unfolding gpt_neo_final_normalize_def
    by (rule gpt_neo_layer_norm_shape[OF gain bias x])
qed

lemma gpt_neo_model_logits_shape:
  assumes valid: "valid_gpt_neo_model m"
    and x: "vector_shape (gpt_neo_model_hidden_size m) x"
  shows "vector_shape (gpt_neo_model_vocabulary_size m)
    (gpt_neo_model_logits m x)"
proof -
  have vocabulary:
    "matrix_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_model_vocabulary_size m)
      (gpt_neo_model_vocabulary_weights m)"
    by (rule valid_gpt_neo_model_vocabulary_shape[OF valid])
  have normalized:
    "vector_shape (gpt_neo_model_hidden_size m)
      (gpt_neo_final_normalize m x)"
    by (rule gpt_neo_final_normalize_shape[OF valid x])
  show ?thesis
    unfolding gpt_neo_model_logits_def
    by (rule gpt_neo_logits_shape[OF vocabulary normalized])
qed

theorem valid_gpt_neo_full_model_logits_shape:
  assumes valid: "valid_gpt_neo_model m"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
  shows "matrix_shape (length tokens)
      (gpt_neo_model_vocabulary_size m)
      (gpt_neo_full_model_logits m position tokens)"
proof -
  have hidden:
    "matrix_shape (length tokens) (gpt_neo_model_hidden_size m)
      (gpt_neo_full_hidden m position tokens)"
    by (rule valid_gpt_neo_full_hidden_shape[
      OF valid token_bounds position_bound])
  have hidden_rows:
    "\<forall>row \<in> set (gpt_neo_full_hidden m position tokens).
      vector_shape (gpt_neo_model_hidden_size m) row"
    using hidden
    by (auto simp: matrix_shape_def vector_shape_def)
  have logits_rows:
    "\<forall>row \<in> set (gpt_neo_full_hidden m position tokens).
      vector_shape (gpt_neo_model_vocabulary_size m)
        (gpt_neo_model_logits m row)"
    using hidden_rows
    by (auto intro:
      gpt_neo_model_logits_shape[OF valid])
  show ?thesis
    unfolding gpt_neo_full_model_logits_def
    using hidden logits_rows
    by (auto simp: matrix_shape_def vector_shape_def)
qed

definition gpt_neo_model_cache_matches ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> bool" where
  "gpt_neo_model_cache_matches m position tokens caches \<longleftrightarrow>
    gpt_neo_transformer_cache_matches (gpt_neo_model_layers m)
      (gpt_neo_model_input_sequence m position tokens) caches"

definition gpt_neo_cached_prompt ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   real vector list \<times> gpt_neo_transformer_cache" where
  "gpt_neo_cached_prompt m position tokens =
    gpt_neo_cached_stack_run (gpt_neo_model_layers m)
      (empty_gpt_neo_transformer_cache (gpt_neo_model_layers m))
      (gpt_neo_model_input_sequence m position tokens)"

theorem gpt_neo_cached_prompt_correct:
  assumes valid: "valid_gpt_neo_model m"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
  shows "fst (gpt_neo_cached_prompt m position tokens) =
      gpt_neo_full_hidden m position tokens"
    and "gpt_neo_model_cache_matches m position tokens
      (snd (gpt_neo_cached_prompt m position tokens))"
proof -
  have stack_valid:
    "valid_gpt_neo_stack (gpt_neo_model_layers m)"
    using valid_gpt_neo_model_stack_compatible[OF valid]
    by (simp add: gpt_neo_stack_compatible_def valid_gpt_neo_stack_def)
  have run:
    "gpt_neo_full_stack (gpt_neo_model_layers m)
        ([] @ gpt_neo_model_input_sequence m position tokens) =
      gpt_neo_full_stack (gpt_neo_model_layers m) []
        @ fst (gpt_neo_cached_stack_run (gpt_neo_model_layers m)
          (empty_gpt_neo_transformer_cache (gpt_neo_model_layers m))
          (gpt_neo_model_input_sequence m position tokens))"
    using initialized_gpt_neo_cached_run_equals_full[OF stack_valid,
      where xs="gpt_neo_model_input_sequence m position tokens"]
    by simp
  have cache:
    "gpt_neo_transformer_cache_matches (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position tokens)
        (snd (gpt_neo_cached_stack_run (gpt_neo_model_layers m)
          (empty_gpt_neo_transformer_cache (gpt_neo_model_layers m))
          (gpt_neo_model_input_sequence m position tokens)))"
    using initialized_gpt_neo_cached_run_cache_invariant[OF stack_valid,
      where xs="gpt_neo_model_input_sequence m position tokens"]
    by simp
  show "fst (gpt_neo_cached_prompt m position tokens) =
      gpt_neo_full_hidden m position tokens"
    using run
    by (simp add: gpt_neo_cached_prompt_def gpt_neo_full_hidden_def)
  show "gpt_neo_model_cache_matches m position tokens
      (snd (gpt_neo_cached_prompt m position tokens))"
    using cache
    by (simp add: gpt_neo_model_cache_matches_def
        gpt_neo_cached_prompt_def)
qed

definition gpt_neo_generation_cache_matches ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> bool" where
  "gpt_neo_generation_cache_matches m position tokens caches \<longleftrightarrow>
    tokens \<noteq> [] \<and>
    gpt_neo_model_cache_matches m position (butlast tokens) caches"

definition gpt_neo_cached_model_evaluate ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow>
   real vector \<times> gpt_neo_transformer_cache" where
  "gpt_neo_cached_model_evaluate m position tokens caches =
    (if tokens = [] then ([], caches)
     else
       (let prefix = butlast tokens;
            token = last tokens;
            x = gpt_neo_model_input m
              (position + length prefix) token;
            step = gpt_neo_cached_stack_step
              (gpt_neo_model_layers m) x caches
        in (gpt_neo_model_logits m (fst step), snd step)))"

lemma gpt_neo_input_sequence_token_split:
  assumes "tokens \<noteq> []"
  shows "gpt_neo_model_input_sequence m position tokens =
      gpt_neo_model_input_sequence m position (butlast tokens) @
        [gpt_neo_model_input m
          (position + length (butlast tokens)) (last tokens)]"
proof -
  have split: "tokens = butlast tokens @ [last tokens]"
    using assms by simp
  have append:
    "gpt_neo_model_input_sequence m position
        (butlast tokens @ [last tokens]) =
      gpt_neo_model_input_sequence m position (butlast tokens) @
        [gpt_neo_model_input m
          (position + length (butlast tokens)) (last tokens)]"
    by (rule gpt_neo_model_input_sequence_append_singleton)
  then show ?thesis using split by simp
qed

theorem gpt_neo_cached_model_evaluate_correct:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match:
      "gpt_neo_generation_cache_matches m position tokens caches"
  shows "fst (gpt_neo_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    and "gpt_neo_model_cache_matches m position tokens
      (snd (gpt_neo_cached_model_evaluate m position tokens caches))"
proof -
  have cache_match:
    "gpt_neo_model_cache_matches m position (butlast tokens) caches"
    using match by (simp add: gpt_neo_generation_cache_matches_def)
  have token_bound:
    "last tokens < gpt_neo_model_vocabulary_size m"
  proof -
    have last_member: "last tokens \<in> set tokens"
      by (rule last_in_set[OF tokens])
    then show ?thesis
      using token_bounds by blast
  qed
  have prefix_position:
    "position + length (butlast tokens) <
      gpt_neo_model_max_position m"
  proof -
    have token_length:
      "length tokens = Suc (length (butlast tokens))"
      using tokens by simp
    have bound:
      "position + Suc (length (butlast tokens)) \<le>
        gpt_neo_model_max_position m"
      using position_bound by (simp only: token_length)
    then show ?thesis by simp
  qed
  have stack_valid:
    "valid_gpt_neo_stack (gpt_neo_model_layers m)"
    using valid_gpt_neo_model_stack_compatible[OF valid]
    by (simp add: gpt_neo_stack_compatible_def valid_gpt_neo_stack_def)
  have stack_match:
    "gpt_neo_transformer_cache_matches (gpt_neo_model_layers m)
      (gpt_neo_model_input_sequence m position (butlast tokens)) caches"
    using cache_match by (simp add: gpt_neo_model_cache_matches_def)
  let ?x = "gpt_neo_model_input m
    (position + length (butlast tokens)) (last tokens)"
  have input_split:
    "gpt_neo_model_input_sequence m position tokens =
      gpt_neo_model_input_sequence m position (butlast tokens) @ [?x]"
  proof -
    have split:
      "gpt_neo_model_input_sequence m position tokens =
        gpt_neo_model_input_sequence m position (butlast tokens) @
          [gpt_neo_model_input m
            (position + length (butlast tokens)) (last tokens)]"
      by (rule gpt_neo_input_sequence_token_split[OF tokens])
    then show ?thesis by simp
  qed
  have stack_step:
    "gpt_neo_full_stack (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position (butlast tokens) @ [?x]) =
      gpt_neo_full_stack (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position (butlast tokens)) @
        [fst (gpt_neo_cached_stack_step
          (gpt_neo_model_layers m) ?x caches)]"
    by (rule gpt_neo_cached_stack_step_correct(1)
        [OF stack_valid stack_match])
  have cache_step:
    "gpt_neo_transformer_cache_matches (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position (butlast tokens) @ [?x])
        (snd (gpt_neo_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    by (rule gpt_neo_cached_stack_step_correct(2)
        [OF stack_valid stack_match])
  have hidden_last:
    "last (gpt_neo_full_hidden m position tokens) =
      fst (gpt_neo_cached_stack_step
        (gpt_neo_model_layers m) ?x caches)"
    using stack_step input_split
    by (simp add: gpt_neo_full_hidden_def)
  have hidden_nonempty:
    "gpt_neo_full_hidden m position tokens \<noteq> []"
  proof -
    have hidden_length:
      "length (gpt_neo_full_hidden m position tokens) = length tokens"
      by (simp add: gpt_neo_full_hidden_def)
    then show ?thesis
      using tokens by auto
  qed
  have mapped_last:
    "last (map (gpt_neo_model_logits m)
        (gpt_neo_full_hidden m position tokens)) =
      gpt_neo_model_logits m
        (last (gpt_neo_full_hidden m position tokens))"
    by (rule last_map[OF hidden_nonempty])
  have logits_map:
    "last (gpt_neo_full_model_logits m position tokens) =
      gpt_neo_model_logits m
        (last (gpt_neo_full_hidden m position tokens))"
    unfolding gpt_neo_full_model_logits_def
    by (rule mapped_last)
  have logits_hidden:
    "gpt_neo_model_logits m
        (last (gpt_neo_full_hidden m position tokens)) =
      gpt_neo_model_logits m
        (fst (gpt_neo_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    by (rule arg_cong[OF hidden_last])
  have logits_last:
    "last (gpt_neo_full_model_logits m position tokens) =
      gpt_neo_model_logits m
        (fst (gpt_neo_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    using logits_map logits_hidden by (rule trans)
  have evaluation_output:
    "fst (gpt_neo_cached_model_evaluate m position tokens caches) =
      gpt_neo_model_logits m
        (fst (gpt_neo_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    unfolding gpt_neo_cached_model_evaluate_def
    using tokens
    by (simp add: Let_def)
  have output_last:
    "fst (gpt_neo_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    using evaluation_output logits_last
    by (metis)
  show "fst (gpt_neo_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    by (rule output_last)
  have cache_target:
    "gpt_neo_transformer_cache_matches (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position tokens)
        (snd (gpt_neo_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    using cache_step input_split
    by (simp only: input_split)
  have evaluation_cache:
    "snd (gpt_neo_cached_model_evaluate m position tokens caches) =
      snd (gpt_neo_cached_stack_step
        (gpt_neo_model_layers m) ?x caches)"
    unfolding gpt_neo_cached_model_evaluate_def
    using tokens
    by (simp add: Let_def tokens)
  show "gpt_neo_model_cache_matches m position tokens
      (snd (gpt_neo_cached_model_evaluate m position tokens caches))"
    unfolding gpt_neo_model_cache_matches_def
    using cache_target evaluation_cache
    by (metis)
qed

corollary gpt_neo_cached_model_evaluate_logits_correct:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match:
      "gpt_neo_generation_cache_matches m position tokens caches"
  shows "fst (gpt_neo_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
  using gpt_neo_cached_model_evaluate_correct(1)
    [OF valid tokens token_bounds position_bound match] .

corollary gpt_neo_cached_model_evaluate_cache_correct:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match:
      "gpt_neo_generation_cache_matches m position tokens caches"
  shows "gpt_neo_model_cache_matches m position tokens
      (snd (gpt_neo_cached_model_evaluate m position tokens caches))"
  using gpt_neo_cached_model_evaluate_correct(2)
    [OF valid tokens token_bounds position_bound match] .

definition gpt_neo_bounded_model_cache_matches ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> bool" where
  "gpt_neo_bounded_model_cache_matches m position tokens caches \<longleftrightarrow>
    gpt_neo_bounded_transformer_cache_matches (gpt_neo_model_layers m)
      (gpt_neo_model_input_sequence m position tokens) caches"

definition gpt_neo_bounded_cached_prompt ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
    real vector list \<times> gpt_neo_transformer_cache" where
  "gpt_neo_bounded_cached_prompt m position tokens =
    gpt_neo_bounded_cached_stack_run (gpt_neo_model_layers m)
      (empty_gpt_neo_bounded_transformer_cache
        (gpt_neo_model_layers m))
      (gpt_neo_model_input_sequence m position tokens)"

theorem gpt_neo_bounded_cached_prompt_correct:
  assumes valid: "valid_gpt_neo_model m"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
  shows "fst (gpt_neo_bounded_cached_prompt m position tokens) =
      gpt_neo_full_hidden m position tokens"
    and "gpt_neo_bounded_model_cache_matches m position tokens
      (snd (gpt_neo_bounded_cached_prompt m position tokens))"
proof -
  have stack_valid:
    "valid_gpt_neo_stack (gpt_neo_model_layers m)"
    using valid_gpt_neo_model_stack_compatible[OF valid]
    by (simp add: gpt_neo_stack_compatible_def valid_gpt_neo_stack_def)
  have run:
    "gpt_neo_full_stack (gpt_neo_model_layers m)
        ([] @ gpt_neo_model_input_sequence m position tokens) =
      gpt_neo_full_stack (gpt_neo_model_layers m) []
        @ fst (gpt_neo_bounded_cached_stack_run
          (gpt_neo_model_layers m)
          (empty_gpt_neo_bounded_transformer_cache
            (gpt_neo_model_layers m))
          (gpt_neo_model_input_sequence m position tokens))"
    using initialized_gpt_neo_bounded_cached_run_equals_full[OF stack_valid,
      where xs="gpt_neo_model_input_sequence m position tokens"]
    by simp
  have cache:
    "gpt_neo_bounded_transformer_cache_matches
        (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position tokens)
        (snd (gpt_neo_bounded_cached_stack_run
          (gpt_neo_model_layers m)
          (empty_gpt_neo_bounded_transformer_cache
            (gpt_neo_model_layers m))
          (gpt_neo_model_input_sequence m position tokens)))"
    using initialized_gpt_neo_bounded_cached_run_cache_invariant[
      OF stack_valid, where xs="gpt_neo_model_input_sequence m position tokens"]
    by simp
  show "fst (gpt_neo_bounded_cached_prompt m position tokens) =
      gpt_neo_full_hidden m position tokens"
    using run
    by (simp add: gpt_neo_bounded_cached_prompt_def
      gpt_neo_full_hidden_def)
  show "gpt_neo_bounded_model_cache_matches m position tokens
      (snd (gpt_neo_bounded_cached_prompt m position tokens))"
    using cache
    by (simp add: gpt_neo_bounded_model_cache_matches_def
      gpt_neo_bounded_cached_prompt_def)
qed

definition gpt_neo_bounded_generation_cache_matches ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> bool" where
  "gpt_neo_bounded_generation_cache_matches m position tokens caches \<longleftrightarrow>
    tokens \<noteq> [] \<and>
    gpt_neo_bounded_model_cache_matches m position (butlast tokens) caches"

definition gpt_neo_bounded_cached_model_evaluate ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow>
   real vector \<times> gpt_neo_transformer_cache" where
  "gpt_neo_bounded_cached_model_evaluate m position tokens caches =
    (if tokens = [] then ([], caches)
     else
       (let prefix = butlast tokens;
            token = last tokens;
            x = gpt_neo_model_input m
              (position + length prefix) token;
            step = gpt_neo_bounded_cached_stack_step
              (gpt_neo_model_layers m) x caches
        in (gpt_neo_model_logits m (fst step), snd step)))"

theorem gpt_neo_bounded_cached_model_evaluate_correct:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match:
      "gpt_neo_bounded_generation_cache_matches m position tokens caches"
  shows "fst (gpt_neo_bounded_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    and "gpt_neo_bounded_model_cache_matches m position tokens
      (snd (gpt_neo_bounded_cached_model_evaluate m position tokens caches))"
proof -
  have cache_match:
    "gpt_neo_bounded_model_cache_matches m position
      (butlast tokens) caches"
    using match by (simp add: gpt_neo_bounded_generation_cache_matches_def)
  have token_bound:
    "last tokens < gpt_neo_model_vocabulary_size m"
  proof -
    have last_member: "last tokens \<in> set tokens"
      by (rule last_in_set[OF tokens])
    then show ?thesis
      using token_bounds by blast
  qed
  have prefix_position:
    "position + length (butlast tokens) <
      gpt_neo_model_max_position m"
  proof -
    have token_length:
      "length tokens = Suc (length (butlast tokens))"
      using tokens by simp
    have bound:
      "position + Suc (length (butlast tokens)) \<le>
        gpt_neo_model_max_position m"
      using position_bound by (simp only: token_length)
    then show ?thesis by simp
  qed
  have stack_valid:
    "valid_gpt_neo_stack (gpt_neo_model_layers m)"
    using valid_gpt_neo_model_stack_compatible[OF valid]
    by (simp add: gpt_neo_stack_compatible_def valid_gpt_neo_stack_def)
  have stack_match:
    "gpt_neo_bounded_transformer_cache_matches (gpt_neo_model_layers m)
      (gpt_neo_model_input_sequence m position (butlast tokens)) caches"
    using cache_match
    by (simp add: gpt_neo_bounded_model_cache_matches_def)
  let ?x = "gpt_neo_model_input m
    (position + length (butlast tokens)) (last tokens)"
  have input_split:
    "gpt_neo_model_input_sequence m position tokens =
      gpt_neo_model_input_sequence m position (butlast tokens) @ [?x]"
  proof -
    have split:
      "gpt_neo_model_input_sequence m position tokens =
        gpt_neo_model_input_sequence m position (butlast tokens) @
          [gpt_neo_model_input m
            (position + length (butlast tokens)) (last tokens)]"
      by (rule gpt_neo_input_sequence_token_split[OF tokens])
    then show ?thesis by simp
  qed
  have stack_step:
    "gpt_neo_full_stack (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position (butlast tokens) @ [?x]) =
      gpt_neo_full_stack (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position (butlast tokens)) @
        [fst (gpt_neo_bounded_cached_stack_step
          (gpt_neo_model_layers m) ?x caches)]"
    by (rule gpt_neo_bounded_cached_stack_step_correct(1)
        [OF stack_valid stack_match])
  have cache_step:
    "gpt_neo_bounded_transformer_cache_matches (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position (butlast tokens) @ [?x])
        (snd (gpt_neo_bounded_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    by (rule gpt_neo_bounded_cached_stack_step_correct(2)
        [OF stack_valid stack_match])
  have hidden_last:
    "last (gpt_neo_full_hidden m position tokens) =
      fst (gpt_neo_bounded_cached_stack_step
        (gpt_neo_model_layers m) ?x caches)"
    using stack_step input_split
    by (simp add: gpt_neo_full_hidden_def)
  have hidden_nonempty:
    "gpt_neo_full_hidden m position tokens \<noteq> []"
  proof -
    have hidden_length:
      "length (gpt_neo_full_hidden m position tokens) = length tokens"
      by (simp add: gpt_neo_full_hidden_def)
    then show ?thesis
      using tokens by auto
  qed
  have mapped_last:
    "last (map (gpt_neo_model_logits m)
        (gpt_neo_full_hidden m position tokens)) =
      gpt_neo_model_logits m
        (last (gpt_neo_full_hidden m position tokens))"
    by (rule last_map[OF hidden_nonempty])
  have logits_map:
    "last (gpt_neo_full_model_logits m position tokens) =
      gpt_neo_model_logits m
        (last (gpt_neo_full_hidden m position tokens))"
    unfolding gpt_neo_full_model_logits_def
    by (rule mapped_last)
  have logits_hidden:
    "gpt_neo_model_logits m
        (last (gpt_neo_full_hidden m position tokens)) =
      gpt_neo_model_logits m
        (fst (gpt_neo_bounded_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    by (rule arg_cong[OF hidden_last])
  have logits_last:
    "last (gpt_neo_full_model_logits m position tokens) =
      gpt_neo_model_logits m
        (fst (gpt_neo_bounded_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    using logits_map logits_hidden by (rule trans)
  have evaluation_output:
    "fst (gpt_neo_bounded_cached_model_evaluate
      m position tokens caches) =
      gpt_neo_model_logits m
        (fst (gpt_neo_bounded_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    unfolding gpt_neo_bounded_cached_model_evaluate_def
    using tokens
    by (simp add: Let_def)
  have output_last:
    "fst (gpt_neo_bounded_cached_model_evaluate
      m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    using evaluation_output logits_last
    by (metis)
  show "fst (gpt_neo_bounded_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    by (rule output_last)
  have cache_target:
    "gpt_neo_bounded_transformer_cache_matches (gpt_neo_model_layers m)
        (gpt_neo_model_input_sequence m position tokens)
        (snd (gpt_neo_bounded_cached_stack_step
          (gpt_neo_model_layers m) ?x caches))"
    using cache_step input_split
    by (simp only: input_split)
  have evaluation_cache:
    "snd (gpt_neo_bounded_cached_model_evaluate
      m position tokens caches) =
      snd (gpt_neo_bounded_cached_stack_step
        (gpt_neo_model_layers m) ?x caches)"
    unfolding gpt_neo_bounded_cached_model_evaluate_def
    using tokens
    by (simp add: Let_def tokens)
  show "gpt_neo_bounded_model_cache_matches m position tokens
      (snd (gpt_neo_bounded_cached_model_evaluate m position tokens caches))"
    unfolding gpt_neo_bounded_model_cache_matches_def
    using cache_target evaluation_cache
    by (metis)
qed

corollary gpt_neo_bounded_cached_model_evaluate_logits_correct:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match:
      "gpt_neo_bounded_generation_cache_matches m position tokens caches"
  shows "fst (gpt_neo_bounded_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
  using gpt_neo_bounded_cached_model_evaluate_correct(1)
    [OF valid tokens token_bounds position_bound match] .

corollary gpt_neo_bounded_cached_model_evaluate_cache_correct:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match:
      "gpt_neo_bounded_generation_cache_matches m position tokens caches"
  shows "gpt_neo_bounded_model_cache_matches m position tokens
      (snd (gpt_neo_bounded_cached_model_evaluate m position tokens caches))"
  using gpt_neo_bounded_cached_model_evaluate_correct(2)
    [OF valid tokens token_bounds position_bound match] .

lemma gpt_neo_bounded_cached_model_evaluate_logits_length:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match:
      "gpt_neo_bounded_generation_cache_matches m position tokens caches"
  shows "length (fst
      (gpt_neo_bounded_cached_model_evaluate m position tokens caches)) =
      gpt_neo_model_vocabulary_size m"
proof -
  have full_shape:
    "matrix_shape (length tokens)
      (gpt_neo_model_vocabulary_size m)
      (gpt_neo_full_model_logits m position tokens)"
    by (rule valid_gpt_neo_full_model_logits_shape[
      OF valid token_bounds position_bound])
  have full_nonempty:
    "gpt_neo_full_model_logits m position tokens \<noteq> []"
  proof -
    have full_length:
      "length (gpt_neo_full_model_logits m position tokens) =
        length tokens"
      by (simp add: gpt_neo_full_model_logits_def
          gpt_neo_full_hidden_def)
    then show ?thesis
      using tokens by auto
  qed
  have last_shape:
    "vector_shape (gpt_neo_model_vocabulary_size m)
      (last (gpt_neo_full_model_logits m position tokens))"
    using matrix_shape_row[OF full_shape]
      last_in_set[OF full_nonempty]
    by (simp add: vector_shape_def)
  have equality:
    "fst (gpt_neo_bounded_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    by (rule gpt_neo_bounded_cached_model_evaluate_correct(1)
      [OF valid tokens token_bounds position_bound match])
  show ?thesis
    using last_shape equality
    by (simp add: vector_shape_def)
qed

end
