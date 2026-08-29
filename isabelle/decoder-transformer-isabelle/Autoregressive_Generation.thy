theory Autoregressive_Generation
  imports Incremental_Decoder
begin

section \<open>Autoregressive Generation\<close>

definition next_token_logits ::
  "nat \<Rightarrow> real matrix \<Rightarrow> real vector \<Rightarrow> real vector" where
  "next_token_logits vocabulary_size W_vocabulary hidden =
    linear_project vocabulary_size W_vocabulary hidden"

definition next_token_distribution ::
  "nat \<Rightarrow> real matrix \<Rightarrow> real vector \<Rightarrow> real vector" where
  "next_token_distribution vocabulary_size W_vocabulary hidden =
    list_softmax (next_token_logits vocabulary_size W_vocabulary hidden)"

lemma length_next_token_logits [simp]:
  "length (next_token_logits vocabulary_size W_vocabulary hidden) =
    vocabulary_size"
  by (simp add: next_token_logits_def linear_project_def matrix_columns_def)

lemma next_token_logits_zero_vocabulary [simp]:
  "next_token_logits 0 W_vocabulary hidden = []"
  by (simp add: next_token_logits_def linear_project_def matrix_columns_def)

lemma length_next_token_distribution [simp]:
  "length (next_token_distribution vocabulary_size W_vocabulary hidden) =
    vocabulary_size"
  by (simp add: next_token_distribution_def)

lemma next_token_distribution_zero_vocabulary [simp]:
  "next_token_distribution 0 W_vocabulary hidden = []"
  by (simp add: next_token_distribution_def)

lemma next_token_logits_nonempty:
  assumes "0 < vocabulary_size"
  shows "next_token_logits vocabulary_size W_vocabulary hidden \<noteq> []"
proof
  assume "next_token_logits vocabulary_size W_vocabulary hidden = []"
  moreover have
    "length (next_token_logits vocabulary_size W_vocabulary hidden) =
      vocabulary_size"
    by (rule length_next_token_logits)
  then have "vocabulary_size = 0"
    using calculation by simp
  with assms show False by simp
qed

theorem next_token_distribution_normalized:
  assumes "0 < vocabulary_size"
  shows "sum_list
    (next_token_distribution vocabulary_size W_vocabulary hidden) = 1"
  unfolding next_token_distribution_def
  apply (rule list_softmax_normalized)
  by (rule next_token_logits_nonempty[OF assms])

definition sample_supported :: "real vector \<Rightarrow> nat \<Rightarrow> bool" where
  "sample_supported distribution token \<longleftrightarrow>
    token < length distribution \<and> 0 < distribution ! token"

lemma sample_supported_bound:
  assumes "sample_supported distribution token"
  shows "token < length distribution"
  using assms by (simp add: sample_supported_def)

theorem next_token_distribution_support:
  assumes "0 < vocabulary_size" "token < vocabulary_size"
  shows "sample_supported
    (next_token_distribution vocabulary_size W_vocabulary hidden) token"
proof -
  have nonempty:
    "next_token_logits vocabulary_size W_vocabulary hidden \<noteq> []"
    by (rule next_token_logits_nonempty[OF assms(1)])
  have positive:
    "0 < next_token_distribution vocabulary_size W_vocabulary hidden ! token"
    unfolding next_token_distribution_def
    apply (rule list_softmax_positive[OF nonempty])
    using assms(2) by simp
  show ?thesis
    using assms(2) positive by (simp add: sample_supported_def)
qed

definition deterministic_next_token ::
  "(real vector \<Rightarrow> nat) \<Rightarrow> real vector \<Rightarrow> nat" where
  "deterministic_next_token select distribution = select distribution"

definition generation_cache_matches ::
  "(nat \<Rightarrow> real vector) \<Rightarrow> decoder_layer_parameters list \<Rightarrow>
   nat list \<Rightarrow> transformer_kv_cache \<Rightarrow> bool" where
  "generation_cache_matches embedding layers tokens caches \<longleftrightarrow>
    tokens \<noteq> [] \<and>
    transformer_cache_matches layers (map embedding (butlast tokens)) caches"

definition cached_generation_evaluate ::
  "decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> real matrix \<Rightarrow> nat list \<Rightarrow>
   transformer_kv_cache \<Rightarrow> real vector \<times> transformer_kv_cache" where
  "cached_generation_evaluate layers embedding vocabulary_size W_vocabulary
      tokens caches =
    (if tokens = [] then ([], caches)
     else
      (let step = cached_decoder_stack_step layers (embedding (last tokens)) caches
       in (next_token_distribution vocabulary_size W_vocabulary (fst step),
           snd step)))"

theorem cached_generation_evaluate_correct:
  assumes match: "generation_cache_matches embedding layers tokens caches"
  shows "fst (cached_generation_evaluate layers embedding vocabulary_size
      W_vocabulary tokens caches) =
    next_token_distribution vocabulary_size W_vocabulary
      (last (full_decoder_stack layers (map embedding tokens)))"
    and "transformer_cache_matches layers (map embedding tokens)
      (snd (cached_generation_evaluate layers embedding vocabulary_size
        W_vocabulary tokens caches))"
proof -
  have nonempty: "tokens \<noteq> []"
    using match by (simp add: generation_cache_matches_def)
  have cache:
    "transformer_cache_matches layers (map embedding (butlast tokens)) caches"
    using match by (simp add: generation_cache_matches_def)
  have token_split: "tokens = butlast tokens @ [last tokens]"
    using nonempty by simp
  have embedding_split:
    "map embedding tokens =
      map embedding (butlast tokens) @ [embedding (last tokens)]"
  proof -
    have "map embedding tokens =
      map embedding (butlast tokens @ [last tokens])"
      by (rule arg_cong[OF token_split])
    then show ?thesis by simp
  qed
  have output_eq:
    "fst (cached_decoder_stack_step layers (embedding (last tokens)) caches) =
      last (full_decoder_stack layers (map embedding tokens))"
    unfolding embedding_split
    by (rule incremental_decoder_equals_full[OF cache])
  have updated:
    "transformer_cache_matches layers (map embedding tokens)
      (snd (cached_decoder_stack_step layers (embedding (last tokens)) caches))"
    unfolding embedding_split
    by (rule cached_decoder_stack_step_correct(2)[OF cache])
  show "fst (cached_generation_evaluate layers embedding vocabulary_size
      W_vocabulary tokens caches) =
    next_token_distribution vocabulary_size W_vocabulary
      (last (full_decoder_stack layers (map embedding tokens)))"
    using nonempty output_eq
    by (simp add: cached_generation_evaluate_def Let_def)
  show "transformer_cache_matches layers (map embedding tokens)
    (snd (cached_generation_evaluate layers embedding vocabulary_size
      W_vocabulary tokens caches))"
    using nonempty updated
    by (simp add: cached_generation_evaluate_def Let_def)
qed

type_synonym generation_state = "nat list \<times> transformer_kv_cache"

definition generation_transition ::
  "(real vector \<Rightarrow> nat) \<Rightarrow>
   decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> real matrix \<Rightarrow> generation_state \<Rightarrow>
   generation_state" where
  "generation_transition select layers embedding vocabulary_size W_vocabulary
      state =
    (let tokens = fst state;
         evaluation = cached_generation_evaluate layers embedding vocabulary_size
          W_vocabulary tokens (snd state);
         next = deterministic_next_token select (fst evaluation)
     in (tokens @ [next], snd evaluation))"

theorem generation_transition_cache_invariant:
  assumes "generation_cache_matches embedding layers (fst state) (snd state)"
  shows "generation_cache_matches embedding layers
    (fst (generation_transition select layers embedding vocabulary_size
      W_vocabulary state))
    (snd (generation_transition select layers embedding vocabulary_size
      W_vocabulary state))"
proof -
  have updated:
    "transformer_cache_matches layers (map embedding (fst state))
      (snd (cached_generation_evaluate layers embedding vocabulary_size
        W_vocabulary (fst state) (snd state)))"
    by (rule cached_generation_evaluate_correct(2)[OF assms])
  show ?thesis
    using updated
    by (simp add: generation_transition_def generation_cache_matches_def Let_def)
qed

fun generate_steps ::
  "nat \<Rightarrow> (real vector \<Rightarrow> nat) \<Rightarrow>
   decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> real matrix \<Rightarrow> generation_state \<Rightarrow>
   generation_state" where
  "generate_steps 0 select layers embedding vocabulary_size W_vocabulary state =
    state"
| "generate_steps (Suc n) select layers embedding vocabulary_size W_vocabulary
      state =
    generate_steps n select layers embedding vocabulary_size W_vocabulary
      (generation_transition select layers embedding vocabulary_size
        W_vocabulary state)"

theorem generate_steps_cache_invariant:
  assumes "generation_cache_matches embedding layers (fst state) (snd state)"
  shows "generation_cache_matches embedding layers
    (fst (generate_steps n select layers embedding vocabulary_size
      W_vocabulary state))
    (snd (generate_steps n select layers embedding vocabulary_size
      W_vocabulary state))"
  using assms
proof (induction n arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have transition:
    "generation_cache_matches embedding layers
      (fst (generation_transition select layers embedding vocabulary_size
        W_vocabulary state))
      (snd (generation_transition select layers embedding vocabulary_size
        W_vocabulary state))"
    by (rule generation_transition_cache_invariant[OF Suc.prems])
  show ?case
    by (simp only: generate_steps.simps)
      (rule Suc.IH[OF transition])
qed

end
