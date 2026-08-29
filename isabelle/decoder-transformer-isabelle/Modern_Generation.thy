theory Modern_Generation
  imports Modern_Incremental_Decoder
begin

section \<open>End-to-End Modern Autoregressive Generation\<close>

definition modern_generation_cache_matches ::
  "(nat \<Rightarrow> real vector) \<Rightarrow> modern_decoder_layer_parameters list \<Rightarrow>
   nat \<Rightarrow> nat list \<Rightarrow> transformer_kv_cache \<Rightarrow> bool" where
  "modern_generation_cache_matches embedding layers start tokens caches \<longleftrightarrow>
    tokens \<noteq> [] \<and>
    valid_modern_decoder_stack layers \<and>
    modern_transformer_cache_matches layers start
      (map embedding (butlast tokens)) caches"

definition cached_modern_generation_evaluate ::
  "modern_decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow> nat list \<Rightarrow>
   transformer_kv_cache \<Rightarrow> real vector \<times> transformer_kv_cache" where
  "cached_modern_generation_evaluate layers embedding start vocabulary_size
      W_vocabulary tokens caches =
    (if tokens = [] then ([], caches)
     else
      (let step = cached_modern_decoder_stack_step layers
        (start + length (butlast tokens)) (embedding (last tokens)) caches
       in (next_token_distribution vocabulary_size W_vocabulary (fst step),
           snd step)))"

theorem cached_modern_generation_evaluate_correct:
  assumes match:
    "modern_generation_cache_matches embedding layers start tokens caches"
  shows "fst (cached_modern_generation_evaluate layers embedding start
      vocabulary_size W_vocabulary tokens caches) =
    next_token_distribution vocabulary_size W_vocabulary
      (last (full_modern_decoder_stack layers start (map embedding tokens)))"
    and "modern_transformer_cache_matches layers start (map embedding tokens)
      (snd (cached_modern_generation_evaluate layers embedding start
        vocabulary_size W_vocabulary tokens caches))"
proof -
  have nonempty: "tokens \<noteq> []"
    using match by (simp add: modern_generation_cache_matches_def)
  have valid: "valid_modern_decoder_stack layers"
    using match by (simp add: modern_generation_cache_matches_def)
  have cache:
    "modern_transformer_cache_matches layers start
      (map embedding (butlast tokens)) caches"
    using match by (simp add: modern_generation_cache_matches_def)
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
    "fst (cached_modern_decoder_stack_step layers
        (start + length (butlast tokens)) (embedding (last tokens)) caches) =
      last (full_modern_decoder_stack layers start (map embedding tokens))"
  proof -
    have step:
      "fst (cached_modern_decoder_stack_step layers
          (start + length (map embedding (butlast tokens)))
          (embedding (last tokens)) caches) =
        last (full_modern_decoder_stack layers start
          (map embedding (butlast tokens) @ [embedding (last tokens)]))"
      by (rule incremental_modern_decoder_equals_full[OF valid cache])
    show ?thesis
      using step embedding_split by simp
  qed
  have updated:
    "modern_transformer_cache_matches layers start (map embedding tokens)
      (snd (cached_modern_decoder_stack_step layers
        (start + length (butlast tokens)) (embedding (last tokens)) caches))"
  proof -
    have step:
      "modern_transformer_cache_matches layers start
        (map embedding (butlast tokens) @ [embedding (last tokens)])
        (snd (cached_modern_decoder_stack_step layers
          (start + length (map embedding (butlast tokens)))
          (embedding (last tokens)) caches))"
      by (rule cached_modern_decoder_stack_step_correct(2)[OF valid cache])
    show ?thesis
      using step embedding_split by simp
  qed
  show "fst (cached_modern_generation_evaluate layers embedding start
      vocabulary_size W_vocabulary tokens caches) =
    next_token_distribution vocabulary_size W_vocabulary
      (last (full_modern_decoder_stack layers start (map embedding tokens)))"
    using nonempty output_eq
    by (simp add: cached_modern_generation_evaluate_def Let_def)
  show "modern_transformer_cache_matches layers start (map embedding tokens)
    (snd (cached_modern_generation_evaluate layers embedding start
      vocabulary_size W_vocabulary tokens caches))"
    using nonempty updated
    by (simp add: cached_modern_generation_evaluate_def Let_def)
qed

corollary cached_modern_next_token_distribution_correct:
  assumes "modern_generation_cache_matches embedding layers start tokens caches"
  shows "fst (cached_modern_generation_evaluate layers embedding start
      vocabulary_size W_vocabulary tokens caches) =
    next_token_distribution vocabulary_size W_vocabulary
      (last (full_modern_decoder_stack layers start (map embedding tokens)))"
  by (rule cached_modern_generation_evaluate_correct(1)[OF assms])

definition initialize_modern_generation_state ::
  "modern_decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> nat list \<Rightarrow> generation_state" where
  "initialize_modern_generation_state layers embedding start tokens =
    (tokens,
      snd (cached_modern_decoder_stack_run layers start
        (empty_modern_transformer_cache layers)
        (map embedding (butlast tokens))))"

theorem initialize_modern_generation_state_correct:
  assumes "valid_modern_decoder_stack layers" "tokens \<noteq> []"
  shows "modern_generation_cache_matches embedding layers start
    (fst (initialize_modern_generation_state layers embedding start tokens))
    (snd (initialize_modern_generation_state layers embedding start tokens))"
  using assms initialized_modern_cached_run_cache_invariant
  by (simp add: initialize_modern_generation_state_def
      modern_generation_cache_matches_def)

definition modern_generation_transition ::
  "(real vector \<Rightarrow> nat) \<Rightarrow>
   modern_decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow> generation_state \<Rightarrow>
   generation_state" where
  "modern_generation_transition select layers embedding start vocabulary_size
      W_vocabulary state =
    (let tokens = fst state;
         evaluation = cached_modern_generation_evaluate layers embedding start
          vocabulary_size W_vocabulary tokens (snd state);
         next = deterministic_next_token select (fst evaluation)
     in (tokens @ [next], snd evaluation))"

theorem modern_generation_transition_cache_invariant:
  assumes "modern_generation_cache_matches embedding layers start
    (fst state) (snd state)"
  shows "modern_generation_cache_matches embedding layers start
    (fst (modern_generation_transition select layers embedding start
      vocabulary_size W_vocabulary state))
    (snd (modern_generation_transition select layers embedding start
      vocabulary_size W_vocabulary state))"
proof -
  have valid: "valid_modern_decoder_stack layers"
    using assms by (simp add: modern_generation_cache_matches_def)
  have updated:
    "modern_transformer_cache_matches layers start (map embedding (fst state))
      (snd (cached_modern_generation_evaluate layers embedding start
        vocabulary_size W_vocabulary (fst state) (snd state)))"
    by (rule cached_modern_generation_evaluate_correct(2)[OF assms])
  show ?thesis
    using valid updated
    by (simp add: modern_generation_transition_def
        modern_generation_cache_matches_def Let_def)
qed

fun modern_generate_steps ::
  "nat \<Rightarrow> (real vector \<Rightarrow> nat) \<Rightarrow>
   modern_decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow> generation_state \<Rightarrow>
   generation_state" where
  "modern_generate_steps 0 select layers embedding start vocabulary_size
      W_vocabulary state = state"
| "modern_generate_steps (Suc n) select layers embedding start vocabulary_size
      W_vocabulary state =
    modern_generate_steps n select layers embedding start vocabulary_size
      W_vocabulary
      (modern_generation_transition select layers embedding start vocabulary_size
        W_vocabulary state)"

theorem modern_generate_steps_cache_invariant:
  assumes "modern_generation_cache_matches embedding layers start
    (fst state) (snd state)"
  shows "modern_generation_cache_matches embedding layers start
    (fst (modern_generate_steps n select layers embedding start vocabulary_size
      W_vocabulary state))
    (snd (modern_generate_steps n select layers embedding start vocabulary_size
      W_vocabulary state))"
  using assms
proof (induction n arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have transition:
    "modern_generation_cache_matches embedding layers start
      (fst (modern_generation_transition select layers embedding start
        vocabulary_size W_vocabulary state))
      (snd (modern_generation_transition select layers embedding start
        vocabulary_size W_vocabulary state))"
    by (rule modern_generation_transition_cache_invariant[OF Suc.prems])
  show ?case
    by (simp only: modern_generate_steps.simps)
      (rule Suc.IH[OF transition])
qed

definition modern_full_next_token ::
  "modern_decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow> nat list \<Rightarrow> nat" where
  "modern_full_next_token layers embedding start vocabulary_size W_vocabulary
      tokens =
    first_argmax (next_token_distribution vocabulary_size W_vocabulary
      (last (full_modern_decoder_stack layers start (map embedding tokens))))"

fun modern_full_generate_steps ::
  "nat \<Rightarrow> modern_decoder_layer_parameters list \<Rightarrow>
   (nat \<Rightarrow> real vector) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow>
   nat list \<Rightarrow> nat list" where
  "modern_full_generate_steps 0 layers embedding start vocabulary_size
      W_vocabulary tokens = tokens"
| "modern_full_generate_steps (Suc n) layers embedding start vocabulary_size
      W_vocabulary tokens =
    modern_full_generate_steps n layers embedding start vocabulary_size
      W_vocabulary
      (tokens @ [modern_full_next_token layers embedding start vocabulary_size
        W_vocabulary tokens])"

theorem modern_generation_transition_full:
  assumes state_valid:
    "modern_generation_cache_matches embedding layers start
      (fst state) (snd state)"
  shows "fst (modern_generation_transition first_argmax layers embedding start
      vocabulary_size W_vocabulary state) =
    fst state @ [modern_full_next_token layers embedding start vocabulary_size
      W_vocabulary (fst state)]"
proof -
  have evaluation:
    "fst (cached_modern_generation_evaluate layers embedding start
      vocabulary_size W_vocabulary (fst state) (snd state)) =
      next_token_distribution vocabulary_size W_vocabulary
        (last (full_modern_decoder_stack layers start
          (map embedding (fst state))))"
    by (rule cached_modern_generation_evaluate_correct(1)[OF state_valid])
  have transition_tokens:
    "fst (modern_generation_transition first_argmax layers embedding start
        vocabulary_size W_vocabulary state) =
      fst state @
        [first_argmax (fst (cached_modern_generation_evaluate layers embedding
          start vocabulary_size W_vocabulary (fst state) (snd state)))]"
    by (simp add: modern_generation_transition_def deterministic_next_token_def
        Let_def)
  show ?thesis
    unfolding modern_full_next_token_def
    using transition_tokens evaluation
    by (simp add: transition_tokens evaluation)
qed

theorem modern_greedy_generate_steps_eq_full:
  assumes state_valid:
    "modern_generation_cache_matches embedding layers start
      (fst state) (snd state)"
  shows "fst (modern_generate_steps n first_argmax layers embedding start
      vocabulary_size W_vocabulary state) =
    modern_full_generate_steps n layers embedding start vocabulary_size
      W_vocabulary (fst state)"
proof -
  show ?thesis
  using state_valid
  proof (induction n arbitrary: state)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have next_valid:
      "modern_generation_cache_matches embedding layers start
        (fst (modern_generation_transition first_argmax layers embedding start
          vocabulary_size W_vocabulary state))
        (snd (modern_generation_transition first_argmax layers embedding start
          vocabulary_size W_vocabulary state))"
      by (rule modern_generation_transition_cache_invariant[OF Suc.prems])
    have recursive:
      "fst (modern_generate_steps n first_argmax layers embedding start
          vocabulary_size W_vocabulary
          (modern_generation_transition first_argmax layers embedding start
            vocabulary_size W_vocabulary state)) =
        modern_full_generate_steps n layers embedding start vocabulary_size
          W_vocabulary
          (fst (modern_generation_transition first_argmax layers embedding start
            vocabulary_size W_vocabulary state))"
      by (rule Suc.IH[OF next_valid])
    have transition_full:
      "fst (modern_generation_transition first_argmax layers embedding start
          vocabulary_size W_vocabulary state) =
        fst state @ [modern_full_next_token layers embedding start
          vocabulary_size W_vocabulary (fst state)]"
      by (rule modern_generation_transition_full[OF Suc.prems])
    have recursive_rewritten:
      "fst (modern_generate_steps (Suc n) first_argmax layers embedding start
          vocabulary_size W_vocabulary state) =
        modern_full_generate_steps n layers embedding start vocabulary_size
          W_vocabulary
          (fst state @ [modern_full_next_token layers embedding start
            vocabulary_size W_vocabulary (fst state)])"
      using recursive transition_full
      by (simp add: modern_generate_steps.simps recursive transition_full)
    show ?case
      by (simp only: modern_full_generate_steps.simps)
        (rule recursive_rewritten)
  qed
  qed

corollary initialized_modern_greedy_generate_steps_eq_full:
  assumes valid: "valid_modern_decoder_stack layers"
    and tokens: "tokens \<noteq> []"
  shows "fst (modern_generate_steps n first_argmax layers embedding start
      vocabulary_size W_vocabulary
      (initialize_modern_generation_state layers embedding start tokens)) =
    modern_full_generate_steps n layers embedding start vocabulary_size
      W_vocabulary tokens"
proof -
  have state_valid:
    "modern_generation_cache_matches embedding layers start
      (fst (initialize_modern_generation_state layers embedding start tokens))
      (snd (initialize_modern_generation_state layers embedding start tokens))"
    by (rule initialize_modern_generation_state_correct[OF valid tokens])
  have equality:
    "fst (modern_generate_steps n first_argmax layers embedding start
        vocabulary_size W_vocabulary
        (initialize_modern_generation_state layers embedding start tokens)) =
      modern_full_generate_steps n layers embedding start vocabulary_size
        W_vocabulary
        (fst (initialize_modern_generation_state layers embedding start tokens))"
    by (rule modern_greedy_generate_steps_eq_full[OF state_valid])
  show ?thesis
    using equality
    by (simp add: initialize_modern_generation_state_def)
qed

theorem modern_generate_steps_preserves_vocabulary:
  assumes selector: "valid_token_selector vocabulary_size select"
    and tokens: "tokens_in_vocabulary vocabulary_size (fst state)"
    and cache: "modern_generation_cache_matches embedding layers start
      (fst state) (snd state)"
  shows "tokens_in_vocabulary vocabulary_size
    (fst (modern_generate_steps n select layers embedding start vocabulary_size
      W_vocabulary state))"
  using tokens cache
proof (induction n arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?next = "modern_generation_transition select layers embedding start
    vocabulary_size W_vocabulary state"
  have nonempty: "fst state \<noteq> []"
    using Suc.prems(2) by (simp add: modern_generation_cache_matches_def)
  have distribution_length:
    "length (fst (cached_modern_generation_evaluate layers embedding start
      vocabulary_size W_vocabulary (fst state) (snd state))) = vocabulary_size"
    using nonempty
    by (simp add: cached_modern_generation_evaluate_def Let_def)
  have selected:
    "select (fst (cached_modern_generation_evaluate layers embedding start
      vocabulary_size W_vocabulary (fst state) (snd state))) < vocabulary_size"
    using selector distribution_length
    by (auto simp: valid_token_selector_def)
  have next_tokens: "tokens_in_vocabulary vocabulary_size (fst ?next)"
    using Suc.prems(1) selected
    by (simp add: modern_generation_transition_def deterministic_next_token_def
        tokens_in_vocabulary_def Let_def)
  have next_cache:
    "modern_generation_cache_matches embedding layers start
      (fst ?next) (snd ?next)"
    by (rule modern_generation_transition_cache_invariant[OF Suc.prems(2)])
  show ?case
    by (simp only: modern_generate_steps.simps)
      (rule Suc.IH[OF next_tokens next_cache])
qed

corollary greedy_modern_generation_is_safe:
  assumes "0 < vocabulary_size"
    and "tokens_in_vocabulary vocabulary_size (fst state)"
    and "modern_generation_cache_matches embedding layers start
      (fst state) (snd state)"
  shows "tokens_in_vocabulary vocabulary_size
    (fst (modern_generate_steps n first_argmax layers embedding start
      vocabulary_size W_vocabulary state))"
  apply (rule modern_generate_steps_preserves_vocabulary)
  using assms first_argmax_is_valid_selector by blast+

end
