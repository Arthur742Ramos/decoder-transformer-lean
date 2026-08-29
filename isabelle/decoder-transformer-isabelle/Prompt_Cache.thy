theory Prompt_Cache
  imports Model_Validity
begin

section \<open>Cache Initialization and Whole-Prompt Refinement\<close>

definition empty_layer_cache ::
  "decoder_layer_parameters \<Rightarrow> layer_kv_cache" where
  "empty_layer_cache p =
    replicate (layer_head_count p) (([], []) :: head_kv_cache)"

definition empty_transformer_cache ::
  "decoder_layer_parameters list \<Rightarrow> transformer_kv_cache" where
  "empty_transformer_cache layers = map empty_layer_cache layers"

lemma length_empty_layer_cache [simp]:
  "length (empty_layer_cache p) = layer_head_count p"
  by (simp add: empty_layer_cache_def)

lemma length_empty_transformer_cache [simp]:
  "length (empty_transformer_cache layers) = length layers"
  by (simp add: empty_transformer_cache_def)

theorem empty_layer_cache_matches:
  "layer_cache_matches p [] (empty_layer_cache p)"
  by (simp add: layer_cache_matches_def empty_layer_cache_def
      rms_norm_sequence_def)

lemma full_decoder_layer_empty [simp]:
  "full_decoder_layer p [] = []"
proof -
  have "length (full_decoder_layer p []) = 0"
    using length_full_decoder_layer[of p "[]"] by simp
  then show ?thesis by (rule iffD1[OF length_0_conv])
qed

lemma full_decoder_stack_empty [simp]:
  "full_decoder_stack layers [] = []"
  by (induction layers) simp_all

theorem empty_transformer_cache_matches:
  "transformer_cache_matches layers [] (empty_transformer_cache layers)"
  by (induction layers)
    (simp_all add: empty_transformer_cache_def empty_layer_cache_matches)

fun cached_decoder_stack_run ::
  "decoder_layer_parameters list \<Rightarrow> transformer_kv_cache \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<times> transformer_kv_cache" where
  "cached_decoder_stack_run layers caches [] = ([], caches)"
| "cached_decoder_stack_run layers caches (x # xs) =
    (let step = cached_decoder_stack_step layers x caches;
         rest = cached_decoder_stack_run layers (snd step) xs
     in (fst step # fst rest, snd rest))"

lemma length_cached_decoder_stack_run [simp]:
  "length (fst (cached_decoder_stack_run layers caches xs)) = length xs"
proof (induction xs arbitrary: caches)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: Let_def split: prod.splits)
qed

theorem cached_decoder_stack_run_correct:
  assumes match: "transformer_cache_matches layers prefix caches"
  shows "full_decoder_stack layers (prefix @ xs) =
      full_decoder_stack layers prefix @
        fst (cached_decoder_stack_run layers caches xs)"
    and "transformer_cache_matches layers (prefix @ xs)
      (snd (cached_decoder_stack_run layers caches xs))"
proof -
  have pair:
    "\<And>prefix caches. transformer_cache_matches layers prefix caches \<Longrightarrow>
      full_decoder_stack layers (prefix @ xs) =
        full_decoder_stack layers prefix @
          fst (cached_decoder_stack_run layers caches xs) \<and>
      transformer_cache_matches layers (prefix @ xs)
        (snd (cached_decoder_stack_run layers caches xs))"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    fix prefix caches
    assume current: "transformer_cache_matches layers prefix caches"
    let ?step = "cached_decoder_stack_step layers x caches"
    have one_output:
      "full_decoder_stack layers (prefix @ [x]) =
        full_decoder_stack layers prefix @ [fst ?step]"
      by (rule cached_decoder_stack_step_correct(1)[OF current])
    have one_cache:
      "transformer_cache_matches layers (prefix @ [x]) (snd ?step)"
      by (rule cached_decoder_stack_step_correct(2)[OF current])
    have tail:
      "full_decoder_stack layers ((prefix @ [x]) @ xs) =
          full_decoder_stack layers (prefix @ [x]) @
            fst (cached_decoder_stack_run layers (snd ?step) xs) \<and>
       transformer_cache_matches layers ((prefix @ [x]) @ xs)
          (snd (cached_decoder_stack_run layers (snd ?step) xs))"
      by (rule Cons.IH[OF one_cache])
    show "full_decoder_stack layers (prefix @ x # xs) =
        full_decoder_stack layers prefix @
          fst (cached_decoder_stack_run layers caches (x # xs)) \<and>
      transformer_cache_matches layers (prefix @ x # xs)
        (snd (cached_decoder_stack_run layers caches (x # xs)))"
      using one_output tail
      by (simp add: Let_def)
  qed
  from pair[OF match] show
    "full_decoder_stack layers (prefix @ xs) =
      full_decoder_stack layers prefix @
        fst (cached_decoder_stack_run layers caches xs)"
    and "transformer_cache_matches layers (prefix @ xs)
      (snd (cached_decoder_stack_run layers caches xs))"
    by blast+
qed

corollary initialized_cached_run_equals_full:
  "fst (cached_decoder_stack_run layers (empty_transformer_cache layers) xs) =
    full_decoder_stack layers xs"
proof -
  have "full_decoder_stack layers ([] @ xs) =
    full_decoder_stack layers [] @
      fst (cached_decoder_stack_run layers (empty_transformer_cache layers) xs)"
    by (rule cached_decoder_stack_run_correct(1)
        [OF empty_transformer_cache_matches, where xs=xs])
  then show ?thesis by simp
qed

corollary initialized_cached_run_cache_invariant:
  "transformer_cache_matches layers xs
    (snd (cached_decoder_stack_run layers (empty_transformer_cache layers) xs))"
  by (rule cached_decoder_stack_run_correct(2)
      [OF empty_transformer_cache_matches, where xs=xs, simplified])

definition initialize_generation_state ::
  "decoder_layer_parameters list \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   nat list \<Rightarrow> generation_state" where
  "initialize_generation_state layers embedding tokens =
    (tokens,
      snd (cached_decoder_stack_run layers (empty_transformer_cache layers)
        (map embedding (butlast tokens))))"

theorem initialize_generation_state_correct:
  assumes "tokens \<noteq> []"
  shows "generation_cache_matches embedding layers
    (fst (initialize_generation_state layers embedding tokens))
    (snd (initialize_generation_state layers embedding tokens))"
  using assms initialized_cached_run_cache_invariant
  by (simp add: initialize_generation_state_def generation_cache_matches_def)

theorem initialized_generation_evaluate_correct:
  assumes "tokens \<noteq> []"
  shows "fst (cached_generation_evaluate layers embedding vocabulary_size
      W_vocabulary tokens
      (snd (initialize_generation_state layers embedding tokens))) =
    next_token_distribution vocabulary_size W_vocabulary
      (last (full_decoder_stack layers (map embedding tokens)))"
  by (rule cached_generation_evaluate_correct(1))
    (use initialize_generation_state_correct[OF assms] in
      \<open>simp add: initialize_generation_state_def\<close>)

end
