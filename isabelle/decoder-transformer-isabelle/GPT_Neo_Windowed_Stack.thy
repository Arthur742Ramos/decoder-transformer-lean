theory GPT_Neo_Windowed_Stack
  imports GPT_Neo_Stack GPT_Neo_Windowed_Cache
begin

section \<open>GPT-Neo Bounded Cache Stack Refinement\<close>

text \<open>
  The layer-level bounded cache refinement composes through the complete
  GPT-Neo stack.  Each layer stores only its active sliding-window tail, while
  the cache relation continues to be indexed by the full output prefix of all
  preceding layers.
\<close>

fun gpt_neo_bounded_transformer_cache_matches ::
  "gpt_neo_layer_parameters list \<Rightarrow> real matrix \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> bool" where
  "gpt_neo_bounded_transformer_cache_matches [] prefix caches =
    (caches = [])"
| "gpt_neo_bounded_transformer_cache_matches (p # ps) prefix [] =
    False"
| "gpt_neo_bounded_transformer_cache_matches (p # ps) prefix
      (cache # caches) =
    (gpt_neo_projected_bounded_cache_matches p prefix cache \<and>
      gpt_neo_bounded_transformer_cache_matches ps
        (gpt_neo_full_layer p prefix) caches)"

fun gpt_neo_bounded_cached_stack_step ::
  "gpt_neo_layer_parameters list \<Rightarrow> real vector \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow>
   real vector \<times> gpt_neo_transformer_cache" where
  "gpt_neo_bounded_cached_stack_step [] x caches = (x, [])"
| "gpt_neo_bounded_cached_stack_step (p # ps) x [] = (x, [])"
| "gpt_neo_bounded_cached_stack_step (p # ps) x (cache # caches) =
    (let layer_step = gpt_neo_projected_bounded_cached_block_step p x cache;
         stack_step =
           gpt_neo_bounded_cached_stack_step ps (fst layer_step) caches
     in (fst stack_step, snd layer_step # snd stack_step))"

theorem gpt_neo_bounded_cached_stack_step_correct:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_bounded_transformer_cache_matches layers prefix caches"
  shows "gpt_neo_full_stack layers (prefix @ [x]) =
      gpt_neo_full_stack layers prefix @
        [fst (gpt_neo_bounded_cached_stack_step layers x caches)]"
    and "gpt_neo_bounded_transformer_cache_matches layers (prefix @ [x])
      (snd (gpt_neo_bounded_cached_stack_step layers x caches))"
proof -
  have pair:
    "\<And>prefix caches x.
      valid_gpt_neo_stack layers \<Longrightarrow>
      gpt_neo_bounded_transformer_cache_matches layers prefix caches \<Longrightarrow>
      gpt_neo_full_stack layers (prefix @ [x]) =
        gpt_neo_full_stack layers prefix @
          [fst (gpt_neo_bounded_cached_stack_step layers x caches)] \<and>
      gpt_neo_bounded_transformer_cache_matches layers (prefix @ [x])
        (snd (gpt_neo_bounded_cached_stack_step layers x caches))"
  proof (induction layers)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    then obtain cache rest where caches: "caches = cache # rest"
      by (cases caches) auto
    have p_valid: "valid_gpt_neo_layer p"
      using Cons.prems(1)
      by (simp add: valid_gpt_neo_stack_def)
    have ps_valid: "valid_gpt_neo_stack ps"
      using Cons.prems(1)
      by (simp add: valid_gpt_neo_stack_def)
    have layer_match:
      "gpt_neo_projected_bounded_cache_matches p prefix cache"
      using Cons.prems(2) unfolding caches by simp
    have rest_match:
      "gpt_neo_bounded_transformer_cache_matches ps
        (gpt_neo_full_layer p prefix) rest"
      using Cons.prems(2) unfolding caches by simp
    let ?layer_step = "gpt_neo_projected_bounded_cached_block_step p x cache"
    let ?y = "fst ?layer_step"
    let ?cache' = "snd ?layer_step"
    have layer_output:
      "?y = gpt_neo_block_at_prefix p x (prefix @ [x])"
      using gpt_neo_projected_bounded_cached_block_step_correct(1)
        [OF p_valid layer_match]
      by simp
    have layer_cache:
      "gpt_neo_projected_bounded_cache_matches p (prefix @ [x]) ?cache'"
      by (rule gpt_neo_projected_bounded_cached_block_step_correct(2)
        [OF p_valid layer_match])
    have layer_append:
      "gpt_neo_full_layer p (prefix @ [x]) =
        gpt_neo_full_layer p prefix @ [?y]"
      using gpt_neo_full_layer_append layer_output by simp
    have stack_pair:
      "gpt_neo_full_stack ps
          (gpt_neo_full_layer p prefix @ [?y]) =
        gpt_neo_full_stack ps (gpt_neo_full_layer p prefix) @
          [fst (gpt_neo_bounded_cached_stack_step ps ?y rest)] \<and>
       gpt_neo_bounded_transformer_cache_matches ps
          (gpt_neo_full_layer p prefix @ [?y])
          (snd (gpt_neo_bounded_cached_stack_step ps ?y rest))"
      using Cons.IH[OF ps_valid rest_match]
      unfolding layer_append by simp
    show ?case
      unfolding caches gpt_neo_bounded_cached_stack_step.simps Let_def
      using layer_cache layer_append stack_pair by simp
  qed
  from pair[OF valid match] show
    "gpt_neo_full_stack layers (prefix @ [x]) =
      gpt_neo_full_stack layers prefix @
        [fst (gpt_neo_bounded_cached_stack_step layers x caches)]"
    and "gpt_neo_bounded_transformer_cache_matches layers (prefix @ [x])
      (snd (gpt_neo_bounded_cached_stack_step layers x caches))"
    by blast+
qed

corollary gpt_neo_bounded_cached_stack_step_output:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_bounded_transformer_cache_matches layers prefix caches"
  shows "fst (gpt_neo_bounded_cached_stack_step layers x caches) =
    last (gpt_neo_full_stack layers (prefix @ [x]))"
  using gpt_neo_bounded_cached_stack_step_correct(1)[OF valid match]
  by simp

corollary gpt_neo_bounded_cached_stack_step_cache:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_bounded_transformer_cache_matches layers prefix caches"
  shows "gpt_neo_bounded_transformer_cache_matches layers (prefix @ [x])
      (snd (gpt_neo_bounded_cached_stack_step layers x caches))"
  using gpt_neo_bounded_cached_stack_step_correct(2)[OF valid match] .

corollary gpt_neo_bounded_incremental_equals_full:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_bounded_transformer_cache_matches layers prefix caches"
  shows "fst (gpt_neo_bounded_cached_stack_step layers x caches) =
    last (gpt_neo_full_stack layers (prefix @ [x]))"
  using gpt_neo_bounded_cached_stack_step_correct(1)[OF valid match]
  by simp

fun gpt_neo_bounded_cached_stack_run ::
  "gpt_neo_layer_parameters list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> real vector list \<Rightarrow>
   real vector list \<times> gpt_neo_transformer_cache" where
  "gpt_neo_bounded_cached_stack_run layers caches [] = ([], caches)"
| "gpt_neo_bounded_cached_stack_run layers caches (x # xs) =
    (let step = gpt_neo_bounded_cached_stack_step layers x caches;
         rest =
           gpt_neo_bounded_cached_stack_run layers (snd step) xs
     in (fst step # fst rest, snd rest))"

theorem gpt_neo_bounded_cached_stack_run_correct:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_bounded_transformer_cache_matches layers prefix caches"
  shows "gpt_neo_full_stack layers (prefix @ xs) =
      gpt_neo_full_stack layers prefix @
        fst (gpt_neo_bounded_cached_stack_run layers caches xs)"
    and "gpt_neo_bounded_transformer_cache_matches layers (prefix @ xs)
      (snd (gpt_neo_bounded_cached_stack_run layers caches xs))"
proof -
  have pair:
    "\<And>prefix caches.
      gpt_neo_bounded_transformer_cache_matches layers prefix caches \<Longrightarrow>
      gpt_neo_full_stack layers (prefix @ xs) =
        gpt_neo_full_stack layers prefix @
          fst (gpt_neo_bounded_cached_stack_run layers caches xs) \<and>
      gpt_neo_bounded_transformer_cache_matches layers (prefix @ xs)
        (snd (gpt_neo_bounded_cached_stack_run layers caches xs))"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    fix prefix caches
    assume current:
      "gpt_neo_bounded_transformer_cache_matches layers prefix caches"
    let ?step = "gpt_neo_bounded_cached_stack_step layers x caches"
    have one_output:
      "gpt_neo_full_stack layers (prefix @ [x]) =
        gpt_neo_full_stack layers prefix @ [fst ?step]"
      using gpt_neo_bounded_cached_stack_step_correct(1)
        [OF valid current] .
    have one_cache:
      "gpt_neo_bounded_transformer_cache_matches layers (prefix @ [x])
        (snd ?step)"
      using gpt_neo_bounded_cached_stack_step_correct(2)
        [OF valid current] .
    have tail:
      "gpt_neo_full_stack layers ((prefix @ [x]) @ xs) =
          gpt_neo_full_stack layers (prefix @ [x]) @
            fst (gpt_neo_bounded_cached_stack_run
              layers (snd ?step) xs) \<and>
       gpt_neo_bounded_transformer_cache_matches layers ((prefix @ [x]) @ xs)
          (snd (gpt_neo_bounded_cached_stack_run
            layers (snd ?step) xs))"
      by (rule Cons.IH[OF one_cache])
    show "gpt_neo_full_stack layers (prefix @ x # xs) =
        gpt_neo_full_stack layers prefix @
          fst (gpt_neo_bounded_cached_stack_run layers caches (x # xs)) \<and>
      gpt_neo_bounded_transformer_cache_matches layers (prefix @ x # xs)
        (snd (gpt_neo_bounded_cached_stack_run layers caches (x # xs)))"
      using one_output tail by (simp add: Let_def)
  qed
  from pair[OF match] show
    "gpt_neo_full_stack layers (prefix @ xs) =
      gpt_neo_full_stack layers prefix @
        fst (gpt_neo_bounded_cached_stack_run layers caches xs)"
    and "gpt_neo_bounded_transformer_cache_matches layers (prefix @ xs)
      (snd (gpt_neo_bounded_cached_stack_run layers caches xs))"
    by blast+
qed

definition empty_gpt_neo_bounded_transformer_cache ::
  "gpt_neo_layer_parameters list \<Rightarrow> gpt_neo_transformer_cache" where
  "empty_gpt_neo_bounded_transformer_cache layers =
    map (\<lambda>p. gpt_neo_projected_bounded_empty_cache p) layers"

lemma gpt_neo_bounded_cache_matches_empty:
  "gpt_neo_projected_bounded_cache_matches p []
    (gpt_neo_projected_bounded_empty_cache p)"
  by (simp add: gpt_neo_projected_bounded_cache_matches_def
      gpt_neo_projected_bounded_empty_cache_def
      gpt_neo_projected_empty_cache_def
      gpt_neo_projected_bounded_cache_of_def
      gpt_neo_projected_bounded_head_cache_of_def
      cache_of_def gpt_neo_attention_context_def
      gpt_neo_local_context_def)

theorem empty_gpt_neo_bounded_transformer_cache_matches:
  "gpt_neo_bounded_transformer_cache_matches layers []
    (empty_gpt_neo_bounded_transformer_cache layers)"
  by (induction layers)
    (simp_all add: empty_gpt_neo_bounded_transformer_cache_def
      gpt_neo_bounded_cache_matches_empty)

corollary initialized_gpt_neo_bounded_cached_run_equals_full:
  assumes "valid_gpt_neo_stack layers"
  shows "fst (gpt_neo_bounded_cached_stack_run layers
      (empty_gpt_neo_bounded_transformer_cache layers) xs) =
    gpt_neo_full_stack layers xs"
proof -
  have decomposition:
    "gpt_neo_full_stack layers ([] @ xs) =
      gpt_neo_full_stack layers [] @
        fst (gpt_neo_bounded_cached_stack_run layers
          (empty_gpt_neo_bounded_transformer_cache layers) xs)"
    by (rule gpt_neo_bounded_cached_stack_run_correct(1)
        [OF assms empty_gpt_neo_bounded_transformer_cache_matches])
  then show ?thesis by simp
qed

corollary initialized_gpt_neo_bounded_cached_run_cache_invariant:
  assumes "valid_gpt_neo_stack layers"
  shows "gpt_neo_bounded_transformer_cache_matches layers xs
    (snd (gpt_neo_bounded_cached_stack_run layers
      (empty_gpt_neo_bounded_transformer_cache layers) xs))"
proof -
  have invariant:
    "gpt_neo_bounded_transformer_cache_matches layers ([] @ xs)
      (snd (gpt_neo_bounded_cached_stack_run layers
        (empty_gpt_neo_bounded_transformer_cache layers) xs))"
    by (rule gpt_neo_bounded_cached_stack_run_correct(2)
        [OF assms empty_gpt_neo_bounded_transformer_cache_matches])
  then show ?thesis by simp
qed

end
