theory GPT_Neo_Stack
  imports GPT_Neo_Incremental
begin

section \<open>GPT-Neo Layer Stacks and Prompt Caches\<close>

text \<open>
  A GPT-Neo stack composes the architecture-specific full layer semantics from
  bottom to top.  The cache relation mirrors that composition: the cache for a
  later layer is indexed by the output sequence of every preceding layer.
  This makes the prompt and incremental theorems apply to an arbitrary finite
  number of GPT-Neo blocks without identifying caches from different layers.
\<close>

lemma length_gpt_neo_full_layer [simp]:
  "length (gpt_neo_full_layer p X) = length X"
  by (simp add: gpt_neo_full_layer_def)

fun gpt_neo_full_stack ::
  "gpt_neo_layer_parameters list \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "gpt_neo_full_stack [] X = X"
| "gpt_neo_full_stack (p # ps) X =
    gpt_neo_full_stack ps (gpt_neo_full_layer p X)"

lemma gpt_neo_full_stack_def:
  "gpt_neo_full_stack layers X =
    (case layers of
      [] => X
    | p # ps => gpt_neo_full_stack ps (gpt_neo_full_layer p X))"
proof (cases layers)
  case Nil
  then show ?thesis by simp
next
  case (Cons p ps)
  then show ?thesis by simp
qed

lemma length_gpt_neo_full_stack [simp]:
  "length (gpt_neo_full_stack layers X) = length X"
  by (induction layers arbitrary: X) simp_all

definition valid_gpt_neo_stack ::
  "gpt_neo_layer_parameters list \<Rightarrow> bool" where
  "valid_gpt_neo_stack layers \<longleftrightarrow>
    (\<forall>p \<in> set layers. valid_gpt_neo_layer p)"

definition gpt_neo_stack_compatible ::
  "nat \<Rightarrow> gpt_neo_layer_parameters list \<Rightarrow> bool" where
  "gpt_neo_stack_compatible model_dim layers \<longleftrightarrow>
    (\<forall>p \<in> set layers.
      valid_gpt_neo_layer p \<and> gpt_neo_model_dimension p = model_dim)"

theorem compatible_gpt_neo_full_stack_shape:
  assumes compatible: "gpt_neo_stack_compatible model_dim layers"
    and input: "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim
    (gpt_neo_full_stack layers X)"
  using compatible input
proof (induction layers arbitrary: X)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have p_valid: "valid_gpt_neo_layer p"
    and p_dim: "gpt_neo_model_dimension p = model_dim"
    using Cons.prems(1)
    by (auto simp: gpt_neo_stack_compatible_def)
  have ps_compatible: "gpt_neo_stack_compatible model_dim ps"
    using Cons.prems(1)
    by (simp add: gpt_neo_stack_compatible_def)
  have layer_shape:
    "matrix_shape seq_len model_dim (gpt_neo_full_layer p X)"
    using valid_gpt_neo_full_layer_shape[OF p_valid]
      Cons.prems(2) p_dim by simp
  show ?case
    by simp (rule Cons.IH[OF ps_compatible layer_shape])
qed

type_synonym gpt_neo_layer_cache =
  "gpt_neo_projected_layer_cache"

type_synonym gpt_neo_transformer_cache =
  "gpt_neo_layer_cache list"

fun gpt_neo_transformer_cache_matches ::
  "gpt_neo_layer_parameters list \<Rightarrow> real matrix \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> bool" where
  "gpt_neo_transformer_cache_matches [] prefix caches = (caches = [])"
| "gpt_neo_transformer_cache_matches (p # ps) prefix [] = False"
| "gpt_neo_transformer_cache_matches (p # ps) prefix (cache # caches) =
    (gpt_neo_projected_cache_matches p prefix cache \<and>
      gpt_neo_transformer_cache_matches ps
        (gpt_neo_full_layer p prefix) caches)"

fun gpt_neo_cached_stack_step ::
  "gpt_neo_layer_parameters list \<Rightarrow> real vector \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow>
   real vector \<times> gpt_neo_transformer_cache" where
  "gpt_neo_cached_stack_step [] x caches = (x, [])"
| "gpt_neo_cached_stack_step (p # ps) x [] = (x, [])"
| "gpt_neo_cached_stack_step (p # ps) x (cache # caches) =
    (let layer_step = gpt_neo_projected_cached_block_step p x cache;
         stack_step = gpt_neo_cached_stack_step ps (fst layer_step) caches
     in (fst stack_step, snd layer_step # snd stack_step))"

theorem gpt_neo_cached_stack_step_correct:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_transformer_cache_matches layers prefix caches"
  shows "gpt_neo_full_stack layers (prefix @ [x]) =
      gpt_neo_full_stack layers prefix @
        [fst (gpt_neo_cached_stack_step layers x caches)]"
    and "gpt_neo_transformer_cache_matches layers (prefix @ [x])
      (snd (gpt_neo_cached_stack_step layers x caches))"
proof -
  have pair:
    "\<And>prefix caches x.
      valid_gpt_neo_stack layers \<Longrightarrow>
      gpt_neo_transformer_cache_matches layers prefix caches \<Longrightarrow>
      gpt_neo_full_stack layers (prefix @ [x]) =
        gpt_neo_full_stack layers prefix @
          [fst (gpt_neo_cached_stack_step layers x caches)] \<and>
      gpt_neo_transformer_cache_matches layers (prefix @ [x])
        (snd (gpt_neo_cached_stack_step layers x caches))"
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
    have layer_match: "gpt_neo_projected_cache_matches p prefix cache"
      using Cons.prems(2) unfolding caches by simp
    have rest_match:
      "gpt_neo_transformer_cache_matches ps
        (gpt_neo_full_layer p prefix) rest"
      using Cons.prems(2) unfolding caches by simp
    let ?layer_step = "gpt_neo_projected_cached_block_step p x cache"
    let ?y = "fst ?layer_step"
    let ?cache' = "snd ?layer_step"
    have layer_output:
      "?y = gpt_neo_block_at_prefix p x (prefix @ [x])"
      using gpt_neo_projected_cached_block_step_correct(1)
        [OF p_valid layer_match]
      by simp
    have layer_cache:
      "gpt_neo_projected_cache_matches p (prefix @ [x]) ?cache'"
      by (rule gpt_neo_projected_cached_block_step_correct(2)
        [OF p_valid layer_match])
    have layer_append:
      "gpt_neo_full_layer p (prefix @ [x]) =
        gpt_neo_full_layer p prefix @ [?y]"
      using gpt_neo_full_layer_append layer_output by simp
    have stack_pair:
      "gpt_neo_full_stack ps
          (gpt_neo_full_layer p prefix @ [?y]) =
        gpt_neo_full_stack ps (gpt_neo_full_layer p prefix) @
          [fst (gpt_neo_cached_stack_step ps ?y rest)] \<and>
       gpt_neo_transformer_cache_matches ps
          (gpt_neo_full_layer p prefix @ [?y])
          (snd (gpt_neo_cached_stack_step ps ?y rest))"
      using Cons.IH[OF ps_valid rest_match]
      unfolding layer_append by simp
    show ?case
      unfolding caches gpt_neo_cached_stack_step.simps Let_def
      using layer_cache layer_append stack_pair by simp
  qed
  from pair[OF valid match] show
    "gpt_neo_full_stack layers (prefix @ [x]) =
      gpt_neo_full_stack layers prefix @
        [fst (gpt_neo_cached_stack_step layers x caches)]"
    and "gpt_neo_transformer_cache_matches layers (prefix @ [x])
      (snd (gpt_neo_cached_stack_step layers x caches))"
    by blast+
qed

corollary gpt_neo_cached_stack_step_output:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_transformer_cache_matches layers prefix caches"
  shows "fst (gpt_neo_cached_stack_step layers x caches) =
    last (gpt_neo_full_stack layers (prefix @ [x]))"
  using gpt_neo_cached_stack_step_correct(1)[OF valid match]
  by simp

corollary gpt_neo_cached_stack_step_cache:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_transformer_cache_matches layers prefix caches"
  shows "gpt_neo_transformer_cache_matches layers (prefix @ [x])
      (snd (gpt_neo_cached_stack_step layers x caches))"
  using gpt_neo_cached_stack_step_correct(2)[OF valid match] .

corollary gpt_neo_incremental_equals_full:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_transformer_cache_matches layers prefix caches"
  shows "fst (gpt_neo_cached_stack_step layers x caches) =
    last (gpt_neo_full_stack layers (prefix @ [x]))"
  using gpt_neo_cached_stack_step_correct(1)[OF valid match]
  by simp

fun gpt_neo_cached_stack_run ::
  "gpt_neo_layer_parameters list \<Rightarrow>
   gpt_neo_transformer_cache \<Rightarrow> real vector list \<Rightarrow>
   real vector list \<times> gpt_neo_transformer_cache" where
  "gpt_neo_cached_stack_run layers caches [] = ([], caches)"
| "gpt_neo_cached_stack_run layers caches (x # xs) =
    (let step = gpt_neo_cached_stack_step layers x caches;
         rest = gpt_neo_cached_stack_run layers (snd step) xs
     in (fst step # fst rest, snd rest))"

theorem gpt_neo_cached_stack_run_correct:
  assumes valid: "valid_gpt_neo_stack layers"
    and match:
      "gpt_neo_transformer_cache_matches layers prefix caches"
  shows "gpt_neo_full_stack layers (prefix @ xs) =
      gpt_neo_full_stack layers prefix @
        fst (gpt_neo_cached_stack_run layers caches xs)"
    and "gpt_neo_transformer_cache_matches layers (prefix @ xs)
      (snd (gpt_neo_cached_stack_run layers caches xs))"
proof -
  have pair:
    "\<And>prefix caches.
      gpt_neo_transformer_cache_matches layers prefix caches \<Longrightarrow>
      gpt_neo_full_stack layers (prefix @ xs) =
        gpt_neo_full_stack layers prefix @
          fst (gpt_neo_cached_stack_run layers caches xs) \<and>
      gpt_neo_transformer_cache_matches layers (prefix @ xs)
        (snd (gpt_neo_cached_stack_run layers caches xs))"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    fix prefix caches
    assume current:
      "gpt_neo_transformer_cache_matches layers prefix caches"
    let ?step = "gpt_neo_cached_stack_step layers x caches"
    have one_output:
      "gpt_neo_full_stack layers (prefix @ [x]) =
        gpt_neo_full_stack layers prefix @ [fst ?step]"
      using gpt_neo_cached_stack_step_correct(1)[OF valid current] .
    have one_cache:
      "gpt_neo_transformer_cache_matches layers (prefix @ [x])
        (snd ?step)"
      using gpt_neo_cached_stack_step_correct(2)[OF valid current] .
    have tail:
      "gpt_neo_full_stack layers ((prefix @ [x]) @ xs) =
          gpt_neo_full_stack layers (prefix @ [x]) @
            fst (gpt_neo_cached_stack_run layers (snd ?step) xs) \<and>
       gpt_neo_transformer_cache_matches layers ((prefix @ [x]) @ xs)
          (snd (gpt_neo_cached_stack_run layers (snd ?step) xs))"
      by (rule Cons.IH[OF one_cache])
    show "gpt_neo_full_stack layers (prefix @ x # xs) =
        gpt_neo_full_stack layers prefix @
          fst (gpt_neo_cached_stack_run layers caches (x # xs)) \<and>
      gpt_neo_transformer_cache_matches layers (prefix @ x # xs)
        (snd (gpt_neo_cached_stack_run layers caches (x # xs)))"
      using one_output tail by (simp add: Let_def)
  qed
  from pair[OF match] show
    "gpt_neo_full_stack layers (prefix @ xs) =
      gpt_neo_full_stack layers prefix @
        fst (gpt_neo_cached_stack_run layers caches xs)"
    and "gpt_neo_transformer_cache_matches layers (prefix @ xs)
      (snd (gpt_neo_cached_stack_run layers caches xs))"
    by blast+
qed

definition empty_gpt_neo_transformer_cache ::
  "gpt_neo_layer_parameters list \<Rightarrow> gpt_neo_transformer_cache" where
  "empty_gpt_neo_transformer_cache layers =
    map (\<lambda>p. gpt_neo_projected_empty_cache p) layers"

lemma gpt_neo_full_layer_empty [simp]:
  "gpt_neo_full_layer p [] = []"
proof -
  have "length (gpt_neo_full_layer p []) = 0" by simp
  then show ?thesis by (rule iffD1[OF length_0_conv])
qed

lemma gpt_neo_full_stack_empty [simp]:
  "gpt_neo_full_stack layers [] = []"
  by (induction layers) simp_all

theorem empty_gpt_neo_transformer_cache_matches:
  "gpt_neo_transformer_cache_matches layers []
    (empty_gpt_neo_transformer_cache layers)"
  by (induction layers)
    (simp_all add: empty_gpt_neo_transformer_cache_def
      gpt_neo_projected_empty_cache_matches)

corollary initialized_gpt_neo_cached_run_equals_full:
  assumes "valid_gpt_neo_stack layers"
  shows "fst (gpt_neo_cached_stack_run layers
      (empty_gpt_neo_transformer_cache layers) xs) =
    gpt_neo_full_stack layers xs"
proof -
  have decomposition:
    "gpt_neo_full_stack layers ([] @ xs) =
      gpt_neo_full_stack layers [] @
        fst (gpt_neo_cached_stack_run layers
          (empty_gpt_neo_transformer_cache layers) xs)"
    by (rule gpt_neo_cached_stack_run_correct(1)
        [OF assms empty_gpt_neo_transformer_cache_matches])
  then show ?thesis by simp
qed

corollary initialized_gpt_neo_cached_run_cache_invariant:
  assumes "valid_gpt_neo_stack layers"
  shows "gpt_neo_transformer_cache_matches layers xs
    (snd (gpt_neo_cached_stack_run layers
      (empty_gpt_neo_transformer_cache layers) xs))"
proof -
  have invariant:
    "gpt_neo_transformer_cache_matches layers ([] @ xs)
      (snd (gpt_neo_cached_stack_run layers
        (empty_gpt_neo_transformer_cache layers) xs))"
    by (rule gpt_neo_cached_stack_run_correct(2)
        [OF assms empty_gpt_neo_transformer_cache_matches])
  then show ?thesis by simp
qed

end
