theory Incremental_Decoder
  imports Decoder_Block
begin

section \<open>Incremental Decoder Stacks\<close>

text \<open>
  Each decoder layer owns one key--value cache per attention head.  The cache
  invariant is stated against the normalized input prefix of that particular
  layer.  Thus later-layer caches track later-layer representations rather than
  the original token embeddings.
\<close>

record decoder_layer_parameters =
  layer_head_count :: nat
  layer_model_dimension :: nat
  layer_head_dimension :: nat
  layer_hidden_dimension :: nat
  layer_norm_epsilon :: real
  layer_activation :: "real \<Rightarrow> real"
  layer_attention_gain :: "real vector"
  layer_mlp_gain :: "real vector"
  layer_query_weights :: "real tensor3"
  layer_key_weights :: "real tensor3"
  layer_value_weights :: "real tensor3"
  layer_output_weights :: "real matrix"
  layer_up_weights :: "real matrix"
  layer_down_weights :: "real matrix"

definition full_decoder_layer ::
  "decoder_layer_parameters \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "full_decoder_layer p =
    decoder_block (layer_head_count p) (layer_model_dimension p)
      (layer_head_dimension p) (layer_hidden_dimension p)
      (layer_norm_epsilon p) (layer_activation p)
      (layer_attention_gain p) (layer_mlp_gain p)
      (layer_query_weights p) (layer_key_weights p) (layer_value_weights p)
      (layer_output_weights p) (layer_up_weights p) (layer_down_weights p)"

definition decoder_layer_at_prefix ::
  "decoder_layer_parameters \<Rightarrow> real matrix \<Rightarrow> real vector \<Rightarrow>
   real vector" where
  "decoder_layer_at_prefix p prefix x =
    (let normalized_x = rms_norm (layer_norm_epsilon p)
        (layer_attention_gain p) x;
       attention = multi_head_at_prefix (layer_head_count p)
        (layer_model_dimension p) (layer_head_dimension p)
        (layer_query_weights p) (layer_key_weights p) (layer_value_weights p)
        (layer_output_weights p) normalized_x
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix @ [normalized_x]);
       attention_residual = vector_add x attention
     in vector_add attention_residual
       (feed_forward (layer_model_dimension p) (layer_hidden_dimension p)
        (layer_activation p) (layer_up_weights p) (layer_down_weights p)
        (rms_norm (layer_norm_epsilon p) (layer_mlp_gain p)
          attention_residual)))"

lemma full_decoder_layer_append:
  "full_decoder_layer p (prefix @ [x]) =
    full_decoder_layer p prefix @ [decoder_layer_at_prefix p prefix x]"
  unfolding full_decoder_layer_def decoder_block_def comp_apply
  unfolding attention_residual_block_append mlp_residual_block_append
  by (simp add: decoder_layer_at_prefix_def Let_def)

lemma length_full_decoder_layer [simp]:
  "length (full_decoder_layer p X) = length X"
  by (simp add: full_decoder_layer_def)

type_synonym head_kv_cache = "real matrix \<times> real matrix"
type_synonym layer_kv_cache = "head_kv_cache list"
type_synonym transformer_kv_cache = "layer_kv_cache list"

definition layer_cache_matches ::
  "decoder_layer_parameters \<Rightarrow> real matrix \<Rightarrow> layer_kv_cache \<Rightarrow>
   bool" where
  "layer_cache_matches p prefix cache \<longleftrightarrow>
    length cache = layer_head_count p \<and>
    (\<forall>h < layer_head_count p.
      fst (cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_key_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) prefix) \<and>
      snd (cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_value_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) prefix))"

definition extend_head_cache ::
  "decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> real vector \<Rightarrow>
   head_kv_cache \<Rightarrow> head_kv_cache" where
  "extend_head_cache p h normalized_x cache =
    (fst cache @ [linear_project (layer_head_dimension p)
      (layer_key_weights p ! h) normalized_x],
     snd cache @ [linear_project (layer_head_dimension p)
      (layer_value_weights p ! h) normalized_x])"

definition extend_layer_cache ::
  "decoder_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   layer_kv_cache \<Rightarrow> layer_kv_cache" where
  "extend_layer_cache p normalized_x cache =
    map (\<lambda>h. extend_head_cache p h normalized_x (cache ! h))
      [0..<layer_head_count p]"

lemma extend_layer_cache_nth:
  assumes "h < layer_head_count p"
  shows "extend_layer_cache p normalized_x cache ! h =
    extend_head_cache p h normalized_x (cache ! h)"
  using assms by (simp add: extend_layer_cache_def)

lemma extend_layer_cache_matches:
  assumes "layer_cache_matches p prefix cache"
  shows "layer_cache_matches p (prefix @ [x])
    (extend_layer_cache p
      (rms_norm (layer_norm_epsilon p) (layer_attention_gain p) x) cache)"
proof -
  let ?nx = "rms_norm (layer_norm_epsilon p) (layer_attention_gain p) x"
  have length_cache:
    "length (extend_layer_cache p ?nx cache) = layer_head_count p"
    by (simp add: extend_layer_cache_def)
  have entries:
    "\<forall>h < layer_head_count p.
      fst (extend_layer_cache p ?nx cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_key_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) (prefix @ [x])) \<and>
      snd (extend_layer_cache p ?nx cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_value_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) (prefix @ [x]))"
  proof (intro allI impI)
    fix h
    assume h: "h < layer_head_count p"
    have old_key:
      "fst (cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_key_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) prefix)"
      using assms h by (auto simp: layer_cache_matches_def)
    have old_value:
      "snd (cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_value_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) prefix)"
      using assms h by (auto simp: layer_cache_matches_def)
    show "fst (extend_layer_cache p ?nx cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_key_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) (prefix @ [x])) \<and>
      snd (extend_layer_cache p ?nx cache ! h) =
        map (linear_project (layer_head_dimension p)
          (layer_value_weights p ! h))
          (rms_norm_sequence (layer_norm_epsilon p)
            (layer_attention_gain p) (prefix @ [x]))"
      using h old_key old_value
      by (simp add: extend_layer_cache_nth extend_head_cache_def
          rms_norm_sequence_def)
  qed
  show ?thesis
    using length_cache entries by (simp add: layer_cache_matches_def)
qed

definition cached_multi_head_output ::
  "decoder_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   layer_kv_cache \<Rightarrow> real vector" where
  "cached_multi_head_output p normalized_x cache =
    linear_project (layer_model_dimension p) (layer_output_weights p)
      (concat (map (\<lambda>h.
        exact_attention (layer_head_dimension p) (layer_head_dimension p)
          (linear_project (layer_head_dimension p)
            (layer_query_weights p ! h) normalized_x)
          (fst (cache ! h)) (snd (cache ! h)))
        [0..<layer_head_count p]))"

lemma cached_multi_head_output_correct:
  fixes x :: "real vector"
  assumes match: "layer_cache_matches p prefix cache"
  defines "normalized_x \<equiv>
    rms_norm (layer_norm_epsilon p) (layer_attention_gain p) x"
  shows "cached_multi_head_output p normalized_x
      (extend_layer_cache p normalized_x cache) =
    multi_head_at_prefix (layer_head_count p) (layer_model_dimension p)
      (layer_head_dimension p) (layer_query_weights p) (layer_key_weights p)
      (layer_value_weights p) (layer_output_weights p) normalized_x
      (rms_norm_sequence (layer_norm_epsilon p)
        (layer_attention_gain p) prefix @ [normalized_x])"
proof -
  have head_cache:
    "\<And>h. h < layer_head_count p \<Longrightarrow>
      extend_layer_cache p normalized_x cache ! h =
      (map (linear_project (layer_head_dimension p)
          (layer_key_weights p ! h))
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix @ [normalized_x]),
       map (linear_project (layer_head_dimension p)
          (layer_value_weights p ! h))
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix @ [normalized_x]))"
  proof -
    fix h
    assume h: "h < layer_head_count p"
    have old_key:
      "fst (cache ! h) = map (linear_project (layer_head_dimension p)
        (layer_key_weights p ! h))
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix)"
      using match h by (auto simp: layer_cache_matches_def)
    have old_value:
      "snd (cache ! h) = map (linear_project (layer_head_dimension p)
        (layer_value_weights p ! h))
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix)"
      using match h by (auto simp: layer_cache_matches_def)
    show "extend_layer_cache p normalized_x cache ! h =
      (map (linear_project (layer_head_dimension p)
          (layer_key_weights p ! h))
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix @ [normalized_x]),
       map (linear_project (layer_head_dimension p)
          (layer_value_weights p ! h))
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix @ [normalized_x]))"
      using h old_key old_value
      by (simp add: extend_layer_cache_nth extend_head_cache_def)
  qed
  have heads_equal:
    "map (\<lambda>h.
      exact_attention (layer_head_dimension p) (layer_head_dimension p)
        (linear_project (layer_head_dimension p)
          (layer_query_weights p ! h) normalized_x)
        (fst (extend_layer_cache p normalized_x cache ! h))
        (snd (extend_layer_cache p normalized_x cache ! h)))
      [0..<layer_head_count p] =
    map (\<lambda>h. projected_head_attention (layer_model_dimension p)
      (layer_head_dimension p) (layer_query_weights p ! h)
      (layer_key_weights p ! h) (layer_value_weights p ! h) normalized_x
      (rms_norm_sequence (layer_norm_epsilon p)
        (layer_attention_gain p) prefix @ [normalized_x]))
      [0..<layer_head_count p]"
    apply (rule map_cong[OF refl])
    using head_cache
    by (auto simp: projected_head_attention_def)
  show ?thesis
    unfolding cached_multi_head_output_def multi_head_at_prefix_def
      concatenated_head_attention_def
    apply (rule arg_cong[where f=
      "linear_project (layer_model_dimension p) (layer_output_weights p)"])
    apply (rule arg_cong[where f=concat])
    by (rule heads_equal)
qed

definition cached_decoder_layer_step ::
  "decoder_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   layer_kv_cache \<Rightarrow> real vector \<times> layer_kv_cache" where
  "cached_decoder_layer_step p x cache =
    (let normalized_x = rms_norm (layer_norm_epsilon p)
        (layer_attention_gain p) x;
       cache' = extend_layer_cache p normalized_x cache;
       attention = cached_multi_head_output p normalized_x cache';
       attention_residual = vector_add x attention;
       output = vector_add attention_residual
        (feed_forward (layer_model_dimension p) (layer_hidden_dimension p)
          (layer_activation p) (layer_up_weights p) (layer_down_weights p)
          (rms_norm (layer_norm_epsilon p) (layer_mlp_gain p)
            attention_residual))
     in (output, cache'))"

theorem cached_decoder_layer_step_correct:
  assumes "layer_cache_matches p prefix cache"
  shows "fst (cached_decoder_layer_step p x cache) =
      decoder_layer_at_prefix p prefix x"
    and "layer_cache_matches p (prefix @ [x])
      (snd (cached_decoder_layer_step p x cache))"
proof -
  let ?nx = "rms_norm (layer_norm_epsilon p) (layer_attention_gain p) x"
  have attention:
    "cached_multi_head_output p ?nx (extend_layer_cache p ?nx cache) =
      multi_head_at_prefix (layer_head_count p) (layer_model_dimension p)
        (layer_head_dimension p) (layer_query_weights p) (layer_key_weights p)
        (layer_value_weights p) (layer_output_weights p) ?nx
        (rms_norm_sequence (layer_norm_epsilon p)
          (layer_attention_gain p) prefix @ [?nx])"
    by (rule cached_multi_head_output_correct[OF assms, where x=x])
  show "fst (cached_decoder_layer_step p x cache) =
    decoder_layer_at_prefix p prefix x"
    using attention
    by (simp add: cached_decoder_layer_step_def decoder_layer_at_prefix_def Let_def)
  show "layer_cache_matches p (prefix @ [x])
    (snd (cached_decoder_layer_step p x cache))"
    unfolding cached_decoder_layer_step_def Let_def snd_conv
    by (rule extend_layer_cache_matches[OF assms])
qed

theorem cached_decoder_layer_step_full:
  assumes "layer_cache_matches p prefix cache"
  shows "full_decoder_layer p (prefix @ [x]) =
      full_decoder_layer p prefix @ [fst (cached_decoder_layer_step p x cache)]"
  unfolding full_decoder_layer_append
  using cached_decoder_layer_step_correct(1)[OF assms] by simp

subsection \<open>Layer-stack refinement\<close>

fun full_decoder_stack ::
  "decoder_layer_parameters list \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "full_decoder_stack [] X = X"
| "full_decoder_stack (p # ps) X =
    full_decoder_stack ps (full_decoder_layer p X)"

fun transformer_cache_matches ::
  "decoder_layer_parameters list \<Rightarrow> real matrix \<Rightarrow>
   transformer_kv_cache \<Rightarrow> bool" where
  "transformer_cache_matches [] prefix caches = (caches = [])"
| "transformer_cache_matches (p # ps) prefix [] = False"
| "transformer_cache_matches (p # ps) prefix (cache # caches) =
    (layer_cache_matches p prefix cache \<and>
      transformer_cache_matches ps (full_decoder_layer p prefix) caches)"

fun cached_decoder_stack_step ::
  "decoder_layer_parameters list \<Rightarrow> real vector \<Rightarrow>
   transformer_kv_cache \<Rightarrow> real vector \<times> transformer_kv_cache" where
  "cached_decoder_stack_step [] x caches = (x, [])"
| "cached_decoder_stack_step (p # ps) x [] = (x, [])"
| "cached_decoder_stack_step (p # ps) x (cache # caches) =
    (let layer_step = cached_decoder_layer_step p x cache;
         stack_step = cached_decoder_stack_step ps (fst layer_step) caches
     in (fst stack_step, snd layer_step # snd stack_step))"

theorem cached_decoder_stack_step_correct:
  assumes match: "transformer_cache_matches layers prefix caches"
  shows "full_decoder_stack layers (prefix @ [x]) =
      full_decoder_stack layers prefix @
        [fst (cached_decoder_stack_step layers x caches)]"
    and "transformer_cache_matches layers (prefix @ [x])
      (snd (cached_decoder_stack_step layers x caches))"
proof -
  have pair:
    "transformer_cache_matches layers prefix caches \<Longrightarrow>
      full_decoder_stack layers (prefix @ [x]) =
        full_decoder_stack layers prefix @
          [fst (cached_decoder_stack_step layers x caches)] \<and>
      transformer_cache_matches layers (prefix @ [x])
        (snd (cached_decoder_stack_step layers x caches))"
  proof (induction layers arbitrary: prefix caches x)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    then obtain cache rest where caches: "caches = cache # rest"
      by (cases caches) auto
    have layer_match: "layer_cache_matches p prefix cache"
      using Cons.prems unfolding caches by simp
    have rest_match:
      "transformer_cache_matches ps (full_decoder_layer p prefix) rest"
      using Cons.prems unfolding caches by simp
    let ?layer_step = "cached_decoder_layer_step p x cache"
    let ?y = "fst ?layer_step"
    let ?cache' = "snd ?layer_step"
    have layer_output: "?y = decoder_layer_at_prefix p prefix x"
      by (rule cached_decoder_layer_step_correct(1)[OF layer_match])
    have layer_cache:
      "layer_cache_matches p (prefix @ [x]) ?cache'"
      by (rule cached_decoder_layer_step_correct(2)[OF layer_match])
    have layer_append:
      "full_decoder_layer p (prefix @ [x]) =
        full_decoder_layer p prefix @ [?y]"
      using full_decoder_layer_append layer_output by simp
    have stack_pair:
      "full_decoder_stack ps (full_decoder_layer p prefix @ [?y]) =
        full_decoder_stack ps (full_decoder_layer p prefix) @
          [fst (cached_decoder_stack_step ps ?y rest)] \<and>
       transformer_cache_matches ps (full_decoder_layer p prefix @ [?y])
        (snd (cached_decoder_stack_step ps ?y rest))"
      by (rule Cons.IH[OF rest_match])
    show ?case
      unfolding caches cached_decoder_stack_step.simps Let_def
      using layer_cache layer_append stack_pair by simp
  qed
  from pair[OF match] show
    "full_decoder_stack layers (prefix @ [x]) =
      full_decoder_stack layers prefix @
        [fst (cached_decoder_stack_step layers x caches)]"
    and "transformer_cache_matches layers (prefix @ [x])
      (snd (cached_decoder_stack_step layers x caches))"
    by blast+
qed

corollary incremental_decoder_equals_full:
  assumes "transformer_cache_matches layers prefix caches"
  shows "fst (cached_decoder_stack_step layers x caches) =
    last (full_decoder_stack layers (prefix @ [x]))"
proof -
  have append:
    "full_decoder_stack layers (prefix @ [x]) =
      full_decoder_stack layers prefix @
        [fst (cached_decoder_stack_step layers x caches)]"
    by (rule cached_decoder_stack_step_correct(1)[OF assms])
  then show ?thesis by simp
qed

end
