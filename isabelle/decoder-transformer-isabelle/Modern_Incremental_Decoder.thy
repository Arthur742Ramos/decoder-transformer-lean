theory Modern_Incremental_Decoder
  imports Decoding_Policies
begin

section \<open>A Unified Modern Decoder Layer\<close>

record modern_decoder_layer_parameters =
  modern_query_head_count :: nat
  modern_kv_head_count :: nat
  modern_model_dimension :: nat
  modern_head_dimension :: nat
  modern_hidden_dimension :: nat
  modern_norm_epsilon :: real
  modern_rope :: "nat \<Rightarrow> real vector \<Rightarrow> real vector"
  modern_attention_gain :: "real vector"
  modern_mlp_gain :: "real vector"
  modern_query_weights :: "real tensor3"
  modern_key_weights :: "real tensor3"
  modern_value_weights :: "real tensor3"
  modern_output_weights :: "real matrix"
  modern_gate_weights :: "real matrix"
  modern_up_weights :: "real matrix"
  modern_down_weights :: "real matrix"

definition valid_modern_decoder_layer ::
  "modern_decoder_layer_parameters \<Rightarrow> bool" where
  "valid_modern_decoder_layer p \<longleftrightarrow>
    0 < modern_query_head_count p \<and>
    0 < modern_kv_head_count p \<and>
    0 < modern_model_dimension p \<and>
    0 < modern_head_dimension p \<and>
    0 < modern_hidden_dimension p \<and>
    modern_model_dimension p =
      modern_query_head_count p * modern_head_dimension p \<and>
    modern_kv_head_count p dvd modern_query_head_count p \<and>
    0 < modern_norm_epsilon p \<and>
    vector_shape (modern_model_dimension p) (modern_attention_gain p) \<and>
    vector_shape (modern_model_dimension p) (modern_mlp_gain p) \<and>
    tensor3_shape (modern_query_head_count p) (modern_model_dimension p)
      (modern_head_dimension p) (modern_query_weights p) \<and>
    tensor3_shape (modern_kv_head_count p) (modern_model_dimension p)
      (modern_head_dimension p) (modern_key_weights p) \<and>
    tensor3_shape (modern_kv_head_count p) (modern_model_dimension p)
      (modern_head_dimension p) (modern_value_weights p) \<and>
    matrix_shape (modern_query_head_count p * modern_head_dimension p)
      (modern_model_dimension p) (modern_output_weights p) \<and>
    matrix_shape (modern_model_dimension p) (modern_hidden_dimension p)
      (modern_gate_weights p) \<and>
    matrix_shape (modern_model_dimension p) (modern_hidden_dimension p)
      (modern_up_weights p) \<and>
    matrix_shape (modern_hidden_dimension p) (modern_model_dimension p)
      (modern_down_weights p) \<and>
    (\<forall>position x. vector_shape (modern_head_dimension p) x \<longrightarrow>
      vector_shape (modern_head_dimension p) (modern_rope p position x))"

definition modern_normalize ::
  "modern_decoder_layer_parameters \<Rightarrow> real vector \<Rightarrow> real vector" where
  "modern_normalize p x =
    rms_norm (modern_norm_epsilon p) (modern_attention_gain p) x"

definition modern_key_at ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "modern_key_at p kv_head position x =
    modern_rope p position
      (linear_project (modern_head_dimension p)
        (modern_key_weights p ! kv_head) (modern_normalize p x))"

definition modern_value_at ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "modern_value_at p kv_head x =
    linear_project (modern_head_dimension p)
      (modern_value_weights p ! kv_head) (modern_normalize p x)"

definition modern_query_at ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "modern_query_at p query_head position x =
    modern_rope p position
      (linear_project (modern_head_dimension p)
        (modern_query_weights p ! query_head) (modern_normalize p x))"

definition modern_grouped_attention_at_prefix ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<times> real vector \<Rightarrow>
   (nat \<times> real vector) list \<Rightarrow> real vector" where
  "modern_grouped_attention_at_prefix p ix prefix =
    linear_project (modern_model_dimension p) (modern_output_weights p)
      (concat (map (\<lambda>h.
        let g = grouped_query_head_index
          (modern_query_head_count p) (modern_kv_head_count p) h
        in exact_attention (modern_head_dimension p) (modern_head_dimension p)
          (modern_query_at p h (fst ix) (snd ix))
          (map (\<lambda>jx. modern_key_at p g (fst jx) (snd jx)) prefix)
          (map (\<lambda>jx. modern_value_at p g (snd jx)) prefix))
        [0..<modern_query_head_count p]))"

definition modern_decoder_at_indexed_prefix ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<times> real vector \<Rightarrow>
   (nat \<times> real vector) list \<Rightarrow> real vector" where
  "modern_decoder_at_indexed_prefix p ix prefix =
    (let x = snd ix;
         attention = modern_grouped_attention_at_prefix p ix prefix;
         attention_residual = vector_add x attention;
         mlp_input = rms_norm (modern_norm_epsilon p) (modern_mlp_gain p)
          attention_residual;
         mlp = swiglu (modern_model_dimension p) (modern_hidden_dimension p)
          (modern_gate_weights p) (modern_up_weights p)
          (modern_down_weights p) mlp_input
     in vector_add attention_residual mlp)"

definition full_modern_decoder_layer ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow>
   real matrix \<Rightarrow> real matrix" where
  "full_modern_decoder_layer p start X =
    causal_attention id id id
      (\<lambda>ix prefix ignored. modern_decoder_at_indexed_prefix p ix prefix)
      (indexed_sequence start X)"

lemma length_full_modern_decoder_layer [simp]:
  "length (full_modern_decoder_layer p start X) = length X"
  by (simp add: full_modern_decoder_layer_def)

lemma full_modern_decoder_layer_append:
  "full_modern_decoder_layer p start (prefix @ [x]) =
    full_modern_decoder_layer p start prefix @
      [modern_decoder_at_indexed_prefix p (start + length prefix, x)
        (indexed_sequence start (prefix @ [x]))]"
proof -
  let ?A = "\<lambda>ix prefix ignored.
    modern_decoder_at_indexed_prefix p ix prefix"
  have indexed:
    "indexed_sequence start (prefix @ [x]) =
      indexed_sequence start prefix @ [(start + length prefix, x)]"
    by (rule indexed_sequence_append_singleton)
  have append:
    "causal_attention id id id ?A
        (indexed_sequence start prefix @ [(start + length prefix, x)]) =
      causal_attention id id id ?A (indexed_sequence start prefix) @
      causal_attention_from id id id ?A (indexed_sequence start prefix)
        [(start + length prefix, x)]"
    by (rule causal_attention_append)
  show ?thesis
    unfolding full_modern_decoder_layer_def indexed append
    by simp
qed

lemma valid_modern_attention_shape:
  assumes valid: "valid_modern_decoder_layer p"
  shows "vector_shape (modern_model_dimension p)
    (modern_grouped_attention_at_prefix p ix prefix)"
proof -
  have rows:
    "\<forall>row \<in> set (map (\<lambda>h.
      let g = grouped_query_head_index
        (modern_query_head_count p) (modern_kv_head_count p) h
      in exact_attention (modern_head_dimension p) (modern_head_dimension p)
        (modern_query_at p h (fst ix) (snd ix))
        (map (\<lambda>jx. modern_key_at p g (fst jx) (snd jx)) prefix)
        (map (\<lambda>jx. modern_value_at p g (snd jx)) prefix))
      [0..<modern_query_head_count p]).
      length row = modern_head_dimension p"
    using exact_attention_shape
    by (auto simp: vector_shape_def Let_def)
  have concatenated:
    "vector_shape (modern_query_head_count p * modern_head_dimension p)
      (concat (map (\<lambda>h.
        let g = grouped_query_head_index
          (modern_query_head_count p) (modern_kv_head_count p) h
        in exact_attention (modern_head_dimension p) (modern_head_dimension p)
          (modern_query_at p h (fst ix) (snd ix))
          (map (\<lambda>jx. modern_key_at p g (fst jx) (snd jx)) prefix)
          (map (\<lambda>jx. modern_value_at p g (snd jx)) prefix))
        [0..<modern_query_head_count p]))"
    unfolding vector_shape_def
    using concat_rows_length[OF rows] by simp
  have output_shape:
    "matrix_shape (modern_query_head_count p * modern_head_dimension p)
      (modern_model_dimension p) (modern_output_weights p)"
    using valid unfolding valid_modern_decoder_layer_def by blast
  show ?thesis
    unfolding modern_grouped_attention_at_prefix_def
    by (rule linear_project_shape[OF output_shape concatenated])
qed

theorem valid_modern_decoder_at_prefix_shape:
  assumes valid: "valid_modern_decoder_layer p"
    and input: "vector_shape (modern_model_dimension p) (snd ix)"
  shows "vector_shape (modern_model_dimension p)
    (modern_decoder_at_indexed_prefix p ix prefix)"
proof -
  have attention:
    "vector_shape (modern_model_dimension p)
      (modern_grouped_attention_at_prefix p ix prefix)"
    by (rule valid_modern_attention_shape[OF valid])
  have residual:
    "vector_shape (modern_model_dimension p)
      (vector_add (snd ix) (modern_grouped_attention_at_prefix p ix prefix))"
    by (rule vector_add_shape[OF input attention])
  have gain:
    "vector_shape (modern_model_dimension p) (modern_mlp_gain p)"
    using valid unfolding valid_modern_decoder_layer_def by blast
  have normalized:
    "vector_shape (modern_model_dimension p)
      (rms_norm (modern_norm_epsilon p) (modern_mlp_gain p)
        (vector_add (snd ix) (modern_grouped_attention_at_prefix p ix prefix)))"
    by (rule rms_norm_shape[OF gain residual])
  have matrices:
    "matrix_shape (modern_model_dimension p) (modern_hidden_dimension p)
      (modern_gate_weights p)"
    "matrix_shape (modern_model_dimension p) (modern_hidden_dimension p)
      (modern_up_weights p)"
    "matrix_shape (modern_hidden_dimension p) (modern_model_dimension p)
      (modern_down_weights p)"
    using valid unfolding valid_modern_decoder_layer_def by blast+
  have mlp:
    "vector_shape (modern_model_dimension p)
      (swiglu (modern_model_dimension p) (modern_hidden_dimension p)
        (modern_gate_weights p) (modern_up_weights p) (modern_down_weights p)
        (rms_norm (modern_norm_epsilon p) (modern_mlp_gain p)
          (vector_add (snd ix)
            (modern_grouped_attention_at_prefix p ix prefix))))"
    by (rule swiglu_shape[OF normalized matrices])
  show ?thesis
    unfolding modern_decoder_at_indexed_prefix_def Let_def
    by (rule vector_add_shape[OF residual mlp])
qed

theorem valid_full_modern_decoder_layer_shape:
  assumes valid: "valid_modern_decoder_layer p"
    and input: "matrix_shape seq_len (modern_model_dimension p) X"
  shows "matrix_shape seq_len (modern_model_dimension p)
    (full_modern_decoder_layer p start X)"
proof -
  let ?A = "\<lambda>ix prefix ignored.
    modern_decoder_at_indexed_prefix p ix prefix"
  have indexed_rows:
    "\<forall>ix \<in> set (indexed_sequence start X).
      vector_shape (modern_model_dimension p) (snd ix)"
    using input
    by (auto simp: indexed_sequence_def matrix_shape_def vector_shape_def
        in_set_zip)
  have from_shape:
    "\<And>xs prefix. (\<forall>ix \<in> set xs.
        vector_shape (modern_model_dimension p) (snd ix)) \<Longrightarrow>
      matrix_shape (length xs) (modern_model_dimension p)
        (causal_attention_from id id id ?A prefix xs)"
  proof -
    fix xs prefix :: "(nat \<times> real vector) list"
    assume rows:
      "\<forall>ix \<in> set xs. vector_shape (modern_model_dimension p) (snd ix)"
    show "matrix_shape (length xs) (modern_model_dimension p)
      (causal_attention_from id id id ?A prefix xs)"
      using rows
    proof (induction xs arbitrary: prefix)
      case Nil
      then show ?case by (simp add: matrix_shape_def)
    next
      case (Cons ix xs)
      have head_shape:
        "vector_shape (modern_model_dimension p)
          (modern_decoder_at_indexed_prefix p ix (prefix @ [ix]))"
        by (rule valid_modern_decoder_at_prefix_shape[OF valid])
          (use Cons.prems in auto)
      have tail_shape:
        "matrix_shape (length xs) (modern_model_dimension p)
          (causal_attention_from id id id ?A (prefix @ [ix]) xs)"
        by (rule Cons.IH) (use Cons.prems in auto)
      show ?case
        using head_shape tail_shape
        by (auto simp: matrix_shape_def vector_shape_def id_def)
    qed
  qed
  have result:
    "matrix_shape (length (indexed_sequence start X))
      (modern_model_dimension p)
      (causal_attention_from id id id ?A [] (indexed_sequence start X))"
    by (rule from_shape[OF indexed_rows])
  show ?thesis
    using input result
    by (simp add: full_modern_decoder_layer_def causal_attention_def
        matrix_shape_def)
qed

fun full_modern_decoder_stack ::
  "modern_decoder_layer_parameters list \<Rightarrow> nat \<Rightarrow>
   real matrix \<Rightarrow> real matrix" where
  "full_modern_decoder_stack [] start X = X"
| "full_modern_decoder_stack (p # ps) start X =
    full_modern_decoder_stack ps start (full_modern_decoder_layer p start X)"

section \<open>Grouped Rotary Key--Value Caches\<close>

definition modern_layer_cache_matches ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow>
   layer_kv_cache \<Rightarrow> bool" where
  "modern_layer_cache_matches p start prefix cache \<longleftrightarrow>
    length cache = modern_kv_head_count p \<and>
    (\<forall>g < modern_kv_head_count p.
      fst (cache ! g) =
        map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
          (indexed_sequence start prefix) \<and>
      snd (cache ! g) =
        map (\<lambda>ix. modern_value_at p g (snd ix))
          (indexed_sequence start prefix))"

definition empty_modern_layer_cache ::
  "modern_decoder_layer_parameters \<Rightarrow> layer_kv_cache" where
  "empty_modern_layer_cache p =
    replicate (modern_kv_head_count p) (([], []) :: head_kv_cache)"

lemma empty_modern_layer_cache_matches:
  "modern_layer_cache_matches p start [] (empty_modern_layer_cache p)"
  by (simp add: modern_layer_cache_matches_def empty_modern_layer_cache_def
      indexed_sequence_def)

definition modern_extend_head_cache ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> head_kv_cache \<Rightarrow> head_kv_cache" where
  "modern_extend_head_cache p g position x cache =
    (fst cache @ [modern_key_at p g position x],
     snd cache @ [modern_value_at p g x])"

definition modern_extend_layer_cache ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> real vector \<Rightarrow>
   layer_kv_cache \<Rightarrow> layer_kv_cache" where
  "modern_extend_layer_cache p position x cache =
    map (\<lambda>g. modern_extend_head_cache p g position x (cache ! g))
      [0..<modern_kv_head_count p]"

lemma modern_extend_layer_cache_nth:
  assumes "g < modern_kv_head_count p"
  shows "modern_extend_layer_cache p position x cache ! g =
    modern_extend_head_cache p g position x (cache ! g)"
  using assms by (simp add: modern_extend_layer_cache_def)

theorem modern_extend_layer_cache_matches:
  assumes match: "modern_layer_cache_matches p start prefix cache"
  shows "modern_layer_cache_matches p start (prefix @ [x])
    (modern_extend_layer_cache p (start + length prefix) x cache)"
proof -
  let ?position = "start + length prefix"
  have length_cache:
    "length (modern_extend_layer_cache p ?position x cache) =
      modern_kv_head_count p"
    by (simp add: modern_extend_layer_cache_def)
  have entries:
    "\<forall>g < modern_kv_head_count p.
      fst (modern_extend_layer_cache p ?position x cache ! g) =
        map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
          (indexed_sequence start (prefix @ [x])) \<and>
      snd (modern_extend_layer_cache p ?position x cache ! g) =
        map (\<lambda>ix. modern_value_at p g (snd ix))
          (indexed_sequence start (prefix @ [x]))"
  proof (intro allI impI)
    fix g
    assume g: "g < modern_kv_head_count p"
    have old_key:
      "fst (cache ! g) =
        map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
          (indexed_sequence start prefix)"
      using match g by (auto simp: modern_layer_cache_matches_def)
    have old_value:
      "snd (cache ! g) =
        map (\<lambda>ix. modern_value_at p g (snd ix))
          (indexed_sequence start prefix)"
      using match g by (auto simp: modern_layer_cache_matches_def)
    show "fst (modern_extend_layer_cache p ?position x cache ! g) =
        map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
          (indexed_sequence start (prefix @ [x])) \<and>
      snd (modern_extend_layer_cache p ?position x cache ! g) =
        map (\<lambda>ix. modern_value_at p g (snd ix))
          (indexed_sequence start (prefix @ [x]))"
      using g old_key old_value
      by (simp add: modern_extend_layer_cache_nth modern_extend_head_cache_def
          indexed_sequence_append_singleton)
  qed
  show ?thesis
    using length_cache entries
    by (simp add: modern_layer_cache_matches_def)
qed

definition cached_modern_grouped_attention ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> real vector \<Rightarrow>
   layer_kv_cache \<Rightarrow> real vector" where
  "cached_modern_grouped_attention p position x cache =
    linear_project (modern_model_dimension p) (modern_output_weights p)
      (concat (map (\<lambda>h.
        let g = grouped_query_head_index
          (modern_query_head_count p) (modern_kv_head_count p) h
        in exact_attention (modern_head_dimension p) (modern_head_dimension p)
          (modern_query_at p h position x)
          (fst (cache ! g)) (snd (cache ! g)))
        [0..<modern_query_head_count p]))"

theorem cached_modern_grouped_attention_correct:
  assumes valid: "valid_modern_decoder_layer p"
    and match: "modern_layer_cache_matches p start prefix cache"
  shows "cached_modern_grouped_attention p (start + length prefix) x
      (modern_extend_layer_cache p (start + length prefix) x cache) =
    modern_grouped_attention_at_prefix p (start + length prefix, x)
      (indexed_sequence start (prefix @ [x]))"
proof -
  let ?position = "start + length prefix"
  let ?cache' = "modern_extend_layer_cache p ?position x cache"
  have query_positive: "0 < modern_query_head_count p"
    using valid unfolding valid_modern_decoder_layer_def by blast
  have kv_positive: "0 < modern_kv_head_count p"
    using valid unfolding valid_modern_decoder_layer_def by blast
  have groups:
    "modern_kv_head_count p dvd modern_query_head_count p"
    using valid unfolding valid_modern_decoder_layer_def by blast
  have cache_entry:
    "\<And>g. g < modern_kv_head_count p \<Longrightarrow>
      ?cache' ! g =
      (map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
        (indexed_sequence start (prefix @ [x])),
       map (\<lambda>ix. modern_value_at p g (snd ix))
        (indexed_sequence start (prefix @ [x])))"
  proof -
    fix g
    assume g: "g < modern_kv_head_count p"
    have old_key:
      "fst (cache ! g) =
        map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
          (indexed_sequence start prefix)"
      using match g by (auto simp: modern_layer_cache_matches_def)
    have old_value:
      "snd (cache ! g) =
        map (\<lambda>ix. modern_value_at p g (snd ix))
          (indexed_sequence start prefix)"
      using match g by (auto simp: modern_layer_cache_matches_def)
    show "?cache' ! g =
      (map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
        (indexed_sequence start (prefix @ [x])),
       map (\<lambda>ix. modern_value_at p g (snd ix))
        (indexed_sequence start (prefix @ [x])))"
      using g old_key old_value
      by (simp add: modern_extend_layer_cache_nth modern_extend_head_cache_def
          indexed_sequence_append_singleton)
  qed
  have heads:
    "map (\<lambda>h.
      let g = grouped_query_head_index
        (modern_query_head_count p) (modern_kv_head_count p) h
      in exact_attention (modern_head_dimension p) (modern_head_dimension p)
        (modern_query_at p h ?position x)
        (fst (?cache' ! g)) (snd (?cache' ! g)))
      [0..<modern_query_head_count p] =
    map (\<lambda>h.
      let g = grouped_query_head_index
        (modern_query_head_count p) (modern_kv_head_count p) h
      in exact_attention (modern_head_dimension p) (modern_head_dimension p)
        (modern_query_at p h ?position x)
        (map (\<lambda>ix. modern_key_at p g (fst ix) (snd ix))
          (indexed_sequence start (prefix @ [x])))
        (map (\<lambda>ix. modern_value_at p g (snd ix))
          (indexed_sequence start (prefix @ [x]))))
      [0..<modern_query_head_count p]"
    apply (rule map_cong[OF refl])
    using query_positive kv_positive groups cache_entry
      grouped_query_head_index_bound
    by (auto simp: Let_def)
  show ?thesis
    unfolding cached_modern_grouped_attention_def
      modern_grouped_attention_at_prefix_def
    apply (rule arg_cong[where f=
      "linear_project (modern_model_dimension p) (modern_output_weights p)"])
    apply (rule arg_cong[where f=concat])
    using heads by simp
qed

definition cached_modern_decoder_layer_step ::
  "modern_decoder_layer_parameters \<Rightarrow> nat \<Rightarrow> real vector \<Rightarrow>
   layer_kv_cache \<Rightarrow> real vector \<times> layer_kv_cache" where
  "cached_modern_decoder_layer_step p position x cache =
    (let cache' = modern_extend_layer_cache p position x cache;
         attention = cached_modern_grouped_attention p position x cache';
         attention_residual = vector_add x attention;
         mlp_input = rms_norm (modern_norm_epsilon p) (modern_mlp_gain p)
          attention_residual;
         mlp = swiglu (modern_model_dimension p) (modern_hidden_dimension p)
          (modern_gate_weights p) (modern_up_weights p)
          (modern_down_weights p) mlp_input
     in (vector_add attention_residual mlp, cache'))"

theorem cached_modern_decoder_layer_step_correct:
  assumes valid: "valid_modern_decoder_layer p"
    and match: "modern_layer_cache_matches p start prefix cache"
  shows "fst (cached_modern_decoder_layer_step p (start + length prefix) x cache) =
      modern_decoder_at_indexed_prefix p (start + length prefix, x)
        (indexed_sequence start (prefix @ [x]))"
    and "modern_layer_cache_matches p start (prefix @ [x])
      (snd (cached_modern_decoder_layer_step p (start + length prefix) x cache))"
proof -
  let ?position = "start + length prefix"
  let ?cache' = "modern_extend_layer_cache p ?position x cache"
  have attention:
    "cached_modern_grouped_attention p ?position x ?cache' =
      modern_grouped_attention_at_prefix p (?position, x)
        (indexed_sequence start (prefix @ [x]))"
    by (rule cached_modern_grouped_attention_correct[OF valid match])
  show "fst (cached_modern_decoder_layer_step p ?position x cache) =
    modern_decoder_at_indexed_prefix p (?position, x)
      (indexed_sequence start (prefix @ [x]))"
    using attention
    by (simp add: cached_modern_decoder_layer_step_def
        modern_decoder_at_indexed_prefix_def Let_def)
  show "modern_layer_cache_matches p start (prefix @ [x])
    (snd (cached_modern_decoder_layer_step p ?position x cache))"
    unfolding cached_modern_decoder_layer_step_def Let_def snd_conv
    by (rule modern_extend_layer_cache_matches[OF match])
qed

corollary cached_modern_decoder_layer_step_full:
  assumes "valid_modern_decoder_layer p"
    and "modern_layer_cache_matches p start prefix cache"
  shows "full_modern_decoder_layer p start (prefix @ [x]) =
    full_modern_decoder_layer p start prefix @
      [fst (cached_modern_decoder_layer_step p (start + length prefix) x cache)]"
  unfolding full_modern_decoder_layer_append
  using cached_modern_decoder_layer_step_correct(1)[OF assms]
  by simp

section \<open>Modern Decoder-Stack Refinement\<close>

definition valid_modern_decoder_stack ::
  "modern_decoder_layer_parameters list \<Rightarrow> bool" where
  "valid_modern_decoder_stack layers \<longleftrightarrow>
    (\<forall>p \<in> set layers. valid_modern_decoder_layer p)"

definition modern_decoder_stack_compatible ::
  "nat \<Rightarrow> modern_decoder_layer_parameters list \<Rightarrow> bool" where
  "modern_decoder_stack_compatible model_dim layers \<longleftrightarrow>
    (\<forall>p \<in> set layers.
      valid_modern_decoder_layer p \<and> modern_model_dimension p = model_dim)"

theorem compatible_full_modern_decoder_stack_shape:
  assumes compatible: "modern_decoder_stack_compatible model_dim layers"
    and input: "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim
    (full_modern_decoder_stack layers start X)"
  using compatible input
proof (induction layers arbitrary: X)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have p_valid: "valid_modern_decoder_layer p"
    and p_dim: "modern_model_dimension p = model_dim"
    using Cons.prems(1)
    by (auto simp: modern_decoder_stack_compatible_def)
  have ps_compatible: "modern_decoder_stack_compatible model_dim ps"
    using Cons.prems(1) by (simp add: modern_decoder_stack_compatible_def)
  have layer_shape:
    "matrix_shape seq_len model_dim (full_modern_decoder_layer p start X)"
    using valid_full_modern_decoder_layer_shape[OF p_valid]
      Cons.prems(2) p_dim by simp
  show ?case
    by simp (rule Cons.IH[OF ps_compatible layer_shape])
qed

fun modern_transformer_cache_matches ::
  "modern_decoder_layer_parameters list \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow>
   transformer_kv_cache \<Rightarrow> bool" where
  "modern_transformer_cache_matches [] start prefix caches = (caches = [])"
| "modern_transformer_cache_matches (p # ps) start prefix [] = False"
| "modern_transformer_cache_matches (p # ps) start prefix (cache # caches) =
    (modern_layer_cache_matches p start prefix cache \<and>
      modern_transformer_cache_matches ps start
        (full_modern_decoder_layer p start prefix) caches)"

fun cached_modern_decoder_stack_step ::
  "modern_decoder_layer_parameters list \<Rightarrow> nat \<Rightarrow> real vector \<Rightarrow>
   transformer_kv_cache \<Rightarrow> real vector \<times> transformer_kv_cache" where
  "cached_modern_decoder_stack_step [] position x caches = (x, [])"
| "cached_modern_decoder_stack_step (p # ps) position x [] = (x, [])"
| "cached_modern_decoder_stack_step (p # ps) position x (cache # caches) =
    (let layer_step = cached_modern_decoder_layer_step p position x cache;
         stack_step = cached_modern_decoder_stack_step ps position
          (fst layer_step) caches
     in (fst stack_step, snd layer_step # snd stack_step))"

theorem cached_modern_decoder_stack_step_correct:
  assumes valid: "valid_modern_decoder_stack layers"
    and match: "modern_transformer_cache_matches layers start prefix caches"
  shows "full_modern_decoder_stack layers start (prefix @ [x]) =
      full_modern_decoder_stack layers start prefix @
        [fst (cached_modern_decoder_stack_step layers
          (start + length prefix) x caches)]"
    and "modern_transformer_cache_matches layers start (prefix @ [x])
      (snd (cached_modern_decoder_stack_step layers
        (start + length prefix) x caches))"
proof -
  have pair:
    "\<And>prefix caches x.
      valid_modern_decoder_stack layers \<Longrightarrow>
      modern_transformer_cache_matches layers start prefix caches \<Longrightarrow>
      full_modern_decoder_stack layers start (prefix @ [x]) =
        full_modern_decoder_stack layers start prefix @
          [fst (cached_modern_decoder_stack_step layers
            (start + length prefix) x caches)] \<and>
      modern_transformer_cache_matches layers start (prefix @ [x])
        (snd (cached_modern_decoder_stack_step layers
          (start + length prefix) x caches))"
  proof (induction layers)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    then obtain cache rest where caches: "caches = cache # rest"
      by (cases caches) auto
    have p_valid: "valid_modern_decoder_layer p"
      using Cons.prems(1) by (simp add: valid_modern_decoder_stack_def)
    have ps_valid: "valid_modern_decoder_stack ps"
      using Cons.prems(1) by (simp add: valid_modern_decoder_stack_def)
    have layer_match: "modern_layer_cache_matches p start prefix cache"
      using Cons.prems(2) unfolding caches by simp
    have rest_match:
      "modern_transformer_cache_matches ps start
        (full_modern_decoder_layer p start prefix) rest"
      using Cons.prems(2) unfolding caches by simp
    let ?position = "start + length prefix"
    let ?layer_step = "cached_modern_decoder_layer_step p ?position x cache"
    let ?y = "fst ?layer_step"
    let ?cache' = "snd ?layer_step"
    have layer_output:
      "?y = modern_decoder_at_indexed_prefix p (?position, x)
        (indexed_sequence start (prefix @ [x]))"
      using cached_modern_decoder_layer_step_correct(1)
        [OF p_valid layer_match] by simp
    have layer_cache:
      "modern_layer_cache_matches p start (prefix @ [x]) ?cache'"
      by (rule cached_modern_decoder_layer_step_correct(2)
          [OF p_valid layer_match])
    have layer_append:
      "full_modern_decoder_layer p start (prefix @ [x]) =
        full_modern_decoder_layer p start prefix @ [?y]"
      using full_modern_decoder_layer_append layer_output by simp
    have position_tail:
      "start + length (full_modern_decoder_layer p start prefix) = ?position"
      by simp
    have stack_pair:
      "full_modern_decoder_stack ps start
          (full_modern_decoder_layer p start prefix @ [?y]) =
        full_modern_decoder_stack ps start
          (full_modern_decoder_layer p start prefix) @
          [fst (cached_modern_decoder_stack_step ps ?position ?y rest)] \<and>
       modern_transformer_cache_matches ps start
          (full_modern_decoder_layer p start prefix @ [?y])
          (snd (cached_modern_decoder_stack_step ps ?position ?y rest))"
      using Cons.IH[OF ps_valid rest_match, of ?y]
      unfolding position_tail .
    show ?case
      unfolding caches cached_modern_decoder_stack_step.simps Let_def
      using layer_append layer_cache stack_pair by simp
  qed
  from pair[OF valid match] show
    "full_modern_decoder_stack layers start (prefix @ [x]) =
      full_modern_decoder_stack layers start prefix @
        [fst (cached_modern_decoder_stack_step layers
          (start + length prefix) x caches)]"
    and "modern_transformer_cache_matches layers start (prefix @ [x])
      (snd (cached_modern_decoder_stack_step layers
        (start + length prefix) x caches))"
    by blast+
qed

corollary incremental_modern_decoder_equals_full:
  assumes "valid_modern_decoder_stack layers"
    and "modern_transformer_cache_matches layers start prefix caches"
  shows "fst (cached_modern_decoder_stack_step layers
      (start + length prefix) x caches) =
    last (full_modern_decoder_stack layers start (prefix @ [x]))"
  using cached_modern_decoder_stack_step_correct(1)[OF assms] by simp

definition empty_modern_transformer_cache ::
  "modern_decoder_layer_parameters list \<Rightarrow> transformer_kv_cache" where
  "empty_modern_transformer_cache layers = map empty_modern_layer_cache layers"

lemma full_modern_decoder_layer_empty [simp]:
  "full_modern_decoder_layer p start [] = []"
proof -
  have "length (full_modern_decoder_layer p start []) = 0" by simp
  then show ?thesis by (rule iffD1[OF length_0_conv])
qed

lemma full_modern_decoder_stack_empty [simp]:
  "full_modern_decoder_stack layers start [] = []"
  by (induction layers) simp_all

theorem empty_modern_transformer_cache_matches:
  "modern_transformer_cache_matches layers start []
    (empty_modern_transformer_cache layers)"
  by (induction layers)
    (simp_all add: empty_modern_transformer_cache_def
      empty_modern_layer_cache_matches)

fun cached_modern_decoder_stack_run ::
  "modern_decoder_layer_parameters list \<Rightarrow> nat \<Rightarrow>
   transformer_kv_cache \<Rightarrow> real matrix \<Rightarrow>
   real matrix \<times> transformer_kv_cache" where
  "cached_modern_decoder_stack_run layers position caches [] = ([], caches)"
| "cached_modern_decoder_stack_run layers position caches (x # xs) =
    (let step = cached_modern_decoder_stack_step layers position x caches;
         rest = cached_modern_decoder_stack_run layers (Suc position)
          (snd step) xs
     in (fst step # fst rest, snd rest))"

theorem cached_modern_decoder_stack_run_correct:
  assumes valid: "valid_modern_decoder_stack layers"
    and match: "modern_transformer_cache_matches layers start prefix caches"
    and position: "position = start + length prefix"
  shows "full_modern_decoder_stack layers start (prefix @ xs) =
      full_modern_decoder_stack layers start prefix @
        fst (cached_modern_decoder_stack_run layers position caches xs)"
    and "modern_transformer_cache_matches layers start (prefix @ xs)
      (snd (cached_modern_decoder_stack_run layers position caches xs))"
proof -
  have pair:
    "\<And>prefix position caches.
      modern_transformer_cache_matches layers start prefix caches \<Longrightarrow>
      position = start + length prefix \<Longrightarrow>
      full_modern_decoder_stack layers start (prefix @ xs) =
        full_modern_decoder_stack layers start prefix @
          fst (cached_modern_decoder_stack_run layers position caches xs) \<and>
      modern_transformer_cache_matches layers start (prefix @ xs)
        (snd (cached_modern_decoder_stack_run layers position caches xs))"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    fix prefix position caches
    assume current:
      "modern_transformer_cache_matches layers start prefix caches"
    assume position: "position = start + length prefix"
    let ?step = "cached_modern_decoder_stack_step layers position x caches"
    have one_output:
      "full_modern_decoder_stack layers start (prefix @ [x]) =
        full_modern_decoder_stack layers start prefix @ [fst ?step]"
      using cached_modern_decoder_stack_step_correct(1)[OF valid current]
      unfolding position .
    have one_cache:
      "modern_transformer_cache_matches layers start (prefix @ [x]) (snd ?step)"
      using cached_modern_decoder_stack_step_correct(2)[OF valid current]
      unfolding position .
    have next_position:
      "Suc position = start + length (prefix @ [x])"
      unfolding position by simp
    have tail:
      "full_modern_decoder_stack layers start ((prefix @ [x]) @ xs) =
          full_modern_decoder_stack layers start (prefix @ [x]) @
            fst (cached_modern_decoder_stack_run layers (Suc position)
              (snd ?step) xs) \<and>
       modern_transformer_cache_matches layers start ((prefix @ [x]) @ xs)
          (snd (cached_modern_decoder_stack_run layers (Suc position)
            (snd ?step) xs))"
      by (rule Cons.IH[OF one_cache next_position])
    show "full_modern_decoder_stack layers start (prefix @ x # xs) =
        full_modern_decoder_stack layers start prefix @
          fst (cached_modern_decoder_stack_run layers position caches (x # xs)) \<and>
      modern_transformer_cache_matches layers start (prefix @ x # xs)
        (snd (cached_modern_decoder_stack_run layers position caches (x # xs)))"
      using one_output tail by (simp add: Let_def)
  qed
  from pair[OF match position] show
    "full_modern_decoder_stack layers start (prefix @ xs) =
      full_modern_decoder_stack layers start prefix @
        fst (cached_modern_decoder_stack_run layers position caches xs)"
    and "modern_transformer_cache_matches layers start (prefix @ xs)
      (snd (cached_modern_decoder_stack_run layers position caches xs))"
    by blast+
qed

corollary initialized_modern_cached_run_equals_full:
  assumes "valid_modern_decoder_stack layers"
  shows "fst (cached_modern_decoder_stack_run layers start
      (empty_modern_transformer_cache layers) xs) =
    full_modern_decoder_stack layers start xs"
proof -
  have "full_modern_decoder_stack layers start ([] @ xs) =
    full_modern_decoder_stack layers start [] @
      fst (cached_modern_decoder_stack_run layers start
        (empty_modern_transformer_cache layers) xs)"
    by (rule cached_modern_decoder_stack_run_correct(1)
        [OF assms empty_modern_transformer_cache_matches, where xs=xs]) simp
  then show ?thesis by simp
qed

corollary initialized_modern_cached_run_cache_invariant:
  assumes "valid_modern_decoder_stack layers"
  shows "modern_transformer_cache_matches layers start xs
    (snd (cached_modern_decoder_stack_run layers start
      (empty_modern_transformer_cache layers) xs))"
proof -
  have "modern_transformer_cache_matches layers start ([] @ xs)
    (snd (cached_modern_decoder_stack_run layers start
      (empty_modern_transformer_cache layers) xs))"
    by (rule cached_modern_decoder_stack_run_correct(2)
        [OF assms empty_modern_transformer_cache_matches,
          where xs=xs and position=start]) simp
  then show ?thesis by simp
qed

end
