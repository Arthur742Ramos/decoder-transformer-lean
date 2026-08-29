theory GPT_Neo_Incremental
  imports GPT_Neo_Components
begin

section \<open>GPT-Neo Exact Cache Refinement\<close>

text \<open>
  LayerNorm is token-local, so a GPT-Neo attention cache can store the
  normalized input vectors from the processed prefix.  The generic cache
  theorem then proves exact equality with the full windowed attention
  evaluator.  This construction is retained as a semantic bridge.  The
  projected per-head key--value cache below stores the reusable implementation
  state explicitly, so old entries are never reprojected during an append.
\<close>

definition gpt_neo_normalized_input ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow> real vector" where
  "gpt_neo_normalized_input p x =
    gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
      (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) x"

definition gpt_neo_cache_matches ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow>
   (real vector, real vector) kv_cache \<Rightarrow> bool" where
  "gpt_neo_cache_matches p prefix cache \<longleftrightarrow>
    cache_matches (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p) prefix cache"

definition gpt_neo_attention_aggregator ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   real vector list \<Rightarrow> real vector list \<Rightarrow> real vector" where
  "gpt_neo_attention_aggregator p x keys values =
    affine_project (gpt_neo_model_dimension p)
      (gpt_neo_output_weights p) (gpt_neo_output_bias p)
      (concat (map (\<lambda>h.
        exact_attention (gpt_neo_head_dimension p)
          (gpt_neo_head_dimension p)
          (linear_project (gpt_neo_head_dimension p)
            (gpt_neo_query_weights p ! h)
            (gpt_neo_normalized_input p x))
          (map (linear_project (gpt_neo_head_dimension p)
            (gpt_neo_key_weights p ! h))
            (gpt_neo_attention_context
              (gpt_neo_attention_window p) keys))
          (map (linear_project (gpt_neo_head_dimension p)
            (gpt_neo_value_weights p ! h))
            (gpt_neo_attention_context
              (gpt_neo_attention_window p) values)))
        [0..<gpt_neo_head_count p]))"

lemma gpt_neo_local_context_map:
  "gpt_neo_local_context window (map f xs) =
    map f (gpt_neo_local_context window xs)"
  by (simp add: gpt_neo_local_context_def drop_map)

lemma gpt_neo_attention_context_map:
  "gpt_neo_attention_context window (map f xs) =
    map f (gpt_neo_attention_context window xs)"
proof (cases "window = 0")
  case True
  then show ?thesis by (simp add: gpt_neo_attention_context_def)
next
  case False
  then show ?thesis
    by (simp add: gpt_neo_attention_context_def gpt_neo_local_context_map)
qed

lemma gpt_neo_attention_aggregator_full:
  "gpt_neo_attention_aggregator p x
      (map (gpt_neo_normalized_input p) prefix)
      (map (gpt_neo_normalized_input p) prefix) =
    gpt_neo_windowed_multi_head_at_prefix
      (gpt_neo_head_count p) (gpt_neo_model_dimension p)
      (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)
      (gpt_neo_output_bias p)
      (gpt_neo_normalized_input p x)
      (map (gpt_neo_normalized_input p) prefix)"
  by (simp add: gpt_neo_attention_aggregator_def
      gpt_neo_windowed_multi_head_at_prefix_def
      gpt_neo_windowed_head_attention_def
      gpt_neo_attention_context_map gpt_neo_normalized_input_def
      map_map comp_def)

lemma gpt_neo_normalized_prefix_as_input:
  "gpt_neo_normalized_prefix p prefix =
    map (gpt_neo_normalized_input p) prefix"
  by (simp add: gpt_neo_normalized_prefix_def
      gpt_neo_normalized_input_def)

definition gpt_neo_cached_attention ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   (real vector, real vector) kv_cache \<Rightarrow> real vector" where
  "gpt_neo_cached_attention p x cache =
    snd (cached_step id (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p)
      (gpt_neo_attention_aggregator p) cache x)"

theorem gpt_neo_cached_attention_correct:
  assumes match: "gpt_neo_cache_matches p prefix cache"
  shows "gpt_neo_cached_attention p x cache =
    gpt_neo_windowed_multi_head_at_prefix
      (gpt_neo_head_count p) (gpt_neo_model_dimension p)
      (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)
      (gpt_neo_output_bias p)
      (gpt_neo_normalized_input p x)
      (map (gpt_neo_normalized_input p) (prefix @ [x]))"
proof -
  have match':
    "cache_matches (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p) prefix cache"
    using match by (simp add: gpt_neo_cache_matches_def)
  have step:
    "cached_step id (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p)
      (gpt_neo_attention_aggregator p) cache x =
      (cache_of (gpt_neo_normalized_input p)
        (gpt_neo_normalized_input p) (prefix @ [x]),
       gpt_neo_attention_aggregator p x
        (map (gpt_neo_normalized_input p) (prefix @ [x]))
        (map (gpt_neo_normalized_input p) (prefix @ [x])))"
    using match'
    by (simp add: cached_step_def cache_matches_def cache_of_def
        Let_def id_def)
  show ?thesis
    unfolding gpt_neo_cached_attention_def
    using step gpt_neo_attention_aggregator_full[where prefix="prefix @ [x]"]
    by simp
qed

theorem gpt_neo_cached_attention_cache_matches:
  assumes match: "gpt_neo_cache_matches p prefix cache"
  shows "gpt_neo_cache_matches p (prefix @ [x])
    (fst (cached_step id (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p)
      (gpt_neo_attention_aggregator p) cache x))"
proof -
  have match':
    "cache_matches (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p) prefix cache"
    using match by (simp add: gpt_neo_cache_matches_def)
  have step:
    "cached_step id (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p)
      (gpt_neo_attention_aggregator p) cache x =
      (cache_of (gpt_neo_normalized_input p)
        (gpt_neo_normalized_input p) (prefix @ [x]),
       gpt_neo_attention_aggregator p x
        (map (gpt_neo_normalized_input p) (prefix @ [x]))
        (map (gpt_neo_normalized_input p) (prefix @ [x])))"
    using match'
    by (simp add: cached_step_def cache_matches_def cache_of_def
        Let_def id_def)
  show ?thesis
    using step by (simp add: gpt_neo_cache_matches_def cache_matches_def)
qed

definition gpt_neo_block_from_attention ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "gpt_neo_block_from_attention p x attention =
    (let attention_residual = vector_add x attention;
         normalized_mlp =
       gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
         (gpt_neo_ln2_gain p) (gpt_neo_ln2_bias p) attention_residual;
         mlp =
       gpt_neo_mlp (gpt_neo_model_dimension p)
         (gpt_neo_hidden_dimension p)
         (gpt_neo_fc_weights p) (gpt_neo_fc_bias p)
         (gpt_neo_projection_weights p) (gpt_neo_projection_bias p)
         normalized_mlp
     in vector_add attention_residual mlp)"

lemma gpt_neo_block_at_prefix_from_attention:
  "gpt_neo_block_at_prefix p x prefix =
    gpt_neo_block_from_attention p x
      (gpt_neo_windowed_multi_head_at_prefix
        (gpt_neo_head_count p) (gpt_neo_model_dimension p)
        (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
        (gpt_neo_query_weights p) (gpt_neo_key_weights p)
        (gpt_neo_value_weights p) (gpt_neo_output_weights p)
        (gpt_neo_output_bias p)
        (gpt_neo_normalized_input p x)
        (map (gpt_neo_normalized_input p) prefix))"
  by (simp add: gpt_neo_block_at_prefix_def
      gpt_neo_block_from_attention_def
      gpt_neo_normalized_input_def
      gpt_neo_normalized_prefix_as_input)

definition gpt_neo_cached_block_step ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   (real vector, real vector) kv_cache \<Rightarrow>
   real vector \<times> (real vector, real vector) kv_cache" where
  "gpt_neo_cached_block_step p x cache =
    (let step = cached_step id (gpt_neo_normalized_input p)
        (gpt_neo_normalized_input p)
        (gpt_neo_attention_aggregator p) cache x
     in (gpt_neo_block_from_attention p x (snd step), fst step))"

theorem gpt_neo_cached_block_step_correct:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_cache_matches p prefix cache"
  shows "fst (gpt_neo_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    and "gpt_neo_cache_matches p (prefix @ [x])
      (snd (gpt_neo_cached_block_step p x cache))"
proof -
  have cached_attention:
    "gpt_neo_cached_attention p x cache =
      gpt_neo_windowed_multi_head_at_prefix
        (gpt_neo_head_count p) (gpt_neo_model_dimension p)
        (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
        (gpt_neo_query_weights p) (gpt_neo_key_weights p)
        (gpt_neo_value_weights p) (gpt_neo_output_weights p)
        (gpt_neo_output_bias p)
        (gpt_neo_normalized_input p x)
        (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    by (rule gpt_neo_cached_attention_correct[OF match])
  have attention:
    "snd (cached_step id (gpt_neo_normalized_input p)
      (gpt_neo_normalized_input p)
      (gpt_neo_attention_aggregator p) cache x) =
      gpt_neo_windowed_multi_head_at_prefix
        (gpt_neo_head_count p) (gpt_neo_model_dimension p)
        (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
        (gpt_neo_query_weights p) (gpt_neo_key_weights p)
        (gpt_neo_value_weights p) (gpt_neo_output_weights p)
         (gpt_neo_output_bias p)
         (gpt_neo_normalized_input p x)
         (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    using cached_attention
    by (simp add: gpt_neo_cached_attention_def)
  show "fst (gpt_neo_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    using attention
    by (simp add: gpt_neo_cached_block_step_def
        gpt_neo_block_at_prefix_from_attention)
  show "gpt_neo_cache_matches p (prefix @ [x])
      (snd (gpt_neo_cached_block_step p x cache))"
    unfolding gpt_neo_cached_block_step_def Let_def snd_conv
    by (rule gpt_neo_cached_attention_cache_matches[OF match])
qed

corollary gpt_neo_cached_block_step_output:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_cache_matches p prefix cache"
  shows "fst (gpt_neo_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
  using gpt_neo_cached_block_step_correct(1)[OF valid match] .

corollary gpt_neo_cached_block_step_cache:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_cache_matches p prefix cache"
  shows "gpt_neo_cache_matches p (prefix @ [x])
      (snd (gpt_neo_cached_block_step p x cache))"
  using gpt_neo_cached_block_step_correct(2)[OF valid match] .

lemma gpt_neo_full_layer_append:
  "gpt_neo_full_layer p (prefix @ [x]) =
    gpt_neo_full_layer p prefix @
      [gpt_neo_block_at_prefix p x (prefix @ [x])]"
proof -
  let ?A = "\<lambda>x prefix _. gpt_neo_block_at_prefix p x prefix"
  have append:
    "causal_attention id id id ?A (prefix @ [x]) =
      causal_attention id id id ?A prefix @
        causal_attention_from id id id ?A prefix [x]"
    by (rule causal_attention_append)
  show ?thesis
    unfolding gpt_neo_full_layer_def append
    by simp
qed

corollary gpt_neo_cached_block_step_full:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_cache_matches p prefix cache"
  shows "gpt_neo_full_layer p (prefix @ [x]) =
    gpt_neo_full_layer p prefix @
      [fst (gpt_neo_cached_block_step p x cache)]"
  unfolding gpt_neo_full_layer_append
  using gpt_neo_cached_block_step_correct(1)[OF valid match]
  by simp

section \<open>Projected GPT-Neo Key--Value Caches\<close>

text \<open>
  The cache used by the stack-level GPT-Neo refinement stores one projected
  key--value history per attention head.  LayerNorm is evaluated only for the
  newly arriving token; old key and value projections are never recomputed.
  The attention aggregator trims the projected histories to the active window
  before applying exact attention.  This is the implementation-level cache
  boundary, in contrast to the normalized-input semantic bridge above.
\<close>

type_synonym gpt_neo_projected_head_cache =
  "(real vector, real vector) kv_cache"

type_synonym gpt_neo_projected_layer_cache =
  "gpt_neo_projected_head_cache list"

definition gpt_neo_projected_query ::
  "gpt_neo_layer_parameters \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "gpt_neo_projected_query p h x =
    linear_project (gpt_neo_head_dimension p)
      (gpt_neo_query_weights p ! h)
      (gpt_neo_normalized_input p x)"

definition gpt_neo_projected_key ::
  "gpt_neo_layer_parameters \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "gpt_neo_projected_key p h x =
    linear_project (gpt_neo_head_dimension p)
      (gpt_neo_key_weights p ! h)
      x"

definition gpt_neo_projected_value ::
  "gpt_neo_layer_parameters \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "gpt_neo_projected_value p h x =
    linear_project (gpt_neo_head_dimension p)
      (gpt_neo_value_weights p ! h)
      x"

definition gpt_neo_projected_head_cache_of ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow> nat \<Rightarrow>
   gpt_neo_projected_head_cache" where
  "gpt_neo_projected_head_cache_of p prefix h =
    cache_of (gpt_neo_projected_key p h)
      (gpt_neo_projected_value p h)
      (map (gpt_neo_normalized_input p) prefix)"

definition gpt_neo_projected_cache_of ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow>
   gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_cache_of p prefix =
    map (gpt_neo_projected_head_cache_of p prefix)
      [0..<gpt_neo_head_count p]"

definition gpt_neo_projected_cache_matches ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow>
    gpt_neo_projected_layer_cache \<Rightarrow> bool" where
  "gpt_neo_projected_cache_matches p prefix cache \<longleftrightarrow>
    cache = gpt_neo_projected_cache_of p prefix"

definition gpt_neo_projected_head_cache_append ::
  "gpt_neo_layer_parameters \<Rightarrow> nat \<Rightarrow> real vector \<Rightarrow>
    gpt_neo_projected_head_cache \<Rightarrow>
   gpt_neo_projected_head_cache" where
  "gpt_neo_projected_head_cache_append p h x cache =
    \<lparr>cache_keys = cache_keys cache @
        [gpt_neo_projected_key p h
          (gpt_neo_normalized_input p x)],
      cache_values = cache_values cache @
        [gpt_neo_projected_value p h
          (gpt_neo_normalized_input p x)]\<rparr>"

fun gpt_neo_projected_cache_extend_on_heads ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow> nat list \<Rightarrow>
    gpt_neo_projected_layer_cache \<Rightarrow>
   gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_cache_extend_on_heads p x [] caches = []"
| "gpt_neo_projected_cache_extend_on_heads p x (h # hs) [] = []"
| "gpt_neo_projected_cache_extend_on_heads p x (h # hs)
      (cache # caches) =
    gpt_neo_projected_head_cache_append p h x cache #
      gpt_neo_projected_cache_extend_on_heads p x hs caches"

definition gpt_neo_projected_cache_extend ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
    gpt_neo_projected_layer_cache \<Rightarrow>
   gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_cache_extend p x cache =
    gpt_neo_projected_cache_extend_on_heads p x
      [0..<gpt_neo_head_count p] cache"

lemma gpt_neo_projected_head_cache_append_of:
  "gpt_neo_projected_head_cache_append p h x
      (gpt_neo_projected_head_cache_of p prefix h) =
    gpt_neo_projected_head_cache_of p (prefix @ [x]) h"
  by (simp add: gpt_neo_projected_head_cache_append_def
      gpt_neo_projected_head_cache_of_def cache_of_def
      gpt_neo_projected_key_def gpt_neo_projected_value_def
      gpt_neo_normalized_input_def)

lemma gpt_neo_projected_cache_extend_on_heads_map:
  "gpt_neo_projected_cache_extend_on_heads p x hs
      (map (gpt_neo_projected_head_cache_of p prefix) hs) =
    map (gpt_neo_projected_head_cache_of p (prefix @ [x])) hs"
proof (induction hs)
  case Nil
  then show ?case by simp
next
  case (Cons h hs)
  then show ?case
    by (simp add: gpt_neo_projected_head_cache_append_of)
qed

lemma gpt_neo_projected_cache_extend_of:
  "gpt_neo_projected_cache_extend p x
      (gpt_neo_projected_cache_of p prefix) =
    gpt_neo_projected_cache_of p (prefix @ [x])"
  by (simp add: gpt_neo_projected_cache_extend_def
      gpt_neo_projected_cache_of_def
      gpt_neo_projected_cache_extend_on_heads_map)

lemma gpt_neo_projected_cache_extend_matches:
  assumes match: "gpt_neo_projected_cache_matches p prefix cache"
  shows "gpt_neo_projected_cache_matches p (prefix @ [x])
    (gpt_neo_projected_cache_extend p x cache)"
  using match
  by (simp add: gpt_neo_projected_cache_matches_def
      gpt_neo_projected_cache_extend_of)

fun gpt_neo_projected_attention_heads ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow> nat list \<Rightarrow>
    gpt_neo_projected_layer_cache \<Rightarrow> real vector list" where
  "gpt_neo_projected_attention_heads p x [] caches = []"
| "gpt_neo_projected_attention_heads p x (h # hs) [] = []"
| "gpt_neo_projected_attention_heads p x (h # hs)
      (cache # caches) =
    exact_attention (gpt_neo_head_dimension p)
      (gpt_neo_head_dimension p)
      (gpt_neo_projected_query p h x)
      (gpt_neo_attention_context (gpt_neo_attention_window p)
        (cache_keys cache))
      (gpt_neo_attention_context (gpt_neo_attention_window p)
        (cache_values cache)) #
    gpt_neo_projected_attention_heads p x hs caches"

definition gpt_neo_projected_attention_aggregator ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
    gpt_neo_projected_layer_cache \<Rightarrow> real vector" where
  "gpt_neo_projected_attention_aggregator p x cache =
    affine_project (gpt_neo_model_dimension p)
      (gpt_neo_output_weights p) (gpt_neo_output_bias p)
      (concat (gpt_neo_projected_attention_heads p x
        [0..<gpt_neo_head_count p] cache))"

lemma gpt_neo_projected_attention_heads_of:
  "gpt_neo_projected_attention_heads p x hs
      (map (gpt_neo_projected_head_cache_of p prefix) hs) =
    map (\<lambda>h. exact_attention (gpt_neo_head_dimension p)
      (gpt_neo_head_dimension p)
      (gpt_neo_projected_query p h x)
      (gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_projected_key p h)
          (map (gpt_neo_normalized_input p) prefix)))
      (gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_projected_value p h)
          (map (gpt_neo_normalized_input p) prefix)))
      ) hs"
proof (induction hs)
  case Nil
  then show ?case by simp
next
  case (Cons h hs)
  then show ?case
    by (simp add: gpt_neo_projected_head_cache_of_def
      gpt_neo_projected_attention_heads.simps cache_of_def)
qed

lemma gpt_neo_projected_attention_aggregator_full:
  "gpt_neo_projected_attention_aggregator p x
      (gpt_neo_projected_cache_of p prefix) =
    gpt_neo_windowed_multi_head_at_prefix
      (gpt_neo_head_count p) (gpt_neo_model_dimension p)
      (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)
      (gpt_neo_output_bias p)
      (gpt_neo_normalized_input p x)
      (map (gpt_neo_normalized_input p) prefix)"
  by (simp add: gpt_neo_projected_attention_aggregator_def
      gpt_neo_projected_cache_of_def
      gpt_neo_projected_attention_heads_of
      gpt_neo_windowed_multi_head_at_prefix_def
      gpt_neo_windowed_head_attention_def
      gpt_neo_projected_query_def
      gpt_neo_projected_key_def
      gpt_neo_projected_value_def
      gpt_neo_attention_context_map map_map comp_def)

definition gpt_neo_projected_cached_attention ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
    gpt_neo_projected_layer_cache \<Rightarrow> real vector" where
  "gpt_neo_projected_cached_attention p x cache =
    gpt_neo_projected_attention_aggregator p x
      (gpt_neo_projected_cache_extend p x cache)"

theorem gpt_neo_projected_cached_attention_correct:
  assumes match: "gpt_neo_projected_cache_matches p prefix cache"
  shows "gpt_neo_projected_cached_attention p x cache =
    gpt_neo_windowed_multi_head_at_prefix
      (gpt_neo_head_count p) (gpt_neo_model_dimension p)
      (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)
      (gpt_neo_output_bias p)
      (gpt_neo_normalized_input p x)
      (map (gpt_neo_normalized_input p) (prefix @ [x]))"
  using match
  by (simp add: gpt_neo_projected_cached_attention_def
      gpt_neo_projected_cache_matches_def
      gpt_neo_projected_cache_extend_of
      gpt_neo_projected_attention_aggregator_full)

definition gpt_neo_projected_cached_block_step ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
    gpt_neo_projected_layer_cache \<Rightarrow>
   real vector \<times> gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_cached_block_step p x cache =
    (gpt_neo_block_from_attention p x
       (gpt_neo_projected_cached_attention p x cache),
     gpt_neo_projected_cache_extend p x cache)"

theorem gpt_neo_projected_cached_block_step_correct:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_projected_cache_matches p prefix cache"
  shows "fst (gpt_neo_projected_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    and "gpt_neo_projected_cache_matches p (prefix @ [x])
      (snd (gpt_neo_projected_cached_block_step p x cache))"
proof -
  have attention:
    "gpt_neo_projected_cached_attention p x cache =
      gpt_neo_windowed_multi_head_at_prefix
        (gpt_neo_head_count p) (gpt_neo_model_dimension p)
        (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
        (gpt_neo_query_weights p) (gpt_neo_key_weights p)
        (gpt_neo_value_weights p) (gpt_neo_output_weights p)
        (gpt_neo_output_bias p)
        (gpt_neo_normalized_input p x)
        (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    by (rule gpt_neo_projected_cached_attention_correct[OF match])
  show "fst (gpt_neo_projected_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    using attention
    by (simp add: gpt_neo_projected_cached_block_step_def
        gpt_neo_block_at_prefix_from_attention)
  show "gpt_neo_projected_cache_matches p (prefix @ [x])
      (snd (gpt_neo_projected_cached_block_step p x cache))"
  proof -
    have extension:
      "gpt_neo_projected_cache_matches p (prefix @ [x])
        (gpt_neo_projected_cache_extend p x cache)"
      by (rule gpt_neo_projected_cache_extend_matches[OF match])
    show ?thesis
      unfolding gpt_neo_projected_cached_block_step_def
      using extension by simp
  qed
qed

corollary gpt_neo_projected_cached_block_step_output:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_projected_cache_matches p prefix cache"
  shows "fst (gpt_neo_projected_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
  using gpt_neo_projected_cached_block_step_correct(1)[OF valid match] .

corollary gpt_neo_projected_cached_block_step_cache:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_projected_cache_matches p prefix cache"
  shows "gpt_neo_projected_cache_matches p (prefix @ [x])
      (snd (gpt_neo_projected_cached_block_step p x cache))"
  using gpt_neo_projected_cached_block_step_correct(2)[OF valid match] .

definition gpt_neo_projected_empty_cache ::
  "gpt_neo_layer_parameters \<Rightarrow> gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_empty_cache p =
    map (\<lambda>h. empty_cache) [0..<gpt_neo_head_count p]"

lemma gpt_neo_projected_empty_cache_matches:
  "gpt_neo_projected_cache_matches p []
    (gpt_neo_projected_empty_cache p)"
  by (simp add: gpt_neo_projected_cache_matches_def
      gpt_neo_projected_empty_cache_def
      gpt_neo_projected_cache_of_def
      gpt_neo_projected_head_cache_of_def
      cache_of_def gpt_neo_attention_context_def
      gpt_neo_local_context_def empty_cache_def)

end
