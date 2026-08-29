theory GPT_Neo_Windowed_Cache
  imports GPT_Neo_Incremental
begin

section \<open>Bounded GPT-Neo Sliding-Window Cache\<close>

text \<open>
  The preceding incremental theory supplies a normalized-input semantic
  bridge.  This theory adds the implementation-level refinement for projected
  per-head keys and values: for a positive GPT-Neo attention window, after each
  append only the active tail is retained.  Global attention (window zero)
  intentionally remains untruncated.
\<close>

lemma gpt_neo_local_context_append_trim:
  "gpt_neo_local_context window
      (gpt_neo_local_context window xs @ [x]) =
    gpt_neo_local_context window (xs @ [x])"
proof (cases "window = 0")
  case True
  then show ?thesis
    by (simp add: gpt_neo_local_context_def)
next
  case False
  have window_nonzero: "window \<noteq> 0"
    using False .
  show ?thesis
  proof (cases "length xs \<le> window")
    case True
    then show ?thesis
      by (simp add: gpt_neo_local_context_short)
  next
    case False
    have window_positive: "0 < window"
      using window_nonzero by simp
    have window_lt_length: "window < length xs"
      using False by simp
    have min_left: "min window (length xs) = window"
      using window_lt_length by simp
    have min_append: "min window (length (xs @ [x])) = window"
      using window_positive window_lt_length by simp
    have trimmed_length:
      "length (gpt_neo_local_context window xs) = window"
      using min_left by simp
    have trimmed_append_length:
      "length (gpt_neo_local_context window xs @ [x]) =
        Suc window"
      using trimmed_length by simp
    have left_drop:
      "length (gpt_neo_local_context window xs @ [x]) -
          min window
            (length (gpt_neo_local_context window xs @ [x])) = 1"
      using window_positive trimmed_append_length by simp
    have right_drop:
      "length (xs @ [x]) - min window (length (xs @ [x])) =
        Suc (length xs - window)"
    proof -
      have window_le_length: "window \<le> length xs"
        using window_lt_length by simp
      have suc_sub:
        "Suc (length xs) - window = Suc (length xs - window)"
        by (rule Suc_diff_le[OF window_le_length])
      then show ?thesis
        using min_append by simp
    qed
    show ?thesis
      unfolding gpt_neo_local_context_def
      using left_drop right_drop min_left
      by (simp add: drop_append drop_drop)
  qed
qed

lemma gpt_neo_attention_context_append_trim:
  "gpt_neo_attention_context window
      (gpt_neo_attention_context window xs @ [x]) =
    gpt_neo_attention_context window (xs @ [x])"
proof (cases "window = 0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
    by (simp add: gpt_neo_attention_context_def
      gpt_neo_local_context_append_trim)
qed

lemma gpt_neo_attention_context_idempotent:
  "gpt_neo_attention_context window
      (gpt_neo_attention_context window xs) =
    gpt_neo_attention_context window xs"
proof (cases "window = 0")
  case True
  then show ?thesis by simp
next
  case False
  have window_nonzero: "window \<noteq> 0"
    using False .
  show ?thesis
  proof (cases "length xs \<le> window")
    case True
    then show ?thesis
      by (simp add: gpt_neo_attention_context_def
        gpt_neo_local_context_def)
  next
    case False
    have window_positive: "0 < window"
      using window_nonzero by simp
    have window_lt_length: "window < length xs"
      using False by simp
    have min_left: "min window (length xs) = window"
      using window_lt_length by simp
    show ?thesis
      unfolding gpt_neo_attention_context_def
        gpt_neo_local_context_def
      using min_left window_positive
      by (simp add: length_drop)
  qed
qed

lemma gpt_neo_attention_context_empty [simp]:
  "gpt_neo_attention_context window [] = []"
  by (cases "window = 0")
    (simp_all add: gpt_neo_attention_context_def
      gpt_neo_local_context_def)

definition gpt_neo_trim_cache ::
  "nat \<Rightarrow> ('a, 'b) kv_cache \<Rightarrow> ('a, 'b) kv_cache" where
  "gpt_neo_trim_cache window cache =
    \<lparr>cache_keys =
       gpt_neo_attention_context window (cache_keys cache),
      cache_values =
       gpt_neo_attention_context window (cache_values cache)\<rparr>"

lemma gpt_neo_trim_cache_keys [simp]:
  "cache_keys (gpt_neo_trim_cache window cache) =
    gpt_neo_attention_context window (cache_keys cache)"
  by (simp add: gpt_neo_trim_cache_def)

lemma gpt_neo_trim_cache_values [simp]:
  "cache_values (gpt_neo_trim_cache window cache) =
    gpt_neo_attention_context window (cache_values cache)"
  by (simp add: gpt_neo_trim_cache_def)

lemma gpt_neo_trim_cache_of:
  "gpt_neo_trim_cache window (cache_of K V xs) =
    cache_of K V (gpt_neo_attention_context window xs)"
  unfolding gpt_neo_trim_cache_def cache_of_def
  by (simp add: gpt_neo_attention_context_map)

definition gpt_neo_bounded_cache_matches ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow>
   (real vector, real vector) kv_cache \<Rightarrow> bool" where
  "gpt_neo_bounded_cache_matches p prefix cache \<longleftrightarrow>
    cache = gpt_neo_trim_cache (gpt_neo_attention_window p)
      (cache_of (gpt_neo_normalized_input p)
        (gpt_neo_normalized_input p) prefix)"

definition gpt_neo_bounded_cache_extend ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   (real vector, real vector) kv_cache \<Rightarrow>
   (real vector, real vector) kv_cache" where
  "gpt_neo_bounded_cache_extend p x cache =
    gpt_neo_trim_cache (gpt_neo_attention_window p)
      \<lparr>cache_keys = cache_keys cache @
          [gpt_neo_normalized_input p x],
       cache_values = cache_values cache @
          [gpt_neo_normalized_input p x]\<rparr>"

lemma gpt_neo_bounded_cache_extend_matches:
  assumes match: "gpt_neo_bounded_cache_matches p prefix cache"
  shows "gpt_neo_bounded_cache_matches p (prefix @ [x])
    (gpt_neo_bounded_cache_extend p x cache)"
proof -
  have cache_eq:
    "cache =
      gpt_neo_trim_cache (gpt_neo_attention_window p)
        (cache_of (gpt_neo_normalized_input p)
          (gpt_neo_normalized_input p) prefix)"
    using match by (simp add: gpt_neo_bounded_cache_matches_def)
  have key_eq:
    "cache_keys cache =
      gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_normalized_input p) prefix)"
    using cache_eq by (simp add: cache_of_def)
  have value_eq:
    "cache_values cache =
      gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_normalized_input p) prefix)"
    using cache_eq by (simp add: cache_of_def)
  have append_map:
    "map (gpt_neo_normalized_input p) (prefix @ [x]) =
      map (gpt_neo_normalized_input p) prefix @
        [gpt_neo_normalized_input p x]"
    by simp
  show ?thesis
    unfolding gpt_neo_bounded_cache_matches_def
      gpt_neo_bounded_cache_extend_def
    using key_eq value_eq append_map
      gpt_neo_attention_context_append_trim[of
        "gpt_neo_attention_window p"
        "map (gpt_neo_normalized_input p) prefix"
        "gpt_neo_normalized_input p x"]
    by (simp add: gpt_neo_trim_cache_of cache_of_def)
qed

definition gpt_neo_bounded_cached_attention ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   (real vector, real vector) kv_cache \<Rightarrow> real vector" where
  "gpt_neo_bounded_cached_attention p x cache =
    gpt_neo_attention_aggregator p x
      (cache_keys (gpt_neo_bounded_cache_extend p x cache))
      (cache_values (gpt_neo_bounded_cache_extend p x cache))"

theorem gpt_neo_bounded_cached_attention_correct:
  assumes match: "gpt_neo_bounded_cache_matches p prefix cache"
  shows "gpt_neo_bounded_cached_attention p x cache =
    gpt_neo_windowed_multi_head_at_prefix
      (gpt_neo_head_count p) (gpt_neo_model_dimension p)
      (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)
      (gpt_neo_output_bias p)
      (gpt_neo_normalized_input p x)
      (map (gpt_neo_normalized_input p) (prefix @ [x]))"
proof -
  have extended:
    "gpt_neo_bounded_cache_extend p x cache =
      gpt_neo_trim_cache (gpt_neo_attention_window p)
        (cache_of (gpt_neo_normalized_input p)
          (gpt_neo_normalized_input p) (prefix @ [x]))"
    using match
    by (simp add: gpt_neo_bounded_cache_extend_def
      gpt_neo_bounded_cache_matches_def cache_of_def
      gpt_neo_attention_context_append_trim)
  have cache_keys_eq:
    "cache_keys (gpt_neo_bounded_cache_extend p x cache) =
      gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    using extended by (simp add: gpt_neo_trim_cache_of cache_of_def)
  have cache_values_eq:
    "cache_values (gpt_neo_bounded_cache_extend p x cache) =
      gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    using extended by (simp add: gpt_neo_trim_cache_of cache_of_def)
  show ?thesis
    unfolding gpt_neo_bounded_cached_attention_def
    using cache_keys_eq cache_values_eq
      gpt_neo_attention_aggregator_full[where prefix="prefix @ [x]"]
    by (simp add: gpt_neo_attention_aggregator_def
      gpt_neo_attention_context_idempotent)
qed

definition gpt_neo_bounded_cached_block_step ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   (real vector, real vector) kv_cache \<Rightarrow>
   real vector \<times> (real vector, real vector) kv_cache" where
  "gpt_neo_bounded_cached_block_step p x cache =
    (let attention = gpt_neo_bounded_cached_attention p x cache
     in (gpt_neo_block_from_attention p x attention,
         gpt_neo_bounded_cache_extend p x cache))"

theorem gpt_neo_bounded_cached_block_step_correct:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_bounded_cache_matches p prefix cache"
  shows "fst (gpt_neo_bounded_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    and "gpt_neo_bounded_cache_matches p (prefix @ [x])
      (snd (gpt_neo_bounded_cached_block_step p x cache))"
proof -
  have attention:
    "gpt_neo_bounded_cached_attention p x cache =
      gpt_neo_windowed_multi_head_at_prefix
        (gpt_neo_head_count p) (gpt_neo_model_dimension p)
        (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
        (gpt_neo_query_weights p) (gpt_neo_key_weights p)
        (gpt_neo_value_weights p) (gpt_neo_output_weights p)
        (gpt_neo_output_bias p)
        (gpt_neo_normalized_input p x)
        (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    by (rule gpt_neo_bounded_cached_attention_correct[OF match])
  show "fst (gpt_neo_bounded_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    using attention
    by (simp add: gpt_neo_bounded_cached_block_step_def
        gpt_neo_block_at_prefix_from_attention)
  show "gpt_neo_bounded_cache_matches p (prefix @ [x])
      (snd (gpt_neo_bounded_cached_block_step p x cache))"
    unfolding gpt_neo_bounded_cached_block_step_def Let_def snd_conv
    by (rule gpt_neo_bounded_cache_extend_matches[OF match])
qed

corollary gpt_neo_bounded_cached_block_step_output:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_bounded_cache_matches p prefix cache"
  shows "fst (gpt_neo_bounded_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
  using gpt_neo_bounded_cached_block_step_correct(1)[OF valid match] .

corollary gpt_neo_bounded_cached_block_step_cache:
  assumes valid: "valid_gpt_neo_layer p"
    and match: "gpt_neo_bounded_cache_matches p prefix cache"
  shows "gpt_neo_bounded_cache_matches p (prefix @ [x])
      (snd (gpt_neo_bounded_cached_block_step p x cache))"
  using gpt_neo_bounded_cached_block_step_correct(2)[OF valid match] .

section \<open>Bounded Projected GPT-Neo Caches\<close>

text \<open>
  The bounded stack path uses the same projected per-head cache as the
  full-history path.  The only storage operation added here is tail trimming;
  the keys and values already in the cache are never projected again.
\<close>

definition gpt_neo_projected_bounded_head_cache_of ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow> nat \<Rightarrow>
   gpt_neo_projected_head_cache" where
  "gpt_neo_projected_bounded_head_cache_of p prefix h =
    cache_of (gpt_neo_projected_key p h)
      (gpt_neo_projected_value p h)
      (gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_normalized_input p) prefix))"

definition gpt_neo_projected_bounded_cache_of ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow>
   gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_bounded_cache_of p prefix =
    map (gpt_neo_projected_bounded_head_cache_of p prefix)
      [0..<gpt_neo_head_count p]"

definition gpt_neo_projected_bounded_empty_cache ::
  "gpt_neo_layer_parameters \<Rightarrow>
   gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_bounded_empty_cache p =
    gpt_neo_projected_bounded_cache_of p []"

definition gpt_neo_projected_bounded_cache_matches ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector list \<Rightarrow>
   gpt_neo_projected_layer_cache \<Rightarrow> bool" where
  "gpt_neo_projected_bounded_cache_matches p prefix cache \<longleftrightarrow>
    cache = gpt_neo_projected_bounded_cache_of p prefix"

lemma gpt_neo_projected_bounded_empty_cache_matches:
  "gpt_neo_projected_bounded_cache_matches p []
    (gpt_neo_projected_bounded_empty_cache p)"
  by (simp add: gpt_neo_projected_bounded_cache_matches_def
      gpt_neo_projected_bounded_empty_cache_def)

definition gpt_neo_projected_bounded_head_cache_append ::
  "gpt_neo_layer_parameters \<Rightarrow> nat \<Rightarrow> real vector \<Rightarrow>
   gpt_neo_projected_head_cache \<Rightarrow>
   gpt_neo_projected_head_cache" where
  "gpt_neo_projected_bounded_head_cache_append p h x cache =
    gpt_neo_trim_cache (gpt_neo_attention_window p)
      \<lparr>cache_keys = cache_keys cache @
          [gpt_neo_projected_key p h
            (gpt_neo_normalized_input p x)],
        cache_values = cache_values cache @
          [gpt_neo_projected_value p h
            (gpt_neo_normalized_input p x)]\<rparr>"

fun gpt_neo_projected_bounded_cache_extend_on_heads ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_projected_layer_cache \<Rightarrow>
   gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_bounded_cache_extend_on_heads p x [] caches = []"
| "gpt_neo_projected_bounded_cache_extend_on_heads p x (h # hs) [] = []"
| "gpt_neo_projected_bounded_cache_extend_on_heads p x (h # hs)
      (cache # caches) =
    gpt_neo_projected_bounded_head_cache_append p h x cache #
      gpt_neo_projected_bounded_cache_extend_on_heads p x hs caches"

definition gpt_neo_projected_bounded_cache_extend ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   gpt_neo_projected_layer_cache \<Rightarrow>
   gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_bounded_cache_extend p x cache =
    gpt_neo_projected_bounded_cache_extend_on_heads p x
      [0..<gpt_neo_head_count p] cache"

lemma gpt_neo_projected_bounded_head_cache_append_of:
  "gpt_neo_projected_bounded_head_cache_append p h x
      (gpt_neo_projected_bounded_head_cache_of p prefix h) =
    gpt_neo_projected_bounded_head_cache_of p (prefix @ [x]) h"
proof -
  have cache_eq:
    "gpt_neo_projected_bounded_head_cache_of p prefix h =
      cache_of (gpt_neo_projected_key p h)
        (gpt_neo_projected_value p h)
        (gpt_neo_attention_context (gpt_neo_attention_window p)
          (map (gpt_neo_normalized_input p) prefix))"
    by (simp add: gpt_neo_projected_bounded_head_cache_of_def)
  have context_append:
    "gpt_neo_attention_context (gpt_neo_attention_window p)
        (gpt_neo_attention_context (gpt_neo_attention_window p)
          (map (gpt_neo_normalized_input p) prefix) @
          [gpt_neo_normalized_input p x]) =
      gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    by (simp add: gpt_neo_attention_context_append_trim)
  have append_record:
    "\<lparr>cache_keys =
        cache_keys (gpt_neo_projected_bounded_head_cache_of p prefix h) @
          [gpt_neo_projected_key p h (gpt_neo_normalized_input p x)],
      cache_values =
        cache_values (gpt_neo_projected_bounded_head_cache_of p prefix h) @
          [gpt_neo_projected_value p h (gpt_neo_normalized_input p x)]\<rparr> =
      cache_of (gpt_neo_projected_key p h)
        (gpt_neo_projected_value p h)
        (gpt_neo_attention_context (gpt_neo_attention_window p)
          (map (gpt_neo_normalized_input p) prefix) @
          [gpt_neo_normalized_input p x])"
    using cache_eq
    by (simp add: cache_eq cache_of_def)
  have trimmed:
    "gpt_neo_trim_cache (gpt_neo_attention_window p)
        (cache_of (gpt_neo_projected_key p h)
          (gpt_neo_projected_value p h)
          (gpt_neo_attention_context (gpt_neo_attention_window p)
            (map (gpt_neo_normalized_input p) prefix) @
            [gpt_neo_normalized_input p x])) =
      cache_of (gpt_neo_projected_key p h)
        (gpt_neo_projected_value p h)
        (gpt_neo_attention_context (gpt_neo_attention_window p)
          (map (gpt_neo_normalized_input p) (prefix @ [x])))"
  proof -
    have trim_step:
      "gpt_neo_trim_cache (gpt_neo_attention_window p)
          (cache_of (gpt_neo_projected_key p h)
            (gpt_neo_projected_value p h)
            (gpt_neo_attention_context (gpt_neo_attention_window p)
              (map (gpt_neo_normalized_input p) prefix) @
              [gpt_neo_normalized_input p x])) =
        cache_of (gpt_neo_projected_key p h)
          (gpt_neo_projected_value p h)
          (gpt_neo_attention_context (gpt_neo_attention_window p)
            (gpt_neo_attention_context (gpt_neo_attention_window p)
              (map (gpt_neo_normalized_input p) prefix) @
              [gpt_neo_normalized_input p x]))"
      by (rule gpt_neo_trim_cache_of)
    show ?thesis
      using trim_step context_append
      by (simp add: trim_step context_append)
  qed
  show ?thesis
    unfolding gpt_neo_projected_bounded_head_cache_append_def
    using append_record trimmed
    by (simp add: append_record trimmed
      gpt_neo_projected_bounded_head_cache_of_def cache_of_def)
qed

lemma gpt_neo_projected_bounded_cache_extend_on_heads_map:
  "gpt_neo_projected_bounded_cache_extend_on_heads p x hs
      (map (gpt_neo_projected_bounded_head_cache_of p prefix) hs) =
    map (gpt_neo_projected_bounded_head_cache_of p (prefix @ [x])) hs"
proof (induction hs)
  case Nil
  then show ?case by simp
next
  case (Cons h hs)
  then show ?case
    by (simp add: gpt_neo_projected_bounded_head_cache_append_of)
qed

lemma gpt_neo_projected_bounded_cache_extend_of:
  "gpt_neo_projected_bounded_cache_extend p x
      (gpt_neo_projected_bounded_cache_of p prefix) =
    gpt_neo_projected_bounded_cache_of p (prefix @ [x])"
  by (simp add: gpt_neo_projected_bounded_cache_extend_def
      gpt_neo_projected_bounded_cache_of_def
      gpt_neo_projected_bounded_cache_extend_on_heads_map)

lemma gpt_neo_projected_bounded_cache_extend_matches:
  assumes match: "gpt_neo_projected_bounded_cache_matches p prefix cache"
  shows "gpt_neo_projected_bounded_cache_matches p (prefix @ [x])
    (gpt_neo_projected_bounded_cache_extend p x cache)"
  using match
  by (simp add: gpt_neo_projected_bounded_cache_matches_def
      gpt_neo_projected_bounded_cache_extend_of)

lemma gpt_neo_projected_attention_heads_bounded:
  "gpt_neo_projected_attention_heads p x hs
      (map (gpt_neo_projected_bounded_head_cache_of p prefix) hs) =
    map (\<lambda>h. exact_attention (gpt_neo_head_dimension p)
      (gpt_neo_head_dimension p)
      (gpt_neo_projected_query p h x)
      (gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_projected_key p h)
          (gpt_neo_attention_context (gpt_neo_attention_window p)
            (map (gpt_neo_normalized_input p) prefix))))
      (gpt_neo_attention_context (gpt_neo_attention_window p)
        (map (gpt_neo_projected_value p h)
          (gpt_neo_attention_context (gpt_neo_attention_window p)
            (map (gpt_neo_normalized_input p) prefix))))
      ) hs"
proof (induction hs)
  case Nil
  then show ?case by simp
next
  case (Cons h hs)
  then show ?case
    by (simp add: gpt_neo_projected_bounded_head_cache_of_def
      gpt_neo_projected_attention_heads.simps cache_of_def)
qed

lemma gpt_neo_projected_attention_aggregator_bounded:
  "gpt_neo_projected_attention_aggregator p x
      (gpt_neo_projected_bounded_cache_of p prefix) =
    gpt_neo_windowed_multi_head_at_prefix
      (gpt_neo_head_count p) (gpt_neo_model_dimension p)
      (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)
      (gpt_neo_output_bias p)
      (gpt_neo_normalized_input p x)
      (map (gpt_neo_normalized_input p) prefix)"
  by (simp add: gpt_neo_projected_attention_aggregator_def
      gpt_neo_projected_bounded_cache_of_def
      gpt_neo_projected_attention_heads_bounded
      gpt_neo_windowed_multi_head_at_prefix_def
      gpt_neo_windowed_head_attention_def
      gpt_neo_projected_query_def
      gpt_neo_projected_key_def
      gpt_neo_projected_value_def
      gpt_neo_attention_context_map
      gpt_neo_attention_context_idempotent map_map comp_def)

definition gpt_neo_projected_bounded_cached_attention ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   gpt_neo_projected_layer_cache \<Rightarrow> real vector" where
  "gpt_neo_projected_bounded_cached_attention p x cache =
    gpt_neo_projected_attention_aggregator p x
      (gpt_neo_projected_bounded_cache_extend p x cache)"

theorem gpt_neo_projected_bounded_cached_attention_correct:
  assumes match:
    "gpt_neo_projected_bounded_cache_matches p prefix cache"
  shows "gpt_neo_projected_bounded_cached_attention p x cache =
    gpt_neo_windowed_multi_head_at_prefix
      (gpt_neo_head_count p) (gpt_neo_model_dimension p)
      (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)
      (gpt_neo_output_bias p)
      (gpt_neo_normalized_input p x)
      (map (gpt_neo_normalized_input p) (prefix @ [x]))"
  using match
  by (simp add: gpt_neo_projected_bounded_cached_attention_def
      gpt_neo_projected_bounded_cache_matches_def
      gpt_neo_projected_bounded_cache_extend_of
      gpt_neo_projected_attention_aggregator_bounded)

definition gpt_neo_projected_bounded_cached_block_step ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   gpt_neo_projected_layer_cache \<Rightarrow>
   real vector \<times> gpt_neo_projected_layer_cache" where
  "gpt_neo_projected_bounded_cached_block_step p x cache =
    (gpt_neo_block_from_attention p x
       (gpt_neo_projected_bounded_cached_attention p x cache),
     gpt_neo_projected_bounded_cache_extend p x cache)"

theorem gpt_neo_projected_bounded_cached_block_step_correct:
  assumes valid: "valid_gpt_neo_layer p"
    and match:
      "gpt_neo_projected_bounded_cache_matches p prefix cache"
  shows "fst (gpt_neo_projected_bounded_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    and "gpt_neo_projected_bounded_cache_matches p (prefix @ [x])
      (snd (gpt_neo_projected_bounded_cached_block_step p x cache))"
proof -
  have attention:
    "gpt_neo_projected_bounded_cached_attention p x cache =
      gpt_neo_windowed_multi_head_at_prefix
        (gpt_neo_head_count p) (gpt_neo_model_dimension p)
        (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
        (gpt_neo_query_weights p) (gpt_neo_key_weights p)
        (gpt_neo_value_weights p) (gpt_neo_output_weights p)
        (gpt_neo_output_bias p)
        (gpt_neo_normalized_input p x)
        (map (gpt_neo_normalized_input p) (prefix @ [x]))"
    by (rule gpt_neo_projected_bounded_cached_attention_correct[OF match])
  show "fst (gpt_neo_projected_bounded_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
    using attention
    by (simp add: gpt_neo_projected_bounded_cached_block_step_def
        gpt_neo_block_at_prefix_from_attention)
  show "gpt_neo_projected_bounded_cache_matches p (prefix @ [x])
      (snd (gpt_neo_projected_bounded_cached_block_step p x cache))"
  proof -
    have extension:
      "gpt_neo_projected_bounded_cache_matches p (prefix @ [x])
        (gpt_neo_projected_bounded_cache_extend p x cache)"
      by (rule gpt_neo_projected_bounded_cache_extend_matches[OF match])
    show ?thesis
      unfolding gpt_neo_projected_bounded_cached_block_step_def
      using extension by simp
  qed
qed

corollary gpt_neo_projected_bounded_cached_block_step_output:
  assumes valid: "valid_gpt_neo_layer p"
    and match:
      "gpt_neo_projected_bounded_cache_matches p prefix cache"
  shows "fst (gpt_neo_projected_bounded_cached_block_step p x cache) =
      gpt_neo_block_at_prefix p x (prefix @ [x])"
  using gpt_neo_projected_bounded_cached_block_step_correct(1)
    [OF valid match] .

corollary gpt_neo_projected_bounded_cached_block_step_cache:
  assumes valid: "valid_gpt_neo_layer p"
    and match:
      "gpt_neo_projected_bounded_cache_matches p prefix cache"
  shows "gpt_neo_projected_bounded_cache_matches p (prefix @ [x])
      (snd (gpt_neo_projected_bounded_cached_block_step p x cache))"
  using gpt_neo_projected_bounded_cached_block_step_correct(2)
    [OF valid match] .

end
