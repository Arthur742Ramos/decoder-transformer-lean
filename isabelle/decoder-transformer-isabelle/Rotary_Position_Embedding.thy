theory Rotary_Position_Embedding
  imports Projection_Stability
begin

section \<open>Rotary Position Embeddings and Cache Alignment\<close>

text \<open>
  The angle schedule is deliberately parametric: different model families use
  different base frequencies and scaling rules.  Adjacent coordinates form a
  rotation plane, while a final unpaired coordinate is left unchanged.
\<close>

fun rope_rotate_from ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "rope_rotate_from angles position pair [] = []"
| "rope_rotate_from angles position pair [x] = [x]"
| "rope_rotate_from angles position pair (x # y # xs) =
    (let theta = angles pair position
     in (x * cos theta - y * sin theta) #
        (x * sin theta + y * cos theta) #
        rope_rotate_from angles position (Suc pair) xs)"

definition rope_rotate ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "rope_rotate angles position x = rope_rotate_from angles position 0 x"

lemma length_rope_rotate_from [simp]:
  "length (rope_rotate_from angles position pair x) = length x"
  by (induction angles position pair x rule: rope_rotate_from.induct)
    (simp_all add: Let_def)

theorem rope_rotate_preserves_shape:
  assumes "vector_shape head_dim x"
  shows "vector_shape head_dim (rope_rotate angles position x)"
  using assms by (simp add: vector_shape_def rope_rotate_def)

definition squared_l2_norm :: "real vector \<Rightarrow> real" where
  "squared_l2_norm x = sum_list (map (\<lambda>v. v * v) x)"

lemma planar_rotation_pair_norm:
  fixes theta x y :: real
  shows "(x * cos theta - y * sin theta) * (x * cos theta - y * sin theta) +
    (x * sin theta + y * cos theta) * (x * sin theta + y * cos theta) =
    x * x + y * y"
proof -
  have trig: "cos theta * cos theta + sin theta * sin theta = 1"
    by (metis sin_cos_squared_add3)
  have "(x * cos theta - y * sin theta) * (x * cos theta - y * sin theta) +
      (x * sin theta + y * cos theta) * (x * sin theta + y * cos theta) =
    (x * x + y * y) * (cos theta * cos theta + sin theta * sin theta)"
    by (simp only: algebra_simps)
  with trig show ?thesis by simp
qed

theorem rope_rotate_from_preserves_squared_norm:
  "squared_l2_norm (rope_rotate_from angles position pair x) =
    squared_l2_norm x"
  by (induction angles position pair x rule: rope_rotate_from.induct)
    (simp_all add: squared_l2_norm_def Let_def planar_rotation_pair_norm)

corollary rope_rotate_preserves_squared_norm:
  "squared_l2_norm (rope_rotate angles position x) = squared_l2_norm x"
  unfolding rope_rotate_def
  by (rule rope_rotate_from_preserves_squared_norm)

subsection \<open>Position-indexed exact attention\<close>

definition indexed_sequence :: "nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> 'a) list" where
  "indexed_sequence start xs = zip [start..<start + length xs] xs"

lemma length_indexed_sequence [simp]:
  "length (indexed_sequence start xs) = length xs"
  by (simp add: indexed_sequence_def)

lemma indexed_sequence_snd [simp]:
  "map snd (indexed_sequence start xs) = xs"
  by (simp add: indexed_sequence_def)

lemma indexed_sequence_append_singleton:
  "indexed_sequence start (xs @ [x]) =
    indexed_sequence start xs @ [(start + length xs, x)]"
  unfolding indexed_sequence_def
  by (simp add: upt_Suc_append)

definition rotary_project ::
  "nat \<Rightarrow> real matrix \<Rightarrow> (nat \<Rightarrow> real vector \<Rightarrow> real vector) \<Rightarrow>
   nat \<times> real vector \<Rightarrow> real vector" where
  "rotary_project out_dim W rotation ix =
    rotation (fst ix) (linear_project out_dim W (snd ix))"

definition positioned_value_project ::
  "nat \<Rightarrow> real matrix \<Rightarrow> nat \<times> real vector \<Rightarrow> real vector" where
  "positioned_value_project out_dim W ix =
    linear_project out_dim W (snd ix)"

definition rotary_exact_causal_attention ::
  "nat \<Rightarrow> nat \<Rightarrow>
   (nat \<Rightarrow> real vector \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real matrix \<Rightarrow> real matrix" where
  "rotary_exact_causal_attention head_dim value_dim rotation start WQ WK WV xs =
    exact_causal_attention head_dim value_dim
      (rotary_project head_dim WQ rotation)
      (rotary_project head_dim WK rotation)
      (positioned_value_project value_dim WV)
      (indexed_sequence start xs)"

definition rotary_exact_cached_attention ::
  "nat \<Rightarrow> nat \<Rightarrow>
   (nat \<Rightarrow> real vector \<Rightarrow> real vector) \<Rightarrow>
   nat \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real matrix \<Rightarrow> real matrix" where
  "rotary_exact_cached_attention head_dim value_dim rotation start WQ WK WV xs =
    exact_cached_attention head_dim value_dim
      (rotary_project head_dim WQ rotation)
      (rotary_project head_dim WK rotation)
      (positioned_value_project value_dim WV)
      (indexed_sequence start xs)"

theorem rotary_cached_attention_equals_full:
  "rotary_exact_cached_attention head_dim value_dim rotation start WQ WK WV xs =
    rotary_exact_causal_attention head_dim value_dim rotation start WQ WK WV xs"
  unfolding rotary_exact_cached_attention_def rotary_exact_causal_attention_def
  by (rule exact_cached_attention_eq_full)

theorem rotary_exact_attention_shape:
  "matrix_shape (length xs) value_dim
    (rotary_exact_causal_attention head_dim value_dim rotation start WQ WK WV xs)"
proof -
  have "matrix_shape (length (indexed_sequence start xs)) value_dim
    (exact_causal_attention head_dim value_dim
      (rotary_project head_dim WQ rotation)
      (rotary_project head_dim WK rotation)
      (positioned_value_project value_dim WV)
      (indexed_sequence start xs))"
    by (rule exact_causal_attention_shape)
  then show ?thesis by (simp add: rotary_exact_causal_attention_def)
qed

theorem positioned_cache_extension:
  fixes C :: "(real vector, real vector) kv_cache"
  assumes cache:
    "cache_matches K V (indexed_sequence start prefix) C"
  shows "cached_step Q K V A C
      (start + length prefix, x) =
    (cache_of K V (indexed_sequence start (prefix @ [x])),
      A (Q (start + length prefix, x))
        (map K (indexed_sequence start (prefix @ [x])))
        (map V (indexed_sequence start (prefix @ [x]))))"
proof -
  have refined:
    "cached_step Q K V A C
        (start + length prefix, x) =
      (cache_of K V
          (indexed_sequence start prefix @ [(start + length prefix, x)]),
       A (Q (start + length prefix, x))
        (map K (indexed_sequence start prefix @ [(start + length prefix, x)]))
        (map V (indexed_sequence start prefix @ [(start + length prefix, x)])))"
    by (rule cached_step_refines_full[OF cache])
  show ?thesis
    using refined indexed_sequence_append_singleton[of start prefix x]
    by simp
qed

end
