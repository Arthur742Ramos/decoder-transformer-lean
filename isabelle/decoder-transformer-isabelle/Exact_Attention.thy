theory Exact_Attention
  imports Shaped_Tensors Complex_Main
begin

section \<open>Exact Scaled Dot-Product Attention\<close>

text \<open>
  This theory instantiates the structural attention interface over real-valued
  vectors.  The list softmax is total; the normalization theorem uses the
  nonempty-prefix condition that is always satisfied at a decoder position.
\<close>

definition softmax_denominator :: "real list \<Rightarrow> real" where
  "softmax_denominator xs = sum_list (map exp xs)"

definition list_softmax :: "real list \<Rightarrow> real list" where
  "list_softmax xs =
    map (\<lambda>x. exp x / softmax_denominator xs) xs"

lemma length_list_softmax [simp]:
  "length (list_softmax xs) = length xs"
  by (simp add: list_softmax_def)

lemma list_softmax_empty [simp]:
  "list_softmax [] = []"
  by (simp add: list_softmax_def)

lemma softmax_denominator_pos:
  assumes "xs \<noteq> []"
  shows "0 < softmax_denominator xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail_nonneg: "0 \<le> sum_list (map exp xs)"
    by (rule sum_list_nonneg) (auto intro: less_imp_le exp_gt_zero)
  have "0 < exp x"
    by simp
  then have "0 < exp x + sum_list (map exp xs)"
    by (rule add_pos_nonneg[OF _ tail_nonneg])
  then show ?case
    by (simp add: softmax_denominator_def)
qed

lemma sum_list_map_divide:
  fixes f :: "'a \<Rightarrow> real"
  shows "sum_list (map (\<lambda>x. f x / c) xs) = sum_list (map f xs) / c"
  by (induction xs) (simp_all add: add_divide_distrib)

theorem list_softmax_normalized:
  assumes "xs \<noteq> []"
  shows "sum_list (list_softmax xs) = 1"
proof -
  have positive: "0 < softmax_denominator xs"
    by (rule softmax_denominator_pos[OF assms])
  then have nonzero: "softmax_denominator xs \<noteq> 0"
    by simp
  have numerator:
    "sum_list (map exp xs) = softmax_denominator xs"
    by (simp add: softmax_denominator_def)
  show ?thesis
    unfolding list_softmax_def
    by (simp add: sum_list_map_divide numerator nonzero)
qed

lemma list_softmax_positive:
  assumes "xs \<noteq> []" "w \<in> set (list_softmax xs)"
  shows "0 < w"
proof -
  have denominator: "0 < softmax_denominator xs"
    by (rule softmax_denominator_pos[OF assms(1)])
  from assms(2) obtain x where
    x: "x \<in> set xs" "w = exp x / softmax_denominator xs"
    by (auto simp: list_softmax_def)
  show ?thesis
    unfolding x(2)
    using denominator by (simp add: divide_pos_pos)
qed

definition scaled_dot_score ::
  "nat \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> real" where
  "scaled_dot_score head_dim q k =
    dot_product q k / sqrt (real head_dim)"

definition attention_weights ::
  "nat \<Rightarrow> real vector \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "attention_weights head_dim q keys =
    list_softmax (map (scaled_dot_score head_dim q) keys)"

lemma attention_weights_length [simp]:
  "length (attention_weights head_dim q keys) = length keys"
  by (simp add: attention_weights_def)

theorem attention_weights_normalized:
  assumes "keys \<noteq> []"
  shows "sum_list (attention_weights head_dim q keys) = 1"
  using assms
  by (simp add: attention_weights_def list_softmax_normalized)

theorem attention_weights_positive:
  assumes "keys \<noteq> []" "w \<in> set (attention_weights head_dim q keys)"
  shows "0 < w"
  using assms
  by (auto simp: attention_weights_def intro: list_softmax_positive)

lemma prefix_attention_weights_normalized:
  "sum_list
    (attention_weights head_dim q (map K (prefix @ [x]))) = 1"
  by (rule attention_weights_normalized) simp

definition weighted_value_sum ::
  "nat \<Rightarrow> real vector \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "weighted_value_sum value_dim weights values =
    map (\<lambda>j. sum_list (map2 (\<lambda>w v. w * (v ! j)) weights values))
      [0..<value_dim]"

lemma weighted_value_sum_shape:
  "vector_shape value_dim (weighted_value_sum value_dim weights values)"
  by (simp add: vector_shape_def weighted_value_sum_def)

definition exact_attention ::
  "nat \<Rightarrow> nat \<Rightarrow>
   real vector \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "exact_attention head_dim value_dim q keys values =
    weighted_value_sum value_dim (attention_weights head_dim q keys) values"

lemma exact_attention_shape:
  "vector_shape value_dim
    (exact_attention head_dim value_dim q keys values)"
  by (simp add: exact_attention_def weighted_value_sum_shape)

lemma map_zero_upt:
  "map (\<lambda>j. (0 :: real)) [0..<n] = replicate n 0"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have mapped:
    "map (\<lambda>j. (0 :: real)) [0..<Suc n] =
      0 # map (\<lambda>j. (0 :: real)) [0..<n]"
    by (simp only: map_upt_Suc; simp)
  then show ?case
    using Suc.IH by (simp add: replicate_Suc)
qed

lemma weighted_value_sum_empty_weights:
  "weighted_value_sum value_dim [] values = replicate value_dim 0"
  unfolding weighted_value_sum_def
  by (simp add: map_zero_upt)

lemma exact_attention_empty_keys [simp]:
  "exact_attention head_dim value_dim q [] values = replicate value_dim 0"
  by (simp add: exact_attention_def attention_weights_def
      weighted_value_sum_empty_weights)

definition exact_causal_attention ::
  "nat \<Rightarrow> nat \<Rightarrow>
   ('x \<Rightarrow> real vector) \<Rightarrow>
   ('x \<Rightarrow> real vector) \<Rightarrow>
   ('x \<Rightarrow> real vector) \<Rightarrow>
   'x list \<Rightarrow> real matrix" where
  "exact_causal_attention head_dim value_dim Q K V =
    causal_attention Q K V (exact_attention head_dim value_dim)"

lemma exact_causal_attention_from_shape:
  "matrix_shape (length xs) value_dim
    (causal_attention_from Q K V (exact_attention head_dim value_dim) prefix xs)"
proof (induction xs arbitrary: prefix)
  case Nil
  then show ?case by (simp add: matrix_shape_def)
next
  case (Cons x xs)
  have head:
    "length (exact_attention head_dim value_dim (Q x)
      (map K (prefix @ [x])) (map V (prefix @ [x]))) = value_dim"
    using exact_attention_shape by (simp add: vector_shape_def)
  have tail:
    "matrix_shape (length xs) value_dim
      (causal_attention_from Q K V (exact_attention head_dim value_dim)
        (prefix @ [x]) xs)"
    by (rule Cons.IH)
  show ?case
    using head tail by (auto simp: matrix_shape_def)
qed

theorem exact_causal_attention_shape:
  "matrix_shape (length xs) value_dim
    (exact_causal_attention head_dim value_dim Q K V xs)"
  unfolding exact_causal_attention_def causal_attention_def
  by (rule exact_causal_attention_from_shape)

theorem exact_causal_attention_independence:
  assumes "i < length xs" "i < length ys"
    and "take (Suc i) xs = take (Suc i) ys"
  shows "exact_causal_attention head_dim value_dim Q K V xs ! i =
    exact_causal_attention head_dim value_dim Q K V ys ! i"
  unfolding exact_causal_attention_def
  by (rule causal_attention_independence[OF assms])

definition exact_cached_attention ::
  "nat \<Rightarrow> nat \<Rightarrow>
   ('x \<Rightarrow> real vector) \<Rightarrow>
   ('x \<Rightarrow> real vector) \<Rightarrow>
   ('x \<Rightarrow> real vector) \<Rightarrow>
   'x list \<Rightarrow> real matrix" where
  "exact_cached_attention head_dim value_dim Q K V =
    cached_attention Q K V (exact_attention head_dim value_dim)"

theorem exact_cached_attention_eq_full:
  "exact_cached_attention head_dim value_dim Q K V xs =
    exact_causal_attention head_dim value_dim Q K V xs"
  unfolding exact_cached_attention_def exact_causal_attention_def
  by (rule cached_attention_eq_full_attention)

end
