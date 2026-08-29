theory Projection_Stability
  imports Prompt_Cache
begin

section \<open>Concrete Stability of Linear Projections\<close>

definition column_l1_norm :: "real vector \<Rightarrow> real" where
  "column_l1_norm w = sum_list (map abs w)"

definition projection_l1_bound ::
  "nat \<Rightarrow> real matrix \<Rightarrow> real \<Rightarrow> bool" where
  "projection_l1_bound out_dim W L \<longleftrightarrow>
    0 \<le> L \<and>
    (\<forall>w \<in> set (matrix_columns out_dim W). column_l1_norm w \<le> L)"

lemma column_l1_norm_nonnegative:
  "0 \<le> column_l1_norm w"
  unfolding column_l1_norm_def
  by (rule sum_list_nonneg) auto

lemma dot_product_sup_error:
  assumes epsilon: "0 \<le> epsilon"
    and xy: "length xs = length ys"
    and coordinates: "\<forall>i < length xs. \<bar>xs ! i - ys ! i\<bar> \<le> epsilon"
  shows "\<bar>dot_product xs w - dot_product ys w\<bar> \<le>
    column_l1_norm w * epsilon"
  using xy coordinates
proof (induction xs arbitrary: ys w)
  case Nil
  then have ys: "ys = []" by (cases ys) auto
  show ?case
    using epsilon column_l1_norm_nonnegative[of w]
    by (simp add: ys dot_product_def mult_nonneg_nonneg)
next
  case (Cons a xs)
  then obtain b ys' where ys: "ys = b # ys'"
    by (cases ys) auto
  have length_xy: "length (a # xs) = length (b # ys')"
    using Cons.prems(1) unfolding ys .
  have all_coordinates:
    "\<forall>i < length (a # xs). \<bar>(a # xs) ! i - (b # ys') ! i\<bar> \<le> epsilon"
    using Cons.prems(2) unfolding ys .
  show ?case
  proof (cases w)
    case Nil
    then show ?thesis
      by (simp add: ys dot_product_def column_l1_norm_def)
  next
    case (Cons c w')
    have length_tail: "length xs = length ys'"
      using length_xy by simp
    have head: "\<bar>a - b\<bar> \<le> epsilon"
      using all_coordinates[rule_format, of 0] by simp
    have tail_coordinates:
      "\<forall>i < length xs. \<bar>xs ! i - ys' ! i\<bar> \<le> epsilon"
    proof (intro allI impI)
      fix i
      assume "i < length xs"
      then show "\<bar>xs ! i - ys' ! i\<bar> \<le> epsilon"
        using all_coordinates[rule_format, of "Suc i"] by simp
    qed
    have tail:
      "\<bar>dot_product xs w' - dot_product ys' w'\<bar> \<le>
        column_l1_norm w' * epsilon"
      by (rule Cons.IH[OF length_tail tail_coordinates])
    have scaled_head: "\<bar>c\<bar> * \<bar>a - b\<bar> \<le> \<bar>c\<bar> * epsilon"
      by (rule mult_left_mono[OF head]) simp
    have decomposition:
      "dot_product (a # xs) (c # w') - dot_product (b # ys') (c # w') =
        (a - b) * c + (dot_product xs w' - dot_product ys' w')"
      by (simp add: dot_product_def algebra_simps)
    have "\<bar>dot_product (a # xs) (c # w') -
        dot_product (b # ys') (c # w')\<bar> \<le>
        column_l1_norm (c # w') * epsilon"
    proof -
      have "\<bar>dot_product (a # xs) (c # w') -
          dot_product (b # ys') (c # w')\<bar> =
        \<bar>(a - b) * c + (dot_product xs w' - dot_product ys' w')\<bar>"
        by (simp only: decomposition)
      also have "... \<le> \<bar>(a - b) * c\<bar> +
          \<bar>dot_product xs w' - dot_product ys' w'\<bar>"
        by (rule abs_triangle_ineq)
      also have "... \<le> \<bar>c\<bar> * epsilon + column_l1_norm w' * epsilon"
        using scaled_head tail by (simp add: abs_mult mult.commute)
      also have "... = column_l1_norm (c # w') * epsilon"
        by (simp add: column_l1_norm_def algebra_simps)
      finally show ?thesis .
    qed
    then show ?thesis
      unfolding ys Cons .
  qed
qed

theorem linear_project_lipschitz:
  assumes bound: "projection_l1_bound out_dim W L"
  shows "vector_lipschitz L (linear_project out_dim W)"
proof (unfold vector_lipschitz_def, intro conjI allI impI)
  show "0 \<le> L"
    using bound by (simp add: projection_l1_bound_def)
next
  fix epsilon xs ys
  assume epsilon: "0 \<le> epsilon"
    and error: "vector_error_bound epsilon xs ys"
  have lengths: "length xs = length ys"
    using error by (simp add: vector_error_bound_def)
  have output_lengths:
    "length (linear_project out_dim W xs) =
      length (linear_project out_dim W ys)"
    by (simp add: linear_project_def matrix_columns_def)
  have coordinates:
    "\<forall>i < length (linear_project out_dim W xs).
      \<bar>linear_project out_dim W xs ! i -
        linear_project out_dim W ys ! i\<bar> \<le> L * epsilon"
  proof (intro allI impI)
    fix i
    assume i: "i < length (linear_project out_dim W xs)"
    let ?columns = "matrix_columns out_dim W"
    let ?w = "?columns ! i"
    have column_count: "length ?columns = out_dim"
      by (simp add: matrix_columns_def)
    have i_out: "i < out_dim"
      using i by (simp add: linear_project_def matrix_columns_def)
    have column_member: "?w \<in> set ?columns"
      using i_out column_count by simp
    have local:
      "\<bar>dot_product xs ?w - dot_product ys ?w\<bar> \<le>
        column_l1_norm ?w * epsilon"
      apply (rule dot_product_sup_error[OF epsilon lengths])
      using error by (simp add: vector_error_bound_def)
    have norm_bound: "column_l1_norm ?w \<le> L"
      using bound column_member by (auto simp: projection_l1_bound_def)
    have scaled: "column_l1_norm ?w * epsilon \<le> L * epsilon"
      by (rule mult_right_mono[OF norm_bound epsilon])
    have projected_x:
      "linear_project out_dim W xs ! i = dot_product xs ?w"
      using i_out by (simp add: linear_project_def matrix_columns_def)
    have projected_y:
      "linear_project out_dim W ys ! i = dot_product ys ?w"
      using i_out by (simp add: linear_project_def matrix_columns_def)
    show "\<bar>linear_project out_dim W xs ! i -
      linear_project out_dim W ys ! i\<bar> \<le> L * epsilon"
      using local scaled projected_x projected_y by linarith
  qed
  show "vector_error_bound (L * epsilon)
    (linear_project out_dim W xs) (linear_project out_dim W ys)"
    using output_lengths coordinates
    by (simp add: vector_error_bound_def)
qed

corollary next_token_logits_lipschitz:
  assumes "matrix_shape model_dim vocabulary_size W_vocabulary"
    and "projection_l1_bound vocabulary_size W_vocabulary L"
  shows "vector_lipschitz L
    (next_token_logits vocabulary_size W_vocabulary)"
  unfolding next_token_logits_def
  by (rule linear_project_lipschitz[OF assms(2)])

corollary concrete_next_token_logit_error:
  assumes model:
    "floating_transformer_relation hidden_error exact_model floating_model"
    and matrix: "matrix_shape model_dim vocabulary_size W_vocabulary"
    and bound: "projection_l1_bound vocabulary_size W_vocabulary L"
    and rounding:
      "rounding_relation rounding_error
        (next_token_logits vocabulary_size W_vocabulary) floating_logits"
  shows "vector_error_bound (L * hidden_error + rounding_error)
    (next_token_logits vocabulary_size W_vocabulary (exact_model input))
    (floating_logits (floating_model input))"
  apply (rule next_token_logit_error[OF model _ rounding])
  by (rule next_token_logits_lipschitz[OF matrix bound])

end
