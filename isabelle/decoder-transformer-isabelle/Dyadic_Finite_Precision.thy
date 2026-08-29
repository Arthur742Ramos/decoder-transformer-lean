theory Dyadic_Finite_Precision
  imports Projection_Stability Modern_Generation
begin

section \<open>Concrete Dyadic Finite-Precision Projection\<close>

text \<open>
  This theory discharges the abstract rounding obligation for a concrete
  arithmetic kernel.  At fractional precision @{term p}, @{term dyadic_round}
  rounds a real number to the nearest point of the grid with spacing
  @{term "inverse ((2::real) ^ p)"}.  A dot product is evaluated by ideal
  fused multiply-adds, with one such rounding after every FMA.

  The model is deliberately narrower than IEEE 754.  It has no bounded
  exponent, subnormal, infinity, NaN, signed-zero, or ties-to-even semantics.
  It is nevertheless a fully specified fixed-fraction arithmetic kernel with
  an explicit accumulated error certificate, rather than an assumed error
  relation.
\<close>

definition dyadic_scale :: "nat \<Rightarrow> real" where
  "dyadic_scale p = (2::real) ^ p"

definition dyadic_unit_roundoff :: "nat \<Rightarrow> real" where
  "dyadic_unit_roundoff p = inverse (2 * dyadic_scale p)"

definition dyadic_round :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "dyadic_round p x = of_int (round (x * dyadic_scale p)) / dyadic_scale p"

lemma dyadic_scale_pos:
  "0 < dyadic_scale p"
  by (simp add: dyadic_scale_def)

lemma dyadic_unit_roundoff_nonnegative:
  "0 \<le> dyadic_unit_roundoff p"
  by (simp add: dyadic_unit_roundoff_def dyadic_scale_def)

lemma dyadic_round_grid [simp]:
  "dyadic_round p (of_int k / dyadic_scale p) =
    of_int k / dyadic_scale p"
  using dyadic_scale_pos[of p]
  by (simp add: dyadic_round_def field_simps)

theorem dyadic_round_idempotent [simp]:
  "dyadic_round p (dyadic_round p x) = dyadic_round p x"
  by (simp add: dyadic_round_def)

theorem dyadic_round_error:
  "\<bar>dyadic_round p x - x\<bar> \<le> dyadic_unit_roundoff p"
proof -
  let ?s = "dyadic_scale p"
  have s_pos: "0 < ?s" by (rule dyadic_scale_pos)
  have local:
    "\<bar>of_int (round (x * ?s)) - x * ?s\<bar> \<le> (1 / 2::real)"
    by (rule of_int_round_abs_le)
  have identity:
    "\<bar>dyadic_round p x - x\<bar> * ?s =
      \<bar>of_int (round (x * ?s)) - x * ?s\<bar>"
    using s_pos
    by (simp add: dyadic_round_def abs_mult[symmetric] field_simps)
  have "\<bar>dyadic_round p x - x\<bar> * ?s \<le> (1 / 2::real)"
    using local identity by simp
  then show ?thesis
    using s_pos
    by (simp add: dyadic_unit_roundoff_def field_simps)
qed

corollary dyadic_round_error_symmetric:
  "\<bar>x - dyadic_round p x\<bar> \<le> dyadic_unit_roundoff p"
  using dyadic_round_error[of p x]
  by (simp add: abs_minus_commute)

fun dyadic_fma_dot :: "nat \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> real" where
  "dyadic_fma_dot p [] ys = 0"
| "dyadic_fma_dot p (x # xs) [] = 0"
| "dyadic_fma_dot p (x # xs) (w # ws) =
    dyadic_round p (x * w + dyadic_fma_dot p xs ws)"

theorem dyadic_fma_dot_error:
  "\<bar>dot_product xs ws - dyadic_fma_dot p xs ws\<bar> \<le>
    real (min (length xs) (length ws)) * dyadic_unit_roundoff p"
proof (induction xs arbitrary: ws)
  case Nil
  show ?case by (simp add: dot_product_def)
next
  case (Cons x xs)
  show ?case
  proof (cases ws)
    case Nil
    then show ?thesis by (simp add: dot_product_def)
  next
    case (Cons w ws')
    have tail:
      "\<bar>dot_product xs ws' - dyadic_fma_dot p xs ws'\<bar> \<le>
        real (min (length xs) (length ws')) * dyadic_unit_roundoff p"
      by (rule Cons.IH)
    have local:
      "\<bar>(x * w + dyadic_fma_dot p xs ws') -
        dyadic_round p (x * w + dyadic_fma_dot p xs ws')\<bar> \<le>
        dyadic_unit_roundoff p"
      by (rule dyadic_round_error_symmetric)
    have decomposition:
      "dot_product (x # xs) (w # ws') -
        dyadic_fma_dot p (x # xs) (w # ws') =
        (dot_product xs ws' - dyadic_fma_dot p xs ws') +
        ((x * w + dyadic_fma_dot p xs ws') -
          dyadic_round p (x * w + dyadic_fma_dot p xs ws'))"
      by (simp add: dot_product_def algebra_simps)
    have "\<bar>dot_product (x # xs) (w # ws') -
        dyadic_fma_dot p (x # xs) (w # ws')\<bar> \<le>
        \<bar>dot_product xs ws' - dyadic_fma_dot p xs ws'\<bar> +
        \<bar>(x * w + dyadic_fma_dot p xs ws') -
          dyadic_round p (x * w + dyadic_fma_dot p xs ws')\<bar>"
      unfolding decomposition by (rule abs_triangle_ineq)
    also have "... \<le>
        real (min (length xs) (length ws')) * dyadic_unit_roundoff p +
        dyadic_unit_roundoff p"
      using tail local by simp
    also have "... =
        real (min (length (x # xs)) (length (w # ws'))) *
          dyadic_unit_roundoff p"
      by (simp add: algebra_simps)
    finally show ?thesis unfolding Cons .
  qed
qed

definition dyadic_linear_project ::
  "nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow> real vector \<Rightarrow> real vector" where
  "dyadic_linear_project p out_dim W x =
    map (dyadic_fma_dot p x) (matrix_columns out_dim W)"

lemma length_dyadic_linear_project [simp]:
  "length (dyadic_linear_project p out_dim W x) = out_dim"
  by (simp add: dyadic_linear_project_def matrix_columns_def)

theorem dyadic_linear_project_error:
  assumes matrix: "matrix_shape in_dim out_dim W"
  shows "vector_error_bound
    (real in_dim * dyadic_unit_roundoff p)
    (linear_project out_dim W x)
    (dyadic_linear_project p out_dim W x)"
proof (unfold vector_error_bound_def, intro conjI allI impI)
  show "length (linear_project out_dim W x) =
    length (dyadic_linear_project p out_dim W x)"
    by (simp add: linear_project_def matrix_columns_def)
next
  fix i
  assume i: "i < length (linear_project out_dim W x)"
  let ?columns = "matrix_columns out_dim W"
  have i_out: "i < out_dim"
    using i by (simp add: linear_project_def matrix_columns_def)
  have columns: "matrix_shape out_dim in_dim ?columns"
    by (rule matrix_columns_shape[OF matrix])
  have column_length: "length (?columns ! i) = in_dim"
    by (rule matrix_shape_nth[OF columns i_out])
  have raw:
    "\<bar>dot_product x (?columns ! i) -
      dyadic_fma_dot p x (?columns ! i)\<bar> \<le>
      real (min (length x) in_dim) * dyadic_unit_roundoff p"
    using dyadic_fma_dot_error[of x "?columns ! i" p]
      column_length by simp
  have scaled:
    "real (min (length x) in_dim) * dyadic_unit_roundoff p \<le>
      real in_dim * dyadic_unit_roundoff p"
    apply (rule mult_right_mono)
    using dyadic_unit_roundoff_nonnegative by simp_all
  have local:
    "\<bar>dot_product x (?columns ! i) -
      dyadic_fma_dot p x (?columns ! i)\<bar> \<le>
      real in_dim * dyadic_unit_roundoff p"
    by (rule order_trans[OF raw scaled])
  show "\<bar>linear_project out_dim W x ! i -
      dyadic_linear_project p out_dim W x ! i\<bar> \<le>
      real in_dim * dyadic_unit_roundoff p"
    using local i_out
    by (simp add: linear_project_def dyadic_linear_project_def
        matrix_columns_def)
qed

definition dyadic_next_token_logits ::
  "nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow> real vector \<Rightarrow> real vector" where
  "dyadic_next_token_logits p vocabulary_size W_vocabulary hidden =
    dyadic_linear_project p vocabulary_size W_vocabulary hidden"

theorem dyadic_next_token_rounding_relation:
  assumes matrix: "matrix_shape model_dim vocabulary_size W_vocabulary"
  shows "rounding_relation
    (real model_dim * dyadic_unit_roundoff p)
    (next_token_logits vocabulary_size W_vocabulary)
    (dyadic_next_token_logits p vocabulary_size W_vocabulary)"
proof (unfold rounding_relation_def, intro conjI allI)
  show "0 \<le> real model_dim * dyadic_unit_roundoff p"
    using dyadic_unit_roundoff_nonnegative
    by (intro mult_nonneg_nonneg) simp_all
next
  fix x
  show "vector_error_bound (real model_dim * dyadic_unit_roundoff p)
    (next_token_logits vocabulary_size W_vocabulary x)
    (dyadic_next_token_logits p vocabulary_size W_vocabulary x)"
    unfolding next_token_logits_def dyadic_next_token_logits_def
    by (rule dyadic_linear_project_error[OF matrix])
qed

theorem concrete_dyadic_next_token_logit_error:
  assumes model:
    "floating_transformer_relation hidden_error exact_model finite_model"
    and matrix: "matrix_shape model_dim vocabulary_size W_vocabulary"
    and bound: "projection_l1_bound vocabulary_size W_vocabulary L"
  shows "vector_error_bound
    (L * hidden_error + real model_dim * dyadic_unit_roundoff p)
    (next_token_logits vocabulary_size W_vocabulary (exact_model input))
    (dyadic_next_token_logits p vocabulary_size W_vocabulary
      (finite_model input))"
  apply (rule concrete_next_token_logit_error[OF model matrix bound])
  by (rule dyadic_next_token_rounding_relation[OF matrix])

theorem cached_modern_dyadic_next_token_logit_error:
  assumes valid: "valid_modern_decoder_stack layers"
    and cache:
      "modern_transformer_cache_matches layers start prefix caches"
    and matrix: "matrix_shape model_dim vocabulary_size W_vocabulary"
  shows "vector_error_bound
    (real model_dim * dyadic_unit_roundoff p)
    (next_token_logits vocabulary_size W_vocabulary
      (last (full_modern_decoder_stack layers start (prefix @ [x]))))
    (dyadic_next_token_logits p vocabulary_size W_vocabulary
      (fst (cached_modern_decoder_stack_step layers
        (start + length prefix) x caches)))"
proof -
  have hidden:
    "fst (cached_modern_decoder_stack_step layers
        (start + length prefix) x caches) =
      last (full_modern_decoder_stack layers start (prefix @ [x]))"
    by (rule incremental_modern_decoder_equals_full[OF valid cache])
  have local:
    "vector_error_bound (real model_dim * dyadic_unit_roundoff p)
      (next_token_logits vocabulary_size W_vocabulary
        (fst (cached_modern_decoder_stack_step layers
          (start + length prefix) x caches)))
      (dyadic_next_token_logits p vocabulary_size W_vocabulary
        (fst (cached_modern_decoder_stack_step layers
          (start + length prefix) x caches)))"
    using dyadic_next_token_rounding_relation[OF matrix, of p]
    by (simp add: rounding_relation_def)
  show ?thesis using local hidden by simp
qed

corollary binary32_fraction_grid_next_token_logit_error:
  assumes model:
    "floating_transformer_relation hidden_error exact_model finite_model"
    and matrix: "matrix_shape model_dim vocabulary_size W_vocabulary"
    and bound: "projection_l1_bound vocabulary_size W_vocabulary L"
  shows "vector_error_bound
    (L * hidden_error + real model_dim / 16777216)
    (next_token_logits vocabulary_size W_vocabulary (exact_model input))
    (dyadic_next_token_logits 23 vocabulary_size W_vocabulary
      (finite_model input))"
  using concrete_dyadic_next_token_logit_error[OF model matrix bound,
      of 23 input]
  by (simp add: dyadic_unit_roundoff_def dyadic_scale_def)

end
