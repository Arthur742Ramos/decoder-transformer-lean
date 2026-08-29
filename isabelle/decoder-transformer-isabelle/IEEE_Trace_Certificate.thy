theory IEEE_Trace_Certificate
  imports IEEE_754_Projection
begin

section \<open>Reusable frozen linear-activation traces\<close>

text \<open>
  A trace records the previous accumulator as the nearest-value witness for
  each fused multiply-add step.  This is useful for small frozen checkpoints:
  the witness is a concrete same-format value, while the proof only needs a
  bound on the individual input products and the accumulator range.
\<close>

fun ieee_fma_dot_tail_witnesses ::
  "('e::len, 'f::len) IEEE.float vector \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow>
   ('e, 'f) IEEE.float vector" where
  "ieee_fma_dot_tail_witnesses [] ys = []"
| "ieee_fma_dot_tail_witnesses (x # xs) [] = []"
| "ieee_fma_dot_tail_witnesses (x # xs) (y # ys) =
     ieee_fma_dot xs ys # ieee_fma_dot_tail_witnesses xs ys"

lemma ieee_fma_dot_abs_bound:
  fixes xs ws :: "('e::len, 'f::len) IEEE.float vector"
  assumes lengths: "length xs = length ws"
    and x_bounds: "\<forall>x \<in> set xs. \<bar>IEEE.valof x\<bar> \<le> a"
    and w_bounds: "\<forall>w \<in> set ws. \<bar>IEEE.valof w\<bar> \<le> b"
  shows "\<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws)\<bar> \<le>
    real (length xs) * (a * b)"
using lengths x_bounds w_bounds
proof (induction xs arbitrary: ws)
  case Nil
  then show ?case by (cases ws) (simp_all add: dot_product_def)
next
  case (Cons x xs)
  have all_x_bounds:
    "\<forall>z \<in> set (x # xs). \<bar>IEEE.valof z\<bar> \<le> a"
    using Cons.prems(2) by assumption
  have all_w_bounds:
    "\<forall>z \<in> set ws. \<bar>IEEE.valof z\<bar> \<le> b"
    using Cons.prems(3) by assumption
  have x_bound: "\<bar>IEEE.valof x\<bar> \<le> a"
    using all_x_bounds by simp
  have tail_x_bounds:
    "\<forall>z \<in> set xs. \<bar>IEEE.valof z\<bar> \<le> a"
    using all_x_bounds by simp
  show ?case
  proof (cases ws)
    case Nil
    then show ?thesis using Cons.prems by simp
  next
    case (Cons w ws')
    have tail_lengths: "length xs = length ws'"
      using Cons.prems unfolding Cons by simp
    have tail_w_bounds: "\<forall>z \<in> set ws'. \<bar>IEEE.valof z\<bar> \<le> b"
      using all_w_bounds by (simp add: Cons)
    have tail:
      "\<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws')\<bar> \<le>
        real (length xs) * (a * b)"
      by (rule Cons.IH[OF tail_lengths tail_x_bounds tail_w_bounds])
    have w_bound: "\<bar>IEEE.valof w\<bar> \<le> b"
      using all_w_bounds by (simp add: Cons)
    have product: "\<bar>IEEE.valof x * IEEE.valof w\<bar> \<le> a * b"
      using x_bound w_bound by (simp add: abs_mult mult_mono)
    have triangle:
      "\<bar>IEEE.valof x * IEEE.valof w +
          dot_product (map IEEE.valof xs) (map IEEE.valof ws')\<bar> \<le>
        a * b + real (length xs) * (a * b)"
      using abs_triangle_ineq[of "IEEE.valof x * IEEE.valof w"
        "dot_product (map IEEE.valof xs) (map IEEE.valof ws')"]
        product tail by linarith
    show ?thesis
      using triangle by (simp add: Cons dot_product_def algebra_simps)
  qed
qed

lemma ieee_fma_dot_tail_certificate:
  fixes xs ws :: "('e::len, 'f::len) IEEE.float vector"
  assumes lengths: "length xs = length ws"
    and length_bound: "length xs \<le> 64"
    and x_finite: "\<forall>x \<in> set xs. IEEE.is_finite x"
    and w_finite: "\<forall>w \<in> set ws. IEEE.is_finite w"
    and x_small: "\<forall>x \<in> set xs. \<bar>IEEE.valof x\<bar> < 1"
    and w_small: "\<forall>w \<in> set ws. \<bar>IEEE.valof w\<bar> < 1"
    and threshold_bound:
      "2 * real (length xs) + 1 <
        IEEE.threshold TYPE(('e, 'f) IEEE.float)"
  shows "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(('e, 'f) IEEE.float)) 1 xs ws
      (ieee_fma_dot_tail_witnesses xs ws)"
using lengths x_finite w_finite x_small w_small length_bound threshold_bound
proof (induction xs arbitrary: ws)
  case Nil
  then show ?case by (cases ws) (simp_all add: ieee_fma_dot_tail_witnesses.simps)
next
  case (Cons x xs)
  have all_x_finite: "\<forall>z \<in> set (x # xs). IEEE.is_finite z"
    using Cons.prems(2) by assumption
  have all_w_finite: "\<forall>z \<in> set ws. IEEE.is_finite z"
    using Cons.prems(3) by assumption
  have all_x_small: "\<forall>z \<in> set (x # xs). \<bar>IEEE.valof z\<bar> < 1"
    using Cons.prems(4) by assumption
  have all_w_small: "\<forall>z \<in> set ws. \<bar>IEEE.valof z\<bar> < 1"
    using Cons.prems(5) by assumption
  have all_length_bound: "length (x # xs) \<le> 64"
    using Cons.prems(6) by assumption
  have all_threshold_bound:
      "2 * real (length (x # xs)) + 1 <
        IEEE.threshold TYPE(('e, 'f) IEEE.float)"
    using Cons.prems(7) by assumption
  show ?case
  proof (cases ws)
    case Nil
    then show ?thesis using Cons.prems
      by (simp_all add: ieee_fma_dot_tail_witnesses.simps)
  next
    case (Cons w ws')
    have tail_lengths: "length xs = length ws'"
      using Cons.prems unfolding Cons by simp
    have tail_x_finite: "\<forall>z \<in> set xs. IEEE.is_finite z"
      using all_x_finite by simp
    have tail_w_finite: "\<forall>z \<in> set ws'. IEEE.is_finite z"
      using all_w_finite by (simp add: Cons)
    have tail_x_small: "\<forall>z \<in> set xs. \<bar>IEEE.valof z\<bar> < 1"
      using all_x_small by simp
    have tail_w_small: "\<forall>z \<in> set ws'. \<bar>IEEE.valof z\<bar> < 1"
      using all_w_small by (simp add: Cons)
    have tail_length_bound: "length xs \<le> 64"
      using all_length_bound by simp
    have tail_threshold_bound:
        "2 * real (length xs) + 1 <
          IEEE.threshold TYPE(('e, 'f) IEEE.float)"
      using all_threshold_bound by (simp add: Cons algebra_simps)
    have tail_certificate:
        "ieee_fma_dot_certificate
          (IEEE.threshold TYPE(('e, 'f) IEEE.float)) 1 xs ws'
          (ieee_fma_dot_tail_witnesses xs ws')"
      by (rule Cons.IH[OF tail_lengths tail_x_finite tail_w_finite
          tail_x_small tail_w_small tail_length_bound tail_threshold_bound])
    have tail_safe:
        "ieee_fma_dot_safe
          (IEEE.threshold TYPE(('e, 'f) IEEE.float)) 1 xs ws'"
      by (rule ieee_fma_dot_certificate_imp_safe[OF tail_certificate])
    have tail_finite:
        "IEEE.is_finite (ieee_fma_dot xs ws')"
      by (rule ieee_fma_dot_finite[OF tail_safe])
    have tail_error:
        "\<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws') -
            IEEE.valof (ieee_fma_dot xs ws')\<bar> \<le>
          real (length xs)"
      using ieee_fma_dot_error[where epsilon=1, OF _ tail_safe]
        by simp
    have tail_dot_bound:
        "\<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws')\<bar> \<le>
          real (length xs)"
    proof -
      have tail_x_le: "\<forall>z \<in> set xs. \<bar>IEEE.valof z\<bar> \<le> (1 :: real)"
        using tail_x_small by (auto intro: less_imp_le)
      have tail_w_le: "\<forall>z \<in> set ws'. \<bar>IEEE.valof z\<bar> \<le> (1 :: real)"
        using tail_w_small by (auto intro: less_imp_le)
      have tail_dot_bound':
          "\<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws')\<bar> \<le>
            real (length xs) * (1 * 1)"
        by (rule ieee_fma_dot_abs_bound
          [where a=1 and b=1, OF tail_lengths tail_x_le tail_w_le])
      show ?thesis using tail_dot_bound' by simp
    qed
    have tail_value_bound:
        "\<bar>IEEE.valof (ieee_fma_dot xs ws')\<bar> \<le>
          2 * real (length xs)"
      using abs_triangle_ineq[of
        "dot_product (map IEEE.valof xs) (map IEEE.valof ws') -
          IEEE.valof (ieee_fma_dot xs ws')"
        "dot_product (map IEEE.valof xs) (map IEEE.valof ws')"]
        tail_error tail_dot_bound by linarith
    have x_finite_head: "IEEE.is_finite x"
      using all_x_finite by simp
    have w_finite_head: "IEEE.is_finite w"
      using all_w_finite by (simp add: Cons)
    have x_small_head: "\<bar>IEEE.valof x\<bar> < 1"
      using all_x_small by simp
    have w_small_head: "\<bar>IEEE.valof w\<bar> < 1"
      using all_w_small by (simp add: Cons)
    have product_small:
        "\<bar>IEEE.valof x * IEEE.valof w\<bar> < 1"
    proof -
      have x_nonnegative: "0 \<le> \<bar>IEEE.valof x\<bar>" by simp
      have w_nonnegative: "0 \<le> \<bar>IEEE.valof w\<bar>" by simp
      have product:
          "\<bar>IEEE.valof x\<bar> * \<bar>IEEE.valof w\<bar> < 1 * 1"
        by (rule mult_strict_mono'[OF x_small_head w_small_head
          x_nonnegative w_nonnegative])
      show ?thesis using product by (simp add: abs_mult)
    qed
    have exact_range:
        "\<bar>ieee_fma_exact x w (ieee_fma_dot xs ws')\<bar> <
          IEEE.threshold TYPE(('e, 'f) IEEE.float)"
    proof -
      have triangle:
          "\<bar>IEEE.valof x * IEEE.valof w +
              IEEE.valof (ieee_fma_dot xs ws')\<bar> <
            1 + 2 * real (length xs)"
        using abs_triangle_ineq[of "IEEE.valof x * IEEE.valof w"
          "IEEE.valof (ieee_fma_dot xs ws')"]
          product_small tail_value_bound by linarith
      show ?thesis
        unfolding ieee_fma_exact_def
        using triangle all_threshold_bound by (simp add: Cons algebra_simps)
    qed
    have witness:
        "ieee_round_witness 1
          (ieee_fma_exact x w (ieee_fma_dot xs ws'))
          (ieee_fma_dot xs ws')"
      unfolding ieee_round_witness_def
    using tail_finite product_small
    by (simp add: ieee_fma_exact_def abs_minus_commute)
    have step:
        "ieee_fma_step_certificate
          (IEEE.threshold TYPE(('e, 'f) IEEE.float)) 1 x w
          (ieee_fma_dot xs ws') (ieee_fma_dot xs ws')"
      unfolding ieee_fma_step_certificate_def
      using x_finite_head w_finite_head tail_finite exact_range witness by simp
    show ?thesis
      using tail_certificate step
      by (simp add: ieee_fma_dot_tail_witnesses.simps
          ieee_fma_dot_certificate.simps Cons)
  qed
qed

end
