theory Concrete_IEEE_Certificate
  imports Two_Layer_GQA_Checkpoint IEEE_754_Projection
begin

section \<open>Concrete binary32 projection certificate\<close>

type_synonym concrete_binary32 = "(8, 23) IEEE.float"

definition concrete_vocabulary_weights :: "concrete_binary32 matrix" where
  "concrete_vocabulary_weights = [[1, 0], [0, 0], [0, 0], [0, 0]]"

definition concrete_hidden :: "concrete_binary32 vector" where
  "concrete_hidden = [1, 0, 0, 0]"

definition concrete_certificates :: "concrete_binary32 matrix" where
  "concrete_certificates = [[1, 0, 0, 0], [0, 0, 0, 0]]"

lemma concrete_one_finite:
  "IEEE.is_finite (1 :: concrete_binary32)"
proof -
  have exponent:
    "IEEE.exponent (1 :: concrete_binary32) = 127"
    by transfer (simp add: IEEE.one_float_def)
  have fraction:
    "IEEE.fraction (1 :: concrete_binary32) = 0"
    by transfer (simp add: IEEE.one_float_def)
  show ?thesis
    unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
    using exponent fraction
    by (simp add: emax_eq)
qed

lemma concrete_vocabulary_shape:
  "matrix_shape 4 2 concrete_vocabulary_weights"
  by (simp add: concrete_vocabulary_weights_def matrix_shape_def)

lemma concrete_hidden_shape:
  "vector_shape 4 concrete_hidden"
  by (simp add: concrete_hidden_def vector_shape_def)

lemma concrete_zero_fma:
  "IEEE.fmul_add IEEE.RNE
      (0 :: concrete_binary32) 0 0 = 0"
  by (simp add: IEEE.fmul_add_def IEEE.zerosign_def float_defs)

lemma concrete_zero_dot:
  "ieee_fma_dot ([0, 0, 0] :: concrete_binary32 vector) [0] = 0"
  by (simp add: concrete_zero_fma)

lemma concrete_zero_dot_3:
  "ieee_fma_dot ([0, 0, 0] :: concrete_binary32 vector)
      [0, 0, 0] = 0"
  by (simp add: ieee_fma_dot.simps concrete_zero_fma)

lemma concrete_zero_dot_2:
  "ieee_fma_dot ([0, 0] :: concrete_binary32 vector)
      [0, 0] = 0"
  by (simp add: ieee_fma_dot.simps concrete_zero_fma)

lemma concrete_zero_dot_1:
  "ieee_fma_dot ([0] :: concrete_binary32 vector)
      [0] = 0"
  by (simp add: ieee_fma_dot.simps concrete_zero_fma)

lemma concrete_empty_dot:
  "ieee_fma_dot ([] :: concrete_binary32 vector)
      ([] :: concrete_binary32 vector) = 0"
  by simp

lemma concrete_zero_finite:
  "IEEE.is_finite (0 :: concrete_binary32)"
  by (simp add: IEEE.is_finite_def)

lemma concrete_one_val:
  "IEEE.valof (1 :: concrete_binary32) = 1"
proof -
  have exponent:
    "IEEE.exponent (1 :: concrete_binary32) = 127"
    by transfer (simp add: IEEE.one_float_def)
  have fraction:
    "IEEE.fraction (1 :: concrete_binary32) = 0"
    by transfer (simp add: IEEE.one_float_def)
  have sign:
    "IEEE.sign (1 :: concrete_binary32) = 0"
    by transfer (simp add: IEEE.one_float_def)
  show ?thesis
    using exponent fraction sign
    by (simp add: valof_eq IEEE.bias_def)
qed

lemma concrete_zero_val:
  "IEEE.valof (0 :: concrete_binary32) = 0"
  by simp

lemma concrete_fma_zero_finite:
  "IEEE.is_finite
    (IEEE.fmul_add IEEE.RNE
      (0 :: concrete_binary32) 0 0)"
  using concrete_zero_fma concrete_zero_finite by simp

lemma concrete_fma_zero_val:
  "IEEE.valof
    (IEEE.fmul_add IEEE.RNE
      (0 :: concrete_binary32) 0 0) = 0"
  using concrete_zero_fma by simp

lemma concrete_threshold_gt_one:
  "1 < IEEE.threshold TYPE(concrete_binary32)"
  using float_val_lt_threshold[where a="(1 :: concrete_binary32)"]
    concrete_one_finite
  using concrete_one_val by simp

lemma concrete_zero_step:
  "ieee_fma_step_certificate
    (IEEE.threshold TYPE(concrete_binary32)) 1
    (0 :: concrete_binary32) 0 0 0"
proof -
  show ?thesis
    unfolding ieee_fma_step_certificate_def ieee_round_witness_def
      ieee_fma_exact_def
    using concrete_zero_finite concrete_zero_val concrete_threshold_gt_one
    by simp
qed

lemma concrete_one_step:
  "ieee_fma_step_certificate
    (IEEE.threshold TYPE(concrete_binary32)) 1
    (1 :: concrete_binary32) 1 0 1"
proof -
  show ?thesis
    unfolding ieee_fma_step_certificate_def ieee_round_witness_def
      ieee_fma_exact_def
    using concrete_one_finite concrete_zero_finite concrete_one_val
      concrete_zero_val concrete_threshold_gt_one
    by simp
qed

lemma concrete_zero_left_zero_step:
  "ieee_fma_step_certificate
    (IEEE.threshold TYPE(concrete_binary32)) 1
    (1 :: concrete_binary32) 0 0 0"
proof -
  show ?thesis
    unfolding ieee_fma_step_certificate_def ieee_round_witness_def
      ieee_fma_exact_def
    using concrete_one_finite concrete_zero_finite concrete_one_val
      concrete_zero_val concrete_threshold_gt_one
    by simp
qed

lemma concrete_projection_certificate:
  "ieee_projection_certificate
    (IEEE.threshold TYPE(concrete_binary32)) 1 2
    concrete_vocabulary_weights concrete_hidden concrete_certificates"
proof -
  have cert0:
    "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(concrete_binary32)) 1
      ([1, 0, 0, 0] :: concrete_binary32 vector)
      ([1, 0, 0, 0] :: concrete_binary32 vector)
      ([1, 0, 0, 0] :: concrete_binary32 vector)"
  proof -
    show ?thesis
      by (simp del: ieee_fma_dot.simps add: ieee_fma_dot_certificate.simps
          concrete_zero_dot_3 concrete_zero_dot_2 concrete_zero_dot_1
          concrete_empty_dot concrete_zero_step concrete_one_step)
  qed
  have cert1:
    "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(concrete_binary32)) 1
      ([1, 0, 0, 0] :: concrete_binary32 vector)
      ([0, 0, 0, 0] :: concrete_binary32 vector)
      ([0, 0, 0, 0] :: concrete_binary32 vector)"
  proof -
    show ?thesis
      by (simp del: ieee_fma_dot.simps add: ieee_fma_dot_certificate.simps
          concrete_zero_dot_3 concrete_zero_dot_2 concrete_zero_dot_1
          concrete_empty_dot concrete_zero_step concrete_zero_left_zero_step)
  qed
  show ?thesis
    unfolding ieee_projection_certificate_def
  proof (rule conjI)
    show "length concrete_certificates = 2"
      by (simp add: concrete_certificates_def)
    show "\<forall>i<2. ieee_fma_dot_certificate
        (IEEE.threshold TYPE(concrete_binary32)) 1
        concrete_hidden (matrix_columns 2 concrete_vocabulary_weights ! i)
        (concrete_certificates ! i)"
    proof (intro allI impI)
      fix i :: nat
      assume i_lt: "i < 2"
      have i_cases: "i = 0 \<or> i = 1"
        using i_lt by arith
      from i_cases
      show "ieee_fma_dot_certificate
          (IEEE.threshold TYPE(concrete_binary32)) 1
          concrete_hidden (matrix_columns 2 concrete_vocabulary_weights ! i)
          (concrete_certificates ! i)"
      proof (elim disjE)
        assume i0: "i = 0"
        show ?thesis
          using i0 cert0
          by (simp add: concrete_vocabulary_weights_def
              concrete_hidden_def concrete_certificates_def matrix_columns_def)
      next
        assume i1: "i = 1"
        show ?thesis
          using i1 cert1
          by (simp add: concrete_vocabulary_weights_def
              concrete_hidden_def concrete_certificates_def matrix_columns_def)
      qed
    qed
  qed
qed

theorem concrete_projection_error:
  "vector_error_bound (4 :: real)
    (linear_project 2 (ieee_decode_matrix concrete_vocabulary_weights)
      (ieee_decode_vector concrete_hidden))
    (ieee_decode_vector
      (ieee_fma_linear_project 2 concrete_vocabulary_weights
        concrete_hidden))"
proof -
  have epsilon: "0 \<le> (1 :: real)"
    by simp
  have bound:
    "vector_error_bound (real 4 * (1 :: real))
      (linear_project 2 (ieee_decode_matrix concrete_vocabulary_weights)
        (ieee_decode_vector concrete_hidden))
      (ieee_decode_vector
        (ieee_fma_linear_project 2 concrete_vocabulary_weights
          concrete_hidden))"
    by (rule ieee_fma_projection_error_from_certificate
      [OF epsilon concrete_vocabulary_shape concrete_hidden_shape
        concrete_projection_certificate])
  then show ?thesis by simp
qed

end
