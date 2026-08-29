theory IEEE_754_Projection
  imports
    Dyadic_Finite_Precision
    "IEEE_Floating_Point.IEEE_Properties"
begin

section \<open>IEEE-754 Fused Projection Refinement\<close>

text \<open>
  This theory connects the decoder's real-valued projection semantics to the
  published AFP model of IEEE-754 arithmetic.  The model includes bounded
  exponent and fraction fields, normal and subnormal numbers, signed zeros,
  infinities, NaNs, overflow thresholds, rounding modes, and fused
  multiply-add.

  The AFP definition of round-nearest-ties-to-even currently records a caveat
  about its tie preference.  The metric closest-value theorem used below is
  independent of that preference: all results therefore certify nearest-value
  error for the operation denoted by @{term IEEE.RNE}, but do not claim that
  the unresolved exact halfway selection has been repaired here.
\<close>

type_synonym ieee_binary32 = "(8, 23) IEEE.float"
type_synonym ieee_binary64 = "(11, 52) IEEE.float"

definition ieee_fma_exact ::
  "('e::len, 'f::len) IEEE.float \<Rightarrow> ('e, 'f) IEEE.float \<Rightarrow>
   ('e, 'f) IEEE.float \<Rightarrow> real" where
  "ieee_fma_exact x y z = IEEE.valof x * IEEE.valof y + IEEE.valof z"

definition ieee_round_witness ::
  "real \<Rightarrow> real \<Rightarrow> ('e::len, 'f::len) IEEE.float \<Rightarrow> bool" where
  "ieee_round_witness epsilon r a \<longleftrightarrow>
    IEEE.is_finite a \<and> \<bar>IEEE.valof a - r\<bar> \<le> epsilon"

definition ieee_fma_step_safe ::
  "real \<Rightarrow> real \<Rightarrow> ('e::len, 'f::len) IEEE.float \<Rightarrow>
   ('e, 'f) IEEE.float \<Rightarrow> ('e, 'f) IEEE.float \<Rightarrow> bool" where
  "ieee_fma_step_safe format_threshold epsilon
      (x :: ('e, 'f) IEEE.float) y z \<longleftrightarrow>
    IEEE.is_finite x \<and> IEEE.is_finite y \<and> IEEE.is_finite z \<and>
    \<bar>ieee_fma_exact x y z\<bar> < format_threshold \<and>
    (\<exists>a :: ('e, 'f) IEEE.float.
      ieee_round_witness epsilon (ieee_fma_exact x y z) a)"

lemma ieee_valof_zerosign [simp]:
  "IEEE.valof (IEEE.zerosign s a) = IEEE.valof a"
proof (cases "IEEE.is_zero a")
  case True
  have "IEEE.valof (IEEE.zerosign s a) = 0"
    by (rule IEEE_Properties.signzero_zero[OF True])
  moreover have "IEEE.valof a = 0"
    by (rule IEEE_Properties.val_zero[OF True])
  ultimately show ?thesis by simp
next
  case False
  then show ?thesis by (simp add: IEEE.zerosign_def)
qed

lemma ieee_fma_finite_reduction:
  fixes x y z :: "('e::len, 'f::len) IEEE.float"
  assumes finite: "IEEE.is_finite x" "IEEE.is_finite y" "IEEE.is_finite z"
  shows "IEEE.fmul_add IEEE.RNE x y z =
    (let r = ieee_fma_exact x y z;
         signP = (if IEEE.sign x = IEEE.sign y then 0 else 1)
     in if r = 0 then
          (if IEEE.valof x * IEEE.valof y = 0 \<and> IEEE.valof z = 0 \<and>
              signP = IEEE.sign z
           then IEEE.zerosign signP 0 else 0)
        else IEEE.zerosign (if r < 0 then 1 else 0) (IEEE.round IEEE.RNE r))"
  using finite
  by (simp add: IEEE.fmul_add_def ieee_fma_exact_def Let_def
      IEEE_Properties.finite_nan IEEE_Properties.finite_infinity)

theorem ieee_fma_finite_and_error:
  fixes x y z a :: "('e::len, 'f::len) IEEE.float"
  assumes finite: "IEEE.is_finite x" "IEEE.is_finite y" "IEEE.is_finite z"
    and range: "\<bar>ieee_fma_exact x y z\<bar> <
      IEEE.threshold TYPE(('e, 'f) IEEE.float)"
    and witness: "ieee_round_witness epsilon (ieee_fma_exact x y z) a"
  shows "IEEE.is_finite (IEEE.fmul_add IEEE.RNE x y z)"
    and "\<bar>IEEE.valof (IEEE.fmul_add IEEE.RNE x y z) -
      ieee_fma_exact x y z\<bar> \<le> epsilon"
proof -
  let ?r = "ieee_fma_exact x y z"
  have a_finite: "IEEE.is_finite a"
    and a_close: "\<bar>IEEE.valof a - ?r\<bar> \<le> epsilon"
    using witness by (simp_all add: ieee_round_witness_def)
  have reduced: "IEEE.fmul_add IEEE.RNE x y z =
    (let signP = (if IEEE.sign x = IEEE.sign y then 0 else 1)
     in if ?r = 0 then
          (if IEEE.valof x * IEEE.valof y = 0 \<and> IEEE.valof z = 0 \<and>
              signP = IEEE.sign z
           then IEEE.zerosign signP 0 else 0)
        else IEEE.zerosign (if ?r < 0 then 1 else 0)
          (IEEE.round IEEE.RNE ?r))"
    using ieee_fma_finite_reduction[OF finite]
    by (simp add: Let_def)
  show "IEEE.is_finite (IEEE.fmul_add IEEE.RNE x y z)"
  proof (cases "?r = 0")
    case True
    have zero_finite: "IEEE.is_finite (0 :: ('e, 'f) IEEE.float)"
      by (simp add: IEEE.is_finite_def)
    then show ?thesis using reduced True by simp
  next
    case False
    have base: "IEEE.is_finite
      (IEEE.zerosign 0 (IEEE.round IEEE.RNE ?r :: ('e, 'f) IEEE.float))"
      by (rule IEEE_Properties.defloat_float_zerosign_round_finite[OF range])
    then have "IEEE.is_finite
      (IEEE.zerosign (if ?r < 0 then 1 else 0)
        (IEEE.round IEEE.RNE ?r :: ('e, 'f) IEEE.float))"
      by simp
    then show ?thesis using reduced False by simp
  qed
  show "\<bar>IEEE.valof (IEEE.fmul_add IEEE.RNE x y z) - ?r\<bar> \<le> epsilon"
  proof (cases "?r = 0")
    case True
    have "0 \<le> epsilon" using a_close True by simp
    then show ?thesis using reduced True
      by (simp add: IEEE_Properties.valof_zero)
  next
    case False
    have closest:
      "\<bar>IEEE.valof (IEEE.round IEEE.RNE ?r :: ('e, 'f) IEEE.float) - ?r\<bar>
        \<le> \<bar>IEEE.valof a - ?r\<bar>"
      by (rule IEEE_Properties.bound_at_worst_lemma[OF range a_finite])
    show ?thesis
      using reduced False closest a_close by simp
  qed
qed

corollary ieee_fma_step_safe_finite:
  fixes x y z :: "('e::len, 'f::len) IEEE.float"
  assumes "ieee_fma_step_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
    epsilon x y z"
  shows "IEEE.is_finite (IEEE.fmul_add IEEE.RNE x y z)"
  using assms ieee_fma_finite_and_error(1)
  by (auto simp: ieee_fma_step_safe_def)

corollary ieee_fma_step_safe_error:
  fixes x y z :: "('e::len, 'f::len) IEEE.float"
  assumes "ieee_fma_step_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
    epsilon x y z"
  shows "\<bar>IEEE.valof (IEEE.fmul_add IEEE.RNE x y z) -
    ieee_fma_exact x y z\<bar> \<le> epsilon"
  using assms ieee_fma_finite_and_error(2)
  by (auto simp: ieee_fma_step_safe_def)

theorem ieee_fma_step_safe_guarantees:
  fixes x y z :: "('e::len, 'f::len) IEEE.float"
  assumes safe:
    "ieee_fma_step_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
      epsilon x y z"
  shows "IEEE.is_finite (IEEE.fmul_add IEEE.RNE x y z) \<and>
    \<bar>IEEE.valof (IEEE.fmul_add IEEE.RNE x y z) -
      ieee_fma_exact x y z\<bar> \<le> epsilon"
  using ieee_fma_step_safe_finite[OF safe]
    ieee_fma_step_safe_error[OF safe]
  by blast

fun ieee_fma_dot ::
  "('e::len, 'f::len) IEEE.float vector \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow> ('e, 'f) IEEE.float" where
  "ieee_fma_dot [] ys = 0"
| "ieee_fma_dot (x # xs) [] = 0"
| "ieee_fma_dot (x # xs) (w # ws) =
    IEEE.fmul_add IEEE.RNE x w (ieee_fma_dot xs ws)"

fun ieee_fma_dot_safe ::
  "real \<Rightarrow> real \<Rightarrow> ('e::len, 'f::len) IEEE.float vector \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow> bool" where
  "ieee_fma_dot_safe format_threshold epsilon [] ys = True"
| "ieee_fma_dot_safe format_threshold epsilon (x # xs) [] = True"
| "ieee_fma_dot_safe format_threshold epsilon (x # xs) (w # ws) =
    (ieee_fma_dot_safe format_threshold epsilon xs ws \<and>
      ieee_fma_step_safe format_threshold epsilon x w
        (ieee_fma_dot xs ws))"

definition ieee_fma_step_certificate ::
  "real \<Rightarrow> real \<Rightarrow> ('e::len, 'f::len) IEEE.float \<Rightarrow>
   ('e, 'f) IEEE.float \<Rightarrow> ('e, 'f) IEEE.float \<Rightarrow>
   ('e, 'f) IEEE.float \<Rightarrow> bool" where
  "ieee_fma_step_certificate format_threshold epsilon x y z a \<longleftrightarrow>
    IEEE.is_finite x \<and> IEEE.is_finite y \<and> IEEE.is_finite z \<and>
    \<bar>ieee_fma_exact x y z\<bar> < format_threshold \<and>
    ieee_round_witness epsilon (ieee_fma_exact x y z) a"

fun ieee_fma_dot_certificate ::
  "real \<Rightarrow> real \<Rightarrow> ('e::len, 'f::len) IEEE.float vector \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow> ('e, 'f) IEEE.float vector \<Rightarrow> bool" where
  "ieee_fma_dot_certificate format_threshold epsilon [] ys witnesses =
    (witnesses = [])"
| "ieee_fma_dot_certificate format_threshold epsilon (x # xs) [] witnesses =
    (witnesses = [])"
| "ieee_fma_dot_certificate format_threshold epsilon (x # xs) (w # ws) [] =
    False"
| "ieee_fma_dot_certificate format_threshold epsilon (x # xs) (w # ws)
      (a # witnesses) =
    (ieee_fma_dot_certificate format_threshold epsilon xs ws witnesses \<and>
      ieee_fma_step_certificate format_threshold epsilon x w
        (ieee_fma_dot xs ws) a)"

lemma ieee_fma_step_certificate_imp_safe:
  assumes "ieee_fma_step_certificate format_threshold epsilon x y z a"
  shows "ieee_fma_step_safe format_threshold epsilon x y z"
  using assms
  by (auto simp: ieee_fma_step_certificate_def ieee_fma_step_safe_def)

theorem ieee_fma_dot_certificate_imp_safe:
  assumes certificate:
    "ieee_fma_dot_certificate format_threshold epsilon xs ws witnesses"
  shows "ieee_fma_dot_safe format_threshold epsilon xs ws"
  using certificate
proof (induction xs arbitrary: ws witnesses)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis by simp
  next
    case (Cons w ws')
    then obtain a witnesses' where witnesses: "witnesses = a # witnesses'"
      using Cons.prems by (cases witnesses) auto
    have tail:
      "ieee_fma_dot_certificate format_threshold epsilon xs ws' witnesses'"
      using Cons.prems unfolding Cons witnesses by simp
    have step:
      "ieee_fma_step_certificate format_threshold epsilon x w
        (ieee_fma_dot xs ws') a"
      using Cons.prems unfolding Cons witnesses by simp
    show ?thesis
      unfolding Cons
      using Cons.IH[OF tail] ieee_fma_step_certificate_imp_safe[OF step]
      by simp
  qed
qed

theorem ieee_fma_dot_finite:
  fixes xs ws :: "('e::len, 'f::len) IEEE.float vector"
  assumes safe:
    "ieee_fma_dot_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
      epsilon xs ws"
  shows "IEEE.is_finite (ieee_fma_dot xs ws)"
  using safe
proof (induction xs arbitrary: ws)
  case Nil
  then show ?case by (simp add: IEEE.is_finite_def)
next
  case (Cons x xs)
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis by (simp add: IEEE.is_finite_def)
  next
    case (Cons w ws')
    have step:
      "ieee_fma_step_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon x w (ieee_fma_dot xs ws')"
      using Cons.prems unfolding Cons by simp
    have result:
      "IEEE.is_finite (IEEE.fmul_add IEEE.RNE x w (ieee_fma_dot xs ws'))"
      by (rule ieee_fma_step_safe_finite[OF step])
    show ?thesis using result unfolding Cons by simp
  qed
qed

theorem ieee_fma_dot_error:
  fixes xs ws :: "('e::len, 'f::len) IEEE.float vector"
  assumes epsilon: "0 \<le> epsilon"
    and safe:
      "ieee_fma_dot_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon xs ws"
  shows "\<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws) -
      IEEE.valof (ieee_fma_dot xs ws)\<bar> \<le>
    real (min (length xs) (length ws)) * epsilon"
  using safe
proof (induction xs arbitrary: ws)
  case Nil
  then show ?case
    using epsilon by (simp add: dot_product_def IEEE_Properties.valof_zero)
next
  case (Cons x xs)
  show ?case
  proof (cases ws)
    case Nil
    then show ?thesis
      using epsilon by (simp add: dot_product_def IEEE_Properties.valof_zero)
  next
    case (Cons w ws')
    have tail_safe:
      "ieee_fma_dot_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon xs ws'"
      using Cons.prems unfolding Cons by simp
    have tail:
      "\<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws') -
          IEEE.valof (ieee_fma_dot xs ws')\<bar> \<le>
        real (min (length xs) (length ws')) * epsilon"
      by (rule Cons.IH[OF tail_safe])
    have step_safe:
      "ieee_fma_step_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon x w (ieee_fma_dot xs ws')"
      using Cons.prems unfolding Cons by simp
    have local:
      "\<bar>(IEEE.valof x * IEEE.valof w + IEEE.valof (ieee_fma_dot xs ws')) -
          IEEE.valof (IEEE.fmul_add IEEE.RNE x w (ieee_fma_dot xs ws'))\<bar>
        \<le> epsilon"
      using ieee_fma_step_safe_error[OF step_safe]
      by (simp add: ieee_fma_exact_def abs_minus_commute)
    have decomposition:
      "dot_product (map IEEE.valof (x # xs)) (map IEEE.valof (w # ws')) -
          IEEE.valof (ieee_fma_dot (x # xs) (w # ws')) =
        (dot_product (map IEEE.valof xs) (map IEEE.valof ws') -
          IEEE.valof (ieee_fma_dot xs ws')) +
        ((IEEE.valof x * IEEE.valof w + IEEE.valof (ieee_fma_dot xs ws')) -
          IEEE.valof (IEEE.fmul_add IEEE.RNE x w (ieee_fma_dot xs ws')))"
      by (simp add: dot_product_def algebra_simps)
    have "\<bar>dot_product (map IEEE.valof (x # xs)) (map IEEE.valof (w # ws')) -
        IEEE.valof (ieee_fma_dot (x # xs) (w # ws'))\<bar> \<le>
        \<bar>dot_product (map IEEE.valof xs) (map IEEE.valof ws') -
          IEEE.valof (ieee_fma_dot xs ws')\<bar> +
        \<bar>(IEEE.valof x * IEEE.valof w + IEEE.valof (ieee_fma_dot xs ws')) -
          IEEE.valof (IEEE.fmul_add IEEE.RNE x w (ieee_fma_dot xs ws'))\<bar>"
      unfolding decomposition by (rule abs_triangle_ineq)
    also have "... \<le>
        real (min (length xs) (length ws')) * epsilon + epsilon"
      using tail local by simp
    also have "... = real (min (length (x # xs)) (length (w # ws'))) * epsilon"
      by (simp add: algebra_simps)
    finally show ?thesis unfolding Cons .
  qed
qed

definition ieee_decode_vector ::
  "('e::len, 'f::len) IEEE.float vector \<Rightarrow> real vector" where
  "ieee_decode_vector xs = map IEEE.valof xs"

definition ieee_decode_matrix ::
  "('e::len, 'f::len) IEEE.float matrix \<Rightarrow> real matrix" where
  "ieee_decode_matrix W = map ieee_decode_vector W"

definition ieee_fma_linear_project ::
  "nat \<Rightarrow> ('e::len, 'f::len) IEEE.float matrix \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow> ('e, 'f) IEEE.float vector" where
  "ieee_fma_linear_project out_dim W x =
    map (ieee_fma_dot x) (matrix_columns out_dim W)"

definition ieee_reference_project ::
  "nat \<Rightarrow> ('e::len, 'f::len) IEEE.float matrix \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow> real vector" where
  "ieee_reference_project out_dim W x =
    map (\<lambda>w. dot_product (ieee_decode_vector x) (ieee_decode_vector w))
      (matrix_columns out_dim W)"

definition ieee_projection_safe ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow>
   ('e::len, 'f::len) IEEE.float matrix \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow> bool" where
  "ieee_projection_safe format_threshold epsilon out_dim W x \<longleftrightarrow>
    (\<forall>w \<in> set (matrix_columns out_dim W).
      ieee_fma_dot_safe format_threshold epsilon x w)"

definition ieee_projection_certificate ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow>
   ('e::len, 'f::len) IEEE.float matrix \<Rightarrow>
   ('e, 'f) IEEE.float vector \<Rightarrow> ('e, 'f) IEEE.float matrix \<Rightarrow> bool"
  where
  "ieee_projection_certificate format_threshold epsilon out_dim W x
      certificates \<longleftrightarrow>
    length certificates = out_dim \<and>
    (\<forall>i < out_dim.
      ieee_fma_dot_certificate format_threshold epsilon x
        (matrix_columns out_dim W ! i) (certificates ! i))"

theorem ieee_projection_certificate_imp_safe:
  assumes certificate:
    "ieee_projection_certificate format_threshold epsilon out_dim W x
      certificates"
  shows "ieee_projection_safe format_threshold epsilon out_dim W x"
proof (unfold ieee_projection_safe_def, intro ballI)
  fix w
  assume member: "w \<in> set (matrix_columns out_dim W)"
  then obtain i where i:
      "i < length (matrix_columns out_dim W)"
      "w = matrix_columns out_dim W ! i"
    by (metis in_set_conv_nth)
  have i_out: "i < out_dim"
    using i(1) by (simp add: matrix_columns_def)
  have certified:
    "ieee_fma_dot_certificate format_threshold epsilon x
      (matrix_columns out_dim W ! i) (certificates ! i)"
    using certificate i_out by (auto simp: ieee_projection_certificate_def)
  have "ieee_fma_dot_safe format_threshold epsilon x
    (matrix_columns out_dim W ! i)"
    by (rule ieee_fma_dot_certificate_imp_safe[OF certified])
  then show "ieee_fma_dot_safe format_threshold epsilon x w"
    using i(2) by simp
qed

lemma ieee_decode_vector_shape:
  assumes "vector_shape n xs"
  shows "vector_shape n (ieee_decode_vector xs)"
  using assms by (simp add: vector_shape_def ieee_decode_vector_def)

lemma ieee_decode_matrix_shape:
  assumes "matrix_shape rows cols W"
  shows "matrix_shape rows cols (ieee_decode_matrix W)"
  using assms
  by (auto simp: matrix_shape_def ieee_decode_matrix_def
      ieee_decode_vector_def)

lemma ieee_decode_matrix_columns:
  assumes matrix: "matrix_shape rows cols W"
  shows "matrix_columns cols (ieee_decode_matrix W) =
    map ieee_decode_vector (matrix_columns cols W)"
proof -
  have pointwise:
    "\<forall>j \<in> set [0..<cols].
      map ((\<lambda>row. row ! j) \<circ> ieee_decode_vector) W =
      (ieee_decode_vector \<circ> (\<lambda>j. map (\<lambda>row. row ! j) W)) j"
  proof (intro ballI)
    fix j
    assume j: "j \<in> set [0..<cols]"
    have in_range: "j < cols" using j by simp
    have rows: "\<forall>row \<in> set W. j < length row"
      using matrix in_range by (auto simp: matrix_shape_def)
    show "map ((\<lambda>row. row ! j) \<circ> ieee_decode_vector) W =
      (ieee_decode_vector \<circ> (\<lambda>j. map (\<lambda>row. row ! j) W)) j"
      using rows
      by (simp add: ieee_decode_vector_def map_map o_def)
  qed
  show ?thesis
    unfolding matrix_columns_def ieee_decode_matrix_def
    apply (simp only: map_map)
    apply (rule map_cong)
     apply simp
    using pointwise by blast
qed

lemma ieee_reference_project_eq_linear:
  assumes matrix: "matrix_shape in_dim out_dim W"
  shows "ieee_reference_project out_dim W x =
    linear_project out_dim (ieee_decode_matrix W) (ieee_decode_vector x)"
  using ieee_decode_matrix_columns[OF matrix]
  by (simp add: ieee_reference_project_def linear_project_def map_map o_def)

lemma length_ieee_fma_linear_project [simp]:
  "length (ieee_fma_linear_project out_dim W x) = out_dim"
  by (simp add: ieee_fma_linear_project_def matrix_columns_def)

lemma length_ieee_reference_project [simp]:
  "length (ieee_reference_project out_dim W x) = out_dim"
  by (simp add: ieee_reference_project_def matrix_columns_def)

theorem ieee_fma_projection_error:
  fixes W :: "('e::len, 'f::len) IEEE.float matrix"
    and x :: "('e, 'f) IEEE.float vector"
  assumes epsilon: "0 \<le> epsilon"
    and matrix: "matrix_shape in_dim out_dim W"
    and input: "vector_shape in_dim x"
    and safe:
      "ieee_projection_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon out_dim W x"
  shows "vector_error_bound (real in_dim * epsilon)
    (linear_project out_dim (ieee_decode_matrix W) (ieee_decode_vector x))
    (ieee_decode_vector (ieee_fma_linear_project out_dim W x))"
proof -
  have reference:
    "ieee_reference_project out_dim W x =
      linear_project out_dim (ieee_decode_matrix W) (ieee_decode_vector x)"
    by (rule ieee_reference_project_eq_linear[OF matrix])
  have lengths:
    "length (ieee_reference_project out_dim W x) =
      length (ieee_decode_vector (ieee_fma_linear_project out_dim W x))"
    by (simp add: ieee_decode_vector_def)
  have coordinates:
    "\<forall>i < length (ieee_reference_project out_dim W x).
      \<bar>ieee_reference_project out_dim W x ! i -
        ieee_decode_vector (ieee_fma_linear_project out_dim W x) ! i\<bar> \<le>
      real in_dim * epsilon"
  proof (intro allI impI)
    fix i
    assume i: "i < length (ieee_reference_project out_dim W x)"
    let ?columns = "matrix_columns out_dim W"
    let ?w = "?columns ! i"
    have i_out: "i < out_dim" using i by simp
    have column_member: "?w \<in> set ?columns"
      using i_out by (auto simp: matrix_columns_def)
    have column_shape: "length ?w = in_dim"
      using matrix_columns_shape[OF matrix] i_out
      by (simp add: matrix_shape_nth)
    have input_shape: "length x = in_dim"
      using input by (simp add: vector_shape_def)
    have local_safe:
      "ieee_fma_dot_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon x ?w"
      using safe column_member by (auto simp: ieee_projection_safe_def)
    have local:
      "\<bar>dot_product (ieee_decode_vector x) (ieee_decode_vector ?w) -
          IEEE.valof (ieee_fma_dot x ?w)\<bar> \<le> real in_dim * epsilon"
      using ieee_fma_dot_error[OF epsilon local_safe]
        input_shape column_shape
      by (simp add: ieee_decode_vector_def)
    show "\<bar>ieee_reference_project out_dim W x ! i -
        ieee_decode_vector (ieee_fma_linear_project out_dim W x) ! i\<bar> \<le>
      real in_dim * epsilon"
      using local i_out
      by (simp add: ieee_reference_project_def ieee_fma_linear_project_def
          ieee_decode_vector_def matrix_columns_def)
  qed
  have "vector_error_bound (real in_dim * epsilon)
    (ieee_reference_project out_dim W x)
    (ieee_decode_vector (ieee_fma_linear_project out_dim W x))"
    using lengths coordinates by (simp add: vector_error_bound_def)
  then show ?thesis using reference by simp
qed

corollary ieee_fma_projection_error_from_certificate:
  fixes W :: "('e::len, 'f::len) IEEE.float matrix"
    and x :: "('e, 'f) IEEE.float vector"
  assumes epsilon: "0 \<le> epsilon"
    and matrix: "matrix_shape in_dim out_dim W"
    and input: "vector_shape in_dim x"
    and certificate:
      "ieee_projection_certificate
        (IEEE.threshold TYPE(('e, 'f) IEEE.float)) epsilon out_dim W x
        certificates"
  shows "vector_error_bound (real in_dim * epsilon)
    (linear_project out_dim (ieee_decode_matrix W) (ieee_decode_vector x))
    (ieee_decode_vector (ieee_fma_linear_project out_dim W x))"
  by (rule ieee_fma_projection_error
      [OF epsilon matrix input
        ieee_projection_certificate_imp_safe[OF certificate]])

theorem ieee_fma_next_token_logit_error:
  fixes W :: "('e::len, 'f::len) IEEE.float matrix"
    and finite_hidden :: "('e, 'f) IEEE.float vector"
  assumes epsilon: "0 \<le> epsilon"
    and hidden_nonnegative: "0 \<le> hidden_error"
    and matrix: "matrix_shape model_dim vocabulary_size W"
    and finite_hidden_shape: "vector_shape model_dim finite_hidden"
    and safe:
      "ieee_projection_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon vocabulary_size W finite_hidden"
    and hidden:
      "vector_error_bound hidden_error exact_hidden
        (ieee_decode_vector finite_hidden)"
    and bound:
      "projection_l1_bound vocabulary_size (ieee_decode_matrix W) L"
  shows "vector_error_bound (L * hidden_error + real model_dim * epsilon)
    (next_token_logits vocabulary_size (ieee_decode_matrix W) exact_hidden)
    (ieee_decode_vector
      (ieee_fma_linear_project vocabulary_size W finite_hidden))"
proof -
  have lipschitz:
    "vector_lipschitz L (linear_project vocabulary_size (ieee_decode_matrix W))"
    by (rule linear_project_lipschitz[OF bound])
  have propagated:
    "vector_error_bound (L * hidden_error)
      (linear_project vocabulary_size (ieee_decode_matrix W) exact_hidden)
      (linear_project vocabulary_size (ieee_decode_matrix W)
        (ieee_decode_vector finite_hidden))"
    using lipschitz hidden hidden_nonnegative
    by (auto simp: vector_lipschitz_def)
  have rounded:
    "vector_error_bound (real model_dim * epsilon)
      (linear_project vocabulary_size (ieee_decode_matrix W)
        (ieee_decode_vector finite_hidden))
      (ieee_decode_vector
        (ieee_fma_linear_project vocabulary_size W finite_hidden))"
    by (rule ieee_fma_projection_error
        [OF epsilon matrix finite_hidden_shape safe])
  have combined:
    "vector_error_bound (L * hidden_error + real model_dim * epsilon)
      (linear_project vocabulary_size (ieee_decode_matrix W) exact_hidden)
      (ieee_decode_vector
        (ieee_fma_linear_project vocabulary_size W finite_hidden))"
    by (rule vector_error_bound_triangle[OF propagated rounded])
  show ?thesis
    using combined by (simp add: next_token_logits_def)
qed

theorem cached_modern_ieee_fma_next_token_logit_error:
  fixes W :: "('e::len, 'f::len) IEEE.float matrix"
    and finite_hidden :: "('e, 'f) IEEE.float vector"
  assumes valid: "valid_modern_decoder_stack layers"
    and cache:
      "modern_transformer_cache_matches layers start prefix caches"
    and epsilon: "0 \<le> epsilon"
    and hidden_nonnegative: "0 \<le> hidden_error"
    and matrix: "matrix_shape model_dim vocabulary_size W"
    and finite_hidden_shape: "vector_shape model_dim finite_hidden"
    and safe:
      "ieee_projection_safe (IEEE.threshold TYPE(('e, 'f) IEEE.float))
        epsilon vocabulary_size W finite_hidden"
    and hidden:
      "vector_error_bound hidden_error
        (fst (cached_modern_decoder_stack_step layers
          (start + length prefix) x caches))
        (ieee_decode_vector finite_hidden)"
    and bound:
      "projection_l1_bound vocabulary_size (ieee_decode_matrix W) L"
  shows "vector_error_bound (L * hidden_error + real model_dim * epsilon)
    (next_token_logits vocabulary_size (ieee_decode_matrix W)
      (last (full_modern_decoder_stack layers start (prefix @ [x]))))
    (ieee_decode_vector
      (ieee_fma_linear_project vocabulary_size W finite_hidden))"
proof -
  have exact_hidden:
    "fst (cached_modern_decoder_stack_step layers
        (start + length prefix) x caches) =
      last (full_modern_decoder_stack layers start (prefix @ [x]))"
    by (rule incremental_modern_decoder_equals_full[OF valid cache])
  have result:
    "vector_error_bound (L * hidden_error + real model_dim * epsilon)
      (next_token_logits vocabulary_size (ieee_decode_matrix W)
        (fst (cached_modern_decoder_stack_step layers
          (start + length prefix) x caches)))
      (ieee_decode_vector
        (ieee_fma_linear_project vocabulary_size W finite_hidden))"
    by (rule ieee_fma_next_token_logit_error
        [OF epsilon hidden_nonnegative matrix finite_hidden_shape safe hidden bound])
  show ?thesis using result exact_hidden by simp
qed

corollary binary32_fma_next_token_logit_error:
  fixes W :: "ieee_binary32 matrix"
    and finite_hidden :: "ieee_binary32 vector"
  assumes epsilon: "0 \<le> epsilon"
    and hidden_nonnegative: "0 \<le> hidden_error"
    and matrix: "matrix_shape model_dim vocabulary_size W"
    and finite_hidden_shape: "vector_shape model_dim finite_hidden"
    and safe:
      "ieee_projection_safe (IEEE.threshold TYPE(ieee_binary32))
        epsilon vocabulary_size W finite_hidden"
    and hidden:
      "vector_error_bound hidden_error exact_hidden
        (ieee_decode_vector finite_hidden)"
    and bound:
      "projection_l1_bound vocabulary_size (ieee_decode_matrix W) L"
  shows "vector_error_bound (L * hidden_error + real model_dim * epsilon)
    (next_token_logits vocabulary_size (ieee_decode_matrix W) exact_hidden)
    (ieee_decode_vector
      (ieee_fma_linear_project vocabulary_size W finite_hidden))"
  by (rule ieee_fma_next_token_logit_error
      [OF epsilon hidden_nonnegative matrix finite_hidden_shape safe hidden bound])

end
