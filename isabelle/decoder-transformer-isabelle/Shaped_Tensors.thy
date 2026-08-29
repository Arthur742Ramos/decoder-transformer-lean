theory Shaped_Tensors
  imports KV_Cache
begin

section \<open>Finite Shape-Safe Tensors\<close>

text \<open>
  Vectors, matrices, and rank-three tensors are represented by nested finite
  lists together with explicit shape predicates.  The operations below are
  total; their shape theorems state the conditions under which they implement
  the intended tensor operations.
\<close>

type_synonym 'a vector = "'a list"
type_synonym 'a matrix = "'a list list"
type_synonym 'a tensor3 = "'a list list list"

definition vector_shape :: "nat \<Rightarrow> 'a vector \<Rightarrow> bool" where
  "vector_shape n xs \<longleftrightarrow> length xs = n"

definition matrix_shape :: "nat \<Rightarrow> nat \<Rightarrow> 'a matrix \<Rightarrow> bool" where
  "matrix_shape rows cols M \<longleftrightarrow>
    length M = rows \<and> (\<forall>row \<in> set M. length row = cols)"

definition tensor3_shape :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tensor3 \<Rightarrow> bool" where
  "tensor3_shape d1 d2 d3 T \<longleftrightarrow>
    length T = d1 \<and> (\<forall>M \<in> set T. matrix_shape d2 d3 M)"

lemma vector_shape_length:
  "vector_shape n xs \<Longrightarrow> length xs = n"
  by (simp add: vector_shape_def)

lemma matrix_shape_length:
  "matrix_shape rows cols M \<Longrightarrow> length M = rows"
  by (simp add: matrix_shape_def)

lemma matrix_shape_row:
  assumes "matrix_shape rows cols M" "row \<in> set M"
  shows "length row = cols"
  using assms by (auto simp: matrix_shape_def)

lemma matrix_shape_nth:
  assumes "matrix_shape rows cols M" "i < rows"
  shows "length (M ! i) = cols"
  using assms by (auto simp: matrix_shape_def)

subsection \<open>Elementwise and linear operations\<close>

definition vector_add :: "'a::plus vector \<Rightarrow> 'a vector \<Rightarrow> 'a vector" where
  "vector_add xs ys = map2 (+) xs ys"

lemma vector_add_shape:
  assumes "vector_shape n xs" "vector_shape n ys"
  shows "vector_shape n (vector_add xs ys)"
  using assms by (simp add: vector_shape_def vector_add_def)

definition matrix_add :: "'a::plus matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" where
  "matrix_add A B =
    map (\<lambda>i. vector_add (A ! i) (B ! i)) [0..<min (length A) (length B)]"

lemma matrix_add_shape:
  assumes A: "matrix_shape rows cols A"
    and B: "matrix_shape rows cols B"
  shows "matrix_shape rows cols (matrix_add A B)"
proof -
  have lengths: "length A = rows" "length B = rows"
    using A B by (simp_all add: matrix_shape_def)
  have row_shape:
    "\<And>i. i < rows \<Longrightarrow> length (vector_add (A ! i) (B ! i)) = cols"
    using A B
    by (simp add: vector_add_def matrix_shape_nth)
  show ?thesis
    unfolding matrix_shape_def matrix_add_def
    using lengths row_shape by auto
qed

definition dot_product ::
  "'a::semiring_0 vector \<Rightarrow> 'a vector \<Rightarrow> 'a" where
  "dot_product xs ys = sum_list (map2 (*) xs ys)"

definition matrix_columns :: "nat \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" where
  "matrix_columns cols M = map (\<lambda>j. map (\<lambda>row. row ! j) M) [0..<cols]"

lemma matrix_columns_shape:
  assumes "matrix_shape rows cols M"
  shows "matrix_shape cols rows (matrix_columns cols M)"
  using assms by (auto simp: matrix_shape_def matrix_columns_def)

definition matrix_multiply ::
  "nat \<Rightarrow> 'a::semiring_0 matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" where
  "matrix_multiply out_cols A B =
    map (\<lambda>row. map (dot_product row) (matrix_columns out_cols B)) A"

lemma matrix_multiply_shape:
  assumes "matrix_shape rows inner A"
    and "matrix_shape inner cols B"
  shows "matrix_shape rows cols (matrix_multiply cols A B)"
  using assms
  by (auto simp: matrix_shape_def matrix_multiply_def matrix_columns_def)

definition linear_project ::
  "nat \<Rightarrow> 'a::semiring_0 matrix \<Rightarrow> 'a vector \<Rightarrow> 'a vector" where
  "linear_project out_dim W x =
    map (dot_product x) (matrix_columns out_dim W)"

lemma linear_project_shape:
  assumes "matrix_shape in_dim out_dim W" "vector_shape in_dim x"
  shows "vector_shape out_dim (linear_project out_dim W x)"
  using assms
  by (simp add: vector_shape_def linear_project_def matrix_columns_def)

definition project_sequence ::
  "nat \<Rightarrow> 'a::semiring_0 matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" where
  "project_sequence out_dim W X = map (linear_project out_dim W) X"

lemma project_sequence_shape:
  assumes X: "matrix_shape seq_len in_dim X"
    and W: "matrix_shape in_dim out_dim W"
  shows "matrix_shape seq_len out_dim (project_sequence out_dim W X)"
  using X W linear_project_shape
  by (auto simp: matrix_shape_def project_sequence_def vector_shape_def)

subsection \<open>Head splitting and concatenation\<close>

fun split_vector :: "nat \<Rightarrow> nat \<Rightarrow> 'a vector \<Rightarrow> 'a matrix" where
  "split_vector 0 head_dim xs = []"
| "split_vector (Suc heads) head_dim xs =
    take head_dim xs # split_vector heads head_dim (drop head_dim xs)"

lemma split_vector_shape:
  assumes "length xs = heads * head_dim"
  shows "matrix_shape heads head_dim (split_vector heads head_dim xs)"
  using assms
proof (induction heads arbitrary: xs)
  case 0
  then show ?case by (simp add: matrix_shape_def)
next
  case (Suc heads)
  have take_length: "length (take head_dim xs) = head_dim"
    using Suc.prems by simp
  have drop_length: "length (drop head_dim xs) = heads * head_dim"
    using Suc.prems by simp
  have tail: "matrix_shape heads head_dim
      (split_vector heads head_dim (drop head_dim xs))"
    by (rule Suc.IH[OF drop_length])
  show ?case
    using take_length tail by (auto simp: matrix_shape_def)
qed

lemma concat_split_vector:
  assumes "length xs = heads * head_dim"
  shows "concat (split_vector heads head_dim xs) = xs"
  using assms
proof (induction heads arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc heads)
  have drop_length: "length (drop head_dim xs) = heads * head_dim"
    using Suc.prems by simp
  have tail: "concat (split_vector heads head_dim (drop head_dim xs)) =
      drop head_dim xs"
    by (rule Suc.IH[OF drop_length])
  show ?case
    by (simp add: tail)
qed

lemma concat_rows_length:
  assumes "\<forall>row \<in> set M. length row = cols"
  shows "length (concat M) = length M * cols"
  using assms by (induction M) auto

lemma matrix_shape_concat_length:
  assumes "matrix_shape rows cols M"
  shows "length (concat M) = rows * cols"
  using assms concat_rows_length
  by (auto simp: matrix_shape_def)

definition split_sequence_heads ::
  "nat \<Rightarrow> nat \<Rightarrow> 'a matrix \<Rightarrow> 'a tensor3" where
  "split_sequence_heads heads head_dim X =
    map (split_vector heads head_dim) X"

theorem tensor3_shape_split_sequence_heads:
  assumes "matrix_shape seq_len (heads * head_dim) X"
  shows "tensor3_shape seq_len heads head_dim
    (split_sequence_heads heads head_dim X)"
  using assms split_vector_shape
  by (auto simp: tensor3_shape_def matrix_shape_def split_sequence_heads_def)

definition concat_sequence_heads :: "'a tensor3 \<Rightarrow> 'a matrix" where
  "concat_sequence_heads T = map concat T"

lemma concat_sequence_heads_shape:
  assumes "tensor3_shape seq_len heads head_dim T"
  shows "matrix_shape seq_len (heads * head_dim) (concat_sequence_heads T)"
proof -
  have outer: "length T = seq_len"
    using assms by (simp add: tensor3_shape_def)
  have rows: "\<And>M. M \<in> set T \<Longrightarrow> length (concat M) = heads * head_dim"
  proof -
    fix M
    assume "M \<in> set T"
    then have "matrix_shape heads head_dim M"
      using assms by (auto simp: tensor3_shape_def)
    then show "length (concat M) = heads * head_dim"
      by (rule matrix_shape_concat_length)
  qed
  show ?thesis
    using outer rows
    by (auto simp: matrix_shape_def concat_sequence_heads_def)
qed

theorem concat_split_sequence_heads:
  assumes "matrix_shape seq_len (heads * head_dim) X"
  shows "concat_sequence_heads (split_sequence_heads heads head_dim X) = X"
proof -
  have rows: "\<And>x. x \<in> set X \<Longrightarrow> length x = heads * head_dim"
    using assms by (auto simp: matrix_shape_def)
  show ?thesis
    unfolding concat_sequence_heads_def split_sequence_heads_def
    apply (simp only: map_map)
    apply (rule map_idI)
    using rows concat_split_vector by auto
qed

end
