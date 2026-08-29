theory Multi_Head_Attention
  imports Exact_Attention
begin

section \<open>Exact Multi-Head Causal Attention\<close>

text \<open>
  A projection tensor contains one model-dimension by head-dimension matrix
  for each head.  The output projection maps the concatenated head vector back
  to the model dimension.  All arithmetic remains exact over the reals.
\<close>

definition multi_head_parameters_shape ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> bool" where
  "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO \<longleftrightarrow>
    tensor3_shape heads model_dim head_dim WQ \<and>
    tensor3_shape heads model_dim head_dim WK \<and>
    tensor3_shape heads model_dim head_dim WV \<and>
    matrix_shape (heads * head_dim) model_dim WO"

lemma multi_head_parameter_nth:
  assumes params:
    "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO"
    and "h < heads"
  shows "matrix_shape model_dim head_dim (WQ ! h)"
    and "matrix_shape model_dim head_dim (WK ! h)"
    and "matrix_shape model_dim head_dim (WV ! h)"
  using assms
  by (auto simp: multi_head_parameters_shape_def tensor3_shape_def
      matrix_shape_def)

definition projected_head_attention ::
  "nat \<Rightarrow> nat \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real vector \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "projected_head_attention model_dim head_dim WQ WK WV x prefix =
    exact_attention head_dim head_dim
      (linear_project head_dim WQ x)
      (map (linear_project head_dim WK) prefix)
      (map (linear_project head_dim WV) prefix)"

lemma projected_head_attention_shape:
  "vector_shape head_dim
    (projected_head_attention model_dim head_dim WQ WK WV x prefix)"
  by (simp add: projected_head_attention_def exact_attention_shape)

definition concatenated_head_attention ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real vector \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "concatenated_head_attention heads model_dim head_dim WQ WK WV x prefix =
    concat
      (map (\<lambda>h. projected_head_attention model_dim head_dim
        (WQ ! h) (WK ! h) (WV ! h) x prefix) [0..<heads])"

lemma concatenated_head_attention_shape:
  "vector_shape (heads * head_dim)
    (concatenated_head_attention heads model_dim head_dim WQ WK WV x prefix)"
proof -
  have rows:
    "\<forall>row \<in> set
      (map (\<lambda>h. projected_head_attention model_dim head_dim
        (WQ ! h) (WK ! h) (WV ! h) x prefix) [0..<heads]).
      length row = head_dim"
    using projected_head_attention_shape
    by (auto simp: vector_shape_def)
  show ?thesis
    unfolding concatenated_head_attention_def vector_shape_def
    using concat_rows_length[OF rows] by simp
qed

definition multi_head_at_prefix ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real vector \<Rightarrow> real matrix \<Rightarrow>
   real vector" where
  "multi_head_at_prefix heads model_dim head_dim WQ WK WV WO x prefix =
    linear_project model_dim WO
      (concatenated_head_attention heads model_dim head_dim WQ WK WV x prefix)"

lemma multi_head_at_prefix_shape:
  assumes
    "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO"
  shows "vector_shape model_dim
    (multi_head_at_prefix heads model_dim head_dim WQ WK WV WO x prefix)"
proof -
  have input:
    "vector_shape (heads * head_dim)
      (concatenated_head_attention heads model_dim head_dim WQ WK WV x prefix)"
    by (rule concatenated_head_attention_shape)
  have output_matrix: "matrix_shape (heads * head_dim) model_dim WO"
    using assms by (simp add: multi_head_parameters_shape_def)
  show ?thesis
    unfolding multi_head_at_prefix_def
    by (rule linear_project_shape[OF output_matrix input])
qed

definition multi_head_causal_attention ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "multi_head_causal_attention heads model_dim head_dim WQ WK WV WO =
    causal_attention id id id
      (\<lambda>x prefix _. multi_head_at_prefix heads model_dim head_dim
        WQ WK WV WO x prefix)"

lemma length_multi_head_causal_attention [simp]:
  "length (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO xs) =
    length xs"
  by (simp add: multi_head_causal_attention_def)

lemma multi_head_causal_attention_from_rows:
  assumes params:
    "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO"
  shows "\<forall>row \<in> set
    (causal_attention_from id id id
      (\<lambda>x prefix _. multi_head_at_prefix heads model_dim head_dim
        WQ WK WV WO x prefix) prefix xs).
    length row = model_dim"
  using params
proof (induction xs arbitrary: prefix)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have head_shape:
    "length (multi_head_at_prefix heads model_dim head_dim
      WQ WK WV WO x (prefix @ [x])) = model_dim"
    using multi_head_at_prefix_shape[OF Cons.prems]
    by (simp add: vector_shape_def)
  have tail_shape:
    "\<forall>row \<in> set
      (causal_attention_from id id id
        (\<lambda>x prefix _. multi_head_at_prefix heads model_dim head_dim
          WQ WK WV WO x prefix) (prefix @ [x]) xs).
      length row = model_dim"
    by (rule Cons.IH[OF Cons.prems])
  show ?case
    using head_shape tail_shape by (simp add: id_def)
qed

theorem multi_head_causal_attention_shape:
  assumes params:
    "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO"
    and input: "matrix_shape seq_len model_dim xs"
  shows "matrix_shape seq_len model_dim
    (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO xs)"
proof -
  have output_length:
    "length (multi_head_causal_attention heads model_dim head_dim
      WQ WK WV WO xs) = seq_len"
    using input by (simp add: multi_head_causal_attention_def matrix_shape_def)
  have output_rows:
    "\<forall>row \<in> set
      (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO xs).
      length row = model_dim"
    unfolding multi_head_causal_attention_def causal_attention_def
    by (rule multi_head_causal_attention_from_rows[OF params])
  show ?thesis
    using output_length output_rows by (simp add: matrix_shape_def)
qed

theorem multi_head_causal_attention_is_causal:
  "causal (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO)"
  unfolding multi_head_causal_attention_def
  by (rule causal_attention_is_causal)

theorem multi_head_causal_attention_independence:
  assumes "i < length xs" "i < length ys"
    and "take (Suc i) xs = take (Suc i) ys"
  shows "multi_head_causal_attention heads model_dim head_dim WQ WK WV WO xs ! i =
    multi_head_causal_attention heads model_dim head_dim WQ WK WV WO ys ! i"
  unfolding multi_head_causal_attention_def
  by (rule causal_attention_independence[OF assms])

lemma multi_head_causal_attention_append:
  "multi_head_causal_attention heads model_dim head_dim WQ WK WV WO (xs @ [x]) =
    multi_head_causal_attention heads model_dim head_dim WQ WK WV WO xs @
      [multi_head_at_prefix heads model_dim head_dim WQ WK WV WO x (xs @ [x])]"
  unfolding multi_head_causal_attention_def
  using causal_attention_append[
    where Q=id and K=id and V=id
      and A="\<lambda>x prefix _. multi_head_at_prefix heads model_dim head_dim
        WQ WK WV WO x prefix"
      and xs=xs and ys="[x]"]
  by (simp add: id_def)

end
