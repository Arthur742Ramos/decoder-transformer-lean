theory Modern_Decoder_Components
  imports Rotary_Position_Embedding
begin

section \<open>Grouped-Query Attention and SwiGLU\<close>

definition grouped_query_parameters_shape ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> bool" where
  "grouped_query_parameters_shape query_heads kv_heads model_dim head_dim
      WQ WK WV WO \<longleftrightarrow>
    0 < query_heads \<and>
    0 < kv_heads \<and>
    kv_heads dvd query_heads \<and>
    tensor3_shape query_heads model_dim head_dim WQ \<and>
    tensor3_shape kv_heads model_dim head_dim WK \<and>
    tensor3_shape kv_heads model_dim head_dim WV \<and>
    matrix_shape (query_heads * head_dim) model_dim WO"

text \<open>
  Query heads are laid out in contiguous groups: each key--value head is
  repeated for @\<open>query_heads div kv_heads@\<close> consecutive query heads.
  This is the convention used by standard GQA implementations; making both
  head counts explicit prevents the degenerate modulo map from silently
  selecting a different layout when there is more than one KV head.
\<close>

definition grouped_query_head_index ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "grouped_query_head_index query_heads kv_heads query_head =
    query_head div (query_heads div kv_heads)"

lemma grouped_query_head_index_bound:
  assumes query_positive: "0 < query_heads"
    and kv_positive: "0 < kv_heads"
    and groups: "kv_heads dvd query_heads"
    and query_bound: "query_head < query_heads"
  shows "grouped_query_head_index query_heads kv_heads query_head < kv_heads"
proof -
  obtain group where query_eq: "query_heads = kv_heads * group"
    using groups by (auto elim: dvdE)
  have quotient: "query_heads div kv_heads = group"
    using query_eq kv_positive
    by (simp add: mult.commute)
  have query_less: "query_head < kv_heads * group"
    using query_bound query_eq by simp
  show ?thesis
    unfolding grouped_query_head_index_def quotient
    by (rule less_mult_imp_div_less[OF query_less])
qed

definition grouped_query_at_prefix ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real vector \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "grouped_query_at_prefix query_heads kv_heads model_dim head_dim
      WQ WK WV WO x prefix =
    linear_project model_dim WO
      (concat (map (\<lambda>h.
        let g = grouped_query_head_index query_heads kv_heads h
        in exact_attention head_dim head_dim
          (linear_project head_dim (WQ ! h) x)
          (map (linear_project head_dim (WK ! g)) prefix)
          (map (linear_project head_dim (WV ! g)) prefix))
        [0..<query_heads]))"

theorem grouped_query_at_prefix_shape:
  assumes params:
    "grouped_query_parameters_shape query_heads kv_heads model_dim head_dim
      WQ WK WV WO"
  shows "vector_shape model_dim
    (grouped_query_at_prefix query_heads kv_heads model_dim head_dim
      WQ WK WV WO x prefix)"
proof -
  have rows:
    "\<forall>row \<in> set (map (\<lambda>h.
      let g = grouped_query_head_index query_heads kv_heads h
      in exact_attention head_dim head_dim
        (linear_project head_dim (WQ ! h) x)
        (map (linear_project head_dim (WK ! g)) prefix)
        (map (linear_project head_dim (WV ! g)) prefix))
      [0..<query_heads]). length row = head_dim"
    using exact_attention_shape
    by (auto simp: vector_shape_def Let_def)
  have concatenated:
    "vector_shape (query_heads * head_dim)
      (concat (map (\<lambda>h.
        let g = grouped_query_head_index query_heads kv_heads h
        in exact_attention head_dim head_dim
          (linear_project head_dim (WQ ! h) x)
          (map (linear_project head_dim (WK ! g)) prefix)
          (map (linear_project head_dim (WV ! g)) prefix))
        [0..<query_heads]))"
    unfolding vector_shape_def
    using concat_rows_length[OF rows] by simp
  have output_matrix:
    "matrix_shape (query_heads * head_dim) model_dim WO"
    using params by (simp add: grouped_query_parameters_shape_def)
  show ?thesis
    unfolding grouped_query_at_prefix_def
    by (rule linear_project_shape[OF output_matrix concatenated])
qed

definition grouped_query_causal_attention ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "grouped_query_causal_attention query_heads kv_heads model_dim head_dim
      WQ WK WV WO =
    causal_attention id id id
      (\<lambda>x prefix ignored.
        grouped_query_at_prefix query_heads kv_heads model_dim head_dim
          WQ WK WV WO x prefix)"

theorem grouped_query_causal_attention_is_causal:
  "causal (grouped_query_causal_attention query_heads kv_heads model_dim
    head_dim WQ WK WV WO)"
  unfolding grouped_query_causal_attention_def
  by (rule causal_attention_is_causal)

theorem grouped_query_causal_attention_shape:
  assumes params:
    "grouped_query_parameters_shape query_heads kv_heads model_dim head_dim
      WQ WK WV WO"
  shows "matrix_shape (length X) model_dim
    (grouped_query_causal_attention query_heads kv_heads model_dim head_dim
      WQ WK WV WO X)"
proof -
  have from_shape:
    "\<And>prefix. matrix_shape (length X) model_dim
      (causal_attention_from id id id
        (\<lambda>x prefix ignored.
          grouped_query_at_prefix query_heads kv_heads model_dim head_dim
            WQ WK WV WO x prefix) prefix X)"
  proof (induction X arbitrary: prefix)
    case Nil
    then show ?case by (simp add: matrix_shape_def)
  next
    case (Cons x xs)
    have head:
      "length (grouped_query_at_prefix query_heads kv_heads model_dim head_dim
        WQ WK WV WO x (prefix @ [x])) = model_dim"
      using grouped_query_at_prefix_shape[OF params]
      by (simp add: vector_shape_def)
    have tail:
      "matrix_shape (length xs) model_dim
        (causal_attention_from id id id
          (\<lambda>x prefix ignored.
            grouped_query_at_prefix query_heads kv_heads model_dim head_dim
              WQ WK WV WO x prefix) (prefix @ [x]) xs)"
      by (rule Cons.IH)
    show ?case
      using head tail by (auto simp: matrix_shape_def id_def)
  qed
  show ?thesis
    unfolding grouped_query_causal_attention_def causal_attention_def
    by (rule from_shape)
qed

subsection \<open>Gated feed-forward networks\<close>

definition vector_hadamard ::
  "real vector \<Rightarrow> real vector \<Rightarrow> real vector" where
  "vector_hadamard xs ys = map2 (*) xs ys"

lemma vector_hadamard_shape:
  assumes "vector_shape n xs" "vector_shape n ys"
  shows "vector_shape n (vector_hadamard xs ys)"
  using assms by (simp add: vector_hadamard_def vector_shape_def)

definition silu :: "real \<Rightarrow> real" where
  "silu x = x / (1 + exp (-x))"

definition gated_feed_forward ::
  "nat \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "gated_feed_forward model_dim hidden_dim activation W_gate W_up W_down x =
    linear_project model_dim W_down
      (vector_hadamard
        (map activation (linear_project hidden_dim W_gate x))
        (linear_project hidden_dim W_up x))"

definition swiglu ::
  "nat \<Rightarrow> nat \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real matrix \<Rightarrow> real vector \<Rightarrow> real vector" where
  "swiglu model_dim hidden_dim W_gate W_up W_down =
    gated_feed_forward model_dim hidden_dim silu W_gate W_up W_down"

theorem gated_feed_forward_shape:
  assumes input: "vector_shape model_dim x"
    and gate: "matrix_shape model_dim hidden_dim W_gate"
    and up: "matrix_shape model_dim hidden_dim W_up"
    and down: "matrix_shape hidden_dim model_dim W_down"
  shows "vector_shape model_dim
    (gated_feed_forward model_dim hidden_dim activation
      W_gate W_up W_down x)"
proof -
  have gate_shape:
    "vector_shape hidden_dim (linear_project hidden_dim W_gate x)"
    by (rule linear_project_shape[OF gate input])
  have activated:
    "vector_shape hidden_dim
      (map activation (linear_project hidden_dim W_gate x))"
    using gate_shape by (simp add: vector_shape_def)
  have up_shape:
    "vector_shape hidden_dim (linear_project hidden_dim W_up x)"
    by (rule linear_project_shape[OF up input])
  have product:
    "vector_shape hidden_dim
      (vector_hadamard (map activation (linear_project hidden_dim W_gate x))
        (linear_project hidden_dim W_up x))"
    by (rule vector_hadamard_shape[OF activated up_shape])
  show ?thesis
    unfolding gated_feed_forward_def
    by (rule linear_project_shape[OF down product])
qed

corollary swiglu_shape:
  assumes "vector_shape model_dim x"
    and "matrix_shape model_dim hidden_dim W_gate"
    and "matrix_shape model_dim hidden_dim W_up"
    and "matrix_shape hidden_dim model_dim W_down"
  shows "vector_shape model_dim
    (swiglu model_dim hidden_dim W_gate W_up W_down x)"
  unfolding swiglu_def
  by (rule gated_feed_forward_shape[OF assms])

definition gated_feed_forward_sequence ::
  "nat \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real matrix \<Rightarrow> real matrix" where
  "gated_feed_forward_sequence model_dim hidden_dim activation
      W_gate W_up W_down X =
    map (gated_feed_forward model_dim hidden_dim activation
      W_gate W_up W_down) X"

theorem gated_feed_forward_sequence_is_causal:
  "causal (gated_feed_forward_sequence model_dim hidden_dim activation
    W_gate W_up W_down)"
  unfolding gated_feed_forward_sequence_def
  by (rule causal_map)

end
