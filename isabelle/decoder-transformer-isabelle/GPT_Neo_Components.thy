theory GPT_Neo_Components
  imports Multi_Head_Attention
begin

section \<open>GPT-Neo-specific exact components\<close>

text \<open>
  The main modern-decoder path models RMSNorm, RoPE, SwiGLU, and grouped
  query attention.  GPT-Neo uses a different stack: learned position vectors,
  LayerNorm, ordinary multi-head attention, a sliding-window attention mode,
  affine projection biases, and GELU.  These definitions keep that
  architecture distinction explicit instead of treating a GPT-Neo checkpoint
  as an instance of the modern path.
\<close>

definition affine_project ::
  "nat \<Rightarrow> 'a::semiring_0 matrix \<Rightarrow> 'a vector \<Rightarrow>
   'a vector \<Rightarrow> 'a vector" where
  "affine_project out_dim W bias x =
    vector_add (linear_project out_dim W x) bias"

lemma affine_project_shape:
  assumes W: "matrix_shape in_dim out_dim W"
    and bias: "vector_shape out_dim bias"
    and x: "vector_shape in_dim x"
  shows "vector_shape out_dim (affine_project out_dim W bias x)"
  unfolding affine_project_def
  by (rule vector_add_shape[OF linear_project_shape[OF W x] bias])

definition gpt_neo_input_embedding ::
  "real matrix \<Rightarrow> real matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real vector" where
  "gpt_neo_input_embedding token_embeddings position_embeddings token position =
    vector_add (token_embeddings ! token) (position_embeddings ! position)"

theorem gpt_neo_input_embedding_shape:
  assumes token_bound: "token < vocab_size"
    and position_bound: "position < max_position"
    and tokens: "matrix_shape vocab_size model_dim token_embeddings"
    and positions: "matrix_shape max_position model_dim position_embeddings"
  shows "vector_shape model_dim
    (gpt_neo_input_embedding token_embeddings position_embeddings token position)"
proof -
  have token_shape:
    "vector_shape model_dim (token_embeddings ! token)"
    using matrix_shape_nth[OF tokens token_bound]
    by (simp add: vector_shape_def)
  have position_shape:
    "vector_shape model_dim (position_embeddings ! position)"
    using matrix_shape_nth[OF positions position_bound]
    by (simp add: vector_shape_def)
  show ?thesis
    unfolding gpt_neo_input_embedding_def
    by (rule vector_add_shape[OF token_shape position_shape])
qed

definition gpt_neo_logits ::
  "nat \<Rightarrow> real matrix \<Rightarrow> real vector \<Rightarrow> real vector" where
  "gpt_neo_logits vocabulary_size vocabulary_weights hidden =
    linear_project vocabulary_size vocabulary_weights hidden"

theorem gpt_neo_logits_shape:
  assumes weights: "matrix_shape model_dim vocabulary_size vocabulary_weights"
    and hidden: "vector_shape model_dim hidden"
  shows "vector_shape vocabulary_size
    (gpt_neo_logits vocabulary_size vocabulary_weights hidden)"
  unfolding gpt_neo_logits_def
  by (rule linear_project_shape[OF weights hidden])

definition gpt_neo_mean :: "real vector \<Rightarrow> real" where
  "gpt_neo_mean x =
    (if x = [] then 0 else sum_list x / real (length x))"

definition gpt_neo_variance :: "real vector \<Rightarrow> real" where
  "gpt_neo_variance x =
    (if x = [] then 0
     else sum_list
       (map (\<lambda>v. (v - gpt_neo_mean x) * (v - gpt_neo_mean x)) x) /
       real (length x))"

definition gpt_neo_normalized ::
  "real vector \<Rightarrow> real \<Rightarrow> real vector" where
  "gpt_neo_normalized x epsilon =
    map (\<lambda>v.
      (v - gpt_neo_mean x) /
        sqrt (gpt_neo_variance x + epsilon)) x"

definition gpt_neo_layer_norm ::
  "real \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "gpt_neo_layer_norm epsilon gain bias x =
    map2 (\<lambda>gb z. fst gb * z + snd gb)
      (zip gain bias) (gpt_neo_normalized x epsilon)"

lemma gpt_neo_layer_norm_shape:
  assumes gain: "vector_shape n gain"
    and bias: "vector_shape n bias"
    and x: "vector_shape n x"
  shows "vector_shape n (gpt_neo_layer_norm epsilon gain bias x)"
  using gain bias x
  by (simp add: gpt_neo_layer_norm_def gpt_neo_normalized_def
      vector_shape_def)

definition gpt_neo_gelu_new :: "real \<Rightarrow> real" where
  "gpt_neo_gelu_new x =
    (1 / 2) * x *
      (1 + tanh (sqrt (2 / pi) * (x + 0.044715 * x * x * x)))"

lemma gpt_neo_gelu_new_zero [simp]:
  "gpt_neo_gelu_new 0 = 0"
  by (simp add: gpt_neo_gelu_new_def)

definition gpt_neo_local_context ::
  "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "gpt_neo_local_context window xs =
    drop (length xs - min window (length xs)) xs"

lemma length_gpt_neo_local_context [simp]:
  "length (gpt_neo_local_context window xs) = min window (length xs)"
  by (simp add: gpt_neo_local_context_def)

lemma gpt_neo_local_context_short:
  assumes "length xs \<le> window"
  shows "gpt_neo_local_context window xs = xs"
  using assms by (simp add: gpt_neo_local_context_def)

definition gpt_neo_attention_context ::
  "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "gpt_neo_attention_context window xs =
    (if window = 0 then xs else gpt_neo_local_context window xs)"

lemma gpt_neo_attention_context_global [simp]:
  "gpt_neo_attention_context 0 xs = xs"
  by (simp add: gpt_neo_attention_context_def)

lemma length_gpt_neo_attention_context:
  "length (gpt_neo_attention_context window xs) =
    (if window = 0 then length xs else min window (length xs))"
  by (simp add: gpt_neo_attention_context_def)

definition gpt_neo_windowed_head_attention ::
  "nat \<Rightarrow> nat \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real vector \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "gpt_neo_windowed_head_attention head_dim window WQ WK WV x prefix =
    exact_attention head_dim head_dim
      (linear_project head_dim WQ x)
      (map (linear_project head_dim WK)
        (gpt_neo_attention_context window prefix))
      (map (linear_project head_dim WV)
        (gpt_neo_attention_context window prefix))"

lemma gpt_neo_windowed_head_attention_shape:
  "vector_shape head_dim
    (gpt_neo_windowed_head_attention head_dim window WQ WK WV x prefix)"
  by (simp add: gpt_neo_windowed_head_attention_def exact_attention_shape)

definition gpt_neo_windowed_multi_head_at_prefix ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real vector \<Rightarrow>
   real vector \<Rightarrow> real matrix \<Rightarrow> real vector" where
  "gpt_neo_windowed_multi_head_at_prefix heads model_dim head_dim window
      WQ WK WV WO out_bias x prefix =
    affine_project model_dim WO out_bias
      (concat (map (\<lambda>h.
        gpt_neo_windowed_head_attention head_dim window
          (WQ ! h) (WK ! h) (WV ! h) x prefix)
        [0..<heads]))"

theorem gpt_neo_windowed_multi_head_at_prefix_shape:
  assumes params:
    "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO"
    and out_bias: "vector_shape model_dim out_bias"
    and input: "vector_shape model_dim x"
  shows "vector_shape model_dim
    (gpt_neo_windowed_multi_head_at_prefix heads model_dim head_dim window
      WQ WK WV WO out_bias x prefix)"
proof -
  have rows:
    "\<forall>row \<in> set
      (map (\<lambda>h.
        gpt_neo_windowed_head_attention head_dim window
          (WQ ! h) (WK ! h) (WV ! h) x prefix)
        [0..<heads]).
      length row = head_dim"
    using gpt_neo_windowed_head_attention_shape
    by (auto simp: vector_shape_def)
  have concatenated:
    "vector_shape (heads * head_dim)
      (concat (map (\<lambda>h.
        gpt_neo_windowed_head_attention head_dim window
          (WQ ! h) (WK ! h) (WV ! h) x prefix)
        [0..<heads]))"
    unfolding vector_shape_def
    using concat_rows_length[OF rows] by simp
  have output_shape:
    "matrix_shape (heads * head_dim) model_dim WO"
    using params by (simp add: multi_head_parameters_shape_def)
  show ?thesis
    unfolding gpt_neo_windowed_multi_head_at_prefix_def
    apply (rule affine_project_shape[OF output_shape out_bias])
    by (rule concatenated)
qed

definition gpt_neo_mlp ::
  "nat \<Rightarrow> nat \<Rightarrow>
   real matrix \<Rightarrow> real vector \<Rightarrow>
   real matrix \<Rightarrow> real vector \<Rightarrow>
   real vector \<Rightarrow> real vector" where
  "gpt_neo_mlp model_dim hidden_dim W_fc b_fc W_proj b_proj x =
    affine_project model_dim W_proj b_proj
      (map gpt_neo_gelu_new
        (affine_project hidden_dim W_fc b_fc x))"

lemma gpt_neo_mlp_shape:
  assumes x: "vector_shape model_dim x"
    and fc: "matrix_shape model_dim hidden_dim W_fc"
    and fc_bias: "vector_shape hidden_dim b_fc"
    and proj: "matrix_shape hidden_dim model_dim W_proj"
    and proj_bias: "vector_shape model_dim b_proj"
  shows "vector_shape model_dim
    (gpt_neo_mlp model_dim hidden_dim W_fc b_fc W_proj b_proj x)"
proof -
  have fc_output:
    "vector_shape hidden_dim (affine_project hidden_dim W_fc b_fc x)"
    by (rule affine_project_shape[OF fc fc_bias x])
  have activated:
    "vector_shape hidden_dim
      (map gpt_neo_gelu_new
        (affine_project hidden_dim W_fc b_fc x))"
    using fc_output by (simp add: vector_shape_def)
  show ?thesis
    unfolding gpt_neo_mlp_def
    by (rule affine_project_shape[OF proj proj_bias activated])
qed

record gpt_neo_layer_parameters =
  gpt_neo_head_count :: nat
  gpt_neo_model_dimension :: nat
  gpt_neo_head_dimension :: nat
  gpt_neo_hidden_dimension :: nat
  gpt_neo_attention_window :: nat
  gpt_neo_norm_epsilon :: real
  gpt_neo_ln1_gain :: "real vector"
  gpt_neo_ln1_bias :: "real vector"
  gpt_neo_ln2_gain :: "real vector"
  gpt_neo_ln2_bias :: "real vector"
  gpt_neo_query_weights :: "real tensor3"
  gpt_neo_key_weights :: "real tensor3"
  gpt_neo_value_weights :: "real tensor3"
  gpt_neo_output_weights :: "real matrix"
  gpt_neo_output_bias :: "real vector"
  gpt_neo_fc_weights :: "real matrix"
  gpt_neo_fc_bias :: "real vector"
  gpt_neo_projection_weights :: "real matrix"
  gpt_neo_projection_bias :: "real vector"

definition gpt_neo_normalized_prefix ::
  "gpt_neo_layer_parameters \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "gpt_neo_normalized_prefix p prefix =
    map (\<lambda>y. gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
      (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) y) prefix"

definition valid_gpt_neo_layer ::
  "gpt_neo_layer_parameters \<Rightarrow> bool" where
  "valid_gpt_neo_layer p \<longleftrightarrow>
    0 < gpt_neo_head_count p \<and>
    0 < gpt_neo_model_dimension p \<and>
    0 < gpt_neo_head_dimension p \<and>
    0 < gpt_neo_hidden_dimension p \<and>
    gpt_neo_model_dimension p =
      gpt_neo_head_count p * gpt_neo_head_dimension p \<and>
    0 < gpt_neo_norm_epsilon p \<and>
    vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln1_gain p) \<and>
    vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln1_bias p) \<and>
    vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln2_gain p) \<and>
    vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln2_bias p) \<and>
    multi_head_parameters_shape (gpt_neo_head_count p)
      (gpt_neo_model_dimension p) (gpt_neo_head_dimension p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p) \<and>
    vector_shape (gpt_neo_model_dimension p) (gpt_neo_output_bias p) \<and>
    matrix_shape (gpt_neo_model_dimension p)
      (gpt_neo_hidden_dimension p) (gpt_neo_fc_weights p) \<and>
    vector_shape (gpt_neo_hidden_dimension p) (gpt_neo_fc_bias p) \<and>
    matrix_shape (gpt_neo_hidden_dimension p)
      (gpt_neo_model_dimension p) (gpt_neo_projection_weights p) \<and>
    vector_shape (gpt_neo_model_dimension p) (gpt_neo_projection_bias p)"

definition gpt_neo_block_at_prefix ::
  "gpt_neo_layer_parameters \<Rightarrow> real vector \<Rightarrow>
   real matrix \<Rightarrow> real vector" where
  "gpt_neo_block_at_prefix p x prefix =
    (let normalized_attention =
       gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
         (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) x;
         attention =
         gpt_neo_windowed_multi_head_at_prefix
         (gpt_neo_head_count p) (gpt_neo_model_dimension p)
         (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
         (gpt_neo_query_weights p) (gpt_neo_key_weights p)
         (gpt_neo_value_weights p) (gpt_neo_output_weights p)
         (gpt_neo_output_bias p) normalized_attention
         (gpt_neo_normalized_prefix p prefix);
         attention_residual = vector_add x attention;
         normalized_mlp =
       gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
         (gpt_neo_ln2_gain p) (gpt_neo_ln2_bias p) attention_residual;
         mlp =
       gpt_neo_mlp (gpt_neo_model_dimension p)
         (gpt_neo_hidden_dimension p)
         (gpt_neo_fc_weights p) (gpt_neo_fc_bias p)
         (gpt_neo_projection_weights p) (gpt_neo_projection_bias p)
         normalized_mlp
     in vector_add attention_residual mlp)"

theorem valid_gpt_neo_block_shape:
  assumes valid: "valid_gpt_neo_layer p"
    and input: "vector_shape (gpt_neo_model_dimension p) x"
  shows "vector_shape (gpt_neo_model_dimension p)
    (gpt_neo_block_at_prefix p x prefix)"
proof -
  have ln1_gain:
    "vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln1_gain p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have ln1_bias:
    "vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln1_bias p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have ln2_gain:
    "vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln2_gain p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have ln2_bias:
    "vector_shape (gpt_neo_model_dimension p) (gpt_neo_ln2_bias p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have ln1:
    "vector_shape (gpt_neo_model_dimension p)
      (gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
        (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) x)"
    by (rule gpt_neo_layer_norm_shape[OF ln1_gain ln1_bias input])
  have attention_params:
    "multi_head_parameters_shape (gpt_neo_head_count p)
      (gpt_neo_model_dimension p) (gpt_neo_head_dimension p)
      (gpt_neo_query_weights p) (gpt_neo_key_weights p)
      (gpt_neo_value_weights p) (gpt_neo_output_weights p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have output_bias:
    "vector_shape (gpt_neo_model_dimension p) (gpt_neo_output_bias p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have attention:
    "vector_shape (gpt_neo_model_dimension p)
      (gpt_neo_windowed_multi_head_at_prefix
        (gpt_neo_head_count p) (gpt_neo_model_dimension p)
        (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
        (gpt_neo_query_weights p) (gpt_neo_key_weights p)
        (gpt_neo_value_weights p) (gpt_neo_output_weights p)
        (gpt_neo_output_bias p)
          (gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
          (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) x)
        (gpt_neo_normalized_prefix p prefix))"
    by (rule gpt_neo_windowed_multi_head_at_prefix_shape
      [OF attention_params output_bias ln1])
  have attention_residual:
    "vector_shape (gpt_neo_model_dimension p)
      (vector_add x
        (gpt_neo_windowed_multi_head_at_prefix
          (gpt_neo_head_count p) (gpt_neo_model_dimension p)
          (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
          (gpt_neo_query_weights p) (gpt_neo_key_weights p)
          (gpt_neo_value_weights p) (gpt_neo_output_weights p)
          (gpt_neo_output_bias p)
            (gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
            (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) x)
          (gpt_neo_normalized_prefix p prefix)))"
    by (rule vector_add_shape[OF input attention])
  have ln2:
    "vector_shape (gpt_neo_model_dimension p)
      (gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
        (gpt_neo_ln2_gain p) (gpt_neo_ln2_bias p)
        (vector_add x
          (gpt_neo_windowed_multi_head_at_prefix
            (gpt_neo_head_count p) (gpt_neo_model_dimension p)
            (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
            (gpt_neo_query_weights p) (gpt_neo_key_weights p)
            (gpt_neo_value_weights p) (gpt_neo_output_weights p)
            (gpt_neo_output_bias p)
              (gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
              (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) x)
            (gpt_neo_normalized_prefix p prefix))))"
    by (rule gpt_neo_layer_norm_shape[OF ln2_gain ln2_bias attention_residual])
  have fc:
    "matrix_shape (gpt_neo_model_dimension p)
      (gpt_neo_hidden_dimension p) (gpt_neo_fc_weights p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have fc_bias:
    "vector_shape (gpt_neo_hidden_dimension p) (gpt_neo_fc_bias p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have projection:
    "matrix_shape (gpt_neo_hidden_dimension p)
      (gpt_neo_model_dimension p) (gpt_neo_projection_weights p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have projection_bias:
    "vector_shape (gpt_neo_model_dimension p)
      (gpt_neo_projection_bias p)"
    using valid unfolding valid_gpt_neo_layer_def by blast
  have mlp:
    "vector_shape (gpt_neo_model_dimension p)
      (gpt_neo_mlp (gpt_neo_model_dimension p)
        (gpt_neo_hidden_dimension p) (gpt_neo_fc_weights p)
        (gpt_neo_fc_bias p) (gpt_neo_projection_weights p)
        (gpt_neo_projection_bias p)
        (gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
          (gpt_neo_ln2_gain p) (gpt_neo_ln2_bias p)
          (vector_add x
            (gpt_neo_windowed_multi_head_at_prefix
              (gpt_neo_head_count p) (gpt_neo_model_dimension p)
              (gpt_neo_head_dimension p) (gpt_neo_attention_window p)
              (gpt_neo_query_weights p) (gpt_neo_key_weights p)
              (gpt_neo_value_weights p) (gpt_neo_output_weights p)
              (gpt_neo_output_bias p)
                (gpt_neo_layer_norm (gpt_neo_norm_epsilon p)
                (gpt_neo_ln1_gain p) (gpt_neo_ln1_bias p) x)
              (gpt_neo_normalized_prefix p prefix)))))"
    by (rule gpt_neo_mlp_shape[OF ln2 fc fc_bias projection projection_bias])
  show ?thesis
    unfolding gpt_neo_block_at_prefix_def Let_def
    by (rule vector_add_shape[OF attention_residual mlp])
qed

definition gpt_neo_full_layer ::
  "gpt_neo_layer_parameters \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "gpt_neo_full_layer p X =
    causal_attention id id id
      (\<lambda>x prefix _. gpt_neo_block_at_prefix p x prefix) X"

theorem gpt_neo_full_layer_is_causal:
  "causal (gpt_neo_full_layer p)"
  unfolding gpt_neo_full_layer_def
  by (rule causal_attention_is_causal)

theorem valid_gpt_neo_full_layer_shape:
  assumes valid: "valid_gpt_neo_layer p"
    and input: "matrix_shape seq_len (gpt_neo_model_dimension p) X"
  shows "matrix_shape seq_len (gpt_neo_model_dimension p)
    (gpt_neo_full_layer p X)"
proof -
  have full_output:
    "\<And>prefix. matrix_shape (length X) (gpt_neo_model_dimension p)
      (causal_attention_from id id id
        (\<lambda>x prefix _. gpt_neo_block_at_prefix p x prefix) prefix X)"
  using input
  proof (induction X arbitrary: prefix seq_len)
    case Nil
    then show ?case by (simp add: matrix_shape_def)
  next
    case (Cons x xs)
    have x_shape: "vector_shape (gpt_neo_model_dimension p) x"
      using Cons.prems by (auto simp: matrix_shape_def vector_shape_def)
    have head:
      "length (gpt_neo_block_at_prefix p x (prefix @ [x])) =
        gpt_neo_model_dimension p"
      using valid_gpt_neo_block_shape[OF valid x_shape]
      by (simp add: vector_shape_def)
    have tail_input:
      "matrix_shape (length xs) (gpt_neo_model_dimension p) xs"
      using Cons.prems by (auto simp: matrix_shape_def)
    have tail:
      "matrix_shape (length xs) (gpt_neo_model_dimension p)
        (causal_attention_from id id id
          (\<lambda>x prefix _. gpt_neo_block_at_prefix p x prefix)
          (prefix @ [x]) xs)"
      by (rule Cons.IH[OF tail_input])
    show ?case
      using head tail by (auto simp: matrix_shape_def id_def)
  qed
  have seq_len_eq: "length X = seq_len"
    using matrix_shape_length[OF input] .
  have full_output_empty:
    "matrix_shape (length X) (gpt_neo_model_dimension p)
      (causal_attention_from id id id
        (\<lambda>x prefix _. gpt_neo_block_at_prefix p x prefix) [] X)"
    using full_output[of "[]"] .
  show ?thesis
    unfolding gpt_neo_full_layer_def causal_attention_def
    using full_output_empty seq_len_eq by simp
qed

definition gpt_neo_windowed_causal_attention ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real vector \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "gpt_neo_windowed_causal_attention heads model_dim head_dim window
      WQ WK WV WO out_bias =
    causal_attention id id id
      (\<lambda>x prefix _.
        gpt_neo_windowed_multi_head_at_prefix heads model_dim head_dim window
          WQ WK WV WO out_bias x prefix)"

theorem gpt_neo_windowed_causal_attention_is_causal:
  "causal (gpt_neo_windowed_causal_attention heads model_dim head_dim window
    WQ WK WV WO out_bias)"
  unfolding gpt_neo_windowed_causal_attention_def
  by (rule causal_attention_is_causal)

end
