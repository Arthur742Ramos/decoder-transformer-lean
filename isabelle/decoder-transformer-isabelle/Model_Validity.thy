theory Model_Validity
  imports Numerical_Refinement
begin

section \<open>Globally Well-Formed Decoder Models\<close>

text \<open>
  The semantic operators are total, as is customary in HOL.  This predicate
  collects the nondegeneracy and tensor-shape obligations required of an
  actual decoder layer.  It turns implicit implementation preconditions into
  explicit, reusable theorem hypotheses.
\<close>

definition valid_decoder_layer :: "decoder_layer_parameters \<Rightarrow> bool" where
  "valid_decoder_layer p \<longleftrightarrow>
    0 < layer_head_count p \<and>
    0 < layer_model_dimension p \<and>
    0 < layer_head_dimension p \<and>
    0 < layer_hidden_dimension p \<and>
    layer_model_dimension p = layer_head_count p * layer_head_dimension p \<and>
    0 < layer_norm_epsilon p \<and>
    vector_shape (layer_model_dimension p) (layer_attention_gain p) \<and>
    vector_shape (layer_model_dimension p) (layer_mlp_gain p) \<and>
    multi_head_parameters_shape (layer_head_count p)
      (layer_model_dimension p) (layer_head_dimension p)
      (layer_query_weights p) (layer_key_weights p) (layer_value_weights p)
      (layer_output_weights p) \<and>
    matrix_shape (layer_model_dimension p) (layer_hidden_dimension p)
      (layer_up_weights p) \<and>
    matrix_shape (layer_hidden_dimension p) (layer_model_dimension p)
      (layer_down_weights p)"

definition decoder_layers_well_formed ::
  "nat \<Rightarrow> decoder_layer_parameters list \<Rightarrow> bool" where
  "decoder_layers_well_formed model_dim layers \<longleftrightarrow>
    (\<forall>p \<in> set layers.
      valid_decoder_layer p \<and> layer_model_dimension p = model_dim)"

definition valid_transformer ::
  "nat \<Rightarrow> decoder_layer_parameters list \<Rightarrow> bool" where
  "valid_transformer model_dim layers \<longleftrightarrow>
    0 < model_dim \<and> layers \<noteq> [] \<and>
    decoder_layers_well_formed model_dim layers"

definition valid_vocabulary ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real vector) \<Rightarrow>
   real matrix \<Rightarrow> bool" where
  "valid_vocabulary model_dim vocabulary_size embedding W_vocabulary \<longleftrightarrow>
    0 < vocabulary_size \<and>
    (\<forall>token < vocabulary_size. vector_shape model_dim (embedding token)) \<and>
    matrix_shape model_dim vocabulary_size W_vocabulary"

definition valid_token_selector ::
  "nat \<Rightarrow> (real vector \<Rightarrow> nat) \<Rightarrow> bool" where
  "valid_token_selector vocabulary_size select \<longleftrightarrow>
    (\<forall>distribution. length distribution = vocabulary_size \<longrightarrow>
      select distribution < vocabulary_size)"

definition tokens_in_vocabulary :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "tokens_in_vocabulary vocabulary_size tokens \<longleftrightarrow>
    (\<forall>token \<in> set tokens. token < vocabulary_size)"

lemma valid_decoder_layer_dimensions:
  assumes "valid_decoder_layer p"
  shows "0 < layer_head_count p"
    and "0 < layer_model_dimension p"
    and "0 < layer_head_dimension p"
    and "0 < layer_hidden_dimension p"
    and "layer_model_dimension p =
      layer_head_count p * layer_head_dimension p"
    and "0 < layer_norm_epsilon p"
  using assms unfolding valid_decoder_layer_def by blast+

lemma valid_decoder_layer_shapes:
  assumes "valid_decoder_layer p"
  shows "vector_shape (layer_model_dimension p) (layer_attention_gain p)"
    and "vector_shape (layer_model_dimension p) (layer_mlp_gain p)"
    and "multi_head_parameters_shape (layer_head_count p)
      (layer_model_dimension p) (layer_head_dimension p)
      (layer_query_weights p) (layer_key_weights p) (layer_value_weights p)
      (layer_output_weights p)"
    and "matrix_shape (layer_model_dimension p) (layer_hidden_dimension p)
      (layer_up_weights p)"
    and "matrix_shape (layer_hidden_dimension p) (layer_model_dimension p)
      (layer_down_weights p)"
  using assms unfolding valid_decoder_layer_def by blast+

lemma rms_denominator_positive:
  assumes "0 < epsilon"
  shows "0 < rms_denominator epsilon x"
proof -
  have squares: "0 \<le> sum_list (map (\<lambda>v. v * v) x)"
    by (rule sum_list_nonneg) auto
  have quotient:
    "0 \<le> sum_list (map (\<lambda>v. v * v) x) / real (length x)"
    by (rule divide_nonneg_nonneg[OF squares]) simp
  have inside:
    "0 < sum_list (map (\<lambda>v. v * v) x) / real (length x) + epsilon"
    using quotient assms by linarith
  show ?thesis
    unfolding rms_denominator_def
    by (rule real_sqrt_gt_zero[OF inside])
qed

corollary valid_layer_rms_denominator_nonzero:
  assumes "valid_decoder_layer p"
  shows "rms_denominator (layer_norm_epsilon p) x \<noteq> 0"
proof -
  have "0 < rms_denominator (layer_norm_epsilon p) x"
    by (rule rms_denominator_positive)
      (rule valid_decoder_layer_dimensions(6)[OF assms])
  then show ?thesis by simp
qed

lemma valid_layer_attention_scale_positive:
  assumes "valid_decoder_layer p"
  shows "0 < sqrt (real (layer_head_dimension p))"
  using valid_decoder_layer_dimensions(3)[OF assms]
  by (simp add: real_sqrt_gt_0_iff)

theorem valid_decoder_layer_preserves_shape:
  assumes valid: "valid_decoder_layer p"
    and input: "matrix_shape seq_len (layer_model_dimension p) X"
  shows "matrix_shape seq_len (layer_model_dimension p)
    (full_decoder_layer p X)"
  unfolding full_decoder_layer_def
  apply (rule decoder_block_shape)
  using valid_decoder_layer_shapes[OF valid] input by blast+

theorem well_formed_decoder_stack_preserves_shape:
  assumes valid: "decoder_layers_well_formed model_dim layers"
    and input: "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim (full_decoder_stack layers X)"
  using valid input
proof (induction layers arbitrary: X)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have layer_valid: "valid_decoder_layer p"
    and layer_dim: "layer_model_dimension p = model_dim"
    using Cons.prems(1)
    by (auto simp: decoder_layers_well_formed_def)
  have tail_valid: "decoder_layers_well_formed model_dim ps"
    using Cons.prems(1) by (simp add: decoder_layers_well_formed_def)
  have layer_shape:
    "matrix_shape seq_len model_dim (full_decoder_layer p X)"
    using valid_decoder_layer_preserves_shape[OF layer_valid]
      Cons.prems(2) layer_dim by simp
  show ?case
    by simp (rule Cons.IH[OF tail_valid layer_shape])
qed

corollary valid_transformer_preserves_shape:
  assumes "valid_transformer model_dim layers"
    and "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim (full_decoder_stack layers X)"
  using assms well_formed_decoder_stack_preserves_shape
  by (auto simp: valid_transformer_def)

lemma cached_generation_distribution_length:
  assumes "tokens \<noteq> []"
  shows "length (fst (cached_generation_evaluate layers embedding vocabulary_size
    W_vocabulary tokens caches)) = vocabulary_size"
  using assms by (simp add: cached_generation_evaluate_def Let_def)

theorem generation_transition_preserves_vocabulary:
  assumes selector: "valid_token_selector vocabulary_size select"
    and tokens: "tokens_in_vocabulary vocabulary_size (fst state)"
    and nonempty: "fst state \<noteq> []"
  shows "tokens_in_vocabulary vocabulary_size
    (fst (generation_transition select layers embedding vocabulary_size
      W_vocabulary state))"
proof -
  have selected:
    "select (fst (cached_generation_evaluate layers embedding vocabulary_size
      W_vocabulary (fst state) (snd state))) < vocabulary_size"
    using selector cached_generation_distribution_length[OF nonempty]
    by (auto simp: valid_token_selector_def)
  show ?thesis
    using tokens selected
    by (simp add: generation_transition_def deterministic_next_token_def
        tokens_in_vocabulary_def Let_def)
qed

theorem generate_steps_preserves_vocabulary:
  assumes selector: "valid_token_selector vocabulary_size select"
    and tokens: "tokens_in_vocabulary vocabulary_size (fst state)"
    and nonempty: "fst state \<noteq> []"
  shows "tokens_in_vocabulary vocabulary_size
    (fst (generate_steps n select layers embedding vocabulary_size
      W_vocabulary state))"
  using tokens nonempty
proof (induction n arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?next = "generation_transition select layers embedding vocabulary_size
    W_vocabulary state"
  have next_tokens: "tokens_in_vocabulary vocabulary_size (fst ?next)"
    by (rule generation_transition_preserves_vocabulary[OF selector Suc.prems])
  have next_nonempty: "fst ?next \<noteq> []"
    using Suc.prems(2) by (simp add: generation_transition_def Let_def)
  show ?case
    by (simp only: generate_steps.simps)
      (rule Suc.IH[OF next_tokens next_nonempty])
qed

end
