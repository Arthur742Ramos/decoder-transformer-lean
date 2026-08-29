theory Decoder_Block
  imports Multi_Head_Attention
begin

section \<open>Normalization, Residuals, and Decoder Blocks\<close>

subsection \<open>Exact RMS normalization\<close>

definition rms_denominator :: "real \<Rightarrow> real vector \<Rightarrow> real" where
  "rms_denominator epsilon x =
    sqrt (sum_list (map (\<lambda>v. v * v) x) / real (length x) + epsilon)"

definition rms_norm ::
  "real \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> real vector" where
  "rms_norm epsilon gain x =
    map2 (\<lambda>g v. g * (v / rms_denominator epsilon x)) gain x"

lemma rms_norm_shape:
  assumes "vector_shape model_dim gain" "vector_shape model_dim x"
  shows "vector_shape model_dim (rms_norm epsilon gain x)"
  using assms by (simp add: rms_norm_def vector_shape_def)

definition rms_norm_sequence ::
  "real \<Rightarrow> real vector \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "rms_norm_sequence epsilon gain X = map (rms_norm epsilon gain) X"

lemma rms_norm_sequence_shape:
  assumes "vector_shape model_dim gain" "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim (rms_norm_sequence epsilon gain X)"
  using assms rms_norm_shape
  by (auto simp: rms_norm_sequence_def matrix_shape_def vector_shape_def)

lemma rms_norm_sequence_is_causal:
  "causal (rms_norm_sequence epsilon gain)"
  unfolding rms_norm_sequence_def by (rule causal_map)

lemma length_rms_norm_sequence [simp]:
  "length (rms_norm_sequence epsilon gain X) = length X"
  by (simp add: rms_norm_sequence_def)

subsection \<open>Pointwise feed-forward networks\<close>

definition feed_forward ::
  "nat \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real vector \<Rightarrow>
   real vector" where
  "feed_forward model_dim hidden_dim activation W_up W_down x =
    linear_project model_dim W_down
      (map activation (linear_project hidden_dim W_up x))"

lemma feed_forward_shape:
  assumes input: "vector_shape model_dim x"
    and up: "matrix_shape model_dim hidden_dim W_up"
    and down: "matrix_shape hidden_dim model_dim W_down"
  shows "vector_shape model_dim
    (feed_forward model_dim hidden_dim activation W_up W_down x)"
proof -
  have hidden:
    "vector_shape hidden_dim (linear_project hidden_dim W_up x)"
    by (rule linear_project_shape[OF up input])
  have activated:
    "vector_shape hidden_dim
      (map activation (linear_project hidden_dim W_up x))"
    using hidden by (simp add: vector_shape_def)
  show ?thesis
    unfolding feed_forward_def
    by (rule linear_project_shape[OF down activated])
qed

definition feed_forward_sequence ::
  "nat \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real matrix" where
  "feed_forward_sequence model_dim hidden_dim activation W_up W_down X =
    map (feed_forward model_dim hidden_dim activation W_up W_down) X"

lemma feed_forward_sequence_shape:
  assumes input: "matrix_shape seq_len model_dim X"
    and up: "matrix_shape model_dim hidden_dim W_up"
    and down: "matrix_shape hidden_dim model_dim W_down"
  shows "matrix_shape seq_len model_dim
    (feed_forward_sequence model_dim hidden_dim activation W_up W_down X)"
  using input feed_forward_shape[OF _ up down]
  by (auto simp: feed_forward_sequence_def matrix_shape_def vector_shape_def)

lemma feed_forward_sequence_is_causal:
  "causal (feed_forward_sequence model_dim hidden_dim activation W_up W_down)"
  unfolding feed_forward_sequence_def by (rule causal_map)

lemma length_feed_forward_sequence [simp]:
  "length (feed_forward_sequence model_dim hidden_dim activation W_up W_down X) =
    length X"
  by (simp add: feed_forward_sequence_def)

subsection \<open>Residual sequence operators\<close>

definition sequence_residual ::
  "real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "sequence_residual X Y =
    map (\<lambda>p. vector_add (fst p) (snd p)) (zip X Y)"

lemma sequence_residual_take:
  "take n (sequence_residual X Y) =
    sequence_residual (take n X) (take n Y)"
  by (simp only: sequence_residual_def take_map take_zip)

lemma sequence_residual_shape:
  assumes X: "matrix_shape seq_len model_dim X"
    and Y: "matrix_shape seq_len model_dim Y"
  shows "matrix_shape seq_len model_dim (sequence_residual X Y)"
proof -
  have lengths: "length X = seq_len" "length Y = seq_len"
    using X Y by (simp_all add: matrix_shape_def)
  have rows:
    "\<forall>row \<in> set (sequence_residual X Y). length row = model_dim"
  proof (intro ballI)
    fix row
    assume "row \<in> set (sequence_residual X Y)"
    then obtain x y where pair: "(x, y) \<in> set (zip X Y)"
      and row: "row = vector_add x y"
      by (auto simp: sequence_residual_def)
    have x_member: "x \<in> set X"
      by (rule set_zip_leftD[OF pair])
    have y_member: "y \<in> set Y"
      by (rule set_zip_rightD[OF pair])
    then have x_shape: "vector_shape model_dim x"
      and y_shape: "vector_shape model_dim y"
      using X Y x_member y_member
      by (auto simp: matrix_shape_def vector_shape_def)
    have "vector_shape model_dim (vector_add x y)"
      by (rule vector_add_shape[OF x_shape y_shape])
    then show "length row = model_dim"
      by (simp add: row vector_shape_def)
  qed
  show ?thesis
    using lengths rows by (simp add: sequence_residual_def matrix_shape_def)
qed

lemma length_sequence_residual:
  assumes "length X = length Y"
  shows "length (sequence_residual X Y) = length X"
  using assms by (simp add: sequence_residual_def)

lemma sequence_residual_append:
  assumes "length X = length Y"
  shows "sequence_residual (X @ [x]) (Y @ [y]) =
    sequence_residual X Y @ [vector_add x y]"
  using assms by (simp add: sequence_residual_def)

definition residual_block ::
  "(real matrix \<Rightarrow> real matrix) \<Rightarrow> real matrix \<Rightarrow>
   real matrix" where
  "residual_block F X = sequence_residual X (F X)"

lemma residual_block_shape:
  assumes "matrix_shape seq_len model_dim X"
    and "matrix_shape seq_len model_dim (F X)"
  shows "matrix_shape seq_len model_dim (residual_block F X)"
  unfolding residual_block_def
  by (rule sequence_residual_shape[OF assms])

lemma residual_block_is_causal:
  assumes "causal F"
  shows "causal (residual_block F)"
proof (rule causalI)
  fix n :: nat and X Y :: "real matrix"
  assume prefix: "take n X = take n Y"
  have transformed: "take n (F X) = take n (F Y)"
    by (rule causalD[OF assms prefix])
  show "take n (residual_block F X) = take n (residual_block F Y)"
    using prefix transformed
    by (simp add: residual_block_def sequence_residual_take)
qed

subsection \<open>Pre-normalized decoder blocks\<close>

definition attention_residual_block ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow>
   real vector \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix" where
  "attention_residual_block heads model_dim head_dim epsilon attention_gain
      WQ WK WV WO =
    residual_block
      (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO \<circ>
        rms_norm_sequence epsilon attention_gain)"

lemma attention_residual_block_shape:
  assumes params:
    "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO"
    and gain: "vector_shape model_dim attention_gain"
    and input: "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim
    (attention_residual_block heads model_dim head_dim epsilon attention_gain
      WQ WK WV WO X)"
proof -
  have normalized:
    "matrix_shape seq_len model_dim
      (rms_norm_sequence epsilon attention_gain X)"
    by (rule rms_norm_sequence_shape[OF gain input])
  have attended:
    "matrix_shape seq_len model_dim
      (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO
        (rms_norm_sequence epsilon attention_gain X))"
    by (rule multi_head_causal_attention_shape[OF params normalized])
  show ?thesis
    unfolding attention_residual_block_def comp_apply
    apply (rule residual_block_shape[OF input])
    by (rule attended)
qed

lemma attention_residual_block_is_causal:
  "causal (attention_residual_block heads model_dim head_dim epsilon
    attention_gain WQ WK WV WO)"
proof -
  have normalized: "causal (rms_norm_sequence epsilon attention_gain)"
    by (rule rms_norm_sequence_is_causal)
  have attended:
    "causal (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO)"
    by (rule multi_head_causal_attention_is_causal)
  have composition:
    "causal (multi_head_causal_attention heads model_dim head_dim WQ WK WV WO \<circ>
      rms_norm_sequence epsilon attention_gain)"
    by (rule causal_comp[OF normalized attended])
  show ?thesis
    unfolding attention_residual_block_def
    by (rule residual_block_is_causal[OF composition])
qed

lemma attention_residual_block_append:
  "attention_residual_block heads model_dim head_dim epsilon attention_gain
      WQ WK WV WO (X @ [x]) =
    attention_residual_block heads model_dim head_dim epsilon attention_gain
      WQ WK WV WO X @
    [vector_add x
      (multi_head_at_prefix heads model_dim head_dim WQ WK WV WO
        (rms_norm epsilon attention_gain x)
        (rms_norm_sequence epsilon attention_gain X @
          [rms_norm epsilon attention_gain x]))]"
proof -
  have normalized:
    "rms_norm_sequence epsilon attention_gain (X @ [x]) =
      rms_norm_sequence epsilon attention_gain X @
        [rms_norm epsilon attention_gain x]"
    by (simp add: rms_norm_sequence_def)
  have attended:
    "multi_head_causal_attention heads model_dim head_dim WQ WK WV WO
        (rms_norm_sequence epsilon attention_gain (X @ [x])) =
      multi_head_causal_attention heads model_dim head_dim WQ WK WV WO
        (rms_norm_sequence epsilon attention_gain X) @
      [multi_head_at_prefix heads model_dim head_dim WQ WK WV WO
        (rms_norm epsilon attention_gain x)
        (rms_norm_sequence epsilon attention_gain X @
          [rms_norm epsilon attention_gain x])]"
    unfolding normalized
    by (rule multi_head_causal_attention_append)
  show ?thesis
    unfolding attention_residual_block_def residual_block_def comp_apply
    unfolding attended
    apply (rule sequence_residual_append)
    by simp
qed

lemma length_attention_residual_block [simp]:
  "length (attention_residual_block heads model_dim head_dim epsilon
    attention_gain WQ WK WV WO X) = length X"
  unfolding attention_residual_block_def residual_block_def comp_apply
  by (rule length_sequence_residual) (simp add: multi_head_causal_attention_def)

definition mlp_residual_block ::
  "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow>
   real vector \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real matrix \<Rightarrow> real matrix" where
  "mlp_residual_block model_dim hidden_dim epsilon activation mlp_gain
      W_up W_down =
    residual_block
      (feed_forward_sequence model_dim hidden_dim activation W_up W_down \<circ>
        rms_norm_sequence epsilon mlp_gain)"

lemma mlp_residual_block_shape:
  assumes gain: "vector_shape model_dim mlp_gain"
    and up: "matrix_shape model_dim hidden_dim W_up"
    and down: "matrix_shape hidden_dim model_dim W_down"
    and input: "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim
    (mlp_residual_block model_dim hidden_dim epsilon activation mlp_gain
      W_up W_down X)"
proof -
  have normalized:
    "matrix_shape seq_len model_dim (rms_norm_sequence epsilon mlp_gain X)"
    by (rule rms_norm_sequence_shape[OF gain input])
  have transformed:
    "matrix_shape seq_len model_dim
      (feed_forward_sequence model_dim hidden_dim activation W_up W_down
        (rms_norm_sequence epsilon mlp_gain X))"
    by (rule feed_forward_sequence_shape[OF normalized up down])
  show ?thesis
    unfolding mlp_residual_block_def comp_apply
    apply (rule residual_block_shape[OF input])
    by (rule transformed)
qed

lemma mlp_residual_block_is_causal:
  "causal (mlp_residual_block model_dim hidden_dim epsilon activation
    mlp_gain W_up W_down)"
proof -
  have normalized: "causal (rms_norm_sequence epsilon mlp_gain)"
    by (rule rms_norm_sequence_is_causal)
  have transformed:
    "causal (feed_forward_sequence model_dim hidden_dim activation W_up W_down)"
    by (rule feed_forward_sequence_is_causal)
  have composition:
    "causal (feed_forward_sequence model_dim hidden_dim activation W_up W_down \<circ>
      rms_norm_sequence epsilon mlp_gain)"
    by (rule causal_comp[OF normalized transformed])
  show ?thesis
    unfolding mlp_residual_block_def
    by (rule residual_block_is_causal[OF composition])
qed

lemma mlp_residual_block_append:
  "mlp_residual_block model_dim hidden_dim epsilon activation mlp_gain
      W_up W_down (X @ [x]) =
    mlp_residual_block model_dim hidden_dim epsilon activation mlp_gain
      W_up W_down X @
    [vector_add x
      (feed_forward model_dim hidden_dim activation W_up W_down
        (rms_norm epsilon mlp_gain x))]"
proof -
  have transformed:
    "(feed_forward_sequence model_dim hidden_dim activation W_up W_down \<circ>
      rms_norm_sequence epsilon mlp_gain) (X @ [x]) =
    (feed_forward_sequence model_dim hidden_dim activation W_up W_down \<circ>
      rms_norm_sequence epsilon mlp_gain) X @
    [feed_forward model_dim hidden_dim activation W_up W_down
      (rms_norm epsilon mlp_gain x)]"
    by (simp add: feed_forward_sequence_def rms_norm_sequence_def)
  show ?thesis
    unfolding mlp_residual_block_def residual_block_def
    unfolding transformed
    apply (rule sequence_residual_append)
    by simp
qed

lemma length_mlp_residual_block [simp]:
  "length (mlp_residual_block model_dim hidden_dim epsilon activation
    mlp_gain W_up W_down X) = length X"
  unfolding mlp_residual_block_def residual_block_def comp_apply
  by (rule length_sequence_residual) simp

definition decoder_block ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow>
   (real \<Rightarrow> real) \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow>
   real tensor3 \<Rightarrow> real tensor3 \<Rightarrow> real tensor3 \<Rightarrow>
   real matrix \<Rightarrow> real matrix \<Rightarrow> real matrix \<Rightarrow>
   real matrix \<Rightarrow> real matrix" where
  "decoder_block heads model_dim head_dim hidden_dim epsilon activation
      attention_gain mlp_gain WQ WK WV WO W_up W_down =
    mlp_residual_block model_dim hidden_dim epsilon activation mlp_gain
      W_up W_down \<circ>
    attention_residual_block heads model_dim head_dim epsilon attention_gain
      WQ WK WV WO"

theorem decoder_block_shape:
  assumes params:
    "multi_head_parameters_shape heads model_dim head_dim WQ WK WV WO"
    and attention_gain: "vector_shape model_dim attention_gain"
    and mlp_gain: "vector_shape model_dim mlp_gain"
    and up: "matrix_shape model_dim hidden_dim W_up"
    and down: "matrix_shape hidden_dim model_dim W_down"
    and input: "matrix_shape seq_len model_dim X"
  shows "matrix_shape seq_len model_dim
    (decoder_block heads model_dim head_dim hidden_dim epsilon activation
      attention_gain mlp_gain WQ WK WV WO W_up W_down X)"
proof -
  have attended:
    "matrix_shape seq_len model_dim
      (attention_residual_block heads model_dim head_dim epsilon attention_gain
        WQ WK WV WO X)"
    by (rule attention_residual_block_shape[OF params attention_gain input])
  show ?thesis
    unfolding decoder_block_def comp_apply
    by (rule mlp_residual_block_shape[OF mlp_gain up down attended])
qed

theorem decoder_block_is_causal:
  "causal (decoder_block heads model_dim head_dim hidden_dim epsilon activation
    attention_gain mlp_gain WQ WK WV WO W_up W_down)"
proof -
  have attention:
    "causal (attention_residual_block heads model_dim head_dim epsilon
      attention_gain WQ WK WV WO)"
    by (rule attention_residual_block_is_causal)
  have mlp:
    "causal (mlp_residual_block model_dim hidden_dim epsilon activation
      mlp_gain W_up W_down)"
    by (rule mlp_residual_block_is_causal)
  show ?thesis
    unfolding decoder_block_def
    by (rule causal_comp[OF attention mlp])
qed

lemma length_decoder_block [simp]:
  "length (decoder_block heads model_dim head_dim hidden_dim epsilon activation
    attention_gain mlp_gain WQ WK WV WO W_up W_down X) = length X"
  by (simp add: decoder_block_def)

end
