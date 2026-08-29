theory Numerical_Refinement
  imports Autoregressive_Generation
begin

section \<open>Numerical Refinement Interface\<close>

text \<open>
  Floating implementations are observed through decoded real vectors.  The
  relation below does not identify floating arithmetic with real arithmetic:
  a concrete IEEE-754 backend must separately prove its local rounding and
  model-error obligations.
\<close>

definition vector_error_bound ::
  "real \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> bool" where
  "vector_error_bound epsilon xs ys \<longleftrightarrow>
    length xs = length ys \<and>
    (\<forall>i < length xs. \<bar>xs ! i - ys ! i\<bar> \<le> epsilon)"

lemma vector_error_bound_refl:
  assumes "0 \<le> epsilon"
  shows "vector_error_bound epsilon xs xs"
  using assms by (simp add: vector_error_bound_def)

lemma vector_error_bound_sym:
  assumes "vector_error_bound epsilon xs ys"
  shows "vector_error_bound epsilon ys xs"
  using assms
  by (auto simp: vector_error_bound_def abs_minus_commute)

theorem vector_error_bound_triangle:
  assumes xy: "vector_error_bound epsilon xs ys"
    and yz: "vector_error_bound delta ys zs"
  shows "vector_error_bound (epsilon + delta) xs zs"
proof -
  have lengths:
    "length xs = length ys" "length ys = length zs"
    using xy yz by (simp_all add: vector_error_bound_def)
  have coordinates:
    "\<forall>i < length xs. \<bar>xs ! i - zs ! i\<bar> \<le> epsilon + delta"
  proof (intro allI impI)
    fix i
    assume i: "i < length xs"
    have i_y: "i < length ys" using i lengths by simp
    have left: "\<bar>xs ! i - ys ! i\<bar> \<le> epsilon"
      using xy i by (auto simp: vector_error_bound_def)
    have right: "\<bar>ys ! i - zs ! i\<bar> \<le> delta"
      using yz i_y by (auto simp: vector_error_bound_def)
    have "\<bar>xs ! i - zs ! i\<bar> =
      \<bar>(xs ! i - ys ! i) + (ys ! i - zs ! i)\<bar>"
      by simp
    also have "... \<le> \<bar>xs ! i - ys ! i\<bar> + \<bar>ys ! i - zs ! i\<bar>"
      by (rule abs_triangle_ineq)
    also have "... \<le> epsilon + delta"
      using left right by simp
    finally show "\<bar>xs ! i - zs ! i\<bar> \<le> epsilon + delta" .
  qed
  show ?thesis
    using lengths coordinates by (simp add: vector_error_bound_def)
qed

definition vector_lipschitz ::
  "real \<Rightarrow> (real vector \<Rightarrow> real vector) \<Rightarrow> bool" where
  "vector_lipschitz L F \<longleftrightarrow>
    0 \<le> L \<and>
    (\<forall>epsilon xs ys. 0 \<le> epsilon \<longrightarrow>
      vector_error_bound epsilon xs ys \<longrightarrow>
      vector_error_bound (L * epsilon) (F xs) (F ys))"

definition floating_transformer_relation ::
  "real \<Rightarrow> ('input \<Rightarrow> real vector) \<Rightarrow>
   ('input \<Rightarrow> real vector) \<Rightarrow> bool" where
  "floating_transformer_relation hidden_error exact_model floating_model \<longleftrightarrow>
    0 \<le> hidden_error \<and>
    (\<forall>input. vector_error_bound hidden_error
      (exact_model input) (floating_model input))"

definition rounding_relation ::
  "real \<Rightarrow> (real vector \<Rightarrow> real vector) \<Rightarrow>
   (real vector \<Rightarrow> real vector) \<Rightarrow> bool" where
  "rounding_relation rounding_error exact_operator floating_operator \<longleftrightarrow>
    0 \<le> rounding_error \<and>
    (\<forall>x. vector_error_bound rounding_error
      (exact_operator x) (floating_operator x))"

theorem end_to_end_logit_error:
  assumes model:
    "floating_transformer_relation hidden_error exact_model floating_model"
    and lipschitz: "vector_lipschitz L exact_logits"
    and rounding:
      "rounding_relation rounding_error exact_logits floating_logits"
  shows "vector_error_bound (L * hidden_error + rounding_error)
    (exact_logits (exact_model input))
    (floating_logits (floating_model input))"
proof -
  have hidden_nonnegative: "0 \<le> hidden_error"
    using model by (simp add: floating_transformer_relation_def)
  have hidden:
    "vector_error_bound hidden_error (exact_model input) (floating_model input)"
    using model by (simp add: floating_transformer_relation_def)
  have propagated:
    "vector_error_bound (L * hidden_error)
      (exact_logits (exact_model input))
      (exact_logits (floating_model input))"
    using lipschitz hidden hidden_nonnegative
    by (auto simp: vector_lipschitz_def)
  have rounded:
    "vector_error_bound rounding_error
      (exact_logits (floating_model input))
      (floating_logits (floating_model input))"
    using rounding by (simp add: rounding_relation_def)
  show ?thesis
    by (rule vector_error_bound_triangle[OF propagated rounded])
qed

corollary next_token_logit_error:
  assumes model:
    "floating_transformer_relation hidden_error exact_model floating_model"
    and projection:
      "vector_lipschitz L (next_token_logits vocabulary_size W_vocabulary)"
    and rounding:
      "rounding_relation rounding_error
        (next_token_logits vocabulary_size W_vocabulary) floating_logits"
  shows "vector_error_bound (L * hidden_error + rounding_error)
    (next_token_logits vocabulary_size W_vocabulary (exact_model input))
    (floating_logits (floating_model input))"
  by (rule end_to_end_logit_error[OF model projection rounding])

end
