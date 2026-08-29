theory Prefix_Sequences
  imports Main
begin

section \<open>Prefix-Local Sequence Operators\<close>

text \<open>
  Decoder inference is causal when equal input prefixes produce equal output
  prefixes.  This theory isolates that property from any particular tensor or
  arithmetic representation.
\<close>

definition prefix_eq :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "prefix_eq n xs ys \<longleftrightarrow> take n xs = take n ys"

definition causal :: "('a list \<Rightarrow> 'b list) \<Rightarrow> bool" where
  "causal F \<longleftrightarrow>
    (\<forall>n xs ys. prefix_eq n xs ys \<longrightarrow> prefix_eq n (F xs) (F ys))"

lemma prefix_eq_refl [simp]: "prefix_eq n xs xs"
  by (simp add: prefix_eq_def)

lemma prefix_eq_sym: "prefix_eq n xs ys \<Longrightarrow> prefix_eq n ys xs"
  by (simp add: prefix_eq_def)

lemma prefix_eq_trans:
  "prefix_eq n xs ys \<Longrightarrow> prefix_eq n ys zs \<Longrightarrow> prefix_eq n xs zs"
  by (simp add: prefix_eq_def)

lemma prefix_eq_mono:
  assumes "prefix_eq n xs ys" "m \<le> n"
  shows "prefix_eq m xs ys"
proof -
  have "take m xs = take m (take n xs)"
    using assms(2) by simp
  also have "... = take m (take n ys)"
    using assms(1) by (simp add: prefix_eq_def)
  also have "... = take m ys"
    using assms(2) by simp
  finally show ?thesis
    by (simp add: prefix_eq_def)
qed

lemma causalI:
  assumes "\<And>n xs ys. take n xs = take n ys \<Longrightarrow> take n (F xs) = take n (F ys)"
  shows "causal F"
  unfolding causal_def prefix_eq_def
proof (intro allI impI)
  fix n :: nat and xs ys :: "'a list"
  assume "take n xs = take n ys"
  then show "take n (F xs) = take n (F ys)"
    by (rule assms)
qed

lemma causalD:
  assumes "causal F" "take n xs = take n ys"
  shows "take n (F xs) = take n (F ys)"
  using assms unfolding causal_def prefix_eq_def by blast

lemma causal_id [simp]: "causal id"
  by (rule causalI) simp

lemma causal_map [simp]: "causal (map f)"
proof (rule causalI)
  fix n :: nat and xs ys :: "'a list"
  assume eq: "take n xs = take n ys"
  have "map f (take n xs) = map f (take n ys)"
    using eq by simp
  then show "take n (map f xs) = take n (map f ys)"
    by (simp only: take_map)
qed

lemma causal_comp:
  assumes "causal F" "causal G"
  shows "causal (G \<circ> F)"
proof (rule causalI)
  fix n :: nat and xs ys :: "'a list"
  assume eq: "take n xs = take n ys"
  have f_eq: "take n (F xs) = take n (F ys)"
    by (rule causalD[OF assms(1) eq])
  have g_eq: "take n (G (F xs)) = take n (G (F ys))"
    by (rule causalD[OF assms(2) f_eq])
  from g_eq show "take n ((G \<circ> F) xs) = take n ((G \<circ> F) ys)"
    by simp
qed

fun apply_blocks :: "('a list \<Rightarrow> 'a list) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "apply_blocks [] xs = xs"
| "apply_blocks (F # Fs) xs = apply_blocks Fs (F xs)"

lemma causal_apply_blocks:
  assumes "\<forall>F \<in> set Fs. causal F"
  shows "causal (apply_blocks Fs)"
  using assms
proof (induction Fs)
  case Nil
  show ?case by (rule causalI) simp
next
  case (Cons F Fs)
  have cF: "causal F" using Cons.prems by simp
  have cFs: "causal (apply_blocks Fs)" using Cons.IH Cons.prems by simp
  have comp: "causal (apply_blocks Fs \<circ> F)"
    using causal_comp[OF cF cFs] .
  have eq: "apply_blocks (F # Fs) = apply_blocks Fs \<circ> F"
    by (rule ext) simp
  show ?case
    using comp by (subst eq)
qed

end
