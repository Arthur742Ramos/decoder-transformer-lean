theory Causal_Attention
  imports Prefix_Sequences
begin

section \<open>Parametric Causal Attention\<close>

text \<open>
  The query, key, and value projections and the attention aggregator are left
  parametric.  Consequently, the structural causality theorem does not depend
  on a choice of scalar field, softmax implementation, number of heads, or
  tensor representation.
\<close>

fun causal_attention_from ::
  "('x \<Rightarrow> 'q) \<Rightarrow>
   ('x \<Rightarrow> 'k) \<Rightarrow>
   ('x \<Rightarrow> 'v) \<Rightarrow>
   ('q \<Rightarrow> 'k list \<Rightarrow> 'v list \<Rightarrow> 'o) \<Rightarrow>
   'x list \<Rightarrow> 'x list \<Rightarrow> 'o list" where
  "causal_attention_from Q K V A prefix [] = []"
| "causal_attention_from Q K V A prefix (x # xs) =
    A (Q x) (map K (prefix @ [x])) (map V (prefix @ [x])) #
      causal_attention_from Q K V A (prefix @ [x]) xs"

definition causal_attention ::
  "('x \<Rightarrow> 'q) \<Rightarrow>
   ('x \<Rightarrow> 'k) \<Rightarrow>
   ('x \<Rightarrow> 'v) \<Rightarrow>
   ('q \<Rightarrow> 'k list \<Rightarrow> 'v list \<Rightarrow> 'o) \<Rightarrow>
   'x list \<Rightarrow> 'o list" where
  "causal_attention Q K V A = causal_attention_from Q K V A []"

lemma length_causal_attention_from [simp]:
  "length (causal_attention_from Q K V A prefix xs) = length xs"
  by (induction xs arbitrary: prefix) simp_all

lemma length_causal_attention [simp]:
  "length (causal_attention Q K V A xs) = length xs"
  by (simp add: causal_attention_def)

lemma causal_attention_from_append:
  "causal_attention_from Q K V A prefix (xs @ ys) =
    causal_attention_from Q K V A prefix xs @
      causal_attention_from Q K V A (prefix @ xs) ys"
  by (induction xs arbitrary: prefix) (simp_all add: append_assoc)

lemma causal_attention_append:
  "causal_attention Q K V A (xs @ ys) =
    causal_attention Q K V A xs @ causal_attention_from Q K V A xs ys"
  by (simp add: causal_attention_def causal_attention_from_append)

lemma causal_attention_take:
  "take n (causal_attention Q K V A xs) =
    causal_attention Q K V A (take n xs)"
proof (cases "n \<le> length xs")
  case True
  have split:
    "causal_attention Q K V A xs =
      causal_attention Q K V A (take n xs) @
        causal_attention_from Q K V A (take n xs) (drop n xs)"
    using causal_attention_append[
      where Q=Q and K=K and V=V and A=A
        and xs="take n xs" and ys="drop n xs"]
    by simp
  have prefix_length:
    "length (causal_attention Q K V A (take n xs)) = n"
    using True by simp
  have take_prefix:
    "take n (causal_attention Q K V A (take n xs)) =
      causal_attention Q K V A (take n xs)"
    using prefix_length by simp
  show ?thesis
    by (simp only: split take_append prefix_length min.idem take_prefix
        diff_self_eq_0 take_0 append_Nil2)
next
  case False
  then show ?thesis by simp
qed

theorem causal_attention_is_causal:
  "causal (causal_attention Q K V A)"
  by (simp add: causalI causal_attention_take)

theorem causal_attention_independence:
  assumes "i < length xs" "i < length ys"
    and "take (Suc i) xs = take (Suc i) ys"
  shows "causal_attention Q K V A xs ! i =
    causal_attention Q K V A ys ! i"
proof -
  have prefix_eq: "take (Suc i) (causal_attention Q K V A xs) =
      take (Suc i) (causal_attention Q K V A ys)"
    using assms(3) causal_attention_is_causal causalD by blast
  have nth_eq:
    "take (Suc i) (causal_attention Q K V A xs) ! i =
      take (Suc i) (causal_attention Q K V A ys) ! i"
    by (rule arg_cong[OF prefix_eq])
  have left:
    "take (Suc i) (causal_attention Q K V A xs) ! i =
      causal_attention Q K V A xs ! i"
    using assms(1) by simp
  have right:
    "take (Suc i) (causal_attention Q K V A ys) ! i =
      causal_attention Q K V A ys ! i"
    using assms(2) by simp
  from nth_eq left right show ?thesis by simp
qed

end
