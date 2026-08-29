theory Decoding_Policies
  imports Modern_Decoder_Components
begin

section \<open>Concrete Decoding Policies\<close>

fun first_argmax :: "real vector \<Rightarrow> nat" where
  "first_argmax [] = 0"
| "first_argmax (x # xs) =
    (if xs = [] then 0
     else let i = first_argmax xs
          in if x \<ge> xs ! i then 0 else Suc i)"

theorem first_argmax_bound:
  assumes "xs \<noteq> []"
  shows "first_argmax xs < length xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    have tail: "first_argmax xs < length xs"
      by (rule Cons.IH) (simp add: Cons)
    show ?thesis
      using tail by (simp add: Cons Let_def split: if_splits)
  qed
qed

theorem first_argmax_maximal:
  assumes nonempty: "xs \<noteq> []"
    and index: "i < length xs"
  shows "xs ! i \<le> xs ! first_argmax xs"
  using nonempty index
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    then have "i = 0"
      using Cons.prems(2) by simp
    with Nil show ?thesis by simp
  next
    case (Cons y ys)
    have tail_nonempty: "xs \<noteq> []"
      by (simp add: Cons)
    let ?j = "first_argmax xs"
    have j_bound: "?j < length xs"
      by (rule first_argmax_bound[OF tail_nonempty])
    have tail_max:
      "\<And>k. k < length xs \<Longrightarrow> xs ! k \<le> xs ! ?j"
      by (rule Cons.IH[OF tail_nonempty])
    show ?thesis
    proof (cases i)
      case 0
      show ?thesis
      proof (cases "x \<ge> xs ! ?j")
        case True
        then show ?thesis
          using 0 tail_nonempty by (simp add: Let_def)
      next
        case False
        then show ?thesis
          using 0 j_bound tail_nonempty by (simp add: Let_def)
      qed
    next
      case (Suc k)
      have k_bound: "k < length xs"
        using Cons.prems(2) Suc by simp
      have k_max: "xs ! k \<le> xs ! ?j"
        by (rule tail_max[OF k_bound])
      show ?thesis
      proof (cases "x \<ge> xs ! ?j")
        case True
        then show ?thesis
          using Suc k_max j_bound tail_nonempty by (simp add: Let_def)
      next
        case False
        then show ?thesis
          using Suc k_max j_bound tail_nonempty by (simp add: Let_def)
      qed
    qed
  qed
qed

corollary first_argmax_is_valid_selector:
  assumes "0 < vocabulary_size"
  shows "valid_token_selector vocabulary_size first_argmax"
  unfolding valid_token_selector_def
proof (intro allI impI)
  fix distribution :: "real vector"
  assume length: "length distribution = vocabulary_size"
  then have nonempty: "distribution \<noteq> []"
    using assms by auto
  have bounded: "first_argmax distribution < length distribution"
    by (rule first_argmax_bound[where xs=distribution]) (rule nonempty)
  from bounded length
  show "first_argmax distribution < vocabulary_size" by simp
qed

definition temperature_logits :: "real \<Rightarrow> real vector \<Rightarrow> real vector" where
  "temperature_logits temperature logits = map (\<lambda>z. z / temperature) logits"

definition temperature_distribution ::
  "real \<Rightarrow> real vector \<Rightarrow> real vector" where
  "temperature_distribution temperature logits =
    list_softmax (temperature_logits temperature logits)"

lemma length_temperature_distribution [simp]:
  "length (temperature_distribution temperature logits) = length logits"
  by (simp add: temperature_distribution_def temperature_logits_def)

theorem temperature_distribution_normalized:
  assumes "logits \<noteq> []"
  shows "sum_list (temperature_distribution temperature logits) = 1"
  using assms
  by (simp add: temperature_distribution_def temperature_logits_def
      list_softmax_normalized)

theorem temperature_distribution_positive:
  assumes "logits \<noteq> []" "i < length logits"
  shows "0 < temperature_distribution temperature logits ! i"
proof -
  have nonempty: "temperature_logits temperature logits \<noteq> []"
    using assms(1) by (simp add: temperature_logits_def)
  have index: "i < length (list_softmax (temperature_logits temperature logits))"
    using assms(2) by (simp add: temperature_logits_def)
  have member:
    "list_softmax (temperature_logits temperature logits) ! i \<in>
      set (list_softmax (temperature_logits temperature logits))"
    by (rule nth_mem[OF index])
  have "0 < list_softmax (temperature_logits temperature logits) ! i"
    by (rule list_softmax_positive[OF nonempty member])
  then show ?thesis
    by (simp add: temperature_distribution_def)
qed

corollary greedy_generate_steps_preserves_vocabulary:
  assumes "0 < vocabulary_size"
    and "tokens_in_vocabulary vocabulary_size (fst state)"
    and "fst state \<noteq> []"
  shows "tokens_in_vocabulary vocabulary_size
    (fst (generate_steps n first_argmax layers embedding vocabulary_size
      W_vocabulary state))"
  apply (rule generate_steps_preserves_vocabulary)
  using assms first_argmax_is_valid_selector by blast+

end
