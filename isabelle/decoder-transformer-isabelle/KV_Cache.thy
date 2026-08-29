theory KV_Cache
  imports Causal_Attention
begin

section \<open>Exact Key--Value Cache Refinement\<close>

record ('k, 'v) kv_cache =
  cache_keys :: "'k list"
  cache_values :: "'v list"

definition empty_cache :: "('k, 'v) kv_cache" where
  "empty_cache = \<lparr>cache_keys = [], cache_values = []\<rparr>"

definition cache_of ::
  "('x \<Rightarrow> 'k) \<Rightarrow> ('x \<Rightarrow> 'v) \<Rightarrow> 'x list \<Rightarrow> ('k, 'v) kv_cache" where
  "cache_of K V xs = \<lparr>cache_keys = map K xs, cache_values = map V xs\<rparr>"

definition cache_matches ::
  "('x \<Rightarrow> 'k) \<Rightarrow> ('x \<Rightarrow> 'v) \<Rightarrow> 'x list \<Rightarrow> ('k, 'v) kv_cache \<Rightarrow> bool" where
  "cache_matches K V xs C \<longleftrightarrow> C = cache_of K V xs"

definition cached_step ::
  "('x \<Rightarrow> 'q) \<Rightarrow>
   ('x \<Rightarrow> 'k) \<Rightarrow>
   ('x \<Rightarrow> 'v) \<Rightarrow>
   ('q \<Rightarrow> 'k list \<Rightarrow> 'v list \<Rightarrow> 'o) \<Rightarrow>
   ('k, 'v) kv_cache \<Rightarrow> 'x \<Rightarrow> ('k, 'v) kv_cache \<times> 'o" where
  "cached_step Q K V A C x =
    (let ks = cache_keys C @ [K x];
         vs = cache_values C @ [V x]
     in (\<lparr>cache_keys = ks, cache_values = vs\<rparr>, A (Q x) ks vs))"

fun cached_run ::
  "('x \<Rightarrow> 'q) \<Rightarrow>
   ('x \<Rightarrow> 'k) \<Rightarrow>
   ('x \<Rightarrow> 'v) \<Rightarrow>
   ('q \<Rightarrow> 'k list \<Rightarrow> 'v list \<Rightarrow> 'o) \<Rightarrow>
   ('k, 'v) kv_cache \<Rightarrow> 'x list \<Rightarrow> ('k, 'v) kv_cache \<times> 'o list" where
  "cached_run Q K V A C [] = (C, [])"
| "cached_run Q K V A C (x # xs) =
    (let (C', y) = cached_step Q K V A C x;
         (C'', ys) = cached_run Q K V A C' xs
     in (C'', y # ys))"

definition cached_attention ::
  "('x \<Rightarrow> 'q) \<Rightarrow>
   ('x \<Rightarrow> 'k) \<Rightarrow>
   ('x \<Rightarrow> 'v) \<Rightarrow>
   ('q \<Rightarrow> 'k list \<Rightarrow> 'v list \<Rightarrow> 'o) \<Rightarrow>
   'x list \<Rightarrow> 'o list" where
  "cached_attention Q K V A xs = snd (cached_run Q K V A empty_cache xs)"

lemma empty_cache_is_cache_of [simp]: "empty_cache = cache_of K V []"
  by (simp add: empty_cache_def cache_of_def)

lemma cached_step_refines_full:
  assumes "cache_matches K V prefix C"
  shows "cached_step Q K V A C x =
    (cache_of K V (prefix @ [x]),
      A (Q x) (map K (prefix @ [x])) (map V (prefix @ [x])))"
  using assms
  by (simp add: cached_step_def cache_matches_def cache_of_def Let_def)

theorem cached_run_refines_full:
  assumes "cache_matches K V prefix C"
  shows "cached_run Q K V A C xs =
    (cache_of K V (prefix @ xs), causal_attention_from Q K V A prefix xs)"
  using assms
proof (induction xs arbitrary: prefix C)
  case Nil
  then show ?case by (simp add: cache_matches_def)
next
  case (Cons x xs)
  have step:
    "cached_step Q K V A C x =
      (cache_of K V (prefix @ [x]),
        A (Q x) (map K (prefix @ [x])) (map V (prefix @ [x])))"
    by (rule cached_step_refines_full[OF Cons.prems])
  have match:
    "cache_matches K V (prefix @ [x]) (cache_of K V (prefix @ [x]))"
    by (simp add: cache_matches_def)
  have tail:
    "cached_run Q K V A (cache_of K V (prefix @ [x])) xs =
      (cache_of K V ((prefix @ [x]) @ xs),
        causal_attention_from Q K V A (prefix @ [x]) xs)"
    by (rule Cons.IH[OF match])
  show ?case
    by (simp add: step tail append_assoc cached_run.simps Let_def)
qed

theorem cached_attention_eq_full_attention:
  "cached_attention Q K V A xs = causal_attention Q K V A xs"
  using cached_run_refines_full[of K V "[]" empty_cache Q A xs]
  by (simp add: cache_matches_def cached_attention_def causal_attention_def)

theorem final_cache_eq_full_projections:
  "fst (cached_run Q K V A empty_cache xs) = cache_of K V xs"
  using cached_run_refines_full[of K V "[]" empty_cache Q A xs]
  by (simp add: cache_matches_def)

corollary cached_attention_is_causal:
  "causal (cached_attention Q K V A)"
  by (simp add: cached_attention_eq_full_attention causalI causal_attention_take)

end
