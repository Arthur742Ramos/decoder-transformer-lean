theory GPT_Neo_Generation
  imports GPT_Neo_Model Decoding_Policies
begin

section \<open>GPT-Neo Autoregressive Generation\<close>

text \<open>
  A generation state keeps the complete token history together with a cache
  for its pending-prefix history.  The final token is evaluated on demand,
  which makes the state transition agree with the full-model logit vector and
  leaves the updated cache ready for the next token.  Absolute learned
  positions impose an explicit finite-context budget on the refinement.
\<close>

type_synonym gpt_neo_generation_state =
  "nat list \<times> gpt_neo_transformer_cache"

definition gpt_neo_generation_state_valid ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow>
   gpt_neo_generation_state \<Rightarrow> bool" where
  "gpt_neo_generation_state_valid m position state \<longleftrightarrow>
    valid_gpt_neo_model m \<and>
    fst state \<noteq> [] \<and>
    tokens_in_vocabulary (gpt_neo_model_vocabulary_size m) (fst state) \<and>
    position + length (fst state) \<le> gpt_neo_model_max_position m \<and>
    gpt_neo_generation_cache_matches m position
      (fst state) (snd state)"

definition gpt_neo_generation_transition ::
  "(real vector \<Rightarrow> nat) \<Rightarrow> gpt_neo_model_parameters \<Rightarrow>
   nat \<Rightarrow> gpt_neo_generation_state \<Rightarrow>
   gpt_neo_generation_state" where
  "gpt_neo_generation_transition select m position state =
    (let tokens = fst state;
         evaluation = gpt_neo_cached_model_evaluate m position
           tokens (snd state);
         next = select (fst evaluation)
     in (tokens @ [next], snd evaluation))"

lemma gpt_neo_generation_transition_tokens:
  "fst (gpt_neo_generation_transition select m position state) =
    fst state @
      [select (fst (gpt_neo_cached_model_evaluate m position
        (fst state) (snd state)))]"
  by (simp add: gpt_neo_generation_transition_def Let_def)

lemma gpt_neo_generation_transition_cache:
  "snd (gpt_neo_generation_transition select m position state) =
    snd (gpt_neo_cached_model_evaluate m position
      (fst state) (snd state))"
  by (simp add: gpt_neo_generation_transition_def Let_def)

definition gpt_neo_full_next_token ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "gpt_neo_full_next_token m position tokens =
    first_argmax (last (gpt_neo_full_model_logits m position tokens))"

fun gpt_neo_full_generate_steps ::
  "nat \<Rightarrow> gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow>
   nat list \<Rightarrow> nat list" where
  "gpt_neo_full_generate_steps 0 m position tokens = tokens"
| "gpt_neo_full_generate_steps (Suc n) m position tokens =
    gpt_neo_full_generate_steps n m position
      (tokens @ [gpt_neo_full_next_token m position tokens])"

lemma gpt_neo_cached_model_evaluate_logits_length:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le> gpt_neo_model_max_position m"
    and match: "gpt_neo_generation_cache_matches m position tokens caches"
  shows "length (fst
      (gpt_neo_cached_model_evaluate m position tokens caches)) =
      gpt_neo_model_vocabulary_size m"
proof -
  have full_shape:
    "matrix_shape (length tokens)
      (gpt_neo_model_vocabulary_size m)
      (gpt_neo_full_model_logits m position tokens)"
    by (rule valid_gpt_neo_full_model_logits_shape[
      OF valid token_bounds position_bound])
  have full_nonempty:
    "gpt_neo_full_model_logits m position tokens \<noteq> []"
  proof -
    have full_length:
      "length (gpt_neo_full_model_logits m position tokens) =
        length tokens"
      by (simp add: gpt_neo_full_model_logits_def
          gpt_neo_full_hidden_def)
    then show ?thesis
      using tokens by auto
  qed
  have last_shape:
    "vector_shape (gpt_neo_model_vocabulary_size m)
      (last (gpt_neo_full_model_logits m position tokens))"
    using matrix_shape_row[OF full_shape]
      last_in_set[OF full_nonempty]
    by (simp add: vector_shape_def)
  have equality:
    "fst (gpt_neo_cached_model_evaluate m position tokens caches) =
      last (gpt_neo_full_model_logits m position tokens)"
    by (rule gpt_neo_cached_model_evaluate_correct(1)
      [OF valid tokens token_bounds position_bound match])
  show ?thesis
    using last_shape equality
    by (simp add: vector_shape_def)
qed

theorem gpt_neo_generation_transition_valid:
  assumes state_valid:
    "gpt_neo_generation_state_valid m position state"
    and selector:
      "valid_token_selector
        (gpt_neo_model_vocabulary_size m) select"
    and room:
      "position + Suc (length (fst state)) \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_generation_state_valid m position
    (gpt_neo_generation_transition select m position state)"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have tokens_nonempty:
    "fst state \<noteq> []"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have tokens_bounded:
    "tokens_in_vocabulary
      (gpt_neo_model_vocabulary_size m) (fst state)"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have position_bound:
    "position + length (fst state) \<le>
      gpt_neo_model_max_position m"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have cache_match:
    "gpt_neo_generation_cache_matches m position
      (fst state) (snd state)"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have token_bounds:
    "\<forall>token \<in> set (fst state).
      token < gpt_neo_model_vocabulary_size m"
    using tokens_bounded
    by (simp add: tokens_in_vocabulary_def)
  have logits_length:
    "length (fst (gpt_neo_cached_model_evaluate m position
      (fst state) (snd state))) =
      gpt_neo_model_vocabulary_size m"
    by (rule gpt_neo_cached_model_evaluate_logits_length[
      OF model_valid tokens_nonempty token_bounds position_bound cache_match])
  have selected:
    "select (fst (gpt_neo_cached_model_evaluate m position
      (fst state) (snd state))) <
      gpt_neo_model_vocabulary_size m"
    using selector logits_length
    by (auto simp: valid_token_selector_def)
  have evaluated_cache:
    "gpt_neo_model_cache_matches m position (fst state)
      (snd (gpt_neo_cached_model_evaluate m position
        (fst state) (snd state)))"
    by (rule gpt_neo_cached_model_evaluate_correct(2)[
      OF model_valid tokens_nonempty token_bounds position_bound cache_match])
  have new_tokens:
    "fst (gpt_neo_generation_transition select m position state) =
      fst state @
        [select (fst (gpt_neo_cached_model_evaluate m position
          (fst state) (snd state)))]"
    by (rule gpt_neo_generation_transition_tokens)
  have new_cache:
    "snd (gpt_neo_generation_transition select m position state) =
      snd (gpt_neo_cached_model_evaluate m position
        (fst state) (snd state))"
    by (rule gpt_neo_generation_transition_cache)
  have new_tokens_nonempty:
    "fst (gpt_neo_generation_transition select m position state) \<noteq> []"
    using new_tokens tokens_nonempty by simp
  have new_tokens_bounded:
    "tokens_in_vocabulary
      (gpt_neo_model_vocabulary_size m)
      (fst (gpt_neo_generation_transition select m position state))"
    using new_tokens tokens_bounded selected
    by (simp add: tokens_in_vocabulary_def)
  have new_position_bound:
    "position + length
      (fst (gpt_neo_generation_transition select m position state)) \<le>
      gpt_neo_model_max_position m"
    using new_tokens room
    by simp
  have new_cache_match:
    "gpt_neo_generation_cache_matches m position
      (fst (gpt_neo_generation_transition select m position state))
      (snd (gpt_neo_generation_transition select m position state))"
    using new_tokens new_cache evaluated_cache tokens_nonempty
    by (simp add: gpt_neo_generation_cache_matches_def)
  show ?thesis
    using model_valid new_tokens_nonempty new_tokens_bounded
      new_position_bound new_cache_match
    by (simp add: gpt_neo_generation_state_valid_def)
qed

fun gpt_neo_generate_steps ::
  "nat \<Rightarrow> (real vector \<Rightarrow> nat) \<Rightarrow>
   gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow>
   gpt_neo_generation_state \<Rightarrow> gpt_neo_generation_state" where
  "gpt_neo_generate_steps 0 select m position state = state"
| "gpt_neo_generate_steps (Suc n) select m position state =
    gpt_neo_generate_steps n select m position
      (gpt_neo_generation_transition select m position state)"

theorem gpt_neo_generate_steps_valid:
  assumes state_valid:
    "gpt_neo_generation_state_valid m position state"
    and selector:
      "valid_token_selector
        (gpt_neo_model_vocabulary_size m) select"
    and room:
      "position + length (fst state) + n \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_generation_state_valid m position
    (gpt_neo_generate_steps n select m position state)"
  using state_valid room
proof (induction n arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have transition_room:
    "position + Suc (length (fst state)) \<le>
      gpt_neo_model_max_position m"
    using Suc.prems(2)
    by (simp add: add.assoc)
  have next_valid:
    "gpt_neo_generation_state_valid m position
      (gpt_neo_generation_transition select m position state)"
    by (rule gpt_neo_generation_transition_valid[
      OF Suc.prems(1) selector transition_room])
  have next_room:
    "position +
        length (fst (gpt_neo_generation_transition
          select m position state)) + n \<le>
      gpt_neo_model_max_position m"
    using Suc.prems(2)
    by (simp add: gpt_neo_generation_transition_tokens add.assoc)
  show ?case
    by (simp only: gpt_neo_generate_steps.simps)
      (rule Suc.IH[OF next_valid next_room])
qed

corollary gpt_neo_greedy_generate_steps_valid:
  assumes state_valid:
    "gpt_neo_generation_state_valid m position state"
    and room:
      "position + length (fst state) + n \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_generation_state_valid m position
    (gpt_neo_generate_steps n first_argmax m position state)"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have vocabulary_positive:
    "0 < gpt_neo_model_vocabulary_size m"
    by (rule valid_gpt_neo_model_dimensions(2)[OF model_valid])
  show ?thesis
    apply (rule gpt_neo_generate_steps_valid[OF state_valid _ room])
    by (rule first_argmax_is_valid_selector[OF vocabulary_positive])
qed

theorem gpt_neo_generation_transition_full:
  assumes state_valid:
    "gpt_neo_generation_state_valid m position state"
  shows "fst (gpt_neo_generation_transition first_argmax m position state) =
    fst state @ [gpt_neo_full_next_token m position (fst state)]"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have tokens_nonempty:
    "fst state \<noteq> []"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have token_bounds:
    "\<forall>token \<in> set (fst state).
      token < gpt_neo_model_vocabulary_size m"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def
      tokens_in_vocabulary_def)
  have position_bound:
    "position + length (fst state) \<le>
      gpt_neo_model_max_position m"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have cache_match:
    "gpt_neo_generation_cache_matches m position
      (fst state) (snd state)"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have evaluation:
    "fst (gpt_neo_cached_model_evaluate m position
      (fst state) (snd state)) =
      last (gpt_neo_full_model_logits m position (fst state))"
    by (rule gpt_neo_cached_model_evaluate_correct(1)
      [OF model_valid tokens_nonempty token_bounds position_bound cache_match])
  have transition_tokens:
    "fst (gpt_neo_generation_transition first_argmax m position state) =
      fst state @
        [first_argmax (fst (gpt_neo_cached_model_evaluate m position
          (fst state) (snd state)))]"
    by (rule gpt_neo_generation_transition_tokens)
  show ?thesis
    unfolding gpt_neo_full_next_token_def
    using transition_tokens evaluation
    by (simp add: transition_tokens evaluation)
qed

theorem gpt_neo_greedy_generate_steps_eq_full:
  assumes state_valid:
    "gpt_neo_generation_state_valid m position state"
    and room:
      "position + length (fst state) + n \<le>
        gpt_neo_model_max_position m"
  shows "fst (gpt_neo_generate_steps n first_argmax m position state) =
    gpt_neo_full_generate_steps n m position (fst state)"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_generation_state_valid_def)
  have vocabulary_positive:
    "0 < gpt_neo_model_vocabulary_size m"
    by (rule valid_gpt_neo_model_dimensions(2)[OF model_valid])
  have selector:
    "valid_token_selector
      (gpt_neo_model_vocabulary_size m) first_argmax"
    by (rule first_argmax_is_valid_selector[OF vocabulary_positive])
  show ?thesis
  using state_valid room
  proof (induction n arbitrary: state)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have transition_room:
      "position + Suc (length (fst state)) \<le>
        gpt_neo_model_max_position m"
      using Suc.prems(2)
      by (simp add: add.assoc)
    have next_valid:
      "gpt_neo_generation_state_valid m position
        (gpt_neo_generation_transition first_argmax m position state)"
      by (rule gpt_neo_generation_transition_valid[
        OF Suc.prems(1) selector transition_room])
    have next_room:
      "position +
          length (fst (gpt_neo_generation_transition
            first_argmax m position state)) + n \<le>
        gpt_neo_model_max_position m"
      using Suc.prems(2)
      by (simp add: gpt_neo_generation_transition_tokens add.assoc)
    have recursive:
      "fst (gpt_neo_generate_steps n first_argmax m position
          (gpt_neo_generation_transition first_argmax m position state)) =
        gpt_neo_full_generate_steps n m position
          (fst (gpt_neo_generation_transition
            first_argmax m position state))"
      by (rule Suc.IH[OF next_valid next_room])
    have transition_full:
      "fst (gpt_neo_generation_transition first_argmax m position state) =
        fst state @ [gpt_neo_full_next_token m position (fst state)]"
      by (rule gpt_neo_generation_transition_full[OF Suc.prems(1)])
    have recursive_rewritten:
      "fst (gpt_neo_generate_steps (Suc n) first_argmax m position state) =
        gpt_neo_full_generate_steps n m position
          (fst state @ [gpt_neo_full_next_token m position (fst state)])"
      using recursive transition_full
      by (simp add: gpt_neo_generate_steps.simps recursive transition_full)
    show ?case
      by (simp only: gpt_neo_full_generate_steps.simps)
        (rule recursive_rewritten)
  qed
qed

definition gpt_neo_initialized_generation_state ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_generation_state" where
  "gpt_neo_initialized_generation_state m position tokens =
    (tokens,
     snd (gpt_neo_cached_prompt m position (butlast tokens)))"

theorem gpt_neo_initialized_generation_state_valid:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_generation_state_valid m position
    (gpt_neo_initialized_generation_state m position tokens)"
proof -
  have prefix_bounds:
    "\<forall>token \<in> set (butlast tokens).
      token < gpt_neo_model_vocabulary_size m"
    using token_bounds
    by (auto simp: in_set_butlastD)
  have prefix_position:
    "position + length (butlast tokens) \<le>
      gpt_neo_model_max_position m"
    using position_bound by simp
  have cache:
    "gpt_neo_model_cache_matches m position (butlast tokens)
      (snd (gpt_neo_cached_prompt m position (butlast tokens)))"
    by (rule gpt_neo_cached_prompt_correct(2)[
      OF valid prefix_bounds prefix_position])
  have tokens_vocabulary:
    "tokens_in_vocabulary
      (gpt_neo_model_vocabulary_size m) tokens"
    using token_bounds
    by (simp add: tokens_in_vocabulary_def)
  have generation_cache:
    "gpt_neo_generation_cache_matches m position tokens
      (snd (gpt_neo_cached_prompt m position (butlast tokens)))"
    using cache tokens
    by (simp add: gpt_neo_generation_cache_matches_def)
  show ?thesis
    unfolding gpt_neo_generation_state_valid_def
      gpt_neo_initialized_generation_state_def
    using valid tokens tokens_vocabulary position_bound generation_cache
    by simp
qed

definition gpt_neo_bounded_generation_state_valid ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow>
   gpt_neo_generation_state \<Rightarrow> bool" where
  "gpt_neo_bounded_generation_state_valid m position state \<longleftrightarrow>
    valid_gpt_neo_model m \<and>
    fst state \<noteq> [] \<and>
    tokens_in_vocabulary (gpt_neo_model_vocabulary_size m) (fst state) \<and>
    position + length (fst state) \<le> gpt_neo_model_max_position m \<and>
    gpt_neo_bounded_generation_cache_matches m position
      (fst state) (snd state)"

definition gpt_neo_bounded_generation_transition ::
  "(real vector \<Rightarrow> nat) \<Rightarrow> gpt_neo_model_parameters \<Rightarrow>
   nat \<Rightarrow> gpt_neo_generation_state \<Rightarrow>
   gpt_neo_generation_state" where
  "gpt_neo_bounded_generation_transition select m position state =
    (let tokens = fst state;
         evaluation = gpt_neo_bounded_cached_model_evaluate m position
           tokens (snd state);
         next = select (fst evaluation)
     in (tokens @ [next], snd evaluation))"

lemma gpt_neo_bounded_generation_transition_tokens:
  "fst (gpt_neo_bounded_generation_transition select m position state) =
    fst state @
      [select (fst (gpt_neo_bounded_cached_model_evaluate m position
        (fst state) (snd state)))]"
  by (simp add: gpt_neo_bounded_generation_transition_def Let_def)

lemma gpt_neo_bounded_generation_transition_cache:
  "snd (gpt_neo_bounded_generation_transition select m position state) =
    snd (gpt_neo_bounded_cached_model_evaluate m position
      (fst state) (snd state))"
  by (simp add: gpt_neo_bounded_generation_transition_def Let_def)

theorem gpt_neo_bounded_generation_transition_valid:
  assumes state_valid:
    "gpt_neo_bounded_generation_state_valid m position state"
    and selector:
      "valid_token_selector
        (gpt_neo_model_vocabulary_size m) select"
    and room:
      "position + Suc (length (fst state)) \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_bounded_generation_state_valid m position
    (gpt_neo_bounded_generation_transition select m position state)"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have tokens_nonempty:
    "fst state \<noteq> []"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have tokens_bounded:
    "tokens_in_vocabulary
      (gpt_neo_model_vocabulary_size m) (fst state)"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have position_bound:
    "position + length (fst state) \<le>
      gpt_neo_model_max_position m"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have cache_match:
    "gpt_neo_bounded_generation_cache_matches m position
      (fst state) (snd state)"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have token_bounds:
    "\<forall>token \<in> set (fst state).
      token < gpt_neo_model_vocabulary_size m"
    using tokens_bounded
    by (simp add: tokens_in_vocabulary_def)
  have logits_length:
    "length (fst (gpt_neo_bounded_cached_model_evaluate m position
      (fst state) (snd state))) =
      gpt_neo_model_vocabulary_size m"
    by (rule gpt_neo_bounded_cached_model_evaluate_logits_length[
      OF model_valid tokens_nonempty token_bounds position_bound cache_match])
  have selected:
    "select (fst (gpt_neo_bounded_cached_model_evaluate m position
      (fst state) (snd state))) <
      gpt_neo_model_vocabulary_size m"
    using selector logits_length
    by (auto simp: valid_token_selector_def)
  have evaluated_cache:
    "gpt_neo_bounded_model_cache_matches m position (fst state)
      (snd (gpt_neo_bounded_cached_model_evaluate m position
        (fst state) (snd state)))"
    by (rule gpt_neo_bounded_cached_model_evaluate_correct(2)[
      OF model_valid tokens_nonempty token_bounds position_bound cache_match])
  have new_tokens:
    "fst (gpt_neo_bounded_generation_transition select m position state) =
      fst state @
        [select (fst (gpt_neo_bounded_cached_model_evaluate m position
          (fst state) (snd state)))]"
    by (rule gpt_neo_bounded_generation_transition_tokens)
  have new_cache:
    "snd (gpt_neo_bounded_generation_transition select m position state) =
      snd (gpt_neo_bounded_cached_model_evaluate m position
        (fst state) (snd state))"
    by (rule gpt_neo_bounded_generation_transition_cache)
  have new_tokens_nonempty:
    "fst (gpt_neo_bounded_generation_transition select m position state) \<noteq> []"
    using new_tokens tokens_nonempty by simp
  have new_tokens_bounded:
    "tokens_in_vocabulary
      (gpt_neo_model_vocabulary_size m)
      (fst (gpt_neo_bounded_generation_transition select m position state))"
    using new_tokens tokens_bounded selected
    by (simp add: tokens_in_vocabulary_def)
  have new_position_bound:
    "position + length
      (fst (gpt_neo_bounded_generation_transition select m position state)) \<le>
      gpt_neo_model_max_position m"
    using new_tokens room
    by simp
  have new_cache_match:
    "gpt_neo_bounded_generation_cache_matches m position
      (fst (gpt_neo_bounded_generation_transition select m position state))
      (snd (gpt_neo_bounded_generation_transition select m position state))"
    using new_tokens new_cache evaluated_cache tokens_nonempty
    by (simp add: gpt_neo_bounded_generation_cache_matches_def)
  show ?thesis
    using model_valid new_tokens_nonempty new_tokens_bounded
      new_position_bound new_cache_match
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
qed

fun gpt_neo_bounded_generate_steps ::
  "nat \<Rightarrow> (real vector \<Rightarrow> nat) \<Rightarrow>
   gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow>
   gpt_neo_generation_state \<Rightarrow> gpt_neo_generation_state" where
  "gpt_neo_bounded_generate_steps 0 select m position state = state"
| "gpt_neo_bounded_generate_steps (Suc n) select m position state =
    gpt_neo_bounded_generate_steps n select m position
      (gpt_neo_bounded_generation_transition select m position state)"

theorem gpt_neo_bounded_generate_steps_valid:
  assumes state_valid:
    "gpt_neo_bounded_generation_state_valid m position state"
    and selector:
      "valid_token_selector
        (gpt_neo_model_vocabulary_size m) select"
    and room:
      "position + length (fst state) + n \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_bounded_generation_state_valid m position
    (gpt_neo_bounded_generate_steps n select m position state)"
  using state_valid room
proof (induction n arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have transition_room:
    "position + Suc (length (fst state)) \<le>
      gpt_neo_model_max_position m"
    using Suc.prems(2)
    by (simp add: add.assoc)
  have next_valid:
    "gpt_neo_bounded_generation_state_valid m position
      (gpt_neo_bounded_generation_transition select m position state)"
    by (rule gpt_neo_bounded_generation_transition_valid[
      OF Suc.prems(1) selector transition_room])
  have next_room:
    "position +
        length (fst (gpt_neo_bounded_generation_transition
          select m position state)) + n \<le>
      gpt_neo_model_max_position m"
    using Suc.prems(2)
    by (simp add: gpt_neo_bounded_generation_transition_tokens add.assoc)
  show ?case
    by (simp only: gpt_neo_bounded_generate_steps.simps)
      (rule Suc.IH[OF next_valid next_room])
qed

corollary gpt_neo_bounded_greedy_generate_steps_valid:
  assumes state_valid:
    "gpt_neo_bounded_generation_state_valid m position state"
    and room:
      "position + length (fst state) + n \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_bounded_generation_state_valid m position
    (gpt_neo_bounded_generate_steps n first_argmax m position state)"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have vocabulary_positive:
    "0 < gpt_neo_model_vocabulary_size m"
    by (rule valid_gpt_neo_model_dimensions(2)[OF model_valid])
  show ?thesis
    apply (rule gpt_neo_bounded_generate_steps_valid[
      OF state_valid _ room])
    by (rule first_argmax_is_valid_selector[OF vocabulary_positive])
qed

theorem gpt_neo_bounded_generation_transition_full:
  assumes state_valid:
    "gpt_neo_bounded_generation_state_valid m position state"
  shows "fst (gpt_neo_bounded_generation_transition
      first_argmax m position state) =
    fst state @ [gpt_neo_full_next_token m position (fst state)]"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have tokens_nonempty:
    "fst state \<noteq> []"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have token_bounds:
    "\<forall>token \<in> set (fst state).
      token < gpt_neo_model_vocabulary_size m"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def
      tokens_in_vocabulary_def)
  have position_bound:
    "position + length (fst state) \<le>
      gpt_neo_model_max_position m"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have cache_match:
    "gpt_neo_bounded_generation_cache_matches m position
      (fst state) (snd state)"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have evaluation:
    "fst (gpt_neo_bounded_cached_model_evaluate m position
      (fst state) (snd state)) =
      last (gpt_neo_full_model_logits m position (fst state))"
    by (rule gpt_neo_bounded_cached_model_evaluate_correct(1)
      [OF model_valid tokens_nonempty token_bounds position_bound cache_match])
  have transition_tokens:
    "fst (gpt_neo_bounded_generation_transition
        first_argmax m position state) =
      fst state @
        [first_argmax
          (fst (gpt_neo_bounded_cached_model_evaluate m position
            (fst state) (snd state)))]"
    by (rule gpt_neo_bounded_generation_transition_tokens)
  show ?thesis
    unfolding gpt_neo_full_next_token_def
    using transition_tokens evaluation
    by (simp add: transition_tokens evaluation)
qed

theorem gpt_neo_bounded_greedy_generate_steps_eq_full:
  assumes state_valid:
    "gpt_neo_bounded_generation_state_valid m position state"
    and room:
      "position + length (fst state) + n \<le>
        gpt_neo_model_max_position m"
  shows "fst (gpt_neo_bounded_generate_steps n first_argmax
      m position state) =
    gpt_neo_full_generate_steps n m position (fst state)"
proof -
  have model_valid:
    "valid_gpt_neo_model m"
    using state_valid
    by (simp add: gpt_neo_bounded_generation_state_valid_def)
  have vocabulary_positive:
    "0 < gpt_neo_model_vocabulary_size m"
    by (rule valid_gpt_neo_model_dimensions(2)[OF model_valid])
  have selector:
    "valid_token_selector
      (gpt_neo_model_vocabulary_size m) first_argmax"
    by (rule first_argmax_is_valid_selector[OF vocabulary_positive])
  show ?thesis
  using state_valid room
  proof (induction n arbitrary: state)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have transition_room:
      "position + Suc (length (fst state)) \<le>
        gpt_neo_model_max_position m"
      using Suc.prems(2)
      by (simp add: add.assoc)
    have next_valid:
      "gpt_neo_bounded_generation_state_valid m position
        (gpt_neo_bounded_generation_transition
          first_argmax m position state)"
      by (rule gpt_neo_bounded_generation_transition_valid[
        OF Suc.prems(1) selector transition_room])
    have next_room:
      "position +
          length (fst (gpt_neo_bounded_generation_transition
            first_argmax m position state)) + n \<le>
        gpt_neo_model_max_position m"
      using Suc.prems(2)
      by (simp add: gpt_neo_bounded_generation_transition_tokens add.assoc)
    have recursive:
      "fst (gpt_neo_bounded_generate_steps n first_argmax
          m position
          (gpt_neo_bounded_generation_transition
            first_argmax m position state)) =
        gpt_neo_full_generate_steps n m position
          (fst (gpt_neo_bounded_generation_transition
            first_argmax m position state))"
      by (rule Suc.IH[OF next_valid next_room])
    have transition_full:
      "fst (gpt_neo_bounded_generation_transition
          first_argmax m position state) =
        fst state @ [gpt_neo_full_next_token m position (fst state)]"
      by (rule gpt_neo_bounded_generation_transition_full[OF Suc.prems(1)])
    have recursive_rewritten:
      "fst (gpt_neo_bounded_generate_steps (Suc n) first_argmax
          m position state) =
        gpt_neo_full_generate_steps n m position
          (fst state @ [gpt_neo_full_next_token m position (fst state)])"
      using recursive transition_full
      by (simp add: gpt_neo_bounded_generate_steps.simps
        recursive transition_full)
    show ?case
      by (simp only: gpt_neo_full_generate_steps.simps)
        (rule recursive_rewritten)
  qed
qed

definition gpt_neo_bounded_initialized_generation_state ::
  "gpt_neo_model_parameters \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
   gpt_neo_generation_state" where
  "gpt_neo_bounded_initialized_generation_state m position tokens =
    (tokens,
     snd (gpt_neo_bounded_cached_prompt m position (butlast tokens)))"

theorem gpt_neo_bounded_initialized_generation_state_valid:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le>
        gpt_neo_model_max_position m"
  shows "gpt_neo_bounded_generation_state_valid m position
    (gpt_neo_bounded_initialized_generation_state m position tokens)"
proof -
  have prefix_bounds:
    "\<forall>token \<in> set (butlast tokens).
      token < gpt_neo_model_vocabulary_size m"
    using token_bounds
    by (auto simp: in_set_butlastD)
  have prefix_position:
    "position + length (butlast tokens) \<le>
      gpt_neo_model_max_position m"
    using position_bound by simp
  have cache:
    "gpt_neo_bounded_model_cache_matches m position (butlast tokens)
      (snd (gpt_neo_bounded_cached_prompt m position (butlast tokens)))"
    by (rule gpt_neo_bounded_cached_prompt_correct(2)[
      OF valid prefix_bounds prefix_position])
  have tokens_vocabulary:
    "tokens_in_vocabulary
      (gpt_neo_model_vocabulary_size m) tokens"
    using token_bounds
    by (simp add: tokens_in_vocabulary_def)
  have generation_cache:
    "gpt_neo_bounded_generation_cache_matches m position tokens
      (snd (gpt_neo_bounded_cached_prompt m position (butlast tokens)))"
    using cache tokens
    by (simp add: gpt_neo_bounded_generation_cache_matches_def)
  show ?thesis
    unfolding gpt_neo_bounded_generation_state_valid_def
      gpt_neo_bounded_initialized_generation_state_def
    using valid tokens tokens_vocabulary position_bound generation_cache
    by simp
qed

corollary gpt_neo_initialized_greedy_generate_steps_eq_full:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le>
        gpt_neo_model_max_position m"
    and room:
      "position + length tokens + n \<le>
        gpt_neo_model_max_position m"
  shows "fst (gpt_neo_generate_steps n first_argmax m position
      (gpt_neo_initialized_generation_state m position tokens)) =
    gpt_neo_full_generate_steps n m position tokens"
proof -
  have state_valid:
    "gpt_neo_generation_state_valid m position
      (gpt_neo_initialized_generation_state m position tokens)"
    by (rule gpt_neo_initialized_generation_state_valid[
      OF valid tokens token_bounds position_bound])
  have equality:
    "fst (gpt_neo_generate_steps n first_argmax m position
        (gpt_neo_initialized_generation_state m position tokens)) =
      gpt_neo_full_generate_steps n m position
        (fst (gpt_neo_initialized_generation_state m position tokens))"
    by (rule gpt_neo_greedy_generate_steps_eq_full[OF state_valid])
      (simp add: gpt_neo_initialized_generation_state_def room)
  show ?thesis
    using equality
    by (simp add: gpt_neo_initialized_generation_state_def)
qed

corollary gpt_neo_bounded_initialized_greedy_generate_steps_eq_full:
  assumes valid: "valid_gpt_neo_model m"
    and tokens: "tokens \<noteq> []"
    and token_bounds:
      "\<forall>token \<in> set tokens.
        token < gpt_neo_model_vocabulary_size m"
    and position_bound:
      "position + length tokens \<le>
        gpt_neo_model_max_position m"
    and room:
      "position + length tokens + n \<le>
        gpt_neo_model_max_position m"
  shows "fst (gpt_neo_bounded_generate_steps n first_argmax
      m position
      (gpt_neo_bounded_initialized_generation_state m position tokens)) =
    gpt_neo_full_generate_steps n m position tokens"
proof -
  have state_valid:
    "gpt_neo_bounded_generation_state_valid m position
      (gpt_neo_bounded_initialized_generation_state m position tokens)"
    by (rule gpt_neo_bounded_initialized_generation_state_valid[
      OF valid tokens token_bounds position_bound])
  have equality:
    "fst (gpt_neo_bounded_generate_steps n first_argmax
        m position
        (gpt_neo_bounded_initialized_generation_state m position tokens)) =
      gpt_neo_full_generate_steps n m position
        (fst (gpt_neo_bounded_initialized_generation_state
          m position tokens))"
    by (rule gpt_neo_bounded_greedy_generate_steps_eq_full[OF state_valid])
      (simp add: gpt_neo_bounded_initialized_generation_state_def room)
  show ?thesis
    using equality
    by (simp add: gpt_neo_bounded_initialized_generation_state_def)
qed

end
