import DecoderTransformer.IEEE754Projection
import Mathlib.Tactic

namespace DecoderTransformer
namespace TinyDecoderCheckpoint

noncomputable section

/-!
# A concrete executable modern-decoder checkpoint

This is the Lean counterpart of `Tiny_Decoder_Checkpoint.thy`.  The fixture is
deliberately tiny: one query/KV head, two-dimensional hidden states, identity
RoPE, and zero attention/MLP weights.  The residual path is therefore the
identity, while the embedding and vocabulary matrices make the generation
trace concrete.
-/

def tiny_zero_matrix : Matrix ℝ := [[0, 0], [0, 0]]

def tiny_zero_tensor : Tensor3 ℝ := [tiny_zero_matrix]

def tiny_identity_matrix : Matrix ℝ := [[1, 0], [0, 1]]

def tiny_embedding (token : Nat) : Vector ℝ :=
  if token = 0 then [1, 0] else [0, 1]

def tiny_modern_layer : ModernDecoderLayerParameters where
  queryHeadCount := 1
  kvHeadCount := 1
  modelDim := 2
  headDim := 2
  hiddenDim := 2
  normEpsilon := 1
  rope := fun _ x => x
  attentionGain := [1, 1]
  mlpGain := [1, 1]
  queryWeights := tiny_zero_tensor
  keyWeights := tiny_zero_tensor
  valueWeights := tiny_zero_tensor
  outputWeights := tiny_zero_matrix
  gateWeights := tiny_zero_matrix
  upWeights := tiny_zero_matrix
  downWeights := tiny_zero_matrix

def tiny_modern_layers : List ModernDecoderLayerParameters :=
  [tiny_modern_layer]

lemma tiny_modern_layer_valid : validModernDecoderLayer tiny_modern_layer := by
  simp [validModernDecoderLayer, tiny_modern_layer, tiny_zero_tensor,
    tiny_zero_matrix, vectorShape, matrixShape, tensor3Shape]

lemma tiny_modern_stack_valid : validModernStack tiny_modern_layers := by
  intro p hp
  simp only [tiny_modern_layers, List.mem_singleton] at hp
  simpa [hp] using tiny_modern_layer_valid

lemma tiny_dot_product_zero_two (x : Vector ℝ) :
    dotProduct x [0, 0] = 0 := by
  cases x with
  | nil => simp [dotProduct]
  | cons a xs =>
      cases xs with
      | nil => simp [dotProduct]
      | cons b ys => simp [dotProduct]

lemma tiny_zero_projection (x : Vector ℝ) :
    linearProject 2 tiny_zero_matrix x = [0, 0] := by
  change [dotProduct x [0, 0], dotProduct x [0, 0]] = [0, 0]
  simp [tiny_dot_product_zero_two]

lemma tiny_identity_projection (a b : ℝ) :
    linearProject 2 tiny_identity_matrix [a, b] = [a, b] := by
  change [dotProduct [a, b] [1, 0], dotProduct [a, b] [0, 1]] = [a, b]
  simp [dotProduct]

lemma tiny_grouped_attention_zero (ix : Nat × Vector ℝ)
    (pref : List (Nat × Vector ℝ)) :
    modernGroupedAttentionAtPrefix tiny_modern_layer ix pref = [0, 0] := by
  unfold modernGroupedAttentionAtPrefix
  change linearProject 2 tiny_zero_matrix _ = [0, 0]
  exact tiny_zero_projection _

lemma tiny_swiglu_zero (x : Vector ℝ) :
    swiglu 2 2 tiny_zero_matrix tiny_zero_matrix tiny_zero_matrix x = [0, 0] := by
  unfold swiglu gatedFeedForward
  change linearProject 2 tiny_zero_matrix _ = [0, 0]
  exact tiny_zero_projection _

theorem tiny_modern_decoder_identity {position : Nat}
    {x : Vector ℝ} {pref : List (Nat × Vector ℝ)}
    (hx : vectorShape 2 x) :
    modernDecoderAtIndexedPrefix tiny_modern_layer (position, x) pref = x := by
  cases x with
  | nil => simp [vectorShape] at hx
  | cons a xs =>
      cases xs with
      | nil => simp [vectorShape] at hx
      | cons b ys =>
          have hys : ys = [] := by
            have hlen : (a :: b :: ys).length = 2 := hx
            have : ys.length = 0 := by simpa using hlen
            exact List.eq_nil_of_length_eq_zero this
          subst hys
          have hattention :
              modernGroupedAttentionAtPrefix tiny_modern_layer (position, [a, b])
                pref = [0, 0] := tiny_grouped_attention_zero _ _
          simp only [modernDecoderAtIndexedPrefix]
          rw [hattention]
          simp [modernDecoderAtIndexedPrefix, tiny_modern_layer, tiny_swiglu_zero,
            vectorAdd]

theorem tiny_full_layer_identity {seqLen start : Nat} {X : Matrix ℝ}
    (hshape : matrixShape seqLen 2 X) :
    fullModernDecoderLayer tiny_modern_layer start X = X := by
  have hrows : ∀ x ∈ X, vectorShape 2 x := by
    intro x hx
    exact hshape.2 x hx
  have hidentity : ∀ Y : Matrix ℝ, (∀ y ∈ Y, vectorShape 2 y) →
      fullModernDecoderLayer tiny_modern_layer start Y = Y := by
    intro Y hY
    induction Y using List.reverseRecOn with
    | nil => rfl
    | append_singleton ys y ih =>
        have hy : vectorShape 2 y := hY y (by simp)
        have hys : ∀ z ∈ ys, vectorShape 2 z := by
          intro z hz
          exact hY z (by simp [hz])
        rw [fullModernDecoderLayer_append]
        rw [ih hys, tiny_modern_decoder_identity hy]
  exact hidentity X hrows

theorem tiny_full_stack_identity {seqLen start : Nat} {X : Matrix ℝ}
    (hshape : matrixShape seqLen 2 X) :
    fullModernDecoderStack tiny_modern_layers start X = X := by
  simp only [tiny_modern_layers, fullModernDecoderStack]
  exact tiny_full_layer_identity hshape

lemma tiny_embedding_shape (token : Nat) :
    vectorShape 2 (tiny_embedding token) := by
  by_cases htoken : token = 0 <;>
    simp [tiny_embedding, vectorShape, htoken]

lemma tiny_vocabulary_shape :
    matrixShape 2 2 tiny_identity_matrix := by
  simp [tiny_identity_matrix, matrixShape]

theorem tiny_checkpoint_logits (start token : Nat) (tokens : List Nat) :
    nextTokenLogits 2 tiny_identity_matrix
        ((fullModernDecoderStack tiny_modern_layers start
          (tokens.map tiny_embedding ++ [tiny_embedding token])).getLast?.getD
          ([] : Vector ℝ)) = tiny_embedding token := by
  have hinput : matrixShape
      (tokens.map tiny_embedding ++ [tiny_embedding token]).length 2
      (tokens.map tiny_embedding ++ [tiny_embedding token]) := by
    refine ⟨by simp, ?_⟩
    intro row hrow
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hrow
    rcases hrow with hrow | rfl
    · rcases hrow with ⟨t, ht, rfl⟩
      exact tiny_embedding_shape t
    · exact tiny_embedding_shape token
  have hstack := tiny_full_stack_identity (start := start) hinput
  have hlast :
      (fullModernDecoderStack tiny_modern_layers start
        (tokens.map tiny_embedding ++ [tiny_embedding token])).getLast?.getD
          ([] : Vector ℝ) = tiny_embedding token := by
    rw [hstack]
    simp [List.getLast?_eq_getLast_of_ne_nil]
  rw [hlast]
  cases token with
  | zero => simp [nextTokenLogits, tiny_embedding, tiny_identity_projection]
  | succ token => simp [nextTokenLogits, tiny_embedding, tiny_identity_projection]

theorem tiny_cached_prompt_outputs (start : Nat) (tokens : List Nat) :
    (cachedModernDecoderStackRun tiny_modern_layers start
      (emptyModernTransformerCache tiny_modern_layers)
      (tokens.map tiny_embedding)).1 =
      (tokens.map tiny_embedding) := by
  have hinput : matrixShape tokens.length 2 (tokens.map tiny_embedding) := by
    refine ⟨by simp, ?_⟩
    intro row hrow
    rcases List.mem_map.1 hrow with ⟨t, ht, rfl⟩
    exact tiny_embedding_shape t
  have hrun := initializedModernCachedRun_equalsFull
    (layers := tiny_modern_layers) tiny_modern_stack_valid start
    (tokens.map tiny_embedding)
  rw [hrun, tiny_full_stack_identity hinput]

theorem tiny_cached_prompt_certificate (start : Nat) (tokens : List Nat) :
    modernTransformerCacheMatches tiny_modern_layers start
      (tokens.map tiny_embedding)
      (cachedModernDecoderStackRun tiny_modern_layers start
        (emptyModernTransformerCache tiny_modern_layers)
        (tokens.map tiny_embedding)).2 := by
  exact initializedModernCachedRun_cacheInvariant
    (layers := tiny_modern_layers) tiny_modern_stack_valid start
    (tokens.map tiny_embedding)

theorem tiny_cached_prompt_execution (start : Nat) (tokens : List Nat) :
    (cachedModernDecoderStackRun tiny_modern_layers start
      (emptyModernTransformerCache tiny_modern_layers)
      (tokens.map tiny_embedding)).1 = tokens.map tiny_embedding ∧
    modernTransformerCacheMatches tiny_modern_layers start
      (tokens.map tiny_embedding)
      (cachedModernDecoderStackRun tiny_modern_layers start
        (emptyModernTransformerCache tiny_modern_layers)
        (tokens.map tiny_embedding)).2 := by
  exact ⟨tiny_cached_prompt_outputs start tokens,
    tiny_cached_prompt_certificate start tokens⟩

theorem tiny_uniform_generation_distribution (hidden : Vector ℝ) :
    nextTokenDistribution 2 tiny_zero_matrix hidden = [1 / 2, 1 / 2] := by
  have hlogits : nextTokenLogits 2 tiny_zero_matrix hidden = [0, 0] := by
    exact tiny_zero_projection hidden
  change listSoftmax (nextTokenLogits 2 tiny_zero_matrix hidden) = [1 / 2, 1 / 2]
  rw [hlogits]
  norm_num [nextTokenDistribution, listSoftmax, softmaxDenominator]

theorem tiny_uniform_generation_selects_zero (hidden : Vector ℝ) :
    firstArgmax (nextTokenDistribution 2 tiny_zero_matrix hidden) = 0 := by
  rw [tiny_uniform_generation_distribution]
  norm_num [firstArgmax]

theorem tiny_cached_next_token {start : Nat} {tokens : List Nat}
    {caches : ModernTransformerCache}
    (hcache : modernGenerationCacheMatches tiny_embedding tiny_modern_layers
      start tokens caches) :
    firstArgmax
      (cachedModernGenerationEvaluate tiny_modern_layers tiny_embedding start 2
        tiny_zero_matrix tokens caches).1 = 0 := by
  have hne : tokens ≠ [] := hcache.1
  unfold cachedModernGenerationEvaluate
  rw [if_neg hne]
  exact tiny_uniform_generation_selects_zero _

theorem tiny_generation_transition_appends_zero
    {start : Nat} {state : ModernGenerationState}
    (hcache : modernGenerationCacheMatches tiny_embedding tiny_modern_layers
      start state.1 state.2) :
    (modernGenerationTransition firstArgmax tiny_modern_layers tiny_embedding
      start 2 tiny_zero_matrix state).1 = state.1 ++ [0] := by
  have hselected := tiny_cached_next_token hcache
  simp [modernGenerationTransition, deterministicNextToken, hselected]

theorem tiny_generate_steps_tokens {n start : Nat}
    {state : ModernGenerationState}
    (hcache : modernGenerationCacheMatches tiny_embedding tiny_modern_layers
      start state.1 state.2) :
    (modernGenerateSteps n firstArgmax tiny_modern_layers tiny_embedding start
      2 tiny_zero_matrix state).1 = state.1 ++ List.replicate n 0 := by
  induction n generalizing state with
  | zero => simp [modernGenerateSteps]
  | succ n ih =>
      have hnext := modernGenerationTransitionCacheInvariant
        (select := firstArgmax) (layers := tiny_modern_layers)
        (embedding := tiny_embedding) (start := start)
        (vocabularySize := 2) (vocabularyWeights := tiny_zero_matrix) hcache
      have htokens := tiny_generation_transition_appends_zero hcache
      change (modernGenerateSteps n firstArgmax tiny_modern_layers tiny_embedding
        start 2 tiny_zero_matrix
        (modernGenerationTransition firstArgmax tiny_modern_layers tiny_embedding
          start 2 tiny_zero_matrix state)).1 =
        state.1 ++ List.replicate (n + 1) 0
      rw [ih hnext, htokens]
      simp [List.replicate_succ, List.append_assoc]

theorem tiny_initialized_generation_trace {n start : Nat}
    {tokens : List Nat} (hne : tokens ≠ []) :
    (modernGenerateSteps n firstArgmax tiny_modern_layers tiny_embedding start
      2 tiny_zero_matrix
      (initializeModernGenerationState tiny_modern_layers tiny_embedding start
        tokens)).1 = tokens ++ List.replicate n 0 := by
  have hcache := initializeModernGenerationState_correct
    (layers := tiny_modern_layers) (embedding := tiny_embedding) (start := start)
    (tokens := tokens) tiny_modern_stack_valid hne
  have htrace := tiny_generate_steps_tokens (n := n) (start := start) hcache
  simpa [initializeModernGenerationState] using htrace

theorem tiny_three_step_demo :
    (modernGenerateSteps 3 firstArgmax tiny_modern_layers tiny_embedding 0 2
      tiny_zero_matrix
      (initializeModernGenerationState tiny_modern_layers tiny_embedding 0
        [1])).1 = [1, 0, 0, 0] := by
  have h := tiny_initialized_generation_trace (n := 3) (start := 0)
    (tokens := [1]) (by simp)
  simpa using h

end
end TinyDecoderCheckpoint
end DecoderTransformer
