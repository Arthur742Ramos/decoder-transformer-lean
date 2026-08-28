import DecoderTransformer.GPTNeoGeneration
import Mathlib.Tactic

namespace DecoderTransformer
namespace GPTNeoTinyCheckpoint

noncomputable section

/-!
# Concrete GPT-Neo model fixture

This is the Lean counterpart of `GPT_Neo_Tiny_Checkpoint.thy`: a one-head,
one-dimensional GPT-Neo block with zero projections, positive normalization
epsilon, a two-token vocabulary, and a four-position context.
-/

def gpt_neo_tiny_zero_matrix : Matrix ℝ := [[0]]

def gpt_neo_tiny_zero_tensor : Tensor3 ℝ := [[[0]]]

def gpt_neo_tiny_layer : GPTNeoLayerParameters where
  headCount := 1
  modelDim := 1
  headDim := 1
  hiddenDim := 1
  attentionWindow := 1
  normEpsilon := 1
  ln1Gain := [1]
  ln1Bias := [0]
  ln2Gain := [1]
  ln2Bias := [0]
  queryWeights := gpt_neo_tiny_zero_tensor
  keyWeights := gpt_neo_tiny_zero_tensor
  valueWeights := gpt_neo_tiny_zero_tensor
  outputWeights := gpt_neo_tiny_zero_matrix
  outputBias := [0]
  fcWeights := gpt_neo_tiny_zero_matrix
  fcBias := [0]
  projectionWeights := gpt_neo_tiny_zero_matrix
  projectionBias := [0]

def gpt_neo_tiny_model : GPTNeoModelParameters where
  layers := [gpt_neo_tiny_layer]
  hiddenSize := 1
  vocabularySize := 2
  maxPosition := 4
  normEpsilon := 1
  tokenEmbeddings := [[0], [1]]
  positionEmbeddings := [[0], [0], [0], [0]]
  finalGain := [1]
  finalBias := [0]
  vocabularyWeights := [[0, 1]]

lemma gpt_neo_tiny_layer_valid : validGPTNeoLayer gpt_neo_tiny_layer := by
  simp [validGPTNeoLayer, gpt_neo_tiny_layer, gpt_neo_tiny_zero_tensor,
    gpt_neo_tiny_zero_matrix, multiHeadParametersShape, vectorShape,
    matrixShape, tensor3Shape]

lemma gpt_neo_tiny_model_valid : validGPTNeoModel gpt_neo_tiny_model := by
  refine ⟨by simp [gpt_neo_tiny_model], by norm_num [gpt_neo_tiny_model],
    by norm_num [gpt_neo_tiny_model], by norm_num [gpt_neo_tiny_model],
    by norm_num [gpt_neo_tiny_model], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpt_neo_tiny_model, matrixShape]
  · simp [gpt_neo_tiny_model, matrixShape]
  · simp [gpt_neo_tiny_model, vectorShape]
  · simp [gpt_neo_tiny_model, vectorShape]
  · simp [gpt_neo_tiny_model, matrixShape]
  · intro p hp
    simp only [gpt_neo_tiny_model, List.mem_singleton] at hp
    subst p
    exact ⟨gpt_neo_tiny_layer_valid, by rfl⟩

lemma gpt_neo_tiny_token_bounds :
    ∀ token ∈ ([1] : List Nat), token < gpt_neo_tiny_model.vocabularySize := by
  intro token htoken
  simp only [List.mem_singleton] at htoken
  subst token
  norm_num [gpt_neo_tiny_model]

lemma gpt_neo_tiny_position_bound :
    0 + ([1] : List Nat).length ≤ gpt_neo_tiny_model.maxPosition := by
  simp [gpt_neo_tiny_model]

theorem gpt_neo_tiny_prompt_cache_refinement :
    (gptNeoCachedPrompt gpt_neo_tiny_model 0 [1]).1 =
        gptNeoFullHidden gpt_neo_tiny_model 0 [1] ∧
      gptNeoModelCacheMatches gpt_neo_tiny_model 0 [1]
        (gptNeoCachedPrompt gpt_neo_tiny_model 0 [1]).2 := by
  exact gptNeoCachedPrompt_correct gpt_neo_tiny_model_valid
    gpt_neo_tiny_token_bounds gpt_neo_tiny_position_bound

theorem gpt_neo_tiny_bounded_prompt_cache_refinement :
    (gptNeoBoundedCachedPrompt gpt_neo_tiny_model 0 [1]).1 =
        gptNeoFullHidden gpt_neo_tiny_model 0 [1] ∧
      gptNeoBoundedModelCacheMatches gpt_neo_tiny_model 0 [1]
        (gptNeoBoundedCachedPrompt gpt_neo_tiny_model 0 [1]).2 := by
  exact gptNeoBoundedCachedPrompt_correct gpt_neo_tiny_model_valid
    gpt_neo_tiny_token_bounds gpt_neo_tiny_position_bound

theorem gpt_neo_tiny_bounded_generation_initialization :
    gptNeoBoundedGenerationStateValid gpt_neo_tiny_model 0
      (gptNeoBoundedInitializedGenerationState gpt_neo_tiny_model 0 [1]) := by
  apply gptNeoBoundedInitializedGenerationStateValid
    gpt_neo_tiny_model_valid
  · simp
  · exact gpt_neo_tiny_token_bounds
  · exact gpt_neo_tiny_position_bound

theorem gpt_neo_tiny_bounded_one_step :
    gptNeoBoundedGenerationStateValid gpt_neo_tiny_model 0
      (gptNeoBoundedGenerateSteps 1 firstArgmax gpt_neo_tiny_model 0
        (gptNeoBoundedInitializedGenerationState gpt_neo_tiny_model 0 [1])) := by
  apply gptNeoBoundedGreedyGenerateStepsValid
    gpt_neo_tiny_bounded_generation_initialization
  simp [gpt_neo_tiny_model, gptNeoBoundedInitializedGenerationState]

end
end GPTNeoTinyCheckpoint
end DecoderTransformer
