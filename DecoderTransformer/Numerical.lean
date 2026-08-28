import DecoderTransformer.Autoregressive
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Numerical refinement interface

The exact semantic development observes floating implementations through
decoded real vectors.  A concrete IEEE backend must separately establish the
local rounding and model-error hypotheses used by these abstract relations.
-/

def vectorErrorBound (epsilon : ℝ) (xs ys : Vector ℝ) : Prop :=
  xs.length = ys.length ∧
    ∀ i, i < xs.length →
      |xs.getD i 0 - ys.getD i 0| ≤ epsilon

theorem vectorErrorBound_refl {epsilon : ℝ} {xs : Vector ℝ}
    (hepsilon : 0 ≤ epsilon) : vectorErrorBound epsilon xs xs := by
  refine ⟨rfl, ?_⟩
  intro i hi
  simp [vectorErrorBound] at *
  exact hepsilon

theorem vectorErrorBound_sym {epsilon : ℝ} {xs ys : Vector ℝ}
    (h : vectorErrorBound epsilon xs ys) : vectorErrorBound epsilon ys xs := by
  rcases h with ⟨hlen, hcoordinates⟩
  refine ⟨hlen.symm, ?_⟩
  intro i hi
  have hi' : i < xs.length := by simpa [hlen] using hi
  simpa [abs_sub_comm] using hcoordinates i hi'

theorem vectorErrorBound_triangle {epsilon delta : ℝ}
    {xs ys zs : Vector ℝ}
    (hxy : vectorErrorBound epsilon xs ys)
    (hyz : vectorErrorBound delta ys zs) :
    vectorErrorBound (epsilon + delta) xs zs := by
  rcases hxy with ⟨hxyLength, hxyCoordinates⟩
  rcases hyz with ⟨hyzLength, hyzCoordinates⟩
  refine ⟨hxyLength.trans hyzLength, ?_⟩
  intro i hi
  have hiY : i < ys.length := by simpa [hxyLength] using hi
  calc
    |xs.getD i 0 - zs.getD i 0| =
        |(xs.getD i 0 - ys.getD i 0) +
          (ys.getD i 0 - zs.getD i 0)| := by ring_nf
    _ ≤ |xs.getD i 0 - ys.getD i 0| +
        |ys.getD i 0 - zs.getD i 0| := by
          exact abs_add_le _ _
    _ ≤ epsilon + delta := by
      exact add_le_add (hxyCoordinates i hi) (hyzCoordinates i hiY)

def vectorLipschitz (L : ℝ) (F : Vector ℝ → Vector ℝ) : Prop :=
  0 ≤ L ∧
    ∀ epsilon xs ys, 0 ≤ epsilon →
      vectorErrorBound epsilon xs ys →
      vectorErrorBound (L * epsilon) (F xs) (F ys)

def floatingTransformerRelation (hiddenError : ℝ)
    (exactModel floatingModel : input → Vector ℝ) : Prop :=
  0 ≤ hiddenError ∧
    ∀ x, vectorErrorBound hiddenError (exactModel x) (floatingModel x)

def roundingRelation (roundingError : ℝ)
    (exactOperator floatingOperator : Vector ℝ → Vector ℝ) : Prop :=
  0 ≤ roundingError ∧
    ∀ x, vectorErrorBound roundingError
      (exactOperator x) (floatingOperator x)

theorem endToEndLogitError
    {hiddenError L roundingError : ℝ}
    {exactModel floatingModel : input → Vector ℝ}
    {exactLogits floatingLogits : Vector ℝ → Vector ℝ}
    (hmodel : floatingTransformerRelation hiddenError exactModel floatingModel)
    (hlipschitz : vectorLipschitz L exactLogits)
    (hrounding : roundingRelation roundingError exactLogits floatingLogits)
    (x : input) :
    vectorErrorBound (L * hiddenError + roundingError)
      (exactLogits (exactModel x)) (floatingLogits (floatingModel x)) := by
  rcases hmodel with ⟨hhiddenNonnegative, hhidden⟩
  rcases hlipschitz with ⟨hLNonnegative, hpropagate⟩
  rcases hrounding with ⟨hroundingNonnegative, hround⟩
  have hpropagated := hpropagate hiddenError (exactModel x) (floatingModel x)
    hhiddenNonnegative (hhidden x)
  have hrounded := hround (floatingModel x)
  exact vectorErrorBound_triangle hpropagated hrounded

theorem nextTokenLogitError
    {hiddenError L roundingError : ℝ}
    {exactModel floatingModel : input → Vector ℝ}
    {floatingLogits : Vector ℝ → Vector ℝ}
    (hmodel : floatingTransformerRelation hiddenError exactModel floatingModel)
    (hprojection : vectorLipschitz L
      (nextTokenLogits vocabularySize vocabularyWeights))
    (hrounding : roundingRelation roundingError
      (nextTokenLogits vocabularySize vocabularyWeights) floatingLogits)
    (x : input) :
    vectorErrorBound (L * hiddenError + roundingError)
      (nextTokenLogits vocabularySize vocabularyWeights (exactModel x))
      (floatingLogits (floatingModel x)) := by
  exact endToEndLogitError hmodel hprojection hrounding x

end
end DecoderTransformer
