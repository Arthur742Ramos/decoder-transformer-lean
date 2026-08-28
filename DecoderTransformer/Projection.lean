import DecoderTransformer.Prompt
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Concrete stability of linear projections
-/

def columnL1Norm (w : Vector ℝ) : ℝ :=
  (w.map abs).sum

def projectionL1Bound (outDim : Nat) (W : Matrix ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧
    ∀ w ∈ matrixColumns outDim W, columnL1Norm w ≤ L

theorem columnL1Norm_nonnegative (w : Vector ℝ) : 0 ≤ columnL1Norm w := by
  induction w with
  | nil => simp [columnL1Norm]
  | cons x xs ih =>
      simp only [columnL1Norm, List.map_cons, List.sum_cons]
      exact add_nonneg (abs_nonneg x) ih

theorem dotProduct_sup_error {epsilon : ℝ}
    {xs ys w : Vector ℝ}
    (hepsilon : 0 ≤ epsilon) (hlength : xs.length = ys.length)
    (hcoordinates : ∀ i, i < xs.length →
      |xs.getD i 0 - ys.getD i 0| ≤ epsilon) :
    |dotProduct xs w - dotProduct ys w| ≤ columnL1Norm w * epsilon := by
  induction xs generalizing ys w with
  | nil =>
      have hys : ys = [] := by
        cases ys with
        | nil => rfl
        | cons y ys => simp at hlength
      subst ys
      simpa [dotProduct] using
        (mul_nonneg (columnL1Norm_nonnegative w) hepsilon)
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlength
      | cons b ys =>
          have hlengthTail : xs.length = ys.length := by simpa using hlength
          have hhead : |a - b| ≤ epsilon := by
            simpa using hcoordinates 0 (by simp)
          have htail : ∀ i, i < xs.length →
              |xs.getD i 0 - ys.getD i 0| ≤ epsilon := by
            intro i hi
            have h := hcoordinates (i + 1) (by simp [hi])
            simpa using h
          cases w with
          | nil => simp [dotProduct, columnL1Norm]
          | cons c w =>
              have htailBound := ih (ys := ys) (w := w)
                hlengthTail htail
              have hscaled : |c| * |a - b| ≤ |c| * epsilon :=
                mul_le_mul_of_nonneg_left hhead (abs_nonneg c)
              calc
                |dotProduct (a :: xs) (c :: w) -
                    dotProduct (b :: ys) (c :: w)| =
                    |(a - b) * c +
                      (dotProduct xs w - dotProduct ys w)| := by
                        simp [dotProduct]
                        ring_nf
                _ ≤ |(a - b) * c| +
                    |dotProduct xs w - dotProduct ys w| := by
                      exact abs_add_le _ _
                _ ≤ |c| * epsilon + columnL1Norm w * epsilon := by
                      exact add_le_add
                        (by simpa [abs_mul, mul_comm] using hscaled)
                        htailBound
                _ = columnL1Norm (c :: w) * epsilon := by
                      simp [columnL1Norm, abs_mul, mul_add, add_mul,
                        mul_comm, mul_left_comm, mul_assoc]

theorem linearProject_lipschitz {outDim : Nat} {W : Matrix ℝ} {L : ℝ}
    (hbound : projectionL1Bound outDim W L) :
    vectorLipschitz L (linearProject outDim W) := by
  refine ⟨hbound.1, ?_⟩
  intro epsilon xs ys hepsilon herror
  have hlengths : xs.length = ys.length := herror.1
  have houtputX : (linearProject outDim W xs).length = outDim := by
    simp [linearProject, matrixColumns]
  have houtputY : (linearProject outDim W ys).length = outDim := by
    simp [linearProject, matrixColumns]
  refine ⟨houtputX.trans houtputY.symm, ?_⟩
  intro i hi
  have hiOut : i < outDim := by simpa [houtputX] using hi
  let columns := matrixColumns outDim W
  let w : Vector ℝ := columns.getD i []
  have hcolumnsLength : columns.length = outDim := by
    simp [columns, matrixColumns]
  have hw : w ∈ columns := by
    have hwi : i < columns.length := by simpa [hcolumnsLength] using hiOut
    have hweq : w = columns[i]'hwi := by
      exact List.getD_eq_getElem _ _ hwi
    rw [hweq]
    exact List.getElem_mem hwi
  have hlocal : |dotProduct xs w - dotProduct ys w| ≤
      columnL1Norm w * epsilon :=
    dotProduct_sup_error (xs := xs) (ys := ys) (w := w)
      hepsilon hlengths (fun j hj => herror.2 j hj)
  have hboundW : columnL1Norm w ≤ L := hbound.2 w hw
  have hscaled : columnL1Norm w * epsilon ≤ L * epsilon :=
    mul_le_mul_of_nonneg_right hboundW hepsilon
  have hprojectedX :
      (linearProject outDim W xs).getD i 0 = dotProduct xs w := by
    change (columns.map (dotProduct xs)).getD i 0 = dotProduct xs w
    have hdefault : (0 : ℝ) = dotProduct xs [] := by simp [dotProduct]
    rw [hdefault, List.getD_map]
  have hprojectedY :
      (linearProject outDim W ys).getD i 0 = dotProduct ys w := by
    change (columns.map (dotProduct ys)).getD i 0 = dotProduct ys w
    have hdefault : (0 : ℝ) = dotProduct ys [] := by simp [dotProduct]
    rw [hdefault, List.getD_map]
  have hlocalW :
      |dotProduct xs w - dotProduct ys w| ≤ columnL1Norm w * epsilon :=
    hlocal
  calc
    |(linearProject outDim W xs).getD i 0 -
        (linearProject outDim W ys).getD i 0| =
        |dotProduct xs w - dotProduct ys w| := by
          rw [hprojectedX, hprojectedY]
    _ ≤ columnL1Norm w * epsilon := hlocalW
    _ ≤ L * epsilon := hscaled

theorem nextTokenLogits_lipschitz {modelDim vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {L : ℝ}
    (hweights : matrixShape modelDim vocabularySize vocabularyWeights)
    (hbound : projectionL1Bound vocabularySize vocabularyWeights L) :
    vectorLipschitz L
      (nextTokenLogits vocabularySize vocabularyWeights) := by
  exact linearProject_lipschitz hbound

theorem concreteNextTokenLogitError
    {hiddenError L roundingError : ℝ}
    {exactModel floatingModel : input → Vector ℝ}
    {floatingLogits : Vector ℝ → Vector ℝ}
    (hmodel : floatingTransformerRelation hiddenError exactModel floatingModel)
    (hweights : matrixShape modelDim vocabularySize vocabularyWeights)
    (hbound : projectionL1Bound vocabularySize vocabularyWeights L)
    (hrounding : roundingRelation roundingError
      (nextTokenLogits vocabularySize vocabularyWeights) floatingLogits)
    (x : input) :
    vectorErrorBound (L * hiddenError + roundingError)
      (nextTokenLogits vocabularySize vocabularyWeights (exactModel x))
      (floatingLogits (floatingModel x)) := by
  exact nextTokenLogitError hmodel
    (nextTokenLogits_lipschitz hweights hbound) hrounding x

end
end DecoderTransformer
