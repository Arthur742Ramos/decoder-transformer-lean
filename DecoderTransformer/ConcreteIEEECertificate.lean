import DecoderTransformer.IEEETraceCertificate
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Concrete binary32 projection certificate

The Isabelle fixture uses the zero/one portion of its binary32 model.  The
same certificate is retained here over the explicit decoded IEEE backend.
It is deliberately a small projection witness, not a trained-model claim.
-/

abbrev concreteBinary32 := ieee_binary32

def concreteVocabularyWeights : Matrix concreteBinary32 :=
  [[1, 0], [0, 0], [0, 0], [0, 0]]

def concreteHidden : Vector concreteBinary32 := [1, 0, 0, 0]

def concreteCertificates : Matrix concreteBinary32 :=
  [[1, 0, 0, 0], [0, 0, 0, 0]]

@[simp] theorem concreteOneFinite :
    ieeeIsFinite (1 : concreteBinary32) := ieeeIsFinite_one

theorem concreteVocabularyShape :
    matrixShape 4 2 concreteVocabularyWeights := by
  simp [concreteVocabularyWeights, matrixShape]

theorem concreteHiddenShape : vectorShape 4 concreteHidden := by
  simp [concreteHidden, vectorShape]

@[simp] theorem concreteZeroFma :
    ieeeFma (0 : concreteBinary32) 0 0 = 0 := by
  apply ieeeFloat_ext <;> simp [ieeeFma, ieeeFmaExact]

@[simp] theorem concreteZeroDot :
    ieeeFmaDot ([0, 0, 0] : Vector concreteBinary32) [0] = 0 := by
  apply ieeeFloat_ext <;> simp [ieeeFmaDot, ieeeFma, ieeeFmaExact]

@[simp] theorem concreteZeroDotThree :
    ieeeFmaDot ([0, 0, 0] : Vector concreteBinary32) [0, 0, 0] = 0 := by
  apply ieeeFloat_ext <;> simp [ieeeFmaDot, ieeeFma, ieeeFmaExact]

@[simp] theorem concrete_zero_dot_3 :
    ieeeFmaDot ([0, 0, 0] : Vector concreteBinary32) [0, 0, 0] = 0 :=
  concreteZeroDotThree

@[simp] theorem concreteZeroDotTwo :
    ieeeFmaDot ([0, 0] : Vector concreteBinary32) [0, 0] = 0 := by
  apply ieeeFloat_ext <;> simp [ieeeFmaDot, ieeeFma, ieeeFmaExact]

@[simp] theorem concrete_zero_dot_2 :
    ieeeFmaDot ([0, 0] : Vector concreteBinary32) [0, 0] = 0 :=
  concreteZeroDotTwo

@[simp] theorem concreteZeroDotOne :
    ieeeFmaDot ([0] : Vector concreteBinary32) [0] = 0 := by
  apply ieeeFloat_ext <;> simp [ieeeFmaDot, ieeeFma, ieeeFmaExact]

@[simp] theorem concrete_zero_dot_1 :
    ieeeFmaDot ([0] : Vector concreteBinary32) [0] = 0 :=
  concreteZeroDotOne

@[simp] theorem concreteEmptyDot :
    ieeeFmaDot ([] : Vector concreteBinary32) ([] : Vector concreteBinary32) = 0 := by
  apply ieeeFloat_ext <;> simp [ieeeFmaDot]

@[simp] theorem concreteZeroFinite :
    ieeeIsFinite (0 : concreteBinary32) := ieeeIsFinite_zero

@[simp] theorem concreteOneVal :
    ieeeVal (1 : concreteBinary32) = 1 := ieeeVal_one

@[simp] theorem concreteZeroVal :
    ieeeVal (0 : concreteBinary32) = 0 := ieeeVal_zero

@[simp] theorem concreteFmaZeroFinite :
    ieeeIsFinite (ieeeFma (0 : concreteBinary32) 0 0) := by
  simp [ieeeFma, ieeeIsFinite]

@[simp] theorem concreteFmaZeroVal :
    ieeeVal (ieeeFma (0 : concreteBinary32) 0 0) = 0 := by
  simp [ieeeFma, ieeeFmaExact, ieeeVal]

theorem concreteThresholdGtOne :
    1 < ieeeThreshold binary32Format := by
  norm_num [ieeeThreshold, binary32Format]

theorem concreteZeroStep :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (0 : concreteBinary32) 0 0 0 := by
  have hpos : 0 < ieeeThreshold binary32Format :=
    lt_trans (by norm_num) concreteThresholdGtOne
  simp [ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaExact, ieeeFma,
    ieeeVal, ieeeIsFinite, concreteThresholdGtOne, hpos]

theorem concreteOneStep :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (1 : concreteBinary32) 1 0 1 := by
  have hpos : 0 < ieeeThreshold binary32Format :=
    lt_trans (by norm_num) concreteThresholdGtOne
  simp [ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaExact, ieeeFma,
    ieeeVal, ieeeIsFinite, concreteThresholdGtOne, hpos]

theorem concreteZeroLeftZeroStep :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (1 : concreteBinary32) 0 0 0 := by
  have hpos : 0 < ieeeThreshold binary32Format :=
    lt_trans (by norm_num) concreteThresholdGtOne
  simp [ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaExact, ieeeFma,
    ieeeVal, ieeeIsFinite, concreteThresholdGtOne, hpos]

theorem concreteProjectionCertificate :
    ieeeProjectionCertificate (ieeeThreshold binary32Format) 1 2
      concreteVocabularyWeights concreteHidden concreteCertificates := by
  refine ⟨by simp [concreteCertificates], ?_⟩
  intro i hi
  have cases : i = 0 ∨ i = 1 := by omega
  have hpos : 0 < ieeeThreshold binary32Format :=
    lt_trans (by norm_num) concreteThresholdGtOne
  rcases cases with rfl | rfl
  · simp [concreteVocabularyWeights, concreteHidden, concreteCertificates,
      matrixColumns, nthOrZero, ieeeFmaDotCertificate,
      ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaDot,
      ieeeFmaExact, ieeeFma, ieeeVal, ieeeIsFinite,
      concreteThresholdGtOne, hpos]
  · simp [concreteVocabularyWeights, concreteHidden, concreteCertificates,
      matrixColumns, nthOrZero, ieeeFmaDotCertificate,
      ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaDot,
      ieeeFmaExact, ieeeFma, ieeeVal, ieeeIsFinite,
      concreteThresholdGtOne, hpos]

theorem concreteProjectionError :
    vectorErrorBound (4 : ℝ)
      (linearProject 2 (ieeeDecodeMatrix concreteVocabularyWeights)
        (ieeeDecodeVector concreteHidden))
      (ieeeDecodeVector
        (ieeeFmaLinearProject 2 concreteVocabularyWeights concreteHidden)) := by
  have h := ieeeFmaProjectionError_from_certificate
    (W := concreteVocabularyWeights) (x := concreteHidden)
    (certificates := concreteCertificates)
    (epsilon := (1 : ℝ)) (inDim := 4) (outDim := 2)
    (by norm_num) concreteVocabularyShape concreteHiddenShape
    concreteProjectionCertificate
  simpa using h

end
end DecoderTransformer
