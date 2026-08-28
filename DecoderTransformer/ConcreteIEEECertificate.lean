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
  change ieeeFma (ieeeZero binary32Format) (ieeeZero binary32Format)
      (ieeeZero binary32Format) = ieeeZero binary32Format
  apply ieeeFloat_ext <;>
    norm_num [ieeeFma, ieeeFmaExact, ieeeIsNaN, ieeeIsInfinity,
      ieeeIsZero, ieeeSign, ieeeZeroSign, ieeeZero, binary32Format,
      ieeeExponentMax, ieeeVal, ieeeSignValue] <;> rfl

@[simp] theorem concreteZeroFmaExplicit :
    ieeeFma (ieeeZero binary32Format) (ieeeZero binary32Format)
      (ieeeZero binary32Format) = ieeeZero binary32Format := by
  exact concreteZeroFma

@[simp] theorem concreteZeroDot :
    ieeeFmaDot ([0, 0, 0] : Vector concreteBinary32) [0] = 0 := by
  simp [ieeeFmaDot]

@[simp] theorem concreteZeroDotThree :
    ieeeFmaDot ([0, 0, 0] : Vector concreteBinary32) [0, 0, 0] = 0 := by
  simp [ieeeFmaDot]

@[simp] theorem concrete_zero_dot_3 :
    ieeeFmaDot ([0, 0, 0] : Vector concreteBinary32) [0, 0, 0] = 0 :=
  concreteZeroDotThree

@[simp] theorem concreteZeroDotTwo :
    ieeeFmaDot ([0, 0] : Vector concreteBinary32) [0, 0] = 0 := by
  simp [ieeeFmaDot]

@[simp] theorem concrete_zero_dot_2 :
    ieeeFmaDot ([0, 0] : Vector concreteBinary32) [0, 0] = 0 :=
  concreteZeroDotTwo

@[simp] theorem concreteZeroDotOne :
    ieeeFmaDot ([0] : Vector concreteBinary32) [0] = 0 := by
  simp [ieeeFmaDot]

@[simp] theorem concrete_zero_dot_1 :
    ieeeFmaDot ([0] : Vector concreteBinary32) [0] = 0 :=
  concreteZeroDotOne

@[simp] theorem concreteZeroDotOneExplicit :
    ieeeFmaDot [ieeeZero binary32Format] [ieeeZero binary32Format] =
      ieeeZero binary32Format := by
  change ieeeFmaDot ([0] : Vector concreteBinary32) [0] = 0
  exact concreteZeroDotOne

@[simp] theorem concreteZeroDotTwoExplicit :
    ieeeFmaDot [ieeeZero binary32Format, ieeeZero binary32Format]
      [ieeeZero binary32Format, ieeeZero binary32Format] =
        ieeeZero binary32Format := by
  change ieeeFmaDot ([0, 0] : Vector concreteBinary32) [0, 0] = 0
  exact concreteZeroDotTwo

@[simp] theorem concreteZeroDotThreeExplicit :
    ieeeFmaDot [ieeeZero binary32Format, ieeeZero binary32Format,
      ieeeZero binary32Format]
      [ieeeZero binary32Format, ieeeZero binary32Format,
        ieeeZero binary32Format] = ieeeZero binary32Format := by
  change ieeeFmaDot ([0, 0, 0] : Vector concreteBinary32) [0, 0, 0] = 0
  exact concreteZeroDotThree

@[simp] theorem concreteEmptyDot :
    ieeeFmaDot ([] : Vector concreteBinary32) ([] : Vector concreteBinary32) = 0 := by
  simp [ieeeFmaDot]

@[simp] theorem concreteZeroFinite :
    ieeeIsFinite (0 : concreteBinary32) := ieeeIsFinite_zero

@[simp] theorem concreteOneVal :
    ieeeVal (1 : concreteBinary32) = 1 := ieeeVal_one

@[simp] theorem concreteZeroVal :
    ieeeVal (0 : concreteBinary32) = 0 := ieeeVal_zero

@[simp] theorem concreteZeroExplicitFinite :
    ieeeIsFinite (ieeeZero binary32Format) := by
  change ieeeIsFinite (0 : concreteBinary32)
  exact concreteZeroFinite

@[simp] theorem concreteOneExplicitFinite :
    ieeeIsFinite (ieeeOne binary32Format) := by
  change ieeeIsFinite (1 : concreteBinary32)
  exact concreteOneFinite

@[simp] theorem concreteZeroExplicitVal :
    ieeeVal (ieeeZero binary32Format) = 0 := by
  change ieeeVal (0 : concreteBinary32) = 0
  exact concreteZeroVal

@[simp] theorem concreteOneExplicitVal :
    ieeeVal (ieeeOne binary32Format) = 1 := by
  change ieeeVal (1 : concreteBinary32) = 1
  exact concreteOneVal

@[simp] theorem concreteFmaZeroFinite :
    ieeeIsFinite (ieeeFma (0 : concreteBinary32) 0 0) := by
  rw [concreteZeroFma]
  exact concreteZeroFinite

@[simp] theorem concreteFmaZeroVal :
    ieeeVal (ieeeFma (0 : concreteBinary32) 0 0) = 0 := by
  rw [concreteZeroFma]
  exact concreteZeroVal

theorem concreteThresholdGtOne :
    1 < ieeeThreshold binary32Format := by
  norm_num [ieeeThreshold, binary32Format, ieeeExponentMax, ieeeBias]

theorem concreteZeroStep :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (0 : concreteBinary32) 0 0 0 := by
  have hpos : 0 < ieeeThreshold binary32Format :=
    lt_trans (by norm_num) concreteThresholdGtOne
  simp [ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaExact,
    concreteThresholdGtOne, hpos]

theorem concreteOneStep :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (1 : concreteBinary32) 1 0 1 := by
  have hpos : 0 < ieeeThreshold binary32Format :=
    lt_trans (by norm_num) concreteThresholdGtOne
  simp [ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaExact,
    concreteThresholdGtOne, hpos]

theorem concreteZeroLeftZeroStep :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (1 : concreteBinary32) 0 0 0 := by
  have hpos : 0 < ieeeThreshold binary32Format :=
    lt_trans (by norm_num) concreteThresholdGtOne
  simp [ieeeFmaStepCertificate, ieeeRoundWitness, ieeeFmaExact,
    concreteThresholdGtOne, hpos]

@[simp] theorem concreteZeroStepExplicit :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (ieeeZero binary32Format) (ieeeZero binary32Format)
      (ieeeZero binary32Format) (ieeeZero binary32Format) := by
  change ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
    (0 : concreteBinary32) 0 0 0
  exact concreteZeroStep

@[simp] theorem concreteOneStepExplicit :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (ieeeOne binary32Format) (ieeeOne binary32Format)
      (ieeeZero binary32Format) (ieeeOne binary32Format) := by
  change ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
    (1 : concreteBinary32) 1 0 1
  exact concreteOneStep

@[simp] theorem concreteZeroLeftZeroStepExplicit :
    ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
      (ieeeOne binary32Format) (ieeeZero binary32Format)
      (ieeeZero binary32Format) (ieeeZero binary32Format) := by
  change ieeeFmaStepCertificate (ieeeThreshold binary32Format) 1
    (1 : concreteBinary32) 0 0 0
  exact concreteZeroLeftZeroStep

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
      concreteZeroDotThreeExplicit, concreteZeroDotTwoExplicit,
      concreteZeroDotOneExplicit, concreteZeroStepExplicit,
      concreteOneStepExplicit, concreteZeroLeftZeroStepExplicit,
      concreteThresholdGtOne, hpos]
  · simp [concreteVocabularyWeights, concreteHidden, concreteCertificates,
      matrixColumns, nthOrZero, ieeeFmaDotCertificate,
      concreteZeroDotThreeExplicit, concreteZeroDotTwoExplicit,
      concreteZeroDotOneExplicit, concreteZeroStepExplicit,
      concreteOneStepExplicit, concreteZeroLeftZeroStepExplicit,
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
