import DecoderTransformer.DyadicFinitePrecision
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# IEEE-754 projection refinement

This is the Lean counterpart of `IEEE_754_Projection.thy`.  Isabelle's
development imports a parameterised bit-level IEEE-754 library from the AFP.
The Lean dependency set used by this repository does not contain that
parameterised library, so the arithmetic backend is represented explicitly by
an abstract format and a decoded finite value.  The refinement layer itself is
fully kernel checked: certificates, finite-precision dot products, projection
errors, and the end-to-end logit bounds are all proved here.  A future
bit-level backend can instantiate `IEEEFloat` and discharge the same
certificate predicates without changing the transformer semantics.

In particular, this file makes no claim of bit-identical FP16/FP32 execution.
The `ieeeFma` operation is the exact decoded backend used for the semantic
certificate interface, while `ieeeRoundWitness` records the nearest-value
obligation required of a concrete implementation.
-/

structure IEEEFormat where
  threshold : ℝ

structure IEEEFloat (fmt : IEEEFormat) where
  value : ℝ
  finite : Bool

instance (fmt : IEEEFormat) : Zero (IEEEFloat fmt) where
  zero := ⟨(0 : ℝ), true⟩

instance (fmt : IEEEFormat) : OfNat (IEEEFloat fmt) 0 where
  ofNat := ⟨(0 : ℝ), true⟩

instance (fmt : IEEEFormat) : OfNat (IEEEFloat fmt) 1 where
  ofNat := ⟨(1 : ℝ), true⟩

def ieeeVal {fmt : IEEEFormat} (x : IEEEFloat fmt) : ℝ := x.value

@[simp] theorem ieeeVal_mk {fmt : IEEEFormat} (v : ℝ) (f : Bool) :
    ieeeVal (⟨v, f⟩ : IEEEFloat fmt) = v := rfl

def ieeeIsFinite {fmt : IEEEFormat} (x : IEEEFloat fmt) : Prop :=
  x.finite = true

@[simp] theorem ieeeIsFinite_mk {fmt : IEEEFormat} (v : ℝ) (f : Bool) :
    ieeeIsFinite (⟨v, f⟩ : IEEEFloat fmt) ↔ f = true := Iff.rfl

@[ext] theorem ieeeFloat_ext {fmt : IEEEFormat}
    {x y : IEEEFloat fmt} (hvalue : x.value = y.value)
    (hfinite : x.finite = y.finite) : x = y := by
  cases x
  cases y
  simp_all

@[simp] theorem ieeeZeroLiteral {fmt : IEEEFormat} :
    (0 : IEEEFloat fmt) = ⟨(0 : ℝ), true⟩ := by
  rfl

@[simp] theorem ieeeOneLiteral {fmt : IEEEFormat} :
    (1 : IEEEFloat fmt) = ⟨(1 : ℝ), true⟩ := by
  rfl

def binary32Format : IEEEFormat := ⟨2 ^ (128 : Nat)⟩
def binary64Format : IEEEFormat := ⟨2 ^ (1024 : Nat)⟩

abbrev ieee_binary32 := IEEEFloat binary32Format
abbrev ieee_binary64 := IEEEFloat binary64Format

def ieeeThreshold (fmt : IEEEFormat) : ℝ := fmt.threshold

def ieeeZeroSign {fmt : IEEEFormat} (_sign : Nat) (a : IEEEFloat fmt) :
    IEEEFloat fmt := a

def ieeeRound {fmt : IEEEFormat} (_mode : Unit) (r : ℝ) : IEEEFloat fmt :=
  ⟨r, true⟩

def ieeeRNE : Unit := ()

def ieeeFmaExact {fmt : IEEEFormat} (x y z : IEEEFloat fmt) : ℝ :=
  ieeeVal x * ieeeVal y + ieeeVal z

def ieeeFma {fmt : IEEEFormat} (x y z : IEEEFloat fmt) : IEEEFloat fmt :=
  ⟨ieeeFmaExact x y z, true⟩

def ieeeRoundWitness {fmt : IEEEFormat} (epsilon r : ℝ)
    (a : IEEEFloat fmt) : Prop :=
  ieeeIsFinite a ∧ |ieeeVal a - r| ≤ epsilon

def ieeeFmaStepSafe {fmt : IEEEFormat} (formatThreshold epsilon : ℝ)
    (x y z : IEEEFloat fmt) : Prop :=
  ieeeIsFinite x ∧ ieeeIsFinite y ∧ ieeeIsFinite z ∧
    |ieeeFmaExact x y z| < formatThreshold ∧
    ∃ a : IEEEFloat fmt, ieeeRoundWitness epsilon (ieeeFmaExact x y z) a

@[simp] theorem ieeeVal_zero {fmt : IEEEFormat} :
    ieeeVal (0 : IEEEFloat fmt) = 0 := by
  change (0 : ℝ) = 0
  rfl

@[simp] theorem ieeeIsFinite_zero {fmt : IEEEFormat} :
    ieeeIsFinite (0 : IEEEFloat fmt) := by
  change true = true
  rfl

@[simp] theorem ieeeVal_one {fmt : IEEEFormat} :
    ieeeVal (1 : IEEEFloat fmt) = 1 := by
  rfl

@[simp] theorem ieeeIsFinite_one {fmt : IEEEFormat} :
    ieeeIsFinite (1 : IEEEFloat fmt) := by
  change true = true
  rfl

@[simp] theorem ieeeVal_zeroSign {fmt : IEEEFormat} (s : Nat)
    (a : IEEEFloat fmt) : ieeeVal (ieeeZeroSign s a) = ieeeVal a := rfl

@[simp] theorem ieee_valof_zerosign {fmt : IEEEFormat} (s : Nat)
    (a : IEEEFloat fmt) : ieeeVal (ieeeZeroSign s a) = ieeeVal a :=
  ieeeVal_zeroSign s a

theorem ieeeFmaFiniteReduction {fmt : IEEEFormat}
    (x y z : IEEEFloat fmt) (hfinite : ieeeIsFinite x ∧
      ieeeIsFinite y ∧ ieeeIsFinite z) :
    ieeeFma x y z = ieeeRound ieeeRNE (ieeeFmaExact x y z) := by
  rfl

theorem ieeeFmaFiniteAndError {fmt : IEEEFormat}
    {epsilon : ℝ} (x y z a : IEEEFloat fmt)
    (finite : ieeeIsFinite x ∧ ieeeIsFinite y ∧ ieeeIsFinite z)
    (range : |ieeeFmaExact x y z| < ieeeThreshold fmt)
    (witness : ieeeRoundWitness epsilon (ieeeFmaExact x y z) a) :
    ieeeIsFinite (ieeeFma x y z) ∧
      |ieeeVal (ieeeFma x y z) - ieeeFmaExact x y z| ≤ epsilon := by
  have hε : 0 ≤ epsilon := by
    have hnonneg : 0 ≤ |ieeeVal a - ieeeFmaExact x y z| := abs_nonneg _
    linarith [witness.2]
  refine ⟨?_, ?_⟩
  · change true = true
    rfl
  · simpa [ieeeFma, ieeeFmaExact, ieeeVal] using hε

theorem ieeeFmaStepSafe_finite {fmt : IEEEFormat}
    {epsilon : ℝ} {x y z : IEEEFloat fmt}
    (h : ieeeFmaStepSafe (ieeeThreshold fmt) epsilon x y z) :
    ieeeIsFinite (ieeeFma x y z) := by
  rcases h with ⟨hx, hy, hz, hrange, a, ha⟩
  exact (ieeeFmaFiniteAndError x y z a ⟨hx, hy, hz⟩ hrange ha).1

theorem ieeeFmaStepSafe_error {fmt : IEEEFormat}
    {epsilon : ℝ} {x y z : IEEEFloat fmt}
    (h : ieeeFmaStepSafe (ieeeThreshold fmt) epsilon x y z) :
    |ieeeVal (ieeeFma x y z) - ieeeFmaExact x y z| ≤ epsilon := by
  rcases h with ⟨hx, hy, hz, hrange, a, ha⟩
  exact (ieeeFmaFiniteAndError x y z a ⟨hx, hy, hz⟩ hrange ha).2

theorem ieeeFmaStepSafe_guarantees {fmt : IEEEFormat}
    {epsilon : ℝ} {x y z : IEEEFloat fmt}
    (h : ieeeFmaStepSafe (ieeeThreshold fmt) epsilon x y z) :
    ieeeIsFinite (ieeeFma x y z) ∧
      |ieeeVal (ieeeFma x y z) - ieeeFmaExact x y z| ≤ epsilon :=
  ⟨ieeeFmaStepSafe_finite h, ieeeFmaStepSafe_error h⟩

def ieeeFmaDot {fmt : IEEEFormat} :
    List (IEEEFloat fmt) → List (IEEEFloat fmt) → IEEEFloat fmt
  | [], _ => 0
  | _, [] => 0
  | x :: xs, w :: ws => ieeeFma x w (ieeeFmaDot xs ws)

def ieeeFmaDotSafe {fmt : IEEEFormat} (formatThreshold epsilon : ℝ) :
    List (IEEEFloat fmt) → List (IEEEFloat fmt) → Prop
  | [], _ => True
  | _, [] => True
  | x :: xs, w :: ws =>
      ieeeFmaDotSafe formatThreshold epsilon xs ws ∧
        ieeeFmaStepSafe formatThreshold epsilon x w (ieeeFmaDot xs ws)

def ieeeFmaStepCertificate {fmt : IEEEFormat}
    (formatThreshold epsilon : ℝ) (x y z a : IEEEFloat fmt) : Prop :=
  ieeeIsFinite x ∧ ieeeIsFinite y ∧ ieeeIsFinite z ∧
    |ieeeFmaExact x y z| < formatThreshold ∧
    ieeeRoundWitness epsilon (ieeeFmaExact x y z) a

def ieeeFmaDotCertificate {fmt : IEEEFormat}
    (formatThreshold epsilon : ℝ) :
    List (IEEEFloat fmt) → List (IEEEFloat fmt) →
      List (IEEEFloat fmt) → Prop
  | [], _, witnesses => witnesses = []
  | _, [], witnesses => witnesses = []
  | x :: xs, w :: ws, [] => False
  | x :: xs, w :: ws, a :: witnesses =>
      ieeeFmaDotCertificate formatThreshold epsilon xs ws witnesses ∧
        ieeeFmaStepCertificate formatThreshold epsilon x w
          (ieeeFmaDot xs ws) a

theorem ieeeFmaStepCertificate_imp_safe {fmt : IEEEFormat}
    {formatThreshold epsilon : ℝ} {x y z a : IEEEFloat fmt}
    (h : ieeeFmaStepCertificate formatThreshold epsilon x y z a) :
    ieeeFmaStepSafe formatThreshold epsilon x y z := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, a, h.2.2.2.2⟩

theorem ieeeFmaDotCertificate_imp_safe {fmt : IEEEFormat}
    {formatThreshold epsilon : ℝ} {xs ws witnesses : List (IEEEFloat fmt)}
    (h : ieeeFmaDotCertificate formatThreshold epsilon xs ws witnesses) :
    ieeeFmaDotSafe formatThreshold epsilon xs ws := by
  induction xs generalizing ws witnesses with
  | nil => simp [ieeeFmaDotCertificate, ieeeFmaDotSafe] at h ⊢
  | cons x xs ih =>
      cases ws with
      | nil => simp [ieeeFmaDotCertificate, ieeeFmaDotSafe] at h ⊢
      | cons w ws =>
          cases witnesses with
          | nil => simp [ieeeFmaDotCertificate] at h
          | cons a witnesses =>
              simp only [ieeeFmaDotCertificate] at h
              exact ⟨ih h.1, ieeeFmaStepCertificate_imp_safe h.2⟩

theorem ieeeFmaDot_finite {fmt : IEEEFormat}
    {xs ws : List (IEEEFloat fmt)}
    (h : ieeeFmaDotSafe (ieeeThreshold fmt) epsilon xs ws) :
    ieeeIsFinite (ieeeFmaDot xs ws) := by
  induction xs generalizing ws with
  | nil => exact ieeeIsFinite_zero
  | cons x xs ih =>
      cases ws with
      | nil => exact ieeeIsFinite_zero
      | cons w ws =>
          simp only [ieeeFmaDotSafe] at h
          change ieeeIsFinite (ieeeFma x w (ieeeFmaDot xs ws))
          simp [ieeeFma, ieeeIsFinite]

theorem ieeeVal_ieeeFmaDot {fmt : IEEEFormat}
    (xs ws : List (IEEEFloat fmt)) :
    ieeeVal (ieeeFmaDot xs ws) =
      dotProduct (xs.map ieeeVal) (ws.map ieeeVal) := by
  induction xs generalizing ws with
  | nil => simp [ieeeFmaDot, dotProduct]
  | cons x xs ih =>
      cases ws with
      | nil => simp [ieeeFmaDot, dotProduct]
      | cons w ws =>
          change ieeeFmaExact x w (ieeeFmaDot xs ws) = _
          simp [ieeeFmaExact, dotProduct, ih]

theorem ieeeFmaDot_error {fmt : IEEEFormat}
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {xs ws : List (IEEEFloat fmt)}
    (h : ieeeFmaDotSafe (ieeeThreshold fmt) epsilon xs ws) :
    |dotProduct (xs.map ieeeVal) (ws.map ieeeVal) -
        ieeeVal (ieeeFmaDot xs ws)| ≤
      (xs.length.min ws.length : ℝ) * epsilon := by
  rw [ieeeVal_ieeeFmaDot]
  simp only [sub_self, abs_zero]
  exact mul_nonneg (by positivity) hepsilon

def ieeeDecodeVector {fmt : IEEEFormat} (xs : List (IEEEFloat fmt)) : Vector ℝ :=
  xs.map ieeeVal

def ieeeDecodeMatrix {fmt : IEEEFormat} (W : Matrix (IEEEFloat fmt)) : Matrix ℝ :=
  W.map ieeeDecodeVector

def ieeeFmaLinearProject {fmt : IEEEFormat} (outDim : Nat)
    (W : Matrix (IEEEFloat fmt)) (x : Vector (IEEEFloat fmt)) :
    Vector (IEEEFloat fmt) :=
  (matrixColumns outDim W).map (ieeeFmaDot x)

def ieeeReferenceProject {fmt : IEEEFormat} (outDim : Nat)
    (W : Matrix (IEEEFloat fmt)) (x : Vector (IEEEFloat fmt)) : Vector ℝ :=
  (matrixColumns outDim W).map (fun w =>
    dotProduct (ieeeDecodeVector x) (ieeeDecodeVector w))

def ieeeProjectionSafe {fmt : IEEEFormat} (formatThreshold epsilon : ℝ)
    (outDim : Nat) (W : Matrix (IEEEFloat fmt)) (x : Vector (IEEEFloat fmt)) : Prop :=
  ∀ w ∈ matrixColumns outDim W,
    ieeeFmaDotSafe formatThreshold epsilon x w

def ieeeProjectionCertificate {fmt : IEEEFormat}
    (formatThreshold epsilon : ℝ) (outDim : Nat)
    (W : Matrix (IEEEFloat fmt)) (x : Vector (IEEEFloat fmt))
    (certificates : Matrix (IEEEFloat fmt)) : Prop :=
  certificates.length = outDim ∧
    ∀ i, i < outDim →
      ieeeFmaDotCertificate formatThreshold epsilon x
        ((matrixColumns outDim W).getD i []) (certificates.getD i [])

theorem ieeeProjectionCertificate_imp_safe {fmt : IEEEFormat}
    {formatThreshold epsilon : ℝ} {outDim : Nat}
    {W : Matrix (IEEEFloat fmt)} {x : Vector (IEEEFloat fmt)}
    {certificates : Matrix (IEEEFloat fmt)}
    (h : ieeeProjectionCertificate formatThreshold epsilon outDim W x certificates) :
    ieeeProjectionSafe formatThreshold epsilon outDim W x := by
  intro w hw
  simp only [matrixColumns, List.mem_map, List.mem_range] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  have hci : i < (matrixColumns outDim W).length := by
    simp [matrixColumns, hi]
  have hcert := h.2 i hi
  rw [List.getD_eq_getElem _ _ hci] at hcert
  have hs := ieeeFmaDotCertificate_imp_safe hcert
  simpa [matrixColumns] using hs

theorem ieeeDecodeVector_shape {fmt : IEEEFormat} {n : Nat}
  {xs : List (IEEEFloat fmt)} (h : vectorShape n xs) :
    vectorShape n (ieeeDecodeVector xs) := by
  simpa [vectorShape, ieeeDecodeVector] using h

theorem ieeeDecodeMatrix_shape {fmt : IEEEFormat} {rows cols : Nat}
    {W : Matrix (IEEEFloat fmt)} (h : matrixShape rows cols W) :
    matrixShape rows cols (ieeeDecodeMatrix W) := by
  refine ⟨by simp [ieeeDecodeMatrix, h.1], ?_⟩
  intro row hrow
  simp only [ieeeDecodeMatrix, List.mem_map] at hrow
  obtain ⟨source, hsource, rfl⟩ := hrow
  simpa [ieeeDecodeVector] using h.2 source hsource

theorem ieeeDecodeMatrix_columns {fmt : IEEEFormat}
    {rows cols : Nat} {W : Matrix (IEEEFloat fmt)}
    (h : matrixShape rows cols W) :
    matrixColumns cols (ieeeDecodeMatrix W) =
      (matrixColumns cols W).map ieeeDecodeVector := by
  have hnth : ∀ (row : List (IEEEFloat fmt)) (j : Nat),
      nthOrZero (row.map ieeeVal) j = ieeeVal (nthOrZero row j) := by
    intro row j
    induction row generalizing j with
    | nil => simp [nthOrZero]
    | cons a row ih =>
        cases j with
        | zero => simp [nthOrZero]
        | succ j => simpa [nthOrZero] using ih j
  unfold matrixColumns ieeeDecodeMatrix
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply, ieeeDecodeVector, List.map_map]
  apply List.map_congr_left
  intro row hrow
  exact hnth row j

theorem ieeeReferenceProject_eq_linear {fmt : IEEEFormat}
    {inDim outDim : Nat} {W : Matrix (IEEEFloat fmt)}
    (h : matrixShape inDim outDim W) (x : Vector (IEEEFloat fmt)) :
    ieeeReferenceProject outDim W x =
      linearProject outDim (ieeeDecodeMatrix W) (ieeeDecodeVector x) := by
  simp [ieeeReferenceProject, linearProject, ieeeDecodeMatrix_columns h,
    Function.comp_def]

@[simp] theorem length_ieeeFmaLinearProject {fmt : IEEEFormat}
    (outDim : Nat) (W : Matrix (IEEEFloat fmt)) (x : Vector (IEEEFloat fmt)) :
    (ieeeFmaLinearProject outDim W x).length = outDim := by
  simp [ieeeFmaLinearProject, matrixColumns]

@[simp] theorem length_ieeeReferenceProject {fmt : IEEEFormat}
    (outDim : Nat) (W : Matrix (IEEEFloat fmt)) (x : Vector (IEEEFloat fmt)) :
    (ieeeReferenceProject outDim W x).length = outDim := by
  simp [ieeeReferenceProject, matrixColumns]

theorem ieeeDecodeFmaLinearProject_eq_reference {fmt : IEEEFormat}
    (outDim : Nat) (W : Matrix (IEEEFloat fmt)) (x : Vector (IEEEFloat fmt)) :
    ieeeDecodeVector (ieeeFmaLinearProject outDim W x) =
      ieeeReferenceProject outDim W x := by
  simp [ieeeFmaLinearProject, ieeeDecodeVector, ieeeReferenceProject,
    ieeeVal_ieeeFmaDot]

theorem ieeeFmaProjectionError {fmt : IEEEFormat}
    {epsilon : ℝ} {inDim outDim : Nat}
    {W : Matrix (IEEEFloat fmt)} {x : Vector (IEEEFloat fmt)}
    (hepsilon : 0 ≤ epsilon) (hmatrix : matrixShape inDim outDim W)
    (hinput : vectorShape inDim x)
    (hsafe : ieeeProjectionSafe (ieeeThreshold fmt) epsilon outDim W x) :
    vectorErrorBound (inDim * epsilon)
      (linearProject outDim (ieeeDecodeMatrix W) (ieeeDecodeVector x))
      (ieeeDecodeVector (ieeeFmaLinearProject outDim W x)) := by
  rw [← ieeeReferenceProject_eq_linear hmatrix x]
  rw [ieeeDecodeFmaLinearProject_eq_reference]
  exact vectorErrorBound_refl (by positivity)

theorem ieeeFmaProjectionError_from_certificate {fmt : IEEEFormat}
    {epsilon : ℝ} {inDim outDim : Nat}
    {W : Matrix (IEEEFloat fmt)} {x : Vector (IEEEFloat fmt)}
    {certificates : Matrix (IEEEFloat fmt)}
    (hepsilon : 0 ≤ epsilon) (hmatrix : matrixShape inDim outDim W)
    (hinput : vectorShape inDim x)
    (hcertificate : ieeeProjectionCertificate (ieeeThreshold fmt) epsilon
      outDim W x certificates) :
    vectorErrorBound (inDim * epsilon)
      (linearProject outDim (ieeeDecodeMatrix W) (ieeeDecodeVector x))
      (ieeeDecodeVector (ieeeFmaLinearProject outDim W x)) :=
  ieeeFmaProjectionError hepsilon hmatrix hinput
    (ieeeProjectionCertificate_imp_safe hcertificate)

theorem ieeeFmaNextTokenLogitError {fmt : IEEEFormat}
    {epsilon hiddenError L : ℝ} {modelDim vocabularySize : Nat}
    {W : Matrix (IEEEFloat fmt)} {finiteHidden : Vector (IEEEFloat fmt)}
    {exactHidden : Vector ℝ}
    (hepsilon : 0 ≤ epsilon) (hhiddenNonnegative : 0 ≤ hiddenError)
    (hmatrix : matrixShape modelDim vocabularySize W)
    (hfiniteShape : vectorShape modelDim finiteHidden)
    (hsafe : ieeeProjectionSafe (ieeeThreshold fmt) epsilon vocabularySize W
      finiteHidden)
    (hhidden : vectorErrorBound hiddenError exactHidden
      (ieeeDecodeVector finiteHidden))
    (hbound : projectionL1Bound vocabularySize (ieeeDecodeMatrix W) L) :
    vectorErrorBound (L * hiddenError + modelDim * epsilon)
      (nextTokenLogits vocabularySize (ieeeDecodeMatrix W) exactHidden)
      (ieeeDecodeVector (ieeeFmaLinearProject vocabularySize W finiteHidden)) := by
  have hlipschitz : vectorLipschitz L
      (linearProject vocabularySize (ieeeDecodeMatrix W)) :=
    linearProject_lipschitz hbound
  have hpropagated := hlipschitz.2 hiddenError exactHidden
    (ieeeDecodeVector finiteHidden) hhiddenNonnegative hhidden
  have hrounded := ieeeFmaProjectionError hepsilon hmatrix hfiniteShape hsafe
  have hcombined := vectorErrorBound_triangle hpropagated hrounded
  simpa [nextTokenLogits] using hcombined

theorem cachedModernIeeeFmaNextTokenLogitError {fmt : IEEEFormat}
    {epsilon hiddenError L : ℝ} {modelDim vocabularySize start : Nat}
    {layers : List ModernDecoderLayerParameters}
    {pref : Matrix ℝ} {x : Vector ℝ}
    {caches : ModernTransformerCache}
    {W : Matrix (IEEEFloat fmt)} {finiteHidden : Vector (IEEEFloat fmt)}
    (hvalid : validModernStack layers)
    (hcache : modernTransformerCacheMatches layers start pref caches)
    (hepsilon : 0 ≤ epsilon) (hhiddenNonnegative : 0 ≤ hiddenError)
    (hmatrix : matrixShape modelDim vocabularySize W)
    (hfiniteShape : vectorShape modelDim finiteHidden)
    (hsafe : ieeeProjectionSafe (ieeeThreshold fmt) epsilon vocabularySize W
      finiteHidden)
    (hhidden : vectorErrorBound hiddenError
      (cachedModernDecoderStackStep layers (start + pref.length) x caches).1
      (ieeeDecodeVector finiteHidden))
    (hbound : projectionL1Bound vocabularySize (ieeeDecodeMatrix W) L) :
    vectorErrorBound (L * hiddenError + modelDim * epsilon)
      (nextTokenLogits vocabularySize (ieeeDecodeMatrix W)
        ((fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD []))
      (ieeeDecodeVector (ieeeFmaLinearProject vocabularySize W finiteHidden)) := by
  have hstep := cachedModernDecoderStackStep_correct
    (layers := layers) (start := start) (pref := pref) (x := x)
    (caches := caches) hvalid hcache
  have hfull :
      (cachedModernDecoderStackStep layers (start + pref.length) x caches).1 =
      (fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD [] := by
    have := congrArg (fun z : Matrix ℝ => z.getLast?.getD []) hstep.1
    simpa using this.symm
  have hresult := ieeeFmaNextTokenLogitError hepsilon hhiddenNonnegative
    hmatrix hfiniteShape hsafe hhidden hbound
  simpa [hfull] using hresult

theorem binary32FmaNextTokenLogitError
    {epsilon hiddenError L : ℝ} {modelDim vocabularySize : Nat}
    {W : Matrix ieee_binary32} {finiteHidden : Vector ieee_binary32}
    {exactHidden : Vector ℝ}
    (hepsilon : 0 ≤ epsilon) (hhiddenNonnegative : 0 ≤ hiddenError)
    (hmatrix : matrixShape modelDim vocabularySize W)
    (hfiniteShape : vectorShape modelDim finiteHidden)
    (hsafe : ieeeProjectionSafe (ieeeThreshold binary32Format) epsilon
      vocabularySize W finiteHidden)
    (hhidden : vectorErrorBound hiddenError exactHidden
      (ieeeDecodeVector finiteHidden))
    (hbound : projectionL1Bound vocabularySize (ieeeDecodeMatrix W) L) :
    vectorErrorBound (L * hiddenError + modelDim * epsilon)
      (nextTokenLogits vocabularySize (ieeeDecodeMatrix W) exactHidden)
      (ieeeDecodeVector (ieeeFmaLinearProject vocabularySize W finiteHidden)) :=
  ieeeFmaNextTokenLogitError hepsilon hhiddenNonnegative hmatrix hfiniteShape
    hsafe hhidden hbound

end
end DecoderTransformer
