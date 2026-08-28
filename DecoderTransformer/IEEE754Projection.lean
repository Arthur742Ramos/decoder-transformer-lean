import DecoderTransformer.DyadicFinitePrecision
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# IEEE-754 projection refinement

This is the Lean counterpart of `IEEE_754_Projection.thy`.  The source
development uses the AFP's parameterized IEEE model.  The model below keeps
the same semantic boundary in Lean: a format has exponent and fraction widths,
an IEEE value is represented by its sign/exponent/fraction fields, finite
values decode by the IEEE normal/subnormal formula, and the nearest-value
rounding operation is selected from the finite representable values.

The source AFP leaves the exact halfway preference of its RNE selector
explicitly unresolved.  Accordingly, the nearest-value selector here proves
the same metric property without making a stronger tie-breaking claim.
-/

structure IEEEFormat where
  exponentBits : Nat
  fractionBits : Nat
  exponentBits_gt_one : 1 < exponentBits
  fractionBits_pos : 0 < fractionBits

instance ieeeFormatExponentModulusNeZero (fmt : IEEEFormat) :
    NeZero (2 ^ fmt.exponentBits) :=
  ⟨by positivity⟩

instance ieeeFormatFractionModulusNeZero (fmt : IEEEFormat) :
    NeZero (2 ^ fmt.fractionBits) :=
  ⟨by positivity⟩

def ieeeBias (fmt : IEEEFormat) : Nat :=
  2 ^ (fmt.exponentBits - 1) - 1

def ieeeExponentMax (fmt : IEEEFormat) : Nat :=
  2 ^ fmt.exponentBits - 1

structure IEEEFloat (fmt : IEEEFormat) where
  sign : Bool
  exponent : Fin (2 ^ fmt.exponentBits)
  fraction : Fin (2 ^ fmt.fractionBits)
  deriving DecidableEq, Fintype

def ieeeZero (fmt : IEEEFormat) : IEEEFloat fmt :=
  ⟨false, Fin.ofNat _ 0, Fin.ofNat _ 0⟩

def ieeeOne (fmt : IEEEFormat) : IEEEFloat fmt :=
  ⟨false, Fin.ofNat _ (ieeeBias fmt), Fin.ofNat _ 0⟩

instance (fmt : IEEEFormat) : Zero (IEEEFloat fmt) := ⟨ieeeZero fmt⟩
instance (fmt : IEEEFormat) : OfNat (IEEEFloat fmt) 0 := ⟨ieeeZero fmt⟩
instance (fmt : IEEEFormat) : OfNat (IEEEFloat fmt) 1 := ⟨ieeeOne fmt⟩

def ieeeSignValue (s : Bool) : ℝ := if s then -1 else 1

def ieeeVal {fmt : IEEEFormat} (x : IEEEFloat fmt) : ℝ :=
  ieeeSignValue x.sign *
    if x.exponent.val = 0 then
      (2 / (2 : ℝ) ^ ieeeBias fmt) *
        ((x.fraction.val : ℝ) / (2 : ℝ) ^ fmt.fractionBits)
    else
      ((2 : ℝ) ^ x.exponent.val / (2 : ℝ) ^ ieeeBias fmt) *
        (1 + (x.fraction.val : ℝ) / (2 : ℝ) ^ fmt.fractionBits)

def ieeeIsNaN {fmt : IEEEFormat} (x : IEEEFloat fmt) : Prop :=
  x.exponent.val = ieeeExponentMax fmt ∧ x.fraction.val ≠ 0

def ieeeIsInfinity {fmt : IEEEFormat} (x : IEEEFloat fmt) : Prop :=
  x.exponent.val = ieeeExponentMax fmt ∧ x.fraction.val = 0

def ieeeIsNormal {fmt : IEEEFormat} (x : IEEEFloat fmt) : Prop :=
  0 < x.exponent.val ∧ x.exponent.val < ieeeExponentMax fmt

def ieeeIsDenormal {fmt : IEEEFormat} (x : IEEEFloat fmt) : Prop :=
  x.exponent.val = 0 ∧ x.fraction.val ≠ 0

def ieeeIsZero {fmt : IEEEFormat} (x : IEEEFloat fmt) : Prop :=
  x.exponent.val = 0 ∧ x.fraction.val = 0

def ieeeIsFinite {fmt : IEEEFormat} (x : IEEEFloat fmt) : Prop :=
  x.exponent.val < ieeeExponentMax fmt

def binary32Format : IEEEFormat :=
  { exponentBits := 8, fractionBits := 23
    exponentBits_gt_one := by norm_num
    fractionBits_pos := by norm_num }

def binary64Format : IEEEFormat :=
  { exponentBits := 11, fractionBits := 52
    exponentBits_gt_one := by norm_num
    fractionBits_pos := by norm_num }

abbrev ieee_binary32 := IEEEFloat binary32Format
abbrev ieee_binary64 := IEEEFloat binary64Format

def ieeeLargest (fmt : IEEEFormat) : ℝ :=
  ((2 : ℝ) ^ (ieeeExponentMax fmt - 1) / (2 : ℝ) ^ ieeeBias fmt) *
    (2 - 1 / (2 : ℝ) ^ fmt.fractionBits)

def ieeeThreshold (fmt : IEEEFormat) : ℝ :=
  ((2 : ℝ) ^ (ieeeExponentMax fmt - 1) / (2 : ℝ) ^ ieeeBias fmt) *
    (2 - 1 / (2 : ℝ) ^ (fmt.fractionBits + 1))

def ieeeSign {fmt : IEEEFormat} (x : IEEEFloat fmt) : Nat :=
  if x.sign then 1 else 0

def ieeeNeg {fmt : IEEEFormat} (x : IEEEFloat fmt) : IEEEFloat fmt :=
  { x with sign := !x.sign }

instance (fmt : IEEEFormat) : Neg (IEEEFloat fmt) := ⟨ieeeNeg⟩

def ieeePlusInfinity (fmt : IEEEFormat) : IEEEFloat fmt :=
  ⟨false, Fin.ofNat _ (ieeeExponentMax fmt), Fin.ofNat _ 0⟩

def ieeeMinusInfinity (fmt : IEEEFormat) : IEEEFloat fmt :=
  -ieeePlusInfinity fmt

def ieeeNaN (fmt : IEEEFormat) : IEEEFloat fmt :=
  ⟨false, Fin.ofNat _ (ieeeExponentMax fmt), Fin.ofNat _ 1⟩

noncomputable def ieeeZeroSign {fmt : IEEEFormat} (s : Nat) (a : IEEEFloat fmt) :
    IEEEFloat fmt := by
  classical
  exact if ieeeIsZero a then
    if s % 2 = 0 then (0 : IEEEFloat fmt) else -(0 : IEEEFloat fmt)
  else a

def ieeeFiniteFloats (fmt : IEEEFormat) : Finset (IEEEFloat fmt) := by
  classical exact Finset.univ.filter ieeeIsFinite

theorem ieeeBias_pos (fmt : IEEEFormat) : 0 < ieeeBias fmt := by
  unfold ieeeBias
  have he : 1 < fmt.exponentBits := fmt.exponentBits_gt_one
  have hpow : 1 < 2 ^ (fmt.exponentBits - 1) := by
    have h := Nat.pow_lt_pow_right (a := 2) (m := 0)
      (n := fmt.exponentBits - 1) (by norm_num)
      (Nat.sub_pos_iff_lt.mpr (by omega))
    simpa using h
  omega

theorem ieeeBias_lt_modulus (fmt : IEEEFormat) :
    ieeeBias fmt < 2 ^ fmt.exponentBits := by
  unfold ieeeBias
  have he : 1 < fmt.exponentBits := fmt.exponentBits_gt_one
  have hpow : 0 < 2 ^ (fmt.exponentBits - 1) := by positivity
  have hlt : 2 ^ (fmt.exponentBits - 1) < 2 ^ fmt.exponentBits := by
    apply Nat.pow_lt_pow_right
    · norm_num
    · omega
  calc
    2 ^ (fmt.exponentBits - 1) - 1 < 2 ^ (fmt.exponentBits - 1) :=
      Nat.sub_lt (by positivity) (by norm_num)
    _ < 2 ^ fmt.exponentBits := hlt

theorem ieeeExponentMax_pos (fmt : IEEEFormat) :
    0 < ieeeExponentMax fmt := by
  unfold ieeeExponentMax
  have he : 1 < fmt.exponentBits := fmt.exponentBits_gt_one
  have hpow : 1 < 2 ^ fmt.exponentBits := by
    have h := Nat.pow_lt_pow_right (a := 2) (m := 0)
      (n := fmt.exponentBits) (by norm_num) (by omega)
    simpa using h
  exact Nat.sub_pos_iff_lt.mpr hpow

@[simp] theorem ieeeVal_zero {fmt : IEEEFormat} :
    ieeeVal (0 : IEEEFloat fmt) = 0 := by
  change ieeeVal (ieeeZero fmt) = 0
  simp [ieeeVal, ieeeZero, ieeeSignValue]

@[simp] theorem ieeeVal_neg_zero {fmt : IEEEFormat} :
    ieeeVal (-(0 : IEEEFloat fmt)) = 0 := by
  change ieeeVal (ieeeNeg (ieeeZero fmt)) = 0
  simp [ieeeVal, ieeeNeg, ieeeZero, ieeeSignValue]

@[simp] theorem ieeeIsFinite_zero {fmt : IEEEFormat} :
    ieeeIsFinite (0 : IEEEFloat fmt) := by
  change (ieeeZero fmt).exponent.val < ieeeExponentMax fmt
  simp only [ieeeZero, Fin.val_ofNat]
  exact ieeeExponentMax_pos fmt

@[simp] theorem ieeeVal_one {fmt : IEEEFormat} :
    ieeeVal (1 : IEEEFloat fmt) = 1 := by
  change ieeeVal (ieeeOne fmt) = 1
  have hb := ieeeBias_lt_modulus fmt
  have hbpos := ieeeBias_pos fmt
  have hbne : ieeeBias fmt ≠ 0 := Nat.ne_of_gt hbpos
  simp [ieeeVal, ieeeOne, ieeeSignValue, hb, hbne, Nat.mod_eq_of_lt]

@[simp] theorem ieeeIsFinite_one {fmt : IEEEFormat} :
    ieeeIsFinite (1 : IEEEFloat fmt) := by
  change (ieeeOne fmt).exponent.val < ieeeExponentMax fmt
  simp only [ieeeOne, Fin.val_ofNat]
  have hb := ieeeBias_lt_modulus fmt
  have he : 1 < fmt.exponentBits := fmt.exponentBits_gt_one
  rw [Nat.mod_eq_of_lt hb]
  unfold ieeeBias ieeeExponentMax
  have hlt : 2 ^ (fmt.exponentBits - 1) < 2 ^ fmt.exponentBits := by
    apply Nat.pow_lt_pow_right
    · norm_num
    · omega
  have hpone : 1 ≤ 2 ^ (fmt.exponentBits - 1) := by
    exact Nat.one_le_pow _ _ (by norm_num)
  exact Nat.sub_lt_sub_right hpone hlt

theorem ieeeIsFinite_not_nan {fmt : IEEEFormat} {x : IEEEFloat fmt}
    (hfinite : ieeeIsFinite x) : ¬ ieeeIsNaN x := by
  intro hnan
  unfold ieeeIsFinite at hfinite
  unfold ieeeIsNaN at hnan
  omega

theorem ieeeIsFinite_not_infinity {fmt : IEEEFormat} {x : IEEEFloat fmt}
    (hfinite : ieeeIsFinite x) : ¬ ieeeIsInfinity x := by
  intro hinfinity
  unfold ieeeIsFinite at hfinite
  unfold ieeeIsInfinity at hinfinity
  omega

@[ext] theorem ieeeFloat_ext {fmt : IEEEFormat}
    {x y : IEEEFloat fmt} (hsign : x.sign = y.sign)
    (hexponent : x.exponent = y.exponent)
    (hfraction : x.fraction = y.fraction) : x = y := by
  cases x
  cases y
  simp_all

@[simp] theorem ieeeZeroLiteral {fmt : IEEEFormat} :
    (0 : IEEEFloat fmt) = ieeeZero fmt := rfl

@[simp] theorem ieeeOneLiteral {fmt : IEEEFormat} :
    (1 : IEEEFloat fmt) = ieeeOne fmt := rfl

@[simp] theorem ieeeVal_zeroSign {fmt : IEEEFormat} (s : Nat)
    (a : IEEEFloat fmt) : ieeeVal (ieeeZeroSign s a) = ieeeVal a := by
  classical
  by_cases ha : ieeeIsZero a
  · have hval : ieeeVal a = 0 := by
      simp [ieeeVal, ha.1, ha.2, ieeeSignValue]
    by_cases hs : s % 2 = 0
    · calc
        ieeeVal (ieeeZeroSign s a) = ieeeVal (0 : IEEEFloat fmt) := by
          simp [ieeeZeroSign, ha, hs]
        _ = 0 := ieeeVal_zero
        _ = ieeeVal a := hval.symm
    · calc
        ieeeVal (ieeeZeroSign s a) = ieeeVal (-(0 : IEEEFloat fmt)) := by
          simp [ieeeZeroSign, ha, hs]
        _ = 0 := ieeeVal_neg_zero
        _ = ieeeVal a := hval.symm
  · simp [ieeeZeroSign, ha]

@[simp] theorem ieee_valof_zerosign {fmt : IEEEFormat} (s : Nat)
    (a : IEEEFloat fmt) : ieeeVal (ieeeZeroSign s a) = ieeeVal a :=
  ieeeVal_zeroSign s a

theorem ieeeIsFinite_zeroSign {fmt : IEEEFormat} (s : Nat)
    (a : IEEEFloat fmt) (ha : ieeeIsFinite a) :
    ieeeIsFinite (ieeeZeroSign s a) := by
  classical
  by_cases hz : ieeeIsZero a
  · by_cases hs : s % 2 = 0
    · have hzero : ieeeZeroSign s a = (0 : IEEEFloat fmt) := by
        simp [ieeeZeroSign, hz, hs]
      rw [hzero]
      exact ieeeIsFinite_zero
    · have hzero : ieeeZeroSign s a = -(0 : IEEEFloat fmt) := by
        simp [ieeeZeroSign, hz, hs]
      rw [hzero]
      change (ieeeNeg (ieeeZero fmt)).exponent.val < ieeeExponentMax fmt
      simp [ieeeNeg, ieeeZero]
      exact ieeeExponentMax_pos fmt
  · simpa [ieeeZeroSign, hz] using ha

theorem ieeeThreshold_pos (fmt : IEEEFormat) : 0 < ieeeThreshold fmt := by
  unfold ieeeThreshold
  have hd : 0 < (2 : ℝ) ^ (fmt.fractionBits + 1) := by positivity
  have hp : 1 < (2 : ℝ) ^ (fmt.fractionBits + 1) := by
    have h := Nat.pow_lt_pow_right (a := 2) (m := 0)
      (n := fmt.fractionBits + 1) (by norm_num) (by omega)
    exact_mod_cast h
  have hsmall : 1 / (2 : ℝ) ^ (fmt.fractionBits + 1) < 1 := by
    rw [div_lt_iff₀ hd]
    simpa using hp
  have hlast : 0 < (2 : ℝ) -
      1 / (2 : ℝ) ^ (fmt.fractionBits + 1) := by linarith
  positivity

theorem ieeeZero_mem_finiteFloats {fmt : IEEEFormat} :
    (0 : IEEEFloat fmt) ∈ ieeeFiniteFloats fmt := by
  classical
  change (0 : IEEEFloat fmt) ∈ (Finset.univ.filter ieeeIsFinite)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ieeeIsFinite_zero⟩

noncomputable def ieeeClosest {fmt : IEEEFormat} (r : ℝ) : IEEEFloat fmt := by
  classical
  exact Classical.choose (Finset.exists_min_image (ieeeFiniteFloats fmt)
    (fun a => |ieeeVal a - r|) ⟨0, ieeeZero_mem_finiteFloats⟩)

theorem ieeeClosest_finite {fmt : IEEEFormat} (r : ℝ) :
    ieeeIsFinite (ieeeClosest (fmt := fmt) r) := by
  classical
  have h := Classical.choose_spec (Finset.exists_min_image
    (ieeeFiniteFloats fmt) (fun a => |ieeeVal a - r|)
      ⟨0, ieeeZero_mem_finiteFloats⟩)
  exact (Finset.mem_filter.mp h.1).2

theorem ieeeClosest_spec {fmt : IEEEFormat} (r : ℝ) (a : IEEEFloat fmt)
    (ha : ieeeIsFinite a) :
    |ieeeVal (ieeeClosest (fmt := fmt) r) - r| ≤ |ieeeVal a - r| := by
  classical
  have h := Classical.choose_spec (Finset.exists_min_image
    (ieeeFiniteFloats fmt) (fun a => |ieeeVal a - r|)
      ⟨0, ieeeZero_mem_finiteFloats⟩)
  exact h.2 a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)

def ieeeRound {fmt : IEEEFormat} (_mode : Unit) (r : ℝ) : IEEEFloat fmt :=
  if r ≤ -ieeeThreshold fmt then ieeeMinusInfinity fmt
  else if r ≥ ieeeThreshold fmt then ieeePlusInfinity fmt
  else ieeeClosest r

def ieeeRNE : Unit := ()

theorem ieeeRound_finite {fmt : IEEEFormat} {r : ℝ}
    (hrange : |r| < ieeeThreshold fmt) :
    ieeeIsFinite (ieeeRound (fmt := fmt) ieeeRNE r) := by
  rcases (abs_lt.mp hrange) with ⟨hlo, hhi⟩
  have hleft : ¬ r ≤ -ieeeThreshold fmt := not_le_of_gt hlo
  have hright : ¬ r ≥ ieeeThreshold fmt := not_le_of_gt hhi
  simp [ieeeRound, hleft, hright, ieeeClosest_finite]

theorem ieeeRound_closest {fmt : IEEEFormat} {r : ℝ}
    (hrange : |r| < ieeeThreshold fmt) (a : IEEEFloat fmt)
    (ha : ieeeIsFinite a) :
    |ieeeVal (ieeeRound (fmt := fmt) ieeeRNE r) - r| ≤ |ieeeVal a - r| := by
  rcases (abs_lt.mp hrange) with ⟨hlo, hhi⟩
  have hleft : ¬ r ≤ -ieeeThreshold fmt := not_le_of_gt hlo
  have hright : ¬ r ≥ ieeeThreshold fmt := not_le_of_gt hhi
  simpa [ieeeRound, hleft, hright] using ieeeClosest_spec r a ha

def ieeeFmaExact {fmt : IEEEFormat} (x y z : IEEEFloat fmt) : ℝ :=
  ieeeVal x * ieeeVal y + ieeeVal z

noncomputable def ieeeFma {fmt : IEEEFormat} (x y z : IEEEFloat fmt) :
    IEEEFloat fmt := by
  classical
  let signP := if ieeeSign x = ieeeSign y then 0 else 1
  let infP := ieeeIsInfinity x ∨ ieeeIsInfinity y
  exact if ieeeIsNaN x ∨ ieeeIsNaN y ∨ ieeeIsNaN z then
      ieeeNaN fmt
    else if (ieeeIsInfinity x ∧ ieeeIsZero y) ∨
        (ieeeIsZero x ∧ ieeeIsInfinity y) ∨
        (ieeeIsInfinity z ∧ infP ∧ signP ≠ ieeeSign z) then
      ieeeNaN fmt
    else if (ieeeIsInfinity z ∧ ieeeSign z = 0) ∨
        (infP ∧ signP = 0) then
      ieeePlusInfinity fmt
    else if (ieeeIsInfinity z ∧ ieeeSign z = 1) ∨
        (infP ∧ signP = 1) then
      ieeeMinusInfinity fmt
    else
      let r1 := ieeeVal x * ieeeVal y
      let r2 := ieeeVal z
      let r := r1 + r2
      if r = 0 then
        if r1 = 0 ∧ r2 = 0 ∧ signP = ieeeSign z then
          ieeeZeroSign signP (0 : IEEEFloat fmt)
        else (0 : IEEEFloat fmt)
      else
        ieeeZeroSign (if r < 0 then 1 else 0)
          (ieeeRound ieeeRNE r)

def ieeeRoundWitness {fmt : IEEEFormat} (epsilon r : ℝ)
    (a : IEEEFloat fmt) : Prop :=
  ieeeIsFinite a ∧ |ieeeVal a - r| ≤ epsilon

def ieeeFmaStepSafe {fmt : IEEEFormat} (formatThreshold epsilon : ℝ)
    (x y z : IEEEFloat fmt) : Prop :=
  ieeeIsFinite x ∧ ieeeIsFinite y ∧ ieeeIsFinite z ∧
    |ieeeFmaExact x y z| < formatThreshold ∧
    ∃ a : IEEEFloat fmt, ieeeRoundWitness epsilon (ieeeFmaExact x y z) a

theorem ieeeFmaFiniteReduction {fmt : IEEEFormat}
    (x y z : IEEEFloat fmt) (hfinite : ieeeIsFinite x ∧
      ieeeIsFinite y ∧ ieeeIsFinite z) :
    ieeeFma x y z =
      (let r := ieeeFmaExact x y z
       let signP := if ieeeSign x = ieeeSign y then 0 else 1
       if r = 0 then
         if ieeeVal x * ieeeVal y = 0 ∧ ieeeVal z = 0 ∧
             signP = ieeeSign z then
           ieeeZeroSign signP (0 : IEEEFloat fmt)
         else (0 : IEEEFloat fmt)
       else
         ieeeZeroSign (if r < 0 then 1 else 0)
           (ieeeRound ieeeRNE r)) := by
  rcases hfinite with ⟨hx, hy, hz⟩
  have hxnan : ¬ ieeeIsNaN x := ieeeIsFinite_not_nan hx
  have hynan : ¬ ieeeIsNaN y := ieeeIsFinite_not_nan hy
  have hznan : ¬ ieeeIsNaN z := ieeeIsFinite_not_nan hz
  have hxinf : ¬ ieeeIsInfinity x := ieeeIsFinite_not_infinity hx
  have hyinf : ¬ ieeeIsInfinity y := ieeeIsFinite_not_infinity hy
  have hzinf : ¬ ieeeIsInfinity z := ieeeIsFinite_not_infinity hz
  simp [ieeeFma, hxnan, hynan, hznan, hxinf, hyinf, hzinf,
    ieeeFmaExact]
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
  have hred := ieeeFmaFiniteReduction x y z finite
  rw [hred]
  dsimp
  by_cases hr : ieeeFmaExact x y z = 0
  · simp only [hr, ↓reduceIte]
    by_cases hzero : ieeeVal x * ieeeVal y = 0 ∧
        ieeeVal z = 0 ∧
        (if ieeeSign x = ieeeSign y then 0 else 1) = ieeeSign z
    · simp only [hzero, true_and, if_true]
      refine ⟨?_, ?_⟩
      · exact ieeeIsFinite_zeroSign _ _ ieeeIsFinite_zero
      · rw [ieeeVal_zeroSign]
        rw [show ieeeZero fmt = (0 : IEEEFloat fmt) by rfl]
        simp only [ieeeVal_zero, abs_zero]
        norm_num
        exact hε
    · simp only [hzero, false_and, if_false]
      refine ⟨ieeeIsFinite_zero, ?_⟩
      rw [show ieeeZero fmt = (0 : IEEEFloat fmt) by rfl]
      simp only [ieeeVal_zero, abs_zero]
      norm_num
      exact hε
  · simp only [hr, ↓reduceIte]
    have hroundFinite :
        ieeeIsFinite (ieeeRound (fmt := fmt) ieeeRNE (ieeeFmaExact x y z)) :=
      ieeeRound_finite range
    have hroundBound :
        |ieeeVal (ieeeRound (fmt := fmt) ieeeRNE (ieeeFmaExact x y z)) -
            ieeeFmaExact x y z| ≤
          |ieeeVal a - ieeeFmaExact x y z| :=
      ieeeRound_closest range a witness.1
    refine ⟨ieeeIsFinite_zeroSign _ _ hroundFinite, ?_⟩
    rw [ieeeVal_zeroSign]
    exact hroundBound.trans witness.2

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
          exact ieeeFmaStepSafe_finite h.2

theorem ieeeFmaDot_error {fmt : IEEEFormat}
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {xs ws : List (IEEEFloat fmt)}
    (h : ieeeFmaDotSafe (ieeeThreshold fmt) epsilon xs ws) :
    |dotProduct (xs.map ieeeVal) (ws.map ieeeVal) -
        ieeeVal (ieeeFmaDot xs ws)| ≤
      (xs.length.min ws.length : ℝ) * epsilon := by
  induction xs generalizing ws with
  | nil =>
      simp [dotProduct, ieeeFmaDot, ieeeVal, ieeeZero, ieeeSignValue]
  | cons x xs ih =>
      cases ws with
      | nil =>
          have hnonneg :
              0 ≤ (min (x :: xs).length ([] : List (IEEEFloat fmt)).length : ℝ) *
                epsilon :=
            mul_nonneg (by positivity) hepsilon
          simpa [dotProduct, ieeeFmaDot, ieeeVal, ieeeZero, ieeeSignValue] using hnonneg
      | cons w ws =>
          simp only [ieeeFmaDotSafe] at h
          have htail := ih (ws := ws) h.1
          have htail' :
              |dotProduct (xs.map ieeeVal) (ws.map ieeeVal) -
                  ieeeVal (ieeeFmaDot xs ws)| ≤
                ((xs.length.min ws.length : Nat) : ℝ) * epsilon := htail
          have hlocal := ieeeFmaStepSafe_error h.2
          have hlocal' :
              |ieeeFmaExact x w (ieeeFmaDot xs ws) -
                ieeeVal (ieeeFma x w (ieeeFmaDot xs ws))| ≤ epsilon := by
            simpa [abs_sub_comm] using hlocal
          have hdecomp :
              dotProduct ((x :: xs).map ieeeVal) ((w :: ws).map ieeeVal) -
                ieeeVal (ieeeFmaDot (x :: xs) (w :: ws)) =
              (dotProduct (xs.map ieeeVal) (ws.map ieeeVal) -
                ieeeVal (ieeeFmaDot xs ws)) +
                ((ieeeVal x * ieeeVal w + ieeeVal (ieeeFmaDot xs ws)) -
                  ieeeVal (ieeeFma x w (ieeeFmaDot xs ws))) := by
            simp [dotProduct, ieeeFmaDot, ieeeFmaExact]
            ring
          calc
            |dotProduct ((x :: xs).map ieeeVal) ((w :: ws).map ieeeVal) -
                ieeeVal (ieeeFmaDot (x :: xs) (w :: ws))| =
                |(dotProduct (xs.map ieeeVal) (ws.map ieeeVal) -
                    ieeeVal (ieeeFmaDot xs ws)) +
                  ((ieeeVal x * ieeeVal w + ieeeVal (ieeeFmaDot xs ws)) -
                    ieeeVal (ieeeFma x w (ieeeFmaDot xs ws)))| := by
                      rw [hdecomp]
            _ ≤ |dotProduct (xs.map ieeeVal) (ws.map ieeeVal) -
                  ieeeVal (ieeeFmaDot xs ws)| +
                |(ieeeVal x * ieeeVal w + ieeeVal (ieeeFmaDot xs ws)) -
                  ieeeVal (ieeeFma x w (ieeeFmaDot xs ws))| :=
                    abs_add_le _ _
            _ ≤ ((xs.length.min ws.length : Nat) : ℝ) * epsilon + epsilon :=
                  add_le_add htail' hlocal'
            _ = ((x :: xs).length.min (w :: ws).length : Nat) * epsilon := by
                  simp only [List.length_cons]
                  have hsucc :
                      (xs.length + 1).min (ws.length + 1) =
                        xs.length.min ws.length + 1 := by
                    simpa [Nat.succ_eq_add_one] using
                      (Nat.succ_min_succ xs.length ws.length)
                  rw [hsucc]
                  norm_num [Nat.cast_add]
                  ring

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
    | nil => simp [nthOrZero, ieeeVal, ieeeZero, ieeeSignValue]
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
  refine ⟨?_, ?_⟩
  · simp [ieeeReferenceProject, ieeeFmaLinearProject, ieeeDecodeVector,
      matrixColumns]
  · intro i hi
    have hiout : i < outDim := by
      simpa [ieeeReferenceProject, matrixColumns] using hi
    let columns := matrixColumns outDim W
    have hcolumns := matrixColumns_shape hmatrix
    have hwi : i < columns.length := by
      simpa [columns, hcolumns.1] using hiout
    have hcol : (columns[i]'hwi).length = inDim :=
      matrixShape_nth hcolumns hiout
    have hsafeColumn : ieeeFmaDotSafe (ieeeThreshold fmt) epsilon x
        (columns[i]'hwi) := by
      exact hsafe (columns[i]'hwi) (List.getElem_mem hwi)
    have hraw := ieeeFmaDot_error hepsilon hsafeColumn
    rw [hcol] at hraw
    have hminNat : ((x.length.min inDim : Nat) : ℝ) ≤ (inDim : ℝ) := by
      exact_mod_cast Nat.min_le_right x.length inDim
    have hscaledNat : ((x.length.min inDim : Nat) : ℝ) * epsilon ≤
        (inDim : ℝ) * epsilon :=
      mul_le_mul_of_nonneg_right hminNat hepsilon
    have hprojX :
        (ieeeReferenceProject outDim W x).getD i 0 =
          dotProduct (ieeeDecodeVector x)
            (ieeeDecodeVector (columns.getD i [])) := by
      change (columns.map (fun w =>
        dotProduct (ieeeDecodeVector x) (ieeeDecodeVector w))).getD i 0 = _
      have hdefault : (0 : ℝ) = dotProduct (ieeeDecodeVector x)
          (ieeeDecodeVector ([] : List (IEEEFloat fmt))) := by
        change (0 : ℝ) = dotProduct (ieeeDecodeVector x) []
        simp [dotProduct]
      rw [hdefault, List.getD_map]
    have hprojY :
        (ieeeDecodeVector (ieeeFmaLinearProject outDim W x)).getD i 0 =
          ieeeVal (ieeeFmaDot x (columns.getD i [])) := by
      simp only [ieeeDecodeVector, ieeeFmaLinearProject, List.map_map,
        Function.comp_apply]
      change (columns.map (fun w => ieeeVal (ieeeFmaDot x w))).getD i 0 = _
      have hdefault : (0 : ℝ) = ieeeVal (ieeeFmaDot x
          ([] : List (IEEEFloat fmt))) := by
        have hdotzero : ieeeFmaDot x ([] : List (IEEEFloat fmt)) =
            (0 : IEEEFloat fmt) := by
          cases x <;> rfl
        rw [hdotzero, ieeeVal_zero]
      rw [hdefault, List.getD_map]
    have hget : columns.getD i [] = columns[i]'hwi :=
      List.getD_eq_getElem _ _ hwi
    rw [hprojX, hprojY, hget]
    exact hraw.trans hscaledNat

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
