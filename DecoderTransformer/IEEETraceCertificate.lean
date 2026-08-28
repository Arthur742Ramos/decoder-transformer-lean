import DecoderTransformer.IEEE754Projection
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Reusable finite-precision trace certificates

The previous accumulator is a nearest-value witness for each fused
multiply-add in a dot product.  This is the Lean counterpart of
`IEEE_Trace_Certificate.thy`; the trace theorem is independent of any one
model checkpoint.
-/

def ieeeFmaDotTailWitnesses {fmt : IEEEFormat} :
    List (IEEEFloat fmt) → List (IEEEFloat fmt) → List (IEEEFloat fmt)
  | [], _ => []
  | _, [] => []
  | _ :: xs, _ :: ws => ieeeFmaDot xs ws :: ieeeFmaDotTailWitnesses xs ws

theorem ieeeFmaDotAbsBound {fmt : IEEEFormat}
    {a b : ℝ} {xs ws : List (IEEEFloat fmt)}
    (hlengths : xs.length = ws.length)
    (hx : ∀ x ∈ xs, |ieeeVal x| ≤ a)
    (hw : ∀ w ∈ ws, |ieeeVal w| ≤ b) :
    |dotProduct (xs.map ieeeVal) (ws.map ieeeVal)| ≤
      (xs.length : ℝ) * (a * b) := by
  induction xs generalizing ws with
  | nil =>
      have hws : ws = [] := by
        cases ws with
        | nil => rfl
        | cons w ws => simp at hlengths
      subst hws
      simp [dotProduct]
  | cons x xs ih =>
      cases ws with
      | nil => simp at hlengths
      | cons w ws =>
          have htailLength : xs.length = ws.length := by simpa using hlengths
          have hxHead : |ieeeVal x| ≤ a := hx x (by simp)
          have hxTail : ∀ y ∈ xs, |ieeeVal y| ≤ a := by
            intro y hy
            exact hx y (by simp [hy])
          have hwHead : |ieeeVal w| ≤ b := hw w (by simp)
          have hwTail : ∀ y ∈ ws, |ieeeVal y| ≤ b := by
            intro y hy
            exact hw y (by simp [hy])
          have htail := ih htailLength hxTail hwTail
          have ha : 0 ≤ a := le_trans (abs_nonneg _) hxHead
          have hb : 0 ≤ b := le_trans (abs_nonneg _) hwHead
          have hproduct :
              |ieeeVal x * ieeeVal w| ≤ a * b := by
            rw [abs_mul]
            exact mul_le_mul hxHead hwHead (abs_nonneg _) ha
          have htriangle := abs_add_le
            (ieeeVal x * ieeeVal w)
            (dotProduct (xs.map ieeeVal) (ws.map ieeeVal))
          have hsum :
              |ieeeVal x * ieeeVal w +
                dotProduct (xs.map ieeeVal) (ws.map ieeeVal)| ≤
                a * b + (xs.length : ℝ) * (a * b) := by
            linarith
          simpa [dotProduct, Nat.cast_add, add_mul, add_comm] using hsum

theorem ieeeFmaDotTailCertificate {fmt : IEEEFormat}
    {xs ws : List (IEEEFloat fmt)}
    (hlengths : xs.length = ws.length)
    (hlengthBound : xs.length ≤ 64)
    (hxFinite : ∀ x ∈ xs, ieeeIsFinite x)
    (hwFinite : ∀ w ∈ ws, ieeeIsFinite w)
    (hxSmall : ∀ x ∈ xs, |ieeeVal x| < 1)
    (hwSmall : ∀ w ∈ ws, |ieeeVal w| < 1)
    (hthreshold : 2 * (xs.length : ℝ) + 1 < ieeeThreshold fmt) :
    ieeeFmaDotCertificate (ieeeThreshold fmt) 1 xs ws
      (ieeeFmaDotTailWitnesses xs ws) := by
  induction xs generalizing ws with
  | nil =>
      cases ws with
      | nil => simp [ieeeFmaDotCertificate, ieeeFmaDotTailWitnesses]
      | cons w ws => simp at hlengths
  | cons x xs ih =>
      cases ws with
      | nil => simp at hlengths
      | cons w ws =>
          have htailLengths : xs.length = ws.length := by simpa using hlengths
          have htailFiniteX : ∀ y ∈ xs, ieeeIsFinite y := by
            intro y hy
            exact hxFinite y (by simp [hy])
          have htailFiniteW : ∀ y ∈ ws, ieeeIsFinite y := by
            intro y hy
            exact hwFinite y (by simp [hy])
          have htailSmallX : ∀ y ∈ xs, |ieeeVal y| < 1 := by
            intro y hy
            exact hxSmall y (by simp [hy])
          have htailSmallW : ∀ y ∈ ws, |ieeeVal y| < 1 := by
            intro y hy
            exact hwSmall y (by simp [hy])
          have htailBound : xs.length ≤ 64 := by
            exact Nat.le_of_lt (by simpa using hlengthBound)
          have htailThreshold :
              2 * (xs.length : ℝ) + 1 < ieeeThreshold fmt := by
            norm_num [Nat.cast_add] at hthreshold ⊢
            linarith
          have htailCertificate := ih htailLengths htailBound
            htailFiniteX htailFiniteW htailSmallX htailSmallW htailThreshold
          have htailSafe := ieeeFmaDotCertificate_imp_safe htailCertificate
          have htailFinite : ieeeIsFinite (ieeeFmaDot xs ws) :=
            ieeeFmaDot_finite htailSafe
          have htailAbsDot :
              |dotProduct (xs.map ieeeVal) (ws.map ieeeVal)| ≤
                (xs.length : ℝ) := by
            have hxLe : ∀ y ∈ xs, |ieeeVal y| ≤ (1 : ℝ) := by
              intro y hy
              exact (hxSmall y (by simp [hy])).le
            have hwLe : ∀ y ∈ ws, |ieeeVal y| ≤ (1 : ℝ) := by
              intro y hy
              exact (hwSmall y (by simp [hy])).le
            have hbound := ieeeFmaDotAbsBound (a := 1) (b := 1)
              htailLengths hxLe hwLe
            simpa using hbound
          have htailValue :
              |ieeeVal (ieeeFmaDot xs ws)| ≤ (xs.length : ℝ) := by
            rw [ieeeVal_ieeeFmaDot]
            exact htailAbsDot
          have hxSmallHead : |ieeeVal x| < 1 := hxSmall x (by simp)
          have hwSmallHead : |ieeeVal w| < 1 := hwSmall w (by simp)
          have hproductSmall : |ieeeVal x * ieeeVal w| < 1 := by
            rw [abs_mul]
            by_cases hwZero : |ieeeVal w| = 0
            · simp [hwZero]
            · have hwPos : 0 < |ieeeVal w| :=
                lt_of_le_of_ne (abs_nonneg _) (Ne.symm hwZero)
              have hfirst := mul_lt_mul_of_pos_right
                hxSmallHead hwPos
              have hsecond : |ieeeVal w| < (1 : ℝ) := hwSmallHead
              have hsecond' : 1 * |ieeeVal w| < 1 * 1 := by
                exact mul_lt_mul_of_pos_left hsecond zero_lt_one
              exact lt_trans (by simpa using hfirst) (by simpa using hsecond')
          have hexactRange :
              |ieeeFmaExact x w (ieeeFmaDot xs ws)| < ieeeThreshold fmt := by
            have htriangle := abs_add_le
              (ieeeVal x * ieeeVal w) (ieeeVal (ieeeFmaDot xs ws))
            rw [ieeeFmaExact]
            have hthreshold' :
                2 * (xs.length : ℝ) + 3 < ieeeThreshold fmt := by
              norm_num [Nat.cast_add] at hthreshold ⊢
              linarith
            linarith
          have hwitness : ieeeRoundWitness 1
              (ieeeFmaExact x w (ieeeFmaDot xs ws))
              (ieeeFmaDot xs ws) := by
            refine ⟨htailFinite, ?_⟩
            have hprodLe : |ieeeVal x * ieeeVal w| ≤ (1 : ℝ) :=
              hproductSmall.le
            have hidentity :
                ieeeVal (ieeeFmaDot xs ws) -
                    ieeeFmaExact x w (ieeeFmaDot xs ws) =
                  -(ieeeVal x * ieeeVal w) := by
              simp [ieeeFmaExact]
            rw [hidentity, abs_neg]
            exact hprodLe
          have hstep : ieeeFmaStepCertificate (ieeeThreshold fmt) 1
              x w (ieeeFmaDot xs ws) (ieeeFmaDot xs ws) :=
            ⟨hxFinite x (by simp), hwFinite w (by simp), htailFinite,
              hexactRange, hwitness⟩
          simpa [ieeeFmaDotTailWitnesses, ieeeFmaDotCertificate] using
            And.intro htailCertificate hstep

end
end DecoderTransformer
