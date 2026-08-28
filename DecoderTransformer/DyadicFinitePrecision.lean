import DecoderTransformer.Projection
import DecoderTransformer.ModernGeneration
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Concrete dyadic finite-precision projection

The dyadic kernel is deliberately narrower than IEEE arithmetic: it rounds to
the nearest point on a fixed fractional grid and records one error budget for
each fused multiply-add.  This gives an explicit executable finite-precision
refinement without making an IEEE bit-level claim.
-/

def dyadicScale (p : Nat) : ℝ := (2 : ℝ) ^ p

def dyadicUnitRoundoff (p : Nat) : ℝ :=
  (2 * dyadicScale p)⁻¹

def dyadicRound (p : Nat) (x : ℝ) : ℝ :=
  (round (x * dyadicScale p) : ℝ) / dyadicScale p

theorem dyadicScale_pos (p : Nat) : 0 < dyadicScale p := by
  simp [dyadicScale]

theorem dyadicUnitRoundoff_nonnegative (p : Nat) :
    0 ≤ dyadicUnitRoundoff p := by
  simp [dyadicUnitRoundoff, dyadicScale_pos p]

theorem dyadicRound_grid (p k : Nat) :
    dyadicRound p ((k : ℝ) / dyadicScale p) =
      (k : ℝ) / dyadicScale p := by
  have hs := dyadicScale_pos p
  have hmul : (k : ℝ) / dyadicScale p * dyadicScale p = k := by
    field_simp [hs.ne]
  simp [dyadicRound, hmul]

theorem dyadicRound_idempotent (p : Nat) (x : ℝ) :
    dyadicRound p (dyadicRound p x) = dyadicRound p x := by
  have hs := dyadicScale_pos p
  unfold dyadicRound
  have hmul :
      ((round (x * dyadicScale p) : ℝ) / dyadicScale p) * dyadicScale p =
        (round (x * dyadicScale p) : ℝ) := by
    field_simp [hs.ne]
  rw [hmul, round_intCast]

theorem dyadicRound_error (p : Nat) (x : ℝ) :
    |dyadicRound p x - x| ≤ dyadicUnitRoundoff p := by
  let s := dyadicScale p
  have hs : 0 < s := dyadicScale_pos p
  have hr : |x * s - (round (x * s) : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa [sub_eq_add_neg, add_comm] using abs_sub_round (x * s)
  have hscaled :
      |((round (x * s) : ℝ) / s) - x| =
        |x * s - (round (x * s) : ℝ)| / s := by
    have hrewrite :
        ((round (x * s) : ℝ) / s) - x =
          ((round (x * s) : ℝ) - x * s) / s := by
      field_simp [hs.ne]
    rw [hrewrite, abs_div, abs_of_pos hs, abs_sub_comm]
  rw [show dyadicRound p x = (round (x * s) : ℝ) / s by rfl, hscaled]
  have hdiv := div_le_div_of_nonneg_right hr (le_of_lt hs)
  calc
    |x * s - (round (x * s) : ℝ)| / s ≤ (1 / 2 : ℝ) / s := hdiv
    _ = dyadicUnitRoundoff p := by
      simp [dyadicUnitRoundoff, s, div_eq_mul_inv]
      ring

theorem dyadicRound_error_symmetric (p : Nat) (x : ℝ) :
    |x - dyadicRound p x| ≤ dyadicUnitRoundoff p := by
  simpa [abs_sub_comm] using dyadicRound_error p x

def dyadicFmaDot (p : Nat) : Vector ℝ → Vector ℝ → ℝ
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, w :: ws =>
      dyadicRound p (x * w + dyadicFmaDot p xs ws)

theorem dyadicFmaDot_error (p : Nat) (xs ws : Vector ℝ) :
    |dotProduct xs ws - dyadicFmaDot p xs ws| ≤
      (min xs.length ws.length : ℝ) * dyadicUnitRoundoff p := by
  induction xs generalizing ws with
  | nil => simp [dotProduct, dyadicFmaDot]
  | cons x xs ih =>
      cases ws with
      | nil =>
          have hnonneg :
              0 ≤ (min (x :: xs).length ([] : Vector ℝ).length : ℝ) *
                dyadicUnitRoundoff p :=
            mul_nonneg (by positivity) (dyadicUnitRoundoff_nonnegative p)
          simpa [dotProduct, dyadicFmaDot] using hnonneg
      | cons w ws =>
          have htail := ih ws
          have hlocal := dyadicRound_error_symmetric p
            (x * w + dyadicFmaDot p xs ws)
          have hdecomp :
              dotProduct (x :: xs) (w :: ws) - dyadicFmaDot p (x :: xs) (w :: ws) =
                (dotProduct xs ws - dyadicFmaDot p xs ws) +
                  ((x * w + dyadicFmaDot p xs ws) -
                    dyadicRound p (x * w + dyadicFmaDot p xs ws)) := by
            simp [dotProduct, dyadicFmaDot]
            ring
          calc
            |dotProduct (x :: xs) (w :: ws) -
                dyadicFmaDot p (x :: xs) (w :: ws)| =
                |(dotProduct xs ws - dyadicFmaDot p xs ws) +
                  ((x * w + dyadicFmaDot p xs ws) -
                    dyadicRound p (x * w + dyadicFmaDot p xs ws))| := by
                      rw [hdecomp]
            _ ≤ |dotProduct xs ws - dyadicFmaDot p xs ws| +
                |(x * w + dyadicFmaDot p xs ws) -
                  dyadicRound p (x * w + dyadicFmaDot p xs ws)| :=
                    abs_add_le _ _
            _ ≤ (min xs.length ws.length : ℝ) * dyadicUnitRoundoff p +
                dyadicUnitRoundoff p := add_le_add htail hlocal
            _ = (min (x :: xs).length (w :: ws).length : ℝ) *
                dyadicUnitRoundoff p := by
                  simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
                  by_cases h : (xs.length : ℝ) ≤ (ws.length : ℝ)
                  · rw [min_eq_left h, min_eq_left (by linarith)]
                    ring
                  · have h' : (ws.length : ℝ) ≤ (xs.length : ℝ) :=
                      le_of_not_ge h
                    rw [min_eq_right h', min_eq_right (by linarith)]
                    ring

def dyadicLinearProject (p outDim : Nat) (W : Matrix ℝ) (x : Vector ℝ) :
    Vector ℝ :=
  (matrixColumns outDim W).map (dyadicFmaDot p x)

@[simp] theorem length_dyadicLinearProject (p outDim : Nat)
    (W : Matrix ℝ) (x : Vector ℝ) :
    (dyadicLinearProject p outDim W x).length = outDim := by
  simp [dyadicLinearProject, matrixColumns]

theorem dyadicLinearProject_error
    {p inDim outDim : Nat} {W : Matrix ℝ} {x : Vector ℝ}
    (hW : matrixShape inDim outDim W) :
    vectorErrorBound (inDim * dyadicUnitRoundoff p)
      (linearProject outDim W x) (dyadicLinearProject p outDim W x) := by
  refine ⟨?_, ?_⟩
  · simp [linearProject, dyadicLinearProject, matrixColumns]
  · intro i hi
    have hiout : i < outDim := by
      simpa [linearProject, matrixColumns] using hi
    let columns := matrixColumns outDim W
    have hcolumns := matrixColumns_shape hW
    have hcol : (columns[i]'(by simpa [columns, hcolumns.1] using hiout)).length = inDim :=
      matrixShape_nth hcolumns hiout
    have hraw := dyadicFmaDot_error p x
      (columns[i]'(by simpa [columns, hcolumns.1] using hiout))
    rw [hcol] at hraw
    have hmin : (min x.length inDim : ℝ) ≤ inDim := by
      exact_mod_cast Nat.min_le_right x.length inDim
    have hscaled : (min x.length inDim : ℝ) * dyadicUnitRoundoff p ≤
        (inDim : ℝ) * dyadicUnitRoundoff p := by
      exact mul_le_mul_of_nonneg_right hmin
        (dyadicUnitRoundoff_nonnegative p)
    have hprojX : (linearProject outDim W x).getD i 0 =
        dotProduct x (columns.getD i []) := by
      have hdefault : (0 : ℝ) = dotProduct x [] := by simp [dotProduct]
      change (columns.map (dotProduct x)).getD i 0 =
        dotProduct x (columns.getD i [])
      rw [hdefault, List.getD_map]
    have hprojY : (dyadicLinearProject p outDim W x).getD i 0 =
        dyadicFmaDot p x (columns.getD i []) := by
      have hdefault : (0 : ℝ) = dyadicFmaDot p x [] := by
        cases x <;> rfl
      change (columns.map (dyadicFmaDot p x)).getD i 0 =
        dyadicFmaDot p x (columns.getD i [])
      rw [hdefault, List.getD_map]
    have hget : columns.getD i [] =
        columns[i]'(by simpa [columns, hcolumns.1] using hiout) := by
      exact List.getD_eq_getElem _ _ _
    rw [hprojX, hprojY, hget]
    exact hraw.trans hscaled

def dyadicNextTokenLogits (p vocabularySize : Nat) (W : Matrix ℝ)
    (hidden : Vector ℝ) : Vector ℝ :=
  dyadicLinearProject p vocabularySize W hidden

theorem dyadicNextTokenRoundingRelation
    {p modelDim vocabularySize : Nat} {W : Matrix ℝ}
    (hW : matrixShape modelDim vocabularySize W) :
    roundingRelation (modelDim * dyadicUnitRoundoff p : ℝ)
      (nextTokenLogits vocabularySize W)
      (dyadicNextTokenLogits p vocabularySize W) := by
  refine ⟨mul_nonneg (by positivity) (dyadicUnitRoundoff_nonnegative p), ?_⟩
  intro x
  exact dyadicLinearProject_error hW

theorem concreteDyadicNextTokenLogitError
    {hiddenError L roundingError : ℝ}
    {exactModel floatingModel : input → Vector ℝ}
    {floatingLogits : Vector ℝ → Vector ℝ}
    {p modelDim vocabularySize : Nat} {W : Matrix ℝ}
    (hmodel : floatingTransformerRelation hiddenError exactModel floatingModel)
    (hW : matrixShape modelDim vocabularySize W)
    (hbound : projectionL1Bound vocabularySize W L) (x : input) :
    vectorErrorBound (L * hiddenError + modelDim * dyadicUnitRoundoff p)
      (nextTokenLogits vocabularySize W (exactModel x))
      (dyadicNextTokenLogits p vocabularySize W (floatingModel x)) := by
  exact nextTokenLogitError hmodel
    (nextTokenLogits_lipschitz hW hbound)
    (dyadicNextTokenRoundingRelation hW) x

theorem binary32_fraction_grid_next_token_logit_error
    {hiddenError L : ℝ}
    {exactModel floatingModel : input → Vector ℝ}
    {modelDim vocabularySize : Nat} {W : Matrix ℝ}
    (hmodel : floatingTransformerRelation hiddenError exactModel floatingModel)
    (hW : matrixShape modelDim vocabularySize W)
    (hbound : projectionL1Bound vocabularySize W L) (x : input) :
    vectorErrorBound (L * hiddenError + (modelDim : ℝ) / 16777216)
      (nextTokenLogits vocabularySize W (exactModel x))
      (dyadicNextTokenLogits 23 vocabularySize W (floatingModel x)) := by
  have h := concreteDyadicNextTokenLogitError
    (roundingError := 0) (floatingLogits := fun _ => [])
    (p := 23) hmodel hW hbound x
  convert h using 1 <;> norm_num [dyadicUnitRoundoff, dyadicScale] <;> ring

theorem cached_modern_dyadic_next_token_logit_error
    {p modelDim vocabularySize start : Nat}
    {layers : List ModernDecoderLayerParameters}
    {pref : Matrix ℝ} {x : Vector ℝ}
    {caches : ModernTransformerCache} {W : Matrix ℝ}
    (hvalid : validModernStack layers)
    (hcache : modernTransformerCacheMatches layers start pref caches)
    (hmatrix : matrixShape modelDim vocabularySize W) :
    vectorErrorBound (modelDim * dyadicUnitRoundoff p)
      (nextTokenLogits vocabularySize W
        ((fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD []))
      (dyadicNextTokenLogits p vocabularySize W
        (cachedModernDecoderStackStep layers (start + pref.length) x caches).1) := by
  have hstep := cachedModernDecoderStackStep_correct
    (layers := layers) (start := start) (pref := pref)
    (caches := caches) (x := x) hvalid hcache
  have hfull :
      (cachedModernDecoderStackStep layers (start + pref.length) x caches).1 =
        (fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD [] := by
    have h := congrArg (fun z : Matrix ℝ => z.getLast?.getD []) hstep.1
    simpa using h.symm
  have hlocal :
      vectorErrorBound (modelDim * dyadicUnitRoundoff p)
        (nextTokenLogits vocabularySize W
          (cachedModernDecoderStackStep layers (start + pref.length) x caches).1)
        (dyadicNextTokenLogits p vocabularySize W
          (cachedModernDecoderStackStep layers (start + pref.length) x caches).1) := by
    exact (dyadicNextTokenRoundingRelation (p := p) hmatrix).2 _
  simpa [hfull] using hlocal

end
end DecoderTransformer
