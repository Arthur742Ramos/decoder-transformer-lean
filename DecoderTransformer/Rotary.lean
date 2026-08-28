import DecoderTransformer.Projection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Intervals
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Rotary position embeddings and cache alignment

Adjacent coordinates form rotation planes; a final unpaired coordinate is
left unchanged.  The angle schedule is intentionally parametric.
-/

def ropeRotateFrom (angles : Nat → Nat → ℝ) (position pair : Nat) :
    Vector ℝ → Vector ℝ
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
      let theta := angles pair position
      (x * Real.cos theta - y * Real.sin theta) ::
        (x * Real.sin theta + y * Real.cos theta) ::
          ropeRotateFrom angles position (pair + 1) xs

def ropeRotate (angles : Nat → Nat → ℝ) (position : Nat) (x : Vector ℝ) :
    Vector ℝ := ropeRotateFrom angles position 0 x

@[simp] theorem length_ropeRotateFrom
    (angles : Nat → Nat → ℝ) (position pair : Nat) (x : Vector ℝ) :
    (ropeRotateFrom angles position pair x).length = x.length := by
  induction x using List.twoStepInduction generalizing pair with
  | nil => simp [ropeRotateFrom]
  | singleton x => simp [ropeRotateFrom]
  | cons_cons x y xs ih =>
      simp [ropeRotateFrom, ih]

theorem ropeRotate_preservesShape {headDim : Nat}
    {angles : Nat → Nat → ℝ} {position : Nat} {x : Vector ℝ}
    (hx : vectorShape headDim x) :
    vectorShape headDim (ropeRotate angles position x) := by
  simpa [ropeRotate, vectorShape] using hx

def squaredL2Norm (x : Vector ℝ) : ℝ :=
  (x.map (fun v => v * v)).sum

theorem planarRotationPairNorm (theta x y : ℝ) :
    (x * Real.cos theta - y * Real.sin theta) *
        (x * Real.cos theta - y * Real.sin theta) +
      (x * Real.sin theta + y * Real.cos theta) *
        (x * Real.sin theta + y * Real.cos theta) =
      x * x + y * y := by
  have htrig : Real.cos theta * Real.cos theta +
      Real.sin theta * Real.sin theta = 1 := by
    simpa [pow_two, add_comm] using Real.cos_sq_add_sin_sq theta
  calc
    (x * Real.cos theta - y * Real.sin theta) *
          (x * Real.cos theta - y * Real.sin theta) +
        (x * Real.sin theta + y * Real.cos theta) *
          (x * Real.sin theta + y * Real.cos theta) =
        (x * x + y * y) *
          (Real.cos theta * Real.cos theta +
            Real.sin theta * Real.sin theta) := by ring
    _ = x * x + y * y := by rw [htrig, mul_one]

theorem ropeRotateFrom_preservesSquaredNorm
    (angles : Nat → Nat → ℝ) (position pair : Nat) (x : Vector ℝ) :
    squaredL2Norm (ropeRotateFrom angles position pair x) =
      squaredL2Norm x := by
  induction x using List.twoStepInduction generalizing pair with
  | nil => simp [ropeRotateFrom, squaredL2Norm]
  | singleton x => simp [ropeRotateFrom, squaredL2Norm]
  | cons_cons x y xs ih =>
      simp only [ropeRotateFrom, squaredL2Norm, List.map_cons, List.sum_cons]
      calc
        (x * Real.cos (angles pair position) - y * Real.sin (angles pair position)) *
              (x * Real.cos (angles pair position) - y * Real.sin (angles pair position)) +
            ((x * Real.sin (angles pair position) +
                y * Real.cos (angles pair position)) *
              (x * Real.sin (angles pair position) +
                y * Real.cos (angles pair position)) +
              (List.map (fun v => v * v)
                (ropeRotateFrom angles position (pair + 1) xs)).sum) =
            ((x * Real.cos (angles pair position) - y * Real.sin (angles pair position)) *
              (x * Real.cos (angles pair position) - y * Real.sin (angles pair position)) +
            (x * Real.sin (angles pair position) + y * Real.cos (angles pair position)) *
              (x * Real.sin (angles pair position) + y * Real.cos (angles pair position))) +
              (List.map (fun v => v * v)
                (ropeRotateFrom angles position (pair + 1) xs)).sum := by ring
        _ = (x * x + y * y) +
              (List.map (fun v => v * v)
                (ropeRotateFrom angles position (pair + 1) xs)).sum := by
              rw [planarRotationPairNorm]
        _ = x * x +
              (y * y + (List.map (fun v => v * v) xs).sum) := by
              have htail := ih (pair + 1)
              simp only [squaredL2Norm] at htail
              rw [htail]
              ring

theorem ropeRotate_preservesSquaredNorm
    (angles : Nat → Nat → ℝ) (position : Nat) (x : Vector ℝ) :
    squaredL2Norm (ropeRotate angles position x) = squaredL2Norm x := by
  exact ropeRotateFrom_preservesSquaredNorm angles position 0 x

def indexedSequence (start : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (start, x) :: indexedSequence (start + 1) xs

@[simp] theorem length_indexedSequence (start : Nat) (xs : List α) :
    (indexedSequence start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => simp [indexedSequence]
  | cons x xs ih => simp [indexedSequence, ih]

@[simp] theorem indexedSequence_snd (start : Nat) (xs : List α) :
    (indexedSequence start xs).map Prod.snd = xs := by
  induction xs generalizing start with
  | nil => simp [indexedSequence]
  | cons x xs ih =>
      simp [indexedSequence, ih]

theorem indexedSequence_append_singleton (start : Nat) (xs : List α) (x : α) :
    indexedSequence start (xs ++ [x]) =
      indexedSequence start xs ++ [(start + xs.length, x)] := by
  induction xs generalizing start with
  | nil => simp [indexedSequence]
  | cons y ys ih =>
      simp [indexedSequence, ih, Nat.add_assoc]
      omega

def rotaryProject (outDim : Nat) (W : Matrix ℝ)
    (rotation : Nat → Vector ℝ → Vector ℝ)
    (ix : Nat × Vector ℝ) : Vector ℝ :=
  rotation ix.1 (linearProject outDim W ix.2)

def positionedValueProject (outDim : Nat) (W : Matrix ℝ)
    (ix : Nat × Vector ℝ) : Vector ℝ :=
  linearProject outDim W ix.2

def rotaryExactCausalAttention (headDim valueDim : Nat)
    (rotation : Nat → Vector ℝ → Vector ℝ) (start : Nat)
    (WQ WK WV : Matrix ℝ) (xs : Matrix ℝ) : Matrix ℝ :=
  exactCausalAttention headDim valueDim
    (rotaryProject headDim WQ rotation)
    (rotaryProject headDim WK rotation)
    (positionedValueProject valueDim WV)
    (indexedSequence start xs)

def rotaryExactCachedAttention (headDim valueDim : Nat)
    (rotation : Nat → Vector ℝ → Vector ℝ) (start : Nat)
    (WQ WK WV : Matrix ℝ) (xs : Matrix ℝ) : Matrix ℝ :=
  exactCachedAttention headDim valueDim
    (rotaryProject headDim WQ rotation)
    (rotaryProject headDim WK rotation)
    (positionedValueProject valueDim WV)
    (indexedSequence start xs)

theorem rotaryCachedAttention_equalsFull
    (headDim valueDim : Nat) (rotation : Nat → Vector ℝ → Vector ℝ)
    (start : Nat) (WQ WK WV : Matrix ℝ) (xs : Matrix ℝ) :
    rotaryExactCachedAttention headDim valueDim rotation start WQ WK WV xs =
      rotaryExactCausalAttention headDim valueDim rotation start WQ WK WV xs := by
  exact exactCachedAttention_eq_full _ _ _ _ _ _

theorem rotaryExactAttention_shape
    (headDim valueDim : Nat) (rotation : Nat → Vector ℝ → Vector ℝ)
    (start : Nat) (WQ WK WV : Matrix ℝ) (xs : Matrix ℝ) :
    matrixShape xs.length valueDim
      (rotaryExactCausalAttention headDim valueDim rotation start WQ WK WV xs) := by
  have h := exactCausalAttention_shape headDim valueDim
    (rotaryProject headDim WQ rotation)
    (rotaryProject headDim WK rotation)
    (positionedValueProject valueDim WV)
    (indexedSequence start xs)
  simpa [rotaryExactCausalAttention] using h

theorem positionedCacheExtension
    {Q : Nat × Vector ℝ → q} {K : Nat × Vector ℝ → k}
    {V : Nat × Vector ℝ → v} {A : q → List k → List v → o}
    {start : Nat} {pref : List (Vector ℝ)} {C : KVCache k v}
    {x : Vector ℝ}
    (hcache : cacheMatches K V (indexedSequence start pref) C) :
    cachedStep Q K V A C (start + pref.length, x) =
      (cacheOf K V (indexedSequence start (pref ++ [x])),
        A (Q (start + pref.length, x))
          ((indexedSequence start (pref ++ [x])).map K)
          ((indexedSequence start (pref ++ [x])).map V)) := by
  have h := cachedStep_refinesFull Q K V A
    (pref := indexedSequence start pref) (C := C)
    (token := (start + pref.length, x)) hcache
  simpa [indexedSequence_append_singleton] using h

end
end DecoderTransformer
