import DecoderTransformer.Modern
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Concrete decoding policies

The policy is deliberately deterministic: `firstArgmax` returns the first
index attaining the maximum value.  The totalized `getD` lookup is harmless
under the accompanying bound theorem and keeps the executable definition
total on all lists.
-/

def firstArgmax : Vector ℝ → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: ys =>
      let i := firstArgmax (y :: ys)
      if x ≥ (y :: ys).getD i 0 then 0 else i + 1

theorem firstArgmax_bound {xs : Vector ℝ} (hne : xs ≠ []) :
    firstArgmax xs < xs.length := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
      cases xs with
      | nil => simp [firstArgmax]
      | cons y ys =>
          have htail : firstArgmax (y :: ys) < (y :: ys).length :=
            ih (by simp)
          have harg : firstArgmax (x :: y :: ys) =
              if x ≥ (y :: ys).getD (firstArgmax (y :: ys)) 0
              then 0 else firstArgmax (y :: ys) + 1 := by
            rw [firstArgmax]
          rw [harg]
          split
          · simp
          · exact Nat.succ_lt_succ htail

theorem firstArgmax_maximal {xs : Vector ℝ} {i : Nat}
    (hne : xs ≠ []) (hi : i < xs.length) :
    xs.getD i 0 ≤ xs.getD (firstArgmax xs) 0 := by
  induction xs generalizing i with
  | nil => contradiction
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hi0 : i = 0 := by simpa using hi
          subst i
          simp [firstArgmax]
      | cons y ys =>
          have htail : (y :: ys) ≠ [] := by simp
          have hj : firstArgmax (y :: ys) < (y :: ys).length :=
            firstArgmax_bound htail
          have tailMax : ∀ k, k < (y :: ys).length →
              (y :: ys).getD k 0 ≤ (y :: ys).getD (firstArgmax (y :: ys)) 0 := by
            intro k hk
            exact ih htail hk
          cases i with
          | zero =>
              by_cases hge : x ≥ (y :: ys).getD (firstArgmax (y :: ys)) 0
              · change (y :: ys)[firstArgmax (y :: ys)]?.getD 0 ≤ x at hge
                have harg : firstArgmax (x :: y :: ys) =
                    if x ≥ (y :: ys).getD (firstArgmax (y :: ys)) 0
                    then 0 else firstArgmax (y :: ys) + 1 := by
                  rw [firstArgmax]
                rw [harg]
                simp [hge]
              · change ¬((y :: ys)[firstArgmax (y :: ys)]?.getD 0 ≤ x) at hge
                have hlt : x < (y :: ys).getD (firstArgmax (y :: ys)) 0 :=
                  lt_of_not_ge hge
                have hlt' : x < (y :: ys)[firstArgmax (y :: ys)]?.getD 0 :=
                  lt_of_not_ge hge
                have harg : firstArgmax (x :: y :: ys) =
                    if x ≥ (y :: ys).getD (firstArgmax (y :: ys)) 0
                    then 0 else firstArgmax (y :: ys) + 1 := by
                  rw [firstArgmax]
                rw [harg]
                simpa [hge] using (le_of_lt hlt')
          | succ k =>
              have hk : k < (y :: ys).length := by simpa using hi
              have hkm : (y :: ys).getD k 0 ≤
                  (y :: ys).getD (firstArgmax (y :: ys)) 0 := tailMax k hk
              by_cases hge : x ≥ (y :: ys).getD (firstArgmax (y :: ys)) 0
              · change (y :: ys)[firstArgmax (y :: ys)]?.getD 0 ≤ x at hge
                change (y :: ys)[k]?.getD 0 ≤
                  (y :: ys)[firstArgmax (y :: ys)]?.getD 0 at hkm
                have hge' := hge
                have harg : firstArgmax (x :: y :: ys) =
                    if x ≥ (y :: ys).getD (firstArgmax (y :: ys)) 0
                    then 0 else firstArgmax (y :: ys) + 1 := by
                  rw [firstArgmax]
                rw [harg]
                simp [hge, hkm.trans hge']
              · change ¬((y :: ys)[firstArgmax (y :: ys)]?.getD 0 ≤ x) at hge
                change (y :: ys)[k]?.getD 0 ≤
                  (y :: ys)[firstArgmax (y :: ys)]?.getD 0 at hkm
                have harg : firstArgmax (x :: y :: ys) =
                    if x ≥ (y :: ys).getD (firstArgmax (y :: ys)) 0
                    then 0 else firstArgmax (y :: ys) + 1 := by
                  rw [firstArgmax]
                rw [harg]
                simp [hge, hkm]

theorem firstArgmax_is_valid_selector {vocabularySize : Nat}
    (hvocab : 0 < vocabularySize) :
    validTokenSelector vocabularySize firstArgmax := by
  intro distribution hlength
  have hne : distribution ≠ [] := by
    intro hnil
    simp [hnil] at hlength
    exact (Nat.ne_of_gt hvocab) hlength.symm
  have hbound := firstArgmax_bound hne
  simpa [hlength] using hbound

def temperatureLogits (temperature : ℝ) (logits : Vector ℝ) : Vector ℝ :=
  logits.map (fun z => z / temperature)

def temperatureDistribution (temperature : ℝ) (logits : Vector ℝ) : Vector ℝ :=
  listSoftmax (temperatureLogits temperature logits)

@[simp] theorem length_temperatureDistribution (temperature : ℝ)
    (logits : Vector ℝ) :
    (temperatureDistribution temperature logits).length = logits.length := by
  simp [temperatureDistribution, temperatureLogits]

theorem temperatureDistribution_normalized {temperature : ℝ}
    {logits : Vector ℝ} (hne : logits ≠ []) :
    (temperatureDistribution temperature logits).sum = 1 := by
  apply listSoftmax_normalized
  simpa [temperatureLogits] using hne

theorem temperatureDistribution_positive {temperature : ℝ}
    {logits : Vector ℝ} {i : Nat} (hne : logits ≠ [])
    (hi : i < logits.length) :
    0 < (temperatureDistribution temperature logits).getD i 0 := by
  have htrans : i < (temperatureLogits temperature logits).length := by
    simpa [temperatureLogits] using hi
  have hdist : i < (listSoftmax (temperatureLogits temperature logits)).length := by
    simpa using htrans
  have hpos : 0 <
      (listSoftmax (temperatureLogits temperature logits))[i]'hdist := by
    exact listSoftmax_positive
      (xs := temperatureLogits temperature logits)
      (w := (listSoftmax (temperatureLogits temperature logits))[i]'hdist)
      (by simpa [temperatureLogits] using hne)
      (List.getElem_mem hdist)
  rw [temperatureDistribution, List.getD_eq_getElem _ _ hdist]
  exact hpos

theorem greedyGenerateSteps_preservesVocabulary
    {vocabularySize : Nat} {n : Nat}
    {layers : List DecoderLayerParameters} {embedding : Nat → Vector ℝ}
    {vocabularyWeights : Matrix ℝ} {state : GenerationState}
    (hvocab : 0 < vocabularySize)
    (htokens : tokensInVocabulary vocabularySize state.1)
    (hne : state.1 ≠ []) :
    tokensInVocabulary vocabularySize
      (generateSteps n firstArgmax layers embedding vocabularySize
        vocabularyWeights state).1 := by
  exact generateSteps_preservesVocabulary
    (firstArgmax_is_valid_selector hvocab) htokens hne

end
end DecoderTransformer
