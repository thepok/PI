import TheoryLib.PiQuantitativeBlockHitting.T97T97SelectedResidueCauchy

/-!
# T98: a positive BBP summand with a geometric majorant

This module combines the four rational BBP poles at one index.  It proves
only finite rational identities and inequalities; it does not assert an
infinite BBP identity, a tail estimate for pi, or any digit conclusion.
-/

namespace Theory.PiDigits.T98BBPArchimedeanTerm

open T74ThreePrimaryDecimation

/-- The four-pole rational BBP coefficient at index `k`, including `16 ^ k`. -/
def bbpCombinedTerm (k : ℕ) : ℚ :=
  poleOne k + poleTwo k + poleThree k + poleFour k

/-- Exact single-fraction form of the combined rational term. -/
theorem bbpCombinedTerm_eq (k : ℕ) :
    bbpCombinedTerm k =
      (120 * k ^ 2 + 151 * k + 47 : ℚ) /
        ((2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5) * 16 ^ k) := by
  simp only [bbpCombinedTerm, poleOne, poleTwo, poleThree, poleFour]
  field_simp
  ring

theorem combinedNumerator_pos (k : ℕ) :
    (0 : ℚ) < 120 * k ^ 2 + 151 * k + 47 := by
  positivity

theorem combinedDenominator_pos (k : ℕ) :
    (0 : ℚ) < (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5) * 16 ^ k := by
  positivity

theorem bbpCombinedTerm_pos (k : ℕ) : 0 < bbpCombinedTerm k := by
  rw [bbpCombinedTerm_eq]
  exact div_pos (combinedNumerator_pos k) (combinedDenominator_pos k)

theorem combinedNumerator_lt_four_times_product (k : ℕ) :
    (120 * k ^ 2 + 151 * k + 47 : ℚ) <
      4 * ((2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)) := by
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have h2 : (0 : ℚ) ≤ k * k := mul_nonneg hk hk
  have h3 : (0 : ℚ) ≤ k * k * k := mul_nonneg h2 hk
  have h4 : (0 : ℚ) ≤ k * k * k * k := mul_nonneg h3 hk
  nlinarith

theorem bbpCombinedTerm_lt_geometric (k : ℕ) :
    bbpCombinedTerm k < 4 / (16 : ℚ) ^ k := by
  rw [bbpCombinedTerm_eq]
  have hden := combinedDenominator_pos k
  have h4 : (4 : ℚ) / 16 ^ k =
      4 * ((2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)) /
        ((2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5) * 16 ^ k) := by
    field_simp
  rw [h4, div_lt_div_iff_of_pos_right hden]
  exact combinedNumerator_lt_four_times_product k

theorem bbpPartial_succ (k : ℕ) :
    T77SelectedPadicDefectShell.bbpPartial (k + 1) =
      T77SelectedPadicDefectShell.bbpPartial k + bbpCombinedTerm (k + 1) := by
  simp only [T77SelectedPadicDefectShell.bbpPartial,
    T77SelectedPadicDefectShell.polePartial, bbpCombinedTerm,
    Finset.sum_range_succ]
  ring

end Theory.PiDigits.T98BBPArchimedeanTerm
