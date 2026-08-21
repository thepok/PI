import TheoryLib.PiQuantitativeBlockHitting.T98T98BBPArchimedeanTerm

/-!
# T99: finite rational BBP truncation bounds

This module proves finite rational identities and inequalities only. It does
not assert an infinite BBP identity, identify a limit with pi, or make a digit,
carry, SP1, or V1 claim.
-/

namespace Theory.PiDigits.T99BBPFiniteTail

open scoped BigOperators
open T98BBPArchimedeanTerm

/-- Closed form for a finite shifted sum of the geometric majorant. -/
theorem finite_geometric_majorant_sum (M N : ℕ) :
    (∑ j ∈ Finset.range N, (4 : ℚ) / (16 : ℚ) ^ (M + j + 1)) =
      (4 : ℚ) / (15 * (16 : ℚ) ^ M) * (1 - 1 / (16 : ℚ) ^ N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h16 : (16 : ℚ) ≠ 0 := by norm_num
    have hM : (16 : ℚ) ^ M ≠ 0 := pow_ne_zero _ h16
    have hn : (16 : ℚ) ^ n ≠ 0 := pow_ne_zero _ h16
    field_simp
    ring

/-- Every finite shifted geometric sum is strictly below its full envelope. -/
theorem finite_geometric_majorant_sum_lt (M N : ℕ) :
    (∑ j ∈ Finset.range N, (4 : ℚ) / (16 : ℚ) ^ (M + j + 1)) <
      (4 : ℚ) / (15 * (16 : ℚ) ^ M) := by
  rw [finite_geometric_majorant_sum]
  have hA : (0 : ℚ) < 4 / (15 * 16 ^ M) := by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hpow : (0 : ℚ) < 16 ^ N := by positivity
    have hdiv : (0 : ℚ) < 1 / 16 ^ N := div_pos one_pos hpow
    have hlt : (1 : ℚ) - 1 / 16 ^ N < 1 := by linarith
    calc
      (4 : ℚ) / (15 * 16 ^ M) * (1 - 1 / 16 ^ N) =
          (1 - 1 / 16 ^ N) * (4 / (15 * 16 ^ M)) := mul_comm _ _
      _ < 1 * (4 / (15 * 16 ^ M)) := mul_lt_mul_of_pos_right hlt hA
      _ = 4 / (15 * 16 ^ M) := one_mul _

/-- Each finite BBP partial sum is strictly smaller than its successor. -/
theorem bbpPartial_lt_succ (M : ℕ) :
    T77SelectedPadicDefectShell.bbpPartial M <
      T77SelectedPadicDefectShell.bbpPartial (M + 1) := by
  rw [bbpPartial_succ]
  have h := bbpCombinedTerm_pos (M + 1)
  linarith

/-- The canonical finite rational BBP partial sums are strictly monotone. -/
theorem bbpPartial_strictMono :
    StrictMono T77SelectedPadicDefectShell.bbpPartial :=
  strictMono_nat_of_lt_succ bbpPartial_lt_succ

/-- Difference of two finite partial sums as the intervening finite block. -/
theorem bbpPartial_add_sub_eq_sum (M N : ℕ) :
    T77SelectedPadicDefectShell.bbpPartial (M + N) -
        T77SelectedPadicDefectShell.bbpPartial M =
      ∑ j ∈ Finset.range N, bbpCombinedTerm (M + j + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hshift : M + (n + 1) = (M + n) + 1 := by omega
    rw [hshift, bbpPartial_succ, Finset.sum_range_succ, ← ih]
    ring

/-- Every finite forward difference of BBP partial sums is nonnegative. -/
theorem bbpPartial_finite_tail_nonneg (M N : ℕ) :
    0 ≤ T77SelectedPadicDefectShell.bbpPartial (M + N) -
      T77SelectedPadicDefectShell.bbpPartial M := by
  rw [bbpPartial_add_sub_eq_sum]
  exact Finset.sum_nonneg fun j _ ↦ (bbpCombinedTerm_pos (M + j + 1)).le

/-- A finite forward difference is strictly below the geometric envelope. -/
theorem bbpPartial_finite_tail_lt (M N : ℕ) :
    T77SelectedPadicDefectShell.bbpPartial (M + N) -
        T77SelectedPadicDefectShell.bbpPartial M <
      (4 : ℚ) / (15 * (16 : ℚ) ^ M) := by
  rw [bbpPartial_add_sub_eq_sum]
  calc
    (∑ j ∈ Finset.range N, bbpCombinedTerm (M + j + 1)) ≤
        ∑ j ∈ Finset.range N, (4 : ℚ) / (16 : ℚ) ^ (M + j + 1) := by
      exact Finset.sum_le_sum fun j _ ↦ (bbpCombinedTerm_lt_geometric (M + j + 1)).le
    _ < (4 : ℚ) / (15 * (16 : ℚ) ^ M) :=
      finite_geometric_majorant_sum_lt M N

end Theory.PiDigits.T99BBPFiniteTail
