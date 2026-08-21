import TheoryLib.PiQuantitativeBlockHitting.T100T100BBPRealBridge

/-!
# T101: summability of the real BBP term

This module proves that the canonical real BBP term is summable by comparison
with a geometric series.  It identifies the sum only with its own `tsum`;
evaluation of that `tsum` is a separate problem.
-/

namespace Theory.PiDigits.T101BBPIdentity

open T98BBPArchimedeanTerm T100BBPRealBridge

/-- The real BBP term is bounded above by its geometric majorant. -/
theorem bbpRealTerm_le_geometric (k : ℕ) :
    bbpRealTerm k ≤ (4 : ℝ) / (16 : ℝ) ^ k := by
  have hc : bbpRealTerm k ≤
      (((4 : ℚ) / (16 : ℚ) ^ k : ℚ) : ℝ) := by
    simp only [bbpRealTerm]
    exact Rat.cast_le.2 (bbpCombinedTerm_lt_geometric k).le
  push_cast at hc
  exact hc

/-- The real BBP term is nonnegative. -/
theorem bbpRealTerm_nonneg (k : ℕ) : 0 ≤ bbpRealTerm k := by
  simp only [bbpRealTerm]
  exact_mod_cast (bbpCombinedTerm_pos k).le

private theorem geometric_majorant_summable :
    Summable (fun k : ℕ ↦ (4 : ℝ) / (16 : ℝ) ^ k) :=
  ((hasSum_geometric_of_lt_one (r := (1 : ℝ) / 16)
      (by positivity) (by norm_num)).mul_left (4 : ℝ)).summable.congr
    (by
      intro k
      show (4 : ℝ) * ((1 : ℝ) / 16) ^ k = (4 : ℝ) / (16 : ℝ) ^ k
      rw [div_pow, one_pow]
      ring)

/-- The canonical real BBP term defines a convergent series. -/
theorem bbpRealTerm_summable : Summable bbpRealTerm :=
  Summable.of_nonneg_of_le bbpRealTerm_nonneg bbpRealTerm_le_geometric
    geometric_majorant_summable

/-- The canonical real BBP series sums to its `tsum`. -/
theorem bbpRealTerm_hasSum_tsum : HasSum bbpRealTerm (∑' k, bbpRealTerm k) :=
  bbpRealTerm_summable.hasSum

end Theory.PiDigits.T101BBPIdentity
