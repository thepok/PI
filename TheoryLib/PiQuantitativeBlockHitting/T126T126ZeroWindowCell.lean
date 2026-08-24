import TheoryLib.PiDigits.T20BaseTenOrbitDensity
import TheoryLib.Shared.DigitAutomata.T13T13T6ArithmeticBridge

/-!
# T126: zero decimal windows place the orbit in the first mesh cell

This module records an endpoint-safe generic consequence of a consecutive
zero window.  It does not establish that such windows occur for `Real.pi`.
-/

noncomputable section

namespace Theory.PiQuantitativeBlockHitting.T126

/-- If the `k` decimal digits following orbit time `n` are all zero, then the
base-ten orbit point is at most `10 ^ (-k)`.  The inequality is deliberately
non-strict because endpoint decimal expansions must be allowed. -/
theorem baseTenOrbit_le_invPow_of_zero_window
    {x : ℝ} (hx : 0 ≤ x) {n k : ℕ}
    (hzero : ∀ i : Fin k,
      (Theory.PiDigits.T20.decimalDigit x (n + i.val)).val = 0) :
    Theory.PiDigits.T20.baseTenOrbit x n ≤ ((10 : ℝ) ^ k)⁻¹ := by
  let y : Theory.Shared.DigitAutomata.T13.DigitSequence 10 :=
    fun i ↦ Real.digits (Theory.PiDigits.T20.baseTenOrbit x n) 10 i
  have hyzero : ∀ i : Fin k, (y i.val).val = 0 := by
    intro i
    change (Theory.PiDigits.T20.decimalDigit
      (Theory.PiDigits.T20.baseTenOrbit x n) i.val).val = 0
    rw [Theory.PiDigits.T20.decimalDigit_baseTenOrbit x hx n i.val]
    exact hzero i
  have hbound :=
    Theory.Shared.DigitAutomata.T13.ofDigits_le_invPow_of_zero_prefix
      10 k (by norm_num) y hyzero
  rw [Real.ofDigits_digits (by norm_num)
    (Theory.PiDigits.T20.baseTenOrbit_mem_Ico x n)] at hbound
  exact hbound

/-- A zero window longer than the resolution of a positive `q`-mesh puts the
orbit point in its first half-open cell `[0, 1/q)`. -/
theorem baseTenOrbit_mem_firstCell_of_zero_window
    {x : ℝ} (hx : 0 ≤ x) {n k q : ℕ} (hq : 0 < q)
    (hqk : q < 10 ^ k)
    (hzero : ∀ i : Fin k,
      (Theory.PiDigits.T20.decimalDigit x (n + i.val)).val = 0) :
    Theory.PiDigits.T20.baseTenOrbit x n ∈
      Set.Ico (0 : ℝ) ((q : ℝ)⁻¹) := by
  constructor
  · exact (Theory.PiDigits.T20.baseTenOrbit_mem_Ico x n).1
  · calc
      Theory.PiDigits.T20.baseTenOrbit x n ≤ ((10 : ℝ) ^ k)⁻¹ :=
        baseTenOrbit_le_invPow_of_zero_window hx hzero
      _ < ((q : ℝ)⁻¹) := by
        apply (inv_lt_inv₀ (by positivity) (by exact_mod_cast hq)).2
        exact_mod_cast hqk

end Theory.PiQuantitativeBlockHitting.T126
