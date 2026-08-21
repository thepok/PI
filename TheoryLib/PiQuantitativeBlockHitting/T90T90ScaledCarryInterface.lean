import TheoryLib.PiQuantitativeBlockHitting.T89T89SelectedDepthScaledIntegrality

/-!
# T90: even scaled partial transport

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module records the exact rational transport identity for consecutive
even selected scaled BBP partial sums.  It does not define or control a hidden
carry, a decimal digit, canonical V1, or an SP1 resolution.
-/

namespace Theory.PiDigits.T90ScaledCarryInterface

open T73ThreePrimaryOrbit T77SelectedPadicDefectShell

/-- The even-epoch scaled BBP partial sum at its selected depth. -/
def evenScaledPartial (t : ℕ) : ℚ :=
  (3 : ℚ) ^ (2 * t) * bbpPartial (selectedDepth (2 * t))

/-- The exact rational transport identity between consecutive even scaled
partials.  It exposes the scaled endpoint defect without selecting a
three-adic representative. -/
theorem evenScaledPartial_transport (t : ℕ) (ht : 1 ≤ t) :
    evenScaledPartial (t + 1) - evenScaledPartial t =
      (3 : ℚ) ^ (2 * t) * endpointDefect (selectedDepth (2 * t)) := by
  have hstep : selectedDepth (2 * (t + 1)) =
      9 * selectedDepth (2 * t) + 13 :=
    T87LiteralSP1Packaging.selectedDepth_even_step t ht
  have hpow : (3 : ℚ) ^ (2 * (t + 1)) = 9 * (3 : ℚ) ^ (2 * t) := by
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, pow_add, pow_two]
    ring
  show (3 : ℚ) ^ (2 * (t + 1)) *
      bbpPartial (selectedDepth (2 * (t + 1))) -
    (3 : ℚ) ^ (2 * t) * bbpPartial (selectedDepth (2 * t)) = _
  rw [hstep, hpow]
  simp only [endpointDefect]
  ring

/-- Consecutive positive even selected depths give the same decimal power in
the three-primary coordinate at precision `3^(2*t+2)`.  This transports only
the exponent; it does not select a residue or a carry digit. -/
theorem selectedDepth_ten_pow_transport (t : ℕ) (ht : 1 ≤ t) :
    ((10 : ℕ) ^ selectedDepth (2 * t + 2) : ZMod (3 ^ (2 * t + 2))) =
      ((10 : ℕ) ^ selectedDepth (2 * t) : ZMod (3 ^ (2 * t + 2))) := by
  set d := selectedDepth (2 * t) with hd
  have hkey : 8 * selectedDepth (2 * t) + 13 = 5 * 3 ^ (2 * t) :=
    T88SelectedDepthDenominatorValuations.selectedDepth_scale_exact t ht
  have hstep := T87LiteralSP1Packaging.selectedDepth_even_step t ht
  have hnext : selectedDepth (2 * t + 2) = d + 5 * 3 ^ (2 * t) := by
    omega
  have hmod : selectedDepth (2 * t + 2) % 3 ^ (2 * t) = d % 3 ^ (2 * t) := by
    rw [hnext, Nat.add_mul_mod_self_right]
  have hunits : tenUnit (2 * t) ^ selectedDepth (2 * t + 2) =
      tenUnit (2 * t) ^ d :=
    (tenUnit_pow_eq_iff (2 * t) _ _).mpr hmod
  have hcoe : ((tenUnit (2 * t) ^ selectedDepth (2 * t + 2) :
          (ZMod (3 ^ (2 * t + 2)))ˣ) : ZMod (3 ^ (2 * t + 2))) =
      ((tenUnit (2 * t) ^ d :
          (ZMod (3 ^ (2 * t + 2)))ˣ) : ZMod (3 ^ (2 * t + 2))) := by
    rw [hunits]
  simpa [tenUnit] using hcoe

end Theory.PiDigits.T90ScaledCarryInterface

#print axioms Theory.PiDigits.T90ScaledCarryInterface.evenScaledPartial
#print axioms Theory.PiDigits.T90ScaledCarryInterface.evenScaledPartial_transport
#print axioms Theory.PiDigits.T90ScaledCarryInterface.selectedDepth_ten_pow_transport
