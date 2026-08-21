import TheoryLib.PiQuantitativeBlockHitting.T73T73ThreePrimaryOrbit

/-!
# T74: the exact one-term BBP ninefold decimation

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The four rational functions below are the partial-fraction summands in the
BBP series, including their powers of sixteen.  This module checks the exact
affine folding and rational identities behind the three-primary decimation.

It does not prove the three-adic integrality of the summed error, instantiate
the BBP denominator epochs, control complementary CRT coordinates, or prove
any decimal-word statement for pi.
-/

namespace Theory.PiDigits.T74ThreePrimaryDecimation

/-- The `8k+1` BBP pole, including its geometric weight. -/
def poleOne (k : ℕ) : ℚ := 4 / (8 * k + 1) / 16 ^ k

/-- The `2k+1` BBP pole, including its geometric weight. -/
def poleTwo (k : ℕ) : ℚ := -(1 : ℚ) / 2 / (2 * k + 1) / 16 ^ k

/-- The `8k+5` BBP pole, including its geometric weight. -/
def poleThree (k : ℕ) : ℚ := -(1 : ℚ) / (8 * k + 5) / 16 ^ k

/-- The `4k+3` BBP pole, including its geometric weight. -/
def poleFour (k : ℕ) : ℚ := -(1 : ℚ) / 2 / (4 * k + 3) / 16 ^ k

/-- The first pole at index `9r+1` has nine times its old linear
denominator. -/
theorem poleOne_affine_fold (r : ℕ) :
    8 * (9 * r + 1) + 1 = 9 * (8 * r + 1) := by
  omega

/-- The second pole at index `9r+4` has nine times its old linear
denominator. -/
theorem poleTwo_affine_fold (r : ℕ) :
    2 * (9 * r + 4) + 1 = 9 * (2 * r + 1) := by
  omega

/-- The third pole at index `9r+5` has nine times its old linear
denominator. -/
theorem poleThree_affine_fold (r : ℕ) :
    8 * (9 * r + 5) + 5 = 9 * (8 * r + 5) := by
  omega

/-- The fourth pole at index `9r+6` has nine times its old linear
denominator. -/
theorem poleFour_affine_fold (r : ℕ) :
    4 * (9 * r + 6) + 3 = 9 * (4 * r + 3) := by
  omega

/-- The exponent increment in the first fold is its old denominator. -/
theorem poleOne_exponent_fold (r : ℕ) : 8 * r + 1 = 8 * r + 1 := rfl

/-- The exponent increment in the second fold is four times its old
denominator. -/
theorem poleTwo_exponent_fold (r : ℕ) : 8 * r + 4 = 4 * (2 * r + 1) := by
  omega

/-- The exponent increment in the third fold is its old denominator. -/
theorem poleThree_exponent_fold (r : ℕ) : 8 * r + 5 = 8 * r + 5 := rfl

/-- The exponent increment in the fourth fold is twice its old denominator. -/
theorem poleFour_exponent_fold (r : ℕ) : 8 * r + 6 = 2 * (4 * r + 3) := by
  omega

/-- Exact rational decimation identity for the first BBP pole. -/
theorem poleOne_decimation (r : ℕ) :
  9 * poleOne (9 * r + 1) - poleOne r =
      poleOne r * ((1 : ℚ) / 16 ^ (8 * r + 1) - 1) := by
  simp only [poleOne]
  have hlin : (8 : ℚ) * (9 * r + 1) + 1 = 9 * ((8 : ℚ) * r + 1) := by
    ring
  push_cast
  rw [hlin]
  rw [show 9 * r + 1 = r + (8 * r + 1) by omega, pow_add]
  field_simp

/-- Exact rational decimation identity for the second BBP pole. -/
theorem poleTwo_decimation (r : ℕ) :
  9 * poleTwo (9 * r + 4) - poleTwo r =
      poleTwo r * ((1 : ℚ) / 16 ^ (8 * r + 4) - 1) := by
  simp only [poleTwo]
  have hlin : (2 : ℚ) * (9 * r + 4) + 1 = 9 * ((2 : ℚ) * r + 1) := by
    ring
  push_cast
  rw [hlin]
  rw [show 9 * r + 4 = r + (8 * r + 4) by omega, pow_add]
  field_simp
  ring

/-- Exact rational decimation identity for the third BBP pole. -/
theorem poleThree_decimation (r : ℕ) :
  9 * poleThree (9 * r + 5) - poleThree r =
      poleThree r * ((1 : ℚ) / 16 ^ (8 * r + 5) - 1) := by
  simp only [poleThree]
  have hlin : (8 : ℚ) * (9 * r + 5) + 5 = 9 * ((8 : ℚ) * r + 5) := by
    ring
  push_cast
  rw [hlin]
  rw [show 9 * r + 5 = r + (8 * r + 5) by omega, pow_add]
  field_simp
  ring

/-- Exact rational decimation identity for the fourth BBP pole. -/
theorem poleFour_decimation (r : ℕ) :
  9 * poleFour (9 * r + 6) - poleFour r =
      poleFour r * ((1 : ℚ) / 16 ^ (8 * r + 6) - 1) := by
  simp only [poleFour]
  have hlin : (4 : ℚ) * (9 * r + 6) + 3 = 9 * ((4 : ℚ) * r + 3) := by
    ring
  push_cast
  rw [hlin]
  rw [show 9 * r + 6 = r + (8 * r + 6) by omega, pow_add]
  field_simp
  ring

end Theory.PiDigits.T74ThreePrimaryDecimation

#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleOne_affine_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleTwo_affine_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleThree_affine_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleFour_affine_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleOne_exponent_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleTwo_exponent_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleThree_exponent_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleFour_exponent_fold
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleOne_decimation
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleTwo_decimation
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleThree_decimation
#print axioms Theory.PiDigits.T74ThreePrimaryDecimation.poleFour_decimation
