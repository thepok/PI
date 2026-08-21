import TheoryLib.PiQuantitativeBlockHitting.T79T79UniformCancelledQuotient

/-!
# T80: exact factorization of selected paired errors

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module records the exact rational factorizations of the four selected
paired errors through the uniform cancelled binomial quotient.  It makes no
claim about SP1, V1, or any decimal-word statement for pi.
-/

namespace Theory.PiDigits.T80SelectedPairedQuotientFactorization

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell
  T78SelectedPadicDefectCongruence

/-- The pole-one paired error factors through the cancelled quotient. -/
theorem pairedError_poleOne_factor (r : ℕ) :
    pairedError poleOne 1 r / 3 =
      ((-20 : ℚ) / 16 ^ (9 * r + 1)) * binomialQuotient (8 * r + 1) := by
  have hdec := poleOne_decimation r
  have hbin : ∀ t : ℕ, binomialQuotient t = ((16 : ℚ) ^ t - 1) / (15 * t) :=
    fun _ => rfl
  have hpow : ((16 : ℚ) ^ (9 * r + 1)) =
      (16 : ℚ) ^ r * (16 : ℚ) ^ (8 * r + 1) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [pairedError]
  rw [hdec, hbin, hpow]
  simp only [poleOne]
  field_simp
  push_cast
  ring

/-- The pole-two paired error factors through the cancelled quotient. -/
theorem pairedError_poleTwo_factor (r : ℕ) :
    pairedError poleTwo 4 r / 3 =
      ((10 : ℚ) / 16 ^ (9 * r + 4)) * binomialQuotient (8 * r + 4) := by
  have hdec := poleTwo_decimation r
  have hbin : ∀ t : ℕ, binomialQuotient t = ((16 : ℚ) ^ t - 1) / (15 * t) :=
    fun _ => rfl
  have hpow : ((16 : ℚ) ^ (9 * r + 4)) =
      (16 : ℚ) ^ r * (16 : ℚ) ^ (8 * r + 4) := by
    rw [← pow_add]
    congr 1
    omega
  have hlin : (8 : ℕ) * r + 4 = 4 * (2 * r + 1) := by omega
  simp only [pairedError]
  rw [hdec, hbin, hpow, hlin]
  simp only [poleTwo]
  field_simp
  push_cast
  ring

/-- The pole-three paired error factors through the cancelled quotient. -/
theorem pairedError_poleThree_factor (r : ℕ) :
    pairedError poleThree 5 r / 3 =
      ((5 : ℚ) / 16 ^ (9 * r + 5)) * binomialQuotient (8 * r + 5) := by
  have hdec := poleThree_decimation r
  have hbin : ∀ t : ℕ, binomialQuotient t = ((16 : ℚ) ^ t - 1) / (15 * t) :=
    fun _ => rfl
  have hpow : ((16 : ℚ) ^ (9 * r + 5)) =
      (16 : ℚ) ^ r * (16 : ℚ) ^ (8 * r + 5) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [pairedError]
  rw [hdec, hbin, hpow]
  simp only [poleThree]
  field_simp
  push_cast
  ring

/-- The pole-four paired error factors through the cancelled quotient. -/
theorem pairedError_poleFour_factor (r : ℕ) :
    pairedError poleFour 6 r / 3 =
      ((5 : ℚ) / 16 ^ (9 * r + 6)) * binomialQuotient (8 * r + 6) := by
  have hdec := poleFour_decimation r
  have hbin : ∀ t : ℕ, binomialQuotient t = ((16 : ℚ) ^ t - 1) / (15 * t) :=
    fun _ => rfl
  have hpow : ((16 : ℚ) ^ (9 * r + 6)) =
      (16 : ℚ) ^ r * (16 : ℚ) ^ (8 * r + 6) := by
    rw [← pow_add]
    congr 1
    omega
  have hlin : (8 : ℕ) * r + 6 = 2 * (4 * r + 3) := by omega
  simp only [pairedError]
  rw [hdec, hbin, hpow, hlin]
  simp only [poleFour]
  field_simp
  push_cast
  ring

end Theory.PiDigits.T80SelectedPairedQuotientFactorization

#print axioms Theory.PiDigits.T80SelectedPairedQuotientFactorization.pairedError_poleOne_factor
#print axioms Theory.PiDigits.T80SelectedPairedQuotientFactorization.pairedError_poleTwo_factor
#print axioms Theory.PiDigits.T80SelectedPairedQuotientFactorization.pairedError_poleThree_factor
#print axioms Theory.PiDigits.T80SelectedPairedQuotientFactorization.pairedError_poleFour_factor
