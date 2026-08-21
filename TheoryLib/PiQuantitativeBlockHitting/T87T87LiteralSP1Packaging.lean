import TheoryLib.PiQuantitativeBlockHitting.T86T86NonselectedEndpointCongruence

/-!
# T87: literal rational SP1 packaging

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module identifies the selected even epoch with T86's exact endpoint
shape and packages its finite rational three-adic congruence.  It makes no
claim about the hidden carry, decimal expansion, canonical V1, or SP1's use
in any further argument.
-/

namespace Theory.PiDigits.T87LiteralSP1Packaging

open T77SelectedPadicDefectShell T78SelectedPadicDefectCongruence
  T86NonselectedEndpointCongruence

/-- Consecutive positive even selected depths have the exact ninefold endpoint
relation used by `endpointDefect`. -/
theorem selectedDepth_even_step (t : ℕ) (ht : 1 ≤ t) :
    selectedDepth (2 * t + 2) = 9 * selectedDepth (2 * t) + 13 := by
  have hpow : 3 ^ (2 * t) % 72 = 9 := by
    rw [show 3 ^ (2 * t) = 9 ^ t by
      rw [pow_mul]
      norm_num]
    exact nine_pow_mod_seventyTwo ht
  have hdecomp : 3 ^ (2 * t) = 72 * (3 ^ (2 * t) / 72) + 9 := by
    have h := Nat.mod_add_div (3 ^ (2 * t)) 72
    omega
  let q : ℕ := 3 ^ (2 * t) / 72
  have hcurr : 5 * 3 ^ (2 * t) - 13 = 8 * (45 * q + 4) := by
    dsimp [q]
    omega
  have hnext : 5 * 3 ^ (2 * t + 2) - 13 = 8 * (405 * q + 49) := by
    rw [show 3 ^ (2 * t + 2) = 9 * 3 ^ (2 * t) by
      rw [show 2 * t + 2 = 2 * t + 2 by rfl, pow_add]
      ring]
    dsimp [q]
    omega
  simp only [selectedDepth]
  rw [hcurr, hnext,
    Nat.mul_div_cancel_left _ (by norm_num),
    Nat.mul_div_cancel_left _ (by norm_num)]
  ring

/-- At every positive even selected epoch, the literal finite rational BBP
endpoint defect is one modulo nine in the three-adic sense. -/
theorem literal_sp1 (t : ℕ) (ht : 1 ≤ t) :
    RatCongruentThree 2
      (9 * bbpPartial (selectedDepth (2 * t + 2)) -
        bbpPartial (selectedDepth (2 * t))) 1 := by
  rw [selectedDepth_even_step t ht]
  exact endpointDefect_congr_one_at_selectedDepth t ht

end Theory.PiDigits.T87LiteralSP1Packaging

#print axioms Theory.PiDigits.T87LiteralSP1Packaging.selectedDepth_even_step
#print axioms Theory.PiDigits.T87LiteralSP1Packaging.literal_sp1
