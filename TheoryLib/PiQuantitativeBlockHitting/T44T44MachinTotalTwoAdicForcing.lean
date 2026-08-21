import TheoryLib.PiQuantitativeBlockHitting.T42T42MachinTwoAdicForcing

/-!
# T44: exact two-adic order of the complete sampled Machin forcing

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T40 expands one sampled Machin forcing increment into twelve rational Taylor
terms, and T42 proves exact two-adic order one for each three-positive-pair
block.  This module combines the differently weighted base-5 and base-239
blocks.  Their valuations are unequal after weighting, so no two-adic
cancellation is possible.  The complete rational forcing at index `N` has
exact two-adic order `N + 4`.

This is exact arithmetic information about the actual Machin forcing.  T43
shows that the same valuation profile can coexist with a nondense forced
base-ten orbit, so the theorem does not imply a cylinder hit, recurrence,
normality, or the every-word conjecture.
-/

noncomputable section

namespace Theory.PiDigits.MachinTotalTwoAdicForcing

open Theory.PiDigits.MachinLocalForcing
open Theory.PiDigits.MachinTwoAdicForcing

/-- The twelve-term forcing is exactly the weighted sum of one three-pair
block at base 5 and one at base 239. -/
theorem sampledMachinForcingRat_eq_threePairBlocks (N : ℕ) :
    sampledMachinForcingRat N =
      (10 : ℚ) ^ (N + 1) *
        (16 * threeOddPowerPairsRat 5 (12 * N + 5) +
          4 * threeOddPowerPairsRat 239 (12 * N + 7)) := by
  rw [sampledMachinForcingRat]
  rw [show 6 * N + 2 = 2 * (3 * N + 1) by omega,
    sixTermArctanWindowRat_even 5 (3 * N + 1) (by norm_num),
    show 4 * (3 * N + 1) + 1 = 12 * N + 5 by omega,
    show 6 * N + 3 = 2 * (3 * N + 1) + 1 by omega,
    sixTermArctanWindowRat_odd 239 (3 * N + 1) (by norm_num),
    show 4 * (3 * N + 1) + 3 = 12 * N + 7 by omega]
  ring

/-- The rational number four has two-adic order two. -/
lemma padicValRat_two_four : padicValRat 2 (4 : ℚ) = 2 := by
  have htwo : padicValRat 2 (2 : ℚ) = 1 :=
    padicValRat.self (by norm_num : 1 < (2 : ℕ))
  rw [show (4 : ℚ) = 2 * 2 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num), htwo]
  norm_num

/-- The rational number ten has two-adic order one. -/
lemma padicValRat_two_ten : padicValRat 2 (10 : ℚ) = 1 := by
  have htwo : padicValRat 2 (2 : ℚ) = 1 :=
    padicValRat.self (by norm_num : 1 < (2 : ℕ))
  have hfive : padicValRat 2 (5 : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd (by norm_num)
  rw [show (10 : ℚ) = 2 * 5 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num), htwo, hfive]
  norm_num

/-- Before the outer power of ten is applied, the weighted two-block sum has
exact two-adic order three. -/
theorem padicValRat_two_weighted_threePairBlocks (N : ℕ) :
    padicValRat 2
      (16 * threeOddPowerPairsRat 5 (12 * N + 5) +
        4 * threeOddPowerPairsRat 239 (12 * N + 7)) = 3 := by
  let A : ℚ := threeOddPowerPairsRat 5 (12 * N + 5)
  let B : ℚ := threeOddPowerPairsRat 239 (12 * N + 7)
  have hodd5 : Odd (12 * N + 5) := by
    refine ⟨6 * N + 2, ?_⟩
    omega
  have hodd239 : Odd (12 * N + 7) := by
    refine ⟨6 * N + 3, ?_⟩
    omega
  have hA : padicValRat 2 A = 1 := by
    exact padicValRat_two_threeOddPowerPairsRat_five _ hodd5
  have hB : padicValRat 2 B = 1 := by
    exact padicValRat_two_threeOddPowerPairsRat_twoThirtyNine _ hodd239
  have hA0 : A ≠ 0 := by
    intro hzero
    simp [hzero] at hA
  have hB0 : B ≠ 0 := by
    intro hzero
    simp [hzero] at hB
  have h4A : padicValRat 2 (4 * A) = 3 := by
    rw [padicValRat.mul (by norm_num) hA0, padicValRat_two_four, hA]
    norm_num
  have hsum0 : 4 * A + B ≠ 0 := by
    intro hzero
    have heq : 4 * A = -B := eq_neg_of_add_eq_zero_left hzero
    have hvaleq := congrArg (padicValRat 2) heq
    rw [h4A, padicValRat.neg, hB] at hvaleq
    omega
  have hinner : padicValRat 2 (4 * A + B) = 1 := by
    rw [add_comm, ← hB]
    exact padicValRat.add_eq_of_lt (p := 2) (by rwa [add_comm]) hB0
      (mul_ne_zero (by norm_num) hA0) (by rw [h4A, hB]; norm_num)
  have houter : 16 * A + 4 * B = 4 * (4 * A + B) := by ring
  rw [show threeOddPowerPairsRat 5 (12 * N + 5) = A by rfl,
    show threeOddPowerPairsRat 239 (12 * N + 7) = B by rfl,
    houter, padicValRat.mul (by norm_num) hsum0, padicValRat_two_four, hinner]
  norm_num

/-- The complete sampled Machin forcing at index `N` has exact two-adic order
`N + 4`.  Equivalently, after reduction its numerator contains exactly
`N + 4` factors of two.  The final two theorems below state the odd reduced
denominator and reduced-numerator exponent explicitly. -/
theorem padicValRat_two_sampledMachinForcingRat (N : ℕ) :
    padicValRat 2 (sampledMachinForcingRat N) = (N : ℤ) + 4 := by
  rw [sampledMachinForcingRat_eq_threePairBlocks]
  have hblocks :
      16 * threeOddPowerPairsRat 5 (12 * N + 5) +
          4 * threeOddPowerPairsRat 239 (12 * N + 7) ≠ 0 := by
    intro hzero
    have hval := padicValRat_two_weighted_threePairBlocks N
    simp [hzero] at hval
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblocks,
    padicValRat.pow (by norm_num), padicValRat_two_ten,
    padicValRat_two_weighted_threePairBlocks]
  push_cast
  ring

/-- A rational number with positive two-adic order has odd reduced
denominator. -/
lemma odd_den_of_pos_padicValRat_two (q : ℚ)
    (hpos : 0 < padicValRat 2 q) : Odd q.den := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hden
  have hcop : Nat.Coprime 2 q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ 2 ∣ q.num.natAbs :=
    Nat.prime_two.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt 2 q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  have hvden : 1 ≤ padicValNat 2 q.den :=
    one_le_padicValNat_of_dvd q.den_nz hden
  rw [padicValRat_def, hvnum] at hpos
  omega

/-- The reduced denominator of the complete sampled Machin forcing is odd. -/
theorem sampledMachinForcingRat_den_odd (N : ℕ) :
    Odd (sampledMachinForcingRat N).den := by
  apply odd_den_of_pos_padicValRat_two
  rw [padicValRat_two_sampledMachinForcingRat]
  omega

/-- The reduced numerator of the complete sampled Machin forcing contains
exactly `N + 4` factors of two. -/
theorem padicValInt_two_sampledMachinForcingRat_num (N : ℕ) :
    padicValInt 2 (sampledMachinForcingRat N).num = N + 4 := by
  have hodd := sampledMachinForcingRat_den_odd N
  have hnotdvd : ¬ 2 ∣ (sampledMachinForcingRat N).den := by
    rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
  have hvden : padicValNat 2 (sampledMachinForcingRat N).den = 0 :=
    padicValNat.eq_zero_of_not_dvd hnotdvd
  have hval := padicValRat_two_sampledMachinForcingRat N
  rw [padicValRat_def, hvden] at hval
  norm_num at hval
  exact_mod_cast hval

end Theory.PiDigits.MachinTotalTwoAdicForcing

#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.sampledMachinForcingRat_eq_threePairBlocks
#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.padicValRat_two_four
#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.padicValRat_two_ten
#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.padicValRat_two_weighted_threePairBlocks
#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.padicValRat_two_sampledMachinForcingRat
#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.odd_den_of_pos_padicValRat_two
#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.sampledMachinForcingRat_den_odd
#print axioms
  Theory.PiDigits.MachinTotalTwoAdicForcing.padicValInt_two_sampledMachinForcingRat_num
