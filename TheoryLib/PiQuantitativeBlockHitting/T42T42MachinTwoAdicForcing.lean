import TheoryLib.PiQuantitativeBlockHitting.T41T41MachinV1Equivalence
import TheoryLib.PiQuantitativeBlockHitting.T40T40MachinLocalForcing
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# T42: two-adic foundations for the sampled Machin forcing

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module isolates the pairwise arithmetic needed to study cancellation in
the twelve-term rational forcing from T40.  It proves exact denominator
clearing, odd-denominator presentations, two-adic order one for each
three-positive-pair block, and the even/odd six-term regroupings.

At the operator stop point, the final combination proving two-adic order
`N + 4` for the complete sampled forcing had not yet been formalized.  That
global statement therefore remains a `proof sketch` in `ultrapi.md`.

This statement does not imply recurrence, orbit density, normality, or the
every-word conjecture.
-/

noncomputable section

namespace Theory.PiDigits.MachinTwoAdicForcing

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinLocalForcing

/-- An odd integer is not divisible by two. -/
lemma two_not_dvd_of_odd_int {z : ℤ} (hz : Odd z) : ¬ (2 : ℤ) ∣ z := by
  rw [← even_iff_two_dvd, Int.not_even_iff_odd]
  exact hz

lemma nat_ne_zero_of_odd {d : ℕ} (hd : Odd d) : d ≠ 0 := by
  intro hzero
  subst d
  norm_num at hd

lemma int_ne_zero_of_odd {z : ℤ} (hz : Odd z) : z ≠ 0 := by
  intro hzero
  subst z
  norm_num at hz

/-- The two-adic valuation of an odd integer, viewed rationally, is zero. -/
lemma padicValRat_two_intCast_eq_zero_of_odd {z : ℤ} (hz : Odd z) :
    padicValRat 2 (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  simpa using padicValInt.eq_zero_of_not_dvd (two_not_dvd_of_odd_int hz)

/-- The two-adic valuation of an odd natural, viewed rationally, is zero. -/
lemma padicValRat_two_natCast_eq_zero_of_odd {d : ℕ} (hd : Odd d) :
    padicValRat 2 (d : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  simpa using padicValNat.eq_zero_of_not_dvd hd.not_two_dvd_nat

/-- A twice-odd integer divided by an odd natural has two-adic order one. -/
lemma padicValRat_two_twiceOdd_div_odd
    {z : ℤ} {d : ℕ} (hz : Odd z) (hd : Odd d) :
    padicValRat 2 (((2 * z : ℤ) : ℚ) / (d : ℚ)) = 1 := by
  have hz0 : (z : ℚ) ≠ 0 := by
    exact_mod_cast int_ne_zero_of_odd hz
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast nat_ne_zero_of_odd hd
  have htwo : padicValRat 2 (2 : ℚ) = 1 :=
    padicValRat.self (by norm_num : 1 < (2 : ℕ))
  rw [show (((2 * z : ℤ) : ℚ)) = (2 : ℚ) * (z : ℚ) by norm_num,
    padicValRat.div (mul_ne_zero (by norm_num) hz0) hd0,
    padicValRat.mul (by norm_num) hz0,
    htwo,
    padicValRat_two_intCast_eq_zero_of_odd hz,
    padicValRat_two_natCast_eq_zero_of_odd hd]
  norm_num

/-- Three fractions with twice-odd numerators and odd denominators still
have exact two-adic order one.  The key point is that, over the common odd
denominator, the half-numerator is a sum of three odd products. -/
lemma padicValRat_two_sum_three_twiceOdd_div_odd
    {z0 z1 z2 : ℤ} {d0 d1 d2 : ℕ}
    (hz0 : Odd z0) (hz1 : Odd z1) (hz2 : Odd z2)
    (hd0 : Odd d0) (hd1 : Odd d1) (hd2 : Odd d2) :
    padicValRat 2
      ((((2 * z0 : ℤ) : ℚ) / (d0 : ℚ)) +
        (((2 * z1 : ℤ) : ℚ) / (d1 : ℚ)) +
        (((2 * z2 : ℤ) : ℚ) / (d2 : ℚ))) = 1 := by
  let z : ℤ :=
    z0 * (d1 : ℤ) * (d2 : ℤ) +
      z1 * (d0 : ℤ) * (d2 : ℤ) +
      z2 * (d0 : ℤ) * (d1 : ℤ)
  have hterm0 : Odd (z0 * (d1 : ℤ) * (d2 : ℤ)) :=
    (hz0.mul hd1.natCast).mul hd2.natCast
  have hterm1 : Odd (z1 * (d0 : ℤ) * (d2 : ℤ)) :=
    (hz1.mul hd0.natCast).mul hd2.natCast
  have hterm2 : Odd (z2 * (d0 : ℤ) * (d1 : ℤ)) :=
    (hz2.mul hd0.natCast).mul hd1.natCast
  have hz : Odd z := by
    exact (hterm0.add_odd hterm1).add_odd hterm2
  have hd : Odd (d0 * d1 * d2) := (hd0.mul hd1).mul hd2
  have hd0q : (d0 : ℚ) ≠ 0 := by
    exact_mod_cast nat_ne_zero_of_odd hd0
  have hd1q : (d1 : ℚ) ≠ 0 := by
    exact_mod_cast nat_ne_zero_of_odd hd1
  have hd2q : (d2 : ℚ) ≠ 0 := by
    exact_mod_cast nat_ne_zero_of_odd hd2
  have hcombine :
      (((2 * z0 : ℤ) : ℚ) / (d0 : ℚ)) +
          (((2 * z1 : ℤ) : ℚ) / (d1 : ℚ)) +
          (((2 * z2 : ℤ) : ℚ) / (d2 : ℚ)) =
        (((2 * z : ℤ) : ℚ) / ((d0 * d1 * d2 : ℕ) : ℚ)) := by
    dsimp [z]
    push_cast
    field_simp [hd0q, hd1q, hd2q]
  rw [hcombine]
  exact padicValRat_two_twiceOdd_div_odd hz hd

/-- The natural common denominator used to clear one positive arctangent
pair. -/
def pairDenominatorNat (q r : ℕ) : ℕ :=
  r * (r + 2) * q ^ (r + 2)

/-- For odd base and odd exponent, the pair denominator is odd. -/
lemma pairDenominatorNat_odd
    {q r : ℕ} (hq : Odd q) (hr : Odd r) :
    Odd (pairDenominatorNat q r) := by
  have hr2 : Odd (r + 2) := hr.add_even (by norm_num)
  exact (hr.mul hr2).mul hq.pow

/-- Rewrite one positive pair as its cleared integer numerator over the
natural common denominator. -/
lemma oddPowerPairRat_eq_pairedNumerator_div
    {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    oddPowerPairRat q r =
      (pairedNumerator q r : ℚ) / (pairDenominatorNat q r : ℚ) := by
  have hden0 : (pairDenominatorNat q r : ℚ) ≠ 0 := by
    exact_mod_cast
      (mul_ne_zero (mul_ne_zero hr (by omega)) (pow_ne_zero _ hq))
  apply (eq_div_iff hden0).2
  have hclear := oddPowerPairRat_denominator_clear q r hq hr
  simpa [pairDenominatorNat, mul_comm, mul_left_comm, mul_assoc] using hclear

/-- If the cleared pair numerator is twice odd, the pair has a
twice-odd-over-odd presentation. -/
lemma oddPowerPairRat_eq_twiceOdd_div_odd
    {q r : ℕ} (hq : Odd q) (hr : Odd r)
    {z : ℤ} (hnum : pairedNumerator q r = 2 * z) :
    oddPowerPairRat q r =
      (((2 * z : ℤ) : ℚ) / (pairDenominatorNat q r : ℚ)) := by
  rw [oddPowerPairRat_eq_pairedNumerator_div
    (nat_ne_zero_of_odd hq) (nat_ne_zero_of_odd hr), hnum]

/-- Three positive pairs whose odd exponents are separated by four. -/
def threeOddPowerPairsRat (q r : ℕ) : ℚ :=
  oddPowerPairRat q r + oddPowerPairRat q (r + 4) +
    oddPowerPairRat q (r + 8)

/-- At base five, every three-pair block beginning at an odd exponent has
exact two-adic order one. -/
theorem padicValRat_two_threeOddPowerPairsRat_five
    (r : ℕ) (hr : Odd r) :
    padicValRat 2 (threeOddPowerPairsRat 5 r) = 1 := by
  have hr4 : Odd (r + 4) := hr.add_even (by norm_num)
  have hr8 : Odd (r + 8) := hr.add_even (by norm_num)
  obtain ⟨z0, hz0, hnum0⟩ := pairedNumerator_five_twice_odd r
  obtain ⟨z1, hz1, hnum1⟩ := pairedNumerator_five_twice_odd (r + 4)
  obtain ⟨z2, hz2, hnum2⟩ := pairedNumerator_five_twice_odd (r + 8)
  rw [threeOddPowerPairsRat,
    oddPowerPairRat_eq_twiceOdd_div_odd (by norm_num) hr hnum0,
    oddPowerPairRat_eq_twiceOdd_div_odd (by norm_num) hr4 hnum1,
    oddPowerPairRat_eq_twiceOdd_div_odd (by norm_num) hr8 hnum2]
  exact padicValRat_two_sum_three_twiceOdd_div_odd hz0 hz1 hz2
    (pairDenominatorNat_odd (by norm_num) hr)
    (pairDenominatorNat_odd (by norm_num) hr4)
    (pairDenominatorNat_odd (by norm_num) hr8)

/-- At base 239, every three-pair block beginning at an odd exponent has
exact two-adic order one. -/
theorem padicValRat_two_threeOddPowerPairsRat_twoThirtyNine
    (r : ℕ) (hr : Odd r) :
    padicValRat 2 (threeOddPowerPairsRat 239 r) = 1 := by
  have hr4 : Odd (r + 4) := hr.add_even (by norm_num)
  have hr8 : Odd (r + 8) := hr.add_even (by norm_num)
  obtain ⟨z0, hz0, hnum0⟩ := pairedNumerator_twoThirtyNine_twice_odd r
  obtain ⟨z1, hz1, hnum1⟩ :=
    pairedNumerator_twoThirtyNine_twice_odd (r + 4)
  obtain ⟨z2, hz2, hnum2⟩ :=
    pairedNumerator_twoThirtyNine_twice_odd (r + 8)
  rw [threeOddPowerPairsRat,
    oddPowerPairRat_eq_twiceOdd_div_odd (by norm_num) hr hnum0,
    oddPowerPairRat_eq_twiceOdd_div_odd (by norm_num) hr4 hnum1,
    oddPowerPairRat_eq_twiceOdd_div_odd (by norm_num) hr8 hnum2]
  exact padicValRat_two_sum_three_twiceOdd_div_odd hz0 hz1 hz2
    (pairDenominatorNat_odd (by norm_num) hr)
    (pairDenominatorNat_odd (by norm_num) hr4)
    (pairDenominatorNat_odd (by norm_num) hr8)

/-- Two consecutive Taylor terms beginning at an even index form one
positive odd-power pair. -/
lemma arctanTermRat_even_pair
    (q k : ℕ) (hq : q ≠ 0) :
    arctanTermRat q (2 * k) + arctanTermRat q (2 * k + 1) =
      oddPowerPairRat q (4 * k + 1) := by
  unfold arctanTermRat oddPowerPairRat
  rw [show (-1 : ℚ) ^ (2 * k) = 1 by
      rw [pow_mul]
      norm_num,
    show (-1 : ℚ) ^ (2 * k + 1) = -1 by
      rw [pow_add, pow_mul]
      norm_num]
  rw [show 2 * (2 * k) + 1 = 4 * k + 1 by omega,
    show 2 * (2 * k + 1) + 1 = 4 * k + 3 by omega,
    show 4 * k + 1 + 2 = 4 * k + 3 by omega]
  simp only [inv_pow]
  push_cast
  field_simp
  ring

/-- Two consecutive Taylor terms beginning at an odd index are the
negative of one positive odd-power pair. -/
lemma arctanTermRat_odd_pair
    (q k : ℕ) (hq : q ≠ 0) :
    arctanTermRat q (2 * k + 1) + arctanTermRat q (2 * k + 2) =
      -oddPowerPairRat q (4 * k + 3) := by
  unfold arctanTermRat oddPowerPairRat
  rw [show (-1 : ℚ) ^ (2 * k + 1) = -1 by
      rw [pow_add, pow_mul]
      norm_num,
    show (-1 : ℚ) ^ (2 * k + 2) = 1 by
      rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
      norm_num]
  rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 by omega,
    show 2 * (2 * k + 2) + 1 = 4 * k + 5 by omega,
    show 4 * k + 3 + 2 = 4 * k + 5 by omega]
  simp only [inv_pow]
  push_cast
  field_simp
  ring

/-- A six-term window beginning at an even Taylor index is exactly three
positive odd-power pairs. -/
lemma sixTermArctanWindowRat_even
    (q k : ℕ) (hq : q ≠ 0) :
    sixTermArctanWindowRat q (2 * k) =
      threeOddPowerPairsRat q (4 * k + 1) := by
  simp only [sixTermArctanWindowRat, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  calc
    (((((arctanTermRat q (2 * k + 0) + arctanTermRat q (2 * k + 1)) +
          arctanTermRat q (2 * k + 2)) + arctanTermRat q (2 * k + 3)) +
          arctanTermRat q (2 * k + 4)) + arctanTermRat q (2 * k + 5)) =
        (arctanTermRat q (2 * k) + arctanTermRat q (2 * k + 1)) +
          (arctanTermRat q (2 * (k + 1)) +
            arctanTermRat q (2 * (k + 1) + 1)) +
          (arctanTermRat q (2 * (k + 2)) +
            arctanTermRat q (2 * (k + 2) + 1)) := by
      rw [Nat.add_zero,
        show 2 * k + 2 = 2 * (k + 1) by omega,
        show 2 * k + 3 = 2 * (k + 1) + 1 by omega,
        show 2 * k + 4 = 2 * (k + 2) by omega,
        show 2 * k + 5 = 2 * (k + 2) + 1 by omega]
      ring
    _ = threeOddPowerPairsRat q (4 * k + 1) := by
      rw [arctanTermRat_even_pair q k hq,
        arctanTermRat_even_pair q (k + 1) hq,
        arctanTermRat_even_pair q (k + 2) hq]
      unfold threeOddPowerPairsRat
      congr 1

/-- A six-term window beginning at an odd Taylor index is the negative of
three positive odd-power pairs. -/
lemma sixTermArctanWindowRat_odd
    (q k : ℕ) (hq : q ≠ 0) :
    sixTermArctanWindowRat q (2 * k + 1) =
      -threeOddPowerPairsRat q (4 * k + 3) := by
  simp only [sixTermArctanWindowRat, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  calc
    (((((arctanTermRat q (2 * k + 1 + 0) +
          arctanTermRat q (2 * k + 1 + 1)) +
          arctanTermRat q (2 * k + 1 + 2)) +
          arctanTermRat q (2 * k + 1 + 3)) +
          arctanTermRat q (2 * k + 1 + 4)) +
          arctanTermRat q (2 * k + 1 + 5)) =
        (arctanTermRat q (2 * k + 1) + arctanTermRat q (2 * k + 2)) +
          (arctanTermRat q (2 * (k + 1) + 1) +
            arctanTermRat q (2 * (k + 1) + 2)) +
          (arctanTermRat q (2 * (k + 2) + 1) +
            arctanTermRat q (2 * (k + 2) + 2)) := by
      rw [Nat.add_zero,
        show 2 * k + 1 + 1 = 2 * k + 2 by omega,
        show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega,
        show 2 * k + 1 + 3 = 2 * (k + 1) + 2 by omega,
        show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by omega,
        show 2 * k + 1 + 5 = 2 * (k + 2) + 2 by omega]
      ring
    _ = -threeOddPowerPairsRat q (4 * k + 3) := by
      rw [arctanTermRat_odd_pair q k hq,
        arctanTermRat_odd_pair q (k + 1) hq,
        arctanTermRat_odd_pair q (k + 2) hq]
      unfold threeOddPowerPairsRat
      congr 1 <;> ring

end Theory.PiDigits.MachinTwoAdicForcing

#print axioms
  Theory.PiDigits.MachinTwoAdicForcing.padicValRat_two_twiceOdd_div_odd
#print axioms
  Theory.PiDigits.MachinTwoAdicForcing.padicValRat_two_sum_three_twiceOdd_div_odd
