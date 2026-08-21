import TheoryLib.PiQuantitativeBlockHitting.T93T93ThreeLocalOperations

/-!
# T94: residue equality from rational three-adic congruence

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module transports rational three-adic congruence between three-integral
rationals to equality of their canonical T91 three-local residues, including
the resulting one-step finite-residue recurrence for scaled BBP partial
sums.  It does not assert a hidden carry, a decimal digit, an SP1 resolution,
or canonical V1.
-/

namespace Theory.PiDigits.T94SelectedResidueTransition

open T78SelectedPadicDefectCongruence T89SelectedDepthScaledIntegrality
  T90ScaledCarryInterface T91ThreeLocalGrowth T92ThreeLocalCongruence
  T93ThreeLocalOperations

/-- Rational three-adic congruence of two three-integral rationals implies
equality of their canonical three-local residues at the same precision. -/
theorem threeLocalResidue_eq_of_ratCongruentThree (n : ℕ) (p q : ℚ)
    (hp : 0 ≤ padicValRat 3 p) (hq : 0 ≤ padicValRat 3 q)
    (h : RatCongruentThree n p q) :
    threeLocalResidue n p (not_dvd_three_den_of_nonneg_val hp) =
      threeLocalResidue n q (not_dvd_three_den_of_nonneg_val hq) :=
  (threeLocalResidue_eq_iff n p q (not_dvd_three_den_of_nonneg_val hp)
    (not_dvd_three_den_of_nonneg_val hq)).2
    (threeLocalCongruent_of_ratCongruentThree n p q hp hq h)

/-- Three-integral rationals are closed under addition at the valuation
level.  The zero-sum case is included explicitly. -/
theorem padicValRat_three_add_nonneg (p q : ℚ)
    (hp : 0 ≤ padicValRat 3 p) (hq : 0 ≤ padicValRat 3 q) :
    0 ≤ padicValRat 3 (p + q) := by
  rcases eq_or_ne (p + q) 0 with hzero | hzero
  · simp [hzero]
  · exact le_trans (min_le_min hp hq) (padicValRat.min_le_padicValRat_add hzero)

/-- The rational target of the selected scaled-partial step is three-integral. -/
theorem evenScaledPartial_step_sum_nonneg (t : ℕ) (ht : 1 ≤ t) :
    0 ≤ padicValRat 3 (evenScaledPartial t + (3 : ℚ) ^ (2 * t)) := by
  apply padicValRat_three_add_nonneg
  · exact scaled_bbpPartial_three_integral t ht
  · rw [show (3 : ℚ) ^ (2 * t) = ((3 ^ (2 * t) : ℕ) : ℚ) by norm_cast]
    exact zero_le_padicValRat_of_nat _

/-- T92's rational selected-partial step gives canonical T92 cross-product
congruence once both rationals are known three-integral. -/
theorem evenScaledPartial_step_threeLocalCongruent (t : ℕ) (ht : 1 ≤ t) :
    ThreeLocalCongruent (2 * t + 2) (evenScaledPartial (t + 1))
      (evenScaledPartial t + (3 : ℚ) ^ (2 * t)) := by
  apply threeLocalCongruent_of_ratCongruentThree
  · exact scaled_bbpPartial_three_integral (t + 1) (by omega)
  · exact evenScaledPartial_step_sum_nonneg t ht
  · exact evenScaledPartial_step_congruent t ht

/-- The two rationals in the selected scaled-partial step have equal local
residues at the corresponding precision. -/
theorem evenScaledPartial_step_residue_eq_sumResidue (t : ℕ) (ht : 1 ≤ t) :
    threeLocalResidue (2 * t + 2) (evenScaledPartial (t + 1))
      (not_dvd_three_den_of_nonneg_val
        (scaled_bbpPartial_three_integral (t + 1) (by omega))) =
    threeLocalResidue (2 * t + 2) (evenScaledPartial t + (3 : ℚ) ^ (2 * t))
      (not_dvd_three_den_of_nonneg_val (evenScaledPartial_step_sum_nonneg t ht)) := by
  exact threeLocalResidue_eq_of_ratCongruentThree _ _ _
    (scaled_bbpPartial_three_integral (t + 1) (by omega))
    (evenScaledPartial_step_sum_nonneg t ht) (evenScaledPartial_step_congruent t ht)

/-- The positive-even scaled BBP partial residues obey the exact finite
`ZMod` recurrence.  This is a residue identity only, not a carry or digit
interpretation. -/
theorem evenScaledResidue_step (t : ℕ) (ht : 1 ≤ t) :
    evenScaledResidue (2 * t + 2) (t + 1) (by omega) =
      evenScaledResidue (2 * t + 2) t ht +
        ((3 : ZMod (3 ^ (2 * t + 2))) ^ (2 * t)) := by
  have hsum := evenScaledPartial_step_sum_nonneg t ht
  have heq := evenScaledPartial_step_residue_eq_sumResidue t ht
  have hpow : 0 ≤ padicValRat 3 ((3 : ℚ) ^ (2 * t)) := by
    rw [show (3 : ℚ) ^ (2 * t) = ((3 ^ (2 * t) : ℕ) : ℚ) by norm_cast]
    exact zero_le_padicValRat_of_nat _
  have hadd := threeLocalResidue_add (2 * t + 2) (evenScaledPartial t)
    ((3 : ℚ) ^ (2 * t))
    (not_dvd_three_den_of_nonneg_val (scaled_bbpPartial_three_integral t ht))
    (not_dvd_three_den_of_nonneg_val hpow)
    (not_dvd_three_den_of_nonneg_val hsum)
  have hpowres : threeLocalResidue (2 * t + 2) ((3 : ℚ) ^ (2 * t))
      (not_dvd_three_den_of_nonneg_val hpow) =
      ((3 : ZMod (3 ^ (2 * t + 2))) ^ (2 * t)) := by
    convert threeLocalResidue_intCast (2 * t + 2) ((3 : ℤ) ^ (2 * t)) using 1 <;> norm_cast
  change threeLocalResidue (2 * t + 2) (evenScaledPartial (t + 1)) _ =
    threeLocalResidue (2 * t + 2) (evenScaledPartial t) _ + _
  calc
    _ = threeLocalResidue (2 * t + 2) (evenScaledPartial t + (3 : ℚ) ^ (2 * t)) _ := heq
    _ = threeLocalResidue (2 * t + 2) (evenScaledPartial t) _ +
        threeLocalResidue (2 * t + 2) ((3 : ℚ) ^ (2 * t)) _ := hadd
    _ = _ := by rw [hpowres]

end Theory.PiDigits.T94SelectedResidueTransition

#print axioms Theory.PiDigits.T94SelectedResidueTransition.threeLocalResidue_eq_of_ratCongruentThree
#print axioms Theory.PiDigits.T94SelectedResidueTransition.padicValRat_three_add_nonneg
#print axioms Theory.PiDigits.T94SelectedResidueTransition.evenScaledPartial_step_sum_nonneg
#print axioms Theory.PiDigits.T94SelectedResidueTransition.evenScaledPartial_step_threeLocalCongruent
#print axioms Theory.PiDigits.T94SelectedResidueTransition.evenScaledPartial_step_residue_eq_sumResidue
#print axioms Theory.PiDigits.T94SelectedResidueTransition.evenScaledResidue_step
