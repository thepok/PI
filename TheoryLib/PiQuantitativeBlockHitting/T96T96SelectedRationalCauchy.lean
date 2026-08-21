import TheoryLib.PiQuantitativeBlockHitting.T94T94SelectedResidueTransition

/-!
# T96: rational three-adic Cauchy structure of scaled BBP partial sums

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The positive-even selected scaled BBP partial sums agree to increasing
three-adic precision.  This is finite rational congruence structure only; no
padic completion, real convergence, carry, decimal digit, SP1 resolution, or
canonical V1 is asserted.
-/

namespace Theory.PiDigits.T96SelectedRationalCauchy

open T78SelectedPadicDefectCongruence T89SelectedDepthScaledIntegrality
  T90ScaledCarryInterface T92ThreeLocalCongruence

/-- Congruence at a higher precision implies congruence at a lower one. -/
theorem ratCongruentThree_mono {n m : ℕ} (hnm : n ≤ m) {x y : ℚ}
    (h : RatCongruentThree m x y) : RatCongruentThree n x y := by
  rcases h with hxy | hval
  · exact Or.inl hxy
  · exact Or.inr (le_trans (by exact_mod_cast hnm) hval)

/-- The step increment vanishes three-adically at precision `2 * t`. -/
theorem pow_three_incr_congruent_zero (t : ℕ) :
    RatCongruentThree (2 * t) ((3 : ℚ) ^ (2 * t)) 0 := by
  right
  rw [show (3 : ℚ) ^ (2 * t) - 0 = (3 : ℚ) ^ (2 * t) by ring,
    show (3 : ℚ) ^ (2 * t) = ((3 ^ (2 * t) : ℕ) : ℚ) by norm_cast,
    padicValRat.of_nat, padicValNat.prime_pow]

/-- Consecutive positive-even scaled partial sums agree modulo `3^(2*t)`. -/
theorem evenScaledPartial_adjacent_congruent (t : ℕ) (ht : 1 ≤ t) :
    RatCongruentThree (2 * t) (evenScaledPartial (t + 1))
      (evenScaledPartial t) := by
  have hstep := evenScaledPartial_step_congruent t ht
  have hlow := ratCongruentThree_mono (n := 2 * t) (m := 2 * t + 2)
    (by omega) hstep
  have hshift : RatCongruentThree (2 * t)
      (evenScaledPartial t + (3 : ℚ) ^ (2 * t))
      (evenScaledPartial t + 0) :=
    ratCongruentThree_add (ratCongruentThree_refl _ _)
      (pow_three_incr_congruent_zero t)
  refine ratCongruentThree_trans hlow ?_
  simpa using hshift

/-- Any two positive-even scaled partial sums agree to the precision selected
by the smaller index. -/
theorem evenScaledPartial_cauchy (s t : ℕ) (hs : 1 ≤ s) (hst : s ≤ t) :
    RatCongruentThree (2 * s) (evenScaledPartial t)
      (evenScaledPartial s) := by
  have key : ∀ d : ℕ,
      RatCongruentThree (2 * s) (evenScaledPartial (s + d))
        (evenScaledPartial s) := by
    intro d
    induction d with
    | zero => exact ratCongruentThree_refl _ _
    | succ d ih =>
      have hadj := evenScaledPartial_adjacent_congruent (s + d) (by omega)
      have hle : 2 * s ≤ 2 * (s + d) := by omega
      exact ratCongruentThree_trans (ratCongruentThree_mono hle hadj) ih
  have hkey := key (t - s)
  rwa [show s + (t - s) = t by omega] at hkey

end Theory.PiDigits.T96SelectedRationalCauchy

#print axioms Theory.PiDigits.T96SelectedRationalCauchy.ratCongruentThree_mono
#print axioms Theory.PiDigits.T96SelectedRationalCauchy.pow_three_incr_congruent_zero
#print axioms Theory.PiDigits.T96SelectedRationalCauchy.evenScaledPartial_adjacent_congruent
#print axioms Theory.PiDigits.T96SelectedRationalCauchy.evenScaledPartial_cauchy
