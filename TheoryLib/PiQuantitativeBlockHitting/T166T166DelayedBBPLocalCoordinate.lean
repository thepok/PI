import TheoryLib.PiQuantitativeBlockHitting.T165T165DelayedBBPActualPhaseArithmetic

/-!
# T166: delayed BBP local-coordinate transport

An exact prime projection of a reduced rational with `p`-adic valuation `-1`
can be transported through the five-primary delayed-numerator factorization.
The result identifies the prime-local coordinate of the pole-removed delayed
numerator.  It does not control the complementary CRT coordinate or prove
Fourier cancellation.
-/

noncomputable section

namespace Theory.PiDigits.T166DelayedBBPLocalCoordinate

open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.T115SampledBBPCellDefectPhase
open Theory.PiDigits.T154DelayedBBPFivePrimary
open Theory.PiDigits.T159ExactBBPTopPrimeProjection
open Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic

/-- Exact multiplicity-one denominator factor forced by valuation `-1` in a
reduced rational. -/
theorem exists_den_eq_prime_mul_of_padicValRat_eq_neg_one
    (p : ℕ) (R : ℚ) (hp : p.Prime)
    (hval : padicValRat p R = -1) :
    ∃ E : ℕ, R.den = p * E ∧ ¬ p ∣ E := by
  have hden : p ∣ R.den := by
    apply dvd_rat_den_of_padicValRat_neg
    omega
  have hcop : Nat.Coprime p R.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden R.reduced).symm
  have hnum : ¬ p ∣ R.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p R.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  have hvden : padicValNat p R.den = 1 := by
    rw [padicValRat_def, hvnum] at hval
    omega
  refine ⟨R.den / p, (Nat.mul_div_cancel' hden).symm, ?_⟩
  intro hdiv
  have hden0 : R.den ≠ 0 := R.den_ne_zero
  have hp2dvd : p ^ 2 ∣ R.den := by
    rw [show R.den = p * (R.den / p) by exact (Nat.mul_div_cancel' hden).symm,
      pow_two]
    exact Nat.mul_dvd_mul_left p hdiv
  have hge : 2 ≤ padicValNat p R.den :=
    (Nat.pow_dvd_iff_le_padicValNat (p := p) (k := 2) hp.ne_one hden0).1 hp2dvd
  omega

/-- Generic delayed local-coordinate transport.  The rational `R=P/D` is
already reduced by its `Rat` representation.  Removing `5^k` from its actual
numerator and the unique factor `p` from its denominator transports the
projection from depth `n+k` to decimal index `n`. -/
theorem exists_delayed_local_coordinate_of_projection
    (p k n : ℕ) (R c : ℚ) (U : ℤ)
    (hp : p.Prime) (hpgt : 5 < p)
    (hval : padicValRat p R = -1)
    (hnum : R.num = (5 : ℤ) ^ k * U)
    (hproj : PrimeCongruent p ((p : ℚ) * R)
      (c * (10 : ℚ) ^ (n + k))) :
    ∃ E : ℕ,
      R.den = p * E ∧ ¬ p ∣ E ∧
        PrimeCongruent p
          ((U : ℚ) / ((2 ^ k * E : ℕ) : ℚ))
          (c * (10 : ℚ) ^ n) := by
  obtain ⟨E, hden, hpE⟩ :=
    exists_den_eq_prime_mul_of_padicValRat_eq_neg_one p R hp hval
  refine ⟨E, hden, hpE, ?_⟩
  have hscaled :=
    Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.PrimeCongruent.div_ten_pow
      (k := k) hp hpgt hproj
  convert hscaled using 1
  · rw [← Rat.num_div_den R, hnum, hden]
    push_cast
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
    field_simp
  · rw [pow_add]
    field_simp

/-- The generic transport specialized to the actual sampled BBP rational and
the actual delayed numerator from T154. -/
theorem exists_scaledBBPRat_delayed_local_coordinate
    (p k n : ℕ) (c : ℚ)
    (hp : p.Prime) (hpgt : 5 < p)
    (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hval : padicValRat p (scaledBBPRat (n + k)) = -1)
    (hproj : PrimeCongruent p
      ((p : ℚ) * scaledBBPRat (n + k))
      (c * (10 : ℚ) ^ (n + k))) :
    ∃ E : ℕ,
      (scaledBBPRat (n + k)).den = p * E ∧ ¬ p ∣ E ∧
        PrimeCongruent p
          ((delayedBBPNumerator k n : ℚ) / ((2 ^ k * E : ℕ) : ℚ))
          (c * (10 : ℚ) ^ n) := by
  exact exists_delayed_local_coordinate_of_projection
    p k n (scaledBBPRat (n + k)) c (delayedBBPNumerator k n)
      hp hpgt hval
      (scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator k n hm hlog)
      hproj

/-- Transport of the top- and safe-block residue `4`.  Any public T159 or
T161 projection theorem can be supplied directly as `hproj`. -/
theorem exists_scaledBBPRat_delayed_local_coordinate_four
    (p k n : ℕ)
    (hp : p.Prime) (hpgt : 5 < p)
    (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hproj : PrimeCongruent p
      ((p : ℚ) * scaledBBPRat (n + k))
      (4 * (10 : ℚ) ^ (n + k))) :
    ∃ E : ℕ,
      (scaledBBPRat (n + k)).den = p * E ∧ ¬ p ∣ E ∧
        PrimeCongruent p
          ((delayedBBPNumerator k n : ℚ) / ((2 ^ k * E : ℕ) : ℚ))
          (4 * (10 : ℚ) ^ n) := by
  have hval := scaledBBPRat_val_eq_neg_one_of_projection
    (n + k) p hp hpgt hproj
  exact exists_scaledBBPRat_delayed_local_coordinate
    p k n 4 hp hpgt hm hlog hval hproj

private lemma minus_two_ten_pow_unit
    (p t : ℕ) (hp : p.Prime) (hpgt : 5 < p) :
    padicValRat p ((-2 : ℚ) * (10 : ℚ) ^ t) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_two p hpgt)
  have h10 : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_ten p hp hpgt)
  rw [padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.neg, h2, padicValRat.pow (by norm_num), h10]
  norm_num

private lemma minus_eight_thirds_ten_pow_unit
    (p t : ℕ) (hp : p.Prime) (hpgt : 5 < p) :
    padicValRat p ((-(8 : ℚ) / 3) * (10 : ℚ) ^ t) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h8not : ¬ p ∣ 8 := by
    intro h
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 3) (by simpa using h)
    exact prime_gt_five_not_dvd_two p hpgt hp2
  have h3not : ¬ p ∣ 3 := by
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
    omega
  have h8 : padicValRat p (8 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd h8not
  have h3 : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd h3not
  have h10 : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_ten p hp hpgt)
  rw [padicValRat.mul (div_ne_zero (by norm_num) (by norm_num))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (neg_ne_zero.mpr (by norm_num)) (by norm_num),
    padicValRat.neg, h8, h3, padicValRat.pow (by norm_num), h10]
  norm_num

/-- Transport of the quiet lower-band residue `-2`.  A public T162 quiet
projection theorem can be supplied directly as `hproj`. -/
theorem exists_scaledBBPRat_delayed_local_coordinate_minus_two
    (p k n : ℕ)
    (hp : p.Prime) (hpgt : 5 < p)
    (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hproj : PrimeCongruent p
      ((p : ℚ) * scaledBBPRat (n + k))
      ((-2 : ℚ) * (10 : ℚ) ^ (n + k))) :
    ∃ E : ℕ,
      (scaledBBPRat (n + k)).den = p * E ∧ ¬ p ∣ E ∧
        PrimeCongruent p
          ((delayedBBPNumerator k n : ℚ) / ((2 ^ k * E : ℕ) : ℚ))
          ((-2 : ℚ) * (10 : ℚ) ^ n) := by
  have hval := scaledBBPRat_val_eq_neg_one_of_projection_of_unit
    (n + k) p hp (by positivity)
      (minus_two_ten_pow_unit p (n + k) hp hpgt) hproj
  exact exists_scaledBBPRat_delayed_local_coordinate
    p k n (-2) hp hpgt hm hlog hval hproj

/-- Transport of the active lower-band residue `-8/3`.  A public T162
secondary-pole projection theorem can be supplied directly as `hproj`. -/
theorem exists_scaledBBPRat_delayed_local_coordinate_minus_eight_thirds
    (p k n : ℕ)
    (hp : p.Prime) (hpgt : 5 < p)
    (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hproj : PrimeCongruent p
      ((p : ℚ) * scaledBBPRat (n + k))
      ((-(8 : ℚ) / 3) * (10 : ℚ) ^ (n + k))) :
    ∃ E : ℕ,
      (scaledBBPRat (n + k)).den = p * E ∧ ¬ p ∣ E ∧
        PrimeCongruent p
          ((delayedBBPNumerator k n : ℚ) / ((2 ^ k * E : ℕ) : ℚ))
          ((-(8 : ℚ) / 3) * (10 : ℚ) ^ n) := by
  have hval := scaledBBPRat_val_eq_neg_one_of_projection_of_unit
    (n + k) p hp (by positivity)
      (minus_eight_thirds_ten_pow_unit p (n + k) hp hpgt) hproj
  exact exists_scaledBBPRat_delayed_local_coordinate
    p k n (-(8 : ℚ) / 3) hp hpgt hm hlog hval hproj

end Theory.PiDigits.T166DelayedBBPLocalCoordinate

#print axioms Theory.PiDigits.T166DelayedBBPLocalCoordinate.exists_den_eq_prime_mul_of_padicValRat_eq_neg_one
#print axioms Theory.PiDigits.T166DelayedBBPLocalCoordinate.exists_delayed_local_coordinate_of_projection
#print axioms Theory.PiDigits.T166DelayedBBPLocalCoordinate.exists_scaledBBPRat_delayed_local_coordinate
#print axioms Theory.PiDigits.T166DelayedBBPLocalCoordinate.exists_scaledBBPRat_delayed_local_coordinate_four
#print axioms Theory.PiDigits.T166DelayedBBPLocalCoordinate.exists_scaledBBPRat_delayed_local_coordinate_minus_two
#print axioms Theory.PiDigits.T166DelayedBBPLocalCoordinate.exists_scaledBBPRat_delayed_local_coordinate_minus_eight_thirds
