import TheoryLib.PiQuantitativeBlockHitting.T154T154DelayedBBPFivePrimary
import TheoryLib.PiQuantitativeBlockHitting.T161T161SafeLaterBBPPrimeProjection
import TheoryLib.PiQuantitativeBlockHitting.T162T162ExactBBPMinusPrimeProjection
import TheoryLib.PiQuantitativeBlockHitting.T163T163EvenBBPDyadicLift

/-!
# T165: actual arithmetic of the delayed BBP phase

At positive even sampled depth, T154's delayed numerator presentation is
already reduced: T163 supplies oddness of the actual numerator, while the
reduced sampled BBP rational supplies coprimality with its denominator.

The second part transports every actual odd-prime projection of the sampled
BBP rational through the delayed decimal scaling.  The resulting statement is
about the literal numerator over `2^k D`, not a premise-only CRT model.

These are exact arithmetic facts.  They prove no cancellation, distribution,
digit occurrence, or V1 conclusion.
-/

noncomputable section

namespace Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic

open Theory.PiDigits.T74ThreePrimaryDecimation
open Theory.PiDigits.T77SelectedPadicDefectShell
open Theory.PiDigits.T115SampledBBPCellDefectPhase
open Theory.PiDigits.T154DelayedBBPFivePrimary
open Theory.PiDigits.T159ExactBBPTopPrimeProjection
open Theory.PiDigits.T161SafeLaterBBPPrimeProjection
open Theory.PiDigits.T162ExactBBPMinusPrimeProjection
open Theory.PiDigits.T163EvenBBPDyadicLift
open Theory.PiDigits.MachinPrimeSurvival

/-- At a positive even sampled depth, the literal delayed numerator is
coprime to the complete displayed denominator `2^k D`. -/
theorem delayedBBPNumerator_coprime_two_pow_mul_den_even
    (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (heven : Even (n + k)) :
    Nat.Coprime (delayedBBPNumerator k n).natAbs
      (2 ^ k * (scaledBBPRat (n + k)).den) := by
  let q : ℚ := scaledBBPRat (n + k)
  let U : ℤ := delayedBBPNumerator k n
  have htpos : 0 < n + k := by omega
  have hprimary := scaledBBPRat_even_two_primary (n + k) heven htpos
  have hnum : q.num = (5 : ℤ) ^ k * U := by
    exact scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator k n hm hlog
  have hUdiv : U.natAbs ∣ q.num.natAbs := by
    rw [hnum, Int.natAbs_mul]
    exact dvd_mul_left _ _
  have hUD : Nat.Coprime U.natAbs q.den :=
    Nat.Coprime.of_dvd_left hUdiv q.reduced
  have hUtwo : Nat.Coprime U.natAbs 2 :=
    Nat.Coprime.of_dvd_left hUdiv (Nat.coprime_two_right.mpr hprimary.2)
  exact Nat.Coprime.mul_right (hUtwo.pow_right k) hUD

/-- Exact no-alias statement for the reduced delayed phase: two distinct
frequencies whose difference is smaller than `2^k D` remain distinct modulo
that denominator after multiplication by the actual delayed numerator. -/
theorem delayedBBPNumerator_frequency_no_alias_even
    (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (heven : Even (n + k)) (h₁ h₂ : ℤ) (hne : h₁ ≠ h₂)
    (hsmall : (h₁ - h₂).natAbs <
      2 ^ k * (scaledBBPRat (n + k)).den) :
    ¬ 2 ^ k * (scaledBBPRat (n + k)).den ∣
      (h₁ - h₂).natAbs * (delayedBBPNumerator k n).natAbs := by
  intro hdvd
  have hcop :=
    (delayedBBPNumerator_coprime_two_pow_mul_den_even k n hm hlog heven).symm
  have hdiv : 2 ^ k * (scaledBBPRat (n + k)).den ∣ (h₁ - h₂).natAbs :=
    hcop.dvd_of_dvd_mul_right hdvd
  have hdiff : 0 < (h₁ - h₂).natAbs := by
    rw [Int.natAbs_pos]
    omega
  exact (not_le_of_gt hsmall) (Nat.le_of_dvd hdiff hdiv)

private lemma four_mul_ten_pow_lt_delayed_den_even
    (k n : ℕ) (hm : 2 ≤ n + k) (heven : Even (n + k)) :
    4 * 10 ^ k < 2 ^ k * (scaledBBPRat (n + k)).den := by
  have hprimary := scaledBBPRat_even_two_primary (n + k) heven (by omega)
  have hden0 : (scaledBBPRat (n + k)).den ≠ 0 := Rat.den_nz _
  have hdvd : 2 ^ (27 * (n + k)) ∣ (scaledBBPRat (n + k)).den := by
    rw [padicValNat_dvd_iff_le hden0, hprimary.1]
  have hdenLower : 2 ^ (27 * (n + k)) ≤ (scaledBBPRat (n + k)).den :=
    Nat.le_of_dvd (by positivity) hdvd
  have hfive : 5 ^ k ≤ 2 ^ (3 * k) := by
    calc
      5 ^ k ≤ 8 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = 2 ^ (3 * k) := by
        rw [show 8 = 2 ^ 3 by norm_num, ← pow_mul]
  have hexp : 3 * k + 2 < 27 * (n + k) := by omega
  have hpow : 4 * 5 ^ k < 2 ^ (27 * (n + k)) := by
    calc
      4 * 5 ^ k ≤ 4 * 2 ^ (3 * k) := Nat.mul_le_mul_left 4 hfive
      _ = 2 ^ (3 * k + 2) := by
        rw [pow_add]
        norm_num
        ring
      _ < 2 ^ (27 * (n + k)) := Nat.pow_lt_pow_right (by norm_num) hexp
  rw [show 10 ^ k = 2 ^ k * 5 ^ k by
    rw [show 10 = 2 * 5 by norm_num, mul_pow]]
  calc
    4 * (2 ^ k * 5 ^ k) = 2 ^ k * (4 * 5 ^ k) := by ring
    _ < 2 ^ k * 2 ^ (27 * (n + k)) :=
      Nat.mul_lt_mul_of_pos_left hpow (by positivity)
    _ ≤ 2 ^ k * (scaledBBPRat (n + k)).den :=
      Nat.mul_le_mul_left _ hdenLower

/-- Distinct frequencies in the complete T155 natural window do not alias
modulo the actual reduced delayed numerator/denominator pair at positive even
depth. -/
theorem delayedBBPNumerator_naturalWindow_no_alias_even
    (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (heven : Even (n + k)) (h₁ h₂ : ℤ) (hne : h₁ ≠ h₂)
    (hh₁ : h₁.natAbs < 2 * 10 ^ k) (hh₂ : h₂.natAbs < 2 * 10 ^ k) :
    ¬ 2 ^ k * (scaledBBPRat (n + k)).den ∣
      (h₁ - h₂).natAbs * (delayedBBPNumerator k n).natAbs := by
  apply delayedBBPNumerator_frequency_no_alias_even
    k n hm hlog heven h₁ h₂ hne
  calc
    (h₁ - h₂).natAbs ≤ h₁.natAbs + h₂.natAbs := Int.natAbs_sub_le _ _
    _ < 4 * 10 ^ k := by omega
    _ < 2 ^ k * (scaledBBPRat (n + k)).den :=
      four_mul_ten_pow_lt_delayed_den_even k n hm heven

/-- Dividing both sides of a `p`-local congruence by a power of ten preserves
the congruence for primes above five. -/
lemma PrimeCongruent.div_ten_pow
    {k p : ℕ} (hp : p.Prime) (hpgt : 5 < p) {x y : ℚ}
    (hxy : PrimeCongruent p x y) :
    PrimeCongruent p (x / (10 : ℚ) ^ k) (y / (10 : ℚ) ^ k) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold PrimeCongruent at hxy ⊢
  rcases hxy with rfl | hval
  · exact Or.inl rfl
  · right
    have hdiff0 : x - y ≠ 0 := by
      intro hz
      simp [hz] at hval
    have h10 : (10 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have h10val : padicValRat p (10 : ℚ) = 0 :=
      padicValRat_natCast_eq_zero_of_not_dvd
        (prime_gt_five_not_dvd_ten p hp hpgt)
    rw [show x / (10 : ℚ) ^ k - y / (10 : ℚ) ^ k =
        (x - y) / (10 : ℚ) ^ k by ring,
      padicValRat.div hdiff0 h10, padicValRat.pow (by norm_num), h10val]
    norm_num
    exact hval

/-- An actual projection of `scaledBBPRat (n+k)` transports exactly to the
literal delayed numerator over `2^k D`; its residue loses the same factor
`10^k`, becoming `c * 10^n`. -/
theorem delayedBBPNumerator_primeProjection
    (k n p : ℕ) (c : ℚ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hp : p.Prime) (hpgt : 5 < p)
    (hproj : PrimeCongruent p
      ((p : ℚ) * scaledBBPRat (n + k))
      (c * (10 : ℚ) ^ (n + k))) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ)))
      (c * (10 : ℚ) ^ n) := by
  have hdiv := PrimeCongruent.div_ten_pow hp hpgt (k := k) hproj
  have hdelayed := delayed_bbpPartial_eq_num_div_two_pow_den k n hm hlog
  have hscaled :
      scaledBBPRat (n + k) / (10 : ℚ) ^ k =
        (10 : ℚ) ^ n * bbpPartial (7 * (n + k)) := by
    unfold scaledBBPRat
    rw [pow_add]
    field_simp
  convert hdiv using 1
  · rw [← hdelayed, ← hscaled]
    ring
  · rw [pow_add]
    field_simp

/-- T159's first-family top-band projection on the literal delayed numerator
coordinate. -/
theorem delayedBBPNumerator_topPrimeProjection_one
    (k n i p : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * (n + k) + 6 < 2 * p)
    (hpUpper : p ≤ 56 * (n + k) + 1) (hpdef : p = 8 * i + 1) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ)))
      (4 * (10 : ℚ) ^ n) := by
  exact delayedBBPNumerator_primeProjection k n p 4 hm hlog hp hpgt
    (scaledBBPRat_topPrimeProjection_one
      (n + k) i p hp hpgt hband hpUpper hpdef)

/-- T159's third-family top-band projection on the literal delayed numerator
coordinate. -/
theorem delayedBBPNumerator_topPrimeProjection_three
    (k n i p : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * (n + k) + 6 < 2 * p)
    (hpUpper : p ≤ 56 * (n + k) + 5) (hpdef : p = 8 * i + 5) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ)))
      (4 * (10 : ℚ) ^ n) := by
  exact delayedBBPNumerator_primeProjection k n p 4 hm hlog hp hpgt
    (scaledBBPRat_topPrimeProjection_three
      (n + k) i p hp hpgt hband hpUpper hpdef)

/-- T161's first-family safe-block projection, now stated for the literal
delayed numerator phase coordinate. -/
theorem delayedBBPNumerator_safeLaterProjection_one
    (m t k n p : ℕ) (htdef : t = n + k)
    (hdepth : 2 ≤ t) (hlog : Nat.log 5 (56 * t + 5) ≤ n)
    (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m - 1)
    (hp : p.Prime) (hpdef : p = 56 * m + 1) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat t).den : ℕ) : ℚ)))
      (4 * (10 : ℚ) ^ n) := by
  subst t
  exact delayedBBPNumerator_primeProjection k n p 4 hdepth hlog hp (by omega)
    (scaledBBPRat_safeLaterProjection_one m (n + k) p hm hmt ht hp hpdef)

/-- T161's third-family safe-block projection, now stated for the literal
delayed numerator phase coordinate. -/
theorem delayedBBPNumerator_safeLaterProjection_three
    (m t k n p : ℕ) (htdef : t = n + k)
    (hdepth : 2 ≤ t) (hlog : Nat.log 5 (56 * t + 5) ≤ n)
    (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m)
    (hp : p.Prime) (hpdef : p = 56 * m + 5) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat t).den : ℕ) : ℚ)))
      (4 * (10 : ℚ) ^ n) := by
  subst t
  exact delayedBBPNumerator_primeProjection k n p 4 hdepth hlog hp (by omega)
    (scaledBBPRat_safeLaterProjection_three m (n + k) p hm hmt ht hp hpdef)

/-- T162's quiet `p = 8*a+3` minus-band projection on the literal delayed
numerator coordinate. -/
theorem delayedBBPNumerator_minusThreeProjection_of_quiet
    (k n a p : ℕ) (hm : 2 ≤ n + k) (hp : p.Prime)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hlow : 14 * (n + k) + 1 < p) (hupper : p ≤ 28 * (n + k) + 3)
    (hquiet : 56 * (n + k) + 1 < 3 * p) (hpdef : p = 8 * a + 3) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ)))
      ((-2 : ℚ) * (10 : ℚ) ^ n) := by
  exact delayedBBPNumerator_primeProjection k n p (-2) hm hlog hp (by omega)
    (scaledBBPRat_minusThreeProjection_of_quiet
      (n + k) a p (by omega) hp hlow hupper hquiet hpdef)

/-- T162's active `p = 8*a+3` minus-band projection on the literal delayed
numerator coordinate. -/
theorem delayedBBPNumerator_minusThreeProjection_of_secondary
    (k n a p : ℕ) (hm : 2 ≤ n + k) (hp : p.Prime)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hlow : 14 * (n + k) + 1 < p) (hupper : p ≤ 28 * (n + k) + 3)
    (hactive : 3 * p ≤ 56 * (n + k) + 1) (hpdef : p = 8 * a + 3) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ)))
      ((-(8 : ℚ) / 3) * (10 : ℚ) ^ n) := by
  exact delayedBBPNumerator_primeProjection k n p (-(8 : ℚ) / 3)
    hm hlog hp (by omega)
    (scaledBBPRat_minusThreeProjection_of_secondary
      (n + k) a p (by omega) hp hlow hupper hactive hpdef)

/-- T162's quiet `p = 8*a+7` minus-band projection on the literal delayed
numerator coordinate. -/
theorem delayedBBPNumerator_minusSevenProjection_of_quiet
    (k n a p : ℕ) (hm : 2 ≤ n + k) (hp : p.Prime)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hlow : 14 * (n + k) + 1 < p) (hupper : p ≤ 28 * (n + k) + 3)
    (hquiet : 56 * (n + k) + 5 < 3 * p) (hpdef : p = 8 * a + 7) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ)))
      ((-2 : ℚ) * (10 : ℚ) ^ n) := by
  exact delayedBBPNumerator_primeProjection k n p (-2) hm hlog hp (by omega)
    (scaledBBPRat_minusSevenProjection_of_quiet
      (n + k) a p (by omega) hp hlow hupper hquiet hpdef)

/-- T162's active `p = 8*a+7` minus-band projection on the literal delayed
numerator coordinate. -/
theorem delayedBBPNumerator_minusSevenProjection_of_secondary
    (k n a p : ℕ) (hm : 2 ≤ n + k) (hp : p.Prime)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n)
    (hlow : 14 * (n + k) + 1 < p) (hupper : p ≤ 28 * (n + k) + 3)
    (hactive : 3 * p ≤ 56 * (n + k) + 5) (hpdef : p = 8 * a + 7) :
    PrimeCongruent p
      ((p : ℚ) *
        ((delayedBBPNumerator k n : ℚ) /
          ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ)))
      ((-(8 : ℚ) / 3) * (10 : ℚ) ^ n) := by
  exact delayedBBPNumerator_primeProjection k n p (-(8 : ℚ) / 3)
    hm hlog hp (by omega)
    (scaledBBPRat_minusSevenProjection_of_secondary
      (n + k) a p (by omega) hp hlow hupper hactive hpdef)

end Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic

#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_coprime_two_pow_mul_den_even
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_frequency_no_alias_even
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_naturalWindow_no_alias_even
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_primeProjection
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_topPrimeProjection_one
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_topPrimeProjection_three
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_safeLaterProjection_one
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_safeLaterProjection_three
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_minusThreeProjection_of_quiet
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_minusThreeProjection_of_secondary
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_minusSevenProjection_of_quiet
#print axioms Theory.PiDigits.T165DelayedBBPActualPhaseArithmetic.delayedBBPNumerator_minusSevenProjection_of_secondary
