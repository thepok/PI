import TheoryLib.PiQuantitativeBlockHitting.T62T62HuttonEligiblePrimeProduct

/-!
# T64: one-third-band prime survival for the rational Hutton shadows

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For `R = 4*K+3`, T61 used `R < 2*p` to isolate the unique odd Taylor
exponent divisible by `p`.  Since every Taylor exponent is odd, the same
isolation already holds under the larger-band hypothesis `R < 3*p`: the only
positive multiples below `3*p` are `p` and `2*p`, and the second is even.

Consequently every prime `p > 7`, `p != 17`, with `R/3 < p <= R` occurs
exactly once in the reduced denominator of the lower Hutton shadow, and the
product of all such primes divides that denominator.

This is exact finite denominator arithmetic.  It supplies no asymptotic
estimate, decimal-prefix distribution, cylinder hit, or every-word theorem
for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.HuttonOneThirdPrimeProduct

open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonEligiblePrimeProduct
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival

/-- Under `4*K+3 < 3*p`, an odd Hutton exponent other than `p` is not
divisible by `p`. -/
lemma oneThirdPrime_not_dvd_other_hutton_exponent
    (K k p j : ℕ)
    (hpLower : 4 * K + 3 < 3 * p)
    (hpdef : p = 2 * k + 1)
    (hj : j ∈ (range (huttonTermCount K)).erase k) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjlt : j < huttonTermCount K :=
    mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 3 * p := by
    unfold huttonTermCount at hjlt
    omega
  rcases hdvd with ⟨t, ht⟩
  have hpt : p * t < p * 3 := by
    rw [← ht]
    simpa [mul_comm] using hexplt
  have hpPos : 0 < p := by omega
  have htlt : t < 3 := (Nat.mul_lt_mul_left hpPos).mp hpt
  interval_cases t <;> omega

/-- Every nonsingular Hutton term has nonnegative `p`-adic valuation in the
one-third band. -/
lemma padicValRat_huttonRegularBlockRat_nonneg_oneThird
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hpLower : 4 * K + 3 < 3 * p)
    (hpdef : p = 2 * k + 1)
    (hregular : huttonRegularBlockRat K k ≠ 0) :
    0 ≤ padicValRat p (huttonRegularBlockRat K k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℚ :=
    ∑ j ∈ (range (huttonTermCount K)).erase k, huttonThreeTermRat j
  let G : ℚ :=
    ∑ j ∈ (range (huttonTermCount K)).erase k, huttonSevenTermRat j
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · apply Or.inr
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_huttonThreeTermRat_eq_zero p j hp hpgt
          (oneThirdPrime_not_dvd_other_hutton_exponent
            K k p j hpLower hpdef hj)]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · apply Or.inr
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_huttonSevenTermRat_eq_zero p j hp hpgt
          (oneThirdPrime_not_dvd_other_hutton_exponent
            K k p j hpLower hpdef hj)]
      · exact hG0
  change 0 ≤ padicValRat p (F + G)
  apply padicValRat_add_nonneg_of_each_nonneg p hp hF hG
  simpa [F, G, huttonRegularBlockRat] using hregular

/-- Every eligible one-third-band prime has valuation exactly `-1` in the
rational lower Hutton shadow. -/
theorem padicValRat_huttonLowerRat_oneThirdPrime
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp17 : p ≠ 17)
    (hpLower : 4 * K + 3 < 3 * p)
    (hpUpper : p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    padicValRat p (huttonLowerRat K) = -1 := by
  rw [huttonLowerRat_eq_regular_add_singular K k p hpdef hpUpper]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_hutton_singular_pair p k hp hpgt hp17 hpdef
  · by_cases hregular : huttonRegularBlockRat K k = 0
    · exact Or.inl hregular
    · exact Or.inr (padicValRat_huttonRegularBlockRat_nonneg_oneThird
        K k p hp hpgt hpLower hpdef hregular)

/-- Every eligible one-third-band prime divides the reduced denominator. -/
theorem oneThirdPrime_dvd_huttonLowerRat_den
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp17 : p ≠ 17)
    (hpLower : 4 * K + 3 < 3 * p)
    (hpUpper : p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    p ∣ (huttonLowerRat K).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_huttonLowerRat_oneThirdPrime
    K k p hp hpgt hp17 hpLower hpUpper hpdef]
  norm_num

/-- Every eligible one-third-band prime occurs exactly once in the reduced
denominator. -/
theorem padicValNat_huttonLowerRat_den_oneThirdPrime
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp17 : p ≠ 17)
    (hpLower : 4 * K + 3 < 3 * p)
    (hpUpper : p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    padicValNat p (huttonLowerRat K).den = 1 := by
  let q := huttonLowerRat K
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_huttonLowerRat_oneThirdPrime
      K k p hp hpgt hp17 hpLower hpUpper hpdef
  have hden : p ∣ q.den :=
    oneThirdPrime_dvd_huttonLowerRat_den
      K k p hp hpgt hp17 hpLower hpUpper hpdef
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

/-- The exact finite set of one-third-band primes. -/
def huttonOneThirdPrimeSet (K : ℕ) : Finset ℕ :=
  (range (4 * K + 4)).filter fun p =>
    p.Prime ∧ 7 < p ∧ p ≠ 17 ∧ 4 * K + 3 < 3 * p

/-- The squarefree product of the one-third-band primes. -/
def huttonOneThirdPrimeProduct (K : ℕ) : ℕ :=
  (huttonOneThirdPrimeSet K).prod id

/-- Membership exposes exactly the one-third-band valuation hypotheses. -/
theorem mem_huttonOneThirdPrimeSet_iff (K p : ℕ) :
    p ∈ huttonOneThirdPrimeSet K ↔
      p.Prime ∧ 7 < p ∧ p ≠ 17 ∧
        4 * K + 3 < 3 * p ∧ p ≤ 4 * K + 3 := by
  rw [huttonOneThirdPrimeSet, mem_filter, mem_range]
  constructor
  · rintro ⟨hpRange, hpPrime, hpgt, hp17, hpLower⟩
    exact ⟨hpPrime, hpgt, hp17, hpLower, by omega⟩
  · rintro ⟨hpPrime, hpgt, hp17, hpLower, hpUpper⟩
    exact ⟨by omega, hpPrime, hpgt, hp17, hpLower⟩

/-- Every member of the set divides the reduced Hutton denominator. -/
theorem huttonOneThirdPrime_dvd_huttonLowerRat_den
    (K p : ℕ) (hp : p ∈ huttonOneThirdPrimeSet K) :
    p ∣ (huttonLowerRat K).den := by
  rcases (mem_huttonOneThirdPrimeSet_iff K p).1 hp with
    ⟨hpPrime, hpgt, hp17, hpLower, hpUpper⟩
  have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
  let k := p / 2
  have hpdef : p = 2 * k + 1 :=
    (Nat.two_mul_div_two_add_one_of_odd hpOdd).symm
  exact oneThirdPrime_dvd_huttonLowerRat_den
    K k p hpPrime hpgt hp17 hpLower hpUpper hpdef

/-- Distinct members of the one-third-band set are coprime. -/
theorem huttonOneThirdPrimeSet_pairwise_coprime (K : ℕ) :
    (huttonOneThirdPrimeSet K : Set ℕ).Pairwise Nat.Coprime := by
  intro p hp q hq hpq
  have hpPrime := ((mem_huttonOneThirdPrimeSet_iff K p).1 hp).1
  have hqPrime := ((mem_huttonOneThirdPrimeSet_iff K q).1 hq).1
  exact (Nat.coprime_primes hpPrime hqPrime).2 hpq

/-- The joint one-third-band product divides the reduced Hutton denominator. -/
theorem huttonOneThirdPrimeProduct_dvd_huttonLowerRat_den (K : ℕ) :
    huttonOneThirdPrimeProduct K ∣ (huttonLowerRat K).den := by
  unfold huttonOneThirdPrimeProduct
  apply finset_prod_id_dvd_of_pairwise_coprime
    (huttonOneThirdPrimeSet K) (huttonLowerRat K).den
  · exact huttonOneThirdPrimeSet_pairwise_coprime K
  · exact huttonOneThirdPrime_dvd_huttonLowerRat_den K

end Theory.PiDigits.HuttonOneThirdPrimeProduct

#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.oneThirdPrime_not_dvd_other_hutton_exponent
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.padicValRat_huttonRegularBlockRat_nonneg_oneThird
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.padicValRat_huttonLowerRat_oneThirdPrime
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.oneThirdPrime_dvd_huttonLowerRat_den
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.padicValNat_huttonLowerRat_den_oneThirdPrime
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.huttonOneThirdPrimeSet
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.huttonOneThirdPrimeProduct
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.mem_huttonOneThirdPrimeSet_iff
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.huttonOneThirdPrime_dvd_huttonLowerRat_den
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.huttonOneThirdPrimeSet_pairwise_coprime
#print axioms Theory.PiDigits.HuttonOneThirdPrimeProduct.huttonOneThirdPrimeProduct_dvd_huttonLowerRat_den
