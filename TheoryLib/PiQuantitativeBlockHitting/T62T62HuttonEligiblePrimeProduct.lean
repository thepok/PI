import TheoryLib.PiQuantitativeBlockHitting.T61T61HuttonUpperHalfPrimeSurvival
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# T62: the joint eligible-prime divisor of a Hutton denominator

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For `R = 4*K+3`, collect the primes `p` satisfying
`7 < p`, `p ≠ 17`, and `R < 2*p ≤ 2*R`.  T61 proves separately that
each such prime occurs exactly once in the reduced denominator of the lower
Hutton shadow.  Since distinct primes are pairwise coprime, their finite
product divides that denominator.

This is exact finite denominator arithmetic.  It does not estimate the size
of the product and supplies no prime-number-theorem, prefix-discrepancy,
decimal-cylinder, distribution, or every-word conclusion for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.HuttonEligiblePrimeProduct

open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonUpperHalfPrimeSurvival

/-- The eligible upper-half primes for the lower Hutton shadow at index `K`. -/
def huttonEligiblePrimeSet (K : ℕ) : Finset ℕ :=
  (range (4 * K + 4)).filter fun p =>
    p.Prime ∧ 7 < p ∧ p ≠ 17 ∧ 4 * K + 3 < 2 * p

/-- The squarefree product of all eligible upper-half primes. -/
def huttonEligiblePrimeProduct (K : ℕ) : ℕ :=
  (huttonEligiblePrimeSet K).prod id

/-- Membership unfolds to exactly the hypotheses needed by T61, including
the upper endpoint `p ≤ 4*K+3` encoded by the ambient range. -/
theorem mem_huttonEligiblePrimeSet_iff (K p : ℕ) :
    p ∈ huttonEligiblePrimeSet K ↔
      p.Prime ∧ 7 < p ∧ p ≠ 17 ∧
        4 * K + 3 < 2 * p ∧ p ≤ 4 * K + 3 := by
  rw [huttonEligiblePrimeSet, mem_filter, mem_range]
  constructor
  · rintro ⟨hpRange, hpPrime, hpgt, hp17, hpLower⟩
    exact ⟨hpPrime, hpgt, hp17, hpLower, by omega⟩
  · rintro ⟨hpPrime, hpgt, hp17, hpLower, hpUpper⟩
    exact ⟨by omega, hpPrime, hpgt, hp17, hpLower⟩

/-- Every eligible prime has the unique odd-index form required by the
singular-pair theorem in T61. -/
theorem huttonEligiblePrime_exists_oddIndex
    (K p : ℕ) (hp : p ∈ huttonEligiblePrimeSet K) :
    ∃ k : ℕ, p = 2 * k + 1 := by
  have hpData := (mem_huttonEligiblePrimeSet_iff K p).1 hp
  have hpOdd : Odd p := hpData.1.odd_of_ne_two (by omega)
  exact ⟨p / 2, (Nat.two_mul_div_two_add_one_of_odd hpOdd).symm⟩

/-- Product-facing form of T61's individual divisibility theorem. -/
theorem huttonEligiblePrime_dvd_huttonLowerRat_den
    (K p : ℕ) (hp : p ∈ huttonEligiblePrimeSet K) :
    p ∣ (huttonLowerRat K).den := by
  rcases (mem_huttonEligiblePrimeSet_iff K p).1 hp with
    ⟨hpPrime, hpgt, hp17, hpLower, hpUpper⟩
  rcases huttonEligiblePrime_exists_oddIndex K p hp with ⟨k, hpdef⟩
  exact upperHalfPrime_dvd_huttonLowerRat_den
    K k p hpPrime hpgt hp17 hpLower hpUpper hpdef

/-- Product-facing form of T61's exact multiplicity-one theorem. -/
theorem padicValNat_huttonLowerRat_den_huttonEligiblePrime
    (K p : ℕ) (hp : p ∈ huttonEligiblePrimeSet K) :
    padicValNat p (huttonLowerRat K).den = 1 := by
  rcases (mem_huttonEligiblePrimeSet_iff K p).1 hp with
    ⟨hpPrime, hpgt, hp17, hpLower, hpUpper⟩
  rcases huttonEligiblePrime_exists_oddIndex K p hp with ⟨k, hpdef⟩
  exact padicValNat_huttonLowerRat_den_upperHalfPrime
    K k p hpPrime hpgt hp17 hpLower hpUpper hpdef

/-- Distinct members of the eligible-prime set are coprime. -/
theorem huttonEligiblePrimeSet_pairwise_coprime (K : ℕ) :
    (huttonEligiblePrimeSet K : Set ℕ).Pairwise Nat.Coprime := by
  intro p hp q hq hpq
  have hpPrime := ((mem_huttonEligiblePrimeSet_iff K p).1 hp).1
  have hqPrime := ((mem_huttonEligiblePrimeSet_iff K q).1 hq).1
  exact (Nat.coprime_primes hpPrime hqPrime).2 hpq

/-- A finite family of pairwise-coprime natural numbers that all divide `n`
has product dividing `n`. -/
theorem finset_prod_id_dvd_of_pairwise_coprime
    (S : Finset ℕ) (n : ℕ)
    (hpair : (S : Set ℕ).Pairwise Nat.Coprime)
    (hdiv : ∀ p ∈ S, p ∣ n) :
    S.prod id ∣ n := by
  classical
  revert hpair hdiv
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
      intro hpair hdiv
      rw [prod_insert hps]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply hpair (by simp) (by simp [hq])
        intro hpq
        have hpq' : p = q := by simpa using hpq
        subst q
        exact hps hq
      · exact hdiv p (by simp)
      · apply ih
        · exact hpair.mono (by simp)
        · intro q hq
          exact hdiv q (by simp [hq])

/-- Joint consequence: the product of all eligible upper-half primes divides
the reduced denominator of the lower Hutton shadow. -/
theorem huttonEligiblePrimeProduct_dvd_huttonLowerRat_den (K : ℕ) :
    huttonEligiblePrimeProduct K ∣ (huttonLowerRat K).den := by
  unfold huttonEligiblePrimeProduct
  apply finset_prod_id_dvd_of_pairwise_coprime
    (huttonEligiblePrimeSet K) (huttonLowerRat K).den
  · exact huttonEligiblePrimeSet_pairwise_coprime K
  · exact huttonEligiblePrime_dvd_huttonLowerRat_den K

end Theory.PiDigits.HuttonEligiblePrimeProduct

#print axioms Theory.PiDigits.HuttonEligiblePrimeProduct.huttonEligiblePrimeSet
#print axioms Theory.PiDigits.HuttonEligiblePrimeProduct.huttonEligiblePrimeProduct
#print axioms Theory.PiDigits.HuttonEligiblePrimeProduct.mem_huttonEligiblePrimeSet_iff
#print axioms Theory.PiDigits.HuttonEligiblePrimeProduct.huttonEligiblePrime_exists_oddIndex
#print axioms
  Theory.PiDigits.HuttonEligiblePrimeProduct.huttonEligiblePrime_dvd_huttonLowerRat_den
#print axioms
  Theory.PiDigits.HuttonEligiblePrimeProduct.padicValNat_huttonLowerRat_den_huttonEligiblePrime
#print axioms
  Theory.PiDigits.HuttonEligiblePrimeProduct.huttonEligiblePrimeSet_pairwise_coprime
#print axioms
  Theory.PiDigits.HuttonEligiblePrimeProduct.finset_prod_id_dvd_of_pairwise_coprime
#print axioms
  Theory.PiDigits.HuttonEligiblePrimeProduct.huttonEligiblePrimeProduct_dvd_huttonLowerRat_den
