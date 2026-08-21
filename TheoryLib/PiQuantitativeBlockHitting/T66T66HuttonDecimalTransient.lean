import TheoryLib.PiQuantitativeBlockHitting.T65T65HuttonOneFifthPrimeProduct
import TheoryLib.PiQuantitativeBlockHitting.T63T63HuttonFiveAdicTransient
import TheoryLib.PiQuantitativeBlockHitting.T44T44MachinTotalTwoAdicForcing

/-!
# T66: exact base-ten denominator transient of the Hutton lower shadow

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T63 proves that, when `5^e <= 4*K+3 < 5^(e+1)`, the reduced denominator
of `huttonLowerRat K` contains exactly `5^e`.  This module closes the other
base-ten primary component: every combined Hutton pair has two-adic
valuation two, so their nonzero finite sum has nonnegative (indeed at least
two) two-adic valuation and therefore has odd reduced denominator.

Consequently the maximum of the two- and five-adic denominator exponents is
exactly `e`.  This is denominator/transient arithmetic only.  It proves no
decimal-cylinder hit, distribution statement, or every-word theorem for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.HuttonDecimalTransient

open Theory.PiDigits.MachinTwoAdicForcing
open Theory.PiDigits.MachinTotalTwoAdicForcing
open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonFiveAdicTransient

/-- The integer numerator factor in a combined Hutton pair is odd. -/
lemma huttonCancellationFactor_odd (p : ℕ) :
    Odd (huttonCancellationFactor p) := by
  unfold huttonCancellationFactor
  exact (even_two_mul (7 ^ p)).add_odd ((by norm_num : Odd 3).pow)

/-- Every combined Hutton pair has exact two-adic valuation two. -/
theorem padicValRat_two_huttonPairRat (k : ℕ) :
    padicValRat 2 (huttonPairRat k) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [huttonPairRat_eq_fraction]
  have hrq : ((2 * k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have h3q : (3 : ℚ) ≠ 0 := by norm_num
  have h7q : (7 : ℚ) ≠ 0 := by norm_num
  have hfactorNat : huttonCancellationFactor (2 * k + 1) ≠ 0 := by
    exact nat_ne_zero_of_odd
      (huttonCancellationFactor_odd (2 * k + 1))
  have hfactorQ :
      (huttonCancellationFactor (2 * k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast hfactorNat
  have hnum0 :
      4 * (-1 : ℚ) ^ k *
        (huttonCancellationFactor (2 * k + 1) : ℚ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hfactorQ
  have hden0 :
      ((2 * k + 1 : ℕ) : ℚ) *
          3 ^ (2 * k + 1) * 7 ^ (2 * k + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hrq (pow_ne_zero _ h3q))
      (pow_ne_zero _ h7q)
  have hvalNegOne : padicValRat 2 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat 2
          (huttonCancellationFactor (2 * k + 1) : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd
      (huttonCancellationFactor_odd (2 * k + 1))
  have hvalr :
      padicValRat 2 (((2 * k + 1 : ℕ) : ℚ)) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd ⟨k, by omega⟩
  have hval3 : padicValRat 2 (3 : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd (by norm_num)
  have hval7 : padicValRat 2 (7 : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hfactorQ,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.pow (by norm_num), padicValRat_two_four, hvalNegOne,
    hvalFactor,
    padicValRat.mul (mul_ne_zero hrq (pow_ne_zero _ h3q))
      (pow_ne_zero _ h7q),
    padicValRat.mul hrq (pow_ne_zero _ h3q), hvalr,
    padicValRat.pow h3q, hval3, padicValRat.pow h7q, hval7]
  norm_num

/-- A finite sum of rationals above a common two-adic threshold is either
zero or remains above that threshold. -/
lemma padicValRat_two_sum_lower
    {S : Finset ℕ} (f : ℕ → ℚ) (c : ℤ)
    (hf : ∀ x ∈ S, c ≤ padicValRat 2 (f x)) :
    (∑ x ∈ S, f x) = 0 ∨
      c ≤ padicValRat 2 (∑ x ∈ S, f x) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hxs ih =>
      rw [sum_insert hxs]
      have hxval := hf x (mem_insert_self x S)
      have hsprop := ih (fun y hy => hf y (mem_insert_of_mem hy))
      by_cases hx0 : f x = 0
      · simpa [hx0] using hsprop
      by_cases hs0 : (∑ y ∈ S, f y) = 0
      · simp [hs0, hx0, hxval]
      rcases hsprop with hsprop | hsval
      · exact False.elim (hs0 hsprop)
      by_cases hsum0 : f x + ∑ y ∈ S, f y = 0
      · exact Or.inl hsum0
      · refine Or.inr (le_trans (le_min hxval hsval) ?_)
        exact padicValRat.min_le_padicValRat_add hsum0

/-- The complete nonzero Hutton lower shadow retains at least two factors of
two in its reduced numerator. -/
theorem two_le_padicValRat_two_huttonLowerRat (K : ℕ) :
    (2 : ℤ) ≤ padicValRat 2 (huttonLowerRat K) := by
  rw [huttonLowerRat_eq_pair_sum]
  have hsum0 :
      ∑ j ∈ range (huttonTermCount K), huttonPairRat j ≠ 0 := by
    rw [← huttonLowerRat_eq_pair_sum]
    exact ne_of_gt (huttonLowerRat_pos K)
  rcases padicValRat_two_sum_lower huttonPairRat 2
      (fun j _ => by rw [padicValRat_two_huttonPairRat]) with hzero | hge
  · exact False.elim (hsum0 hzero)
  · exact hge

/-- Every reduced Hutton lower denominator is odd. -/
theorem huttonLowerRat_den_odd (K : ℕ) :
    Odd (huttonLowerRat K).den := by
  apply odd_den_of_pos_padicValRat_two
  have hge := two_le_padicValRat_two_huttonLowerRat K
  omega

/-- The reduced Hutton lower denominator has no factor two. -/
theorem padicValNat_two_huttonLowerRat_den (K : ℕ) :
    padicValNat 2 (huttonLowerRat K).den = 0 := by
  exact padicValNat.eq_zero_of_not_dvd
    (huttonLowerRat_den_odd K).not_two_dvd_nat

/-- Under T63's exact five-adic range, the maximum base-ten denominator
exponent is exactly `e`. -/
theorem huttonLowerRat_baseTen_denominator_exponent
    (K e : ℕ)
    (hlow : 5 ^ e ≤ 4 * K + 3)
    (hhigh : 4 * K + 3 < 5 ^ (e + 1)) :
    max (padicValNat 2 (huttonLowerRat K).den)
        (padicValNat 5 (huttonLowerRat K).den) = e := by
  rw [padicValNat_two_huttonLowerRat_den,
    padicValNat_five_huttonLowerRat_den K e hlow hhigh]
  simp

end Theory.PiDigits.HuttonDecimalTransient

#print axioms Theory.PiDigits.HuttonDecimalTransient.huttonCancellationFactor_odd
#print axioms Theory.PiDigits.HuttonDecimalTransient.padicValRat_two_huttonPairRat
#print axioms Theory.PiDigits.HuttonDecimalTransient.padicValRat_two_sum_lower
#print axioms Theory.PiDigits.HuttonDecimalTransient.two_le_padicValRat_two_huttonLowerRat
#print axioms Theory.PiDigits.HuttonDecimalTransient.huttonLowerRat_den_odd
#print axioms Theory.PiDigits.HuttonDecimalTransient.padicValNat_two_huttonLowerRat_den
#print axioms Theory.PiDigits.HuttonDecimalTransient.huttonLowerRat_baseTen_denominator_exponent
