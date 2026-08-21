import TheoryLib.PiQuantitativeBlockHitting.T60T60HuttonAdjacentIncrement
import TheoryLib.PiQuantitativeBlockHitting.T48T48MachinSeedUpperHalfPrimeSurvival

/-!
# T61: upper-half prime survival in the rational Hutton shadows

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For `R = 4*K+3`, every prime `p > 7` in the upper half `R/2 < p ≤ R`,
apart from the fixed prime `17`, occurs exactly once in the reduced
denominator of the lower Hutton shadow.  The only terms with a `p`-divisible
linear denominator are the two terms at odd exponent `p`; after combination,
Fermat's theorem reduces their numerator to `4 * (2*7+3) = 68` modulo `p`.

This is exact denominator arithmetic.  It supplies no prefix discrepancy,
decimal-cylinder hit, distribution statement, or every-word theorem for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.HuttonUpperHalfPrimeSurvival

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonRationalShadow

/-- Number of terms in either lower Hutton Taylor prefix. -/
def huttonTermCount (K : ℕ) : ℕ := 2 * (K + 1)

/-- The coefficient-eight base-three Hutton term. -/
def huttonThreeTermRat (j : ℕ) : ℚ := 8 * arctanTermRat 3 j

/-- The coefficient-four base-seven Hutton term. -/
def huttonSevenTermRat (j : ℕ) : ℚ := 4 * arctanTermRat 7 j

/-- The integer numerator factor after combining the two Hutton terms at
the same odd exponent. -/
def huttonCancellationFactor (p : ℕ) : ℕ := 2 * 7 ^ p + 3 ^ p

/-- All Hutton terms except the pair at Taylor index `k`. -/
def huttonRegularBlockRat (K k : ℕ) : ℚ :=
  (∑ j ∈ (range (huttonTermCount K)).erase k, huttonThreeTermRat j) +
    ∑ j ∈ (range (huttonTermCount K)).erase k, huttonSevenTermRat j

lemma huttonThreeTermRat_eq_fraction (j : ℕ) :
    huttonThreeTermRat j =
      8 * (-1 : ℚ) ^ j /
        ((((2 * j + 1 : ℕ) : ℚ)) * 3 ^ (2 * j + 1)) := by
  unfold huttonThreeTermRat arctanTermRat
  simp only [inv_pow]
  push_cast
  rw [pow_add]
  field_simp

lemma huttonSevenTermRat_eq_fraction (j : ℕ) :
    huttonSevenTermRat j =
      4 * (-1 : ℚ) ^ j /
        ((((2 * j + 1 : ℕ) : ℚ)) * 7 ^ (2 * j + 1)) := by
  unfold huttonSevenTermRat arctanTermRat
  simp only [inv_pow]
  push_cast
  rw [pow_add]
  field_simp

/-- Exact expansion of the rational Hutton lower shadow into its two finite
Taylor sums. -/
theorem huttonLowerRat_eq_term_sums (K : ℕ) :
    huttonLowerRat K =
      (∑ j ∈ range (huttonTermCount K), huttonThreeTermRat j) +
        ∑ j ∈ range (huttonTermCount K), huttonSevenTermRat j := by
  unfold huttonLowerRat huttonTermCount huttonThreeTermRat
    huttonSevenTermRat arctanPartialRat
  simp only [mul_sum]

/-- The two terms at odd exponent `p = 2*k+1` combine over one exact
denominator. -/
theorem hutton_singular_pair_eq (p k : ℕ) (hpdef : p = 2 * k + 1) :
    huttonThreeTermRat k + huttonSevenTermRat k =
      4 * (-1 : ℚ) ^ k * (huttonCancellationFactor p : ℚ) /
        ((p : ℚ) * 3 ^ p * 7 ^ p) := by
  rw [huttonThreeTermRat_eq_fraction, huttonSevenTermRat_eq_fraction]
  unfold huttonCancellationFactor
  subst p
  push_cast
  field_simp
  ring

/-- Fermat reduction of the combined numerator factor. -/
theorem huttonCancellationFactor_cast_zmod
    (p : ℕ) (hp : p.Prime) :
    (huttonCancellationFactor p : ZMod p) = 17 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [huttonCancellationFactor, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]
  rw [ZMod.pow_card, ZMod.pow_card]
  norm_num

/-- Outside the single exceptional prime `17`, the combined numerator is a
`p`-unit. -/
lemma prime_not_dvd_huttonCancellationFactor
    (p : ℕ) (hp : p.Prime) (hp17 : p ≠ 17) :
    ¬ p ∣ huttonCancellationFactor p := by
  intro hdvd
  have hzero : (huttonCancellationFactor p : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  rw [huttonCancellationFactor_cast_zmod p hp] at hzero
  have hdvd17 : p ∣ 17 := (ZMod.natCast_eq_zero_iff 17 p).1 hzero
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hdvd17 with h1 | h17
  · exact hp.ne_one h1
  · exact hp17 h17

/-- Every other odd linear denominator in the prefix is a `p`-unit under
the upper-half hypothesis. -/
lemma upperHalfPrime_not_dvd_other_hutton_exponent
    (K k p j : ℕ)
    (hpLower : 4 * K + 3 < 2 * p)
    (hpdef : p = 2 * k + 1)
    (hj : j ∈ (range (huttonTermCount K)).erase k) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjlt : j < huttonTermCount K :=
    mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 2 * p := by
    unfold huttonTermCount at hjlt
    omega
  have heq : 2 * j + 1 = p :=
    eq_of_dvd_of_pos_of_lt_two_mul (by omega) (by omega) hexplt hdvd
  apply hjne
  omega

lemma padicValRat_huttonThreeTermRat_eq_zero
    (p j : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hexp : ¬ p ∣ 2 * j + 1) :
    padicValRat p (huttonThreeTermRat j) = 0 := by
  rw [huttonThreeTermRat_eq_fraction]
  have hc : ¬ p ∣ 8 := by
    intro h
    have hpow : p ∣ 2 ^ 3 := by norm_num at h ⊢; exact h
    have hsplit : p ∣ 2 := hp.dvd_of_dvd_pow hpow
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hsplit
    omega
  have hq : ¬ p ∣ 3 := by
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
    omega
  exact padicValRat_signed_fraction_eq_zero
    p 8 3 (2 * j + 1) j hp
      hc hq
      hexp (by norm_num) (by norm_num) (by positivity)

lemma padicValRat_huttonSevenTermRat_eq_zero
    (p j : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hexp : ¬ p ∣ 2 * j + 1) :
    padicValRat p (huttonSevenTermRat j) = 0 := by
  rw [huttonSevenTermRat_eq_fraction]
  have hc : ¬ p ∣ 4 := by
    intro h
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
    omega
  have hq : ¬ p ∣ 7 := by
    intro h
    have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) h
    omega
  exact padicValRat_signed_fraction_eq_zero
    p 4 7 (2 * j + 1) j hp
      hc hq
      hexp (by norm_num) (by norm_num) (by positivity)

/-- The combined upper-half pair has exact valuation `-1`. -/
theorem padicValRat_hutton_singular_pair
    (p k : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp17 : p ≠ 17)
    (hpdef : p = 2 * k + 1) :
    padicValRat p (huttonThreeTermRat k + huttonSevenTermRat k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [hutton_singular_pair_eq p k hpdef]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h3q : (3 : ℚ) ≠ 0 := by norm_num
  have h7q : (7 : ℚ) ≠ 0 := by norm_num
  have hfactorNat : huttonCancellationFactor p ≠ 0 := by
    exact Nat.ne_of_gt (by unfold huttonCancellationFactor; positivity)
  have hfactorQ : (huttonCancellationFactor p : ℚ) ≠ 0 := by
    exact_mod_cast hfactorNat
  have hnum0 :
      4 * (-1 : ℚ) ^ k * (huttonCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
      hfactorQ
  have hden0 : (p : ℚ) * 3 ^ p * 7 ^ p ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpq (pow_ne_zero _ h3q)) (pow_ne_zero _ h7q)
  have hp4 : ¬ p ∣ 4 := by
    intro h
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
    omega
  have hp3 : ¬ p ∣ 3 := by
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
    omega
  have hp7 : ¬ p ∣ 7 := by
    intro h
    have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) h
    omega
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp4
  have hvalNegOne : padicValRat p (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat p (huttonCancellationFactor p : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_not_dvd_huttonCancellationFactor p hp hp17)
  have hval3 : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp3
  have hval7 : padicValRat p (7 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp7
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hfactorQ,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.pow (by norm_num), hval4, hvalNegOne, hvalFactor,
    padicValRat.mul (mul_ne_zero hpq (pow_ne_zero _ h3q))
      (pow_ne_zero _ h7q),
    padicValRat.mul hpq (pow_ne_zero _ h3q),
    padicValRat.self hp.one_lt, padicValRat.pow h3q, hval3,
    padicValRat.pow h7q, hval7]
  norm_num

/-- Every nonsingular Hutton term has nonnegative valuation. -/
lemma padicValRat_huttonRegularBlockRat_nonneg
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hpLower : 4 * K + 3 < 2 * p)
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
          (upperHalfPrime_not_dvd_other_hutton_exponent
            K k p j hpLower hpdef hj)]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · apply Or.inr
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_huttonSevenTermRat_eq_zero p j hp hpgt
          (upperHalfPrime_not_dvd_other_hutton_exponent
            K k p j hpLower hpdef hj)]
      · exact hG0
  change 0 ≤ padicValRat p (F + G)
  apply padicValRat_add_nonneg_of_each_nonneg p hp hF hG
  simpa [F, G, huttonRegularBlockRat] using hregular

/-- Exact decomposition into the regular block and the upper-half singular
pair. -/
theorem huttonLowerRat_eq_regular_add_singular
    (K k p : ℕ) (hpdef : p = 2 * k + 1)
    (hpUpper : p ≤ 4 * K + 3) :
    huttonLowerRat K = huttonRegularBlockRat K k +
      (huttonThreeTermRat k + huttonSevenTermRat k) := by
  have hk : k < huttonTermCount K := by
    unfold huttonTermCount
    omega
  have hkmem : k ∈ range (huttonTermCount K) := mem_range.2 hk
  have hthree :=
    sum_erase_add (range (huttonTermCount K)) huttonThreeTermRat hkmem
  have hseven :=
    sum_erase_add (range (huttonTermCount K)) huttonSevenTermRat hkmem
  rw [huttonLowerRat_eq_term_sums]
  unfold huttonRegularBlockRat
  rw [← hthree, ← hseven]
  ring

/-- Main valuation theorem: every eligible upper-half prime occurs with
valuation exactly `-1` in the rational Hutton lower shadow. -/
theorem padicValRat_huttonLowerRat_upperHalfPrime
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp17 : p ≠ 17)
    (hpLower : 4 * K + 3 < 2 * p)
    (hpUpper : p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    padicValRat p (huttonLowerRat K) = -1 := by
  rw [huttonLowerRat_eq_regular_add_singular K k p hpdef hpUpper]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_hutton_singular_pair p k hp hpgt hp17 hpdef
  · by_cases hregular : huttonRegularBlockRat K k = 0
    · exact Or.inl hregular
    · exact Or.inr (padicValRat_huttonRegularBlockRat_nonneg
        K k p hp hpgt hpLower hpdef hregular)

/-- The eligible prime divides the reduced denominator. -/
theorem upperHalfPrime_dvd_huttonLowerRat_den
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp17 : p ≠ 17)
    (hpLower : 4 * K + 3 < 2 * p)
    (hpUpper : p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    p ∣ (huttonLowerRat K).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_huttonLowerRat_upperHalfPrime
    K k p hp hpgt hp17 hpLower hpUpper hpdef]
  norm_num

/-- The eligible prime occurs exactly once in the reduced denominator. -/
theorem padicValNat_huttonLowerRat_den_upperHalfPrime
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp17 : p ≠ 17)
    (hpLower : 4 * K + 3 < 2 * p)
    (hpUpper : p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    padicValNat p (huttonLowerRat K).den = 1 := by
  let q := huttonLowerRat K
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_huttonLowerRat_upperHalfPrime
      K k p hp hpgt hp17 hpLower hpUpper hpdef
  have hden : p ∣ q.den :=
    upperHalfPrime_dvd_huttonLowerRat_den
      K k p hp hpgt hp17 hpLower hpUpper hpdef
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

end Theory.PiDigits.HuttonUpperHalfPrimeSurvival

#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.huttonThreeTermRat_eq_fraction
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.huttonSevenTermRat_eq_fraction
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.huttonLowerRat_eq_term_sums
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.hutton_singular_pair_eq
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.huttonCancellationFactor_cast_zmod
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.prime_not_dvd_huttonCancellationFactor
#print axioms
  Theory.PiDigits.HuttonUpperHalfPrimeSurvival.upperHalfPrime_not_dvd_other_hutton_exponent
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.padicValRat_huttonThreeTermRat_eq_zero
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.padicValRat_huttonSevenTermRat_eq_zero
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.padicValRat_hutton_singular_pair
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.padicValRat_huttonRegularBlockRat_nonneg
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.huttonLowerRat_eq_regular_add_singular
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.padicValRat_huttonLowerRat_upperHalfPrime
#print axioms Theory.PiDigits.HuttonUpperHalfPrimeSurvival.upperHalfPrime_dvd_huttonLowerRat_den
#print axioms
  Theory.PiDigits.HuttonUpperHalfPrimeSurvival.padicValNat_huttonLowerRat_den_upperHalfPrime
