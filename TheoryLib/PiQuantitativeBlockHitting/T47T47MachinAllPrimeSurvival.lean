import TheoryLib.PiQuantitativeBlockHitting.T45T45MachinPrimeSurvival

/-!
# T47: endpoint and all-prime survival for the sampled Machin forcing

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T45 proves exact denominator survival for the three admissible interior
prime slots.  This module treats the two endpoint slots.  At either endpoint
there is exactly one term of valuation `-1`; every other term is integral at
the slot prime, so the strict ultrametric inequality prevents cancellation.

The final section treats the Machin base `239` separately and combines the
slot cases into a statement about every prime greater than twelve.  These
are exact rational-arithmetic results.  They do not imply an archimedean
cylinder hit, recurrence, density, normality, or the every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinAllPrimeSurvival

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinLocalForcing
open Theory.PiDigits.MachinPrimeSurvival

/-- A single signed fraction whose linear denominator is the prime `p`,
while its exponential base is a `p`-unit, has valuation exactly `-1`. -/
lemma padicValRat_signed_prime_fraction_eq_neg_one
    (p c q j : ℕ) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hq : ¬ p ∣ q)
    (hc0 : c ≠ 0) (hq0 : q ≠ 0) :
    padicValRat p
      ((c : ℚ) * (-1 : ℚ) ^ j / ((p : ℚ) * q ^ p)) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hneg : (-1 : ℚ) ≠ 0 := by norm_num
  have hnum : (c : ℚ) * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero hcq (pow_ne_zero _ hneg)
  have hden : (p : ℚ) * q ^ p ≠ 0 :=
    mul_ne_zero hpq (pow_ne_zero _ hqq)
  have hvalc : padicValRat p (c : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hc
  have hvalq : padicValRat p (q : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hq
  have hvalneg : padicValRat p (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  rw [padicValRat.div hnum hden,
    padicValRat.mul hcq (pow_ne_zero _ hneg),
    padicValRat.pow hneg, hvalc, hvalneg,
    padicValRat.mul hpq (pow_ne_zero _ hqq),
    padicValRat.self hp.one_lt, padicValRat.pow hqq, hvalq]
  norm_num

/-- A signed fraction whose exponential base itself is `p`, but whose
linear denominator is a `p`-unit, has valuation minus its exponent. -/
lemma padicValRat_signed_basePrime_fraction_eq_neg_exponent
    (p c a j : ℕ) (hp : p.Prime)
    (hc : ¬ p ∣ c) (ha : ¬ p ∣ a)
    (hc0 : c ≠ 0) (ha0 : a ≠ 0) :
    padicValRat p
      ((c : ℚ) * (-1 : ℚ) ^ j / ((a : ℚ) * p ^ a)) = -(a : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  have hneg : (-1 : ℚ) ≠ 0 := by norm_num
  have hnum : (c : ℚ) * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero hcq (pow_ne_zero _ hneg)
  have hden : (a : ℚ) * p ^ a ≠ 0 :=
    mul_ne_zero haq (pow_ne_zero _ hpq)
  have hvalc : padicValRat p (c : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hc
  have hvala : padicValRat p (a : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd ha
  have hvalneg : padicValRat p (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  rw [padicValRat.div hnum hden,
    padicValRat.mul hcq (pow_ne_zero _ hneg),
    padicValRat.pow hneg, hvalc, hvalneg,
    padicValRat.mul haq (pow_ne_zero _ hpq),
    padicValRat.pow hpq, hvala, padicValRat.self hp.one_lt]
  norm_num

/-- When both the linear denominator and the exponential base are `p`, the
valuation is `-(p+1)`. -/
lemma padicValRat_signed_self_basePrime_fraction
    (p c j : ℕ) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hc0 : c ≠ 0) :
    padicValRat p
      ((c : ℚ) * (-1 : ℚ) ^ j / ((p : ℚ) * p ^ p)) =
        -((p + 1 : ℕ) : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  have hneg : (-1 : ℚ) ≠ 0 := by norm_num
  have hnum : (c : ℚ) * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero hcq (pow_ne_zero _ hneg)
  have hden : (p : ℚ) * p ^ p ≠ 0 :=
    mul_ne_zero hpq (pow_ne_zero _ hpq)
  have hvalc : padicValRat p (c : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hc
  have hvalneg : padicValRat p (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  rw [padicValRat.div hnum hden,
    padicValRat.mul hcq (pow_ne_zero _ hneg),
    padicValRat.pow hneg, hvalc, hvalneg,
    padicValRat.mul hpq (pow_ne_zero _ hpq),
    padicValRat.pow hpq, padicValRat.self hp.one_lt]
  push_cast
  ring

/-- Strict lower bounds on every term of a nonzero finite sum pass to the
sum by the ultrametric inequality. -/
lemma padicValRat_sum_gt
    {p : ℕ} (hp : p.Prime) {α : Type*}
    (bound : ℤ) (s : Finset α) (f : α → ℚ)
    (hf : ∀ a ∈ s, bound < padicValRat p (f a))
    (hs : ∑ a ∈ s, f a ≠ 0) :
    bound < padicValRat p (∑ a ∈ s, f a) := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  induction s using Finset.induction with
  | empty => simp at hs
  | @insert a s ha ih =>
      rw [sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · simp [hfa] at hs ⊢
        exact ih (fun b hb => hf b (mem_insert_of_mem hb)) hs
      by_cases hsum : ∑ b ∈ s, f b = 0
      · simp [hsum]
        exact hf a (mem_insert_self a s)
      · have htail := ih (fun b hb => hf b (mem_insert_of_mem hb)) hsum
        exact lt_of_lt_of_le
          (lt_min (hf a (mem_insert_self a s)) htail)
          (padicValRat.min_le_padicValRat_add hs)

/-- If one summand has valuation `-1` and the other is zero or has
nonnegative valuation, their sum retains valuation `-1`. -/
lemma padicValRat_add_eq_neg_one_of_nonneg
    (p : ℕ) (hp : p.Prime) {singular regular : ℚ}
    (hsingular : padicValRat p singular = -1)
    (hregular : regular = 0 ∨ 0 ≤ padicValRat p regular) :
    padicValRat p (regular + singular) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsingular0 : singular ≠ 0 := by
    intro hzero
    simp [hzero] at hsingular
  by_cases hregular0 : regular = 0
  · simpa [hregular0] using hsingular
  · have hregularVal : 0 ≤ padicValRat p regular :=
      hregular.resolve_left hregular0
    have hsum : singular + regular ≠ 0 := by
      intro hzero
      have heq : regular = -singular := by linarith
      have hvaleq := congrArg (padicValRat p) heq
      rw [padicValRat.neg, hsingular] at hvaleq
      omega
    rw [add_comm]
    calc
      padicValRat p (singular + regular) = padicValRat p singular :=
        padicValRat.add_eq_of_lt hsum hsingular0 hregular0
          (by rw [hsingular]; omega)
      _ = -1 := hsingular

/-- The eleven terms left after removing the left endpoint base-5 term. -/
def leftEndpointRegularBlockRat (N : ℕ) : ℚ :=
  ∑ j ∈ (range 6).erase 0, baseFiveWindowTermRat N j
    + ∑ j ∈ range 6, base239WindowTermRat N j

/-- The eleven terms left after removing the right endpoint base-239 term. -/
def rightEndpointRegularBlockRat (N : ℕ) : ℚ :=
  ∑ j ∈ range 6, baseFiveWindowTermRat N j
    + ∑ j ∈ (range 6).erase 5, base239WindowTermRat N j

theorem actualMachinBlockRat_eq_leftEndpointRegular_add
    (N : ℕ) :
    actualMachinBlockRat N =
      leftEndpointRegularBlockRat N + baseFiveWindowTermRat N 0 := by
  have hzero : 0 ∈ range 6 := mem_range.2 (by omega)
  have hfive := sum_erase_add (range 6) (baseFiveWindowTermRat N) hzero
  unfold actualMachinBlockRat leftEndpointRegularBlockRat
  rw [← hfive]
  ring

theorem actualMachinBlockRat_eq_rightEndpointRegular_add
    (N : ℕ) :
    actualMachinBlockRat N =
      rightEndpointRegularBlockRat N + base239WindowTermRat N 5 := by
  have hfive : 5 ∈ range 6 := mem_range.2 (by omega)
  have h239 := sum_erase_add (range 6) (base239WindowTermRat N) hfive
  unfold actualMachinBlockRat rightEndpointRegularBlockRat
  rw [← h239]
  ring

lemma prime_not_dvd_left_regular_239_exponent
    (N p j : ℕ) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5) (hj : j ∈ range 6) :
    ¬ p ∣ 12 * N + 7 + 2 * j := by
  intro hdvd
  have hj6 : j < 6 := mem_range.1 hj
  have heq : 12 * N + 7 + 2 * j = p :=
    eq_of_dvd_of_pos_of_lt_two_mul
      (by omega) (by omega) (by omega) hdvd
  omega

lemma prime_not_dvd_right_regular_five_exponent
    (N p j : ℕ) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 17) (hj : j ∈ range 6) :
    ¬ p ∣ 12 * N + 5 + 2 * j := by
  intro hdvd
  have hj6 : j < 6 := mem_range.1 hj
  have heq : 12 * N + 5 + 2 * j = p :=
    eq_of_dvd_of_pos_of_lt_two_mul
      (by omega) (by omega) (by omega) hdvd
  omega

lemma leftEndpointPrime_ne_239
    (N p : ℕ) (hpdef : p = 12 * N + 5) :
    p ≠ 239 := by
  omega

lemma rightEndpointPrime_ne_239
    (N p : ℕ) (hpdef : p = 12 * N + 17) :
    p ≠ 239 := by
  omega

lemma padicValRat_leftEndpointRegularBlockRat_nonneg
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5)
    (hregular : leftEndpointRegularBlockRat N ≠ 0) :
    0 ≤ padicValRat p (leftEndpointRegularBlockRat N) := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℚ := ∑ j ∈ (range 6).erase 0, baseFiveWindowTermRat N j
  let G : ℚ := ∑ j ∈ range 6, base239WindowTermRat N j
  have hF (hF0 : F ≠ 0) : 0 ≤ padicValRat p F := by
    apply padicValRat_sum_nonneg hp
    · intro j hj
      rw [padicValRat_regular_five_term_eq_zero N 0 p j hp hpgt
        (by simpa using hpdef) hj]
    · exact hF0
  have hG (hG0 : G ≠ 0) : 0 ≤ padicValRat p G := by
    apply padicValRat_sum_nonneg hp
    · intro j hj
      unfold base239WindowTermRat
      change 0 ≤ padicValRat p
        (((4 : ℕ) : ℚ) * (-1 : ℚ) ^ j /
          ((((12 * N + 7 + 2 * j : ℕ) : ℚ)) *
            ((239 : ℕ) : ℚ) ^ (12 * N + 7 + 2 * j)))
      rw [padicValRat_signed_fraction_eq_zero
        p 4 239 (12 * N + 7 + 2 * j) j hp
        (prime_gt_twelve_not_dvd_four p hp hpgt)
        (prime_ne_239_not_dvd_239 p hp
          (leftEndpointPrime_ne_239 N p hpdef))
        (prime_not_dvd_left_regular_239_exponent N p j hpgt hpdef hj)
        (by norm_num) (by norm_num) (by omega)]
    · exact hG0
  change 0 ≤ padicValRat p (F + G)
  have hFG : F + G ≠ 0 := by
    simpa [F, G, leftEndpointRegularBlockRat] using hregular
  by_cases hF0 : F = 0
  · simp [hF0] at hFG ⊢
    exact hG hFG
  by_cases hG0 : G = 0
  · simp [hG0]
    exact hF hF0
  exact le_trans (le_min (hF hF0) (hG hG0))
    (padicValRat.min_le_padicValRat_add hFG)

lemma padicValRat_rightEndpointRegularBlockRat_nonneg
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 17)
    (hregular : rightEndpointRegularBlockRat N ≠ 0) :
    0 ≤ padicValRat p (rightEndpointRegularBlockRat N) := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℚ := ∑ j ∈ range 6, baseFiveWindowTermRat N j
  let G : ℚ := ∑ j ∈ (range 6).erase 5, base239WindowTermRat N j
  have hF (hF0 : F ≠ 0) : 0 ≤ padicValRat p F := by
    apply padicValRat_sum_nonneg hp
    · intro j hj
      unfold baseFiveWindowTermRat
      change 0 ≤ padicValRat p
        (((16 : ℕ) : ℚ) * (-1 : ℚ) ^ j /
          ((((12 * N + 5 + 2 * j : ℕ) : ℚ)) *
            ((5 : ℕ) : ℚ) ^ (12 * N + 5 + 2 * j)))
      rw [padicValRat_signed_fraction_eq_zero
        p 16 5 (12 * N + 5 + 2 * j) j hp
        (prime_gt_twelve_not_dvd_sixteen p hp hpgt)
        (prime_gt_twelve_not_dvd_five p hp hpgt)
        (prime_not_dvd_right_regular_five_exponent N p j hpgt hpdef hj)
        (by norm_num) (by norm_num) (by omega)]
    · exact hF0
  have hG (hG0 : G ≠ 0) : 0 ≤ padicValRat p G := by
    apply padicValRat_sum_nonneg hp
    · intro j hj
      rw [padicValRat_regular_239_term_eq_zero N 6 p j hp hpgt
        (rightEndpointPrime_ne_239 N p hpdef)
        (by simpa using hpdef) hj (by omega)]
    · exact hG0
  change 0 ≤ padicValRat p (F + G)
  have hFG : F + G ≠ 0 := by
    simpa [F, G, rightEndpointRegularBlockRat] using hregular
  by_cases hF0 : F = 0
  · simp [hF0] at hFG ⊢
    exact hG hFG
  by_cases hG0 : G = 0
  · simp [hG0]
    exact hF hF0
  exact le_trans (le_min (hF hF0) (hG hG0))
    (padicValRat.min_le_padicValRat_add hFG)

lemma padicValRat_leftEndpointSingularTerm
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5) :
    padicValRat p (baseFiveWindowTermRat N 0) = -1 := by
  have hterm :
      baseFiveWindowTermRat N 0 =
        (16 : ℚ) * (-1 : ℚ) ^ 0 / ((p : ℚ) * 5 ^ p) := by
    simp only [baseFiveWindowTermRat]
    rw [← hpdef]
  rw [hterm]
  exact padicValRat_signed_prime_fraction_eq_neg_one
    p 16 5 0 hp
    (prime_gt_twelve_not_dvd_sixteen p hp hpgt)
    (prime_gt_twelve_not_dvd_five p hp hpgt)
    (by norm_num) (by norm_num)

lemma padicValRat_rightEndpointSingularTerm
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 17) :
    padicValRat p (base239WindowTermRat N 5) = -1 := by
  have hterm :
      base239WindowTermRat N 5 =
        (4 : ℚ) * (-1 : ℚ) ^ 5 / ((p : ℚ) * 239 ^ p) := by
    simp only [base239WindowTermRat]
    rw [← hpdef]
  rw [hterm]
  exact padicValRat_signed_prime_fraction_eq_neg_one
    p 4 239 5 hp
    (prime_gt_twelve_not_dvd_four p hp hpgt)
    (prime_ne_239_not_dvd_239 p hp
      (rightEndpointPrime_ne_239 N p hpdef))
    (by norm_num) (by norm_num)

/-- Left endpoint prime survival for the complete unscaled block. -/
theorem padicValRat_actualMachinBlockRat_leftEndpoint
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5) :
    padicValRat p (actualMachinBlockRat N) = -1 := by
  rw [actualMachinBlockRat_eq_leftEndpointRegular_add]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_leftEndpointSingularTerm N p hp hpgt hpdef
  · by_cases hregular : leftEndpointRegularBlockRat N = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_leftEndpointRegularBlockRat_nonneg
          N p hp hpgt hpdef hregular)

/-- Right endpoint prime survival for the complete unscaled block. -/
theorem padicValRat_actualMachinBlockRat_rightEndpoint
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 17) :
    padicValRat p (actualMachinBlockRat N) = -1 := by
  rw [actualMachinBlockRat_eq_rightEndpointRegular_add]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_rightEndpointSingularTerm N p hp hpgt hpdef
  · by_cases hregular : rightEndpointRegularBlockRat N = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_rightEndpointRegularBlockRat_nonneg
          N p hp hpgt hpdef hregular)

lemma padicValRat_decimalPower_eq_zero
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p) :
    padicValRat p ((10 : ℚ) ^ (N + 1)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have htenNotDvd : ¬ p ∣ 10 := by
    intro hdvd
    have hle : p ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have htenVal : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd htenNotDvd
  rw [padicValRat.pow (by norm_num), htenVal]
  norm_num

/-- Left endpoint prime survival in the complete sampled forcing. -/
theorem padicValRat_prime_sampledMachinForcingRat_leftEndpoint
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5) :
    padicValRat p (sampledMachinForcingRat N) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [sampledMachinForcingRat_eq_actualMachinBlockRat]
  have hblock :=
    padicValRat_actualMachinBlockRat_leftEndpoint N p hp hpgt hpdef
  have hblock0 : actualMachinBlockRat N ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_decimalPower_eq_zero N p hp hpgt, hblock]
  norm_num

/-- Right endpoint prime survival in the complete sampled forcing. -/
theorem padicValRat_prime_sampledMachinForcingRat_rightEndpoint
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 17) :
    padicValRat p (sampledMachinForcingRat N) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [sampledMachinForcingRat_eq_actualMachinBlockRat]
  have hblock :=
    padicValRat_actualMachinBlockRat_rightEndpoint N p hp hpgt hpdef
  have hblock0 : actualMachinBlockRat N ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_decimalPower_eq_zero N p hp hpgt, hblock]
  norm_num

/-- At `N = 19`, all terms except the final base-239 term. -/
def machin239RegularBlockRat : ℚ :=
  ∑ j ∈ range 6, baseFiveWindowTermRat 19 j
    + ∑ j ∈ (range 6).erase 5, base239WindowTermRat 19 j

theorem actualMachinBlockRat_nineteen_eq_regular_add_last :
    actualMachinBlockRat 19 =
      machin239RegularBlockRat + base239WindowTermRat 19 5 := by
  have hfive : 5 ∈ range 6 := mem_range.2 (by omega)
  have h239 := sum_erase_add (range 6) (base239WindowTermRat 19) hfive
  unfold actualMachinBlockRat machin239RegularBlockRat
  rw [← h239]
  ring

lemma padicValRat_baseFiveWindowTermRat_nineteen_gt
    (j : ℕ) (hj : j ∈ range 6) :
    (-245 : ℤ) < padicValRat 239 (baseFiveWindowTermRat 19 j) := by
  have hj6 : j < 6 := mem_range.1 hj
  by_cases ha : 239 ∣ 12 * 19 + 5 + 2 * j
  · have haeq : 12 * 19 + 5 + 2 * j = 239 :=
      eq_of_dvd_of_pos_of_lt_two_mul
        (by norm_num) (by omega) (by omega) ha
    have hj3 : j = 3 := by omega
    subst j
    unfold baseFiveWindowTermRat
    change (-245 : ℤ) < padicValRat 239
      (((16 : ℕ) : ℚ) * (-1 : ℚ) ^ 3 /
        (((239 : ℕ) : ℚ) * ((5 : ℕ) : ℚ) ^ 239))
    rw [padicValRat_signed_prime_fraction_eq_neg_one
      239 16 5 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    norm_num
  · unfold baseFiveWindowTermRat
    change (-245 : ℤ) < padicValRat 239
      (((16 : ℕ) : ℚ) * (-1 : ℚ) ^ j /
        ((((12 * 19 + 5 + 2 * j : ℕ) : ℚ)) *
          ((5 : ℕ) : ℚ) ^ (12 * 19 + 5 + 2 * j)))
    rw [padicValRat_signed_fraction_eq_zero
      239 16 5 (12 * 19 + 5 + 2 * j) j
      (by norm_num) (by norm_num) (by norm_num) ha
      (by norm_num) (by norm_num) (by omega)]
    norm_num

lemma padicValRat_base239WindowTermRat_nineteen_regular_gt
    (j : ℕ) (hj : j ∈ (range 6).erase 5) :
    (-245 : ℤ) < padicValRat 239 (base239WindowTermRat 19 j) := by
  have hj6 : j < 6 := mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ 5 := ne_of_mem_erase hj
  by_cases ha : 239 ∣ 12 * 19 + 7 + 2 * j
  · have haeq : 12 * 19 + 7 + 2 * j = 239 :=
      eq_of_dvd_of_pos_of_lt_two_mul
        (by norm_num) (by omega) (by omega) ha
    have hj2 : j = 2 := by omega
    subst j
    unfold base239WindowTermRat
    change (-245 : ℤ) < padicValRat 239
      (((4 : ℕ) : ℚ) * (-1 : ℚ) ^ 2 /
        (((239 : ℕ) : ℚ) * ((239 : ℕ) : ℚ) ^ 239))
    rw [padicValRat_signed_self_basePrime_fraction
      239 4 2 (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · unfold base239WindowTermRat
    change (-245 : ℤ) < padicValRat 239
      (((4 : ℕ) : ℚ) * (-1 : ℚ) ^ j /
        ((((12 * 19 + 7 + 2 * j : ℕ) : ℚ)) *
          ((239 : ℕ) : ℚ) ^ (12 * 19 + 7 + 2 * j)))
    rw [padicValRat_signed_basePrime_fraction_eq_neg_exponent
      239 4 (12 * 19 + 7 + 2 * j) j
      (by norm_num) (by norm_num) ha (by norm_num) (by omega)]
    push_cast
    omega

/-- The final base-239 term at `N = 19` has the unique smallest valuation
`-245`. -/
theorem padicValRat_base239WindowTermRat_nineteen_last :
    padicValRat 239 (base239WindowTermRat 19 5) = -245 := by
  unfold base239WindowTermRat
  change padicValRat 239
    (((4 : ℕ) : ℚ) * (-1 : ℚ) ^ 5 /
      (((245 : ℕ) : ℚ) * ((239 : ℕ) : ℚ) ^ 245)) = -245
  rw [padicValRat_signed_basePrime_fraction_eq_neg_exponent
    239 4 245 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num

lemma padicValRat_machin239RegularBlockRat_gt
    (hregular : machin239RegularBlockRat ≠ 0) :
    (-245 : ℤ) < padicValRat 239 machin239RegularBlockRat := by
  letI : Fact (Nat.Prime 239) := ⟨by norm_num⟩
  let F : ℚ := ∑ j ∈ range 6, baseFiveWindowTermRat 19 j
  let G : ℚ := ∑ j ∈ (range 6).erase 5, base239WindowTermRat 19 j
  have hF (hF0 : F ≠ 0) : (-245 : ℤ) < padicValRat 239 F := by
    apply padicValRat_sum_gt (by norm_num) (-245) (range 6)
      (baseFiveWindowTermRat 19)
    · exact padicValRat_baseFiveWindowTermRat_nineteen_gt
    · exact hF0
  have hG (hG0 : G ≠ 0) : (-245 : ℤ) < padicValRat 239 G := by
    apply padicValRat_sum_gt (by norm_num) (-245) ((range 6).erase 5)
      (base239WindowTermRat 19)
    · exact padicValRat_base239WindowTermRat_nineteen_regular_gt
    · exact hG0
  change (-245 : ℤ) < padicValRat 239 (F + G)
  have hFG : F + G ≠ 0 := by
    simpa [F, G, machin239RegularBlockRat] using hregular
  by_cases hF0 : F = 0
  · simp [hF0] at hFG ⊢
    exact hG hFG
  by_cases hG0 : G = 0
  · simp [hG0]
    exact hF hF0
  exact lt_of_lt_of_le (lt_min (hF hF0) (hG hG0))
    (padicValRat.min_le_padicValRat_add hFG)

/-- Exceptional Machin-base survival in the complete unscaled block. -/
theorem padicValRat_actualMachinBlockRat_nineteen_239 :
    padicValRat 239 (actualMachinBlockRat 19) = -245 := by
  letI : Fact (Nat.Prime 239) := ⟨by norm_num⟩
  rw [actualMachinBlockRat_nineteen_eq_regular_add_last]
  have hlast := padicValRat_base239WindowTermRat_nineteen_last
  have hlast0 : base239WindowTermRat 19 5 ≠ 0 := by
    intro hzero
    simp [hzero] at hlast
  by_cases hregular : machin239RegularBlockRat = 0
  · simpa [hregular] using hlast
  have hregularVal := padicValRat_machin239RegularBlockRat_gt hregular
  have hsum :
      base239WindowTermRat 19 5 + machin239RegularBlockRat ≠ 0 := by
    intro hzero
    have heq :
        machin239RegularBlockRat = -base239WindowTermRat 19 5 := by
      linarith
    have hvaleq := congrArg (padicValRat 239) heq
    rw [padicValRat.neg, hlast] at hvaleq
    omega
  rw [add_comm]
  calc
    padicValRat 239
        (base239WindowTermRat 19 5 + machin239RegularBlockRat) =
        padicValRat 239 (base239WindowTermRat 19 5) :=
      padicValRat.add_eq_of_lt hsum hlast0 hregular
        (by simpa [hlast] using hregularVal)
    _ = -245 := hlast

/-- Exceptional Machin-base survival in the complete sampled forcing. -/
theorem padicValRat_sampledMachinForcingRat_nineteen_239 :
    padicValRat 239 (sampledMachinForcingRat 19) = -245 := by
  letI : Fact (Nat.Prime 239) := ⟨by norm_num⟩
  rw [sampledMachinForcingRat_eq_actualMachinBlockRat]
  have hblock := padicValRat_actualMachinBlockRat_nineteen_239
  have hblock0 : actualMachinBlockRat 19 ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_decimalPower_eq_zero 19 239 (by norm_num) (by norm_num),
    hblock]
  norm_num

/-- A prime greater than twelve occupies one of the four reduced residue
classes modulo twelve. -/
lemma prime_gt_twelve_mod_twelve
    (p : ℕ) (hp : p.Prime) (hpgt : 12 < p) :
    p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
  have hnot2 : ¬ 2 ∣ p := by
    intro h2
    rcases (Nat.dvd_prime hp).mp h2 with h21 | h2p <;> omega
  have hnot3 : ¬ 3 ∣ p := by
    intro h3
    rcases (Nat.dvd_prime hp).mp h3 with h31 | h3p <;> omega
  have hmodlt : p % 12 < 12 := Nat.mod_lt p (by norm_num)
  have hmod2 : p % 12 % 2 = p % 2 :=
    Nat.mod_mod_of_dvd p (by norm_num)
  have hmod3 : p % 12 % 3 = p % 3 :=
    Nat.mod_mod_of_dvd p (by norm_num)
  interval_cases hmod : p % 12 <;>
    norm_num at hmod2 hmod3 ⊢ <;> omega

/-- Every nonexceptional prime greater than twelve has valuation `-1` in an
explicit sampled Machin forcing window. -/
theorem exists_padicValRat_prime_sampledMachinForcingRat_eq_neg_one
    (p : ℕ) (hp : p.Prime) (hpgt : 12 < p) (hpne : p ≠ 239) :
    ∃ N : ℕ, padicValRat p (sampledMachinForcingRat N) = -1 := by
  have hdivision := Nat.div_add_mod p 12
  rcases prime_gt_twelve_mod_twelve p hp hpgt with h1 | h5 | h7 | h11
  · refine ⟨p / 12 - 1, ?_⟩
    apply padicValRat_prime_sampledMachinForcingRat
      (p / 12 - 1) 4 p hp hpgt hpne
    · omega
    · exact Or.inr (Or.inr rfl)
  · refine ⟨p / 12, ?_⟩
    apply padicValRat_prime_sampledMachinForcingRat_leftEndpoint
      (p / 12) p hp hpgt
    omega
  · refine ⟨p / 12, ?_⟩
    apply padicValRat_prime_sampledMachinForcingRat
      (p / 12) 1 p hp hpgt hpne
    · omega
    · exact Or.inl rfl
  · refine ⟨p / 12, ?_⟩
    apply padicValRat_prime_sampledMachinForcingRat
      (p / 12) 3 p hp hpgt hpne
    · omega
    · exact Or.inr (Or.inl rfl)

/-- Every prime greater than twelve has negative valuation in at least one
actual sampled Machin forcing.  The prime `239` uses `N = 19` and valuation
`-245`; all other primes use a residue-class slot and valuation `-1`. -/
theorem exists_padicValRat_prime_sampledMachinForcingRat_neg
    (p : ℕ) (hp : p.Prime) (hpgt : 12 < p) :
    ∃ N : ℕ, padicValRat p (sampledMachinForcingRat N) < 0 := by
  by_cases hp239 : p = 239
  · subst p
    exact ⟨19, by
      rw [padicValRat_sampledMachinForcingRat_nineteen_239]
      norm_num⟩
  · obtain ⟨N, hN⟩ :=
      exists_padicValRat_prime_sampledMachinForcingRat_eq_neg_one
        p hp hpgt hp239
    exact ⟨N, by rw [hN]; norm_num⟩

/-- Negative `p`-adic valuation of a rational forces `p` to divide its
reduced denominator. -/
lemma dvd_rat_den_of_padicValRat_neg
    {p : ℕ} {q : ℚ}
    (hneg : padicValRat p q < 0) :
    p ∣ q.den := by
  by_contra hnot
  have hden : padicValNat p q.den = 0 :=
    padicValNat.eq_zero_of_not_dvd hnot
  rw [padicValRat_def, hden] at hneg
  omega

/-- Universal prime-survival law: every prime greater than twelve divides
the reduced denominator of at least one actual sampled Machin forcing. -/
theorem every_prime_gt_twelve_dvd_some_sampledMachinForcingRat_den
    (p : ℕ) (hp : p.Prime) (hpgt : 12 < p) :
    ∃ N : ℕ, p ∣ (sampledMachinForcingRat N).den := by
  obtain ⟨N, hN⟩ :=
    exists_padicValRat_prime_sampledMachinForcingRat_neg p hp hpgt
  exact ⟨N, dvd_rat_den_of_padicValRat_neg hN⟩

end Theory.PiDigits.MachinAllPrimeSurvival

#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.padicValRat_actualMachinBlockRat_leftEndpoint
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.padicValRat_actualMachinBlockRat_rightEndpoint
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.padicValRat_prime_sampledMachinForcingRat_leftEndpoint
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.padicValRat_prime_sampledMachinForcingRat_rightEndpoint
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.padicValRat_actualMachinBlockRat_nineteen_239
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.padicValRat_sampledMachinForcingRat_nineteen_239
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.exists_padicValRat_prime_sampledMachinForcingRat_eq_neg_one
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.exists_padicValRat_prime_sampledMachinForcingRat_neg
#print axioms
  Theory.PiDigits.MachinAllPrimeSurvival.every_prime_gt_twelve_dvd_some_sampledMachinForcingRat_den
