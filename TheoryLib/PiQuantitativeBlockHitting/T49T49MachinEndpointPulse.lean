import TheoryLib.PiQuantitativeBlockHitting.T48T48MachinSeedUpperHalfPrimeSurvival

/-!
# T49: a class-five endpoint-to-endpoint Machin pulse

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Let `p = 12*N+17` be prime.  In the forcing at index `N`, `p` is the
right base-239 endpoint.  In the next forcing it is the left base-5
endpoint.  The recurrence therefore combines their singular contributions
at `sampledMachinValueRat (N+2)` into

`10^(N+2) * (16 / 5^p - 4 / 239^p)`.

After localization at `p`, Fermat's theorem reduces this to the nonzero
class

`10^(N+2) * 4*951 / (5*239)`.

The rest of the seed is `p`-integral.  The later forcing windows remain
`p`-integral through the stated pulse range because every possible odd
linear denominator lies strictly between `p` and `3*p`, where the only
intermediate multiple `2*p` is even.

These are exact rational and local-arithmetic statements.  They do not
give archimedean cancellation, a decimal cylinder hit, recurrence, density,
normality, or the every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinEndpointPulse

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinLocalForcing
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinFixedModulusTelescoping
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival

/-- Exact combined singular contribution after multiplication by `p`. -/
def endpointPulseCoreRat (N p : ℕ) : ℚ :=
  (10 : ℚ) ^ (N + 2) *
    (16 / (5 : ℚ) ^ p - 4 / (239 : ℚ) ^ p)

/-- All terms in the two-step recurrence other than the two endpoint
singular terms. -/
def endpointPulseRegularRat (N : ℕ) : ℚ :=
  100 * sampledMachinValueRat N
    + 10 * (10 : ℚ) ^ (N + 1) * rightEndpointRegularBlockRat N
    + (10 : ℚ) ^ (N + 2) * leftEndpointRegularBlockRat (N + 1)

lemma rightEndpointSingularTerm_eq
    (N p : ℕ) (hpdef : p = 12 * N + 17) :
    base239WindowTermRat N 5 =
      -4 / ((p : ℚ) * 239 ^ p) := by
  unfold base239WindowTermRat
  rw [← hpdef]
  norm_num

lemma nextLeftEndpointSingularTerm_eq
    (N p : ℕ) (hpdef : p = 12 * N + 17) :
    baseFiveWindowTermRat (N + 1) 0 =
      16 / ((p : ℚ) * 5 ^ p) := by
  unfold baseFiveWindowTermRat
  have he : 12 * (N + 1) + 5 + 2 * 0 = p := by omega
  rw [he]
  norm_num

/-- Exact two-step endpoint decomposition.  No congruence or asymptotic
argument is used here. -/
theorem p_mul_sampledMachinValueRat_add_two_eq_core_add_regular
    (N p : ℕ) (hpdef : p = 12 * N + 17) :
    (p : ℚ) * sampledMachinValueRat (N + 2) =
      endpointPulseCoreRat N p +
        (p : ℚ) * endpointPulseRegularRat N := by
  rw [show N + 2 = (N + 1) + 1 by omega,
    sampledMachinValueRat_succ, sampledMachinValueRat_succ]
  rw [sampledMachinForcingRat_eq_actualMachinBlockRat,
    sampledMachinForcingRat_eq_actualMachinBlockRat]
  rw [actualMachinBlockRat_eq_rightEndpointRegular_add N,
    actualMachinBlockRat_eq_leftEndpointRegular_add (N + 1)]
  rw [rightEndpointSingularTerm_eq N p hpdef,
    nextLeftEndpointSingularTerm_eq N p hpdef]
  unfold endpointPulseCoreRat endpointPulseRegularRat
  have hpq : (p : ℚ) ≠ 0 := by
    rw [hpdef]
    positivity
  field_simp
  ring

/-- Fermat localization of the exact pulse core.  The statement is made
directly in `ZMod p` using only denominators known to be `p`-units. -/
theorem endpointPulseCore_zmod_eq_expected
    (N p : ℕ) [Fact p.Prime]
    (hpgt : 12 < p) (hp239 : p ≠ 239) :
    (10 : ZMod p) ^ (N + 2) *
        ((16 : ZMod p) / (5 : ZMod p) ^ p -
          4 / (239 : ZMod p) ^ p) =
      (4 * 951 : ZMod p) * (10 : ZMod p) ^ (N + 2) /
        ((5 : ZMod p) * 239) := by
  have hp : p.Prime := Fact.out
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : (((5 : ℤ) : ZMod p)) = 0 := by
      norm_num at hzero ⊢
      exact hzero
    have hdvdInt : (p : ℤ) ∣ 5 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (5 : ℤ) p).mp hzero'
    have hdvd : p ∣ 5 := by exact_mod_cast hdvdInt
    have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h239 : (239 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : (((239 : ℤ) : ZMod p)) = 0 := by
      norm_num at hzero ⊢
      exact hzero
    have hdvdInt : (p : ℤ) ∣ 239 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (239 : ℤ) p).mp hzero'
    have hdvd : p ∣ 239 := by exact_mod_cast hdvdInt
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 239)).mp hdvd with h1 | heq
    · exact hp.ne_one h1
    · exact hp239 heq
  rw [ZMod.pow_card, ZMod.pow_card]
  field_simp
  ring

/-- The expected localized class is nonzero.  The only prime factors of
`951` are `3` and `317`. -/
theorem endpointPulse_expected_zmod_ne_zero
    (N p : ℕ) [Fact p.Prime]
    (hpgt : 12 < p) (hp239 : p ≠ 239) (hp317 : p ≠ 317) :
    (4 * 951 : ZMod p) * (10 : ZMod p) ^ (N + 2) /
        ((5 : ZMod p) * 239) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : (((4 : ℤ) : ZMod p)) = 0 := by
      norm_num at hzero ⊢
      exact hzero
    have hdvdInt : (p : ℤ) ∣ 4 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (4 : ℤ) p).mp hzero'
    have hdvd : p ∣ 4 := by exact_mod_cast hdvdInt
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h951 : (951 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : (((951 : ℤ) : ZMod p)) = 0 := by
      norm_num at hzero ⊢
      exact hzero
    have hdvdInt : (p : ℤ) ∣ 951 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (951 : ℤ) p).mp hzero'
    have hdvd : p ∣ 951 := by exact_mod_cast hdvdInt
    exact prime_gt_five_ne_317_not_dvd_951 p hp (by omega) hp317 hdvd
  have h10 : (10 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : (((10 : ℤ) : ZMod p)) = 0 := by
      norm_num at hzero ⊢
      exact hzero
    have hdvdInt : (p : ℤ) ∣ 10 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (10 : ℤ) p).mp hzero'
    have hdvd : p ∣ 10 := by exact_mod_cast hdvdInt
    have hle : p ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : (((5 : ℤ) : ZMod p)) = 0 := by
      norm_num at hzero ⊢
      exact hzero
    have hdvdInt : (p : ℤ) ∣ 5 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (5 : ℤ) p).mp hzero'
    have hdvd : p ∣ 5 := by exact_mod_cast hdvdInt
    have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h239 : (239 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : (((239 : ℤ) : ZMod p)) = 0 := by
      norm_num at hzero ⊢
      exact hzero
    have hdvdInt : (p : ℤ) ∣ 239 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (239 : ℤ) p).mp hzero'
    have hdvd : p ∣ 239 := by exact_mod_cast hdvdInt
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 239)).mp hdvd with h1 | heq
    · exact hp.ne_one h1
    · exact hp239 heq
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero h4 h951) (pow_ne_zero _ h10))
    (mul_ne_zero h5 h239)

/-- Number of odd exponents shared by the two Taylor prefixes at the sample
immediately before the endpoint pair. -/
def priorCommonTermCount (N : ℕ) : ℕ :=
  6 * N + 2

/-- Exact Taylor-prefix expansion of the prior sample. -/
theorem machinLowerRat_prior_eq (N : ℕ) :
    machinLowerRat (3 * N) =
      (∑ j ∈ range (priorCommonTermCount N), seedFiveTermRat j)
        + (∑ j ∈ range (priorCommonTermCount N), seed239TermRat j)
        + seed239TermRat (priorCommonTermCount N) := by
  unfold machinLowerRat arctanPartialRat
  have hcount : 2 * (3 * N + 1) = priorCommonTermCount N := by
    simp [priorCommonTermCount]
    omega
  rw [hcount, sum_range_succ]
  simp only [seedFiveTermRat, seed239TermRat, mul_sum]
  simp only [← mul_sum]
  ring

lemma endpointPrime_not_dvd_prior_common_exponent
    (N p j : ℕ) (hpdef : p = 12 * N + 17)
    (hj : j ∈ range (priorCommonTermCount N)) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjlt : j < priorCommonTermCount N := mem_range.1 hj
  have hexplt : 2 * j + 1 < p := by
    simp [priorCommonTermCount] at hjlt
    omega
  have hle : p ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) hdvd
  omega

lemma endpointPrime_not_dvd_prior_endpoint
    (N p : ℕ) (hpdef : p = 12 * N + 17) :
    ¬ p ∣ 2 * priorCommonTermCount N + 1 := by
  intro hdvd
  have hlt : 2 * priorCommonTermCount N + 1 < p := by
    simp [priorCommonTermCount]
    omega
  have hle : p ≤ 2 * priorCommonTermCount N + 1 :=
    Nat.le_of_dvd (by positivity) hdvd
  omega

/-- Multiplication by a nonzero `p`-adic unit preserves the property of
being zero or having nonnegative valuation. -/
lemma padicValRat_unit_mul_nonneg_or_zero
    (p : ℕ) (hp : p.Prime) {a q : ℚ}
    (ha0 : a ≠ 0) (haval : padicValRat p a = 0)
    (hq : q = 0 ∨ 0 ≤ padicValRat p q) :
    a * q = 0 ∨ 0 ≤ padicValRat p (a * q) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hq with rfl | hqval
  · exact Or.inl (by ring)
  by_cases hq0 : q = 0
  · exact Or.inl (by simp [hq0])
  refine Or.inr ?_
  rw [padicValRat.mul ha0 hq0, haval]
  simpa using hqval

/-- The sample before the two endpoint forcings is `p`-integral. -/
lemma padicValRat_prior_sample_nonneg_or_zero
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17) :
    sampledMachinValueRat N = 0 ∨
      0 ≤ padicValRat p (sampledMachinValueRat N) := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℚ :=
    ∑ j ∈ range (priorCommonTermCount N), seedFiveTermRat j
  let G : ℚ :=
    ∑ j ∈ range (priorCommonTermCount N), seed239TermRat j
  let E : ℚ := seed239TermRat (priorCommonTermCount N)
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seedFiveTermRat_eq_zero p j hp (by omega)
          (endpointPrime_not_dvd_prior_common_exponent N p j hpdef hj)]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seed239TermRat_eq_zero p j hp hp239 (by omega)
          (endpointPrime_not_dvd_prior_common_exponent N p j hpdef hj)]
      · exact hG0
  have hEVal : padicValRat p E = 0 :=
    padicValRat_seed239TermRat_eq_zero
      p (priorCommonTermCount N) hp hp239 (by omega)
      (endpointPrime_not_dvd_prior_endpoint N p hpdef)
  have hE : E = 0 ∨ 0 ≤ padicValRat p E := Or.inr (by rw [hEVal])
  have hFG : F + G = 0 ∨ 0 ≤ padicValRat p (F + G) := by
    by_cases hzero : F + G = 0
    · exact Or.inl hzero
    · exact Or.inr
        (padicValRat_add_nonneg_of_each_nonneg p hp hF hG hzero)
  have hblock : (F + G) + E = 0 ∨
      0 ≤ padicValRat p ((F + G) + E) := by
    by_cases hzero : (F + G) + E = 0
    · exact Or.inl hzero
    · exact Or.inr
        (padicValRat_add_nonneg_of_each_nonneg p hp hFG hE hzero)
  have htenVal :=
    padicValRat_ten_pow_eq_zero_of_prime_gt_five N p hp (by omega)
  have hten0 : (10 : ℚ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [sampledMachinValueRat, machinLowerRat_prior_eq]
  change (10 : ℚ) ^ N * ((F + G) + E) = 0 ∨
    0 ≤ padicValRat p ((10 : ℚ) ^ N * ((F + G) + E))
  exact padicValRat_unit_mul_nonneg_or_zero
    p hp hten0 htenVal hblock

/-- The complete regular remainder in the initial endpoint pulse is
`p`-integral. -/
lemma padicValRat_endpointPulseRegularRat_nonneg_or_zero
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17) :
    endpointPulseRegularRat N = 0 ∨
      0 ≤ padicValRat p (endpointPulseRegularRat N) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hprior :=
    padicValRat_prior_sample_nonneg_or_zero N p hp hpgt hp239 hpdef
  have hright : rightEndpointRegularBlockRat N = 0 ∨
      0 ≤ padicValRat p (rightEndpointRegularBlockRat N) := by
    by_cases hzero : rightEndpointRegularBlockRat N = 0
    · exact Or.inl hzero
    · exact Or.inr (padicValRat_rightEndpointRegularBlockRat_nonneg
        N p hp hpgt hpdef hzero)
  have hleft : leftEndpointRegularBlockRat (N + 1) = 0 ∨
      0 ≤ padicValRat p (leftEndpointRegularBlockRat (N + 1)) := by
    by_cases hzero : leftEndpointRegularBlockRat (N + 1) = 0
    · exact Or.inl hzero
    · refine Or.inr (padicValRat_leftEndpointRegularBlockRat_nonneg
        (N + 1) p hp hpgt ?_ hzero)
      omega
  have hten2 : padicValRat p ((10 : ℚ) ^ 2) = 0 :=
    padicValRat_ten_pow_eq_zero_of_prime_gt_five 2 p hp (by omega)
  have htenN2 : padicValRat p ((10 : ℚ) ^ (N + 2)) = 0 :=
    padicValRat_ten_pow_eq_zero_of_prime_gt_five (N + 2) p hp (by omega)
  have hA : 100 * sampledMachinValueRat N = 0 ∨
      0 ≤ padicValRat p (100 * sampledMachinValueRat N) := by
    have h100 : (100 : ℚ) = (10 : ℚ) ^ 2 := by norm_num
    rw [h100]
    exact padicValRat_unit_mul_nonneg_or_zero p hp
      (pow_ne_zero _ (by norm_num)) hten2 hprior
  have hB : 10 * (10 : ℚ) ^ (N + 1) * rightEndpointRegularBlockRat N = 0 ∨
      0 ≤ padicValRat p
        (10 * (10 : ℚ) ^ (N + 1) * rightEndpointRegularBlockRat N) := by
    have hpow : (10 : ℚ) * 10 ^ (N + 1) = 10 ^ (N + 2) := by
      rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    exact padicValRat_unit_mul_nonneg_or_zero p hp
      (pow_ne_zero _ (by norm_num)) htenN2 hright
  have hC : (10 : ℚ) ^ (N + 2) * leftEndpointRegularBlockRat (N + 1) = 0 ∨
      0 ≤ padicValRat p
        ((10 : ℚ) ^ (N + 2) * leftEndpointRegularBlockRat (N + 1)) :=
    padicValRat_unit_mul_nonneg_or_zero p hp
      (pow_ne_zero _ (by norm_num)) htenN2 hleft
  have hAB : 100 * sampledMachinValueRat N +
      10 * (10 : ℚ) ^ (N + 1) * rightEndpointRegularBlockRat N = 0 ∨
      0 ≤ padicValRat p
        (100 * sampledMachinValueRat N +
          10 * (10 : ℚ) ^ (N + 1) * rightEndpointRegularBlockRat N) := by
    by_cases hzero : 100 * sampledMachinValueRat N +
        10 * (10 : ℚ) ^ (N + 1) * rightEndpointRegularBlockRat N = 0
    · exact Or.inl hzero
    · exact Or.inr
        (padicValRat_add_nonneg_of_each_nonneg p hp hA hB hzero)
  unfold endpointPulseRegularRat
  by_cases hzero :
      (100 * sampledMachinValueRat N +
        10 * (10 : ℚ) ^ (N + 1) * rightEndpointRegularBlockRat N) +
          (10 : ℚ) ^ (N + 2) * leftEndpointRegularBlockRat (N + 1) = 0
  · exact Or.inl (by simpa [add_assoc] using hzero)
  · refine Or.inr ?_
    exact padicValRat_add_nonneg_of_each_nonneg p hp hAB hC hzero

lemma padicValRat_p_mul_endpointPulseRegularRat_ge_one_or_zero
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17) :
    (p : ℚ) * endpointPulseRegularRat N = 0 ∨
      1 ≤ padicValRat p ((p : ℚ) * endpointPulseRegularRat N) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hprop := padicValRat_endpointPulseRegularRat_nonneg_or_zero
    N p hp hpgt hp239 hpdef
  by_cases hreg0 : endpointPulseRegularRat N = 0
  · exact Or.inl (by simp [hreg0])
  · have hval : 0 ≤ padicValRat p (endpointPulseRegularRat N) :=
      hprop.resolve_left hreg0
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine Or.inr ?_
    rw [padicValRat.mul hpq hreg0, padicValRat.self hp.one_lt]
    omega

/-- Integer-factor presentation of the localized pulse core. -/
theorem endpointPulseCoreRat_eq_cancellationFactor
    (N p : ℕ) :
    endpointPulseCoreRat N p =
      (10 : ℚ) ^ (N + 2) *
        ((4 : ℚ) * (machinCancellationFactor p : ℚ) /
          ((5 : ℚ) ^ p * (239 : ℚ) ^ p)) := by
  unfold endpointPulseCoreRat machinCancellationFactor
  push_cast
  field_simp
  ring

/-- The localized pulse core is a `p`-adic unit. -/
theorem padicValRat_endpointPulseCoreRat
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317) :
    padicValRat p (endpointPulseCoreRat N p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hten0 : (10 : ℚ) ^ (N + 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have h4q : (4 : ℚ) ≠ 0 := by norm_num
  have h5q : (5 : ℚ) ≠ 0 := by norm_num
  have h239q : (239 : ℚ) ≠ 0 := by norm_num
  have hfactor0 : (machinCancellationFactor p : ℚ) ≠ 0 :=
    machinCancellationFactor_ratCast_ne_zero_upperHalfPrime
      p hp (by omega) hp317
  have hnum0 : (4 : ℚ) * (machinCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero h4q hfactor0
  have hden0 : (5 : ℚ) ^ p * (239 : ℚ) ^ p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h5q) (pow_ne_zero _ h239q)
  have hfrac0 :
      (4 : ℚ) * (machinCancellationFactor p : ℚ) /
        ((5 : ℚ) ^ p * (239 : ℚ) ^ p) ≠ 0 :=
    div_ne_zero hnum0 hden0
  have hval10 : padicValRat p ((10 : ℚ) ^ (N + 2)) = 0 :=
    padicValRat_ten_pow_eq_zero_of_prime_gt_five
      (N + 2) p hp (by omega)
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_twelve_not_dvd_four p hp hpgt)
  have hvalFactor :
      padicValRat p (machinCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (machinCancellationFactor_not_dvd_upperHalfPrime
        p hp (by omega) hp317)
  have hval5 : padicValRat p (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_twelve_not_dvd_five p hp hpgt)
  have hval239 : padicValRat p (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_ne_239_not_dvd_239 p hp hp239)
  rw [endpointPulseCoreRat_eq_cancellationFactor,
    padicValRat.mul hten0 hfrac0,
    padicValRat.div hnum0 hden0,
    padicValRat.mul h4q hfactor0,
    padicValRat.mul (pow_ne_zero _ h5q) (pow_ne_zero _ h239q),
    padicValRat.pow h5q, padicValRat.pow h239q,
    hval10, hval4, hvalFactor, hval5, hval239]
  norm_num

lemma endpointPulseCoreRat_ne_zero
    (N p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hp317 : p ≠ 317) :
    endpointPulseCoreRat N p ≠ 0 := by
  have hten0 : (10 : ℚ) ^ (N + 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hfactor0 : (machinCancellationFactor p : ℚ) ≠ 0 :=
    machinCancellationFactor_ratCast_ne_zero_upperHalfPrime
      p hp hpgt hp317
  rw [endpointPulseCoreRat_eq_cancellationFactor]
  exact mul_ne_zero hten0
    (div_ne_zero (mul_ne_zero (by norm_num) hfactor0)
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num))))

lemma p_mul_sampledMachinValueRat_add_two_ne_zero
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpdef : p = 12 * N + 17) :
    (p : ℚ) * sampledMachinValueRat (N + 2) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [p_mul_sampledMachinValueRat_add_two_eq_core_add_regular N p hpdef]
  have hcore0 := endpointPulseCoreRat_ne_zero N p hp (by omega) hp317
  have hcoreVal :=
    padicValRat_endpointPulseCoreRat N p hp hpgt hp239 hp317
  have hcorr := padicValRat_p_mul_endpointPulseRegularRat_ge_one_or_zero
    N p hp hpgt hp239 hpdef
  by_cases hcorr0 : (p : ℚ) * endpointPulseRegularRat N = 0
  · simpa [hcorr0] using hcore0
  have hcorrVal :
      1 ≤ padicValRat p ((p : ℚ) * endpointPulseRegularRat N) :=
    hcorr.resolve_left hcorr0
  intro hzero
  have heq : (p : ℚ) * endpointPulseRegularRat N =
      -endpointPulseCoreRat N p := by linarith
  have hvaleq := congrArg (padicValRat p) heq
  rw [padicValRat.neg, hcoreVal] at hvaleq
  omega

/-- The full localized initial value has valuation zero after multiplication
by `p`; equivalently, its correction to the explicit core is divisible by
`p` in the local ring. -/
theorem padicValRat_p_mul_sampledMachinValueRat_add_two
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpdef : p = 12 * N + 17) :
    padicValRat p ((p : ℚ) * sampledMachinValueRat (N + 2)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [p_mul_sampledMachinValueRat_add_two_eq_core_add_regular N p hpdef]
  have hcoreVal :=
    padicValRat_endpointPulseCoreRat N p hp hpgt hp239 hp317
  have hcore0 := endpointPulseCoreRat_ne_zero N p hp (by omega) hp317
  have hcorr := padicValRat_p_mul_endpointPulseRegularRat_ge_one_or_zero
    N p hp hpgt hp239 hpdef
  by_cases hcorr0 : (p : ℚ) * endpointPulseRegularRat N = 0
  · simpa [hcorr0] using hcoreVal
  have hcorrVal :
      1 ≤ padicValRat p ((p : ℚ) * endpointPulseRegularRat N) :=
    hcorr.resolve_left hcorr0
  have hsum : endpointPulseCoreRat N p +
      (p : ℚ) * endpointPulseRegularRat N ≠ 0 := by
    rw [← p_mul_sampledMachinValueRat_add_two_eq_core_add_regular
      N p hpdef]
    exact p_mul_sampledMachinValueRat_add_two_ne_zero
      N p hp hpgt hp239 hp317 hpdef
  calc
    padicValRat p
        (endpointPulseCoreRat N p +
          (p : ℚ) * endpointPulseRegularRat N) =
        padicValRat p (endpointPulseCoreRat N p) :=
      padicValRat.add_eq_of_lt hsum hcore0 hcorr0 (by
        rw [hcoreVal]
        omega)
    _ = 0 := hcoreVal

/-- Initial class-five endpoint pulse: the sample at `N+2` has exact
valuation `-1`. -/
theorem padicValRat_sampledMachinValueRat_endpointPulse
    (N p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpdef : p = 12 * N + 17) :
    padicValRat p (sampledMachinValueRat (N + 2)) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hprod := padicValRat_p_mul_sampledMachinValueRat_add_two
    N p hp hpgt hp239 hp317 hpdef
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hprod0 := p_mul_sampledMachinValueRat_add_two_ne_zero
    N p hp hpgt hp239 hp317 hpdef
  have hy0 : sampledMachinValueRat (N + 2) ≠ 0 :=
    fun hzero => hprod0 (by simp [hzero])
  rw [padicValRat.mul hpq hy0, padicValRat.self hp.one_lt] at hprod
  omega

/-! ## Propagation through the endpoint-prime-free window -/

/-- Through offset `2*N`, a later base-5 exponent lies strictly between
`p` and `3*p`.  Divisibility would force the odd exponent to equal the
even number `2*p`. -/
lemma endpointPrime_not_dvd_future_five_exponent
    (N p u j : ℕ) (hpdef : p = 12 * N + 17)
    (hu : u ≤ 2 * N) (hj : j < 6) :
    ¬ p ∣ 12 * (N + 2 + u) + 5 + 2 * j := by
  intro hdvd
  have hp0 : 0 < p := by omega
  have hplt : p < 12 * (N + 2 + u) + 5 + 2 * j := by omega
  have hsubpos :
      0 < 12 * (N + 2 + u) + 5 + 2 * j - p := by omega
  have hdvdsub :
      p ∣ 12 * (N + 2 + u) + 5 + 2 * j - p :=
    Nat.dvd_sub hdvd (dvd_refl p)
  have hsublt :
      12 * (N + 2 + u) + 5 + 2 * j - p < 2 * p := by omega
  have heq : 12 * (N + 2 + u) + 5 + 2 * j - p = p :=
    eq_of_dvd_of_pos_of_lt_two_mul hp0 hsubpos hsublt hdvdsub
  omega

/-- The analogous exclusion for every later base-239 exponent. -/
lemma endpointPrime_not_dvd_future_239_exponent
    (N p u j : ℕ) (hpdef : p = 12 * N + 17)
    (hu : u ≤ 2 * N) (hj : j < 6) :
    ¬ p ∣ 12 * (N + 2 + u) + 7 + 2 * j := by
  intro hdvd
  have hp0 : 0 < p := by omega
  have hplt : p < 12 * (N + 2 + u) + 7 + 2 * j := by omega
  have hsubpos :
      0 < 12 * (N + 2 + u) + 7 + 2 * j - p := by omega
  have hdvdsub :
      p ∣ 12 * (N + 2 + u) + 7 + 2 * j - p :=
    Nat.dvd_sub hdvd (dvd_refl p)
  have hsublt :
      12 * (N + 2 + u) + 7 + 2 * j - p < 2 * p := by omega
  have heq : 12 * (N + 2 + u) + 7 + 2 * j - p = p :=
    eq_of_dvd_of_pos_of_lt_two_mul hp0 hsubpos hsublt hdvdsub
  omega

lemma padicValRat_future_baseFiveWindowTermRat_eq_zero
    (N p u j : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 17) (hu : u ≤ 2 * N) (hj : j < 6) :
    padicValRat p (baseFiveWindowTermRat (N + 2 + u) j) = 0 := by
  unfold baseFiveWindowTermRat
  exact padicValRat_signed_fraction_eq_zero
    p 16 5 (12 * (N + 2 + u) + 5 + 2 * j) j hp
    (prime_gt_twelve_not_dvd_sixteen p hp hpgt)
    (prime_gt_twelve_not_dvd_five p hp hpgt)
    (endpointPrime_not_dvd_future_five_exponent N p u j hpdef hu hj)
    (by norm_num) (by norm_num) (by omega)

lemma padicValRat_future_base239WindowTermRat_eq_zero
    (N p u j : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17)
    (hu : u ≤ 2 * N) (hj : j < 6) :
    padicValRat p (base239WindowTermRat (N + 2 + u) j) = 0 := by
  unfold base239WindowTermRat
  exact padicValRat_signed_fraction_eq_zero
    p 4 239 (12 * (N + 2 + u) + 7 + 2 * j) j hp
    (prime_gt_twelve_not_dvd_four p hp hpgt)
    (prime_ne_239_not_dvd_239 p hp hp239)
    (endpointPrime_not_dvd_future_239_exponent N p u j hpdef hu hj)
    (by norm_num) (by norm_num) (by omega)

/-- Each complete later twelve-term block is zero or `p`-integral. -/
lemma padicValRat_future_actualMachinBlockRat_nonneg_or_zero
    (N p u : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17)
    (hu : u ≤ 2 * N) :
    actualMachinBlockRat (N + 2 + u) = 0 ∨
      0 ≤ padicValRat p (actualMachinBlockRat (N + 2 + u)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℚ :=
    ∑ j ∈ range 6, baseFiveWindowTermRat (N + 2 + u) j
  let G : ℚ :=
    ∑ j ∈ range 6, base239WindowTermRat (N + 2 + u) j
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_future_baseFiveWindowTermRat_eq_zero
          N p u j hp hpgt hpdef hu (mem_range.1 hj)]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_future_base239WindowTermRat_eq_zero
          N p u j hp hpgt hp239 hpdef hu (mem_range.1 hj)]
      · exact hG0
  change F + G = 0 ∨ 0 ≤ padicValRat p (F + G)
  by_cases hzero : F + G = 0
  · exact Or.inl hzero
  · exact Or.inr
      (padicValRat_add_nonneg_of_each_nonneg p hp hF hG hzero)

/-- Every intervening scaled forcing is `p`-integral. -/
lemma padicValRat_future_sampledMachinForcingRat_nonneg
    (N p u : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17)
    (hu : u ≤ 2 * N) :
    0 ≤ padicValRat p (sampledMachinForcingRat (N + 2 + u)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hforce0 : sampledMachinForcingRat (N + 2 + u) ≠ 0 :=
    ne_of_gt (sampledMachinForcingRat_pos (N + 2 + u))
  have hblock0 : actualMachinBlockRat (N + 2 + u) ≠ 0 := by
    intro hzero
    apply hforce0
    rw [sampledMachinForcingRat_eq_actualMachinBlockRat, hzero]
    ring
  have hblockVal :
      0 ≤ padicValRat p (actualMachinBlockRat (N + 2 + u)) :=
    (padicValRat_future_actualMachinBlockRat_nonneg_or_zero
      N p u hp hpgt hp239 hpdef hu).resolve_left hblock0
  have hten0 : (10 : ℚ) ^ (N + 2 + u + 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have htenVal :
      padicValRat p ((10 : ℚ) ^ (N + 2 + u + 1)) = 0 :=
    padicValRat_ten_pow_eq_zero_of_prime_gt_five
      (N + 2 + u + 1) p hp (by omega)
  rw [sampledMachinForcingRat_eq_actualMachinBlockRat,
    padicValRat.mul hten0 hblock0, htenVal]
  simpa using hblockVal

/-- The complete weighted intervening forcing accumulation is `p`-integral
through the endpoint pulse range. -/
lemma padicValRat_future_accumulation_nonneg
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17)
    (ht : t ≤ 2 * N + 1) :
    0 ≤ padicValRat p
      (sampledMachinForcingAccumulationRat (N + 2) t) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hzero :
      sampledMachinForcingAccumulationRat (N + 2) t = 0
  · simp [hzero]
  · rw [sampledMachinForcingAccumulationRat]
    apply padicValRat_sum_nonneg hp
    · intro u hu
      have hut : u < t := mem_range.1 hu
      have huN : u ≤ 2 * N := by omega
      have hpow0 : (10 : ℚ) ^ (t - 1 - u) ≠ 0 :=
        pow_ne_zero _ (by norm_num)
      have hforce0 : sampledMachinForcingRat (N + 2 + u) ≠ 0 :=
        ne_of_gt (sampledMachinForcingRat_pos (N + 2 + u))
      have hpowVal :
          padicValRat p ((10 : ℚ) ^ (t - 1 - u)) = 0 :=
        padicValRat_ten_pow_eq_zero_of_prime_gt_five
          (t - 1 - u) p hp (by omega)
      rw [padicValRat.mul hpow0 hforce0, hpowVal]
      simpa using padicValRat_future_sampledMachinForcingRat_nonneg
        N p u hp hpgt hp239 hpdef huN
    · simpa [sampledMachinForcingAccumulationRat] using hzero

/-- The correction to the transported explicit core.  Both summands carry
an explicit factor `p` in the local ring. -/
def endpointPulseCorrectionRat (N p t : ℕ) : ℚ :=
  (10 : ℚ) ^ t * ((p : ℚ) * endpointPulseRegularRat N)
    + (p : ℚ) * sampledMachinForcingAccumulationRat (N + 2) t

/-- Exact transported endpoint-pulse decomposition. -/
theorem p_mul_sampledMachinValueRat_endpointPulse_add_eq
    (N p t : ℕ) (hpdef : p = 12 * N + 17) :
    (p : ℚ) * sampledMachinValueRat (N + 2 + t) =
      (10 : ℚ) ^ t * endpointPulseCoreRat N p
        + endpointPulseCorrectionRat N p t := by
  rw [sampledMachinValueRat_add (N + 2) t]
  calc
    (p : ℚ) *
        ((10 : ℚ) ^ t * sampledMachinValueRat (N + 2) +
          sampledMachinForcingAccumulationRat (N + 2) t) =
        (10 : ℚ) ^ t *
            ((p : ℚ) * sampledMachinValueRat (N + 2)) +
          (p : ℚ) *
            sampledMachinForcingAccumulationRat (N + 2) t := by ring
    _ = (10 : ℚ) ^ t *
            (endpointPulseCoreRat N p +
              (p : ℚ) * endpointPulseRegularRat N) +
          (p : ℚ) *
            sampledMachinForcingAccumulationRat (N + 2) t := by
      rw [p_mul_sampledMachinValueRat_add_two_eq_core_add_regular
        N p hpdef]
    _ = (10 : ℚ) ^ t * endpointPulseCoreRat N p
          + endpointPulseCorrectionRat N p t := by
      unfold endpointPulseCorrectionRat
      ring

/-- Multiplication by a nonzero `p`-adic unit preserves being zero or
having valuation at least one. -/
lemma padicValRat_unit_mul_ge_one_or_zero
    (p : ℕ) (hp : p.Prime) {a q : ℚ}
    (ha0 : a ≠ 0) (haval : padicValRat p a = 0)
    (hq : q = 0 ∨ 1 ≤ padicValRat p q) :
    a * q = 0 ∨ 1 ≤ padicValRat p (a * q) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hq with rfl | hqval
  · exact Or.inl (by ring)
  by_cases hq0 : q = 0
  · exact Or.inl (by simp [hq0])
  refine Or.inr ?_
  rw [padicValRat.mul ha0 hq0, haval]
  simpa using hqval

/-- Two locally `p`-divisible quantities have locally `p`-divisible sum
whenever the sum is nonzero. -/
lemma padicValRat_add_ge_one_of_each_ge_one
    (p : ℕ) (hp : p.Prime) {q r : ℚ}
    (hq : q = 0 ∨ 1 ≤ padicValRat p q)
    (hr : r = 0 ∨ 1 ≤ padicValRat p r)
    (hqr : q + r ≠ 0) :
    1 ≤ padicValRat p (q + r) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hq with rfl | hqval
  · simpa using hr.resolve_left (by simpa using hqr)
  rcases hr with rfl | hrval
  · simpa using hqval
  exact le_trans (le_min hqval hrval)
    (padicValRat.min_le_padicValRat_add hqr)

/-- The transported correction vanishes or has valuation at least one. -/
theorem padicValRat_endpointPulseCorrectionRat_ge_one_or_zero
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17)
    (ht : t ≤ 2 * N + 1) :
    endpointPulseCorrectionRat N p t = 0 ∨
      1 ≤ padicValRat p (endpointPulseCorrectionRat N p t) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hten0 : (10 : ℚ) ^ t ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have htenVal : padicValRat p ((10 : ℚ) ^ t) = 0 :=
    padicValRat_ten_pow_eq_zero_of_prime_gt_five t p hp (by omega)
  have hseed := padicValRat_unit_mul_ge_one_or_zero p hp hten0 htenVal
    (padicValRat_p_mul_endpointPulseRegularRat_ge_one_or_zero
      N p hp hpgt hp239 hpdef)
  have haccVal := padicValRat_future_accumulation_nonneg
    N p t hp hpgt hp239 hpdef ht
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hacc :
      (p : ℚ) * sampledMachinForcingAccumulationRat (N + 2) t = 0 ∨
        1 ≤ padicValRat p
          ((p : ℚ) * sampledMachinForcingAccumulationRat (N + 2) t) := by
    by_cases hacc0 : sampledMachinForcingAccumulationRat (N + 2) t = 0
    · exact Or.inl (by simp [hacc0])
    · refine Or.inr ?_
      rw [padicValRat.mul hpq hacc0, padicValRat.self hp.one_lt]
      omega
  unfold endpointPulseCorrectionRat
  by_cases hzero :
      (10 : ℚ) ^ t * ((p : ℚ) * endpointPulseRegularRat N)
          + (p : ℚ) *
            sampledMachinForcingAccumulationRat (N + 2) t = 0
  · exact Or.inl hzero
  · exact Or.inr
      (padicValRat_add_ge_one_of_each_ge_one p hp hseed hacc hzero)

/-- Inspectable localized propagation statement: the exact transported
core plus a correction divisible by `p` in the local ring. -/
theorem endpointPulse_localized_propagation
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hpdef : p = 12 * N + 17)
    (ht : t ≤ 2 * N + 1) :
    (p : ℚ) * sampledMachinValueRat (N + 2 + t) =
        (10 : ℚ) ^ t * endpointPulseCoreRat N p
          + endpointPulseCorrectionRat N p t
      ∧
    (endpointPulseCorrectionRat N p t = 0 ∨
      1 ≤ padicValRat p (endpointPulseCorrectionRat N p t)) := by
  exact ⟨p_mul_sampledMachinValueRat_endpointPulse_add_eq N p t hpdef,
    padicValRat_endpointPulseCorrectionRat_ge_one_or_zero
      N p t hp hpgt hp239 hpdef ht⟩

lemma endpointPulseTransportedCore_ne_zero
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp317 : p ≠ 317) :
    (10 : ℚ) ^ t * endpointPulseCoreRat N p ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (endpointPulseCoreRat_ne_zero N p hp (by omega) hp317)

lemma padicValRat_endpointPulseTransportedCore
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317) :
    padicValRat p
      ((10 : ℚ) ^ t * endpointPulseCoreRat N p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hten0 : (10 : ℚ) ^ t ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hcore0 := endpointPulseCoreRat_ne_zero
    N p hp (by omega) hp317
  have htenVal : padicValRat p ((10 : ℚ) ^ t) = 0 :=
    padicValRat_ten_pow_eq_zero_of_prime_gt_five t p hp (by omega)
  rw [padicValRat.mul hten0 hcore0, htenVal,
    padicValRat_endpointPulseCoreRat N p hp hpgt hp239 hp317]
  norm_num

/-- The transported core cannot be canceled by its locally
`p`-divisible correction. -/
theorem p_mul_sampledMachinValueRat_endpointPulse_add_ne_zero
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpdef : p = 12 * N + 17) (ht : t ≤ 2 * N + 1) :
    (p : ℚ) * sampledMachinValueRat (N + 2 + t) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [p_mul_sampledMachinValueRat_endpointPulse_add_eq N p t hpdef]
  have hlead0 := endpointPulseTransportedCore_ne_zero
    N p t hp hpgt hp317
  have hleadVal := padicValRat_endpointPulseTransportedCore
    N p t hp hpgt hp239 hp317
  have hcorr := padicValRat_endpointPulseCorrectionRat_ge_one_or_zero
    N p t hp hpgt hp239 hpdef ht
  by_cases hcorr0 : endpointPulseCorrectionRat N p t = 0
  · simpa [hcorr0] using hlead0
  have hcorrVal :
      1 ≤ padicValRat p (endpointPulseCorrectionRat N p t) :=
    hcorr.resolve_left hcorr0
  intro hzero
  have heq : endpointPulseCorrectionRat N p t =
      -((10 : ℚ) ^ t * endpointPulseCoreRat N p) := by
    linarith
  have hvaleq := congrArg (padicValRat p) heq
  rw [padicValRat.neg, hleadVal] at hvaleq
  omega

/-- After multiplication by `p`, the entire propagated pulse remains a
`p`-adic unit through offset `2*N+1`. -/
theorem padicValRat_p_mul_sampledMachinValueRat_endpointPulse_add
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpdef : p = 12 * N + 17) (ht : t ≤ 2 * N + 1) :
    padicValRat p
      ((p : ℚ) * sampledMachinValueRat (N + 2 + t)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [p_mul_sampledMachinValueRat_endpointPulse_add_eq N p t hpdef]
  have hlead0 := endpointPulseTransportedCore_ne_zero
    N p t hp hpgt hp317
  have hleadVal := padicValRat_endpointPulseTransportedCore
    N p t hp hpgt hp239 hp317
  have hcorr := padicValRat_endpointPulseCorrectionRat_ge_one_or_zero
    N p t hp hpgt hp239 hpdef ht
  by_cases hcorr0 : endpointPulseCorrectionRat N p t = 0
  · simpa [hcorr0] using hleadVal
  have hcorrVal :
      1 ≤ padicValRat p (endpointPulseCorrectionRat N p t) :=
    hcorr.resolve_left hcorr0
  have hsum :
      (10 : ℚ) ^ t * endpointPulseCoreRat N p +
          endpointPulseCorrectionRat N p t ≠ 0 := by
    rw [← p_mul_sampledMachinValueRat_endpointPulse_add_eq
      N p t hpdef]
    exact p_mul_sampledMachinValueRat_endpointPulse_add_ne_zero
      N p t hp hpgt hp239 hp317 hpdef ht
  calc
    padicValRat p
        ((10 : ℚ) ^ t * endpointPulseCoreRat N p +
          endpointPulseCorrectionRat N p t) =
        padicValRat p
          ((10 : ℚ) ^ t * endpointPulseCoreRat N p) :=
      padicValRat.add_eq_of_lt hsum hlead0 hcorr0 (by
        rw [hleadVal]
        omega)
    _ = 0 := hleadVal

/-- Full class-five endpoint pulse propagation: every sample through the
stated window has exact valuation `-1` at the endpoint prime. -/
theorem padicValRat_sampledMachinValueRat_endpointPulse_add
    (N p t : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpdef : p = 12 * N + 17) (ht : t ≤ 2 * N + 1) :
    padicValRat p (sampledMachinValueRat (N + 2 + t)) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hprod :=
    padicValRat_p_mul_sampledMachinValueRat_endpointPulse_add
      N p t hp hpgt hp239 hp317 hpdef ht
  have hprod0 :=
    p_mul_sampledMachinValueRat_endpointPulse_add_ne_zero
      N p t hp hpgt hp239 hp317 hpdef ht
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hy0 : sampledMachinValueRat (N + 2 + t) ≠ 0 :=
    fun hzero => hprod0 (by simp [hzero])
  rw [padicValRat.mul hpq hy0, padicValRat.self hp.one_lt] at hprod
  omega

#print axioms p_mul_sampledMachinValueRat_add_two_eq_core_add_regular
#print axioms endpointPulseCore_zmod_eq_expected
#print axioms endpointPulse_expected_zmod_ne_zero
#print axioms padicValRat_sampledMachinValueRat_endpointPulse
#print axioms endpointPulse_localized_propagation
#print axioms padicValRat_sampledMachinValueRat_endpointPulse_add

end Theory.PiDigits.MachinEndpointPulse
