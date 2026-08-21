import TheoryLib.PiQuantitativeBlockHitting.T50T50MachinSeedLowerBandPrimeSurvival

/-!
# T51: third-band prime survival in the fixed Machin seed

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Put `d = 12*N+15`.  This file treats primes in the third fixed-seed band

`5*p <= d` and `d < 7*p`.

The only common odd Taylor exponents divisible by such a prime are
`p`, `3*p`, and `5*p`.  Their exact localized coefficient is

`38279241713339684 / 12184551018734375`,

whose odd numerator prime factors are exactly
`19, 37, 79, 48049, 3586217`.  Outside those genuine exceptions and the
Machin base `239`, the seed has exact `p`-adic valuation `-1`.

If the extra base-239 endpoint is singular, the band forces
`12*N+17 = 7*p`, hence `p % 12 = 11`.  The endpoint-adjusted coefficient
has numerator prime factors
`2, 3, 13, 29, 8429, 35533, 470668789`; none can equal a prime that is
`11` modulo `12`.  Thus the final theorem needs no endpoint hypothesis.

This is local rational arithmetic.  It does not control the complementary
CRT phase or imply a decimal-cylinder hit, density, normality, or the
every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinSeedThirdBandPrimeSurvival

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinFixedModulusTelescoping
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival
open Theory.PiDigits.MachinSeedLowerBandPrimeSurvival

/-- The Taylor index whose odd exponent is five times `2*k+1`. -/
def thirdBandThirdIndex (k : ℕ) : ℕ :=
  5 * k + 2

/-- Integer factor obtained after combining the common singular exponents
`p`, `3*p`, and `5*p`, apart from `4 * (-1)^k`. -/
def thirdBandCancellationFactor (p : ℕ) : ℤ :=
  5 * lowerBandCancellationFactor p *
      (5 : ℤ) ^ (2 * p) * (239 : ℤ) ^ (2 * p) +
    3 * machinCancellationFactor (5 * p)

/-- Fermat reduction of `thirdBandCancellationFactor p` modulo `p`. -/
def thirdBandFixedResidue : ℤ :=
  5 * lowerBandFixedResidue * 5 ^ 2 * 239 ^ 2 +
    3 * (4 * 239 ^ 5 - 5 ^ 5)

theorem thirdBandFixedResidue_eq_factorization :
    thirdBandFixedResidue =
      3 * 19 * 37 * 79 * 48049 * 3586217 := by
  norm_num [thirdBandFixedResidue, lowerBandFixedResidue]

/-- Exact reduced rational coefficient of the three common singular pairs. -/
theorem thirdBand_full_coefficient_eq :
    (4 : ℚ) * (thirdBandFixedResidue : ℚ) /
        ((15 : ℚ) * 5 ^ 5 * 239 ^ 5) =
      38279241713339684 / 12184551018734375 := by
  norm_num [thirdBandFixedResidue, lowerBandFixedResidue]

theorem thirdBand_full_coefficient_numerator_eq_factorization :
    38279241713339684 =
      2 ^ 2 * 19 * 37 * 79 * 48049 * 3586217 := by
  norm_num

theorem thirdBand_fixed_exception_primes :
    Nat.Prime 19 ∧ Nat.Prime 37 ∧ Nat.Prime 79 ∧
      Nat.Prime 48049 ∧ Nat.Prime 3586217 := by
  norm_num

/-- Fermat's theorem reduces the variable third-band factor to the fixed
integer residue. -/
theorem thirdBandCancellationFactor_cast_zmod
    (p : ℕ) (hp : p.Prime) :
    (thirdBandCancellationFactor p : ZMod p) = thirdBandFixedResidue := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [thirdBandCancellationFactor, thirdBandFixedResidue,
    machinCancellationFactor, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_pow]
  rw [lowerBandCancellationFactor_cast_zmod p hp]
  rw [show 2 * p = p * 2 by omega, show 5 * p = p * 5 by omega]
  simp only [pow_mul]
  simp only [ZMod.pow_card]

lemma prime_not_dvd_thirdBandFixedResidue
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217) :
    ¬ (p : ℤ) ∣ thirdBandFixedResidue := by
  intro hdvdInt
  rw [thirdBandFixedResidue_eq_factorization] at hdvdInt
  have hdvd : p ∣ 3 * (19 * (37 * (79 * (48049 * 3586217)))) := by
    exact_mod_cast hdvdInt
  rcases hp.dvd_mul.mp hdvd with h3 | hrest
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  rcases hp.dvd_mul.mp hrest with h19 | hrest
  · rcases (Nat.dvd_prime thirdBand_fixed_exception_primes.1).mp h19 with h1 | heq
    · exact hp.ne_one h1
    · exact hp19 heq
  rcases hp.dvd_mul.mp hrest with h37 | hrest
  · rcases (Nat.dvd_prime thirdBand_fixed_exception_primes.2.1).mp h37 with h1 | heq
    · exact hp.ne_one h1
    · exact hp37 heq
  rcases hp.dvd_mul.mp hrest with h79 | hrest
  · rcases (Nat.dvd_prime thirdBand_fixed_exception_primes.2.2.1).mp h79 with h1 | heq
    · exact hp.ne_one h1
    · exact hp79 heq
  rcases hp.dvd_mul.mp hrest with h48049 | h3586217
  · rcases (Nat.dvd_prime thirdBand_fixed_exception_primes.2.2.2.1).mp
        h48049 with h1 | heq
    · exact hp.ne_one h1
    · exact hp48049 heq
  · rcases (Nat.dvd_prime thirdBand_fixed_exception_primes.2.2.2.2).mp
        h3586217 with h1 | heq
    · exact hp.ne_one h1
    · exact hp3586217 heq

lemma thirdBandCancellationFactor_not_dvd
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217) :
    ¬ (p : ℤ) ∣ thirdBandCancellationFactor p := by
  intro hdvd
  have hz : (thirdBandCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (thirdBandCancellationFactor p) p).2 hdvd
  rw [thirdBandCancellationFactor_cast_zmod p hp] at hz
  have hdvdFixed : (p : ℤ) ∣ thirdBandFixedResidue :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd thirdBandFixedResidue p).mp hz
  exact prime_not_dvd_thirdBandFixedResidue
    p hp hpgt hp19 hp37 hp79 hp48049 hp3586217 hdvdFixed

lemma thirdBandCancellationFactor_ratCast_ne_zero
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217) :
    (thirdBandCancellationFactor p : ℚ) ≠ 0 := by
  have hz : thirdBandCancellationFactor p ≠ 0 := by
    intro hzero
    apply thirdBandCancellationFactor_not_dvd
      p hp hpgt hp19 hp37 hp79 hp48049 hp3586217
    rw [hzero]
    exact dvd_zero _
  exact_mod_cast hz

/-- The six common terms at exponents `p`, `3*p`, and `5*p`. -/
def seedThirdBandSingularBlockRat (k : ℕ) : ℚ :=
  seedLowerBandSingularBlockRat k +
    (seedFiveTermRat (thirdBandThirdIndex k) +
      seed239TermRat (thirdBandThirdIndex k))

/-- All common terms after deleting the three third-band singular indices,
together with the extra base-239 endpoint. -/
def seedThirdBandRegularBlockRat (N k : ℕ) : ℚ :=
  ∑ j ∈ (((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k)).erase (thirdBandThirdIndex k),
      seedFiveTermRat j
    + ∑ j ∈ (((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k)).erase (thirdBandThirdIndex k),
      seed239TermRat j
    + seed239TermRat (seedCommonTermCount N)

lemma thirdBand_third_sign (k : ℕ) :
    (-1 : ℚ) ^ (thirdBandThirdIndex k) = (-1 : ℚ) ^ k := by
  unfold thirdBandThirdIndex
  rw [show 5 * k + 2 = 2 * (2 * k + 1) + k by omega,
    pow_add, pow_mul]
  norm_num

/-- Exact combination of the six common singular terms. -/
theorem seedThirdBandSingularBlockRat_eq_fraction
    (p k : ℕ) (hpdef : p = 2 * k + 1) :
    seedThirdBandSingularBlockRat k =
      (4 * (-1 : ℚ) ^ k * (thirdBandCancellationFactor p : ℚ)) /
        ((15 : ℚ) * (p : ℚ) * 5 ^ (5 * p) * 239 ^ (5 * p)) := by
  have hthirddef :
      5 * p = 2 * thirdBandThirdIndex k + 1 := by
    simp [thirdBandThirdIndex]
    omega
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  unfold seedThirdBandSingularBlockRat
  rw [seed_singular_pair_eq (5 * p) (thirdBandThirdIndex k) hthirddef]
  unfold interiorSingularPairRat thirdBandCancellationFactor
  rw [seedLowerBandSingularBlockRat_eq_fraction p k hpdef,
    thirdBand_third_sign]
  push_cast
  have hpow5 : (5 : ℚ) ^ (5 * p) = 5 ^ (3 * p) * 5 ^ (2 * p) := by
    rw [show 5 * p = 3 * p + 2 * p by omega, pow_add]
  have hpow239 : (239 : ℚ) ^ (5 * p) =
      239 ^ (3 * p) * 239 ^ (2 * p) := by
    rw [show 5 * p = 3 * p + 2 * p by omega, pow_add]
  simp_rw [hpow5, hpow239]
  field_simp [hpq]
  ring

/-- Exact decomposition of the unscaled fixed seed into its third-band
regular and singular blocks. -/
theorem machinLowerRat_seed_eq_thirdBandRegular_add_singular
    (N k : ℕ)
    (hk : k < seedCommonTermCount N)
    (hsecond : lowerBandSecondIndex k < seedCommonTermCount N)
    (hthird : thirdBandThirdIndex k < seedCommonTermCount N) :
    machinLowerRat (3 * (N + 1)) =
      seedThirdBandRegularBlockRat N k +
        seedThirdBandSingularBlockRat k := by
  have hthirdmem :
      thirdBandThirdIndex k ∈
        ((range (seedCommonTermCount N)).erase k).erase
          (lowerBandSecondIndex k) := by
    apply mem_erase.mpr
    constructor
    · simp [thirdBandThirdIndex, lowerBandSecondIndex]
      omega
    apply mem_erase.mpr
    constructor
    · simp [thirdBandThirdIndex]
      omega
    exact mem_range.2 hthird
  have hfiveThird :=
    sum_erase_add
      (((range (seedCommonTermCount N)).erase k).erase
        (lowerBandSecondIndex k)) seedFiveTermRat hthirdmem
  have h239Third :=
    sum_erase_add
      (((range (seedCommonTermCount N)).erase k).erase
        (lowerBandSecondIndex k)) seed239TermRat hthirdmem
  rw [machinLowerRat_seed_eq_lowerBandRegular_add_singular N k hk hsecond]
  unfold seedLowerBandRegularBlockRat seedThirdBandRegularBlockRat
  unfold seedThirdBandSingularBlockRat
  rw [← hfiveThird, ← h239Third]
  ring

/-- Below `7*p`, an odd multiple of `p` can only have odd cofactor
`1`, `3`, or `5`; all three corresponding indices were erased. -/
lemma thirdBandPrime_not_dvd_regular_common_exponent
    (N k p j : ℕ) (hpgt : 7 < p)
    (hpdef : p = 2 * k + 1)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hj : j ∈ (((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k)).erase (thirdBandThirdIndex k)) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hj2 : j ∈ ((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k) := mem_of_mem_erase hj
  have hj1 : j ∈ (range (seedCommonTermCount N)).erase k :=
    mem_of_mem_erase hj2
  have hjlt : j < seedCommonTermCount N :=
    mem_range.1 (mem_of_mem_erase hj1)
  have hjne : j ≠ k := ne_of_mem_erase hj1
  have hjsecondne : j ≠ lowerBandSecondIndex k := ne_of_mem_erase hj2
  have hjthirdne : j ≠ thirdBandThirdIndex k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 7 * p := by
    simp [seedCommonTermCount] at hjlt
    omega
  rcases hdvd with ⟨m, hm⟩
  have hp0 : 0 < p := by omega
  have hmul : p * m < p * 7 := by
    calc
      p * m = 2 * j + 1 := hm.symm
      _ < 7 * p := hexplt
      _ = p * 7 := by omega
  have hm7 : m < 7 := (Nat.mul_lt_mul_left hp0).mp hmul
  have hmpos : 0 < m := by
    by_contra hnot
    have hmzero : m = 0 := by omega
    subst m
    simp at hm
  interval_cases m
  all_goals simp_all [lowerBandSecondIndex, thirdBandThirdIndex]
  all_goals omega

/-- The six-term singular block has exact valuation `-1` outside the five
genuine coefficient exceptions. -/
theorem padicValRat_seedThirdBandSingularBlockRat
    (p k : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217)
    (hpdef : p = 2 * k + 1) :
    padicValRat p (seedThirdBandSingularBlockRat k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h15q : (15 : ℚ) ≠ 0 := by norm_num
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4q : (4 : ℚ) ≠ 0 := by norm_num
  have h5q : (5 : ℚ) ≠ 0 := by norm_num
  have h239q : (239 : ℚ) ≠ 0 := by norm_num
  have hsign0 : (-1 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfactor0 : (thirdBandCancellationFactor p : ℚ) ≠ 0 :=
    thirdBandCancellationFactor_ratCast_ne_zero
      p hp hpgt hp19 hp37 hp79 hp48049 hp3586217
  have hnum0 :
      4 * (-1 : ℚ) ^ k * (thirdBandCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4q hsign0) hfactor0
  have h5pow0 : (5 : ℚ) ^ (5 * p) ≠ 0 := pow_ne_zero _ h5q
  have h239pow0 : (239 : ℚ) ^ (5 * p) ≠ 0 := pow_ne_zero _ h239q
  have hden0 :
      (15 : ℚ) * (p : ℚ) * 5 ^ (5 * p) * 239 ^ (5 * p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h15q hpq) h5pow0) h239pow0
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp (by omega))
  have hvalSign : padicValRat p ((-1 : ℚ) ^ k) = 0 := by
    rw [padicValRat.pow (by norm_num), padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat p (thirdBandCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (thirdBandCancellationFactor_not_dvd
        p hp hpgt hp19 hp37 hp79 hp48049 hp3586217)
  have hval15 : padicValRat p (15 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_fifteen p hp (by omega))
  have hval5 : padicValRat p (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_five p hp (by omega))
  have hval239 : padicValRat p (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_ne_239_not_dvd_239 p hp hp239)
  rw [seedThirdBandSingularBlockRat_eq_fraction p k hpdef,
    padicValRat.div hnum0 hden0,
    padicValRat.mul (mul_ne_zero h4q hsign0) hfactor0,
    padicValRat.mul h4q hsign0,
    padicValRat.mul (mul_ne_zero (mul_ne_zero h15q hpq) h5pow0) h239pow0,
    padicValRat.mul (mul_ne_zero h15q hpq) h5pow0,
    padicValRat.mul h15q hpq,
    padicValRat.self hp.one_lt,
    padicValRat.pow h5q, padicValRat.pow h239q,
    hval4, hvalSign, hvalFactor, hval15, hval5, hval239]
  norm_num

/-- Every term outside the three common singular exponents is `p`-integral;
the possible endpoint divisor is explicit. -/
lemma padicValRat_seedThirdBandRegularBlockRat_nonneg
    (N k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hpdef : p = 2 * k + 1)
    (hendpoint : ¬ p ∣ 12 * N + 17)
    (hregular : seedThirdBandRegularBlockRat N k ≠ 0) :
    0 ≤ padicValRat p (seedThirdBandRegularBlockRat N k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let A := (((range (seedCommonTermCount N)).erase k).erase
    (lowerBandSecondIndex k)).erase (thirdBandThirdIndex k)
  let F : ℚ := ∑ j ∈ A, seedFiveTermRat j
  let G : ℚ := ∑ j ∈ A, seed239TermRat j
  let E : ℚ := seed239TermRat (seedCommonTermCount N)
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seedFiveTermRat_eq_zero p j hp (by omega)
          (thirdBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdUpper (by simpa [A] using hj))]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seed239TermRat_eq_zero p j hp hp239 (by omega)
          (thirdBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdUpper (by simpa [A] using hj))]
      · exact hG0
  have hendpoint' : ¬ p ∣ 2 * seedCommonTermCount N + 1 := by
    have heq : 2 * seedCommonTermCount N + 1 = 12 * N + 17 := by
      simp [seedCommonTermCount]
      omega
    rw [heq]
    exact hendpoint
  have hEval : padicValRat p E = 0 :=
    padicValRat_seed239TermRat_eq_zero
      p (seedCommonTermCount N) hp hp239 (by omega) hendpoint'
  have hE : E = 0 ∨ 0 ≤ padicValRat p E := Or.inr (by rw [hEval])
  have hFG : F + G = 0 ∨ 0 ≤ padicValRat p (F + G) := by
    by_cases hFG0 : F + G = 0
    · exact Or.inl hFG0
    · exact Or.inr
        (padicValRat_add_nonneg_of_each_nonneg p hp hF hG hFG0)
  change 0 ≤ padicValRat p ((F + G) + E)
  have hFGE : (F + G) + E ≠ 0 := by
    simpa [F, G, E, A, seedThirdBandRegularBlockRat] using hregular
  exact padicValRat_add_nonneg_of_each_nonneg p hp hFG hE hFGE

theorem padicValRat_machinLowerRat_seed_thirdBandPrime
    (N k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217)
    (h5pLower : 5 * p ≤ 12 * N + 15)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hpdef : p = 2 * k + 1)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValRat p (machinLowerRat (3 * (N + 1))) = -1 := by
  have hk : k < seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  have hsecond : lowerBandSecondIndex k < seedCommonTermCount N := by
    simp [lowerBandSecondIndex, seedCommonTermCount]
    omega
  have hthird : thirdBandThirdIndex k < seedCommonTermCount N := by
    simp [thirdBandThirdIndex, seedCommonTermCount]
    omega
  rw [machinLowerRat_seed_eq_thirdBandRegular_add_singular
    N k hk hsecond hthird]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_seedThirdBandSingularBlockRat
      p k hp hpgt hp239 hp19 hp37 hp79 hp48049 hp3586217 hpdef
  · by_cases hregular : seedThirdBandRegularBlockRat N k = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_seedThirdBandRegularBlockRat_nonneg
          N k p hp hpgt hp239 hdUpper hpdef hendpoint hregular)

/-- Main third-band valuation theorem with the endpoint kept explicit. -/
theorem padicValRat_sampledMachinValueRat_thirdBandPrime
    (N p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217)
    (h5pLower : 5 * p ≤ 12 * N + 15)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  have hpne2 : p ≠ 2 := by omega
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two hpne2
  have hpdef : p = 2 * k + 1 := by omega
  have hblock := padicValRat_machinLowerRat_seed_thirdBandPrime
    N k p hp hpgt hp239 hp19 hp37 hp79 hp48049 hp3586217
      h5pLower hdUpper hpdef hendpoint
  have hblock0 : machinLowerRat (3 * (N + 1)) ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  letI : Fact p.Prime := ⟨hp⟩
  unfold sampledMachinValueRat
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_ten_pow_eq_zero_of_prime_gt_five (N + 1) p hp (by omega),
    hblock]
  norm_num

theorem thirdBandPrime_dvd_sampledMachinValueRat_den
    (N p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217)
    (h5pLower : 5 * p ≤ 12 * N + 15)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    p ∣ (sampledMachinValueRat (N + 1)).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_sampledMachinValueRat_thirdBandPrime
    N p hp hpgt hp239 hp19 hp37 hp79 hp48049 hp3586217
      h5pLower hdUpper hendpoint]
  norm_num

theorem padicValNat_sampledMachinValueRat_den_thirdBandPrime
    (N p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217)
    (h5pLower : 5 * p ≤ 12 * N + 15)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_sampledMachinValueRat_thirdBandPrime
      N p hp hpgt hp239 hp19 hp37 hp79 hp48049 hp3586217
        h5pLower hdUpper hendpoint
  have hden : p ∣ q.den :=
    thirdBandPrime_dvd_sampledMachinValueRat_den
      N p hp hpgt hp239 hp19 hp37 hp79 hp48049 hp3586217
        h5pLower hdUpper hendpoint
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

/-! ## Closing the extra endpoint -/

/-- In the third band, endpoint divisibility forces the endpoint exponent
to be exactly `7*p`. -/
lemma endpoint_divisor_eq_seven_mul
    (N p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (h5pLower : 5 * p ≤ 12 * N + 15)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hendpoint : p ∣ 12 * N + 17) :
    12 * N + 17 = 7 * p := by
  rcases hendpoint with ⟨m, hm⟩
  have hp0 : 0 < p := by omega
  have hmul : p * m < p * 8 := by omega
  have hm8 : m < 8 := (Nat.mul_lt_mul_left hp0).mp hmul
  have hpne2 : p ≠ 2 := by omega
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two hpne2
  interval_cases m <;> omega

/-- The endpoint equality forces the endpoint prime into residue class
`11 (mod 12)`. -/
lemma endpointThirdBandPrime_mod_twelve
    (N p : ℕ) (hendpointEq : 12 * N + 17 = 7 * p) :
    p % 12 = 11 := by
  omega

/-- Integer factor after adding the singular base-239 endpoint at `7*p`. -/
def endpointThirdBandCancellationFactor (p : ℕ) : ℤ :=
  7 * thirdBandCancellationFactor p * (239 : ℤ) ^ (2 * p) +
    15 * (5 : ℤ) ^ (5 * p)

def endpointThirdBandFixedResidue : ℤ :=
  7 * thirdBandFixedResidue * 239 ^ 2 + 15 * 5 ^ 5

theorem endpointThirdBandFixedResidue_eq_factorization :
    endpointThirdBandFixedResidue =
      2 ^ 3 * 3 ^ 3 * 13 * 29 * 8429 * 35533 * 470668789 := by
  norm_num [endpointThirdBandFixedResidue, thirdBandFixedResidue,
    lowerBandFixedResidue]

theorem endpointThirdBand_full_coefficient_eq :
    (4 : ℚ) * (endpointThirdBandFixedResidue : ℚ) /
        ((105 : ℚ) * 5 ^ 5 * 239 ^ 7) =
      15305839961353732690848 / 4871956171187883640625 := by
  norm_num [endpointThirdBandFixedResidue, thirdBandFixedResidue,
    lowerBandFixedResidue]

theorem endpointThirdBand_full_coefficient_numerator_eq_factorization :
    15305839961353732690848 =
      2 ^ 5 * 3 ^ 2 * 13 * 29 * 8429 * 35533 * 470668789 := by
  norm_num

theorem endpointThirdBand_fixed_factor_primes :
    Nat.Prime 13 ∧ Nat.Prime 29 ∧ Nat.Prime 8429 ∧
      Nat.Prime 35533 ∧ Nat.Prime 470668789 := by
  norm_num

theorem endpointThirdBandCancellationFactor_cast_zmod
    (p : ℕ) (hp : p.Prime) :
    (endpointThirdBandCancellationFactor p : ZMod p) =
      endpointThirdBandFixedResidue := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [endpointThirdBandCancellationFactor,
    endpointThirdBandFixedResidue, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_pow]
  rw [thirdBandCancellationFactor_cast_zmod p hp]
  rw [show 2 * p = p * 2 by omega, show 5 * p = p * 5 by omega]
  simp only [pow_mul]
  rw [ZMod.pow_card, ZMod.pow_card]

/-- A prime in residue class `11` modulo `12` cannot divide the adjusted
endpoint residue. -/
lemma prime_mod_twelve_not_dvd_endpointThirdBandFixedResidue
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hpmod : p % 12 = 11) :
    ¬ (p : ℤ) ∣ endpointThirdBandFixedResidue := by
  intro hdvdInt
  rw [endpointThirdBandFixedResidue_eq_factorization] at hdvdInt
  have hdvd :
      p ∣ 2 ^ 3 * (3 ^ 3 * (13 * (29 * (8429 * (35533 * 470668789))))) := by
    exact_mod_cast hdvdInt
  rcases hp.dvd_mul.mp hdvd with h2 | hrest
  · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
    omega
  rcases hp.dvd_mul.mp hrest with h3 | hrest
  · have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
    omega
  rcases hp.dvd_mul.mp hrest with h13 | hrest
  · rcases (Nat.dvd_prime endpointThirdBand_fixed_factor_primes.1).mp
        h13 with h1 | heq
    · exact hp.ne_one h1
    · subst p
      norm_num at hpmod
  rcases hp.dvd_mul.mp hrest with h29 | hrest
  · rcases (Nat.dvd_prime endpointThirdBand_fixed_factor_primes.2.1).mp
        h29 with h1 | heq
    · exact hp.ne_one h1
    · subst p
      norm_num at hpmod
  rcases hp.dvd_mul.mp hrest with h8429 | hrest
  · rcases (Nat.dvd_prime endpointThirdBand_fixed_factor_primes.2.2.1).mp
        h8429 with h1 | heq
    · exact hp.ne_one h1
    · subst p
      norm_num at hpmod
  rcases hp.dvd_mul.mp hrest with h35533 | h470668789
  · rcases (Nat.dvd_prime endpointThirdBand_fixed_factor_primes.2.2.2.1).mp
        h35533 with h1 | heq
    · exact hp.ne_one h1
    · subst p
      norm_num at hpmod
  · rcases (Nat.dvd_prime endpointThirdBand_fixed_factor_primes.2.2.2.2).mp
        h470668789 with h1 | heq
    · exact hp.ne_one h1
    · subst p
      norm_num at hpmod

lemma endpointThirdBandCancellationFactor_not_dvd
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hpmod : p % 12 = 11) :
    ¬ (p : ℤ) ∣ endpointThirdBandCancellationFactor p := by
  intro hdvd
  have hz : (endpointThirdBandCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (endpointThirdBandCancellationFactor p) p).2 hdvd
  rw [endpointThirdBandCancellationFactor_cast_zmod p hp] at hz
  have hdvdFixed : (p : ℤ) ∣ endpointThirdBandFixedResidue :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      endpointThirdBandFixedResidue p).mp hz
  exact prime_mod_twelve_not_dvd_endpointThirdBandFixedResidue
    p hp hpgt hpmod hdvdFixed

lemma endpointThirdBandCancellationFactor_ratCast_ne_zero
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hpmod : p % 12 = 11) :
    (endpointThirdBandCancellationFactor p : ℚ) ≠ 0 := by
  have hz : endpointThirdBandCancellationFactor p ≠ 0 := by
    intro hzero
    apply endpointThirdBandCancellationFactor_not_dvd p hp hpgt hpmod
    rw [hzero]
    exact dvd_zero _
  exact_mod_cast hz

/-- The three common singular pairs plus the extra endpoint term. -/
def seedEndpointThirdBandSingularBlockRat (N k : ℕ) : ℚ :=
  seedThirdBandSingularBlockRat k +
    seed239TermRat (seedCommonTermCount N)

/-- The common seed terms after deleting the three singular indices. -/
def seedEndpointThirdBandRegularBlockRat (N k : ℕ) : ℚ :=
  ∑ j ∈ (((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k)).erase (thirdBandThirdIndex k),
      seedFiveTermRat j
    + ∑ j ∈ (((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k)).erase (thirdBandThirdIndex k),
      seed239TermRat j

lemma seed239TermRat_thirdBandEndpoint_eq_fraction
    (N p k : ℕ) (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 7 * p) :
    seed239TermRat (seedCommonTermCount N) =
      (4 * (-1 : ℚ) ^ k) /
        ((7 : ℚ) * (p : ℚ) * 239 ^ (7 * p)) := by
  rw [seed239TermRat_eq_fraction]
  have hexp : 2 * seedCommonTermCount N + 1 = 7 * p := by
    simp [seedCommonTermCount]
    omega
  have hsign :
      (-1 : ℚ) ^ seedCommonTermCount N = -((-1 : ℚ) ^ k) := by
    rw [show seedCommonTermCount N = 2 * (3 * k + 1) + (k + 1) by
      simp [seedCommonTermCount]; omega,
      pow_add, pow_mul, pow_succ]
    norm_num
    rw [pow_succ]
    ring
  rw [hexp, hsign]
  push_cast
  ring

/-- Exact endpoint-adjusted singular fraction. -/
theorem seedEndpointThirdBandSingularBlockRat_eq_fraction
    (N p k : ℕ) (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 7 * p) :
    seedEndpointThirdBandSingularBlockRat N k =
      (4 * (-1 : ℚ) ^ k *
          (endpointThirdBandCancellationFactor p : ℚ)) /
        ((105 : ℚ) * (p : ℚ) * 5 ^ (5 * p) * 239 ^ (7 * p)) := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  unfold seedEndpointThirdBandSingularBlockRat
  rw [seedThirdBandSingularBlockRat_eq_fraction p k hpdef,
    seed239TermRat_thirdBandEndpoint_eq_fraction N p k hpdef hendpointEq]
  unfold endpointThirdBandCancellationFactor
  push_cast
  have hpow239 : (239 : ℚ) ^ (7 * p) =
      239 ^ (5 * p) * 239 ^ (2 * p) := by
    rw [show 7 * p = 5 * p + 2 * p by omega, pow_add]
  rw [hpow239]
  field_simp [hpq]
  ring

theorem machinLowerRat_seed_eq_endpointThirdBandRegular_add_singular
    (N k : ℕ)
    (hk : k < seedCommonTermCount N)
    (hsecond : lowerBandSecondIndex k < seedCommonTermCount N)
    (hthird : thirdBandThirdIndex k < seedCommonTermCount N) :
    machinLowerRat (3 * (N + 1)) =
      seedEndpointThirdBandRegularBlockRat N k +
        seedEndpointThirdBandSingularBlockRat N k := by
  rw [machinLowerRat_seed_eq_thirdBandRegular_add_singular
    N k hk hsecond hthird]
  unfold seedThirdBandRegularBlockRat
  unfold seedEndpointThirdBandRegularBlockRat
  unfold seedEndpointThirdBandSingularBlockRat
  ring

theorem padicValRat_seedEndpointThirdBandSingularBlockRat
    (N p k : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 7 * p) :
    padicValRat p (seedEndpointThirdBandSingularBlockRat N k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h105q : (105 : ℚ) ≠ 0 := by norm_num
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4q : (4 : ℚ) ≠ 0 := by norm_num
  have h5q : (5 : ℚ) ≠ 0 := by norm_num
  have h239q : (239 : ℚ) ≠ 0 := by norm_num
  have hsign0 : (-1 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpmod : p % 12 = 11 :=
    endpointThirdBandPrime_mod_twelve N p hendpointEq
  have hfactor0 : (endpointThirdBandCancellationFactor p : ℚ) ≠ 0 :=
    endpointThirdBandCancellationFactor_ratCast_ne_zero p hp hpgt hpmod
  have hnum0 :
      4 * (-1 : ℚ) ^ k *
          (endpointThirdBandCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4q hsign0) hfactor0
  have h5pow0 : (5 : ℚ) ^ (5 * p) ≠ 0 := pow_ne_zero _ h5q
  have h239pow0 : (239 : ℚ) ^ (7 * p) ≠ 0 := pow_ne_zero _ h239q
  have hden0 :
      (105 : ℚ) * (p : ℚ) * 5 ^ (5 * p) * 239 ^ (7 * p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h105q hpq) h5pow0) h239pow0
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp (by omega))
  have hvalSign : padicValRat p ((-1 : ℚ) ^ k) = 0 := by
    rw [padicValRat.pow (by norm_num), padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat p (endpointThirdBandCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (endpointThirdBandCancellationFactor_not_dvd p hp hpgt hpmod)
  have hnot105 : ¬ p ∣ 105 := by
    intro hdvd
    have hsplit : p ∣ 3 ∨ p ∣ 5 * 7 := by
      apply hp.dvd_mul.mp
      norm_num at hdvd ⊢
      exact hdvd
    rcases hsplit with h3 | h57
    · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      omega
    rcases hp.dvd_mul.mp h57 with h5 | h7
    · have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
      omega
    · have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) h7
      omega
  have hval105 : padicValRat p (105 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hnot105
  have hval5 : padicValRat p (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_five p hp (by omega))
  have hval239 : padicValRat p (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_ne_239_not_dvd_239 p hp hp239)
  rw [seedEndpointThirdBandSingularBlockRat_eq_fraction
      N p k hpdef hendpointEq,
    padicValRat.div hnum0 hden0,
    padicValRat.mul (mul_ne_zero h4q hsign0) hfactor0,
    padicValRat.mul h4q hsign0,
    padicValRat.mul (mul_ne_zero (mul_ne_zero h105q hpq) h5pow0)
      h239pow0,
    padicValRat.mul (mul_ne_zero h105q hpq) h5pow0,
    padicValRat.mul h105q hpq,
    padicValRat.self hp.one_lt,
    padicValRat.pow h5q, padicValRat.pow h239q,
    hval4, hvalSign, hvalFactor, hval105, hval5, hval239]
  norm_num

lemma padicValRat_seedEndpointThirdBandRegularBlockRat_nonneg
    (N k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hdUpper : 12 * N + 15 < 7 * p)
    (hpdef : p = 2 * k + 1)
    (hregular : seedEndpointThirdBandRegularBlockRat N k ≠ 0) :
    0 ≤ padicValRat p (seedEndpointThirdBandRegularBlockRat N k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let A := (((range (seedCommonTermCount N)).erase k).erase
    (lowerBandSecondIndex k)).erase (thirdBandThirdIndex k)
  let F : ℚ := ∑ j ∈ A, seedFiveTermRat j
  let G : ℚ := ∑ j ∈ A, seed239TermRat j
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seedFiveTermRat_eq_zero p j hp (by omega)
          (thirdBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdUpper (by simpa [A] using hj))]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seed239TermRat_eq_zero p j hp hp239 (by omega)
          (thirdBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdUpper (by simpa [A] using hj))]
      · exact hG0
  change 0 ≤ padicValRat p (F + G)
  have hFG : F + G ≠ 0 := by
    simpa [F, G, A, seedEndpointThirdBandRegularBlockRat] using hregular
  exact padicValRat_add_nonneg_of_each_nonneg p hp hF hG hFG

theorem padicValRat_machinLowerRat_seed_endpointThirdBandPrime
    (N k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 7 * p) :
    padicValRat p (machinLowerRat (3 * (N + 1))) = -1 := by
  have hk : k < seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  have hsecond : lowerBandSecondIndex k < seedCommonTermCount N := by
    simp [lowerBandSecondIndex, seedCommonTermCount]
    omega
  have hthird : thirdBandThirdIndex k < seedCommonTermCount N := by
    simp [thirdBandThirdIndex, seedCommonTermCount]
    omega
  rw [machinLowerRat_seed_eq_endpointThirdBandRegular_add_singular
    N k hk hsecond hthird]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_seedEndpointThirdBandSingularBlockRat
      N p k hp hpgt hp239 hpdef hendpointEq
  · by_cases hregular : seedEndpointThirdBandRegularBlockRat N k = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_seedEndpointThirdBandRegularBlockRat_nonneg
          N k p hp hpgt hp239 (by omega) hpdef hregular)

theorem padicValRat_sampledMachinValueRat_endpointThirdBandPrime
    (N p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp239 : p ≠ 239)
    (hendpointEq : 12 * N + 17 = 7 * p) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  have hpne2 : p ≠ 2 := by omega
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two hpne2
  have hpdef : p = 2 * k + 1 := by omega
  have hblock := padicValRat_machinLowerRat_seed_endpointThirdBandPrime
    N k p hp hpgt hp239 hpdef hendpointEq
  have hblock0 : machinLowerRat (3 * (N + 1)) ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  letI : Fact p.Prime := ⟨hp⟩
  unfold sampledMachinValueRat
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_ten_pow_eq_zero_of_prime_gt_five (N + 1) p hp (by omega),
    hblock]
  norm_num

/-- Final third-band survival theorem with the endpoint case discharged. -/
theorem padicValRat_sampledMachinValueRat_thirdBandPrime_closedEndpoint
    (N p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217)
    (h5pLower : 5 * p ≤ 12 * N + 15)
    (hdUpper : 12 * N + 15 < 7 * p) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  by_cases hendpoint : p ∣ 12 * N + 17
  · have hendpointEq := endpoint_divisor_eq_seven_mul
      N p hp hpgt h5pLower hdUpper hendpoint
    exact padicValRat_sampledMachinValueRat_endpointThirdBandPrime
      N p hp hpgt hp239 hendpointEq
  · exact padicValRat_sampledMachinValueRat_thirdBandPrime
      N p hp hpgt hp239 hp19 hp37 hp79 hp48049 hp3586217
        h5pLower hdUpper hendpoint

/-- Exact reduced-denominator multiplicity throughout the closed-endpoint
third band. -/
theorem padicValNat_sampledMachinValueRat_den_thirdBandPrime_closedEndpoint
    (N p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp239 : p ≠ 239)
    (hp19 : p ≠ 19) (hp37 : p ≠ 37) (hp79 : p ≠ 79)
    (hp48049 : p ≠ 48049) (hp3586217 : p ≠ 3586217)
    (h5pLower : 5 * p ≤ 12 * N + 15)
    (hdUpper : 12 * N + 15 < 7 * p) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_sampledMachinValueRat_thirdBandPrime_closedEndpoint
      N p hp hpgt hp239 hp19 hp37 hp79 hp48049 hp3586217
        h5pLower hdUpper
  have hden : p ∣ q.den := by
    apply dvd_rat_den_of_padicValRat_neg
    rw [hval]
    norm_num
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

#print axioms thirdBand_full_coefficient_eq
#print axioms padicValRat_sampledMachinValueRat_thirdBandPrime
#print axioms padicValNat_sampledMachinValueRat_den_thirdBandPrime
#print axioms endpoint_divisor_eq_seven_mul
#print axioms endpointThirdBandPrime_mod_twelve
#print axioms endpointThirdBand_full_coefficient_eq
#print axioms padicValRat_sampledMachinValueRat_endpointThirdBandPrime
#print axioms padicValRat_sampledMachinValueRat_thirdBandPrime_closedEndpoint
#print axioms padicValNat_sampledMachinValueRat_den_thirdBandPrime_closedEndpoint

end Theory.PiDigits.MachinSeedThirdBandPrimeSurvival
