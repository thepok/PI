import TheoryLib.PiQuantitativeBlockHitting.T48T48MachinSeedUpperHalfPrimeSurvival

/-!
# T50: lower-band prime survival in the fixed Machin seed

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Put `d = 12*N+15`.  This file treats primes in the lower band

`d < 5*p` and `3*p <= d`.

Among the common odd Taylor denominators up to `d`, the only multiples of
such an odd prime are `p` and `3*p`.  The signs at those two exponents are
opposite.  Combining all four base-5/base-239 terms leaves a fixed residue
modulo `p`.  The full localized coefficient is exactly

`5359397032 / 1706489875`,

whose only prime numerator factors above five are
`11, 19, 233, 13757`.  Away from these four primes, the Machin bases, and an
explicit possible endpoint divisor, the fixed seed has exact `p`-adic
valuation `-1` and its reduced denominator contains `p` exactly once.

The final section also resolves that endpoint divisor: in the two-band range
it forces the extra exponent to equal `5*p`, and the resulting three-term
singular block has a second fixed noncancelling residue.  The strengthened
final theorems therefore cover the entire band `d/5 < p ≤ d` subject only to
the displayed fixed prime exceptions.

This is local rational arithmetic.  It does not control the complementary
CRT phase or imply an archimedean cylinder hit, recurrence, density,
normality, or the every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinSeedLowerBandPrimeSurvival

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinFixedModulusTelescoping
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival

/-- The Taylor index whose odd exponent is three times the odd exponent at
index `k`. -/
def lowerBandSecondIndex (k : ℕ) : ℕ :=
  3 * k + 1

/-- After the terms with odd exponents `p` and `3*p` are put over one
denominator, this is the integer factor left after removing
`4 * (-1)^k`. -/
def lowerBandCancellationFactor (p : ℕ) : ℤ :=
  3 * machinCancellationFactor p *
      (5 : ℤ) ^ (2 * p) * (239 : ℤ) ^ (2 * p) -
    machinCancellationFactor (3 * p)

/-- The Fermat reduction of `lowerBandCancellationFactor p` modulo `p`. -/
def lowerBandFixedResidue : ℤ :=
  3 * (4 * 239 - 5) * 5 ^ 2 * 239 ^ 2 - (4 * 239 ^ 3 - 5 ^ 3)

/-- Independent exact-arithmetic check of the fixed residue and all of its
prime factors. -/
theorem lowerBandFixedResidue_eq_factorization :
    lowerBandFixedResidue = 2 * 3 * 11 * 19 * 233 * 13757 := by
  norm_num [lowerBandFixedResidue]

/-- Independent exact-arithmetic check of the full four-term coefficient.
The factor `4` is part of the coefficient, while
`lowerBandCancellationFactor` deliberately removes it. -/
theorem lowerBand_full_coefficient_eq :
    (4 : ℚ) * (lowerBandFixedResidue : ℚ) /
        ((3 : ℚ) * 5 ^ 3 * 239 ^ 3) =
      5359397032 / 1706489875 := by
  norm_num [lowerBandFixedResidue]

theorem lowerBand_full_coefficient_numerator_eq_factorization :
    5359397032 = 2 ^ 3 * 11 * 19 * 233 * 13757 := by
  norm_num

theorem lowerBand_fixed_exception_primes :
    Nat.Prime 11 ∧ Nat.Prime 19 ∧ Nat.Prime 233 ∧ Nat.Prime 13757 := by
  norm_num

/-- Fermat's theorem reduces the variable cancellation factor to the fixed
integer residue. -/
theorem lowerBandCancellationFactor_cast_zmod
    (p : ℕ) (hp : p.Prime) :
    (lowerBandCancellationFactor p : ZMod p) = lowerBandFixedResidue := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [lowerBandCancellationFactor, machinCancellationFactor,
    lowerBandFixedResidue,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow]
  rw [show 2 * p = p * 2 by omega, show 3 * p = p * 3 by omega]
  simp only [pow_mul]
  rw [ZMod.pow_card, ZMod.pow_card]

/-- A prime above five outside the four displayed exceptions does not divide
the fixed lower-band residue. -/
lemma prime_not_dvd_lowerBandFixedResidue
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757) :
    ¬ (p : ℤ) ∣ lowerBandFixedResidue := by
  intro hdvdInt
  have hdvd : p ∣ 2 * (3 * (11 * (19 * (233 * 13757)))) := by
    have hdvd' : (p : ℤ) ∣ (2 * (3 * (11 * (19 * (233 * 13757)))) : ℤ) := by
      norm_num [lowerBandFixedResidue] at hdvdInt ⊢
      exact hdvdInt
    exact_mod_cast hdvd'
  rcases hp.dvd_mul.mp hdvd with h2 | hrest
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  rcases hp.dvd_mul.mp hrest with h3 | hrest
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  rcases hp.dvd_mul.mp hrest with h11 | hrest
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp h11 with h1 | heq
    · exact hp.ne_one h1
    · exact hp11 heq
  rcases hp.dvd_mul.mp hrest with h19 | hrest
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp h19 with h1 | heq
    · exact hp.ne_one h1
    · exact hp19 heq
  rcases hp.dvd_mul.mp hrest with h233 | h13757
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 233)).mp h233 with h1 | heq
    · exact hp.ne_one h1
    · exact hp233 heq
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13757)).mp h13757 with h1 | heq
    · exact hp.ne_one h1
    · exact hp13757 heq

/-- The variable cancellation factor is a `p`-unit under exactly the fixed
prime exclusions dictated by its Fermat residue. -/
lemma lowerBandCancellationFactor_not_dvd
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757) :
    ¬ (p : ℤ) ∣ lowerBandCancellationFactor p := by
  intro hdvd
  have hz : (lowerBandCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (lowerBandCancellationFactor p) p).2 hdvd
  rw [lowerBandCancellationFactor_cast_zmod p hp] at hz
  have hdvdFixed : (p : ℤ) ∣ lowerBandFixedResidue :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd lowerBandFixedResidue p).mp hz
  exact prime_not_dvd_lowerBandFixedResidue
    p hp hpgt hp11 hp19 hp233 hp13757 hdvdFixed

lemma lowerBandCancellationFactor_ratCast_ne_zero
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757) :
    (lowerBandCancellationFactor p : ℚ) ≠ 0 := by
  have hz : lowerBandCancellationFactor p ≠ 0 := by
    intro hzero
    apply lowerBandCancellationFactor_not_dvd
      p hp hpgt hp11 hp19 hp233 hp13757
    rw [hzero]
    exact dvd_zero _
  exact_mod_cast hz

/-- The four common Taylor terms whose odd exponents are `p` and `3*p`. -/
def seedLowerBandSingularBlockRat (k : ℕ) : ℚ :=
  (seedFiveTermRat k + seed239TermRat k) +
    (seedFiveTermRat (lowerBandSecondIndex k) +
      seed239TermRat (lowerBandSecondIndex k))

/-- All common seed terms after deleting the two Taylor indices with odd
exponents `p` and `3*p`, together with the extra base-239 endpoint. -/
def seedLowerBandRegularBlockRat (N k : ℕ) : ℚ :=
  ∑ j ∈ ((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k), seedFiveTermRat j
    + ∑ j ∈ ((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k), seed239TermRat j
    + seed239TermRat (seedCommonTermCount N)

lemma lowerBand_second_sign (k : ℕ) :
    (-1 : ℚ) ^ (lowerBandSecondIndex k) = -((-1 : ℚ) ^ k) := by
  unfold lowerBandSecondIndex
  rw [show 3 * k + 1 = 2 * k + (k + 1) by omega,
    pow_add, pow_mul, pow_succ]
  norm_num
  rw [pow_succ]
  ring

/-- Exact four-term combination.  The two singular Taylor pairs have
opposite signs, producing `lowerBandCancellationFactor`. -/
theorem seedLowerBandSingularBlockRat_eq_fraction
    (p k : ℕ) (hpdef : p = 2 * k + 1) :
    seedLowerBandSingularBlockRat k =
      (4 * (-1 : ℚ) ^ k * (lowerBandCancellationFactor p : ℚ)) /
        ((3 : ℚ) * (p : ℚ) * 5 ^ (3 * p) * 239 ^ (3 * p)) := by
  have hseconddef :
      3 * p = 2 * lowerBandSecondIndex k + 1 := by
    simp [lowerBandSecondIndex]
    omega
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  unfold seedLowerBandSingularBlockRat
  rw [seed_singular_pair_eq p k hpdef,
    seed_singular_pair_eq (3 * p) (lowerBandSecondIndex k) hseconddef]
  unfold interiorSingularPairRat lowerBandCancellationFactor
  rw [lowerBand_second_sign]
  push_cast
  have hpow5 : (5 : ℚ) ^ (3 * p) = 5 ^ p * 5 ^ (2 * p) := by
    rw [show 3 * p = p + 2 * p by omega, pow_add]
  have hpow239 : (239 : ℚ) ^ (3 * p) = 239 ^ p * 239 ^ (2 * p) := by
    rw [show 3 * p = p + 2 * p by omega, pow_add]
  simp_rw [hpow5, hpow239]
  field_simp [hpq]
  ring

/-- Exact decomposition of the unscaled fixed seed into its lower-band
regular block and the four singular terms. -/
theorem machinLowerRat_seed_eq_lowerBandRegular_add_singular
    (N k : ℕ)
    (hk : k < seedCommonTermCount N)
    (hsecond : lowerBandSecondIndex k < seedCommonTermCount N) :
    machinLowerRat (3 * (N + 1)) =
      seedLowerBandRegularBlockRat N k +
        seedLowerBandSingularBlockRat k := by
  have hkmem : k ∈ range (seedCommonTermCount N) := mem_range.2 hk
  have hsecondmem :
      lowerBandSecondIndex k ∈ range (seedCommonTermCount N) :=
    mem_range.2 hsecond
  have hsecondne : lowerBandSecondIndex k ≠ k := by
    simp [lowerBandSecondIndex]
    omega
  have hsecondErase :
      lowerBandSecondIndex k ∈ (range (seedCommonTermCount N)).erase k :=
    mem_erase.mpr ⟨hsecondne, hsecondmem⟩
  have hfiveFirst :=
    sum_erase_add (range (seedCommonTermCount N)) seedFiveTermRat hkmem
  have hfiveSecond :=
    sum_erase_add ((range (seedCommonTermCount N)).erase k)
      seedFiveTermRat hsecondErase
  have h239First :=
    sum_erase_add (range (seedCommonTermCount N)) seed239TermRat hkmem
  have h239Second :=
    sum_erase_add ((range (seedCommonTermCount N)).erase k)
      seed239TermRat hsecondErase
  rw [machinLowerRat_seed_eq, ← hfiveFirst, ← hfiveSecond,
    ← h239First, ← h239Second]
  unfold seedLowerBandRegularBlockRat seedLowerBandSingularBlockRat
  ring

/-- Below `5*p`, an odd multiple of the odd prime `p` can only have odd
cofactor one or three.  Both corresponding Taylor indices were erased. -/
lemma lowerBandPrime_not_dvd_regular_common_exponent
    (N k p j : ℕ) (hpgt : 5 < p)
    (hpdef : p = 2 * k + 1)
    (hdLower : 12 * N + 15 < 5 * p)
    (hj : j ∈ ((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k)) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjInner : j ∈ (range (seedCommonTermCount N)).erase k :=
    mem_of_mem_erase hj
  have hjlt : j < seedCommonTermCount N :=
    mem_range.1 (mem_of_mem_erase hjInner)
  have hjne : j ≠ k := ne_of_mem_erase hjInner
  have hjsecondne : j ≠ lowerBandSecondIndex k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 5 * p := by
    simp [seedCommonTermCount] at hjlt
    omega
  rcases hdvd with ⟨m, hm⟩
  have hp0 : 0 < p := by omega
  have hmul : p * m < p * 5 := by
    calc
      p * m = 2 * j + 1 := hm.symm
      _ < 5 * p := hexplt
      _ = p * 5 := by omega
  have hm5 : m < 5 := (Nat.mul_lt_mul_left hp0).mp hmul
  have hmpos : 0 < m := by
    by_contra hnot
    have hmzero : m = 0 := by omega
    subst m
    simp at hm
  interval_cases m
  all_goals simp_all [lowerBandSecondIndex]
  all_goals omega

lemma prime_gt_five_not_dvd_three
    (p : ℕ) (_hp : p.Prime) (hpgt : 5 < p) :
    ¬ p ∣ 3 := by
  intro hdvd
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- The combined contribution from exponents `p` and `3*p` has exact
valuation `-1`; the fixed residue factorization prevents cancellation. -/
theorem padicValRat_seedLowerBandSingularBlockRat
    (p k : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hpdef : p = 2 * k + 1) :
    padicValRat p (seedLowerBandSingularBlockRat k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h3q : (3 : ℚ) ≠ 0 := by norm_num
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4q : (4 : ℚ) ≠ 0 := by norm_num
  have h5q : (5 : ℚ) ≠ 0 := by norm_num
  have h239q : (239 : ℚ) ≠ 0 := by norm_num
  have hsign0 : (-1 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfactor0 : (lowerBandCancellationFactor p : ℚ) ≠ 0 :=
    lowerBandCancellationFactor_ratCast_ne_zero
      p hp hpgt hp11 hp19 hp233 hp13757
  have hnum0 :
      4 * (-1 : ℚ) ^ k * (lowerBandCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4q hsign0) hfactor0
  have h5pow0 : (5 : ℚ) ^ (3 * p) ≠ 0 := pow_ne_zero _ h5q
  have h239pow0 : (239 : ℚ) ^ (3 * p) ≠ 0 := pow_ne_zero _ h239q
  have hden0 :
      (3 : ℚ) * (p : ℚ) * 5 ^ (3 * p) * 239 ^ (3 * p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h3q hpq) h5pow0) h239pow0
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp hpgt)
  have hvalSign : padicValRat p ((-1 : ℚ) ^ k) = 0 := by
    rw [padicValRat.pow (by norm_num), padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat p (lowerBandCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (lowerBandCancellationFactor_not_dvd
        p hp hpgt hp11 hp19 hp233 hp13757)
  have hval3 : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_three p hp hpgt)
  have hval5 : padicValRat p (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_five p hp hpgt)
  have hval239 : padicValRat p (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_ne_239_not_dvd_239 p hp hp239)
  rw [seedLowerBandSingularBlockRat_eq_fraction p k hpdef,
    padicValRat.div hnum0 hden0,
    padicValRat.mul (mul_ne_zero h4q hsign0) hfactor0,
    padicValRat.mul h4q hsign0,
    padicValRat.mul (mul_ne_zero (mul_ne_zero h3q hpq) h5pow0) h239pow0,
    padicValRat.mul (mul_ne_zero h3q hpq) h5pow0,
    padicValRat.mul h3q hpq,
    padicValRat.self hp.one_lt,
    padicValRat.pow h5q, padicValRat.pow h239q,
    hval4, hvalSign, hvalFactor, hval3, hval5, hval239]
  norm_num

/-- Every term outside the two singular common exponents is `p`-integral;
the possible endpoint divisor is kept as an explicit hypothesis. -/
lemma padicValRat_seedLowerBandRegularBlockRat_nonneg
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hdLower : 12 * N + 15 < 5 * p)
    (hpdef : p = 2 * k + 1)
    (hendpoint : ¬ p ∣ 12 * N + 17)
    (hregular : seedLowerBandRegularBlockRat N k ≠ 0) :
    0 ≤ padicValRat p (seedLowerBandRegularBlockRat N k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let A := ((range (seedCommonTermCount N)).erase k).erase
    (lowerBandSecondIndex k)
  let F : ℚ := ∑ j ∈ A, seedFiveTermRat j
  let G : ℚ := ∑ j ∈ A, seed239TermRat j
  let E : ℚ := seed239TermRat (seedCommonTermCount N)
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seedFiveTermRat_eq_zero p j hp hpgt
          (lowerBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdLower (by simpa [A] using hj))]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seed239TermRat_eq_zero p j hp hp239 hpgt
          (lowerBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdLower (by simpa [A] using hj))]
      · exact hG0
  have hendpoint' : ¬ p ∣ 2 * seedCommonTermCount N + 1 := by
    have heq : 2 * seedCommonTermCount N + 1 = 12 * N + 17 := by
      simp [seedCommonTermCount]
      omega
    rw [heq]
    exact hendpoint
  have hEval : padicValRat p E = 0 :=
    padicValRat_seed239TermRat_eq_zero
      p (seedCommonTermCount N) hp hp239 hpgt hendpoint'
  have hE : E = 0 ∨ 0 ≤ padicValRat p E := Or.inr (by rw [hEval])
  have hFG : F + G = 0 ∨ 0 ≤ padicValRat p (F + G) := by
    by_cases hFG0 : F + G = 0
    · exact Or.inl hFG0
    · exact Or.inr
        (padicValRat_add_nonneg_of_each_nonneg p hp hF hG hFG0)
  change 0 ≤ padicValRat p ((F + G) + E)
  have hFGE : (F + G) + E ≠ 0 := by
    simpa [F, G, E, A, seedLowerBandRegularBlockRat] using hregular
  exact padicValRat_add_nonneg_of_each_nonneg p hp hFG hE hFGE

/-- The complete unscaled seed prefix has valuation `-1` in the audited
lower band. -/
theorem padicValRat_machinLowerRat_seed_lowerBandPrime
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (h3pUpper : 3 * p ≤ 12 * N + 15)
    (hpdef : p = 2 * k + 1)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValRat p (machinLowerRat (3 * (N + 1))) = -1 := by
  have hk : k < seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  have hsecond : lowerBandSecondIndex k < seedCommonTermCount N := by
    simp [lowerBandSecondIndex, seedCommonTermCount]
    omega
  rw [machinLowerRat_seed_eq_lowerBandRegular_add_singular N k hk hsecond]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_seedLowerBandSingularBlockRat
      p k hp hpgt hp239 hp11 hp19 hp233 hp13757 hpdef
  · by_cases hregular : seedLowerBandRegularBlockRat N k = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_seedLowerBandRegularBlockRat_nonneg
          N k p hp hpgt hp239 hdLower hpdef hendpoint hregular)

/-- Main lower-band survival theorem, stated without an auxiliary Taylor
index. -/
theorem padicValRat_sampledMachinValueRat_lowerBandPrime
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (h3pUpper : 3 * p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  have hpgt3 : 3 < p := by omega
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two (by omega)
  have hpdef : p = 2 * k + 1 := by omega
  have hpgt : 5 < p := by omega
  have hblock := padicValRat_machinLowerRat_seed_lowerBandPrime
    N k p hp hpgt hp239 hp11 hp19 hp233 hp13757
      hdLower h3pUpper hpdef hendpoint
  have hblock0 : machinLowerRat (3 * (N + 1)) ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  letI : Fact p.Prime := ⟨hp⟩
  unfold sampledMachinValueRat
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_ten_pow_eq_zero_of_prime_gt_five (N + 1) p hp hpgt,
    hblock]
  norm_num

/-- Reduced-denominator form of lower-band survival. -/
theorem lowerBandPrime_dvd_sampledMachinValueRat_den
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (h3pUpper : 3 * p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    p ∣ (sampledMachinValueRat (N + 1)).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_sampledMachinValueRat_lowerBandPrime
    N p hp hp5 hp239 hp11 hp19 hp233 hp13757
      hdLower h3pUpper hendpoint]
  norm_num

/-- Exact reduced-denominator multiplicity in the lower band. -/
theorem padicValNat_sampledMachinValueRat_den_lowerBandPrime
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (h3pUpper : 3 * p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_sampledMachinValueRat_lowerBandPrime
      N p hp hp5 hp239 hp11 hp19 hp233 hp13757
        hdLower h3pUpper hendpoint
  have hden : p ∣ q.den :=
    lowerBandPrime_dvd_sampledMachinValueRat_den
      N p hp hp5 hp239 hp11 hp19 hp233 hp13757
        hdLower h3pUpper hendpoint
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

/-- In the whole band `d < 3*p`, not merely the upper half `d < 2*p`, the
only common odd denominator divisible by the odd prime `p` is `p` itself.
The potential second multiple `2*p` is even. -/
lemma uniqueTermBandPrime_not_dvd_regular_common_exponent
    (N k p j : ℕ) (hpgt : 5 < p)
    (hpdef : p = 2 * k + 1)
    (hdLower : 12 * N + 15 < 3 * p)
    (hj : j ∈ (range (seedCommonTermCount N)).erase k) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjlt : j < seedCommonTermCount N :=
    mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 3 * p := by
    simp [seedCommonTermCount] at hjlt
    omega
  rcases hdvd with ⟨m, hm⟩
  have hp0 : 0 < p := by omega
  have hmul : p * m < p * 3 := by
    calc
      p * m = 2 * j + 1 := hm.symm
      _ < 3 * p := hexplt
      _ = p * 3 := by omega
  have hm3 : m < 3 := (Nat.mul_lt_mul_left hp0).mp hmul
  have hmpos : 0 < m := by
    by_contra hnot
    have hmzero : m = 0 := by omega
    subst m
    simp at hm
  interval_cases m
  all_goals simp_all
  all_goals omega

/-- Every nonsingular term in the one-exponent band is `p`-integral.  This
is T48's regular-block argument with the sharp odd-denominator cutoff
`d < 3*p` and an explicit endpoint hypothesis. -/
lemma padicValRat_seedRegularBlockRat_nonneg_uniqueTermBand
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hdLower : 12 * N + 15 < 3 * p)
    (hpdef : p = 2 * k + 1)
    (hendpoint : ¬ p ∣ 12 * N + 17)
    (hregular : seedRegularBlockRat N k ≠ 0) :
    0 ≤ padicValRat p (seedRegularBlockRat N k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℚ :=
    ∑ j ∈ (range (seedCommonTermCount N)).erase k, seedFiveTermRat j
  let G : ℚ :=
    ∑ j ∈ (range (seedCommonTermCount N)).erase k, seed239TermRat j
  let E : ℚ := seed239TermRat (seedCommonTermCount N)
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seedFiveTermRat_eq_zero p j hp hpgt
          (uniqueTermBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdLower hj)]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seed239TermRat_eq_zero p j hp hp239 hpgt
          (uniqueTermBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdLower hj)]
      · exact hG0
  have hendpoint' : ¬ p ∣ 2 * seedCommonTermCount N + 1 := by
    have heq : 2 * seedCommonTermCount N + 1 = 12 * N + 17 := by
      simp [seedCommonTermCount]
      omega
    rw [heq]
    exact hendpoint
  have hEval : padicValRat p E = 0 :=
    padicValRat_seed239TermRat_eq_zero
      p (seedCommonTermCount N) hp hp239 hpgt hendpoint'
  have hE : E = 0 ∨ 0 ≤ padicValRat p E := Or.inr (by rw [hEval])
  have hFG : F + G = 0 ∨ 0 ≤ padicValRat p (F + G) := by
    by_cases hFG0 : F + G = 0
    · exact Or.inl hFG0
    · exact Or.inr
        (padicValRat_add_nonneg_of_each_nonneg p hp hF hG hFG0)
  change 0 ≤ padicValRat p ((F + G) + E)
  have hFGE : (F + G) + E ≠ 0 := by
    simpa [F, G, E, seedRegularBlockRat] using hregular
  exact padicValRat_add_nonneg_of_each_nonneg p hp hFG hE hFGE

/-- The unscaled seed has valuation `-1` throughout the complete unique
common-term band `d/3 < p ≤ d`. -/
theorem padicValRat_machinLowerRat_seed_uniqueTermBandPrime
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hdLower : 12 * N + 15 < 3 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hpdef : p = 2 * k + 1)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValRat p (machinLowerRat (3 * (N + 1))) = -1 := by
  have hk : k < seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  rw [machinLowerRat_seed_eq_regular_add_singular N k p hpdef hk]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_seed_singular_pair
      p k hp hpgt hp239 hp317
  · by_cases hregular : seedRegularBlockRat N k = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_seedRegularBlockRat_nonneg_uniqueTermBand
          N k p hp hpgt hp239 hdLower hpdef hendpoint hregular)

/-- Combined middle-plus-upper theorem: T48's upper-half result extends to
the entire one-singular-exponent range `d/3 < p ≤ d`. -/
theorem padicValRat_sampledMachinValueRat_uniqueTermBandPrime
    (N p : ℕ) (hp : p.Prime)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hdLower : 12 * N + 15 < 3 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  have hpgt : 5 < p := by omega
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two (by omega)
  have hpdef : p = 2 * k + 1 := by omega
  have hblock := padicValRat_machinLowerRat_seed_uniqueTermBandPrime
    N k p hp hpgt hp239 hp317 hdLower hpUpper hpdef hendpoint
  have hblock0 : machinLowerRat (3 * (N + 1)) ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  letI : Fact p.Prime := ⟨hp⟩
  unfold sampledMachinValueRat
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_ten_pow_eq_zero_of_prime_gt_five (N + 1) p hp hpgt,
    hblock]
  norm_num

theorem uniqueTermBandPrime_dvd_sampledMachinValueRat_den
    (N p : ℕ) (hp : p.Prime)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hdLower : 12 * N + 15 < 3 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    p ∣ (sampledMachinValueRat (N + 1)).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_sampledMachinValueRat_uniqueTermBandPrime
    N p hp hp239 hp317 hdLower hpUpper hendpoint]
  norm_num

theorem padicValNat_sampledMachinValueRat_den_uniqueTermBandPrime
    (N p : ℕ) (hp : p.Prime)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hdLower : 12 * N + 15 < 3 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_sampledMachinValueRat_uniqueTermBandPrime
      N p hp hp239 hp317 hdLower hpUpper hendpoint
  have hden : p ∣ q.den :=
    uniqueTermBandPrime_dvd_sampledMachinValueRat_den
      N p hp hp239 hp317 hdLower hpUpper hendpoint
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

/-- Union of the one-exponent and two-exponent bands: every prime
`d/5 < p ≤ d` survives, subject to the union of the explicit arithmetic
exceptions and the endpoint condition. -/
theorem padicValRat_sampledMachinValueRat_twoBandPrime
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  by_cases h3pUpper : 3 * p ≤ 12 * N + 15
  · exact padicValRat_sampledMachinValueRat_lowerBandPrime
      N p hp hp5 hp239 hp11 hp19 hp233 hp13757
        hdLower h3pUpper hendpoint
  · exact padicValRat_sampledMachinValueRat_uniqueTermBandPrime
      N p hp hp239 hp317 (by omega) hpUpper hendpoint

theorem padicValNat_sampledMachinValueRat_den_twoBandPrime
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hendpoint : ¬ p ∣ 12 * N + 17) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  by_cases h3pUpper : 3 * p ≤ 12 * N + 15
  · exact padicValNat_sampledMachinValueRat_den_lowerBandPrime
      N p hp hp5 hp239 hp11 hp19 hp233 hp13757
        hdLower h3pUpper hendpoint
  · exact padicValNat_sampledMachinValueRat_den_uniqueTermBandPrime
      N p hp hp239 hp317 (by omega) hpUpper hendpoint

/-! ## Closing the extra-endpoint case

The preceding API deliberately kept divisibility of the one extra base-239
denominator as a hypothesis.  In the two-band range that exceptional geometry
is rigid: divisibility forces the endpoint exponent to be exactly `5*p`.
The resulting third singular term has another fixed nonzero residue, so the
endpoint condition can be removed in a strengthened theorem while preserving
all earlier theorem signatures. -/

/-- In the two-band range, an endpoint divisor can only occur at the exact
lower edge `12*N+17 = 5*p`. -/
lemma endpoint_divisor_eq_five_mul
    (N p : ℕ) (hpgt : 5 < p)
    (hdLower : 12 * N + 15 < 5 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hendpoint : p ∣ 12 * N + 17) :
    12 * N + 17 = 5 * p := by
  rcases hendpoint with ⟨m, hm⟩
  have hp0 : 0 < p := by omega
  have hmul : p * m < p * 6 := by omega
  have hm6 : m < 6 := (Nat.mul_lt_mul_left hp0).mp hmul
  interval_cases m <;> omega

/-- The cancellation factor after the common exponents `p,3*p` and the
extra base-239 endpoint exponent `5*p` are combined. -/
def endpointLowerBandCancellationFactor (p : ℕ) : ℤ :=
  5 * lowerBandCancellationFactor p * (239 : ℤ) ^ (2 * p) -
    3 * (5 : ℤ) ^ (3 * p)

/-- Fermat reduction of the endpoint cancellation factor. -/
def endpointLowerBandFixedResidue : ℤ :=
  5 * lowerBandFixedResidue * 239 ^ 2 - 3 * 5 ^ 3

theorem endpointLowerBandFixedResidue_eq_factorization :
    endpointLowerBandFixedResidue =
      3 * (3 * (5 * (463 * 55099733237))) := by
  norm_num [endpointLowerBandFixedResidue, lowerBandFixedResidue]

theorem endpointLowerBand_full_coefficient_eq :
    (4 : ℚ) * (endpointLowerBandFixedResidue : ℚ) /
        ((15 : ℚ) * 5 ^ 3 * 239 ^ 5) =
      306134117864772 / 97476408149875 := by
  norm_num [endpointLowerBandFixedResidue, lowerBandFixedResidue]

theorem endpointLowerBand_full_coefficient_numerator_eq_factorization :
    306134117864772 = 2 ^ 2 * 3 * 463 * 55099733237 := by
  norm_num

theorem endpointLowerBand_fixed_exception_primes :
    Nat.Prime 463 ∧ Nat.Prime 55099733237 := by
  norm_num

/-- Fermat reduction of the variable endpoint cancellation factor. -/
theorem endpointLowerBandCancellationFactor_cast_zmod
    (p : ℕ) (hp : p.Prime) :
    (endpointLowerBandCancellationFactor p : ZMod p) =
      endpointLowerBandFixedResidue := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [endpointLowerBandCancellationFactor,
    endpointLowerBandFixedResidue, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_pow]
  rw [lowerBandCancellationFactor_cast_zmod p hp]
  rw [show 2 * p = p * 2 by omega, show 3 * p = p * 3 by omega]
  simp only [pow_mul]
  rw [ZMod.pow_card, ZMod.pow_card]

lemma prime_not_dvd_endpointLowerBandFixedResidue
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp463 : p ≠ 463) (hpBig : p ≠ 55099733237) :
    ¬ (p : ℤ) ∣ endpointLowerBandFixedResidue := by
  intro hdvdInt
  rw [endpointLowerBandFixedResidue_eq_factorization] at hdvdInt
  have hdvd : p ∣ 3 * (3 * (5 * (463 * 55099733237))) := by
    exact_mod_cast hdvdInt
  rcases hp.dvd_mul.mp hdvd with h3 | hrest
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  rcases hp.dvd_mul.mp hrest with h3 | hrest
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  rcases hp.dvd_mul.mp hrest with h5 | hrest
  · have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
    omega
  rcases hp.dvd_mul.mp hrest with h463 | hBig
  · rcases (Nat.dvd_prime endpointLowerBand_fixed_exception_primes.1).mp
        h463 with h1 | heq
    · exact hp.ne_one h1
    · exact hp463 heq
  · rcases (Nat.dvd_prime endpointLowerBand_fixed_exception_primes.2).mp
        hBig with h1 | heq
    · exact hp.ne_one h1
    · exact hpBig heq

lemma endpointLowerBandCancellationFactor_not_dvd
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp463 : p ≠ 463) (hpBig : p ≠ 55099733237) :
    ¬ (p : ℤ) ∣ endpointLowerBandCancellationFactor p := by
  intro hdvd
  have hz : (endpointLowerBandCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (endpointLowerBandCancellationFactor p) p).2 hdvd
  rw [endpointLowerBandCancellationFactor_cast_zmod p hp] at hz
  have hdvdFixed : (p : ℤ) ∣ endpointLowerBandFixedResidue :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      endpointLowerBandFixedResidue p).mp hz
  exact prime_not_dvd_endpointLowerBandFixedResidue
    p hp hpgt hp463 hpBig hdvdFixed

lemma endpointLowerBandCancellationFactor_ratCast_ne_zero
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp463 : p ≠ 463) (hpBig : p ≠ 55099733237) :
    (endpointLowerBandCancellationFactor p : ℚ) ≠ 0 := by
  have hz : endpointLowerBandCancellationFactor p ≠ 0 := by
    intro hzero
    apply endpointLowerBandCancellationFactor_not_dvd
      p hp hpgt hp463 hpBig
    rw [hzero]
    exact dvd_zero _
  exact_mod_cast hz

/-- The three singular contributions in the endpoint case. -/
def seedEndpointLowerBandSingularBlockRat (N k : ℕ) : ℚ :=
  seedLowerBandSingularBlockRat k +
    seed239TermRat (seedCommonTermCount N)

/-- The common seed terms after deleting the exponents `p` and `3*p`; in
the endpoint case the extra base-239 term belongs to the singular block. -/
def seedEndpointLowerBandRegularBlockRat (N k : ℕ) : ℚ :=
  ∑ j ∈ ((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k), seedFiveTermRat j
    + ∑ j ∈ ((range (seedCommonTermCount N)).erase k).erase
      (lowerBandSecondIndex k), seed239TermRat j

lemma lowerBandEndpoint_first_sign
    (N k p : ℕ) (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 5 * p) :
    (-1 : ℚ) ^ k = 1 := by
  have htwoDvdFiveK : 2 ∣ 5 * k := by
    refine ⟨3 * (N + 1), ?_⟩
    omega
  have htwoDvdK : 2 ∣ k := by
    rcases (show Nat.Prime 2 by norm_num).dvd_mul.mp htwoDvdFiveK with
      htwoDvdFive | htwoDvdK
    · norm_num at htwoDvdFive
    · exact htwoDvdK
  rcases htwoDvdK with ⟨r, rfl⟩
  rw [pow_mul]
  norm_num

lemma seed239TermRat_endpoint_eq_fraction
    (N p : ℕ) (hendpointEq : 12 * N + 17 = 5 * p) :
    seed239TermRat (seedCommonTermCount N) =
      -(4 / ((5 : ℚ) * (p : ℚ) * 239 ^ (5 * p))) := by
  rw [seed239TermRat_eq_fraction]
  have hexp : 2 * seedCommonTermCount N + 1 = 5 * p := by
    simp [seedCommonTermCount]
    omega
  have hsign : (-1 : ℚ) ^ seedCommonTermCount N = 1 := by
    rw [show seedCommonTermCount N = 2 * (3 * (N + 1) + 1) by
      simp [seedCommonTermCount]; omega, pow_mul]
    norm_num
  rw [hexp, hsign]
  push_cast
  ring

/-- Exact three-term endpoint combination. -/
theorem seedEndpointLowerBandSingularBlockRat_eq_fraction
    (N p k : ℕ) (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 5 * p) :
    seedEndpointLowerBandSingularBlockRat N k =
      (4 * (endpointLowerBandCancellationFactor p : ℚ)) /
        ((15 : ℚ) * (p : ℚ) * 5 ^ (3 * p) * 239 ^ (5 * p)) := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  unfold seedEndpointLowerBandSingularBlockRat
  rw [seedLowerBandSingularBlockRat_eq_fraction p k hpdef,
    lowerBandEndpoint_first_sign N k p hpdef hendpointEq,
    seed239TermRat_endpoint_eq_fraction N p hendpointEq]
  unfold endpointLowerBandCancellationFactor
  push_cast
  have hpow239 : (239 : ℚ) ^ (5 * p) =
      239 ^ (3 * p) * 239 ^ (2 * p) := by
    rw [show 5 * p = 3 * p + 2 * p by omega, pow_add]
  rw [hpow239]
  field_simp [hpq]
  ring

/-- Exact seed decomposition with all three endpoint singular terms grouped
together. -/
theorem machinLowerRat_seed_eq_endpointLowerBandRegular_add_singular
    (N k : ℕ)
    (hk : k < seedCommonTermCount N)
    (hsecond : lowerBandSecondIndex k < seedCommonTermCount N) :
    machinLowerRat (3 * (N + 1)) =
      seedEndpointLowerBandRegularBlockRat N k +
        seedEndpointLowerBandSingularBlockRat N k := by
  rw [machinLowerRat_seed_eq_lowerBandRegular_add_singular N k hk hsecond]
  unfold seedLowerBandRegularBlockRat
  unfold seedEndpointLowerBandRegularBlockRat
  unfold seedEndpointLowerBandSingularBlockRat
  ring

lemma prime_gt_five_not_dvd_fifteen
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p) :
    ¬ p ∣ 15 := by
  intro hdvd
  have hsplit : p ∣ 3 ∨ p ∣ 5 := by
    apply hp.dvd_mul.mp
    norm_num at hdvd ⊢
    exact hdvd
  rcases hsplit with h3 | h5
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  · have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
    omega

/-- The endpoint singular block has exact valuation `-1`; its fixed residue
cannot cancel for an admissible endpoint prime. -/
theorem padicValRat_seedEndpointLowerBandSingularBlockRat
    (N p k : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hp463 : p ≠ 463) (hpBig : p ≠ 55099733237)
    (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 5 * p) :
    padicValRat p (seedEndpointLowerBandSingularBlockRat N k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h4q : (4 : ℚ) ≠ 0 := by norm_num
  have h15q : (15 : ℚ) ≠ 0 := by norm_num
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h5q : (5 : ℚ) ≠ 0 := by norm_num
  have h239q : (239 : ℚ) ≠ 0 := by norm_num
  have hfactor0 : (endpointLowerBandCancellationFactor p : ℚ) ≠ 0 :=
    endpointLowerBandCancellationFactor_ratCast_ne_zero
      p hp hpgt hp463 hpBig
  have hnum0 :
      4 * (endpointLowerBandCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero h4q hfactor0
  have h5pow0 : (5 : ℚ) ^ (3 * p) ≠ 0 := pow_ne_zero _ h5q
  have h239pow0 : (239 : ℚ) ^ (5 * p) ≠ 0 := pow_ne_zero _ h239q
  have hden0 :
      (15 : ℚ) * (p : ℚ) * 5 ^ (3 * p) * 239 ^ (5 * p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h15q hpq) h5pow0) h239pow0
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp hpgt)
  have hvalFactor :
      padicValRat p (endpointLowerBandCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (endpointLowerBandCancellationFactor_not_dvd
        p hp hpgt hp463 hpBig)
  have hval15 : padicValRat p (15 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_fifteen p hp hpgt)
  have hval5 : padicValRat p (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_five p hp hpgt)
  have hval239 : padicValRat p (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_ne_239_not_dvd_239 p hp hp239)
  rw [seedEndpointLowerBandSingularBlockRat_eq_fraction
      N p k hpdef hendpointEq,
    padicValRat.div hnum0 hden0,
    padicValRat.mul h4q hfactor0,
    padicValRat.mul (mul_ne_zero (mul_ne_zero h15q hpq) h5pow0)
      h239pow0,
    padicValRat.mul (mul_ne_zero h15q hpq) h5pow0,
    padicValRat.mul h15q hpq,
    padicValRat.self hp.one_lt,
    padicValRat.pow h5q, padicValRat.pow h239q,
    hval4, hvalFactor, hval15, hval5, hval239]
  norm_num

/-- Every remaining common term is p-integral after all three endpoint
singular terms have been removed. -/
lemma padicValRat_seedEndpointLowerBandRegularBlockRat_nonneg
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hdLower : 12 * N + 15 < 5 * p)
    (hpdef : p = 2 * k + 1)
    (hregular : seedEndpointLowerBandRegularBlockRat N k ≠ 0) :
    0 ≤ padicValRat p (seedEndpointLowerBandRegularBlockRat N k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let A := ((range (seedCommonTermCount N)).erase k).erase
    (lowerBandSecondIndex k)
  let F : ℚ := ∑ j ∈ A, seedFiveTermRat j
  let G : ℚ := ∑ j ∈ A, seed239TermRat j
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seedFiveTermRat_eq_zero p j hp hpgt
          (lowerBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdLower (by simpa [A] using hj))]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seed239TermRat_eq_zero p j hp hp239 hpgt
          (lowerBandPrime_not_dvd_regular_common_exponent
            N k p j hpgt hpdef hdLower (by simpa [A] using hj))]
      · exact hG0
  change 0 ≤ padicValRat p (F + G)
  have hFG : F + G ≠ 0 := by
    simpa [F, G, A, seedEndpointLowerBandRegularBlockRat] using hregular
  exact padicValRat_add_nonneg_of_each_nonneg p hp hF hG hFG

/-- Exact valuation of the unscaled seed when its extra endpoint is `5*p`. -/
theorem padicValRat_machinLowerRat_seed_endpointLowerBandPrime
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hpdef : p = 2 * k + 1)
    (hendpointEq : 12 * N + 17 = 5 * p) :
    padicValRat p (machinLowerRat (3 * (N + 1))) = -1 := by
  have hk : k < seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  have hsecond : lowerBandSecondIndex k < seedCommonTermCount N := by
    simp [lowerBandSecondIndex, seedCommonTermCount]
    omega
  have hp463 : p ≠ 463 := by
    intro heq
    subst p
    omega
  have hpBig : p ≠ 55099733237 := by
    intro heq
    subst p
    omega
  have hdLower : 12 * N + 15 < 5 * p := by omega
  rw [machinLowerRat_seed_eq_endpointLowerBandRegular_add_singular
    N k hk hsecond]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_seedEndpointLowerBandSingularBlockRat
      N p k hp hpgt hp239 hp463 hpBig hpdef hendpointEq
  · by_cases hregular : seedEndpointLowerBandRegularBlockRat N k = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_seedEndpointLowerBandRegularBlockRat_nonneg
          N k p hp hpgt hp239 hdLower hpdef hregular)

/-- Endpoint-case survival for the scaled fixed seed. -/
theorem padicValRat_sampledMachinValueRat_endpointLowerBandPrime
    (N p : ℕ) (hp : p.Prime)
    (_hp5 : p ≠ 5) (hp239 : p ≠ 239)
    (hendpointEq : 12 * N + 17 = 5 * p) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  have hpne2 : p ≠ 2 := by omega
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two hpne2
  have hpdef : p = 2 * k + 1 := by omega
  have hpgt : 5 < p := by omega
  have hblock := padicValRat_machinLowerRat_seed_endpointLowerBandPrime
    N k p hp hpgt hp239 hpdef hendpointEq
  have hblock0 : machinLowerRat (3 * (N + 1)) ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  letI : Fact p.Prime := ⟨hp⟩
  unfold sampledMachinValueRat
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_ten_pow_eq_zero_of_prime_gt_five (N + 1) p hp hpgt,
    hblock]
  norm_num

theorem endpointLowerBandPrime_dvd_sampledMachinValueRat_den
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239)
    (hendpointEq : 12 * N + 17 = 5 * p) :
    p ∣ (sampledMachinValueRat (N + 1)).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_sampledMachinValueRat_endpointLowerBandPrime
    N p hp hp5 hp239 hendpointEq]
  norm_num

theorem padicValNat_sampledMachinValueRat_den_endpointLowerBandPrime
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239)
    (hendpointEq : 12 * N + 17 = 5 * p) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_sampledMachinValueRat_endpointLowerBandPrime
      N p hp hp5 hp239 hendpointEq
  have hden : p ∣ q.den :=
    endpointLowerBandPrime_dvd_sampledMachinValueRat_den
      N p hp hp5 hp239 hendpointEq
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

/-- Final two-band survival theorem with the endpoint case discharged rather
than assumed away.  Only the displayed fixed arithmetic exceptions remain. -/
theorem padicValRat_sampledMachinValueRat_twoBandPrime_closedEndpoint
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (hpUpper : p ≤ 12 * N + 15) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  by_cases hendpoint : p ∣ 12 * N + 17
  · have hpne2 : p ≠ 2 := by omega
    obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two hpne2
    have hpgt : 5 < p := by omega
    have hendpointEq := endpoint_divisor_eq_five_mul
      N p hpgt hdLower hpUpper hendpoint
    exact padicValRat_sampledMachinValueRat_endpointLowerBandPrime
      N p hp hp5 hp239 hendpointEq
  · exact padicValRat_sampledMachinValueRat_twoBandPrime
      N p hp hp5 hp239 hp317 hp11 hp19 hp233 hp13757
        hdLower hpUpper hendpoint

/-- Exact reduced-denominator multiplicity throughout the closed-endpoint
two-band range. -/
theorem padicValNat_sampledMachinValueRat_den_twoBandPrime_closedEndpoint
    (N p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hp11 : p ≠ 11) (hp19 : p ≠ 19)
    (hp233 : p ≠ 233) (hp13757 : p ≠ 13757)
    (hdLower : 12 * N + 15 < 5 * p)
    (hpUpper : p ≤ 12 * N + 15) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_sampledMachinValueRat_twoBandPrime_closedEndpoint
      N p hp hp5 hp239 hp317 hp11 hp19 hp233 hp13757 hdLower hpUpper
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

#print axioms
  lowerBand_full_coefficient_eq
#print axioms
  padicValRat_sampledMachinValueRat_lowerBandPrime
#print axioms
  padicValNat_sampledMachinValueRat_den_lowerBandPrime
#print axioms
  padicValRat_sampledMachinValueRat_uniqueTermBandPrime
#print axioms
  padicValNat_sampledMachinValueRat_den_uniqueTermBandPrime
#print axioms
  padicValRat_sampledMachinValueRat_twoBandPrime
#print axioms
  padicValNat_sampledMachinValueRat_den_twoBandPrime
#print axioms
  endpointLowerBand_full_coefficient_eq
#print axioms
  endpoint_divisor_eq_five_mul
#print axioms
  padicValRat_sampledMachinValueRat_endpointLowerBandPrime
#print axioms
  padicValNat_sampledMachinValueRat_den_endpointLowerBandPrime
#print axioms
  padicValRat_sampledMachinValueRat_twoBandPrime_closedEndpoint
#print axioms
  padicValNat_sampledMachinValueRat_den_twoBandPrime_closedEndpoint

end Theory.PiDigits.MachinSeedLowerBandPrimeSurvival
