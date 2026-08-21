import TheoryLib.PiQuantitativeBlockHitting.T46T46MachinFixedModulusTelescoping
import TheoryLib.PiQuantitativeBlockHitting.T47T47MachinAllPrimeSurvival

/-!
# T48: upper-half prime survival in the fixed Machin seed

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Put `d = 12*N+15`.  The fixed pulse seed from T46 is
`sampledMachinValueRat (N+1)`.  If a prime `p` lies in the upper half of
`[1,d]`, then among the common odd linear denominators in its two Machin
Taylor prefixes, only the denominator `p` is divisible by `p`.  The two
terms at that denominator have the same noncancelling residue `951` as in
T45.  The extra base-239 endpoint has denominator `d+2`; its odd parity and
the upper-half bound exclude divisibility by `p`.

Under the explicit exclusions of the two possible arithmetic exceptions
`239` and `317`, the seed therefore has exact `p`-adic valuation `-1`.
This is local rational arithmetic.  It does not control the complementary
CRT phase or imply an archimedean cylinder hit, recurrence, density,
normality, or the every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinFixedModulusTelescoping

/-- Number of odd exponents shared by the two Taylor prefixes in the seed
at sampled index `N+1`. -/
def seedCommonTermCount (N : ℕ) : ℕ :=
  6 * (N + 1) + 2

/-- The coefficient-16 base-5 term at Taylor index `j`. -/
def seedFiveTermRat (j : ℕ) : ℚ :=
  16 * arctanTermRat 5 j

/-- The coefficient-minus-four base-239 term at Taylor index `j`. -/
def seed239TermRat (j : ℕ) : ℚ :=
  -4 * arctanTermRat 239 j

/-- All seed terms except the two common terms at Taylor index `k`.
The final base-239 term is written separately because that Taylor prefix
has one more term than the base-5 prefix. -/
def seedRegularBlockRat (N k : ℕ) : ℚ :=
  ∑ j ∈ (range (seedCommonTermCount N)).erase k, seedFiveTermRat j
    + ∑ j ∈ (range (seedCommonTermCount N)).erase k, seed239TermRat j
    + seed239TermRat (seedCommonTermCount N)

lemma seedFiveTermRat_eq_fraction (j : ℕ) :
    seedFiveTermRat j =
      16 * (-1 : ℚ) ^ j /
        ((((2 * j + 1 : ℕ) : ℚ)) * 5 ^ (2 * j + 1)) := by
  unfold seedFiveTermRat arctanTermRat
  simp only [inv_pow]
  push_cast
  rw [pow_add]
  field_simp

lemma seed239TermRat_eq_fraction (j : ℕ) :
    seed239TermRat j =
      -(4 * (-1 : ℚ) ^ j /
        ((((2 * j + 1 : ℕ) : ℚ)) * 239 ^ (2 * j + 1))) := by
  unfold seed239TermRat arctanTermRat
  simp only [inv_pow]
  push_cast
  rw [pow_add]
  field_simp

/-- The two common seed terms at exponent `p = 2*k+1` are exactly T45's
combined singular pair. -/
lemma seed_singular_pair_eq
    (p k : ℕ) (hpdef : p = 2 * k + 1) :
    seedFiveTermRat k + seed239TermRat k =
      interiorSingularPairRat p k := by
  rw [seedFiveTermRat_eq_fraction, seed239TermRat_eq_fraction]
  simp only [interiorSingularPairRat, machinCancellationFactor]
  subst p
  push_cast
  field_simp
  ring

/-- Exact common-prefix plus endpoint expansion of the unscaled seed. -/
theorem machinLowerRat_seed_eq (N : ℕ) :
    machinLowerRat (3 * (N + 1)) =
      (∑ j ∈ range (seedCommonTermCount N), seedFiveTermRat j)
        + (∑ j ∈ range (seedCommonTermCount N), seed239TermRat j)
        + seed239TermRat (seedCommonTermCount N) := by
  unfold machinLowerRat arctanPartialRat
  have hcount : 2 * (3 * (N + 1) + 1) = seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  rw [hcount, sum_range_succ]
  simp only [seedFiveTermRat, seed239TermRat, mul_sum]
  simp only [← mul_sum]
  ring

/-- Exact decomposition of the Machin prefix underlying the seed into its
regular terms and one combined singular pair. -/
theorem machinLowerRat_seed_eq_regular_add_singular
    (N k p : ℕ) (hpdef : p = 2 * k + 1)
    (hk : k < seedCommonTermCount N) :
    machinLowerRat (3 * (N + 1)) =
      seedRegularBlockRat N k + interiorSingularPairRat p k := by
  have hkmem : k ∈ range (seedCommonTermCount N) := mem_range.2 hk
  have hfive :=
    sum_erase_add (range (seedCommonTermCount N)) seedFiveTermRat hkmem
  have h239 :=
    sum_erase_add (range (seedCommonTermCount N)) seed239TermRat hkmem
  rw [machinLowerRat_seed_eq, ← seed_singular_pair_eq p k hpdef]
  unfold seedRegularBlockRat
  rw [← hfive, ← h239]
  ring

/-- The division-free upper-half condition makes every other common odd
linear denominator a `p`-unit. -/
lemma upperHalfPrime_not_dvd_regular_common_exponent
    (N k p j : ℕ)
    (hpLower : 12 * N + 15 < 2 * p)
    (hpdef : p = 2 * k + 1)
    (hj : j ∈ (range (seedCommonTermCount N)).erase k) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjlt : j < seedCommonTermCount N :=
    mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 2 * p := by
    simp [seedCommonTermCount] at hjlt
    omega
  have heq : 2 * j + 1 = p :=
    eq_of_dvd_of_pos_of_lt_two_mul
      (by omega) (by omega) hexplt hdvd
  exact hjne (by omega)

/-- The extra endpoint `12*N+17` is not divisible by an upper-half prime.
If it were, the bounds would force it to equal `2*p`, impossible because
the endpoint is odd. -/
lemma upperHalfPrime_not_dvd_endpoint
    (N p : ℕ) (hpgt : 5 < p)
    (hpLower : 12 * N + 15 < 2 * p)
    (hpUpper : p ≤ 12 * N + 15) :
    ¬ p ∣ 12 * N + 17 := by
  intro hdvd
  have hp0 : 0 < p := by omega
  have hplt : p < 12 * N + 17 := by omega
  have hsubpos : 0 < 12 * N + 17 - p := by omega
  have hdvdsub : p ∣ 12 * N + 17 - p :=
    Nat.dvd_sub hdvd (dvd_refl p)
  have hsub_lt : 12 * N + 17 - p < 2 * p := by omega
  have heq : 12 * N + 17 - p = p :=
    eq_of_dvd_of_pos_of_lt_two_mul hp0 hsubpos hsub_lt hdvdsub
  omega

lemma prime_gt_five_not_dvd_four
    (p : ℕ) (_hp : p.Prime) (hpgt : 5 < p) :
    ¬ p ∣ 4 := by
  intro hdvd
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  omega

lemma prime_gt_five_not_dvd_five
    (p : ℕ) (_hp : p.Prime) (hpgt : 5 < p) :
    ¬ p ∣ 5 := by
  intro hdvd
  have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- Apart from `317`, a prime greater than five cannot divide the fixed
cancellation residue `951 = 3*317`. -/
lemma prime_gt_five_ne_317_not_dvd_951
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hp317 : p ≠ 317) :
    ¬ p ∣ 951 := by
  intro hdvd
  have hsplit : p ∣ 3 ∨ p ∣ 317 := by
    apply hp.dvd_mul.mp
    norm_num at hdvd ⊢
    exact hdvd
  rcases hsplit with h3 | h317
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 317)).mp h317 with h1 | heq
    · exact hp.ne_one h1
    · exact hp317 heq

/-- The Machin cancellation factor is a `p`-unit for the upper-half primes
under consideration. -/
lemma machinCancellationFactor_not_dvd_upperHalfPrime
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hp317 : p ≠ 317) :
    ¬ (p : ℤ) ∣ machinCancellationFactor p := by
  intro hdvd
  have hz : (machinCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (machinCancellationFactor p) p).2 hdvd
  rw [machinCancellationFactor_cast_zmod p hp] at hz
  have hz' : (((951 : ℤ) : ZMod p)) = 0 := by
    norm_num at hz ⊢
    exact hz
  have hdvd951 : (p : ℤ) ∣ (951 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (951 : ℤ) p).mp hz'
  have hdvdNat : p ∣ 951 := by exact_mod_cast hdvd951
  exact prime_gt_five_ne_317_not_dvd_951 p hp hpgt hp317 hdvdNat

lemma machinCancellationFactor_ratCast_ne_zero_upperHalfPrime
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hp317 : p ≠ 317) :
    (machinCancellationFactor p : ℚ) ≠ 0 := by
  have hz : machinCancellationFactor p ≠ 0 := by
    intro hzero
    apply machinCancellationFactor_not_dvd_upperHalfPrime p hp hpgt hp317
    rw [hzero]
    exact dvd_zero _
  exact_mod_cast hz

/-- The combined terms at the unique common denominator `p` have exact
valuation `-1`; the fixed residue `951` prevents their cancellation. -/
theorem padicValRat_seed_singular_pair
    (p k : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317) :
    padicValRat p (interiorSingularPairRat p k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h5q : (5 : ℚ) ≠ 0 := by norm_num
  have h239q : (239 : ℚ) ≠ 0 := by norm_num
  have hfactor0 : (machinCancellationFactor p : ℚ) ≠ 0 :=
    machinCancellationFactor_ratCast_ne_zero_upperHalfPrime
      p hp hpgt hp317
  have hnum0 :
      4 * (-1 : ℚ) ^ k * (machinCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (by norm_num))) hfactor0
  have hden0 : (p : ℚ) * 5 ^ p * 239 ^ p ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpq (pow_ne_zero _ h5q))
      (pow_ne_zero _ h239q)
  have hvalFactor :
      padicValRat p (machinCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (machinCancellationFactor_not_dvd_upperHalfPrime p hp hpgt hp317)
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp hpgt)
  have hvalNegOne : padicValRat p (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hval5 : padicValRat p (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_five p hp hpgt)
  have hval239 : padicValRat p (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_ne_239_not_dvd_239 p hp hp239)
  unfold interiorSingularPairRat
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (by norm_num))) hfactor0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.pow (by norm_num), hval4, hvalNegOne, hvalFactor,
    padicValRat.mul (mul_ne_zero hpq (pow_ne_zero _ h5q))
      (pow_ne_zero _ h239q),
    padicValRat.mul hpq (pow_ne_zero _ h5q),
    padicValRat.self hp.one_lt,
    padicValRat.pow h5q, hval5,
    padicValRat.pow h239q, hval239]
  norm_num

lemma padicValRat_seedFiveTermRat_eq_zero
    (p j : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hexp : ¬ p ∣ 2 * j + 1) :
    padicValRat p (seedFiveTermRat j) = 0 := by
  rw [seedFiveTermRat_eq_fraction]
  exact padicValRat_signed_fraction_eq_zero
    p 16 5 (2 * j + 1) j hp
    (by
      intro hdvd
      have hle : p ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp
          (hp.dvd_of_dvd_pow (n := 4) (by norm_num at hdvd ⊢; exact hdvd)) with h1 | h2
      · exact hp.ne_one h1
      · omega)
    (prime_gt_five_not_dvd_five p hp hpgt) hexp
    (by norm_num) (by norm_num) (by omega)

lemma padicValRat_seed239TermRat_eq_zero
    (p j : ℕ) (hp : p.Prime) (hp239 : p ≠ 239)
    (hpgt : 5 < p) (hexp : ¬ p ∣ 2 * j + 1) :
    padicValRat p (seed239TermRat j) = 0 := by
  rw [seed239TermRat_eq_fraction, padicValRat.neg]
  exact padicValRat_signed_fraction_eq_zero
    p 4 239 (2 * j + 1) j hp
    (prime_gt_five_not_dvd_four p hp hpgt)
    (prime_ne_239_not_dvd_239 p hp hp239) hexp
    (by norm_num) (by norm_num) (by omega)

/-- Two terms that are individually zero or have nonnegative valuation
have a nonnegative-valuation sum whenever that sum is nonzero. -/
lemma padicValRat_add_nonneg_of_each_nonneg
    (p : ℕ) (hp : p.Prime) {q r : ℚ}
    (hq : q = 0 ∨ 0 ≤ padicValRat p q)
    (hr : r = 0 ∨ 0 ≤ padicValRat p r)
    (hqr : q + r ≠ 0) :
    0 ≤ padicValRat p (q + r) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hq with rfl | hqval
  · simpa using hr.resolve_left (by simpa using hqr)
  rcases hr with rfl | hrval
  · simpa using hqval
  exact le_trans (le_min hqval hrval)
    (padicValRat.min_le_padicValRat_add hqr)

/-- Every nonsingular term of the unscaled seed is `p`-integral. -/
lemma padicValRat_seedRegularBlockRat_nonneg
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239)
    (hpLower : 12 * N + 15 < 2 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hpdef : p = 2 * k + 1)
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
          (upperHalfPrime_not_dvd_regular_common_exponent
            N k p j hpLower hpdef hj)]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · refine Or.inr ?_
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_seed239TermRat_eq_zero p j hp hp239 hpgt
          (upperHalfPrime_not_dvd_regular_common_exponent
            N k p j hpLower hpdef hj)]
      · exact hG0
  have hendpoint : ¬ p ∣ 2 * seedCommonTermCount N + 1 := by
    have h := upperHalfPrime_not_dvd_endpoint
      N p hpgt hpLower hpUpper
    have heq : 2 * seedCommonTermCount N + 1 = 12 * N + 17 := by
      simp [seedCommonTermCount]
      omega
    rw [heq]
    exact h
  have hEval : padicValRat p E = 0 := by
    exact padicValRat_seed239TermRat_eq_zero
      p (seedCommonTermCount N) hp hp239 hpgt hendpoint
  have hE : E = 0 ∨ 0 ≤ padicValRat p E :=
    Or.inr (by rw [hEval])
  have hFG : F + G = 0 ∨ 0 ≤ padicValRat p (F + G) := by
    by_cases hFG0 : F + G = 0
    · exact Or.inl hFG0
    · exact Or.inr
        (padicValRat_add_nonneg_of_each_nonneg p hp hF hG hFG0)
  change 0 ≤ padicValRat p ((F + G) + E)
  have hFGE : (F + G) + E ≠ 0 := by
    simpa [F, G, E, seedRegularBlockRat] using hregular
  exact padicValRat_add_nonneg_of_each_nonneg p hp hFG hE hFGE

/-- The complete unscaled Machin seed prefix has valuation `-1` at every
admissible upper-half prime. -/
theorem padicValRat_machinLowerRat_seed_upperHalfPrime
    (N k p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpLower : 12 * N + 15 < 2 * p)
    (hpUpper : p ≤ 12 * N + 15)
    (hpdef : p = 2 * k + 1)
    (hk : k < seedCommonTermCount N) :
    padicValRat p (machinLowerRat (3 * (N + 1))) = -1 := by
  rw [machinLowerRat_seed_eq_regular_add_singular N k p hpdef hk]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_seed_singular_pair p k hp hpgt hp239 hp317
  · by_cases hregular : seedRegularBlockRat N k = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_seedRegularBlockRat_nonneg
          N k p hp hpgt hp239 hpLower hpUpper hpdef hregular)

lemma padicValRat_ten_pow_eq_zero_of_prime_gt_five
    (n p : ℕ) (hp : p.Prime) (hpgt : 5 < p) :
    padicValRat p ((10 : ℚ) ^ n) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hten : ¬ p ∣ 10 := by
    intro hdvd
    have hle : p ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
    have hsplit : p ∣ 2 ∨ p ∣ 5 := hp.dvd_mul.mp (by norm_num at hdvd ⊢; exact hdvd)
    rcases hsplit with h2 | h5
    · have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega
    · have hle5 : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
      omega
  have htenVal : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hten
  rw [padicValRat.pow (by norm_num), htenVal]
  norm_num

/-- Main seed-survival theorem.  The upper-half condition is written as
`d < 2*p` with `d = 12*N+15`, a division-free equivalent of `d/2 < p`
because `d` is odd. -/
theorem padicValRat_sampledMachinValueRat_upperHalfPrime
    (N p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpLower : 12 * N + 15 < 2 * p)
    (hpUpper : p ≤ 12 * N + 15) :
    padicValRat p (sampledMachinValueRat (N + 1)) = -1 := by
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two (by omega)
  have hpdef : p = 2 * k + 1 := by omega
  have hk : k < seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  have hblock := padicValRat_machinLowerRat_seed_upperHalfPrime
    N k p hp hpgt hp239 hp317 hpLower hpUpper hpdef hk
  have hblock0 : machinLowerRat (3 * (N + 1)) ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
  letI : Fact p.Prime := ⟨hp⟩
  unfold sampledMachinValueRat
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_ten_pow_eq_zero_of_prime_gt_five (N + 1) p hp hpgt,
    hblock]
  norm_num

/-- Reduced-denominator form of the same survival statement. -/
theorem upperHalfPrime_dvd_sampledMachinValueRat_den
    (N p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpLower : 12 * N + 15 < 2 * p)
    (hpUpper : p ≤ 12 * N + 15) :
    p ∣ (sampledMachinValueRat (N + 1)).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_sampledMachinValueRat_upperHalfPrime
    N p hp hpgt hp239 hp317 hpLower hpUpper]
  norm_num

/-- Exact reduced-denominator multiplicity: an admissible upper-half prime
occurs once, not merely at least once. -/
theorem padicValNat_sampledMachinValueRat_den_upperHalfPrime
    (N p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hp239 : p ≠ 239) (hp317 : p ≠ 317)
    (hpLower : 12 * N + 15 < 2 * p)
    (hpUpper : p ≤ 12 * N + 15) :
    padicValNat p (sampledMachinValueRat (N + 1)).den = 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_sampledMachinValueRat_upperHalfPrime
      N p hp hpgt hp239 hp317 hpLower hpUpper
  have hden : p ∣ q.den :=
    upperHalfPrime_dvd_sampledMachinValueRat_den
      N p hp hpgt hp239 hp317 hpLower hpUpper
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs :=
    hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

end Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival

#print axioms
  Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival.padicValRat_machinLowerRat_seed_upperHalfPrime
#print axioms
  Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival.padicValRat_sampledMachinValueRat_upperHalfPrime
#print axioms
  Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival.upperHalfPrime_dvd_sampledMachinValueRat_den
