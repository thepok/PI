import TheoryLib.PiQuantitativeBlockHitting.T48T48MachinSeedUpperHalfPrimeSurvival

/-!
# T52: exact persistent three-primary part of the fixed Machin seed

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For the sampled seed at index `N+1`, put `d = 12*N+15`.  If
`3^a <= d < 3^(a+1)`, the common Taylor exponent `3^a` is the unique odd
exponent at or below `d` with maximal three-adic order.  The two Machin
terms at every common odd exponent `u` combine with numerator
`4*239^u-5^u`, whose three-adic order is exactly one.  Consequently the
pair at `u=3^a` has strictly smaller valuation than every other common pair,
while the extra base-239 endpoint is three-integral.  The exact result is

`padicValRat 3 (sampledMachinValueRat (N+1)) = 1-a`.

This proves a persistent local denominator component.  It does not select
the complementary numerator phase and does not imply a decimal cylinder
hit, recurrence, density, normality, or the every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinSeedThreePrimaryPersistence

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinFixedModulusTelescoping
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival

/-- The cancellation factor is congruent to `3*5^u` modulo nine. -/
theorem machinCancellationFactor_cast_zmod_nine (u : ℕ) :
    (machinCancellationFactor u : ZMod 9) =
      3 * (5 : ZMod 9) ^ u := by
  simp only [machinCancellationFactor, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_pow]
  have h239 : (239 : ZMod 9) = 5 := by decide
  rw [h239]
  ring

/-- `3*5^u` is nonzero modulo nine. -/
lemma three_mul_five_pow_ne_zero_zmod_nine (u : ℕ) :
    (3 : ZMod 9) * (5 : ZMod 9) ^ u ≠ 0 := by
  have hu : IsUnit ((5 : ZMod 9) ^ u) :=
    ((ZMod.isUnit_iff_coprime 5 9).2 (by norm_num)).pow u
  intro hzero
  have hcancel : (3 : ZMod 9) = 0 := by
    apply hu.mul_right_cancel
    simpa using hzero
  have hne : (3 : ZMod 9) ≠ 0 := by
    intro hzero
    have hdvd : (9 : ℤ) ∣ 3 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (3 : ℤ) 9).mp
        (by exact_mod_cast hzero)
    norm_num at hdvd
  exact hne hcancel

/-- Every cancellation factor is divisible by three. -/
lemma three_dvd_machinCancellationFactor (u : ℕ) :
    (3 : ℤ) ∣ machinCancellationFactor u := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  simp only [machinCancellationFactor, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_pow]
  have h239 : (239 : ZMod 3) = 2 := by decide
  have h5 : (5 : ZMod 3) = 2 := by decide
  have h4 : (4 : ZMod 3) = 1 := by decide
  rw [h239, h5, h4]
  ring

/-- No cancellation factor is divisible by nine. -/
lemma nine_not_dvd_machinCancellationFactor (u : ℕ) :
    ¬ (9 : ℤ) ∣ machinCancellationFactor u := by
  intro hdvd
  have hzero : (machinCancellationFactor u : ZMod 9) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).2 hdvd
  rw [machinCancellationFactor_cast_zmod_nine] at hzero
  exact three_mul_five_pow_ne_zero_zmod_nine u hzero

/-- Exact three-adic order of the Machin cancellation factor. -/
theorem padicValInt_three_machinCancellationFactor (u : ℕ) :
    padicValInt 3 (machinCancellationFactor u) = 1 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h1 : 1 ≤ padicValInt 3 (machinCancellationFactor u) := by
    have h :=
      (padicValInt_dvd_iff (p := 3) 1
        (machinCancellationFactor u)).mp (by
          simpa using three_dvd_machinCancellationFactor u)
    rcases h with hzero | hle
    · exact False.elim
        (nine_not_dvd_machinCancellationFactor u (by simp [hzero]))
    · exact hle
  have hn2 : ¬ 2 ≤ padicValInt 3 (machinCancellationFactor u) := by
    intro h2
    have hd :=
      (padicValInt_dvd_iff (p := 3) 2
        (machinCancellationFactor u)).2 (Or.inr h2)
    norm_num at hd
    exact nine_not_dvd_machinCancellationFactor u hd
  omega

/-- Every combined common-exponent Machin pair has valuation one minus the
three-adic order of its odd exponent. -/
theorem padicValRat_three_interiorSingularPairRat
    (u k : ℕ) (hu : 0 < u) :
    padicValRat 3 (interiorSingularPairRat u k) =
      1 - (padicValNat 3 u : ℤ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have h5q : (5 : ℚ) ≠ 0 := by norm_num
  have h239q : (239 : ℚ) ≠ 0 := by norm_num
  have hfactorZ : machinCancellationFactor u ≠ 0 := by
    intro hzero
    exact nine_not_dvd_machinCancellationFactor u (by simp [hzero])
  have hfactorQ : (machinCancellationFactor u : ℚ) ≠ 0 := by
    exact_mod_cast hfactorZ
  have hnum0 :
      4 * (-1 : ℚ) ^ k * (machinCancellationFactor u : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (by norm_num))) hfactorQ
  have hden0 : (u : ℚ) * 5 ^ u * 239 ^ u ≠ 0 :=
    mul_ne_zero (mul_ne_zero huq (pow_ne_zero _ h5q))
      (pow_ne_zero _ h239q)
  have hval4 : padicValRat 3 (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 3 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat 3 (machinCancellationFactor u : ℚ) = 1 := by
    rw [padicValRat.of_int, padicValInt_three_machinCancellationFactor]
    norm_num
  have hval5 : padicValRat 3 (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hval239 : padicValRat 3 (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalu : padicValRat 3 (u : ℚ) = (padicValNat 3 u : ℤ) := by
    rw [padicValRat.of_nat]
  unfold interiorSingularPairRat
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hfactorQ,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.pow (by norm_num), hval4, hvalNegOne, hvalFactor,
    padicValRat.mul (mul_ne_zero huq (pow_ne_zero _ h5q))
      (pow_ne_zero _ h239q),
    padicValRat.mul huq (pow_ne_zero _ h5q),
    hvalu, padicValRat.pow h5q, hval5,
    padicValRat.pow h239q, hval239]
  norm_num

/-- The common pair at Taylor index `k`. -/
def threePrimaryCommonPairRat (k : ℕ) : ℚ :=
  seedFiveTermRat k + seed239TermRat k

/-- All common pairs except the distinguished one, followed by the single
extra base-239 endpoint. -/
def threePrimaryRegularSeedRat (N k : ℕ) : ℚ :=
  (∑ j ∈ (range (seedCommonTermCount N)).erase k,
      threePrimaryCommonPairRat j) +
    seed239TermRat (seedCommonTermCount N)

lemma threePrimaryCommonPairRat_eq
    (u k : ℕ) (hu : u = 2 * k + 1) :
    threePrimaryCommonPairRat k = interiorSingularPairRat u k := by
  unfold threePrimaryCommonPairRat
  exact seed_singular_pair_eq u k hu

/-- Exact decomposition of the seed into one distinguished combined pair
and the regular paired remainder. -/
theorem machinLowerRat_seed_eq_threePrimaryRegular_add_pair
    (N k u : ℕ) (hu : u = 2 * k + 1)
    (hk : k < seedCommonTermCount N) :
    machinLowerRat (3 * (N + 1)) =
      threePrimaryRegularSeedRat N k + interiorSingularPairRat u k := by
  have hkmem : k ∈ range (seedCommonTermCount N) := mem_range.2 hk
  have hpair :=
    sum_erase_add (range (seedCommonTermCount N))
      threePrimaryCommonPairRat hkmem
  rw [machinLowerRat_seed_eq]
  rw [← sum_add_distrib]
  rw [show
      (∑ x ∈ range (seedCommonTermCount N),
        (seedFiveTermRat x + seed239TermRat x)) =
        (∑ x ∈ (range (seedCommonTermCount N)).erase k,
          threePrimaryCommonPairRat x) + threePrimaryCommonPairRat k by
      simpa [threePrimaryCommonPairRat] using hpair.symm]
  rw [threePrimaryCommonPairRat_eq u k hu]
  unfold threePrimaryRegularSeedRat
  ring

/-- An integer below `3^(a+1)` has three-adic order at most `a`. -/
lemma padicValNat_three_le_of_lt_pow_succ
    (u a : ℕ) (hu : u ≠ 0) (hlt : u < 3 ^ (a + 1)) :
    padicValNat 3 u ≤ a := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hnot
  have ha : a + 1 ≤ padicValNat 3 u := by omega
  have hdvd : 3 ^ (a + 1) ∣ u :=
    (padicValNat_dvd_iff_le hu).2 ha
  have hle : 3 ^ (a + 1) ≤ u :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hdvd
  omega

/-- Below `3^(a+1)`, the unique odd integer of exact three-adic order `a`
is `3^a`. -/
lemma odd_eq_three_pow_of_padicValNat_eq
    (u d a : ℕ) (hu : 0 < u) (huodd : Odd u)
    (hud : u ≤ d) (hdlt : d < 3 ^ (a + 1))
    (hval : padicValNat 3 u = a) :
    u = 3 ^ a := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdvd : 3 ^ a ∣ u :=
    (padicValNat_dvd_iff_le (Nat.ne_of_gt hu)).2 (by omega)
  obtain ⟨k, hk⟩ := hdvd
  have hpowpos : 0 < 3 ^ a := by positivity
  have hkpos : 0 < k := by
    by_contra hnot
    have hkzero : k = 0 := by omega
    simp [hkzero] at hk
    omega
  have hklt : k < 3 := by
    rw [pow_succ] at hdlt
    rw [hk] at hud
    have hmullt : 3 ^ a * k < 3 ^ a * 3 := by omega
    exact (Nat.mul_lt_mul_left hpowpos).mp hmullt
  interval_cases k
  · simpa using hk
  · rcases huodd with ⟨t, ht⟩
    omega

/-- Valuation formula for a common pair, indexed by its odd exponent. -/
theorem padicValRat_three_threePrimaryCommonPairRat (k : ℕ) :
    padicValRat 3 (threePrimaryCommonPairRat k) =
      1 - (padicValNat 3 (2 * k + 1) : ℤ) := by
  rw [threePrimaryCommonPairRat_eq (2 * k + 1) k rfl]
  exact padicValRat_three_interiorSingularPairRat
    (2 * k + 1) k (by omega)

/-- A base-239 seed term is a three-adic unit whenever its odd linear
denominator is not divisible by three. -/
lemma padicValRat_three_seed239TermRat_of_not_dvd
    (k : ℕ) (hnot : ¬ 3 ∣ 2 * k + 1) :
    padicValRat 3 (seed239TermRat k) = 0 := by
  rw [seed239TermRat_eq_fraction, padicValRat.neg]
  exact padicValRat_signed_fraction_eq_zero
    3 4 239 (2 * k + 1) k (by norm_num)
    (by norm_num) (by norm_num) hnot
    (by norm_num) (by norm_num) (by omega)

/-- The extra endpoint exponent `12*N+17` is a three-adic unit. -/
theorem padicValRat_three_seed239TermRat_endpoint (N : ℕ) :
    padicValRat 3 (seed239TermRat (seedCommonTermCount N)) = 0 := by
  apply padicValRat_three_seed239TermRat_of_not_dvd
  intro hdvd
  obtain ⟨t, ht⟩ := hdvd
  simp [seedCommonTermCount] at ht
  omega

/-- The exponent selected by `12*N+15 < 3^(a+1)` is at least two. -/
lemma two_le_threePrimaryExponent
    (N a : ℕ) (hhigh : 12 * N + 15 < 3 ^ (a + 1)) :
    2 ≤ a := by
  by_contra hnot
  have ha : a ≤ 1 := by omega
  interval_cases a <;> norm_num at hhigh <;> omega

/-- Every common pair other than the unique maximal-order pair has
valuation at least `2-a`. -/
lemma padicValRat_three_regularCommonPair_ge
    (N a k j : ℕ)
    (hhigh : 12 * N + 15 < 3 ^ (a + 1))
    (hkpow : 3 ^ a = 2 * k + 1)
    (hj : j ∈ (range (seedCommonTermCount N)).erase k) :
    (2 : ℤ) - a ≤ padicValRat 3 (threePrimaryCommonPairRat j) := by
  have hjlt : j < seedCommonTermCount N :=
    mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have huPos : 0 < 2 * j + 1 := by omega
  have huOdd : Odd (2 * j + 1) := ⟨j, by omega⟩
  have huLe : 2 * j + 1 ≤ 12 * N + 15 := by
    simp [seedCommonTermCount] at hjlt
    omega
  have huLt : 2 * j + 1 < 3 ^ (a + 1) :=
    lt_of_le_of_lt huLe hhigh
  have hvalLe : padicValNat 3 (2 * j + 1) ≤ a :=
    padicValNat_three_le_of_lt_pow_succ
      (2 * j + 1) a (by omega) huLt
  have hvalNe : padicValNat 3 (2 * j + 1) ≠ a := by
    intro hvalEq
    have huniq := odd_eq_three_pow_of_padicValNat_eq
      (2 * j + 1) (12 * N + 15) a huPos huOdd huLe hhigh hvalEq
    apply hjne
    omega
  have hvalLt : padicValNat 3 (2 * j + 1) < a := by omega
  rw [padicValRat_three_threePrimaryCommonPairRat]
  have hcast :
      (padicValNat 3 (2 * j + 1) : ℤ) < (a : ℤ) := by
    exact_mod_cast hvalLt
  omega

/-- A finite sum of terms above a common three-adic valuation threshold is
either zero or remains above that threshold. -/
lemma padicValRat_three_sum_lower
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) (c : ℤ)
    (hf : ∀ x ∈ s, c ≤ padicValRat 3 (f x)) :
    (∑ x ∈ s, f x) = 0 ∨
      c ≤ padicValRat 3 (∑ x ∈ s, f x) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      rw [sum_insert hxs]
      have hxval : c ≤ padicValRat 3 (f x) :=
        hf x (mem_insert_self x s)
      have hsprop := ih (fun y hy => hf y (mem_insert_of_mem hy))
      by_cases hx0 : f x = 0
      · simpa [hx0] using hsprop
      by_cases hs0 : (∑ y ∈ s, f y) = 0
      · simp [hs0, hx0, hxval]
      rcases hsprop with hsprop | hsval
      · exact False.elim (hs0 hsprop)
      by_cases hsum0 : f x + ∑ y ∈ s, f y = 0
      · exact Or.inl hsum0
      · refine Or.inr (le_trans (le_min hxval hsval) ?_)
        exact padicValRat.min_le_padicValRat_add hsum0

/-- Two possibly-zero terms above a common threshold have a sum which is
either zero or remains above that threshold. -/
lemma padicValRat_three_add_lower
    (q r : ℚ) (c : ℤ)
    (hq : q = 0 ∨ c ≤ padicValRat 3 q)
    (hr : r = 0 ∨ c ≤ padicValRat 3 r) :
    q + r = 0 ∨ c ≤ padicValRat 3 (q + r) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_cases hsum0 : q + r = 0
  · exact Or.inl hsum0
  rcases hq with rfl | hqval
  · exact Or.inr (by
      simpa using hr.resolve_left (by simpa using hsum0))
  rcases hr with rfl | hrval
  · exact Or.inr (by simpa using hqval)
  exact Or.inr (le_trans (le_min hqval hrval)
    (padicValRat.min_le_padicValRat_add hsum0))

/-- The complete paired regular remainder is either zero or has valuation
at least `2-a`. -/
theorem padicValRat_three_threePrimaryRegularSeedRat_ge_or_zero
    (N a k : ℕ)
    (hhigh : 12 * N + 15 < 3 ^ (a + 1))
    (hkpow : 3 ^ a = 2 * k + 1) :
    threePrimaryRegularSeedRat N k = 0 ∨
      (2 : ℤ) - a ≤
        padicValRat 3 (threePrimaryRegularSeedRat N k) := by
  let A := (range (seedCommonTermCount N)).erase k
  let S : ℚ := ∑ j ∈ A, threePrimaryCommonPairRat j
  let E : ℚ := seed239TermRat (seedCommonTermCount N)
  have hS : S = 0 ∨ (2 : ℤ) - a ≤ padicValRat 3 S := by
    unfold S
    apply padicValRat_three_sum_lower
    intro j hj
    exact padicValRat_three_regularCommonPair_ge
      N a k j hhigh hkpow hj
  have ha2 : 2 ≤ a := two_le_threePrimaryExponent N a hhigh
  have hEval : padicValRat 3 E = 0 := by
    exact padicValRat_three_seed239TermRat_endpoint N
  have hE : E = 0 ∨ (2 : ℤ) - a ≤ padicValRat 3 E := by
    exact Or.inr (by rw [hEval]; omega)
  have h := padicValRat_three_add_lower S E ((2 : ℤ) - a) hS hE
  simpa [threePrimaryRegularSeedRat, S, E, A] using h

/-- The unscaled fixed Machin seed has exact valuation `1-a`. -/
theorem padicValRat_three_machinLowerRat_seed
    (N a : ℕ)
    (hlow : 3 ^ a ≤ 12 * N + 15)
    (hhigh : 12 * N + 15 < 3 ^ (a + 1)) :
    padicValRat 3 (machinLowerRat (3 * (N + 1))) =
      1 - (a : ℤ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ha2 : 2 ≤ a := two_le_threePrimaryExponent N a hhigh
  have hodd : Odd (3 ^ a) := (by norm_num : Odd (3 : ℕ)).pow
  obtain ⟨k, hkpow⟩ := hodd
  have hklt : k < seedCommonTermCount N := by
    simp [seedCommonTermCount]
    omega
  have hpairVal :
      padicValRat 3 (interiorSingularPairRat (3 ^ a) k) =
        1 - (a : ℤ) := by
    rw [padicValRat_three_interiorSingularPairRat
      (3 ^ a) k (by positivity), padicValNat.prime_pow]
  have hpair0 : interiorSingularPairRat (3 ^ a) k ≠ 0 := by
    intro hzero
    simp [hzero] at hpairVal
    omega
  have hreg :=
    padicValRat_three_threePrimaryRegularSeedRat_ge_or_zero
      N a k hhigh hkpow
  rw [machinLowerRat_seed_eq_threePrimaryRegular_add_pair
    N k (3 ^ a) hkpow hklt]
  by_cases hreg0 : threePrimaryRegularSeedRat N k = 0
  · simp [hreg0, hpairVal]
  have hregVal := hreg.resolve_left hreg0
  have hsum0 :
      threePrimaryRegularSeedRat N k +
        interiorSingularPairRat (3 ^ a) k ≠ 0 := by
    intro hzero
    have heq : threePrimaryRegularSeedRat N k =
        -interiorSingularPairRat (3 ^ a) k := by linarith
    have hvals := congrArg (padicValRat 3) heq
    rw [padicValRat.neg, hpairVal] at hvals
    omega
  rw [add_comm]
  calc
    padicValRat 3
        (interiorSingularPairRat (3 ^ a) k +
          threePrimaryRegularSeedRat N k) =
        padicValRat 3 (interiorSingularPairRat (3 ^ a) k) := by
      apply padicValRat.add_eq_of_lt (p := 3)
      · simpa [add_comm] using hsum0
      · exact hpair0
      · exact hreg0
      · rw [hpairVal]
        omega
    _ = 1 - (a : ℤ) := hpairVal

/-- Decimal scaling is a three-adic unit. -/
lemma padicValRat_three_ten_pow (n : ℕ) :
    padicValRat 3 ((10 : ℚ) ^ n) = 0 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hten : padicValRat 3 (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  rw [padicValRat.pow (by norm_num), hten]
  norm_num

/-- Main three-primary seed theorem.  For `j=N+1`, its inequalities are
exactly `3^a ≤ 12*j+3 < 3^(a+1)`. -/
theorem padicValRat_three_sampledMachinValueRat
    (N a : ℕ)
    (hlow : 3 ^ a ≤ 12 * N + 15)
    (hhigh : 12 * N + 15 < 3 ^ (a + 1)) :
    padicValRat 3 (sampledMachinValueRat (N + 1)) =
      1 - (a : ℤ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hblock := padicValRat_three_machinLowerRat_seed N a hlow hhigh
  have ha2 := two_le_threePrimaryExponent N a hhigh
  have hblock0 : machinLowerRat (3 * (N + 1)) ≠ 0 := by
    intro hzero
    simp [hzero] at hblock
    omega
  unfold sampledMachinValueRat
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat_three_ten_pow, hblock]
  norm_num

/-- The reduced denominator is divisible by three. -/
theorem three_dvd_sampledMachinValueRat_den
    (N a : ℕ)
    (hlow : 3 ^ a ≤ 12 * N + 15)
    (hhigh : 12 * N + 15 < 3 ^ (a + 1)) :
    3 ∣ (sampledMachinValueRat (N + 1)).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_three_sampledMachinValueRat N a hlow hhigh]
  have ha2 := two_le_threePrimaryExponent N a hhigh
  omega

/-- Exact reduced-denominator multiplicity: the persistent three-primary
part is `3^(a-1)`. -/
theorem padicValNat_three_sampledMachinValueRat_den
    (N a : ℕ)
    (hlow : 3 ^ a ≤ 12 * N + 15)
    (hhigh : 12 * N + 15 < 3 ^ (a + 1)) :
    padicValNat 3 (sampledMachinValueRat (N + 1)).den = a - 1 := by
  let q := sampledMachinValueRat (N + 1)
  change padicValNat 3 q.den = a - 1
  have hval : padicValRat 3 q = 1 - (a : ℤ) :=
    padicValRat_three_sampledMachinValueRat N a hlow hhigh
  have hden : 3 ∣ q.den :=
    three_dvd_sampledMachinValueRat_den N a hlow hhigh
  have hcop : Nat.Coprime 3 q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ 3 ∣ q.num.natAbs :=
    (by norm_num : Nat.Prime 3).coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt 3 q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  have ha2 := two_le_threePrimaryExponent N a hhigh
  rw [padicValRat_def, hvnum] at hval
  omega

/-- Direct index form of the main theorem. -/
theorem padicValRat_three_sampledMachinValueRat_at_index
    (j a : ℕ) (hj : 1 ≤ j)
    (hlow : 3 ^ a ≤ 12 * j + 3)
    (hhigh : 12 * j + 3 < 3 ^ (a + 1)) :
    padicValRat 3 (sampledMachinValueRat j) = 1 - (a : ℤ) := by
  have hjEq : j = (j - 1) + 1 := by omega
  have hdEq : 12 * (j - 1) + 15 = 12 * j + 3 := by omega
  rw [hjEq]
  apply padicValRat_three_sampledMachinValueRat (j - 1) a
  · rwa [hdEq]
  · rwa [hdEq]

/-- Direct index form of the exact denominator multiplicity. -/
theorem padicValNat_three_sampledMachinValueRat_den_at_index
    (j a : ℕ) (hj : 1 ≤ j)
    (hlow : 3 ^ a ≤ 12 * j + 3)
    (hhigh : 12 * j + 3 < 3 ^ (a + 1)) :
    padicValNat 3 (sampledMachinValueRat j).den = a - 1 := by
  have hjEq : j = (j - 1) + 1 := by omega
  have hdEq : 12 * (j - 1) + 15 = 12 * j + 3 := by omega
  rw [hjEq]
  apply padicValNat_three_sampledMachinValueRat_den (j - 1) a
  · rwa [hdEq]
  · rwa [hdEq]

#print axioms padicValInt_three_machinCancellationFactor
#print axioms padicValRat_three_interiorSingularPairRat
#print axioms padicValRat_three_machinLowerRat_seed
#print axioms padicValRat_three_sampledMachinValueRat_at_index
#print axioms padicValNat_three_sampledMachinValueRat_den_at_index

end Theory.PiDigits.MachinSeedThreePrimaryPersistence
