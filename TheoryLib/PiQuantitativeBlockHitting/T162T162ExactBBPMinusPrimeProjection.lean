import TheoryLib.PiQuantitativeBlockHitting.T161T161SafeLaterBBPPrimeProjection

/-!
# T162: exact lower-band minus-prime projections of the sampled BBP rational

For primes `p ≡ 3,7 (mod 8)` in the band
`14*m+1 < p ≤ 28*m+3`, the fourth BBP pole is always present.  Depending on
whether a compatible `3*p` pole has entered the sevenfold prefix, the exact
local residue is `-2` or `-8/3`.  These are actual projections of
`scaledBBPRat`; no cancellation or distribution statement is asserted.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Theory.PiDigits.T162ExactBBPMinusPrimeProjection

open Theory.PiDigits.T74ThreePrimaryDecimation
open Theory.PiDigits.T77SelectedPadicDefectShell
open Theory.PiDigits.T115SampledBBPCellDefectPhase
open Theory.PiDigits.T159ExactBBPTopPrimeProjection
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival

private lemma two_pow_half_eq_neg_one_of_prime_eq_eight_mul_add_three
    (a p : ℕ) (hp : p.Prime) (hpdef : p = 8 * a + 3) :
    (2 : ZMod p) ^ (4 * a + 1) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpmod : p % 8 = 3 := by omega
  have hnonsquare : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]
    omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    omega
  have hnotone : (2 : ZMod p) ^ (p / 2) ≠ 1 := by
    intro h
    exact hnonsquare ((ZMod.euler_criterion p htwo).2 h)
  have hneg :=
    (ZMod.pow_div_two_eq_neg_one_or_one p htwo).resolve_left hnotone
  have hhalf : p / 2 = 4 * a + 1 := by omega
  simpa [hhalf] using hneg

private lemma two_pow_half_eq_one_of_prime_eq_eight_mul_add_seven
    (a p : ℕ) (hp : p.Prime) (hpdef : p = 8 * a + 7) :
    (2 : ZMod p) ^ (4 * a + 3) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpmod : p % 8 = 7 := by omega
  have hsquare : IsSquare (2 : ZMod p) :=
    (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inr hpmod)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    omega
  have hone : (2 : ZMod p) ^ (p / 2) = 1 :=
    (ZMod.euler_criterion p htwo).1 hsquare
  have hhalf : p / 2 = 4 * a + 3 := by omega
  simpa [hhalf] using hone

private lemma four_mul_sixteen_pow_primary_eq_one
    (i p : ℕ) (hp : p.Prime) (hpdef : p = 4 * i + 3) :
    (4 : ZMod p) * 16 ^ i = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    omega
  have hor := ZMod.pow_div_two_eq_neg_one_or_one p htwo
  have hhalf : p / 2 = 2 * i + 1 := by omega
  rcases hor with hone | hneg
  · rw [hhalf] at hone
    calc
      (4 : ZMod p) * 16 ^ i = ((2 : ZMod p) ^ (2 * i + 1)) ^ 2 := by
        rw [show (4 : ZMod p) = 2 ^ 2 by norm_num,
          show (16 : ZMod p) = 2 ^ 4 by norm_num]
        simp only [← pow_add, ← pow_mul]
        congr 1 <;> omega
      _ = 1 := by rw [hone]; norm_num
  · rw [hhalf] at hneg
    calc
      (4 : ZMod p) * 16 ^ i = ((2 : ZMod p) ^ (2 * i + 1)) ^ 2 := by
        rw [show (4 : ZMod p) = 2 ^ 2 by norm_num,
          show (16 : ZMod p) = 2 ^ 4 by norm_num]
        simp only [← pow_add, ← pow_mul]
        congr 1 <;> omega
      _ = 1 := by rw [hneg]; norm_num

private lemma sixteen_pow_secondary_three_eq_neg_two
    (a p : ℕ) (hp : p.Prime) (hpdef : p = 8 * a + 3) :
    (16 : ZMod p) ^ (3 * a + 1) = -2 := by
  have h := two_pow_half_eq_neg_one_of_prime_eq_eight_mul_add_three a p hp hpdef
  have hexp : 4 * (3 * a + 1) = (4 * a + 1) * 3 + 1 := by omega
  calc
    (16 : ZMod p) ^ (3 * a + 1) =
        ((2 : ZMod p) ^ (4 * a + 1)) ^ 3 * 2 := by
      rw [show (16 : ZMod p) = 2 ^ 4 by norm_num]
      rw [← pow_mul, hexp, pow_add, pow_mul]
      norm_num
    _ = -2 := by rw [h]; ring

private lemma two_mul_sixteen_pow_secondary_seven_eq_one
    (a p : ℕ) (hp : p.Prime) (hpdef : p = 8 * a + 7) :
    (2 : ZMod p) * 16 ^ (3 * a + 2) = 1 := by
  have h := two_pow_half_eq_one_of_prime_eq_eight_mul_add_seven a p hp hpdef
  have hexp : 1 + 4 * (3 * a + 2) = (4 * a + 3) * 3 := by omega
  calc
    (2 : ZMod p) * 16 ^ (3 * a + 2) =
        ((2 : ZMod p) ^ (4 * a + 3)) ^ 3 := by
      rw [show (2 : ZMod p) = 2 ^ 1 by norm_num,
        show (16 : ZMod p) = 2 ^ 4 by norm_num,
        ← pow_mul, ← pow_add, hexp, pow_mul]
      simp only [pow_one]
    _ = 1 := by rw [h]; norm_num

private lemma primeCongruent_primary_four
    (i p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hpdef : p = 4 * i + 3) :
    PrimeCongruent p ((p : ℚ) * poleFour i) (-2) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow := four_mul_sixteen_pow_primary_eq_one i p hp hpdef
  have hpos : 1 ≤ 4 * 16 ^ i := by
    have : 0 < 16 ^ i := pow_pos (by omega) _
    omega
  have hdvd : p ∣ 4 * 16 ^ i - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    rw [Nat.cast_sub hpos]
    simpa using sub_eq_zero.mpr hpow
  unfold PrimeCongruent
  right
  have hnum0 : 4 * 16 ^ i - 1 ≠ 0 := by
    have : 0 < 16 ^ i := pow_pos (by omega) _
    omega
  have hvalnum : (1 : ℤ) ≤ padicValRat p (((4 * 16 ^ i - 1 : ℕ) : ℚ)) := by
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd hnum0 hdvd
  have h2val : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_two p hpgt)
  have h16val : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  have heq :
      (p : ℚ) * (-(1 : ℚ) / 2 / ((4 : ℚ) * i + 3) / 16 ^ i) - (-2) =
        (4 * (16 : ℚ) ^ i - 1) / (2 * 16 ^ i) := by
    rw [hpdef]
    push_cast
    field_simp
    ring
  change (1 : ℤ) ≤ padicValRat p
    ((p : ℚ) * (-(1 : ℚ) / 2 / ((4 : ℚ) * i + 3) / 16 ^ i) - (-2))
  rw [heq, padicValRat.div (by exact_mod_cast hnum0) (by positivity),
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)), h2val,
    padicValRat.pow (by norm_num), h16val]
  norm_num
  simpa [Nat.cast_sub hpos] using hvalnum

private lemma primeCongruent_secondary_one
    (a p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hpdef : p = 8 * a + 3) :
    PrimeCongruent p ((p : ℚ) * poleOne (3 * a + 1)) (-(2 : ℚ) / 3) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow := sixteen_pow_secondary_three_eq_neg_two a p hp hpdef
  have hdvd : p ∣ 16 ^ (3 * a + 1) + 2 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    push_cast
    simpa using (show (16 : ZMod p) ^ (3 * a + 1) + 2 = 0 by rw [hpow]; ring)
  unfold PrimeCongruent
  right
  have hnum0 : 16 ^ (3 * a + 1) + 2 ≠ 0 := by positivity
  have hvalnum : (1 : ℤ) ≤
      padicValRat p (((16 ^ (3 * a + 1) + 2 : ℕ) : ℚ)) := by
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd hnum0 hdvd
  have h2val : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_two p hpgt)
  have h3val : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by
      intro h
      have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h
      omega)
  have h16val : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  have heq :
      (p : ℚ) * poleOne (3 * a + 1) - (-(2 : ℚ) / 3) =
        2 * ((16 : ℚ) ^ (3 * a + 1) + 2) /
          (3 * 16 ^ (3 * a + 1)) := by
    simp only [poleOne]
    have hden : (8 : ℚ) * ((3 * a + 1 : ℕ) : ℚ) + 1 = 3 * (p : ℚ) := by
      norm_num [hpdef]
      ring
    rw [hden]
    push_cast
    field_simp
    ring
  change (1 : ℤ) ≤ padicValRat p
    ((p : ℚ) * poleOne (3 * a + 1) - (-(2 : ℚ) / 3))
  rw [heq, padicValRat.div (mul_ne_zero (by norm_num) (by exact_mod_cast hnum0))
      (by positivity),
    padicValRat.mul (by norm_num) (by exact_mod_cast hnum0),
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    h2val, h3val, padicValRat.pow (by norm_num), h16val]
  norm_num
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hvalnum

private lemma primeCongruent_secondary_three
    (a p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hpdef : p = 8 * a + 7) :
    PrimeCongruent p ((p : ℚ) * poleThree (3 * a + 2)) (-(2 : ℚ) / 3) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow := two_mul_sixteen_pow_secondary_seven_eq_one a p hp hpdef
  have hpos : 1 ≤ 2 * 16 ^ (3 * a + 2) := by
    have : 0 < 16 ^ (3 * a + 2) := pow_pos (by omega) _
    omega
  have hdvd : p ∣ 2 * 16 ^ (3 * a + 2) - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    rw [Nat.cast_sub hpos]
    simpa using sub_eq_zero.mpr hpow
  unfold PrimeCongruent
  right
  have hnum0 : 2 * 16 ^ (3 * a + 2) - 1 ≠ 0 := by
    have : 0 < 16 ^ (3 * a + 2) := pow_pos (by omega) _
    omega
  have hvalnum : (1 : ℤ) ≤
      padicValRat p (((2 * 16 ^ (3 * a + 2) - 1 : ℕ) : ℚ)) := by
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd hnum0 hdvd
  have h3val : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by
      intro h
      have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h
      omega)
  have h16val : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  have heq :
      (p : ℚ) * poleThree (3 * a + 2) - (-(2 : ℚ) / 3) =
        (2 * (16 : ℚ) ^ (3 * a + 2) - 1) /
          (3 * 16 ^ (3 * a + 2)) := by
    simp only [poleThree]
    have hden : (8 : ℚ) * ((3 * a + 2 : ℕ) : ℚ) + 5 = 3 * (p : ℚ) := by
      norm_num [hpdef]
      ring
    rw [hden]
    push_cast
    field_simp
    ring
  change (1 : ℤ) ≤ padicValRat p
    ((p : ℚ) * poleThree (3 * a + 2) - (-(2 : ℚ) / 3))
  rw [heq, padicValRat.div (by exact_mod_cast hnum0) (by positivity),
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)), h3val,
    padicValRat.pow (by norm_num), h16val]
  norm_num
  simpa only [Nat.cast_sub hpos, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    using hvalnum

def minusQuietRegularRat (m i : ℕ) : ℚ :=
  polePartial poleOne (7 * m) + polePartial poleTwo (7 * m) +
    polePartial poleThree (7 * m) +
      (∑ j ∈ (range (7 * m + 1)).erase i, poleFour j)

def minusThreeSecondaryRegularRat (m i s : ℕ) : ℚ :=
  (∑ j ∈ (range (7 * m + 1)).erase s, poleOne j) +
    polePartial poleTwo (7 * m) + polePartial poleThree (7 * m) +
      (∑ j ∈ (range (7 * m + 1)).erase i, poleFour j)

def minusSevenSecondaryRegularRat (m i s : ℕ) : ℚ :=
  polePartial poleOne (7 * m) + polePartial poleTwo (7 * m) +
    (∑ j ∈ (range (7 * m + 1)).erase s, poleThree j) +
      (∑ j ∈ (range (7 * m + 1)).erase i, poleFour j)

private lemma regular_nonneg
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hone : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * m, j ≠ i → ¬ p ∣ 4 * j + 3) :
    minusQuietRegularRat m i = 0 ∨
      0 ≤ padicValRat p (minusQuietRegularRat m i) := by
  have h1 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleOne) (by
      intro j hj
      exact padicValRat_poleOne_eq_zero p j hp hpgt
        (hone j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h2 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleTwo) (by
      intro j hj
      exact padicValRat_poleTwo_eq_zero p j hp hpgt
        (htwo j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h3 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleThree) (by
      intro j hj
      exact padicValRat_poleThree_eq_zero p j hp hpgt
        (hthree j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h4 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * m + 1)).erase i) (f := poleFour) (by
      intro j hj
      exact padicValRat_poleFour_eq_zero p j hp hpgt
        (hfour j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  unfold minusQuietRegularRat polePartial
  exact zero_or_padicValRat_add_nonneg hp
    (zero_or_padicValRat_add_nonneg hp
      (zero_or_padicValRat_add_nonneg hp h1 h2) h3) h4

private lemma threeSecondary_regular_nonneg
    (m i s p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hone : ∀ j ≤ 7 * m, j ≠ s → ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * m, j ≠ i → ¬ p ∣ 4 * j + 3) :
    minusThreeSecondaryRegularRat m i s = 0 ∨
      0 ≤ padicValRat p (minusThreeSecondaryRegularRat m i s) := by
  have h1 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * m + 1)).erase s) (f := poleOne) (by
      intro j hj
      exact padicValRat_poleOne_eq_zero p j hp hpgt
        (hone j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  have h2 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleTwo) (by
      intro j hj
      exact padicValRat_poleTwo_eq_zero p j hp hpgt
        (htwo j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h3 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleThree) (by
      intro j hj
      exact padicValRat_poleThree_eq_zero p j hp hpgt
        (hthree j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h4 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * m + 1)).erase i) (f := poleFour) (by
      intro j hj
      exact padicValRat_poleFour_eq_zero p j hp hpgt
        (hfour j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  unfold minusThreeSecondaryRegularRat polePartial
  exact zero_or_padicValRat_add_nonneg hp
    (zero_or_padicValRat_add_nonneg hp
      (zero_or_padicValRat_add_nonneg hp h1 h2) h3) h4

private lemma sevenSecondary_regular_nonneg
    (m i s p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hone : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * m, j ≠ s → ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * m, j ≠ i → ¬ p ∣ 4 * j + 3) :
    minusSevenSecondaryRegularRat m i s = 0 ∨
      0 ≤ padicValRat p (minusSevenSecondaryRegularRat m i s) := by
  have h1 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleOne) (by
      intro j hj
      exact padicValRat_poleOne_eq_zero p j hp hpgt
        (hone j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h2 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleTwo) (by
      intro j hj
      exact padicValRat_poleTwo_eq_zero p j hp hpgt
        (htwo j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h3 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * m + 1)).erase s) (f := poleThree) (by
      intro j hj
      exact padicValRat_poleThree_eq_zero p j hp hpgt
        (hthree j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  have h4 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * m + 1)).erase i) (f := poleFour) (by
      intro j hj
      exact padicValRat_poleFour_eq_zero p j hp hpgt
        (hfour j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  unfold minusSevenSecondaryRegularRat polePartial
  exact zero_or_padicValRat_add_nonneg hp
    (zero_or_padicValRat_add_nonneg hp
      (zero_or_padicValRat_add_nonneg hp h1 h2) h3) h4

private lemma PrimeCongruent.add
    {p : ℕ} (hp : p.Prime) {x y u v : ℚ}
    (hxy : PrimeCongruent p x y) (huv : PrimeCongruent p u v) :
    PrimeCongruent p (x + u) (y + v) := by
  unfold PrimeCongruent at hxy huv ⊢
  have hx : x - y = 0 ∨ (1 : ℤ) ≤ padicValRat p (x - y) :=
    hxy.imp sub_eq_zero.mpr id
  have hu : u - v = 0 ∨ (1 : ℤ) ≤ padicValRat p (u - v) :=
    huv.imp sub_eq_zero.mpr id
  have hadd := zero_or_padicValRat_add_ge_one hp hx hu
  rcases hadd with hz | hv
  · left
    linarith
  · right
    rw [show x + u - (y + v) = (x - y) + (u - v) by ring]
    exact hv

private lemma regular_primeCongruent_zero
    {p : ℕ} (hp : p.Prime) {x : ℚ}
    (hx : x = 0 ∨ 0 ≤ padicValRat p x) :
    PrimeCongruent p ((p : ℚ) * x) 0 := by
  unfold PrimeCongruent
  rcases mul_prime_zero_or_val_ge_one hp hx with hz | hv
  · exact Or.inl (by simpa using hz)
  · exact Or.inr (by simpa using hv)

private lemma bbpPartial_eq_minusQuiet_add
    (m i : ℕ) (hi : i ≤ 7 * m) :
    bbpPartial (7 * m) = minusQuietRegularRat m i + poleFour i := by
  have himem : i ∈ range (7 * m + 1) := mem_range.mpr (by omega)
  have hs := sum_erase_add (range (7 * m + 1)) poleFour himem
  unfold bbpPartial minusQuietRegularRat polePartial
  rw [← hs]
  ring

private lemma bbpPartial_eq_minusThreeSecondary_add
    (m i s : ℕ) (hi : i ≤ 7 * m) (hs : s ≤ 7 * m) :
    bbpPartial (7 * m) =
      minusThreeSecondaryRegularRat m i s + poleFour i + poleOne s := by
  have himem : i ∈ range (7 * m + 1) := mem_range.mpr (by omega)
  have hsmem : s ∈ range (7 * m + 1) := mem_range.mpr (by omega)
  have hiErase := sum_erase_add (range (7 * m + 1)) poleFour himem
  have hsErase := sum_erase_add (range (7 * m + 1)) poleOne hsmem
  unfold bbpPartial minusThreeSecondaryRegularRat polePartial
  rw [← hiErase, ← hsErase]
  ring

private lemma bbpPartial_eq_minusSevenSecondary_add
    (m i s : ℕ) (hi : i ≤ 7 * m) (hs : s ≤ 7 * m) :
    bbpPartial (7 * m) =
      minusSevenSecondaryRegularRat m i s + poleFour i + poleThree s := by
  have himem : i ∈ range (7 * m + 1) := mem_range.mpr (by omega)
  have hsmem : s ∈ range (7 * m + 1) := mem_range.mpr (by omega)
  have hiErase := sum_erase_add (range (7 * m + 1)) poleFour himem
  have hsErase := sum_erase_add (range (7 * m + 1)) poleThree hsmem
  unfold bbpPartial minusSevenSecondaryRegularRat polePartial
  rw [← hiErase, ← hsErase]
  ring

private lemma caseThree_poleTwo_not_dvd
    (m a p j : ℕ) (hlow : 14 * m + 1 < p) (hj : j ≤ 7 * m) :
    ¬ p ∣ 2 * j + 1 := by
  intro hd
  have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 1) hd
  omega

private lemma caseThree_poleFour_dvd_iff
    (m a p j : ℕ) (hlow : 14 * m + 1 < p)
    (hpdef : p = 8 * a + 3) (hj : j ≤ 7 * m) :
    p ∣ 4 * j + 3 ↔ j = 2 * a := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hc0 : 0 < c := by
      by_contra h
      have : c = 0 := by omega
      subst c
      simp at hc
    have hclt : c < 2 := by nlinarith
    interval_cases c
    omega
  · rintro rfl
    rw [show 4 * (2 * a) + 3 = p by omega]

private lemma caseThree_poleThree_not_dvd
    (m a p j : ℕ) (hlow : 14 * m + 1 < p)
    (hpdef : p = 8 * a + 3) (hj : j ≤ 7 * m) :
    ¬ p ∣ 8 * j + 5 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    subst c
    simp at hc
  have hclt : c < 4 := by nlinarith
  interval_cases c <;> omega

private lemma caseThree_poleOne_dvd_iff_active
    (m a p j : ℕ) (hlow : 14 * m + 1 < p)
    (hpdef : p = 8 * a + 3) (hj : j ≤ 7 * m) :
    p ∣ 8 * j + 1 ↔ j = 3 * a + 1 := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hc0 : 0 < c := by
      by_contra h
      have : c = 0 := by omega
      subst c
      simp at hc
    have hclt : c < 4 := by nlinarith
    interval_cases c <;> omega
  · rintro rfl
    rw [show 8 * (3 * a + 1) + 1 = 3 * p by omega]
    exact dvd_mul_left p 3

private lemma caseSeven_poleTwo_not_dvd
    (m a p j : ℕ) (hlow : 14 * m + 1 < p) (hj : j ≤ 7 * m) :
    ¬ p ∣ 2 * j + 1 := caseThree_poleTwo_not_dvd m a p j hlow hj

private lemma caseSeven_poleFour_dvd_iff
    (m a p j : ℕ) (hlow : 14 * m + 1 < p)
    (hpdef : p = 8 * a + 7) (hj : j ≤ 7 * m) :
    p ∣ 4 * j + 3 ↔ j = 2 * a + 1 := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hc0 : 0 < c := by
      by_contra h
      have : c = 0 := by omega
      subst c
      simp at hc
    have hclt : c < 2 := by nlinarith
    interval_cases c
    omega
  · rintro rfl
    rw [show 4 * (2 * a + 1) + 3 = p by omega]

private lemma caseSeven_poleOne_not_dvd
    (m a p j : ℕ) (hlow : 14 * m + 1 < p)
    (hpdef : p = 8 * a + 7) (hj : j ≤ 7 * m) :
    ¬ p ∣ 8 * j + 1 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    subst c
    simp at hc
  have hclt : c < 4 := by nlinarith
  interval_cases c <;> omega

private lemma caseSeven_poleThree_dvd_iff_active
    (m a p j : ℕ) (hlow : 14 * m + 1 < p)
    (hpdef : p = 8 * a + 7) (hj : j ≤ 7 * m) :
    p ∣ 8 * j + 5 ↔ j = 3 * a + 2 := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hc0 : 0 < c := by
      by_contra h
      have : c = 0 := by omega
      subst c
      simp at hc
    have hclt : c < 4 := by nlinarith
    interval_cases c <;> omega
  · rintro rfl
    rw [show 8 * (3 * a + 2) + 5 = 3 * p by omega]
    exact dvd_mul_left p 3

/-- In the `p = 8*a+3` minus band, before the optional `3*p` first-family
pole enters, the fourth-family pole is the only `p`-divisible pole. -/
theorem caseThree_quiet_unique_poles
    (m a p : ℕ) (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hquiet : 56 * m + 1 < 3 * p) (hpdef : p = 8 * a + 3) :
    2 * a ≤ 7 * m ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1) ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1) ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5) ∧
    (∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro j hj hd
    have hj' := (caseThree_poleOne_dvd_iff_active m a p j hlow hpdef hj).1 hd
    subst j
    omega
  · exact fun j hj ↦ caseThree_poleTwo_not_dvd m a p j hlow hj
  · exact fun j hj ↦ caseThree_poleThree_not_dvd m a p j hlow hpdef hj
  · exact fun j hj ↦ caseThree_poleFour_dvd_iff m a p j hlow hpdef hj

/-- In the `p = 8*a+3` active minus band, exactly the primary fourth-family
pole and the compatible `3*p` first-family pole are singular. -/
theorem caseThree_active_unique_poles
    (m a p : ℕ) (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hactive : 3 * p ≤ 56 * m + 1) (hpdef : p = 8 * a + 3) :
    2 * a ≤ 7 * m ∧ 3 * a + 1 ≤ 7 * m ∧
    (∀ j ≤ 7 * m, p ∣ 8 * j + 1 ↔ j = 3 * a + 1) ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1) ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5) ∧
    (∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a) := by
  exact ⟨by omega, by omega,
    fun j hj ↦ caseThree_poleOne_dvd_iff_active m a p j hlow hpdef hj,
    fun j hj ↦ caseThree_poleTwo_not_dvd m a p j hlow hj,
    fun j hj ↦ caseThree_poleThree_not_dvd m a p j hlow hpdef hj,
    fun j hj ↦ caseThree_poleFour_dvd_iff m a p j hlow hpdef hj⟩

/-- In the `p = 8*a+7` minus band, before the optional `3*p` third-family
pole enters, the fourth-family pole is the only `p`-divisible pole. -/
theorem caseSeven_quiet_unique_poles
    (m a p : ℕ) (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hquiet : 56 * m + 5 < 3 * p) (hpdef : p = 8 * a + 7) :
    2 * a + 1 ≤ 7 * m ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1) ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1) ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5) ∧
    (∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a + 1) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · exact fun j hj ↦ caseSeven_poleOne_not_dvd m a p j hlow hpdef hj
  · exact fun j hj ↦ caseSeven_poleTwo_not_dvd m a p j hlow hj
  · intro j hj hd
    have hj' := (caseSeven_poleThree_dvd_iff_active m a p j hlow hpdef hj).1 hd
    subst j
    omega
  · exact fun j hj ↦ caseSeven_poleFour_dvd_iff m a p j hlow hpdef hj

/-- In the `p = 8*a+7` active minus band, exactly the primary fourth-family
pole and the compatible `3*p` third-family pole are singular. -/
theorem caseSeven_active_unique_poles
    (m a p : ℕ) (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hactive : 3 * p ≤ 56 * m + 5) (hpdef : p = 8 * a + 7) :
    2 * a + 1 ≤ 7 * m ∧ 3 * a + 2 ≤ 7 * m ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1) ∧
    (∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1) ∧
    (∀ j ≤ 7 * m, p ∣ 8 * j + 5 ↔ j = 3 * a + 2) ∧
    (∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a + 1) := by
  exact ⟨by omega, by omega,
    fun j hj ↦ caseSeven_poleOne_not_dvd m a p j hlow hpdef hj,
    fun j hj ↦ caseSeven_poleTwo_not_dvd m a p j hlow hj,
    fun j hj ↦ caseSeven_poleThree_dvd_iff_active m a p j hlow hpdef hj,
    fun j hj ↦ caseSeven_poleFour_dvd_iff m a p j hlow hpdef hj⟩

private lemma bbpPartial_minusThree_quiet_projection
    (m a p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hi : 2 * a ≤ 7 * m)
    (hone : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a)
    (hpdef : p = 8 * a + 3) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * m)) (-2) := by
  have hr := regular_primeCongruent_zero hp
    (regular_nonneg m (2 * a) p hp hpgt hone htwo hthree
      (fun j hj hne ↦ (hfour j hj).not.mpr hne))
  have hs := primeCongruent_primary_four (2 * a) p hp hpgt (by omega)
  have hadd := PrimeCongruent.add hp hr hs
  rw [bbpPartial_eq_minusQuiet_add m (2 * a) hi]
  convert hadd using 1 <;> ring

private lemma bbpPartial_minusThree_active_projection
    (m a p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hi : 2 * a ≤ 7 * m) (hs : 3 * a + 1 ≤ 7 * m)
    (hone : ∀ j ≤ 7 * m, p ∣ 8 * j + 1 ↔ j = 3 * a + 1)
    (htwo : ∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a)
    (hpdef : p = 8 * a + 3) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * m)) (-(8 : ℚ) / 3) := by
  have hr := regular_primeCongruent_zero hp
    (threeSecondary_regular_nonneg m (2 * a) (3 * a + 1) p hp hpgt
      (fun j hj hne ↦ (hone j hj).not.mpr hne) htwo hthree
      (fun j hj hne ↦ (hfour j hj).not.mpr hne))
  have hprimary := primeCongruent_primary_four (2 * a) p hp hpgt (by omega)
  have hsecondary := primeCongruent_secondary_one a p hp hpgt hpdef
  have hsing := PrimeCongruent.add hp hprimary hsecondary
  have hadd := PrimeCongruent.add hp hr hsing
  rw [bbpPartial_eq_minusThreeSecondary_add m (2 * a) (3 * a + 1) hi hs]
  convert hadd using 1 <;> ring

private lemma bbpPartial_minusSeven_quiet_projection
    (m a p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hi : 2 * a + 1 ≤ 7 * m)
    (hone : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a + 1)
    (hpdef : p = 8 * a + 7) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * m)) (-2) := by
  have hr := regular_primeCongruent_zero hp
    (regular_nonneg m (2 * a + 1) p hp hpgt hone htwo hthree
      (fun j hj hne ↦ (hfour j hj).not.mpr hne))
  have hs := primeCongruent_primary_four (2 * a + 1) p hp hpgt (by omega)
  have hadd := PrimeCongruent.add hp hr hs
  rw [bbpPartial_eq_minusQuiet_add m (2 * a + 1) hi]
  convert hadd using 1 <;> ring

private lemma bbpPartial_minusSeven_active_projection
    (m a p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hi : 2 * a + 1 ≤ 7 * m) (hs : 3 * a + 2 ≤ 7 * m)
    (hone : ∀ j ≤ 7 * m, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * m, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * m, p ∣ 8 * j + 5 ↔ j = 3 * a + 2)
    (hfour : ∀ j ≤ 7 * m, p ∣ 4 * j + 3 ↔ j = 2 * a + 1)
    (hpdef : p = 8 * a + 7) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * m)) (-(8 : ℚ) / 3) := by
  have hr := regular_primeCongruent_zero hp
    (sevenSecondary_regular_nonneg m (2 * a + 1) (3 * a + 2) p hp hpgt
      hone htwo (fun j hj hne ↦ (hthree j hj).not.mpr hne)
      (fun j hj hne ↦ (hfour j hj).not.mpr hne))
  have hprimary := primeCongruent_primary_four (2 * a + 1) p hp hpgt (by omega)
  have hsecondary := primeCongruent_secondary_three a p hp hpgt hpdef
  have hsing := PrimeCongruent.add hp hprimary hsecondary
  have hadd := PrimeCongruent.add hp hr hsing
  rw [bbpPartial_eq_minusSevenSecondary_add m (2 * a + 1) (3 * a + 2) hi hs]
  convert hadd using 1 <;> ring

/-- Actual scaled BBP projection with residue `-2` in the quiet
`p = 8*a+3` minus band. -/
theorem scaledBBPRat_minusThreeProjection_of_quiet
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hquiet : 56 * m + 1 < 3 * p) (hpdef : p = 8 * a + 3) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat m)
      ((-2 : ℚ) * (10 : ℚ) ^ m) := by
  have hpgt : 5 < p := by omega
  rcases caseThree_quiet_unique_poles m a p hlow hupper hquiet hpdef with
    ⟨hi, hone, htwo, hthree, hfour⟩
  have hpartial := bbpPartial_minusThree_quiet_projection
    m a p hp hpgt hi hone htwo hthree hfour hpdef
  have h := PrimeCongruent.mul_ten_pow (m := m) hp hpgt hpartial
  unfold scaledBBPRat
  convert h using 1 <;> ring

/-- Actual scaled BBP projection with residue `-8/3` after the compatible
`3*p` first-family pole enters the `p = 8*a+3` minus band. -/
theorem scaledBBPRat_minusThreeProjection_of_secondary
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hactive : 3 * p ≤ 56 * m + 1) (hpdef : p = 8 * a + 3) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat m)
      ((-(8 : ℚ) / 3) * (10 : ℚ) ^ m) := by
  have hpgt : 5 < p := by omega
  rcases caseThree_active_unique_poles m a p hlow hupper hactive hpdef with
    ⟨hi, hs, hone, htwo, hthree, hfour⟩
  have hpartial := bbpPartial_minusThree_active_projection
    m a p hp hpgt hi hs hone htwo hthree hfour hpdef
  have h := PrimeCongruent.mul_ten_pow (m := m) hp hpgt hpartial
  unfold scaledBBPRat
  convert h using 1 <;> ring

/-- Actual scaled BBP projection with residue `-2` in the quiet
`p = 8*a+7` minus band. -/
theorem scaledBBPRat_minusSevenProjection_of_quiet
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hquiet : 56 * m + 5 < 3 * p) (hpdef : p = 8 * a + 7) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat m)
      ((-2 : ℚ) * (10 : ℚ) ^ m) := by
  have hpgt : 5 < p := by omega
  rcases caseSeven_quiet_unique_poles m a p hlow hupper hquiet hpdef with
    ⟨hi, hone, htwo, hthree, hfour⟩
  have hpartial := bbpPartial_minusSeven_quiet_projection
    m a p hp hpgt hi hone htwo hthree hfour hpdef
  have h := PrimeCongruent.mul_ten_pow (m := m) hp hpgt hpartial
  unfold scaledBBPRat
  convert h using 1 <;> ring

/-- Actual scaled BBP projection with residue `-8/3` after the compatible
`3*p` third-family pole enters the `p = 8*a+7` minus band. -/
theorem scaledBBPRat_minusSevenProjection_of_secondary
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hactive : 3 * p ≤ 56 * m + 5) (hpdef : p = 8 * a + 7) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat m)
      ((-(8 : ℚ) / 3) * (10 : ℚ) ^ m) := by
  have hpgt : 5 < p := by omega
  rcases caseSeven_active_unique_poles m a p hlow hupper hactive hpdef with
    ⟨hi, hs, hone, htwo, hthree, hfour⟩
  have hpartial := bbpPartial_minusSeven_active_projection
    m a p hp hpgt hi hs hone htwo hthree hfour hpdef
  have h := PrimeCongruent.mul_ten_pow (m := m) hp hpgt hpartial
  unfold scaledBBPRat
  convert h using 1 <;> ring

private lemma minusTwo_mul_ten_pow_unit
    (m p : ℕ) (hp : p.Prime) (hpgt : 5 < p) :
    padicValRat p ((-2 : ℚ) * (10 : ℚ) ^ m) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_two p hpgt)
  have h10 : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_ten p hp hpgt)
  rw [padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.neg, h2, padicValRat.pow (by norm_num), h10]
  norm_num

private lemma minusEightThird_mul_ten_pow_unit
    (m p : ℕ) (hp : p.Prime) (hpgt : 5 < p) :
    padicValRat p ((-(8 : ℚ) / 3) * (10 : ℚ) ^ m) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_two p hpgt)
  have h3 : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by
      intro h
      have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h
      omega)
  have h10 : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_ten p hp hpgt)
  have h8 : padicValRat p (8 : ℚ) = 0 := by
    rw [show (8 : ℚ) = 2 ^ 3 by norm_num, padicValRat.pow (by norm_num), h2]
    norm_num
  rw [padicValRat.mul (div_ne_zero (neg_ne_zero.mpr (by norm_num)) (by norm_num))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (neg_ne_zero.mpr (by norm_num)) (by norm_num),
    padicValRat.neg, h8, h3, padicValRat.pow (by norm_num), h10]
  norm_num

/-- Exact valuation `-1` in the quiet `p = 8*a+3` minus band. -/
theorem scaledBBPRat_minusThreeVal_of_quiet
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hquiet : 56 * m + 1 < 3 * p) (hpdef : p = 8 * a + 3) :
    padicValRat p (scaledBBPRat m) = -1 := by
  have hpgt : 5 < p := by omega
  exact scaledBBPRat_val_eq_neg_one_of_projection_of_unit m p hp
    (by positivity) (minusTwo_mul_ten_pow_unit m p hp hpgt)
    (scaledBBPRat_minusThreeProjection_of_quiet
      m a p hm hp hlow hupper hquiet hpdef)

/-- Exact valuation `-1` in the active `p = 8*a+3` minus band. -/
theorem scaledBBPRat_minusThreeVal_of_secondary
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hactive : 3 * p ≤ 56 * m + 1) (hpdef : p = 8 * a + 3) :
    padicValRat p (scaledBBPRat m) = -1 := by
  have hpgt : 5 < p := by omega
  exact scaledBBPRat_val_eq_neg_one_of_projection_of_unit m p hp
    (by positivity) (minusEightThird_mul_ten_pow_unit m p hp hpgt)
    (scaledBBPRat_minusThreeProjection_of_secondary
      m a p hm hp hlow hupper hactive hpdef)

/-- Exact valuation `-1` in the quiet `p = 8*a+7` minus band. -/
theorem scaledBBPRat_minusSevenVal_of_quiet
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hquiet : 56 * m + 5 < 3 * p) (hpdef : p = 8 * a + 7) :
    padicValRat p (scaledBBPRat m) = -1 := by
  have hpgt : 5 < p := by omega
  exact scaledBBPRat_val_eq_neg_one_of_projection_of_unit m p hp
    (by positivity) (minusTwo_mul_ten_pow_unit m p hp hpgt)
    (scaledBBPRat_minusSevenProjection_of_quiet
      m a p hm hp hlow hupper hquiet hpdef)

/-- Exact valuation `-1` in the active `p = 8*a+7` minus band. -/
theorem scaledBBPRat_minusSevenVal_of_secondary
    (m a p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hlow : 14 * m + 1 < p) (hupper : p ≤ 28 * m + 3)
    (hactive : 3 * p ≤ 56 * m + 5) (hpdef : p = 8 * a + 7) :
    padicValRat p (scaledBBPRat m) = -1 := by
  have hpgt : 5 < p := by omega
  exact scaledBBPRat_val_eq_neg_one_of_projection_of_unit m p hp
    (by positivity) (minusEightThird_mul_ten_pow_unit m p hp hpgt)
    (scaledBBPRat_minusSevenProjection_of_secondary
      m a p hm hp hlow hupper hactive hpdef)

end Theory.PiDigits.T162ExactBBPMinusPrimeProjection

#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.caseThree_quiet_unique_poles
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.caseThree_active_unique_poles
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.caseSeven_quiet_unique_poles
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.caseSeven_active_unique_poles
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusThreeProjection_of_quiet
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusThreeProjection_of_secondary
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusSevenProjection_of_quiet
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusSevenProjection_of_secondary
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusThreeVal_of_quiet
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusThreeVal_of_secondary
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusSevenVal_of_quiet
#print axioms Theory.PiDigits.T162ExactBBPMinusPrimeProjection.scaledBBPRat_minusSevenVal_of_secondary
