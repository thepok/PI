import TheoryLib.PiQuantitativeBlockHitting.T158T158ExactBBPFiveAdicPulses
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# T159: exact top-band prime projection of the sampled BBP rational

This module isolates an actual odd prime in one of the two top BBP pole
families.  Under a strict top-band hypothesis, every other pole in the
sampled prefix is `p`-integral.  Quadratic reciprocity then evaluates the
unique singular pole, giving the exact local residue `4`.

The result concerns the literal `bbpPartial (7*m)` and `scaledBBPRat m`.
It proves no cancellation, distribution, digit occurrence, or V1 statement.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Theory.PiDigits.T159ExactBBPTopPrimeProjection

open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival
open Theory.PiDigits.T74ThreePrimaryDecimation
open Theory.PiDigits.T77SelectedPadicDefectShell
open Theory.PiDigits.T115SampledBBPCellDefectPhase

/-- Congruence modulo `p` inside the `p`-local rationals. -/
def PrimeCongruent (p : ℕ) (x y : ℚ) : Prop :=
  x = y ∨ (1 : ℤ) ≤ padicValRat p (x - y)

lemma prime_gt_five_not_dvd_two
    (p : ℕ) (hpgt : 5 < p) : ¬ p ∣ 2 := by
  intro h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
  omega

lemma prime_gt_five_not_dvd_sixteen
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p) : ¬ p ∣ 16 := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 4) (by simpa using h)
  exact prime_gt_five_not_dvd_two p hpgt h2

lemma prime_gt_five_not_dvd_ten
    (p : ℕ) (hp : p.Prime) (hpgt : 5 < p) : ¬ p ∣ 10 := by
  intro h
  have h' : p ∣ 2 * 5 := by norm_num at h ⊢; exact h
  rcases hp.dvd_mul.mp h' with h2 | h5
  · exact prime_gt_five_not_dvd_two p hpgt h2
  · have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
    omega

lemma padicValRat_poleOne_eq_zero
    (p j : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hlin : ¬ p ∣ 8 * j + 1) :
    padicValRat p (poleOne j) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [poleOne]
  rw [show (8 : ℚ) * j + 1 = ((8 * j + 1 : ℕ) : ℚ) by push_cast; ring]
  have hv4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp hpgt)
  have hv16 : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  rw [padicValRat.div (div_ne_zero (by norm_num) (by positivity))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (by norm_num) (by positivity),
    hv4,
    padicValRat_natCast_eq_zero_of_not_dvd hlin,
    padicValRat.pow (by norm_num), hv16]
  norm_num

lemma padicValRat_poleTwo_eq_zero
    (p j : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hlin : ¬ p ∣ 2 * j + 1) :
    padicValRat p (poleTwo j) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [poleTwo]
  rw [show (2 : ℚ) * j + 1 = ((2 * j + 1 : ℕ) : ℚ) by push_cast; ring]
  have hv2 : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_two p hpgt)
  have hv16 : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  rw [padicValRat.div (div_ne_zero (div_ne_zero (by norm_num) (by norm_num))
      (by positivity)) (pow_ne_zero _ (by norm_num)),
    padicValRat.div (div_ne_zero (by norm_num) (by norm_num)) (by positivity),
    padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
    hv2,
    padicValRat_natCast_eq_zero_of_not_dvd hlin,
    padicValRat.pow (by norm_num), hv16]
  norm_num

lemma padicValRat_poleThree_eq_zero
    (p j : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hlin : ¬ p ∣ 8 * j + 5) :
    padicValRat p (poleThree j) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [poleThree]
  rw [show (8 : ℚ) * j + 5 = ((8 * j + 5 : ℕ) : ℚ) by push_cast; ring]
  have hv16 : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  rw [padicValRat.div (div_ne_zero (by norm_num) (by positivity))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (by norm_num) (by positivity), padicValRat.neg,
    padicValRat_natCast_eq_zero_of_not_dvd hlin,
    padicValRat.pow (by norm_num), hv16]
  norm_num

lemma padicValRat_poleFour_eq_zero
    (p j : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hlin : ¬ p ∣ 4 * j + 3) :
    padicValRat p (poleFour j) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [poleFour]
  rw [show (4 : ℚ) * j + 3 = ((4 * j + 3 : ℕ) : ℚ) by push_cast; ring]
  have hv2 : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_two p hpgt)
  have hv16 : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  rw [padicValRat.div (div_ne_zero (div_ne_zero (by norm_num) (by norm_num))
      (by positivity)) (pow_ne_zero _ (by norm_num)),
    padicValRat.div (div_ne_zero (by norm_num) (by norm_num)) (by positivity),
    padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
    hv2,
    padicValRat_natCast_eq_zero_of_not_dvd hlin,
    padicValRat.pow (by norm_num), hv16]
  norm_num

/-- In the strict top band, a `p`-divisible positive integer in the full pole
window must equal `p`. -/
private lemma eq_prime_of_dvd_top_window
    {m p d : ℕ} (hpgt : 0 < p) (hdpos : 0 < d)
    (hd : d ≤ 56 * m + 6) (hband : 56 * m + 6 < 2 * p)
    (hpd : p ∣ d) : d = p := by
  exact eq_of_dvd_of_pos_of_lt_two_mul hpgt hdpos
    (lt_of_le_of_lt hd hband) hpd

private lemma top_one_regular_not_dvd
    {m p i j : ℕ} (hpgt : 0 < p) (hband : 56 * m + 6 < 2 * p)
    (hpdef : p = 8 * i + 1) (hj : j ≤ 7 * m) (hji : j ≠ i) :
    ¬ p ∣ 8 * j + 1 := by
  intro h
  have heq := eq_prime_of_dvd_top_window hpgt (by omega) (by omega) hband h
  omega

private lemma top_one_other_three_not_dvd
    {m p i j : ℕ} (hpgt : 0 < p) (hband : 56 * m + 6 < 2 * p)
    (hpdef : p = 8 * i + 1) (hj : j ≤ 7 * m) :
    ¬ p ∣ 8 * j + 5 := by
  intro h
  have heq := eq_prime_of_dvd_top_window hpgt (by omega) (by omega) hband h
  omega

private lemma top_three_other_one_not_dvd
    {m p i j : ℕ} (hpgt : 0 < p) (hband : 56 * m + 6 < 2 * p)
    (hpdef : p = 8 * i + 5) (hj : j ≤ 7 * m) :
    ¬ p ∣ 8 * j + 1 := by
  intro h
  have heq := eq_prime_of_dvd_top_window hpgt (by omega) (by omega) hband h
  omega

private lemma top_three_regular_not_dvd
    {m p i j : ℕ} (hpgt : 0 < p) (hband : 56 * m + 6 < 2 * p)
    (hpdef : p = 8 * i + 5) (hj : j ≤ 7 * m) (hji : j ≠ i) :
    ¬ p ∣ 8 * j + 5 := by
  intro h
  have heq := eq_prime_of_dvd_top_window hpgt (by omega) (by omega) hband h
  omega

private lemma top_small_poleTwo_not_dvd
    {m p j : ℕ} (hband : 56 * m + 6 < 2 * p) (hj : j ≤ 7 * m) :
    ¬ p ∣ 2 * j + 1 := by
  intro h
  have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 1) h
  omega

private lemma top_small_poleFour_not_dvd
    {m p j : ℕ} (hband : 56 * m + 6 < 2 * p) (hj : j ≤ 7 * m) :
    ¬ p ∣ 4 * j + 3 := by
  intro h
  have hle := Nat.le_of_dvd (by omega : 0 < 4 * j + 3) h
  omega

private lemma sixteen_pow_eq_one_zmod_of_prime_eq_eight_mul_add_one
    (p i : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hpdef : p = 8 * i + 1) :
    (16 : ZMod p) ^ i = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpmod : p % 8 = 1 := by omega
  have hsquare : IsSquare (2 : ZMod p) :=
    (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inl hpmod)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    exact prime_gt_five_not_dvd_two p hpgt hdvd
  have heuler : (2 : ZMod p) ^ (p / 2) = 1 :=
    (ZMod.euler_criterion p htwo).1 hsquare
  have hhalf : p / 2 = 4 * i := by omega
  rw [hhalf] at heuler
  simpa [show (16 : ZMod p) = 2 ^ 4 by norm_num, pow_mul] using heuler

private lemma four_mul_sixteen_pow_add_one_eq_zero_zmod_of_prime_eq_eight_mul_add_five
    (p i : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hpdef : p = 8 * i + 5) :
    (4 : ZMod p) * 16 ^ i + 1 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpmod : p % 8 = 5 := by omega
  have hnonsquare : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]
    omega
  have htwo : (2 : ZMod p) ≠ 0 :=
    fun hzero => prime_gt_five_not_dvd_two p hpgt
      ((ZMod.natCast_eq_zero_iff 2 p).1 hzero)
  have hnotone : (2 : ZMod p) ^ (p / 2) ≠ 1 := by
    intro h
    exact hnonsquare ((ZMod.euler_criterion p htwo).2 h)
  have hneg : (2 : ZMod p) ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p htwo).resolve_left hnotone
  have hhalf : p / 2 = 4 * i + 2 := by omega
  rw [hhalf, pow_add] at hneg
  have h16 : (16 : ZMod p) ^ i * 4 = -1 := by
    simpa [show (16 : ZMod p) = 2 ^ 4 by norm_num, pow_mul,
      show (2 : ZMod p) ^ 2 = 4 by norm_num] using hneg
  rw [mul_comm] at h16
  rw [h16]
  ring

private lemma primeCongruent_singular_one
    (p i : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hpdef : p = 8 * i + 1) :
    PrimeCongruent p ((p : ℚ) * poleOne i) 4 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow := sixteen_pow_eq_one_zmod_of_prime_eq_eight_mul_add_one
    p i hp hpgt hpdef
  have hdvd : p ∣ 16 ^ i - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    rw [Nat.cast_sub (Nat.one_le_pow i 16 (by norm_num))]
    simpa using sub_eq_zero.mpr hpow
  unfold PrimeCongruent poleOne
  right
  have hi : 0 < i := by omega
  have hsubpos : 0 < 16 ^ i - 1 :=
    (Nat.sub_pos_iff_lt).2 (by exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hi))
  have hsub0 : 16 ^ i - 1 ≠ 0 := Nat.ne_of_gt hsubpos
  have hvalnum : (1 : ℤ) ≤ padicValRat p (((16 ^ i - 1 : ℕ) : ℚ)) := by
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd hsub0 hdvd
  have h16val : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  have h4val : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp hpgt)
  have heq :
      (p : ℚ) * (4 / ((8 : ℚ) * i + 1) / 16 ^ i) - 4 =
        -(4 : ℚ) * ((16 ^ i - 1 : ℕ) : ℚ) / 16 ^ i := by
    have hcast : (((16 ^ i - 1 : ℕ) : ℚ)) = (16 : ℚ) ^ i - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow i 16 (by norm_num))]
      norm_num
    rw [hcast, hpdef]
    push_cast
    field_simp
    ring
  rw [heq]
  rw [padicValRat.div
      (mul_ne_zero (neg_ne_zero.mpr (by norm_num)) (by exact_mod_cast hsub0))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.mul (neg_ne_zero.mpr (by norm_num)) (by exact_mod_cast hsub0),
    padicValRat.neg, h4val, padicValRat.pow (by norm_num), h16val]
  norm_num
  simpa [Nat.cast_sub (Nat.one_le_pow i 16 (by norm_num))] using hvalnum

private lemma primeCongruent_singular_three
    (p i : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hpdef : p = 8 * i + 5) :
    PrimeCongruent p ((p : ℚ) * poleThree i) 4 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow :=
    four_mul_sixteen_pow_add_one_eq_zero_zmod_of_prime_eq_eight_mul_add_five
      p i hp hpgt hpdef
  have hdvd : p ∣ 4 * 16 ^ i + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    push_cast
    simpa using hpow
  unfold PrimeCongruent poleThree
  right
  have hnum0 : 4 * 16 ^ i + 1 ≠ 0 := by positivity
  have hvalnum : (1 : ℤ) ≤ padicValRat p (((4 * 16 ^ i + 1 : ℕ) : ℚ)) := by
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd hnum0 hdvd
  have h16val : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_sixteen p hp hpgt)
  have heq :
      (p : ℚ) * (-(1 : ℚ) / ((8 : ℚ) * i + 5) / 16 ^ i) - 4 =
        -(((4 * 16 ^ i + 1 : ℕ) : ℚ)) / 16 ^ i := by
    rw [hpdef]
    push_cast
    field_simp
    ring
  rw [heq]
  rw [padicValRat.div (neg_ne_zero.mpr (by exact_mod_cast hnum0))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.neg, padicValRat.pow (by norm_num), h16val]
  norm_num
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hvalnum

/-- The actual BBP prefix with the selected first-family pole removed. -/
def topOneRegularRat (m i : ℕ) : ℚ :=
  (∑ j ∈ (range (7 * m + 1)).erase i, poleOne j) +
    polePartial poleTwo (7 * m) + polePartial poleThree (7 * m) +
      polePartial poleFour (7 * m)

/-- The actual BBP prefix with the selected third-family pole removed. -/
def topThreeRegularRat (m i : ℕ) : ℚ :=
  polePartial poleOne (7 * m) + polePartial poleTwo (7 * m) +
    (∑ j ∈ (range (7 * m + 1)).erase i, poleThree j) +
      polePartial poleFour (7 * m)

lemma zero_or_padicValRat_sum_nonneg
    {p : ℕ} (hp : p.Prime) {s : Finset ℕ} {f : ℕ → ℚ}
    (hf : ∀ j ∈ s, padicValRat p (f j) = 0) :
    (∑ j ∈ s, f j) = 0 ∨ 0 ≤ padicValRat p (∑ j ∈ s, f j) := by
  by_cases hz : (∑ j ∈ s, f j) = 0
  · exact Or.inl hz
  · exact Or.inr (padicValRat_sum_nonneg hp s f
      (fun j hj ↦ by rw [hf j hj]) hz)

lemma zero_or_padicValRat_add_nonneg
    {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : x = 0 ∨ 0 ≤ padicValRat p x)
    (hy : y = 0 ∨ 0 ≤ padicValRat p y) :
    x + y = 0 ∨ 0 ≤ padicValRat p (x + y) := by
  by_cases hz : x + y = 0
  · exact Or.inl hz
  · exact Or.inr (padicValRat_add_nonneg_of_each_nonneg p hp hx hy hz)

lemma zero_or_padicValRat_add_ge_one
    {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : x = 0 ∨ (1 : ℤ) ≤ padicValRat p x)
    (hy : y = 0 ∨ (1 : ℤ) ≤ padicValRat p y) :
    x + y = 0 ∨ (1 : ℤ) ≤ padicValRat p (x + y) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hz : x + y = 0
  · exact Or.inl hz
  · right
    rcases hx with rfl | hx
    · simpa using hy.resolve_left (by simpa using hz)
    rcases hy with rfl | hy
    · simpa using hx
    exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add hz)

lemma mul_prime_zero_or_val_ge_one
    {p : ℕ} (hp : p.Prime) {x : ℚ}
    (hx : x = 0 ∨ 0 ≤ padicValRat p x) :
    (p : ℚ) * x = 0 ∨ (1 : ℤ) ≤ padicValRat p ((p : ℚ) * x) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hx with rfl | hx
  · exact Or.inl (mul_zero _)
  · by_cases hx0 : x = 0
    · exact Or.inl (by simp [hx0])
    right
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.mul hpq hx0, padicValRat.of_nat, padicValNat_self]
    omega

private lemma topOneRegularRat_zero_or_nonneg
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpdef : p = 8 * i + 1) :
    topOneRegularRat m i = 0 ∨
      0 ≤ padicValRat p (topOneRegularRat m i) := by
  have hp0 : 0 < p := hp.pos
  have h1 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * m + 1)).erase i) (f := poleOne) (by
      intro j hj
      exact padicValRat_poleOne_eq_zero p j hp hpgt
        (top_one_regular_not_dvd hp0 hband hpdef
          (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  have h2 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleTwo) (by
      intro j hj
      exact padicValRat_poleTwo_eq_zero p j hp hpgt
        (top_small_poleTwo_not_dvd hband
          (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h3 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleThree) (by
      intro j hj
      exact padicValRat_poleThree_eq_zero p j hp hpgt
        (top_one_other_three_not_dvd hp0 hband hpdef
          (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h4 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleFour) (by
      intro j hj
      exact padicValRat_poleFour_eq_zero p j hp hpgt
        (top_small_poleFour_not_dvd hband
          (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  unfold topOneRegularRat polePartial
  exact zero_or_padicValRat_add_nonneg hp
    (zero_or_padicValRat_add_nonneg hp
      (zero_or_padicValRat_add_nonneg hp h1 h2) h3) h4

private lemma topThreeRegularRat_zero_or_nonneg
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpdef : p = 8 * i + 5) :
    topThreeRegularRat m i = 0 ∨
      0 ≤ padicValRat p (topThreeRegularRat m i) := by
  have hp0 : 0 < p := hp.pos
  have h1 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleOne) (by
      intro j hj
      exact padicValRat_poleOne_eq_zero p j hp hpgt
        (top_three_other_one_not_dvd hp0 hband hpdef
          (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h2 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleTwo) (by
      intro j hj
      exact padicValRat_poleTwo_eq_zero p j hp hpgt
        (top_small_poleTwo_not_dvd hband
          (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h3 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * m + 1)).erase i) (f := poleThree) (by
      intro j hj
      exact padicValRat_poleThree_eq_zero p j hp hpgt
        (top_three_regular_not_dvd hp0 hband hpdef
          (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  have h4 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * m + 1)) (f := poleFour) (by
      intro j hj
      exact padicValRat_poleFour_eq_zero p j hp hpgt
        (top_small_poleFour_not_dvd hband
          (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  unfold topThreeRegularRat polePartial
  exact zero_or_padicValRat_add_nonneg hp
    (zero_or_padicValRat_add_nonneg hp
      (zero_or_padicValRat_add_nonneg hp h1 h2) h3) h4

private lemma bbpPartial_eq_topOneRegular_add
    (m i p : ℕ) (hpdef : p = 8 * i + 1) (hpUpper : p ≤ 56 * m + 1) :
    bbpPartial (7 * m) = topOneRegularRat m i + poleOne i := by
  have hi : i ∈ range (7 * m + 1) := by
    apply mem_range.mpr
    omega
  have hs := sum_erase_add (range (7 * m + 1)) poleOne hi
  unfold bbpPartial topOneRegularRat polePartial
  rw [← hs]
  ring

private lemma bbpPartial_eq_topThreeRegular_add
    (m i p : ℕ) (hpdef : p = 8 * i + 5) (hpUpper : p ≤ 56 * m + 5) :
    bbpPartial (7 * m) = topThreeRegularRat m i + poleThree i := by
  have hi : i ∈ range (7 * m + 1) := by
    apply mem_range.mpr
    omega
  have hs := sum_erase_add (range (7 * m + 1)) poleThree hi
  unfold bbpPartial topThreeRegularRat polePartial
  rw [← hs]
  ring

private lemma topOneRegularRat_zero_or_nonneg_of_unique
    (t i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hone : ∀ j ≤ 7 * t, j ≠ i → ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) :
    topOneRegularRat t i = 0 ∨
      0 ≤ padicValRat p (topOneRegularRat t i) := by
  have h1 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * t + 1)).erase i) (f := poleOne) (by
      intro j hj
      exact padicValRat_poleOne_eq_zero p j hp hpgt
        (hone j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  have h2 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * t + 1)) (f := poleTwo) (by
      intro j hj
      exact padicValRat_poleTwo_eq_zero p j hp hpgt
        (htwo j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h3 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * t + 1)) (f := poleThree) (by
      intro j hj
      exact padicValRat_poleThree_eq_zero p j hp hpgt
        (hthree j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h4 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * t + 1)) (f := poleFour) (by
      intro j hj
      exact padicValRat_poleFour_eq_zero p j hp hpgt
        (hfour j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  unfold topOneRegularRat polePartial
  exact zero_or_padicValRat_add_nonneg hp
    (zero_or_padicValRat_add_nonneg hp
      (zero_or_padicValRat_add_nonneg hp h1 h2) h3) h4

private lemma topThreeRegularRat_zero_or_nonneg_of_unique
    (t i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hone : ∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * t, j ≠ i → ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) :
    topThreeRegularRat t i = 0 ∨
      0 ≤ padicValRat p (topThreeRegularRat t i) := by
  have h1 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * t + 1)) (f := poleOne) (by
      intro j hj
      exact padicValRat_poleOne_eq_zero p j hp hpgt
        (hone j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h2 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * t + 1)) (f := poleTwo) (by
      intro j hj
      exact padicValRat_poleTwo_eq_zero p j hp hpgt
        (htwo j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  have h3 := zero_or_padicValRat_sum_nonneg hp
    (s := (range (7 * t + 1)).erase i) (f := poleThree) (by
      intro j hj
      exact padicValRat_poleThree_eq_zero p j hp hpgt
        (hthree j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
          (ne_of_mem_erase hj)))
  have h4 := zero_or_padicValRat_sum_nonneg hp
    (s := range (7 * t + 1)) (f := poleFour) (by
      intro j hj
      exact padicValRat_poleFour_eq_zero p j hp hpgt
        (hfour j (Nat.lt_succ_iff.mp (mem_range.mp hj))))
  unfold topThreeRegularRat polePartial
  exact zero_or_padicValRat_add_nonneg hp
    (zero_or_padicValRat_add_nonneg hp
      (zero_or_padicValRat_add_nonneg hp h1 h2) h3) h4

/-- Projection at an arbitrary sevenfold sampled depth once the selected
first-family pole is the unique `p`-divisible pole in the four BBP families. -/
theorem bbpPartial_primeProjection_one_of_unique
    (t i p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hi : i ≤ 7 * t)
    (hpdef : p = 8 * i + 1)
    (hone : ∀ j ≤ 7 * t, j ≠ i → ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * t)) 4 := by
  rw [bbpPartial_eq_topOneRegular_add t i p hpdef (by omega)]
  unfold PrimeCongruent at ⊢
  have hs := primeCongruent_singular_one p i hp hpgt hpdef
  unfold PrimeCongruent at hs
  have hs' : (p : ℚ) * poleOne i - 4 = 0 ∨
      (1 : ℤ) ≤ padicValRat p ((p : ℚ) * poleOne i - 4) :=
    hs.imp sub_eq_zero.mpr id
  have hr := mul_prime_zero_or_val_ge_one hp
    (topOneRegularRat_zero_or_nonneg_of_unique t i p hp hpgt
      hone htwo hthree hfour)
  have hadd := zero_or_padicValRat_add_ge_one hp hs' hr
  rcases hadd with hz | hv
  · left
    linarith
  · right
    rw [show (p : ℚ) * (topOneRegularRat t i + poleOne i) - 4 =
        ((p : ℚ) * poleOne i - 4) + (p : ℚ) * topOneRegularRat t i by ring]
    exact hv

/-- Projection at an arbitrary sevenfold sampled depth once the selected
third-family pole is the unique `p`-divisible pole in the four BBP families. -/
theorem bbpPartial_primeProjection_three_of_unique
    (t i p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hi : i ≤ 7 * t)
    (hpdef : p = 8 * i + 5)
    (hone : ∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * t, j ≠ i → ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * t)) 4 := by
  rw [bbpPartial_eq_topThreeRegular_add t i p hpdef (by omega)]
  unfold PrimeCongruent at ⊢
  have hs := primeCongruent_singular_three p i hp hpgt hpdef
  unfold PrimeCongruent at hs
  have hs' : (p : ℚ) * poleThree i - 4 = 0 ∨
      (1 : ℤ) ≤ padicValRat p ((p : ℚ) * poleThree i - 4) :=
    hs.imp sub_eq_zero.mpr id
  have hr := mul_prime_zero_or_val_ge_one hp
    (topThreeRegularRat_zero_or_nonneg_of_unique t i p hp hpgt
      hone htwo hthree hfour)
  have hadd := zero_or_padicValRat_add_ge_one hp hs' hr
  rcases hadd with hz | hv
  · left
    linarith
  · right
    rw [show (p : ℚ) * (topThreeRegularRat t i + poleThree i) - 4 =
        ((p : ℚ) * poleThree i - 4) + (p : ℚ) * topThreeRegularRat t i by ring]
    exact hv

/-- Actual top-band projection for a prime in the `8*i+1` pole
family.  The square and endpoint hypotheses are displayed explicitly; the
strict band already implies that no second multiple of `p` occurs. -/
theorem bbpPartial_topPrimeProjection_one
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpUpper : p ≤ 56 * m + 1)
    (hpdef : p = 8 * i + 1) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * m)) 4 := by
  rw [bbpPartial_eq_topOneRegular_add m i p hpdef hpUpper]
  unfold PrimeCongruent at ⊢
  have hs := primeCongruent_singular_one p i hp hpgt hpdef
  unfold PrimeCongruent at hs
  have hs' : (p : ℚ) * poleOne i - 4 = 0 ∨
      (1 : ℤ) ≤ padicValRat p ((p : ℚ) * poleOne i - 4) :=
    hs.imp sub_eq_zero.mpr id
  have hr := mul_prime_zero_or_val_ge_one hp
    (topOneRegularRat_zero_or_nonneg m i p hp hpgt hband hpdef)
  have hadd := zero_or_padicValRat_add_ge_one hp hs' hr
  rcases hadd with hz | hv
  · left
    linarith
  · right
    rw [show (p : ℚ) * (topOneRegularRat m i + poleOne i) - 4 =
        ((p : ℚ) * poleOne i - 4) + (p : ℚ) * topOneRegularRat m i by ring]
    exact hv

/-- Actual top-band projection for a prime in the `8*i+5` pole
family. -/
theorem bbpPartial_topPrimeProjection_three
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpUpper : p ≤ 56 * m + 5)
    (hpdef : p = 8 * i + 5) :
    PrimeCongruent p ((p : ℚ) * bbpPartial (7 * m)) 4 := by
  rw [bbpPartial_eq_topThreeRegular_add m i p hpdef hpUpper]
  unfold PrimeCongruent at ⊢
  have hs := primeCongruent_singular_three p i hp hpgt hpdef
  unfold PrimeCongruent at hs
  have hs' : (p : ℚ) * poleThree i - 4 = 0 ∨
      (1 : ℤ) ≤ padicValRat p ((p : ℚ) * poleThree i - 4) :=
    hs.imp sub_eq_zero.mpr id
  have hr := mul_prime_zero_or_val_ge_one hp
    (topThreeRegularRat_zero_or_nonneg m i p hp hpgt hband hpdef)
  have hadd := zero_or_padicValRat_add_ge_one hp hs' hr
  rcases hadd with hz | hv
  · left
    linarith
  · right
    rw [show (p : ℚ) * (topThreeRegularRat m i + poleThree i) - 4 =
        ((p : ℚ) * poleThree i - 4) + (p : ℚ) * topThreeRegularRat m i by ring]
    exact hv

lemma PrimeCongruent.mul_ten_pow
    {m p : ℕ} (hp : p.Prime) (hpgt : 5 < p) {x y : ℚ}
    (hxy : PrimeCongruent p x y) :
    PrimeCongruent p ((10 : ℚ) ^ m * x) ((10 : ℚ) ^ m * y) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold PrimeCongruent at hxy ⊢
  rcases hxy with rfl | hval
  · exact Or.inl rfl
  · right
    have hdiff0 : x - y ≠ 0 := by
      intro hz
      simp [hz] at hval
    have h10 : (10 : ℚ) ≠ 0 := by norm_num
    have h10val : padicValRat p (10 : ℚ) = 0 :=
      padicValRat_natCast_eq_zero_of_not_dvd
        (prime_gt_five_not_dvd_ten p hp hpgt)
    rw [show (10 : ℚ) ^ m * x - 10 ^ m * y = 10 ^ m * (x - y) by ring,
      padicValRat.mul (pow_ne_zero _ h10) hdiff0,
      padicValRat.pow h10, h10val]
    norm_num
    exact hval

/-- The unique first-family pole projection transported to the actual scaled
sampled BBP rational. -/
theorem scaledBBPRat_primeProjection_one_of_unique
    (t i p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hi : i ≤ 7 * t)
    (hpdef : p = 8 * i + 1)
    (hone : ∀ j ≤ 7 * t, j ≠ i → ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat t) (4 * (10 : ℚ) ^ t) := by
  have h := PrimeCongruent.mul_ten_pow (m := t) hp hpgt
    (bbpPartial_primeProjection_one_of_unique t i p hp hpgt hi hpdef
      hone htwo hthree hfour)
  unfold scaledBBPRat
  convert h using 1 <;> ring

/-- The unique third-family pole projection transported to the actual scaled
sampled BBP rational. -/
theorem scaledBBPRat_primeProjection_three_of_unique
    (t i p : ℕ) (hp : p.Prime) (hpgt : 5 < p) (hi : i ≤ 7 * t)
    (hpdef : p = 8 * i + 5)
    (hone : ∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 1)
    (htwo : ∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1)
    (hthree : ∀ j ≤ 7 * t, j ≠ i → ¬ p ∣ 8 * j + 5)
    (hfour : ∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat t) (4 * (10 : ℚ) ^ t) := by
  have h := PrimeCongruent.mul_ten_pow (m := t) hp hpgt
    (bbpPartial_primeProjection_three_of_unique t i p hp hpgt hi hpdef
      hone htwo hthree hfour)
  unfold scaledBBPRat
  convert h using 1 <;> ring

/-- The first-family top-prime projection for the actual scaled sampled BBP
rational. -/
theorem scaledBBPRat_topPrimeProjection_one
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpUpper : p ≤ 56 * m + 1)
    (hpdef : p = 8 * i + 1) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat m) (4 * (10 : ℚ) ^ m) := by
  have h := PrimeCongruent.mul_ten_pow (m := m) hp hpgt
    (bbpPartial_topPrimeProjection_one m i p hp hpgt hband hpUpper hpdef)
  unfold scaledBBPRat
  convert h using 1 <;> ring

/-- The third-family top-prime projection for the actual scaled sampled BBP
rational. -/
theorem scaledBBPRat_topPrimeProjection_three
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpUpper : p ≤ 56 * m + 5)
    (hpdef : p = 8 * i + 5) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat m) (4 * (10 : ℚ) ^ m) := by
  have h := PrimeCongruent.mul_ten_pow (m := m) hp hpgt
    (bbpPartial_topPrimeProjection_three m i p hp hpgt hband hpUpper hpdef)
  unfold scaledBBPRat
  convert h using 1 <;> ring

lemma padicValRat_eq_zero_of_primeCongruent
    {p : ℕ} (hp : p.Prime) {x y : ℚ} (hy0 : y ≠ 0)
    (hy : padicValRat p y = 0) (hxy : PrimeCongruent p x y) :
    padicValRat p x = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold PrimeCongruent at hxy
  rcases hxy with rfl | hd
  · exact hy
  · have hd0 : x - y ≠ 0 := by
      intro hz
      simp [hz] at hd
    have hsum : y + (x - y) ≠ 0 := by
      intro hz
      have heq : x - y = -y := by linarith
      have hv := congrArg (padicValRat p) heq
      rw [padicValRat.neg, hy] at hv
      omega
    have hv := padicValRat.add_eq_of_lt hsum hy0 hd0 (by omega :
      padicValRat p y < padicValRat p (x - y))
    rw [show x = y + (x - y) by ring]
    exact hv.trans hy

theorem scaledBBPRat_val_eq_neg_one_of_projection_of_unit
    (m p : ℕ) (hp : p.Prime) {y : ℚ} (hy0 : y ≠ 0)
    (hy : padicValRat p y = 0)
    (hproj : PrimeCongruent p ((p : ℚ) * scaledBBPRat m) y) :
    padicValRat p (scaledBBPRat m) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hx := padicValRat_eq_zero_of_primeCongruent hp hy0 hy hproj
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hR := Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPRat_ne_zero m
  rw [padicValRat.mul hpq hR, padicValRat.of_nat, padicValNat_self] at hx
  omega

theorem scaledBBPRat_val_eq_neg_one_of_projection
    (m p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hproj : PrimeCongruent p ((p : ℚ) * scaledBBPRat m)
      (4 * (10 : ℚ) ^ m)) :
    padicValRat p (scaledBBPRat m) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_four p hp hpgt)
  have h10 : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_five_not_dvd_ten p hp hpgt)
  have hy0 : (4 : ℚ) * 10 ^ m ≠ 0 := by positivity
  have hy : padicValRat p ((4 : ℚ) * 10 ^ m) = 0 := by
    rw [padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)), h4,
      padicValRat.pow (by norm_num), h10]
    norm_num
  exact scaledBBPRat_val_eq_neg_one_of_projection_of_unit m p hp hy0 hy hproj

/-- Every first-family prime covered by the actual projection occurs with
exact valuation `-1` in the reduced sampled BBP rational. -/
theorem scaledBBPRat_topPrime_val_eq_neg_one
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpUpper : p ≤ 56 * m + 1)
    (hpdef : p = 8 * i + 1) :
    padicValRat p (scaledBBPRat m) = -1 := by
  exact scaledBBPRat_val_eq_neg_one_of_projection m p hp hpgt
    (scaledBBPRat_topPrimeProjection_one m i p hp hpgt hband hpUpper hpdef)

/-- Every third-family prime covered by the actual projection occurs with
exact valuation `-1` in the reduced sampled BBP rational. -/
theorem scaledBBPRat_topPrimeThree_val_eq_neg_one
    (m i p : ℕ) (hp : p.Prime) (hpgt : 5 < p)
    (hband : 56 * m + 6 < 2 * p) (hpUpper : p ≤ 56 * m + 5)
    (hpdef : p = 8 * i + 5) :
    padicValRat p (scaledBBPRat m) = -1 := by
  exact scaledBBPRat_val_eq_neg_one_of_projection m p hp hpgt
    (scaledBBPRat_topPrimeProjection_three m i p hp hpgt hband hpUpper hpdef)

end Theory.PiDigits.T159ExactBBPTopPrimeProjection

#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.bbpPartial_primeProjection_one_of_unique
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.bbpPartial_primeProjection_three_of_unique
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_primeProjection_one_of_unique
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_primeProjection_three_of_unique
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_val_eq_neg_one_of_projection
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.bbpPartial_topPrimeProjection_one
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.bbpPartial_topPrimeProjection_three
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrimeProjection_one
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrimeProjection_three
#print axioms Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrime_val_eq_neg_one
#print axioms
  Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrimeThree_val_eq_neg_one
