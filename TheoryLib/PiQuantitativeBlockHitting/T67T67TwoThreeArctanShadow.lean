import TheoryLib.PiQuantitativeBlockHitting.T66T66HuttonDecimalTransient

/-!
# T67: exact two-primary wall for the `1/2 + 1/3` arctangent shadow

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Mathlib proves `arctan (1/2) + arctan (1/3) = pi/4`.  Equal adjacent
Taylor truncations therefore give an exact rational bracket for pi.  This
module proves that the lower endpoint at index `K` has two-adic valuation
`-(4*K+1)`, so its reduced denominator contains exactly `2^(4*K+1)`.

The proof exposes the structural reason: the combined base-two/base-three
pair at Taylor index `j` has valuation `1-2*j`, and these valuations strictly
decrease.  The final pair is therefore the unique minimum of the prefix.

This is exact bracket and denominator arithmetic only.  It proves no decimal
cylinder hit, distribution statement, or every-word theorem for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.TwoThreeArctanShadow

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinTwoAdicForcing
open Theory.PiDigits.MachinTotalTwoAdicForcing
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonFiveAdicTransient

/-- Number of Taylor terms in either lower `1/2 + 1/3` prefix. -/
def twoThreeTermCount (K : ℕ) : ℕ := 2 * (K + 1)

/-- The two equal-index Taylor terms, after multiplication by four. -/
def twoThreePairRat (j : ℕ) : ℚ :=
  4 * arctanTermRat 2 j + 4 * arctanTermRat 3 j

/-- The lower rational shadow coming from equal even-length truncations. -/
def twoThreeLowerRat (K : ℕ) : ℚ :=
  4 * arctanPartialRat 2 (twoThreeTermCount K) +
    4 * arctanPartialRat 3 (twoThreeTermCount K)

/-- The adjacent upper rational shadow. -/
def twoThreeUpperRat (K : ℕ) : ℚ :=
  4 * arctanPartialRat 2 (twoThreeTermCount K + 1) +
    4 * arctanPartialRat 3 (twoThreeTermCount K + 1)

/-- Real embedding of the lower rational shadow. -/
def twoThreeLower (K : ℕ) : ℝ := (twoThreeLowerRat K : ℝ)

/-- Real embedding of the upper rational shadow. -/
def twoThreeUpper (K : ℕ) : ℝ := (twoThreeUpperRat K : ℝ)

/-- Exact adjacent-bracket width. -/
def twoThreeWidth (K : ℕ) : ℝ :=
  4 * arctanMagnitude 2 (twoThreeTermCount K) +
    4 * arctanMagnitude 3 (twoThreeTermCount K)

/-- The lower shadow is the finite sum of its combined equal-index pairs. -/
theorem twoThreeLowerRat_eq_pair_sum (K : ℕ) :
    twoThreeLowerRat K =
      ∑ j ∈ range (twoThreeTermCount K), twoThreePairRat j := by
  unfold twoThreeLowerRat twoThreePairRat arctanPartialRat
  rw [sum_add_distrib]
  simp only [mul_sum]

/-- Closed fraction for the coefficient-four base-two term. -/
lemma four_mul_arctanTermRat_two_eq_fraction (j : ℕ) :
    4 * arctanTermRat 2 j =
      4 * (-1 : ℚ) ^ j /
        ((((2 * j + 1 : ℕ) : ℚ)) * 2 ^ (2 * j + 1)) := by
  unfold arctanTermRat
  simp only [inv_pow]
  push_cast
  rw [pow_add]
  field_simp

/-- Closed fraction for the coefficient-four base-three term. -/
lemma four_mul_arctanTermRat_three_eq_fraction (j : ℕ) :
    4 * arctanTermRat 3 j =
      4 * (-1 : ℚ) ^ j /
        ((((2 * j + 1 : ℕ) : ℚ)) * 3 ^ (2 * j + 1)) := by
  unfold arctanTermRat
  simp only [inv_pow]
  push_cast
  rw [pow_add]
  field_simp

/-- The coefficient-four base-two term has exact two-adic valuation
`1 - 2*j`. -/
lemma padicValRat_two_four_mul_arctanTermRat_two (j : ℕ) :
    padicValRat 2 (4 * arctanTermRat 2 j) = 1 - 2 * (j : ℤ) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [four_mul_arctanTermRat_two_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have htwoq : (2 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 4 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 2 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ htwoq)
  have hvalNegOne : padicValRat 2 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr : padicValRat 2 (((2 * j + 1 : ℕ) : ℚ)) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd ⟨j, by omega⟩
  have hvalTwo : padicValRat 2 (2 : ℚ) = 1 :=
    padicValRat.self (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat_two_four, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ htwoq), hvalr,
    padicValRat.pow htwoq, hvalTwo]
  push_cast
  ring

/-- The coefficient-four base-three term has exact two-adic valuation two. -/
lemma padicValRat_two_four_mul_arctanTermRat_three (j : ℕ) :
    padicValRat 2 (4 * arctanTermRat 3 j) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [four_mul_arctanTermRat_three_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hthreeq : (3 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 4 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 3 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ hthreeq)
  have hvalNegOne : padicValRat 2 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr : padicValRat 2 (((2 * j + 1 : ℕ) : ℚ)) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd ⟨j, by omega⟩
  have hvalThree : padicValRat 2 (3 : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat_two_four, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ hthreeq), hvalr,
    padicValRat.pow hthreeq, hvalThree]
  norm_num

/-- Each combined pair is nonzero. -/
lemma twoThreePairRat_ne_zero (j : ℕ) : twoThreePairRat j ≠ 0 := by
  intro hzero
  have heq : 4 * arctanTermRat 2 j = -(4 * arctanTermRat 3 j) :=
    eq_neg_of_add_eq_zero_left hzero
  have hval := congrArg (padicValRat 2) heq
  rw [padicValRat_two_four_mul_arctanTermRat_two,
    padicValRat.neg, padicValRat_two_four_mul_arctanTermRat_three] at hval
  omega

/-- Exact two-adic valuation of one combined equal-index pair. -/
theorem padicValRat_two_twoThreePairRat (j : ℕ) :
    padicValRat 2 (twoThreePairRat j) = 1 - 2 * (j : ℤ) := by
  unfold twoThreePairRat
  have htwo0 : 4 * arctanTermRat 2 j ≠ 0 := by
    rw [four_mul_arctanTermRat_two_eq_fraction]
    positivity
  have hthree0 : 4 * arctanTermRat 3 j ≠ 0 := by
    rw [four_mul_arctanTermRat_three_eq_fraction]
    positivity
  calc
    padicValRat 2 (twoThreePairRat j) =
        padicValRat 2 (4 * arctanTermRat 2 j) := by
      exact padicValRat.add_eq_of_lt (twoThreePairRat_ne_zero j)
        htwo0 hthree0 (by
          rw [padicValRat_two_four_mul_arctanTermRat_two,
            padicValRat_two_four_mul_arctanTermRat_three]
          omega)
    _ = 1 - 2 * (j : ℤ) :=
      padicValRat_two_four_mul_arctanTermRat_two j

/-- A nonempty prefix of pairs has the valuation of its final pair. -/
theorem padicValRat_two_twoThreePair_prefix (n : ℕ) :
    padicValRat 2 (∑ j ∈ range (n + 1), twoThreePairRat j) =
      1 - 2 * (n : ℤ) := by
  induction n with
  | zero =>
      simpa using padicValRat_two_twoThreePairRat 0
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by rfl, sum_range_succ]
      have hprefix0 :
          (∑ j ∈ range (n + 1), twoThreePairRat j) ≠ 0 := by
        intro hzero
        rw [hzero] at ih
        simp at ih
        omega
      have hlast0 := twoThreePairRat_ne_zero (n + 1)
      have hsum0 :
          (∑ j ∈ range (n + 1), twoThreePairRat j) +
              twoThreePairRat (n + 1) ≠ 0 := by
        intro hzero
        have heq :
            (∑ j ∈ range (n + 1), twoThreePairRat j) =
              -twoThreePairRat (n + 1) :=
          eq_neg_of_add_eq_zero_left hzero
        have hval := congrArg (padicValRat 2) heq
        rw [ih, padicValRat.neg,
          padicValRat_two_twoThreePairRat] at hval
        omega
      rw [add_comm]
      calc
        padicValRat 2
            (twoThreePairRat (n + 1) +
              ∑ j ∈ range (n + 1), twoThreePairRat j) =
            padicValRat 2 (twoThreePairRat (n + 1)) := by
          exact padicValRat.add_eq_of_lt (by rwa [add_comm])
            hlast0 hprefix0 (by
              rw [padicValRat_two_twoThreePairRat, ih]
              push_cast
              omega)
        _ = 1 - 2 * ((n + 1 : ℕ) : ℤ) :=
          padicValRat_two_twoThreePairRat (n + 1)

/-- Exact two-adic valuation of the complete lower rational shadow. -/
theorem padicValRat_two_twoThreeLowerRat (K : ℕ) :
    padicValRat 2 (twoThreeLowerRat K) = -(4 * (K : ℤ) + 1) := by
  rw [twoThreeLowerRat_eq_pair_sum]
  have h := padicValRat_two_twoThreePair_prefix (2 * K + 1)
  unfold twoThreeTermCount
  rw [show 2 * (K + 1) = (2 * K + 1) + 1 by omega]
  rw [h]
  push_cast
  ring

/-- The complete lower rational shadow is nonzero. -/
lemma twoThreeLowerRat_ne_zero (K : ℕ) : twoThreeLowerRat K ≠ 0 := by
  intro hzero
  have hval := padicValRat_two_twoThreeLowerRat K
  rw [hzero] at hval
  simp at hval
  omega

/-- Exact multiplicity of two in the reduced denominator. -/
theorem padicValNat_two_twoThreeLowerRat_den (K : ℕ) :
    padicValNat 2 (twoThreeLowerRat K).den = 4 * K + 1 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hval := padicValRat_two_twoThreeLowerRat K
  have hnumZ : (twoThreeLowerRat K).num ≠ 0 := by
    intro hz
    apply twoThreeLowerRat_ne_zero K
    rw [← (twoThreeLowerRat K).num_div_den, hz]
    norm_num
  have hnumAbs : (twoThreeLowerRat K).num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr hnumZ
  have hnumNot : ¬ 2 ∣ (twoThreeLowerRat K).num.natAbs := by
    intro hnumDiv
    have hcop : Nat.Coprime 2 (twoThreeLowerRat K).den :=
      Nat.Coprime.of_dvd_left hnumDiv (twoThreeLowerRat K).reduced
    have hdenNot : ¬ 2 ∣ (twoThreeLowerRat K).den :=
      Nat.prime_two.coprime_iff_not_dvd.mp hcop
    have hvden : padicValNat 2 (twoThreeLowerRat K).den = 0 :=
      padicValNat.eq_zero_of_not_dvd hdenNot
    have hvnumNat : 1 ≤ padicValNat 2 (twoThreeLowerRat K).num.natAbs :=
      (padicValNat_dvd_iff_le hnumAbs).1 (by simpa using hnumDiv)
    have hvnumInt : (1 : ℤ) ≤ padicValInt 2 (twoThreeLowerRat K).num := by
      simpa [padicValInt] using hvnumNat
    rw [padicValRat_def, hvden] at hval
    omega
  have hvnumInt : padicValInt 2 (twoThreeLowerRat K).num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnumNot
  rw [padicValRat_def, hvnumInt] at hval
  omega

/-- Exact five-adic valuation of one coefficient-four base-two term. -/
lemma padicValRat_five_four_mul_arctanTermRat_two (j : ℕ) :
    padicValRat 5 (4 * arctanTermRat 2 j) =
      -(padicValNat 5 (2 * j + 1) : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [four_mul_arctanTermRat_two_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have htwoq : (2 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 4 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 2 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ htwoq)
  have hval4 : padicValRat 5 (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 5 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr :
      padicValRat 5 (((2 * j + 1 : ℕ) : ℚ)) =
        (padicValNat 5 (2 * j + 1) : ℤ) := by
    rw [padicValRat.of_nat]
  have hvalTwo : padicValRat 5 (2 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    hval4, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ htwoq), hvalr,
    padicValRat.pow htwoq, hvalTwo]
  norm_num

/-- Exact five-adic valuation of one coefficient-four base-three term. -/
lemma padicValRat_five_four_mul_arctanTermRat_three (j : ℕ) :
    padicValRat 5 (4 * arctanTermRat 3 j) =
      -(padicValNat 5 (2 * j + 1) : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [four_mul_arctanTermRat_three_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hthreeq : (3 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 4 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 3 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ hthreeq)
  have hval4 : padicValRat 5 (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 5 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr :
      padicValRat 5 (((2 * j + 1 : ℕ) : ℚ)) =
        (padicValNat 5 (2 * j + 1) : ℤ) := by
    rw [padicValRat.of_nat]
  have hvalThree : padicValRat 5 (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    hval4, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ hthreeq), hvalr,
    padicValRat.pow hthreeq, hvalThree]
  norm_num

/-- The five-adic valuation of a combined pair cannot fall below its common
term valuation. -/
lemma neg_padicValNat_five_le_twoThreePairRat (j : ℕ) :
    -(padicValNat 5 (2 * j + 1) : ℤ) ≤
      padicValRat 5 (twoThreePairRat j) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmin := padicValRat.min_le_padicValRat_add
    (p := 5) (twoThreePairRat_ne_zero j)
  unfold twoThreePairRat at hmin
  rw [padicValRat_five_four_mul_arctanTermRat_two,
    padicValRat_five_four_mul_arctanTermRat_three, min_self] at hmin
  exact hmin

/-- Every odd linear exponent in the prefix has five-adic order at most the
two-primary denominator wall `4*K+1`. -/
lemma padicValNat_five_exponent_le_twoPrimaryWall
    (K j : ℕ) (hj : j < twoThreeTermCount K) :
    padicValNat 5 (2 * j + 1) ≤ 4 * K + 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  cases K with
  | zero =>
      unfold twoThreeTermCount at hj
      have hnot : ¬ 5 ∣ 2 * j + 1 := by
        intro hdvd
        have hle : 5 ≤ 2 * j + 1 :=
          Nat.le_of_dvd (by positivity) hdvd
        omega
      rw [padicValNat.eq_zero_of_not_dvd hnot]
      omega
  | succ K =>
      have hrle : 2 * j + 1 ≤ 4 * (K + 1) + 3 := by
        unfold twoThreeTermCount at hj
        omega
      by_cases hr : 5 < 2 * j + 1
      · have hvaladd := padicValNat_add_le_self hr
        omega
      · have hrsmall : 2 * j + 1 ≤ 5 := by omega
        have hvalLog := padicValNat_le_nat_log (p := 5) (2 * j + 1)
        have hlogMono := Nat.log_mono_right (b := 5) hrsmall
        norm_num at hlogMono
        omega

/-- The complete lower shadow cannot have five-adic valuation below the
negative two-primary wall. -/
lemma neg_twoPrimaryWall_le_padicValRat_five_twoThreeLowerRat (K : ℕ) :
    -(4 * (K : ℤ) + 1) ≤ padicValRat 5 (twoThreeLowerRat K) := by
  rw [twoThreeLowerRat_eq_pair_sum]
  have hsum := padicValRat_five_sum_lower twoThreePairRat
    (-(4 * (K : ℤ) + 1)) (S := range (twoThreeTermCount K)) (by
      intro j hj
      have hbound := padicValNat_five_exponent_le_twoPrimaryWall
        K j (mem_range.1 hj)
      have hpair := neg_padicValNat_five_le_twoThreePairRat j
      exact le_trans (by exact_mod_cast (show
        -(4 * (K : ℤ) + 1) ≤
          -(padicValNat 5 (2 * j + 1) : ℤ) by omega)) hpair)
  rcases hsum with hzero | hge
  · exact False.elim (twoThreeLowerRat_ne_zero K
      ((twoThreeLowerRat_eq_pair_sum K).trans hzero))
  · exact hge

/-- The five-primary exponent in the reduced denominator does not exceed
the exact two-primary exponent. -/
theorem padicValNat_five_twoThreeLowerRat_den_le (K : ℕ) :
    padicValNat 5 (twoThreeLowerRat K).den ≤ 4 * K + 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hden : 5 ∣ (twoThreeLowerRat K).den
  · have hcop : Nat.Coprime 5 (twoThreeLowerRat K).num.natAbs :=
      (Nat.Coprime.of_dvd_right hden (twoThreeLowerRat K).reduced).symm
    have hnumNot : ¬ 5 ∣ (twoThreeLowerRat K).num.natAbs :=
      (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mp hcop
    have hvnum : padicValInt 5 (twoThreeLowerRat K).num = 0 := by
      simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnumNot
    have hval := neg_twoPrimaryWall_le_padicValRat_five_twoThreeLowerRat K
    rw [padicValRat_def, hvnum] at hval
    omega
  · have hvden : padicValNat 5 (twoThreeLowerRat K).den = 0 :=
      padicValNat.eq_zero_of_not_dvd hden
    omega

/-- The exact base-ten denominator exponent, hence the exact decimal
preperiod length, is `4*K+1`. -/
theorem twoThreeLowerRat_baseTen_denominator_exponent (K : ℕ) :
    max (padicValNat 2 (twoThreeLowerRat K).den)
        (padicValNat 5 (twoThreeLowerRat K).den) = 4 * K + 1 := by
  rw [padicValNat_two_twoThreeLowerRat_den]
  exact max_eq_left (padicValNat_five_twoThreeLowerRat_den_le K)

/-- The lower shadow is the displayed pair of real finite Taylor sums. -/
theorem twoThreeLower_eq (K : ℕ) :
    twoThreeLower K =
      4 * arctanPartial 2 (twoThreeTermCount K) +
        4 * arctanPartial 3 (twoThreeTermCount K) := by
  simp [twoThreeLower, twoThreeLowerRat, arctanPartial]

/-- The upper shadow is the displayed adjacent pair of real finite sums. -/
theorem twoThreeUpper_eq (K : ℕ) :
    twoThreeUpper K =
      4 * arctanPartial 2 (twoThreeTermCount K + 1) +
        4 * arctanPartial 3 (twoThreeTermCount K + 1) := by
  simp [twoThreeUpper, twoThreeUpperRat, arctanPartial]

/-- The classical `1/2 + 1/3` arctangent identity, solved for pi. -/
theorem pi_eq_twoThreeArctan :
    Real.pi = 4 * Real.arctan (2 : ℝ)⁻¹ +
      4 * Real.arctan (3 : ℝ)⁻¹ := by
  have h := Real.arctan_inv_2_add_arctan_inv_3
  linarith

/-- Every lower shadow lies below pi. -/
theorem twoThreeLower_le_pi (K : ℕ) : twoThreeLower K ≤ Real.pi := by
  rw [twoThreeLower_eq, pi_eq_twoThreeArctan]
  have h2 := arctanPartial_even_le 2 (K + 1) (by norm_num)
  have h3 := arctanPartial_even_le 3 (K + 1) (by norm_num)
  unfold twoThreeTermCount
  linarith

/-- Every adjacent upper shadow lies above pi. -/
theorem pi_le_twoThreeUpper (K : ℕ) : Real.pi ≤ twoThreeUpper K := by
  rw [twoThreeUpper_eq, pi_eq_twoThreeArctan]
  have h2 := arctan_le_arctanPartial_odd 2 (K + 1) (by norm_num)
  have h3 := arctan_le_arctanPartial_odd 3 (K + 1) (by norm_num)
  unfold twoThreeTermCount
  linarith

/-- The adjacent endpoints differ by the exact first-omitted-term width. -/
theorem twoThreeUpper_sub_lower_eq_width (K : ℕ) :
    twoThreeUpper K - twoThreeLower K = twoThreeWidth K := by
  rw [twoThreeUpper_eq, twoThreeLower_eq]
  rw [arctanPartial_succ, arctanPartial_succ]
  have heven : Even (twoThreeTermCount K) := ⟨K + 1, by
    unfold twoThreeTermCount
    omega⟩
  simp only [heven.neg_one_pow, one_mul]
  unfold twoThreeWidth
  ring

/-- Complete exact rational bracket for pi. -/
theorem pi_mem_twoThree_bracket (K : ℕ) :
    twoThreeLower K ≤ Real.pi ∧
      Real.pi ≤ twoThreeUpper K ∧
      twoThreeUpper K - twoThreeLower K = twoThreeWidth K := by
  exact ⟨twoThreeLower_le_pi K, pi_le_twoThreeUpper K,
    twoThreeUpper_sub_lower_eq_width K⟩

/-- Closed form of the exact adjacent width. -/
theorem twoThreeWidth_eq_explicit (K : ℕ) :
    twoThreeWidth K =
      4 / (((4 * K + 5 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * K + 5)) +
        4 / (((4 * K + 5 : ℕ) : ℝ) * (3 : ℝ) ^ (4 * K + 5)) := by
  unfold twoThreeWidth twoThreeTermCount arctanMagnitude
  rw [show 2 * (2 * (K + 1)) + 1 = 4 * K + 5 by omega]
  rw [inv_pow, inv_pow]
  have hden :
      (2 : ℝ) * ((2 * (K + 1) : ℕ) : ℝ) + 1 =
        ((4 * K + 5 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hden]
  (field_simp; ring_nf)

/-- Elementary growth inequality behind the post-transient width wall. -/
lemma ten_mul_four_mul_add_five_lt_five_pow (K : ℕ) :
    10 * (4 * K + 5) < 5 ^ (4 * K + 3) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [show 4 * (K + 1) + 3 = (4 * K + 3) + 4 by omega, pow_add]
      calc
        10 * (4 * (K + 1) + 5) < 625 * (10 * (4 * K + 5)) := by
          omega
        _ < 625 * 5 ^ (4 * K + 3) := by omega
        _ = 5 ^ (4 * K + 3) * 5 ^ 4 := by norm_num; ring

/-- Exact rescaling of the base-two first omitted term at the first
post-two-primary position. -/
lemma scaled_first_omitted_two_term (K : ℕ) :
    (10 : ℝ) ^ (4 * K + 1) *
        (4 / (((4 * K + 5 : ℕ) : ℝ) *
          (2 : ℝ) ^ (4 * K + 5))) =
      (5 : ℝ) ^ (4 * K + 3) /
        (100 * ((4 * K + 5 : ℕ) : ℝ)) := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, mul_pow]
  rw [show 4 * K + 5 = (4 * K + 1) + 4 by omega, pow_add]
  rw [show 4 * K + 3 = (4 * K + 1) + 2 by omega, pow_add]
  norm_num
  field_simp
  ring

/-- At the first position after the exact base-ten transient, the scaled
bracket is already wider than one tenth.  Hence it is wider than every
nonempty decimal cylinder. -/
theorem postTransient_scaled_width_gt_one_tenth (K : ℕ) :
    (1 : ℝ) / 10 < (10 : ℝ) ^ (4 * K + 1) * twoThreeWidth K := by
  have hnat := ten_mul_four_mul_add_five_lt_five_pow K
  have hreal :
      (10 : ℝ) * ((4 * K + 5 : ℕ) : ℝ) <
        (5 : ℝ) ^ (4 * K + 3) := by
    exact_mod_cast hnat
  have hquot :
      (1 : ℝ) / 10 <
        (5 : ℝ) ^ (4 * K + 3) /
          (100 * ((4 * K + 5 : ℕ) : ℝ)) := by
    rw [lt_div_iff₀ (by positivity :
      (0 : ℝ) < 100 * ((4 * K + 5 : ℕ) : ℝ))]
    calc
      (1 : ℝ) / 10 *
          (100 * ((4 * K + 5 : ℕ) : ℝ)) =
        10 * ((4 * K + 5 : ℕ) : ℝ) := by ring
      _ < (5 : ℝ) ^ (4 * K + 3) := hreal
  calc
    (1 : ℝ) / 10 <
        (5 : ℝ) ^ (4 * K + 3) /
          (100 * ((4 * K + 5 : ℕ) : ℝ)) := hquot
    _ = (10 : ℝ) ^ (4 * K + 1) *
        (4 / (((4 * K + 5 : ℕ) : ℝ) *
          (2 : ℝ) ^ (4 * K + 5))) :=
      (scaled_first_omitted_two_term K).symm
    _ < (10 : ℝ) ^ (4 * K + 1) * twoThreeWidth K := by
      rw [twoThreeWidth_eq_explicit]
      apply mul_lt_mul_of_pos_left _ (by positivity)
      have hpositive :
          (0 : ℝ) <
            4 / (((4 * K + 5 : ℕ) : ℝ) *
              (3 : ℝ) ^ (4 * K + 5)) := by
        positivity
      linarith

end Theory.PiDigits.TwoThreeArctanShadow

#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeLowerRat_eq_pair_sum
#print axioms Theory.PiDigits.TwoThreeArctanShadow.four_mul_arctanTermRat_two_eq_fraction
#print axioms Theory.PiDigits.TwoThreeArctanShadow.four_mul_arctanTermRat_three_eq_fraction
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_two_four_mul_arctanTermRat_two
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_two_four_mul_arctanTermRat_three
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreePairRat_ne_zero
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_two_twoThreePairRat
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_two_twoThreePair_prefix
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_two_twoThreeLowerRat
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeLowerRat_ne_zero
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValNat_two_twoThreeLowerRat_den
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_five_four_mul_arctanTermRat_two
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_five_four_mul_arctanTermRat_three
#print axioms Theory.PiDigits.TwoThreeArctanShadow.neg_padicValNat_five_le_twoThreePairRat
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValNat_five_exponent_le_twoPrimaryWall
#print axioms Theory.PiDigits.TwoThreeArctanShadow.neg_twoPrimaryWall_le_padicValRat_five_twoThreeLowerRat
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValNat_five_twoThreeLowerRat_den_le
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeLowerRat_baseTen_denominator_exponent
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeLower_eq
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeUpper_eq
#print axioms Theory.PiDigits.TwoThreeArctanShadow.pi_eq_twoThreeArctan
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeLower_le_pi
#print axioms Theory.PiDigits.TwoThreeArctanShadow.pi_le_twoThreeUpper
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeUpper_sub_lower_eq_width
#print axioms Theory.PiDigits.TwoThreeArctanShadow.pi_mem_twoThree_bracket
#print axioms Theory.PiDigits.TwoThreeArctanShadow.twoThreeWidth_eq_explicit
#print axioms Theory.PiDigits.TwoThreeArctanShadow.ten_mul_four_mul_add_five_lt_five_pow
#print axioms Theory.PiDigits.TwoThreeArctanShadow.scaled_first_omitted_two_term
#print axioms Theory.PiDigits.TwoThreeArctanShadow.postTransient_scaled_width_gt_one_tenth
