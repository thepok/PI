import TheoryLib.PiQuantitativeBlockHitting.T67T67TwoThreeArctanShadow

/-!
# T68: simultaneous three- and seven-primary layers in Hutton shadows

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For `a >= 2`, put `R_a = 3^a * 7^(a+1)` and choose `K_a` from
`R_a = 4*K_a+3`.  This module isolates the elementary dominant-layer
mechanism behind the simultaneous primary-denominator calculation.  It
proves exact three- and seven-adic valuations of the rational Hutton lower
shadow at `K_a`, and hence exact multiplicities in its reduced denominator.

This is exact rational denominator arithmetic.  It proves no decimal
cylinder hit, phase-cancellation estimate, distribution theorem, or
every-word theorem for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.HuttonSimultaneousPrimary

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonFiveAdicTransient

/-- Radius at which the powers of three and seven are simultaneously large. -/
def primaryRadius (a : ℕ) : ℕ := 3 ^ a * 7 ^ (a + 1)

/-- The Hutton index corresponding to `primaryRadius`; the radius theorem
below proves that the remainder on division by four is exactly three. -/
def primaryIndex (a : ℕ) : ℕ := primaryRadius a / 4

/-- The elementary exponential inequality used inside the dominant-layer
argument. -/
lemma add_two_le_three_pow (t : ℕ) (ht : 1 ≤ t) : t + 2 ≤ 3 ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst t
        norm_num
      · have iht : t + 2 ≤ 3 ^ t := ih (by omega)
        rw [pow_succ]
        omega

/-- Dominant-layer lemma.  If the largest possible valuation below `R` is
small compared with the exact `p`-power in `R`, every earlier odd index has
score at least two below the endpoint score. -/
theorem odd_padic_score_le_radius_sub_two
    (p R u r : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hRodd : Odd R) (hrodd : Odd r)
    (hrpos : 0 < r) (hrR : r < R)
    (hvalR : padicValNat p R = u)
    (hlog : Nat.log p R ≤ p ^ u - 2) :
    r + padicValNat p r ≤ R - 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  let t := padicValNat p r
  have hRpos : R ≠ 0 := Nat.ne_of_gt (lt_trans hrpos hrR)
  have htlog : t ≤ Nat.log p R := by
    exact (padicValNat_le_nat_log r).trans
      (Nat.log_mono_right (Nat.le_of_lt hrR))
  have htbound : t ≤ p ^ u - 2 := htlog.trans hlog
  have htpowr : p ^ t ∣ r := by
    exact (padicValNat_dvd_iff_le (Nat.ne_of_gt hrpos)).2 (by simp [t])
  have hupowR : p ^ u ∣ R := by
    exact (padicValNat_dvd_iff_le hRpos).2 (by rw [hvalR])
  have hdpos : 0 < R - r := Nat.sub_pos_of_lt hrR
  have hdTwo : 2 ≤ R - r := by
    rcases hRodd with ⟨x, hx⟩
    rcases hrodd with ⟨y, hy⟩
    have hyx : y < x := by omega
    omega
  by_cases htzero : t = 0
  · omega
  have htpos : 1 ≤ t := by omega
  have hpge : 3 ≤ p := hp.odd_iff.mp hpodd
  by_cases htu : t < u
  · have htpowR : p ^ t ∣ R :=
      (pow_dvd_pow p (Nat.le_of_lt htu)).trans hupowR
    have htpowd : p ^ t ∣ R - r := Nat.dvd_sub htpowR htpowr
    have hpowlow : t + 2 ≤ p ^ t := by
      exact (add_two_le_three_pow t htpos).trans
        (Nat.pow_le_pow_left hpge t)
    have hpowdle : p ^ t ≤ R - r := Nat.le_of_dvd hdpos htpowd
    omega
  · have hut : u ≤ t := by omega
    have hupowr : p ^ u ∣ r :=
      (pow_dvd_pow p hut).trans htpowr
    have hupowd : p ^ u ∣ R - r := Nat.dvd_sub hupowR hupowr
    have hpowdle : p ^ u ≤ R - r := Nat.le_of_dvd hdpos hupowd
    omega

/-- The simultaneous radius is odd. -/
lemma primaryRadius_odd (a : ℕ) : Odd (primaryRadius a) := by
  unfold primaryRadius
  exact (by norm_num : Odd (3 : ℕ)).pow.mul
    (by norm_num : Odd (7 : ℕ)).pow

/-- The simultaneous radius is three modulo four. -/
lemma primaryRadius_mod_four (a : ℕ) : primaryRadius a % 4 = 3 := by
  have h21 : 21 ≡ 1 [MOD 4] := by decide
  have h7 : 7 ≡ 3 [MOD 4] := by decide
  have hprod : (3 * 7) ^ a * 7 ≡ 1 ^ a * 3 [MOD 4] :=
    (h21.pow a).mul h7
  have hprodmod : ((3 * 7) ^ a * 7) % 4 = 3 := by
    simpa [Nat.ModEq, mul_comm] using hprod
  calc
    primaryRadius a % 4 = ((3 * 7) ^ a * 7) % 4 := by
      congr 1
      unfold primaryRadius
      rw [pow_succ, mul_pow]
      ring
    _ = 3 := hprodmod

/-- The quotient definition of `primaryIndex` has the required exact Hutton
radius. -/
theorem four_mul_primaryIndex_add_three (a : ℕ) :
    4 * primaryIndex a + 3 = primaryRadius a := by
  have hmod := primaryRadius_mod_four a
  have hdiv := Nat.mod_add_div (primaryRadius a) 4
  unfold primaryIndex
  omega

/-- Exact three-adic order of the simultaneous radius. -/
theorem padicValNat_three_primaryRadius (a : ℕ) :
    padicValNat 3 (primaryRadius a) = a := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  unfold primaryRadius
  exact padicValNat_mul_pow_left a (a + 1) (by norm_num)

/-- Exact seven-adic order of the simultaneous radius. -/
theorem padicValNat_seven_primaryRadius (a : ℕ) :
    padicValNat 7 (primaryRadius a) = a + 1 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  unfold primaryRadius
  exact padicValNat_mul_pow_right a (a + 1) (by norm_num)

/-- A linear quantity is eventually dominated by the matching power of
three; the endpoint `a=2` is exact. -/
lemma three_mul_add_three_le_three_pow (a : ℕ) (ha : 2 ≤ a) :
    3 * a + 3 ≤ 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
      rw [pow_succ]
      omega

/-- The corresponding elementary domination for powers of seven. -/
lemma two_mul_add_two_le_seven_pow_succ (a : ℕ) :
    2 * a + 2 ≤ 7 ^ (a + 1) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      rw [show a + 1 + 1 = (a + 1) + 1 by rfl, pow_succ]
      omega

/-- The radius lies below the indicated pure power of three. -/
lemma primaryRadius_lt_three_pow (a : ℕ) :
    primaryRadius a < 3 ^ (3 * a + 2) := by
  have hseven : 7 ^ (a + 1) < 9 ^ (a + 1) :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  calc
    primaryRadius a = 3 ^ a * 7 ^ (a + 1) := rfl
    _ < 3 ^ a * 9 ^ (a + 1) :=
      Nat.mul_lt_mul_of_pos_left hseven (by positivity)
    _ = 3 ^ (3 * a + 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega

/-- The radius lies below the indicated pure power of seven. -/
lemma primaryRadius_lt_seven_pow (a : ℕ) (ha : 1 ≤ a) :
    primaryRadius a < 7 ^ (2 * a + 1) := by
  have hthree : 3 ^ a < 7 ^ a :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  calc
    primaryRadius a = 3 ^ a * 7 ^ (a + 1) := rfl
    _ < 7 ^ a * 7 ^ (a + 1) :=
      Nat.mul_lt_mul_of_pos_right hthree (by positivity)
    _ = 7 ^ (2 * a + 1) := by
      rw [← pow_add]
      congr 1
      omega

/-- The logarithmic hypothesis of the dominant-layer lemma at the prime
three. -/
theorem primaryRadius_log_three_le (a : ℕ) (ha : 2 ≤ a) :
    Nat.log 3 (primaryRadius a) ≤ 3 ^ a - 2 := by
  have hlog : Nat.log 3 (primaryRadius a) < 3 * a + 2 :=
    Nat.log_lt_of_lt_pow (by unfold primaryRadius; positivity)
      (primaryRadius_lt_three_pow a)
  have hpow := three_mul_add_three_le_three_pow a ha
  omega

/-- The logarithmic hypothesis of the dominant-layer lemma at the prime
seven. -/
theorem primaryRadius_log_seven_le (a : ℕ) (ha : 2 ≤ a) :
    Nat.log 7 (primaryRadius a) ≤ 7 ^ (a + 1) - 2 := by
  have hlog : Nat.log 7 (primaryRadius a) < 2 * a + 1 :=
    Nat.log_lt_of_lt_pow (by unfold primaryRadius; positivity)
      (primaryRadius_lt_seven_pow a (by omega))
  have hpow := two_mul_add_two_le_seven_pow_succ a
  omega

/-- Every earlier odd exponent has three-primary score at least two below
the simultaneous endpoint. -/
theorem primary_three_score_gap
    (a r : ℕ) (ha : 2 ≤ a) (hrodd : Odd r)
    (hrpos : 0 < r) (hrR : r < primaryRadius a) :
    r + padicValNat 3 r ≤ primaryRadius a - 2 := by
  exact odd_padic_score_le_radius_sub_two
    3 (primaryRadius a) a r (by norm_num) (by norm_num)
    (primaryRadius_odd a) hrodd hrpos hrR
    (padicValNat_three_primaryRadius a)
    (primaryRadius_log_three_le a ha)

/-- Every earlier odd exponent has seven-primary score at least two below
the simultaneous endpoint. -/
theorem primary_seven_score_gap
    (a r : ℕ) (ha : 2 ≤ a) (hrodd : Odd r)
    (hrpos : 0 < r) (hrR : r < primaryRadius a) :
    r + padicValNat 7 r ≤ primaryRadius a - 2 := by
  exact odd_padic_score_le_radius_sub_two
    7 (primaryRadius a) (a + 1) r (by norm_num) (by norm_num)
    (primaryRadius_odd a) hrodd hrpos hrR
    (padicValNat_seven_primaryRadius a)
    (primaryRadius_log_seven_le a ha)

/-- Exact three-adic valuation of one base-three Hutton term. -/
lemma padicValRat_three_huttonThreeTermRat (j : ℕ) :
    padicValRat 3 (huttonThreeTermRat j) =
      -(((2 * j + 1 : ℕ) : ℤ) +
        (padicValNat 3 (2 * j + 1) : ℤ)) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [huttonThreeTermRat_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hthreeq : (3 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 8 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 3 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ hthreeq)
  have hval8 : padicValRat 3 (8 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 3 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr :
      padicValRat 3 (((2 * j + 1 : ℕ) : ℚ)) =
        (padicValNat 3 (2 * j + 1) : ℤ) := by
    rw [padicValRat.of_nat]
  have hvalThree : padicValRat 3 (3 : ℚ) = 1 :=
    padicValRat.self (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    hval8, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ hthreeq), hvalr,
    padicValRat.pow hthreeq, hvalThree]
  push_cast
  ring

/-- Exact three-adic valuation of one base-seven Hutton term. -/
lemma padicValRat_three_huttonSevenTermRat (j : ℕ) :
    padicValRat 3 (huttonSevenTermRat j) =
      -(padicValNat 3 (2 * j + 1) : ℤ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [huttonSevenTermRat_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hsevenq : (7 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 4 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 7 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ hsevenq)
  have hval4 : padicValRat 3 (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 3 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr :
      padicValRat 3 (((2 * j + 1 : ℕ) : ℚ)) =
        (padicValNat 3 (2 * j + 1) : ℤ) := by
    rw [padicValRat.of_nat]
  have hvalSeven : padicValRat 3 (7 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    hval4, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ hsevenq), hvalr,
    padicValRat.pow hsevenq, hvalSeven]
  norm_num

/-- Exact seven-adic valuation of one base-three Hutton term. -/
lemma padicValRat_seven_huttonThreeTermRat (j : ℕ) :
    padicValRat 7 (huttonThreeTermRat j) =
      -(padicValNat 7 (2 * j + 1) : ℤ) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [huttonThreeTermRat_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hthreeq : (3 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 8 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 3 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ hthreeq)
  have hval8 : padicValRat 7 (8 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 7 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr :
      padicValRat 7 (((2 * j + 1 : ℕ) : ℚ)) =
        (padicValNat 7 (2 * j + 1) : ℤ) := by
    rw [padicValRat.of_nat]
  have hvalThree : padicValRat 7 (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    hval8, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ hthreeq), hvalr,
    padicValRat.pow hthreeq, hvalThree]
  norm_num

/-- Exact seven-adic valuation of one base-seven Hutton term. -/
lemma padicValRat_seven_huttonSevenTermRat (j : ℕ) :
    padicValRat 7 (huttonSevenTermRat j) =
      -(((2 * j + 1 : ℕ) : ℤ) +
        (padicValNat 7 (2 * j + 1) : ℤ)) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [huttonSevenTermRat_eq_fraction]
  have hrq : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hsevenq : (7 : ℚ) ≠ 0 := by norm_num
  have hnum0 : 4 * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hden0 :
      ((2 * j + 1 : ℕ) : ℚ) * 7 ^ (2 * j + 1) ≠ 0 :=
    mul_ne_zero hrq (pow_ne_zero _ hsevenq)
  have hval4 : padicValRat 7 (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 7 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalr :
      padicValRat 7 (((2 * j + 1 : ℕ) : ℚ)) =
        (padicValNat 7 (2 * j + 1) : ℤ) := by
    rw [padicValRat.of_nat]
  have hvalSeven : padicValRat 7 (7 : ℚ) = 1 :=
    padicValRat.self (by norm_num)
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    hval4, padicValRat.pow (by norm_num), hvalNegOne,
    padicValRat.mul hrq (pow_ne_zero _ hsevenq), hvalr,
    padicValRat.pow hsevenq, hvalSeven]
  push_cast
  ring

/-- Taylor index of the final Hutton term at the simultaneous radius. -/
def primaryLastIndex (a : ℕ) : ℕ := 2 * primaryIndex a + 1

/-- The odd exponent at `primaryLastIndex` is exactly `primaryRadius`. -/
theorem two_mul_primaryLastIndex_add_one (a : ℕ) :
    2 * primaryLastIndex a + 1 = primaryRadius a := by
  unfold primaryLastIndex
  rw [← four_mul_primaryIndex_add_three]
  omega

/-- The Hutton prefix at `primaryIndex` ends immediately after
`primaryLastIndex`. -/
theorem huttonTermCount_primaryIndex (a : ℕ) :
    huttonTermCount (primaryIndex a) = primaryLastIndex a + 1 := by
  unfold huttonTermCount primaryLastIndex
  omega

/-- At the prime three, remove the uniquely dominant final base-three term. -/
def primaryThreeRegularRat (a : ℕ) : ℚ :=
  (∑ j ∈ range (primaryLastIndex a), huttonThreeTermRat j) +
    ∑ j ∈ range (primaryLastIndex a + 1), huttonSevenTermRat j

/-- At the prime seven, remove the uniquely dominant final base-seven term. -/
def primarySevenRegularRat (a : ℕ) : ℚ :=
  (∑ j ∈ range (primaryLastIndex a + 1), huttonThreeTermRat j) +
    ∑ j ∈ range (primaryLastIndex a), huttonSevenTermRat j

/-- Exact three-primary decomposition of the Hutton lower shadow. -/
theorem huttonLowerRat_primary_eq_threeRegular_add_final (a : ℕ) :
    huttonLowerRat (primaryIndex a) =
      primaryThreeRegularRat a + huttonThreeTermRat (primaryLastIndex a) := by
  rw [huttonLowerRat_eq_term_sums, huttonTermCount_primaryIndex,
    sum_range_succ]
  unfold primaryThreeRegularRat
  ring

/-- Exact seven-primary decomposition of the Hutton lower shadow. -/
theorem huttonLowerRat_primary_eq_sevenRegular_add_final (a : ℕ) :
    huttonLowerRat (primaryIndex a) =
      primarySevenRegularRat a + huttonSevenTermRat (primaryLastIndex a) := by
  rw [huttonLowerRat_eq_term_sums, huttonTermCount_primaryIndex]
  unfold primarySevenRegularRat
  simp only [sum_range_succ]
  ring

/-- A finite rational sum whose terms all lie above a common `p`-adic
threshold is either zero or remains above that threshold. -/
lemma padicValRat_sum_lower
    (p : ℕ) (hp : p.Prime) {S : Finset ℕ} (f : ℕ → ℚ) (c : ℤ)
    (hf : ∀ x ∈ S, c ≤ padicValRat p (f x)) :
    (∑ x ∈ S, f x) = 0 ∨ c ≤ padicValRat p (∑ x ∈ S, f x) := by
  letI : Fact p.Prime := ⟨hp⟩
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hxs ih =>
      rw [sum_insert hxs]
      have hxval := hf x (mem_insert_self x S)
      have hsprop := ih (fun y hy => hf y (mem_insert_of_mem hy))
      by_cases hx0 : f x = 0
      · simpa [hx0] using hsprop
      by_cases hs0 : (∑ y ∈ S, f y) = 0
      · simp [hs0, hx0, hxval]
      rcases hsprop with hsprop | hsval
      · exact False.elim (hs0 hsprop)
      by_cases hsum0 : f x + ∑ y ∈ S, f y = 0
      · exact Or.inl hsum0
      · refine Or.inr (le_trans (le_min hxval hsval) ?_)
        exact padicValRat.min_le_padicValRat_add hsum0

/-- The same lower-threshold principle for adding two already controlled
blocks. -/
lemma padicValRat_add_lower
    (p : ℕ) (hp : p.Prime) (x y : ℚ) (c : ℤ)
    (hx : x = 0 ∨ c ≤ padicValRat p x)
    (hy : y = 0 ∨ c ≤ padicValRat p y) :
    x + y = 0 ∨ c ≤ padicValRat p (x + y) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hx with hx | hx
  · subst x
    simpa using hy
  rcases hy with hy | hy
  · subst y
    simpa using Or.inr hx
  by_cases hsum : x + y = 0
  · exact Or.inl hsum
  · exact Or.inr <| le_trans (le_min hx hy)
      (padicValRat.min_le_padicValRat_add hsum)

/-- The base-seven block is above the three-primary endpoint threshold. -/
lemma padicValRat_three_huttonSevenTerm_ge
    (a j : ℕ) (ha : 2 ≤ a) (hj : j < primaryLastIndex a + 1) :
    -((primaryRadius a - 2 : ℕ) : ℤ) ≤
      padicValRat 3 (huttonSevenTermRat j) := by
  have hrle : 2 * j + 1 ≤ primaryRadius a := by
    have hjle : j ≤ primaryLastIndex a := by omega
    rw [← two_mul_primaryLastIndex_add_one a]
    omega
  have hvalLog :
      padicValNat 3 (2 * j + 1) ≤ Nat.log 3 (primaryRadius a) :=
    (padicValNat_le_nat_log (2 * j + 1)).trans
      (Nat.log_mono_right hrle)
  have hlog := primaryRadius_log_three_le a ha
  have hpowle : 3 ^ a ≤ primaryRadius a := by
    unfold primaryRadius
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hvalNat :
      padicValNat 3 (2 * j + 1) ≤ primaryRadius a - 2 := by
    omega
  rw [padicValRat_three_huttonSevenTermRat]
  exact neg_le_neg (Int.ofNat_le.mpr hvalNat)

/-- The base-three block is above the seven-primary endpoint threshold. -/
lemma padicValRat_seven_huttonThreeTerm_ge
    (a j : ℕ) (ha : 2 ≤ a) (hj : j < primaryLastIndex a + 1) :
    -((primaryRadius a - 2 : ℕ) : ℤ) ≤
      padicValRat 7 (huttonThreeTermRat j) := by
  have hrle : 2 * j + 1 ≤ primaryRadius a := by
    have hjle : j ≤ primaryLastIndex a := by omega
    rw [← two_mul_primaryLastIndex_add_one a]
    omega
  have hvalLog :
      padicValNat 7 (2 * j + 1) ≤ Nat.log 7 (primaryRadius a) :=
    (padicValNat_le_nat_log (2 * j + 1)).trans
      (Nat.log_mono_right hrle)
  have hlog := primaryRadius_log_seven_le a ha
  have hpowle : 7 ^ (a + 1) ≤ primaryRadius a := by
    unfold primaryRadius
    rw [mul_comm]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hvalNat :
      padicValNat 7 (2 * j + 1) ≤ primaryRadius a - 2 := by
    omega
  rw [padicValRat_seven_huttonThreeTermRat]
  exact neg_le_neg (Int.ofNat_le.mpr hvalNat)

/-- Every earlier base-three term is above the three-primary endpoint
threshold. -/
lemma padicValRat_three_earlier_huttonThreeTerm_ge
    (a j : ℕ) (ha : 2 ≤ a) (hj : j < primaryLastIndex a) :
    -((primaryRadius a - 2 : ℕ) : ℤ) ≤
      padicValRat 3 (huttonThreeTermRat j) := by
  have hrlt : 2 * j + 1 < primaryRadius a := by
    rw [← two_mul_primaryLastIndex_add_one a]
    omega
  have hscore := primary_three_score_gap a (2 * j + 1) ha
    ⟨j, by omega⟩ (by omega) hrlt
  have hscoreZ :
      (((2 * j + 1) + padicValNat 3 (2 * j + 1) : ℕ) : ℤ) ≤
        ((primaryRadius a - 2 : ℕ) : ℤ) := by
    exact_mod_cast hscore
  rw [padicValRat_three_huttonThreeTermRat]
  simpa only [Nat.cast_add] using neg_le_neg hscoreZ

/-- Every earlier base-seven term is above the seven-primary endpoint
threshold. -/
lemma padicValRat_seven_earlier_huttonSevenTerm_ge
    (a j : ℕ) (ha : 2 ≤ a) (hj : j < primaryLastIndex a) :
    -((primaryRadius a - 2 : ℕ) : ℤ) ≤
      padicValRat 7 (huttonSevenTermRat j) := by
  have hrlt : 2 * j + 1 < primaryRadius a := by
    rw [← two_mul_primaryLastIndex_add_one a]
    omega
  have hscore := primary_seven_score_gap a (2 * j + 1) ha
    ⟨j, by omega⟩ (by omega) hrlt
  have hscoreZ :
      (((2 * j + 1) + padicValNat 7 (2 * j + 1) : ℕ) : ℤ) ≤
        ((primaryRadius a - 2 : ℕ) : ℤ) := by
    exact_mod_cast hscore
  rw [padicValRat_seven_huttonSevenTermRat]
  simpa only [Nat.cast_add] using neg_le_neg hscoreZ

/-- The complete regular block is above the three-primary endpoint
threshold, unless it vanishes. -/
theorem padicValRat_three_primaryThreeRegularRat_ge_or_zero
    (a : ℕ) (ha : 2 ≤ a) :
    primaryThreeRegularRat a = 0 ∨
      -((primaryRadius a - 2 : ℕ) : ℤ) ≤
        padicValRat 3 (primaryThreeRegularRat a) := by
  unfold primaryThreeRegularRat
  apply padicValRat_add_lower 3 (by norm_num)
  · apply padicValRat_sum_lower 3 (by norm_num)
    intro j hj
    exact padicValRat_three_earlier_huttonThreeTerm_ge
      a j ha (mem_range.mp hj)
  · apply padicValRat_sum_lower 3 (by norm_num)
    intro j hj
    exact padicValRat_three_huttonSevenTerm_ge
      a j ha (mem_range.mp hj)

/-- The complete regular block is above the seven-primary endpoint
threshold, unless it vanishes. -/
theorem padicValRat_seven_primarySevenRegularRat_ge_or_zero
    (a : ℕ) (ha : 2 ≤ a) :
    primarySevenRegularRat a = 0 ∨
      -((primaryRadius a - 2 : ℕ) : ℤ) ≤
        padicValRat 7 (primarySevenRegularRat a) := by
  unfold primarySevenRegularRat
  apply padicValRat_add_lower 7 (by norm_num)
  · apply padicValRat_sum_lower 7 (by norm_num)
    intro j hj
    exact padicValRat_seven_huttonThreeTerm_ge
      a j ha (mem_range.mp hj)
  · apply padicValRat_sum_lower 7 (by norm_num)
    intro j hj
    exact padicValRat_seven_earlier_huttonSevenTerm_ge
      a j ha (mem_range.mp hj)

/-- Exact valuation of the final, dominant base-three term. -/
theorem padicValRat_three_primary_final (a : ℕ) :
    padicValRat 3 (huttonThreeTermRat (primaryLastIndex a)) =
      -((primaryRadius a : ℤ) + a) := by
  rw [padicValRat_three_huttonThreeTermRat,
    two_mul_primaryLastIndex_add_one,
    padicValNat_three_primaryRadius]

/-- Exact valuation of the final, dominant base-seven term. -/
theorem padicValRat_seven_primary_final (a : ℕ) :
    padicValRat 7 (huttonSevenTermRat (primaryLastIndex a)) =
      -((primaryRadius a : ℤ) + (a + 1 : ℕ)) := by
  rw [padicValRat_seven_huttonSevenTermRat,
    two_mul_primaryLastIndex_add_one,
    padicValNat_seven_primaryRadius]

/-- Every base-three Hutton term is nonzero. -/
lemma huttonThreeTermRat_ne_zero (j : ℕ) : huttonThreeTermRat j ≠ 0 := by
  rw [huttonThreeTermRat_eq_fraction]
  positivity

/-- Every base-seven Hutton term is nonzero. -/
lemma huttonSevenTermRat_ne_zero (j : ℕ) : huttonSevenTermRat j ≠ 0 := by
  rw [huttonSevenTermRat_eq_fraction]
  positivity

/-- Adding a controlled regular block to a strictly lower nonzero endpoint
preserves the endpoint valuation. -/
lemma padicValRat_add_eq_right_of_lower
    (p : ℕ) (hp : p.Prime) (regular minimal : ℚ) (c m : ℤ)
    (hregular : regular = 0 ∨ c ≤ padicValRat p regular)
    (hminimal : padicValRat p minimal = m)
    (hminimal0 : minimal ≠ 0) (hmc : m < c) :
    padicValRat p (regular + minimal) = m := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hregular0 : regular = 0
  · simp [hregular0, hminimal]
  have hregularVal : c ≤ padicValRat p regular :=
    hregular.resolve_left hregular0
  have hlt : padicValRat p minimal < padicValRat p regular := by
    rw [hminimal]
    exact hmc.trans_le hregularVal
  have hsum0 : regular + minimal ≠ 0 := by
    intro hzero
    have heq : regular = -minimal := eq_neg_of_add_eq_zero_left hzero
    have hvaleq := congrArg (padicValRat p) heq
    rw [padicValRat.neg, hminimal] at hvaleq
    omega
  rw [add_comm]
  exact (padicValRat.add_eq_of_lt (by rwa [add_comm])
    hminimal0 hregular0 hlt).trans hminimal

/-- Exact three-adic valuation of the Hutton lower shadow on the simultaneous
primary subsequence. -/
theorem padicValRat_three_huttonLowerRat_primary
    (a : ℕ) (ha : 2 ≤ a) :
    padicValRat 3 (huttonLowerRat (primaryIndex a)) =
      -((primaryRadius a : ℤ) + a) := by
  rw [huttonLowerRat_primary_eq_threeRegular_add_final]
  apply padicValRat_add_eq_right_of_lower 3 (by norm_num)
    (primaryThreeRegularRat a)
    (huttonThreeTermRat (primaryLastIndex a))
    (-((primaryRadius a - 2 : ℕ) : ℤ))
    (-((primaryRadius a : ℤ) + a))
  · exact padicValRat_three_primaryThreeRegularRat_ge_or_zero a ha
  · exact padicValRat_three_primary_final a
  · exact huttonThreeTermRat_ne_zero _
  · have hpow : 3 ^ 2 ≤ 3 ^ a :=
      Nat.pow_le_pow_right (by norm_num) ha
    have hfactor : 3 ^ a ≤ primaryRadius a := by
      unfold primaryRadius
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hR : 2 ≤ primaryRadius a :=
      (by norm_num : 2 ≤ 3 ^ 2).trans (hpow.trans hfactor)
    omega

/-- Exact seven-adic valuation of the Hutton lower shadow on the simultaneous
primary subsequence. -/
theorem padicValRat_seven_huttonLowerRat_primary
    (a : ℕ) (ha : 2 ≤ a) :
    padicValRat 7 (huttonLowerRat (primaryIndex a)) =
      -((primaryRadius a : ℤ) + (a + 1 : ℕ)) := by
  rw [huttonLowerRat_primary_eq_sevenRegular_add_final]
  apply padicValRat_add_eq_right_of_lower 7 (by norm_num)
    (primarySevenRegularRat a)
    (huttonSevenTermRat (primaryLastIndex a))
    (-((primaryRadius a - 2 : ℕ) : ℤ))
    (-((primaryRadius a : ℤ) + (a + 1 : ℕ)))
  · exact padicValRat_seven_primarySevenRegularRat_ge_or_zero a ha
  · exact padicValRat_seven_primary_final a
  · exact huttonSevenTermRat_ne_zero _
  · have hpow : 3 ^ 2 ≤ 3 ^ a :=
      Nat.pow_le_pow_right (by norm_num) ha
    have hfactor : 3 ^ a ≤ primaryRadius a := by
      unfold primaryRadius
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hR : 2 ≤ primaryRadius a :=
      (by norm_num : 2 ≤ 3 ^ 2).trans (hpow.trans hfactor)
    omega

/-- A negative exact rational valuation is exactly the corresponding
reduced-denominator multiplicity. -/
lemma padicValNat_den_eq_of_padicValRat_neg
    (p : ℕ) (hp : p.Prime) (q : ℚ) (e : ℕ) (hq0 : q ≠ 0)
    (hval : padicValRat p q = -(e : ℤ)) :
    padicValNat p q.den = e := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnumZ : q.num ≠ 0 := by
    intro hz
    apply hq0
    rw [← q.num_div_den, hz]
    norm_num
  have hnumAbs : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnumZ
  have hnumNot : ¬ p ∣ q.num.natAbs := by
    intro hnumDiv
    have hcop : Nat.Coprime p q.den :=
      Nat.Coprime.of_dvd_left hnumDiv q.reduced
    have hdenNot : ¬ p ∣ q.den := hp.coprime_iff_not_dvd.mp hcop
    have hvden : padicValNat p q.den = 0 :=
      padicValNat.eq_zero_of_not_dvd hdenNot
    have hvnumNat : 1 ≤ padicValNat p q.num.natAbs :=
      (padicValNat_dvd_iff_le hnumAbs).1 (by simpa using hnumDiv)
    have hvnumInt : (1 : ℤ) ≤ padicValInt p q.num := by
      simpa [padicValInt] using hvnumNat
    rw [padicValRat_def, hvden] at hval
    omega
  have hvnumInt : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnumNot
  rw [padicValRat_def, hvnumInt] at hval
  omega

/-- Exact multiplicity of three in the reduced denominator of the selected
Hutton lower shadow. -/
theorem padicValNat_three_huttonLowerRat_den_primary
    (a : ℕ) (ha : 2 ≤ a) :
    padicValNat 3 (huttonLowerRat (primaryIndex a)).den =
      primaryRadius a + a := by
  apply padicValNat_den_eq_of_padicValRat_neg 3 (by norm_num)
    (huttonLowerRat (primaryIndex a)) (primaryRadius a + a)
  · exact ne_of_gt (huttonLowerRat_pos _)
  · simpa only [Nat.cast_add] using
      padicValRat_three_huttonLowerRat_primary a ha

/-- Exact multiplicity of seven in the reduced denominator of the same
Hutton lower shadow. -/
theorem padicValNat_seven_huttonLowerRat_den_primary
    (a : ℕ) (ha : 2 ≤ a) :
    padicValNat 7 (huttonLowerRat (primaryIndex a)).den =
      primaryRadius a + a + 1 := by
  apply padicValNat_den_eq_of_padicValRat_neg 7 (by norm_num)
    (huttonLowerRat (primaryIndex a)) (primaryRadius a + a + 1)
  · exact ne_of_gt (huttonLowerRat_pos _)
  · have hval := padicValRat_seven_huttonLowerRat_primary a ha
    push_cast at hval ⊢
    simpa [add_assoc] using hval

/-- The two primary multiplicities hold simultaneously at every selected
index. -/
theorem huttonLowerRat_den_simultaneous_primary
    (a : ℕ) (ha : 2 ≤ a) :
    padicValNat 3 (huttonLowerRat (primaryIndex a)).den =
        primaryRadius a + a ∧
      padicValNat 7 (huttonLowerRat (primaryIndex a)).den =
        primaryRadius a + a + 1 :=
  ⟨padicValNat_three_huttonLowerRat_den_primary a ha,
    padicValNat_seven_huttonLowerRat_den_primary a ha⟩

end Theory.PiDigits.HuttonSimultaneousPrimary

#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.add_two_le_three_pow
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.odd_padic_score_le_radius_sub_two
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primaryRadius_odd
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primaryRadius_mod_four
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.four_mul_primaryIndex_add_three
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValNat_three_primaryRadius
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValNat_seven_primaryRadius
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.three_mul_add_three_le_three_pow
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.two_mul_add_two_le_seven_pow_succ
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primaryRadius_lt_three_pow
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primaryRadius_lt_seven_pow
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primaryRadius_log_three_le
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primaryRadius_log_seven_le
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primary_three_score_gap
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.primary_seven_score_gap
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_three_huttonThreeTermRat
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_three_huttonSevenTermRat
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_seven_huttonThreeTermRat
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_seven_huttonSevenTermRat
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.two_mul_primaryLastIndex_add_one
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.huttonTermCount_primaryIndex
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.huttonLowerRat_primary_eq_threeRegular_add_final
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.huttonLowerRat_primary_eq_sevenRegular_add_final
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_sum_lower
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_add_lower
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_three_huttonSevenTerm_ge
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_seven_huttonThreeTerm_ge
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_three_earlier_huttonThreeTerm_ge
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_seven_earlier_huttonSevenTerm_ge
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_three_primaryThreeRegularRat_ge_or_zero
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_seven_primarySevenRegularRat_ge_or_zero
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_three_primary_final
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_seven_primary_final
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.huttonThreeTermRat_ne_zero
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.huttonSevenTermRat_ne_zero
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_add_eq_right_of_lower
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_three_huttonLowerRat_primary
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValRat_seven_huttonLowerRat_primary
#print axioms Theory.PiDigits.HuttonSimultaneousPrimary.padicValNat_den_eq_of_padicValRat_neg
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValNat_three_huttonLowerRat_den_primary
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.padicValNat_seven_huttonLowerRat_den_primary
#print axioms
  Theory.PiDigits.HuttonSimultaneousPrimary.huttonLowerRat_den_simultaneous_primary
