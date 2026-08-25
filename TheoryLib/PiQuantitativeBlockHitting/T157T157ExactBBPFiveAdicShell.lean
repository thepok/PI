import TheoryLib.PiQuantitativeBlockHitting.T141T141ScaledBBPFiveAdicNumerator

/-!
# T157: exact five-adic shell of the sampled BBP rational

This module isolates the actual maximal five-primary poles in the four-term
BBP partial sum.  It proves the exact valuation of `scaledBBPRat m` and its
leading five-adic unit.  The congruence relation used below is defined inside
the five-local rationals, so it also handles an exactly zero difference.

No distribution or digit-hitting conclusion is asserted.
-/

open scoped BigOperators

namespace Theory.PiDigits.T157ExactBBPFiveAdicShell

open Theory.PiDigits.HuttonFiveAdicTransient
open Theory.PiDigits.MachinPrimeSurvival
open T74ThreePrimaryDecimation
open T77SelectedPadicDefectShell
open T98BBPArchimedeanTerm
open T115SampledBBPCellDefectPhase

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Exponent of the largest power of five not exceeding the largest BBP pole
denominator at sampled depth `7*m`. -/
def fiveShellLog (m : ℕ) : ℕ := Nat.log 5 (56 * m + 5)

/-- The largest five-power in the sampled BBP denominator window. -/
def fiveShellScale (m : ℕ) : ℕ := 5 ^ fiveShellLog m

/-- The second pole of the BBP sum reaches the maximal five-power exactly
when this indicator is one. -/
def secondaryPoleIndicator (m : ℕ) : ℕ :=
  if fiveShellScale m ≤ 14 * m + 1 then 1 else 0

/-- A congruence modulo five in the five-local rationals.  The first branch is
needed because `padicValRat` assigns an ordinary integer value to zero. -/
def FiveCongruent (x y : ℚ) : Prop :=
  x = y ∨ (1 : ℤ) ≤ padicValRat 5 (x - y)

/-- The normalized sampled BBP rational.  Unlike `5^(m-ℓ)`, this definition
uses only natural powers and is meaningful also at `m=0,1`, where the exact
valuation is negative. -/
def scaledBBPFiveUnit (m : ℕ) : ℚ :=
  (2 : ℚ) ^ m * (fiveShellScale m : ℚ) * bbpPartial (7 * m)

lemma fiveShellScale_pos (m : ℕ) : 0 < fiveShellScale m := by
  simp [fiveShellScale]

lemma fiveShellScale_le (m : ℕ) : fiveShellScale m ≤ 56 * m + 5 := by
  exact Nat.pow_log_le_self 5 (by omega)

lemma linear_lt_five_mul_shellScale (m : ℕ) :
    56 * m + 5 < 5 * fiveShellScale m := by
  simpa [fiveShellScale, fiveShellLog, pow_succ, mul_comm] using
    (Nat.lt_pow_succ_log_self (b := 5) (by norm_num) (56 * m + 5))

lemma fiveShellLog_padicVal_le {m d : ℕ} (hd : d ≤ 56 * m + 5) :
    padicValNat 5 d ≤ fiveShellLog m := by
  exact (padicValNat_le_nat_log d).trans (Nat.log_mono_right hd)

/-- An odd denominator in the sampled window having maximal five-adic
valuation is either the maximal five-power or three times that power. -/
lemma odd_eq_shellScale_or_three_mul_shellScale
    {m d : ℕ} (hd0 : d ≠ 0) (hodd : Odd d) (hd : d ≤ 56 * m + 5)
    (hval : padicValNat 5 d = fiveShellLog m) :
    d = fiveShellScale m ∨ d = 3 * fiveShellScale m := by
  have hpow : fiveShellScale m ∣ d := by
    apply (Nat.pow_dvd_iff_le_padicValNat (p := 5) (by norm_num) hd0).2
    simpa [fiveShellScale] using hval.ge
  obtain ⟨c, hc⟩ := hpow
  have hcLt : c < 5 := by
    have hT := fiveShellScale_pos m
    have hdLt : d < 5 * fiveShellScale m :=
      lt_of_le_of_lt hd (linear_lt_five_mul_shellScale m)
    rw [hc, Nat.mul_comm] at hdLt
    exact (Nat.mul_lt_mul_right hT).mp hdLt
  interval_cases c
  · simp_all
  · left; omega
  · exfalso
    rcases hodd with ⟨r, hr⟩
    omega
  · right; omega
  · exfalso
    rcases hodd with ⟨r, hr⟩
    omega

lemma five_pow_even_mod_eight (r : ℕ) : 5 ^ (2 * r) % 8 = 1 := by
  have h : 25 ≡ 1 [MOD 8] := by decide
  have hp := h.pow r
  simpa [pow_mul] using hp

lemma five_pow_odd_mod_eight (r : ℕ) : 5 ^ (2 * r + 1) % 8 = 5 := by
  rw [pow_add, Nat.mul_mod, five_pow_even_mod_eight]
  norm_num

/-- The maximal five-power occurs in exactly one of the first and third pole
families, according to the parity of the shell exponent. -/
lemma primaryPole_shellScale (m : ℕ) :
    (Even (fiveShellLog m) ∧
        8 * (fiveShellScale m / 8) + 1 = fiveShellScale m) ∨
      (Odd (fiveShellLog m) ∧
        8 * (fiveShellScale m / 8) + 5 = fiveShellScale m) := by
  rcases Nat.even_or_odd (fiveShellLog m) with he | ho
  · left
    rcases he with ⟨r, hr⟩
    have hmod : fiveShellScale m % 8 = 1 := by
      simp only [fiveShellScale, hr]
      simpa [two_mul] using five_pow_even_mod_eight r
    constructor
    · exact ⟨r, hr⟩
    · have hdiv := Nat.mod_add_div (fiveShellScale m) 8
      omega
  · right
    rcases ho with ⟨r, hr⟩
    have hmod : fiveShellScale m % 8 = 5 := by
      simp only [fiveShellScale, hr]
      exact five_pow_odd_mod_eight r
    constructor
    · exact ⟨r, hr⟩
    · have hdiv := Nat.mod_add_div (fiveShellScale m) 8
      omega

lemma primaryPole_index_le (m : ℕ) : fiveShellScale m / 8 ≤ 7 * m := by
  rcases primaryPole_shellScale m with h | h
  · have hle := fiveShellScale_le m
    omega
  · have hle := fiveShellScale_le m
    omega

lemma shellScale_eq_two_mul_index_add_one (m : ℕ) :
    2 * (fiveShellScale m / 2) + 1 = fiveShellScale m := by
  have hodd : Odd (fiveShellScale m) := by
    exact Odd.pow (by norm_num : Odd 5)
  rcases hodd with ⟨r, hr⟩
  have hdiv := Nat.mod_add_div (fiveShellScale m) 2
  have hmod : fiveShellScale m % 2 = 1 := by omega
  omega

lemma secondaryPoleIndicator_eq_one_iff (m : ℕ) :
    secondaryPoleIndicator m = 1 ↔ fiveShellScale m ≤ 14 * m + 1 := by
  simp [secondaryPoleIndicator]

lemma secondaryPoleIndicator_le_one (m : ℕ) :
    secondaryPoleIndicator m ≤ 1 := by
  unfold secondaryPoleIndicator
  split <;> omega

private lemma poleOne_val_lt_shell_of_ne
    (m k : ℕ) (hk : k ≤ 7 * m)
    (hne : 8 * k + 1 ≠ fiveShellScale m) :
    padicValNat 5 (8 * k + 1) < fiveShellLog m := by
  have hle : 8 * k + 1 ≤ 56 * m + 5 := by omega
  have hvle := fiveShellLog_padicVal_le hle
  by_contra hnot
  have hv : padicValNat 5 (8 * k + 1) = fiveShellLog m := by omega
  rcases odd_eq_shellScale_or_three_mul_shellScale
      (m := m) (d := 8 * k + 1) (by omega) ⟨4 * k, by omega⟩ hle hv with h | h
  · exact hne h
  · rcases primaryPole_shellScale m with hs | hs <;> omega

private lemma poleThree_val_lt_shell_of_ne
    (m k : ℕ) (hk : k ≤ 7 * m)
    (hne : 8 * k + 5 ≠ fiveShellScale m) :
    padicValNat 5 (8 * k + 5) < fiveShellLog m := by
  have hle : 8 * k + 5 ≤ 56 * m + 5 := by omega
  have hvle := fiveShellLog_padicVal_le hle
  by_contra hnot
  have hv : padicValNat 5 (8 * k + 5) = fiveShellLog m := by omega
  rcases odd_eq_shellScale_or_three_mul_shellScale
      (m := m) (d := 8 * k + 5) (by omega) ⟨4 * k + 2, by omega⟩ hle hv with h | h
  · exact hne h
  · rcases primaryPole_shellScale m with hs | hs <;> omega

private lemma poleTwo_val_lt_shell_of_ne
    (m k : ℕ) (hk : k ≤ 7 * m)
    (hne : 2 * k + 1 ≠ fiveShellScale m) :
    padicValNat 5 (2 * k + 1) < fiveShellLog m := by
  have hle : 2 * k + 1 ≤ 56 * m + 5 := by omega
  have hvle := fiveShellLog_padicVal_le hle
  by_contra hnot
  have hv : padicValNat 5 (2 * k + 1) = fiveShellLog m := by omega
  rcases odd_eq_shellScale_or_three_mul_shellScale
      (m := m) (d := 2 * k + 1) (by omega) ⟨k, by omega⟩ hle hv with h | h
  · exact hne h
  · have hwindow := linear_lt_five_mul_shellScale m
    omega

private lemma shellScale_mod_four (m : ℕ) : fiveShellScale m % 4 = 1 := by
  have h : 5 ≡ 1 [MOD 4] := by decide
  simpa [fiveShellScale] using h.pow (fiveShellLog m)

private lemma poleFour_val_lt_shell
    (m k : ℕ) (hk : k ≤ 7 * m) :
    padicValNat 5 (4 * k + 3) < fiveShellLog m := by
  have hle : 4 * k + 3 ≤ 56 * m + 5 := by omega
  have hvle := fiveShellLog_padicVal_le hle
  by_contra hnot
  have hv : padicValNat 5 (4 * k + 3) = fiveShellLog m := by omega
  rcases odd_eq_shellScale_or_three_mul_shellScale
      (m := m) (d := 4 * k + 3) (by omega) ⟨2 * k + 1, by omega⟩ hle hv with h | h
  · have hmod := shellScale_mod_four m
    have hdiv := Nat.mod_add_div (fiveShellScale m) 4
    omega
  · have hwindow := linear_lt_five_mul_shellScale m
    omega

private lemma padicValRat_five_two : padicValRat 5 (2 : ℚ) = 0 :=
  padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)

private lemma padicValRat_five_five : padicValRat 5 (5 : ℚ) = 1 :=
  padicValRat.self (by norm_num)

private lemma padicValRat_five_four : padicValRat 5 (4 : ℚ) = 0 :=
  padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)

private lemma padicValRat_five_sixteen : padicValRat 5 (16 : ℚ) = 0 :=
  padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)

private lemma normalized_poleOne_val_ge_one
    (m k : ℕ) (hk : k ≤ 7 * m)
    (hne : 8 * k + 1 ≠ fiveShellScale m) :
    (1 : ℤ) ≤ padicValRat 5 ((fiveShellScale m : ℚ) * poleOne k) := by
  have hv := poleOne_val_lt_shell_of_ne m k hk hne
  simp only [poleOne]
  rw [show (8 : ℚ) * k + 1 = ((8 * k + 1 : ℕ) : ℚ) by push_cast; ring]
  change (1 : ℤ) ≤ padicValRat 5
    (((fiveShellScale m : ℕ) : ℚ) *
      ((4 : ℚ) / ((8 * k + 1 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [show ((fiveShellScale m : ℕ) : ℚ) = (5 : ℚ) ^ fiveShellLog m by
      simp [fiveShellScale],
    padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_five,
    padicValRat.div (div_ne_zero (by norm_num) (by positivity))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (by norm_num) (by positivity), padicValRat_five_four,
    padicValRat.of_nat, padicValRat.pow (by norm_num),
    padicValRat_five_sixteen]
  norm_num
  omega

private lemma normalized_poleTwo_val_ge_one
    (m k : ℕ) (hk : k ≤ 7 * m)
    (hne : 2 * k + 1 ≠ fiveShellScale m) :
    (1 : ℤ) ≤ padicValRat 5 ((fiveShellScale m : ℚ) * poleTwo k) := by
  have hv := poleTwo_val_lt_shell_of_ne m k hk hne
  simp only [poleTwo]
  rw [show (2 : ℚ) * k + 1 = ((2 * k + 1 : ℕ) : ℚ) by push_cast; ring]
  change (1 : ℤ) ≤ padicValRat 5
    (((fiveShellScale m : ℕ) : ℚ) *
      ((-1 : ℚ) / 2 / ((2 * k + 1 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [show ((fiveShellScale m : ℕ) : ℚ) = (5 : ℚ) ^ fiveShellLog m by
      simp [fiveShellScale],
    padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_five,
    padicValRat.div (div_ne_zero (div_ne_zero (by norm_num) (by norm_num))
      (by positivity)) (pow_ne_zero _ (by norm_num)),
    padicValRat.div (div_ne_zero (by norm_num) (by norm_num)) (by positivity),
    padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
    padicValRat_five_two, padicValRat.of_nat,
    padicValRat.pow (by norm_num), padicValRat_five_sixteen]
  norm_num
  omega

private lemma normalized_poleThree_val_ge_one
    (m k : ℕ) (hk : k ≤ 7 * m)
    (hne : 8 * k + 5 ≠ fiveShellScale m) :
    (1 : ℤ) ≤ padicValRat 5 ((fiveShellScale m : ℚ) * poleThree k) := by
  have hv := poleThree_val_lt_shell_of_ne m k hk hne
  simp only [poleThree]
  rw [show (8 : ℚ) * k + 5 = ((8 * k + 5 : ℕ) : ℚ) by push_cast; ring]
  change (1 : ℤ) ≤ padicValRat 5
    (((fiveShellScale m : ℕ) : ℚ) *
      ((-1 : ℚ) / ((8 * k + 5 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [show ((fiveShellScale m : ℕ) : ℚ) = (5 : ℚ) ^ fiveShellLog m by
      simp [fiveShellScale],
    padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_five,
    padicValRat.div (div_ne_zero (by norm_num) (by positivity))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (by norm_num) (by positivity), padicValRat.neg,
    padicValRat.of_nat, padicValRat.pow (by norm_num),
    padicValRat_five_sixteen]
  norm_num
  omega

private lemma normalized_poleFour_val_ge_one
    (m k : ℕ) (hk : k ≤ 7 * m) :
    (1 : ℤ) ≤ padicValRat 5 ((fiveShellScale m : ℚ) * poleFour k) := by
  have hv := poleFour_val_lt_shell m k hk
  simp only [poleFour]
  rw [show (4 : ℚ) * k + 3 = ((4 * k + 3 : ℕ) : ℚ) by push_cast; ring]
  change (1 : ℤ) ≤ padicValRat 5
    (((fiveShellScale m : ℕ) : ℚ) *
      ((-1 : ℚ) / 2 / ((4 * k + 3 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [show ((fiveShellScale m : ℕ) : ℚ) = (5 : ℚ) ^ fiveShellLog m by
      simp [fiveShellScale],
    padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_five,
    padicValRat.div (div_ne_zero (div_ne_zero (by norm_num) (by norm_num))
      (by positivity)) (pow_ne_zero _ (by norm_num)),
    padicValRat.div (div_ne_zero (by norm_num) (by norm_num)) (by positivity),
    padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
    padicValRat_five_two, padicValRat.of_nat,
    padicValRat.pow (by norm_num), padicValRat_five_sixteen]
  norm_num
  omega

lemma FiveCongruent.refl (x : ℚ) : FiveCongruent x x := Or.inl rfl

lemma FiveCongruent.add {x y a b : ℚ}
    (hx : FiveCongruent x a) (hy : FiveCongruent y b) :
    FiveCongruent (x + y) (a + b) := by
  unfold FiveCongruent at hx hy ⊢
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · right
    simpa using hx
  by_cases hx0 : x - a = 0
  · right
    have hxa : x = a := sub_eq_zero.mp hx0
    simpa [hxa] using hy
  by_cases hy0 : y - b = 0
  · right
    have hyb : y = b := sub_eq_zero.mp hy0
    simpa [hyb] using hx
  have hs := padicValRat_five_sum_lower (S := Finset.range 2)
    (fun i ↦ if i = 0 then x - a else y - b) 1 (by
      intro i hi
      have hi' : i < 2 := Finset.mem_range.mp hi
      interval_cases i <;> simp_all)
  norm_num [Finset.sum_range_succ] at hs
  rcases hs with hs | hs
  · left
    have heq : x + y - (a + b) = (x - a) + (y - b) := by ring
    apply sub_eq_zero.mp
    rw [heq, hs]
  · right
    have heq : x + y - (a + b) = (x - a) + (y - b) := by ring
    rw [heq]
    exact hs

lemma FiveCongruent.sum {S : Finset ℕ} {f g : ℕ → ℚ}
    (h : ∀ i ∈ S, FiveCongruent (f i) (g i)) :
    FiveCongruent (∑ i ∈ S, f i) (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FiveCongruent.refl]
  | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih (fun i hi ↦ h i (by simp [hi])))

private lemma five_dvd_sixteen_pow_sub_one (k : ℕ) : 5 ∣ 16 ^ k - 1 := by
  have h : 16 ≡ 1 [MOD 5] := by decide
  have hp : 16 ^ k ≡ 1 [MOD 5] := by simpa using h.pow k
  have hpos : 0 < 16 ^ k := by positivity
  exact Nat.modEq_zero_iff_dvd.mp
    (hp.sub (by omega) (by omega) (Nat.ModEq.refl 1))

private lemma five_dvd_one_add_four_mul_sixteen_pow (k : ℕ) :
    5 ∣ 1 + 4 * 16 ^ k := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
  have h : 16 ≡ 1 [MOD 5] := by decide
  have hp := h.pow k
  rw [show 16 ^ k % 5 = 1 by simpa using hp]

private lemma padicValRat_nat_ge_one_of_five_dvd
    {n : ℕ} (hn0 : n ≠ 0) (hd : 5 ∣ n) :
    (1 : ℤ) ≤ padicValRat 5 (n : ℚ) := by
  rw [padicValRat.of_nat]
  exact_mod_cast
    ((Nat.pow_dvd_iff_le_padicValNat (p := 5) (by norm_num) hn0).1
      (by simpa using hd))

private lemma poleOne_at_shell_congruent_four
    (m k : ℕ) (hden : 8 * k + 1 = fiveShellScale m) :
    FiveCongruent ((fiveShellScale m : ℚ) * poleOne k) 4 := by
  simp only [poleOne]
  rw [show (8 : ℚ) * k + 1 = ((8 * k + 1 : ℕ) : ℚ) by push_cast; ring,
    hden]
  have hT : ((fiveShellScale m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (fiveShellScale_pos m).ne'
  change FiveCongruent
    (((fiveShellScale m : ℕ) : ℚ) *
      (4 / ((fiveShellScale m : ℕ) : ℚ) / (16 : ℚ) ^ k)) 4
  rw [show ((fiveShellScale m : ℕ) : ℚ) *
      (4 / ((fiveShellScale m : ℕ) : ℚ) / (16 : ℚ) ^ k) =
        4 / (16 : ℚ) ^ k by field_simp [hT]]
  by_cases hk0 : k = 0
  · subst k; norm_num [FiveCongruent]
  right
  have hn0 : 16 ^ k - 1 ≠ 0 := by
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have : 1 < 16 ^ k := one_lt_pow₀ (by norm_num) hkpos.ne'
    omega
  have hv := padicValRat_nat_ge_one_of_five_dvd hn0
    (five_dvd_sixteen_pow_sub_one k)
  have hpow0 : (16 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hle : 1 ≤ 16 ^ k := Nat.one_le_pow k 16 (by norm_num)
  have hcast : (((16 ^ k - 1 : ℕ) : ℚ)) = (16 : ℚ) ^ k - 1 := by
    rw [Nat.cast_sub hle]
    norm_num
  rw [show 4 / (16 : ℚ) ^ k - 4 =
      (-4 : ℚ) * ((16 ^ k - 1 : ℕ) : ℚ) / (16 : ℚ) ^ k by
        rw [hcast]
        field_simp
        ring,
    padicValRat.div (mul_ne_zero (by norm_num) (by exact_mod_cast hn0)) hpow0,
    padicValRat.mul (by norm_num) (by exact_mod_cast hn0),
    padicValRat.neg, padicValRat_five_four,
    padicValRat.pow (by norm_num), padicValRat_five_sixteen]
  simpa using hv

private lemma poleThree_at_shell_congruent_four
    (m k : ℕ) (hden : 8 * k + 5 = fiveShellScale m) :
    FiveCongruent ((fiveShellScale m : ℚ) * poleThree k) 4 := by
  simp only [poleThree]
  rw [show (8 : ℚ) * k + 5 = ((8 * k + 5 : ℕ) : ℚ) by push_cast; ring,
    hden]
  have hT : ((fiveShellScale m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (fiveShellScale_pos m).ne'
  rw [show ((fiveShellScale m : ℕ) : ℚ) *
      ((-1 : ℚ) / ((fiveShellScale m : ℕ) : ℚ) / (16 : ℚ) ^ k) =
        (-1 : ℚ) / (16 : ℚ) ^ k by
          field_simp [hT]]
  right
  let n := 1 + 4 * 16 ^ k
  have hn0 : n ≠ 0 := by dsimp [n]; positivity
  have hv := padicValRat_nat_ge_one_of_five_dvd hn0
    (five_dvd_one_add_four_mul_sixteen_pow k)
  have hpow0 : (16 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show (-1 : ℚ) / 16 ^ k - 4 =
      -((n : ℕ) : ℚ) / (16 : ℚ) ^ k by
        dsimp [n]; push_cast; field_simp; ring,
    padicValRat.div (neg_ne_zero.mpr (by exact_mod_cast hn0)) hpow0,
    padicValRat.neg, padicValRat.pow (by norm_num),
    padicValRat_five_sixteen]
  simpa using hv

private lemma poleTwo_at_shell_congruent_two
    (m k : ℕ) (hden : 2 * k + 1 = fiveShellScale m) :
    FiveCongruent ((fiveShellScale m : ℚ) * poleTwo k) 2 := by
  simp only [poleTwo]
  rw [show (2 : ℚ) * k + 1 = ((2 * k + 1 : ℕ) : ℚ) by push_cast; ring,
    hden]
  have hT : ((fiveShellScale m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (fiveShellScale_pos m).ne'
  rw [show ((fiveShellScale m : ℕ) : ℚ) *
      ((-1 : ℚ) / 2 / ((fiveShellScale m : ℕ) : ℚ) / (16 : ℚ) ^ k) =
        (-1 : ℚ) / 2 / (16 : ℚ) ^ k by
          field_simp [hT]]
  right
  let n := 1 + 4 * 16 ^ k
  have hn0 : n ≠ 0 := by dsimp [n]; positivity
  have hv := padicValRat_nat_ge_one_of_five_dvd hn0
    (five_dvd_one_add_four_mul_sixteen_pow k)
  have hpow0 : (16 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show (-1 : ℚ) / 2 / 16 ^ k - 2 =
      -((n : ℕ) : ℚ) / (2 * (16 : ℚ) ^ k) by
        dsimp [n]; push_cast; field_simp; ring,
    padicValRat.div (neg_ne_zero.mpr (by exact_mod_cast hn0))
      (mul_ne_zero (by norm_num) hpow0),
    padicValRat.neg,
    padicValRat.mul (by norm_num) hpow0,
    padicValRat_five_two, padicValRat.pow (by norm_num),
    padicValRat_five_sixteen]
  simpa using hv

private def poleOneCorrection (m k : ℕ) : ℚ :=
  if 8 * k + 1 = fiveShellScale m then 4 else 0

private def poleTwoCorrection (m k : ℕ) : ℚ :=
  if 2 * k + 1 = fiveShellScale m then 2 else 0

private def poleThreeCorrection (m k : ℕ) : ℚ :=
  if 8 * k + 5 = fiveShellScale m then 4 else 0

private lemma normalized_poleOne_congruent (m k : ℕ) (hk : k ≤ 7 * m) :
    FiveCongruent ((fiveShellScale m : ℚ) * poleOne k)
      (poleOneCorrection m k) := by
  by_cases h : 8 * k + 1 = fiveShellScale m
  · simpa [poleOneCorrection, h] using poleOne_at_shell_congruent_four m k h
  · right
    simpa [poleOneCorrection, h] using normalized_poleOne_val_ge_one m k hk h

private lemma normalized_poleTwo_congruent (m k : ℕ) (hk : k ≤ 7 * m) :
    FiveCongruent ((fiveShellScale m : ℚ) * poleTwo k)
      (poleTwoCorrection m k) := by
  by_cases h : 2 * k + 1 = fiveShellScale m
  · simpa [poleTwoCorrection, h] using poleTwo_at_shell_congruent_two m k h
  · right
    simpa [poleTwoCorrection, h] using normalized_poleTwo_val_ge_one m k hk h

private lemma normalized_poleThree_congruent (m k : ℕ) (hk : k ≤ 7 * m) :
    FiveCongruent ((fiveShellScale m : ℚ) * poleThree k)
      (poleThreeCorrection m k) := by
  by_cases h : 8 * k + 5 = fiveShellScale m
  · simpa [poleThreeCorrection, h] using poleThree_at_shell_congruent_four m k h
  · right
    simpa [poleThreeCorrection, h] using normalized_poleThree_val_ge_one m k hk h

private lemma normalized_poleFour_congruent_zero
    (m k : ℕ) (hk : k ≤ 7 * m) :
    FiveCongruent ((fiveShellScale m : ℚ) * poleFour k) 0 := by
  right
  simpa using normalized_poleFour_val_ge_one m k hk

private lemma sum_poleOneCorrection_of_even (m : ℕ)
    (he : Even (fiveShellLog m)) :
    ∑ k ∈ Finset.range (7 * m + 1), poleOneCorrection m k = 4 := by
  let j := fiveShellScale m / 8
  have hjle : j ≤ 7 * m := primaryPole_index_le m
  have hjmem : j ∈ Finset.range (7 * m + 1) := Finset.mem_range.mpr (by omega)
  have hjden : 8 * j + 1 = fiveShellScale m := by
    rcases primaryPole_shellScale m with h | h
    · exact h.2
    · exfalso
      rcases he with ⟨a, ha⟩
      rcases h.1 with ⟨b, hb⟩
      omega
  calc
    (∑ k ∈ Finset.range (7 * m + 1), poleOneCorrection m k) =
        poleOneCorrection m j := by
      apply Finset.sum_eq_single j
      · intro k hk hkj
        simp only [poleOneCorrection]
        split_ifs with hden
        · have : k = j := by omega
          exact (hkj this).elim
        · rfl
      · simp [hjmem]
    _ = 4 := by simp [poleOneCorrection, hjden]

private lemma sum_poleOneCorrection_of_odd (m : ℕ)
    (ho : Odd (fiveShellLog m)) :
    ∑ k ∈ Finset.range (7 * m + 1), poleOneCorrection m k = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  simp only [poleOneCorrection]
  split_ifs with hden
  · rcases primaryPole_shellScale m with h | h
    · rcases ho with ⟨a, ha⟩
      rcases h.1 with ⟨b, hb⟩
      omega
    · omega
  · rfl

private lemma sum_poleThreeCorrection_of_even (m : ℕ)
    (he : Even (fiveShellLog m)) :
    ∑ k ∈ Finset.range (7 * m + 1), poleThreeCorrection m k = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  simp only [poleThreeCorrection]
  split_ifs with hden
  · rcases primaryPole_shellScale m with h | h
    · omega
    · rcases he with ⟨a, ha⟩
      rcases h.1 with ⟨b, hb⟩
      omega
  · rfl

private lemma sum_poleThreeCorrection_of_odd (m : ℕ)
    (ho : Odd (fiveShellLog m)) :
    ∑ k ∈ Finset.range (7 * m + 1), poleThreeCorrection m k = 4 := by
  let j := fiveShellScale m / 8
  have hjle : j ≤ 7 * m := primaryPole_index_le m
  have hjmem : j ∈ Finset.range (7 * m + 1) := Finset.mem_range.mpr (by omega)
  have hjden : 8 * j + 5 = fiveShellScale m := by
    rcases primaryPole_shellScale m with h | h
    · exfalso
      rcases ho with ⟨a, ha⟩
      rcases h.1 with ⟨b, hb⟩
      omega
    · exact h.2
  calc
    (∑ k ∈ Finset.range (7 * m + 1), poleThreeCorrection m k) =
        poleThreeCorrection m j := by
      apply Finset.sum_eq_single j
      · intro k hk hkj
        simp only [poleThreeCorrection]
        split_ifs with hden
        · have : k = j := by omega
          exact (hkj this).elim
        · rfl
      · simp [hjmem]
    _ = 4 := by simp [poleThreeCorrection, hjden]

private lemma primaryCorrection_sum (m : ℕ) :
    (∑ k ∈ Finset.range (7 * m + 1), poleOneCorrection m k) +
      ∑ k ∈ Finset.range (7 * m + 1), poleThreeCorrection m k = 4 := by
  rcases Nat.even_or_odd (fiveShellLog m) with he | ho
  · rw [sum_poleOneCorrection_of_even m he,
      sum_poleThreeCorrection_of_even m he]
    norm_num
  · rw [sum_poleOneCorrection_of_odd m ho,
      sum_poleThreeCorrection_of_odd m ho]
    norm_num

private lemma secondaryCorrection_sum (m : ℕ) :
    ∑ k ∈ Finset.range (7 * m + 1), poleTwoCorrection m k =
      2 * secondaryPoleIndicator m := by
  by_cases hactive : fiveShellScale m ≤ 14 * m + 1
  · let j := fiveShellScale m / 2
    have hjden : 2 * j + 1 = fiveShellScale m :=
      shellScale_eq_two_mul_index_add_one m
    have hjle : j ≤ 7 * m := by omega
    have hjmem : j ∈ Finset.range (7 * m + 1) := Finset.mem_range.mpr (by omega)
    rw [secondaryPoleIndicator, if_pos hactive]
    calc
      (∑ k ∈ Finset.range (7 * m + 1), poleTwoCorrection m k) =
          poleTwoCorrection m j := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          simp only [poleTwoCorrection]
          split_ifs with hden
          · have : k = j := by omega
            exact (hkj this).elim
          · rfl
        · simp [hjmem]
      _ = 2 * (1 : ℚ) := by simp [poleTwoCorrection, hjden]
  · rw [secondaryPoleIndicator, if_neg hactive]
    norm_num
    apply Finset.sum_eq_zero
    intro k hk
    simp only [poleTwoCorrection]
    split_ifs with hden
    · exfalso
      apply hactive
      have hk' : k ≤ 7 * m := by
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      omega
    · rfl

/-- The normalized four-pole BBP partial sum has leading residue
`4 + 2*η_m` modulo five. -/
theorem normalized_bbpPartial_five_congruent (m : ℕ) :
    FiveCongruent
      ((fiveShellScale m : ℚ) * bbpPartial (7 * m))
      (4 + 2 * secondaryPoleIndicator m) := by
  let S := Finset.range (7 * m + 1)
  have h1 : FiveCongruent
      (∑ k ∈ S, (fiveShellScale m : ℚ) * poleOne k)
      (∑ k ∈ S, poleOneCorrection m k) := by
    apply FiveCongruent.sum
    intro k hk
    exact normalized_poleOne_congruent m k
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have h2 : FiveCongruent
      (∑ k ∈ S, (fiveShellScale m : ℚ) * poleTwo k)
      (∑ k ∈ S, poleTwoCorrection m k) := by
    apply FiveCongruent.sum
    intro k hk
    exact normalized_poleTwo_congruent m k
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have h3 : FiveCongruent
      (∑ k ∈ S, (fiveShellScale m : ℚ) * poleThree k)
      (∑ k ∈ S, poleThreeCorrection m k) := by
    apply FiveCongruent.sum
    intro k hk
    exact normalized_poleThree_congruent m k
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have h4 : FiveCongruent
      (∑ k ∈ S, (fiveShellScale m : ℚ) * poleFour k) 0 := by
    have hs : FiveCongruent
        (∑ k ∈ S, (fiveShellScale m : ℚ) * poleFour k)
        (∑ _k ∈ S, (0 : ℚ)) := by
      apply FiveCongruent.sum
      intro k hk
      exact normalized_poleFour_congruent_zero m k
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    simpa using hs
  have hall := ((h1.add h2).add h3).add h4
  have hprimary := primaryCorrection_sum m
  have hsecondary := secondaryCorrection_sum m
  unfold S at hall
  have hleft :
      (fiveShellScale m : ℚ) * bbpPartial (7 * m) =
        (∑ k ∈ Finset.range (7 * m + 1),
            (fiveShellScale m : ℚ) * poleOne k) +
          (∑ k ∈ Finset.range (7 * m + 1),
            (fiveShellScale m : ℚ) * poleTwo k) +
          (∑ k ∈ Finset.range (7 * m + 1),
            (fiveShellScale m : ℚ) * poleThree k) +
          (∑ k ∈ Finset.range (7 * m + 1),
            (fiveShellScale m : ℚ) * poleFour k) := by
    simp only [bbpPartial, polePartial, mul_add, Finset.mul_sum]
  have hright :
      (∑ k ∈ Finset.range (7 * m + 1), poleOneCorrection m k) +
          (∑ k ∈ Finset.range (7 * m + 1), poleTwoCorrection m k) +
          (∑ k ∈ Finset.range (7 * m + 1), poleThreeCorrection m k) + 0 =
        4 + 2 * secondaryPoleIndicator m := by
    linarith
  rw [hleft, ← hright]
  exact hall

lemma FiveCongruent.mul_left_of_val_zero {x y c : ℚ}
    (hc0 : c ≠ 0) (hc : padicValRat 5 c = 0)
    (hxy : FiveCongruent x y) : FiveCongruent (c * x) (c * y) := by
  unfold FiveCongruent at hxy ⊢
  rcases hxy with rfl | hxy
  · left; rfl
  by_cases hd0 : x - y = 0
  · left
    rw [sub_eq_zero.mp hd0]
  · right
    rw [show c * x - c * y = c * (x - y) by ring,
      padicValRat.mul hc0 hd0, hc]
    norm_num
    exact hxy

/-- Explicit leading five-adic unit of the actual sampled BBP rational.  In
the usual notation this is
`5^(ℓ_m-m) * scaledBBPRat m ≡ 2^m(4+2η_m) (mod 5)`, but the natural-power
normalization here also covers `m=0,1` without a signed exponent. -/
theorem scaledBBPFiveUnit_five_congruent (m : ℕ) :
    FiveCongruent (scaledBBPFiveUnit m)
      ((2 : ℚ) ^ m * (4 + 2 * secondaryPoleIndicator m)) := by
  have h2 : padicValRat 5 ((2 : ℚ) ^ m) = 0 := by
    rw [padicValRat.pow (by norm_num), padicValRat_five_two]
    norm_num
  have h := (normalized_bbpPartial_five_congruent m).mul_left_of_val_zero
    (pow_ne_zero _ (by norm_num)) h2
  simpa [scaledBBPFiveUnit, mul_assoc] using h

private lemma leadingUnitModel_five_val (m : ℕ) :
    padicValRat 5 ((2 : ℚ) ^ m * (4 + 2 * secondaryPoleIndicator m)) = 0 := by
  have heta := secondaryPoleIndicator_le_one m
  have h2pow : padicValRat 5 ((2 : ℚ) ^ m) = 0 := by
    rw [padicValRat.pow (by norm_num), padicValRat_five_two]
    norm_num
  interval_cases h : secondaryPoleIndicator m
  · norm_num [h, h2pow, padicValRat.mul, padicValRat_five_four]
  · have h6 : padicValRat 5 (6 : ℚ) = 0 :=
      padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
    norm_num [h, padicValRat.mul, h2pow, h6]

lemma padicVal_eq_zero_of_fiveCongruent_unit
    {x u : ℚ} (hu0 : u ≠ 0) (hu : padicValRat 5 u = 0)
    (h : FiveCongruent x u) : padicValRat 5 x = 0 := by
  unfold FiveCongruent at h
  rcases h with rfl | h
  · exact hu
  by_cases hd0 : x - u = 0
  · rw [sub_eq_zero.mp hd0]
    exact hu
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    rw [zero_sub, padicValRat.neg, hu] at h
    omega
  have heq : x = u + (x - u) := by ring
  rw [heq]
  calc
    padicValRat 5 (u + (x - u)) = padicValRat 5 u := by
      apply padicValRat.add_eq_of_lt
      · rwa [← heq]
      · exact hu0
      · exact hd0
      · rw [hu]
        omega
    _ = 0 := hu

lemma ne_zero_of_fiveCongruent_unit
    {x u : ℚ} (hu0 : u ≠ 0) (hu : padicValRat 5 u = 0)
    (h : FiveCongruent x u) : x ≠ 0 := by
  intro hx
  subst x
  unfold FiveCongruent at h
  rcases h with h | h
  · exact hu0 h.symm
  · rw [zero_sub, padicValRat.neg, hu] at h
    omega

/-- The normalized actual BBP rational is a five-adic unit at every sampled
depth, including the exceptional depths `m=0,1`. -/
theorem scaledBBPFiveUnit_five_val (m : ℕ) :
    padicValRat 5 (scaledBBPFiveUnit m) = 0 := by
  let u : ℚ := (2 : ℚ) ^ m * (4 + 2 * secondaryPoleIndicator m)
  have hu : padicValRat 5 u = 0 := leadingUnitModel_five_val m
  have hu0 : u ≠ 0 := by
    have heta := secondaryPoleIndicator_le_one m
    interval_cases h : secondaryPoleIndicator m <;>
      norm_num [u, h]
  exact padicVal_eq_zero_of_fiveCongruent_unit hu0 hu
    (scaledBBPFiveUnit_five_congruent m)

theorem scaledBBPFiveUnit_ne_zero (m : ℕ) : scaledBBPFiveUnit m ≠ 0 := by
  let u : ℚ := (2 : ℚ) ^ m * (4 + 2 * secondaryPoleIndicator m)
  have hu : padicValRat 5 u = 0 := leadingUnitModel_five_val m
  have hu0 : u ≠ 0 := by
    have heta := secondaryPoleIndicator_le_one m
    interval_cases h : secondaryPoleIndicator m <;>
      norm_num [u, h]
  exact ne_zero_of_fiveCongruent_unit hu0 hu
    (scaledBBPFiveUnit_five_congruent m)

theorem bbpPartial_sampled_ne_zero (m : ℕ) : bbpPartial (7 * m) ≠ 0 := by
  intro hp
  apply scaledBBPFiveUnit_ne_zero m
  simp [scaledBBPFiveUnit, hp]

theorem scaledBBPRat_ne_zero (m : ℕ) : scaledBBPRat m ≠ 0 := by
  unfold scaledBBPRat
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (bbpPartial_sampled_ne_zero m)

/-- Exact T141 valuation, with no burn-in: the loss of five-powers is exactly
the logarithmic shell exponent. -/
theorem scaledBBPRat_five_val_eq (m : ℕ) :
    padicValRat 5 (scaledBBPRat m) =
      (m : ℤ) - fiveShellLog m := by
  have hu := scaledBBPFiveUnit_five_val m
  have hu0 : scaledBBPFiveUnit m ≠ 0 := scaledBBPFiveUnit_ne_zero m
  have hp0 : bbpPartial (7 * m) ≠ 0 := bbpPartial_sampled_ne_zero m
  have h2pow0 : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hT0 : (fiveShellScale m : ℚ) ≠ 0 := by
    exact_mod_cast (fiveShellScale_pos m).ne'
  have hunit :
      padicValRat 5 (bbpPartial (7 * m)) = -(fiveShellLog m : ℤ) := by
    unfold scaledBBPFiveUnit at hu
    rw [padicValRat.mul (mul_ne_zero h2pow0 hT0) hp0,
      padicValRat.mul h2pow0 hT0,
      padicValRat.pow (by norm_num), padicValRat_five_two,
      show (fiveShellScale m : ℚ) = (5 : ℚ) ^ fiveShellLog m by
        simp [fiveShellScale],
      padicValRat.pow (by norm_num), padicValRat_five_five] at hu
    norm_num at hu
    omega
  unfold scaledBBPRat
  rw [show (10 : ℚ) ^ m = (2 : ℚ) ^ m * (5 : ℚ) ^ m by
      rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow],
    padicValRat.mul (mul_ne_zero h2pow0 (pow_ne_zero _ (by norm_num))) hp0,
    padicValRat.mul h2pow0 (pow_ne_zero _ (by norm_num)),
    padicValRat.pow (by norm_num), padicValRat_five_two,
    padicValRat.pow (by norm_num), padicValRat_five_five, hunit]
  ring

#print axioms Theory.PiDigits.T157ExactBBPFiveAdicShell.normalized_bbpPartial_five_congruent
#print axioms Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPFiveUnit_five_congruent
#print axioms Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPFiveUnit_five_val
#print axioms Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPFiveUnit_ne_zero
#print axioms Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPRat_five_val_eq

end Theory.PiDigits.T157ExactBBPFiveAdicShell
