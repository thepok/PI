import TheoryLib.PiQuantitativeBlockHitting.T63T63HuttonFiveAdicTransient
import TheoryLib.PiQuantitativeBlockHitting.T115T115SampledBBPCellDefectPhase

/-!
# T141: five-adic divisibility of the sampled BBP numerator

This module proves an exact arithmetic property of the actual reduced rational
`10^m * bbpPartial (7*m)`.  For `m >= 8`, its reduced denominator is a
five-unit and its reduced numerator contains at least `ceil(m/2)` factors of
five.  No distribution, covariance, conductor, cancellation, or digit-hitting
claim is made.
-/

open scoped BigOperators

namespace Theory.PiDigits.T141ScaledBBPFiveAdicNumerator

open Theory.PiDigits.HuttonFiveAdicTransient
open T74ThreePrimaryDecimation
open T77SelectedPadicDefectShell
open T98BBPArchimedeanTerm
open T115SampledBBPCellDefectPhase

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private lemma padicValRat_five_two : padicValRat 5 (2 : ℚ) = 0 :=
  Theory.PiDigits.MachinPrimeSurvival.padicValRat_natCast_eq_zero_of_not_dvd
    (by norm_num)

private lemma padicValRat_five_four : padicValRat 5 (4 : ℚ) = 0 :=
  Theory.PiDigits.MachinPrimeSurvival.padicValRat_natCast_eq_zero_of_not_dvd
    (by norm_num)

private lemma padicValRat_five_sixteen : padicValRat 5 (16 : ℚ) = 0 :=
  Theory.PiDigits.MachinPrimeSurvival.padicValRat_natCast_eq_zero_of_not_dvd
    (by norm_num)

private lemma padicValRat_five_ten : padicValRat 5 (10 : ℚ) = 1 := by
  have h5 : padicValRat 5 (5 : ℚ) = 1 :=
    padicValRat.self (p := 5) (by norm_num)
  rw [show (10 : ℚ) = (5 : ℚ) * 2 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num), h5, padicValRat_five_two]
  norm_num

private lemma linear_lt_five_pow (m : ℕ) (hm : 8 ≤ m) :
    56 * m + 5 < 5 ^ (m / 2 + 1) := by
  have haux : ∀ e : ℕ, 4 ≤ e → 112 * e + 61 < 5 ^ (e + 1) := by
    intro e he
    induction e, he using Nat.le_induction with
    | base => norm_num
    | succ e he ih =>
        rw [show e + 1 + 1 = (e + 1) + 1 by rfl, pow_succ]
        omega
  have he : 4 ≤ m / 2 := by omega
  have hmle : m ≤ 2 * (m / 2) + 1 := by omega
  exact lt_of_le_of_lt (by omega) (haux (m / 2) he)

private lemma linear_padicVal_le (m a : ℕ) (hm : 8 ≤ m)
    (ha0 : a ≠ 0) (ha : a ≤ 56 * m + 5) :
    padicValNat 5 a ≤ m / 2 := by
  by_contra h
  have hdvd : 5 ^ (m / 2 + 1) ∣ a :=
    (Nat.pow_dvd_iff_le_padicValNat (p := 5) (by norm_num) ha0).2 (by omega)
  have hle : 5 ^ (m / 2 + 1) ≤ a := Nat.le_of_dvd (by positivity) hdvd
  exact (not_lt_of_ge hle) (lt_of_le_of_lt ha (linear_lt_five_pow m hm))

private lemma poleOne_five_val_ge (m k : ℕ) (hm : 8 ≤ m) (hk : k ≤ 7 * m) :
    ((m + 1) / 2 : ℤ) ≤ padicValRat 5 ((10 : ℚ) ^ m * poleOne k) := by
  have hlin : padicValNat 5 (8 * k + 1) ≤ m / 2 :=
    linear_padicVal_le m (8 * k + 1) hm (by omega) (by omega)
  simp only [poleOne]
  rw [show (8 : ℚ) * k + 1 = ((8 * k + 1 : ℕ) : ℚ) by push_cast; ring]
  change ((m + 1) / 2 : ℤ) ≤ padicValRat 5
    ((10 : ℚ) ^ m * ((4 : ℚ) / ((8 * k + 1 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_ten,
    padicValRat.div (div_ne_zero (by norm_num) (by positivity))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (by norm_num) (by positivity), padicValRat_five_four,
    padicValRat.of_nat, padicValRat.pow (by norm_num), padicValRat_five_sixteen]
  norm_num
  omega

private lemma poleTwo_five_val_ge (m k : ℕ) (hm : 8 ≤ m) (hk : k ≤ 7 * m) :
    ((m + 1) / 2 : ℤ) ≤ padicValRat 5 ((10 : ℚ) ^ m * poleTwo k) := by
  have hlin : padicValNat 5 (2 * k + 1) ≤ m / 2 :=
    linear_padicVal_le m (2 * k + 1) hm (by omega) (by omega)
  simp only [poleTwo]
  rw [show (2 : ℚ) * k + 1 = ((2 * k + 1 : ℕ) : ℚ) by push_cast; ring]
  change ((m + 1) / 2 : ℤ) ≤ padicValRat 5
    ((10 : ℚ) ^ m * ((-1 : ℚ) / 2 / ((2 * k + 1 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_ten,
    padicValRat.div (div_ne_zero (div_ne_zero (by norm_num) (by norm_num))
      (by positivity)) (pow_ne_zero _ (by norm_num)),
    padicValRat.div (div_ne_zero (by norm_num) (by norm_num)) (by positivity),
    padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
    padicValRat_five_two, padicValRat.of_nat,
    padicValRat.pow (by norm_num), padicValRat_five_sixteen]
  norm_num
  omega

private lemma poleThree_five_val_ge (m k : ℕ) (hm : 8 ≤ m) (hk : k ≤ 7 * m) :
    ((m + 1) / 2 : ℤ) ≤ padicValRat 5 ((10 : ℚ) ^ m * poleThree k) := by
  have hlin : padicValNat 5 (8 * k + 5) ≤ m / 2 :=
    linear_padicVal_le m (8 * k + 5) hm (by omega) (by omega)
  simp only [poleThree]
  rw [show (8 : ℚ) * k + 5 = ((8 * k + 5 : ℕ) : ℚ) by push_cast; ring]
  change ((m + 1) / 2 : ℤ) ≤ padicValRat 5
    ((10 : ℚ) ^ m * ((-1 : ℚ) / ((8 * k + 5 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_ten,
    padicValRat.div (div_ne_zero (by norm_num) (by positivity))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.div (by norm_num) (by positivity), padicValRat.neg,
    padicValRat.of_nat, padicValRat.pow (by norm_num), padicValRat_five_sixteen]
  norm_num
  omega

private lemma poleFour_five_val_ge (m k : ℕ) (hm : 8 ≤ m) (hk : k ≤ 7 * m) :
    ((m + 1) / 2 : ℤ) ≤ padicValRat 5 ((10 : ℚ) ^ m * poleFour k) := by
  have hlin : padicValNat 5 (4 * k + 3) ≤ m / 2 :=
    linear_padicVal_le m (4 * k + 3) hm (by omega) (by omega)
  simp only [poleFour]
  rw [show (4 : ℚ) * k + 3 = ((4 * k + 3 : ℕ) : ℚ) by push_cast; ring]
  change ((m + 1) / 2 : ℤ) ≤ padicValRat 5
    ((10 : ℚ) ^ m * ((-1 : ℚ) / 2 / ((4 * k + 3 : ℕ) : ℚ) / (16 : ℚ) ^ k))
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
    padicValRat.pow (by norm_num), padicValRat_five_ten,
    padicValRat.div (div_ne_zero (div_ne_zero (by norm_num) (by norm_num))
      (by positivity)) (pow_ne_zero _ (by norm_num)),
    padicValRat.div (div_ne_zero (by norm_num) (by norm_num)) (by positivity),
    padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
    padicValRat_five_two, padicValRat.of_nat,
    padicValRat.pow (by norm_num), padicValRat_five_sixteen]
  norm_num
  omega

private lemma scaled_combined_five_val_ge (m k : ℕ) (hm : 8 ≤ m)
    (hk : k ≤ 7 * m) :
    ((m + 1) / 2 : ℤ) ≤
      padicValRat 5 ((10 : ℚ) ^ m * bbpCombinedTerm k) := by
  let c : ℤ := ((m + 1) / 2 : ℕ)
  have h1 := poleOne_five_val_ge m k hm hk
  have h2 := poleTwo_five_val_ge m k hm hk
  have h3 := poleThree_five_val_ge m k hm hk
  have h4 := poleFour_five_val_ge m k hm hk
  have hs := padicValRat_five_sum_lower (S := Finset.range 4)
    (fun i ↦ match i with
      | 0 => (10 : ℚ) ^ m * poleOne k
      | 1 => (10 : ℚ) ^ m * poleTwo k
      | 2 => (10 : ℚ) ^ m * poleThree k
      | _ => (10 : ℚ) ^ m * poleFour k)
    c (by
      intro i hi
      have hi' : i < 4 := Finset.mem_range.mp hi
      interval_cases i <;> simp_all [c])
  have hpos : 0 < (10 : ℚ) ^ m * bbpCombinedTerm k :=
    mul_pos (by positivity) (bbpCombinedTerm_pos k)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
  change ((10 : ℚ) ^ m * poleOne k + (10 : ℚ) ^ m * poleTwo k +
      (10 : ℚ) ^ m * poleThree k + (10 : ℚ) ^ m * poleFour k = 0) ∨ _ at hs
  have heq :
      (10 : ℚ) ^ m * poleOne k + (10 : ℚ) ^ m * poleTwo k +
          (10 : ℚ) ^ m * poleThree k + (10 : ℚ) ^ m * poleFour k =
        (10 : ℚ) ^ m * bbpCombinedTerm k := by
    simp only [bbpCombinedTerm]
    ring
  rw [heq] at hs
  exact hs.resolve_left (ne_of_gt hpos)

private theorem scaledBBPRat_five_val_ge (m : ℕ) (hm : 8 ≤ m) :
    ((m + 1) / 2 : ℤ) ≤ padicValRat 5 (scaledBBPRat m) := by
  have heq : scaledBBPRat m =
      ∑ k ∈ Finset.range (7 * m + 1), (10 : ℚ) ^ m * bbpCombinedTerm k := by
    unfold scaledBBPRat bbpPartial polePartial bbpCombinedTerm
    simp only [mul_add, Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
  rw [heq]
  have hs := padicValRat_five_sum_lower (S := Finset.range (7 * m + 1))
    (fun k ↦ (10 : ℚ) ^ m * bbpCombinedTerm k)
    (((m + 1) / 2 : ℕ) : ℤ) (fun k hk ↦
      scaled_combined_five_val_ge m k hm
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hpos : 0 < ∑ k ∈ Finset.range (7 * m + 1),
      (10 : ℚ) ^ m * bbpCombinedTerm k := by
    apply Finset.sum_pos'
    · intro k hk
      exact le_of_lt (mul_pos (pow_pos (by norm_num) _) (bbpCombinedTerm_pos k))
    · refine ⟨0, by simp, ?_⟩
      exact mul_pos (pow_pos (by norm_num) _) (bbpCombinedTerm_pos 0)
  exact hs.resolve_left (ne_of_gt hpos)

private lemma not_five_dvd_den_of_nonneg_val {q : ℚ}
    (h : 0 ≤ padicValRat 5 q) : ¬ 5 ∣ q.den := by
  intro hd
  have hnum : ¬ 5 ∣ q.num.natAbs := by
    intro hn
    have hg : 5 ∣ q.num.natAbs.gcd q.den := Nat.dvd_gcd hn hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at hg
    norm_num at hg
  have hvnum : padicValInt 5 q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  have hvden : 1 ≤ padicValNat 5 q.den :=
    one_le_padicValNat_of_dvd q.den_nz hd
  rw [padicValRat_def, hvnum] at h
  omega

/-- For `m >= 8`, the reduced denominator of the actual sampled BBP rational
is prime to five, while its reduced numerator contains `5^ceil(m/2)`. -/
theorem scaledBBPRat_five_arithmetic (m : ℕ) (hm : 8 ≤ m) :
    ¬ 5 ∣ (scaledBBPRat m).den ∧
      5 ^ ((m + 1) / 2) ∣ (scaledBBPRat m).num.natAbs := by
  have hv := scaledBBPRat_five_val_ge m hm
  have hv0 : 0 ≤ padicValRat 5 (scaledBBPRat m) := by omega
  have hden := not_five_dvd_den_of_nonneg_val hv0
  refine ⟨hden, ?_⟩
  by_cases hz : (scaledBBPRat m).num.natAbs = 0
  · simp [hz]
  · have hvden : padicValNat 5 (scaledBBPRat m).den = 0 :=
      padicValNat.eq_zero_of_not_dvd hden
    have hvnum : ((m + 1) / 2 : ℤ) ≤
        padicValInt 5 (scaledBBPRat m).num := by
      rw [padicValRat_def, hvden] at hv
      simpa using hv
    apply (Nat.pow_dvd_iff_le_padicValNat (p := 5) (by norm_num) hz).2
    exact_mod_cast (show (((m + 1) / 2 : ℕ) : ℤ) ≤
      (padicValNat 5 (scaledBBPRat m).num.natAbs : ℤ) by
        simpa [padicValInt] using hvnum)

end Theory.PiDigits.T141ScaledBBPFiveAdicNumerator

#print axioms Theory.PiDigits.T141ScaledBBPFiveAdicNumerator.scaledBBPRat_five_arithmetic
