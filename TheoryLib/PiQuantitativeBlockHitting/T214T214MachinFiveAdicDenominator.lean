import TheoryLib.PiQuantitativeBlockHitting.T198T198MachinBracketPack
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# T214: exact five-adic denominator law

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t214; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

namespace Theory.PiDigits.T214MachinFiveAdicDenominator

open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonFiveAdicTransient

def oddMachinTerm (d : ℕ) : ℚ :=
  (-1 : ℚ) ^ ((d - 1) / 2) * (8 * (3 : ℚ)⁻¹ ^ d + 4 * (7 : ℚ)⁻¹ ^ d) / d

section
variable {d m : ℕ}

/-- The combined numerator of the paired Hutton term at an odd exponent is a
five-unit. -/
lemma five_not_dvd_pairNumerator (d : ℕ) (hodd : Odd d) :
    ¬ (5 : ℕ) ∣ (8 * 7 ^ d + 4 * 3 ^ d) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hdvd
  have hz : ((8 * 7 ^ d + 4 * 3 ^ d : ℕ) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  have hcast : ((8 * 7 ^ d + 4 * 3 ^ d : ℕ) : ZMod 5) = 4 * 2 ^ d := by
    push_cast
    have h7 : (7 : ZMod 5) = 2 := by decide
    have h3 : (3 : ZMod 5) = -2 := by decide
    rw [h7, h3, hodd.neg_pow]
    ring
  rw [hcast] at hz
  exact
    (mul_ne_zero (by decide : (4 : ZMod 5) ≠ 0)
      (pow_ne_zero d (by decide : (2 : ZMod 5) ≠ 0))) hz

/-- The common denominator of the paired Hutton term is a five-unit. -/
lemma five_not_dvd_pairDenominator (d : ℕ) :
    ¬ (5 : ℕ) ∣ (3 ^ d * 7 ^ d) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hdvd
  have hz : ((3 ^ d * 7 ^ d : ℕ) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  have hcast : ((3 ^ d * 7 ^ d : ℕ) : ZMod 5) = 3 ^ d * 2 ^ d := by
    push_cast
    rw [show (7 : ZMod 5) = 2 by decide]
  rw [hcast] at hz
  exact
    (mul_ne_zero (pow_ne_zero d (by decide : (3 : ZMod 5) ≠ 0))
      (pow_ne_zero d (by decide : (2 : ZMod 5) ≠ 0))) hz

/-- Exact five-adic valuation of the odd Machin term: minus the five-adic
order of its odd exponent. -/
lemma oddMachinTerm_padicVal (d : ℕ) (hd0 : d ≠ 0) (hodd : Odd d) :
    padicValRat 5 (oddMachinTerm d) = -(padicValNat 5 d : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3 : (3 : ℚ) ≠ 0 := by norm_num
  have h7 : (7 : ℚ) ≠ 0 := by norm_num
  have hNQ : ((8 * 7 ^ d + 4 * 3 ^ d : ℕ) : ℚ) ≠ 0 := by
    have : (8 * 7 ^ d + 4 * 3 ^ d : ℕ) ≠ 0 := by positivity
    exact_mod_cast this
  have hDQ : ((3 ^ d * 7 ^ d : ℕ) : ℚ) ≠ 0 := by
    have : (3 ^ d * 7 ^ d : ℕ) ≠ 0 := by positivity
    exact_mod_cast this
  have hdQ : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd0
  have hinner :
      (8 * (3 : ℚ)⁻¹ ^ d + 4 * (7 : ℚ)⁻¹ ^ d) =
        ((8 * 7 ^ d + 4 * 3 ^ d : ℕ) : ℚ) / ((3 ^ d * 7 ^ d : ℕ) : ℚ) := by
    push_cast
    rw [inv_pow, inv_pow]
    field_simp
  have hpow : ((-1 : ℚ)) ^ ((d - 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hquot :
      ((8 * 7 ^ d + 4 * 3 ^ d : ℕ) : ℚ) / ((3 ^ d * 7 ^ d : ℕ) : ℚ) ≠ 0 :=
    div_ne_zero hNQ hDQ
  have hvalNum : padicValRat 5 ((8 * 7 ^ d + 4 * 3 ^ d : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    simpa using padicValNat.eq_zero_of_not_dvd (five_not_dvd_pairNumerator d hodd)
  have hvalDen : padicValRat 5 ((3 ^ d * 7 ^ d : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    simpa using padicValNat.eq_zero_of_not_dvd (five_not_dvd_pairDenominator d)
  have hvalNegOne : padicValRat 5 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  unfold oddMachinTerm
  rw [hinner, padicValRat.div (mul_ne_zero hpow hquot) hdQ,
    padicValRat.mul hpow hquot, padicValRat.pow (by norm_num : (-1 : ℚ) ≠ 0),
    hvalNegOne, padicValRat.div hNQ hDQ, hvalNum, hvalDen,
    padicValRat.of_nat]
  simp

lemma valuation_lower_bound (hd : d ∈ Finset.Icc 1 (4 * m + 3)) (hodd : Odd d) :
    -(Int.ofNat (Nat.log 5 (4 * m + 3))) ≤ padicValRat 5 (oddMachinTerm d) := by
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have hlt : d < 5 ^ (Nat.log 5 (4 * m + 3) + 1) :=
    lt_of_le_of_lt hd2 (Nat.lt_pow_succ_log_self (by norm_num) _)
  have hle :=
    Theory.PiDigits.HuttonFiveAdicTransient.padicValNat_five_le_of_lt_pow_succ
      d (Nat.log 5 (4 * m + 3)) (by omega) hlt
  have hofNat : (Int.ofNat (Nat.log 5 (4 * m + 3))) =
      ((Nat.log 5 (4 * m + 3) : ℕ) : ℤ) := rfl
  rw [oddMachinTerm_padicVal d (by omega) hodd, hofNat]
  omega
end

section
variable {m : ℕ}

lemma maximal_five_power_indices :
    {d ∈ Finset.Icc 1 (4 * m + 3) |
      Odd d ∧ padicValNat 5 d = Nat.log 5 (4 * m + 3)} ⊆
      {5 ^ Nat.log 5 (4 * m + 3), 3 * 5 ^ Nat.log 5 (4 * m + 3)} := by
  intro d hd
  rw [Finset.mem_filter, Finset.mem_Icc] at hd
  obtain ⟨⟨hd1, hd2⟩, hodd, hval⟩ := hd
  have hshape :=
    Theory.PiDigits.HuttonFiveAdicTransient.odd_maximal_five_adic_shape
      d (4 * m + 3) (Nat.log 5 (4 * m + 3)) (by omega) hodd hd2
      (Nat.lt_pow_succ_log_self (by norm_num) _) hval
  rcases hshape with h | h <;> simp [Finset.mem_insert, Finset.mem_singleton, h]

lemma surviving_residue_nonzero :
    ¬ (5 : ℤ) ∣
      Theory.PiDigits.HuttonFiveAdicTransient.fiveMinimumLayerNumerator
        (Nat.log 5 (4 * m + 3)) :=
  Theory.PiDigits.HuttonFiveAdicTransient.five_not_dvd_minimumLayerNumerator _

/-- The five-adic window bounds for the prefix length `4*m+3`. -/
lemma log_five_window (m : ℕ) :
    5 ^ Nat.log 5 (4 * m + 3) ≤ 4 * m + 3 ∧
      4 * m + 3 < 5 ^ (Nat.log 5 (4 * m + 3) + 1) := by
  refine ⟨Nat.pow_log_le_self 5 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _⟩

lemma machinLower_padicVal :
    padicValRat 5
      (Theory.PiDigits.HuttonRationalShadow.huttonLowerRat m) =
      -(Int.ofNat (Nat.log 5 (4 * m + 3))) := by
  obtain ⟨hlow, hhigh⟩ := log_five_window m
  simpa using
    Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_huttonLowerRat
      m (Nat.log 5 (4 * m + 3)) hlow hhigh

theorem denominator_five_adic
    (hVal : padicValRat 5
      (Theory.PiDigits.HuttonRationalShadow.huttonLowerRat m) =
        -(Int.ofNat (Nat.log 5 (4 * m + 3)))) :
    padicValNat 5
      (Theory.PiDigits.HuttonRationalShadow.huttonLowerRat m).den =
      Nat.log 5 (4 * m + 3) := by
  refine Theory.PiDigits.HuttonFiveAdicTransient.padicValNat_den_eq_of_padicValRat_neg
    _ _ (ne_of_gt (Theory.PiDigits.HuttonFiveAdicTransient.huttonLowerRat_pos m)) ?_
  simpa using hVal

/-- Discharged form: `machinLower_padicVal` supplies the explicit valuation
dependency of the denominator law. -/
theorem denominator_five_adic_discharged :
    padicValNat 5
      (Theory.PiDigits.HuttonRationalShadow.huttonLowerRat m).den =
      Nat.log 5 (4 * m + 3) :=
  denominator_five_adic machinLower_padicVal

end

end Theory.PiDigits.T214MachinFiveAdicDenominator
