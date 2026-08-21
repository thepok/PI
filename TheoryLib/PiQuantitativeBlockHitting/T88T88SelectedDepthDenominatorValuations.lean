import TheoryLib.PiQuantitativeBlockHitting.T87T87LiteralSP1Packaging

/-!
# T88: selected-depth denominator valuations

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module records elementary denominator valuation bounds for the four BBP
linear denominators at positive even selected depths.  It is only a
denominator-clearing layer for later finite rational calculations.  It makes
no assertion about a hidden carry, a decimal expansion, canonical V1, or an
SP1 resolution.
-/

namespace Theory.PiDigits.T88SelectedDepthDenominatorValuations

open T77SelectedPadicDefectShell

/-- Even powers of three leave remainder one modulo eight. -/
theorem three_pow_two_t_mod_eight (t : ℕ) : 3 ^ (2 * t) % 8 = 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have h2 : 2 * (t + 1) = 2 * t + 2 := by omega
      rw [h2, pow_add, Nat.mul_mod, ih]
      norm_num

/-- The selected-depth numerator at a positive even epoch is divisible by
eight. -/
theorem eight_dvd_five_three_pow_sub_thirteen (t : ℕ) (ht : 1 ≤ t) :
    8 ∣ 5 * 3 ^ (2 * t) - 13 := by
  have hmod := three_pow_two_t_mod_eight t
  have hunpack : 1 + 8 * (3 ^ (2 * t) / 8) = 3 ^ (2 * t) := by
    have h := Nat.mod_add_div (3 ^ (2 * t)) 8
    omega
  have hnine : 9 ≤ 3 ^ (2 * t) := by
    have h2 : 3 ^ 2 = 9 := by norm_num
    have hle : 3 ^ 2 ≤ 3 ^ (2 * t) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨5 * (3 ^ (2 * t) / 8) - 1, ?_⟩
  omega

/-- Even powers of three leave remainder one modulo four. -/
theorem three_pow_two_t_mod_four (t : ℕ) : 3 ^ (2 * t) % 4 = 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have h2 : 2 * (t + 1) = 2 * t + 2 := by omega
      rw [h2, pow_add, Nat.mul_mod, ih]
      norm_num

/-- At every positive even epoch, the selected-depth quotient is exact. -/
theorem selectedDepth_scale_exact (t : ℕ) (ht : 1 ≤ t) :
    8 * selectedDepth (2 * t) + 13 = 5 * 3 ^ (2 * t) := by
  have hq8 : 8 * selectedDepth (2 * t) = 5 * 3 ^ (2 * t) - 13 := by
    simp only [selectedDepth]
    exact Nat.mul_div_cancel'
      (eight_dvd_five_three_pow_sub_thirteen t ht)
  have hpow9 : 9 ≤ 3 ^ (2 * t) := by
    have h2 : 3 ^ 2 = 9 := by norm_num
    have hle : 3 ^ 2 ≤ 3 ^ (2 * t) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

/-- The four BBP linear denominators have the indicated strict size bounds
through an inclusive positive even selected depth. -/
theorem denominator_size_bundle (t k : ℕ) (ht : 1 ≤ t)
    (hk : k ≤ selectedDepth (2 * t)) :
    2 * k + 1 < 3 ^ (2 * t + 1) ∧
      4 * k + 3 < 3 ^ (2 * t + 1) ∧
      8 * k + 1 < 2 * 3 ^ (2 * t + 1) ∧
      8 * k + 5 < 2 * 3 ^ (2 * t + 1) := by
  have hscale := selectedDepth_scale_exact t ht
  have hpow9 : 9 ≤ 3 ^ (2 * t) := by
    have h2 : 3 ^ 2 = 9 := by norm_num
    have hle : 3 ^ 2 ≤ 3 ^ (2 * t) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : 3 ^ (2 * t + 1) = 3 * 3 ^ (2 * t) := by
    rw [pow_succ]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [hpow] <;> omega

/-- Inside the inclusive positive even selected-depth range, the second BBP
linear denominator carries at most the epoch's `2 * t` factors of three. -/
theorem poleTwo_denominator_val_le (t k : ℕ) (ht : 1 ≤ t)
    (hk : k ≤ selectedDepth (2 * t)) :
    padicValNat 3 (2 * k + 1) ≤ 2 * t := by
  by_contra hcon
  have hv : 2 * t < padicValNat 3 (2 * k + 1) := by omega
  have hdvd : 3 ^ (2 * t + 1) ∣ 2 * k + 1 :=
    (Nat.pow_dvd_iff_le_padicValNat (p := 3) (by norm_num) (by omega)).2
      (by omega)
  have hle : 3 ^ (2 * t + 1) ≤ 2 * k + 1 :=
    Nat.le_of_dvd (by omega) hdvd
  have hpow : 3 ^ (2 * t + 1) = 3 * 3 ^ (2 * t) := by
    rw [pow_succ]
    ring
  have hsd : selectedDepth (2 * t) = (5 * 3 ^ (2 * t) - 13) / 8 := rfl
  have hq8 : 8 * selectedDepth (2 * t) = 5 * 3 ^ (2 * t) - 13 := by
    rw [hsd]
    exact Nat.mul_div_cancel'
      (eight_dvd_five_three_pow_sub_thirteen t ht)
  rw [hpow] at hle
  omega

/-- Inside the inclusive positive even selected-depth range, the first BBP
linear denominator carries at most the epoch's `2 * t` factors of three. -/
theorem poleOne_denominator_val_le (t k : ℕ) (ht : 1 ≤ t)
    (hk : k ≤ selectedDepth (2 * t)) :
    padicValNat 3 (8 * k + 1) ≤ 2 * t := by
  by_contra hcon
  have hv : 2 * t < padicValNat 3 (8 * k + 1) := by omega
  have hdvd : 3 ^ (2 * t + 1) ∣ 8 * k + 1 :=
    (Nat.pow_dvd_iff_le_padicValNat (p := 3) (by norm_num) (by omega)).2
      (by omega)
  have hmpos : 0 < 8 * k + 1 := by omega
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 1 ≤ m := by
    by_contra hc
    have h0 : m = 0 := by omega
    rw [h0, Nat.mul_zero] at hm
    omega
  have hscale := selectedDepth_scale_exact t ht
  have hpow : 3 ^ (2 * t + 1) = 3 * 3 ^ (2 * t) := by
    rw [pow_succ]
    ring
  have hx9 : 9 ≤ 3 ^ (2 * t) := by
    have h2 : 3 ^ 2 = 9 := by norm_num
    have hle : 3 ^ 2 ≤ 3 ^ (2 * t) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlt : 8 * k + 1 < 2 * 3 ^ (2 * t + 1) := by
    rw [hpow]
    omega
  rw [hm] at hlt
  have hm2 : m < 2 := by
    by_contra hc
    have h2 : 2 ≤ m := by omega
    have hstep : 3 ^ (2 * t + 1) * 2 ≤ 3 ^ (2 * t + 1) * m :=
      Nat.mul_le_mul_left _ h2
    rw [Nat.mul_comm 2 (3 ^ (2 * t + 1))] at hlt
    exact Nat.not_lt.2 hstep hlt
  have hmeq : m = 1 := by omega
  rw [hmeq, Nat.mul_one] at hm
  have hmodpow : 3 ^ (2 * t + 1) % 8 = 3 := by
    rw [hpow, Nat.mul_mod, three_pow_two_t_mod_eight]
  have hmodk : (8 * k + 1) % 8 = 1 := by omega
  rw [hm] at hmodk
  omega

/-- Inside the inclusive positive even selected-depth range, the fourth BBP
linear denominator carries at most `2 * t - 1` factors of three. -/
theorem poleFour_denominator_val_le_sharp (t k : ℕ) (ht : 1 ≤ t)
    (hk : k ≤ selectedDepth (2 * t)) :
    padicValNat 3 (4 * k + 3) ≤ 2 * t - 1 := by
  by_contra hcon
  have hv : 2 * t ≤ padicValNat 3 (4 * k + 3) := by omega
  have hdvd : 3 ^ (2 * t) ∣ 4 * k + 3 :=
    (Nat.pow_dvd_iff_le_padicValNat (p := 3) (by norm_num) (by omega)).2
      (by omega)
  obtain ⟨m, hm⟩ := hdvd
  have hmod4 := three_pow_two_t_mod_four t
  have hrhs : 3 ^ (2 * t) * m % 4 = m % 4 := by
    rw [Nat.mul_mod, hmod4, Nat.one_mul, Nat.mod_mod]
  have hm4 : m % 4 = 3 := by
    have h : (4 * k + 3) % 4 = (3 ^ (2 * t) * m) % 4 := by rw [hm]
    rw [hrhs] at h
    omega
  have hmge : 3 ≤ m := by omega
  have hlower : 3 * 3 ^ (2 * t) ≤ 4 * k + 3 := by
    calc 3 * 3 ^ (2 * t) = 3 ^ (2 * t) * 3 := by ring
      _ ≤ 3 ^ (2 * t) * m := Nat.mul_le_mul_left _ hmge
      _ = 4 * k + 3 := hm.symm
  have hscale := selectedDepth_scale_exact t ht
  have hpow9 : 9 ≤ 3 ^ (2 * t) := by
    have h2 : 3 ^ 2 = 9 := by norm_num
    have hle : 3 ^ 2 ≤ 3 ^ (2 * t) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk8 : 8 * k + 13 ≤ 5 * 3 ^ (2 * t) := by omega
  have hcontra : 3 ^ (2 * t) ≤ 0 := by omega
  exact absurd hcontra (Nat.not_le.mpr (by positivity))

/-- Inside the inclusive positive even selected-depth range, the third BBP
linear denominator carries at most `2 * t - 1` factors of three.  The strict
bound follows from the selected-depth size formula and the residue of an even
power of three modulo eight. -/
theorem poleThree_denominator_val_le_sharp (t k : ℕ) (ht : 1 ≤ t)
    (hk : k ≤ selectedDepth (2 * t)) :
    padicValNat 3 (8 * k + 5) ≤ 2 * t - 1 := by
  by_contra hcon
  have hv : 2 * t ≤ padicValNat 3 (8 * k + 5) := by omega
  have hdvd : 3 ^ (2 * t) ∣ 8 * k + 5 :=
    (Nat.pow_dvd_iff_le_padicValNat (p := 3) (by norm_num) (by omega)).2
      (by omega)
  obtain ⟨c, hc⟩ := hdvd
  have hsd : selectedDepth (2 * t) = (5 * 3 ^ (2 * t) - 13) / 8 := rfl
  have hq8 : 8 * selectedDepth (2 * t) = 5 * 3 ^ (2 * t) - 13 := by
    rw [hsd]
    exact Nat.mul_div_cancel' (eight_dvd_five_three_pow_sub_thirteen t ht)
  have h9 : 9 ≤ 3 ^ (2 * t) := by
    have h2 : 3 ^ 2 = 9 := by norm_num
    have hle : 3 ^ 2 ≤ 3 ^ (2 * t) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsize : c < 5 := by
    have hprod : c * 3 ^ (2 * t) < 5 * 3 ^ (2 * t) := by
      calc c * 3 ^ (2 * t) = 3 ^ (2 * t) * c := Nat.mul_comm _ _
        _ = 8 * k + 5 := hc.symm
        _ ≤ 5 * 3 ^ (2 * t) - 8 := by omega
        _ < 5 * 3 ^ (2 * t) := by omega
    rw [Nat.mul_comm c (3 ^ (2 * t)), Nat.mul_comm 5 (3 ^ (2 * t))] at hprod
    exact Nat.lt_of_mul_lt_mul_left hprod
  have hpow8 := three_pow_two_t_mod_eight t
  have hkey : c % 8 = 5 := by
    have hstep : c % 8 = (8 * k + 5) % 8 := by
      rw [hc, Nat.mul_mod, hpow8]
      norm_num
    omega
  omega

end Theory.PiDigits.T88SelectedDepthDenominatorValuations

#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.three_pow_two_t_mod_eight
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.eight_dvd_five_three_pow_sub_thirteen
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.three_pow_two_t_mod_four
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.selectedDepth_scale_exact
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.denominator_size_bundle
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.poleTwo_denominator_val_le
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.poleOne_denominator_val_le
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.poleFour_denominator_val_le_sharp
#print axioms Theory.PiDigits.T88SelectedDepthDenominatorValuations.poleThree_denominator_val_le_sharp
