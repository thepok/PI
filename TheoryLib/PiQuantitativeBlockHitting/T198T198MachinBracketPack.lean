import TheoryLib.PiQuantitativeBlockHitting.T63T63HuttonFiveAdicTransient
import TheoryLib.PiQuantitativeBlockHitting.T126T126ZeroWindowCell

/-!
# T198: Machin 3/7 bracket pack

Produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-03 against the contracted signatures in AllMath task pack t198;
gate-checked.
-/

noncomputable section

namespace Theory.PiDigits.T198MachinBracketPack

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.HuttonRationalShadow

/-- Value of the odd-index arctangent Taylor term driving the 3/7 width. -/
lemma arctanTermRat_odd_succ (q m : ℕ) :
    arctanTermRat q (2 * m + 1) =
      -(((q : ℚ)⁻¹) ^ (4 * m + 3) / ((4 * m + 3 : ℕ) : ℚ)) := by
  have hexp : 2 * (2 * m + 1) + 1 = 4 * m + 3 := by omega
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  unfold arctanTermRat
  rw [hodd.neg_one_pow, hexp]
  push_cast
  ring

/-- The Document B upper approximant minus the Hutton lower approximant,
stated with single omitted terms. -/
lemma machinUpperRat_sub_lowerRat (m : ℕ) :
    (8 * arctanPartialRat 3 (2 * m + 1) + 4 * arctanPartialRat 7 (2 * m + 1))
      - huttonLowerRat m =
      8 * (-(arctanTermRat 3 (2 * m + 1))) + 4 * (-(arctanTermRat 7 (2 * m + 1))) := by
  have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  unfold huttonLowerRat
  rw [h2]
  simp only [arctanPartialRat_succ]
  ring

/-- Rational form of the exact 3/7 bracket width. -/
lemma machinUpperRat_width_eq (m : ℕ) :
    (8 * arctanPartialRat 3 (2 * m + 1) + 4 * arctanPartialRat 7 (2 * m + 1))
      - huttonLowerRat m =
      8 * ((((3 : ℚ))⁻¹) ^ (4 * m + 3) / ((4 * m + 3 : ℕ) : ℚ)) +
      4 * ((((7 : ℚ))⁻¹) ^ (4 * m + 3) / ((4 * m + 3 : ℕ) : ℚ)) := by
  rw [machinUpperRat_sub_lowerRat, arctanTermRat_odd_succ,
    arctanTermRat_odd_succ]
  ring

/-- Real form of the exact 3/7 bracket width. -/
lemma machinRealWidth_eq (m : ℕ) :
    (((8 * arctanPartialRat 3 (2 * m + 1) + 4 * arctanPartialRat 7 (2 * m + 1) : ℚ)) : ℝ)
      - huttonLower m =
      8 / (((4 * m + 3 : ℕ) : ℝ) * (3 : ℝ) ^ (4 * m + 3)) +
      4 / (((4 * m + 3 : ℕ) : ℝ) * (7 : ℝ) ^ (4 * m + 3)) := by
  have hLr : huttonLower m = ((huttonLowerRat m : ℚ) : ℝ) := rfl
  have hQ := machinUpperRat_width_eq m
  have hcast : ((((8 * arctanPartialRat 3 (2 * m + 1)
      + 4 * arctanPartialRat 7 (2 * m + 1) : ℚ)) : ℝ)
      - huttonLower m)
      = 8 * (((((3 : ℚ))⁻¹) ^ (4 * m + 3) / ((4 * m + 3 : ℕ) : ℚ) : ℚ) : ℝ)
      + 4 * (((((7 : ℚ))⁻¹) ^ (4 * m + 3) / ((4 * m + 3 : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [hLr, ← Rat.cast_sub, hQ]
    push_cast
    ring
  rw [hcast]
  push_cast
  simp only [div_eq_mul_inv, inv_pow, mul_inv_rev]

/-- The lower index sequence tends to infinity. -/
lemma tendsto_lower_index :
    Filter.Tendsto (fun m : ℕ => 2 * (m + 1)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun a ha => by omega⟩

/-- The upper index sequence tends to infinity. -/
lemma tendsto_upper_index :
    Filter.Tendsto (fun m : ℕ => 2 * m + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun a ha => by omega⟩

/-- One-step floor expansion of a pi decimal digit. -/
lemma singleDigitFloor (t : ℕ) :
    ⌊Real.pi * (10 : ℝ) ^ (t + 1)⌋₊ =
      10 * ⌊Real.pi * (10 : ℝ) ^ t⌋₊ + (Theory.PiDigits.piDigit t).val := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hBle : ((⌊Real.pi * (10 : ℝ) ^ t⌋₊ : ℕ) : ℝ) ≤ Real.pi * (10 : ℝ) ^ t :=
    Nat.floor_le (mul_nonneg hpi (by positivity))
  have hle : 10 * ⌊Real.pi * (10 : ℝ) ^ t⌋₊ ≤ ⌊Real.pi * (10 : ℝ) ^ (t + 1)⌋₊ := by
    apply Nat.le_floor
    calc ((((10 * ⌊Real.pi * (10 : ℝ) ^ t⌋₊ : ℕ))) : ℝ)
        = 10 * ((((⌊Real.pi * (10 : ℝ) ^ t⌋₊ : ℕ))) : ℝ) := by push_cast; ring
      _ ≤ 10 * (Real.pi * (10 : ℝ) ^ t) :=
        mul_le_mul_of_nonneg_left hBle (by norm_num)
      _ = Real.pi * (10 : ℝ) ^ (t + 1) := by ring
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  have hAge : ((⌊Real.pi * (10 : ℝ) ^ (t + 1)⌋₊ : ℕ) : ℝ)
      ≤ Real.pi * (10 : ℝ) ^ (t + 1) :=
    Nat.floor_le (mul_nonneg hpi (by positivity))
  have hBlt : Real.pi * (10 : ℝ) ^ t < ((((⌊Real.pi * (10 : ℝ) ^ t⌋₊ : ℕ))) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hcast : ((⌊Real.pi * (10 : ℝ) ^ (t + 1)⌋₊ : ℕ) : ℝ)
      = 10 * ((((⌊Real.pi * (10 : ℝ) ^ t⌋₊ : ℕ))) : ℝ) + (r : ℝ) := by
    rw [hr]; push_cast; ring
  have hr10 : r < 10 := by
    have hrr : (r : ℝ) < 10 := by
      have h10 : Real.pi * (10 : ℝ) ^ (t + 1) = 10 * (Real.pi * (10 : ℝ) ^ t) := by
        ring
      linarith
    exact_mod_cast hrr
  have hmod : ⌊Real.pi * (10 : ℝ) ^ (t + 1)⌋₊ % 10 = r := by omega
  have hval : (Theory.PiDigits.piDigit t).val = r := by
    have hrfl : (Theory.PiDigits.piDigit t).val
        = ⌊Real.pi * (10 : ℝ) ^ (t + 1)⌋₊ % 10 := rfl
    rw [hrfl, hmod]
  rw [hval]
  exact hr

/-- A zero block is exactly a scaled-floor fixed point. -/
lemma zeroBlock_iff_floorEq (n : ℕ) : ∀ (ell : ℕ),
    (∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0) ↔
    ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ = 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ := by
  intro ell
  induction ell with
  | zero =>
    constructor
    · intro _
      simp
    · intro _ i
      exact Fin.elim0 i
  | succ ell ih =>
    have hstep := singleDigitFloor (n + ell)
    have hexp1 : n + (ell + 1) = (n + ell) + 1 := by omega
    have hpow : (10 : ℕ) ^ (ell + 1) = 10 ^ ell * 10 := pow_succ 10 ell
    constructor
    · intro h
      have hrest : ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0 :=
        fun i => h i.castSucc
      have hlast : Theory.PiDigits.piDigit (n + ell) = 0 := h (Fin.last ell)
      have hIH := ih.mp hrest
      have hval0 : (Theory.PiDigits.piDigit (n + ell)).val = 0 := by
        rw [hlast]; rfl
      rw [hexp1, hpow, hstep, hval0, hIH]
      ring
    · intro h
      rw [hexp1, hpow] at h
      rw [hstep] at h
      have hmono : 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊
          ≤ ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ := by
        apply Nat.le_floor
        have hBle : ((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ) : ℝ)
            ≤ Real.pi * (10 : ℝ) ^ n :=
          Nat.floor_le (mul_nonneg Real.pi_pos.le (by positivity))
        have hmul := mul_le_mul_of_nonneg_left hBle
          (show (0 : ℝ) ≤ (10 : ℝ) ^ ell by positivity)
        have hsplit : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ ell * (10 : ℝ) ^ n := by
          ring
        calc (((((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)))) : ℝ)
            = (10 : ℝ) ^ ell * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) := by
              push_cast; ring
          _ ≤ (10 : ℝ) ^ ell * (Real.pi * (10 : ℝ) ^ n) := hmul
          _ = Real.pi * (10 : ℝ) ^ (n + ell) := by rw [hsplit]; ring
      have h10 : 10 * (10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊)
          ≤ 10 * ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ :=
        mul_le_mul_right hmono 10
      have hnorm : ((10 ^ ell * 10) * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)
          = 10 * (10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊) := by ring
      rw [hnorm] at h
      have hFeq : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊
          = 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ := by
        have h' : 10 * ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊
            + (Theory.PiDigits.piDigit (n + ell)).val
            = 10 * (10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊) := h
        omega
      have hval0 : (Theory.PiDigits.piDigit (n + ell)).val = 0 := by omega
      have hlast : Theory.PiDigits.piDigit (n + ell) = 0 := by
        apply Fin.ext
        simpa using hval0
      have hrest := ih.mpr hFeq
      rw [Fin.forall_fin_succ']
      exact ⟨fun i => hrest i, hlast⟩

/-- A decimal cylinder is exactly a scaled-floor fixed point. -/
lemma cylinder_iff_floorEq (n ell : ℕ) :
    (∃ k : ℤ, (k : ℝ) / (10 : ℝ) ^ n ≤ Real.pi ∧
      Real.pi < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell)) ↔
    ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ = 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ := by
  have h10n : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have h10e : (0 : ℝ) < (10 : ℝ) ^ ell := by positivity
  have h10ne : (0 : ℝ) < (10 : ℝ) ^ (n + ell) := by positivity
  have hsplit : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ n * (10 : ℝ) ^ ell := by ring
  have hpi0 : (0 : ℝ) ≤ Real.pi * (10 : ℝ) ^ n :=
    mul_nonneg Real.pi_pos.le h10n.le
  have h10ne' : (0 : ℝ) < (10 : ℝ) ^ n * (10 : ℝ) ^ ell := mul_pos h10n h10e
  constructor
  · rintro ⟨k, hk1, hk2⟩
    have hk1' : (k : ℝ) ≤ Real.pi * (10 : ℝ) ^ n := by
      rwa [div_le_iff₀ h10n] at hk1
    have hfrac : (10 : ℝ) ^ n / (10 : ℝ) ^ (n + ell) ≤ 1 := by
      rw [div_le_one h10ne]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have heq1 : ((k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell)) * (10 : ℝ) ^ n
        = (k : ℝ) + (10 : ℝ) ^ n / (10 : ℝ) ^ (n + ell) := by
      rw [add_mul, div_mul_cancel₀ _ h10n.ne', div_mul_eq_mul_div, one_mul]
    have hk2' : Real.pi * (10 : ℝ) ^ n < (k : ℝ) + 1 := by
      have hmul := mul_lt_mul_of_pos_right hk2 h10n
      rw [heq1] at hmul
      linarith [hfrac]
    have t1 : (k : ℝ) / (10 : ℝ) ^ n * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
        = (k : ℝ) * (10 : ℝ) ^ ell := by
      have e : (k : ℝ) / (10 : ℝ) ^ n * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
          = (((k : ℝ) / (10 : ℝ) ^ n * (10 : ℝ) ^ n)) * (10 : ℝ) ^ ell := by ring
      rw [e, div_mul_cancel₀ _ h10n.ne']
    have t2 : (1 : ℝ) / ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
        * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell) = 1 :=
      div_mul_cancel₀ _ h10ne'.ne'
    have e2 : Real.pi * (10 : ℝ) ^ (n + ell) < (k : ℝ) * (10 : ℝ) ^ ell + 1 := by
      have h2 := hk2
      rw [hsplit] at h2
      have hmul := mul_lt_mul_of_pos_right h2 h10ne'
      have heq2 : ((k : ℝ) / (10 : ℝ) ^ n + 1 / ((10 : ℝ) ^ n * (10 : ℝ) ^ ell))
          * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
          = (k : ℝ) * (10 : ℝ) ^ ell + 1 := by
        rw [add_mul, t1, t2]
      rw [heq2] at hmul
      rw [hsplit]
      exact hmul
    have e1 : (k : ℝ) * (10 : ℝ) ^ ell ≤ Real.pi * (10 : ℝ) ^ (n + ell) := by
      have hmul := mul_le_mul_of_nonneg_right hk1' h10e.le
      rw [hsplit]
      calc (k : ℝ) * (10 : ℝ) ^ ell
          ≤ (Real.pi * (10 : ℝ) ^ n) * (10 : ℝ) ^ ell := hmul
        _ = Real.pi * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell) := by ring
    have hI1 : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋ = k * (10 ^ ell : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast e1
      · exact_mod_cast e2
    have hk0 : 0 ≤ k := by
      have hkle : k ≤ -1 ∨ 0 ≤ k := by omega
      rcases hkle with hneg | hpos
      · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hneg
        linarith [hpi0, hk2']
      · exact hpos
    have hI0 : ⌊Real.pi * (10 : ℝ) ^ n⌋ = k := by
      rw [Int.floor_eq_iff]
      exact ⟨hk1', by linarith [hk2', hfrac]⟩
    have hnn1 : 0 ≤ ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg Real.pi_pos.le h10ne.le)
    have hnn0 : 0 ≤ ⌊Real.pi * (10 : ℝ) ^ n⌋ := Int.floor_nonneg.mpr hpi0
    have g1 : ((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ) : ℤ) = k * (10 ^ ell : ℤ) := by
      have e : ((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ) : ℤ)
          = ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋ := by
        rw [← Int.floor_toNat]
        exact Int.toNat_of_nonneg hnn1
      rw [e, hI1]
    have g0 : ((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ) : ℤ) = k := by
      have e : ((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ) : ℤ) = ⌊Real.pi * (10 : ℝ) ^ n⌋ := by
        rw [← Int.floor_toNat]
        exact Int.toNat_of_nonneg hnn0
      rw [e, hI0]
    have hcast : ((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ) : ℤ)
        = (10 ^ ell : ℤ) * k := by
      push_cast
      rw [g0]
    have g : ((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ) : ℤ)
        = ((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ) : ℤ) := by
      rw [g1, hcast]
      ring
    exact_mod_cast g
  · intro hF
    have hnn0 : 0 ≤ ⌊Real.pi * (10 : ℝ) ^ n⌋ := Int.floor_nonneg.mpr hpi0
    have hI1 : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋
        = (10 ^ ell : ℤ) * ⌊Real.pi * (10 : ℝ) ^ n⌋ := by
      have e : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋
          = ((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ) : ℤ) := by
        rw [← Int.floor_toNat]
        exact (Int.toNat_of_nonneg (Int.floor_nonneg.mpr
          (mul_nonneg Real.pi_pos.le h10ne.le))).symm
      have e0 : (⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ)
          = ((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ) : ℤ) := by
        rw [← Int.floor_toNat]
        exact (Int.toNat_of_nonneg hnn0).symm
      rw [e, hF]
      push_cast
      rw [e0]
    refine ⟨⌊Real.pi * (10 : ℝ) ^ n⌋, ?_, ?_⟩
    · rw [div_le_iff₀ h10n]
      exact Int.floor_le _
    · have e2 : Real.pi * (10 : ℝ) ^ (n + ell)
          < ((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) * (10 : ℝ) ^ ell + 1 := by
        have h := Int.lt_floor_add_one (Real.pi * (10 : ℝ) ^ (n + ell))
        rw [hI1] at h
        push_cast at h
        linarith
      have heq : ((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n
          + 1 / (10 : ℝ) ^ (n + ell)
          = ((((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) * (10 : ℝ) ^ ell + 1))
            / (10 : ℝ) ^ (n + ell) := by
        rw [hsplit]
        have t1 : ((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n
            * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
            = ((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) * (10 : ℝ) ^ ell := by
          have e' : ((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n
              * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
              = ((((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n
                * (10 : ℝ) ^ n)) * (10 : ℝ) ^ ell := by ring
          rw [e', div_mul_cancel₀ _ h10n.ne']
        rw [eq_div_iff h10ne'.ne']
        have t2 : (1 : ℝ) / ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
            * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell) = 1 :=
          div_mul_cancel₀ _ h10ne'.ne'
        have hadd : (((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n
            + 1 / ((10 : ℝ) ^ n * (10 : ℝ) ^ ell))
            * ((10 : ℝ) ^ n * (10 : ℝ) ^ ell)
            = ((⌊Real.pi * (10 : ℝ) ^ n⌋ : ℤ) : ℝ) * (10 : ℝ) ^ ell + 1 := by
          rw [add_mul, t1, t2]
        exact hadd
      rw [heq, lt_div_iff₀ h10ne]
      exact e2

theorem machin37_strict_bracket_and_width :
    ∀ m : ℕ, Theory.PiDigits.HuttonRationalShadow.huttonLower m < Real.pi ∧ Real.pi < (((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1) + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)) ∧ (((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1) + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)) - Theory.PiDigits.HuttonRationalShadow.huttonLower m = 8 / (((4 * m + 3 : ℕ) : ℝ) * (3 : ℝ) ^ (4 * m + 3)) + 4 / (((4 * m + 3 : ℕ) : ℝ) * (7 : ℝ) ^ (4 * m + 3)) := by
  intro m
  have hLr : huttonLower m = ((huttonLowerRat m : ℚ) : ℝ) := rfl
  have hUr : (((8 * arctanPartialRat 3 (2 * m + 1)
      + 4 * arctanPartialRat 7 (2 * m + 1) : ℚ)) : ℝ)
      = 8 * arctanPartial 3 (2 * m + 1) + 4 * arctanPartial 7 (2 * m + 1) := by
    unfold arctanPartial
    push_cast
    ring
  have hle : huttonLower m ≤ Real.pi := huttonLower_le_pi m
  have hpiU : Real.pi ≤ (((8 * arctanPartialRat 3 (2 * m + 1)
      + 4 * arctanPartialRat 7 (2 * m + 1) : ℚ)) : ℝ) := by
    rw [hUr, pi_eq_hutton]
    have h3 := arctan_le_arctanPartial_odd 3 m (by norm_num)
    have h7 := arctan_le_arctanPartial_odd 7 m (by norm_num)
    linarith
  have hneU : Real.pi ≠ (((8 * arctanPartialRat 3 (2 * m + 1)
      + 4 * arctanPartialRat 7 (2 * m + 1) : ℚ)) : ℝ) :=
    irrational_pi.ne_rat _
  refine ⟨lt_of_le_of_ne hle ?_, lt_of_le_of_ne hpiU hneU, machinRealWidth_eq m⟩
  exact fun h => irrational_pi.ne_rat _ (hLr.trans h).symm

theorem tendsto_machin37_endpoints :
    Filter.Tendsto Theory.PiDigits.HuttonRationalShadow.huttonLower Filter.atTop (nhds Real.pi) ∧ Filter.Tendsto (fun m : ℕ => ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1) + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)) Filter.atTop (nhds Real.pi) := by
  have hL3 := (tendsto_arctanPartial 3 (by norm_num)).comp tendsto_lower_index
  have hL7 := (tendsto_arctanPartial 7 (by norm_num)).comp tendsto_lower_index
  have hU3 := (tendsto_arctanPartial 3 (by norm_num)).comp tendsto_upper_index
  have hU7 := (tendsto_arctanPartial 7 (by norm_num)).comp tendsto_upper_index
  have hlim : (8 : ℝ) * Real.arctan (3 : ℝ)⁻¹ + 4 * Real.arctan (7 : ℝ)⁻¹
      = Real.pi :=
    pi_eq_hutton.symm
  have hL : Filter.Tendsto
      (fun m : ℕ => 8 * arctanPartial 3 (2 * (m + 1))
        + 4 * arctanPartial 7 (2 * (m + 1)))
      Filter.atTop
      (nhds (8 * Real.arctan (3 : ℝ)⁻¹ + 4 * Real.arctan (7 : ℝ)⁻¹)) :=
    ((tendsto_const_nhds (x := (8 : ℝ))).mul hL3).add
      ((tendsto_const_nhds (x := (4 : ℝ))).mul hL7)
  have hU : Filter.Tendsto
      (fun m : ℕ => 8 * arctanPartial 3 (2 * m + 1)
        + 4 * arctanPartial 7 (2 * m + 1))
      Filter.atTop
      (nhds (8 * Real.arctan (3 : ℝ)⁻¹ + 4 * Real.arctan (7 : ℝ)⁻¹)) :=
    ((tendsto_const_nhds (x := (8 : ℝ))).mul hU3).add
      ((tendsto_const_nhds (x := (4 : ℝ))).mul hU7)
  have hL' : Filter.Tendsto
      (fun m : ℕ => 8 * arctanPartial 3 (2 * (m + 1))
        + 4 * arctanPartial 7 (2 * (m + 1)))
      Filter.atTop (nhds Real.pi) := by
    rw [← hlim]
    exact hL
  have hU' : Filter.Tendsto
      (fun m : ℕ => 8 * arctanPartial 3 (2 * m + 1)
        + 4 * arctanPartial 7 (2 * m + 1))
      Filter.atTop (nhds Real.pi) := by
    rw [← hlim]
    exact hU
  have hLfinal : Filter.Tendsto Theory.PiDigits.HuttonRationalShadow.huttonLower
      Filter.atTop (nhds Real.pi) :=
    hL'.congr (fun m => (huttonLower_eq m).symm)
  have hUpt : ∀ m : ℕ, 8 * arctanPartial 3 (2 * m + 1)
      + 4 * arctanPartial 7 (2 * m + 1)
      = (((8 * arctanPartialRat 3 (2 * m + 1)
        + 4 * arctanPartialRat 7 (2 * m + 1) : ℚ)) : ℝ) := by
    intro m
    unfold arctanPartial
    push_cast
    ring
  have hUfinal : Filter.Tendsto
      (fun m : ℕ => ((8 * arctanPartialRat 3 (2 * m + 1)
        + 4 * arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ))
      Filter.atTop (nhds Real.pi) :=
    hU'.congr hUpt
  exact ⟨hLfinal, hUfinal⟩

theorem piZeroBlock_iff_decimalCylinder :
    ∀ (n ell : ℕ), 1 ≤ ell → ((∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0) ↔ ∃ k : ℤ, (k : ℝ) / (10 : ℝ) ^ n ≤ Real.pi ∧ Real.pi < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell)) := by
  intro n ell _
  rw [zeroBlock_iff_floorEq n ell]
  exact (cylinder_iff_floorEq n ell).symm

theorem machinMC0_iff_piZeroCylinder :
    (let U : ℕ → ℝ := fun m => ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1) + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ); (∀ ell : ℕ, 1 ≤ ell → ∃ m n : ℕ, ∃ k : ℤ, (k : ℝ) / (10 : ℝ) ^ n ≤ Theory.PiDigits.HuttonRationalShadow.huttonLower m ∧ Theory.PiDigits.HuttonRationalShadow.huttonLower m < U m ∧ U m < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell)) ↔ (∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∃ k : ℤ, (k : ℝ) / (10 : ℝ) ^ n ≤ Real.pi ∧ Real.pi < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell))) := by
  show (∀ ell : ℕ, 1 ≤ ell → ∃ m n : ℕ, ∃ k : ℤ,
      (k : ℝ) / (10 : ℝ) ^ n ≤ Theory.PiDigits.HuttonRationalShadow.huttonLower m ∧
      Theory.PiDigits.HuttonRationalShadow.huttonLower m
        < ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1)
          + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ) ∧
      ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1)
        + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)
        < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell))
    ↔ (∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∃ k : ℤ,
      (k : ℝ) / (10 : ℝ) ^ n ≤ Real.pi ∧
      Real.pi < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell))
  constructor
  · intro h ell hle
    obtain ⟨m, n, k, hk1, -, hk3⟩ := h ell hle
    have hb := machin37_strict_bracket_and_width m
    exact ⟨n, k, le_trans hk1 hb.1.le, lt_trans hb.2.1 hk3⟩
  · intro h ell hle
    obtain ⟨n, k, hk1, hk2⟩ := h ell hle
    have h10n : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
    have hlt : (k : ℝ) / (10 : ℝ) ^ n < Real.pi := by
      have hne : (k : ℝ) / (10 : ℝ) ^ n ≠ Real.pi := by
        intro heq
        have hcast : ((((10 ^ n : ℕ) : ℤ)) : ℝ) = (10 : ℝ) ^ n := by
          push_cast; ring
        have hrw : Real.pi = (k : ℝ) / ((((10 ^ n : ℕ) : ℤ)) : ℝ) := by
          rw [← heq, hcast]
        exact irrational_pi.ne_rational k ((10 ^ n : ℕ) : ℤ) hrw
      exact lt_of_le_of_ne hk1 hne
    have hTL := tendsto_machin37_endpoints.1
    have hTU := tendsto_machin37_endpoints.2
    have eL : ∀ᶠ m : ℕ in Filter.atTop,
        (k : ℝ) / (10 : ℝ) ^ n < Theory.PiDigits.HuttonRationalShadow.huttonLower m :=
      hTL.eventually (Ioi_mem_nhds hlt)
    have eU : ∀ᶠ m : ℕ in Filter.atTop,
        ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1)
          + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)
        < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell) :=
      hTU.eventually (Iio_mem_nhds hk2)
    obtain ⟨m, hLm, hUm⟩ := (eL.and eU).exists
    have hb := machin37_strict_bracket_and_width m
    exact ⟨m, n, k, hLm.le, hb.1.trans hb.2.1, hUm⟩

theorem machinMC0_iff_piCW0 :
    (let U : ℕ → ℝ := fun m => ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1) + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ); (∀ ell : ℕ, 1 ≤ ell → ∃ m n : ℕ, ∃ k : ℤ, (k : ℝ) / (10 : ℝ) ^ n ≤ Theory.PiDigits.HuttonRationalShadow.huttonLower m ∧ Theory.PiDigits.HuttonRationalShadow.huttonLower m < U m ∧ U m < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell)) ↔ (∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0)) := by
  show (∀ ell : ℕ, 1 ≤ ell → ∃ m n : ℕ, ∃ k : ℤ,
      (k : ℝ) / (10 : ℝ) ^ n ≤ Theory.PiDigits.HuttonRationalShadow.huttonLower m ∧
      Theory.PiDigits.HuttonRationalShadow.huttonLower m
        < ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1)
          + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ) ∧
      ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1)
        + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)
        < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell))
    ↔ (∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ,
      ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0)
  have h4' : (∀ ell : ℕ, 1 ≤ ell → ∃ m n : ℕ, ∃ k : ℤ,
      (k : ℝ) / (10 : ℝ) ^ n ≤ Theory.PiDigits.HuttonRationalShadow.huttonLower m ∧
      Theory.PiDigits.HuttonRationalShadow.huttonLower m
        < ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1)
          + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ) ∧
      ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1)
        + 4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)
        < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell))
      ↔ (∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∃ k : ℤ,
        (k : ℝ) / (10 : ℝ) ^ n ≤ Real.pi ∧
        Real.pi < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell)) :=
    machinMC0_iff_piZeroCylinder
  constructor
  · intro h ell hle
    obtain ⟨n, k, hk1, hk2⟩ := (h4'.mp h) ell hle
    exact ⟨n, (piZeroBlock_iff_decimalCylinder n ell hle).mpr ⟨k, hk1, hk2⟩⟩
  · intro h
    have hpi : ∀ ell' : ℕ, 1 ≤ ell' → ∃ n : ℕ, ∃ k : ℤ,
        (k : ℝ) / (10 : ℝ) ^ n ≤ Real.pi ∧
        Real.pi < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell') := by
      intro ell' hle'
      obtain ⟨n, hn⟩ := h ell' hle'
      obtain ⟨k, hk1, hk2⟩ :=
        (piZeroBlock_iff_decimalCylinder n ell' hle').mp hn
      exact ⟨n, k, hk1, hk2⟩
    exact h4'.mpr hpi

end Theory.PiDigits.T198MachinBracketPack
