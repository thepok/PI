import TheoryLib.PiQuantitativeBlockHitting.T164T164QuadraticBBPTailTransfer
import TheoryLib.PiQuantitativeBlockHitting.T198T198MachinBracketPack

/-!
# T199: Base-10 BBP shadow pack

Produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-03 against the contracted signatures of AllMath task pack t199,
gate-checked; 2900 s wall.
-/

noncomputable section

namespace Theory.PiDigits.T199BBPShadowPack

open Theory.PiDigits.T100BBPRealBridge
open Theory.PiDigits.T104BBPSeriesIdentity
open Theory.PiDigits.T164QuadraticBBPTailTransfer

private lemma cPosAux (n : ℕ) (hn : 2 ≤ n) : (0 : ℝ) < (10 : ℝ) ^ n - 16 := by
  have h100 : (100 : ℝ) ≤ (10 : ℝ) ^ n := by
    have h : (10 : ℝ) ^ 2 ≤ (10 : ℝ) ^ n :=
      pow_le_pow_right₀ (by norm_num) hn
    norm_num at h
    linarith
  linarith

private lemma fiveEighth_pos (n : ℕ) : (0 : ℝ) < ((5 : ℝ) / 8) ^ n := by positivity

private lemma fiveEighth_eq (n : ℕ) : ((5 : ℝ) / 8) ^ n = (10 : ℝ) ^ n / (16 : ℝ) ^ n := by
  have h : (10 : ℝ) / 16 = 5 / 8 := by norm_num
  rw [← h, div_pow]

private lemma scale_ge_306 (n : ℕ) (hn : 2 ≤ n) : (306 : ℝ) ≤ bbpTailScale (n - 1) := by
  unfold bbpTailScale
  have h1 : (17 : ℝ) ≤ (((8 * (n - 1) + 9 : ℕ)) : ℝ) := by
    have hh : 17 ≤ 8 * (n - 1) + 9 := by omega
    exact_mod_cast hh
  have h2 : (18 : ℝ) ≤ (((8 * (n - 1) + 10 : ℕ)) : ℝ) := by
    have hh : 18 ≤ 8 * (n - 1) + 10 := by omega
    exact_mod_cast hh
  have gA : (0 : ℝ) ≤ (((8 * (n - 1) + 9 : ℕ)) : ℝ) := by positivity
  have e : (17 : ℝ) * 18 ≤
      (((8 * (n - 1) + 9 : ℕ)) : ℝ) * (((8 * (n - 1) + 10 : ℕ)) : ℝ) :=
    mul_le_mul h1 h2 (by norm_num) gA
  have h306 : (306 : ℝ) = 17 * 18 := by norm_num
  rw [h306]
  exact e

theorem bbp10_defect_bounds_and_exact_shadow :
    ∀ n : ℕ, 2 ≤ n → (let B : ℝ := Theory.PiDigits.T100BBPRealBridge.bbpRealPartial (n - 1); let E : ℝ := ((10 : ℝ) ^ n - 16) * (Real.pi - B); let head : ℝ := Int.fract (((10 : ℝ) ^ n - 16) * B); let a : ℝ := 51 - 16 * Real.pi; 0 < E ∧ E < ((5 : ℝ) / 8) ^ n ∧ Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) = Int.fract (head + E) ∧ (10 : ℝ) ^ n * Real.pi = (⌊((10 : ℝ) ^ n - 16) * B⌋ : ℝ) + 51 + (head + E - a) ∧ |‖((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle)‖ - ‖((((10 : ℝ) ^ n - 16) * B : ℝ) : UnitAddCircle)‖| < ((5 : ℝ) / 8) ^ n) := by
  intro n hn
  show 0 < ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) ∧
    ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < ((5 : ℝ) / 8) ^ n ∧
    Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
      Int.fract (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) ∧
    (10 : ℝ) ^ n * Real.pi = (⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℝ) + 51 +
      (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - (51 - 16 * Real.pi)) ∧
    |‖((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle)‖ -
      ‖((((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) : ℝ) : UnitAddCircle)‖| < ((5 : ℝ) / 8) ^ n
  have hc_pos : (0 : ℝ) < (10 : ℝ) ^ n - 16 := cPosAux n hn
  have htail := real_bbp_tail_quadratic_bounds (n - 1)
  have hpiB_pos : 0 < Real.pi - bbpRealPartial (n - 1) := by
    have hpos : (0 : ℝ) < 1 / (4 * bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := by
      unfold bbpTailScale
      positivity
    linarith [htail.1]
  have hE_pos : (0 : ℝ) < ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) :=
    mul_pos hc_pos hpiB_pos
  have hscale_ge : (306 : ℝ) ≤ bbpTailScale (n - 1) := scale_ge_306 n hn
  have hscale_pos : (0 : ℝ) < bbpTailScale (n - 1) := by linarith
  have h16m1 : (0 : ℝ) < (16 : ℝ) ^ (n - 1) := by positivity
  have hupper : Real.pi - bbpRealPartial (n - 1) <
      1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := htail.2
  have hup_pos : (0 : ℝ) < 1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := by positivity
  have hE_lt_aux : ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) <
      ((10 : ℝ) ^ n - 16) * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) :=
    mul_lt_mul_of_pos_left hupper hc_pos
  have hc_lt10 : ((10 : ℝ) ^ n - 16) < (10 : ℝ) ^ n := by
    have h10 : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
    linarith
  have h10scale : ((10 : ℝ) ^ n - 16) * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) <
      (10 : ℝ) ^ n * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) :=
    mul_lt_mul_of_pos_right hc_lt10 hup_pos
  have hn_eq : n - 1 + 1 = n := by omega
  have h16n : (16 : ℝ) ^ n = (16 : ℝ) ^ (n - 1) * 16 := by
    conv_lhs => rw [← hn_eq, pow_succ]
  have h10n_eq : (10 : ℝ) ^ n * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) =
      (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) := by
    rw [fiveEighth_eq, h16n]
    field_simp
  have h16scale : (16 : ℝ) / bbpTailScale (n - 1) ≤ 1 := by
    rw [div_le_one hscale_pos]
    linarith
  have h58nn : (0 : ℝ) ≤ ((5 : ℝ) / 8) ^ n := le_of_lt (fiveEighth_pos n)
  have hle : (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) ≤ ((5 : ℝ) / 8) ^ n := by
    calc (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n)
        ≤ 1 * (((5 : ℝ) / 8) ^ n) := mul_le_mul_of_nonneg_right h16scale h58nn
      _ = ((5 : ℝ) / 8) ^ n := one_mul _
  have hE_lt : ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < ((5 : ℝ) / 8) ^ n := by
    calc ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))
        < ((10 : ℝ) ^ n - 16) * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) := hE_lt_aux
      _ < (10 : ℝ) ^ n * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) := h10scale
      _ = (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) := h10n_eq
      _ ≤ ((5 : ℝ) / 8) ^ n := hle
  have hXeq : ((10 : ℝ) ^ n - 16) * Real.pi =
      ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by ring
  have hfract_id : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
      Int.fract (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) := by
    have hX : ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) =
        ((⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℤ) : ℝ) +
          Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) := by
      have h := Int.floor_add_fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1))
      linarith
    conv_lhs => rw [hXeq, hX]
    have hcomm2 : ((⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℤ) : ℝ) +
        Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) =
        (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) +
        ((⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℤ) : ℝ) := by ring
    rw [hcomm2, Int.fract_add_intCast]
  have hlift : (10 : ℝ) ^ n * Real.pi =
      (⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℝ) + 51 +
        (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - (51 - 16 * Real.pi)) := by
    have h1 : (10 : ℝ) ^ n * Real.pi =
        ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) + 16 * Real.pi := by ring
    have h2 : ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) =
        ((⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℤ) : ℝ) +
          Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) := by
      have h := Int.floor_add_fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1))
      linarith
    linear_combination h1 + h2
  have hcirc : |‖((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle)‖ -
      ‖((((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) : ℝ) : UnitAddCircle)‖| <
      ((5 : ℝ) / 8) ^ n := by
    have hle1 : |‖((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle)‖ -
        ‖((((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) : ℝ) : UnitAddCircle)‖| ≤
        ‖((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle) -
          ((((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) : ℝ) : UnitAddCircle)‖ :=
      abs_norm_sub_norm_le _ _
    have hmap : ((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle) =
        ((((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) : ℝ) : UnitAddCircle) +
          (((((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) : ℝ)) : UnitAddCircle) := by
      conv_lhs => rw [hXeq]
      simp
    have hsub : ((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle) -
        ((((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) : ℝ) : UnitAddCircle) =
        (((((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) : ℝ)) : UnitAddCircle) := by
      rw [hmap]
      simp
    rw [hsub] at hle1
    have hnorm : ‖(((((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) : ℝ)) : UnitAddCircle)‖ ≤
        |((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))| :=
      calc ‖(((((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) : ℝ)) : UnitAddCircle)‖
          ≤ ‖((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))‖ :=
            QuotientAddGroup.norm_mk_le_norm
        _ = |((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))| := Real.norm_eq_abs _
    have habs : |((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))| =
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := abs_of_pos hE_pos
    calc |‖((((10 : ℝ) ^ n - 16) * Real.pi : ℝ) : UnitAddCircle)‖ -
        ‖((((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) : ℝ) : UnitAddCircle)‖|
          ≤ ‖(((((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) : ℝ)) : UnitAddCircle)‖ := hle1
        _ ≤ |((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))| := hnorm
        _ = ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := habs
        _ < ((5 : ℝ) / 8) ^ n := hE_lt
  exact ⟨hE_pos, hE_lt, hfract_id, hlift, hcirc⟩

open Theory.PiDigits.T98BBPArchimedeanTerm

private lemma termPos (k : ℕ) : 0 < bbpRealTerm k := by
  unfold bbpRealTerm
  exact Rat.cast_pos.mpr (bbpCombinedTerm_pos k)

private lemma Rcast_eq (k : ℕ) :
    (16 : ℝ) ^ k * bbpRealTerm k =
      ((((120 * (k : ℚ) ^ 2 + 151 * (k : ℚ) + 47) /
        (((2 * (k : ℚ) + 1) * (4 * (k : ℚ) + 3) * (8 * (k : ℚ) + 1) * (8 * (k : ℚ) + 5))) : ℚ)) : ℝ) := by
  have heq := bbpCombinedTerm_eq k
  unfold bbpRealTerm
  have h16 : (16 : ℝ) ^ k = ((((16 : ℚ) ^ k : ℚ)) : ℝ) := by
    norm_cast
  rw [h16, ← Rat.cast_mul, heq]
  congr 1
  field_simp

private lemma Rmono (n : ℕ) :
    (16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1) < (16 : ℝ) ^ n * bbpRealTerm n := by
  rw [Rcast_eq (n+1), Rcast_eq n]
  apply Rat.cast_lt.mpr
  set q : ℚ := (n : ℚ) with hq
  have hN1 : (120 * (((n+1 : ℕ) : ℚ)) ^ 2 + 151 * (((n+1 : ℕ) : ℚ)) + 47) =
      120 * (q+1) ^ 2 + 151 * (q+1) + 47 := by
    simp [hq, Nat.cast_add, Nat.cast_one]
  have hD1 : ((2 * (((n+1 : ℕ) : ℚ)) + 1) * (4 * (((n+1 : ℕ) : ℚ)) + 3) *
      (8 * (((n+1 : ℕ) : ℚ)) + 1) * (8 * (((n+1 : ℕ) : ℚ)) + 5)) =
      (2 * (q+1) + 1) * (4 * (q+1) + 3) * (8 * (q+1) + 1) * (8 * (q+1) + 5) := by
    simp [hq, Nat.cast_add, Nat.cast_one]
  rw [hN1, hD1]
  have hDpos0 : (0 : ℚ) < (2 * q + 1) * (4 * q + 3) * (8 * q + 1) * (8 * q + 5) := by positivity
  have hDpos1 : (0 : ℚ) < (2 * (q+1) + 1) * (4 * (q+1) + 3) * (8 * (q+1) + 1) * (8 * (q+1) + 5) := by positivity
  rw [div_lt_div_iff₀ hDpos1 hDpos0]
  have hpoly : (120 * (q+1) ^ 2 + 151 * (q+1) + 47) * ((2 * q + 1) * (4 * q + 3) * (8 * q + 1) * (8 * q + 5)) -
      (120 * q ^ 2 + 151 * q + 47) * ((2 * (q+1) + 1) * (4 * (q+1) + 3) * (8 * (q+1) + 1) * (8 * (q+1) + 5)) =
      -(122880 * q ^ 5 + 662016 * q ^ 4 + 1360896 * q ^ 3 + 1330440 * q ^ 2 + 620136 * q + 110709) := by ring
  have hsum : (0 : ℚ) < 122880 * q ^ 5 + 662016 * q ^ 4 + 1360896 * q ^ 3 + 1330440 * q ^ 2 + 620136 * q + 110709 := by positivity
  linarith

private lemma BsuccAux (n : ℕ) (hn : 1 ≤ n) :
    bbpRealPartial n = bbpRealPartial (n - 1) + bbpRealTerm n := by
  have heq : n - 1 + 1 = n := by omega
  conv_lhs => rw [← heq]
  rw [bbpRealPartial_succ, heq]

theorem bbp10_theta_formula_strictAnti_tendsto :
    (let B : ℕ → ℝ := fun n ↦ Theory.PiDigits.T100BBPRealBridge.bbpRealPartial (n - 1); let E : ℕ → ℝ := fun n ↦ ((10 : ℝ) ^ n - 16) * (Real.pi - B n); let Θ : ℕ → ℝ := fun n ↦ ((10 : ℝ) ^ (n + 1) - 16) * B (n + 1) - 10 * ((10 : ℝ) ^ n - 16) * B n; (∀ n : ℕ, 2 ≤ n → Θ n = 144 * B n + ((10 : ℝ) ^ (n + 1) - 16) * Theory.PiDigits.T100BBPRealBridge.bbpRealTerm n) ∧ (∀ n : ℕ, 2 ≤ n → Θ (n + 1) < Θ n) ∧ Filter.Tendsto Θ Filter.atTop (nhds (144 * Real.pi)) ∧ ∀ n : ℕ, 2 ≤ n → Θ n - 144 * Real.pi = 10 * E n - E (n + 1)) := by
  show (∀ n : ℕ, 2 ≤ n →
      ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) - 10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) =
        144 * bbpRealPartial (n - 1) + ((10 : ℝ) ^ (n + 1) - 16) * bbpRealTerm n) ∧
    (∀ n : ℕ, 2 ≤ n →
      ((10 : ℝ) ^ ((n + 1) + 1) - 16) * bbpRealPartial (((n + 1) + 1) - 1) -
        10 * ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) <
      ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) ∧
    Filter.Tendsto (fun n ↦ ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) Filter.atTop (nhds (144 * Real.pi)) ∧
    ∀ n : ℕ, 2 ≤ n →
      (((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) - 144 * Real.pi =
      10 * (((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) -
        ((10 : ℝ) ^ (n + 1) - 16) * (Real.pi - bbpRealPartial (((n + 1)) - 1)))
  -- auxiliary pow relation
  have hpow10 : ∀ n : ℕ, (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := fun n => pow_succ _ _
  -- (d) defect identity holds for all n
  have hdef : ∀ n : ℕ,
      (((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) - 144 * Real.pi =
      10 * (((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) -
        ((10 : ℝ) ^ (n + 1) - 16) * (Real.pi - bbpRealPartial ((n + 1) - 1))) := by
    intro n
    rw [hpow10 n]
    ring
  -- (a) theta formula for n ≥ 1
  have hform : ∀ n : ℕ, 1 ≤ n →
      ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) =
        144 * bbpRealPartial (n - 1) + ((10 : ℝ) ^ (n + 1) - 16) * bbpRealTerm n := by
    intro n hn
    have hB : bbpRealPartial ((n + 1) - 1) = bbpRealPartial (n - 1) + bbpRealTerm n := by
      have h1 : (n + 1) - 1 = n := by omega
      rw [h1]
      exact BsuccAux n hn
    rw [hB, hpow10 n]
    ring
  have hform2 : ∀ n : ℕ, 2 ≤ n →
      ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) - 10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) =
        144 * bbpRealPartial (n - 1) + ((10 : ℝ) ^ (n + 1) - 16) * bbpRealTerm n :=
    fun n hn => hform n (by omega)
  -- E tends to zero via (5/8)^n squeeze
  have hE_tendsto : Filter.Tendsto (fun n : ℕ ↦ ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)))
      Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ ↦ ((5 : ℝ) / 8) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    apply squeeze_zero' _ _ hg
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hc := cPosAux n hn
      have htail := real_bbp_tail_quadratic_bounds (n - 1)
      have hpos : (0 : ℝ) < 1 / (4 * bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := by
        unfold bbpTailScale; positivity
      have hpiB : 0 < Real.pi - bbpRealPartial (n - 1) := by linarith [htail.1]
      exact mul_nonneg hc.le hpiB.le
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hc := cPosAux n hn
      have htail := real_bbp_tail_quadratic_bounds (n - 1)
      have hge := scale_ge_306 n hn
      have hpos : (0 : ℝ) < bbpTailScale (n - 1) := by linarith
      have h16m : (0 : ℝ) < (16 : ℝ) ^ (n - 1) := by positivity
      have hup : Real.pi - bbpRealPartial (n - 1) < 1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := htail.2
      have hupnn : (0 : ℝ) ≤ 1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := le_of_lt (by positivity)
      have hn_eq : n - 1 + 1 = n := by omega
      have h16n : (16 : ℝ) ^ n = (16 : ℝ) ^ (n - 1) * 16 := by
        conv_lhs => rw [← hn_eq, pow_succ]
      have h10eq : (10 : ℝ) ^ n * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) =
          (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) := by
        rw [fiveEighth_eq, h16n]; field_simp
      have h16s : (16 : ℝ) / bbpTailScale (n - 1) ≤ 1 := by
        rw [div_le_one hpos]; linarith
      have hnn : (0 : ℝ) ≤ ((5 : ℝ) / 8) ^ n := le_of_lt (fiveEighth_pos n)
      have hle2 : (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) ≤ ((5 : ℝ) / 8) ^ n := by
        calc (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n)
            ≤ 1 * (((5 : ℝ) / 8) ^ n) := mul_le_mul_of_nonneg_right h16s hnn
          _ = ((5 : ℝ) / 8) ^ n := one_mul _
      calc ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))
          ≤ ((10 : ℝ) ^ n - 16) * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) :=
            mul_le_mul_of_nonneg_left hup.le hc.le
        _ ≤ (10 : ℝ) ^ n * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) := by
            apply mul_le_mul_of_nonneg_right _ hupnn
            have : (0 : ℝ) ≤ (10 : ℝ) ^ n := by positivity
            linarith
        _ = (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) := h10eq
        _ ≤ ((5 : ℝ) / 8) ^ n := hle2
  -- Theta tends to 144 pi via defect identity
  have hTheta_tendsto : Filter.Tendsto (fun n ↦ ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) Filter.atTop (nhds (144 * Real.pi)) := by
    have hsucc : Filter.Tendsto (fun n : ℕ ↦ n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_add_atTop_nat 1
    have hE1 := hE_tendsto.comp hsucc
    have hdiff : Filter.Tendsto (fun n : ℕ ↦ 10 * (((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) -
        ((10 : ℝ) ^ (n + 1) - 16) * (Real.pi - bbpRealPartial (((n + 1)) - 1))) Filter.atTop (nhds 0) := by
      have h10 : Filter.Tendsto (fun n : ℕ ↦ 10 * (((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)))) Filter.atTop (nhds (10 * 0)) :=
        hE_tendsto.const_mul 10
      simp only [mul_zero] at h10
      have hE1' : Filter.Tendsto (fun n : ℕ ↦ ((10 : ℝ) ^ (n + 1) - 16) * (Real.pi - bbpRealPartial (((n + 1)) - 1)))
          Filter.atTop (nhds 0) := hE1
      simpa using h10.sub hE1'
    have heq : ∀ᶠ n in Filter.atTop, 144 * Real.pi + (10 * (((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) -
        ((10 : ℝ) ^ (n + 1) - 16) * (Real.pi - bbpRealPartial (((n + 1)) - 1))) =
        ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hd := hdef n
      linarith
    have hlim : Filter.Tendsto (fun n : ℕ ↦ 144 * Real.pi + (10 * (((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) -
        ((10 : ℝ) ^ (n + 1) - 16) * (Real.pi - bbpRealPartial (((n + 1)) - 1)))) Filter.atTop (nhds (144 * Real.pi + 0)) :=
      Filter.Tendsto.add tendsto_const_nhds hdiff
    simp only [add_zero] at hlim
    exact hlim.congr' heq
  -- strict decrease
  have hdec : ∀ n : ℕ, 2 ≤ n →
      ((10 : ℝ) ^ ((n + 1) + 1) - 16) * bbpRealPartial (((n + 1) + 1) - 1) -
        10 * ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) <
      ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hBn1 : bbpRealPartial ((n + 1) - 1) = bbpRealPartial (n - 1) + bbpRealTerm n := by
      have h1 : (n + 1) - 1 = n := by omega
      rw [h1]; exact BsuccAux n hn1
    have hBn2 : bbpRealPartial (((n + 1) + 1) - 1) = bbpRealPartial ((n + 1) - 1) + bbpRealTerm (n + 1) := by
      have h1 : ((n + 1) + 1) - 1 = (n + 1) := by omega
      rw [h1]
      exact BsuccAux (n + 1) (by omega)
    have hApos : (0 : ℝ) < (10 : ℝ) ^ (n + 1) - 160 := by
      have h1000 : (1000 : ℝ) ≤ (10 : ℝ) ^ (n + 1) := by
        have h : (10 : ℝ) ^ 3 ≤ (10 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        norm_num at h; linarith
      linarith
    have hBpos : (0 : ℝ) < (10 : ℝ) ^ (n + 2) - 16 := by
      have h100 : (100 : ℝ) ≤ (10 : ℝ) ^ (n + 2) := by
        have h : (10 : ℝ) ^ 2 ≤ (10 : ℝ) ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
        norm_num at h; linarith
      linarith
    have hR0 : (0 : ℝ) < (16 : ℝ) ^ n * bbpRealTerm n := mul_pos (by positivity) (termPos n)
    have hR1 : (0 : ℝ) < (16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1) := mul_pos (by positivity) (termPos (n+1))
    have hRlt := Rmono n
    have hcoeff : ((10 : ℝ) ^ (n + 2) - 16) / 16 < (10 : ℝ) ^ (n + 1) - 160 := by
      have h10n : (10 : ℝ) ^ (n + 2) = (10 : ℝ) ^ (n + 1) * 10 := pow_succ _ _
      rw [h10n]
      have h1000 : (1000 : ℝ) ≤ (10 : ℝ) ^ (n + 1) := by
        have h : (10 : ℝ) ^ 3 ≤ (10 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        norm_num at h; linarith
      have hA : (0 : ℝ) < (10 : ℝ) ^ (n + 1) := by positivity
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 16)]
      nlinarith
    have hprod : ((10 : ℝ) ^ (n + 2) - 16) / 16 * ((16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1)) <
        ((10 : ℝ) ^ (n + 1) - 160) * ((16 : ℝ) ^ n * bbpRealTerm n) := by
      have h1 : ((10 : ℝ) ^ (n + 2) - 16) / 16 * ((16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1)) <
          ((10 : ℝ) ^ (n + 1) - 160) * ((16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1)) :=
        mul_lt_mul_of_pos_right hcoeff hR1
      have h2 : ((10 : ℝ) ^ (n + 1) - 160) * ((16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1)) ≤
          ((10 : ℝ) ^ (n + 1) - 160) * ((16 : ℝ) ^ n * bbpRealTerm n) :=
        mul_le_mul_of_nonneg_left hRlt.le hApos.le
      linarith
    have h16n : (0 : ℝ) < (16 : ℝ) ^ n := by positivity
    have hdiff_eq : (((10 : ℝ) ^ ((n + 1) + 1) - 16) * bbpRealPartial (((n + 1) + 1) - 1) -
        10 * ((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1)) -
        (((10 : ℝ) ^ (n + 1) - 16) * bbpRealPartial ((n + 1) - 1) -
        10 * ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) =
        (((10 : ℝ) ^ (n + 2) - 16) / 16 * ((16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1)) -
        ((10 : ℝ) ^ (n + 1) - 160) * ((16 : ℝ) ^ n * bbpRealTerm n)) / (16 : ℝ) ^ n := by
      have e1 : ((n + 1) + 1) = n + 2 := by omega
      have e2 : (16 : ℝ) ^ (n + 1) = (16 : ℝ) ^ n * 16 := by rw [pow_succ]
      have e3 : (10 : ℝ) ^ ((n + 1) + 1) = (10 : ℝ) ^ (n + 2) := by rw [e1]
      have h16ne : (16 : ℝ) ^ n ≠ 0 := ne_of_gt h16n
      rw [eq_div_iff h16ne]
      rw [hBn2, hBn1, e3, e2]
      rw [hpow10 n, hpow10 (n+1)]
      ring
    have hnum_neg : ((10 : ℝ) ^ (n + 2) - 16) / 16 * ((16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1)) -
        ((10 : ℝ) ^ (n + 1) - 160) * ((16 : ℝ) ^ n * bbpRealTerm n) < 0 := by linarith [hprod]
    have hdiv_neg : ((((10 : ℝ) ^ (n + 2) - 16) / 16 * ((16 : ℝ) ^ (n + 1) * bbpRealTerm (n + 1)) -
        ((10 : ℝ) ^ (n + 1) - 160) * ((16 : ℝ) ^ n * bbpRealTerm n)) / (16 : ℝ) ^ n) < 0 :=
      div_neg_of_neg_of_pos hnum_neg h16n
    linarith [hdiff_eq, hdiv_neg]
  exact ⟨hform2, hdec, hTheta_tendsto, fun n hn => hdef n⟩

private lemma pi144_bounds : (452 : ℝ) < 144 * Real.pi ∧ 144 * Real.pi < 453 := by
  have h1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h2 : Real.pi < 3.1416 := Real.pi_lt_d4
  constructor <;> nlinarith

private lemma pi16_bounds : (50 : ℝ) < 16 * Real.pi ∧ 16 * Real.pi < 51 := by
  have h1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h2 : Real.pi < 3.1416 := Real.pi_lt_d4
  constructor <;> nlinarith

theorem bbp10_affine_fixedPoint :
    (let v : ℕ → ℝ := fun n ↦ Int.fract (((10 : ℝ) ^ n - 16) * Real.pi); let c : ℝ := Int.fract (144 * Real.pi); let a : ℝ := 51 - 16 * Real.pi; (∀ n : ℕ, v (n + 1) = Int.fract (10 * v n + c)) ∧ c = 144 * Real.pi - 452 ∧ 0 < a ∧ a < 1 ∧ 10 * a + c = a + 7 ∧ Int.fract (16 * Real.pi) = 1 - a ∧ ∀ n : ℕ, v n = Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + a)) := by
  show (∀ n : ℕ, Int.fract (((10 : ℝ) ^ (n + 1) - 16) * Real.pi) =
      Int.fract (10 * Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) + Int.fract (144 * Real.pi))) ∧
    Int.fract (144 * Real.pi) = 144 * Real.pi - 452 ∧
    0 < 51 - 16 * Real.pi ∧ 51 - 16 * Real.pi < 1 ∧
    10 * (51 - 16 * Real.pi) + Int.fract (144 * Real.pi) = (51 - 16 * Real.pi) + 7 ∧
    Int.fract (16 * Real.pi) = 1 - (51 - 16 * Real.pi) ∧
    ∀ n : ℕ, Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
      Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi))
  have h144 := pi144_bounds
  have h16 := pi16_bounds
  have hfloor144 : ⌊144 * Real.pi⌋ = 452 := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num; linarith [h144.1]
    · norm_num; linarith [h144.2]
  have hc_eq : Int.fract (144 * Real.pi) = 144 * Real.pi - 452 := by
    have h := Int.floor_add_fract (144 * Real.pi)
    rw [hfloor144] at h
    push_cast at h
    linarith
  have ha_pos : (0 : ℝ) < 51 - 16 * Real.pi := by linarith [h16.2]
  have ha_lt1 : (51 : ℝ) - 16 * Real.pi < 1 := by linarith [h16.1]
  have hfix : 10 * (51 - 16 * Real.pi) + (144 * Real.pi - 452) = (51 - 16 * Real.pi) + 7 := by ring
  have hfix' : 10 * (51 - 16 * Real.pi) + Int.fract (144 * Real.pi) = (51 - 16 * Real.pi) + 7 := by
    rw [hc_eq]; exact hfix
  have hfloor16 : ⌊16 * Real.pi⌋ = 50 := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num; linarith [h16.1]
    · norm_num; linarith [h16.2]
  have hf16 : Int.fract (16 * Real.pi) = 1 - (51 - 16 * Real.pi) := by
    have h := Int.floor_add_fract (16 * Real.pi)
    rw [hfloor16] at h
    push_cast at h
    linarith
  have hrec : ∀ n : ℕ, Int.fract (((10 : ℝ) ^ (n + 1) - 16) * Real.pi) =
      Int.fract (10 * Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) + Int.fract (144 * Real.pi)) := by
    intro n
    have hpow : (10 : ℝ) ^ (n + 1) = 10 * (10 : ℝ) ^ n := by rw [pow_succ]; ring
    have hdecomp : ((10 : ℝ) ^ (n + 1) - 16) * Real.pi =
        10 * (((10 : ℝ) ^ n - 16) * Real.pi) + 144 * Real.pi := by
      rw [hpow]; ring
    have hY : (((10 : ℝ) ^ n - 16) * Real.pi) =
        ((⌊(((10 : ℝ) ^ n - 16) * Real.pi)⌋ : ℤ) : ℝ) +
          Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) := by
      have h := Int.floor_add_fract (((10 : ℝ) ^ n - 16) * Real.pi)
      linarith
    have hC : (144 : ℝ) * Real.pi =
        ((⌊(144 : ℝ) * Real.pi⌋ : ℤ) : ℝ) + Int.fract (144 * Real.pi) := by
      have h := Int.floor_add_fract (144 * Real.pi)
      linarith
    conv_lhs => rw [hdecomp, hY, hC]
    have hcomm : 10 * (((⌊(((10 : ℝ) ^ n - 16) * Real.pi)⌋ : ℤ) : ℝ) +
          Int.fract (((10 : ℝ) ^ n - 16) * Real.pi)) +
          (((⌊(144 : ℝ) * Real.pi⌋ : ℤ) : ℝ) + Int.fract (144 * Real.pi)) =
        (10 * Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) + Int.fract (144 * Real.pi)) +
          ((((10 * ⌊(((10 : ℝ) ^ n - 16) * Real.pi)⌋ + ⌊(144 : ℝ) * Real.pi⌋ : ℤ))) : ℝ) := by
      push_cast
      ring
    rw [hcomm, Int.fract_add_intCast]
  have hshadow : ∀ n : ℕ, Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
      Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) := by
    intro n
    have horb : Theory.PiDigits.T20.baseTenOrbit Real.pi n = Int.fract ((10 : ℝ) ^ n * Real.pi) := rfl
    have hdecomp : ((10 : ℝ) ^ n - 16) * Real.pi =
        ((10 : ℝ) ^ n * Real.pi) + (51 - 16 * Real.pi) - 51 := by ring
    have hX : ((10 : ℝ) ^ n * Real.pi) =
        ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + Int.fract ((10 : ℝ) ^ n * Real.pi) := by
      have h := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
      linarith
    conv_lhs => rw [hdecomp, hX]
    have hcomm : ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + Int.fract ((10 : ℝ) ^ n * Real.pi) +
          (51 - 16 * Real.pi) - 51 =
        (Int.fract ((10 : ℝ) ^ n * Real.pi) + (51 - 16 * Real.pi)) +
          ((((⌊((10 : ℝ) ^ n * Real.pi)⌋ - 51 : ℤ))) : ℝ) := by
      push_cast
      ring
    rw [hcomm, Int.fract_add_intCast]
    rw [horb]
  exact ⟨hrec, hc_eq, ha_pos, ha_lt1, hfix', hf16, hshadow⟩

-- orbit positivity and irrationality helpers
private lemma tenPowPi_notInt (n : ℕ) (k : ℤ) : (10 : ℝ) ^ n * Real.pi ≠ (k : ℝ) := by
  intro h
  have h10R : (10 : ℝ) ^ n ≠ 0 := by positivity
  have hpi : Real.pi = (k : ℝ) / (10 : ℝ) ^ n := by
    rw [eq_div_iff h10R]
    have hcomm : (10 : ℝ) ^ n * Real.pi = Real.pi * (10 : ℝ) ^ n := by ring
    linarith [h, hcomm]
  have hQ : Real.pi = ((((k : ℚ) / (10 : ℚ) ^ n : ℚ)) : ℝ) := by
    push_cast
    exact hpi
  exact irrational_pi.ne_rat _ hQ

private lemma orbitPos_aux (n : ℕ) : 0 < Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
  have hnn : 0 ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n := Int.fract_nonneg _
  have hne : Theory.PiDigits.T20.baseTenOrbit Real.pi n ≠ 0 := by
    intro h0
    have hfr : Int.fract ((10 : ℝ) ^ n * Real.pi) = 0 := h0
    have hfl : ((10 : ℝ) ^ n * Real.pi) = ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) := by
      have h := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
      rw [hfr, add_zero] at h
      linarith
    exact tenPowPi_notInt n _ hfl
  exact lt_of_le_of_ne hnn (Ne.symm hne)

private lemma orbitLtOne_aux (n : ℕ) :
    Theory.PiDigits.T20.baseTenOrbit Real.pi n < 1 := Int.fract_lt_one _

private lemma aBounds_aux : 0 < (51 : ℝ) - 16 * Real.pi ∧ (51 : ℝ) - 16 * Real.pi < 1 := by
  have h16 := pi16_bounds
  constructor <;> linarith

-- zero block implies orbit bound (via T126 + strictness)
private lemma zeroBlock_imp_orbit (n ell : ℕ)
    (h : ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0) :
    Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ ell)⁻¹ := by
  have hzero : ∀ i : Fin ell, (Theory.PiDigits.T20.decimalDigit Real.pi (n + i.val)).val = 0 := by
    intro i
    rw [Theory.PiDigits.T20.decimalDigit_pi, h i]
    rfl
  have hle := Theory.PiQuantitativeBlockHitting.T126.baseTenOrbit_le_invPow_of_zero_window
    Real.pi_pos.le hzero
  have hlt_or_eq : Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ ell)⁻¹ ∨
      Theory.PiDigits.T20.baseTenOrbit Real.pi n = ((10 : ℝ) ^ ell)⁻¹ := lt_or_eq_of_le hle
  rcases hlt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    -- equality would make 10^n pi rational
    have horb : Theory.PiDigits.T20.baseTenOrbit Real.pi n = Int.fract ((10 : ℝ) ^ n * Real.pi) := rfl
    have hfl : ((10 : ℝ) ^ n * Real.pi) =
        ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + ((10 : ℝ) ^ ell)⁻¹ := by
      have h := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
      rw [← horb, heq] at h
      linarith
    -- so 10^{n+ell} pi is integer
    have h10 : (0 : ℝ) < (10 : ℝ) ^ ell := by positivity
    have h10e_ne : ((10 : ℝ) ^ ell) ≠ 0 := ne_of_gt h10
    have hmul : ((10 : ℝ) ^ (n + ell) * Real.pi) =
        ((((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) * (10 : ℝ) ^ ell + 1)) := by
      have hsplit : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ n * (10 : ℝ) ^ ell := by ring
      have h1 : (10 : ℝ) ^ (n + ell) * Real.pi = ((10 : ℝ) ^ n * Real.pi) * (10 : ℝ) ^ ell := by
        rw [hsplit]; ring
      conv_lhs => rw [h1, hfl, add_mul, inv_mul_cancel₀ h10e_ne]
    have hint : ((10 : ℝ) ^ (n + ell) * Real.pi) = ((((⌊((10 : ℝ) ^ n * Real.pi)⌋ * (10 ^ ell : ℕ) : ℤ) + 1 : ℤ)) : ℝ) := by
      rw [hmul]
      push_cast
      ring
    exact tenPowPi_notInt (n + ell) _ hint

-- orbit small implies zero block (via T198 cylinder)
private lemma orbit_imp_zeroBlock (n ell : ℕ) (hell : 1 ≤ ell)
    (h : Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ ell)⁻¹) :
    ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0 := by
  have h10n : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hsplit : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ n * (10 : ℝ) ^ ell := by ring
  have horb : Theory.PiDigits.T20.baseTenOrbit Real.pi n = Int.fract ((10 : ℝ) ^ n * Real.pi) := rfl
  have hfloor_le : ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) ≤ (10 : ℝ) ^ n * Real.pi :=
    Int.floor_le _
  have hlt1 : (10 : ℝ) ^ n * Real.pi < ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + ((10 : ℝ) ^ ell)⁻¹ := by
    have hfloor := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
    have horb' : Int.fract ((10 : ℝ) ^ n * Real.pi) < ((10 : ℝ) ^ ell)⁻¹ := by
      rw [← horb]; exact h
    linarith
  have hk : ∃ k : ℤ, (k : ℝ) / (10 : ℝ) ^ n ≤ Real.pi ∧
      Real.pi < (k : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + ell) := by
    refine ⟨⌊((10 : ℝ) ^ n * Real.pi)⌋, ?_, ?_⟩
    · have hle : ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) ≤ (10 : ℝ) ^ n * Real.pi :=
        Int.floor_le _
      have e : (10 : ℝ) ^ n * Real.pi = Real.pi * (10 : ℝ) ^ n := by ring
      rw [div_le_iff₀ h10n]
      linarith
    · have h10e : (0 : ℝ) < (10 : ℝ) ^ ell := by positivity
      have h10e_ne : ((10 : ℝ) ^ ell) ≠ 0 := ne_of_gt h10e
      have hdiv : ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n +
          1 / (10 : ℝ) ^ (n + ell) =
          (((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + ((10 : ℝ) ^ ell)⁻¹) / (10 : ℝ) ^ n := by
        rw [hsplit]
        field_simp
      rw [hdiv, lt_div_iff₀ h10n]
      have e : Real.pi * (10 : ℝ) ^ n = (10 : ℝ) ^ n * Real.pi := by ring
      rw [e]
      linarith [hlt1]
  have hblock := (Theory.PiDigits.T198MachinBracketPack.piZeroBlock_iff_decimalCylinder n ell hell).mpr hk
  exact hblock

private lemma nineBlock_iff_floorEqNat (n : ℕ) : ∀ (ell : ℕ),
    (∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 9) ↔
    ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ = 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) := by
  intro ell
  induction ell with
  | zero =>
    constructor
    · intro _
      simp
    · intro _ i
      exact Fin.elim0 i
  | succ ell ih =>
    have hstep := Theory.PiDigits.T198MachinBracketPack.singleDigitFloor (n + ell)
    have hexp1 : n + (ell + 1) = (n + ell) + 1 := by omega
    have hpow : (10 : ℕ) ^ (ell + 1) = 10 ^ ell * 10 := pow_succ 10 ell
    have hpow1 : (10 : ℕ) ^ (ell + 1) - 1 = (10 ^ ell - 1) * 10 + 9 := by
      have hge : 1 ≤ 10 ^ ell := Nat.one_le_pow ell 10 (by norm_num)
      omega
    constructor
    · intro h
      have hrest : ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 9 :=
        fun i => h i.castSucc
      have hlast : Theory.PiDigits.piDigit (n + ell) = 9 := h (Fin.last ell)
      have hIH := ih.mp hrest
      have hval9 : (Theory.PiDigits.piDigit (n + ell)).val = 9 := by
        rw [hlast]; rfl
      have hge : 1 ≤ 10 ^ ell := Nat.one_le_pow ell 10 (by norm_num)
      obtain ⟨E', hE'⟩ := Nat.exists_eq_add_of_le hge
      have hE : 10 ^ ell = 1 + E' := by omega
      have hsub : (1 + E') - 1 = E' := by omega
      have hsub2 : ((1 + E') * 10) - 1 = E' * 10 + 9 := by omega
      rw [hexp1, hstep, hval9, hIH, hpow, hE, hsub, hsub2]
      ring
    · intro h
      rw [hexp1] at h
      rw [hstep] at h
      rw [hpow1, hpow] at h
      have hEq : (10 ^ ell * 10) * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ = 10 * (10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊) := by
        ring
      rw [hEq] at h
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
      have hupper : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ ≤ 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) := by
        have h10 : (0 : ℝ) < (10 : ℝ) ^ ell := by positivity
        have hlt : Real.pi * (10 : ℝ) ^ (n + ell) < ((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell : ℕ) : ℝ) := by
          have hBle : Real.pi * (10 : ℝ) ^ n < (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          have hsplit : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ ell * (10 : ℝ) ^ n := by ring
          calc Real.pi * (10 : ℝ) ^ (n + ell)
              = (10 : ℝ) ^ ell * (Real.pi * (10 : ℝ) ^ n) := by rw [hsplit]; ring
            _ < (10 : ℝ) ^ ell * ((((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + 1) := by
                apply mul_lt_mul_of_pos_left hBle h10
            _ = (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell : ℕ)) : ℝ) := by
                push_cast; ring
        have hlt2 : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ < 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell := by
          have e : (((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ)) : ℝ) < (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell : ℕ)) : ℝ) := by
            calc (((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ)) : ℝ)
                ≤ Real.pi * (10 : ℝ) ^ (n + ell) := Nat.floor_le (by positivity)
              _ < (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell : ℕ)) : ℝ) := hlt
          exact_mod_cast e
        have hge1 : 1 ≤ 10 ^ ell := Nat.one_le_pow ell 10 (by norm_num)
        omega
      have hval_le : (Theory.PiDigits.piDigit (n + ell)).val ≤ 9 := Nat.lt_succ_iff.mp (Fin.isLt _)
      have hge : 1 ≤ 10 ^ ell := Nat.one_le_pow ell 10 (by norm_num)
      have hFeq : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊
          = 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) := by
        omega
      have hval9 : (Theory.PiDigits.piDigit (n + ell)).val = 9 := by omega
      have hlast : Theory.PiDigits.piDigit (n + ell) = 9 := by
        apply Fin.ext
        simpa using hval9
      have hrest := ih.mpr hFeq
      rw [Fin.forall_fin_succ']
      exact ⟨fun i => hrest i, hlast⟩

private lemma nineBlock_imp_orbit (n ell : ℕ)
    (h : ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 9) :
    1 - ((10 : ℝ) ^ ell)⁻¹ < Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
  have hell1 : 1 ≤ 10 ^ ell := Nat.one_le_pow ell 10 (by norm_num)
  have hfloor := (nineBlock_iff_floorEqNat n ell).mp h
  have h10e : (0 : ℝ) < (10 : ℝ) ^ ell := by positivity
  have h10e_ne : ((10 : ℝ) ^ ell) ≠ 0 := ne_of_gt h10e
  have hsplit : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ n * (10 : ℝ) ^ ell := by ring
  have hsplit2 : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ ell * (10 : ℝ) ^ n := by ring
  have horb_n : Theory.PiDigits.T20.baseTenOrbit Real.pi n = Int.fract ((10 : ℝ) ^ n * Real.pi) := rfl
  have hFn_eq : (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) = ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) := by
    have hnn : 0 ≤ ((10 : ℝ) ^ n * Real.pi) := mul_nonneg (by positivity) Real.pi_pos.le
    have h1 : ((⌊((10 : ℝ) ^ n * Real.pi)⌋.toNat : ℕ) : ℤ) = ⌊((10 : ℝ) ^ n * Real.pi)⌋ :=
      Int.toNat_of_nonneg (Int.floor_nonneg.mpr hnn)
    have h2 : ⌊((10 : ℝ) ^ n * Real.pi)⌋.toNat = ⌊Real.pi * (10 : ℝ) ^ n⌋₊ := by
      have e : Real.pi * (10 : ℝ) ^ n = (10 : ℝ) ^ n * Real.pi := by ring
      rw [e]
      exact (Int.floor_toNat _).symm
    rw [← h1, h2]
    push_cast
    ring
  have hFnell_eq : (((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ)) : ℝ) =
      ((⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋ : ℤ) : ℝ) := by
    have hnn : 0 ≤ ((10 : ℝ) ^ (n + ell) * Real.pi) := mul_nonneg (by positivity) Real.pi_pos.le
    have h1 : ((⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋.toNat : ℕ) : ℤ) = ⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋ :=
      Int.toNat_of_nonneg (Int.floor_nonneg.mpr hnn)
    have h2 : ⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋.toNat = ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ := by
      have e : Real.pi * (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ (n + ell) * Real.pi := by ring
      rw [e]
      exact (Int.floor_toNat _).symm
    rw [← h1, h2]
    push_cast
    ring
  have h1 : (10 : ℝ) ^ n * Real.pi =
      ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
    have h := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
    rw [← horb_n] at h
    linarith
  have hdelta_pos : 0 < Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := orbitPos_aux (n + ell)
  have hdelta_lt : Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) < 1 := orbitLtOne_aux (n + ell)
  have h2 : (10 : ℝ) ^ (n + ell) * Real.pi =
      ((⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋ : ℤ) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := by
    have h := Int.floor_add_fract ((10 : ℝ) ^ (n + ell) * Real.pi)
    have horb : Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) =
        Int.fract ((10 : ℝ) ^ (n + ell) * Real.pi) := rfl
    rw [← horb] at h
    linarith
  have hfloor_cast : (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) : ℕ)) : ℝ) =
      ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + (((10 ^ ell - 1 : ℕ)) : ℝ) := by
    push_cast; ring
  have hsub_cast : (((10 ^ ell - 1 : ℕ)) : ℝ) = (10 : ℝ) ^ ell - 1 := by
    simpa using Nat.cast_sub hell1
  have hEq : (10 : ℝ) ^ (n + ell) * Real.pi =
      ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + ((10 : ℝ) ^ ell - 1) +
        Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := by
    have hfloorR : (((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ)) : ℝ) =
        ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + ((10 : ℝ) ^ ell - 1) := by
      have hcast : (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) : ℕ)) : ℝ) =
          ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + (((10 ^ ell - 1 : ℕ)) : ℝ) := by
        push_cast; ring
      rw [← hsub_cast, ← hcast, hfloor]
    have h2R : (10 : ℝ) ^ (n + ell) * Real.pi =
        (((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ)) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := by
      have hF : (((⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ : ℕ)) : ℝ) =
          ((⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋ : ℤ) : ℝ) := by
        have hnn : 0 ≤ ((10 : ℝ) ^ (n + ell) * Real.pi) := mul_nonneg (by positivity) Real.pi_pos.le
        have h1 : ((⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋.toNat : ℕ) : ℤ) = ⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋ :=
          Int.toNat_of_nonneg (Int.floor_nonneg.mpr hnn)
        have h2e : ⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋.toNat = ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ := by
          have e : Real.pi * (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ (n + ell) * Real.pi := by ring
          rw [e]
          exact (Int.floor_toNat _).symm
        rw [← h1, h2e]
        push_cast
        ring
      have hI : (10 : ℝ) ^ (n + ell) * Real.pi =
          ((⌊((10 : ℝ) ^ (n + ell) * Real.pi)⌋ : ℤ) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := by
        have h := Int.floor_add_fract ((10 : ℝ) ^ (n + ell) * Real.pi)
        have horb : Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) =
            Int.fract ((10 : ℝ) ^ (n + ell) * Real.pi) := rfl
        rw [← horb] at h
        linarith
      linarith [hF, hI]
    linarith [h2R, hfloorR]
  have hEq2 : (10 : ℝ) ^ (n + ell) * Real.pi =
      ((10 : ℝ) ^ ell) * ((10 : ℝ) ^ n * Real.pi) := by
    rw [hsplit]; ring
  have hE_orbit : ((10 : ℝ) ^ ell) * Theory.PiDigits.T20.baseTenOrbit Real.pi n =
      ((10 : ℝ) ^ ell - 1) + Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := by
    have h1' : ((10 : ℝ) ^ ell) * ((10 : ℝ) ^ n * Real.pi) =
        ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) +
          ((10 : ℝ) ^ ell) * Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
      have h1Nat : (10 : ℝ) ^ n * Real.pi =
          (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
        linarith [h1, hFn_eq]
      rw [h1Nat]; ring
    have h2' : (10 : ℝ) ^ (n + ell) * Real.pi =
        ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + ((10 : ℝ) ^ ell - 1) +
          Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := hEq
    have h3 : ((10 : ℝ) ^ ell) * ((10 : ℝ) ^ n * Real.pi) = (10 : ℝ) ^ (n + ell) * Real.pi := by
      rw [hsplit]; ring
    linarith [h1', h2', h3]
  have hlt : (1 - Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell)) / (10 : ℝ) ^ ell <
      ((10 : ℝ) ^ ell)⁻¹ := by
    have h1δ : 1 - Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) < 1 := by linarith [hdelta_pos]
    have hpos : 0 < 1 - Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell) := by linarith [hdelta_lt]
    calc (1 - Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell)) / (10 : ℝ) ^ ell
        < 1 / (10 : ℝ) ^ ell := by
          apply div_lt_div_of_pos_right h1δ h10e
      _ = ((10 : ℝ) ^ ell)⁻¹ := by rw [one_div]
  have horb_eq : Theory.PiDigits.T20.baseTenOrbit Real.pi n =
      1 - (1 - Theory.PiDigits.T20.baseTenOrbit Real.pi (n + ell)) / (10 : ℝ) ^ ell := by
    field_simp
    linarith [hE_orbit]
  linarith [horb_eq, hlt]

private lemma orbit_imp_nineBlock (n ell : ℕ) (hell : 1 ≤ ell)
    (h : 1 - ((10 : ℝ) ^ ell)⁻¹ < Theory.PiDigits.T20.baseTenOrbit Real.pi n) :
    ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 9 := by
  have h10e : (0 : ℝ) < (10 : ℝ) ^ ell := by positivity
  have hell1 : 1 ≤ 10 ^ ell := Nat.one_le_pow ell 10 (by norm_num)
  have horb_lt : Theory.PiDigits.T20.baseTenOrbit Real.pi n < 1 := orbitLtOne_aux n
  have hEorb : ((10 : ℝ) ^ ell - 1) < (10 : ℝ) ^ ell * Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
    have h1 : ((10 : ℝ) ^ ell) * (1 - ((10 : ℝ) ^ ell)⁻¹) = (10 : ℝ) ^ ell - 1 := by
      field_simp
    have h2 : ((10 : ℝ) ^ ell) * (1 - ((10 : ℝ) ^ ell)⁻¹) <
        (10 : ℝ) ^ ell * Theory.PiDigits.T20.baseTenOrbit Real.pi n :=
      mul_lt_mul_of_pos_left h h10e
    linarith [h1, h2]
  have hEorb_lt : (10 : ℝ) ^ ell * Theory.PiDigits.T20.baseTenOrbit Real.pi n < (10 : ℝ) ^ ell := by
    calc (10 : ℝ) ^ ell * Theory.PiDigits.T20.baseTenOrbit Real.pi n
        < (10 : ℝ) ^ ell * 1 := mul_lt_mul_of_pos_left horb_lt h10e
      _ = (10 : ℝ) ^ ell := mul_one _
  have h1 : (10 : ℝ) ^ n * Real.pi =
      (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
    have hF : (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) = ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) := by
      have hnn : 0 ≤ ((10 : ℝ) ^ n * Real.pi) := mul_nonneg (by positivity) Real.pi_pos.le
      have h1e : ((⌊((10 : ℝ) ^ n * Real.pi)⌋.toNat : ℕ) : ℤ) = ⌊((10 : ℝ) ^ n * Real.pi)⌋ :=
        Int.toNat_of_nonneg (Int.floor_nonneg.mpr hnn)
      have h2e : ⌊((10 : ℝ) ^ n * Real.pi)⌋.toNat = ⌊Real.pi * (10 : ℝ) ^ n⌋₊ := by
        have e : Real.pi * (10 : ℝ) ^ n = (10 : ℝ) ^ n * Real.pi := by ring
        rw [e]
        exact (Int.floor_toNat _).symm
      rw [← h1e, h2e]
      push_cast
      ring
    have hI : (10 : ℝ) ^ n * Real.pi =
        ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
      have h := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
      have horb' : Theory.PiDigits.T20.baseTenOrbit Real.pi n =
          Int.fract ((10 : ℝ) ^ n * Real.pi) := rfl
      rw [← horb'] at h
      linarith
    linarith [hF, hI]
  have hsplit2 : (10 : ℝ) ^ (n + ell) = (10 : ℝ) ^ ell * (10 : ℝ) ^ n := by ring
  have hlow : (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) : ℕ)) : ℝ) ≤
      Real.pi * (10 : ℝ) ^ (n + ell) := by
    have hcast : (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) : ℕ)) : ℝ) =
        ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + ((10 : ℝ) ^ ell - 1) := by
      have hc : (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) : ℕ)) : ℝ) =
          ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + (((10 ^ ell - 1 : ℕ)) : ℝ) := by
        push_cast; ring
      rw [hc]
      have hs : (((10 ^ ell - 1 : ℕ)) : ℝ) = (10 : ℝ) ^ ell - 1 := by
        simpa using Nat.cast_sub hell1
      rw [hs]
    rw [hcast, hsplit2]
    have hle1 : ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + ((10 : ℝ) ^ ell - 1) ≤
        ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) +
          ((10 : ℝ) ^ ell * Theory.PiDigits.T20.baseTenOrbit Real.pi n) := by
      linarith [hEorb.le]
    have heq1 : ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) +
          ((10 : ℝ) ^ ell * Theory.PiDigits.T20.baseTenOrbit Real.pi n) =
        (10 : ℝ) ^ ell * (Real.pi * (10 : ℝ) ^ n) := by
      have he : (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi n =
          Real.pi * (10 : ℝ) ^ n := by
        have e : (10 : ℝ) ^ n * Real.pi = Real.pi * (10 : ℝ) ^ n := by ring
        linarith [h1, e]
      have hd : ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) +
          ((10 : ℝ) ^ ell * Theory.PiDigits.T20.baseTenOrbit Real.pi n) =
          (10 : ℝ) ^ ell * ((((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + Theory.PiDigits.T20.baseTenOrbit Real.pi n) := by
        ring
      rw [hd, he]
    linarith [hle1, heq1]
  have hhigh : Real.pi * (10 : ℝ) ^ (n + ell) <
      (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell : ℕ)) : ℝ) := by
    have hcast2 : (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell : ℕ)) : ℝ) =
        ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + (10 : ℝ) ^ ell := by
      push_cast; ring
    rw [hcast2, hsplit2]
    have hlt2 : Real.pi * (10 : ℝ) ^ n < (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hmul := mul_lt_mul_of_pos_left hlt2 h10e
    have heq : ((10 : ℝ) ^ ell) * ((((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + 1) =
        ((10 : ℝ) ^ ell) * (((⌊Real.pi * (10 : ℝ) ^ n⌋₊ : ℕ)) : ℝ) + (10 : ℝ) ^ ell := by
      ring
    have hpi_eq : (10 : ℝ) ^ ell * (Real.pi * (10 : ℝ) ^ n) = Real.pi * ((10 : ℝ) ^ ell * (10 : ℝ) ^ n) := by
      ring
    linarith [hmul, heq, hpi_eq, h1]
  have hfloor_eq : ⌊Real.pi * (10 : ℝ) ^ (n + ell)⌋₊ =
      10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor
    · exact hlow
    · have eNat : 10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) + 1 =
          10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell := by omega
      have hlt3 : ((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) : Nat) : ℝ) + 1 =
          ((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + 10 ^ ell : Nat) : ℝ) := by
        have c1 : (((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) + 1 : Nat) : ℝ)) =
            ((((10 ^ ell * ⌊Real.pi * (10 : ℝ) ^ n⌋₊ + (10 ^ ell - 1) : Nat) : ℝ)) + 1) := by
          push_cast; ring
        rw [← c1, eNat]
      linarith [hlow, hhigh, hlt3]
  exact (nineBlock_iff_floorEqNat n ell).mpr hfloor_eq

-- v-orbit link (no pi bounds needed, only integer shifts)
private lemma v_orbit_eq (n : ℕ) :
    Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
      Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) := by
  have horb : Theory.PiDigits.T20.baseTenOrbit Real.pi n = Int.fract ((10 : ℝ) ^ n * Real.pi) := rfl
  have hdecomp : ((10 : ℝ) ^ n - 16) * Real.pi =
      ((10 : ℝ) ^ n * Real.pi) + (51 - 16 * Real.pi) - 51 := by ring
  have hX : ((10 : ℝ) ^ n * Real.pi) =
      ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + Int.fract ((10 : ℝ) ^ n * Real.pi) := by
    have h := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
    linarith
  conv_lhs => rw [hdecomp, hX]
  have hcomm : ((⌊((10 : ℝ) ^ n * Real.pi)⌋ : ℤ) : ℝ) + Int.fract ((10 : ℝ) ^ n * Real.pi) +
        (51 - 16 * Real.pi) - 51 =
      (Int.fract ((10 : ℝ) ^ n * Real.pi) + (51 - 16 * Real.pi)) +
        ((((⌊((10 : ℝ) ^ n * Real.pi)⌋ - 51 : ℤ))) : ℝ) := by
    push_cast; ring
  rw [hcomm, Int.fract_add_intCast, horb]

private lemma aBounds : 0 < (51 : ℝ) - 16 * Real.pi ∧ (51 : ℝ) - 16 * Real.pi < 1 := by
  have h16 := pi16_bounds
  constructor <;> linarith

private lemma one_sub_a_pos : 0 < 1 - ((51 : ℝ) - 16 * Real.pi) := by
  have h := aBounds
  linarith

private lemma invPow_pos (k : ℕ) : (0 : ℝ) < ((10 : ℝ) ^ k)⁻¹ := by positivity

private lemma exists_invPow_lt (δ : ℝ) (hδ : 0 < δ) : ∃ k : ℕ, ((10 : ℝ) ^ k)⁻¹ < δ := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/10 : ℝ) < 1)
  refine ⟨m, ?_⟩
  have e : ((1/10 : ℝ)) ^ m = ((10 : ℝ) ^ m)⁻¹ := by
    rw [div_pow, one_pow, inv_eq_one_div]
  linarith [hm, e]

theorem bbp10_rightApproach_iff_piCW0 :
    (let v : ℕ → ℝ := fun n ↦ Int.fract (((10 : ℝ) ^ n - 16) * Real.pi); let a : ℝ := 51 - 16 * Real.pi; (∀ η : ℝ, 0 < η → ∃ n : ℕ, a < v n ∧ v n < a + η) ↔ ∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0) := by
  show (∀ η : ℝ, 0 < η → ∃ n : ℕ,
      51 - 16 * Real.pi < Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) ∧
      Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) < 51 - 16 * Real.pi + η) ↔
    ∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0
  have ha := aBounds
  have h1ma : 0 < 1 - (51 - 16 * Real.pi) := by linarith
  constructor
  · intro hRight ell hell
    have h10e : (0 : ℝ) < ((10 : ℝ) ^ ell)⁻¹ := invPow_pos ell
    have hδ : 0 < min ((10 : ℝ) ^ ell)⁻¹ (1 - (51 - 16 * Real.pi)) := lt_min h10e h1ma
    obtain ⟨η0, hη0⟩ := exists_invPow_lt _ hδ
    -- Actually need η with 10^{-η}? No, need v approach with η0 = min(...)?? Wait hRight gives n with v∈(a,a+η) for any η>0. Choose η = min(10^{-ell},1-a)?? But η must be ℝ, not Nat pow? Choose η0 = min(10^{-ell},1-a) >0, then hRight η0 gives n with v∈(a,a+η0), then orbit = v-a <10^{-ell}, giving zero block.
    -- To avoid exists_invPow_lt (which gives k with 10^{-k}<δ), directly take η = min(10^{-ell},1-a) >0.
    have heta : 0 < min (((10 : ℝ) ^ ell)⁻¹) (1 - (51 - 16 * Real.pi)) := hδ
    obtain ⟨n, hn1, hn2⟩ := hRight _ heta
    have hv : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
        Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) :=
      v_orbit_eq n
    have horb_lt1a : Theory.PiDigits.T20.baseTenOrbit Real.pi n < 1 - (51 - 16 * Real.pi) := by
      -- since v∈(a,a+η) with η<1-a, orbit must be <1-a (otherwise v<a)
      by_contra hcon
      have horb_ge : 1 - (51 - 16 * Real.pi) ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n :=
        le_of_not_gt hcon
      have horb_lt1 := orbitLtOne_aux n
      have horb_pos := orbitPos_aux n
      have hcase : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) <
          51 - 16 * Real.pi := by
        by_cases heq : Theory.PiDigits.T20.baseTenOrbit Real.pi n = 1 - (51 - 16 * Real.pi)
        · rw [heq]
          have h1 : (1 - (51 - 16 * Real.pi) + (51 - 16 * Real.pi) : ℝ) = 1 := by ring
          rw [h1, Int.fract_one]
          linarith [ha.1]
        · have hgt : 1 - (51 - 16 * Real.pi) < Theory.PiDigits.T20.baseTenOrbit Real.pi n := lt_of_le_of_ne horb_ge (Ne.symm heq)
          have hsum_gt1 : 1 < Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by linarith
          have hsum_lt2 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 2 := by
            linarith [horb_lt1, ha.2]
          have hfract : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) =
              Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) - 1 := by
            have hfl : ⌊Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)⌋ = 1 := by
              rw [Int.floor_eq_iff]
              constructor
              · norm_num; linarith
              · norm_num; linarith
            have h := Int.floor_add_fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi))
            rw [hfl] at h
            push_cast at h
            linarith
          linarith [hfract, horb_lt1]
      linarith [hcase, hv, hn1]
    have horb_eq : Theory.PiDigits.T20.baseTenOrbit Real.pi n =
        Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) - (51 - 16 * Real.pi) := by
      have hsum_lt1 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 1 := by
        linarith [horb_lt1a, ha.2]
        -- orbit+(a) < (1-a)+a =1
      have hsum_pos : 0 ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
        have h1 := orbitPos_aux n
        linarith [ha.1]
      have hfract : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) =
          Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
        exact Int.fract_eq_self.mpr ⟨hsum_pos, hsum_lt1⟩
      linarith [hv, hfract]
    have horb_lt_inv : Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ ell)⁻¹ := by
      have hle : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) < 51 - 16 * Real.pi + min (((10 : ℝ) ^ ell)⁻¹) (1 - (51 - 16 * Real.pi)) := hn2
      have hmin : min (((10 : ℝ) ^ ell)⁻¹) (1 - (51 - 16 * Real.pi)) ≤ ((10 : ℝ) ^ ell)⁻¹ := min_le_left _ _
      linarith [horb_eq, hle, hmin]
    exact ⟨n, orbit_imp_zeroBlock n ell hell horb_lt_inv⟩
  · intro hCW η hη
    obtain ⟨k, hk⟩ := exists_invPow_lt (min η (1 - (51 - 16 * Real.pi))) (lt_min hη h1ma)
    have hk_lt : ((10 : ℝ) ^ k)⁻¹ < η := lt_of_lt_of_le hk (min_le_left _ _)
    have hk_1a : ((10 : ℝ) ^ k)⁻¹ < 1 - (51 - 16 * Real.pi) := lt_of_lt_of_le hk (min_le_right _ _)
    have hk1 : 1 ≤ k := by
      by_contra hcon
      have hle : k < 1 := lt_of_not_ge hcon
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      norm_num at hk
      linarith [hk, hη, ha.1, ha.2]
      -- 1 < min(η,1-a) ≤1-a<1? Since 1-a<1 (as a>0), 1<1-a impossible.
    obtain ⟨n, hn⟩ := hCW k hk1
    have horb := zeroBlock_imp_orbit n k hn
    have horb_1a : Theory.PiDigits.T20.baseTenOrbit Real.pi n < 1 - (51 - 16 * Real.pi) := lt_trans horb hk_1a
    have hv_eq : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
        Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
      have hsum_lt1 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 1 := by
        linarith [horb_1a, ha.2]
      have hsum_pos : 0 ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
        linarith [orbitPos_aux n, ha.1]
      have hfract := Int.fract_eq_self.mpr ⟨hsum_pos, hsum_lt1⟩
      have hv := v_orbit_eq n
      linarith [hv, hfract]
    refine ⟨n, ?_, ?_⟩
    · linarith [hv_eq, orbitPos_aux n]
    · linarith [hv_eq, horb, hk_lt]

theorem bbp10_leftApproach_iff_piCW9 :
    (let v : ℕ → ℝ := fun n ↦ Int.fract (((10 : ℝ) ^ n - 16) * Real.pi); let a : ℝ := 51 - 16 * Real.pi; (∀ η : ℝ, 0 < η → ∃ n : ℕ, a - η < v n ∧ v n < a) ↔ ∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 9) := by
  show (∀ η : ℝ, 0 < η → ∃ n : ℕ,
      51 - 16 * Real.pi - η < Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) ∧
      Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) < 51 - 16 * Real.pi) ↔
    ∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 9
  have ha := aBounds
  have ha_pos : 0 < (51 - 16 * Real.pi) := ha.1
  constructor
  · intro hLeft ell hell
    have h10e : (0 : ℝ) < ((10 : ℝ) ^ ell)⁻¹ := invPow_pos ell
    have hδ : 0 < min (((10 : ℝ) ^ ell)⁻¹) (51 - 16 * Real.pi) := lt_min h10e ha_pos
    obtain ⟨n, hn1, hn2⟩ := hLeft _ hδ
    have hv : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
        Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) :=
      v_orbit_eq n
    -- show orbit > 1-a (otherwise v ≥ a)
    have horb_gt1a : 1 - (51 - 16 * Real.pi) < Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
      by_contra hcon
      have hle : Theory.PiDigits.T20.baseTenOrbit Real.pi n ≤ 1 - (51 - 16 * Real.pi) :=
        le_of_not_gt hcon
      have horb_lt1 := orbitLtOne_aux n
      have hmin_a : min (((10 : ℝ) ^ ell)⁻¹) (51 - 16 * Real.pi) ≤ 51 - 16 * Real.pi :=
        min_le_right _ _
      by_cases heq : Theory.PiDigits.T20.baseTenOrbit Real.pi n = 1 - (51 - 16 * Real.pi)
      · -- equality gives v = 0, contradicting v > a-η ≥ 0
        have hv0 : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) = 0 := by
          rw [heq]
          have h1 : (1 - (51 - 16 * Real.pi) + (51 - 16 * Real.pi) : ℝ) = 1 := by ring
          rw [h1, Int.fract_one]
        linarith [hv, hv0, hn1, hmin_a, ha.1]
      · have hlt : Theory.PiDigits.T20.baseTenOrbit Real.pi n < 1 - (51 - 16 * Real.pi) :=
          lt_of_le_of_ne hle heq
        have hsum_lt1 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 1 := by linarith
        have hsum_pos : 0 ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
          linarith [orbitPos_aux n, ha.1]
        have hfract := Int.fract_eq_self.mpr ⟨hsum_pos, hsum_lt1⟩
        have hcase : 51 - 16 * Real.pi ≤
            Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) := by
          linarith [hfract, orbitPos_aux n]
        linarith [hcase, hv, hn2]
    have horb_eq : Theory.PiDigits.T20.baseTenOrbit Real.pi n =
        Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) - (51 - 16 * Real.pi) + 1 := by
      have hsum_gt1 : 1 < Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by linarith [horb_gt1a]
      have hsum_lt2 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 2 := by
        linarith [orbitLtOne_aux n, ha.2]
      have hfract : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) =
          Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) - 1 := by
        have hfl : ⌊Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)⌋ = 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · norm_num; linarith
          · norm_num; linarith
        have h := Int.floor_add_fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi))
        rw [hfl] at h
        push_cast at h
        linarith
      linarith [hv, hfract]
    have horb_low : 1 - ((10 : ℝ) ^ ell)⁻¹ < Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
      have hle : 51 - 16 * Real.pi - min (((10 : ℝ) ^ ell)⁻¹) (51 - 16 * Real.pi) <
          Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) := hn1
      have hmin : min (((10 : ℝ) ^ ell)⁻¹) (51 - 16 * Real.pi) ≤ ((10 : ℝ) ^ ell)⁻¹ := min_le_left _ _
      have hmin2 : min (((10 : ℝ) ^ ell)⁻¹) (51 - 16 * Real.pi) ≤ 51 - 16 * Real.pi := min_le_right _ _
      -- v = orbit+a-1, so orbit = v-a+1 > (a-η)-a+1 = 1-η ≥ 1-10^{-ell}
      linarith [horb_eq, hle, hmin]
    exact ⟨n, orbit_imp_nineBlock n ell hell horb_low⟩
  · intro hCW η hη
    obtain ⟨k, hk⟩ := exists_invPow_lt (min η (51 - 16 * Real.pi)) (lt_min hη ha_pos)
    have hk_lt : ((10 : ℝ) ^ k)⁻¹ < η := lt_of_lt_of_le hk (min_le_left _ _)
    have hk_a : ((10 : ℝ) ^ k)⁻¹ < 51 - 16 * Real.pi := lt_of_lt_of_le hk (min_le_right _ _)
    have hk1 : 1 ≤ k := by
      by_contra hcon
      have hle : k < 1 := lt_of_not_ge hcon
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      norm_num at hk
      linarith [hk, hη, ha.1]
    obtain ⟨n, hn⟩ := hCW k hk1
    have horb := nineBlock_imp_orbit n k hn
    have horb_1a : 1 - (51 - 16 * Real.pi) < Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
      -- since 10^{-k} < a, 1-10^{-k} > 1-a
      have h10a : ((10 : ℝ) ^ k)⁻¹ < 51 - 16 * Real.pi := hk_a
      have h1a : 1 - (51 - 16 * Real.pi) < 1 - ((10 : ℝ) ^ k)⁻¹ := by linarith
      linarith [horb, h1a]
    have hv_eq : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
        Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) - 1 := by
      have hsum_gt1 : 1 < Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by linarith [horb_1a]
      have hsum_lt2 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 2 := by
        linarith [orbitLtOne_aux n, ha.2]
      have hfract : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) =
          Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) - 1 := by
        have hfl : ⌊Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)⌋ = 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · norm_num; linarith
          · norm_num; linarith
        have h := Int.floor_add_fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi))
        rw [hfl] at h
        push_cast at h
        linarith
      have hv := v_orbit_eq n
      linarith [hv, hfract]
    refine ⟨n, ?_, ?_⟩
    · -- a-η < v = orbit+a-1  ⟸ orbit > 1-η  (since orbit > 1-10^{-k} > 1-η)
      have horb_eta : 1 - η < Theory.PiDigits.T20.baseTenOrbit Real.pi n := by
        linarith [horb, hk_lt]
      linarith [hv_eq, horb_eta]
    · linarith [hv_eq, orbitLtOne_aux n]

-- helpers for SOH (E bounds, head/v relationship)
private lemma Epos_aux (n : ℕ) (hn : 2 ≤ n) :
    0 < ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by
  have hc := cPosAux n hn
  have htail := real_bbp_tail_quadratic_bounds (n - 1)
  have hpos : (0 : ℝ) < 1 / (4 * bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := by
    unfold bbpTailScale; positivity
  have hpiB : 0 < Real.pi - bbpRealPartial (n - 1) := by linarith [htail.1]
  exact mul_pos hc hpiB

private lemma Elt58_aux (n : ℕ) (hn : 2 ≤ n) :
    ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < ((5 : ℝ) / 8) ^ n := by
  have hc := cPosAux n hn
  have htail := real_bbp_tail_quadratic_bounds (n - 1)
  have hge := scale_ge_306 n hn
  have hpos : (0 : ℝ) < bbpTailScale (n - 1) := by linarith
  have h16m : (0 : ℝ) < (16 : ℝ) ^ (n - 1) := by positivity
  have hup : Real.pi - bbpRealPartial (n - 1) < 1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := htail.2
  have hupnn : (0 : ℝ) ≤ 1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1)) := le_of_lt (by positivity)
  have hn_eq : n - 1 + 1 = n := by omega
  have h16n : (16 : ℝ) ^ n = (16 : ℝ) ^ (n - 1) * 16 := by
    conv_lhs => rw [← hn_eq, pow_succ]
  have h10eq : (10 : ℝ) ^ n * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) =
      (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) := by
    rw [fiveEighth_eq, h16n]; field_simp
  have h16s : (16 : ℝ) / bbpTailScale (n - 1) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  have hnn : (0 : ℝ) ≤ ((5 : ℝ) / 8) ^ n := le_of_lt (fiveEighth_pos n)
  have hle2 : (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) ≤ ((5 : ℝ) / 8) ^ n := by
    calc (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n)
        ≤ 1 * (((5 : ℝ) / 8) ^ n) := mul_le_mul_of_nonneg_right h16s hnn
      _ = ((5 : ℝ) / 8) ^ n := one_mul _
  calc ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))
      < ((10 : ℝ) ^ n - 16) * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) :=
        mul_lt_mul_of_pos_left hup hc
    _ ≤ (10 : ℝ) ^ n * (1 / (bbpTailScale (n - 1) * (16 : ℝ) ^ (n - 1))) := by
        apply mul_le_mul_of_nonneg_right _ hupnn
        have : (0 : ℝ) ≤ (10 : ℝ) ^ n := by positivity
        linarith
    _ = (16 / bbpTailScale (n - 1)) * (((5 : ℝ) / 8) ^ n) := h10eq
    _ ≤ ((5 : ℝ) / 8) ^ n := hle2

private lemma EltA_aux (n : ℕ) (hn : 2 ≤ n) :
    ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < 51 - 16 * Real.pi := by
  have h58 := Elt58_aux n hn
  have h58_2 : ((5 : ℝ) / 8) ^ n ≤ ((5 : ℝ) / 8) ^ 2 := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h2564 : ((5 : ℝ) / 8) ^ (2 : ℕ) = 25 / 64 := by norm_num
  have ha : (25 : ℝ) / 64 < 51 - 16 * Real.pi := by
    have h2 : Real.pi < 3.1416 := Real.pi_lt_d4
    nlinarith
  linarith [h58, h58_2, h2564, ha]

private lemma v_headE_aux (n : ℕ) :
    Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
      Int.fract (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) := by
  have hXeq : ((10 : ℝ) ^ n - 16) * Real.pi =
      ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by ring
  have hX : ((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1) =
      ((⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℤ) : ℝ) +
        Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) := by
    have h := Int.floor_add_fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1))
    linarith
  conv_lhs => rw [hXeq, hX]
  have hcomm2 : ((⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℤ) : ℝ) +
      Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
      ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) =
      (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) +
      ((⌊((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)⌋ : ℤ) : ℝ) := by ring
  rw [hcomm2, Int.fract_add_intCast]

private lemma invPow_le_one_sub_a (k : ℕ) (hk : 1 ≤ k) :
    ((10 : ℝ) ^ k)⁻¹ ≤ 1 - (51 - 16 * Real.pi) := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h1a_ge : (0.24 : ℝ) ≤ 1 - (51 - 16 * Real.pi) := by
    have : 1 - (51 - 16 * Real.pi) = 16 * Real.pi - 50 := by ring
    linarith
  have h10k : (10 : ℝ) ≤ (10 : ℝ) ^ k := by
    calc (10 : ℝ) = (10 : ℝ) ^ 1 := by norm_num
      _ ≤ (10 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hinv : ((10 : ℝ) ^ k)⁻¹ ≤ ((10 : ℝ))⁻¹ := by gcongr
  have h01 : ((10 : ℝ))⁻¹ = (0.1 : ℝ) := by norm_num
  linarith [hinv, h01, h1a_ge]

theorem bbp10_soh0_iff_piCW0 :
    (let B : ℕ → ℝ := fun n ↦ Theory.PiDigits.T100BBPRealBridge.bbpRealPartial (n - 1); let E : ℕ → ℝ := fun n ↦ ((10 : ℝ) ^ n - 16) * (Real.pi - B n); let a : ℝ := 51 - 16 * Real.pi; (∀ k N : ℕ, 1 ≤ k → 1 ≤ N → ∃ n : ℕ, max N 2 ≤ n ∧ 0 < Int.fract (((10 : ℝ) ^ n - 16) * B n) + E n - a ∧ Int.fract (((10 : ℝ) ^ n - 16) * B n) + E n - a < ((10 : ℝ) ^ k)⁻¹) ↔ ∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0) := by
  show (∀ k N : ℕ, 1 ≤ k → 1 ≤ N → ∃ n : ℕ, max N 2 ≤ n ∧
      0 < Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - (51 - 16 * Real.pi) ∧
      Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - (51 - 16 * Real.pi) < ((10 : ℝ) ^ k)⁻¹) ↔
    ∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ, ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0
  have ha := aBounds
  have h1ma : 0 < 1 - (51 - 16 * Real.pi) := by linarith
  constructor
  · -- SOH ⇒ CW0: given ell, choose k' with 10^{-k'} < min(1-a,10^{-ell}), get t∈(0,10^{-k'}), deduce orbit<10^{-ell}
    intro hSOH ell hell
    have h10e : (0 : ℝ) < ((10 : ℝ) ^ ell)⁻¹ := invPow_pos ell
    have hδ : 0 < min (((10 : ℝ) ^ ell)⁻¹) (1 - (51 - 16 * Real.pi)) := lt_min h10e h1ma
    obtain ⟨k', hk'⟩ := exists_invPow_lt _ hδ
    have hk'_ell : ((10 : ℝ) ^ k')⁻¹ < ((10 : ℝ) ^ ell)⁻¹ := lt_of_lt_of_le hk' (min_le_left _ _)
    have hk'_1a : ((10 : ℝ) ^ k')⁻¹ < 1 - (51 - 16 * Real.pi) := lt_of_lt_of_le hk' (min_le_right _ _)
    have hk'1 : 1 ≤ k' := by
      by_contra hcon
      have hle : k' < 1 := lt_of_not_ge hcon
      have hk0 : k' = 0 := by omega
      rw [hk0] at hk'
      norm_num at hk'
      linarith [hk', h10e, h1ma]
    obtain ⟨n, hn_ge, ht_pos, ht_lt⟩ := hSOH k' 1 hk'1 (by norm_num)
    have hn2 : 2 ≤ n := le_trans (Nat.le_max_right 1 2) hn_ge
    have hEpos := Epos_aux n hn2
    have hEa := EltA_aux n hn2
    have hhead_lt1 : Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) < 1 :=
      Int.fract_lt_one _
    have hhead_nn : 0 ≤ Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) :=
      Int.fract_nonneg _
    -- head+E ∈ (a, a+10^{-k'}) ⊂ (0,1) since a>0, a+10^{-k'}<1 (as 10^{-k'}<1-a)
    have hsum_lt1 : Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < 1 := by
      have ht : Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - (51 - 16 * Real.pi) <
          ((10 : ℝ) ^ k')⁻¹ := ht_lt
      linarith [ht, hk'_1a, ha.1, ha.2]
      -- t+a = head+E < a+10^{-k'} < a+(1-a)=1
    have hsum_pos : 0 < Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by
      linarith [ht_pos, ha.1]
    have hv_eq : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
        Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by
      have hfr := v_headE_aux n
      have hfract_self : Int.fract (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) =
          Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
            ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by
        exact Int.fract_eq_self.mpr ⟨le_of_lt hsum_pos, hsum_lt1⟩
      linarith [hfr, hfract_self]
    -- so v ∈ (a, a+10^{-k'}) with 10^{-k'}<1-a, giving orbit = v-a <10^{-ell}
    have hv_mem : 51 - 16 * Real.pi < Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) ∧
        Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) < 51 - 16 * Real.pi + ((10 : ℝ) ^ k')⁻¹ := by
      constructor
      · linarith [hv_eq, ht_pos]
      · linarith [hv_eq, ht_lt]
    have horb_1a : Theory.PiDigits.T20.baseTenOrbit Real.pi n < 1 - (51 - 16 * Real.pi) := by
      by_contra hcon
      have hle : 1 - (51 - 16 * Real.pi) ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n :=
        le_of_not_gt hcon
      have horb_lt1 := orbitLtOne_aux n
      by_cases heq : Theory.PiDigits.T20.baseTenOrbit Real.pi n = 1 - (51 - 16 * Real.pi)
      · have hv0 : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) = 0 := by
          rw [heq]
          have h1 : (1 - (51 - 16 * Real.pi) + (51 - 16 * Real.pi) : ℝ) = 1 := by ring
          rw [h1, Int.fract_one]
        have hv2 := v_orbit_eq n
        linarith [hv2, hv0, hv_mem.1, ha.1]
      · have hlt : 1 - (51 - 16 * Real.pi) < Theory.PiDigits.T20.baseTenOrbit Real.pi n :=
          lt_of_le_of_ne hle (Ne.symm heq)
        have hsum_gt1 : 1 < Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by linarith
        have hsum_lt2 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 2 := by
          linarith [horb_lt1, ha.2]
        have hfract : Int.fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)) =
            Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) - 1 := by
          have hfl : ⌊Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi)⌋ = 1 := by
            rw [Int.floor_eq_iff]
            constructor
            · norm_num; linarith
            · norm_num; linarith
          have h := Int.floor_add_fract (Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi))
          rw [hfl] at h
          push_cast at h
          linarith
        have hv2 := v_orbit_eq n
        linarith [hv2, hfract, hv_mem.1, horb_lt1]
    have horb_eq : Theory.PiDigits.T20.baseTenOrbit Real.pi n =
        Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) - (51 - 16 * Real.pi) := by
      have hsum_lt1 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 1 := by linarith [horb_1a]
      have hsum_pos : 0 ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
        linarith [orbitPos_aux n, ha.1]
      have hfract := Int.fract_eq_self.mpr ⟨hsum_pos, hsum_lt1⟩
      have hv2 := v_orbit_eq n
      linarith [hv2, hfract]
    have horb_lt_inv : Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ ell)⁻¹ := by
      linarith [horb_eq, hv_mem.2, hk'_ell]
    exact ⟨n, orbit_imp_zeroBlock n ell hell horb_lt_inv⟩
  · -- CW0 ⇒ SOH: given k,N, take L = max N 2 + k, get n0 with L zeros, pass to suffix n = max n0 (max N 2)
    intro hCW k N hk hN
    have hN' : 1 ≤ max N 2 := le_trans hN (Nat.le_max_left N 2)
    set N' : ℕ := max N 2 with hN'def
    have hN'2 : 2 ≤ N' := Nat.le_max_right N 2
    have hL : 1 ≤ N' + k := by omega
    obtain ⟨n0, hn0⟩ := hCW (N' + k) hL
    set n : ℕ := max n0 N' with hndef
    have hn_ge_N' : N' ≤ n := Nat.le_max_right n0 N'
    have hn_ge_n0 : n0 ≤ n := Nat.le_max_left n0 N'
    have hn_ge2 : 2 ≤ n := le_trans hN'2 hn_ge_N'
    have hn_geN : max N 2 ≤ n := hn_ge_N'
    -- n has k zeros (suffix of longer block)
    have hzero_k : ∀ i : Fin k, Theory.PiDigits.piDigit (n + i.val) = 0 := by
      intro i
      have hi_lt : i.val < k := i.isLt
      have hN0_le : n0 ≤ n := hn_ge_n0
      have hn_le : n + i.val < n0 + (N' + k) := by
        have h1 : n ≤ n0 + N' := by
          have hmax : max n0 N' ≤ n0 + N' := Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
          linarith [hmax, hndef]
        omega
      have hmem : n + i.val = n0 + (n - n0 + i.val) := by omega
      have hidx_lt : n - n0 + i.val < N' + k := by omega
      have hdigit : Theory.PiDigits.piDigit (n0 + (n - n0 + i.val)) = 0 := by
        have hfin : n - n0 + i.val < N' + k := hidx_lt
        have hmem2 : ∀ j : Fin (N' + k), Theory.PiDigits.piDigit (n0 + j.val) = 0 := hn0
        exact hmem2 ⟨n - n0 + i.val, hfin⟩
      rwa [← hmem] at hdigit
    have horb_lt : Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ k)⁻¹ :=
      zeroBlock_imp_orbit n k hzero_k
    have hEpos := Epos_aux n hn_ge2
    have hEa := EltA_aux n hn_ge2
    have hhead_nn : 0 ≤ Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) :=
      Int.fract_nonneg _
    have hhead_lt1 : Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) < 1 :=
      Int.fract_lt_one _
    have h10k_1a : ((10 : ℝ) ^ k)⁻¹ ≤ 1 - (51 - 16 * Real.pi) := invPow_le_one_sub_a k hk
    have horb_1a : Theory.PiDigits.T20.baseTenOrbit Real.pi n < 1 - (51 - 16 * Real.pi) :=
      lt_of_lt_of_le horb_lt h10k_1a
    have hv_orb : Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) =
        Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
      have hsum_lt1 : Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) < 1 := by linarith [horb_1a]
      have hsum_pos : 0 ≤ Theory.PiDigits.T20.baseTenOrbit Real.pi n + (51 - 16 * Real.pi) := by
        linarith [orbitPos_aux n, ha.1]
      have hfract := Int.fract_eq_self.mpr ⟨hsum_pos, hsum_lt1⟩
      have hv := v_orbit_eq n
      linarith [hv, hfract]
    -- v = fract(head+E) ∈ (a, a+10^{-k}) with 10^{-k} ≤ 1-a, so head+E ∈ (a, a+10^{-k}) (ruling out head+E ≥ 1+a via E<a)
    have hv_mem : 51 - 16 * Real.pi < Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) ∧
        Int.fract (((10 : ℝ) ^ n - 16) * Real.pi) < 51 - 16 * Real.pi + ((10 : ℝ) ^ k)⁻¹ := by
      constructor
      · linarith [hv_orb, orbitPos_aux n]
      · have hle : Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ k)⁻¹ := horb_lt
        linarith [hv_orb, hle]
    have hfr := v_headE_aux n
    -- head+E ∈ [0,1+a) with fract ∈ (a,a+10^{-k}), so head+E ∈ (a,a+10^{-k}) (not (1+a,...))
    have hsum_range : 0 ≤ Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) ∧
        Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < 1 + (51 - 16 * Real.pi) := by
      constructor
      · linarith [hhead_nn, hEpos]
      · linarith [hhead_lt1, hEa]
        -- head<1, E<a ⇒ head+E<1+a
    have ht_pos : 0 < Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
        ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - (51 - 16 * Real.pi) ∧
        Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - (51 - 16 * Real.pi) < ((10 : ℝ) ^ k)⁻¹ := by
      have hsum_lt2 : Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < 2 := by
        linarith [hsum_range.2, ha.2]
        -- <1+a<2 since a<1
      by_cases hlt1 : Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
          ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) < 1
      · have hfract : Int.fract (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
            ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) =
            Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
              ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by
          exact Int.fract_eq_self.mpr ⟨hsum_range.1, hlt1⟩
        constructor
        · linarith [hfr, hfract, hv_mem.1]
        · linarith [hfr, hfract, hv_mem.2]
      · have hge1 : 1 ≤ Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
            ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) :=
          le_of_not_gt hlt1
        have hfract : Int.fract (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
            ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))) =
            Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
              ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) - 1 := by
          have hfl : ⌊Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
              ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1))⌋ = 1 := by
            rw [Int.floor_eq_iff]
            constructor
            · norm_num; linarith
            · norm_num; linarith [hsum_lt2]
          have h := Int.floor_add_fract (Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
              ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)))
          rw [hfl] at h
          push_cast at h
          linarith
        have hcontra : 1 + (51 - 16 * Real.pi) ≤
            Int.fract (((10 : ℝ) ^ n - 16) * bbpRealPartial (n - 1)) +
              ((10 : ℝ) ^ n - 16) * (Real.pi - bbpRealPartial (n - 1)) := by
          linarith [hfr, hfract, hv_mem.1]
        linarith [hcontra, hsum_range.2]
    exact ⟨n, hn_geN, ht_pos.1, ht_pos.2⟩

end Theory.PiDigits.T199BBPShadowPack
