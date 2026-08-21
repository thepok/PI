import TheoryLib.PiDecimalFactorComplexity.T8PiLacunaryNearReturns
import TheoryLib.PiDigits.T27FiniteExponentialCylinderCoverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A finite weighted Fourier reduction for pi's decimal factor complexity

Source: `problems/local/pi-decimal-factor-complexity.txt`
SHA-256: `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`

This file imports T8 and formalizes the finite Fejer-kernel reduction from the
strictly sufficient sibling C2 to a weighted Fourier-energy hypothesis.  It
does not prove that hypothesis, C2, C1, or canonical A1 for pi.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset Set

namespace DecimalFactorComplexity
namespace WeightedFourierReduction

abbrev phase := Theory.PiDigits.T27.phase
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-- The point of the base-ten lacunary orbit used in T8. -/
def orbitPoint (i : ℕ) : ℝ :=
  (10 : ℝ) ^ i * Real.pi

/-- T9's unnormalized lacunary exponential sum `S_h(N)`. -/
def lacunarySum (h : ℤ) (N : ℕ) : ℂ :=
  ∑ i : Fin N, phase h (orbitPoint i)

/-- The radius `10^(-n)` of T8's open near-return interval. -/
def nearReturnRadius (n : ℕ) : ℝ :=
  ((10 : ℝ) ^ n)⁻¹

/-- Half the reciprocal of `H+1`, the short Fejer averaging radius. -/
def fejerRadius (H : ℕ) : ℝ :=
  (2 * (H + 1 : ℝ))⁻¹

/-- The enlarged interval radius in the Fejer convolution. -/
def majorantRadius (n H : ℕ) : ℝ :=
  nearReturnRadius n + fejerRadius H

/-- The normalizing mass of the Fejer kernel on its short central interval. -/
def fejerMass (H : ℕ) : ℝ :=
  ∫ t in -(fejerRadius H)..fejerRadius H, fejerKernel H t

/-- T9's explicit interval-convolution majorant. -/
def intervalMajorant (n H : ℕ) (x : ℝ) : ℝ :=
  (fejerMass H)⁻¹ *
    ∫ y in -(majorantRadius n H)..majorantRadius n H,
      fejerKernel H (x - y)

/-- The triangular coefficient of frequency `h` in the Fejer kernel. -/
def fejerCoefficient (H : ℕ) (h : ℤ) : ℝ :=
  1 - (h.natAbs : ℝ) / (H + 1 : ℝ)

/-- The coefficient of frequency `h` in the explicit majorant. -/
def majorantCoefficient (n H : ℕ) (h : ℤ) : ℝ :=
  if h.natAbs ≤ H then
    (fejerMass H)⁻¹ * fejerCoefficient H h *
      (∫ y in -(majorantRadius n H)..majorantRadius n H,
        phase (-h) y).re
  else 0

/-- T9's coefficient weight after discarding the triangular factor. -/
def energyWeight (n H h : ℕ) : ℝ :=
  min (2 * nearReturnRadius n + 1 / (H + 1 : ℝ))
    (1 / (Real.pi * (h : ℝ)))

/-- T9's weighted Fourier energy `W_{n,H}(N)`. -/
def weightedFourierEnergy (n H N : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 H,
    energyWeight n H h * ‖lacunarySum (h : ℤ) N‖ ^ 2

lemma nearReturnRadius_pos (n : ℕ) : 0 < nearReturnRadius n := by
  simp [nearReturnRadius]

lemma fejerRadius_pos (H : ℕ) : 0 < fejerRadius H := by
  unfold fejerRadius
  positivity

lemma majorantRadius_pos (n H : ℕ) : 0 < majorantRadius n H := by
  exact add_pos (nearReturnRadius_pos n) (fejerRadius_pos H)

lemma exists_int_abs_sub_lt_of_circleDistance_lt {x r : ℝ}
    (h : circleDistance x < r) :
    ∃ z : ℤ, |x - (z : ℝ)| < r := by
  rcases exists_lt_of_csInf_lt (Set.range_nonempty _) h with ⟨_, ⟨z, rfl⟩, hz⟩
  exact ⟨z, hz⟩

lemma phase_int_shift (h z : ℤ) (x : ℝ) :
    phase h (x + z) = phase h x := by
  change Theory.PiDigits.T27.phase h (x + (z : ℝ)) =
    Theory.PiDigits.T27.phase h x
  rw [Theory.PiDigits.T27.phase_add_real]
  have hz : Theory.PiDigits.T27.phase h (z : ℝ) = 1 := by
    unfold Theory.PiDigits.T27.phase
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((z : ℝ) : ℂ) =
        ((h * z : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I (h * z)
  rw [hz, mul_one]

lemma fejerKernel_int_shift (H : ℕ) (z : ℤ) (x : ℝ) :
    fejerKernel H (x + z) = fejerKernel H x := by
  have hdir : Theory.PiDigits.T27.dirichletKernel H (x + z) =
      Theory.PiDigits.T27.dirichletKernel H x := by
    unfold Theory.PiDigits.T27.dirichletKernel
    apply Finset.sum_congr rfl
    intro r hr
    exact phase_int_shift (r : ℤ) z x
  unfold fejerKernel Theory.PiDigits.T27.fejerKernel
  rw [hdir]

lemma dirichletKernel_continuous (H : ℕ) :
    Continuous (Theory.PiDigits.T27.dirichletKernel H) := by
  unfold Theory.PiDigits.T27.dirichletKernel Theory.PiDigits.T27.phase
  fun_prop

lemma fejerKernel_continuous (H : ℕ) : Continuous (fejerKernel H) := by
  unfold fejerKernel Theory.PiDigits.T27.fejerKernel
  have := dirichletKernel_continuous H
  fun_prop

lemma fejerKernel_intervalIntegrable (H : ℕ) (a b : ℝ) :
    IntervalIntegrable (fejerKernel H) MeasureTheory.volume a b :=
  (fejerKernel_continuous H).intervalIntegrable a b

lemma fejerKernel_lower_on_centralInterval (H : ℕ) (t : ℝ)
    (ht : |t| ≤ fejerRadius H) :
    4 * (H + 1 : ℝ) / Real.pi ^ 2 ≤ fejerKernel H t := by
  by_cases ht0 : t = 0
  · subst t
    have hpi : 4 ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hkernel : fejerKernel H 0 = (H + 1 : ℝ) := by
      have hdir : Theory.PiDigits.T27.dirichletKernel H 0 =
          ((H + 1 : ℕ) : ℂ) := by
        simp [Theory.PiDigits.T27.dirichletKernel, Theory.PiDigits.T27.phase]
      unfold fejerKernel Theory.PiDigits.T27.fejerKernel
      rw [hdir]
      rw [Complex.norm_natCast]
      field_simp
      push_cast
      rfl
    rw [hkernel]
    exact (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2 (by
      nlinarith [show 0 < (H + 1 : ℝ) by positivity])
  · have habst : 0 < |t| := abs_pos.mpr ht0
    have heta : fejerRadius H = 1 / (2 * (H + 1 : ℝ)) := by
      rw [fejerRadius, inv_eq_one_div]
    have harg0 : 0 ≤ Real.pi * (H + 1 : ℝ) * |t| := by positivity
    have harg1 : Real.pi * (H + 1 : ℝ) * |t| ≤ Real.pi / 2 := by
      rw [heta] at ht
      have hH : 0 < (H + 1 : ℝ) := by positivity
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2)).2
      calc
        (Real.pi * (H + 1 : ℝ) * |t|) * 2 =
            Real.pi * (2 * (H + 1 : ℝ) * |t|) := by ring
        _ ≤ Real.pi * 1 := by
          gcongr
          simpa [mul_comm] using
            ((le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (H + 1 : ℝ))).mp ht)
        _ = Real.pi := mul_one _
    have hsinLower := Real.mul_le_sin harg0 harg1
    have hsinAbs :
        |Real.sin (Real.pi * (H + 1 : ℝ) * t)| =
          Real.sin (Real.pi * (H + 1 : ℝ) * |t|) := by
      have hbound : |Real.pi * (H + 1 : ℝ) * t| ≤ Real.pi := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (H + 1 : ℝ))]
        linarith [Real.pi_pos]
      rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hbound]
      congr 1
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (H + 1 : ℝ))]
    have hnum :
        4 * (H + 1 : ℝ) * |t| ≤
          ‖1 - Theory.PiDigits.T27.phase 1 t ^ (H + 1)‖ := by
      have hphase : Theory.PiDigits.T27.phase 1 ((H + 1 : ℝ) * t) =
          Theory.PiDigits.T27.phase 1 t ^ (H + 1) := by
        rw [← Theory.PiDigits.T27.phase_nat_eq_pow]
        unfold Theory.PiDigits.T27.phase
        congr 1
        push_cast
        ring
      rw [← hphase, Theory.PiDigits.T27.norm_one_sub_phase_one]
      rw [show Real.pi * ((H + 1 : ℝ) * t) =
          Real.pi * (H + 1 : ℝ) * t by ring]
      rw [hsinAbs]
      convert (mul_le_mul_of_nonneg_left hsinLower (by norm_num : (0 : ℝ) ≤ 2)) using 1
      · field_simp [Real.pi_ne_zero]
        ring
    have hden :
        ‖1 - Theory.PiDigits.T27.phase 1 t‖ ≤ 2 * Real.pi * |t| := by
      rw [Theory.PiDigits.T27.norm_one_sub_phase_one]
      calc
        2 * |Real.sin (Real.pi * t)| ≤ 2 * |Real.pi * t| := by
          exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
        _ = 2 * Real.pi * |t| := by
          rw [abs_mul, abs_of_pos Real.pi_pos]
          ring
    have hproduct :
        ‖Theory.PiDigits.T27.dirichletKernel H t‖ *
            ‖1 - Theory.PiDigits.T27.phase 1 t‖ =
          ‖1 - Theory.PiDigits.T27.phase 1 t ^ (H + 1)‖ := by
      rw [← norm_mul, Theory.PiDigits.T27.dirichletKernel_mul_one_sub]
    have hnorm :
        2 * (H + 1 : ℝ) / Real.pi ≤
          ‖Theory.PiDigits.T27.dirichletKernel H t‖ := by
      have hscaled :
          4 * (H + 1 : ℝ) * |t| ≤
            ‖Theory.PiDigits.T27.dirichletKernel H t‖ *
              (2 * Real.pi * |t|) := by
        calc
          _ ≤ ‖1 - Theory.PiDigits.T27.phase 1 t ^ (H + 1)‖ := hnum
          _ = ‖Theory.PiDigits.T27.dirichletKernel H t‖ *
                ‖1 - Theory.PiDigits.T27.phase 1 t‖ := hproduct.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      have hpos : 0 < 2 * Real.pi * |t| := mul_pos (mul_pos (by norm_num) Real.pi_pos) habst
      apply (le_of_mul_le_mul_right ?_ hpos)
      calc
        (2 * (H + 1 : ℝ) / Real.pi) * (2 * Real.pi * |t|) =
            4 * (H + 1 : ℝ) * |t| := by
          field_simp [Real.pi_ne_zero]
          norm_num
        _ ≤ _ := hscaled
    unfold fejerKernel Theory.PiDigits.T27.fejerKernel
    have hH : 0 < (H + 1 : ℝ) := by positivity
    have hsquare :
        (2 * (H + 1 : ℝ) / Real.pi) ^ 2 ≤
          ‖Theory.PiDigits.T27.dirichletKernel H t‖ ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hnorm
    calc
      4 * (H + 1 : ℝ) / Real.pi ^ 2 =
          (2 * (H + 1 : ℝ) / Real.pi) ^ 2 / (H + 1 : ℝ) := by
        field_simp [Real.pi_ne_zero]
        ring
      _ ≤ ‖Theory.PiDigits.T27.dirichletKernel H t‖ ^ 2 / (H + 1 : ℝ) :=
        div_le_div_of_nonneg_right hsquare hH.le

theorem four_div_pi_sq_le_fejerMass (H : ℕ) :
    4 / Real.pi ^ 2 ≤ fejerMass H := by
  let c : ℝ := 4 * (H + 1 : ℝ) / Real.pi ^ 2
  have hab : -(fejerRadius H) ≤ fejerRadius H := by
    linarith [fejerRadius_pos H]
  have hconst : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume
      (-(fejerRadius H)) (fejerRadius H) :=
    continuous_const.intervalIntegrable _ _
  have hkernel := fejerKernel_intervalIntegrable H (-(fejerRadius H)) (fejerRadius H)
  have hmono :
      (∫ _t in -(fejerRadius H)..fejerRadius H, c) ≤
        ∫ t in -(fejerRadius H)..fejerRadius H, fejerKernel H t := by
    apply intervalIntegral.integral_mono_on hab hconst hkernel
    intro t ht
    exact fejerKernel_lower_on_centralInterval H t (by
      rw [Set.mem_Icc] at ht
      rw [abs_le]
      exact ht)
  rw [intervalIntegral.integral_const] at hmono
  change _ ≤ fejerMass H
  calc
    4 / Real.pi ^ 2 = (fejerRadius H - -fejerRadius H) * c := by
      dsimp [c]
      rw [fejerRadius, inv_eq_one_div]
      field_simp [Real.pi_ne_zero]
      ring
    _ = (fejerRadius H - -fejerRadius H) • c := by rw [smul_eq_mul]
    _ ≤ fejerMass H := hmono

theorem fejerMass_pos (H : ℕ) : 0 < fejerMass H := by
  exact (div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)).trans_le
    (four_div_pi_sq_le_fejerMass H)

theorem inv_fejerMass_le (H : ℕ) :
    (fejerMass H)⁻¹ ≤ Real.pi ^ 2 / 4 := by
  have hm := four_div_pi_sq_le_fejerMass H
  have hleft : 0 < 4 / Real.pi ^ 2 := div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
  calc
    (fejerMass H)⁻¹ ≤ (4 / Real.pi ^ 2)⁻¹ :=
      (inv_le_inv₀ (fejerMass_pos H) hleft).2 hm
    _ = Real.pi ^ 2 / 4 := by field_simp [Real.pi_ne_zero]

lemma shiftedFejer_intervalIntegrable (H : ℕ) (x a b : ℝ) :
    IntervalIntegrable (fun y => fejerKernel H (x - y))
      MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  have hk := fejerKernel_continuous H
  fun_prop

theorem intervalMajorant_nonneg (n H : ℕ) (x : ℝ) :
    0 ≤ intervalMajorant n H x := by
  unfold intervalMajorant
  exact mul_nonneg (inv_nonneg.mpr (fejerMass_pos H).le)
    (intervalIntegral.integral_nonneg_of_forall
      (by linarith [majorantRadius_pos n H])
      (fun y => Theory.PiDigits.T27.fejerKernel_nonneg H (x - y)))

lemma shortIntegral_eq_fejerMass (H : ℕ) (x : ℝ) (z : ℤ) :
    (∫ y in (x - z) - fejerRadius H..(x - z) + fejerRadius H,
      fejerKernel H (x - y)) = fejerMass H := by
  have hpoint : ∀ y : ℝ,
      fejerKernel H (x - y) = fejerKernel H ((x - z) - y) := by
    intro y
    symm
    rw [show x - y = ((x - z) - y) + z by ring,
      fejerKernel_int_shift]
  calc
    (∫ y in (x - z) - fejerRadius H..(x - z) + fejerRadius H,
        fejerKernel H (x - y)) =
        ∫ y in (x - z) - fejerRadius H..(x - z) + fejerRadius H,
          fejerKernel H ((x - z) - y) := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact hpoint y
    _ = ∫ t in (x - z) - ((x - z) + fejerRadius H)..
          (x - z) - ((x - z) - fejerRadius H), fejerKernel H t := by
            rw [intervalIntegral.integral_comp_sub_left]
    _ = fejerMass H := by
      congr 1 <;> ring

theorem intervalMajorant_ge_one_of_nearReturn
    (n H : ℕ) (x : ℝ) (hx : circleDistance x < nearReturnRadius n) :
    1 ≤ intervalMajorant n H x := by
  obtain ⟨z, hz⟩ := exists_int_abs_sub_lt_of_circleDistance_lt hx
  have hzu : -(nearReturnRadius n) < x - z := (abs_lt.mp hz).1
  have huz : x - z < nearReturnRadius n := (abs_lt.mp hz).2
  have hca : -(majorantRadius n H) ≤ (x - z) - fejerRadius H := by
    unfold majorantRadius
    linarith
  have hab : (x - z) - fejerRadius H ≤ (x - z) + fejerRadius H := by
    linarith [fejerRadius_pos H]
  have hbd : (x - z) + fejerRadius H ≤ majorantRadius n H := by
    unfold majorantRadius
    linarith
  have hmono : fejerMass H ≤
      ∫ y in -(majorantRadius n H)..majorantRadius n H,
        fejerKernel H (x - y) := by
    rw [← shortIntegral_eq_fejerMass H x z]
    apply intervalIntegral.integral_mono_interval hca hab hbd
    · filter_upwards [] with y
      exact Theory.PiDigits.T27.fejerKernel_nonneg H (x - y)
    · exact shiftedFejer_intervalIntegrable H x _ _
  unfold intervalMajorant
  calc
    1 = (fejerMass H)⁻¹ * fejerMass H := by
      rw [inv_mul_cancel₀ (fejerMass_pos H).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (fejerMass_pos H).le)

/-- Pointwise majorization of T8's strict circle interval by the explicit
finite Fejer convolution. -/
theorem nearReturnIndicator_le_intervalMajorant (n H : ℕ) (x : ℝ) :
    (if circleDistance x < nearReturnRadius n then 1 else 0 : ℝ) ≤
      intervalMajorant n H x := by
  split_ifs with hx
  · exact intervalMajorant_ge_one_of_nearReturn n H x hx
  · exact intervalMajorant_nonneg n H x

lemma integral_phase_neg_formula {h : ℤ} (hh : h ≠ 0) (a : ℝ) :
    (∫ y in -a..a, phase (-h) y) =
      (Complex.exp
          ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * (a : ℂ)) -
        Complex.exp
          ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * ((-a : ℝ) : ℂ))) /
        (2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) := by
  have hc : 2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      · exact Complex.I_ne_zero
    · simpa using (Int.cast_ne_zero.mpr (neg_ne_zero.mpr hh) : ((-h : ℤ) : ℂ) ≠ 0)
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)
  have hc' : c ≠ 0 := hc
  have hphase : (fun y : ℝ => phase (-h) y) =
      fun y : ℝ => Complex.exp (c * y) := by
    funext y
    unfold phase Theory.PiDigits.T27.phase c
    congr 1
    push_cast
    ring
  rw [hphase]
  have D : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
        (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc']
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using
      ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
  rw [intervalIntegral.integral_deriv_eq_sub' _
    (funext fun x => (D x).deriv) (fun x _ => (D x).differentiableAt)]
  · dsimp [c]
    ring
  · fun_prop

lemma norm_integral_phase_le_length (h : ℤ) {a : ℝ} (ha : 0 ≤ a) :
    ‖∫ y in -a..a, phase h y‖ ≤ 2 * a := by
  calc
    ‖∫ y in -a..a, phase h y‖ ≤
        ∫ y in -a..a, ‖phase h y‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = 2 * a := by
      simp [Theory.PiDigits.T27.norm_phase]
      ring

lemma norm_integral_phase_neg_le_frequency {h : ℤ} (hh : h ≠ 0) (a : ℝ) :
    ‖∫ y in -a..a, phase (-h) y‖ ≤
      1 / (Real.pi * (h.natAbs : ℝ)) := by
  rw [integral_phase_neg_formula hh]
  have hnum :
      ‖Complex.exp
          ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * (a : ℂ)) -
        Complex.exp
          ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * ((-a : ℝ) : ℂ))‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp
            ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * (a : ℂ))‖ +
          ‖Complex.exp
            ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * ((-a : ℝ) : ℂ))‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        norm_num
  have hden :
      ‖2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)‖ =
        2 * Real.pi * (h.natAbs : ℝ) := by
    have habs : |(h : ℝ)| = (h.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_neg,
      Complex.norm_intCast]
    rw [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, habs]
    ring
  rw [norm_div, hden]
  have hpos : 0 < Real.pi * (h.natAbs : ℝ) := by
    apply mul_pos Real.pi_pos
    exact_mod_cast Int.natAbs_pos.mpr hh
  calc
    ‖Complex.exp
          ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * (a : ℂ)) -
        Complex.exp
          ((2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) * ((-a : ℝ) : ℂ))‖ /
          (2 * Real.pi * (h.natAbs : ℝ)) ≤
        2 / (2 * Real.pi * (h.natAbs : ℝ)) := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / (Real.pi * (h.natAbs : ℝ)) := by field_simp

lemma abs_integral_phase_neg_re_le {h : ℤ} (hh : h ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    |(∫ y in -a..a, phase (-h) y).re| ≤
      min (2 * a) (1 / (Real.pi * (h.natAbs : ℝ))) := by
  rw [le_min_iff]
  constructor
  · exact (Complex.abs_re_le_norm _).trans (norm_integral_phase_le_length (-h) ha)
  · exact (Complex.abs_re_le_norm _).trans (norm_integral_phase_neg_le_frequency hh a)

lemma fejerCoefficient_nonneg {H : ℕ} {h : ℤ} (hh : h.natAbs ≤ H) :
    0 ≤ fejerCoefficient H h := by
  unfold fejerCoefficient
  have hden : 0 < (H + 1 : ℝ) := by positivity
  rw [sub_nonneg, div_le_one hden]
  exact_mod_cast (hh.trans (Nat.le_add_right H 1))

lemma fejerCoefficient_le_one (H : ℕ) (h : ℤ) :
    fejerCoefficient H h ≤ 1 := by
  unfold fejerCoefficient
  exact sub_le_self _ (div_nonneg (by positivity) (by positivity))

lemma two_mul_majorantRadius (n H : ℕ) :
    2 * majorantRadius n H =
      2 * nearReturnRadius n + 1 / (H + 1 : ℝ) := by
  unfold majorantRadius fejerRadius
  rw [inv_eq_one_div]
  field_simp

@[simp] theorem majorantCoefficient_zero (n H : ℕ) :
    majorantCoefficient n H 0 =
      2 * majorantRadius n H / fejerMass H := by
  have hzero : (0 : ℤ).natAbs ≤ H := by simp
  rw [majorantCoefficient, if_pos hzero]
  have hint :
      (∫ y in -majorantRadius n H..majorantRadius n H, phase 0 y).re =
        2 * majorantRadius n H := by
    simp [phase, Theory.PiDigits.T27.phase,
      intervalIntegral.integral_const]
    ring
  rw [show -(0 : ℤ) = 0 by rfl, hint]
  simp [fejerCoefficient, div_eq_mul_inv]
  ring

theorem majorantCoefficient_zero_le (n H : ℕ) :
    majorantCoefficient n H 0 ≤
      Real.pi ^ 2 / 2 * nearReturnRadius n +
        Real.pi ^ 2 / (4 * (H + 1 : ℝ)) := by
  rw [majorantCoefficient_zero, div_eq_mul_inv, mul_comm]
  have hr : 0 ≤ 2 * majorantRadius n H :=
    mul_nonneg (by norm_num) (majorantRadius_pos n H).le
  calc
    (fejerMass H)⁻¹ * (2 * majorantRadius n H) ≤
        (Real.pi ^ 2 / 4) * (2 * majorantRadius n H) := by
      exact mul_le_mul_of_nonneg_right (inv_fejerMass_le H) hr
    _ = Real.pi ^ 2 / 2 * nearReturnRadius n +
        Real.pi ^ 2 / (4 * (H + 1 : ℝ)) := by
      rw [two_mul_majorantRadius]
      field_simp
      ring

theorem abs_majorantCoefficient_le {n H : ℕ} {h : ℤ}
    (hh0 : h ≠ 0) (hhH : h.natAbs ≤ H) :
    |majorantCoefficient n H h| ≤
      Real.pi ^ 2 / 4 *
        min (2 * nearReturnRadius n + 1 / (H + 1 : ℝ))
          (1 / (Real.pi * (h.natAbs : ℝ))) := by
  rw [majorantCoefficient, if_pos hhH, abs_mul, abs_mul,
    abs_of_pos (inv_pos.mpr (fejerMass_pos H)),
    abs_of_nonneg (fejerCoefficient_nonneg hhH)]
  have hi := abs_integral_phase_neg_re_le hh0 (majorantRadius_pos n H).le
  rw [two_mul_majorantRadius] at hi
  have hcoeff0 := fejerCoefficient_nonneg hhH
  have habs0 : 0 ≤
      |(∫ y in -majorantRadius n H..majorantRadius n H, phase (-h) y).re| :=
    abs_nonneg _
  have hmin0 : 0 ≤
      min (2 * nearReturnRadius n + 1 / (H + 1 : ℝ))
        (1 / (Real.pi * (h.natAbs : ℝ))) := hi.trans' habs0
  calc
    (fejerMass H)⁻¹ * fejerCoefficient H h *
        |(∫ y in -majorantRadius n H..majorantRadius n H, phase (-h) y).re| ≤
      (Real.pi ^ 2 / 4) * fejerCoefficient H h *
        |(∫ y in -majorantRadius n H..majorantRadius n H, phase (-h) y).re| := by
      have hbase : (fejerMass H)⁻¹ * fejerCoefficient H h ≤
          (Real.pi ^ 2 / 4) * fejerCoefficient H h :=
        mul_le_mul_of_nonneg_right (inv_fejerMass_le H) hcoeff0
      exact mul_le_mul_of_nonneg_right hbase habs0
    _ ≤ (Real.pi ^ 2 / 4) * 1 *
        |(∫ y in -majorantRadius n H..majorantRadius n H, phase (-h) y).re| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fejerCoefficient_le_one H h) (by positivity)) habs0
    _ ≤ (Real.pi ^ 2 / 4) * 1 *
        min (2 * nearReturnRadius n + 1 / (H + 1 : ℝ))
          (1 / (Real.pi * (h.natAbs : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

lemma phase_neg_real (h : ℤ) (x : ℝ) :
    phase h (-x) = conj (phase h x) := by
  rw [show phase h (-x) = phase (-h) x by
    unfold phase Theory.PiDigits.T27.phase
    congr 1
    push_cast
    ring]
  exact Theory.PiDigits.T27.phase_neg h x

lemma phase_real_sub (h : ℤ) (x y : ℝ) :
    phase h (x - y) = phase h x * conj (phase h y) := by
  change Theory.PiDigits.T27.phase h (x - y) =
    Theory.PiDigits.T27.phase h x * conj (Theory.PiDigits.T27.phase h y)
  rw [show x - y = x + (-y) by ring,
    Theory.PiDigits.T27.phase_add_real]
  congr 1
  exact phase_neg_real h y

/-- The exact ordered-pair identity. Both orders and all diagonal pairs are
present; no factor of two is inserted. -/
theorem orderedPair_phase_identity {N : ℕ} (x : Fin N → ℝ) (h : ℤ) :
    ∑ ij : Fin N × Fin N, phase h (x ij.2 - x ij.1) =
      ((‖∑ i : Fin N, phase h (x i)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  simp_rw [phase_real_sub]
  rw [Fintype.sum_prod_type]
  change (∑ i : Fin N, ∑ j : Fin N,
      phase h (x j) * conj (phase h (x i))) = _
  calc
    (∑ i : Fin N, ∑ j : Fin N,
        phase h (x j) * conj (phase h (x i))) =
        ∑ i : Fin N, (∑ j : Fin N, phase h (x j)) *
          conj (phase h (x i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_mul]
    _ = (∑ j : Fin N, phase h (x j)) *
        (∑ i : Fin N, conj (phase h (x i))) := by
          rw [Finset.mul_sum]
    _ = (∑ j : Fin N, phase h (x j)) *
        conj (∑ i : Fin N, phase h (x i)) := by rw [map_sum]
    _ = ((‖∑ i : Fin N, phase h (x i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]

theorem pi_orderedPair_phase_identity (N : ℕ) (h : ℤ) :
    ∑ ij : Fin N × Fin N,
        phase h
          (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) =
      ((‖lacunarySum h N‖ ^ 2 : ℝ) : ℂ) := by
  convert orderedPair_phase_identity (fun i : Fin N => orbitPoint i) h using 1
  · apply Finset.sum_congr rfl
    intro ij hij
    congr 1
    simp only [orbitPoint]
    ring

theorem Q_pi_le_majorantPairSum (n H N : ℕ) :
    (Q_pi n N : ℝ) ≤
      ∑ ij : Fin N × Fin N,
        intervalMajorant n H
          (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) := by
  classical
  have hcard : (Q_pi n N : ℝ) =
      ∑ ij : Fin N × Fin N,
        (if circleDistance
            (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
              nearReturnRadius n then 1 else 0 : ℝ) := by
    unfold Q_pi piNearReturnPairs
    norm_cast
    simp [nearReturnRadius]
  rw [hcard]
  apply Finset.sum_le_sum
  intro ij hij
  exact nearReturnIndicator_le_intervalMajorant n H _

/-- A nonnegative weight of the absolute difference of two indices is bounded
by one copy of its zero value and two copies of each positive value per row. -/
theorem pairDifference_sum_le (H : ℕ) (g : ℕ → ℝ) (hg : ∀ h, 0 ≤ g h) :
    (∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
        g (Int.natAbs ((s : ℤ) - r))) ≤
      (H + 1 : ℝ) * (g 0 + 2 * ∑ h ∈ Icc 1 H, g h) := by
  classical
  have sum_inj_le {A B : Finset ℕ} (f : ℕ → ℕ) (hf : Set.InjOn f A)
      (hAB : ∀ a ∈ A, f a ∈ B) :
      (∑ a ∈ A, g (f a)) ≤ ∑ b ∈ B, g b := by
    calc
      (∑ a ∈ A, g (f a)) = ∑ b ∈ A.image f, g b := (sum_image hf).symm
      _ ≤ ∑ b ∈ B, g b := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact image_subset_iff.mpr hAB
        · intro b _ _
          exact hg b
  have row_bound (r : ℕ) (hr : r ∈ range (H + 1)) :
      (∑ s ∈ range (H + 1), g (Int.natAbs ((s : ℤ) - r))) ≤
        g 0 + 2 * ∑ h ∈ Icc 1 H, g h := by
    let S := range (H + 1)
    let L := S.filter fun s => s < r
    let U := S.filter fun s => r < s
    have hrH : r ≤ H := by simpa [Finset.mem_range] using hr
    have term_split (s : ℕ) :
        g (Int.natAbs ((s : ℤ) - r)) =
          (if s = r then g 0 else 0) +
            (if s < r then g (r - s) else 0) +
              (if r < s then g (s - r) else 0) := by
      rcases lt_trichotomy s r with hsr | hsr | hrs
      · simp [hsr, hsr.ne, not_lt_of_ge hsr.le,
          Int.natAbs_natCast_sub_natCast_of_le hsr.le]
      · subst s
        simp
      · simp [hrs, hrs.ne', not_lt_of_ge hrs.le,
          Int.natAbs_natCast_sub_natCast_of_ge hrs.le]
    have split_sum :
        (∑ s ∈ S, g (Int.natAbs ((s : ℤ) - r))) =
          g 0 + (∑ s ∈ L, g (r - s)) + ∑ s ∈ U, g (s - r) := by
      calc
        (∑ s ∈ S, g (Int.natAbs ((s : ℤ) - r))) =
            ∑ s ∈ S,
              ((if s = r then g 0 else 0) +
                (if s < r then g (r - s) else 0) +
                  (if r < s then g (s - r) else 0)) := by
                    apply sum_congr rfl
                    intro s _
                    exact term_split s
        _ = g 0 + (∑ s ∈ L, g (r - s)) + ∑ s ∈ U, g (s - r) := by
          rw [sum_add_distrib, sum_add_distrib]
          simp [L, U, S, hr]
          rw [sum_filter, sum_filter]
    have lower_le : (∑ s ∈ L, g (r - s)) ≤ ∑ h ∈ Icc 1 H, g h := by
      apply sum_inj_le (fun s => r - s)
      · intro a ha b hb hab
        have ha' : a ∈ S ∧ a < r := by simpa [L] using ha
        have hb' : b ∈ S ∧ b < r := by simpa [L] using hb
        calc
          a = r - (r - a) := (Nat.sub_sub_self ha'.2.le).symm
          _ = r - (r - b) := congrArg (r - ·) hab
          _ = b := Nat.sub_sub_self hb'.2.le
      · intro s hs
        simp only [L, Finset.mem_filter, S, Finset.mem_range] at hs
        simp only [Finset.mem_Icc]
        omega
    have upper_le : (∑ s ∈ U, g (s - r)) ≤ ∑ h ∈ Icc 1 H, g h := by
      apply sum_inj_le (fun s => s - r)
      · intro a ha b hb hab
        have ha' : a ∈ S ∧ r < a := by simpa [U] using ha
        have hb' : b ∈ S ∧ r < b := by simpa [U] using hb
        calc
          a = (a - r) + r := (Nat.sub_add_cancel ha'.2.le).symm
          _ = (b - r) + r := congrArg (· + r) hab
          _ = b := Nat.sub_add_cancel hb'.2.le
      · intro s hs
        simp only [U, Finset.mem_filter, S, Finset.mem_range] at hs
        simp only [Finset.mem_Icc]
        omega
    rw [show range (H + 1) = S from rfl, split_sum]
    linarith
  calc
    (∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
        g (Int.natAbs ((s : ℤ) - r))) ≤
        ∑ r ∈ range (H + 1), (g 0 + 2 * ∑ h ∈ Icc 1 H, g h) := by
          apply sum_le_sum
          intro r hr
          exact row_bound r hr
    _ = (H + 1 : ℝ) * (g 0 + 2 * ∑ h ∈ Icc 1 H, g h) := by
      simp
      ring

/-- The integral of one Fourier mode after summing over all ordered orbit
pairs. -/
theorem pi_orderedPair_integral_phase_identity (N : ℕ) (h : ℤ) (a : ℝ) :
    ∑ ij : Fin N × Fin N,
        ∫ y in -a..a,
          (phase h
            ((((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) - y)).re =
      (∫ y in -a..a, phase (-h) y).re * ‖lacunarySum h N‖ ^ 2 := by
  classical
  have hpairIntegrable : ∀ ij ∈ (Finset.univ : Finset (Fin N × Fin N)),
      IntervalIntegrable
        (fun y : ℝ =>
          (phase h
            ((((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) - y)).re)
        MeasureTheory.volume (-a) a := by
    intro ij hij
    apply Continuous.intervalIntegrable
    simp only [phase]
    unfold Theory.PiDigits.T27.phase
    fun_prop
  rw [← intervalIntegral.integral_finsetSum hpairIntegrable]
  have hpoint (y : ℝ) :
      (∑ ij : Fin N × Fin N,
          (phase h
            ((((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) - y)).re) =
        ‖lacunarySum h N‖ ^ 2 * (phase (-h) y).re := by
    have hcomplex :
        (∑ ij : Fin N × Fin N,
            phase h
              ((((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) - y)) =
          ((‖lacunarySum h N‖ ^ 2 : ℝ) : ℂ) * phase (-h) y := by
      simp_rw [phase_real_sub]
      rw [← Finset.sum_mul, pi_orderedPair_phase_identity,
        ← Theory.PiDigits.T27.phase_neg]
    calc
      (∑ ij : Fin N × Fin N,
          (phase h
            ((((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) - y)).re) =
          (∑ ij : Fin N × Fin N,
            phase h
              ((((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) - y)).re := by
            simpa only [Complex.reCLM_apply] using
              (map_sum Complex.reCLM _ Finset.univ).symm
      _ = (((‖lacunarySum h N‖ ^ 2 : ℝ) : ℂ) * phase (-h) y).re :=
        congrArg Complex.re hcomplex
      _ = _ := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
  rw [intervalIntegral.integral_congr (fun y _ => hpoint y)]
  rw [intervalIntegral.integral_const_mul]
  have hint : IntervalIntegrable (fun y : ℝ => phase (-h) y)
      MeasureTheory.volume (-a) a := by
    apply Continuous.intervalIntegrable
    unfold phase Theory.PiDigits.T27.phase
    fun_prop
  have hmap := Complex.reCLM.intervalIntegral_comp_comm hint
  simp only [Complex.reCLM_apply] at hmap
  rw [hmap]
  ring

/-- Exact expansion of the majorant pair sum into the ordered frequency
differences of the finite Fejer kernel. -/
theorem majorantPairSum_eq_doubleFrequencySum (n H N : ℕ) :
    (∑ ij : Fin N × Fin N,
        intervalMajorant n H
          (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi)) =
      (fejerMass H)⁻¹ / (H + 1 : ℝ) *
        ∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
          (∫ y in -(majorantRadius n H)..majorantRadius n H,
            phase (-((s : ℤ) - r)) y).re *
              ‖lacunarySum ((s : ℤ) - r) N‖ ^ 2 := by
  classical
  have hkernel (x : ℝ) :
      (∫ y in -(majorantRadius n H)..majorantRadius n H,
          fejerKernel H (x - y)) =
        (∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
          ∫ y in -(majorantRadius n H)..majorantRadius n H,
            (phase ((s : ℤ) - r) (x - y)).re) / (H + 1 : ℝ) := by
    simp_rw [Theory.PiDigits.T27.fejerKernel_eq_doubleSum]
    simp only [← Complex.reCLM_apply, map_sum]
    rw [intervalIntegral.integral_div]
    congr 1
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro r hr
      rw [intervalIntegral.integral_finsetSum]
      intro s hs
      apply Continuous.intervalIntegrable
      unfold Theory.PiDigits.T27.phase
      fun_prop
    · intro r hr
      apply Continuous.intervalIntegrable
      unfold Theory.PiDigits.T27.phase
      fun_prop
  simp_rw [intervalMajorant, hkernel]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_div]
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply congrArg (· / (H + 1 : ℝ))
  apply congrArg ((fejerMass H)⁻¹ * ·)
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  exact pi_orderedPair_integral_phase_identity N ((s : ℤ) - r)
    (majorantRadius n H)

/-- T9's explicit finite Fourier reduction with the stated constants. -/
theorem Q_pi_explicit_bound (n H N : ℕ) :
    (Q_pi n N : ℝ) ≤
      (Real.pi^2/2 * nearReturnRadius n + Real.pi^2/(4*(H+1:ℝ))) * (N:ℝ)^2 +
        Real.pi^2/2 * weightedFourierEnergy n H N := by
  classical
  let g : ℕ → ℝ := fun h =>
    if h = 0 then 2 * majorantRadius n H * (N : ℝ) ^ 2
    else energyWeight n H h * ‖lacunarySum (h : ℤ) N‖ ^ 2
  have hg : ∀ h, 0 ≤ g h := by
    intro h
    simp only [g]
    split_ifs with hh
    · exact mul_nonneg (mul_nonneg (by norm_num) (majorantRadius_pos n H).le)
        (sq_nonneg _)
    · have hhpos : 0 < (h : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hh
      apply mul_nonneg
      · apply le_min
        · exact add_nonneg
            (mul_nonneg (by norm_num) (nearReturnRadius_pos n).le)
            (div_nonneg (by norm_num) (by positivity))
        · exact div_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le hhpos.le)
      · exact sq_nonneg _
  have hfrequency (r s : ℕ) (hr : r ∈ range (H + 1))
      (hs : s ∈ range (H + 1)) :
      (∫ y in -(majorantRadius n H)..majorantRadius n H,
          phase (-((s : ℤ) - r)) y).re *
            ‖lacunarySum ((s : ℤ) - r) N‖ ^ 2 ≤
        g (Int.natAbs ((s : ℤ) - r)) := by
    by_cases hrs : s = r
    · subst s
      have hzeroSum : lacunarySum 0 N = (N : ℂ) := by
        simp [lacunarySum, phase, Theory.PiDigits.T27.phase]
      rw [sub_self]
      simp only [neg_zero, hzeroSum, Complex.norm_natCast]
      simp [g, phase, Theory.PiDigits.T27.phase, intervalIntegral.integral_const]
      ring_nf
      exact le_rfl
    · have hk0 : (s : ℤ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hrs)
      have hkH : Int.natAbs ((s : ℤ) - r) ≤ H := by
        have hr' : r ≤ H := by simpa [Finset.mem_range] using hr
        have hs' : s ≤ H := by simpa [Finset.mem_range] using hs
        omega
      have hint := abs_integral_phase_neg_re_le hk0 (majorantRadius_pos n H).le
      rw [two_mul_majorantRadius] at hint
      have hcast :
          energyWeight n H (Int.natAbs ((s : ℤ) - r)) =
            min (2 * nearReturnRadius n + 1 / (H + 1 : ℝ))
              (1 / (Real.pi * (Int.natAbs ((s : ℤ) - r) : ℝ))) := rfl
      have hsumNorm :
          ‖lacunarySum ((Int.natAbs ((s : ℤ) - r) : ℕ) : ℤ) N‖ =
            ‖lacunarySum ((s : ℤ) - r) N‖ := by
        by_cases hk : 0 ≤ (s : ℤ) - r
        · rw [Int.natAbs_of_nonneg hk]
        · have hneg : (s : ℤ) - r < 0 := lt_of_not_ge hk
          have heq := Int.eq_neg_natAbs_of_nonpos hneg.le
          have hconj :
              lacunarySum (-((Int.natAbs ((s : ℤ) - r) : ℕ) : ℤ)) N =
                conj (lacunarySum ((Int.natAbs ((s : ℤ) - r) : ℕ) : ℤ) N) := by
            unfold lacunarySum
            simp_rw [Theory.PiDigits.T27.phase_neg]
            rw [map_sum]
          calc
            ‖lacunarySum ((Int.natAbs ((s : ℤ) - r) : ℕ) : ℤ) N‖ =
                ‖conj (lacunarySum ((Int.natAbs ((s : ℤ) - r) : ℕ) : ℤ) N)‖ :=
              (Complex.norm_conj _).symm
            _ = ‖lacunarySum (-((Int.natAbs ((s : ℤ) - r) : ℕ) : ℤ)) N‖ := by
              rw [hconj]
            _ = _ := (congrArg (fun q : ℤ => ‖lacunarySum q N‖) heq).symm
      simp only [g, if_neg (Int.natAbs_ne_zero.mpr hk0), hcast, hsumNorm]
      exact mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) hint) (sq_nonneg _)
  calc
    (Q_pi n N : ℝ) ≤ ∑ ij : Fin N × Fin N,
        intervalMajorant n H
          (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) :=
      Q_pi_le_majorantPairSum n H N
    _ = (fejerMass H)⁻¹ / (H + 1 : ℝ) *
        ∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
          (∫ y in -(majorantRadius n H)..majorantRadius n H,
            phase (-((s : ℤ) - r)) y).re *
              ‖lacunarySum ((s : ℤ) - r) N‖ ^ 2 :=
      majorantPairSum_eq_doubleFrequencySum n H N
    _ ≤ (fejerMass H)⁻¹ / (H + 1 : ℝ) *
        ∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
          g (Int.natAbs ((s : ℤ) - r)) := by
      apply mul_le_mul_of_nonneg_left
      · apply sum_le_sum
        intro r hr
        apply sum_le_sum
        intro s hs
        exact hfrequency r s hr hs
      · exact div_nonneg (inv_nonneg.mpr (fejerMass_pos H).le) (by positivity)
    _ ≤ (fejerMass H)⁻¹ *
        (g 0 + 2 * ∑ h ∈ Icc 1 H, g h) := by
      have hpairs := pairDifference_sum_le H g hg
      have hmass : 0 ≤ (fejerMass H)⁻¹ := inv_nonneg.mpr (fejerMass_pos H).le
      calc
        (fejerMass H)⁻¹ / (H + 1 : ℝ) *
            ∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
              g (Int.natAbs ((s : ℤ) - r)) ≤
            (fejerMass H)⁻¹ / (H + 1 : ℝ) *
              ((H + 1 : ℝ) * (g 0 + 2 * ∑ h ∈ Icc 1 H, g h)) := by
          gcongr
        _ = _ := by field_simp
    _ ≤ (Real.pi^2/2 * nearReturnRadius n + Real.pi^2/(4*(H+1:ℝ))) *
          (N:ℝ)^2 + Real.pi^2/2 * weightedFourierEnergy n H N := by
      have hzero : g 0 = 2 * majorantRadius n H * (N : ℝ) ^ 2 := by simp [g]
      have hpositive : (∑ h ∈ Icc 1 H, g h) = weightedFourierEnergy n H N := by
        apply sum_congr rfl
        intro h hh
        have hh0 : h ≠ 0 := by
          simp only [Finset.mem_Icc] at hh
          omega
        simp [g, hh0]
      rw [hzero, hpositive, mul_add]
      have hzeroBound := majorantCoefficient_zero_le n H
      rw [majorantCoefficient_zero, div_eq_mul_inv, mul_comm] at hzeroBound
      have henergy0 : 0 ≤ weightedFourierEnergy n H N := by
        apply sum_nonneg
        intro h hh
        have hhpos : 0 < (h : ℝ) := by
          simp only [Finset.mem_Icc] at hh
          exact_mod_cast hh.1
        apply mul_nonneg
        · apply le_min
          · exact add_nonneg
              (mul_nonneg (by norm_num) (nearReturnRadius_pos n).le)
              (div_nonneg (by norm_num) (by positivity))
          · exact div_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le hhpos.le)
        · exact sq_nonneg _
      calc
        (fejerMass H)⁻¹ * (2 * majorantRadius n H * (N : ℝ) ^ 2) +
            (fejerMass H)⁻¹ * (2 * weightedFourierEnergy n H N) ≤
          (Real.pi^2/2 * nearReturnRadius n + Real.pi^2/(4*(H+1:ℝ))) *
              (N : ℝ) ^ 2 +
            (Real.pi ^ 2 / 4) * (2 * weightedFourierEnergy n H N) := by
          apply add_le_add
          · calc
              (fejerMass H)⁻¹ * (2 * majorantRadius n H * (N : ℝ) ^ 2) =
                  ((fejerMass H)⁻¹ * (2 * majorantRadius n H)) * (N : ℝ) ^ 2 := by
                    ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hzeroBound (sq_nonneg _)
          · exact mul_le_mul_of_nonneg_right (inv_fejerMass_le H)
              (mul_nonneg (by norm_num) henergy0)
        _ = _ := by ring

/-- The ordered pairs of Fejer frequencies whose integer difference is `h`. -/
def doubleFrequencyFiber (H : ℕ) (h : ℤ) : Finset (ℕ × ℕ) :=
  (range (H + 1) ×ˢ range (H + 1)).filter
    (fun rs => (rs.2 : ℤ) - rs.1 = h)

/-- A supported frequency occurs in exactly `H + 1 - |h|` ordered pairs. -/
theorem card_doubleFrequencyFiber {H : ℕ} {h : ℤ} (hh : h.natAbs ≤ H) :
    #(doubleFrequencyFiber H h) = H + 1 - h.natAbs := by
  classical
  by_cases hnonneg : 0 ≤ h
  · have hcast : (h.natAbs : ℤ) = h := Int.natAbs_of_nonneg hnonneg
    have hfiber : doubleFrequencyFiber H h =
        (range (H + 1 - h.natAbs)).image
          (fun r => (r, r + h.natAbs)) := by
      ext rs
      simp only [doubleFrequencyFiber, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hr, hs⟩, hrs⟩
        refine ⟨rs.1, ?_, ?_⟩
        · omega
        · apply Prod.ext
          · rfl
          · simp only
            omega
      · rintro ⟨r, hr, rfl⟩
        constructor
        · constructor <;> omega
        · rw [Nat.cast_add]
          calc
            (r : ℤ) + h.natAbs - r = (h.natAbs : ℤ) := by ring
            _ = h := hcast
    have hinj : Set.InjOn (fun r : ℕ => (r, r + h.natAbs))
        (↑(Finset.range (H + 1 - h.natAbs)) : Set ℕ) := by
      intro a ha b hb hab
      exact congrArg Prod.fst hab
    rw [hfiber, card_image_iff.mpr hinj]
    simp
  · have hnonpos : h ≤ 0 := le_of_not_ge hnonneg
    have hcast : -((h.natAbs : ℕ) : ℤ) = h :=
      (Int.eq_neg_natAbs_of_nonpos hnonpos).symm
    have hfiber : doubleFrequencyFiber H h =
        (range (H + 1 - h.natAbs)).image
          (fun s => (s + h.natAbs, s)) := by
      ext rs
      simp only [doubleFrequencyFiber, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hr, hs⟩, hrs⟩
        refine ⟨rs.2, ?_, ?_⟩
        · omega
        · apply Prod.ext
          · simp only
            omega
          · rfl
      · rintro ⟨s, hs, rfl⟩
        constructor
        · constructor <;> omega
        · rw [Nat.cast_add]
          calc
            (s : ℤ) - (s + h.natAbs) = -(h.natAbs : ℤ) := by ring
            _ = h := hcast
    have hinj : Set.InjOn (fun s : ℕ => (s + h.natAbs, s))
        (↑(Finset.range (H + 1 - h.natAbs)) : Set ℕ) := by
      intro a ha b hb hab
      exact congrArg Prod.snd hab
    rw [hfiber, card_image_iff.mpr hinj]
    simp

/-- The contribution of one frequency fiber to the normalized integral in the
exact double-frequency expansion. -/
def normalizedIntegralCoefficientFiber (n H : ℕ) (h : ℤ) : ℝ :=
  (fejerMass H)⁻¹ / (H + 1 : ℝ) *
    ∑ rs ∈ doubleFrequencyFiber H h,
      (∫ y in -(majorantRadius n H)..majorantRadius n H,
        phase (-((rs.2 : ℤ) - rs.1)) y).re

/-- Aggregating the exact double-frequency terms with difference `h` recovers
the corresponding explicit majorant coefficient. -/
theorem normalizedIntegralCoefficientFiber_eq_majorantCoefficient
    (n H : ℕ) (h : ℤ) (hh : h.natAbs ≤ H) :
    normalizedIntegralCoefficientFiber n H h = majorantCoefficient n H h := by
  classical
  let I : ℝ :=
    (∫ y in -(majorantRadius n H)..majorantRadius n H, phase (-h) y).re
  have hsum :
      (∑ rs ∈ doubleFrequencyFiber H h,
        (∫ y in -(majorantRadius n H)..majorantRadius n H,
          phase (-((rs.2 : ℤ) - rs.1)) y).re) =
        (H + 1 - h.natAbs : ℕ) * I := by
    calc
      _ = ∑ _rs ∈ doubleFrequencyFiber H h, I := by
        apply sum_congr rfl
        intro rs hrs
        have hrs' : (rs.2 : ℤ) - rs.1 = h :=
          (mem_filter.mp hrs).2
        simp only [I, hrs']
      _ = (H + 1 - h.natAbs : ℕ) * I := by
        rw [sum_const, nsmul_eq_mul, card_doubleFrequencyFiber hh]
  have hcast : ((H + 1 - h.natAbs : ℕ) : ℝ) =
      (H + 1 : ℝ) - h.natAbs := by
    rw [Nat.cast_sub]
    · norm_num
    · omega
  rw [normalizedIntegralCoefficientFiber, hsum, majorantCoefficient, if_pos hh]
  rw [hcast]
  unfold fejerCoefficient
  dsimp only [I]
  field_simp

/-- The linear frequency cutoff used in T9's hypothesis. -/
def frequencyCutoff (A : ℝ) (n : ℕ) : ℕ :=
  ⌈A * (n : ℝ)⌉₊

/-- The exact weighted Fourier-energy hypothesis HFE(pi). The sample size may
depend on `A`, `epsilon`, and `n`. This hypothesis is not proved here. -/
def HFE_pi : Prop :=
  ∀ A : ℝ, 0 < A → ∀ ε : ℝ, 0 < ε →
    ∃ nstar : ℕ, 1 ≤ nstar ∧
      ∀ n : ℕ, nstar ≤ n →
        ∃ N : ℕ, 1 ≤ N ∧
          weightedFourierEnergy n (frequencyCutoff A n) N <
            ε * (N : ℝ) ^ 2 / (n : ℝ)

lemma nearReturnRadius_eq_inv_pow (n : ℕ) :
    nearReturnRadius n = ((10 : ℝ)⁻¹) ^ n := by
  simp [nearReturnRadius, inv_pow]

lemma eventually_scaled_nearReturnRadius_lt_one (D : ℝ) (_hD : 0 < D) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      D * (n : ℝ) * nearReturnRadius n < 1 := by
  have ht : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * ((10 : ℝ)⁻¹) ^ n)
      Filter.atTop (nhds 0) := by
    exact tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hscaled : Filter.Tendsto
      (fun n : ℕ => D * ((n : ℝ) * ((10 : ℝ)⁻¹) ^ n))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul ht : Filter.Tendsto
      (fun n : ℕ => D * ((n : ℝ) * ((10 : ℝ)⁻¹) ^ n))
      Filter.atTop (nhds (D * 0)))
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      D * ((n : ℝ) * ((10 : ℝ)⁻¹) ^ n) < 1 :=
    (tendsto_order.1 hscaled).2 1 (by norm_num)
  obtain ⟨m, hm⟩ := (Filter.eventually_atTop.1 hev)
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  have hnm : m ≤ n := (le_max_right 1 m).trans hn
  simpa [nearReturnRadius_eq_inv_pow, mul_assoc] using hm n hnm

/-- T9's conditional conclusion with T8's eventual-length and existential
sample-size quantifiers unchanged. This theorem does not assert HFE(pi). -/
theorem HFE_pi_implies_lacunaryNearReturnC2 (hHFE : HFE_pi) :
    LacunaryNearReturnC2 := by
  intro C hC
  let A : ℝ := Real.pi ^ 2 * C + 1
  let ε : ℝ := 1 / (Real.pi ^ 2 * C)
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have heps : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨nstar, hnstar, hstar⟩ := hHFE A hA ε heps
  have hD : 0 < 2 * Real.pi ^ 2 * C := by positivity
  obtain ⟨nexp, hnexp, hexp⟩ :=
    eventually_scaled_nearReturnRadius_lt_one
      (2 * Real.pi ^ 2 * C) hD
  refine ⟨max nstar nexp, hnstar.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hnstar' : nstar ≤ n := (le_max_left nstar nexp).trans hn
  have hnexp' : nexp ≤ n := (le_max_right nstar nexp).trans hn
  have hn1 : 1 ≤ n := hnstar.trans hnstar'
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn1
  let H := frequencyCutoff A n
  obtain ⟨N, hN, henergy⟩ := hstar n hnstar'
  refine ⟨N, hN, ?_⟩
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcutoff : A * (n : ℝ) ≤ (H : ℝ) := by
    exact Nat.le_ceil (A * (n : ℝ))
  have hHpos : 0 < (H + 1 : ℝ) := by positivity
  have hAstrict : Real.pi ^ 2 * C < A := by
    dsimp [A]
    linarith
  have hdenCutoff : Real.pi ^ 2 * C * (n : ℝ) < (H + 1 : ℝ) := by
    have hmul : Real.pi ^ 2 * C * (n : ℝ) < A * (n : ℝ) :=
      mul_lt_mul_of_pos_right hAstrict hnR
    exact hmul.trans_le (hcutoff.trans (by linarith))
  have hexp' :
      2 * Real.pi ^ 2 * C * (n : ℝ) * nearReturnRadius n < 1 :=
    hexp n hnexp'
  have hfirstCoeff :
      Real.pi ^ 2 / 2 * nearReturnRadius n < 1 / (4 * C * (n : ℝ)) := by
    have hden : 0 < 4 * C * (n : ℝ) := by positivity
    apply (lt_div_iff₀ hden).2
    calc
      Real.pi ^ 2 / 2 * nearReturnRadius n * (4 * C * (n : ℝ)) =
          2 * Real.pi ^ 2 * C * (n : ℝ) * nearReturnRadius n := by ring
      _ < 1 := hexp'
  have hsecondCoeff :
      Real.pi ^ 2 / (4 * (H + 1 : ℝ)) <
        1 / (4 * C * (n : ℝ)) := by
    have hleft : 0 < 4 * (H + 1 : ℝ) := by positivity
    have hright : 0 < 4 * C * (n : ℝ) := by positivity
    rw [div_lt_div_iff₀ hleft hright]
    nlinarith
  have henergy' : weightedFourierEnergy n H N <
      (1 / (Real.pi ^ 2 * C)) * (N : ℝ) ^ 2 / (n : ℝ) := by
    simpa [H, ε] using henergy
  have henergyTerm :
      Real.pi ^ 2 / 2 * weightedFourierEnergy n H N <
        (N : ℝ) ^ 2 / (2 * C * (n : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_left henergy' (by positivity : 0 < Real.pi ^ 2 / 2)
    calc
      Real.pi ^ 2 / 2 * weightedFourierEnergy n H N <
          Real.pi ^ 2 / 2 *
            ((1 / (Real.pi ^ 2 * C)) * (N : ℝ) ^ 2 / (n : ℝ)) := hmul
      _ = (N : ℝ) ^ 2 / (2 * C * (n : ℝ)) := by
        field_simp [Real.pi_ne_zero, hC.ne', hnR.ne']
  have hzeroTerm :
      (Real.pi ^ 2 / 2 * nearReturnRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * (N : ℝ) ^ 2 <
        (N : ℝ) ^ 2 / (2 * C * (n : ℝ)) := by
    have hsum :
        Real.pi ^ 2 / 2 * nearReturnRadius n +
            Real.pi ^ 2 / (4 * (H + 1 : ℝ)) <
          1 / (2 * C * (n : ℝ)) := by
      calc
        _ < 1 / (4 * C * (n : ℝ)) + 1 / (4 * C * (n : ℝ)) :=
          add_lt_add hfirstCoeff hsecondCoeff
        _ = 1 / (2 * C * (n : ℝ)) := by field_simp; ring
    have hN2 : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hNR
    calc
      _ < (1 / (2 * C * (n : ℝ))) * (N : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hsum hN2
      _ = (N : ℝ) ^ 2 / (2 * C * (n : ℝ)) := by ring
  calc
    (Q_pi n N : ℝ) ≤
        (Real.pi ^ 2 / 2 * nearReturnRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * (N : ℝ) ^ 2 +
            Real.pi ^ 2 / 2 * weightedFourierEnergy n H N :=
      Q_pi_explicit_bound n H N
    _ < (N : ℝ) ^ 2 / (2 * C * (n : ℝ)) +
        (N : ℝ) ^ 2 / (2 * C * (n : ℝ)) :=
      add_lt_add hzeroTerm henergyTerm
    _ = (N : ℝ) ^ 2 / (C * (n : ℝ)) := by field_simp; ring

/-!
## Unproved frontier

`HFE_pi` is an explicit hypothesis, not a theorem about pi. Consequently this
file does not prove T8's sibling `LacunaryNearReturnC2`, T4's sibling
`CollisionEnergyC1 piDecimalStream`, or canonical A1. It proves only the
conditional implication `HFE_pi -> LacunaryNearReturnC2`; T8 supplies the
separate conditional chain C2 -> C1 -> A1.
-/

end WeightedFourierReduction
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.WeightedFourierReduction.four_div_pi_sq_le_fejerMass
#print axioms DecimalFactorComplexity.WeightedFourierReduction.nearReturnIndicator_le_intervalMajorant
#print axioms DecimalFactorComplexity.WeightedFourierReduction.majorantCoefficient_zero_le
#print axioms DecimalFactorComplexity.WeightedFourierReduction.abs_majorantCoefficient_le
#print axioms DecimalFactorComplexity.WeightedFourierReduction.orderedPair_phase_identity
#print axioms DecimalFactorComplexity.WeightedFourierReduction.pi_orderedPair_phase_identity
#print axioms DecimalFactorComplexity.WeightedFourierReduction.majorantPairSum_eq_doubleFrequencySum
#print axioms DecimalFactorComplexity.WeightedFourierReduction.card_doubleFrequencyFiber
#print axioms DecimalFactorComplexity.WeightedFourierReduction.normalizedIntegralCoefficientFiber_eq_majorantCoefficient
#print axioms DecimalFactorComplexity.WeightedFourierReduction.Q_pi_explicit_bound
#print axioms DecimalFactorComplexity.WeightedFourierReduction.HFE_pi_implies_lacunaryNearReturnC2
