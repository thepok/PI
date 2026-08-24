import TheoryLib.PiQuantitativeBlockHitting.T133T133BoundaryDecimalScaleSeparator
import Mathlib.Analysis.Calculus.Taylor

/-!
# T134: aggregate boundary-kernel separator at decimal scale

This file verifies the finite 26-point separator from the boundary-matched
kernel note.  It is a finite predicate comparison only and contains no
estimate for the decimal orbit of pi.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.BoundaryAggregateDecimalScaleSeparator

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.SharperNaturalScaleResonance
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison
open Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra
open Theory.PiDigits.EdgeFrequencyFibers

/-- The fifth-degree alternating Taylor upper bound used by the exact
26-point calculation. -/
lemma sin_le_quintic {u : ℝ} (hu0 : 0 ≤ u) (hupi : u ≤ Real.pi / 2) :
    Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 := by
  rcases hu0.eq_or_lt with rfl | hu
  · norm_num
  obtain ⟨z, hz, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.sin) (x₀ := 0) (x := u) (n := 5) hu.ne
    (Real.contDiff_sin.contDiffOn.of_le le_rfl)
  have hzIoo : z ∈ Set.Ioo (0 : ℝ) u := by simpa [uIoo, hu.le] using hz
  have hzpi : z ≤ Real.pi := by
    have hhalf : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    exact hzIoo.2.le.trans (hupi.trans hhalf)
  have hsinz : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hzIoo.1.le hzpi
  have hpoly :
      taylorWithinEval Real.sin 5 (uIcc (0 : ℝ) u) 0 u =
        u - u ^ 3 / 6 + u ^ 5 / 120 := by
    rw [uIcc_of_le hu.le, taylor_within_apply]
    norm_num only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial]
    simp_rw [Real.iteratedDerivWithin_sin_Icc _ hu
      (show (0 : ℝ) ∈ Set.Icc 0 u by exact ⟨le_rfl, hu.le⟩)]
    norm_num [Real.iteratedDeriv_even_sin, Real.iteratedDeriv_odd_sin]
    ring
  rw [hpoly] at hTaylor
  have hderiv : iteratedDeriv 6 Real.sin z = -Real.sin z := by
    rw [show 6 = 2 * 3 by norm_num, Real.iteratedDeriv_even_sin]
    norm_num
  rw [hderiv] at hTaylor
  norm_num at hTaylor
  have hu6 : 0 ≤ u ^ 6 := pow_nonneg hu.le 6
  nlinarith

/-- The complete 26-grid with its zero entry replaced by a second copy of
`1/26`.  Only the first 26 terms are used. -/
def boundaryAggregateSeparatorSample (j : ℕ) : ℝ :=
  if j = 0 then 1 / 26 else (j : ℝ) / 26

/-- The shorter residue representative in the 26-grid chord formula. -/
def gridRadius (h : ℕ) : ℕ := min h (26 - h)

/-- Minimal positive-frequency form of the boundary aggregate load at
`q = 10`.  The factor two accounts for conjugate negative frequencies. -/
def boundaryAggregateLoadTen (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (2 * ∑ h ∈ Finset.range 19,
    affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
      ‖Theory.PiDigits.T27.exponentialSum x N (h + 1 : ℕ)‖) / N

/-- Matching positive-frequency form of the existing aggregated Jackson
load at `q = 10`. -/
def jacksonAggregateLoadTen (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (2 * ∑ h ∈ Finset.range 19,
    affineCoefficient 10 (h + 1) (jacksonBeta 10) *
      ‖Theory.PiDigits.T27.exponentialSum x N (h + 1 : ℕ)‖) / N

private lemma boundaryAggregateSeparatorSample_exponentialSum
    (h : ℕ) (hh0 : 0 < h) (hh26 : h < 26) :
    Theory.PiDigits.T27.exponentialSum boundaryAggregateSeparatorSample 26 h =
      Theory.PiDigits.T27.phase h (1 / 26 : ℝ) - 1 := by
  have hgrid := uniformGrid_exponentialSum_nat_eq_zero h 26
    (by norm_num) hh0 hh26
  rw [Theory.PiDigits.T27.exponentialSum]
  have hrange : Finset.range 26 = {0} ∪ Finset.Ico 1 26 := by
    ext j
    simp
    omega
  rw [hrange, Finset.sum_union]
  · have htail :
        (∑ j ∈ Finset.Ico 1 26,
            Theory.PiDigits.T27.phase (h : ℤ)
              (boundaryAggregateSeparatorSample j)) = -1 := by
      rw [Theory.PiDigits.T27.exponentialSum, hrange, Finset.sum_union] at hgrid
      · have heq :
            (∑ j ∈ Finset.Ico 1 26,
              Theory.PiDigits.T27.phase (h : ℤ)
                (boundaryAggregateSeparatorSample j)) =
            ∑ j ∈ Finset.Ico 1 26,
              Theory.PiDigits.T27.phase (h : ℤ) (uniformGrid 26 j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [show boundaryAggregateSeparatorSample j = uniformGrid 26 j by
              simp [boundaryAggregateSeparatorSample, uniformGrid,
                Nat.ne_of_gt (Finset.mem_Ico.mp hj).1]]
        rw [heq]
        have hgrid' :
            (1 : ℂ) + ∑ j ∈ Finset.Ico 1 26,
              Theory.PiDigits.T27.phase (h : ℤ) (uniformGrid 26 j) = 0 := by
          simpa [uniformGrid, Theory.PiDigits.T27.phase] using hgrid
        calc
          (∑ j ∈ Finset.Ico 1 26,
              Theory.PiDigits.T27.phase (h : ℤ) (uniformGrid 26 j)) =
              (1 + ∑ j ∈ Finset.Ico 1 26,
                Theory.PiDigits.T27.phase (h : ℤ) (uniformGrid 26 j)) - 1 := by ring
          _ = -1 := by rw [hgrid']; ring
      · simp
    rw [Finset.sum_singleton, htail]
    simp [boundaryAggregateSeparatorSample]
    ring
  · simp

private lemma separatorSample_norm_eq_sine
    (h : ℕ) (hh0 : 0 < h) (hh19 : h ≤ 19) :
    ‖Theory.PiDigits.T27.exponentialSum boundaryAggregateSeparatorSample 26 h‖ =
      2 * Real.sin (Real.pi * gridRadius h / 26) := by
  rw [boundaryAggregateSeparatorSample_exponentialSum h hh0 (by omega),
    norm_sub_rev]
  have hphase : Theory.PiDigits.T27.phase (h : ℤ) (1 / 26 : ℝ) =
      Theory.PiDigits.T27.phase 1 ((h : ℝ) / 26) := by
    rw [Theory.PiDigits.T27.phase, Theory.PiDigits.T27.phase]
    congr 1
    push_cast
    ring
  rw [hphase, Theory.PiDigits.T27.norm_one_sub_phase_one]
  have harg0 : 0 ≤ Real.pi * ((h : ℝ) / 26) := by positivity
  have hargpi : Real.pi * ((h : ℝ) / 26) ≤ Real.pi := by
    have hhR : (h : ℝ) ≤ 26 := by exact_mod_cast (hh19.trans (by norm_num))
    nlinarith [Real.pi_pos]
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi harg0 hargpi)]
  by_cases hh13 : h ≤ 13
  · have hle : h ≤ 26 - h := Nat.le_sub_of_add_le (by omega)
    rw [show gridRadius h = h by exact Nat.min_eq_left hle]
    ring
  · have hle : 26 - h ≤ h := by omega
    rw [show gridRadius h = 26 - h by exact Nat.min_eq_right hle]
    rw [← Real.sin_pi_sub]
    congr 2
    rw [Nat.cast_sub (by omega : h ≤ 26)]
    ring

private lemma jackson_weighted_radius_moment :
    (∑ h ∈ Finset.range 19,
      (gridRadius (h + 1) : ℝ) * affineCoefficient 10 (h + 1) (jacksonBeta 10)) =
      (4608 : ℝ) / 625 := by
  norm_num [Finset.sum_range_succ, gridRadius, affineCoefficient, neighboringCoefficient,
    fejerSquareCoefficient, cubicMultiplicity, jacksonBeta]

private lemma boundary_weighted_radius_moment_one :
    (∑ h ∈ Finset.range 19,
      (gridRadius (h + 1) : ℝ) *
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10))) =
      9 * (2577 - 2546 * Real.cos (Real.pi / 10)) / 100 := by
  norm_num [Finset.sum_range_succ, gridRadius, affineCoefficient, neighboringCoefficient,
    fejerSquareCoefficient, cubicMultiplicity]
  ring

private lemma boundary_weighted_radius_moment_three :
    (∑ h ∈ Finset.range 19,
      (gridRadius (h + 1) : ℝ) ^ 3 *
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10))) =
      3 * (454699 - 441156 * Real.cos (Real.pi / 10)) / 100 := by
  norm_num [Finset.sum_range_succ, gridRadius, affineCoefficient, neighboringCoefficient,
    fejerSquareCoefficient, cubicMultiplicity]
  ring

private lemma boundary_weighted_radius_moment_five :
    (∑ h ∈ Finset.range 19,
      (gridRadius (h + 1) : ℝ) ^ 5 *
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10))) =
      3 * (43167431 - 41414828 * Real.cos (Real.pi / 10)) / 100 := by
  norm_num [Finset.sum_range_succ, gridRadius, affineCoefficient, neighboringCoefficient,
    fejerSquareCoefficient, cubicMultiplicity]
  ring

private lemma cos_pi_div_ten_sq :
    Real.cos (Real.pi / 10) ^ 2 = (5 + Real.sqrt 5) / 8 := by
  have hdouble : Real.cos (Real.pi / 5) =
      2 * Real.cos (Real.pi / 10) ^ 2 - 1 := by
    rw [show Real.pi / 5 = 2 * (Real.pi / 10) by ring, Real.cos_two_mul]
  rw [Real.cos_pi_div_five] at hdouble
  nlinarith

private lemma cos_pi_div_ten_lower :
    (951 : ℝ) / 1000 < Real.cos (Real.pi / 10) := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 5 ^ 2 = 5 := by norm_num
  have hsqrtLower : (559 : ℝ) / 250 < Real.sqrt 5 := by nlinarith
  have hcos0 : 0 ≤ Real.cos (Real.pi / 10) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [← sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 951 / 1000) hcos0]
  rw [cos_pi_div_ten_sq]
  nlinarith

private lemma cos_pi_div_ten_upper :
    Real.cos (Real.pi / 10) < (119 : ℝ) / 125 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 5 ^ 2 = 5 := by norm_num
  have hsqrtUpper : Real.sqrt 5 < (9 : ℝ) / 4 := by nlinarith
  have hcos0 : 0 ≤ Real.cos (Real.pi / 10) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [← sq_lt_sq₀ hcos0 (by norm_num : (0 : ℝ) ≤ 119 / 125)]
  rw [cos_pi_div_ten_sq]
  nlinarith

private lemma boundaryCoefficient_ten_nonneg
    (h : ℕ) (hh0 : 0 < h) (hh19 : h ≤ 19) :
    0 ≤ affineCoefficient 10 h (Real.cos (Real.pi / 10)) := by
  interval_cases h <;>
    norm_num [affineCoefficient, neighboringCoefficient, fejerSquareCoefficient,
      cubicMultiplicity] <;>
    nlinarith [cos_pi_div_ten_upper]

private lemma jacksonCoefficient_ten_nonneg
    (h : ℕ) (hh0 : 0 < h) (hh19 : h ≤ 19) :
    0 ≤ affineCoefficient 10 h (jacksonBeta 10) := by
  interval_cases h <;>
    norm_num [affineCoefficient, neighboringCoefficient, fejerSquareCoefficient,
      cubicMultiplicity, jacksonBeta]

private lemma boundaryAggregateLoadTen_separatorSample_eq :
    boundaryAggregateLoadTen boundaryAggregateSeparatorSample 26 =
      (2 / 13 : ℝ) * ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
          Real.sin (Real.pi * gridRadius (h + 1) / 26) := by
  unfold boundaryAggregateLoadTen
  rw [show (∑ h ∈ Finset.range 19,
      affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
        ‖Theory.PiDigits.T27.exponentialSum boundaryAggregateSeparatorSample 26
          (h + 1 : ℕ)‖) =
      ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
          (2 * Real.sin (Real.pi * gridRadius (h + 1) / 26)) by
    apply Finset.sum_congr rfl
    intro h hh
    have hh' := Finset.mem_range.mp hh
    rw [separatorSample_norm_eq_sine (h + 1) (by omega)
      (by omega)]]
  rw [show (∑ h ∈ Finset.range 19,
      affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
        (2 * Real.sin (Real.pi * gridRadius (h + 1) / 26))) =
      2 * ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
          Real.sin (Real.pi * gridRadius (h + 1) / 26) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring]
  ring

private lemma jacksonAggregateLoadTen_separatorSample_eq :
    jacksonAggregateLoadTen boundaryAggregateSeparatorSample 26 =
      (2 / 13 : ℝ) * ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (jacksonBeta 10) *
          Real.sin (Real.pi * gridRadius (h + 1) / 26) := by
  unfold jacksonAggregateLoadTen
  rw [show (∑ h ∈ Finset.range 19,
      affineCoefficient 10 (h + 1) (jacksonBeta 10) *
        ‖Theory.PiDigits.T27.exponentialSum boundaryAggregateSeparatorSample 26
          (h + 1 : ℕ)‖) =
      ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (jacksonBeta 10) *
          (2 * Real.sin (Real.pi * gridRadius (h + 1) / 26)) by
    apply Finset.sum_congr rfl
    intro h hh
    have hh' := Finset.mem_range.mp hh
    rw [separatorSample_norm_eq_sine (h + 1) (by omega)
      (by omega)]]
  rw [show (∑ h ∈ Finset.range 19,
      affineCoefficient 10 (h + 1) (jacksonBeta 10) *
        (2 * Real.sin (Real.pi * gridRadius (h + 1) / 26))) =
      2 * ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (jacksonBeta 10) *
          Real.sin (Real.pi * gridRadius (h + 1) / 26) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring]
  ring

private lemma gridRadius_le_thirteen (h : ℕ) : gridRadius h ≤ 13 := by
  unfold gridRadius
  omega

private lemma radius_div_thirteen_le_sin (h : ℕ) :
    (gridRadius h : ℝ) / 13 ≤
      Real.sin (Real.pi * gridRadius h / 26) := by
  let u : ℝ := Real.pi * gridRadius h / 26
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have huhalf : u ≤ Real.pi / 2 := by
    dsimp [u]
    have hr : (gridRadius h : ℝ) ≤ 13 := by exact_mod_cast gridRadius_le_thirteen h
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hu0 huhalf
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  convert hs using 1 <;> dsimp [u] <;> field_simp <;> ring

/-- The 26-point witness fails the old Jackson aggregate threshold. -/
theorem jacksonAggregateCriterion_ten_fails :
    (17 : ℝ) / 500 <
      jacksonAggregateLoadTen boundaryAggregateSeparatorSample 26 := by
  rw [jacksonAggregateLoadTen_separatorSample_eq]
  have hsum :
      (∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (jacksonBeta 10) *
          ((gridRadius (h + 1) : ℝ) / 13)) ≤
      ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (jacksonBeta 10) *
          Real.sin (Real.pi * gridRadius (h + 1) / 26) := by
    apply Finset.sum_le_sum
    intro h hh
    have hh' := Finset.mem_range.mp hh
    exact mul_le_mul_of_nonneg_left (radius_div_thirteen_le_sin (h + 1))
      (jacksonCoefficient_ten_nonneg (h + 1) (by omega) (by omega))
  have hlower :
      (2 / 169 : ℝ) * (4608 / 625) ≤
        (2 / 13 : ℝ) * ∑ h ∈ Finset.range 19,
          affineCoefficient 10 (h + 1) (jacksonBeta 10) *
            Real.sin (Real.pi * gridRadius (h + 1) / 26) := by
    have hsumeq :
        (∑ h ∈ Finset.range 19,
          affineCoefficient 10 (h + 1) (jacksonBeta 10) *
            ((gridRadius (h + 1) : ℝ) / 13)) =
          (1 / 13 : ℝ) * (4608 / 625) := by
      calc
        _ = (1 / 13 : ℝ) * ∑ h ∈ Finset.range 19,
            (gridRadius (h + 1) : ℝ) *
              affineCoefficient 10 (h + 1) (jacksonBeta 10) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h hh
          ring
        _ = _ := by rw [jackson_weighted_radius_moment]
    calc
      (2 / 169 : ℝ) * (4608 / 625) =
          (2 / 13 : ℝ) * ∑ h ∈ Finset.range 19,
            affineCoefficient 10 (h + 1) (jacksonBeta 10) *
              ((gridRadius (h + 1) : ℝ) / 13) := by
        rw [hsumeq]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
  norm_num at hlower ⊢
  linarith

private lemma boundaryAggregateLoadTen_le_taylor :
    boundaryAggregateLoadTen boundaryAggregateSeparatorSample 26 ≤
      (2 / 13 : ℝ) *
        ((Real.pi / 26) *
            (9 * (2577 - 2546 * Real.cos (Real.pi / 10)) / 100) -
          (Real.pi ^ 3 / (6 * 26 ^ 3)) *
            (3 * (454699 - 441156 * Real.cos (Real.pi / 10)) / 100) +
          (Real.pi ^ 5 / (120 * 26 ^ 5)) *
            (3 * (43167431 - 41414828 * Real.cos (Real.pi / 10)) / 100)) := by
  rw [boundaryAggregateLoadTen_separatorSample_eq]
  have hsum :
      (∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
          Real.sin (Real.pi * gridRadius (h + 1) / 26)) ≤
      ∑ h ∈ Finset.range 19,
        affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
          ((Real.pi * gridRadius (h + 1) / 26) -
            (Real.pi * gridRadius (h + 1) / 26) ^ 3 / 6 +
            (Real.pi * gridRadius (h + 1) / 26) ^ 5 / 120) := by
    apply Finset.sum_le_sum
    intro h hh
    have hh' := Finset.mem_range.mp hh
    have hr13 := gridRadius_le_thirteen (h + 1)
    have hu0 : 0 ≤ Real.pi * (gridRadius (h + 1) : ℝ) / 26 := by positivity
    have hupi : Real.pi * (gridRadius (h + 1) : ℝ) / 26 ≤ Real.pi / 2 := by
      have hrR : (gridRadius (h + 1) : ℝ) ≤ 13 := by exact_mod_cast hr13
      nlinarith [Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (sin_le_quintic hu0 hupi)
      (boundaryCoefficient_ten_nonneg (h + 1) (by omega) (by omega))
  refine (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans_eq ?_
  congr 1
  calc
    (∑ h ∈ Finset.range 19,
      affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10)) *
        ((Real.pi * gridRadius (h + 1) / 26) -
          (Real.pi * gridRadius (h + 1) / 26) ^ 3 / 6 +
          (Real.pi * gridRadius (h + 1) / 26) ^ 5 / 120)) =
        (Real.pi / 26) * (∑ h ∈ Finset.range 19,
          (gridRadius (h + 1) : ℝ) *
            affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10))) -
        (Real.pi ^ 3 / (6 * 26 ^ 3)) * (∑ h ∈ Finset.range 19,
          (gridRadius (h + 1) : ℝ) ^ 3 *
            affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10))) +
        (Real.pi ^ 5 / (120 * 26 ^ 5)) * (∑ h ∈ Finset.range 19,
          (gridRadius (h + 1) : ℝ) ^ 5 *
            affineCoefficient 10 (h + 1) (Real.cos (Real.pi / 10))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = _ := by
      rw [boundary_weighted_radius_moment_one,
        boundary_weighted_radius_moment_three,
        boundary_weighted_radius_moment_five]

private lemma boundaryAggregateLoadTen_separatorSample_lt_rational :
    boundaryAggregateLoadTen boundaryAggregateSeparatorSample 26 <
      (220454069602381739591 : ℝ) / 1014052235787500000000 := by
  have hload := boundaryAggregateLoadTen_le_taylor
  let g : ℝ := Real.cos (Real.pi / 10)
  let m₁ : ℝ := 9 * (2577 - 2546 * g) / 100
  let m₃ : ℝ := 3 * (454699 - 441156 * g) / 100
  let m₅ : ℝ := 3 * (43167431 - 41414828 * g) / 100
  have hgLower : (951 : ℝ) / 1000 < g := by
    simpa only [g] using cos_pi_div_ten_lower
  have hgUpper : g < (119 : ℝ) / 125 := by
    simpa only [g] using cos_pi_div_ten_upper
  have hm₁nonneg : 0 ≤ m₁ := by dsimp [m₁]; nlinarith
  have hm₁upper : m₁ < 9 * (2577 - 2546 * ((951 : ℝ) / 1000)) / 100 := by
    dsimp [m₁]
    nlinarith
  have hm₃lower :
      3 * (454699 - 441156 * ((119 : ℝ) / 125)) / 100 < m₃ := by
    dsimp [m₃]
    nlinarith
  have hm₃nonneg : 0 ≤ m₃ := by
    dsimp [m₃]
    nlinarith
  have hm₅nonneg : 0 ≤ m₅ := by
    dsimp [m₅]
    nlinarith
  have hm₅upper :
      m₅ < 3 * (43167431 - 41414828 * ((951 : ℝ) / 1000)) / 100 := by
    dsimp [m₅]
    nlinarith
  have hpiLower : (157 : ℝ) / 50 < Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    exact h
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    nlinarith [Real.pi_lt_d20]
  have hpi3Lower : ((157 : ℝ) / 50) ^ 3 < Real.pi ^ 3 :=
    pow_lt_pow_left₀ hpiLower (by norm_num) (by norm_num)
  have hpi5Upper : Real.pi ^ 5 < ((22 : ℝ) / 7) ^ 5 :=
    pow_lt_pow_left₀ hpiUpper Real.pi_pos.le (by norm_num)
  have hterm₁ :
      Real.pi * m₁ < (22 / 7 : ℝ) *
        (9 * (2577 - 2546 * ((951 : ℝ) / 1000)) / 100) := by
    exact (mul_lt_mul_of_pos_left hm₁upper Real.pi_pos).trans_le
      (mul_le_mul_of_nonneg_right hpiUpper.le (by positivity))
  have hterm₃ :
      ((157 : ℝ) / 50) ^ 3 *
          (3 * (454699 - 441156 * ((119 : ℝ) / 125)) / 100) <
        Real.pi ^ 3 * m₃ := by
    exact mul_lt_mul hpi3Lower hm₃lower.le (by positivity) (by positivity)
  have hterm₅ :
      Real.pi ^ 5 * m₅ < ((22 : ℝ) / 7) ^ 5 *
        (3 * (43167431 - 41414828 * ((951 : ℝ) / 1000)) / 100) := by
    exact (mul_lt_mul_of_pos_left hm₅upper (pow_pos Real.pi_pos 5)).trans_le
      (mul_le_mul_of_nonneg_right hpi5Upper.le (by positivity))
  change boundaryAggregateLoadTen boundaryAggregateSeparatorSample 26 ≤
      (2 / 13 : ℝ) *
        ((Real.pi / 26) * m₁ -
          (Real.pi ^ 3 / (6 * 26 ^ 3)) * m₃ +
          (Real.pi ^ 5 / (120 * 26 ^ 5)) * m₅) at hload
  have hpoly :
      (2 / 13 : ℝ) *
          ((Real.pi / 26) * m₁ -
            (Real.pi ^ 3 / (6 * 26 ^ 3)) * m₃ +
            (Real.pi ^ 5 / (120 * 26 ^ 5)) * m₅) <
        (220454069602381739591 : ℝ) / 1014052235787500000000 := by
    norm_num at hterm₁ hterm₃ hterm₅ ⊢
    nlinarith
  exact hload.trans_lt hpoly

private lemma boundaryZeroCoefficient_ten_gt :
    (277 : ℝ) / 1250 < boundaryZeroCoefficient 10 := by
  rw [boundaryZeroCoefficient_eq 10 (by norm_num)]
  norm_num
  nlinarith [cos_pi_div_ten_upper]

/-- Exact threshold crossing on one finite witness: the boundary aggregate
criterion passes while the Jackson aggregate criterion fails.  This makes no
claim about pi-orbit cancellation. -/
theorem boundary_aggregate_decimalScale_ten_strict_vs_jackson :
    boundaryAggregateLoadTen boundaryAggregateSeparatorSample 26 <
        boundaryZeroCoefficient 10 ∧
      ¬ jacksonAggregateLoadTen boundaryAggregateSeparatorSample 26 <
        aggregatedCoefficient (jacksonCoefficient 10 10)
          (@jacksonFrequency 10) 0 := by
  constructor
  · have hload := boundaryAggregateLoadTen_separatorSample_lt_rational
    have hgap :
        (220454069602381739591 : ℝ) / 1014052235787500000000 <
          277 / 1250 := by norm_num
    exact hload.trans hgap |>.trans boundaryZeroCoefficient_ten_gt
  · rw [jacksonZeroCoefficient_eq 10 (by norm_num)]
    norm_num
    exact jacksonAggregateCriterion_ten_fails.le

end Theory.PiDigits.BoundaryAggregateDecimalScaleSeparator

#print axioms Theory.PiDigits.BoundaryAggregateDecimalScaleSeparator.sin_le_quintic
#print axioms Theory.PiDigits.BoundaryAggregateDecimalScaleSeparator.jacksonAggregateCriterion_ten_fails
#print axioms Theory.PiDigits.BoundaryAggregateDecimalScaleSeparator.boundary_aggregate_decimalScale_ten_strict_vs_jackson
