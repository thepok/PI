import TheoryLib.PiQuantitativeBlockHitting.T132T132EdgeFrequencyFibers
import TheoryLib.PiQuantitativeBlockHitting.T18T18SharperNaturalScaleResonance

/-!
# T133: strict boundary-kernel separator at decimal scale

At the actual decimal scale `q = 10`, the singleton `x₀ = 1/12` for the
target interval `[0, 1/10)` passes the boundary-matched directional threshold
but fails the older Jackson directional threshold.  This is a finite
predicate separator only.  It asserts no cancellation estimate for the
decimal orbit of pi.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.BoundaryDecimalScaleSeparator

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.SharperNaturalScaleResonance
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.DirectionalJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison

private lemma singleton_directional_defect_eq_zero_sub_minorant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (minorant : ℝ → ℂ)
    (hminorant : ∀ t, minorant t = ∑ i, coefficient i *
      Theory.PiDigits.T27.phase (frequency i) t)
    (x center : ℝ) :
    normalizedDirectionalFourierDefect coefficient frequency (fun _ => x) 1 center =
      aggregatedCoefficient coefficient frequency 0 - (minorant (x - center)).re := by
  classical
  have hregroup := sum_aggregatedCoefficient_mul_ne_zero coefficient frequency
    (fun h => Theory.PiDigits.T27.phase h (-center) *
      Theory.PiDigits.T27.exponentialSum (fun _ => x) 1 h)
  have hphase (h : ℤ) :
      Theory.PiDigits.T27.phase h (-center) *
          Theory.PiDigits.T27.exponentialSum (fun _ => x) 1 h =
        Theory.PiDigits.T27.phase h (x - center) := by
    rw [Theory.PiDigits.T27.exponentialSum, Finset.sum_range_one,
      ← Theory.PiDigits.T27.phase_add_real]
    congr 1
    ring
  simp_rw [hphase] at hregroup
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : ι => frequency i = 0)
    (fun i => (coefficient i : ℂ) *
      Theory.PiDigits.T27.phase (frequency i) (x - center))
  have hzero :
      (∑ i : ι with frequency i = 0,
        (coefficient i : ℂ) *
          Theory.PiDigits.T27.phase (frequency i) (x - center)) =
        aggregatedCoefficient coefficient frequency 0 := by
    unfold aggregatedCoefficient
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 := (Finset.mem_filter.mp hi).2
    simp [hi0, Theory.PiDigits.T27.phase]
  have htotal :
      minorant (x - center) =
        (aggregatedCoefficient coefficient frequency 0 : ℂ) +
          ∑ i with frequency i ≠ 0,
            (coefficient i : ℂ) *
              Theory.PiDigits.T27.phase (frequency i) (x - center) := by
    rw [hminorant, ← hsplit, hzero]
  unfold normalizedDirectionalFourierDefect centeredAggregatedNonzeroSum
  norm_num only [Nat.cast_one, div_one]
  simp_rw [mul_assoc, hphase]
  rw [hregroup]
  rw [htotal]
  norm_num

private lemma fejerFactor_ten_one_thirtieth_pos :
    0 < fejerFactor 10 (1 / 30 : ℝ) := by
  have hphase : Theory.PiDigits.T27.phase (10 : ℤ) (1 / 30 : ℝ) ≠ 1 := by
    simpa using phase_uniformGrid_root_ne_one 10 30 (by norm_num) (by norm_num) (by norm_num)
  have hgeom : geometricSum 10 (1 / 30 : ℝ) ≠ 0 := by
    intro hz
    have hmul := geometricSum_mul_one_sub_phase 10 (1 / 30 : ℝ)
    rw [hz, zero_mul] at hmul
    exact hphase (sub_eq_zero.mp hmul.symm).symm
  unfold fejerFactor
  exact div_pos (Complex.normSq_pos.mpr hgeom) (by norm_num)

private lemma cos_pi_div_ten_lt_cos_pi_div_fifteen :
    Real.cos (Real.pi / 10) < Real.cos (Real.pi / 15) := by
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private lemma cos_pi_div_fifteen_lt_jacksonBeta_ten :
    Real.cos (Real.pi / 15) < (49 : ℝ) / 50 := by
  let y : ℝ := Real.pi / 30
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := by
    dsimp [y]
    nlinarith [Real.pi_lt_four]
  have hsin := Real.sin_gt_sub_cube hy0 hy1
  have hyLower : (157 : ℝ) / 1500 < y := by
    dsimp [y]
    nlinarith [Real.pi_gt_d2]
  have hyUpper : y < (2 : ℝ) / 15 := by
    dsimp [y]
    nlinarith [Real.pi_lt_four]
  have hyNonneg : 0 ≤ y := hy0.le
  have hcub : y ^ 3 < ((2 : ℝ) / 15) ^ 3 := by
    exact pow_lt_pow_left₀ hyUpper hyNonneg (by norm_num)
  have hsinLower : (1 : ℝ) / 10 < Real.sin y := by
    nlinarith
  have hsinNonneg : 0 ≤ Real.sin y := (le_trans (by norm_num) hsinLower.le)
  have hsq : (1 : ℝ) / 100 < Real.sin y ^ 2 := by
    nlinarith
  have hcos : Real.cos (Real.pi / 15) = 1 - 2 * Real.sin y ^ 2 := by
    rw [show Real.pi / 15 = 2 * y by dsimp [y]; ring]
    exact Real.cos_two_mul_eq_one_sub y
  rw [hcos]
  nlinarith

private lemma boundaryMinorant_ten_one_thirtieth_pos :
    0 < (boundaryMinorant 10 (1 / 30 : ℝ)).re := by
  rw [boundaryMinorant_eq 10 (by norm_num)]
  norm_num only [Complex.ofReal_re, Nat.cast_ofNat]
  convert mul_pos (sub_pos.mpr cos_pi_div_ten_lt_cos_pi_div_fifteen)
    (sq_pos_of_pos fejerFactor_ten_one_thirtieth_pos) using 1 <;> ring

private lemma jacksonMinorant_ten_one_thirtieth_nonpos :
    (jacksonMinorant 10 10 (1 / 30 : ℝ)).re ≤ 0 := by
  rw [jacksonMinorant_eq 10 10 (by norm_num) (by norm_num),
    edgeValue_eq 10 (by norm_num), Complex.normSq_mul]
  have hreal : Complex.normSq (fejerFactor 10 (1 / 30 : ℝ) : ℂ) =
      fejerFactor 10 (1 / 30 : ℝ) ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [hreal]
  have hedge : Complex.normSq
      (1 - Theory.PiDigits.T27.phase 1 (1 / 30 : ℝ)) =
      2 * (1 - Real.cos (Real.pi / 15)) := by
    rw [Complex.normSq_sub, Complex.normSq_one]
    have hnorm : Complex.normSq (Theory.PiDigits.T27.phase 1 (1 / 30 : ℝ)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Theory.PiDigits.T27.norm_phase]
      norm_num
    rw [hnorm]
    simp only [one_mul, Complex.conj_re]
    rw [show (Theory.PiDigits.T27.phase 1 (1 / 30 : ℝ)).re =
        Real.cos (Real.pi / 15) by
      rw [Theory.PiDigits.T27.phase]
      convert Complex.exp_ofReal_mul_I_re (Real.pi / 15) using 1 <;> push_cast <;> ring]
    ring
  rw [hedge]
  change 2 / (10 : ℝ) ^ 2 * fejerFactor 10 (1 / 30 : ℝ) ^ 2 -
      1 / 2 * (2 * (1 - Real.cos (Real.pi / 15)) *
        fejerFactor 10 (1 / 30 : ℝ) ^ 2) ≤ 0
  have hfac : 2 / (10 : ℝ) ^ 2 - (1 - Real.cos (Real.pi / 15)) < 0 := by
    norm_num
    linarith [cos_pi_div_fifteen_lt_jacksonBeta_ten]
  have hsq : 0 ≤ fejerFactor 10 (1 / 30 : ℝ) ^ 2 := sq_nonneg _
  nlinarith

set_option maxRecDepth 100000 in
/-- Exact strictness at the actual decimal scale: the boundary-matched
directional predicate accepts the singleton `x₀ = 1/12`, while the Jackson
directional predicate rejects the same singleton and target interval.

This is a generic finite separator, not a statement about the orbit of pi. -/
theorem boundary_directional_decimalScale_ten_strict_vs_jackson :
    let x : ℕ → ℝ := fun _ => 1 / 12
    directionalBoundaryDefect x 1 10 0 < boundaryZeroCoefficient 10 ∧
      ¬ directionalJacksonDefect x 1 10 0 <
        aggregatedCoefficient (jacksonCoefficient 10 10)
          (@jacksonFrequency 10) 0 := by
  dsimp only
  constructor
  · unfold directionalBoundaryDefect
    rw [show (0 : ℝ) + ((10 : ℕ) : ℝ)⁻¹ / 2 = 1 / 20 by norm_num]
    rw [singleton_directional_defect_eq_zero_sub_minorant
      (boundaryCoefficient 10) (@jacksonFrequency 10) (boundaryMinorant 10)
      (fun _ => rfl)]
    rw [show (1 / 12 : ℝ) - 1 / 20 = 1 / 30 by norm_num]
    change boundaryZeroCoefficient 10 -
      (boundaryMinorant 10 (1 / 30 : ℝ)).re < boundaryZeroCoefficient 10
    linarith [boundaryMinorant_ten_one_thirtieth_pos]
  · unfold directionalJacksonDefect
    rw [show (0 : ℝ) + ((10 : ℕ) : ℝ)⁻¹ / 2 = 1 / 20 by norm_num]
    rw [singleton_directional_defect_eq_zero_sub_minorant
      (jacksonCoefficient 10 10) (@jacksonFrequency 10) (jacksonMinorant 10 10)
      (fun _ => rfl)]
    rw [show (1 / 12 : ℝ) - 1 / 20 = 1 / 30 by norm_num]
    linarith [jacksonMinorant_ten_one_thirtieth_nonpos]

end Theory.PiDigits.BoundaryDecimalScaleSeparator

#print axioms Theory.PiDigits.BoundaryDecimalScaleSeparator.boundary_directional_decimalScale_ten_strict_vs_jackson
