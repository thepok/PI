import TheoryLib.PiQuantitativeBlockHitting.T150T150BoundaryKernelFloors

/-!
# T151: root-grid projected boundary-layer floor

The exact T149 projector combines one global kernel floor with the sharper
away-from-the-central-lobe floor at all remaining root-grid points.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace Theory.PiDigits.BoundaryProjectedLayerFloor

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.BoundaryRootGridProjection
open Theory.PiDigits.BoundaryKernelFloors

private lemma rootGrid_sum_gt
    (q d : ℕ) (hq : 1000 ≤ q) (hd : 10 ≤ d) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -(193 / 1000 : ℝ) -
        (d - 1 : ℕ) * (8 * (d : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2)) <
      ∑ r ∈ range d, (boundaryMinorant q ((t + r) / d)).re := by
  classical
  have hd0 : 0 < d := by omega
  let f : ℕ → ℝ := fun r => (boundaryMinorant q ((t + r) / d)).re
  let F : ℝ := 8 * (d : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2)
  by_cases hhalf : t ≤ 1 / 2
  · have hzero : -(193 / 1000 : ℝ) < f 0 := by
      apply boundaryMinorant_re_gt_neg_193 q hq
      · dsimp [f]
        positivity
      · dsimp [f]
        apply (div_lt_one (by positivity : (0 : ℝ) < d)).2
        have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
        norm_num
        linarith
    have hfar : ∀ r ∈ range d \ {0}, -F ≤ f r := by
      intro r hr
      have hrange := mem_range.mp (mem_sdiff.mp hr).1
      have hr0 : r ≠ 0 := by simpa using (mem_sdiff.mp hr).2
      have hr1 : 1 ≤ r := by omega
      apply le_of_lt
      apply boundaryMinorant_re_gt_neg_eight_mul_sq_div q d (by omega) hd
      · dsimp [f, F]
        have hdR : (0 : ℝ) < d := by positivity
        apply (le_div_iff₀ hdR).2
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
        field_simp
        nlinarith
      · dsimp [f, F]
        have hdR : (0 : ℝ) < d := by positivity
        apply (div_le_iff₀ hdR).2
        have hrTop : r ≤ d - 1 := by omega
        have hrTopR : (r : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hrTop
        rw [Nat.cast_sub (by omega : 1 ≤ d)] at hrTopR
        norm_num at hrTopR
        field_simp
        nlinarith
    have hsumFar : (card (range d \ {0}) : ℝ) * (-F) ≤
        ∑ r ∈ range d \ {0}, f r := by
      simpa [mul_comm] using sum_le_sum hfar
    have hcard : card (range d \ {0}) = d - 1 := by
      simp [Finset.card_sdiff, hd0]
    change -(193 / 1000 : ℝ) - (d - 1 : ℕ) * F < ∑ r ∈ range d, f r
    rw [sum_eq_add_sum_diff_singleton 0 f (fun h => (h (by simp [hd0])).elim)]
    rw [hcard] at hsumFar
    dsimp [F] at hsumFar ⊢
    linarith
  · let e : ℕ := d - 1
    have heMem : e ∈ range d := by dsimp [e]; simp [hd0]
    have hglobal : -(193 / 1000 : ℝ) < f e := by
      apply boundaryMinorant_re_gt_neg_193 q hq
      · dsimp [f, e]
        positivity
      · dsimp [f, e]
        apply (div_lt_one (by positivity : (0 : ℝ) < d)).2
        rw [Nat.cast_sub (by omega : 1 ≤ d)]
        norm_num
        nlinarith
    have hfar : ∀ r ∈ range d \ {e}, -F ≤ f r := by
      intro r hr
      have hrange := mem_range.mp (mem_sdiff.mp hr).1
      have hre : r ≠ e := by simpa using (mem_sdiff.mp hr).2
      have hrTop : r ≤ d - 2 := by dsimp [e] at hre; omega
      apply le_of_lt
      apply boundaryMinorant_re_gt_neg_eight_mul_sq_div q d (by omega) hd
      · dsimp [f, F]
        have hdR : (0 : ℝ) < d := by positivity
        apply (le_div_iff₀ hdR).2
        have htHalf : 1 / 2 < t := lt_of_not_ge hhalf
        field_simp
        nlinarith
      · dsimp [f, F]
        have hdR : (0 : ℝ) < d := by positivity
        apply (div_le_iff₀ hdR).2
        have hrTopR : (r : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by exact_mod_cast hrTop
        rw [Nat.cast_sub (by omega : 2 ≤ d)] at hrTopR
        norm_num at hrTopR
        field_simp
        nlinarith
    have hsumFar : (card (range d \ {e}) : ℝ) * (-F) ≤
        ∑ r ∈ range d \ {e}, f r := by
      simpa [mul_comm] using sum_le_sum hfar
    have hcard : card (range d \ {e}) = d - 1 := by
      simp [Finset.card_sdiff, heMem]
    change -(193 / 1000 : ℝ) - (d - 1 : ℕ) * F < ∑ r ∈ range d, f r
    rw [sum_eq_add_sum_diff_singleton e f (fun h => (h heMem).elim)]
    rw [hcard] at hsumFar
    dsimp [F] at hsumFar ⊢
    linarith

/-- Exact floor for one divisibility layer obtained from its root-grid
projection. -/
theorem divisibleBoundaryPolynomial_re_gt_of_mem_Ico
    (q d : ℕ) (hq : 1000 ≤ q) (hd : 10 ≤ d) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -(193 / (2000 * (d : ℝ))) -
        4 * (d : ℝ) * (d - 1 : ℕ) / (9 * (q : ℝ) ^ 2) -
        boundaryZeroCoefficient q / 2 <
      (divisibleBoundaryPolynomial q d t).re := by
  have hd0 : 0 < d := by omega
  have hq0 : 0 < q := by omega
  have hsum := rootGrid_sum_gt q d hq hd t ht0 ht1
  have hproj := rootGridProjection_eq q d hq0 hd0 t
  have hdR : (0 : ℝ) < d := by positivity
  have havg := mul_lt_mul_of_pos_left hsum (one_div_pos.mpr hdR)
  rw [← hproj] at havg
  field_simp at havg ⊢
  nlinarith [sq_pos_of_pos (show (0 : ℝ) < (q : ℕ) by positivity)]

private lemma divisibleBoundaryPolynomial_fract
    (q d : ℕ) (t : ℝ) :
    divisibleBoundaryPolynomial q d (Int.fract t) =
      divisibleBoundaryPolynomial q d t := by
  unfold divisibleBoundaryPolynomial
  apply Finset.sum_congr rfl
  intro h hh
  change (positiveBoundaryCoefficient q h : ℂ) *
      Theory.PiDigits.T27.phase ((h / d : ℕ) : ℤ) (Int.fract t) =
    (positiveBoundaryCoefficient q h : ℂ) *
      Theory.PiDigits.T27.phase ((h / d : ℕ) : ℤ) t
  unfold Theory.PiDigits.T27.phase
  rw [Theory.PiDigits.T29.phase_fract_eq_phase]

/-- Periodic global form of the projected-layer floor. -/
theorem divisibleBoundaryPolynomial_re_gt
    (q d : ℕ) (hq : 1000 ≤ q) (hd : 10 ≤ d) (t : ℝ) :
    -(193 / (2000 * (d : ℝ))) -
        4 * (d : ℝ) * (d - 1 : ℕ) / (9 * (q : ℝ) ^ 2) -
        boundaryZeroCoefficient q / 2 <
      (divisibleBoundaryPolynomial q d t).re := by
  rw [← divisibleBoundaryPolynomial_fract q d t]
  exact divisibleBoundaryPolynomial_re_gt_of_mem_Ico q d hq hd (Int.fract t)
    (Int.fract_nonneg t) (Int.fract_lt_one t)

end Theory.PiDigits.BoundaryProjectedLayerFloor

#print axioms Theory.PiDigits.BoundaryProjectedLayerFloor.divisibleBoundaryPolynomial_re_gt
