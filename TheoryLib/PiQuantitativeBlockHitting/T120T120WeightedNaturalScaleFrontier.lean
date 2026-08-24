import TheoryLib.PiQuantitativeBlockHitting.T19T19ExactNaturalScaleResonance

/-!
# Weighted natural-scale Fourier frontier

T19 turns an empty decimal cylinder into one large Fourier mode by bounding the
whole nonzero Fourier contribution with a worst-mode maximum.  The argument
first proves a stronger statement: the coefficient-weighted sum of all
nonzero Fourier magnitudes is large.

This module exposes that pre-maximum obstruction.  Its cancellation premise is
strictly weaker than T19's pointwise premise because it permits uneven
cancellation across frequencies.  The final pi theorem remains conditional:
no weighted cancellation estimate is asserted for pi, and V1 is not proved
unconditionally.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.WeightedNaturalScaleFrontier

namespace T6 = Theory.PiDigits.PiNaturalScaleResonanceObstruction
namespace T18 = Theory.PiDigits.SharperNaturalScaleResonance
namespace T19 = Theory.PiDigits.ExactNaturalScaleResonance
namespace T20 = Theory.PiDigits.DigitBlockOrbitTarget
namespace T27 = Theory.PiDigits.T27

/-- The exact coefficient-weighted nonzero Fourier load, normalized by the
sample size. -/
def normalizedWeightedFourierLoad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ i with frequency i ≠ 0,
      |coefficient i| *
        ‖T27.exponentialSum x N (frequency i)‖) / (N : ℝ)

/-- A nonpositive finite Fourier presentation with positive zero mode forces
its full coefficient-weighted nonzero Fourier load to dominate the zero-mode
lower bound.  Unlike the earlier resonance theorem, no maximum over modes and
no coefficient-mass relaxation is used. -/
theorem finiteFourierPresentation_weighted_obstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (center c0 : ℝ)
    (hN : 0 < N)
    (hzero : c0 ≤ ∑ i with frequency i = 0, coefficient i)
    (hnonpos : ∀ j < N,
      (∑ i, coefficient i *
        T27.phase (frequency i) (x j - center)).re ≤ 0) :
    c0 ≤ normalizedWeightedFourierLoad coefficient frequency x N := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let z : ℂ := ∑ i with frequency i ≠ 0,
    coefficient i * T27.phase (frequency i) (-center) *
      T27.exponentialSum x N (frequency i)
  have htotal :
      (∑ j ∈ Finset.range N, ∑ i, coefficient i *
        T27.phase (frequency i) (x j - center)).re ≤ 0 := by
    simp_rw [← Complex.reCLM_apply]
    rw [map_sum]
    exact Finset.sum_nonpos fun j hj => hnonpos j (Finset.mem_range.mp hj)
  have hfourier :
      (∑ j ∈ Finset.range N, ∑ i, coefficient i *
        T27.phase (frequency i) (x j - center)) =
      ∑ i, coefficient i * T27.phase (frequency i) (-center) *
        T27.exponentialSum x N (frequency i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [T27.exponentialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show x j - center = -center + x j by ring,
      T27.phase_add_real]
    ring
  rw [hfourier] at htotal
  have hsplit :
      (∑ i, coefficient i * T27.phase (frequency i) (-center) *
        T27.exponentialSum x N (frequency i)) =
      (N : ℝ) * (∑ i with frequency i = 0, coefficient i) + z := by
    calc
      (∑ i, coefficient i * T27.phase (frequency i) (-center) *
          T27.exponentialSum x N (frequency i)) =
        (∑ i with frequency i = 0, coefficient i *
          T27.phase (frequency i) (-center) *
            T27.exponentialSum x N (frequency i)) +
        ∑ i with frequency i ≠ 0, coefficient i *
          T27.phase (frequency i) (-center) *
            T27.exponentialSum x N (frequency i) :=
          (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => frequency i = 0) _).symm
      _ = (N : ℝ) * (∑ i with frequency i = 0, coefficient i) + z := by
        congr 1
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hz := (Finset.mem_filter.mp hi).2
        simp [hz, T27.phase_zero, T27.exponentialSum_zero]
        ring
  rw [hsplit] at htotal
  have htotal' :
      (N : ℝ) * (∑ i with frequency i = 0, coefficient i) + z.re ≤ 0 := by
    simpa using htotal
  have hzlarge : c0 * (N : ℝ) ≤ ‖z‖ := by
    calc
      c0 * (N : ℝ) ≤
          (N : ℝ) * (∑ i with frequency i = 0, coefficient i) := by
            nlinarith
      _ ≤ -z.re := by linarith
      _ ≤ |z.re| := neg_le_abs _
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzupper :
      ‖z‖ ≤ ∑ i with frequency i ≠ 0,
        |coefficient i| *
          ‖T27.exponentialSum x N (frequency i)‖ := by
    calc
      ‖z‖ ≤ ∑ i with frequency i ≠ 0,
          ‖coefficient i * T27.phase (frequency i) (-center) *
            T27.exponentialSum x N (frequency i)‖ :=
        norm_sum_le _ _
      _ = ∑ i with frequency i ≠ 0,
          |coefficient i| *
            ‖T27.exponentialSum x N (frequency i)‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          T27.norm_phase, mul_one]
  unfold normalizedWeightedFourierLoad
  exact (le_div_iff₀ hNR).2 (hzlarge.trans hzupper)

/-- The normalized weighted load for the exact order-`q` Jackson
presentation used in T19. -/
def jacksonWeightedFourierLoad
    (x : ℕ → ℝ) (N q : ℕ) : ℝ :=
  normalizedWeightedFourierLoad
    (T6.jacksonCoefficient q q) (@T6.jacksonFrequency q) x N

/-- An empty interval of length `1/q` forces the exact Jackson-weighted load
to be at least the sharp zero-mode lower bound from T19. -/
theorem finite_empty_decimalInterval_weighted_obstruction
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ≤
      jacksonWeightedFourierLoad x N q := by
  let center := a + (q : ℝ)⁻¹ / 2
  unfold jacksonWeightedFourierLoad
  refine finiteFourierPresentation_weighted_obstruction
    (T6.jacksonCoefficient q q) (@T6.jacksonFrequency q)
    x N center
    (1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3))
    hN (T19.jackson_zeroCoefficient_self_lower q hq) ?_
  intro j hj
  simpa only [T6.jacksonMinorant, center] using
    T6.jacksonMinorant_re_nonpos_outside q q hq hq (x j) a
      (hx j hj) ha haq (hempty j hj)

/-- Direct contrapositive of the weighted empty-interval obstruction. -/
theorem finite_decimalInterval_hit_of_weighted_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall :
      jacksonWeightedFourierLoad x N q <
        1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  have hlarge :=
    finite_empty_decimalInterval_weighted_obstruction
      x N q a hN hq hx ha haq (fun j hj => hno j hj)
  exact (not_lt_of_ge hlarge) hsmall

end Theory.PiDigits.WeightedNaturalScaleFrontier

#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.finiteFourierPresentation_weighted_obstruction
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.finite_empty_decimalInterval_weighted_obstruction
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.finite_decimalInterval_hit_of_weighted_smallness
