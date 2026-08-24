import TheoryLib.PiQuantitativeBlockHitting.T121T121WeightedNaturalScaleCriterion

/-!
# T122: frequency-aggregated Jackson frontier

T120/T121 expose the exact coefficient-weighted load before the worst-mode
step.  That load still takes absolute values once per Jackson index, even when
many indices carry the same Fourier frequency.  The underlying trigonometric
polynomial first adds all coefficients in one frequency fibre.

This module performs that exact regrouping before the triangle inequality.
The resulting frequency-aggregated load is bounded above by the T120 weighted
load, and its pi cancellation premise still implies canonical V1.  Thus it is
a strictly more economical analytic target once a separator is supplied.

No cancellation estimate is proved for pi, and V1 is not proved
unconditionally.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.ExactNaturalScaleResonance
open Theory.PiDigits.WeightedNaturalScaleFrontier

/-- Indices carrying nonzero Fourier frequency. -/
def nonzeroFrequencyIndices
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frequency : ι → ℤ) : Finset ι :=
  Finset.univ.filter fun i => frequency i ≠ 0

/-- The finite set of nonzero frequencies actually represented by the
presentation. -/
def nonzeroFrequencySupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frequency : ι → ℤ) : Finset ℤ :=
  (nonzeroFrequencyIndices frequency).image frequency

/-- The exact coefficient obtained after summing one nonzero frequency fibre. -/
def frequencyCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ) (h : ℤ) : ℝ :=
  ∑ i in nonzeroFrequencyIndices frequency with frequency i = h,
    coefficient i

/-- The normalized Fourier load after exact coefficient aggregation at each
represented nonzero frequency. -/
def normalizedFrequencyAggregatedFourierLoad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ h in nonzeroFrequencySupport frequency,
      |frequencyCoefficient coefficient frequency h| *
        ‖Theory.PiDigits.T27.exponentialSum x N h‖) / (N : ℝ)

/-- Regroup a nonzero Fourier presentation by its exact integer frequency. -/
theorem nonzeroFourierSum_eq_frequencyAggregated
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (value : ℤ → ℂ) (t : ℝ) :
    (∑ i in nonzeroFrequencyIndices frequency,
        coefficient i * Theory.PiDigits.T27.phase (frequency i) t *
          value (frequency i)) =
      ∑ h in nonzeroFrequencySupport frequency,
        frequencyCoefficient coefficient frequency h *
          Theory.PiDigits.T27.phase h t * value h := by
  classical
  have hmaps : ∀ i ∈ nonzeroFrequencyIndices frequency,
      frequency i ∈ nonzeroFrequencySupport frequency := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  calc
    (∑ i in nonzeroFrequencyIndices frequency,
        coefficient i * Theory.PiDigits.T27.phase (frequency i) t *
          value (frequency i)) =
      ∑ h in nonzeroFrequencySupport frequency,
        ∑ i in nonzeroFrequencyIndices frequency with frequency i = h,
          coefficient i * Theory.PiDigits.T27.phase (frequency i) t *
            value (frequency i) := by
      symm
      simpa using
        (Finset.sum_fiberwise_of_maps_to
          (s := nonzeroFrequencyIndices frequency)
          (t := nonzeroFrequencySupport frequency)
          (g := frequency) hmaps
          (fun i => coefficient i *
            Theory.PiDigits.T27.phase (frequency i) t *
              value (frequency i)))
    _ = ∑ h in nonzeroFrequencySupport frequency,
        frequencyCoefficient coefficient frequency h *
          Theory.PiDigits.T27.phase h t * value h := by
      apply Finset.sum_congr rfl
      intro h hh
      symm
      rw [frequencyCoefficient, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hfrequency : frequency i = h := (Finset.mem_filter.mp hi).2
      rw [hfrequency]

/-- A nonpositive finite Fourier presentation with positive zero mode forces
its exact frequency-aggregated nonzero load to dominate the zero-mode lower
bound.  This is the pre-index-triangle-inequality obstruction. -/
theorem finiteFourierPresentation_frequencyAggregated_obstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (center c0 : ℝ)
    (hN : 0 < N)
    (hzero : c0 ≤ ∑ i with frequency i = 0, coefficient i)
    (hnonpos : ∀ j < N,
      (∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)).re ≤ 0) :
    c0 ≤ normalizedFrequencyAggregatedFourierLoad
      coefficient frequency x N := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let z : ℂ := ∑ i in nonzeroFrequencyIndices frequency,
    coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
      Theory.PiDigits.T27.exponentialSum x N (frequency i)
  have htotal :
      (∑ j ∈ Finset.range N, ∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)).re ≤ 0 := by
    simp_rw [← Complex.reCLM_apply]
    rw [map_sum]
    exact Finset.sum_nonpos fun j hj => hnonpos j (Finset.mem_range.mp hj)
  have hfourier :
      (∑ j ∈ Finset.range N, ∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)) =
      ∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
        Theory.PiDigits.T27.exponentialSum x N (frequency i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Theory.PiDigits.T27.exponentialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show x j - center = -center + x j by ring,
      Theory.PiDigits.T27.phase_add_real]
    ring
  rw [hfourier] at htotal
  have hsplit :
      (∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
        Theory.PiDigits.T27.exponentialSum x N (frequency i)) =
      (N : ℝ) * (∑ i with frequency i = 0, coefficient i) + z := by
    calc
      (∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
          Theory.PiDigits.T27.exponentialSum x N (frequency i)) =
        (∑ i with frequency i = 0, coefficient i *
          Theory.PiDigits.T27.phase (frequency i) (-center) *
            Theory.PiDigits.T27.exponentialSum x N (frequency i)) +
        ∑ i with frequency i ≠ 0, coefficient i *
          Theory.PiDigits.T27.phase (frequency i) (-center) *
            Theory.PiDigits.T27.exponentialSum x N (frequency i) :=
          (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => frequency i = 0) _).symm
      _ = (N : ℝ) * (∑ i with frequency i = 0, coefficient i) + z := by
        dsimp [z, nonzeroFrequencyIndices]
        congr 1
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hz := (Finset.mem_filter.mp hi).2
        simp [hz, Theory.PiDigits.T27.phase_zero,
          Theory.PiDigits.T27.exponentialSum_zero]
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
  have hzgroup :
      z = ∑ h in nonzeroFrequencySupport frequency,
        frequencyCoefficient coefficient frequency h *
          Theory.PiDigits.T27.phase h (-center) *
            Theory.PiDigits.T27.exponentialSum x N h := by
    dsimp [z]
    exact nonzeroFourierSum_eq_frequencyAggregated
      coefficient frequency
      (fun h => Theory.PiDigits.T27.exponentialSum x N h) (-center)
  have hzupper :
      ‖z‖ ≤ ∑ h in nonzeroFrequencySupport frequency,
        |frequencyCoefficient coefficient frequency h| *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
    rw [hzgroup]
    calc
      ‖∑ h in nonzeroFrequencySupport frequency,
          frequencyCoefficient coefficient frequency h *
            Theory.PiDigits.T27.phase h (-center) *
              Theory.PiDigits.T27.exponentialSum x N h‖ ≤
        ∑ h in nonzeroFrequencySupport frequency,
          ‖frequencyCoefficient coefficient frequency h *
            Theory.PiDigits.T27.phase h (-center) *
              Theory.PiDigits.T27.exponentialSum x N h‖ :=
        norm_sum_le _ _
      _ = ∑ h in nonzeroFrequencySupport frequency,
          |frequencyCoefficient coefficient frequency h| *
            ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Theory.PiDigits.T27.norm_phase, mul_one]
  unfold normalizedFrequencyAggregatedFourierLoad
  exact (le_div_iff₀ hNR).2 (hzlarge.trans hzupper)

/-- Aggregating coefficients by exact frequency can only decrease the T120
index-weighted load. -/
theorem normalizedFrequencyAggregatedFourierLoad_le_weighted
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    normalizedFrequencyAggregatedFourierLoad coefficient frequency x N ≤
      normalizedWeightedFourierLoad coefficient frequency x N := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmaps : ∀ i ∈ nonzeroFrequencyIndices frequency,
      frequency i ∈ nonzeroFrequencySupport frequency := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hnum :
      (∑ h in nonzeroFrequencySupport frequency,
        |frequencyCoefficient coefficient frequency h| *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖) ≤
      ∑ i in nonzeroFrequencyIndices frequency,
        |coefficient i| *
          ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ := by
    calc
      (∑ h in nonzeroFrequencySupport frequency,
          |frequencyCoefficient coefficient frequency h| *
            ‖Theory.PiDigits.T27.exponentialSum x N h‖) ≤
        ∑ h in nonzeroFrequencySupport frequency,
          ∑ i in nonzeroFrequencyIndices frequency with frequency i = h,
            |coefficient i| *
              ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ := by
        apply Finset.sum_le_sum
        intro h hh
        have habs :
            |frequencyCoefficient coefficient frequency h| ≤
              ∑ i in nonzeroFrequencyIndices frequency with frequency i = h,
                |coefficient i| := by
          unfold frequencyCoefficient
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le
              ((nonzeroFrequencyIndices frequency).filter
                (fun i => frequency i = h)) coefficient)
        calc
          |frequencyCoefficient coefficient frequency h| *
              ‖Theory.PiDigits.T27.exponentialSum x N h‖ ≤
            (∑ i in nonzeroFrequencyIndices frequency with frequency i = h,
                |coefficient i|) *
              ‖Theory.PiDigits.T27.exponentialSum x N h‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg _)
          _ = ∑ i in nonzeroFrequencyIndices frequency with frequency i = h,
              |coefficient i| *
                ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            have hfrequency : frequency i = h := (Finset.mem_filter.mp hi).2
            rw [hfrequency]
      _ = ∑ i in nonzeroFrequencyIndices frequency,
          |coefficient i| *
            ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ := by
        exact Finset.sum_fiberwise_of_maps_to
          (s := nonzeroFrequencyIndices frequency)
          (t := nonzeroFrequencySupport frequency)
          (g := frequency) hmaps
          (fun i => |coefficient i| *
            ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖)
  unfold normalizedFrequencyAggregatedFourierLoad
  unfold normalizedWeightedFourierLoad
  rw [div_le_div_iff_of_pos_right hNR]
  simpa only [nonzeroFrequencyIndices] using hnum

/-- The frequency-aggregated load for the exact order-`q` Jackson
presentation. -/
def jacksonFrequencyAggregatedFourierLoad
    (x : ℕ → ℝ) (N q : ℕ) : ℝ :=
  normalizedFrequencyAggregatedFourierLoad
    (jacksonCoefficient q q) (@jacksonFrequency q) x N

/-- The frequency-aggregated Jackson load is no larger than T120's
index-weighted Jackson load. -/
theorem jacksonFrequencyAggregatedFourierLoad_le_weighted
    (x : ℕ → ℝ) (N q : ℕ) (hN : 0 < N) :
    jacksonFrequencyAggregatedFourierLoad x N q ≤
      jacksonWeightedFourierLoad x N q := by
  exact normalizedFrequencyAggregatedFourierLoad_le_weighted
    (jacksonCoefficient q q) (@jacksonFrequency q) x N hN

/-- An empty interval of length `1/q` forces the exact
frequency-aggregated Jackson load to dominate the same zero-mode lower bound
used by T120. -/
theorem finite_empty_decimalInterval_frequencyAggregated_obstruction
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ≤
      jacksonFrequencyAggregatedFourierLoad x N q := by
  let center := a + (q : ℝ)⁻¹ / 2
  unfold jacksonFrequencyAggregatedFourierLoad
  refine finiteFourierPresentation_frequencyAggregated_obstruction
    (jacksonCoefficient q q) (@jacksonFrequency q)
    x N center
    (1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3))
    hN (jackson_zeroCoefficient_self_lower q hq) ?_
  intro j hj
  simpa only [jacksonMinorant, center] using
    jacksonMinorant_re_nonpos_outside q q hq hq (x j) a
      (hx j hj) ha haq (hempty j hj)

/-- Direct contrapositive of the frequency-aggregated empty-interval
obstruction. -/
theorem finite_decimalInterval_hit_of_frequencyAggregated_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall :
      jacksonFrequencyAggregatedFourierLoad x N q <
        1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  have hlarge :=
    finite_empty_decimalInterval_frequencyAggregated_obstruction
      x N q a hN hq hx ha haq (fun j hj => hno j hj)
  exact (not_lt_of_ge hlarge) hsmall

/-- A missing decimal word before time `N` forces the frequency-aggregated
order-`10^|s|` obstruction for the exact base-ten orbit of pi. -/
theorem piOrbit_frequencyAggregated_obstruction_of_missingBefore
    (s : List (Fin 10)) (N : ℕ) (hN : 0 < N)
    (hmissing : ∀ n : ℕ, n < N → ¬ ∀ i : ℕ, ∀ hi : i < s.length,
      Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩) :
    1 / (3 * (10 : ℝ) ^ s.length) +
        2 / (3 * ((10 : ℝ) ^ s.length) ^ 3) ≤
      jacksonFrequencyAggregatedFourierLoad
        Theory.PiDigits.T27.piFractionalOrbit N (10 ^ s.length) := by
  let q := 10 ^ s.length
  let a := Theory.PiDigits.T27.decimalCylinderLeft s
  have hq : 0 < q := by positivity
  have hempty : ∀ j < N,
      Theory.PiDigits.T27.piFractionalOrbit j ∉
        Set.Ico a (a + (q : ℝ)⁻¹) := by
    intro j hj hmem
    apply hmissing j hj
    have hinterval : Theory.PiDigits.T27.piFractionalOrbit j ∈
        Set.Ico
          ((Theory.PiDigits.T20.wordValue s : ℝ) / (10 : ℝ) ^ s.length)
          (((Theory.PiDigits.T20.wordValue s + 1 : ℕ) : ℝ) /
            (10 : ℝ) ^ s.length) := by
      have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
      rw [hpow] at hmem
      have hmem' : Theory.PiDigits.T27.piFractionalOrbit j ∈
          Set.Ico (Theory.PiDigits.T27.decimalCylinderLeft s)
            (Theory.PiDigits.T27.decimalCylinderLeft s +
              Theory.PiDigits.T27.decimalCylinderLength s.length) := by
        simpa only [a, q, Theory.PiDigits.T27.decimalCylinderLength] using hmem
      rw [Theory.PiDigits.T27.decimalCylinder_interval] at hmem'
      exact hmem'
    have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
      s (Theory.PiDigits.T27.piFractionalOrbit j) hinterval
    intro i hi
    have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
      Real.pi Real.pi_pos.le j i
    exact (Theory.PiDigits.T20.decimalDigit_pi (j + i)).symm.trans
      (hshift.symm.trans (hdigits i hi))
  simpa only [q, a, Nat.cast_pow, Nat.cast_ofNat,
    Theory.PiDigits.T27.decimalCylinderLength] using
    finite_empty_decimalInterval_frequencyAggregated_obstruction
      Theory.PiDigits.T27.piFractionalOrbit N q a hN hq
      (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (by
        have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
        rw [hpow]
        simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
          Theory.PiDigits.T27.decimalCylinderRight_le_one s)
      hempty

/-- The open frequency-aggregated natural-scale cancellation target for pi. -/
def PiNaturalScaleFrequencyAggregatedCancellation : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    jacksonFrequencyAggregatedFourierLoad
        Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) <
      1 / (3 * (10 : ℝ) ^ k) +
        2 / (3 * ((10 : ℝ) ^ k) ^ 3)

/-- The current T120/T121 weighted pi premise implies the new
frequency-aggregated premise. -/
theorem piNaturalScaleWeightedCancellation_implies_frequencyAggregated
    (hweighted : PiNaturalScaleWeightedCancellation) :
    PiNaturalScaleFrequencyAggregatedCancellation := by
  intro k hk
  obtain ⟨N, hN, hsmall⟩ := hweighted k hk
  refine ⟨N, hN, ?_⟩
  exact lt_of_le_of_lt
    (jacksonFrequencyAggregatedFourierLoad_le_weighted
      Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) hN)
    hsmall

/-- The frequency-aggregated cancellation target still implies canonical V1.
The premise is not asserted for pi. -/
theorem piNaturalScaleFrequencyAggregatedCancellation_implies_canonicalV1
    (haggregated : PiNaturalScaleFrequencyAggregatedCancellation) :
    Theory.PiDigits.V1 := by
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons d s =>
      obtain ⟨N, hN, hsmall⟩ :=
        haggregated (d :: s).length (by simp)
      by_contra hmissing
      have hmissingBefore : ∀ n : ℕ, n < N →
          ¬ ∀ i : ℕ, ∀ hi : i < (d :: s).length,
            Theory.PiDigits.piDigit (n + i) =
              (d :: s).get ⟨i, hi⟩ := by
        intro n hn hocc
        exact hmissing ⟨n, hocc⟩
      have hlarge :=
        piOrbit_frequencyAggregated_obstruction_of_missingBefore
          (d :: s) N hN hmissingBefore
      exact (not_lt_of_ge hlarge) hsmall

end Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier

#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.nonzeroFourierSum_eq_frequencyAggregated
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.finiteFourierPresentation_frequencyAggregated_obstruction
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.normalizedFrequencyAggregatedFourierLoad_le_weighted
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.finite_empty_decimalInterval_frequencyAggregated_obstruction
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.finite_decimalInterval_hit_of_frequencyAggregated_smallness
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.piOrbit_frequencyAggregated_obstruction_of_missingBefore
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.piNaturalScaleWeightedCancellation_implies_frequencyAggregated
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.piNaturalScaleFrequencyAggregatedCancellation_implies_canonicalV1
