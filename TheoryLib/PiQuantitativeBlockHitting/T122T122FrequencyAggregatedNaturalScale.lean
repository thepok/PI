import TheoryLib.PiQuantitativeBlockHitting.T120T120WeightedNaturalScaleFrontier

/-!
# Frequency-aggregated natural-scale Fourier frontier

The indexed Jackson presentation used by T120 can contain several terms at the
same Fourier frequency.  T120 takes absolute values before those terms are
combined.  This module instead sums the coefficients on each frequency fiber
and takes one absolute value afterwards.

The resulting finite obstruction is proved directly by regrouping the exact
Fourier polynomial before applying the triangle inequality.  It is bounded
above by T120's indexed weighted load, so the corresponding cancellation
premise is weaker.  No cancellation estimate for the decimal orbit of pi is
asserted here.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier

/-- The canonical coefficient obtained after combining every presentation
term carrying the same Fourier frequency. -/
def frequencyAggregatedCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ) (h : ℤ) : ℝ :=
  ∑ i with frequency i = h, coefficient i

/-- The normalized Fourier load after coefficients have first been combined
on each nonzero frequency fiber. -/
def normalizedFrequencyAggregatedFourierLoad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ h ∈ Finset.image frequency
        ((Finset.univ : Finset ι).filter fun i => frequency i ≠ 0),
      |frequencyAggregatedCoefficient coefficient frequency h| *
        ‖Theory.PiDigits.T27.exponentialSum x N h‖) / (N : ℝ)

/-- A nonpositive finite Fourier presentation forces its frequency-aggregated
nonzero load to dominate the zero-mode lower bound.  The regrouping is done
before the triangle inequality, unlike T120's indexed weighted obstruction. -/
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
  let source : Finset ι :=
    Finset.univ.filter fun i => frequency i ≠ 0
  let z : ℂ := ∑ h ∈ Finset.image frequency source,
    frequencyAggregatedCoefficient coefficient frequency h *
      Theory.PiDigits.T27.phase h (-center) *
        Theory.PiDigits.T27.exponentialSum x N h
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
  have hgroup :
      (∑ i ∈ source,
        coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
          Theory.PiDigits.T27.exponentialSum x N (frequency i)) = z := by
    dsimp [z]
    symm
    apply Finset.sum_image'
      (fun i => coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (-center) *
          Theory.PiDigits.T27.exponentialSum x N (frequency i))
    intro i hi
    have hi0 : frequency i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hfiber :
        (Finset.univ.filter fun j => frequency j = frequency i) =
          source.filter fun j => frequency j = frequency i := by
      ext j
      simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hji
        exact ⟨hji.trans_ne hi0, hji⟩
      · exact fun h => h.2
    unfold frequencyAggregatedCoefficient
    rw [hfiber, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : frequency j = frequency i := (Finset.mem_filter.mp hj).2
    rw [hji]
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
        congr 1
        · push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hz := (Finset.mem_filter.mp hi).2
          simp [hz, Theory.PiDigits.T27.phase_zero,
            Theory.PiDigits.T27.exponentialSum_zero]
          ring
        · simpa only [source] using hgroup
  rw [hfourier, hsplit] at htotal
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
      ‖z‖ ≤ ∑ h ∈ Finset.image frequency source,
        |frequencyAggregatedCoefficient coefficient frequency h| *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
    calc
      ‖z‖ ≤ ∑ h ∈ Finset.image frequency source,
          ‖frequencyAggregatedCoefficient coefficient frequency h *
            Theory.PiDigits.T27.phase h (-center) *
              Theory.PiDigits.T27.exponentialSum x N h‖ :=
        norm_sum_le _ _
      _ = ∑ h ∈ Finset.image frequency source,
          |frequencyAggregatedCoefficient coefficient frequency h| *
            ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Theory.PiDigits.T27.norm_phase, mul_one]
  unfold normalizedFrequencyAggregatedFourierLoad
  simpa only [source] using
    ((le_div_iff₀ hNR).2 (hzlarge.trans hzupper))

/-- Combining coefficients on frequency fibers cannot increase the indexed
absolute-value load used by T120. -/
theorem frequencyAggregatedLoad_le_indexedWeightedLoad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    normalizedFrequencyAggregatedFourierLoad coefficient frequency x N ≤
      Theory.PiDigits.WeightedNaturalScaleFrontier.normalizedWeightedFourierLoad
        coefficient frequency x N := by
  classical
  let source : Finset ι :=
    Finset.univ.filter fun i => frequency i ≠ 0
  have hnum :
      (∑ h ∈ Finset.image frequency source,
        |frequencyAggregatedCoefficient coefficient frequency h| *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖) ≤
      ∑ i ∈ source,
        |coefficient i| *
          ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ := by
    calc
      (∑ h ∈ Finset.image frequency source,
          |frequencyAggregatedCoefficient coefficient frequency h| *
            ‖Theory.PiDigits.T27.exponentialSum x N h‖) ≤
        ∑ h ∈ Finset.image frequency source,
          (∑ i ∈ source with frequency i = h, |coefficient i|) *
            ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
          apply Finset.sum_le_sum
          intro h hh
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rcases Finset.mem_image.mp hh with ⟨i, hi, rfl⟩
          have hi0 : frequency i ≠ 0 := (Finset.mem_filter.mp hi).2
          have hfiber :
              (Finset.univ.filter fun j => frequency j = frequency i) =
                source.filter fun j => frequency j = frequency i := by
            ext j
            simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hji
              exact ⟨hji.trans_ne hi0, hji⟩
            · exact fun h => h.2
          unfold frequencyAggregatedCoefficient
          rw [hfiber]
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le (source.filter fun j => frequency j = frequency i)
              coefficient)
      _ = ∑ i ∈ source,
          |coefficient i| *
            ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ := by
        apply Finset.sum_image'
          (fun i => |coefficient i| *
            ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖)
        intro i hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hji : frequency j = frequency i := (Finset.mem_filter.mp hj).2
        rw [hji]
  unfold normalizedFrequencyAggregatedFourierLoad
  unfold Theory.PiDigits.WeightedNaturalScaleFrontier.normalizedWeightedFourierLoad
  apply div_le_div_of_nonneg_right
  · simpa only [source] using hnum
  · positivity

/-- The frequency-aggregated load for the exact order-`q` Jackson
presentation. -/
def jacksonFrequencyAggregatedFourierLoad
    (x : ℕ → ℝ) (N q : ℕ) : ℝ :=
  normalizedFrequencyAggregatedFourierLoad
    (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q)
    (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency q)
    x N

/-- An empty interval of length `1/q` forces the frequency-aggregated Jackson
load to be at least the exact zero-mode lower bound. -/
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
    (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q)
    (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency q)
    x N center
    (1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3))
    hN
    (Theory.PiDigits.ExactNaturalScaleResonance.jackson_zeroCoefficient_self_lower
      q hq) ?_
  intro j hj
  simpa only
      [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonMinorant, center] using
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonMinorant_re_nonpos_outside
      q q hq hq (x j) a (hx j hj) ha haq (hempty j hj)

/-- Direct contrapositive of the frequency-aggregated obstruction. -/
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

/-- The frequency-aggregated finite cancellation target for pi.  It remains
an open hypothesis. -/
def PiNaturalScaleFrequencyAggregatedCancellation : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    jacksonFrequencyAggregatedFourierLoad
        Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) <
      1 / (3 * (10 : ℝ) ^ k) +
        2 / (3 * ((10 : ℝ) ^ k) ^ 3)

/-- A missing decimal word before time `N` forces the frequency-aggregated
order-`10^|s|` obstruction. -/
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

/-- The frequency-aggregated cancellation target implies canonical V1.  No
assertion is made that pi satisfies the target. -/
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

#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.finiteFourierPresentation_frequencyAggregated_obstruction
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.frequencyAggregatedLoad_le_indexedWeightedLoad
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.finite_empty_decimalInterval_frequencyAggregated_obstruction
#print axioms Theory.PiDigits.FrequencyAggregatedNaturalScaleFrontier.piNaturalScaleFrequencyAggregatedCancellation_implies_canonicalV1
