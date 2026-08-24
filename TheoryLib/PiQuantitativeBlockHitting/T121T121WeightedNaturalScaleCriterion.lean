import TheoryLib.PiQuantitativeBlockHitting.T122T122FrequencyAggregatedNaturalScale

/-!
# Weighted natural-scale cancellation criterion

This file specializes the exact weighted obstruction to the base-ten orbit of
pi and compares it with T19's pointwise condition.

The mathematical gain is literal and formally testable:

* T19's pointwise premise implies the weighted premise.
* The converse fails on an explicit two-point grid.
* The weighted pi premise implies canonical V1.

The pi premise remains open.  No unconditional digit-occurrence claim is made.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.WeightedNaturalScaleFrontier


/-- A missing decimal word in the first `N` starts forces the weighted
order-`10^|s|` obstruction for the base-ten orbit of pi. -/
theorem piOrbit_weighted_obstruction_of_missingBefore
    (s : List (Fin 10)) (N : ℕ) (hN : 0 < N)
    (hmissing : ∀ n : ℕ, n < N → ¬ ∀ i : ℕ, ∀ hi : i < s.length,
      Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩) :
    1 / (3 * (10 : ℝ) ^ s.length) +
        2 / (3 * ((10 : ℝ) ^ s.length) ^ 3) ≤
      jacksonWeightedFourierLoad Theory.PiDigits.T27.piFractionalOrbit N
        (10 ^ s.length) := by
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
    finite_empty_decimalInterval_weighted_obstruction
      Theory.PiDigits.T27.piFractionalOrbit N q a hN hq
      (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (by
        have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
        rw [hpow]
        simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
          Theory.PiDigits.T27.decimalCylinderRight_le_one s)
      hempty

/-- The weighted finite cancellation target for pi.  This is an open
hypothesis: the module proves only that it is sufficient for V1. -/
def PiNaturalScaleWeightedCancellation : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    jacksonWeightedFourierLoad Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) <
      1 / (3 * (10 : ℝ) ^ k) +
        2 / (3 * ((10 : ℝ) ^ k) ^ 3)

/-- The weighted cancellation target implies canonical V1.  No assertion is
made that pi satisfies the target. -/
theorem piNaturalScaleWeightedCancellation_implies_canonicalV1
    (hweighted : PiNaturalScaleWeightedCancellation) :
    Theory.PiDigits.V1 := by
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons d s =>
      obtain ⟨N, hN, hsmall⟩ :=
        hweighted (d :: s).length (by simp)
      by_contra hmissing
      have hmissingBefore : ∀ n : ℕ, n < N →
          ¬ ∀ i : ℕ, ∀ hi : i < (d :: s).length,
            Theory.PiDigits.piDigit (n + i) =
              (d :: s).get ⟨i, hi⟩ := by
        intro n hn hocc
        exact hmissing ⟨n, hocc⟩
      have hlarge :=
        piOrbit_weighted_obstruction_of_missingBefore
          (d :: s) N hN hmissingBefore
      exact (not_lt_of_ge hlarge) hsmall

/-- T19's pointwise finite hypothesis implies the weighted finite hypothesis.
The implication loses no frequency support information beyond the coefficient
mass identity `4`; its converse is false by the explicit separator below. -/
theorem exact_finite_frequency_hypothesis_implies_weighted
    (x : ℕ → ℝ) (N q : ℕ) (hq : 0 < q)
    (hexact : ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) :
    jacksonWeightedFourierLoad x N q <
      1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) := by
  classical
  let t : ℝ :=
    1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hmass :
      (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex q,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q i|) = 4 := by
    rw [Theory.PiDigits.ExactNaturalScaleResonance.jacksonCoefficient_mass_general q q hq hq]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [hqR]
    norm_num
  unfold jacksonWeightedFourierLoad normalizedWeightedFourierLoad
  calc
    (∑ i with Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q i| *
          ‖Theory.PiDigits.T27.exponentialSum x N (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i)‖) / (N : ℝ) =
      ∑ i with Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q i| *
          (‖Theory.PiDigits.T27.exponentialSum x N (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i)‖ /
            (N : ℝ)) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ ≤ ∑ i with Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q i| * t := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact (hexact (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i)
          (Finset.mem_filter.mp hi).2
          (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency_bound i)).le
      · exact abs_nonneg _
    _ = (∑ i with Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q i|) * t := by
      rw [Finset.sum_mul]
    _ ≤ (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex q,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q i|) * t := by
      apply mul_le_mul_of_nonneg_right _ ht
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> simp [abs_nonneg]
    _ = 4 * t := by rw [hmass]
    _ < 1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) := by
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have heq :
          4 * t =
            (1 / (3 * (q : ℝ)) +
              2 / (3 * (q : ℝ) ^ 3)) / 2 := by
        dsimp [t]
        field_simp [hqR.ne']
        ring
      rw [heq]
      have hc :
          0 < 1 / (3 * (q : ℝ)) +
            2 / (3 * (q : ℝ) ^ 3) := by positivity
      linarith

/-- T19's open pointwise pi premise implies the weighted pi premise. -/
theorem piNaturalScaleCancellationExact_implies_weighted
    (hexact : Theory.PiDigits.ExactNaturalScaleResonance.PiNaturalScaleCancellationExact) :
    PiNaturalScaleWeightedCancellation := by
  intro k hk
  obtain ⟨N, hN, hsmall⟩ := hexact k hk
  refine ⟨N, hN, ?_⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (exact_finite_frequency_hypothesis_implies_weighted
      Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) (by positivity)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hsmall))

lemma jacksonFrequency_one_natAbs_eq_one_of_ne_zero
    (i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 1)
    (hi : Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0) :
    (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i).natAbs = 1 := by
  rcases i with i | i
  · rcases i with ⟨r, s, u, v⟩
    fin_cases r
    fin_cases s
    fin_cases u
    fin_cases v
    simp [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency] at hi
  · rcases i with ⟨⟨b, r⟩, ⟨c, s⟩⟩
    fin_cases r
    fin_cases s
    cases b <;> cases c <;>
      simp [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency, Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency] at hi ⊢

lemma uniformGridTwo_exponentialSum_eq_zero_of_natAbs_eq_one
    (h : ℤ) (hh : h.natAbs = 1) :
    Theory.PiDigits.T27.exponentialSum (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 2) 2 h = 0 := by
  have hpos :=
    Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid_exponentialSum_nat_eq_zero
      h.natAbs 2 (by norm_num) (by omega) (by omega)
  rcases Int.natAbs_eq h with hEq | hEq
  · rw [hEq, hpos]
  · rw [hEq, Theory.PiDigits.SharperNaturalScaleResonance.exponentialSum_neg, hpos, map_zero]

lemma jacksonWeightedFourierLoad_uniformGridTwo_one :
    jacksonWeightedFourierLoad (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 2) 2 1 = 0 := by
  unfold jacksonWeightedFourierLoad normalizedWeightedFourierLoad
  have hsum :
      (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 1 with Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 1 1 i| *
          ‖Theory.PiDigits.T27.exponentialSum (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 2) 2
            (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i)‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hfreq :=
      jacksonFrequency_one_natAbs_eq_one_of_ne_zero i
        (Finset.mem_filter.mp hi).2
    rw [uniformGridTwo_exponentialSum_eq_zero_of_natAbs_eq_one
      (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i) hfreq]
    simp
  rw [hsum]
  norm_num

/-- Literal strictness separator.  The two-point grid has zero weighted load
at Jackson order `1`, because the presentation's nonzero support is only
`±1`; T19's pointwise hypothesis additionally controls the crude endpoint
frequency `2`, where this grid is fully resonant. -/
theorem weighted_finite_frequency_hypothesis_strict_vs_exact :
    ∃ x : ℕ → ℝ, ∃ N q : ℕ, 0 < N ∧ 0 < q ∧
      (jacksonWeightedFourierLoad x N q <
        1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) ∧
      ¬ (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q →
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
          1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) := by
  refine ⟨Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 2, 2, 1, by norm_num, by norm_num, ?_, ?_⟩
  · rw [jacksonWeightedFourierLoad_uniformGridTwo_one]
    norm_num
  · intro hexact
    have htwo := hexact 2 (by norm_num) (by norm_num)
    have hsum :
        Theory.PiDigits.T27.exponentialSum (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 2) 2 (2 : ℤ) =
          (2 : ℂ) := by
      simpa using Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid_exponentialSum_self 2 (by norm_num)
    rw [hsum] at htwo
    norm_num at htwo

end Theory.PiDigits.WeightedNaturalScaleFrontier

#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.piOrbit_weighted_obstruction_of_missingBefore
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.piNaturalScaleWeightedCancellation_implies_canonicalV1
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.exact_finite_frequency_hypothesis_implies_weighted
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.piNaturalScaleCancellationExact_implies_weighted
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.weighted_finite_frequency_hypothesis_strict_vs_exact
