import TheoryLib.PiQuantitativeBlockHitting.T123T123AggregatedJacksonFrontier

/-!
# Directional Jackson cancellation before modulus

For a prescribed interval this file retains the signed real part of the
centered, frequency-regrouped Jackson sum.  This removes the triangle
inequality from the finite interval consumer.  The resulting pi statement is
still conditional: no directional cancellation estimate for pi is asserted.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.DirectionalJacksonFrontier

open Theory.PiDigits.AggregatedJacksonFrontier

/-- The nonzero, frequency-regrouped part of a finite Fourier presentation,
centered at `center`. -/
def centeredAggregatedNonzeroSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (center : ℝ) : ℂ :=
  ∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
    aggregatedCoefficient coefficient frequency h *
      Theory.PiDigits.T27.phase h (-center) *
        Theory.PiDigits.T27.exponentialSum x N h

/-- The signed directional defect.  Unlike a Fourier load it may be negative
and depends on the target interval center. -/
def normalizedDirectionalFourierDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (center : ℝ) : ℝ :=
  -(centeredAggregatedNonzeroSum coefficient frequency x N center).re / (N : ℝ)

/-- Regrouping the nonzero frequencies preserves their signed complex sum. -/
lemma sum_aggregatedCoefficient_mul_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ) (f : ℤ → ℂ) :
    ∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
        aggregatedCoefficient coefficient frequency h * f h =
      ∑ i with frequency i ≠ 0, coefficient i * f (frequency i) := by
  classical
  have h := sum_aggregatedCoefficient_mul coefficient frequency
    (fun h => if h = 0 then 0 else f h)
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ a ∈ Finset.image frequency Finset.univ,
        if a ≠ 0 then aggregatedCoefficient coefficient frequency a * f a else 0) =
      ∑ a ∈ Finset.image frequency Finset.univ,
        aggregatedCoefficient coefficient frequency a *
          (if a = 0 then 0 else f a) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases ha0 : a = 0 <;> simp [ha0]
    _ = ∑ i, coefficient i * (if frequency i = 0 then 0 else f (frequency i)) := h
    _ = ∑ i, if frequency i ≠ 0 then coefficient i * f (frequency i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : frequency i = 0 <;> simp [hi0]

/-- A nonpositive finite Fourier presentation forces a large directional
defect at the prescribed center, before taking any modulus. -/
theorem finiteFourierPresentation_directional_obstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (center c0 : ℝ)
    (hN : 0 < N)
    (hzero : c0 ≤ aggregatedCoefficient coefficient frequency 0)
    (hnonpos : ∀ j < N,
      (∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)).re ≤ 0) :
    c0 ≤ normalizedDirectionalFourierDefect
      coefficient frequency x N center := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let z := centeredAggregatedNonzeroSum coefficient frequency x N center
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
      (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z := by
    calc
      _ = (∑ i with frequency i = 0,
            coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
              Theory.PiDigits.T27.exponentialSum x N (frequency i)) +
          ∑ i with frequency i ≠ 0,
            coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
              Theory.PiDigits.T27.exponentialSum x N (frequency i) :=
          (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => frequency i = 0) _).symm
      _ = (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z := by
        congr 1
        · unfold aggregatedCoefficient
          push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hi0 : frequency i = 0 := (Finset.mem_filter.mp hi).2
          simp [hi0, Theory.PiDigits.T27.phase_zero,
            Theory.PiDigits.T27.exponentialSum_zero]
          ring
        · unfold z centeredAggregatedNonzeroSum
          symm
          simpa only [mul_assoc] using
            (sum_aggregatedCoefficient_mul_ne_zero coefficient frequency
              (fun h => Theory.PiDigits.T27.phase h (-center) *
                Theory.PiDigits.T27.exponentialSum x N h))
  rw [hsplit] at htotal
  have htotal' :
      (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z.re ≤ 0 := by
    simpa using htotal
  unfold normalizedDirectionalFourierDefect
  change c0 ≤ -z.re / (N : ℝ)
  rw [le_div_iff₀ hNR]
  nlinarith

/-- The directional defect is bounded above by the frequency-aggregated
modulus load. -/
theorem normalizedDirectionalFourierDefect_le_aggregatedLoad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (center : ℝ) (hN : 0 < N) :
    normalizedDirectionalFourierDefect coefficient frequency x N center ≤
      normalizedAggregatedFourierLoad coefficient frequency x N := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let z := centeredAggregatedNonzeroSum coefficient frequency x N center
  have hz :
      -z.re ≤ ∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
        |aggregatedCoefficient coefficient frequency h| *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
    calc
      -z.re ≤ |z.re| := neg_le_abs _
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
      _ ≤ ∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
          ‖aggregatedCoefficient coefficient frequency h *
            Theory.PiDigits.T27.phase h (-center) *
              Theory.PiDigits.T27.exponentialSum x N h‖ := by
        unfold z centeredAggregatedNonzeroSum
        exact norm_sum_le _ _
      _ = ∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
          |aggregatedCoefficient coefficient frequency h| *
            ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Theory.PiDigits.T27.norm_phase, mul_one]
  unfold normalizedDirectionalFourierDefect normalizedAggregatedFourierLoad
  exact (div_le_div_iff_of_pos_right hNR).2 hz

/-- The directional defect for the exact order-`q` Jackson presentation and
the interval `[a,a+1/q)`. -/
def directionalJacksonDefect (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) : ℝ :=
  normalizedDirectionalFourierDefect
    (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q)
    (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency q)
    x N (a + (q : ℝ)⁻¹ / 2)

/-- Directional Jackson defect is pointwise no larger than the aggregated
Jackson load. -/
theorem directionalJacksonDefect_le_aggregatedJacksonFourierLoad
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) :
    directionalJacksonDefect x N q a ≤ aggregatedJacksonFourierLoad x N q := by
  exact normalizedDirectionalFourierDefect_le_aggregatedLoad _ _ _ _ _ hN

/-- An empty interval forces the exact directional Jackson obstruction. -/
theorem finite_empty_decimalInterval_directional_obstruction
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ≤
      directionalJacksonDefect x N q a := by
  unfold directionalJacksonDefect
  refine finiteFourierPresentation_directional_obstruction _ _ x N
    (a + (q : ℝ)⁻¹ / 2) _ hN ?_ ?_
  · exact Theory.PiDigits.ExactNaturalScaleResonance.jackson_zeroCoefficient_self_lower q hq
  · intro j hj
    simpa only [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonMinorant] using
      Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonMinorant_re_nonpos_outside
        q q hq hq (x j) a (hx j hj) ha haq (hempty j hj)

/-- A directional defect below threshold forces a hit in its prescribed
interval. -/
theorem finite_decimalInterval_hit_of_directional_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : directionalJacksonDefect x N q a <
      1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  exact (not_lt_of_ge (finite_empty_decimalInterval_directional_obstruction
    x N q a hN hq hx ha haq (fun j hj => hno j hj))) hsmall

private lemma jacksonAggregatedCoefficient_one_pos :
    aggregatedCoefficient
      (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 1 1)
      (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 1) 1 = 1 / 2 := by
  unfold aggregatedCoefficient
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeSign,
    Fintype.sum_prod_type]

private lemma jacksonAggregatedCoefficient_one_neg :
    aggregatedCoefficient
      (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 1 1)
      (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 1) (-1) = 1 / 2 := by
  unfold aggregatedCoefficient
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeSign,
    Fintype.sum_prod_type]

private lemma jacksonFrequency_one_nonzero_support :
    (Finset.image
      (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 1)
      Finset.univ).filter (fun h => h ≠ 0) = {(-1 : ℤ), 1} := by
  decide

private lemma centered_singleton_phase (h : ℤ) (c : ℝ) :
    Theory.PiDigits.T27.phase h (-c) *
      Theory.PiDigits.T27.exponentialSum (fun _ => c) 1 h = 1 := by
  rw [Theory.PiDigits.T27.exponentialSum]
  simp only [Finset.sum_range_one]
  rw [← Theory.PiDigits.T27.phase_add_real]
  simp [Theory.PiDigits.T27.phase]

private lemma scalar_centered_singleton_phase (r : ℂ) (h : ℤ) (c : ℝ) :
    r * Theory.PiDigits.T27.phase h (-c) *
      Theory.PiDigits.T27.exponentialSum (fun _ => c) 1 h = r := by
  rw [mul_assoc, centered_singleton_phase, mul_one]

/-- At the genuine Jackson order `q = 1`, the singleton at the center of
`[0,1)` passes the directional threshold while it fails the aggregated
threshold.  Thus the finite directional criterion is strictly weaker than
the aggregated one for the actual Jackson presentation. -/
theorem directional_finite_criterion_strict_vs_aggregated :
    ∃ x : ℕ → ℝ, ∃ N q : ℕ, ∃ a : ℝ,
      0 < N ∧ 0 < q ∧
      (∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1) ∧
      0 ≤ a ∧ a + (q : ℝ)⁻¹ ≤ 1 ∧
      directionalJacksonDefect x N q a <
        1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ∧
      ¬ aggregatedJacksonFourierLoad x N q <
        1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) := by
  refine ⟨(fun _ => (1 / 2 : ℝ)), 1, 1, 0, by norm_num, by norm_num,
    ?_, by norm_num, by norm_num, ?_, ?_⟩
  · intro j hj
    norm_num
  · unfold directionalJacksonDefect normalizedDirectionalFourierDefect
      centeredAggregatedNonzeroSum
    rw [jacksonFrequency_one_nonzero_support]
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
    rw [jacksonAggregatedCoefficient_one_neg,
      jacksonAggregatedCoefficient_one_pos]
    norm_num only [Nat.cast_one, inv_one, zero_add]
    rw [scalar_centered_singleton_phase, scalar_centered_singleton_phase]
    norm_num
  · intro hsmall
    unfold aggregatedJacksonFourierLoad normalizedAggregatedFourierLoad at hsmall
    rw [jacksonFrequency_one_nonzero_support] at hsmall
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton] at hsmall
    rw [jacksonAggregatedCoefficient_one_neg,
      jacksonAggregatedCoefficient_one_pos] at hsmall
    simp only [Theory.PiDigits.T27.exponentialSum, Finset.sum_range_one,
      Theory.PiDigits.T27.norm_phase] at hsmall
    norm_num at hsmall

set_option maxHeartbeats 2000000 in
private lemma jacksonAggregatedCoefficient_ten_zero :
    aggregatedCoefficient
      (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10)
      (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10) 0 =
        (17 : ℝ) / 500 := by
  unfold aggregatedCoefficient
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num (config := { maxSteps := 2000000 })
    [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeSign,
    Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
private lemma jacksonAggregatedCoefficient_ten_ten :
    aggregatedCoefficient
      (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10)
      (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10) 10 =
        (83 : ℝ) / 1000 := by
  unfold aggregatedCoefficient
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num (config := { maxSteps := 2000000 })
    [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeSign,
    Fin.sum_univ_succ]

private lemma jacksonCoefficient_ten_total :
    (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 10,
      Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10 i) =
        (2 : ℝ) := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeSign,
    Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/- At the decimal scale `q = 10`, the singleton at the center of `[0,1/10)`
passes the directional threshold while it fails the aggregated threshold. -/
theorem directional_decimalScale_ten_strict_vs_aggregated :
    let x : ℕ → ℝ := fun _ => 1 / 20
    directionalJacksonDefect x 1 10 0 <
        1 / (3 * (10 : ℝ)) + 2 / (3 * (10 : ℝ) ^ 3) ∧
      ¬ aggregatedJacksonFourierLoad x 1 10 <
        1 / (3 * (10 : ℝ)) + 2 / (3 * (10 : ℝ) ^ 3) := by
  dsimp only
  constructor
  · unfold directionalJacksonDefect normalizedDirectionalFourierDefect
      centeredAggregatedNonzeroSum
    norm_num only [Nat.cast_ofNat, zero_add]
    have hregroup := sum_aggregatedCoefficient_mul_ne_zero
      (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10)
      (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10)
      (fun h => Theory.PiDigits.T27.phase h (-(1 / 20 : ℝ)) *
        Theory.PiDigits.T27.exponentialSum (fun _ => (1 / 20 : ℝ)) 1 h)
    simp_rw [centered_singleton_phase] at hregroup
    simp_rw [scalar_centered_singleton_phase]
    have hregroup' :
        (∑ h ∈ Finset.image
            (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10)
            Finset.univ with h ≠ 0,
          (aggregatedCoefficient
            (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10)
            (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10) h : ℂ)) =
          ∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 10 with
            Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
            (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10 i : ℂ) := by
      simpa using hregroup
    rw [hregroup']
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 10 =>
        Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i = 0)
      (fun i => (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient
        10 10 i : ℂ))
    have hzero :
        (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 10 with
          Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i = 0,
          (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10 i : ℂ)) =
            (17 : ℝ) / 500 := by
      exact_mod_cast jacksonAggregatedCoefficient_ten_zero
    have htotal :
        (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 10,
          (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10 i : ℂ)) = 2 := by
      exact_mod_cast jacksonCoefficient_ten_total
    rw [← hsplit] at htotal
    rw [hzero] at htotal
    have hnonzero :
        (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 10 with
          Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
          (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10 i : ℂ)) =
            (983 : ℝ) / 500 := by
      apply Complex.ext
      · have h := congrArg Complex.re htotal
        norm_num at h ⊢
        linarith
      · have h := congrArg Complex.im htotal
        norm_num at h ⊢
    rw [hnonzero]
    norm_num
  · intro hsmall
    unfold aggregatedJacksonFourierLoad normalizedAggregatedFourierLoad at hsmall
    have hmem : (10 : ℤ) ∈ Finset.image
        (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10)
        Finset.univ := by
      apply Finset.mem_image.mpr
      refine ⟨Sum.inr (((false, ⟨0, by norm_num⟩), (true, ⟨0, by norm_num⟩))),
        Finset.mem_univ _, ?_⟩
      norm_num [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
        Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency]
    have hterm :
        |aggregatedCoefficient
            (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10)
            (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10) 10| *
            ‖Theory.PiDigits.T27.exponentialSum (fun _ => (1 / 20 : ℝ)) 1 10‖ ≤
          ∑ h ∈ Finset.image
              (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10)
              Finset.univ with h ≠ 0,
            |aggregatedCoefficient
              (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10)
              (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10) h| *
              ‖Theory.PiDigits.T27.exponentialSum (fun _ => (1 / 20 : ℝ)) 1 h‖ := by
      let s := (Finset.image
        (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10)
        Finset.univ).filter (fun h => h ≠ 0)
      let f : ℤ → ℝ := fun h =>
        |aggregatedCoefficient
            (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 10 10)
            (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 10) h| *
          ‖Theory.PiDigits.T27.exponentialSum (fun _ => (1 / 20 : ℝ)) 1 h‖
      have hf : ∀ h ∈ s, 0 ≤ f h := by
        intro h hh
        exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
      have h10 : (10 : ℤ) ∈ s := Finset.mem_filter.mpr ⟨hmem, by norm_num⟩
      simpa only [s, f] using (Finset.single_le_sum hf h10)
    rw [jacksonAggregatedCoefficient_ten_ten] at hterm
    simp only [Theory.PiDigits.T27.exponentialSum, Finset.sum_range_one,
      Theory.PiDigits.T27.norm_phase, abs_of_pos (by norm_num : (0 : ℝ) < 83 / 1000),
      mul_one] at hterm
    simp_rw [Theory.PiDigits.T27.exponentialSum, Finset.sum_range_one,
      Theory.PiDigits.T27.norm_phase, mul_one] at hsmall
    norm_num at hsmall hterm
    linarith

/-- Wordwise directional cancellation for pi.  Its cutoff may depend on the
actual word, not only on its length. -/
def PiWordwiseDirectionalJacksonCancellation : Prop :=
  ∀ s : List (Fin 10), s ≠ [] → ∃ N : ℕ, 0 < N ∧
    directionalJacksonDefect Theory.PiDigits.T27.piFractionalOrbit N
      (10 ^ s.length) (Theory.PiDigits.T27.decimalCylinderLeft s) <
        1 / (3 * (10 : ℝ) ^ s.length) +
          2 / (3 * ((10 : ℝ) ^ s.length) ^ 3)

/-- The lengthwise aggregated pi premise implies the wordwise directional
premise. -/
theorem piNaturalScaleAggregatedCancellation_implies_wordwiseDirectional
    (hagg : PiNaturalScaleAggregatedCancellation) :
    PiWordwiseDirectionalJacksonCancellation := by
  intro s hs
  obtain ⟨N, hN, hsmall⟩ := hagg s.length (by
    cases s with
    | nil => contradiction
    | cons d s => simp)
  refine ⟨N, hN, ?_⟩
  exact (directionalJacksonDefect_le_aggregatedJacksonFourierLoad
    _ N (10 ^ s.length) _ hN).trans_lt hsmall

/-- The existing raw T121 pi premise also implies the wordwise directional
premise. -/
theorem piNaturalScaleWeightedCancellation_implies_wordwiseDirectional
    (hraw : Theory.PiDigits.WeightedNaturalScaleFrontier.PiNaturalScaleWeightedCancellation) :
    PiWordwiseDirectionalJacksonCancellation :=
  piNaturalScaleAggregatedCancellation_implies_wordwiseDirectional
    (Theory.PiDigits.AggregatedJacksonFrontier.piNaturalScaleWeightedCancellation_implies_aggregated hraw)

/-- Wordwise directional cancellation implies canonical V1. -/
theorem piWordwiseDirectionalJacksonCancellation_implies_canonicalV1
    (hdir : PiWordwiseDirectionalJacksonCancellation) : Theory.PiDigits.V1 := by
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons d s =>
      obtain ⟨N, hN, hsmall⟩ := hdir (d :: s) (by simp)
      let q := 10 ^ (d :: s).length
      let a := Theory.PiDigits.T27.decimalCylinderLeft (d :: s)
      have hhit := finite_decimalInterval_hit_of_directional_smallness
        Theory.PiDigits.T27.piFractionalOrbit N q a hN (by positivity)
        (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
        (Theory.PiDigits.T27.decimalCylinderLeft_nonneg (d :: s))
        (by
          have hpow : (q : ℝ) = (10 : ℝ) ^ (d :: s).length := by simp [q]
          rw [hpow]
          simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
            Theory.PiDigits.T27.decimalCylinderRight_le_one (d :: s))
        (by simpa only [q, a, Nat.cast_pow, Nat.cast_ofNat] using hsmall)
      obtain ⟨j, hj, hjmem⟩ := hhit
      refine ⟨j, ?_⟩
      have hinterval : Theory.PiDigits.T27.piFractionalOrbit j ∈
          Set.Ico
            ((Theory.PiDigits.T20.wordValue (d :: s) : ℝ) /
              (10 : ℝ) ^ (d :: s).length)
            (((Theory.PiDigits.T20.wordValue (d :: s) + 1 : ℕ) : ℝ) /
              (10 : ℝ) ^ (d :: s).length) := by
        have hpow : (q : ℝ) = (10 : ℝ) ^ (d :: s).length := by simp [q]
        rw [hpow] at hjmem
        have hmem' : Theory.PiDigits.T27.piFractionalOrbit j ∈
            Set.Ico (Theory.PiDigits.T27.decimalCylinderLeft (d :: s))
              (Theory.PiDigits.T27.decimalCylinderLeft (d :: s) +
                Theory.PiDigits.T27.decimalCylinderLength (d :: s).length) := by
          simpa only [a, q, Theory.PiDigits.T27.decimalCylinderLength] using hjmem
        rw [Theory.PiDigits.T27.decimalCylinder_interval] at hmem'
        exact hmem'
      have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
        (d :: s) (Theory.PiDigits.T27.piFractionalOrbit j) hinterval
      intro i hi
      have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
        Real.pi Real.pi_pos.le j i
      exact (Theory.PiDigits.T20.decimalDigit_pi (j + i)).symm.trans
        (hshift.symm.trans (hdigits i hi))

end Theory.PiDigits.DirectionalJacksonFrontier

#print axioms Theory.PiDigits.DirectionalJacksonFrontier.finiteFourierPresentation_directional_obstruction
#print axioms Theory.PiDigits.DirectionalJacksonFrontier.directionalJacksonDefect_le_aggregatedJacksonFourierLoad
#print axioms Theory.PiDigits.DirectionalJacksonFrontier.finite_decimalInterval_hit_of_directional_smallness
#print axioms Theory.PiDigits.DirectionalJacksonFrontier.directional_finite_criterion_strict_vs_aggregated
#print axioms Theory.PiDigits.DirectionalJacksonFrontier.directional_decimalScale_ten_strict_vs_aggregated
#print axioms Theory.PiDigits.DirectionalJacksonFrontier.piWordwiseDirectionalJacksonCancellation_implies_canonicalV1
