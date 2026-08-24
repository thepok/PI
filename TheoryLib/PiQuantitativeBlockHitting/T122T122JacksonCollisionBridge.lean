import TheoryLib.PiQuantitativeBlockHitting.T121T121WeightedNaturalScaleCriterion

/-!
# Jackson weighted L2 and collision bridge

This module gives a quadratic sufficient condition for the weighted Fourier
criterion of T120/T121.  It deliberately keeps the existing, unaggregated
`JacksonIndex`: duplicate frequencies are harmless because their absolute
coefficient masses are summed by the finite index sum.

The final specialization to pi is conditional.  No collision estimate for pi
is asserted, and hence no unconditional digit-occurrence statement is proved.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.WeightedNaturalScaleFrontier

open Theory.PiDigits.PiNaturalScaleResonanceObstruction

/-- Absolute coefficient mass of one unaggregated Jackson index. -/
def jacksonAbsoluteWeight (q : ℕ) (i : JacksonIndex q) : ℝ :=
  |jacksonCoefficient q q i|

/-- Total absolute coefficient mass away from frequency zero. -/
def jacksonNonzeroMass (q : ℕ) : ℝ :=
  ∑ i : JacksonIndex q with jacksonFrequency i ≠ 0,
    jacksonAbsoluteWeight q i

/-- Absolute coefficient mass at frequency zero. -/
def jacksonZeroMass (q : ℕ) : ℝ :=
  ∑ i : JacksonIndex q with jacksonFrequency i = 0,
    jacksonAbsoluteWeight q i

/-- The coefficient-weighted quadratic Fourier load, normalized by `N²`. -/
def jacksonQuadraticFourierLoad
    (x : ℕ → ℝ) (N q : ℕ) : ℝ :=
  ∑ i : JacksonIndex q with jacksonFrequency i ≠ 0,
    jacksonAbsoluteWeight q i *
      (‖Theory.PiDigits.T27.exponentialSum x N (jacksonFrequency i)‖ /
        (N : ℝ)) ^ 2

/-- The real collision kernel attached to all absolute Jackson coefficients. -/
def jacksonCollisionKernel (q : ℕ) (t : ℝ) : ℝ :=
  ∑ i : JacksonIndex q,
    jacksonAbsoluteWeight q i * (Theory.PiDigits.T27.phase (jacksonFrequency i) t).re

lemma jacksonAbsoluteWeight_nonneg (q : ℕ) (i : JacksonIndex q) :
    0 ≤ jacksonAbsoluteWeight q i := by
  exact abs_nonneg _

lemma jacksonQuadraticFourierLoad_nonneg (x : ℕ → ℝ) (N q : ℕ) :
    0 ≤ jacksonQuadraticFourierLoad x N q := by
  unfold jacksonQuadraticFourierLoad
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (jacksonAbsoluteWeight_nonneg q i) (sq_nonneg _)

/-- The safe coefficient-mass bound used by the quadratic bridge.  The exact
nonzero mass is smaller, but the already verified total-mass identity gives
the clean universal factor `4`. -/
lemma jacksonNonzeroMass_le_four (q : ℕ) (hq : 0 < q) :
    jacksonNonzeroMass q ≤ 4 := by
  have hmass :
      (∑ i : JacksonIndex q, jacksonAbsoluteWeight q i) = 4 := by
    unfold jacksonAbsoluteWeight
    rw [Theory.PiDigits.ExactNaturalScaleResonance.jacksonCoefficient_mass_general
      q q hq hq]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [hqR]
    norm_num
  calc
    jacksonNonzeroMass q ≤ ∑ i : JacksonIndex q, jacksonAbsoluteWeight q i := by
      unfold jacksonNonzeroMass
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> simp [jacksonAbsoluteWeight_nonneg]
    _ = 4 := hmass

/-- Weighted Cauchy--Schwarz with the exact nonzero absolute mass. -/
theorem jacksonWeightedFourierLoad_sq_le_mass_mul_quadratic
    (x : ℕ → ℝ) (N q : ℕ) (hN : 0 < N) :
    jacksonWeightedFourierLoad x N q ^ 2 ≤
      jacksonNonzeroMass q * jacksonQuadraticFourierLoad x N q := by
  classical
  let s := (Finset.univ : Finset (JacksonIndex q)).filter fun i =>
    jacksonFrequency i ≠ 0
  let b : JacksonIndex q → ℝ := fun i =>
    ‖Theory.PiDigits.T27.exponentialSum x N (jacksonFrequency i)‖ / (N : ℝ)
  have hsqrt (i : JacksonIndex q) :
      Real.sqrt (jacksonAbsoluteWeight q i) ^ 2 = jacksonAbsoluteWeight q i :=
    Real.sq_sqrt (jacksonAbsoluteWeight_nonneg q i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (jacksonAbsoluteWeight q i))
    (fun i => Real.sqrt (jacksonAbsoluteWeight q i) * b i)
  have hleft :
      (∑ i ∈ s, Real.sqrt (jacksonAbsoluteWeight q i) *
          (Real.sqrt (jacksonAbsoluteWeight q i) * b i)) =
        ∑ i ∈ s, jacksonAbsoluteWeight q i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← pow_two, hsqrt]
  have hright :
      (∑ i ∈ s, Real.sqrt (jacksonAbsoluteWeight q i) ^ 2) *
          (∑ i ∈ s, (Real.sqrt (jacksonAbsoluteWeight q i) * b i) ^ 2) =
        jacksonNonzeroMass q * jacksonQuadraticFourierLoad x N q := by
    unfold jacksonNonzeroMass jacksonQuadraticFourierLoad
    dsimp only [s, b]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact hsqrt i
    · apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow, hsqrt]
  rw [hleft, hright] at hcs
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hload :
      jacksonWeightedFourierLoad x N q =
        ∑ i ∈ s, jacksonAbsoluteWeight q i * b i := by
    unfold jacksonWeightedFourierLoad normalizedWeightedFourierLoad
    dsimp only [s, b, jacksonAbsoluteWeight]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hNR]
  rw [hload]
  exact hcs

/-- Safe-factor form of weighted Cauchy--Schwarz. -/
theorem jacksonWeightedFourierLoad_sq_le_four_mul_quadratic
    (x : ℕ → ℝ) (N q : ℕ) (hN : 0 < N) (hq : 0 < q) :
    jacksonWeightedFourierLoad x N q ^ 2 ≤
      4 * jacksonQuadraticFourierLoad x N q := by
  calc
    jacksonWeightedFourierLoad x N q ^ 2 ≤
        jacksonNonzeroMass q * jacksonQuadraticFourierLoad x N q :=
      jacksonWeightedFourierLoad_sq_le_mass_mul_quadratic x N q hN
    _ ≤ 4 * jacksonQuadraticFourierLoad x N q :=
      mul_le_mul_of_nonneg_right (jacksonNonzeroMass_le_four q hq)
        (jacksonQuadraticFourierLoad_nonneg x N q)

lemma phase_sub_real_argument (h : ℤ) (x y : ℝ) :
    Theory.PiDigits.T27.phase h (y - x) =
      conj (Theory.PiDigits.T27.phase h x) *
        Theory.PiDigits.T27.phase h y := by
  rw [show y - x = -x + y by ring, Theory.PiDigits.T27.phase_add_real]
  have hneg : Theory.PiDigits.T27.phase h (-x) =
      Theory.PiDigits.T27.phase (-h) x := by
    unfold Theory.PiDigits.T27.phase
    congr 1
    push_cast
    ring
  rw [hneg, Theory.PiDigits.T27.phase_neg]

/-- Exact pair expansion of one exponential-sum square. -/
lemma exponentialSum_normSq_eq_pairPhase
    (x : ℕ → ℝ) (N : ℕ) (h : ℤ) :
    Complex.normSq (Theory.PiDigits.T27.exponentialSum x N h) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        (Theory.PiDigits.T27.phase h (x n - x m)).re := by
  have hc :
      conj (Theory.PiDigits.T27.exponentialSum x N h) *
          Theory.PiDigits.T27.exponentialSum x N h =
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          Theory.PiDigits.T27.phase h (x n - x m) := by
    unfold Theory.PiDigits.T27.exponentialSum
    rw [map_sum]
    simp_rw [Finset.sum_mul, Finset.mul_sum, phase_sub_real_argument]
  calc
    Complex.normSq (Theory.PiDigits.T27.exponentialSum x N h) =
        (conj (Theory.PiDigits.T27.exponentialSum x N h) *
          Theory.PiDigits.T27.exponentialSum x N h).re := by
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
    _ = _ := by
      rw [hc]
      change Complex.reCLM
          (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
            Theory.PiDigits.T27.phase h (x n - x m)) = _
      simp_rw [map_sum]
      rfl

/-- Exact collision identity before normalization and centering. -/
theorem sum_jacksonCollisionKernel_eq_weighted_normSq
    (x : ℕ → ℝ) (N q : ℕ) :
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        jacksonCollisionKernel q (x n - x m)) =
      ∑ i : JacksonIndex q, jacksonAbsoluteWeight q i *
        Complex.normSq
          (Theory.PiDigits.T27.exponentialSum x N (jacksonFrequency i)) := by
  classical
  unfold jacksonCollisionKernel
  conv_rhs =>
    enter [2, i]
    rw [exponentialSum_normSq_eq_pairPhase]
  simp_rw [Finset.mul_sum]
  calc
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        ∑ i : JacksonIndex q,
          jacksonAbsoluteWeight q i *
            (Theory.PiDigits.T27.phase (jacksonFrequency i) (x n - x m)).re) =
      ∑ m ∈ Finset.range N, ∑ i : JacksonIndex q,
        ∑ n ∈ Finset.range N,
          jacksonAbsoluteWeight q i *
            (Theory.PiDigits.T27.phase (jacksonFrequency i) (x n - x m)).re := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The centered pair average is exactly the nonzero quadratic Fourier load. -/
theorem jacksonQuadraticFourierLoad_eq_pairAverage_sub_zeroMass
    (x : ℕ → ℝ) (N q : ℕ) (hN : 0 < N) :
    jacksonQuadraticFourierLoad x N q =
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        jacksonCollisionKernel q (x n - x m)) / (N : ℝ) ^ 2 -
          jacksonZeroMass q := by
  classical
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sum_jacksonCollisionKernel_eq_weighted_normSq]
  unfold jacksonQuadraticFourierLoad jacksonZeroMass
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : JacksonIndex q => jacksonFrequency i = 0)]
  have hzero :
      (∑ i : JacksonIndex q with jacksonFrequency i = 0,
          jacksonAbsoluteWeight q i *
            Complex.normSq
              (Theory.PiDigits.T27.exponentialSum x N (jacksonFrequency i))) /
          (N : ℝ) ^ 2 =
        ∑ i : JacksonIndex q with jacksonFrequency i = 0,
          jacksonAbsoluteWeight q i := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hz := (Finset.mem_filter.mp hi).2
    rw [hz, Theory.PiDigits.T27.exponentialSum_zero,
      Complex.normSq_natCast]
    field_simp [hNR]
  have hnonzero :
      (∑ i : JacksonIndex q with ¬ jacksonFrequency i = 0,
          jacksonAbsoluteWeight q i *
            Complex.normSq
              (Theory.PiDigits.T27.exponentialSum x N (jacksonFrequency i))) /
          (N : ℝ) ^ 2 =
        ∑ i : JacksonIndex q with jacksonFrequency i ≠ 0,
          jacksonAbsoluteWeight q i *
            (‖Theory.PiDigits.T27.exponentialSum x N (jacksonFrequency i)‖ /
              (N : ℝ)) ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.normSq_eq_norm_sq]
    field_simp [hNR]
  rw [add_div, hzero, hnonzero]
  ring

/-- A centered collision estimate at the natural `q⁻²` scale forces the
T120 interval hit.  The factor `4` is the safe total absolute mass. -/
theorem finite_decimalInterval_hit_of_collision_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hcollision :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        jacksonCollisionKernel q (x n - x m)) / (N : ℝ) ^ 2 -
          jacksonZeroMass q <
        (1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) ^ 2 / 4) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  apply finite_decimalInterval_hit_of_weighted_smallness x N q a hN hq hx ha haq
  let c : ℝ := 1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : jacksonQuadraticFourierLoad x N q < c ^ 2 / 4 := by
    rw [jacksonQuadraticFourierLoad_eq_pairAverage_sub_zeroMass x N q hN]
    exact hcollision
  have hsq := jacksonWeightedFourierLoad_sq_le_four_mul_quadratic x N q hN hq
  have hload0 : 0 ≤ jacksonWeightedFourierLoad x N q := by
    unfold jacksonWeightedFourierLoad normalizedWeightedFourierLoad
    positivity
  have : jacksonWeightedFourierLoad x N q < c := by nlinarith
  simpa [c] using this

/-- Open collision premise for the decimal orbit of pi. -/
def PiNaturalScaleJacksonCollision : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      jacksonCollisionKernel (10 ^ k)
        (Theory.PiDigits.T27.piFractionalOrbit n -
          Theory.PiDigits.T27.piFractionalOrbit m)) / (N : ℝ) ^ 2 -
        jacksonZeroMass (10 ^ k) <
      (1 / (3 * (10 : ℝ) ^ k) +
        2 / (3 * ((10 : ℝ) ^ k) ^ 3)) ^ 2 / 4

/-- The explicit collision premise implies T121's weighted cancellation
premise.  It remains an unproved hypothesis for pi. -/
theorem piNaturalScaleJacksonCollision_implies_weightedCancellation
    (hcollision : PiNaturalScaleJacksonCollision) :
    PiNaturalScaleWeightedCancellation := by
  intro k hk
  obtain ⟨N, hN, hpair⟩ := hcollision k hk
  refine ⟨N, hN, ?_⟩
  have hq : 0 < 10 ^ k := by positivity
  have hQ :
      jacksonQuadraticFourierLoad Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) <
        (1 / (3 * (10 : ℝ) ^ k) +
          2 / (3 * ((10 : ℝ) ^ k) ^ 3)) ^ 2 / 4 := by
    rw [jacksonQuadraticFourierLoad_eq_pairAverage_sub_zeroMass
      Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) hN]
    exact hpair
  have hsq := jacksonWeightedFourierLoad_sq_le_four_mul_quadratic
    Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) hN hq
  have hload0 :
      0 ≤ jacksonWeightedFourierLoad Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) := by
    unfold jacksonWeightedFourierLoad normalizedWeightedFourierLoad
    positivity
  have hc :
      0 < 1 / (3 * (10 : ℝ) ^ k) +
        2 / (3 * ((10 : ℝ) ^ k) ^ 3) := by positivity
  nlinarith

/-- Conditional canonical-V1 consumer for the collision premise. -/
theorem piNaturalScaleJacksonCollision_implies_canonicalV1
    (hcollision : PiNaturalScaleJacksonCollision) :
    Theory.PiDigits.V1 :=
  piNaturalScaleWeightedCancellation_implies_canonicalV1
    (piNaturalScaleJacksonCollision_implies_weightedCancellation hcollision)

end Theory.PiDigits.WeightedNaturalScaleFrontier

#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.jacksonWeightedFourierLoad_sq_le_four_mul_quadratic
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.sum_jacksonCollisionKernel_eq_weighted_normSq
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.jacksonQuadraticFourierLoad_eq_pairAverage_sub_zeroMass
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.finite_decimalInterval_hit_of_collision_smallness
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.piNaturalScaleJacksonCollision_implies_canonicalV1
