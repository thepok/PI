import TheoryLib.PiQuantitativeBlockHitting.T121T121WeightedNaturalScaleCriterion

/-!
# Frequency-aggregated Jackson frontier

The finite Jackson presentation has many indices with the same integer
frequency.  This file collects their signed coefficients before taking an
absolute value.  The resulting criterion is therefore never stronger than
the unaggregated T120 criterion, while the same empty-interval obstruction
and conditional implication to canonical V1 remain valid.

No cancellation estimate for the decimal orbit of pi is proved here.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.AggregatedJacksonFrontier

/-- The signed coefficient obtained by collecting every index with frequency
`h`. -/
def aggregatedCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ) (h : ℤ) : ℝ :=
  ∑ i with frequency i = h, coefficient i

/-- The normalized Fourier load after equal frequencies have been collected
with their signs. -/
def normalizedAggregatedFourierLoad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
      |aggregatedCoefficient coefficient frequency h| *
        ‖Theory.PiDigits.T27.exponentialSum x N h‖) / (N : ℝ)

/-- Collecting equal frequencies does not change the underlying finite
Fourier polynomial. -/
lemma sum_aggregatedCoefficient_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ) (f : ℤ → ℂ) :
    ∑ h ∈ Finset.image frequency Finset.univ,
        aggregatedCoefficient coefficient frequency h * f h =
      ∑ i, coefficient i * f (frequency i) := by
  classical
  apply Finset.sum_image'
  intro i hi
  unfold aggregatedCoefficient
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjfreq : frequency j = frequency i := (Finset.mem_filter.mp hj).2
  rw [hjfreq]

/-- A nonpositive finite Fourier presentation forces its aggregated nonzero
load to dominate the same signed zero-mode lower bound.  This is the exact
point at which the triangle inequality is delayed until after equal-frequency
cancellation. -/
theorem finiteFourierPresentation_aggregated_obstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (center c0 : ℝ)
    (hN : 0 < N)
    (hzero : c0 ≤ aggregatedCoefficient coefficient frequency 0)
    (hnonpos : ∀ j < N,
      (∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)).re ≤ 0) :
    c0 ≤ normalizedAggregatedFourierLoad coefficient frequency x N := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let support : Finset ℤ := Finset.image frequency Finset.univ
  let z : ℂ := ∑ h ∈ support with h ≠ 0,
    aggregatedCoefficient coefficient frequency h *
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
      ∑ h ∈ support, aggregatedCoefficient coefficient frequency h *
        Theory.PiDigits.T27.phase h (-center) *
          Theory.PiDigits.T27.exponentialSum x N h := by
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ j ∈ Finset.range N,
          coefficient i * Theory.PiDigits.T27.phase (frequency i) (x j - center)) =
          ∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
            Theory.PiDigits.T27.exponentialSum x N (frequency i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Theory.PiDigits.T27.exponentialSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show x j - center = -center + x j by ring,
          Theory.PiDigits.T27.phase_add_real]
        ring
      _ = ∑ h ∈ support, aggregatedCoefficient coefficient frequency h *
          (Theory.PiDigits.T27.phase h (-center) *
            Theory.PiDigits.T27.exponentialSum x N h) := by
        symm
        simpa only [support, mul_assoc] using
          (sum_aggregatedCoefficient_mul coefficient frequency
            (fun h => Theory.PiDigits.T27.phase h (-center) *
              Theory.PiDigits.T27.exponentialSum x N h))
      _ = ∑ h ∈ support, aggregatedCoefficient coefficient frequency h *
          Theory.PiDigits.T27.phase h (-center) *
            Theory.PiDigits.T27.exponentialSum x N h := by
        apply Finset.sum_congr rfl
        intro h hh
        ring
  rw [hfourier] at htotal
  have hzero_mem : 0 ∈ support ∨ aggregatedCoefficient coefficient frequency 0 = 0 := by
    by_cases hz : 0 ∈ support
    · exact Or.inl hz
    · right
      unfold aggregatedCoefficient
      apply Finset.sum_eq_zero
      intro i hi
      exfalso
      apply hz
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hsplit :
      (∑ h ∈ support, aggregatedCoefficient coefficient frequency h *
        Theory.PiDigits.T27.phase h (-center) *
          Theory.PiDigits.T27.exponentialSum x N h) =
      (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z := by
    by_cases hz : 0 ∈ support
    · calc
        _ = (∑ h ∈ support with h = 0,
              aggregatedCoefficient coefficient frequency h *
                Theory.PiDigits.T27.phase h (-center) *
                  Theory.PiDigits.T27.exponentialSum x N h) +
            ∑ h ∈ support with h ≠ 0,
              aggregatedCoefficient coefficient frequency h *
                Theory.PiDigits.T27.phase h (-center) *
                  Theory.PiDigits.T27.exponentialSum x N h :=
            (Finset.sum_filter_add_sum_filter_not support (fun h => h = 0) _).symm
        _ = (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z := by
          congr 1
          · rw [Finset.sum_eq_single 0]
            · simp [Theory.PiDigits.T27.phase_zero,
                Theory.PiDigits.T27.exponentialSum_zero]
              ring
            · intro b hb hb0
              exact (hb0 (Finset.mem_filter.mp hb).2).elim
            · intro hz0
              exact (hz0 (Finset.mem_filter.mpr ⟨hz, rfl⟩)).elim
    · have hcoeff : aggregatedCoefficient coefficient frequency 0 = 0 :=
        hzero_mem.resolve_left hz
      have hfilter : {h ∈ support | h ≠ 0} = support := by
        ext h
        simp only [Finset.mem_filter]
        constructor
        · exact fun hh => hh.1
        · intro hh
          exact ⟨hh, fun heq => hz (heq ▸ hh)⟩
      simp [hcoeff, z, hfilter]
  rw [hsplit] at htotal
  have htotal' :
      (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z.re ≤ 0 := by
    simpa using htotal
  have hzlarge : c0 * (N : ℝ) ≤ ‖z‖ := by
    calc
      c0 * (N : ℝ) ≤
          (N : ℝ) * aggregatedCoefficient coefficient frequency 0 := by
            nlinarith
      _ ≤ -z.re := by linarith
      _ ≤ |z.re| := neg_le_abs _
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzupper :
      ‖z‖ ≤ ∑ h ∈ support with h ≠ 0,
        |aggregatedCoefficient coefficient frequency h| *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
    calc
      ‖z‖ ≤ ∑ h ∈ support with h ≠ 0,
          ‖aggregatedCoefficient coefficient frequency h *
            Theory.PiDigits.T27.phase h (-center) *
              Theory.PiDigits.T27.exponentialSum x N h‖ := norm_sum_le _ _
      _ = ∑ h ∈ support with h ≠ 0,
          |aggregatedCoefficient coefficient frequency h| *
            ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Theory.PiDigits.T27.norm_phase, mul_one]
  unfold normalizedAggregatedFourierLoad
  exact (le_div_iff₀ hNR).2 (hzlarge.trans hzupper)

/-- Aggregation can only decrease the weighted Fourier load. -/
theorem normalizedAggregatedFourierLoad_le_normalizedWeightedFourierLoad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    normalizedAggregatedFourierLoad coefficient frequency x N ≤
      Theory.PiDigits.WeightedNaturalScaleFrontier.normalizedWeightedFourierLoad
        coefficient frequency x N := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [normalizedAggregatedFourierLoad,
    Theory.PiDigits.WeightedNaturalScaleFrontier.normalizedWeightedFourierLoad,
    div_le_div_iff_of_pos_right hNR]
  calc
    (∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
        |aggregatedCoefficient coefficient frequency h| *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖) ≤
      ∑ h ∈ Finset.image frequency Finset.univ with h ≠ 0,
        (∑ i with frequency i = h, |coefficient i|) *
          ‖Theory.PiDigits.T27.exponentialSum x N h‖ := by
      apply Finset.sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      unfold aggregatedCoefficient
      exact abs_sum_le_sum_abs _ _
    _ = ∑ i with frequency i ≠ 0,
        |coefficient i| *
          ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ := by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_image'
      intro i hi
      by_cases hi0 : frequency i = 0
      · simp only [hi0, ne_eq, not_true_eq_false, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        simp [(Finset.mem_filter.mp hj).2]
      · rw [Finset.sum_mul]
        rw [if_pos hi0]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjfreq : frequency j = frequency i
        · simp [hjfreq, hi0]
        · simp [hjfreq]

/-- Aggregation is a genuinely strict operation in general: two opposite
coefficients at the same nonzero frequency cancel completely after grouping,
while the termwise-absolute load remains positive. -/
theorem normalizedAggregatedFourierLoad_strict_separator :
    ∃ coefficient : Bool → ℝ, ∃ frequency : Bool → ℤ,
      ∃ x : ℕ → ℝ, ∃ N : ℕ, 0 < N ∧
        normalizedAggregatedFourierLoad coefficient frequency x N <
          Theory.PiDigits.WeightedNaturalScaleFrontier.normalizedWeightedFourierLoad
            coefficient frequency x N := by
  refine ⟨(fun b => if b then (1 : ℝ) else -1), (fun _ => (1 : ℤ)),
    (fun _ => 0), 1, by norm_num, ?_⟩
  unfold normalizedAggregatedFourierLoad
    Theory.PiDigits.WeightedNaturalScaleFrontier.normalizedWeightedFourierLoad
    aggregatedCoefficient Theory.PiDigits.T27.exponentialSum
  norm_num [Theory.PiDigits.T27.phase, Finset.sum_filter, Finset.sum_insert]

/-- The aggregated load for the exact order-`q` Jackson presentation. -/
def aggregatedJacksonFourierLoad (x : ℕ → ℝ) (N q : ℕ) : ℝ :=
  normalizedAggregatedFourierLoad
    (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q)
    (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency q) x N

/-- The existing raw Jackson load dominates the frequency-aggregated load. -/
theorem aggregatedJacksonFourierLoad_le_jacksonWeightedFourierLoad
    (x : ℕ → ℝ) (N q : ℕ) (hN : 0 < N) :
    aggregatedJacksonFourierLoad x N q ≤
      Theory.PiDigits.WeightedNaturalScaleFrontier.jacksonWeightedFourierLoad x N q := by
  exact normalizedAggregatedFourierLoad_le_normalizedWeightedFourierLoad _ _ x N hN

/-- An empty interval of length `1/q` forces the aggregated Jackson load above
the same exact signed zero coefficient as T120. -/
theorem finite_empty_decimalInterval_aggregated_obstruction
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ≤
      aggregatedJacksonFourierLoad x N q := by
  let center := a + (q : ℝ)⁻¹ / 2
  unfold aggregatedJacksonFourierLoad
  refine finiteFourierPresentation_aggregated_obstruction _ _ x N center _ hN ?_ ?_
  · exact Theory.PiDigits.ExactNaturalScaleResonance.jackson_zeroCoefficient_self_lower q hq
  · intro j hj
    simpa only [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonMinorant, center] using
      Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonMinorant_re_nonpos_outside
        q q hq hq (x j) a (hx j hj) ha haq (hempty j hj)

/-- Direct contrapositive: aggregated smallness forces an interval hit. -/
theorem finite_decimalInterval_hit_of_aggregated_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : aggregatedJacksonFourierLoad x N q <
      1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  exact (not_lt_of_ge (finite_empty_decimalInterval_aggregated_obstruction
    x N q a hN hq hx ha haq (fun j hj => hno j hj))) hsmall

/-- The open frequency-aggregated cancellation target for the decimal orbit
of pi. -/
def PiNaturalScaleAggregatedCancellation : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    aggregatedJacksonFourierLoad Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) <
      1 / (3 * (10 : ℝ) ^ k) + 2 / (3 * ((10 : ℝ) ^ k) ^ 3)

/-- The raw T121 cancellation premise implies the aggregated premise. -/
theorem piNaturalScaleWeightedCancellation_implies_aggregated
    (h : Theory.PiDigits.WeightedNaturalScaleFrontier.PiNaturalScaleWeightedCancellation) :
    PiNaturalScaleAggregatedCancellation := by
  intro k hk
  obtain ⟨N, hN, hsmall⟩ := h k hk
  exact ⟨N, hN, (aggregatedJacksonFourierLoad_le_jacksonWeightedFourierLoad
    _ N (10 ^ k) hN).trans_lt hsmall⟩

/-- The aggregated pi premise implies canonical V1.  The premise remains
unproved. -/
theorem piNaturalScaleAggregatedCancellation_implies_canonicalV1
    (hagg : PiNaturalScaleAggregatedCancellation) : Theory.PiDigits.V1 := by
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons d s =>
      obtain ⟨N, hN, hsmall⟩ := hagg (d :: s).length (by simp)
      by_contra hmissing
      have hmissingBefore : ∀ n : ℕ, n < N →
          ¬ ∀ i : ℕ, ∀ hi : i < (d :: s).length,
            Theory.PiDigits.piDigit (n + i) = (d :: s).get ⟨i, hi⟩ := by
        intro n hn hocc
        exact hmissing ⟨n, hocc⟩
      let q := 10 ^ (d :: s).length
      let a := Theory.PiDigits.T27.decimalCylinderLeft (d :: s)
      have hq : 0 < q := by positivity
      have hempty : ∀ j < N,
          Theory.PiDigits.T27.piFractionalOrbit j ∉ Set.Ico a (a + (q : ℝ)⁻¹) := by
        intro j hj hmem
        apply hmissingBefore j hj
        have hinterval : Theory.PiDigits.T27.piFractionalOrbit j ∈
            Set.Ico
              ((Theory.PiDigits.T20.wordValue (d :: s) : ℝ) / (10 : ℝ) ^ (d :: s).length)
              (((Theory.PiDigits.T20.wordValue (d :: s) + 1 : ℕ) : ℝ) /
                (10 : ℝ) ^ (d :: s).length) := by
          have hpow : (q : ℝ) = (10 : ℝ) ^ (d :: s).length := by simp [q]
          rw [hpow] at hmem
          have hmem' : Theory.PiDigits.T27.piFractionalOrbit j ∈
              Set.Ico (Theory.PiDigits.T27.decimalCylinderLeft (d :: s))
                (Theory.PiDigits.T27.decimalCylinderLeft (d :: s) +
                  Theory.PiDigits.T27.decimalCylinderLength (d :: s).length) := by
            simpa only [a, q, Theory.PiDigits.T27.decimalCylinderLength] using hmem
          rw [Theory.PiDigits.T27.decimalCylinder_interval] at hmem'
          exact hmem'
        have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
          (d :: s) (Theory.PiDigits.T27.piFractionalOrbit j) hinterval
        intro i hi
        have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
          Real.pi Real.pi_pos.le j i
        exact (Theory.PiDigits.T20.decimalDigit_pi (j + i)).symm.trans
          (hshift.symm.trans (hdigits i hi))
      have hlarge := finite_empty_decimalInterval_aggregated_obstruction
        Theory.PiDigits.T27.piFractionalOrbit N q a hN hq
        (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
        (Theory.PiDigits.T27.decimalCylinderLeft_nonneg (d :: s))
        (by
          have hpow : (q : ℝ) = (10 : ℝ) ^ (d :: s).length := by simp [q]
          rw [hpow]
          simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
            Theory.PiDigits.T27.decimalCylinderRight_le_one (d :: s))
        hempty
      exact (not_lt_of_ge (by simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using hlarge)) hsmall

/-! ## Jackson-specific strict separator -/

/-- Seven equally spaced points followed by a duplicate of zero.  Only the
first eight entries are used by the separator. -/
def jacksonSeparatorSample (j : ℕ) : ℝ :=
  if j < 7 then
    Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 7 j
  else 0

lemma jacksonSeparatorSample_exponentialSum
    (h : ℤ) (h0 : h ≠ 0) (hbound : h.natAbs ≤ 3) :
    Theory.PiDigits.T27.exponentialSum jacksonSeparatorSample 8 h = 1 := by
  have habs0 : 0 < h.natAbs := Int.natAbs_pos.mpr h0
  have habs7 : h.natAbs < 7 := by omega
  have hgridPos :=
    Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid_exponentialSum_nat_eq_zero
      h.natAbs 7 (by norm_num) habs0 habs7
  have hgrid :
      Theory.PiDigits.T27.exponentialSum
        (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 7) 7 h = 0 := by
    rcases Int.natAbs_eq h with hh | hh
    · rw [hh, hgridPos]
    · rw [hh, Theory.PiDigits.SharperNaturalScaleResonance.exponentialSum_neg,
        hgridPos, map_zero]
  rw [Theory.PiDigits.T27.exponentialSum]
  rw [show Finset.range 8 = Finset.range 7 ∪ {7} by ext j; simp; omega]
  rw [Finset.sum_union]
  · have hprefix :
        (∑ j ∈ Finset.range 7,
            Theory.PiDigits.T27.phase h (jacksonSeparatorSample j)) = 0 := by
      rw [← hgrid]
      unfold Theory.PiDigits.T27.exponentialSum
      apply Finset.sum_congr rfl
      intro j hj
      simp [jacksonSeparatorSample, Finset.mem_range.mp hj]
    rw [hprefix]
    simp only [Finset.sum_singleton, zero_add]
    rw [show jacksonSeparatorSample 7 = 0 by simp [jacksonSeparatorSample]]
    rw [Theory.PiDigits.T27.phase]
    norm_num
  · simp

lemma jacksonFrequency_two_natAbs_le_three
    (i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 2) :
    (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i).natAbs ≤ 3 := by
  rcases i with i | i
  · rcases i with ⟨r, s, u, v⟩
    fin_cases r <;> fin_cases s <;> fin_cases u <;> fin_cases v <;>
      norm_num [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency]
  · rcases i with ⟨⟨b, r⟩, ⟨c, s⟩⟩
    fin_cases r <;> fin_cases s <;> cases b <;> cases c <;>
      norm_num [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
        Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency]

lemma jackson_two_raw_nonzeroMass :
    (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 2 with
        Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
      |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 2 2 i|) =
      (11 : ℝ) / 4 := by
  rw [Finset.sum_filter]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  norm_num [Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeSign,
    Fin.sum_univ_succ]

lemma jackson_two_aggregated_nonzeroMass :
    (∑ h ∈ Finset.image
        (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 2)
        Finset.univ with h ≠ 0,
      |aggregatedCoefficient
        (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 2 2)
        (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 2) h|) =
      (7 : ℝ) / 4 := by
  have himage :
      Finset.image
        (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 2)
          Finset.univ = {-3, -2, -1, 0, 1, 2, 3} := by
    decide
  rw [himage]
  norm_num [aggregatedCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeFrequency,
    Theory.PiDigits.PiNaturalScaleResonanceObstruction.edgeSign,
    Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

lemma jacksonWeightedFourierLoad_separatorSample_two :
    Theory.PiDigits.WeightedNaturalScaleFrontier.jacksonWeightedFourierLoad
      jacksonSeparatorSample 8 2 = (11 : ℝ) / 32 := by
  unfold Theory.PiDigits.WeightedNaturalScaleFrontier.jacksonWeightedFourierLoad
    Theory.PiDigits.WeightedNaturalScaleFrontier.normalizedWeightedFourierLoad
  have hsum :
      (∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 2 with
          Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
        |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 2 2 i| *
          ‖Theory.PiDigits.T27.exponentialSum jacksonSeparatorSample 8
            (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i)‖) =
        (11 : ℝ) / 4 := by
    calc
      _ = ∑ i : Theory.PiDigits.PiNaturalScaleResonanceObstruction.JacksonIndex 2 with
          Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency i ≠ 0,
          |Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 2 2 i| := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne := (Finset.mem_filter.mp hi).2
        rw [jacksonSeparatorSample_exponentialSum _ hne
          (jacksonFrequency_two_natAbs_le_three i)]
        simp
      _ = (11 : ℝ) / 4 := jackson_two_raw_nonzeroMass
  rw [hsum]
  norm_num

lemma aggregatedJacksonFourierLoad_separatorSample_two :
    aggregatedJacksonFourierLoad jacksonSeparatorSample 8 2 = (7 : ℝ) / 32 := by
  unfold aggregatedJacksonFourierLoad normalizedAggregatedFourierLoad
  have hsum :
      (∑ h ∈ Finset.image
          (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 2)
          Finset.univ with h ≠ 0,
        |aggregatedCoefficient
          (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 2 2)
          (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 2) h| *
          ‖Theory.PiDigits.T27.exponentialSum jacksonSeparatorSample 8 h‖) =
        (7 : ℝ) / 4 := by
    calc
      _ = ∑ h ∈ Finset.image
          (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 2)
          Finset.univ with h ≠ 0,
          |aggregatedCoefficient
            (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient 2 2)
            (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency 2) h| := by
        apply Finset.sum_congr rfl
        intro h hh
        have hne := (Finset.mem_filter.mp hh).2
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hh).1
        rw [jacksonSeparatorSample_exponentialSum _ hne
          (jacksonFrequency_two_natAbs_le_three i)]
        simp
      _ = (7 : ℝ) / 4 := jackson_two_aggregated_nonzeroMass
  rw [hsum]
  norm_num

/-- Jackson-specific strictness at an actual threshold: the aggregated load
passes the order-two criterion while the raw termwise-absolute load fails it.
This is a generic finite separator, not a claim about the decimal orbit of pi. -/
theorem aggregatedJacksonCriterion_strict_separator :
    ∃ x : ℕ → ℝ, ∃ N q : ℕ, 0 < N ∧ 0 < q ∧
      aggregatedJacksonFourierLoad x N q <
        1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ∧
      ¬ (Theory.PiDigits.WeightedNaturalScaleFrontier.jacksonWeightedFourierLoad
          x N q < 1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) := by
  refine ⟨jacksonSeparatorSample, 8, 2, by norm_num, by norm_num, ?_, ?_⟩
  · rw [aggregatedJacksonFourierLoad_separatorSample_two]
    norm_num
  · rw [jacksonWeightedFourierLoad_separatorSample_two]
    norm_num

end Theory.PiDigits.AggregatedJacksonFrontier

#print axioms Theory.PiDigits.AggregatedJacksonFrontier.finiteFourierPresentation_aggregated_obstruction
#print axioms Theory.PiDigits.AggregatedJacksonFrontier.aggregatedJacksonFourierLoad_le_jacksonWeightedFourierLoad
#print axioms Theory.PiDigits.AggregatedJacksonFrontier.finite_decimalInterval_hit_of_aggregated_smallness
#print axioms Theory.PiDigits.AggregatedJacksonFrontier.piNaturalScaleAggregatedCancellation_implies_canonicalV1
#print axioms Theory.PiDigits.AggregatedJacksonFrontier.aggregatedJacksonCriterion_strict_separator
