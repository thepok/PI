import TheoryLib.PiLongLagBlockCollisionDecay.T19T19SparsePeriodicIslands
import TheoryLib.PiLongLagBlockCollisionDecay.T53T53PrefixFaithfulFiniteWords
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn
import Mathlib.Analysis.Real.OfDigits
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational

/-!
# T55: direct infinite selection for the sparse-periodic sibling

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
Canonical SHA-256:
`db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
Original source URL: none; the canonical file records a local formulation on 2026-07-23.

This module constructs a sibling base-ten stream. It makes no assertion about
the distinguished constant in the canonical question and does not assert the
canonical collision-decay statement.
-/

noncomputable section

open Finset Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T55

open Theory.PiDigits.LongLagBlockCollisionDecay.T19
open Theory.PiDigits.LongLagBlockCollisionDecay.T53

/-- Uniform probability on one base-ten digit. -/
def digitMeasure : Measure (Fin 10) := uniformOn Set.univ

instance digitMeasure_isProbability : IsProbabilityMeasure digitMeasure := by
  unfold digitMeasure
  infer_instance

/-- Independent uniform digits before sparse-periodic coordinates are identified. -/
def independentDigitMeasure : Measure DecimalStream :=
  Measure.infinitePi fun _ : ℕ => digitMeasure

instance independentDigitMeasure_isProbability :
    IsProbabilityMeasure independentDigitMeasure := by
  unfold independentDigitMeasure
  infer_instance

/-- Identify every repeated-island coordinate with its cutoff-independent T53 root. -/
def rootProjection (x : DecimalStream) : DecimalStream :=
  fun i => x (rootIndex i)

theorem measurable_rootProjection : Measurable rootProjection := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (rootIndex i)

/-- The infinite probability measure supported on root-projected streams. -/
def sparseStreamMeasure : Measure DecimalStream :=
  independentDigitMeasure.map rootProjection

instance sparseStreamMeasure_isProbability :
    IsProbabilityMeasure sparseStreamMeasure := by
  unfold sparseStreamMeasure
  exact Measure.isProbabilityMeasure_map measurable_rootProjection.aemeasurable

/-- The constructed infinite stream measure has total mass one. -/
theorem sparseStreamMeasure_univ : sparseStreamMeasure Set.univ = 1 := by
  exact measure_univ

instance prefixFaithfulWordSpace_finite (n : ℕ) :
    Finite (PrefixFaithfulWordSpace n) :=
  Finite.of_injective (prefixFaithfulWordEquiv n)
    (prefixFaithfulWordEquiv n).injective

instance prefixFaithfulWordSpace_nonempty (n : ℕ) :
    Nonempty (PrefixFaithfulWordSpace n) :=
  ⟨(prefixFaithfulWordEquiv n).symm (fun _ => 0)⟩

instance prefixFaithfulWordSpace_measurableSpace (n : ℕ) :
    MeasurableSpace (PrefixFaithfulWordSpace n) := ⊤

/-- The prefix-faithful word generated from the independent root digits. -/
def generatedPrefix (n : ℕ) (x : DecimalStream) : PrefixFaithfulWordSpace n :=
  (prefixFaithfulWordEquiv n).symm
    ((partialFreeCoordinates n).restrict x)

@[simp] theorem generatedPrefix_apply (n : ℕ) (x : DecimalStream) (i : Fin n) :
    (generatedPrefix n x).1 i = x (rootIndex i.val) := by
  rfl

theorem measurable_generatedPrefix (n : ℕ) : Measurable (generatedPrefix n) := by
  exact (measurable_of_finite _).comp (measurable_restrict _)

/-- Uniform probability on the complete T53 prefix space. -/
def prefixUniformMeasure (n : ℕ) : Measure (PrefixFaithfulWordSpace n) :=
  uniformOn Set.univ

instance prefixUniformMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (prefixUniformMeasure n) := by
  unfold prefixUniformMeasure
  infer_instance

theorem map_uniformOn_univ_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (e : α ≃ β) :
    (uniformOn (Set.univ : Set α)).map e =
      uniformOn (Set.univ : Set β) := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite e) (measurableSet_singleton b)]
  have hpre : e ⁻¹' ({b} : Set β) = {e.symm b} := by
    ext a
    exact e.apply_eq_iff_eq_symm_apply
  rw [hpre, uniformOn_univ, uniformOn_univ]
  simp [Fintype.card_congr e]

/-- Restricting independent digits to T53's genuinely free coordinates is
the finite uniform product measure. -/
theorem independentDigitMeasure_map_freeRestriction (n : ℕ) :
    independentDigitMeasure.map (partialFreeCoordinates n).restrict =
      uniformOn (Set.univ : Set (FreeCoordinate n → Fin 10)) := by
  rw [independentDigitMeasure, Measure.infinitePi_map_restrict]
  symm
  simpa [digitMeasure] using
    (uniformOn_pi
      (Ω := Fin 10)
      (ι := FreeCoordinate n)
      (f := fun _ : FreeCoordinate n => (Set.univ : Set (Fin 10))))

/-- Exact finite-prefix pushforward: every T53 prefix-faithful word has the
uniform marginal prescribed by its finite cardinality. -/
theorem generatedPrefix_pushforward (n : ℕ) :
    independentDigitMeasure.map (generatedPrefix n) = prefixUniformMeasure n := by
  letI : Fintype (PrefixFaithfulWordSpace n) := Fintype.ofFinite _
  have hcomp : generatedPrefix n =
      (prefixFaithfulWordEquiv n).symm ∘
        (partialFreeCoordinates n).restrict := rfl
  rw [hcomp, ← Measure.map_map]
  rw [independentDigitMeasure_map_freeRestriction]
  exact map_uniformOn_univ_equiv (prefixFaithfulWordEquiv n).symm
  · exact measurable_of_countable _
  · exact Finset.measurable_restrict _

/-- Prefix pushforwards are projectively consistent under T53 restriction. -/
theorem generatedPrefix_restriction_consistency
    {m n : ℕ} (hmn : m ≤ n) :
    (prefixUniformMeasure n).map (restrictWord hmn) = prefixUniformMeasure m := by
  rw [← generatedPrefix_pushforward n, ← generatedPrefix_pushforward m,
    Measure.map_map]
  · congr 1
  · exact measurable_of_countable _
  · exact measurable_generatedPrefix n

/-- Literal first-`n` coordinates of an arbitrary infinite stream. -/
def streamPrefix (n : ℕ) (d : DecimalStream) : DecimalWord n :=
  fun i => d i.val

theorem measurable_streamPrefix (n : ℕ) : Measurable (streamPrefix n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.val

/-- Forget the T53 proof field of a finite prefix-faithful word. -/
def prefixValue (n : ℕ) (w : PrefixFaithfulWordSpace n) : DecimalWord n := w.1

theorem measurable_prefixValue (n : ℕ) : Measurable (prefixValue n) := by
  exact measurable_of_finite _

/-- Direct marginal statement for the constrained infinite measure: its
literal first `n` digits are the value-map pushforward of uniform T53 words. -/
theorem sparseStreamMeasure_prefixMarginal (n : ℕ) :
    sparseStreamMeasure.map (streamPrefix n) =
      (prefixUniformMeasure n).map (prefixValue n) := by
  rw [sparseStreamMeasure, Measure.map_map,
    ← generatedPrefix_pushforward n, Measure.map_map]
  · congr 1
  · exact measurable_prefixValue n
  · exact measurable_generatedPrefix n
  · exact measurable_streamPrefix n
  · exact measurable_rootProjection

/-- The root projection agrees with every one of its finite prefix words. -/
theorem rootProjection_prefix (n : ℕ) (x : DecimalStream) (i : Fin n) :
    rootProjection x i.val = (generatedPrefix n x).1 i := by
  rfl

/-- Every root-projected stream carries all of T19's sparse periodic islands. -/
theorem rootProjection_satisfiesSparsePeriodicSchedule (x : DecimalStream) :
    SatisfiesSparsePeriodicSchedule (rootProjection x) := by
  intro k
  refine
    { period_pos := (schedule_parameters k).1
      island_fits := le_of_eq (schedule_parameters k).2
      periodic := ?_ }
  intro t ht
  funext r
  let n := scheduleSampleSize k
  let w := generatedPrefix n x
  have hvisible :
      scheduleStart k + t * scheduleBlockLength k + r.val < n := by
    dsimp [n]
    have ht1 : t + 1 ≤ schedulePeriodCount k := by omega
    have hr := r.isLt
    simp only [scheduleSampleSize]
    have hmul : (t + 1) * scheduleBlockLength k ≤
        schedulePeriodCount k * scheduleBlockLength k :=
      Nat.mul_le_mul_right (scheduleBlockLength k) ht1
    nlinarith
  have hw := prefixFaithfulWord_partialIslandConstraint w ht r hvisible
  simpa [streamBlock, rootProjection, w, n] using hw

/-- Measurable support set carrying every exact T19 sparse-periodic island. -/
def sparseScheduleSet : Set DecimalStream :=
  {d | SatisfiesSparsePeriodicSchedule d}

theorem measurableSet_sparseScheduleSet : MeasurableSet sparseScheduleSet := by
  let C : Set DecimalStream :=
    ⋂ k : ℕ, ⋂ t : Fin (schedulePeriodCount k),
      ⋂ r : Fin (scheduleBlockLength k),
        {d | d (scheduleStart k + t.val * scheduleBlockLength k + r.val) =
          d (scheduleStart k + r.val)}
  have hC : MeasurableSet C := by
    dsimp [C]
    exact MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun t =>
        MeasurableSet.iInter fun r =>
          measurableSet_eq_fun
            (measurable_pi_apply
              (scheduleStart k + t.val * scheduleBlockLength k + r.val))
            (measurable_pi_apply (scheduleStart k + r.val))
  have heq : sparseScheduleSet = C := by
    ext d
    constructor
    · intro hd
      rw [Set.mem_iInter]
      intro k
      rw [Set.mem_iInter]
      intro t
      rw [Set.mem_iInter]
      intro r
      exact congrFun ((hd k).periodic t.val t.isLt) r
    · intro hd
      rw [Set.mem_iInter] at hd
      intro k
      refine
        { period_pos := (schedule_parameters k).1
          island_fits := le_of_eq (schedule_parameters k).2
          periodic := ?_ }
      intro t ht
      funext r
      have hk := hd k
      rw [Set.mem_iInter] at hk
      have hkt := hk ⟨t, ht⟩
      rw [Set.mem_iInter] at hkt
      exact hkt r
  rw [heq]
  exact hC

/-- The constructed infinite probability measure is supported almost surely
on streams satisfying every T19 sparse-periodic-island constraint. -/
theorem sparseStreamMeasure_schedule_ae :
    ∀ᵐ d ∂sparseStreamMeasure, SatisfiesSparsePeriodicSchedule d := by
  rw [sparseStreamMeasure]
  apply (ae_map_iff measurable_rootProjection.aemeasurable
    measurableSet_sparseScheduleSet).2
  exact ae_of_all independentDigitMeasure
    rootProjection_satisfiesSparsePeriodicSchedule

/-- Base-ten evaluation of an infinite sibling stream. -/
def decimalEvaluation (d : DecimalStream) : ℝ := Real.ofDigits d

theorem continuous_decimalEvaluation : Continuous decimalEvaluation := by
  exact Real.continuous_ofDigits

theorem measurable_decimalEvaluation : Measurable decimalEvaluation :=
  continuous_decimalEvaluation.measurable

/-- The finite sum of the first `n` digits is the T53 numerical prefix code
divided by `10^n`. -/
theorem generatedPrefix_sum_eq_code_div
    (n : ℕ) (x : DecimalStream) :
    (∑ i ∈ Finset.range n, Real.ofDigitsTerm (rootProjection x) i) =
      (finiteWordCode (generatedPrefix n x)).val / ((10 : ℝ) ^ n) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Real.ofDigitsTerm, rootProjection,
    finiteWordCode,
    Theory.PiDigits.LongLagBlockCollisionDecay.T53.toCompletedWord,
    Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCode,
    Theory.PiDigits.PositiveLowerBlockDensity.T12.decimalWordIndexEquiv,
    Theory.PiDigits.PositiveLowerBlockDensity.T10.alignedIndexEquiv,
    Equiv.trans_apply, Equiv.arrowCongr_apply,
    finFunctionFinEquiv_apply, finCongr_apply, Fin.val_cast]
  rw [Nat.cast_sum]
  conv_lhs => rw [← Equiv.sum_comp Fin.revPerm]
  rw [Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.revPerm_apply]
  have hsum : i.rev.val + 1 + i.val = n := by
    simp [Fin.rev]
    omega
  have hpow : (10 : ℝ) ^ n =
      (10 : ℝ) ^ (i.rev.val + 1) * (10 : ℝ) ^ i.val := by
    rw [← pow_add, hsum]
  rw [hpow]
  field_simp
  change (((x (rootIndex i.rev.val)).val : ℕ) : ℝ) =
    ((((generatedPrefix n x).1 i.rev).val : ℕ) : ℝ)
  rw [generatedPrefix_apply]

/-- Every root-projected evaluation lies in the closed level-`n` cylinder
with code given by its exact T53 prefix. -/
theorem decimalEvaluation_mem_generatedPrefix_closedCylinder
    (n : ℕ) (x : DecimalStream) :
    decimalEvaluation (rootProjection x) ∈ Set.Icc
      ((finiteWordCode (generatedPrefix n x)).val / ((10 ^ n : ℕ) : ℝ))
      ((((finiteWordCode (generatedPrefix n x)).val + 1 : ℕ) : ℝ) /
        ((10 ^ n : ℕ) : ℝ)) := by
  rw [decimalEvaluation, Real.ofDigits_eq_sum_add_ofDigits,
    generatedPrefix_sum_eq_code_div]
  have htail0 := Real.ofDigits_nonneg
    (fun i => rootProjection x (i + n))
  have htail1 := Real.ofDigits_le_one
    (fun i => rootProjection x (i + n))
  have hpow : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (by positivity) htail0)
  · calc
      (finiteWordCode (generatedPrefix n x)).val / (10 : ℝ) ^ n +
          ((10 : ℝ) ^ n)⁻¹ *
            Real.ofDigits (fun i => rootProjection x (i + n)) ≤
        (finiteWordCode (generatedPrefix n x)).val / (10 : ℝ) ^ n +
          ((10 : ℝ) ^ n)⁻¹ * 1 := by gcongr
      _ = (((finiteWordCode (generatedPrefix n x)).val + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ n := by
        push_cast
        field_simp

/-- Prefix words whose half-open T53 cylinder meets a closed real interval. -/
def prefixIntervalEventSet (n : ℕ) (a b : ℝ) :
    Set (PrefixFaithfulWordSpace n) :=
  {w | (finiteWordCylinder w ∩ Set.Icc a b).Nonempty}

/-- A root-projected value in the open interval forces its generated prefix
to belong to T53's endpoint-safe interval event. -/
theorem openInterval_subset_generatedPrefix_event
    (n : ℕ) (a b : ℝ) :
    {x : DecimalStream | decimalEvaluation (rootProjection x) ∈ Set.Ioo a b} ⊆
      generatedPrefix n ⁻¹' prefixIntervalEventSet n a b := by
  intro x hx
  let w := generatedPrefix n x
  let L : ℝ := (finiteWordCode w).val / ((10 ^ n : ℕ) : ℝ)
  let U : ℝ := (((finiteWordCode w).val + 1 : ℕ) : ℝ) /
    ((10 ^ n : ℕ) : ℝ)
  have hclosed : decimalEvaluation (rootProjection x) ∈ Set.Icc L U := by
    simpa [w, L, U] using
      decimalEvaluation_mem_generatedPrefix_closedCylinder n x
  change (finiteWordCylinder w ∩ Set.Icc a b).Nonempty
  have hLU : L < U := by
    dsimp [L, U]
    have hpow : (0 : ℝ) < ((10 ^ n : ℕ) : ℝ) := by positivity
    apply (div_lt_div_iff_of_pos_right hpow).2
    norm_num
  by_cases hbelow : decimalEvaluation (rootProjection x) < U
  · exact ⟨decimalEvaluation (rootProjection x),
      by simpa [finiteWordCylinder, w, L, U] using ⟨hclosed.1, hbelow⟩,
      ⟨hx.1.le, hx.2.le⟩⟩
  · have heq : decimalEvaluation (rootProjection x) = U := by
      exact le_antisymm hclosed.2 (le_of_not_gt hbelow)
    let y := max L ((a + U) / 2)
    have haU : a < U := by simpa [heq] using hx.1
    have hyL : L ≤ y := le_max_left _ _
    have hyMid : (a + U) / 2 ≤ y := le_max_right _ _
    have hmidU : (a + U) / 2 < U := by linarith
    have hyU : y < U := (max_lt_iff.mpr ⟨hLU, hmidU⟩)
    have hay : a ≤ y := by linarith
    have hyb : y ≤ b := by
      have hUb : U < b := by simpa [heq] using hx.2
      linarith
    exact ⟨y,
      by simpa [finiteWordCylinder, w, L, U] using ⟨hyL, hyU⟩,
      ⟨hay, hyb⟩⟩

/-- The exact real-valued mass of T53's finite interval event under the
uniform prefix marginal. -/
theorem prefixUniformMeasure_interval_real
    (n : ℕ) (a b : ℝ) :
    (prefixUniformMeasure n).real (prefixIntervalEventSet n a b) =
      finiteIntervalMass n a b := by
  letI : Fintype (PrefixFaithfulWordSpace n) := Fintype.ofFinite _
  rw [Measure.real, prefixUniformMeasure, uniformOn_univ]
  simp only [finiteIntervalMass]
  rw [Measure.count_apply_finite _ (Set.toFinite _)]
  rw [ENNReal.toReal_div]
  · simp only [ENNReal.toReal_natCast]
    congr 1
    · norm_cast
      rw [← Nat.card_eq_card_finite_toFinset (Set.toFinite _)]
      rfl
    · rw [Fintype.card_eq_nat_card]

/-- Infinite-measure interval bound obtained by combining the exact prefix
marginal with T53's finite anti-concentration estimate. -/
theorem sparseStreamMeasure_openInterval_le
    (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (hab : a ≤ b)
    (hlength : b - a ≤ (((10 ^ n : ℕ) : ℝ))⁻¹) :
    sparseStreamMeasure.real
        {d : DecimalStream | decimalEvaluation d ∈ Set.Ioo a b} ≤
      3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) := by
  have hmeas : MeasurableSet
      {d : DecimalStream | decimalEvaluation d ∈ Set.Ioo a b} :=
    (isOpen_Ioo.preimage continuous_decimalEvaluation).measurableSet
  have hmap : sparseStreamMeasure.real
      {d : DecimalStream | decimalEvaluation d ∈ Set.Ioo a b} =
      independentDigitMeasure.real
        {x : DecimalStream |
          decimalEvaluation (rootProjection x) ∈ Set.Ioo a b} := by
    simp only [sparseStreamMeasure, Measure.real]
    rw [Measure.map_apply measurable_rootProjection hmeas]
    congr 2
  rw [hmap]
  have hmono := measureReal_mono
    (openInterval_subset_generatedPrefix_event n a b)
    (measure_ne_top independentDigitMeasure
      (generatedPrefix n ⁻¹' prefixIntervalEventSet n a b))
  calc
    independentDigitMeasure.real
        {x : DecimalStream |
          decimalEvaluation (rootProjection x) ∈ Set.Ioo a b} ≤
        independentDigitMeasure.real
          (generatedPrefix n ⁻¹' prefixIntervalEventSet n a b) := hmono
    _ = (prefixUniformMeasure n).real (prefixIntervalEventSet n a b) := by
      simp only [Measure.real]
      rw [← Measure.map_apply (measurable_generatedPrefix n)]
      · rw [generatedPrefix_pushforward]
      · exact Set.toFinite _ |>.measurableSet
    _ = finiteIntervalMass n a b :=
      prefixUniformMeasure_interval_real n a b
    _ ≤ 3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) :=
      finiteIntervalMass_le_halfDensity n hn a b hab hlength

/-- Decimal depth assigned to the denominator shell
`10^k ≤ q < 10^(k+1)`. -/
def shellDepth (k : ℕ) : ℕ := 7 * k - 1

/-- Strict exponent-seven approximation by the displayed rational `p/q`. -/
def rationalApproxEvent (q : ℕ) (p : ℤ) : Set DecimalStream :=
  {d | |decimalEvaluation d - (p : ℝ) / (q : ℝ)| <
    1 / (q : ℝ) ^ 7}

theorem measurableSet_rationalApproxEvent (q : ℕ) (p : ℤ) :
    MeasurableSet (rationalApproxEvent q p) := by
  unfold rationalApproxEvent
  exact measurableSet_lt
    ((measurable_decimalEvaluation.sub measurable_const).abs)
    measurable_const

/-- At shell depth `7k-1`, one level-`n` cylinder is at least as long as
an exponent-seven rational interval for every `q ≥ 10^k`. -/
theorem exponentSeven_interval_le_shellCylinder
    {k q : ℕ} (hk : 1 ≤ k) (hq : 10 ^ k ≤ q) :
    2 / (q : ℝ) ^ 7 ≤
      (((10 ^ shellDepth k : ℕ) : ℝ))⁻¹ := by
  have hdepth : shellDepth k + 1 = 7 * k := by
    unfold shellDepth
    omega
  have hnat : 2 * 10 ^ shellDepth k ≤ q ^ 7 := by
    calc
      2 * 10 ^ shellDepth k ≤ 10 * 10 ^ shellDepth k := by
        exact Nat.mul_le_mul_right _ (by norm_num)
      _ = 10 ^ (shellDepth k + 1) := by
        rw [pow_succ']
      _ = 10 ^ (7 * k) := by rw [hdepth]
      _ = (10 ^ k) ^ 7 := by
        rw [show 7 * k = k * 7 by omega, pow_mul]
      _ ≤ q ^ 7 := by gcongr
  have hreal : (2 : ℝ) * ((10 ^ shellDepth k : ℕ) : ℝ) ≤
      (q : ℝ) ^ 7 := by exact_mod_cast hnat
  have hqreal : (0 : ℝ) < (q : ℝ) ^ 7 := by
    have hqpos : 0 < q :=
      lt_of_lt_of_le (pow_pos (by norm_num : 0 < 10) k) hq
    positivity
  have htenreal : (0 : ℝ) < ((10 ^ shellDepth k : ℕ) : ℝ) := by
    positivity
  rw [inv_eq_one_div]
  exact (div_le_div_iff₀ hqreal htenreal).2 (by simpa using hreal)

/-- T53's finite exponent-seven estimate lifted to the infinite stream
measure, with the shell and rational center explicit in the theorem type. -/
theorem sparseStreamMeasure_rationalApproxEvent_le
    {k q : ℕ} (hk : 1 ≤ k) (hq : 10 ^ k ≤ q) (p : ℤ) :
    sparseStreamMeasure.real (rationalApproxEvent q p) ≤
      3 * (10 : ℝ) ^ (-((shellDepth k / 2 : ℕ) : ℤ)) := by
  let c : ℝ := (p : ℝ) / (q : ℝ)
  let r : ℝ := 1 / (q : ℝ) ^ 7
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast lt_of_lt_of_le (pow_pos (by norm_num : 0 < 10) k) hq
  have hr : 0 < r := by dsimp [r]; positivity
  have hn : 1 ≤ shellDepth k := by
    unfold shellDepth
    omega
  have hlength : (c + r) - (c - r) ≤
      (((10 ^ shellDepth k : ℕ) : ℝ))⁻¹ := by
    have hscale := exponentSeven_interval_le_shellCylinder hk hq
    calc
      (c + r) - (c - r) = 2 / (q : ℝ) ^ 7 := by
        dsimp [r]
        ring
      _ ≤ (((10 ^ shellDepth k : ℕ) : ℝ))⁻¹ := hscale
  have hbound := sparseStreamMeasure_openInterval_le
    (shellDepth k) hn (c - r) (c + r) (by linarith) hlength
  have hevent : rationalApproxEvent q p =
      {d : DecimalStream | decimalEvaluation d ∈ Set.Ioo (c - r) (c + r)} := by
    ext d
    change (|decimalEvaluation d - (p : ℝ) / (q : ℝ)| <
      1 / (q : ℝ) ^ 7) ↔ _
    rw [Set.mem_setOf_eq, Set.mem_Ioo]
    dsimp [c, r]
    rw [abs_lt]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rwa [hevent]

/-- A coarser power form used for summing complete denominator shells. -/
theorem sparseStreamMeasure_rationalApproxEvent_le_shellPower
    {k q : ℕ} (hk : 1 ≤ k) (hq : 10 ^ k ≤ q) (p : ℤ) :
    sparseStreamMeasure.real (rationalApproxEvent q p) ≤
      3 * (10 : ℝ) ^ (-((3 * k : ℕ) : ℤ)) := by
  refine (sparseStreamMeasure_rationalApproxEvent_le hk hq p).trans ?_
  have hhalf : 3 * k ≤ shellDepth k / 2 := by
    unfold shellDepth
    omega
  have hpow : (10 : ℝ) ^ (3 * k) ≤
      (10 : ℝ) ^ (shellDepth k / 2) :=
    pow_le_pow_right₀ (by norm_num) hhalf
  have hinv : ((10 : ℝ) ^ (shellDepth k / 2))⁻¹ ≤
      ((10 : ℝ) ^ (3 * k))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hneg : (10 : ℝ) ^ (-((shellDepth k / 2 : ℕ) : ℤ)) ≤
      (10 : ℝ) ^ (-((3 * k : ℕ) : ℤ)) := by
    simpa [zpow_neg, zpow_natCast] using hinv
  exact mul_le_mul_of_nonneg_left hneg (by norm_num)

/-- Denominators in the `k`th decimal shell. -/
def denominatorShell (k : ℕ) : Finset ℕ :=
  Finset.Ico (10 ^ k) (10 ^ (k + 1))

/-- All integer numerators capable of approximating a value in `[0,1]` to
distance less than one with denominator `q`. -/
def numeratorWindow (q : ℕ) : Finset ℤ :=
  Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))

theorem numeratorWindow_card (q : ℕ) :
    (numeratorWindow q).card = 3 * q + 1 := by
  simp [numeratorWindow]
  omega

/-- The union of all exponent-seven rational events in shell `k+1`.
The shift makes every shell depth positive. -/
def denominatorShellEvent (k : ℕ) : Set DecimalStream :=
  ⋃ q ∈ denominatorShell (k + 1),
    ⋃ p ∈ numeratorWindow q, rationalApproxEvent q p

/-- Explicit geometric majorant for complete denominator shells. -/
def shellMajorant (k : ℕ) : ℝ :=
  1200 * (1 / 10 : ℝ) ^ (k + 1)

/-- A complete denominator shell has geometrically decaying mass after
summing every admissible numerator. -/
theorem denominatorShellEvent_measureReal_le (k : ℕ) :
    sparseStreamMeasure.real (denominatorShellEvent k) ≤ shellMajorant k := by
  let K := k + 1
  let A : ℝ := 3 * (10 : ℝ) ^ (-((3 * K : ℕ) : ℤ))
  have hK : 1 ≤ K := by simp [K]
  have houter : sparseStreamMeasure.real (denominatorShellEvent k) ≤
      ∑ q ∈ denominatorShell K,
        sparseStreamMeasure.real
          (⋃ p ∈ numeratorWindow q, rationalApproxEvent q p) := by
    simpa only [denominatorShellEvent, K] using
      (measureReal_biUnion_finset_le
        (μ := sparseStreamMeasure)
        (denominatorShell K)
        (fun q => ⋃ p ∈ numeratorWindow q, rationalApproxEvent q p))
  have hinner (q : ℕ) (hq : q ∈ denominatorShell K) :
      sparseStreamMeasure.real
          (⋃ p ∈ numeratorWindow q, rationalApproxEvent q p) ≤
        ∑ p ∈ numeratorWindow q, A := by
    refine (measureReal_biUnion_finset_le
      (μ := sparseStreamMeasure) (numeratorWindow q)
      (rationalApproxEvent q)).trans ?_
    apply Finset.sum_le_sum
    intro p hp
    have hqlower : 10 ^ K ≤ q := (Finset.mem_Ico.mp hq).1
    exact sparseStreamMeasure_rationalApproxEvent_le_shellPower
      hK hqlower p
  have hsum : sparseStreamMeasure.real (denominatorShellEvent k) ≤
      ∑ q ∈ denominatorShell K, ∑ p ∈ numeratorWindow q, A :=
    houter.trans (Finset.sum_le_sum fun q hq => hinner q hq)
  have hnum (q : ℕ) (hq : q ∈ denominatorShell K) :
      (numeratorWindow q).card ≤ 4 * 10 ^ (K + 1) := by
    rw [numeratorWindow_card]
    have hqupper : q < 10 ^ (K + 1) := (Finset.mem_Ico.mp hq).2
    omega
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hshellcard : (denominatorShell K).card ≤ 10 ^ (K + 1) := by
    rw [denominatorShell, Nat.card_Ico]
    exact Nat.sub_le _ _
  have hcount :
      (∑ q ∈ denominatorShell K, ∑ p ∈ numeratorWindow q, A) ≤
        ((10 ^ (K + 1) : ℕ) : ℝ) *
          (((4 * 10 ^ (K + 1) : ℕ) : ℝ) * A) := by
    calc
      (∑ q ∈ denominatorShell K, ∑ p ∈ numeratorWindow q, A) =
          ∑ q ∈ denominatorShell K, ((numeratorWindow q).card : ℝ) * A := by
            simp
      _ ≤ ∑ _q ∈ denominatorShell K,
          ((4 * 10 ^ (K + 1) : ℕ) : ℝ) * A := by
            apply Finset.sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnum q hq) hA
      _ = ((denominatorShell K).card : ℝ) *
          (((4 * 10 ^ (K + 1) : ℕ) : ℝ) * A) := by simp
      _ ≤ ((10 ^ (K + 1) : ℕ) : ℝ) *
          (((4 * 10 ^ (K + 1) : ℕ) : ℝ) * A) := by
            gcongr
  refine hsum.trans (hcount.trans_eq ?_)
  dsimp [shellMajorant, A]
  change ((10 ^ (K + 1) : ℕ) : ℝ) *
      (((4 * 10 ^ (K + 1) : ℕ) : ℝ) *
        (3 * (10 : ℝ) ^ (-((3 * K : ℕ) : ℤ)))) =
    1200 * (1 / 10 : ℝ) ^ K
  rw [zpow_neg, zpow_natCast]
  have hpowK : (0 : ℝ) < (10 : ℝ) ^ K := by positivity
  have hnext : ((10 ^ (K + 1) : ℕ) : ℝ) =
      (10 : ℝ) ^ K * 10 := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_succ]
  have hthree : (10 : ℝ) ^ (3 * K) = ((10 : ℝ) ^ K) ^ 3 := by
    rw [show 3 * K = K * 3 by omega, pow_mul]
  have hinv : (1 / 10 : ℝ) ^ K = ((10 : ℝ) ^ K)⁻¹ := by
    simp
  rw [hnext, hthree, hinv]
  push_cast
  field_simp [hpowK.ne']
  ring

/-- The explicit denominator-shell majorant is summable. -/
theorem summable_shellMajorant : Summable shellMajorant := by
  unfold shellMajorant
  exact (summable_nat_add_iff 1).2
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 1200)

/-- Real masses of all denominator-shell events are summable. -/
theorem summable_denominatorShellEvent_measureReal :
    Summable (fun k => sparseStreamMeasure.real (denominatorShellEvent k)) := by
  exact summable_shellMajorant.of_nonneg_of_le
    (fun _ => measureReal_nonneg)
    denominatorShellEvent_measureReal_le

/-- Streams lying in infinitely many complete denominator shells. -/
def rationalExceptionalSet : Set DecimalStream :=
  {d | {k : ℕ | d ∈ denominatorShellEvent k}.Infinite}

/-- First Borel-Cantelli for the exponent-seven denominator shells. -/
theorem sparseStreamMeasure_rationalExceptionalSet_eq_zero :
    sparseStreamMeasure rationalExceptionalSet = 0 := by
  have hreal := summable_denominatorShellEvent_measureReal
  have heq :
      (fun k => ENNReal.ofReal
        (sparseStreamMeasure.real (denominatorShellEvent k))) =
      (fun k => sparseStreamMeasure (denominatorShellEvent k)) := by
    funext k
    exact ofReal_measureReal
  have hsum : (∑' k, sparseStreamMeasure (denominatorShellEvent k)) ≠ ∞ := by
    rw [← heq]
    exact hreal.tsum_ofReal_ne_top
  have hfinite : ∀ᵐ d ∂sparseStreamMeasure,
      {k : ℕ | d ∈ denominatorShellEvent k}.Finite :=
    ae_finite_setOf_mem hsum
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hfinite] with d hd
  exact fun hinfinite => hinfinite hd

theorem decimalEvaluation_mem_unitInterval (d : DecimalStream) :
    decimalEvaluation d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg d, Real.ofDigits_le_one d⟩

/-- Every exponent-seven approximation to a decimal value uses a numerator
in the finite window employed by its denominator shell. -/
theorem numerator_mem_window_of_mem_rationalApproxEvent
    {d : DecimalStream} {q : ℕ} {p : ℤ} (hq : 1 ≤ q)
    (hd : d ∈ rationalApproxEvent q p) : p ∈ numeratorWindow q := by
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqreal
  have hr : 1 / (q : ℝ) ^ 7 ≤ 1 := by
    have hp : (1 : ℝ) ≤ (q : ℝ) ^ 7 := one_le_pow₀ hqreal
    simpa only [one_div] using (inv_le_one₀ (by positivity)).2 hp
  have habs : |decimalEvaluation d - (p : ℝ) / (q : ℝ)| <
      1 / (q : ℝ) ^ 7 := hd
  have hparts := abs_lt.mp habs
  have hx := decimalEvaluation_mem_unitInterval d
  have hpLowerDiv : (-1 : ℝ) < (p : ℝ) / (q : ℝ) := by
    linarith [hparts.2, hx.1]
  have hpUpperDiv : (p : ℝ) / (q : ℝ) < 2 := by
    linarith [hparts.1, hx.2]
  have hpLower : -(q : ℝ) < (p : ℝ) := by
    have := (lt_div_iff₀ hqpos).mp hpLowerDiv
    simpa using this
  have hpUpper : (p : ℝ) < 2 * (q : ℝ) :=
    (div_lt_iff₀ hqpos).mp hpUpperDiv
  rw [numeratorWindow, Finset.mem_Icc]
  constructor
  · exact_mod_cast le_of_lt hpLower
  · exact_mod_cast le_of_lt hpUpper

/-- Explicit meaning of “irrationality exponent at most seven” used here:
beyond one denominator onset, no displayed rational is closer than `q⁻⁷`. -/
def IrrationalityExponentAtMostSeven (x : ℝ) : Prop :=
  ∃ Q0 : ℕ, ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ p : ℤ,
    1 / (q : ℝ) ^ 7 ≤ |x - (p : ℝ) / (q : ℝ)|

/-- Avoiding the Borel-Cantelli exceptional set gives the explicit
exponent-seven lower bound for the decimal evaluation. -/
theorem not_mem_rationalExceptionalSet_implies_exponentSeven
    {d : DecimalStream} (hd : d ∉ rationalExceptionalSet) :
    IrrationalityExponentAtMostSeven (decimalEvaluation d) := by
  have hfinite : {k : ℕ | d ∈ denominatorShellEvent k}.Finite := by
    exact Set.not_infinite.mp hd
  let s : Finset ℕ := hfinite.toFinset
  let K0 : ℕ := s.sup id + 1
  have htail : ∀ k : ℕ, K0 ≤ k → d ∉ denominatorShellEvent k := by
    intro k hk hmem
    have hks : k ∈ s := by simpa [s] using hmem
    have hle : k ≤ s.sup id := by
      exact Finset.le_sup (f := id) hks
    dsimp [K0] at hk
    omega
  refine ⟨10 ^ (K0 + 1), ?_⟩
  intro q hqQ hqpos p
  by_contra hbad
  have happrox : d ∈ rationalApproxEvent q p := by
    rw [rationalApproxEvent, Set.mem_setOf_eq]
    exact lt_of_not_ge hbad
  let L := Nat.log 10 q
  have hqmem : q ∈ denominatorShell L := by
    rw [denominatorShell, Finset.mem_Ico]
    exact ⟨Nat.pow_log_le_self 10 (Nat.ne_of_gt hqpos),
      Nat.lt_pow_succ_log_self (by norm_num) q⟩
  have hlog : K0 + 1 ≤ L := by
    exact Nat.le_log_of_pow_le (by norm_num) hqQ
  have hLpos : 1 ≤ L := le_trans (Nat.succ_le_succ (Nat.zero_le K0)) hlog
  have hindex : K0 ≤ L - 1 := by omega
  have hpwin : p ∈ numeratorWindow q :=
    numerator_mem_window_of_mem_rationalApproxEvent (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hqpos)) happrox
  have hshell : d ∈ denominatorShellEvent (L - 1) := by
    rw [denominatorShellEvent]
    have hsucc : L - 1 + 1 = L := by omega
    rw [hsucc]
    exact Set.mem_iUnion_of_mem q <| Set.mem_iUnion_of_mem hqmem <|
      Set.mem_iUnion_of_mem p <| Set.mem_iUnion_of_mem hpwin happrox
  exact htail (L - 1) hindex hshell

theorem measurableSet_denominatorShellEvent (k : ℕ) :
    MeasurableSet (denominatorShellEvent k) := by
  unfold denominatorShellEvent
  apply Finset.measurableSet_biUnion
  intro q hq
  apply Finset.measurableSet_biUnion
  intro p hp
  exact measurableSet_rationalApproxEvent q p

/-- Pullback of one shell event to the independent root-digit space. -/
def sourceShellEvent (k : ℕ) : Set DecimalStream :=
  rootProjection ⁻¹' denominatorShellEvent k

theorem sourceShellEvent_measureReal (k : ℕ) :
    independentDigitMeasure.real (sourceShellEvent k) =
      sparseStreamMeasure.real (denominatorShellEvent k) := by
  simp only [sourceShellEvent, sparseStreamMeasure, Measure.real]
  rw [Measure.map_apply measurable_rootProjection
    (measurableSet_denominatorShellEvent k)]

theorem summable_sourceShellEvent_measureReal :
    Summable (fun k => independentDigitMeasure.real (sourceShellEvent k)) := by
  apply summable_denominatorShellEvent_measureReal.congr
  intro k
  exact (sourceShellEvent_measureReal k).symm

/-- Borel-Cantelli exceptional set on the independent source space. -/
def sourceExceptionalSet : Set DecimalStream :=
  {x | {k : ℕ | x ∈ sourceShellEvent k}.Infinite}

theorem independentDigitMeasure_sourceExceptionalSet_eq_zero :
    independentDigitMeasure sourceExceptionalSet = 0 := by
  have hreal := summable_sourceShellEvent_measureReal
  have heq :
      (fun k => ENNReal.ofReal
        (independentDigitMeasure.real (sourceShellEvent k))) =
      (fun k => independentDigitMeasure (sourceShellEvent k)) := by
    funext k
    exact ofReal_measureReal
  have hsum : (∑' k, independentDigitMeasure (sourceShellEvent k)) ≠ ∞ := by
    rw [← heq]
    exact hreal.tsum_ofReal_ne_top
  have hfinite : ∀ᵐ x ∂independentDigitMeasure,
      {k : ℕ | x ∈ sourceShellEvent k}.Finite :=
    ae_finite_setOf_mem hsum
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hfinite] with x hx
  exact fun hinfinite => hinfinite hx

theorem exists_source_not_exceptional :
    ∃ x : DecimalStream, x ∉ sourceExceptionalSet := by
  by_contra hnone
  push Not at hnone
  have hall : sourceExceptionalSet = Set.univ := Set.eq_univ_of_forall hnone
  have hzero := independentDigitMeasure_sourceExceptionalSet_eq_zero
  rw [hall, measure_univ] at hzero
  norm_num at hzero

theorem rootProjection_not_exceptional_of_source
    {x : DecimalStream} (hx : x ∉ sourceExceptionalSet) :
    rootProjection x ∉ rationalExceptionalSet := by
  intro hbad
  apply hx
  simpa [sourceExceptionalSet, rationalExceptionalSet, sourceShellEvent] using hbad

/-- The explicit exponent-seven lower bound excludes rational values. -/
theorem irrational_of_exponentAtMostSeven
    {x : ℝ} (hx : IrrationalityExponentAtMostSeven x) : Irrational x := by
  by_contra hrat
  obtain ⟨r : ℚ, hr : x = r⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨Q0, hQ0⟩ := hx
  let M : ℕ := Q0 + 1
  let q : ℕ := r.den * M
  let p : ℤ := r.num * (M : ℤ)
  have hM : 0 < M := by simp [M]
  have hrden : 0 < r.den := r.den_pos
  have hqpos : 0 < q := by exact Nat.mul_pos hrden hM
  have hqQ0 : Q0 ≤ q := by
    have hMle : M ≤ q := by
      dsimp [q]
      exact Nat.le_mul_of_pos_left M hrden
    dsimp [M] at hMle
    omega
  have hlower := hQ0 q hqQ0 hqpos p
  have heq : (p : ℝ) / (q : ℝ) = x := by
    calc
      (p : ℝ) / (q : ℝ) =
          ((r.num : ℝ) * (M : ℝ)) /
            ((r.den : ℝ) * (M : ℝ)) := by
              simp [p, q]
      _ = (r.num : ℝ) / (r.den : ℝ) := by
            field_simp
      _ = (r : ℝ) := (Rat.cast_def r).symm
      _ = x := hr.symm
  rw [heq, sub_self, abs_zero] at hlower
  have : (0 : ℝ) < 1 / (q : ℝ) ^ 7 := by positivity
  linarith

/-- Direct infinite sibling selection. The theorem exposes the evaluated
real, exponent-seven bound, irrationality, T19 schedule transfer, and exact
failure of the ordered collision predicate at `s=1/2`. -/
theorem exists_irrational_sparsePeriodic_collisionFailure :
    ∃ d : DecimalStream,
      Irrational (decimalEvaluation d) ∧
      IrrationalityExponentAtMostSeven (decimalEvaluation d) ∧
      SatisfiesSparsePeriodicSchedule d ∧
      ¬ StreamCollisionDecayAt d (1 / 2 : ℝ) := by
  obtain ⟨x, hx⟩ := exists_source_not_exceptional
  let d := rootProjection x
  have hdExceptional : d ∉ rationalExceptionalSet :=
    rootProjection_not_exceptional_of_source hx
  have hdExponent : IrrationalityExponentAtMostSeven (decimalEvaluation d) :=
    not_mem_rationalExceptionalSet_implies_exponentSeven hdExceptional
  have hdSchedule : SatisfiesSparsePeriodicSchedule d :=
    rootProjection_satisfiesSparsePeriodicSchedule x
  exact ⟨d, irrational_of_exponentAtMostSeven hdExponent, hdExponent,
    hdSchedule, sparsePeriodicSchedule_fails_collisionDecayAt_half hdSchedule⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T55

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.sparseStreamMeasure_univ
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.generatedPrefix_pushforward
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.generatedPrefix_restriction_consistency
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.sparseStreamMeasure_prefixMarginal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.rootProjection_satisfiesSparsePeriodicSchedule
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.sparseStreamMeasure_schedule_ae
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.measurable_decimalEvaluation
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.decimalEvaluation_mem_generatedPrefix_closedCylinder
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.sparseStreamMeasure_openInterval_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.sparseStreamMeasure_rationalApproxEvent_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.denominatorShellEvent_measureReal_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.summable_denominatorShellEvent_measureReal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.sparseStreamMeasure_rationalExceptionalSet_eq_zero
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.not_mem_rationalExceptionalSet_implies_exponentSeven
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.independentDigitMeasure_sourceExceptionalSet_eq_zero
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.irrational_of_exponentAtMostSeven
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T55.exists_irrational_sparsePeriodic_collisionFailure
