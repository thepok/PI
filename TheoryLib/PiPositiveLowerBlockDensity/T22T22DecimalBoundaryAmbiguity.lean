import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiPositiveLowerBlockDensity.T20T20SynchronizedObstruction
import TheoryLib.PiPositiveLowerBlockDensity.T8T8AlignedEntropyDeficit
import TheoryLib.PiQuantitativeBlockHitting.T16T16DecimalBoundaryWordObstruction
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy

/-!
# T22: decimal-boundary ambiguity for the synchronized obstruction

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

Every conclusion about pi is necessary-only and conditional on the literal
negation of canonical C1. The endpoint estimates retain the entire possible
atom at `0`; no left-right split of that atom is asserted.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T22

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open DecimalFactorComplexity
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.FiniteCylinderEnergy

/-- A point of `R/Z` is a terminating decimal boundary precisely when some
iterate of multiplication by ten reaches `0`. -/
def IsTerminatingDecimalBoundary (x : UnitAddCircle) : Prop :=
  ∃ k : ℕ, (timesTen^[k]) x = 0

/-- The decimal grid point `m / 10^k`, viewed on `R/Z`. -/
def decimalBoundaryPoint (k m : ℕ) : UnitAddCircle :=
  (((m : ℝ) / (10 : ℝ) ^ k : ℝ) : UnitAddCircle)

theorem iterate_timesTen (k : ℕ) (x : UnitAddCircle) :
    (timesTen^[k]) x = (10 ^ k : ℕ) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [timesTen, pow_succ]
      rw [mul_nsmul]

/-- Every power-of-ten rational grid point is a terminating decimal boundary. -/
theorem decimalBoundaryPoint_isTerminating (k m : ℕ) :
    IsTerminatingDecimalBoundary (decimalBoundaryPoint k m) := by
  refine ⟨k, ?_⟩
  rw [iterate_timesTen]
  unfold decimalBoundaryPoint
  rw [← AddCircle.coe_nsmul]
  simp only [nsmul_eq_mul]
  change ((((10 ^ k : ℕ) : ℝ) * ((m : ℝ) / (10 : ℝ) ^ k) : ℝ) :
    UnitAddCircle) = 0
  have hpow : ((10 ^ k : ℕ) : ℝ) = (10 : ℝ) ^ k := by norm_cast
  rw [hpow]
  field_simp
  exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2 ⟨(m : ℤ), by simp⟩

/-- Invariance identifies the mass of a measurable set with the mass of its
preimage under multiplication by ten. -/
theorem measure_preimage_timesTen_eq_of_invariant
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {A : Set UnitAddCircle} (hA : MeasurableSet A) :
    (ν : Measure UnitAddCircle) (timesTen ⁻¹' A) =
      (ν : Measure UnitAddCircle) A := by
  have h := congrArg
    (fun ρ : ProbabilityMeasure UnitAddCircle => (ρ : Measure UnitAddCircle) A)
    hinvariant
  simpa [timesTenMap, Measure.map_apply_of_aemeasurable
    timesTen_continuous.measurable.aemeasurable hA] using h

/-- A nonzero point immediately mapping to zero cannot carry mass in an
invariant probability measure: the zero atom already consumes the full mass
of the preimage of `{0}`. -/
theorem atom_eq_zero_of_timesTen_eq_zero
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {x : UnitAddCircle} (hx0 : x ≠ 0) (hx : timesTen x = 0) :
    (ν : Measure UnitAddCircle) {x} = 0 := by
  have hsubset : ({0} ∪ {x} : Set UnitAddCircle) ⊆ timesTen ⁻¹' {0} := by
    intro y hy
    rcases hy with hy | hy
    · subst y
      simp [timesTen]
    · subst y
      simpa using hx
  have hle : (ν : Measure UnitAddCircle) ({0} ∪ {x}) ≤
      (ν : Measure UnitAddCircle) (timesTen ⁻¹' {0}) :=
    measure_mono hsubset
  have hdis : Disjoint ({0} : Set UnitAddCircle) {x} := by
    simp only [Set.disjoint_singleton_right, Set.mem_singleton_iff]
    exact hx0
  rw [measure_union hdis (measurableSet_singleton x),
    measure_preimage_timesTen_eq_of_invariant ν hinvariant
      (measurableSet_singleton (0 : UnitAddCircle))] at hle
  have hxle : (ν : Measure UnitAddCircle) {x} ≤
      (ν : Measure UnitAddCircle) {0} - (ν : Measure UnitAddCircle) {0} :=
    ENNReal.le_sub_of_add_le_left (measure_ne_top _ _) hle
  exact bot_unique (by simpa using hxle)

/-- Every nonzero terminating decimal boundary is atomless for an invariant
probability measure. -/
theorem terminatingDecimalBoundary_atomless
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {x : UnitAddCircle} (hterm : IsTerminatingDecimalBoundary x) (hx0 : x ≠ 0) :
    (ν : Measure UnitAddCircle) {x} = 0 := by
  obtain ⟨k, hk⟩ := hterm
  induction k generalizing x with
  | zero =>
      simp only [Function.iterate_zero_apply] at hk
      exact (hx0 hk).elim
  | succ k ih =>
      have hnext : (timesTen^[k]) (timesTen x) = 0 := by
        simpa only [Function.iterate_succ_apply] using hk
      by_cases htx : timesTen x = 0
      · exact atom_eq_zero_of_timesTen_eq_zero ν hinvariant hx0 htx
      · have hnextZero : (ν : Measure UnitAddCircle) {timesTen x} = 0 :=
          ih htx hnext
        apply le_antisymm
        · calc
            (ν : Measure UnitAddCircle) {x} ≤
                (ν : Measure UnitAddCircle) (timesTen ⁻¹' {timesTen x}) := by
              apply measure_mono
              intro y hy
              simpa only [Set.mem_singleton_iff] using congrArg timesTen hy
            _ = (ν : Measure UnitAddCircle) {timesTen x} :=
              measure_preimage_timesTen_eq_of_invariant ν hinvariant
                (measurableSet_singleton (timesTen x))
            _ = 0 := hnextZero
        · exact bot_le

/-- The canonical half-open circle cylinder belonging to a decimal word. -/
def wordCylinder (w : List (Fin 10)) : Set UnitAddCircle :=
  decimalCylinder w.length (wordIndex w)

/-- The left endpoint of a word cylinder. -/
def wordLeftBoundary (w : List (Fin 10)) : UnitAddCircle :=
  decimalBoundaryPoint w.length (Theory.PiDigits.T20.wordValue w)

/-- The right endpoint of a word cylinder. -/
def wordRightBoundary (w : List (Fin 10)) : UnitAddCircle :=
  decimalBoundaryPoint w.length (Theory.PiDigits.T20.wordValue w + 1)

theorem wordLeftBoundary_isTerminating (w : List (Fin 10)) :
    IsTerminatingDecimalBoundary (wordLeftBoundary w) :=
  decimalBoundaryPoint_isTerminating _ _

theorem wordRightBoundary_isTerminating (w : List (Fin 10)) :
    IsTerminatingDecimalBoundary (wordRightBoundary w) :=
  decimalBoundaryPoint_isTerminating _ _

/-- The half-open cylinder event is exactly the block event for the pi orbit. -/
theorem piCircleOrbit_mem_wordCylinder_iff (w : List (Fin 10)) (n : ℕ) :
    piCircleOrbit n ∈ wordCylinder w ↔
      ∀ i : Fin w.length, Theory.PiDigits.piDigit (n + i.val) = w.get i := by
  have horbit : piCircleOrbit n =
      DecimalFactorComplexity.ClusterNearReturns.piDecimalCircleOrbit n := rfl
  rw [horbit, wordCylinder]
  change decimalCode w.length
      (DecimalFactorComplexity.ClusterNearReturns.piDecimalCircleOrbit n) = wordIndex w ↔ _
  rw [← piCylinderCode_eq_decimalCode]
  constructor
  · intro hcode
    have hvalue : Theory.PiDigits.T20.wordValue
        (prefixWord piDecimalStream w.length n) =
        Theory.PiDigits.T20.wordValue w := congrArg Fin.val hcode
    have hword : prefixWord piDecimalStream w.length n = w :=
      Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_injective_of_length
        (by simp [prefixWord]) hvalue
    intro i
    have hget := congrArg (fun u : List (Fin 10) => u[i.val]?) hword
    simp [prefixWord, i.isLt] at hget
    simpa [List.get_eq_getElem, piDecimalStream,
      Theory.PiDigits.T20.decimalDigit_pi] using hget
  · intro hmatch
    apply Fin.ext
    change Theory.PiDigits.T20.wordValue
        (prefixWord piDecimalStream w.length n) =
      Theory.PiDigits.T20.wordValue w
    congr 1
    apply List.ext_get
    · simp [prefixWord]
    · intro i hi₁ hi₂
      simpa [prefixWord, piDecimalStream,
        Theory.PiDigits.T20.decimalDigit_pi] using hmatch ⟨i, hi₂⟩

theorem piOrbitSetCount_wordCylinder_eq_blockCount
    (w : List (Fin 10)) (N : ℕ) :
    piOrbitSetCount N (wordCylinder w) =
      blockCount Theory.PiDigits.piDigit w N := by
  classical
  unfold piOrbitSetCount blockCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact piCircleOrbit_mem_wordCylinder_iff w n.val

/-- At every positive cutoff, empirical cylinder mass is exactly the
corresponding overlapping block frequency. -/
theorem piEmpiricalMeasure_wordCylinder
    (w : List (Fin 10)) (N : ℕ) (hN : 0 < N) :
    (piEmpiricalMeasure N : Measure UnitAddCircle) (wordCylinder w) =
      ENNReal.ofReal (blockFrequency Theory.PiDigits.piDigit w N) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [piEmpiricalMeasure_apply_succ M (A := wordCylinder w)
      (by exact decimalCylinder_measurable _ _),
    piOrbitSetCount_wordCylinder_eq_blockCount]
  rw [blockFrequency, ENNReal.ofReal_div_of_pos]
  · simp only [ENNReal.ofReal_natCast, Nat.succ_eq_add_one, Nat.cast_add,
      Nat.cast_one]
    rw [ENNReal.ofReal_add (Nat.cast_nonneg M) zero_le_one]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  · positivity

def wordLeftReal (w : List (Fin 10)) : ℝ :=
  (Theory.PiDigits.T20.wordValue w : ℝ) / (10 : ℝ) ^ w.length

def wordRightReal (w : List (Fin 10)) : ℝ :=
  ((Theory.PiDigits.T20.wordValue w + 1 : ℕ) : ℝ) /
    (10 : ℝ) ^ w.length

def wordOpenCylinder (w : List (Fin 10)) : Set UnitAddCircle :=
  ((fun x : ℝ => (x : UnitAddCircle)) ''
    Set.Ioo (wordLeftReal w) (wordRightReal w))

def wordClosedCylinder (w : List (Fin 10)) : Set UnitAddCircle :=
  ((fun x : ℝ => (x : UnitAddCircle)) ''
    Set.Icc (wordLeftReal w) (wordRightReal w))

theorem wordLeftReal_nonneg (w : List (Fin 10)) : 0 ≤ wordLeftReal w := by
  simp [wordLeftReal]
  positivity

theorem wordLeftReal_lt_right (w : List (Fin 10)) :
    wordLeftReal w < wordRightReal w := by
  unfold wordLeftReal wordRightReal
  apply div_lt_div_of_pos_right _ (by positivity)
  push_cast
  linarith

theorem wordRightReal_le_one (w : List (Fin 10)) : wordRightReal w ≤ 1 := by
  unfold wordRightReal
  apply (div_le_one (by positivity)).2
  exact_mod_cast Theory.PiDigits.T20.wordValue_lt_pow_length w

theorem wordLeftBoundary_eq_coe (w : List (Fin 10)) :
    wordLeftBoundary w = (wordLeftReal w : UnitAddCircle) := rfl

theorem wordRightBoundary_eq_coe (w : List (Fin 10)) :
    wordRightBoundary w = (wordRightReal w : UnitAddCircle) := rfl

/-- The code-based canonical cylinder is the quotient image of its ordinary
half-open real interval. -/
theorem wordCylinder_eq_image_Ico (w : List (Fin 10)) :
    wordCylinder w =
      ((fun x : ℝ => (x : UnitAddCircle)) ''
        Set.Ico (wordLeftReal w) (wordRightReal w)) := by
  ext x
  rw [Set.mem_image]
  constructor
  · intro hx
    have hcoord := (mem_decimalCylinder_iff w.length (wordIndex w) x).1 hx
    refine ⟨unitCoordinate x, ?_, coe_unitCoordinate x⟩
    simpa [wordLeftReal, wordRightReal, wordIndex] using hcoord
  · rintro ⟨y, hy, rfl⟩
    apply (mem_decimalCylinder_iff w.length (wordIndex w) (y : UnitAddCircle)).2
    have hy01 : y ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨(wordLeftReal_nonneg w).trans hy.1,
        hy.2.trans_le (wordRightReal_le_one w)⟩
    have hcoord : unitCoordinate (y : UnitAddCircle) = y := by
      exact congrArg Subtype.val
        (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0)
          (by simpa only [zero_add] using hy01))
    rw [hcoord]
    simpa [wordLeftReal, wordRightReal, wordIndex] using hy

theorem wordOpenCylinder_isOpen (w : List (Fin 10)) :
    IsOpen (wordOpenCylinder w) := by
  exact (QuotientAddGroup.isOpenMap_coe :
    IsOpenMap ((↑) : ℝ → UnitAddCircle)) _ isOpen_Ioo

theorem wordClosedCylinder_isClosed (w : List (Fin 10)) :
    IsClosed (wordClosedCylinder w) := by
  exact (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed

theorem wordOpenCylinder_subset_wordCylinder (w : List (Fin 10)) :
    wordOpenCylinder w ⊆ wordCylinder w := by
  rw [wordCylinder_eq_image_Ico]
  exact Set.image_mono Set.Ioo_subset_Ico_self

theorem wordCylinder_subset_wordClosedCylinder (w : List (Fin 10)) :
    wordCylinder w ⊆ wordClosedCylinder w := by
  rw [wordCylinder_eq_image_Ico]
  exact Set.image_mono Set.Ico_subset_Icc_self

/-- The closed/open envelope differs only at the two represented endpoints. -/
theorem wordClosedCylinder_subset_open_union_endpoints (w : List (Fin 10)) :
    wordClosedCylinder w ⊆
      wordOpenCylinder w ∪ {wordLeftBoundary w, wordRightBoundary w} := by
  rintro x ⟨y, hy, rfl⟩
  by_cases hleft : y = wordLeftReal w
  · right
    left
    simpa [wordLeftBoundary_eq_coe] using congrArg
      (fun z : ℝ => (z : UnitAddCircle)) hleft
  by_cases hright : y = wordRightReal w
  · right
    right
    simpa [wordRightBoundary_eq_coe] using congrArg
      (fun z : ℝ => (z : UnitAddCircle)) hright
  · left
    exact ⟨y, ⟨lt_of_le_of_ne hy.1 (Ne.symm hleft),
      lt_of_le_of_ne hy.2 hright⟩, rfl⟩

theorem wordBoundary_atoms_eq_zero_of_ne_zero
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    (w : List (Fin 10))
    (hleft : wordLeftBoundary w ≠ 0) (hright : wordRightBoundary w ≠ 0) :
    (ν : Measure UnitAddCircle) {wordLeftBoundary w} = 0 ∧
      (ν : Measure UnitAddCircle) {wordRightBoundary w} = 0 := by
  exact ⟨terminatingDecimalBoundary_atomless ν hinvariant
      (wordLeftBoundary_isTerminating w) hleft,
    terminatingDecimalBoundary_atomless ν hinvariant
      (wordRightBoundary_isTerminating w) hright⟩

/-- The entire closed/open cylinder gap is supported on its two endpoint
atoms. -/
theorem measure_wordClosedCylinder_le_open_add_endpoint_atoms
    (ν : ProbabilityMeasure UnitAddCircle) (w : List (Fin 10)) :
    (ν : Measure UnitAddCircle) (wordClosedCylinder w) ≤
      (ν : Measure UnitAddCircle) (wordOpenCylinder w) +
        (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
          (ν : Measure UnitAddCircle) {wordRightBoundary w} := by
  calc
    (ν : Measure UnitAddCircle) (wordClosedCylinder w) ≤
        (ν : Measure UnitAddCircle)
          (wordOpenCylinder w ∪ {wordLeftBoundary w, wordRightBoundary w}) :=
      measure_mono (wordClosedCylinder_subset_open_union_endpoints w)
    _ ≤ (ν : Measure UnitAddCircle) (wordOpenCylinder w) +
        (ν : Measure UnitAddCircle) {wordLeftBoundary w, wordRightBoundary w} :=
      measure_union_le _ _
    _ ≤ (ν : Measure UnitAddCircle) (wordOpenCylinder w) +
        ((ν : Measure UnitAddCircle) {wordLeftBoundary w} +
          (ν : Measure UnitAddCircle) {wordRightBoundary w}) := by
      gcongr
      have hp : (ν : Measure UnitAddCircle)
          (({wordLeftBoundary w} : Set UnitAddCircle) ∪
            {wordRightBoundary w}) ≤
          (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w} :=
        measure_union_le _ _
      simpa only [Set.insert_eq] using hp
    _ = _ := by ac_rfl

theorem tendsto_empirical_wordCylinder
    (w : List (Fin 10)) (cutoffs : ℕ → ℕ) (hpositive : ∀ n, 0 < cutoffs n)
    (edge : ℝ)
    (hfrequency : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit w (cutoffs n))
      atTop (𝓝 edge)) :
    Tendsto
      (fun n => (piEmpiricalMeasure (cutoffs n) : Measure UnitAddCircle)
        (wordCylinder w)) atTop (𝓝 (ENNReal.ofReal edge)) := by
  apply ((ENNReal.continuous_ofReal.tendsto edge).comp hfrequency).congr'
  exact Filter.Eventually.of_forall fun n =>
    (piEmpiricalMeasure_wordCylinder w (cutoffs n) (hpositive n)).symm

/-- Portmanteau places the limiting flow coordinate between the open and
closed cylinder masses. -/
theorem flowCoordinate_between_open_closed_masses
    (w : List (Fin 10)) (cutoffs : ℕ → ℕ) (hpositive : ∀ n, 0 < cutoffs n)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν))
    (edge : ℝ)
    (hfrequency : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit w (cutoffs n))
      atTop (𝓝 edge)) :
    (ν : Measure UnitAddCircle) (wordOpenCylinder w) ≤ ENNReal.ofReal edge ∧
      ENNReal.ofReal edge ≤
        (ν : Measure UnitAddCircle) (wordClosedCylinder w) := by
  have hC := tendsto_empirical_wordCylinder w cutoffs hpositive edge hfrequency
  constructor
  · have hopen := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν
      (wordOpenCylinder_isOpen w)
    have hmono : liminf (fun n =>
        (piEmpiricalMeasure (cutoffs n) : Measure UnitAddCircle)
          (wordOpenCylinder w)) atTop ≤
        liminf (fun n =>
          (piEmpiricalMeasure (cutoffs n) : Measure UnitAddCircle)
            (wordCylinder w)) atTop :=
      liminf_le_liminf (Filter.Eventually.of_forall fun n =>
        measure_mono (wordOpenCylinder_subset_wordCylinder w))
    rw [hC.liminf_eq] at hmono
    exact hopen.trans hmono
  · have hclosed :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν
        (wordClosedCylinder_isClosed w)
    have hmono : limsup (fun n =>
        (piEmpiricalMeasure (cutoffs n) : Measure UnitAddCircle)
          (wordCylinder w)) atTop ≤
        limsup (fun n =>
          (piEmpiricalMeasure (cutoffs n) : Measure UnitAddCircle)
            (wordClosedCylinder w)) atTop :=
      limsup_le_limsup (Filter.Eventually.of_forall fun n =>
        measure_mono (wordCylinder_subset_wordClosedCylinder w))
    rw [hC.limsup_eq] at hmono
    exact hmono.trans hclosed

/-- Both directions of the endpoint discrepancy are bounded by the endpoint
atoms, with no convention assigning either side of an atom. -/
theorem endpointCylinder_discrepancy_bounds
    (w : List (Fin 10)) (cutoffs : ℕ → ℕ) (hpositive : ∀ n, 0 < cutoffs n)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν))
    (edge : ℝ)
    (hfrequency : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit w (cutoffs n))
      atTop (𝓝 edge)) :
    (ν : Measure UnitAddCircle) (wordCylinder w) ≤
        ENNReal.ofReal edge +
          (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w} ∧
      ENNReal.ofReal edge ≤
        (ν : Measure UnitAddCircle) (wordCylinder w) +
          (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w} := by
  have hbetween := flowCoordinate_between_open_closed_masses
    w cutoffs hpositive ν hν edge hfrequency
  have hgap := measure_wordClosedCylinder_le_open_add_endpoint_atoms ν w
  constructor
  · calc
      (ν : Measure UnitAddCircle) (wordCylinder w) ≤
          (ν : Measure UnitAddCircle) (wordClosedCylinder w) :=
        measure_mono (wordCylinder_subset_wordClosedCylinder w)
      _ ≤ (ν : Measure UnitAddCircle) (wordOpenCylinder w) +
          (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w} := hgap
      _ ≤ ENNReal.ofReal edge +
          (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w} := by
        gcongr
        exact hbetween.1
  · calc
      ENNReal.ofReal edge ≤
          (ν : Measure UnitAddCircle) (wordClosedCylinder w) := hbetween.2
      _ ≤ (ν : Measure UnitAddCircle) (wordOpenCylinder w) +
          (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w} := hgap
      _ ≤ (ν : Measure UnitAddCircle) (wordCylinder w) +
          (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w} := by
        gcongr
        exact wordOpenCylinder_subset_wordCylinder w

/-- If neither represented endpoint is `0`, invariance makes the cylinder a
continuity set and identifies its mass with the flow coordinate. -/
theorem flowCoordinate_eq_halfOpenCylinder_of_boundaries_ne_zero
    (w : List (Fin 10)) (cutoffs : ℕ → ℕ) (hpositive : ∀ n, 0 < cutoffs n)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν))
    (hinvariant : timesTenMap ν = ν)
    (edge : ℝ)
    (hfrequency : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit w (cutoffs n))
      atTop (𝓝 edge))
    (hleft : wordLeftBoundary w ≠ 0) (hright : wordRightBoundary w ≠ 0) :
    (ν : Measure UnitAddCircle) (wordCylinder w) = ENNReal.ofReal edge := by
  obtain ⟨hleftZero, hrightZero⟩ :=
    wordBoundary_atoms_eq_zero_of_ne_zero ν hinvariant w hleft hright
  obtain ⟨hle, hge⟩ := endpointCylinder_discrepancy_bounds
    w cutoffs hpositive ν hν edge hfrequency
  rw [hleftZero, hrightZero, add_zero, add_zero] at hle hge
  exact le_antisymm hle hge

theorem wordBoundaries_not_both_zero (w : List (Fin 10)) (hw : 0 < w.length) :
    wordLeftBoundary w ≠ 0 ∨ wordRightBoundary w ≠ 0 := by
  by_cases hleft : wordLeftBoundary w ≠ 0
  · exact Or.inl hleft
  · right
    have hleftEq : wordLeftBoundary w = 0 := not_ne_iff.mp hleft
    have hleftMem : wordLeftReal w ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨wordLeftReal_nonneg w,
        (wordLeftReal_lt_right w).trans_le (wordRightReal_le_one w)⟩
    have hzeroMem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by norm_num
    have hleftReal : wordLeftReal w = 0 :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
        (by simpa only [zero_add] using hleftMem)
        (by simpa only [zero_add] using hzeroMem)).mp (by
        simpa [wordLeftBoundary_eq_coe] using hleftEq)
    have hvalueReal : (Theory.PiDigits.T20.wordValue w : ℝ) = 0 := by
      have hdiv : (Theory.PiDigits.T20.wordValue w : ℝ) /
          (10 : ℝ) ^ w.length = 0 := by
        simpa [wordLeftReal] using hleftReal
      exact (div_eq_zero_iff.mp hdiv).resolve_right (by positivity)
    have hvalue : Theory.PiDigits.T20.wordValue w = 0 := by
      exact_mod_cast hvalueReal
    have hpowNat : 10 ≤ 10 ^ w.length := by
      simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hw
    have hpowReal : (10 : ℝ) ≤ (10 : ℝ) ^ w.length := by
      exact_mod_cast hpowNat
    have hrightReal : wordRightReal w = 1 / (10 : ℝ) ^ w.length := by
      simp [wordRightReal, hvalue]
    have hrightPos : 0 < wordRightReal w := by
      rw [hrightReal]
      positivity
    have hrightLt : wordRightReal w < 1 := by
      rw [hrightReal]
      have hden : (1 : ℝ) < (10 : ℝ) ^ w.length := by linarith
      exact (div_lt_one (by positivity)).2 hden
    intro hrightEq
    have hrightRealZero : wordRightReal w = 0 :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
        (by simpa only [zero_add] using (show wordRightReal w ∈
          Set.Ico (0 : ℝ) 1 from ⟨hrightPos.le, hrightLt⟩))
        (by simpa only [zero_add] using hzeroMem)).mp (by
          simpa [wordRightBoundary_eq_coe] using hrightEq)
    linarith

theorem wordEndpointAtoms_le_zeroAtom
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    (w : List (Fin 10)) (hnotboth :
      wordLeftBoundary w ≠ 0 ∨ wordRightBoundary w ≠ 0) :
    (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
        (ν : Measure UnitAddCircle) {wordRightBoundary w} ≤
      (ν : Measure UnitAddCircle) {0} := by
  rcases hnotboth with hleft | hright
  · have hleftZero := terminatingDecimalBoundary_atomless ν hinvariant
      (wordLeftBoundary_isTerminating w) hleft
    by_cases hright0 : wordRightBoundary w = 0
    · rw [hleftZero, hright0, zero_add]
    · have hrightZero := terminatingDecimalBoundary_atomless ν hinvariant
        (wordRightBoundary_isTerminating w) hright0
      rw [hleftZero, hrightZero, add_zero]
      exact bot_le
  · have hrightZero := terminatingDecimalBoundary_atomless ν hinvariant
      (wordRightBoundary_isTerminating w) hright
    by_cases hleft0 : wordLeftBoundary w = 0
    · rw [hrightZero, hleft0, add_zero]
    · have hleftZero := terminatingDecimalBoundary_atomless ν hinvariant
        (wordLeftBoundary_isTerminating w) hleft0
      rw [hleftZero, hrightZero, add_zero]
      exact bot_le

/-- For every nonempty cylinder, both discrepancy directions are supported
and bounded by the single possible atom at `0`. -/
theorem endpointCylinder_discrepancy_supported_at_zero
    (w : List (Fin 10)) (hw : w ≠ [])
    (cutoffs : ℕ → ℕ) (hpositive : ∀ n, 0 < cutoffs n)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν))
    (hinvariant : timesTenMap ν = ν)
    (edge : ℝ)
    (hfrequency : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit w (cutoffs n))
      atTop (𝓝 edge)) :
    (ν : Measure UnitAddCircle) (wordCylinder w) ≤
        ENNReal.ofReal edge + (ν : Measure UnitAddCircle) {0} ∧
      ENNReal.ofReal edge ≤
        (ν : Measure UnitAddCircle) (wordCylinder w) +
          (ν : Measure UnitAddCircle) {0} := by
  have hwlen : 0 < w.length := List.length_pos_of_ne_nil hw
  have hatoms := wordEndpointAtoms_le_zeroAtom ν hinvariant w
    (wordBoundaries_not_both_zero w hwlen)
  obtain ⟨hle, hge⟩ := endpointCylinder_discrepancy_bounds
    w cutoffs hpositive ν hν edge hfrequency
  constructor
  · calc
      (ν : Measure UnitAddCircle) (wordCylinder w) ≤
          ENNReal.ofReal edge +
            (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
              (ν : Measure UnitAddCircle) {wordRightBoundary w} := hle
      _ = ENNReal.ofReal edge +
          ((ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w}) := by ac_rfl
      _ ≤ ENNReal.ofReal edge + (ν : Measure UnitAddCircle) {0} := by
        gcongr
  · calc
      ENNReal.ofReal edge ≤
          (ν : Measure UnitAddCircle) (wordCylinder w) +
            (ν : Measure UnitAddCircle) {wordLeftBoundary w} +
              (ν : Measure UnitAddCircle) {wordRightBoundary w} := hge
      _ = (ν : Measure UnitAddCircle) (wordCylinder w) +
          ((ν : Measure UnitAddCircle) {wordLeftBoundary w} +
            (ν : Measure UnitAddCircle) {wordRightBoundary w}) := by ac_rfl
      _ ≤ (ν : Measure UnitAddCircle) (wordCylinder w) +
          (ν : Measure UnitAddCircle) {0} := by
        gcongr

/-- T20's synchronized cluster has no atom at any nonzero terminating decimal
boundary. -/
theorem synchronizedCluster_terminatingBoundary_atomless
    (o : T20.NecessaryPiSynchronizedObstruction)
    {x : UnitAddCircle} (hterm : IsTerminatingDecimalBoundary x) (hx0 : x ≠ 0) :
    (o.cluster : Measure UnitAddCircle) {x} = 0 :=
  terminatingDecimalBoundary_atomless o.cluster o.cluster_invariant hterm hx0

/-- Every synchronized flow coordinate whose two cylinder endpoints avoid
`0` is exactly the corresponding half-open cluster mass. -/
theorem synchronizedFlow_eq_halfOpenCylinder_of_boundaries_ne_zero
    (o : T20.NecessaryPiSynchronizedObstruction)
    (u : T19.DecimalWord (o.vertexLength + 1))
    (hleft : wordLeftBoundary (List.ofFn u) ≠ 0)
    (hright : wordRightBoundary (List.ofFn u) ≠ 0) :
    (o.cluster : Measure UnitAddCircle) (wordCylinder (List.ofFn u)) =
      ENNReal.ofReal (o.edgeLimit u) := by
  apply flowCoordinate_eq_halfOpenCylinder_of_boundaries_ne_zero
    (List.ofFn u) o.cutoffs o.cutoffs_positive o.cluster
    o.empiricalMeasures_converge o.cluster_invariant (o.edgeLimit u)
  · simpa [T19.frequencyVector] using o.completeVector_converges u
  · exact hleft
  · exact hright

/-- For every synchronized edge, both endpoint-cylinder discrepancies are
bounded by and supported on the cluster atom at `0`. -/
theorem synchronizedEndpointCylinder_discrepancy_supported_at_zero
    (o : T20.NecessaryPiSynchronizedObstruction)
    (u : T19.DecimalWord (o.vertexLength + 1)) :
    (o.cluster : Measure UnitAddCircle) (wordCylinder (List.ofFn u)) ≤
        ENNReal.ofReal (o.edgeLimit u) +
          (o.cluster : Measure UnitAddCircle) {0} ∧
      ENNReal.ofReal (o.edgeLimit u) ≤
        (o.cluster : Measure UnitAddCircle) (wordCylinder (List.ofFn u)) +
          (o.cluster : Measure UnitAddCircle) {0} := by
  apply endpointCylinder_discrepancy_supported_at_zero
    (List.ofFn u) (by
      intro hempty
      have hlen := congrArg List.length hempty
      simp only [List.length_ofFn, List.length_nil] at hlen
      omega)
    o.cutoffs o.cutoffs_positive
    o.cluster o.empiricalMeasures_converge o.cluster_invariant (o.edgeLimit u)
  simpa [T19.frequencyVector] using o.completeVector_converges u

/-- Literal failure of canonical C1 gives T20's missing minimal word with the
exact boundary alternative: either its two endpoints avoid `0` and its
half-open cylinder has zero cluster mass, or an endpoint is `0` and the
cylinder mass is bounded by the unsplit atom at `0`. -/
theorem literal_not_C1_implies_missingWord_boundaryAlternative
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ o : T20.NecessaryPiSynchronizedObstruction,
      let w := List.ofFn o.deficientWord
      ((wordLeftBoundary w ≠ 0 ∧ wordRightBoundary w ≠ 0) ∧
          (o.cluster : Measure UnitAddCircle) (wordCylinder w) = 0) ∨
        ((wordLeftBoundary w = 0 ∨ wordRightBoundary w = 0) ∧
          (o.cluster : Measure UnitAddCircle) (wordCylinder w) ≤
            (o.cluster : Measure UnitAddCircle) {0}) := by
  obtain ⟨o⟩ := T20.literal_not_C1_implies_synchronized_minimal_flow_cluster hnot
  refine ⟨o, ?_⟩
  let w := List.ofFn o.deficientWord
  by_cases hleft : wordLeftBoundary w = 0
  · right
    refine ⟨Or.inl hleft, ?_⟩
    have hbound :=
      (synchronizedEndpointCylinder_discrepancy_supported_at_zero
        o o.deficientWord).1
    rw [o.deficientWord_zero_edge] at hbound
    simpa [w] using hbound
  · by_cases hright : wordRightBoundary w = 0
    · right
      refine ⟨Or.inr hright, ?_⟩
      have hbound :=
        (synchronizedEndpointCylinder_discrepancy_supported_at_zero
          o o.deficientWord).1
      rw [o.deficientWord_zero_edge] at hbound
      simpa [w] using hbound
    · left
      refine ⟨⟨hleft, hright⟩, ?_⟩
      have heq := synchronizedFlow_eq_halfOpenCylinder_of_boundaries_ne_zero
        o o.deficientWord (by simpa [w] using hleft) (by simpa [w] using hright)
      rw [o.deficientWord_zero_edge] at heq
      simpa [w] using heq

end Theory.PiDigits.PositiveLowerBlockDensity.T22

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T22.synchronizedCluster_terminatingBoundary_atomless
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T22.synchronizedFlow_eq_halfOpenCylinder_of_boundaries_ne_zero
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T22.synchronizedEndpointCylinder_discrepancy_supported_at_zero
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T22.literal_not_C1_implies_missingWord_boundaryAlternative
