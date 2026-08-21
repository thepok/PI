import TheoryLib.PiDigits.T27FiniteExponentialCylinderCoverage
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Probability.UniformOn

/-!
# Positive lower decimal-block density

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module formalizes the canonical A1 statement and its A8 empirical-measure
form.  It proves only equivalences and conditional implications; it does not
prove either open statement for the digits of pi.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity

/-- Number of starts `0 ≤ n < N` at which `w` occurs in `s`.
Occurrences overlap, and every start before `N` is tested even when the word
extends beyond the first `N` stream entries. -/
def blockCount (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) : ℕ :=
  (Finset.univ.filter fun n : Fin N =>
    ∀ i : Fin w.length, s (n.val + i) = w.get i).card

/-- Canonical normalization of the overlapping block count.  The value at
`N = 0` is immaterial to the limit along `atTop`. -/
def blockFrequency (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) : ℝ :=
  (blockCount s w N : ℝ) / N

/-- Positive lower asymptotic frequency for every nonempty decimal word.
Lists include words with leading zeros. -/
def HasPositiveLowerBlockDensity (s : ℕ → Fin 10) : Prop :=
  ∀ w : List (Fin 10), w ≠ [] →
    0 < liminf (blockFrequency s w) atTop

/-- A1, specialized to the exact floor-based pi stream from T7. -/
def PiPositiveLowerBlockDensity : Prop :=
  HasPositiveLowerBlockDensity Theory.PiDigits.piDigit

lemma blockFrequency_nonneg (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) :
    0 ≤ blockFrequency s w N := by
  exact div_nonneg (by positivity) (by positivity)

lemma blockCount_le (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) :
    blockCount s w N ≤ N := by
  unfold blockCount
  calc
    _ ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = N := Fintype.card_fin N

lemma blockFrequency_le_one (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) :
    blockFrequency s w N ≤ 1 := by
  by_cases hN : N = 0
  · simp [blockFrequency, hN]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)).2
    exact_mod_cast blockCount_le s w N

/-- A positive lower frequency supplies an actual contiguous occurrence. -/
theorem exists_block_occurrence_of_pos_liminf
    (s : ℕ → Fin 10) (w : List (Fin 10))
    (h : 0 < liminf (blockFrequency s w) atTop) :
    ∃ n : ℕ, ∀ i : ℕ, ∀ hi : i < w.length,
      s (n + i) = w.get ⟨i, hi⟩ := by
  have hb : atTop.IsBoundedUnder (· ≥ ·) (blockFrequency s w) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (blockFrequency_nonneg s w))
  have hevent : ∀ᶠ N : ℕ in atTop, 0 < blockFrequency s w N :=
    eventually_lt_of_lt_liminf h hb
  obtain ⟨N, hN⟩ := hevent.exists
  have hcount : 0 < blockCount s w N := by
    by_contra hzero
    have : blockCount s w N = 0 := Nat.eq_zero_of_not_pos hzero
    simp [blockFrequency, this] at hN
  rw [blockCount, Finset.card_pos] at hcount
  obtain ⟨n, hn⟩ := hcount
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
  refine ⟨n.val, ?_⟩
  intro i hi
  exact hn ⟨i, hi⟩

/-- Canonical A1 implies the exact T7.V1 proposition, without changing its
quantifiers or digit stream. -/
theorem piPositiveLowerBlockDensity_implies_T7V1
    (hA1 : PiPositiveLowerBlockDensity) : Theory.PiDigits.V1 := by
  intro w
  by_cases hw : w = []
  · exact ⟨0, by simp [hw]⟩
  · exact exists_block_occurrence_of_pos_liminf
      Theory.PiDigits.piDigit w (hA1 w hw)

/-- The exact base-ten fractional-part orbit from A8, represented on
`ℝ/ℤ = UnitAddCircle`. -/
def piCircleOrbit (n : ℕ) : UnitAddCircle :=
  (((10 : ℝ) ^ n * Real.pi : ℝ) : UnitAddCircle)

/-- The quotient-space orbit is exactly the source's fractional-part orbit. -/
theorem piCircleOrbit_eq_fract (n : ℕ) :
    piCircleOrbit n =
      ((Int.fract (((10 : ℝ) ^ n * Real.pi : ℝ)) : ℝ) : UnitAddCircle) := by
  exact (AddCircle.coe_fract ((10 : ℝ) ^ n * Real.pi)).symm

/-- The first-`N` empirical probability measure from A8.  At `N = 0` we use
an arbitrary Dirac mass; this isolated value does not affect accumulation at
`atTop`. -/
def piEmpiricalMeasure : ℕ → ProbabilityMeasure UnitAddCircle
  | 0 => diracProba 0
  | N + 1 =>
      let uniform : ProbabilityMeasure (Fin (N + 1)) :=
        ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
      uniform.map
        (measurable_of_finite
          (fun n : Fin (N + 1) => piCircleOrbit n.val)).aemeasurable

/-- Number of the first `N` orbit points lying in a set, with multiplicity. -/
def piOrbitSetCount (N : ℕ) (A : Set UnitAddCircle) : ℕ := by
  classical
  exact (Finset.univ.filter fun n : Fin N => piCircleOrbit n.val ∈ A).card

/-- Evaluation of the empirical measure is the normalized finite count,
including multiplicities. -/
theorem piEmpiricalMeasure_apply_succ (N : ℕ) {A : Set UnitAddCircle}
    (hA : MeasurableSet A) :
    (piEmpiricalMeasure (N + 1) : Measure UnitAddCircle) A =
      (piOrbitSetCount (N + 1) A : ENNReal) / (N + 1) := by
  rw [piEmpiricalMeasure]
  rw [ProbabilityMeasure.map_apply']
  · change ProbabilityTheory.uniformOn Set.univ
        ((fun n : Fin (N + 1) => piCircleOrbit n.val) ⁻¹' A) = _
    rw [ProbabilityTheory.uniformOn_univ]
    let S : Set (Fin (N + 1)) :=
      (fun n : Fin (N + 1) => piCircleOrbit n.val) ⁻¹' A
    have hS : S.Finite := Set.toFinite S
    rw [Measure.count_apply_finite S hS]
    simp only [Fintype.card_fin]
    congr 1
    norm_cast
    unfold piOrbitSetCount
    congr 1
    ext n
    simp [S]
    norm_num
  · exact hA

/-- A8: every weak-* accumulation point of the exact empirical measures on
`ℝ/ℤ` has full topological support. -/
def PiEveryEmpiricalClusterFullSupport : Prop :=
  ∀ μ : ProbabilityMeasure UnitAddCircle,
    MapClusterPt μ atTop piEmpiricalMeasure →
      (μ : Measure UnitAddCircle).support = Set.univ

/-- The length-`k` floor-based decimal prefix of a point of `[0,1)`. -/
def decimalPrefix (y : ℝ) (k : ℕ) : List (Fin 10) :=
  List.ofFn fun i : Fin k => Real.digits y 10 i.val

@[simp] theorem decimalPrefix_length (y : ℝ) (k : ℕ) :
    (decimalPrefix y k).length = k := by
  simp [decimalPrefix]

/-- Matching the first `k` digits of `y` puts the corresponding pi orbit
point in the closed circle ball of radius `10⁻ᵏ`.  Closedness is deliberate:
it is the direction needed by the closed-set Portmanteau inequality. -/
theorem pi_blockMatch_mem_closedBall (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (k n : ℕ)
    (hmatch : ∀ i : Fin k,
      Theory.PiDigits.piDigit (n + i.val) = Real.digits y 10 i.val) :
    piCircleOrbit n ∈ Metric.closedBall (y : UnitAddCircle) ((10 : ℝ) ^ k)⁻¹ := by
  have hprefix : ∀ i < k,
      Real.digits (Theory.PiDigits.T20.baseTenOrbit Real.pi n) 10 i =
        Real.digits y 10 i := by
    intro i hi
    change Theory.PiDigits.T20.decimalDigit
        (Theory.PiDigits.T20.baseTenOrbit Real.pi n) i = Real.digits y 10 i
    calc
      _ = Theory.PiDigits.T20.decimalDigit Real.pi (n + i) :=
        Theory.PiDigits.T20.decimalDigit_baseTenOrbit
          Real.pi Real.pi_pos.le n i
      _ = Theory.PiDigits.piDigit (n + i) :=
        Theory.PiDigits.T20.decimalDigit_pi (n + i)
      _ = Real.digits y 10 i := hmatch ⟨i, hi⟩
  have hclose := Real.abs_ofDigits_sub_ofDigits_le hprefix
  rw [Real.ofDigits_digits (by norm_num)
      (Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi n),
    Real.ofDigits_digits (by norm_num) hy] at hclose
  rw [Metric.mem_closedBall]
  change dist ((((10 : ℝ) ^ n * Real.pi : ℝ) : UnitAddCircle))
      (y : UnitAddCircle) ≤ ((10 : ℝ) ^ k)⁻¹
  rw [← AddCircle.coe_fract ((10 : ℝ) ^ n * Real.pi), dist_eq_norm,
    ← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm.trans (by
    simpa [Theory.PiDigits.T20.baseTenOrbit, Real.norm_eq_abs] using hclose)

/-- Center of the decimal cylinder for `w`. -/
def decimalCylinderCenter (w : List (Fin 10)) : ℝ :=
  Theory.PiDigits.T27.decimalCylinderLeft w +
    Theory.PiDigits.T27.decimalCylinderLength w.length / 2

/-- Radius of a ball strictly inside the decimal cylinder for `w`. -/
def decimalCylinderInnerRadius (w : List (Fin 10)) : ℝ :=
  Theory.PiDigits.T27.decimalCylinderLength w.length / 4

theorem decimalCylinderInnerRadius_pos (w : List (Fin 10)) :
    0 < decimalCylinderInnerRadius w := by
  exact div_pos (Theory.PiDigits.T27.decimalCylinderLength_pos w.length) (by norm_num)

theorem decimalCylinderInnerRadius_lt_center (w : List (Fin 10)) :
    decimalCylinderInnerRadius w < decimalCylinderCenter w := by
  have hleft := Theory.PiDigits.T27.decimalCylinderLeft_nonneg w
  have hlen := Theory.PiDigits.T27.decimalCylinderLength_pos w.length
  unfold decimalCylinderInnerRadius decimalCylinderCenter
  linarith

theorem decimalCylinderInnerRadius_lt_one_sub_center (w : List (Fin 10)) :
    decimalCylinderInnerRadius w < 1 - decimalCylinderCenter w := by
  have hright := Theory.PiDigits.T27.decimalCylinderRight_le_one w
  have hlen := Theory.PiDigits.T27.decimalCylinderLength_pos w.length
  unfold decimalCylinderInnerRadius decimalCylinderCenter
  linarith

/-- Explicit boundary handling in the converse direction: the open inner
circle ball lies strictly inside the left-closed/right-open decimal cylinder.
Thus no mass at either decimal endpoint is used. -/
theorem circleInnerBall_implies_mem_wordCylinder (w : List (Fin 10)) (x : ℝ)
    (hx : (x : UnitAddCircle) ∈ Metric.ball
      (decimalCylinderCenter w : UnitAddCircle)
      (decimalCylinderInnerRadius w)) :
    Int.fract x ∈ Set.Ico
      ((Theory.PiDigits.T20.wordValue w : ℝ) / (10 : ℝ) ^ w.length)
      (((Theory.PiDigits.T20.wordValue w + 1 : ℕ) : ℝ) /
        (10 : ℝ) ^ w.length) := by
  have habs : |Int.fract x - decimalCylinderCenter w| <
      decimalCylinderInnerRadius w :=
    Theory.PiDigits.T26.abs_fract_sub_lt_of_circle_dist_lt
      (decimalCylinderInnerRadius_lt_center w)
      (decimalCylinderInnerRadius_lt_one_sub_center w) hx
  have hleft : Theory.PiDigits.T27.decimalCylinderLeft w < Int.fract x := by
    rw [abs_lt] at habs
    unfold decimalCylinderCenter decimalCylinderInnerRadius at habs
    linarith [Theory.PiDigits.T27.decimalCylinderLength_pos w.length]
  have hright : Int.fract x <
      Theory.PiDigits.T27.decimalCylinderLeft w +
        Theory.PiDigits.T27.decimalCylinderLength w.length := by
    rw [abs_lt] at habs
    unfold decimalCylinderCenter decimalCylinderInnerRadius at habs
    linarith [Theory.PiDigits.T27.decimalCylinderLength_pos w.length]
  rw [← Theory.PiDigits.T27.decimalCylinder_interval w]
  exact ⟨hleft.le, hright⟩

/-- Membership in the open inner cylinder ball forces the exact block in the
T7 pi stream. -/
theorem piCircleOrbit_mem_innerBall_implies_blockMatch
    (w : List (Fin 10)) (n : ℕ)
    (hn : piCircleOrbit n ∈ Metric.ball
      (decimalCylinderCenter w : UnitAddCircle)
      (decimalCylinderInnerRadius w)) :
    ∀ i : Fin w.length,
      Theory.PiDigits.piDigit (n + i.val) = w.get i := by
  have hcyl := circleInnerBall_implies_mem_wordCylinder w
    ((10 : ℝ) ^ n * Real.pi) hn
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
    w (Int.fract ((10 : ℝ) ^ n * Real.pi)) hcyl
  intro i
  rw [← Theory.PiDigits.T20.decimalDigit_pi (n + i.val)]
  rw [← Theory.PiDigits.T20.decimalDigit_baseTenOrbit
    Real.pi Real.pi_pos.le n i.val]
  exact hdigits i.val i.isLt

/-- Every counted occurrence of a decimal prefix contributes an orbit point
to the corresponding closed ball. -/
theorem blockCount_decimalPrefix_le_closedBallCount
    (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) (k N : ℕ) :
    blockCount Theory.PiDigits.piDigit (decimalPrefix y k) N ≤
      piOrbitSetCount N
        (Metric.closedBall (y : UnitAddCircle) ((10 : ℝ) ^ k)⁻¹) := by
  classical
  unfold blockCount piOrbitSetCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
  apply pi_blockMatch_mem_closedBall y hy k n.val
  intro i
  have hi := hn ⟨i.val, by rw [decimalPrefix_length]; exact i.isLt⟩
  simpa [decimalPrefix] using hi

/-- Every orbit point in the open inner ball contributes an occurrence of
the corresponding word. -/
theorem innerBallCount_le_blockCount (w : List (Fin 10)) (N : ℕ) :
    piOrbitSetCount N
        (Metric.ball (decimalCylinderCenter w : UnitAddCircle)
          (decimalCylinderInnerRadius w)) ≤
      blockCount Theory.PiDigits.piDigit w N := by
  classical
  unfold piOrbitSetCount blockCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
  exact piCircleOrbit_mem_innerBall_implies_blockMatch w n.val hn

/-- Closed-ball empirical mass dominates the real block frequency. -/
theorem ofReal_blockFrequency_le_empirical_closedBall
    (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) (k N : ℕ) (hN : 0 < N) :
    ENNReal.ofReal
        (blockFrequency Theory.PiDigits.piDigit (decimalPrefix y k) N) ≤
      (piEmpiricalMeasure N : Measure UnitAddCircle)
        (Metric.closedBall (y : UnitAddCircle) ((10 : ℝ) ^ k)⁻¹) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [piEmpiricalMeasure_apply_succ M
    (A := Metric.closedBall (y : UnitAddCircle) ((10 : ℝ) ^ k)⁻¹)
    Metric.isClosed_closedBall.measurableSet]
  rw [blockFrequency, ENNReal.ofReal_div_of_pos]
  simp only [ENNReal.ofReal_natCast, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  rw [ENNReal.ofReal_add (Nat.cast_nonneg M) zero_le_one]
  simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  · apply ENNReal.div_le_div_right
    exact_mod_cast blockCount_decimalPrefix_le_closedBallCount y hy k (M + 1)
  · positivity

/-- Open inner-ball empirical mass is bounded by the corresponding real block
frequency. -/
theorem empirical_innerBall_le_ofReal_blockFrequency
    (w : List (Fin 10)) (N : ℕ) (hN : 0 < N) :
    (piEmpiricalMeasure N : Measure UnitAddCircle)
        (Metric.ball (decimalCylinderCenter w : UnitAddCircle)
          (decimalCylinderInnerRadius w)) ≤
      ENNReal.ofReal
        (blockFrequency Theory.PiDigits.piDigit w N) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [piEmpiricalMeasure_apply_succ M
    (A := Metric.ball (decimalCylinderCenter w : UnitAddCircle)
      (decimalCylinderInnerRadius w)) Metric.isOpen_ball.measurableSet]
  rw [blockFrequency, ENNReal.ofReal_div_of_pos]
  simp only [ENNReal.ofReal_natCast, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  rw [ENNReal.ofReal_add (Nat.cast_nonneg M) zero_le_one]
  simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  · apply ENNReal.div_le_div_right
    exact_mod_cast innerBallCount_le_blockCount w (M + 1)
  · positivity

/-- Forward half of the canonical dynamical equivalence. -/
theorem piPositiveLowerBlockDensity_implies_everyEmpiricalClusterFullSupport
    (hA1 : PiPositiveLowerBlockDensity) :
    PiEveryEmpiricalClusterFullSupport := by
  intro μ hcluster
  obtain ⟨φ, hφmono, hμlim⟩ := hcluster.tendsto_subseq
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  apply Set.eq_univ_of_forall
  intro x
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ε, hε, hballU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  let y₀ : ℝ := Int.fract y
  have hy₀ : y₀ ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (lt_min hε zero_lt_one)
    (by norm_num : (10 : ℝ)⁻¹ < 1)
  have hkε : ((10 : ℝ) ^ k)⁻¹ < ε := by
    simpa [inv_pow] using hk.trans_le (min_le_left _ _)
  have hkpos : 0 < k := by
    by_contra hkzero
    have : k = 0 := Nat.eq_zero_of_not_pos hkzero
    subst k
    norm_num at hk
  let w := decimalPrefix y₀ k
  have hwne : w ≠ [] := by
    intro hw
    have hwlen : w.length = 0 := congrArg List.length hw
    simp [w, hkpos.ne'] at hwlen
  let L := liminf (blockFrequency Theory.PiDigits.piDigit w) atTop
  have hL : 0 < L := hA1 w hwne
  let δ := L / 2
  have hδ : 0 < δ := div_pos hL (by norm_num)
  have hδL : δ < L := by
    dsimp [δ]
    linarith
  have hb : atTop.IsBoundedUnder (· ≥ ·)
      (blockFrequency Theory.PiDigits.piDigit w) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall
        (blockFrequency_nonneg Theory.PiDigits.piDigit w))
  have hfreq : ∀ᶠ N : ℕ in atTop,
      δ < blockFrequency Theory.PiDigits.piDigit w N :=
    eventually_lt_of_lt_liminf hδL hb
  have hfreqφ : ∀ᶠ j : ℕ in atTop,
      δ < blockFrequency Theory.PiDigits.piDigit w (φ j) :=
    hφtop.eventually hfreq
  have hφpos : ∀ᶠ j : ℕ in atTop, 0 < φ j :=
    hφtop.eventually (eventually_ge_atTop 1)
  let F : Set UnitAddCircle :=
    Metric.closedBall (y₀ : UnitAddCircle) ((10 : ℝ) ^ k)⁻¹
  have hFU : F ⊆ U := by
    intro z hz
    apply hballU
    change dist z (y : UnitAddCircle) < ε
    rw [← AddCircle.coe_fract y]
    exact lt_of_le_of_lt hz hkε
  have hmass : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal δ ≤
        (piEmpiricalMeasure (φ j) : Measure UnitAddCircle) F := by
    filter_upwards [hfreqφ, hφpos] with j hj hNj
    calc
      ENNReal.ofReal δ ≤ ENNReal.ofReal
          (blockFrequency Theory.PiDigits.piDigit w (φ j)) :=
        ENNReal.ofReal_le_ofReal hj.le
      _ ≤ (piEmpiricalMeasure (φ j) : Measure UnitAddCircle) F := by
        exact ofReal_blockFrequency_le_empirical_closedBall y₀ hy₀ k (φ j) hNj
  have hδlimsup : ENNReal.ofReal δ ≤
      limsup (fun j =>
        (piEmpiricalMeasure (φ j) : Measure UnitAddCircle) F) atTop :=
    le_limsup_of_frequently_le hmass.frequently
  have hport :
      limsup (fun j =>
        (piEmpiricalMeasure (φ j) : Measure UnitAddCircle) F) atTop ≤
        (μ : Measure UnitAddCircle) F :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμlim
      Metric.isClosed_closedBall
  have hμF : 0 < (μ : Measure UnitAddCircle) F :=
    (ENNReal.ofReal_pos.mpr hδ).trans_le (hδlimsup.trans hport)
  exact hμF.trans_le (measure_mono hFU)

/-- Converse half of the canonical dynamical equivalence. -/
theorem everyEmpiricalClusterFullSupport_implies_piPositiveLowerBlockDensity
    (hA8 : PiEveryEmpiricalClusterFullSupport) :
    PiPositiveLowerBlockDensity := by
  intro w hw
  let f : ℕ → ℝ := blockFrequency Theory.PiDigits.piDigit w
  have hfnonneg : ∀ N, 0 ≤ f N :=
    blockFrequency_nonneg Theory.PiDigits.piDigit w
  have hfle : ∀ N, f N ≤ 1 :=
    blockFrequency_le_one Theory.PiDigits.piDigit w
  have hb : atTop.IsBoundedUnder (· ≥ ·) f :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall hfnonneg)
  have hc : atTop.IsCoboundedUnder (· ≥ ·) f :=
    Filter.isCoboundedUnder_ge_of_le atTop hfle
  have hliminf_nonneg : 0 ≤ liminf f atTop :=
    le_liminf_of_le hc (Filter.Eventually.of_forall hfnonneg)
  by_contra hnot
  have hzero : liminf f atTop = 0 :=
    le_antisymm (le_of_not_gt hnot) hliminf_nonneg
  obtain ⟨φ, hfφ, hφtop⟩ := exists_seq_tendsto_liminf hc hb
  rw [hzero] at hfφ
  obtain ⟨μ, ψ, hψmono, hμlim⟩ :=
    CompactSpace.tendsto_subseq
      (fun j => piEmpiricalMeasure (φ j))
  have hψtop : Tendsto ψ atTop atTop := hψmono.tendsto_atTop
  have hindexTop : Tendsto (φ ∘ ψ) atTop atTop := hφtop.comp hψtop
  have hcluster : MapClusterPt μ atTop piEmpiricalMeasure := by
    apply MapClusterPt.of_comp hindexTop
    simpa [Function.comp_def] using hμlim.mapClusterPt
  have hsupport := hA8 μ hcluster
  let G : Set UnitAddCircle :=
    Metric.ball (decimalCylinderCenter w : UnitAddCircle)
      (decimalCylinderInnerRadius w)
  have hcenterG : (decimalCylinderCenter w : UnitAddCircle) ∈ G := by
    exact Metric.mem_ball_self (decimalCylinderInnerRadius_pos w)
  have hcenterSupport :
      (decimalCylinderCenter w : UnitAddCircle) ∈
        (μ : Measure UnitAddCircle).support := by
    rw [hsupport]
    exact Set.mem_univ _
  have hμG : 0 < (μ : Measure UnitAddCircle) G :=
    (Measure.mem_support_iff_forall
      (decimalCylinderCenter w : UnitAddCircle)).mp hcenterSupport G
        (Metric.isOpen_ball.mem_nhds hcenterG)
  have hport :
      (μ : Measure UnitAddCircle) G ≤
        liminf (fun j =>
          (piEmpiricalMeasure (φ (ψ j)) : Measure UnitAddCircle) G) atTop := by
    simpa [Function.comp_def] using
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμlim Metric.isOpen_ball
  have hfsub : Tendsto (fun j => f (φ (ψ j))) atTop (nhds 0) := by
    simpa [Function.comp_def] using hfφ.comp hψtop
  have hindexPos : ∀ᶠ j : ℕ in atTop, 0 < φ (ψ j) :=
    hindexTop.eventually (eventually_ge_atTop 1)
  have hmeasureLe : ∀ᶠ j : ℕ in atTop,
      (piEmpiricalMeasure (φ (ψ j)) : Measure UnitAddCircle) G ≤
        ENNReal.ofReal (f (φ (ψ j))) := by
    filter_upwards [hindexPos] with j hj
    exact empirical_innerBall_le_ofReal_blockFrequency w (φ (ψ j)) hj
  have hliminfLe :
      liminf (fun j =>
        (piEmpiricalMeasure (φ (ψ j)) : Measure UnitAddCircle) G) atTop ≤
        liminf (fun j => ENNReal.ofReal (f (φ (ψ j)))) atTop :=
    liminf_le_liminf hmeasureLe
  have hofRealTend :
      Tendsto (fun j => ENNReal.ofReal (f (φ (ψ j)))) atTop (nhds 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hfsub
  have hliminfZero :
      liminf (fun j => ENNReal.ofReal (f (φ (ψ j)))) atTop = 0 :=
    hofRealTend.liminf_eq
  have hμGzero : (μ : Measure UnitAddCircle) G ≤ 0 :=
    hport.trans (hliminfLe.trans_eq hliminfZero)
  exact (not_le_of_gt hμG) hμGzero

/-- Exact equivalence between A1 and A8, with A1 and A8 exposed as named
definitions carrying the source quantifiers. -/
theorem piPositiveLowerBlockDensity_iff_everyEmpiricalClusterFullSupport :
    PiPositiveLowerBlockDensity ↔ PiEveryEmpiricalClusterFullSupport :=
  ⟨piPositiveLowerBlockDensity_implies_everyEmpiricalClusterFullSupport,
    everyEmpiricalClusterFullSupport_implies_piPositiveLowerBlockDensity⟩

/-- A1 with the source's explicit `k ≥ 1` and `w ∈ D^k` quantifiers. -/
theorem piPositiveLowerBlockDensity_iff_A1_quantifiers :
    PiPositiveLowerBlockDensity ↔
      ∀ k : ℕ, 1 ≤ k → ∀ w : Fin k → Fin 10,
        0 < liminf
          (blockFrequency Theory.PiDigits.piDigit (List.ofFn w)) atTop := by
  constructor
  · intro h k hk w
    apply h (List.ofFn w)
    simp [Nat.ne_of_gt hk]
  · intro h w hw
    have hk : 1 ≤ w.length := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      exact hw (List.length_eq_zero_iff.mp hz)
    simpa using h w.length hk (fun i : Fin w.length => w.get i)

/-- A8 with the source's universal weak-* accumulation-point quantifiers. -/
theorem everyEmpiricalClusterFullSupport_iff_A8_quantifiers :
    PiEveryEmpiricalClusterFullSupport ↔
      ∀ μ : ProbabilityMeasure UnitAddCircle,
        MapClusterPt μ atTop piEmpiricalMeasure →
          (μ : Measure UnitAddCircle).support = Set.univ :=
  Iff.rfl

end Theory.PiDigits.PositiveLowerBlockDensity

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.exists_block_occurrence_of_pos_liminf
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.piPositiveLowerBlockDensity_implies_T7V1
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.piCircleOrbit_eq_fract
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.pi_blockMatch_mem_closedBall
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.circleInnerBall_implies_mem_wordCylinder
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.piPositiveLowerBlockDensity_iff_everyEmpiricalClusterFullSupport
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.piPositiveLowerBlockDensity_iff_A1_quantifiers
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.everyEmpiricalClusterFullSupport_iff_A8_quantifiers
