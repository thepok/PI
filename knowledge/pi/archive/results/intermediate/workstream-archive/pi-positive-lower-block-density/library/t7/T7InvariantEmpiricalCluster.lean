import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiPositiveLowerBlockDensity.T6T6FixedFrequencyLowerDensityObstruction
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# T7: an invariant resonant empirical cluster forced by failure of C1

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only a necessary consequence of literal failure of the
canonical positive lower block-density statement. It makes no unconditional
claim about pi or C1.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace Theory.PiDigits.PositiveLowerBlockDensity.T7

open Theory.PiDigits.PositiveLowerBlockDensity

/-- Multiplication by ten on `R/Z`. -/
def timesTen (x : UnitAddCircle) : UnitAddCircle := (10 : ℕ) • x

theorem timesTen_continuous : Continuous timesTen := by
  simpa [timesTen] using (continuous_nsmul 10 :
    Continuous fun x : UnitAddCircle => (10 : ℕ) • x)

/-- Push-forward by multiplication by ten. -/
def timesTenMap (ν : ProbabilityMeasure UnitAddCircle) :
    ProbabilityMeasure UnitAddCircle :=
  ν.map timesTen_continuous.measurable.aemeasurable

/-- The Fourier coefficient convention matching T6's exponential sums. -/
def measureFourierCoeff (ν : ProbabilityMeasure UnitAddCircle) (h : ℤ) : ℂ :=
  ∫ x, fourier h x ∂(ν : Measure UnitAddCircle)

/-- T1's explicit open ball strictly inside the decimal cylinder of `w`. -/
def decimalInnerSet (w : List (Fin 10)) : Set UnitAddCircle :=
  Metric.ball (decimalCylinderCenter w : UnitAddCircle)
    (decimalCylinderInnerRadius w)

theorem decimalInnerSet_isOpen (w : List (Fin 10)) :
    IsOpen (decimalInnerSet w) := by
  exact Metric.isOpen_ball

theorem decimalInnerSet_nonempty (w : List (Fin 10)) :
    (decimalInnerSet w).Nonempty := by
  exact ⟨decimalCylinderCenter w,
    Metric.mem_ball_self (decimalCylinderInnerRadius_pos w)⟩

theorem decimalInnerSet_subset_wordCylinder (w : List (Fin 10)) :
    ∀ x : ℝ, (x : UnitAddCircle) ∈ decimalInnerSet w →
      Int.fract x ∈ Set.Ico
        ((Theory.PiDigits.T20.wordValue w : ℝ) / (10 : ℝ) ^ w.length)
        (((Theory.PiDigits.T20.wordValue w + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ w.length) := by
  intro x hx
  exact circleInnerBall_implies_mem_wordCylinder w x hx

/-- Recursively select simultaneous T6 witnesses, requesting each new cutoff
past both the preceding cutoff and the next reciprocal scale. -/
def selectedCutoffs (f r : ℕ → ℝ) (eta : ℝ)
    (hwitness : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ,
      m ≤ N ∧ f N ≤ 1 / (m : ℝ) ∧ eta ≤ r N) : ℕ → ℕ
  | 0 => Classical.choose (hwitness 1 (by omega))
  | n + 1 =>
      Classical.choose
        (hwitness (max (n + 2) (selectedCutoffs f r eta hwitness n + 1))
          (by omega))

theorem selectedCutoffs_strictMono (f r : ℕ → ℝ) (eta : ℝ)
    (hwitness : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ,
      m ≤ N ∧ f N ≤ 1 / (m : ℝ) ∧ eta ≤ r N) :
    StrictMono (selectedCutoffs f r eta hwitness) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hspec := Classical.choose_spec
    (hwitness (max (n + 2) (selectedCutoffs f r eta hwitness n + 1))
      (by omega))
  exact Nat.lt_of_succ_le ((le_max_right _ _).trans hspec.1)

theorem selectedCutoffs_frequency_bound (f r : ℕ → ℝ) (eta : ℝ)
    (hwitness : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ,
      m ≤ N ∧ f N ≤ 1 / (m : ℝ) ∧ eta ≤ r N) (n : ℕ) :
    f (selectedCutoffs f r eta hwitness n) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  cases n with
  | zero =>
      exact (Classical.choose_spec (hwitness 1 (by omega))).2.1
  | succ n =>
      let m := max (n + 2) (selectedCutoffs f r eta hwitness n + 1)
      have hspec := Classical.choose_spec (hwitness m (by dsimp [m]; omega))
      exact hspec.2.1.trans (one_div_le_one_div_of_le (by positivity) (by
        exact_mod_cast (le_max_left (n + 2)
          (selectedCutoffs f r eta hwitness n + 1))))

theorem selectedCutoffs_resonance (f r : ℕ → ℝ) (eta : ℝ)
    (hwitness : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ,
      m ≤ N ∧ f N ≤ 1 / (m : ℝ) ∧ eta ≤ r N) (n : ℕ) :
    eta ≤ r (selectedCutoffs f r eta hwitness n) := by
  cases n with
  | zero =>
      exact (Classical.choose_spec (hwitness 1 (by omega))).2.2
  | succ n =>
      exact (Classical.choose_spec
        (hwitness (max (n + 2) (selectedCutoffs f r eta hwitness n + 1))
          (by omega))).2.2

theorem selectedCutoffs_positive (f r : ℕ → ℝ) (eta : ℝ)
    (hwitness : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ,
      m ≤ N ∧ f N ≤ 1 / (m : ℝ) ∧ eta ≤ r N) (n : ℕ) :
    0 < selectedCutoffs f r eta hwitness n := by
  cases n with
  | zero =>
      exact lt_of_lt_of_le Nat.zero_lt_one
        (Classical.choose_spec (hwitness 1 (by omega))).1
  | succ n =>
      have hspec := Classical.choose_spec
        (hwitness (max (n + 2) (selectedCutoffs f r eta hwitness n + 1))
          (by omega))
      exact lt_of_lt_of_le (by omega : 0 <
        max (n + 2) (selectedCutoffs f r eta hwitness n + 1)) hspec.1

/-- Integration against a positive-length empirical measure is the normalized
finite orbit sum. -/
theorem integral_piEmpiricalMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (N : ℕ) (hN : 0 < N)
    (f : C(UnitAddCircle, E)) :
    ∫ x, f x ∂(piEmpiricalMeasure N : Measure UnitAddCircle) =
      (N : ℝ)⁻¹ • ∑ j ∈ range N, f (piCircleOrbit j) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [piEmpiricalMeasure]
  rw [ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map
    (measurable_of_finite
      (fun n : Fin (M + 1) => piCircleOrbit n.val)).aemeasurable
    f.continuous.aestronglyMeasurable]
  change (∫ x : Fin (M + 1), f (piCircleOrbit x.val)
    ∂ProbabilityTheory.uniformOn Set.univ) = _
  have huniform :
      ProbabilityTheory.uniformOn (Set.univ : Set (Fin (M + 1))) =
        ((Fintype.card (Fin (M + 1)) : ENNReal)⁻¹ • Measure.count) := by
    ext A hA
    rw [ProbabilityTheory.uniformOn_univ]
    simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
  rw [huniform]
  simp only [Fintype.card_fin,
    MeasureTheory.integral_smul_measure, MeasureTheory.integral_count,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  simpa only [Nat.succ_eq_add_one] using
    (Fin.sum_univ_eq_sum_range (fun j => f (piCircleOrbit j)) (M + 1))

theorem fourier_piCircleOrbit_eq_phase (h : ℤ) (j : ℕ) :
    fourier h (piCircleOrbit j) =
      Theory.PiDigits.T27.phase h
        (Theory.PiDigits.T27.piFractionalOrbit j) := by
  rw [piCircleOrbit_eq_fract]
  simp only [Theory.PiDigits.T27.piFractionalOrbit,
    Theory.PiDigits.T27.phase, fourier_coe_apply]
  norm_num

theorem norm_measureFourierCoeff_piEmpiricalMeasure (N : ℕ) (hN : 0 < N)
    (h : ℤ) :
    ‖measureFourierCoeff (piEmpiricalMeasure N) h‖ =
      ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) := by
  rw [measureFourierCoeff, integral_piEmpiricalMeasure N hN (fourier h)]
  simp_rw [fourier_piCircleOrbit_eq_phase]
  rw [Theory.PiDigits.T27.exponentialSum]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv]
  rw [abs_of_nonneg (Nat.cast_nonneg N)]
  ring

theorem piCircleOrbit_succ (n : ℕ) :
    piCircleOrbit (n + 1) = timesTen (piCircleOrbit n) := by
  unfold piCircleOrbit timesTen
  rw [← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul, pow_succ]
  ring

/-- The endpoint identity behind invariance of every empirical cluster. -/
theorem integral_timesTenMap_piEmpiricalMeasure_sub (N : ℕ) (hN : 0 < N)
    (f : UnitAddCircle →ᵇ ℝ) :
    (∫ x, f x ∂(timesTenMap (piEmpiricalMeasure N) : Measure UnitAddCircle)) -
        ∫ x, f x ∂(piEmpiricalMeasure N : Measure UnitAddCircle) =
      (N : ℝ)⁻¹ * (f (piCircleOrbit N) - f (piCircleOrbit 0)) := by
  rw [timesTenMap, ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map
    timesTen_continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  have hfirst := integral_piEmpiricalMeasure N hN
    (f.toContinuousMap.comp ⟨timesTen, timesTen_continuous⟩)
  change (∫ x, f (timesTen x) ∂(piEmpiricalMeasure N : Measure UnitAddCircle)) =
    (N : ℝ)⁻¹ • ∑ j ∈ range N, f (timesTen (piCircleOrbit j)) at hfirst
  have hsecond := integral_piEmpiricalMeasure N hN f.toContinuousMap
  change (∫ x, f x ∂(piEmpiricalMeasure N : Measure UnitAddCircle)) =
    (N : ℝ)⁻¹ • ∑ j ∈ range N, f (piCircleOrbit j) at hsecond
  rw [hfirst, hsecond]
  simp_rw [← piCircleOrbit_succ]
  rw [← smul_sub]
  change (N : ℝ)⁻¹ *
      ((∑ j ∈ range N, f (piCircleOrbit (j + 1))) -
        ∑ j ∈ range N, f (piCircleOrbit j)) = _
  congr 1
  have hfront := Finset.sum_range_succ' (fun j => f (piCircleOrbit j)) N
  have hend := Finset.sum_range_succ (fun j => f (piCircleOrbit j)) N
  linarith

/-- Every weak limit along cutoffs tending to infinity is invariant under
multiplication by ten. -/
theorem empiricalCluster_invariant (cutoffs : ℕ → ℕ)
    (hcutoffs : Tendsto cutoffs atTop atTop)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν)) :
    timesTenMap ν = ν := by
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < cutoffs n :=
    hcutoffs.eventually (eventually_ge_atTop 1)
  have hinv : Tendsto (fun n => ((cutoffs n : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hcutoffs).inv_tendsto_atTop
  have hmapped : Tendsto
      (fun n => timesTenMap (piEmpiricalMeasure (cutoffs n))) atTop (𝓝 ν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hbounded : atTop.IsBoundedUnder (· ≤ ·)
        (norm ∘ fun n => f (piCircleOrbit (cutoffs n)) - f (piCircleOrbit 0)) :=
      Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => by
        dsimp only [Function.comp_apply]
        calc
          ‖f (piCircleOrbit (cutoffs n)) - f (piCircleOrbit 0)‖ ≤
              ‖f (piCircleOrbit (cutoffs n))‖ + ‖f (piCircleOrbit 0)‖ :=
            norm_sub_le _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add
            (f.norm_coe_le_norm _) (f.norm_coe_le_norm _))
    have hproduct : Tendsto (fun n =>
        ((cutoffs n : ℝ))⁻¹ *
          (f (piCircleOrbit (cutoffs n)) - f (piCircleOrbit 0)))
        atTop (𝓝 0) :=
      hinv.zero_mul_isBoundedUnder_le hbounded
    have hdifference : Tendsto (fun n =>
        (∫ x, f x ∂(timesTenMap (piEmpiricalMeasure (cutoffs n)) :
          Measure UnitAddCircle)) -
          ∫ x, f x ∂(piEmpiricalMeasure (cutoffs n) :
            Measure UnitAddCircle)) atTop (𝓝 0) := by
      apply hproduct.congr'
      filter_upwards [hpositive] with n hn
      exact (integral_timesTenMap_piEmpiricalMeasure_sub (cutoffs n) hn f).symm
    have hbase :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hν f
    convert hdifference.add hbase using 1 <;> ring
  have hmapped' : Tendsto
      (fun n => timesTenMap (piEmpiricalMeasure (cutoffs n))) atTop
      (𝓝 (timesTenMap ν)) := by
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => piEmpiricalMeasure (cutoffs n)) ν hν timesTen_continuous
  exact tendsto_nhds_unique hmapped' hmapped

theorem zero_mass_decimalInnerSet_of_tendsto (w : List (Fin 10))
    (cutoffs : ℕ → ℕ) (hpositive : ∀ n, 0 < cutoffs n)
    (hfrequency : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit w (cutoffs n))
      atTop (𝓝 0))
    (ν : ProbabilityMeasure UnitAddCircle)
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν)) :
    (ν : Measure UnitAddCircle) (decimalInnerSet w) = 0 := by
  have hofReal : Tendsto (fun n => ENNReal.ofReal
      (blockFrequency Theory.PiDigits.piDigit w (cutoffs n)))
      atTop (𝓝 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hfrequency
  have hport : (ν : Measure UnitAddCircle) (decimalInnerSet w) ≤
      liminf (fun n =>
        (piEmpiricalMeasure (cutoffs n) : Measure UnitAddCircle)
          (decimalInnerSet w)) atTop :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν
      (decimalInnerSet_isOpen w)
  have hliminfLe : liminf (fun n =>
      (piEmpiricalMeasure (cutoffs n) : Measure UnitAddCircle)
        (decimalInnerSet w)) atTop ≤
      liminf (fun n => ENNReal.ofReal
        (blockFrequency Theory.PiDigits.piDigit w (cutoffs n))) atTop :=
    liminf_le_liminf (Eventually.of_forall fun n => by
      simpa [decimalInnerSet] using
        empirical_innerBall_le_ofReal_blockFrequency w (cutoffs n) (hpositive n))
  rw [hofReal.liminf_eq] at hliminfLe
  exact bot_unique (hport.trans hliminfLe)

theorem measureFourierCoeff_tendsto {cutoffs : ℕ → ℕ}
    {ν : ProbabilityMeasure UnitAddCircle}
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν))
    (h : ℤ) :
    Tendsto (fun n => measureFourierCoeff (piEmpiricalMeasure (cutoffs n)) h)
      atTop (𝓝 (measureFourierCoeff ν h)) := by
  let χ : UnitAddCircle →ᵇ ℂ :=
    BoundedContinuousFunction.mkOfCompact (fourier h)
  simpa [measureFourierCoeff, χ] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hν χ

theorem measureFourierCoeff_lower_bound_of_tendsto
    {cutoffs : ℕ → ℕ} {ν : ProbabilityMeasure UnitAddCircle}
    (hν : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν))
    (h : ℤ) (eta : ℝ)
    (hlower : ∀ n, eta ≤
      ‖measureFourierCoeff (piEmpiricalMeasure (cutoffs n)) h‖) :
    eta ≤ ‖measureFourierCoeff ν h‖ := by
  exact ge_of_tendsto' (measureFourierCoeff_tendsto hν h).norm hlower

theorem fourier_timesTen (h : ℤ) (x : UnitAddCircle) :
    fourier h (timesTen x) = fourier (10 * h) x := by
  unfold timesTen
  simp only [fourier_apply, ← natCast_zsmul, ← mul_smul]
  congr 2
  norm_num
  exact congrArg (fun z : ℤ => z • x) (mul_comm h 10)

theorem invariant_measureFourierCoeff_step (ν : ProbabilityMeasure UnitAddCircle)
    (hinvariant : timesTenMap ν = ν) (h : ℤ) :
    measureFourierCoeff ν (10 * h) = measureFourierCoeff ν h := by
  unfold measureFourierCoeff
  calc
    (∫ x, fourier (10 * h) x ∂(ν : Measure UnitAddCircle)) =
        ∫ x, fourier h (timesTen x) ∂(ν : Measure UnitAddCircle) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (fourier_timesTen h x).symm
    _ = ∫ x, fourier h x ∂(timesTenMap ν : Measure UnitAddCircle) := by
      rw [timesTenMap, ProbabilityMeasure.toMeasure_map]
      exact (MeasureTheory.integral_map
        timesTen_continuous.measurable.aemeasurable
        (fourier h).continuous.aestronglyMeasurable).symm
    _ = ∫ x, fourier h x ∂(ν : Measure UnitAddCircle) := by
      rw [hinvariant]

theorem invariant_measureFourierCoeff_pow (ν : ProbabilityMeasure UnitAddCircle)
    (hinvariant : timesTenMap ν = ν) (h : ℤ) (r : ℕ) :
    measureFourierCoeff ν ((10 : ℤ) ^ r * h) = measureFourierCoeff ν h := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        measureFourierCoeff ν ((10 : ℤ) ^ (r + 1) * h) =
            measureFourierCoeff ν (10 * ((10 : ℤ) ^ r * h)) := by
          apply congrArg (measureFourierCoeff ν)
          rw [pow_succ]
          ring
        _ = measureFourierCoeff ν ((10 : ℤ) ^ r * h) :=
          invariant_measureFourierCoeff_step ν hinvariant _
        _ = measureFourierCoeff ν h := ih

/-- Necessary-only T7 conclusion. Failure of canonical C1 concentrates T6's
simultaneous block and Fourier witnesses into one invariant empirical cluster.
No failure (or truth) of C1 is asserted. -/
theorem not_piPositiveLowerBlockDensity_implies_invariant_resonant_cluster
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ w : List (Fin 10), w.length = k ∧
      ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ (2 * k) ∧
        ∃ eta : ℝ, eta = (8 * (10 : ℝ) ^ (2 * k))⁻¹ ∧ 0 < eta ∧
          ∃ cutoffs : ℕ → ℕ, StrictMono cutoffs ∧
            (∀ n : ℕ,
              blockFrequency Theory.PiDigits.piDigit w (cutoffs n) ≤
                1 / ((n + 1 : ℕ) : ℝ) ∧
              eta ≤ ‖∑ j ∈ range (cutoffs n),
                Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
                    ((Theory.PiDigits.T27.piFractionalOrbit j : ℝ) : ℂ))‖ /
                  (cutoffs n : ℝ)) ∧
            ∃ ν : ProbabilityMeasure UnitAddCircle,
              Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν) ∧
              MapClusterPt ν atTop piEmpiricalMeasure ∧
              timesTenMap ν = ν ∧
              IsOpen (decimalInnerSet w) ∧
              (decimalInnerSet w).Nonempty ∧
              (∀ x : ℝ, (x : UnitAddCircle) ∈ decimalInnerSet w →
                Int.fract x ∈ Set.Ico
                  ((Theory.PiDigits.T20.wordValue w : ℝ) /
                    (10 : ℝ) ^ w.length)
                  (((Theory.PiDigits.T20.wordValue w + 1 : ℕ) : ℝ) /
                    (10 : ℝ) ^ w.length)) ∧
              (ν : Measure UnitAddCircle) (decimalInnerSet w) = 0 ∧
              eta ≤ ‖measureFourierCoeff ν h‖ ∧
              ∀ r : ℕ,
                measureFourierCoeff ν ((10 : ℤ) ^ r * h) =
                  measureFourierCoeff ν h := by
  obtain ⟨k, hk, w, hw, h, hh0, hhbound, heta, hwitness⟩ :=
    T6.not_piPositiveLowerBlockDensity_implies_fixed_frequency_obstruction hnot
  let eta : ℝ := (8 * (10 : ℝ) ^ (2 * k))⁻¹
  let f : ℕ → ℝ := fun N =>
    blockFrequency Theory.PiDigits.piDigit w N
  let resonance : ℕ → ℝ := fun N =>
    ‖Theory.PiDigits.T27.exponentialSum
      Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ)
  have hwitness' : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ,
      m ≤ N ∧ f N ≤ 1 / (m : ℝ) ∧ eta ≤ resonance N := by
    simpa [f, resonance, eta, Theory.PiDigits.T27.exponentialSum,
      Theory.PiDigits.T27.phase] using hwitness
  let baseCutoffs := selectedCutoffs f resonance eta hwitness'
  have hbaseStrict : StrictMono baseCutoffs := by
    exact selectedCutoffs_strictMono f resonance eta hwitness'
  have hbaseFrequency (n : ℕ) :
      f (baseCutoffs n) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    exact selectedCutoffs_frequency_bound f resonance eta hwitness' n
  have hbaseResonance (n : ℕ) :
      eta ≤ resonance (baseCutoffs n) := by
    exact selectedCutoffs_resonance f resonance eta hwitness' n
  have hbasePositive (n : ℕ) : 0 < baseCutoffs n := by
    exact selectedCutoffs_positive f resonance eta hwitness' n
  obtain ⟨ν, ψ, hψstrict, hν⟩ :=
    CompactSpace.tendsto_subseq
      (fun n => piEmpiricalMeasure (baseCutoffs n))
  let cutoffs : ℕ → ℕ := baseCutoffs ∘ ψ
  have hcutoffsStrict : StrictMono cutoffs :=
    hbaseStrict.comp hψstrict
  have hcutoffsTop : Tendsto cutoffs atTop atTop :=
    hcutoffsStrict.tendsto_atTop
  have hfrequencyBound (n : ℕ) :
      f (cutoffs n) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    calc
      f (cutoffs n) ≤ 1 / ((ψ n + 1 : ℕ) : ℝ) := by
        simpa [cutoffs, Function.comp_def] using hbaseFrequency (ψ n)
      _ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (StrictMono.id_le hψstrict n) 1
  have hfrequencyTendsto : Tendsto (fun n => f (cutoffs n)) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => by
        exact blockFrequency_nonneg Theory.PiDigits.piDigit w (cutoffs n)
    · exact Eventually.of_forall hfrequencyBound
    · simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have hresonance (n : ℕ) : eta ≤ resonance (cutoffs n) := by
    simpa [cutoffs, Function.comp_def] using hbaseResonance (ψ n)
  have hpositive (n : ℕ) : 0 < cutoffs n := by
    simpa [cutoffs, Function.comp_def] using hbasePositive (ψ n)
  have hν' : Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 ν) := by
    simpa [cutoffs, Function.comp_def] using hν
  have hcluster : MapClusterPt ν atTop piEmpiricalMeasure := by
    apply MapClusterPt.of_comp hcutoffsTop
    exact hν'.mapClusterPt
  have hinvariant : timesTenMap ν = ν :=
    empiricalCluster_invariant cutoffs hcutoffsTop ν hν'
  have hzero : (ν : Measure UnitAddCircle) (decimalInnerSet w) = 0 := by
    apply zero_mass_decimalInnerSet_of_tendsto w cutoffs hpositive
    · simpa [f] using hfrequencyTendsto
    · exact hν'
  have hcoeffEach (n : ℕ) : eta ≤
      ‖measureFourierCoeff (piEmpiricalMeasure (cutoffs n)) h‖ := by
    rw [norm_measureFourierCoeff_piEmpiricalMeasure (cutoffs n) (hpositive n) h]
    exact hresonance n
  have hcoeff : eta ≤ ‖measureFourierCoeff ν h‖ :=
    measureFourierCoeff_lower_bound_of_tendsto hν' h eta hcoeffEach
  refine ⟨k, hk, w, hw, h, hh0, hhbound, eta, rfl, ?_, cutoffs,
    hcutoffsStrict, ?_, ν, hν', hcluster, hinvariant,
    decimalInnerSet_isOpen w, decimalInnerSet_nonempty w,
    decimalInnerSet_subset_wordCylinder w, hzero, hcoeff, ?_⟩
  · simpa [eta] using heta
  · intro n
    refine ⟨?_, ?_⟩
    · simpa [f] using hfrequencyBound n
    · simpa [resonance, Theory.PiDigits.T27.exponentialSum,
        Theory.PiDigits.T27.phase] using hresonance n
  · exact invariant_measureFourierCoeff_pow ν hinvariant h

end Theory.PiDigits.PositiveLowerBlockDensity.T7

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.selectedCutoffs_strictMono
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.integral_piEmpiricalMeasure
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.norm_measureFourierCoeff_piEmpiricalMeasure
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.empiricalCluster_invariant
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.zero_mass_decimalInnerSet_of_tendsto
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.measureFourierCoeff_lower_bound_of_tendsto
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.invariant_measureFourierCoeff_pow
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T7.not_piPositiveLowerBlockDensity_implies_invariant_resonant_cluster
