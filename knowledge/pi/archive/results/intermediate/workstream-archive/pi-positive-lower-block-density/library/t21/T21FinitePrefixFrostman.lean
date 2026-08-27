import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiPositiveLowerBlockDensity.T11T11HausdorffDimensionDefect

/-!
# T21: finite-prefix Frostman criterion for canonical C1

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module gives a conditional sufficient criterion for canonical C1. It does
not assert that the decimal orbit of pi satisfies the criterion.
-/

noncomputable section

open Filter Set Topology
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T21

open Theory.PiDigits.PositiveLowerBlockDensity

/-- Uniform finite-prefix Frostman anti-concentration for the exact empirical
measures from T1. The constants `C` and `N0` may depend on `s`, but are uniform
in the prefix length `N`, center `x`, and radius `r`. -/
def PiUniformFinitePrefixFrostman : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N →
        ∀ x : UnitAddCircle, ∀ r : ℝ, 0 < r → r ≤ 1 →
          (piEmpiricalMeasure N : Measure UnitAddCircle)
              (Metric.closedBall x r) ≤
            ENNReal.ofReal (C * r ^ s + C / (N : ℝ))

/-- The finite-prefix criterion with every dependency and uniformity
quantifier displayed for direct inspection. -/
theorem piUniformFinitePrefixFrostman_iff_quantifiers :
    PiUniformFinitePrefixFrostman ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ,
          ∀ N : ℕ, N0 ≤ N →
            ∀ x : UnitAddCircle, ∀ r : ℝ, 0 < r → r ≤ 1 →
              (piEmpiricalMeasure N : Measure UnitAddCircle)
                  (Metric.closedBall x r) ≤
                ENNReal.ofReal (C * r ^ s + C / (N : ℝ)) :=
  Iff.rfl

/-- A fixed finite-prefix Frostman estimate passes to every weak empirical
cluster. The `C / N` term vanishes along the cluster subsequence. -/
theorem finitePrefixFrostman_passes_to_cluster
    (s C : ℝ) (hs : 0 < s) (hC : 1 ≤ C) (N0 : ℕ)
    (hfinite : ∀ N : ℕ, N0 ≤ N →
      ∀ x : UnitAddCircle, ∀ r : ℝ, 0 < r → r ≤ 1 →
        (piEmpiricalMeasure N : Measure UnitAddCircle)
            (Metric.closedBall x r) ≤
          ENNReal.ofReal (C * r ^ s + C / (N : ℝ)))
    (ν : ProbabilityMeasure UnitAddCircle)
    (hcluster : MapClusterPt ν atTop piEmpiricalMeasure) :
    ∀ x : UnitAddCircle, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (ν : Measure UnitAddCircle) (Metric.closedBall x r) ≤
        ENNReal.ofReal (C * r ^ s) := by
  obtain ⟨φ, hφmono, hν⟩ := hcluster.tendsto_subseq
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hlarge : ∀ᶠ j : ℕ in atTop, N0 ≤ φ j :=
    hφtop.eventually (eventually_ge_atTop N0)
  have herror : Tendsto (fun j : ℕ => C / (φ j : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C).comp hφtop
  intro x r hr hrle
  have hopen (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1) :
      (ν : Measure UnitAddCircle) (Metric.ball x R) ≤
        ENNReal.ofReal (C * R ^ s) := by
    have hemass : ∀ᶠ j : ℕ in atTop,
        (piEmpiricalMeasure (φ j) : Measure UnitAddCircle)
            (Metric.ball x R) ≤
          ENNReal.ofReal (C * R ^ s + C / (φ j : ℝ)) := by
      filter_upwards [hlarge] with j hj
      exact (measure_mono Metric.ball_subset_closedBall).trans
        (hfinite (φ j) hj x R hR0 hR1)
    have hport :
        (ν : Measure UnitAddCircle) (Metric.ball x R) ≤
          liminf (fun j =>
            (piEmpiricalMeasure (φ j) : Measure UnitAddCircle)
              (Metric.ball x R)) atTop := by
      simpa [Function.comp_def] using
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto
          hν Metric.isOpen_ball
    have hrhsReal :
        Tendsto (fun j : ℕ => C * R ^ s + C / (φ j : ℝ)) atTop
          (nhds (C * R ^ s)) := by
      simpa using tendsto_const_nhds.add herror
    have hrhs :
        Tendsto
          (fun j : ℕ => ENNReal.ofReal
            (C * R ^ s + C / (φ j : ℝ))) atTop
          (nhds (ENNReal.ofReal (C * R ^ s))) :=
      ENNReal.tendsto_ofReal hrhsReal
    calc
      (ν : Measure UnitAddCircle) (Metric.ball x R) ≤
          liminf (fun j =>
            (piEmpiricalMeasure (φ j) : Measure UnitAddCircle)
              (Metric.ball x R)) atTop := hport
      _ ≤ liminf (fun j => ENNReal.ofReal
          (C * R ^ s + C / (φ j : ℝ))) atTop :=
        liminf_le_liminf hemass
      _ = ENNReal.ofReal (C * R ^ s) := hrhs.liminf_eq
  by_cases hr1 : r = 1
  · subst r
    calc
      (ν : Measure UnitAddCircle) (Metric.closedBall x 1) ≤
          (ν : Measure UnitAddCircle) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal C := ENNReal.one_le_ofReal.mpr hC
      _ = ENNReal.ofReal (C * (1 : ℝ) ^ s) := by simp
  · have hrlt : r < 1 := lt_of_le_of_ne hrle hr1
    let R : ℕ → ℝ := fun n => r + (1 - r) / ((n : ℝ) + 1)
    have hRgt (n : ℕ) : r < R n := by
      have hq : 0 < (1 - r) / ((n : ℝ) + 1) := by positivity
      simpa [R] using lt_add_of_pos_right r hq
    have hRle (n : ℕ) : R n ≤ 1 := by
      have hd : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
      have hq : (1 - r) / ((n : ℝ) + 1) ≤ 1 - r :=
        div_le_self (sub_nonneg.mpr hrle) hd
      dsimp [R]
      linarith
    have hRpos (n : ℕ) : 0 < R n := hr.trans (hRgt n)
    have hone :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop
          (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hRlim : Tendsto R atTop (nhds r) := by
      simpa [R, div_eq_mul_inv] using
        tendsto_const_nhds.add (tendsto_const_nhds.mul hone)
    have hpow : Tendsto (fun n => R n ^ s) atTop (nhds (r ^ s)) :=
      ((Real.continuous_rpow_const hs.le).tendsto r).comp hRlim
    have hboundLim :
        Tendsto (fun n => ENNReal.ofReal (C * R n ^ s)) atTop
          (nhds (ENNReal.ofReal (C * r ^ s))) :=
      ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hpow)
    have hbound (n : ℕ) :
        (ν : Measure UnitAddCircle) (Metric.closedBall x r) ≤
          ENNReal.ofReal (C * R n ^ s) :=
      (measure_mono (Metric.closedBall_subset_ball (hRgt n))).trans
        (hopen (R n) (hRpos n) (hRle n))
    exact ge_of_tendsto' hboundLim hbound

/-- A local closed-ball Frostman bound implies absolute continuity with
respect to the corresponding Hausdorff measure. -/
theorem absolutelyContinuous_hausdorffMeasure_of_closedBall_le
    (μ : Measure UnitAddCircle) (s C : ℝ) (hs : 0 < s) (hC : 1 ≤ C)
    (hball : ∀ x : UnitAddCircle, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r ^ s)) :
    μ ≪ μH[s] := by
  let c : ENNReal := ENNReal.ofReal C
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hctop : c ≠ ∞ := by simp [c]
  have hczero : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hCpos
  have hsmall : ∀ A : Set UnitAddCircle,
      Metric.ediam A ≤ ENNReal.ofReal (1 / 2 : ℝ) →
        μ A ≤ c * Metric.ediam A ^ s := by
    intro A hA
    rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hAtop : Metric.ediam A ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
      have hdiam : Metric.diam A ≤ (1 / 2 : ℝ) :=
        ENNReal.toReal_le_of_le_ofReal (by norm_num) hA
      let q : ℕ → ℝ := fun n =>
        Metric.diam A + (1 / 2 : ℝ) / ((n : ℝ) + 1)
      have hqpos (n : ℕ) : 0 < q n := by
        dsimp [q]
        have hdiam0 : 0 ≤ Metric.diam A := Metric.diam_nonneg
        positivity
      have hqle (n : ℕ) : q n ≤ 1 := by
        have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
        have hhalf : (1 / 2 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 2 :=
          div_le_self (by norm_num) hden
        dsimp [q]
        linarith
      have hone :
          Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop
            (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hqReal : Tendsto q atTop (nhds (Metric.diam A)) := by
        simpa [q, div_eq_mul_inv] using
          tendsto_const_nhds.add (tendsto_const_nhds.mul hone)
      have hqENN : Tendsto (fun n => ENNReal.ofReal (q n)) atTop
          (nhds (Metric.ediam A)) := by
        have := ENNReal.tendsto_ofReal hqReal
        simpa [Metric.diam, ENNReal.ofReal_toReal hAtop] using this
      have hlim : Tendsto
          (fun n => c * ENNReal.ofReal (q n) ^ s) atTop
          (nhds (c * Metric.ediam A ^ s)) :=
        ENNReal.Tendsto.const_mul (hqENN.ennrpow_const s) (Or.inr hctop)
      apply ge_of_tendsto' hlim
      intro n
      have hsubset : A ⊆ Metric.closedBall x (q n) := by
        intro y hy
        rw [Metric.mem_closedBall]
        exact (Metric.dist_le_diam_of_mem' hAtop hy hx).trans
          (le_add_of_nonneg_right (by positivity))
      calc
        μ A ≤ μ (Metric.closedBall x (q n)) := measure_mono hsubset
        _ ≤ ENNReal.ofReal (C * (q n) ^ s) :=
          hball x (q n) (hqpos n) (hqle n)
        _ = c * ENNReal.ofReal (q n) ^ s := by
          rw [ENNReal.ofReal_mul' (Real.rpow_nonneg (hqpos n).le s)]
          rw [← ENNReal.ofReal_rpow_of_nonneg (hqpos n).le hs.le]
  have hmk : μ ≤ Measure.mkMetric (fun r : ENNReal => c * r ^ s) :=
    Measure.le_mkMetric _ μ (ENNReal.ofReal (1 / 2 : ℝ))
      (by positivity) hsmall
  have hmkH :
      (Measure.mkMetric (fun r : ENNReal => c * r ^ s) :
          Measure UnitAddCircle) ≤ c • μH[s] := by
    rw [Measure.hausdorffMeasure]
    apply Measure.mkMetric_mono_smul hctop hczero
    exact Eventually.of_forall fun _ => le_rfl
  exact Measure.absolutelyContinuous_of_le_smul (hmk.trans hmkH)

/-- A Frostman measure gives zero mass to every set whose Hausdorff dimension
is strictly smaller than its exponent. -/
theorem measure_zero_of_dimH_lt_of_closedBall_le
    (μ : Measure UnitAddCircle) (s C : ℝ) (hs : 0 < s) (hC : 1 ≤ C)
    (hball : ∀ x : UnitAddCircle, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r ^ s))
    (E : Set UnitAddCircle) (hE : dimH E < ENNReal.ofReal s) :
    μ E = 0 := by
  let d : NNReal := ⟨s, hs.le⟩
  have hac : μ ≪ μH[(d : ℝ)] := by
    simpa [d] using
      absolutelyContinuous_hausdorffMeasure_of_closedBall_le
        μ s C hs hC hball
  have hd_eq : (d : ENNReal) = ENNReal.ofReal s := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  have hEd : dimH E < (d : ENNReal) := by
    rw [hd_eq]
    exact hE
  exact measure_zero_of_dimH_lt hac hEd

/-- Every empirical cluster is zero on every set of Hausdorff dimension below
one, assuming the finite-prefix criterion. -/
theorem everyEmpiricalCluster_zero_on_dimH_lt_one
    (hF : PiUniformFinitePrefixFrostman) :
    ∀ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure →
        ∀ E : Set UnitAddCircle, dimH E < 1 →
          (ν : Measure UnitAddCircle) E = 0 := by
  intro ν hcluster E hE
  have hdimtop : dimH E ≠ ∞ :=
    ne_top_of_lt (hE.trans ENNReal.one_lt_top)
  have hdimReal_lt : (dimH E).toReal < 1 := by
    simpa using ENNReal.toReal_strict_mono ENNReal.one_ne_top hE
  let s : ℝ := ((dimH E).toReal + 1) / 2
  have hs : 0 < s := by
    dsimp [s]
    have hnonneg : 0 ≤ (dimH E).toReal := ENNReal.toReal_nonneg
    linarith
  have hslt : s < 1 := by
    dsimp [s]
    linarith
  have hdim_s : dimH E < ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_toReal hdimtop,
      ENNReal.ofReal_lt_ofReal_iff hs]
    dsimp [s]
    linarith
  obtain ⟨C, hC, N0, hfinite⟩ := hF s hs hslt
  have hball := finitePrefixFrostman_passes_to_cluster
    s C hs hC N0 hfinite ν hcluster
  exact measure_zero_of_dimH_lt_of_closedBall_le
    (ν : Measure UnitAddCircle) s C hs hC hball E hdim_s

/-- Conditional T21 conclusion: the uniform finite-prefix Frostman criterion
implies T1's canonical positive lower block-density predicate, via T11. -/
theorem piUniformFinitePrefixFrostman_implies_piPositiveLowerBlockDensity
    (hF : PiUniformFinitePrefixFrostman) :
    PiPositiveLowerBlockDensity := by
  exact T11.piPositiveLowerBlockDensity_of_clusters_zero_on_dimH_lt_one
    (everyEmpiricalCluster_zero_on_dimH_lt_one hF)

end Theory.PiDigits.PositiveLowerBlockDensity.T21

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T21.finitePrefixFrostman_passes_to_cluster
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T21.piUniformFinitePrefixFrostman_iff_quantifiers
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T21.absolutelyContinuous_hausdorffMeasure_of_closedBall_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T21.measure_zero_of_dimH_lt_of_closedBall_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T21.everyEmpiricalCluster_zero_on_dimH_lt_one
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T21.piUniformFinitePrefixFrostman_implies_piPositiveLowerBlockDensity
