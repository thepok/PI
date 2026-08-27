import TheoryLib.PiLacunaryNearReturnSparsity.T1LagDecomposition
import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiDecimalFactorComplexity.T10PiWeightedFourierReduction
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Empirical clusters imply sparse near returns

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves a conditional reduction only.  Its polynomial small-ball
cluster hypothesis is C2 from the research agenda; no theorem asserts C2 for
`Real.pi`.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory

namespace DecimalFactorComplexity.ClusterNearReturns

/-- The uniform empirical probability measure on the first `N` terms of `u`.
Only positive `N` are used below; the value at zero is an arbitrary Dirac mass. -/
def circleEmpiricalMeasure (u : ℕ → UnitAddCircle) : ℕ →
    ProbabilityMeasure UnitAddCircle
  | 0 => diracProba 0
  | N + 1 =>
      let uniform : ProbabilityMeasure (Fin (N + 1)) :=
        ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
      uniform.map
        (measurable_of_finite (fun i : Fin (N + 1) => u i.val)).aemeasurable

/-- Ordered pairs among the first `N` orbit points at strict circle distance
less than `r`.  The diagonal is retained whenever `r > 0`. -/
def orderedNearReturnCount (u : ℕ → UnitAddCircle) (r : ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    dist (u ij.1.val) (u ij.2.val) < r).card

/-- Ordered pairs in the corresponding closed diagonal neighborhood. -/
def orderedClosedPairCount (u : ℕ → UnitAddCircle) (r : ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    dist (u ij.1.val) (u ij.2.val) ≤ r).card

/-- The closed `r`-neighborhood of the diagonal in `(ℝ/ℤ)²`. -/
def closedDiagonal (r : ℝ) : Set (UnitAddCircle × UnitAddCircle) :=
  {xy | dist xy.1 xy.2 ≤ r}

theorem closedDiagonal_isClosed (r : ℝ) : IsClosed (closedDiagonal r) := by
  exact isClosed_le (continuous_fst.dist continuous_snd) continuous_const

theorem orderedNearReturnCount_le_closed (u : ℕ → UnitAddCircle) (r : ℝ) (N : ℕ) :
    orderedNearReturnCount u r N ≤ orderedClosedPairCount u r N := by
  classical
  apply Finset.card_le_card
  intro ij hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hij.le

theorem diagonal_mem_orderedNearReturnCount (u : ℕ → UnitAddCircle) (r : ℝ)
    (hr : 0 < r) (N : ℕ) (i : Fin N) :
    (i, i) ∈ (Finset.univ.filter fun ij : Fin N × Fin N =>
      dist (u ij.1.val) (u ij.2.val) < r) := by
  simp [hr]

/-- The product of two uniform laws on `Fin (M+1)` is the uniform law on
ordered pairs. -/
theorem uniformFin_prod_eq_uniformFinProd (M : ℕ) :
    let uniform : ProbabilityMeasure (Fin (M + 1)) :=
      ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
    let pairUniform : ProbabilityMeasure (Fin (M + 1) × Fin (M + 1)) :=
      ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
    uniform.prod uniform = pairUniform := by
  dsimp
  apply Subtype.ext
  apply Measure.ext_of_singleton
  intro ij
  rw [show ({ij} : Set (Fin (M + 1) × Fin (M + 1))) =
      ({ij.1} : Set (Fin (M + 1))) ×ˢ {ij.2} by ext xy; simp]
  change (Measure.prod (ProbabilityTheory.uniformOn Set.univ)
      (ProbabilityTheory.uniformOn Set.univ)) ({ij.1} ×ˢ {ij.2}) =
    ProbabilityTheory.uniformOn Set.univ ({ij.1} ×ˢ {ij.2})
  rw [Measure.prod_prod]
  simp [ProbabilityTheory.uniformOn_univ, Fintype.card_prod]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
  field_simp

/-- Evaluation of an empirical self-product is exactly the normalized ordered
pair count.  Multiplicity and diagonal pairs are therefore both visible. -/
theorem empiricalProduct_apply_closedDiagonal (u : ℕ → UnitAddCircle)
    (r : ℝ) (N : ℕ) (hN : 0 < N) :
    ((circleEmpiricalMeasure u N).prod (circleEmpiricalMeasure u N) :
      Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal r) =
        (orderedClosedPairCount u r N : ENNReal) / (N : ENNReal) ^ 2 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let sample : Fin (M + 1) → UnitAddCircle := fun i => u i.val
  let uniform : ProbabilityMeasure (Fin (M + 1)) :=
    ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
  let pairUniform : ProbabilityMeasure (Fin (M + 1) × Fin (M + 1)) :=
    ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
  have hsample : Measurable sample := measurable_of_finite sample
  have hdiag : MeasurableSet (closedDiagonal r) := (closedDiagonal_isClosed r).measurableSet
  have hprod : uniform.prod uniform = pairUniform := by
    exact uniformFin_prod_eq_uniformFinProd M
  change ((uniform.map hsample.aemeasurable).prod
      (uniform.map hsample.aemeasurable) :
        Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal r) = _
  rw [ProbabilityMeasure.map_prod_map uniform uniform hsample hsample, hprod]
  rw [ProbabilityMeasure.map_apply' pairUniform
    (hsample.prodMap hsample).aemeasurable hdiag]
  change ProbabilityTheory.uniformOn Set.univ
      (Prod.map sample sample ⁻¹' closedDiagonal r) = _
  rw [ProbabilityTheory.uniformOn_univ]
  let S : Set (Fin (M + 1) × Fin (M + 1)) :=
    Prod.map sample sample ⁻¹' closedDiagonal r
  have hS : S.Finite := Set.toFinite S
  change Measure.count S / (Fintype.card (Fin (M + 1) × Fin (M + 1)) : ENNReal) = _
  rw [Measure.count_apply_finite S hS]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have hcard : hS.toFinset.card = orderedClosedPairCount u r (M + 1) := by
    apply congrArg Finset.card
    ext ij
    simp [S, sample, closedDiagonal]
  rw [hcard]
  congr 1
  push_cast
  ring

/-- Weak convergence of empirical measures implies weak convergence of their
self-products; this is the product-convergence step used by Portmanteau. -/
theorem empiricalProduct_tendsto {u : ℕ → UnitAddCircle} {cutoffs : ℕ → ℕ}
    {ν : ProbabilityMeasure UnitAddCircle}
    (hν : Tendsto (fun k => circleEmpiricalMeasure u (cutoffs k)) atTop (𝓝 ν)) :
    Tendsto (fun k => (circleEmpiricalMeasure u (cutoffs k)).prod
      (circleEmpiricalMeasure u (cutoffs k))) atTop (𝓝 (ν.prod ν)) := by
  exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hν.prodMk_nhds hν)

/-- The canonical decimal radius `10⁻ⁿ`. -/
def decimalRadius (n : ℕ) : ℝ := ((10 : ℝ) ^ n)⁻¹

theorem decimalRadius_pos (n : ℕ) : 0 < decimalRadius n := by
  simp [decimalRadius]

theorem decimalRadius_tendsto_zero :
    Tendsto decimalRadius atTop (𝓝 0) := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 10)).inv_tendsto_atTop

/-- Exponential decimal scales beat the linear factor in the canonical
estimate, for every positive real exponent. -/
theorem tendsto_nat_mul_const_mul_decimalRadius_rpow (α C : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ => (n : ℝ) * C * (decimalRadius n) ^ α)
      atTop (𝓝 0) := by
  have hb : 0 < α * Real.log 10 := mul_pos hα (Real.log_pos (by norm_num))
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
    (α * Real.log 10) hb).comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun n : ℕ => C * ((n : ℝ) ^ (1 : ℝ) *
      Real.exp (-(α * Real.log 10) * (n : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (tendsto_const_nhds.mul h : Tendsto (fun n : ℕ => C *
        (((n : ℝ) ^ (1 : ℝ) * Real.exp (-(α * Real.log 10) * (n : ℝ)))))
        atTop (𝓝 (C * 0)))
  convert hC using 1
  · ext n
    have hr : decimalRadius n ^ α =
        Real.exp (-(α * Real.log 10) * (n : ℝ)) := by
      rw [decimalRadius, Real.inv_rpow (by positivity)]
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
      rw [← Real.exp_neg]
      ring_nf
    rw [Real.rpow_one, hr]
    ring

/-- C2 for a circle orbit: a positive, strictly increasing subsequence of
empirical measures converges weakly to a probability measure whose product
has a polynomial upper bound on every sufficiently small closed diagonal
neighborhood. -/
def PolynomialSmallBallCluster (u : ℕ → UnitAddCircle) : Prop :=
  ∃ α C : ℝ, 0 < α ∧ 0 < C ∧
    ∃ cutoffs : ℕ → ℕ, StrictMono cutoffs ∧ (∀ k, 0 < cutoffs k) ∧
      ∃ ν : ProbabilityMeasure UnitAddCircle,
        Tendsto (fun k => circleEmpiricalMeasure u (cutoffs k)) atTop (𝓝 ν) ∧
          ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
            (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
                (closedDiagonal r) ≤ ENNReal.ofReal (C * r ^ α)

/-- Generic cluster-to-near-return theorem.  The count is ordered and
diagonal-inclusive, while its defining distance inequality is strict. -/
theorem polynomialSmallBallCluster_implies_nearReturnEstimate
    (u : ℕ → UnitAddCircle) (hC2 : PolynomialSmallBallCluster u) :
    ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * orderedNearReturnCount u (decimalRadius n) N ≤ N ^ 2 := by
  rintro A hA
  obtain ⟨α, C, hα, hC, cutoffs, _hcutoffs, hcutoffsPos, ν, hν, r0, hr0,
    hsmall⟩ := hC2
  have hdecay := tendsto_nat_mul_const_mul_decimalRadius_rpow α ((A : ℝ) * C) hα
  have heventDecay : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ((A : ℝ) * C) * (decimalRadius n) ^ α < 1 :=
    hdecay.eventually (Iio_mem_nhds zero_lt_one)
  have heventRadius : ∀ᶠ n : ℕ in atTop, decimalRadius n < r0 :=
    decimalRadius_tendsto_zero.eventually (Iio_mem_nhds hr0)
  obtain ⟨m, hm⟩ := (eventually_atTop.1 (heventDecay.and heventRadius))
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  have hnm : m ≤ n := (le_max_right 1 m).trans hn
  obtain ⟨hdecayN, hradiusN⟩ := hm n hnm
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 m).trans hn)
  have hAn : 0 < (A : ℝ) * (n : ℝ) := by positivity
  have hnumeric : C * (decimalRadius n) ^ α <
      1 / ((A : ℝ) * (n : ℝ)) := by
    apply (lt_div_iff₀ hAn).2
    calc
      C * decimalRadius n ^ α * ((A : ℝ) * (n : ℝ)) =
          (n : ℝ) * ((A : ℝ) * C) * decimalRadius n ^ α := by ring
      _ < 1 := hdecayN
  have hprodTendsto := empiricalProduct_tendsto hν
  have hport : limsup (fun k =>
      ((circleEmpiricalMeasure u (cutoffs k)).prod
        (circleEmpiricalMeasure u (cutoffs k)) :
          Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal (decimalRadius n)))
        atTop ≤ (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
          (closedDiagonal (decimalRadius n)) :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hprodTendsto
      (closedDiagonal_isClosed (decimalRadius n))
  have hlimitBound : limsup (fun k =>
      ((circleEmpiricalMeasure u (cutoffs k)).prod
        (circleEmpiricalMeasure u (cutoffs k)) :
          Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal (decimalRadius n)))
        atTop ≤ ENNReal.ofReal (C * (decimalRadius n) ^ α) :=
    hport.trans (hsmall (decimalRadius n) (decimalRadius_pos n) hradiusN.le)
  have hthresholdPos : 0 < 1 / ((A : ℝ) * (n : ℝ)) := by positivity
  have hlimitStrict : limsup (fun k =>
      ((circleEmpiricalMeasure u (cutoffs k)).prod
        (circleEmpiricalMeasure u (cutoffs k)) :
          Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal (decimalRadius n)))
        atTop < ENNReal.ofReal (1 / ((A : ℝ) * (n : ℝ))) :=
    hlimitBound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hthresholdPos).2 hnumeric)
  have heventProduct : ∀ᶠ k : ℕ in atTop,
      ((circleEmpiricalMeasure u (cutoffs k)).prod
        (circleEmpiricalMeasure u (cutoffs k)) :
          Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal (decimalRadius n)) <
        ENNReal.ofReal (1 / ((A : ℝ) * (n : ℝ))) :=
    eventually_lt_of_limsup_lt hlimitStrict
  obtain ⟨k, hk⟩ := heventProduct.exists
  let N := cutoffs k
  have hN : 0 < N := hcutoffsPos k
  have hk' : (orderedClosedPairCount u (decimalRadius n) N : ENNReal) /
      (N : ENNReal) ^ 2 < ENNReal.ofReal (1 / ((A : ℝ) * (n : ℝ))) := by
    rw [← empiricalProduct_apply_closedDiagonal u (decimalRadius n) N hN]
    exact hk
  have hkReal : (orderedClosedPairCount u (decimalRadius n) N : ℝ) /
      (N : ℝ) ^ 2 < 1 / ((A : ℝ) * (n : ℝ)) := by
    have hconverted := (ENNReal.toReal_lt_toReal (by finiteness)
      ENNReal.ofReal_ne_top).2 hk'
    simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hthresholdPos.le] using hconverted
  have hNreal : 0 < (N : ℝ) ^ 2 := by positivity
  have hclosed : (orderedClosedPairCount u (decimalRadius n) N : ℝ) <
      (N : ℝ) ^ 2 / ((A : ℝ) * (n : ℝ)) := by
    calc
      (orderedClosedPairCount u (decimalRadius n) N : ℝ) <
          (1 / ((A : ℝ) * (n : ℝ))) * (N : ℝ) ^ 2 :=
        (div_lt_iff₀ hNreal).1 hkReal
      _ = (N : ℝ) ^ 2 / ((A : ℝ) * (n : ℝ)) := by ring
  have hscaledClosed : (A : ℝ) * (n : ℝ) *
      (orderedClosedPairCount u (decimalRadius n) N : ℝ) < (N : ℝ) ^ 2 := by
    have := (lt_div_iff₀ hAn).1 hclosed
    nlinarith
  have hnearReal : (A : ℝ) * (n : ℝ) *
      (orderedNearReturnCount u (decimalRadius n) N : ℝ) < (N : ℝ) ^ 2 := by
    calc
      (A : ℝ) * (n : ℝ) *
          (orderedNearReturnCount u (decimalRadius n) N : ℝ) ≤
          (A : ℝ) * (n : ℝ) *
            (orderedClosedPairCount u (decimalRadius n) N : ℝ) := by
        gcongr
        exact_mod_cast orderedNearReturnCount_le_closed u (decimalRadius n) N
      _ < (N : ℝ) ^ 2 := hscaledClosed
  refine ⟨N, hN, ?_⟩
  have hnat : A * n * orderedNearReturnCount u (decimalRadius n) N < N ^ 2 := by
    exact_mod_cast hnearReal
  exact hnat.le

/-- The base-ten orbit of pi on `ℝ/ℤ`. -/
def piDecimalCircleOrbit (j : ℕ) : UnitAddCircle :=
  (((10 : ℝ) ^ j * Real.pi : ℝ) : UnitAddCircle)

/-- Positive-length empirical measures of the decimal orbit of pi.  C2 below
uses this definition only at the explicitly positive subsequence lengths. -/
def piDecimalEmpiricalMeasure (N : ℕ) : ProbabilityMeasure UnitAddCircle :=
  circleEmpiricalMeasure piDecimalCircleOrbit N

/-- The agenda's C2 hypothesis for pi, stated but not asserted. -/
def PiPolynomialSmallBallC2 : Prop :=
  PolynomialSmallBallCluster piDecimalCircleOrbit

/-- Every pair counted by T1's strict custom circle distance is counted by the
strict metric near-return count on `ℝ/ℤ`. -/
theorem Q_pi_le_orderedNearReturnCount (n N : ℕ) :
    Q_pi n N ≤ orderedNearReturnCount piDecimalCircleOrbit (decimalRadius n) N := by
  classical
  rw [Q_pi, orderedNearReturnCount]
  apply Finset.card_le_card
  intro ij hij
  rw [mem_piNearReturnPairs_iff] at hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨z, hz⟩ :=
    WeightedFourierReduction.exists_int_abs_sub_lt_of_circleDistance_lt hij
  let x : ℝ := ((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi
  have hz0 : (((z : ℝ) : ℝ) : UnitAddCircle) = 0 := by
    rw [show (z : ℝ) = z • (1 : ℝ) by simp, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero]
  have hcoe : ((x : ℝ) : UnitAddCircle) = (((x - (z : ℝ) : ℝ)) : UnitAddCircle) := by
    calc
      ((x : ℝ) : UnitAddCircle) =
          ((((x - (z : ℝ)) + (z : ℝ) : ℝ)) : UnitAddCircle) :=
        congrArg (fun t : ℝ => (t : UnitAddCircle)) (by ring)
      _ = (((x - (z : ℝ) : ℝ)) : UnitAddCircle) + (((z : ℝ) : ℝ) : UnitAddCircle) :=
        AddCircle.coe_add (1 : ℝ) (x - (z : ℝ)) (z : ℝ)
      _ = (((x - (z : ℝ) : ℝ)) : UnitAddCircle) := by rw [hz0, add_zero]
  rw [dist_comm, dist_eq_norm]
  change ‖(((10 : ℝ) ^ (ij.2 : ℕ) * Real.pi : ℝ) : UnitAddCircle) -
      (((10 : ℝ) ^ (ij.1 : ℕ) * Real.pi : ℝ) : UnitAddCircle)‖ < decimalRadius n
  rw [← QuotientAddGroup.mk_sub]
  have hx : (10 : ℝ) ^ (ij.2 : ℕ) * Real.pi -
      (10 : ℝ) ^ (ij.1 : ℕ) * Real.pi = x := by
    dsimp [x]
    ring
  rw [hx]
  change ‖((x : ℝ) : UnitAddCircle)‖ < decimalRadius n
  rw [hcoe]
  exact QuotientAddGroup.norm_mk_le_norm.trans_lt (by
    simpa only [Real.norm_eq_abs, x, decimalRadius] using hz)

/-- Conditional pi specialization with the canonical quantifier order and
T1's exact ordered, diagonal-inclusive, strict-distance `Q_pi`.  This theorem
assumes C2 and makes no unconditional assertion about pi. -/
theorem piPolynomialSmallBallC2_implies_canonical_C1
    (hC2 : PiPolynomialSmallBallC2) :
    ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2 := by
  intro A hA
  obtain ⟨n0, hn0, hall⟩ :=
    polynomialSmallBallCluster_implies_nearReturnEstimate
      piDecimalCircleOrbit hC2 A hA
  refine ⟨n0, hn0, ?_⟩
  intro n hn
  obtain ⟨N, hN, hbound⟩ := hall n hn
  refine ⟨N, hN, ?_⟩
  calc
    A * n * Q_pi n N ≤ A * n *
        orderedNearReturnCount piDecimalCircleOrbit (decimalRadius n) N := by
      gcongr
      exact Q_pi_le_orderedNearReturnCount n N
    _ ≤ N ^ 2 := hbound

end DecimalFactorComplexity.ClusterNearReturns

#print axioms DecimalFactorComplexity.ClusterNearReturns.empiricalProduct_apply_closedDiagonal
#print axioms DecimalFactorComplexity.ClusterNearReturns.empiricalProduct_tendsto
#print axioms DecimalFactorComplexity.ClusterNearReturns.polynomialSmallBallCluster_implies_nearReturnEstimate
#print axioms DecimalFactorComplexity.ClusterNearReturns.Q_pi_le_orderedNearReturnCount
#print axioms DecimalFactorComplexity.ClusterNearReturns.piPolynomialSmallBallC2_implies_canonical_C1
