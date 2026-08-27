import TheoryLib.PiLacunaryNearReturnSparsity.T4ClusterNearReturns
import TheoryLib.PiLacunaryNearReturnSparsity.T6CylinderCollision
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy

/-!
# Coherent finite-prefix characterization of open C2

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module characterizes the agenda's open C2 hypothesis by synchronized
finite-prefix collision-energy decay. It does not assert C2, the finite-prefix
decay, or the canonical near-return statement for `Real.pi`.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

namespace DecimalFactorComplexity.CoherentFinitePrefixDecay

open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.CylinderCollision
open DecimalFactorComplexity.FiniteCylinderEnergy

/-- The open `r`-neighborhood of the diagonal in `(R/Z)^2`. -/
def openDiagonal (r : ℝ) : Set (UnitAddCircle × UnitAddCircle) :=
  {xy | dist xy.1 xy.2 < r}

theorem openDiagonal_isOpen (r : ℝ) : IsOpen (openDiagonal r) := by
  exact isOpen_lt (continuous_fst.dist continuous_snd) continuous_const

theorem closedDiagonal_subset_openDiagonal {r R : ℝ} (hrR : r < R) :
    closedDiagonal r ⊆ openDiagonal R := by
  intro xy hxy
  exact hxy.trans_lt hrR

theorem openDiagonal_subset_closedDiagonal (r : ℝ) :
    openDiagonal r ⊆ closedDiagonal r := by
  intro xy hxy
  change dist xy.1 xy.2 < r at hxy
  change dist xy.1 xy.2 ≤ r
  exact hxy.le

/-- Ordered first-`N` pairs whose orbit-image lies in `S`. -/
def empiricalSetPairCount (u : ℕ → UnitAddCircle)
    (S : Set (UnitAddCircle × UnitAddCircle)) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    (u ij.1.val, u ij.2.val) ∈ S).card

/-- Evaluation of an empirical product on any measurable set. This is the
set-parametric form of T4's closed-diagonal counting identity. -/
theorem empiricalProduct_apply_measurableSet (u : ℕ → UnitAddCircle)
    (S : Set (UnitAddCircle × UnitAddCircle)) (hS : MeasurableSet S)
    (N : ℕ) (hN : 0 < N) :
    ((circleEmpiricalMeasure u N).prod (circleEmpiricalMeasure u N) :
      Measure (UnitAddCircle × UnitAddCircle)) S =
        (empiricalSetPairCount u S N : ENNReal) / (N : ENNReal) ^ 2 := by
  classical
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let sample : Fin (M + 1) → UnitAddCircle := fun i => u i.val
  let uniform : ProbabilityMeasure (Fin (M + 1)) :=
    ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
  let pairUniform : ProbabilityMeasure (Fin (M + 1) × Fin (M + 1)) :=
    ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
  have hsample : Measurable sample := measurable_of_finite sample
  have hprod : uniform.prod uniform = pairUniform :=
    uniformFin_prod_eq_uniformFinProd M
  change ((uniform.map hsample.aemeasurable).prod
      (uniform.map hsample.aemeasurable) :
        Measure (UnitAddCircle × UnitAddCircle)) S = _
  rw [ProbabilityMeasure.map_prod_map uniform uniform hsample hsample, hprod]
  rw [ProbabilityMeasure.map_apply' pairUniform
    (hsample.prodMap hsample).aemeasurable hS]
  change ProbabilityTheory.uniformOn Set.univ
      (Prod.map sample sample ⁻¹' S) = _
  rw [ProbabilityTheory.uniformOn_univ]
  let T : Set (Fin (M + 1) × Fin (M + 1)) :=
    Prod.map sample sample ⁻¹' S
  have hT : T.Finite := Set.toFinite T
  change Measure.count T /
      (Fintype.card (Fin (M + 1) × Fin (M + 1)) : ENNReal) = _
  rw [Measure.count_apply_finite T hT]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have hcard : hT.toFinset.card =
      ((Finset.univ : Finset (Fin (M + 1) × Fin (M + 1))).filter
        fun ij : Fin (M + 1) × Fin (M + 1) =>
        (u ij.1.val, u ij.2.val) ∈ S).card := by
    apply congrArg Finset.card
    ext ij
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Finset.mem_univ,
      true_and, T, Set.mem_preimage, sample]
    rcases ij with ⟨i, j⟩
    rfl
  rw [hcard]
  unfold empiricalSetPairCount
  congr 1
  push_cast
  ring

/-- T6's cylinder energy of a positive pi empirical measure is exactly T7's
normalized finite-prefix energy. -/
theorem cylinderCollisionEnergy_piDecimalEmpiricalMeasure
    (m N : ℕ) (hN : 0 < N) :
    cylinderCollisionEnergy (piDecimalEmpiricalMeasure N) m =
      normalizedPiCylinderCollisionEnergy m N := by
  classical
  let G := codeGraph m (Equiv.refl (Fin (10 ^ m)))
  have happ := empiricalProduct_apply_measurableSet piDecimalCircleOrbit G
    (codeGraph_measurable m (Equiv.refl _)) N hN
  have hcard : empiricalSetPairCount piDecimalCircleOrbit G N =
      piCylinderCollisionEnergy m N := by
    rw [piCylinderCollisionEnergy_eq_equalPairs_card]
    unfold empiricalSetPairCount
    apply congrArg Finset.card
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      piCylinderEqualPairs]
    rw [mem_codeGraph_iff]
    simp only [Equiv.refl_apply]
    rw [← piCylinderCode_eq_decimalCode, ← piCylinderCode_eq_decimalCode]
    exact eq_comm
  have happReal :
      (((piDecimalEmpiricalMeasure N).prod (piDecimalEmpiricalMeasure N) :
        Measure (UnitAddCircle × UnitAddCircle)) G).toReal =
        (empiricalSetPairCount piDecimalCircleOrbit G N : ℝ) /
          (N : ℝ) ^ 2 := by
    have h := congrArg ENNReal.toReal happ
    simpa only [piDecimalEmpiricalMeasure, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_pow] using h
  calc
    cylinderCollisionEnergy (piDecimalEmpiricalMeasure N) m =
        (((piDecimalEmpiricalMeasure N).prod (piDecimalEmpiricalMeasure N) :
          Measure (UnitAddCircle × UnitAddCircle)) G).toReal := by
      simpa only [G] using
        (codeGraph_refl_mass_eq_cylinderCollisionEnergy
          (piDecimalEmpiricalMeasure N) m).symm
    _ = (empiricalSetPairCount piDecimalCircleOrbit G N : ℝ) /
          (N : ℝ) ^ 2 := happReal
    _ = normalizedPiCylinderCollisionEnergy m N := by
      rw [hcard]
      rfl

/-- A generic diagonal extraction lemma. Pointwise eventual estimates can be
synchronized on every finite triangle `m <= k` along a strict subsequence. -/
theorem exists_strictMono_diagonal_subsequence
    (P : ℕ → ℕ → Prop) (hP : ∀ m, ∀ᶠ j : ℕ in atTop, P j m) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k m : ℕ, m ≤ k → P (s k) m := by
  have hrow (k : ℕ) : ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, m ≤ k → P j m := by
    change ∀ᶠ j : ℕ in atTop, ∀ m ∈ Set.Iic k, P j m
    exact (Set.finite_Iic k).eventually_all.mpr fun m _hm => hP m
  choose t ht using fun k => eventually_atTop.1 (hrow k)
  let s : ℕ → ℕ := fun k => Nat.rec (t 0)
    (fun k previous => max (previous + 1) (t (k + 1))) k
  have hs_succ (k : ℕ) : s (k + 1) = max (s k + 1) (t (k + 1)) := by
    simp [s]
  have hsStrict : StrictMono s := strictMono_nat_of_lt_succ fun k => by
    rw [hs_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  refine ⟨s, hsStrict, ?_⟩
  intro k m hmk
  apply ht k (s k) ?_ m hmk
  cases k with
  | zero => simp [s]
  | succ k =>
      rw [hs_succ]
      exact le_max_right _ _

/-- Fully quantitative coherent finite-prefix decay. The same prefix `N k`
obeys the same exponential estimate at every depth in the finite triangle
`m0 <= m <= k`, after the row threshold `k0`. -/
def PiCoherentFinitePrefixDecayAt
    (β D : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (ν : ProbabilityMeasure UnitAddCircle) : Prop :=
  0 < β ∧ 0 < D ∧ StrictMono N ∧ (∀ k, 0 < N k) ∧
    Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 ν) ∧
    ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
      normalizedPiCylinderCollisionEnergy m (N k) ≤
        D * (decimalRadius m) ^ β

/-- The quantitative coherent predicate with every constant, threshold,
subsequence condition, and triangular `m <= k` quantifier exposed. -/
theorem piCoherentFinitePrefixDecayAt_iff_quantifiers
    (β D : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (ν : ProbabilityMeasure UnitAddCircle) :
    PiCoherentFinitePrefixDecayAt β D m0 k0 N ν ↔
      0 < β ∧ 0 < D ∧ StrictMono N ∧ (∀ k, 0 < N k) ∧
      Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 ν) ∧
      ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
        normalizedPiCylinderCollisionEnergy m (N k) ≤
          D * (decimalRadius m) ^ β :=
  Iff.rfl

/-- Existential coherent finite-prefix decay. This is only a predicate; no
theorem in this module asserts that it holds for pi. -/
def PiCoherentFinitePrefixDecay : Prop :=
  ∃ β D : ℝ, ∃ m0 k0 : ℕ, ∃ N : ℕ → ℕ,
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      PiCoherentFinitePrefixDecayAt β D m0 k0 N ν

/-- Quantitative C2-to-prefix direction. The exponent is explicitly reduced
from `α` to `α/2`, giving strict slack for Portmanteau and finite
diagonalization. The resulting bound has constant `1`. -/
theorem c2_witnesses_imply_coherent_finitePrefix
    (α C : ℝ) (hα : 0 < α) (hC : 0 < C)
    (cutoffs : ℕ → ℕ) (hcutoffs : StrictMono cutoffs)
    (hcutoffsPos : ∀ k, 0 < cutoffs k)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hν : Tendsto (fun k => piDecimalEmpiricalMeasure (cutoffs k))
      atTop (𝓝 ν))
    (r0 : ℝ) (hr0 : 0 < r0)
    (hsmall : ∀ r : ℝ, 0 < r → r ≤ r0 →
      (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
        (closedDiagonal r) ≤ ENNReal.ofReal (C * r ^ α)) :
    ∃ m0 k0 : ℕ, ∃ s : ℕ → ℕ,
      StrictMono s ∧
      PiCoherentFinitePrefixDecayAt (α / 2) 1 m0 k0
        (cutoffs ∘ s) ν := by
  have hC0 : 0 ≤ C := hC.le
  let β := α / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hpow : Tendsto (fun m : ℕ => (decimalRadius m) ^ β)
      atTop (𝓝 0) := by
    have hcont := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    have h := hcont.comp decimalRadius_tendsto_zero
    simpa [Real.zero_rpow hβ.ne'] using h
  have hCpow : Tendsto (fun m : ℕ => C * (decimalRadius m) ^ β)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  have heventSlack : ∀ᶠ m : ℕ in atTop,
      C * (decimalRadius m) ^ β < 1 :=
    hCpow.eventually (Iio_mem_nhds zero_lt_one)
  have heventRadius : ∀ᶠ m : ℕ in atTop, decimalRadius m ≤ r0 :=
    (decimalRadius_tendsto_zero.eventually (Iic_mem_nhds hr0)).mono
      fun _ hm => hm
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 (heventSlack.and heventRadius)
  have hstrict (m : ℕ) (hm : m0 ≤ m) :
      C * (decimalRadius m) ^ α < (decimalRadius m) ^ β := by
    have hs := (hm0 m hm).1
    have hrpow : 0 < (decimalRadius m) ^ β :=
      Real.rpow_pos_of_pos (decimalRadius_pos m) _
    rw [show α = β + β by dsimp [β]; ring,
      Real.rpow_add (decimalRadius_pos m)]
    nlinarith [hC0]
  have hpointwise (m : ℕ) : ∀ᶠ j : ℕ in atTop,
      m0 ≤ m → normalizedPiCylinderCollisionEnergy m (cutoffs j) ≤
        (decimalRadius m) ^ β := by
    by_cases hm : m0 ≤ m
    · have hprodTendsto := empiricalProduct_tendsto hν
      have hport : limsup (fun j =>
          ((piDecimalEmpiricalMeasure (cutoffs j)).prod
            (piDecimalEmpiricalMeasure (cutoffs j)) :
              Measure (UnitAddCircle × UnitAddCircle))
                (closedDiagonal (decimalRadius m))) atTop ≤
          (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
            (closedDiagonal (decimalRadius m)) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hprodTendsto
          (closedDiagonal_isClosed (decimalRadius m))
      have hlimit : limsup (fun j =>
          ((piDecimalEmpiricalMeasure (cutoffs j)).prod
            (piDecimalEmpiricalMeasure (cutoffs j)) :
              Measure (UnitAddCircle × UnitAddCircle))
                (closedDiagonal (decimalRadius m))) atTop <
          ENNReal.ofReal ((decimalRadius m) ^ β) := by
        refine hport.trans_lt ((hsmall (decimalRadius m)
          (decimalRadius_pos m) (hm0 m hm).2).trans_lt ?_)
        exact (ENNReal.ofReal_lt_ofReal_iff
          (Real.rpow_pos_of_pos (decimalRadius_pos m) _)).2 (hstrict m hm)
      have hevent := eventually_lt_of_limsup_lt hlimit
      filter_upwards [hevent] with j hj
      intro _hm
      have hreal : closedSmallBallMass (piDecimalEmpiricalMeasure (cutoffs j))
          (decimalRadius m) < (decimalRadius m) ^ β := by
        exact (ENNReal.lt_ofReal_iff_toReal_lt
          (measure_ne_top
            ((piDecimalEmpiricalMeasure (cutoffs j)).prod
              (piDecimalEmpiricalMeasure (cutoffs j)) :
                Measure (UnitAddCircle × UnitAddCircle)) _)).1 hj
      rw [← cylinderCollisionEnergy_piDecimalEmpiricalMeasure m (cutoffs j)
        (hcutoffsPos j)]
      exact (cylinderCollisionEnergy_le_closedSmallBallMass
        (piDecimalEmpiricalMeasure (cutoffs j)) m).trans hreal.le
    · exact Eventually.of_forall fun _ h => (hm h).elim
  obtain ⟨s, hs, hsdiag⟩ := exists_strictMono_diagonal_subsequence
    (fun j m => m0 ≤ m →
      normalizedPiCylinderCollisionEnergy m (cutoffs j) ≤
        (decimalRadius m) ^ β) hpointwise
  refine ⟨m0, m0, s, hs, hβ, by norm_num,
    hcutoffs.comp hs, fun k => hcutoffsPos (s k), ?_, ?_⟩
  · simpa [Function.comp_def] using hν.comp hs.tendsto_atTop
  · intro k _hk m hm hmk
    simpa [β, Function.comp_def] using hsdiag k m hmk hm

/-- Explicit decimal endpoint and open/closed enlargement used in the reverse
Portmanteau argument. Bracketing `10*r` gives a depth at least `m0`, an open
radius strictly larger than `r`, and endpoint loss strictly below `100`. -/
theorem exists_decimal_openClosed_enlargement
    (m0 : ℕ) {r : ℝ} (hr : 0 < r)
    (hr0 : r ≤ min (1 / 10 : ℝ) (decimalRadius m0 / 10)) :
    ∃ m : ℕ, m0 ≤ m ∧ r < decimalRadius m ∧
      decimalRadius m < 100 * r ∧
      closedDiagonal r ⊆ openDiagonal (decimalRadius m) ∧
      openDiagonal (decimalRadius m) ⊆ closedDiagonal (decimalRadius m) := by
  have htenr : 0 < 10 * r := by positivity
  have htenrOne : 10 * r ≤ 1 := by
    have := hr0.trans (min_le_left (1 / 10 : ℝ) (decimalRadius m0 / 10))
    linarith
  have htenrDepth : 10 * r ≤ decimalRadius m0 := by
    have := hr0.trans (min_le_right (1 / 10 : ℝ) (decimalRadius m0 / 10))
    linarith
  obtain ⟨m, hmnext, htenr_m⟩ :=
    exists_decimalRadius_bracket htenr htenrOne
  have hm0 : m0 ≤ m := by
    by_contra hnot
    have hsucc : m + 1 ≤ m0 := by omega
    have hmono := decimalRadius_antitone hsucc
    linarith
  have hr_m : r < decimalRadius m := by linarith
  have hm_lt_hundred : decimalRadius m < 100 * r := by
    rw [decimalRadius_succ_eq_div_ten] at hmnext
    linarith
  exact ⟨m, hm0, hr_m, hm_lt_hundred,
    closedDiagonal_subset_openDiagonal hr_m,
    openDiagonal_subset_closedDiagonal (decimalRadius m)⟩

/-- Quantitative prefix-to-C2 direction. A closed radius-`r` diagonal is
enlarged to an open diagonal whose decimal endpoint comes from bracketing
`10*r`; that endpoint is strictly below `100*r`. T6 contributes the factor
`3`, so the displayed C2 constant is `3*D*100^β`. -/
theorem coherent_finitePrefix_witnesses_imply_c2
    (β D : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hcoh : PiCoherentFinitePrefixDecayAt β D m0 k0 N ν) :
    0 < β ∧ 0 < 3 * D * 100 ^ β ∧
      StrictMono N ∧ (∀ k, 0 < N k) ∧
      Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 ν) ∧
      ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
        (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
            (closedDiagonal r) ≤
          ENNReal.ofReal ((3 * D * 100 ^ β) * r ^ β) := by
  rcases hcoh with ⟨hβ, hD, hNmono, hNpos, hν, henergy⟩
  refine ⟨hβ, by positivity, hNmono, hNpos, hν, ?_⟩
  let r0 := min (1 / 10 : ℝ) (decimalRadius m0 / 10)
  have hr0 : 0 < r0 := by
    dsimp [r0]
    exact lt_min (by norm_num)
      (div_pos (decimalRadius_pos m0) (by norm_num))
  refine ⟨r0, hr0, ?_⟩
  intro r hr hrle
  have hrle' : r ≤ min (1 / 10 : ℝ) (decimalRadius m0 / 10) := by
    simpa only [r0] using hrle
  obtain ⟨m, hm0, hr_m, hm_lt_hundred, hclosedG, hGclosed⟩ :=
    exists_decimal_openClosed_enlargement m0 hr hrle'
  let G := openDiagonal (decimalRadius m)
  have hGopen : IsOpen G := openDiagonal_isOpen (decimalRadius m)
  have hport : (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) G ≤
      liminf (fun k =>
        ((piDecimalEmpiricalMeasure (N k)).prod
          (piDecimalEmpiricalMeasure (N k)) :
            Measure (UnitAddCircle × UnitAddCircle)) G) atTop := by
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (empiricalProduct_tendsto hν) hGopen
  have heventBound : ∀ᶠ k : ℕ in atTop,
      ((piDecimalEmpiricalMeasure (N k)).prod
        (piDecimalEmpiricalMeasure (N k)) :
          Measure (UnitAddCircle × UnitAddCircle)) G ≤
        ENNReal.ofReal (3 * D * (decimalRadius m) ^ β) := by
    filter_upwards [eventually_ge_atTop (max k0 m)] with k hk
    have hk0 : k0 ≤ k := (le_max_left _ _).trans hk
    have hmk : m ≤ k := (le_max_right _ _).trans hk
    have hfinite := henergy k hk0 m hm0 hmk
    have hNpositive := hNpos k
    have hclosed :=
      closedSmallBallMass_le_three_mul_cylinderCollisionEnergy
        (piDecimalEmpiricalMeasure (N k)) m
    rw [cylinderCollisionEnergy_piDecimalEmpiricalMeasure m (N k)
      hNpositive] at hclosed
    have hclosedBound :
        closedSmallBallMass (piDecimalEmpiricalMeasure (N k))
            (decimalRadius m) ≤ 3 * D * (decimalRadius m) ^ β := by
      calc
        closedSmallBallMass (piDecimalEmpiricalMeasure (N k))
            (decimalRadius m) ≤
            3 * normalizedPiCylinderCollisionEnergy m (N k) := hclosed
        _ ≤ 3 * (D * (decimalRadius m) ^ β) := by gcongr
        _ = 3 * D * (decimalRadius m) ^ β := by ring
    have hreal :
        (((piDecimalEmpiricalMeasure (N k)).prod
          (piDecimalEmpiricalMeasure (N k)) :
            Measure (UnitAddCircle × UnitAddCircle)) G).toReal ≤
          3 * D * (decimalRadius m) ^ β := by
      exact (ENNReal.toReal_mono
        (measure_ne_top
          ((piDecimalEmpiricalMeasure (N k)).prod
            (piDecimalEmpiricalMeasure (N k)) :
              Measure (UnitAddCircle × UnitAddCircle)) _)
        (measure_mono hGclosed)).trans hclosedBound
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top
        ((piDecimalEmpiricalMeasure (N k)).prod
          (piDecimalEmpiricalMeasure (N k)) :
            Measure (UnitAddCircle × UnitAddCircle)) _)
      (mul_nonneg (mul_nonneg (by norm_num) hD.le)
        (Real.rpow_nonneg (decimalRadius_pos m).le β))).2 hreal
  have hendpointReal : 3 * D * (decimalRadius m) ^ β ≤
      (3 * D * 100 ^ β) * r ^ β := by
    have hrpow : (decimalRadius m) ^ β ≤ (100 * r) ^ β :=
      Real.rpow_le_rpow (decimalRadius_pos m).le hm_lt_hundred.le hβ.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 100) hr.le] at hrpow
    nlinarith [Real.rpow_pos_of_pos (decimalRadius_pos m) β]
  calc
    (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
        (closedDiagonal r) ≤
        (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) G :=
      measure_mono hclosedG
    _ ≤ liminf (fun k =>
        ((piDecimalEmpiricalMeasure (N k)).prod
          (piDecimalEmpiricalMeasure (N k)) :
            Measure (UnitAddCircle × UnitAddCircle)) G) atTop := hport
    _ ≤ liminf (fun _k : ℕ =>
        ENNReal.ofReal (3 * D * (decimalRadius m) ^ β)) atTop :=
      liminf_le_liminf heventBound
    _ = ENNReal.ofReal (3 * D * (decimalRadius m) ^ β) :=
      by simp
    _ ≤ ENNReal.ofReal ((3 * D * 100 ^ β) * r ^ β) :=
      ENNReal.ofReal_le_ofReal hendpointReal

/-- C2 implies coherent finite-prefix energy decay. This is a conditional
implication and makes no assertion that C2 holds for pi. -/
theorem piPolynomialSmallBallC2_implies_coherentFinitePrefixDecay
    (hC2 : PiPolynomialSmallBallC2) : PiCoherentFinitePrefixDecay := by
  rcases hC2 with
    ⟨α, C, hα, hC, cutoffs, hcutoffs, hcutoffsPos, ν, hν,
      r0, hr0, hsmall⟩
  obtain ⟨m0, k0, s, hs, hcoh⟩ :=
    c2_witnesses_imply_coherent_finitePrefix α C hα hC cutoffs
      hcutoffs hcutoffsPos ν hν r0 hr0 hsmall
  exact ⟨α / 2, 1, m0, k0, cutoffs ∘ s, ν, hcoh⟩

/-- Coherent finite-prefix energy decay implies C2. This is a conditional
implication and makes no assertion that the finite-prefix premise holds. -/
theorem coherentFinitePrefixDecay_implies_piPolynomialSmallBallC2
    (hfinite : PiCoherentFinitePrefixDecay) : PiPolynomialSmallBallC2 := by
  rcases hfinite with ⟨β, D, m0, k0, N, ν, hcoh⟩
  obtain ⟨hβ, hC, hNmono, hNpos, hν, r0, hr0, hsmall⟩ :=
    coherent_finitePrefix_witnesses_imply_c2 β D m0 k0 N ν hcoh
  exact ⟨β, 3 * D * 100 ^ β, hβ, hC, N, hNmono, hNpos,
    ν, hν, r0, hr0, hsmall⟩

/-- Finite-prefix characterization of the agenda's open C2 hypothesis. It is
not a proof of C2, of the canonical A1 near-return statement, or of any decay
property of pi. -/
theorem piPolynomialSmallBallC2_iff_coherentFinitePrefixDecay :
    PiPolynomialSmallBallC2 ↔ PiCoherentFinitePrefixDecay :=
  ⟨piPolynomialSmallBallC2_implies_coherentFinitePrefixDecay,
    coherentFinitePrefixDecay_implies_piPolynomialSmallBallC2⟩

end DecimalFactorComplexity.CoherentFinitePrefixDecay

#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.cylinderCollisionEnergy_piDecimalEmpiricalMeasure
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.exists_strictMono_diagonal_subsequence
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.piCoherentFinitePrefixDecayAt_iff_quantifiers
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.c2_witnesses_imply_coherent_finitePrefix
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.exists_decimal_openClosed_enlargement
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.coherent_finitePrefix_witnesses_imply_c2
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.piPolynomialSmallBallC2_implies_coherentFinitePrefixDecay
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.coherentFinitePrefixDecay_implies_piPolynomialSmallBallC2
#print axioms DecimalFactorComplexity.CoherentFinitePrefixDecay.piPolynomialSmallBallC2_iff_coherentFinitePrefixDecay
