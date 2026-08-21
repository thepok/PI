import TheoryLib.PiPositiveDecimalFactorEntropy.T1CanonicalEntropy
import TheoryLib.PiPositiveDecimalFactorEntropy.T16T16MicroscopicFullEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T22T22DecimalBoundaryAmbiguity
import Mathlib.MeasureTheory.Measure.Real

/-!
# T20: a kernel-checked times-16 transversal entropy criterion

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The circle is `UnitAddCircle = R/Z`.  Decimal cylinders use the existing
left-closed, right-open convention.  All logarithms are natural.  The final
pi theorems are conditional: neither C6 nor the stronger sublogarithmic rate
is proved here.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory

namespace DecimalFactorEntropy.TransversalEntropy

open DecimalFactorComplexity
open DecimalFactorComplexity.MicroscopicFullEntropy
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.FiniteCylinderEnergy
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open Theory.PiDigits.PositiveLowerBlockDensity.T22

/-- Multiplication by a natural number on `R/Z`. -/
def circleMul (m : ℕ) (x : UnitAddCircle) : UnitAddCircle := m • x

/-- The finite union of the first `R + 1` times-16 images of `K`. -/
def timesSixteenTransversal (K : Set UnitAddCircle) (R : ℕ) : Set UnitAddCircle :=
  ⋃ j ∈ Finset.range (R + 1), circleMul (16 ^ j) '' K

/-- Closed-radius metric density. -/
def EpsilonDense (S : Set UnitAddCircle) (ε : ℝ) : Prop :=
  ∀ y : UnitAddCircle, ∃ x ∈ S, dist y x ≤ ε

/-- A particular finite time witnesses an epsilon-dense times-16 transversal. -/
def IsTransversalTime (K : Set UnitAddCircle) (ε : ℝ) (R : ℕ) : Prop :=
  EpsilonDense (timesSixteenTransversal K R) ε

/-- Finiteness of the transversal time, without assigning an artificial value
when no finite transversal exists. -/
def HasFiniteTransversalTime (K : Set UnitAddCircle) (ε : ℝ) : Prop :=
  ∃ R : ℕ, IsTransversalTime K ε R

/-- The occupied half-open length-`n` decimal labels of `K`. -/
def occupiedLabels (K : Set UnitAddCircle) (n : ℕ) : Finset (Fin (10 ^ n)) :=
  by
    classical
    exact Finset.univ.filter fun a => (K ∩ decimalCylinder n a).Nonempty

/-- Number of occupied half-open length-`n` decimal cylinders. -/
def occupiedCount (K : Set UnitAddCircle) (n : ℕ) : ℕ :=
  (occupiedLabels K n).card

/-- Center of the closed hull of a decimal cylinder. -/
def decimalCellCenter (n : ℕ) (a : Fin (10 ^ n)) : UnitAddCircle :=
  ((((a : ℕ) : ℝ) + 1 / 2) / (10 : ℝ) ^ n : ℝ)

/-- Radius of the closed hull of a decimal cylinder. -/
def decimalCellRadius (n : ℕ) : ℝ := ((10 : ℝ) ^ n)⁻¹ / 2

theorem decimalCylinder_subset_center_closedBall (n : ℕ)
    (a : Fin (10 ^ n)) :
    decimalCylinder n a ⊆
      Metric.closedBall (decimalCellCenter n a) (decimalCellRadius n) := by
  intro x hx
  have hcell := (mem_decimalCylinder_iff n a x).mp hx
  have hq : 0 < (10 : ℝ) ^ n := by positivity
  rw [Metric.mem_closedBall]
  change dist (x : UnitAddCircle)
      (((((a : ℕ) : ℝ) + 1 / 2) / (10 : ℝ) ^ n : ℝ) : UnitAddCircle) ≤
        ((10 : ℝ) ^ n)⁻¹ / 2
  rw [← coe_unitCoordinate x, dist_eq_norm, ← QuotientAddGroup.mk_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  change |unitCoordinate x -
      ((((a : ℕ) : ℝ) + 1 / 2) / (10 : ℝ) ^ n)| ≤
        ((10 : ℝ) ^ n)⁻¹ / 2
  rw [abs_le]
  constructor
  · have hleft :
        (((a : ℕ) : ℝ) / (10 : ℝ) ^ n) =
          ((((a : ℕ) : ℝ) + 1 / 2) / (10 : ℝ) ^ n) -
            ((10 : ℝ) ^ n)⁻¹ / 2 := by
      field_simp
      ring
    linarith [hcell.1]
  · have hright :
        ((((a : ℕ) : ℝ) + 1) / (10 : ℝ) ^ n) =
          ((((a : ℕ) : ℝ) + 1 / 2) / (10 : ℝ) ^ n) +
            ((10 : ℝ) ^ n)⁻¹ / 2 := by
      field_simp
      ring
    linarith [hcell.2]

theorem circleMul_continuous (m : ℕ) : Continuous (circleMul m) := by
  simpa [circleMul] using
    (continuous_nsmul m : Continuous fun x : UnitAddCircle => m • x)

theorem dist_circleMul_le (m : ℕ) (x y : UnitAddCircle) :
    dist (circleMul m x) (circleMul m y) ≤ (m : ℝ) * dist x y := by
  simpa only [circleMul, dist_eq_norm, ← nsmul_sub] using
    (norm_nsmul_le : ‖m • (x - y)‖ ≤ (m : ℝ) * ‖x - y‖)

/-- The image ball used in the finite transversal cover. -/
def transversalCoverBall (n : ℕ) (ε : ℝ) (j : ℕ)
    (a : Fin (10 ^ n)) : Set UnitAddCircle :=
  Metric.closedBall (circleMul (16 ^ j) (decimalCellCenter n a))
    (ε + (16 : ℝ) ^ j * decimalCellRadius n)

theorem univ_subset_transversalCoverBalls
    (K : Set UnitAddCircle) (n R : ℕ) (ε : ℝ)
    (htransversal : IsTransversalTime K ε R) :
    (Set.univ : Set UnitAddCircle) ⊆
      ⋃ j ∈ Finset.range (R + 1),
        ⋃ a ∈ occupiedLabels K n, transversalCoverBall n ε j a := by
  classical
  intro y _hy
  obtain ⟨z, hz, hyz⟩ := htransversal y
  simp only [timesSixteenTransversal, Set.mem_iUnion] at hz
  obtain ⟨j, hj, x, hxK, rfl⟩ := hz
  let a := decimalCode n x
  have ha : a ∈ occupiedLabels K n := by
    simp only [occupiedLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨x, hxK, ?_⟩
    change decimalCode n x = a
    rfl
  have hcell : x ∈ Metric.closedBall (decimalCellCenter n a)
      (decimalCellRadius n) :=
    decimalCylinder_subset_center_closedBall n a rfl
  have himage : dist (circleMul (16 ^ j) x)
      (circleMul (16 ^ j) (decimalCellCenter n a)) ≤
        (16 : ℝ) ^ j * decimalCellRadius n := by
    have h := dist_circleMul_le (16 ^ j) x (decimalCellCenter n a)
    rw [Metric.mem_closedBall] at hcell
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      h.trans (mul_le_mul_of_nonneg_left hcell (by positivity))
  have hball : y ∈ transversalCoverBall n ε j a := by
    rw [transversalCoverBall, Metric.mem_closedBall]
    exact (dist_triangle y (circleMul (16 ^ j) x)
      (circleMul (16 ^ j) (decimalCellCenter n a))).trans
        (add_le_add hyz himage)
  exact Set.mem_iUnion_of_mem j <| Set.mem_iUnion_of_mem hj <|
    Set.mem_iUnion_of_mem a <| Set.mem_iUnion_of_mem ha hball

theorem volumeReal_transversalCoverBall_le
    (n j : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (a : Fin (10 ^ n)) :
    (volume : Measure UnitAddCircle).real (transversalCoverBall n ε j a) ≤
      2 * (ε + (16 : ℝ) ^ j * decimalCellRadius n) := by
  have hradius : 0 ≤ ε + (16 : ℝ) ^ j * decimalCellRadius n := by
    unfold decimalCellRadius
    positivity
  rw [transversalCoverBall, Measure.real, AddCircle.volume_closedBall,
    ENNReal.toReal_ofReal
      (le_min zero_le_one (mul_nonneg zero_le_two hradius))]
  exact min_le_right _ _

/-- The exact boundary-robust finite cover inequality.  The first term pays
for enlarging each image ball by `ε`; the second is the geometric sum of the
times-16 image radii. -/
theorem occupiedCount_cover_inequality
    (K : Set UnitAddCircle) (n R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (htransversal : IsTransversalTime K ε R) :
    1 ≤ (occupiedCount K n : ℝ) *
      (2 * (R + 1 : ℝ) * ε +
        (10 : ℝ) ^ (-(n : ℤ)) *
          ((16 : ℝ) ^ (R + 1) - 1) / 15) := by
  classical
  let U : Set UnitAddCircle :=
    ⋃ j ∈ Finset.range (R + 1),
      ⋃ a ∈ occupiedLabels K n, transversalCoverBall n ε j a
  have huniv : (Set.univ : Set UnitAddCircle) ⊆ U := by
    simpa only [U] using
      univ_subset_transversalCoverBalls K n R ε htransversal
  have hmono : (volume : Measure UnitAddCircle).real Set.univ ≤
      (volume : Measure UnitAddCircle).real U :=
    measureReal_mono huniv (measure_ne_top _ _)
  have houter : (volume : Measure UnitAddCircle).real U ≤
      ∑ j ∈ Finset.range (R + 1),
        (volume : Measure UnitAddCircle).real
          (⋃ a ∈ occupiedLabels K n, transversalCoverBall n ε j a) := by
    simpa only [U] using
      (measureReal_biUnion_finset_le (μ := (volume : Measure UnitAddCircle))
        (Finset.range (R + 1))
        (fun j => ⋃ a ∈ occupiedLabels K n, transversalCoverBall n ε j a))
  have hinner (j : ℕ) :
      (volume : Measure UnitAddCircle).real
          (⋃ a ∈ occupiedLabels K n, transversalCoverBall n ε j a) ≤
        ∑ a ∈ occupiedLabels K n,
          2 * (ε + (16 : ℝ) ^ j * decimalCellRadius n) := by
    exact (measureReal_biUnion_finset_le
      (μ := (volume : Measure UnitAddCircle)) (occupiedLabels K n)
      (transversalCoverBall n ε j)).trans
        (Finset.sum_le_sum fun a _ha =>
          volumeReal_transversalCoverBall_le n j ε hε a)
  have hsum : (volume : Measure UnitAddCircle).real U ≤
      ∑ j ∈ Finset.range (R + 1),
        ∑ a ∈ occupiedLabels K n,
          2 * (ε + (16 : ℝ) ^ j * decimalCellRadius n) :=
    houter.trans (Finset.sum_le_sum fun j _hj => hinner j)
  have hone : (volume : Measure UnitAddCircle).real
      (Set.univ : Set UnitAddCircle) = 1 := by
    norm_num [Measure.real]
  have halgebra :
      (∑ j ∈ Finset.range (R + 1),
        ∑ a ∈ occupiedLabels K n,
          2 * (ε + (16 : ℝ) ^ j * decimalCellRadius n)) =
      (occupiedCount K n : ℝ) *
        (2 * (R + 1 : ℝ) * ε +
          (10 : ℝ) ^ (-(n : ℤ)) *
            ((16 : ℝ) ^ (R + 1) - 1) / 15) := by
    rw [show (∑ j ∈ Finset.range (R + 1),
          ∑ _a ∈ occupiedLabels K n,
            2 * (ε + (16 : ℝ) ^ j * decimalCellRadius n)) =
        ∑ j ∈ Finset.range (R + 1),
          (occupiedCount K n : ℝ) *
            (2 * (ε + (16 : ℝ) ^ j * decimalCellRadius n)) by
      apply Finset.sum_congr rfl
      intro j hj
      simp [occupiedCount]]
    rw [← Finset.mul_sum]
    congr 1
    calc
      (∑ j ∈ Finset.range (R + 1),
          2 * (ε + (16 : ℝ) ^ j * decimalCellRadius n)) =
          ∑ j ∈ Finset.range (R + 1),
            (2 * ε + (2 * decimalCellRadius n) * (16 : ℝ) ^ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (R + 1 : ℝ) * (2 * ε) +
          (2 * decimalCellRadius n) *
            ∑ j ∈ Finset.range (R + 1), (16 : ℝ) ^ j := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        push_cast
        rfl
      _ = 2 * (R + 1 : ℝ) * ε +
          (10 : ℝ) ^ (-(n : ℤ)) *
            ((16 : ℝ) ^ (R + 1) - 1) / 15 := by
        rw [geom_sum_eq (by norm_num : (16 : ℝ) ≠ 1)]
        unfold decimalCellRadius
        rw [zpow_neg, zpow_natCast]
        ring
  rw [← halgebra, ← hone]
  exact hmono.trans (hsum)

/-- Exact expanded quantifiers for `R_K(ε) = O(log(1/ε))`.  The additive
The constant is an arbitrary real; finiteness is part of every radius witness. -/
def LogarithmicTransversalBound (K : Set UnitAddCircle)
    (A B ε₀ : ℝ) : Prop :=
  0 ≤ A ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ R : ℕ, IsTransversalTime K ε R ∧
        (R : ℝ) ≤ A * Real.log (1 / ε) + B

theorem logarithmicTransversalBound_iff_quantifiers
    (K : Set UnitAddCircle) (A B ε₀ : ℝ) :
    LogarithmicTransversalBound K A B ε₀ ↔
      0 ≤ A ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ R : ℕ, EpsilonDense (timesSixteenTransversal K R) ε ∧
            (R : ℝ) ≤ A * Real.log (1 / ε) + B := by
  rfl

/-- Exact expanded quantifiers for `R_K(ε) = o(log(1/ε))`. -/
def SublogarithmicTransversalBound (K : Set UnitAddCircle) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ εη : ℝ, 0 < εη ∧ εη < 1 ∧
    ∀ ε : ℝ, 0 < ε → ε < εη →
      ∃ R : ℕ, IsTransversalTime K ε R ∧
        (R : ℝ) ≤ η * Real.log (1 / ε)

theorem sublogarithmicTransversalBound_iff_quantifiers
    (K : Set UnitAddCircle) :
    SublogarithmicTransversalBound K ↔
      ∀ η : ℝ, 0 < η → ∃ εη : ℝ, 0 < εη ∧ εη < 1 ∧
        ∀ ε : ℝ, 0 < ε → ε < εη →
          ∃ R : ℕ, EpsilonDense (timesSixteenTransversal K R) ε ∧
            (R : ℝ) ≤ η * Real.log (1 / ε) := by
  rfl

/-- Forward times-10 invariance, explicitly weaker than equality invariance. -/
def ForwardTimesTenInvariant (K : Set UnitAddCircle) : Prop :=
  Set.MapsTo timesTen K K

theorem tendsto_affine_mul_exp_neg_nat
    (C D b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ =>
      (C * (n : ℝ) + D) * Real.exp (-b * (n : ℝ))) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₀ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert (h₁.const_mul C).add (h₀.const_mul D) using 1
  · ext n
    simp only [Real.rpow_one, Real.rpow_zero, one_mul, Function.comp_apply]
    ring_nf
  · simp

theorem eventually_affine_mul_rpow_two_le_one
    (C D η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (C * (n : ℝ) + D) * (10 : ℝ) ^ (-2 * η * (n : ℝ)) ≤
        (10 : ℝ) ^ (-η * (n : ℝ)) := by
  have hb : 0 < η * Real.log 10 := mul_pos hη (Real.log_pos (by norm_num))
  have ht := tendsto_affine_mul_exp_neg_nat C D (η * Real.log 10) hb
  have hevent : ∀ᶠ n : ℕ in atTop,
      (C * (n : ℝ) + D) * Real.exp (-(η * Real.log 10) * (n : ℝ)) ≤ 1 :=
    ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hevent] with n hn
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hleft :
      Real.exp (Real.log 10 * (-2 * η * (n : ℝ))) =
        Real.exp (-(η * Real.log 10) * (n : ℝ)) *
          Real.exp ((-η * (n : ℝ)) * Real.log 10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hleft]
  have hright :
      Real.exp (Real.log 10 * (-η * (n : ℝ))) =
        Real.exp ((-η * (n : ℝ)) * Real.log 10) := by
    congr 1
    ring
  rw [hright]
  calc
    (C * (n : ℝ) + D) *
          (Real.exp (-(η * Real.log 10) * (n : ℝ)) *
            Real.exp (-η * (n : ℝ) * Real.log 10)) =
        ((C * (n : ℝ) + D) *
          Real.exp (-(η * Real.log 10) * (n : ℝ))) *
            Real.exp (-η * (n : ℝ) * Real.log 10) := by ring
    _ ≤ 1 * Real.exp (-η * (n : ℝ) * Real.log 10) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ = Real.exp (-η * (n : ℝ) * Real.log 10) := one_mul _

theorem logarithmic_exponent_identity
    (A B η : ℝ) (hdenpos : 0 < 2 * (1 + A * Real.log 16))
    (hηeq : η = 1 / (2 * (1 + A * Real.log 16))) (n : ℕ) :
    (10 : ℝ) ^ (-(n : ℤ)) *
        (16 : ℝ) ^ (A * (2 * η * (n : ℝ) * Real.log 10) + B + 1) =
      (16 : ℝ) ^ (B + 1) * (10 : ℝ) ^ (-2 * η * (n : ℝ)) := by
  have hden : 2 * η * (1 + A * Real.log 16) = 1 := by
    have hinner : 0 < 1 + A * Real.log 16 := by nlinarith [hdenpos]
    rw [hηeq]
    field_simp [ne_of_gt hinner]
  rw [← Real.rpow_neg_natCast]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination ((n : ℝ) * Real.log 10) * hden

/-- A logarithmic transversal rate gives an explicit eventual exponential
lower bound for occupied decimal cylinders. -/
theorem occupiedCount_eventually_exponential_of_logarithmic
    (K : Set UnitAddCircle) (hKne : K.Nonempty) (hKclosed : IsClosed K)
    (hKinv : ForwardTimesTenInvariant K)
    (A B ε₀ : ℝ) (hrate : LogarithmicTransversalBound K A B ε₀) :
    ∃ η : ℝ, η = 1 / (2 * (1 + A * Real.log 16)) ∧ 0 < η ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        (10 : ℝ) ^ (η * (n : ℝ)) ≤ (occupiedCount K n : ℝ) := by
  rcases hrate with ⟨hA, hε₀, hε₀_one, hrate⟩
  let η : ℝ := 1 / (2 * (1 + A * Real.log 16))
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hden : 0 < 2 * (1 + A * Real.log 16) := by positivity
  have hη : 0 < η := by
    dsimp [η]
    positivity
  refine ⟨η, rfl, hη, ?_⟩
  have hε_tendsto : Tendsto
      (fun n : ℕ => (10 : ℝ) ^ (-2 * η * (n : ℝ))) atTop (𝓝 0) := by
    have hb : 0 < (10 : ℝ) ^ (-2 * η : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hb_one : (10 : ℝ) ^ (-2 * η : ℝ) < 1 := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10), Real.exp_lt_one_iff]
      exact mul_neg_of_pos_of_neg (Real.log_pos (by norm_num)) (by linarith)
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hb.le hb_one
    convert hp using 1
    ext n
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hε_small : ∀ᶠ n : ℕ in atTop,
      (10 : ℝ) ^ (-2 * η * (n : ℝ)) < ε₀ :=
    hε_tendsto.eventually (Iio_mem_nhds hε₀)
  have habsorb := eventually_affine_mul_rpow_two_le_one
    (4 * A * η * Real.log 10)
    (2 * (B + 1) + 16 ^ (B + 1) / 15) η hη
  have hall : ∀ᶠ n : ℕ in atTop,
      (10 : ℝ) ^ (-2 * η * (n : ℝ)) < ε₀ ∧
      (4 * A * η * Real.log 10 * (n : ℝ) +
          (2 * (B + 1) + 16 ^ (B + 1) / 15)) *
            (10 : ℝ) ^ (-2 * η * (n : ℝ)) ≤
          (10 : ℝ) ^ (-η * (n : ℝ)) := by
    filter_upwards [hε_small, habsorb] with n hn₁ hn₂
    exact ⟨hn₁, hn₂⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hall
  refine ⟨max 1 N₀, by omega, fun m hm => ?_⟩
  have hmN₀ : N₀ ≤ m := le_trans (le_max_right 1 N₀) hm
  have hm_all := hN₀ m hmN₀
  let ε : ℝ := (10 : ℝ) ^ (-2 * η * (m : ℝ))
  have hε : 0 < ε := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨R, htransversal, hR⟩ := hrate ε hε hm_all.1
  have hlogε : Real.log (1 / ε) = 2 * η * (m : ℝ) * Real.log 10 := by
    rw [Real.log_div (by norm_num) hε.ne', Real.log_one, zero_sub,
      Real.log_rpow (by norm_num : (0 : ℝ) < 10)]
    ring
  have hR' : (R : ℝ) ≤ A * (2 * η * (m : ℝ) * Real.log 10) + B := by
    simpa only [hlogε] using hR
  have hcover := occupiedCount_cover_inequality K m R ε hε.le htransversal
  have hfirst_bound :
      2 * (R + 1 : ℝ) * ε ≤
        (4 * A * η * Real.log 10 * (m : ℝ) + 2 * (B + 1)) *
          (10 : ℝ) ^ (-2 * η * (m : ℝ)) := by
    dsimp [ε]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hpowR :
      (16 : ℝ) ^ (R + 1) ≤
        (16 : ℝ) ^ (A * (2 * η * (m : ℝ) * Real.log 10) + B + 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hsecond_bound :
      (10 : ℝ) ^ (-(m : ℤ)) * ((16 : ℝ) ^ (R + 1) - 1) / 15 ≤
        (16 ^ (B + 1) / 15) *
          (10 : ℝ) ^ (-2 * η * (m : ℝ)) := by
    have hzpow : 0 ≤ (10 : ℝ) ^ (-(m : ℤ)) := by positivity
    calc
      (10 : ℝ) ^ (-(m : ℤ)) * ((16 : ℝ) ^ (R + 1) - 1) / 15
          ≤ (10 : ℝ) ^ (-(m : ℤ)) * (16 : ℝ) ^ (R + 1) / 15 := by
            gcongr
            linarith
      _ ≤ (10 : ℝ) ^ (-(m : ℤ)) *
            (16 : ℝ) ^ (A * (2 * η * (m : ℝ) * Real.log 10) + B + 1) / 15 := by
            gcongr
      _ = (16 ^ (B + 1) / 15) *
            (10 : ℝ) ^ (-2 * η * (m : ℝ)) := by
            rw [logarithmic_exponent_identity A B η hden rfl m]
            ring
  have hfactor :
      2 * (R + 1 : ℝ) * ε +
          (10 : ℝ) ^ (-(m : ℤ)) * ((16 : ℝ) ^ (R + 1) - 1) / 15 ≤
        (10 : ℝ) ^ (-η * (m : ℝ)) := by
    calc
      _ ≤ (4 * A * η * Real.log 10 * (m : ℝ) + 2 * (B + 1)) *
              (10 : ℝ) ^ (-2 * η * (m : ℝ)) +
            (16 ^ (B + 1) / 15) *
              (10 : ℝ) ^ (-2 * η * (m : ℝ)) :=
        add_le_add hfirst_bound hsecond_bound
      _ ≤ (10 : ℝ) ^ (-η * (m : ℝ)) := by
        convert hm_all.2 using 1 <;> ring
  have hcover' :
      1 ≤ (occupiedCount K m : ℝ) * (10 : ℝ) ^ (-η * (m : ℝ)) :=
    hcover.trans (mul_le_mul_of_nonneg_left hfactor (by positivity))
  have hinverse :
      (10 : ℝ) ^ (η * (m : ℝ)) * (10 : ℝ) ^ (-η * (m : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
    convert Real.rpow_zero 10 using 2 <;> ring
  calc
    (10 : ℝ) ^ (η * (m : ℝ)) =
        (10 : ℝ) ^ (η * (m : ℝ)) * 1 := by ring
    _ ≤ (10 : ℝ) ^ (η * (m : ℝ)) *
          ((occupiedCount K m : ℝ) * (10 : ℝ) ^ (-η * (m : ℝ))) := by
        gcongr
    _ = (occupiedCount K m : ℝ) *
          ((10 : ℝ) ^ (η * (m : ℝ)) *
            (10 : ℝ) ^ (-η * (m : ℝ))) := by ring
    _ = (occupiedCount K m : ℝ) := by rw [hinverse, mul_one]

theorem occupiedCount_pos (K : Set UnitAddCircle) (hKne : K.Nonempty) (n : ℕ) :
    0 < occupiedCount K n := by
  classical
  obtain ⟨x, hx⟩ := hKne
  rw [occupiedCount, Finset.card_pos]
  refine ⟨decimalCode n x, ?_⟩
  simp only [occupiedLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, hx, rfl⟩

theorem occupiedCount_le_pow (K : Set UnitAddCircle) (n : ℕ) :
    occupiedCount K n ≤ 10 ^ n := by
  classical
  rw [occupiedCount]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_univ.trans (Fintype.card_fin _))

theorem two_mul_succ_le_sixteen_pow (R : ℕ) :
    2 * (R + 1 : ℝ) ≤ (16 : ℝ) ^ (R + 1) := by
  induction R with
  | zero => norm_num
  | succ R ih =>
      rw [pow_succ' (16 : ℝ) (R + 1)]
      have hp : 1 ≤ (16 : ℝ) ^ (R + 1) := one_le_pow₀ (by norm_num)
      push_cast at ih ⊢
      nlinarith

theorem occupiedCount_log_lower_of_transversal
    (K : Set UnitAddCircle) (hKne : K.Nonempty) (n R : ℕ)
    (htransversal : IsTransversalTime K (((10 : ℝ) ^ (-(n : ℤ))) ^ 2) R) :
    (n : ℝ) * Real.log 10 -
        ((R + 1 : ℝ) * Real.log 16 + Real.log 2) ≤
      Real.log (occupiedCount K n : ℝ) := by
  let q : ℝ := (10 : ℝ) ^ (-(n : ℤ))
  have hq : 0 < q := by positivity
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    rw [zpow_neg, zpow_natCast]
    exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hcoef := two_mul_succ_le_sixteen_pow R
  have hgeom : ((16 : ℝ) ^ (R + 1) - 1) / 15 ≤
      (16 : ℝ) ^ (R + 1) := by
    have hp : 1 ≤ (16 : ℝ) ^ (R + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hcover := occupiedCount_cover_inequality K n R (q ^ 2)
    (sq_nonneg q) htransversal
  have hbracket :
      2 * (R + 1 : ℝ) * q ^ 2 +
          q * ((16 : ℝ) ^ (R + 1) - 1) / 15 ≤
        2 * ((16 : ℝ) ^ (R + 1) * q) := by
    have hfirst : 2 * (R + 1 : ℝ) * q ^ 2 ≤
        (16 : ℝ) ^ (R + 1) * q := by
      calc
        2 * (R + 1 : ℝ) * q ^ 2 ≤
            (16 : ℝ) ^ (R + 1) * q ^ 2 := by gcongr
        _ ≤ (16 : ℝ) ^ (R + 1) * q := by
          gcongr
          nlinarith [sq_nonneg (q - 1)]
    have hsecond : q * ((16 : ℝ) ^ (R + 1) - 1) / 15 ≤
        (16 : ℝ) ^ (R + 1) * q := by
      calc
        q * ((16 : ℝ) ^ (R + 1) - 1) / 15 =
            q * (((16 : ℝ) ^ (R + 1) - 1) / 15) := by ring
        _ ≤ q * ((16 : ℝ) ^ (R + 1)) := by gcongr
        _ = (16 : ℝ) ^ (R + 1) * q := by ring
    linarith
  have hproduct : 1 ≤ (occupiedCount K n : ℝ) *
      (2 * ((16 : ℝ) ^ (R + 1) * q)) := by
    apply hcover.trans
    gcongr
  have hcount_pos : (0 : ℝ) < occupiedCount K n := by
    exact_mod_cast occupiedCount_pos K hKne n
  have hbound_pos : 0 < 2 * ((16 : ℝ) ^ (R + 1) * q) := by positivity
  have hreciprocal :
      (2 * ((16 : ℝ) ^ (R + 1) * q))⁻¹ ≤
        (occupiedCount K n : ℝ) := by
    rw [inv_le_iff_one_le_mul₀' hbound_pos]
    simpa [mul_comm] using hproduct
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (inv_pos.mpr hbound_pos))
    (Set.mem_Ioi.mpr hcount_pos) hreciprocal
  calc
    (n : ℝ) * Real.log 10 -
          ((R + 1 : ℝ) * Real.log 16 + Real.log 2) =
        Real.log (2 * ((16 : ℝ) ^ (R + 1) * q))⁻¹ := by
      rw [Real.log_inv]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (mul_ne_zero (by positivity) hq.ne')]
      rw [Real.log_mul (by positivity : (16 : ℝ) ^ (R + 1) ≠ 0) hq.ne',
        Real.log_pow]
      dsimp [q]
      rw [Real.log_zpow]
      push_cast
      ring
    _ ≤ Real.log (occupiedCount K n : ℝ) := hlog

/-- A sublogarithmic transversal rate forces full normalized occupied-cylinder
entropy. -/
theorem occupiedCount_entropy_tendsto_one_of_sublogarithmic
    (K : Set UnitAddCircle) (hKne : K.Nonempty) (hKclosed : IsClosed K)
    (hKinv : ForwardTimesTenInvariant K)
    (hrate : SublogarithmicTransversalBound K) :
    Tendsto (fun n : ℕ =>
      Real.log (occupiedCount K n : ℝ) / ((n : ℝ) * Real.log 10))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlogSixteen : 0 < Real.log 16 := Real.log_pos (by norm_num)
  let η : ℝ := δ / (4 * Real.log 16)
  have hη : 0 < η := div_pos hδ (mul_pos (by norm_num) hlogSixteen)
  obtain ⟨εη, hεη, hεη_one, hrateη⟩ := hrate η hη
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ,
      ∀ n : ℕ, N₁ ≤ n → ((10 : ℝ) ^ (-(n : ℤ))) ^ 2 < εη := by
    have ht : Tendsto (fun n : ℕ => ((10 : ℝ) ^ (-(n : ℤ))) ^ 2)
        atTop (𝓝 0) := by
      have hbase : (0 : ℝ) ≤ 10⁻¹ ∧ (10 : ℝ)⁻¹ < 1 := by norm_num
      simpa [zpow_neg, zpow_natCast, inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hbase.1 hbase.2).pow 2
    exact eventually_atTop.1 ((tendsto_order.1 ht).2 εη hεη)
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n →
      (Real.log 16 + Real.log 2) /
          ((n : ℝ) * Real.log 10) < δ / 2 := by
    have ht : Tendsto (fun n : ℕ =>
        (Real.log 16 + Real.log 2) / ((n : ℝ) * Real.log 10))
        atTop (𝓝 0) := by
      simpa only [mul_comm] using
        (tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.const_mul_atTop hlogTen))
    exact eventually_atTop.1
      ((tendsto_order.1 ht).2 (δ / 2) (half_pos hδ))
  refine ⟨max 1 (max N₁ N₂), ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnN₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans
    ((le_max_right 1 (max N₁ N₂)).trans hn)
  have hnN₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans
    ((le_max_right 1 (max N₁ N₂)).trans hn)
  let q : ℝ := (10 : ℝ) ^ (-(n : ℤ))
  have hq : 0 < q := by positivity
  have hq2η : q ^ 2 < εη := by simpa only [q] using hN₁ n hnN₁
  obtain ⟨R, htransversal, hR⟩ := hrateη (q ^ 2) (sq_pos_of_pos hq) hq2η
  have hlogq : Real.log (1 / q ^ 2) = 2 * (n : ℝ) * Real.log 10 := by
    rw [one_div, Real.log_inv, Real.log_pow]
    dsimp [q]
    rw [Real.log_zpow]
    push_cast
    ring
  have hR' : (R : ℝ) ≤ η * (2 * (n : ℝ) * Real.log 10) := by
    simpa only [hlogq] using hR
  have hden : 0 < (n : ℝ) * Real.log 10 := mul_pos hnR hlogTen
  have hlowerLog := occupiedCount_log_lower_of_transversal
    K hKne n R (by simpa only [q] using htransversal)
  have hlower : 1 - δ <
      Real.log (occupiedCount K n : ℝ) / ((n : ℝ) * Real.log 10) := by
    have hRterm : (R : ℝ) * Real.log 16 /
        ((n : ℝ) * Real.log 10) ≤ δ / 2 := by
      rw [div_le_iff₀ hden]
      dsimp [η] at hR'
      calc
        (R : ℝ) * Real.log 16 ≤
            (δ / (4 * Real.log 16) *
              (2 * (n : ℝ) * Real.log 10)) * Real.log 16 := by gcongr
        _ = δ / 2 * ((n : ℝ) * Real.log 10) := by
          field_simp [hlogSixteen.ne']
          ring
    have herror : ((R + 1 : ℝ) * Real.log 16 + Real.log 2) /
        ((n : ℝ) * Real.log 10) < δ := by
      calc
        ((R + 1 : ℝ) * Real.log 16 + Real.log 2) /
            ((n : ℝ) * Real.log 10) =
          (R : ℝ) * Real.log 16 / ((n : ℝ) * Real.log 10) +
            (Real.log 16 + Real.log 2) /
              ((n : ℝ) * Real.log 10) := by ring
        _ < δ / 2 + δ / 2 := add_lt_add_of_le_of_lt hRterm (hN₂ n hnN₂)
        _ = δ := by ring
    apply lt_of_lt_of_le ?_ ((div_le_div_iff_of_pos_right hden).2 hlowerLog)
    rw [sub_div, div_self hden.ne']
    linarith
  have hupperCount : (occupiedCount K n : ℝ) ≤ (10 : ℝ) ^ n := by
    exact_mod_cast occupiedCount_le_pow K n
  have hcountPos : (0 : ℝ) < occupiedCount K n := by
    exact_mod_cast occupiedCount_pos K hKne n
  have hupperLog : Real.log (occupiedCount K n : ℝ) ≤
      Real.log ((10 : ℝ) ^ n) :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hcountPos)
      (Set.mem_Ioi.mpr (by positivity)) hupperCount
  have hupper : Real.log (occupiedCount K n : ℝ) /
      ((n : ℝ) * Real.log 10) ≤ 1 := by
    rw [div_le_one hden]
    calc
      Real.log (occupiedCount K n : ℝ) ≤ Real.log ((10 : ℝ) ^ n) := hupperLog
      _ = (n : ℝ) * Real.log 10 := by rw [Real.log_pow]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The exact circle orbit closure used in C6. -/
def piOrbitClosure : Set UnitAddCircle :=
  closure (Set.range piCircleOrbit)

theorem piOrbitClosure_nonempty : piOrbitClosure.Nonempty := by
  exact Set.Nonempty.closure ⟨piCircleOrbit 0, Set.mem_range_self 0⟩

theorem piOrbitClosure_isClosed : IsClosed piOrbitClosure :=
  isClosed_closure

theorem piOrbitClosure_forward_timesTen_invariant :
    ForwardTimesTenInvariant piOrbitClosure := by
  have hrange : Set.MapsTo timesTen (Set.range piCircleOrbit)
      (Set.range piCircleOrbit) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n + 1, piCircleOrbit_succ n⟩
  exact hrange.closure timesTen_continuous

/-- The closed hull of a half-open decimal cylinder. -/
def closedDecimalCell (n : ℕ) (a : Fin (10 ^ n)) : Set UnitAddCircle :=
  ((fun x : ℝ => (x : UnitAddCircle)) ''
    Set.Icc ((a : ℕ) / (10 : ℝ) ^ n)
      (((a : ℕ) + 1) / (10 : ℝ) ^ n))

theorem closedDecimalCell_isClosed (n : ℕ) (a : Fin (10 ^ n)) :
    IsClosed (closedDecimalCell n a) := by
  exact (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed

theorem decimalCylinder_subset_closedDecimalCell (n : ℕ)
    (a : Fin (10 ^ n)) :
    decimalCylinder n a ⊆ closedDecimalCell n a := by
  intro x hx
  refine ⟨unitCoordinate x, ?_, coe_unitCoordinate x⟩
  exact Set.Ico_subset_Icc_self ((mem_decimalCylinder_iff n a x).mp hx)

/-- Numerical label of an occurring factor. -/
def factorCylinderCode (n : ℕ)
    (w : Factor Theory.PiDigits.piDigit n) : Fin (10 ^ n) :=
  ⟨Theory.PiDigits.T20.wordValue (List.ofFn w.1), by
    simpa using Theory.PiDigits.T20.wordValue_lt_pow_length (List.ofFn w.1)⟩

theorem factorCylinderCode_injective (n : ℕ) :
    Function.Injective (factorCylinderCode n) := by
  intro u v huv
  apply Subtype.ext
  apply List.ofFn_inj.mp
  apply Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_injective_of_length
    (by simp)
  exact congrArg Fin.val huv

/-- The finite set of decimal labels attained by pi factors. -/
def piFactorLabels (n : ℕ) : Finset (Fin (10 ^ n)) := by
  classical
  letI : Fintype (Factor Theory.PiDigits.piDigit n) :=
    Fintype.ofFinite (Factor Theory.PiDigits.piDigit n)
  exact Finset.univ.image (factorCylinderCode n)

theorem piFactorLabels_card (n : ℕ) :
    (piFactorLabels n).card =
      Theory.PiDigits.FactorComplexity.piFactorComplexity n := by
  classical
  letI : Fintype (Factor Theory.PiDigits.piDigit n) :=
    Fintype.ofFinite (Factor Theory.PiDigits.piDigit n)
  rw [piFactorLabels, Finset.card_image_iff.mpr]
  · simp [Theory.PiDigits.FactorComplexity.piFactorComplexity,
      canonicalFactorComplexity, Nat.card_eq_fintype_card]
  · exact (factorCylinderCode_injective n).injOn

theorem factorCylinderCode_factorAt (n i : ℕ) :
    factorCylinderCode n (factorAt Theory.PiDigits.piDigit n i) =
      piCylinderCode n i := by
  apply Fin.ext
  rfl

theorem mem_piFactorLabels_iff (n : ℕ) (a : Fin (10 ^ n)) :
    a ∈ piFactorLabels n ↔ ∃ i : ℕ, piCylinderCode n i = a := by
  classical
  constructor
  · intro ha
    simp only [piFactorLabels, Finset.mem_image, Finset.mem_univ, true_and] at ha
    obtain ⟨w, hw⟩ := ha
    obtain ⟨i, hi⟩ := w.2
    refine ⟨i, ?_⟩
    rw [← factorCylinderCode_factorAt, ← hw]
    congr 1
    apply Subtype.ext
    funext j
    exact (hi j).symm
  · rintro ⟨i, rfl⟩
    simp only [piFactorLabels, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨factorAt Theory.PiDigits.piDigit n i,
      factorCylinderCode_factorAt n i⟩

/-- The cyclic decimal cell immediately to the right. -/
def decimalCellSuccessor (n : ℕ) (a : Fin (10 ^ n)) : Fin (10 ^ n) :=
  if h : a.val + 1 < 10 ^ n then ⟨a.val + 1, h⟩ else ⟨0, by positivity⟩

theorem decimalCellSuccessor_eq_of_lt (n : ℕ) (a : Fin (10 ^ n))
    (h : a.val + 1 < 10 ^ n) :
    (decimalCellSuccessor n a).val = a.val + 1 := by
  simp [decimalCellSuccessor, h]

theorem decimalCellSuccessor_eq_zero_of_eq (n : ℕ) (a : Fin (10 ^ n))
    (h : a.val + 1 = 10 ^ n) :
    (decimalCellSuccessor n a).val = 0 := by
  simp [decimalCellSuccessor, h]

/-- A half-open cell meets only its own closed hull and the hull on its left,
including the wraparound endpoint `0 = 1`. -/
theorem decimalCylinder_inter_closedDecimalCell (n : ℕ)
    (a b : Fin (10 ^ n)) (x : UnitAddCircle)
    (ha : x ∈ decimalCylinder n a) (hb : x ∈ closedDecimalCell n b) :
    a = b ∨ a = decimalCellSuccessor n b := by
  let q : ℕ := 10 ^ n
  let u : ℝ := unitCoordinate x
  have hq : (0 : ℝ) < q := by positivity
  have hau : u ∈ Set.Ico ((a.val : ℝ) / q) ((a.val + 1 : ℕ) / q) := by
    simpa [q, u] using (mem_decimalCylinder_iff n a x).mp ha
  obtain ⟨y, hy, hyx⟩ := hb
  have hy' : y ∈ Set.Icc ((b.val : ℝ) / q) ((b.val + 1 : ℕ) / q) := by
    simpa [closedDecimalCell, q] using hy
  have hy0 : 0 ≤ y := (div_nonneg (by positivity) hq.le).trans hy'.1
  have hy1 : y ≤ 1 := by
    calc
      y ≤ ((b.val + 1 : ℕ) : ℝ) / q := hy'.2
      _ ≤ 1 := (div_le_one hq).2 (by exact_mod_cast b.isLt)
  by_cases hyone : y = 1
  · have hx0 : x = 0 := by
      rw [← hyx, hyone]
      norm_num
    have hu0 : u = 0 := by
      apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
        (by simpa only [zero_add] using (show u ∈ Set.Ico (0 : ℝ) 1 from
          ⟨unitCoordinate_nonneg x, unitCoordinate_lt_one x⟩))
        (by simp)).mp
      calc
        (u : UnitAddCircle) = x := coe_unitCoordinate x
        _ = 0 := hx0
        _ = ((0 : ℝ) : UnitAddCircle) := by norm_num
    have ha0 : a.val = 0 := by
      have h : (a.val : ℝ) ≤ 0 := by
        calc
          (a.val : ℝ) ≤ u * q := (div_le_iff₀ hq).mp hau.1
          _ = 0 := by rw [hu0]; ring
      have haR0 : (a.val : ℝ) = 0 :=
        le_antisymm h (Nat.cast_nonneg a.val)
      exact_mod_cast haR0
    have hbtop : b.val + 1 = q := by
      have hleR : (q : ℝ) ≤ b.val + 1 := by
        have h := hy'.2
        rw [hyone] at h
        simpa only [one_mul, Nat.cast_add, Nat.cast_one] using
          (le_div_iff₀ hq).mp h
      have hle : q ≤ b.val + 1 := by exact_mod_cast hleR
      omega
    right
    apply Fin.ext
    rw [ha0, decimalCellSuccessor_eq_zero_of_eq n b (by simpa [q] using hbtop)]
  · have hylt : y < 1 := lt_of_le_of_ne hy1 hyone
    have hyu : y = u := by
      apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
        (by simpa only [zero_add] using (show y ∈ Set.Ico (0 : ℝ) 1 from
          ⟨hy0, hylt⟩))
        (by simpa only [zero_add] using (show u ∈ Set.Ico (0 : ℝ) 1 from
          ⟨unitCoordinate_nonneg x, unitCoordinate_lt_one x⟩))).mp
      calc
        (y : UnitAddCircle) = x := hyx
        _ = (u : UnitAddCircle) := (coe_unitCoordinate x).symm
    have habR : (a.val : ℝ) ≤ b.val + 1 := by
      calc
        (a.val : ℝ) = q * ((a.val : ℝ) / q) := by field_simp
        _ ≤ q * u := mul_le_mul_of_nonneg_left hau.1 hq.le
        _ = q * y := by rw [hyu]
        _ ≤ q * (((b.val + 1 : ℕ) : ℝ) / q) :=
          mul_le_mul_of_nonneg_left hy'.2 hq.le
        _ = b.val + 1 := by field_simp; norm_num
    have hbaR : (b.val : ℝ) < a.val + 1 := by
      calc
        (b.val : ℝ) = q * ((b.val : ℝ) / q) := by field_simp
        _ ≤ q * y := mul_le_mul_of_nonneg_left hy'.1 hq.le
        _ = q * u := by rw [hyu]
        _ < q * (((a.val + 1 : ℕ) : ℝ) / q) :=
          mul_lt_mul_of_pos_left hau.2 hq
        _ = a.val + 1 := by field_simp; norm_num
    have hab : a.val ≤ b.val + 1 := by exact_mod_cast habR
    have hba : b.val < a.val + 1 := by exact_mod_cast hbaR
    have hcases : a.val = b.val ∨ a.val = b.val + 1 := by omega
    rcases hcases with heq | heq
    · exact Or.inl (Fin.ext heq)
    · right
      apply Fin.ext
      rw [decimalCellSuccessor_eq_of_lt n b]
      · exact heq
      · rw [← heq]
        exact a.isLt

theorem isClosed_biUnion_finset {α β : Type*} [TopologicalSpace β]
    (s : Finset α) (f : α → Set β) (hf : ∀ a ∈ s, IsClosed (f a)) :
    IsClosed (⋃ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      exact (hf a (Finset.mem_insert_self a s)).union
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

theorem piOrbitClosure_subset_factorClosedCells (n : ℕ) :
    piOrbitClosure ⊆ ⋃ a ∈ piFactorLabels n, closedDecimalCell n a := by
  apply closure_minimal
  · rintro x ⟨i, rfl⟩
    let a := piCylinderCode n i
    have ha : a ∈ piFactorLabels n :=
      (mem_piFactorLabels_iff n a).2 ⟨i, rfl⟩
    refine Set.mem_iUnion_of_mem a (Set.mem_iUnion_of_mem ha ?_)
    apply decimalCylinder_subset_closedDecimalCell n a
    change decimalCode n (piCircleOrbit i) = a
    simpa [a] using (piCylinderCode_eq_decimalCode n i).symm
  · exact isClosed_biUnion_finset (piFactorLabels n) (closedDecimalCell n)
      (fun a _ha => closedDecimalCell_isClosed n a)

theorem occupiedLabels_subset_factorLabels_union_successors (n : ℕ) :
    occupiedLabels piOrbitClosure n ⊆
      piFactorLabels n ∪ (piFactorLabels n).image (decimalCellSuccessor n) := by
  intro a ha
  simp only [occupiedLabels, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨x, hxK, hxa⟩ := ha
  have hxcover := piOrbitClosure_subset_factorClosedCells n hxK
  simp only [Set.mem_iUnion] at hxcover
  obtain ⟨b, hb, hxb⟩ := hxcover
  rcases decimalCylinder_inter_closedDecimalCell n a b x hxa hxb with h | h
  · apply Finset.mem_union_left
    simpa [h] using hb
  · apply Finset.mem_union_right
    have hs : decimalCellSuccessor n b ∈
        (piFactorLabels n).image (decimalCellSuccessor n) :=
      Finset.mem_image.mpr ⟨b, hb, rfl⟩
    simpa [h] using hs

/-- Boundary-robust comparison: closure can add only the cell immediately to
the right of an attained label, hence at most doubles the finite count. -/
theorem pi_factorComplexity_le_occupiedCount_le_two_mul (n : ℕ) :
    Theory.PiDigits.FactorComplexity.piFactorComplexity n ≤
        occupiedCount piOrbitClosure n ∧
      occupiedCount piOrbitClosure n ≤
        2 * Theory.PiDigits.FactorComplexity.piFactorComplexity n := by
  constructor
  · rw [← piFactorLabels_card]
    apply Finset.card_le_card
    intro a ha
    rw [occupiedLabels]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨i, hi⟩ := (mem_piFactorLabels_iff n a).mp ha
    refine ⟨piCircleOrbit i, ?_, ?_⟩
    · exact subset_closure ⟨i, rfl⟩
    · change decimalCode n (piCircleOrbit i) = a
      rw [← hi]
      exact (piCylinderCode_eq_decimalCode n i).symm
  · rw [occupiedCount, ← piFactorLabels_card]
    calc
      (occupiedLabels piOrbitClosure n).card ≤
          (piFactorLabels n ∪
            (piFactorLabels n).image (decimalCellSuccessor n)).card :=
        Finset.card_le_card
          (occupiedLabels_subset_factorLabels_union_successors n)
      _ ≤ (piFactorLabels n).card +
          ((piFactorLabels n).image (decimalCellSuccessor n)).card :=
        Finset.card_union_le _ _
      _ ≤ (piFactorLabels n).card + (piFactorLabels n).card := by
        exact Nat.add_le_add_left
          (Finset.card_image_le (f := decimalCellSuccessor n)
            (s := piFactorLabels n)) _
      _ = 2 * (piFactorLabels n).card := by omega

/-- C6 with every constant and radius witness displayed.  This is an open
premise, not a theorem about pi. -/
def PiC6 : Prop :=
  ∃ A B ε₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ R : ℕ, IsTransversalTime piOrbitClosure ε R ∧
        (R : ℝ) ≤ A * Real.log (1 / ε) + B

theorem piC6_iff_literal_quantifiers :
    PiC6 ↔
      ∃ A B ε₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ R : ℕ,
            EpsilonDense (timesSixteenTransversal piOrbitClosure R) ε ∧
              (R : ℝ) ≤ A * Real.log (1 / ε) + B := by
  rfl

/-- C6 supplies a logarithmic bound after harmlessly shrinking its cutoff
below one. -/
theorem logarithmicTransversalBound_piOrbitClosure_of_piC6
    (hC6 : PiC6) :
    ∃ A B ε₀ : ℝ, LogarithmicTransversalBound piOrbitClosure A B ε₀ := by
  obtain ⟨A, B, ε₀, hA, hε₀, hrate⟩ := hC6
  refine ⟨A, B, min ε₀ (1 / 2), hA.le, ?_, ?_, ?_⟩
  · exact lt_min hε₀ (by norm_num)
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · intro ε hε hεsmall
    exact hrate ε hε (hεsmall.trans_le (min_le_left _ _))

/-- A fixed factor two can be absorbed by halving a positive decimal
exponent. -/
theorem eventually_half_exponential_le_of_le_two_mul
    (p q : ℕ → ℕ) (η : ℝ) (hη : 0 < η)
    (hpq : ∀ n : ℕ, q n ≤ 2 * p n)
    (N : ℕ) (hN : 1 ≤ N)
    (hq : ∀ n : ℕ, N ≤ n →
      (10 : ℝ) ^ (η * (n : ℝ)) ≤ (q n : ℝ)) :
    ∃ N' : ℕ, 1 ≤ N' ∧ ∀ n : ℕ, N' ≤ n →
      (10 : ℝ) ^ ((η / 2) * (n : ℝ)) ≤ (p n : ℝ) := by
  let b : ℝ := (10 : ℝ) ^ (η / 2)
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) (half_pos hη)
  have ht : Tendsto (fun n : ℕ => b ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb
  have hevent : ∀ᶠ n : ℕ in atTop, 2 < b ^ n :=
    ht.eventually_gt_atTop 2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
  refine ⟨max N N₀, hN.trans (le_max_left _ _), fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left N N₀).trans hn
  have hnN₀ : N₀ ≤ n := (le_max_right N N₀).trans hn
  let x : ℝ := (10 : ℝ) ^ ((η / 2) * (n : ℝ))
  have hx_nonneg : 0 ≤ x := (Real.rpow_pos_of_pos (by norm_num) _).le
  have htwo : (2 : ℝ) ≤ x := by
    calc
      (2 : ℝ) ≤ b ^ n := (hN₀ n hnN₀).le
      _ = x := by
        dsimp [b, x]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hfull : x * x = (10 : ℝ) ^ (η * (n : ℝ)) := by
    dsimp [x]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
    congr 1
    ring
  have hqcast : (q n : ℝ) ≤ 2 * (p n : ℝ) := by
    exact_mod_cast hpq n
  have htwox : 2 * x ≤ 2 * (p n : ℝ) := by
    calc
      2 * x = x * 2 := by ring
      _ ≤ x * x := mul_le_mul_of_nonneg_left htwo hx_nonneg
      _ = (10 : ℝ) ^ (η * (n : ℝ)) := hfull
      _ ≤ (q n : ℝ) := hq n hnN
      _ ≤ 2 * (p n : ℝ) := hqcast
  linarith

/-- Conditional positive entropy for pi.  The open C6 premise is explicit. -/
theorem piC6_implies_positive_decimal_factor_entropy
    (hC6 : PiC6) : 0 < DecimalFactorEntropy.piEntropyBaseTen := by
  obtain ⟨A, B, ε₀, hrate⟩ :=
    logarithmicTransversalBound_piOrbitClosure_of_piC6 hC6
  obtain ⟨η, _hηeq, hη, N, hN, hgrowth⟩ :=
    occupiedCount_eventually_exponential_of_logarithmic
      piOrbitClosure piOrbitClosure_nonempty piOrbitClosure_isClosed
      piOrbitClosure_forward_timesTen_invariant A B ε₀ hrate
  apply DecimalFactorEntropy.pi_positive_entropy_iff_canonical_exponential_quantifiers.mpr
  refine ⟨η / 2, half_pos hη, ?_⟩
  exact eventually_half_exponential_le_of_le_two_mul
    Theory.PiDigits.FactorComplexity.piFactorComplexity
    (occupiedCount piOrbitClosure) η hη
    (fun n => (pi_factorComplexity_le_occupiedCount_le_two_mul n).2)
    N hN hgrowth

/-- The normalized logarithmic loss from the factor-two boundary comparison
vanishes. -/
theorem normalized_log_two_gap_tendsto_zero :
    Tendsto (fun n : ℕ =>
      Real.log 2 / ((n : ℝ) * Real.log 10)) atTop (𝓝 0) := by
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  simpa only [mul_comm] using
    (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.const_mul_atTop hlogTen))

/-- The pi factor ratio is trapped between the occupied-cylinder ratio and
that ratio minus the factor-two loss. -/
theorem pi_entropyRatio_occupiedCount_sandwich (n : ℕ) (hn : 0 < n) :
    Real.log (occupiedCount piOrbitClosure n : ℝ) /
          ((n : ℝ) * Real.log 10) -
        Real.log 2 / ((n : ℝ) * Real.log 10) ≤
      entropyRatio Theory.PiDigits.piDigit n ∧
    entropyRatio Theory.PiDigits.piDigit n ≤
      Real.log (occupiedCount piOrbitClosure n : ℝ) /
        ((n : ℝ) * Real.log 10) := by
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * Real.log 10 := mul_pos hnR hlogTen
  have hfactorPos : (0 : ℝ) <
      canonicalFactorComplexity Theory.PiDigits.piDigit n := by
    exact_mod_cast canonicalFactorComplexity_pos Theory.PiDigits.piDigit n
  have hoccupiedPos : (0 : ℝ) < occupiedCount piOrbitClosure n := by
    exact_mod_cast occupiedCount_pos piOrbitClosure piOrbitClosure_nonempty n
  have hcomparison :
      canonicalFactorComplexity Theory.PiDigits.piDigit n ≤
          occupiedCount piOrbitClosure n ∧
        occupiedCount piOrbitClosure n ≤
          2 * canonicalFactorComplexity Theory.PiDigits.piDigit n := by
    simpa [Theory.PiDigits.FactorComplexity.piFactorComplexity] using
      pi_factorComplexity_le_occupiedCount_le_two_mul n
  have hlowerCount :
      (canonicalFactorComplexity Theory.PiDigits.piDigit n : ℝ) ≤
        occupiedCount piOrbitClosure n := by
    exact_mod_cast hcomparison.1
  have hupperCount :
      (occupiedCount piOrbitClosure n : ℝ) ≤
        2 * canonicalFactorComplexity Theory.PiDigits.piDigit n := by
    exact_mod_cast hcomparison.2
  have hlowerLog :
      Real.log (canonicalFactorComplexity Theory.PiDigits.piDigit n : ℝ) ≤
        Real.log (occupiedCount piOrbitClosure n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hfactorPos)
      (Set.mem_Ioi.mpr hoccupiedPos) hlowerCount
  have hupperLog :
      Real.log (occupiedCount piOrbitClosure n : ℝ) ≤
        Real.log 2 +
          Real.log (canonicalFactorComplexity Theory.PiDigits.piDigit n : ℝ) := by
    calc
      Real.log (occupiedCount piOrbitClosure n : ℝ) ≤
          Real.log
            (2 * canonicalFactorComplexity Theory.PiDigits.piDigit n : ℝ) :=
        Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hoccupiedPos)
          (Set.mem_Ioi.mpr (mul_pos (by norm_num) hfactorPos)) hupperCount
      _ = Real.log 2 +
          Real.log (canonicalFactorComplexity Theory.PiDigits.piDigit n : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hfactorPos.ne']
  rw [entropyRatio]
  constructor
  · rw [← sub_div]
    exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
  · exact (div_le_div_iff_of_pos_right hden).2 hlowerLog

/-- Conditional full entropy for pi.  The sublogarithmic premise is strictly
stronger than C6 and remains explicit and unproved. -/
theorem pi_sublogarithmic_transversal_implies_full_entropy
    (hsublog : SublogarithmicTransversalBound piOrbitClosure) :
    DecimalFactorEntropy.piEntropyBaseTen = 1 := by
  let occupiedRatio : ℕ → ℝ := fun n =>
    Real.log (occupiedCount piOrbitClosure n : ℝ) /
      ((n : ℝ) * Real.log 10)
  let factorTwoGap : ℕ → ℝ := fun n =>
    Real.log 2 / ((n : ℝ) * Real.log 10)
  have hoccupied : Tendsto occupiedRatio atTop (𝓝 1) := by
    simpa only [occupiedRatio] using
      occupiedCount_entropy_tendsto_one_of_sublogarithmic piOrbitClosure
        piOrbitClosure_nonempty piOrbitClosure_isClosed
        piOrbitClosure_forward_timesTen_invariant hsublog
  have hgap : Tendsto factorTwoGap atTop (𝓝 0) := by
    simpa only [factorTwoGap] using normalized_log_two_gap_tendsto_zero
  have hlower : Tendsto (fun n => occupiedRatio n - factorTwoGap n)
      atTop (𝓝 1) := by
    simpa using hoccupied.sub hgap
  have hsandwich : ∀ᶠ n : ℕ in atTop,
      occupiedRatio n - factorTwoGap n ≤
          entropyRatio Theory.PiDigits.piDigit n ∧
        entropyRatio Theory.PiDigits.piDigit n ≤ occupiedRatio n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [occupiedRatio, factorTwoGap] using
      pi_entropyRatio_occupiedCount_sandwich n (by omega)
  have hfactor : Tendsto (entropyRatio Theory.PiDigits.piDigit)
      atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hoccupied
      (hsandwich.mono fun n hn => hn.1)
      (hsandwich.mono fun n hn => hn.2)
  have hentropy : entropyBaseTen Theory.PiDigits.piDigit = 1 :=
    tendsto_nhds_unique
      (entropyRatio_tendsto Theory.PiDigits.piDigit) hfactor
  simpa only [piEntropyBaseTen] using hentropy

end DecimalFactorEntropy.TransversalEntropy

#print axioms DecimalFactorEntropy.TransversalEntropy.decimalCylinder_subset_center_closedBall
#print axioms DecimalFactorEntropy.TransversalEntropy.dist_circleMul_le
#print axioms DecimalFactorEntropy.TransversalEntropy.occupiedCount_cover_inequality
#print axioms DecimalFactorEntropy.TransversalEntropy.logarithmicTransversalBound_iff_quantifiers
#print axioms DecimalFactorEntropy.TransversalEntropy.sublogarithmicTransversalBound_iff_quantifiers
#print axioms DecimalFactorEntropy.TransversalEntropy.occupiedCount_eventually_exponential_of_logarithmic
#print axioms DecimalFactorEntropy.TransversalEntropy.occupiedCount_entropy_tendsto_one_of_sublogarithmic
#print axioms DecimalFactorEntropy.TransversalEntropy.piOrbitClosure_forward_timesTen_invariant
#print axioms DecimalFactorEntropy.TransversalEntropy.pi_factorComplexity_le_occupiedCount_le_two_mul
#print axioms DecimalFactorEntropy.TransversalEntropy.piC6_iff_literal_quantifiers
#print axioms DecimalFactorEntropy.TransversalEntropy.piC6_implies_positive_decimal_factor_entropy
#print axioms DecimalFactorEntropy.TransversalEntropy.pi_sublogarithmic_transversal_implies_full_entropy
