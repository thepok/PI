import Mathlib.Analysis.Fourier.AddCircle
import TheoryLib.PiLongLagBlockCollisionDecay.T66T66DeterministicShiftedFrequencyVdC

/-!
# T68: deterministic half-open half-arc discrepancy endpoint

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module proves only a deterministic residual-A12, `m = 1`, dyadic
primitive-sector reduction. It proves no discrepancy estimate at `Real.pi`,
no full T29 predicate, and none of C1, C2, or C3.
-/

noncomputable section

open Finset Set MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T68

open Theory.PiDigits.LongLagBlockCollisionDecay.T66

/-- The representative of a circle point in the literal fundamental interval
`[-1/2, 1/2)`. -/
def centeredRepresentative (z : UnitAddCircle) : ℝ :=
  AddCircle.equivIco 1 (-(1 / 2 : ℝ)) z

/-- Membership in the literal centered half-open half-circle `[-1/4, 1/4)`. -/
def inCenteredHalfArc (z : UnitAddCircle) : Prop :=
  centeredRepresentative z ∈ Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ)

/-- Membership in the translate by `y` of the centered half-open half-circle. -/
def inHalfOpenHalfArc (y x : UnitAddCircle) : Prop :=
  inCenteredHalfArc (x - y)

/-- The complex indicator of the literal real interval `[-1/4,1/4)`. -/
def realHalfArcIndicator (u : ℝ) : ℂ :=
  Set.indicator (Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) (fun _ => (1 : ℂ)) u

/-- The complex-valued indicator of the centered half-open half-circle. -/
def halfArcIndicator : UnitAddCircle → ℂ :=
  AddCircle.liftIco 1 (-(1 / 2 : ℝ)) realHalfArcIndicator

/-- The literal count, with multiplicity in `k`, of the first `n` points in
the half-open half-circle centered at `y`. -/
def halfArcCount (n : ℕ) (x : ℕ → UnitAddCircle) (y : UnitAddCircle) : ℕ :=
  (@Finset.filter ℕ (fun k => inHalfOpenHalfArc y (x k))
    (Classical.decPred _) (Finset.range n)).card

/-- The count excess over the exact uniform mass `n/2`. -/
def halfArcExcess (n : ℕ) (x : ℕ → UnitAddCircle) (y : UnitAddCircle) : ℝ :=
  (halfArcCount n x y : ℝ) - (n : ℝ) / 2

/-- A literal half-open half-circle, represented either by the centered
translate or by its complementary half-open translate. The second constructor
is needed to retain an unambiguous endpoint convention when changing the sign
of a count excess. -/
inductive HalfOpenHalfArc
  | centered (y : UnitAddCircle)
  | complementary (y : UnitAddCircle)

/-- Membership in an explicitly represented half-open half-circle. -/
def HalfOpenHalfArc.Contains (A : HalfOpenHalfArc) (x : UnitAddCircle) : Prop :=
  match A with
  | .centered y => inHalfOpenHalfArc y x
  | .complementary y => ¬ inHalfOpenHalfArc y x

/-- Literal multiplicity-retaining count in an explicitly represented
half-open half-circle. -/
def explicitHalfArcCount (n : ℕ) (x : ℕ → UnitAddCircle)
    (A : HalfOpenHalfArc) : ℕ :=
  (@Finset.filter ℕ (fun k => A.Contains (x k))
    (Classical.decPred _) (Finset.range n)).card

def explicitHalfArcExcess (n : ℕ) (x : ℕ → UnitAddCircle)
    (A : HalfOpenHalfArc) : ℝ :=
  (explicitHalfArcCount n x A : ℝ) - (n : ℝ) / 2

/-- T66's exact fixed-pi shifted orbit point, reduced modulo one. -/
def shiftedOrbitPoint (h r k : ℕ) : UnitAddCircle :=
  (((shiftedFrequency h r k : ℕ) : ℝ) * Real.pi : UnitAddCircle)

/-- The literal shifted-orbit half-open half-circle count. -/
def shiftedHalfArcCount (t h r : ℕ) (y : UnitAddCircle) : ℕ :=
  halfArcCount (N t - r) (shiftedOrbitPoint h r) y

/-- The literal shifted-orbit excess, normalized later by
`(N_t-r)/(H_t-1)`. -/
def shiftedHalfArcExcess (t h r : ℕ) (y : UnitAddCircle) : ℝ :=
  (shiftedHalfArcCount t h r y : ℝ) - ((N t - r : ℕ) : ℝ) / 2

def shiftedExplicitHalfArcExcess (t h r : ℕ) (A : HalfOpenHalfArc) : ℝ :=
  explicitHalfArcExcess (N t - r) (shiftedOrbitPoint h r) A

/-- A single nonnegative `Delta`, chosen before every scale, inclusive
frequency, shift, and half-open half-circle, controls the exact single-shift
excess by `Delta * (N_t-r)/(H_t-1)`. -/
def UniformShiftedHalfArcDiscrepancy (Delta : ℝ) : Prop :=
  0 ≤ Delta ∧
    ∀ t h : ℕ, h ∈ Finset.Icc 1 10 →
      ∀ r ∈ Finset.Ico 1 (H t), ∀ y : UnitAddCircle,
        |shiftedHalfArcExcess t h r y| ≤
          Delta * ((N t - r : ℕ) : ℝ) / ((H t - 1 : ℕ) : ℝ)

theorem halfArcIndicator_eq (z : UnitAddCircle) :
    halfArcIndicator z =
      @ite ℂ (inCenteredHalfArc z) (Classical.propDecidable _) 1 0 := by
  classical
  unfold halfArcIndicator AddCircle.liftIco realHalfArcIndicator
  change Set.indicator (Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
      (fun _ => (1 : ℂ)) (centeredRepresentative z) = _
  by_cases hz : inCenteredHalfArc z <;>
    simp [Set.indicator, inCenteredHalfArc] at hz ⊢

theorem halfArcCount_eq_sum (n : ℕ) (x : ℕ → UnitAddCircle)
    (y : UnitAddCircle) :
    (halfArcCount n x y : ℂ) =
      ∑ k ∈ Finset.range n, halfArcIndicator (x k - y) := by
  classical
  simp_rw [halfArcIndicator_eq]
  simpa only [halfArcCount, inHalfOpenHalfArc] using
    (Finset.natCast_card_filter (R := ℂ)
      (fun k => inCenteredHalfArc (x k - y)) (Finset.range n))

theorem integral_fourier_neg_one_on_halfArc :
    (∫ u in (-(1 / 4 : ℝ))..(1 / 4 : ℝ),
      fourier (-1) (u : UnitAddCircle)) = (1 / Real.pi : ℂ) := by
  simp_rw [fourier_coe_apply]
  let c : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr <| mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hexp (u : ℝ) :
      2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) * (u : ℂ) /
          ((1 : ℝ) : ℂ) = c * (u : ℂ) := by
    dsimp [c]
    push_cast
    ring
  simp_rw [hexp]
  rw [integral_exp_mul_complex hc]
  have hupper : c * ((1 / 4 : ℝ) : ℂ) =
      -(Real.pi : ℂ) / 2 * Complex.I := by
    dsimp [c]
    push_cast
    ring
  have hlower : c * ((-(1 / 4 : ℝ) : ℝ) : ℂ) =
      (Real.pi : ℂ) / 2 * Complex.I := by
    dsimp [c]
    push_cast
    ring
  rw [hupper, hlower, Complex.exp_neg_pi_div_two_mul_I,
    Complex.exp_pi_div_two_mul_I]
  dsimp [c]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
  ring

/-- The exact first Fourier coefficient of the literal half-open half-circle. -/
theorem halfArcIndicator_fourierCoeff :
    fourierCoeff halfArcIndicator 1 = (1 / Real.pi : ℂ) := by
  rw [show halfArcIndicator =
      AddCircle.liftIco 1 (-(1 / 2 : ℝ)) realHalfArcIndicator by rfl]
  rw [fourierCoeff_liftIco_eq]
  rw [fourierCoeffOn_eq_integral]
  have hscale : (1 / (-(1 / 2 : ℝ) + 1 - -(1 / 2 : ℝ))) = 1 := by norm_num
  have hend : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
  rw [hscale, one_smul, hend]
  have hperiod : ((1 / 2 : ℝ) - -(1 / 2 : ℝ)) = 1 := by norm_num
  rw [hperiod]
  have hpoint : (fun u : ℝ =>
      fourier (-1) (u : UnitAddCircle) • realHalfArcIndicator u) =
      Set.indicator (Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
        (fun u : ℝ => fourier (-1) (u : UnitAddCircle)) := by
    funext u
    by_cases hu : u ∈ Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ)
    · rw [realHalfArcIndicator, Set.indicator_of_mem hu,
        Set.indicator_of_mem hu]
      simp
    · rw [realHalfArcIndicator, Set.indicator_of_notMem hu,
        Set.indicator_of_notMem hu]
      simp
  have hint :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        fourier (-1) (x : UnitAddCircle) • realHalfArcIndicator x) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        Set.indicator (Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
          (fun u : ℝ => fourier (-1) (u : UnitAddCircle)) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrFun hpoint x
  refine hint.trans ?_
  norm_num
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ico]
  have hsubset : Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ) ⊆
      Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  rw [Set.inter_eq_right.mpr hsubset]
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-(1 / 4 : ℝ)) ≤ 1 / 4)]
  simpa [fourier_apply] using integral_fourier_neg_one_on_halfArc

theorem measurableSet_centeredHalfArc :
    MeasurableSet {z : UnitAddCircle | inCenteredHalfArc z} := by
  change MeasurableSet
    ((AddCircle.equivIco 1 (-(1 / 2 : ℝ))) ⁻¹'
      (Subtype.val ⁻¹' Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ)))
  exact (measurableSet_Ico.preimage measurable_subtype_coe).preimage
    (AddCircle.measurableEquivIco 1 (-(1 / 2 : ℝ))).measurable

theorem integrable_halfArcIndicator : Integrable halfArcIndicator := by
  have heq : halfArcIndicator =
      Set.indicator {z : UnitAddCircle | inCenteredHalfArc z}
        (fun _ => (1 : ℂ)) := by
    funext z
    rw [halfArcIndicator_eq]
    by_cases hz : inCenteredHalfArc z <;> simp [hz]
  rw [heq]
  exact (integrable_const (1 : ℂ)).indicator measurableSet_centeredHalfArc

theorem integrable_halfArcIndicator_mul_fourier (m : ℤ) :
    Integrable (fun z : UnitAddCircle => halfArcIndicator z * fourier m z) := by
  apply integrable_halfArcIndicator.mul_bdd
  · exact (fourier m).continuous.aestronglyMeasurable
  · filter_upwards [] with z
    rw [fourier_apply, Circle.norm_coe]

/-- One point contributes its first character divided by `pi` to the sliding
half-arc transform. -/
theorem integral_shiftedHalfArcIndicator_mul_fourier (x : UnitAddCircle) :
    (∫ y : UnitAddCircle, halfArcIndicator (x - y) * fourier 1 y) =
      fourier 1 x / (Real.pi : ℂ) := by
  let f : UnitAddCircle → ℂ := fun u =>
    halfArcIndicator u * fourier (-1) u
  have hpoint (y : UnitAddCircle) :
    halfArcIndicator (x - y) * fourier 1 y = fourier 1 x * f (x - y) := by
    have hchar : fourier 1 (x - y) * fourier 1 y = fourier 1 x := by
      simpa [fourier_apply] using congrArg (fun z : Circle => (z : ℂ))
        (AddCircle.toCircle_add (x - y) y).symm
    have hunit : fourier 1 (x - y) * fourier (-1) (x - y) = 1 := by
      rw [fourier_neg]
      rw [Complex.mul_conj]
      simp [fourier_apply]
    dsimp [f]
    calc
      halfArcIndicator (x - y) * fourier 1 y =
          halfArcIndicator (x - y) *
            (fourier 1 (x - y) * fourier (-1) (x - y)) * fourier 1 y := by
              rw [hunit]
              ring
      _ = (fourier 1 (x - y) * fourier 1 y) *
          (halfArcIndicator (x - y) * fourier (-1) (x - y)) := by ring
      _ = fourier 1 x *
          (halfArcIndicator (x - y) * fourier (-1) (x - y)) := by
            rw [hchar]
  have hmeasure : (volume : Measure UnitAddCircle) =
      AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
  calc
    (∫ y : UnitAddCircle, halfArcIndicator (x - y) * fourier 1 y) =
        ∫ y : UnitAddCircle, fourier 1 x * f (x - y) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = fourier 1 x * ∫ y : UnitAddCircle, f (x - y) := by
          rw [integral_const_mul]
    _ = fourier 1 x * ∫ u : UnitAddCircle, f u := by
          rw [MeasureTheory.integral_sub_left_eq_self f volume x]
    _ = fourier 1 x *
        ∫ u : UnitAddCircle, f u ∂AddCircle.haarAddCircle := by rw [← hmeasure]
    _ = fourier 1 x * fourierCoeff halfArcIndicator 1 := by
          congr 1
          unfold f fourierCoeff
          apply integral_congr_ae
          filter_upwards [] with u
          rw [smul_eq_mul]
          ring
    _ = fourier 1 x / (Real.pi : ℂ) := by
          rw [halfArcIndicator_fourierCoeff]
          ring

/-- The finite sliding-arc Fourier identity. The half-open endpoint convention,
finite orbit length, count excess, character, and constant are all literal. -/
theorem finite_slidingHalfArc_fourierIdentity
    (n : ℕ) (x : ℕ → UnitAddCircle) :
    (∫ y : UnitAddCircle,
        (halfArcExcess n x y : ℂ) * fourier 1 y) =
      (∑ k ∈ Finset.range n, fourier 1 (x k)) / (Real.pi : ℂ) := by
  classical
  have hterm (k : ℕ) : Integrable (fun y : UnitAddCircle =>
      halfArcIndicator (x k - y) * fourier 1 y) := by
    apply (integrable_halfArcIndicator.comp_sub_left (x k)).mul_bdd
    · exact (fourier 1).continuous.aestronglyMeasurable
    · filter_upwards [] with y
      rw [fourier_apply, Circle.norm_coe]
  have hfourier : Integrable (fun y : UnitAddCircle => fourier 1 y) := by
    simpa only [mul_one] using
      (integrable_const (1 : ℂ)).bdd_mul
        (fourier 1).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [fourier_apply, Circle.norm_coe])
  have hzero : (∫ y : UnitAddCircle, fourier 1 y) = 0 := by
    exact integral_eq_zero_of_add_right_eq_neg
      (μ := volume)
      (fourier_add_half_inv_index (by norm_num : (1 : ℤ) ≠ 0) (by norm_num) :
        ∀ y : UnitAddCircle,
          fourier 1 (y + ↑((1 : ℝ) / 2 / (1 : ℤ))) = -fourier 1 y)
  have hpoint (y : UnitAddCircle) :
      (halfArcExcess n x y : ℂ) * fourier 1 y =
        (∑ k ∈ Finset.range n,
          halfArcIndicator (x k - y) * fourier 1 y) -
            ((n : ℂ) / 2) * fourier 1 y := by
    have hcast : ((halfArcExcess n x y : ℝ) : ℂ) =
        (halfArcCount n x y : ℂ) - (n : ℂ) / 2 := by
      unfold halfArcExcess
      push_cast
      norm_num
    rw [hcast, halfArcCount_eq_sum]
    simp only [sub_mul, Finset.sum_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_sub]
  · rw [MeasureTheory.integral_finsetSum]
    · rw [integral_const_mul, hzero, mul_zero, sub_zero]
      calc
        (∑ k ∈ Finset.range n,
            ∫ y : UnitAddCircle,
              halfArcIndicator (x k - y) * fourier 1 y) =
            ∑ k ∈ Finset.range n, fourier 1 (x k) / (Real.pi : ℂ) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact integral_shiftedHalfArcIndicator_mul_fourier (x k)
        _ = (∑ k ∈ Finset.range n, fourier 1 (x k)) /
              (Real.pi : ℂ) := by
              rw [Finset.sum_div]
    · intro k hk
      exact hterm k
  · apply integrable_finsetSum
    intro k hk
    exact hterm k
  · exact hfourier.const_mul ((n : ℂ) / 2)

/-- A half-open half-arc count attains its maximum despite the discontinuous
endpoint convention, because its range is a finite subset of `{0,...,n}`. -/
theorem exists_halfArcCount_maximizer
    (n : ℕ) (x : ℕ → UnitAddCircle) :
    ∃ y : UnitAddCircle, ∀ z : UnitAddCircle,
      halfArcCount n x z ≤ halfArcCount n x y := by
  classical
  let S : Set ℕ := Set.range (halfArcCount n x)
  have hbound (y : UnitAddCircle) : halfArcCount n x y ≤ n := by
    unfold halfArcCount
    simpa using Finset.card_filter_le
      (s := Finset.range n) (p := fun k => inHalfOpenHalfArc y (x k))
  have hfinite : S.Finite := by
    apply (Set.finite_le_nat n).subset
    intro q hq
    rcases hq with ⟨y, rfl⟩
    exact hbound y
  have hnonempty : S.Nonempty := Set.range_nonempty _
  rcases Set.exists_max_image S (fun q : ℕ => q) hfinite hnonempty with
    ⟨q, hqS, hqmax⟩
  rcases hqS with ⟨y, rfl⟩
  refine ⟨y, ?_⟩
  intro z
  exact hqmax (halfArcCount n x z) ⟨z, rfl⟩

/-- The explicitly complementary half-open arc has exactly the negative
centered excess, with every endpoint assigned to exactly one side. -/
theorem explicitHalfArcExcess_complementary
    (n : ℕ) (x : ℕ → UnitAddCircle) (y : UnitAddCircle) :
    explicitHalfArcExcess n x (.complementary y) =
      -halfArcExcess n x y := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.range n) (p := fun k => inHalfOpenHalfArc y (x k))
  have hcent : explicitHalfArcCount n x (.centered y) = halfArcCount n x y := by
    rfl
  have hcomp : explicitHalfArcCount n x (.complementary y) +
      halfArcCount n x y = n := by
    simpa only [explicitHalfArcCount, HalfOpenHalfArc.Contains, hcent,
      Finset.card_range, add_comm] using hsum
  have hcompR : (explicitHalfArcCount n x (.complementary y) : ℝ) +
      (halfArcCount n x y : ℝ) = n := by exact_mod_cast hcomp
  unfold explicitHalfArcExcess halfArcExcess
  linarith

/-- T66's exact shifted character sum is the first character sum of the
literal shifted orbit points. -/
theorem shiftedSum_eq_fourier_sum (t h r : ℕ) :
    shiftedSum t h r =
      ∑ k ∈ Finset.range (N t - r), fourier 1 (shiftedOrbitPoint h r k) := by
  classical
  unfold shiftedSum shiftedCharacter shiftedOrbitPoint
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem three_le_H (t : ℕ) : 3 ≤ H t := by
  have hN : (5 : ℝ) ≤ N t := by exact_mod_cast five_le_N t
  have hs : (2 : ℝ) < Real.sqrt (N t : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hle := sqrt_N_le_H t
  exact_mod_cast (lt_of_lt_of_le hs hle)

theorem sum_triangularWeights (H0 : ℕ) (hH : 1 ≤ H0) :
    (∑ r ∈ Finset.Ico 1 H0, ((H0 - r : ℕ) : ℝ)) =
      (H0 : ℝ) * (H0 - 1 : ℕ) / 2 := by
  have hreflect :
      (∑ r ∈ Finset.Ico 1 H0, ((H0 - r : ℕ) : ℝ)) =
        ∑ r ∈ Finset.Ico 1 H0, (r : ℝ) := by
    apply Finset.sum_bij' (fun r _ => H0 - r) (fun r _ => H0 - r)
    · intro r hr
      simp only [Finset.mem_Ico] at hr ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ico] at hr ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ico] at hr
      omega
    · intro r hr
      simp only [Finset.mem_Ico] at hr
      omega
    · intro r hr
      rfl
  rw [hreflect]
  rw [Finset.sum_Ico_eq_sub _ hH]
  simp only [Finset.sum_range_one, Nat.cast_zero, sub_zero, Nat.cast_sub hH]
  have hnat := Finset.sum_range_id_mul_two H0
  have hcast := congrArg (fun q : ℕ => (q : ℝ)) hnat
  have hreal : (∑ r ∈ Finset.range H0, (r : ℝ)) * 2 =
      (H0 : ℝ) * ((H0 - 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using hcast
  rw [Nat.cast_sub hH] at hreal
  norm_num at hreal ⊢
  calc
    (∑ r ∈ Finset.range H0, (r : ℝ)) =
        ((∑ r ∈ Finset.range H0, (r : ℝ)) * 2) / 2 := by ring
    _ = (H0 : ℝ) * ((H0 : ℝ) - 1) / 2 := by rw [hreal]

theorem shiftedSum_re_le_of_halfArcDiscrepancy
    {Delta : ℝ} (hDisc : UniformShiftedHalfArcDiscrepancy Delta)
    (t h r : ℕ) (hh : h ∈ Finset.Icc 1 10)
    (hr : r ∈ Finset.Ico 1 (H t)) :
    (shiftedSum t h r).re ≤
      Real.pi * Delta * ((N t - r : ℕ) : ℝ) / ((H t - 1 : ℕ) : ℝ) := by
  rcases hDisc with ⟨hDelta, hDisc⟩
  have hD := hDisc t h hh r hr
  have hid := finite_slidingHalfArc_fourierIdentity
    (N t - r) (shiftedOrbitPoint h r)
  rw [← shiftedSum_eq_fourier_sum t h r] at hid
  let B : ℝ := Delta * ((N t - r : ℕ) : ℝ) / ((H t - 1 : ℕ) : ℝ)
  have hnormInt :
      ‖∫ y : UnitAddCircle,
          (halfArcExcess (N t - r) (shiftedOrbitPoint h r) y : ℂ) *
            fourier 1 y‖ ≤ B := by
    calc
      ‖∫ y : UnitAddCircle,
          (halfArcExcess (N t - r) (shiftedOrbitPoint h r) y : ℂ) *
            fourier 1 y‖ ≤ B * volume.real (Set.univ : Set UnitAddCircle) := by
        apply norm_integral_le_of_norm_le_const
        filter_upwards [] with y
        rw [norm_mul, Complex.norm_real, fourier_apply, Circle.norm_coe, mul_one]
        simpa only [B, shiftedHalfArcExcess, shiftedHalfArcCount,
          halfArcExcess] using hD y
      _ = B := by
        rw [measureReal_def, UnitAddCircle.measure_univ]
        norm_num
  have hnormDiv : ‖shiftedSum t h r / (Real.pi : ℂ)‖ ≤ B := by
    rw [← hid]
    exact hnormInt
  have hpiNorm : ‖(Real.pi : ℂ)‖ = Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hdiv : ‖shiftedSum t h r‖ / Real.pi ≤ B := by
    simpa only [norm_div, hpiNorm] using hnormDiv
  have hnorm : ‖shiftedSum t h r‖ ≤ Real.pi * B := by
    have := (div_le_iff₀ Real.pi_pos).mp hdiv
    nlinarith
  calc
    (shiftedSum t h r).re ≤ ‖shiftedSum t h r‖ := Complex.re_le_norm _
    _ ≤ Real.pi * B := hnorm
    _ = Real.pi * Delta * ((N t - r : ℕ) : ℝ) /
        ((H t - 1 : ℕ) : ℝ) := by simp [B]; ring

/-- The explicit uniform single-shift half-open discrepancy hypothesis gives
T66's exact triangular shifted-correlation premise with `K = 1 + pi*Delta`. -/
theorem uniformHalfArcDiscrepancy_implies_fixedPiShiftedCorrelation
    {Delta : ℝ} (hDisc : UniformShiftedHalfArcDiscrepancy Delta) :
    FixedPiShiftedCorrelation (1 + Real.pi * Delta) := by
  rcases hDisc with ⟨hDelta, hDisc⟩
  refine ⟨by positivity, ?_⟩
  intro t h hh
  have hH3 := three_le_H t
  have hH1 : 1 ≤ H t := by omega
  have hdenNat : 0 < H t - 1 := by omega
  have hden : (0 : ℝ) < ((H t - 1 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  let C : ℝ := Real.pi * Delta * (N t : ℝ) / ((H t - 1 : ℕ) : ℝ)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hrBound (r : ℕ) (hr : r ∈ Finset.Ico 1 (H t)) :
      (shiftedSum t h r).re ≤ C := by
    have hbase := shiftedSum_re_le_of_halfArcDiscrepancy
      ⟨hDelta, hDisc⟩ t h r hh hr
    have hsub : ((N t - r : ℕ) : ℝ) ≤ (N t : ℝ) := by
      exact_mod_cast Nat.sub_le (N t) r
    dsimp [C]
    calc
      (shiftedSum t h r).re ≤
          Real.pi * Delta * ((N t - r : ℕ) : ℝ) /
            ((H t - 1 : ℕ) : ℝ) := hbase
      _ ≤ Real.pi * Delta * (N t : ℝ) /
            ((H t - 1 : ℕ) : ℝ) := by gcongr
  unfold triangularEnergy
  calc
    (H t : ℝ) * N t +
        2 * ∑ r ∈ Finset.Ico 1 (H t),
          ((H t - r : ℕ) : ℝ) * (shiftedSum t h r).re ≤
      (H t : ℝ) * N t +
        2 * ∑ r ∈ Finset.Ico 1 (H t),
          ((H t - r : ℕ) : ℝ) * C := by
            gcongr with r hr
            exact hrBound r hr
    _ = (H t : ℝ) * N t +
        2 * (((H t : ℝ) * (H t - 1 : ℕ) / 2) * C) := by
          rw [← Finset.sum_mul]
          rw [sum_triangularWeights (H t) hH1]
    _ = (1 + Real.pi * Delta) * (H t : ℝ) * N t := by
          dsimp [C]
          field_simp [hden.ne']

/-- Literal failure of every nonnegative T66 constant forces arbitrarily large
positive normalized excess in one quantified frequency, shift, and half-open
half-circle. No such failure is asserted here. -/
theorem failure_implies_halfArcExcessCertificate
    (hFail : ¬ ∃ K : ℝ, FixedPiShiftedCorrelation K) :
    ∀ Delta : ℝ, 0 < Delta →
      ∃ t h r : ℕ, ∃ A : HalfOpenHalfArc,
        h ∈ Finset.Icc 1 10 ∧ r ∈ Finset.Ico 1 (H t) ∧
        Delta * ((N t - r : ℕ) : ℝ) /
            ((H t - 1 : ℕ) : ℝ) <
          shiftedExplicitHalfArcExcess t h r A := by
  intro Delta hDelta
  have hDelta0 : 0 ≤ Delta := hDelta.le
  have hnot : ¬ (∀ t h : ℕ, h ∈ Finset.Icc 1 10 →
      ∀ r ∈ Finset.Ico 1 (H t), ∀ y : UnitAddCircle,
        |shiftedHalfArcExcess t h r y| ≤
          Delta * ((N t - r : ℕ) : ℝ) / ((H t - 1 : ℕ) : ℝ)) := by
    intro hall
    exact hFail ⟨1 + Real.pi * Delta,
      uniformHalfArcDiscrepancy_implies_fixedPiShiftedCorrelation
        ⟨hDelta0, hall⟩⟩
  push Not at hnot
  rcases hnot with ⟨t, h, hh, r, hr, y, hviol⟩
  let B : ℝ := Delta * ((N t - r : ℕ) : ℝ) / ((H t - 1 : ℕ) : ℝ)
  have habs : B < |shiftedHalfArcExcess t h r y| := by
    simpa only [B] using hviol
  by_cases hnonneg : 0 ≤ shiftedHalfArcExcess t h r y
  · refine ⟨t, h, r, .centered y, hh, hr, ?_⟩
    have hcenter : shiftedExplicitHalfArcExcess t h r (.centered y) =
        shiftedHalfArcExcess t h r y := by rfl
    rw [hcenter]
    simpa [abs_of_nonneg hnonneg, B] using habs
  · refine ⟨t, h, r, .complementary y, hh, hr, ?_⟩
    have hneg : shiftedHalfArcExcess t h r y < 0 := lt_of_not_ge hnonneg
    have hcomp : shiftedExplicitHalfArcExcess t h r (.complementary y) =
        -shiftedHalfArcExcess t h r y := by
      unfold shiftedExplicitHalfArcExcess shiftedHalfArcExcess shiftedHalfArcCount
      exact explicitHalfArcExcess_complementary
        (N t - r) (shiftedOrbitPoint h r) y
    rw [hcomp]
    simpa [abs_of_neg hneg, B] using habs

/-- Fully literal audit wrapper for the failure certificate. The failed T66
premise and the resulting half-open count expose every cutoff, shift,
frequency, orbit point, triangular weight, normalization, and quantifier. -/
theorem literal_failure_implies_halfArcExcessCertificate
    (hFail : ¬ ∃ K : ℝ, 0 ≤ K ∧
      ∀ t h : ℕ, h ∈ Finset.Icc 1 10 →
        ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
            (4 * 2 ^ t + 1 : ℕ) +
          2 * ∑ r ∈ Finset.Ico 1
              (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
            ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
              (∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I *
                    (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                      (Real.pi : ℂ))).re) ≤
          K * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
            (4 * 2 ^ t + 1 : ℕ)) :
    ∀ Delta : ℝ, 0 < Delta →
      ∃ t h r : ℕ, ∃ A : HalfOpenHalfArc,
        h ∈ Finset.Icc 1 10 ∧
        r ∈ Finset.Ico 1
          (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))) ∧
        Delta * (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) /
            ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - 1 : ℕ) : ℝ) <
          (((@Finset.filter ℕ
              (fun k =>
                match A with
                | .centered y =>
                    (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                      (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * Real.pi : ℝ) :
                        UnitAddCircle) - y) : ℝ) ∈
                      Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ)
                | .complementary y =>
                    (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                      (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * Real.pi : ℝ) :
                        UnitAddCircle) - y) : ℝ) ∉
                      Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
              (Classical.decPred _)
              (Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))).card : ℕ) : ℝ) -
            (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) / 2 := by
  have hFail' : ¬ ∃ K : ℝ, FixedPiShiftedCorrelation K := by
    intro h
    apply hFail
    rcases h with ⟨K, hK, hCorr⟩
    refine ⟨K, hK, ?_⟩
    intro t h hh
    simpa only [triangularEnergy, shiftedSum, shiftedCharacter,
      shiftedFrequency, H, N] using hCorr t h hh
  simpa only [shiftedExplicitHalfArcExcess, explicitHalfArcExcess,
    explicitHalfArcCount, HalfOpenHalfArc.Contains, inHalfOpenHalfArc,
    inCenteredHalfArc, centeredRepresentative, shiftedOrbitPoint,
    shiftedFrequency, N, H] using
    failure_implies_halfArcExcessCertificate hFail'

/-- Conditional composition with T66's kernel-checked specialized
primitive-sector budget. Every constant and lower-order term remains exposed. -/
theorem uniformHalfArcDiscrepancy_implies_primitiveBudget
    {Delta : ℝ} (hDisc : UniformShiftedHalfArcDiscrepancy Delta)
    (Q0 t : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (2 : ℝ) * (
      (∑ p ∈ Theory.PiDigits.LongLagBlockCollisionDecay.T59.selectedRecordDomain t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1)) +
      (∑ p ∈ Theory.PiDigits.LongLagBlockCollisionDecay.T59.unmatchedDefect Q0 t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤
      10 * ((225 / 8 : ℝ) * (1 + Real.pi * Delta) ^ 2 + 5) *
        ((4 * 2 ^ t + 1 : ℕ) +
          (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s) ) := by
  have hFixed := uniformHalfArcDiscrepancy_implies_fixedPiShiftedCorrelation hDisc
  apply fixedPi_shiftedCorrelation_implies_primitiveBudget hFixed.1
  · intro j h hh
    simpa only [triangularEnergy, shiftedSum, shiftedCharacter,
      shiftedFrequency, H, N] using hFixed.2 j h hh
  · exact hs0
  · exact hs1

/-- Fully literal audit wrapper for the discrepancy-to-T66 converse and its
specialized primitive-sector budget. No discrepancy hypothesis is asserted. -/
theorem literal_uniformHalfArcDiscrepancy_implies_primitiveBudget
    {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hDisc : ∀ t h : ℕ, h ∈ Finset.Icc 1 10 →
      ∀ r ∈ Finset.Ico 1
          (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
        ∀ y : UnitAddCircle,
          abs ((((@Finset.filter ℕ
              (fun k =>
                (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                  (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * Real.pi : ℝ) :
                    UnitAddCircle) - y) : ℝ) ∈
                  Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
              (Classical.decPred _)
              (Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))).card : ℕ) : ℝ) -
              (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) / 2) ≤
            Delta * (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) /
              ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - 1 : ℕ) : ℝ))
    (Q0 t : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (2 : ℝ) * (
      (∑ p ∈ Theory.PiDigits.LongLagBlockCollisionDecay.T59.selectedRecordDomain t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1)) +
      (∑ p ∈ Theory.PiDigits.LongLagBlockCollisionDecay.T59.unmatchedDefect Q0 t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤
      10 * ((225 / 8 : ℝ) * (1 + Real.pi * Delta) ^ 2 + 5) *
        ((4 * 2 ^ t + 1 : ℕ) +
          (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s) ) := by
  apply uniformHalfArcDiscrepancy_implies_primitiveBudget
  · refine ⟨hDelta, ?_⟩
    intro j h hh r hr y
    unfold shiftedHalfArcExcess shiftedHalfArcCount halfArcCount
      inHalfOpenHalfArc inCenteredHalfArc centeredRepresentative
      shiftedOrbitPoint shiftedFrequency N H
    convert hDisc j h hh r hr y using 1
  · exact hs0
  · exact hs1

end Theory.PiDigits.LongLagBlockCollisionDecay.T68

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.halfArcCount_eq_sum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.halfArcIndicator_fourierCoeff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.integral_shiftedHalfArcIndicator_mul_fourier
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.finite_slidingHalfArc_fourierIdentity
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.exists_halfArcCount_maximizer
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.explicitHalfArcExcess_complementary
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.shiftedSum_eq_fourier_sum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.sum_triangularWeights
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.shiftedSum_re_le_of_halfArcDiscrepancy
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.uniformHalfArcDiscrepancy_implies_fixedPiShiftedCorrelation
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.failure_implies_halfArcExcessCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.literal_failure_implies_halfArcExcessCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.uniformHalfArcDiscrepancy_implies_primitiveBudget
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T68.literal_uniformHalfArcDiscrepancy_implies_primitiveBudget
