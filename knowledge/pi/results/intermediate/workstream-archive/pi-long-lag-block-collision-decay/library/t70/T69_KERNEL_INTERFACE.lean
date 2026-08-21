import TheoryLib.PiLongLagBlockCollisionDecay.T63T63ExactFiniteFourthMoment
import TheoryLib.PiLongLagBlockCollisionDecay.T66T66DeterministicShiftedFrequencyVdC
import TheoryLib.PiLongLagBlockCollisionDecay.T68T68HalfArcDiscrepancy

/-!
# T69: aggregate shifted-frequency half-arc frontier

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module proves only conditional residual-A12, `m = 1`, dyadic
primitive-sector implications. It proves no aggregate or discrepancy estimate
at `Real.pi`, no full T29 predicate, and none of C1, C2, or C3.
-/

noncomputable section

open Finset Set MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T69

open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T59
open Theory.PiDigits.LongLagBlockCollisionDecay.T63
open Theory.PiDigits.LongLagBlockCollisionDecay.T66
open Theory.PiDigits.LongLagBlockCollisionDecay.T68

/-- T66's triangular energy, summed before any squaring over the ten literal
frequencies. -/
def aggregateEnergy (t : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10, triangularEnergy t h

/-- One constant controls the aggregate over all ten frequencies. This is a
conditional proposition; no witness is supplied at pi. -/
def AggregateShiftedCorrelation (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ t : ℕ, aggregateEnergy t ≤ K * (H t : ℝ) * N t

/-- The exact triangular sum over frequencies, shifts, and half-open `k`
ranges. -/
theorem aggregateEnergy_literal (t : ℕ) :
    aggregateEnergy t =
      10 * (H t : ℝ) * N t +
        2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ((H t - r : ℕ) : ℝ) *
              (∑ k ∈ Finset.range (N t - r),
                Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I *
                    (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                      (Real.pi : ℂ))).re := by
  unfold aggregateEnergy triangularEnergy shiftedSum shiftedCharacter
    shiftedFrequency
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  norm_num
  rw [Finset.mul_sum]
  ring

/-- T66's one-frequency inequalities are summed before the fourth-moment
step. -/
theorem summed_van_der_corput (t : ℕ) :
    (H t : ℝ) ^ 2 * firstMoment t ≤
      ((N t + H t - 1 : ℕ) : ℝ) * aggregateEnergy t := by
  unfold firstMoment aggregateEnergy
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun h _ => finite_van_der_corput t h

/-- The aggregate threshold gives the `N_t^3` fourth-moment scale with the
explicit constant `9/4`; no aggregate hypothesis is asserted. -/
theorem fourthMoment_le_of_aggregate
    {K : ℝ} (hAggregate : AggregateShiftedCorrelation K) (t : ℕ) :
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
      X h (4 * 2 ^ t + 1) ^ 2) ≤
        (9 / 4 : ℝ) * K ^ 2 * (4 * 2 ^ t + 1 : ℕ) ^ 3 := by
  rcases hAggregate with ⟨hK, hAggregate⟩
  have hHpos : (0 : ℝ) < H t := by exact_mod_cast H_pos t
  have hN0 : (0 : ℝ) ≤ N t := by positivity
  have hs0 : 0 ≤ Real.sqrt (N t : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (N t : ℝ)) ^ 2 = (N t : ℝ) :=
    Real.sq_sqrt hN0
  have hsum0 : 0 ≤ firstMoment t := by
    apply Finset.sum_nonneg
    intro h hh
    exact Complex.normSq_nonneg _
  have hvdc := summed_van_der_corput t
  have hmult := endpointMultiplier_le t
  have hcoeff : (0 : ℝ) ≤ (N t + H t - 1 : ℕ) := by positivity
  have hchain :
      (H t : ℝ) ^ 2 * firstMoment t ≤
        (3 / 2 : ℝ) * (H t : ℝ) * Real.sqrt (N t : ℝ) *
          (K * (H t : ℝ) * N t) := by
    calc
      (H t : ℝ) ^ 2 * firstMoment t ≤
          ((N t + H t - 1 : ℕ) : ℝ) * aggregateEnergy t := hvdc
      _ ≤ ((N t + H t - 1 : ℕ) : ℝ) *
          (K * (H t : ℝ) * N t) := by
            gcongr
            exact hAggregate t
      _ ≤ ((3 / 2 : ℝ) * (H t : ℝ) * Real.sqrt (N t : ℝ)) *
          (K * (H t : ℝ) * N t) := by
            gcongr
  have hfirst : firstMoment t ≤
      (3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ) := by
    have hscaled : (H t : ℝ) ^ 2 * firstMoment t ≤
        (H t : ℝ) ^ 2 *
          ((3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ)) := by
      calc
        (H t : ℝ) ^ 2 * firstMoment t ≤
            (3 / 2 : ℝ) * (H t : ℝ) * Real.sqrt (N t : ℝ) *
              (K * (H t : ℝ) * N t) := hchain
        _ = (H t : ℝ) ^ 2 *
            ((3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ)) := by ring
    exact le_of_mul_le_mul_left hscaled (sq_pos_of_pos hHpos)
  have hfourth : fourthMoment t ≤ firstMoment t ^ 2 := by
    exact sum_sq_le_sq_sum_of_nonneg fun h hh => Complex.normSq_nonneg _
  have hright0 : 0 ≤
      (3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ) := by positivity
  have hsq := mul_self_le_mul_self hsum0 hfirst
  change fourthMoment t ≤ (9 / 4 : ℝ) * K ^ 2 * (N t : ℝ) ^ 3
  calc
    fourthMoment t ≤ firstMoment t ^ 2 := hfourth
    _ ≤ ((3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ)) ^ 2 := by
      simpa [pow_two] using hsq
    _ = (9 / 4 : ℝ) * K ^ 2 * (N t : ℝ) ^ 2 *
        (Real.sqrt (N t : ℝ)) ^ 2 := by ring
    _ = (9 / 4 : ℝ) * K ^ 2 * (N t : ℝ) ^ 3 := by rw [hs2]; ring

/-- The combined multiplicity-retaining count in one common centered,
half-open half-arc. -/
def combinedHalfArcCount (t : ℕ) (y : UnitAddCircle) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
    ∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℝ) * (shiftedHalfArcCount t h r y : ℝ)

/-- The total weighted number of orbit points before imposing an arc. -/
def combinedTotalMass (t : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
    ∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℝ) * ((N t - r : ℕ) : ℝ)

/-- The combined count excess over half of the exact total mass. -/
def combinedHalfArcExcess (t : ℕ) (y : UnitAddCircle) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
    ∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℝ) * shiftedHalfArcExcess t h r y

/-- The analogous excess for either explicit half-open orientation. -/
def combinedExplicitHalfArcExcess (t : ℕ) (A : HalfOpenHalfArc) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
    ∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℝ) * shiftedExplicitHalfArcExcess t h r A

/-- The exact complex aggregate whose real part occurs in `aggregateEnergy`. -/
def aggregateShiftedSum (t : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
    ∑ r ∈ Finset.Ico 1 (H t),
      (((H t - r : ℕ) : ℕ) : ℂ) * shiftedSum t h r

theorem sum_range_id_real (n : ℕ) :
    (∑ r ∈ Finset.range n, (r : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hnat : (∑ r ∈ Finset.range (n + 1), r) * 2 =
          (n + 1) * n := by
        simpa using Finset.sum_range_id_mul_two (n + 1)
      have hcast := congrArg (fun q : ℕ => (q : ℝ)) hnat
      have hreal : (∑ r ∈ Finset.range (n + 1), (r : ℝ)) * 2 =
          ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at hcast
        convert hcast using 1 <;> push_cast <;> ring
      linarith

theorem sum_range_sq_real (n : ℕ) :
    (∑ r ∈ Finset.range n, (r : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem H_le_N (t : ℕ) : H t ≤ N t := by
  have hN1 : (1 : ℝ) ≤ N t := by exact_mod_cast (show 1 ≤ N t by
    have := five_le_N t
    omega)
  have hN0 : (0 : ℝ) ≤ N t := le_trans (by norm_num) hN1
  have hs2 : (Real.sqrt (N t : ℝ)) ^ 2 = (N t : ℝ) :=
    Real.sq_sqrt hN0
  have hs : Real.sqrt (N t : ℝ) ≤ (N t : ℝ) := by
    have hs0 := Real.sqrt_nonneg (N t : ℝ)
    nlinarith
  unfold H
  rw [Nat.ceil_le]
  exact_mod_cast hs

/-- Exact weighted-length identity behind the requested total mass. -/
theorem sum_weighted_shift_lengths (t : ℕ) :
    (∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℝ) * ((N t - r : ℕ) : ℝ)) =
        (H t : ℝ) * ((H t : ℝ) - 1) *
          (3 * (N t : ℝ) - (H t : ℝ) - 1) / 6 := by
  have hH3 := three_le_H t
  have hH1 : 1 ≤ H t := by omega
  have hHN := H_le_N t
  have hterm (r : ℕ) (hr : r ∈ Finset.Ico 1 (H t)) :
      ((H t - r : ℕ) : ℝ) * ((N t - r : ℕ) : ℝ) =
        ((H t : ℝ) - r) * ((N t : ℝ) - r) := by
    simp only [Finset.mem_Ico] at hr
    rw [Nat.cast_sub (Nat.le_of_lt hr.2), Nat.cast_sub (le_trans
      (Nat.le_of_lt hr.2) hHN)]
  calc
    (∑ r ∈ Finset.Ico 1 (H t),
        ((H t - r : ℕ) : ℝ) * ((N t - r : ℕ) : ℝ)) =
        ∑ r ∈ Finset.Ico 1 (H t),
          (((H t : ℝ) - r) * ((N t : ℝ) - r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hterm r hr
    _ = (∑ r ∈ Finset.range (H t),
          (((H t : ℝ) - r) * ((N t : ℝ) - r))) -
        (H t : ℝ) * (N t : ℝ) := by
          rw [Finset.sum_Ico_eq_sub _ hH1]
          norm_num
    _ = (H t : ℝ) * ((H t : ℝ) - 1) *
          (3 * (N t : ℝ) - (H t : ℝ) - 1) / 6 := by
      simp_rw [show ∀ r : ℕ,
          ((H t : ℝ) - r) * ((N t : ℝ) - r) =
            (H t : ℝ) * N t - ((H t : ℝ) + N t) * r + (r : ℝ) ^ 2 by
        intro r
        push_cast
        ring]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, ← Finset.mul_sum, sum_range_id_real,
        sum_range_sq_real]
      simp only [Finset.card_range, nsmul_eq_mul]
      ring

/-- The combined count has exactly the requested total weighted mass. -/
theorem combinedTotalMass_exact (t : ℕ) :
    combinedTotalMass t =
      10 * (H t : ℝ) * ((H t : ℝ) - 1) *
        (3 * (N t : ℝ) - (H t : ℝ) - 1) / 6 := by
  unfold combinedTotalMass
  rw [sum_weighted_shift_lengths]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  norm_num
  ring

/-- The excess definition is literally count minus half the exact mass. -/
theorem combinedHalfArcExcess_eq_count_sub_mass
    (t : ℕ) (y : UnitAddCircle) :
    combinedHalfArcExcess t y =
      combinedHalfArcCount t y - combinedTotalMass t / 2 := by
  unfold combinedHalfArcExcess combinedHalfArcCount combinedTotalMass
    shiftedHalfArcExcess shiftedHalfArcCount
  rw [Finset.sum_div]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_div]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- A displayed combined discrepancy controls one pooled count, preserving
cancellation between frequencies and shifts. -/
def CombinedHalfArcDiscrepancy (Delta : ℝ) : Prop :=
  0 ≤ Delta ∧ ∀ t : ℕ, ∀ y : UnitAddCircle,
    |combinedHalfArcExcess t y| ≤ Delta * (H t : ℝ) * N t

theorem integrable_halfArcExcess_mul_fourier
    (n : ℕ) (x : ℕ → UnitAddCircle) :
    Integrable (fun y : UnitAddCircle =>
      (halfArcExcess n x y : ℂ) * fourier 1 y) := by
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
  have hsum : Integrable (fun y : UnitAddCircle =>
      ∑ k ∈ Finset.range n,
        halfArcIndicator (x k - y) * fourier 1 y) := by
    apply integrable_finsetSum
    intro k hk
    exact hterm k
  exact (hsum.sub (hfourier.const_mul ((n : ℂ) / 2))).congr
    (Filter.Eventually.of_forall fun y => hpoint y |>.symm)

theorem shiftedHalfArc_fourierIdentity (t h r : ℕ) :
    (∫ y : UnitAddCircle,
      (shiftedHalfArcExcess t h r y : ℂ) * fourier 1 y) =
        shiftedSum t h r / (Real.pi : ℂ) := by
  have hid := finite_slidingHalfArc_fourierIdentity
    (N t - r) (shiftedOrbitPoint h r)
  rw [← shiftedSum_eq_fourier_sum t h r] at hid
  simpa only [shiftedHalfArcExcess, shiftedHalfArcCount, halfArcExcess] using hid

theorem integrable_shiftedHalfArcExcess_mul_fourier (t h r : ℕ) :
    Integrable (fun y : UnitAddCircle =>
      (shiftedHalfArcExcess t h r y : ℂ) * fourier 1 y) := by
  simpa only [shiftedHalfArcExcess, shiftedHalfArcCount, halfArcExcess] using
    integrable_halfArcExcess_mul_fourier
      (N t - r) (shiftedOrbitPoint h r)

/-- The pooled half-arc excess has exactly the aggregate shifted sum as its
first Fourier coefficient, divided by pi. -/
theorem combinedHalfArc_fourierIdentity (t : ℕ) :
    (∫ y : UnitAddCircle,
      (combinedHalfArcExcess t y : ℂ) * fourier 1 y) =
        aggregateShiftedSum t / (Real.pi : ℂ) := by
  unfold combinedHalfArcExcess aggregateShiftedSum
  simp_rw [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  simp_rw [mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro h hh
    rw [MeasureTheory.integral_finsetSum]
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      rw [integral_const_mul, shiftedHalfArc_fourierIdentity]
      simp only [div_eq_mul_inv]
      have hcast : ((((H t - r : ℕ) : ℝ) : ℂ)) =
          (((H t - r : ℕ) : ℕ) : ℂ) := by norm_num
      rw [hcast]
      ac_rfl
    · intro r hr
      simpa only [mul_assoc] using
        (integrable_shiftedHalfArcExcess_mul_fourier t h r).const_mul
          (((H t - r : ℕ) : ℕ) : ℂ)
  · intro h hh
    apply integrable_finsetSum
    intro r hr
    simpa only [mul_assoc] using
      (integrable_shiftedHalfArcExcess_mul_fourier t h r).const_mul
        (((H t - r : ℕ) : ℕ) : ℂ)

theorem aggregateEnergy_eq_real_aggregateShiftedSum (t : ℕ) :
    aggregateEnergy t =
      10 * (H t : ℝ) * N t + 2 * (aggregateShiftedSum t).re := by
  unfold aggregateEnergy aggregateShiftedSum triangularEnergy
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  norm_num
  rw [← Finset.mul_sum]
  ring

theorem aggregateShiftedSum_re_le_of_combinedDiscrepancy
    {Delta : ℝ} (hDisc : CombinedHalfArcDiscrepancy Delta) (t : ℕ) :
    (aggregateShiftedSum t).re ≤
      Real.pi * Delta * (H t : ℝ) * N t := by
  rcases hDisc with ⟨hDelta, hDisc⟩
  have hid := combinedHalfArc_fourierIdentity t
  let B : ℝ := Delta * (H t : ℝ) * N t
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hnormInt :
      ‖∫ y : UnitAddCircle,
        (combinedHalfArcExcess t y : ℂ) * fourier 1 y‖ ≤ B := by
    calc
      ‖∫ y : UnitAddCircle,
          (combinedHalfArcExcess t y : ℂ) * fourier 1 y‖ ≤
          B * volume.real (Set.univ : Set UnitAddCircle) := by
            apply norm_integral_le_of_norm_le_const
            filter_upwards [] with y
            rw [norm_mul, Complex.norm_real, fourier_apply, Circle.norm_coe,
              mul_one]
            simpa only [B] using hDisc t y
      _ = B := by
        rw [measureReal_def, UnitAddCircle.measure_univ]
        norm_num
  have hnormDiv : ‖aggregateShiftedSum t / (Real.pi : ℂ)‖ ≤ B := by
    rw [← hid]
    exact hnormInt
  have hpiNorm : ‖(Real.pi : ℂ)‖ = Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hdiv : ‖aggregateShiftedSum t‖ / Real.pi ≤ B := by
    simpa only [norm_div, hpiNorm] using hnormDiv
  have hnorm : ‖aggregateShiftedSum t‖ ≤ Real.pi * B := by
    have := (div_le_iff₀ Real.pi_pos).mp hdiv
    nlinarith
  calc
    (aggregateShiftedSum t).re ≤ ‖aggregateShiftedSum t‖ :=
      Complex.re_le_norm _
    _ ≤ Real.pi * B := hnorm
    _ = Real.pi * Delta * (H t : ℝ) * N t := by simp [B]; ring

/-- A uniform displayed combined discrepancy bound implies the aggregate
threshold with explicit constant `10 + 2*pi*Delta`. -/
theorem combinedDiscrepancy_implies_aggregate
    {Delta : ℝ} (hDisc : CombinedHalfArcDiscrepancy Delta) :
    AggregateShiftedCorrelation (10 + 2 * Real.pi * Delta) := by
  rcases hDisc with ⟨hDelta, hDisc⟩
  refine ⟨by positivity, ?_⟩
  intro t
  rw [aggregateEnergy_eq_real_aggregateShiftedSum]
  have hre := aggregateShiftedSum_re_le_of_combinedDiscrepancy
    ⟨hDelta, hDisc⟩ t
  nlinarith

theorem combinedExplicitHalfArcExcess_centered
    (t : ℕ) (y : UnitAddCircle) :
    combinedExplicitHalfArcExcess t (.centered y) =
      combinedHalfArcExcess t y := by
  rfl

theorem combinedExplicitHalfArcExcess_complementary
    (t : ℕ) (y : UnitAddCircle) :
    combinedExplicitHalfArcExcess t (.complementary y) =
      -combinedHalfArcExcess t y := by
  unfold combinedExplicitHalfArcExcess combinedHalfArcExcess
  simp_rw [show ∀ h r : ℕ,
      shiftedExplicitHalfArcExcess t h r (.complementary y) =
        -shiftedHalfArcExcess t h r y by
    intro h r
    unfold shiftedExplicitHalfArcExcess shiftedHalfArcExcess shiftedHalfArcCount
    exact explicitHalfArcExcess_complementary
      (N t - r) (shiftedOrbitPoint h r) y]
  simp only [mul_neg, Finset.sum_neg_distrib]

/-- Literal failure of every aggregate constant yields, for every positive
normalization, one explicit half-open half-arc with positive pooled excess. -/
theorem aggregate_failure_implies_combinedHalfArcExcessCertificate
    (hFail : ¬ ∃ K : ℝ, AggregateShiftedCorrelation K) :
    ∀ Delta : ℝ, 0 < Delta →
      ∃ t : ℕ, ∃ A : HalfOpenHalfArc,
        Delta * (H t : ℝ) * N t < combinedExplicitHalfArcExcess t A := by
  intro Delta hDelta
  have hDelta0 : 0 ≤ Delta := hDelta.le
  have hnot : ¬ (∀ t : ℕ, ∀ y : UnitAddCircle,
      |combinedHalfArcExcess t y| ≤ Delta * (H t : ℝ) * N t) := by
    intro hall
    exact hFail ⟨10 + 2 * Real.pi * Delta,
      combinedDiscrepancy_implies_aggregate ⟨hDelta0, hall⟩⟩
  push Not at hnot
  rcases hnot with ⟨t, y, hviol⟩
  by_cases hnonneg : 0 ≤ combinedHalfArcExcess t y
  · refine ⟨t, .centered y, ?_⟩
    rw [combinedExplicitHalfArcExcess_centered]
    simpa [abs_of_nonneg hnonneg] using hviol
  · refine ⟨t, .complementary y, ?_⟩
    have hneg : combinedHalfArcExcess t y < 0 := lt_of_not_ge hnonneg
    rw [combinedExplicitHalfArcExcess_complementary]
    simpa [abs_of_neg hneg] using hviol

/-- T68's separate uniform single-shift discrepancy hypothesis implies the
new aggregate condition. The factor ten is explicit and no discrepancy
hypothesis is asserted. -/
theorem T68_uniformDiscrepancy_implies_aggregate
    {Delta : ℝ} (hDisc : UniformShiftedHalfArcDiscrepancy Delta) :
    AggregateShiftedCorrelation (10 * (1 + Real.pi * Delta)) := by
  have hFixed := uniformHalfArcDiscrepancy_implies_fixedPiShiftedCorrelation
    hDisc
  refine ⟨mul_nonneg (by norm_num) hFixed.1, ?_⟩
  intro t
  unfold aggregateEnergy
  calc
    (∑ h ∈ Finset.Icc (1 : ℕ) 10, triangularEnergy t h) ≤
        ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          (1 + Real.pi * Delta) * (H t : ℝ) * N t := by
            apply Finset.sum_le_sum
            intro h hh
            exact hFixed.2 t h hh
    _ = 10 * (1 + Real.pi * Delta) * (H t : ℝ) * N t := by
      simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      norm_num
      ring

/-- T63's exact selected-plus-defect recombination, exposed with every
lower-order term and the literal width. -/
theorem selectedDefectContribution_exact (Q0 t : ℕ) :
    selectedDefectContribution Q0 t =
      ((∑ h ∈ Finset.Icc (1 : ℕ) 10,
          X h (4 * 2 ^ t + 1) ^ 2) -
        4 * ((4 * 2 ^ t + 1 : ℕ) - 1) *
          (∑ h ∈ Finset.Icc (1 : ℕ) 10,
            X h (4 * 2 ^ t + 1)) +
        20 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
        30 * (4 * 2 ^ t + 1 : ℕ)) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1) := by
  exact selectedDefectContribution_eq_T63Polynomial Q0 t

/-- Conditional specialized primitive-sector budget obtained only from the
aggregate hypothesis and T63's exact selected-plus-defect identity. -/
theorem aggregate_implies_primitiveBudget
    {K : ℝ} (hAggregate : AggregateShiftedCorrelation K)
    (Q0 t : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (2 : ℝ) * (
      (∑ p ∈ selectedRecordDomain t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1)) +
      (∑ p ∈ unmatchedDefect Q0 t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤
      10 * ((45 / 16 : ℝ) * K ^ 2 + 5) *
        ((4 * 2 ^ t + 1 : ℕ) +
          (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s)) := by
  have hF := fourthMoment_le_of_aggregate hAggregate t
  have hN5 : (5 : ℝ) ≤ (4 * 2 ^ t + 1 : ℕ) := by
    exact_mod_cast five_le_N t
  have hN0 : (0 : ℝ) ≤ (4 * 2 ^ t + 1 : ℕ) := by positivity
  have hS0 : 0 ≤
      ∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1) := by
    apply Finset.sum_nonneg
    intro h hh
    exact Complex.normSq_nonneg _
  let n : ℝ := (4 * 2 ^ t + 1 : ℕ)
  let w : ℝ := Real.sqrt (n ^ 2 - 1)
  let B : ℝ := (9 / 4 : ℝ) * K ^ 2
  let A : ℝ := (45 / 16 : ℝ) * K ^ 2 + 5
  let target : ℝ := n + n ^ 2 * (10 : ℝ) ^ (-s)
  have hn5 : (5 : ℝ) ≤ n := hN5
  have hn0 : 0 ≤ n := hN0
  have hB0 : 0 ≤ B := by unfold B; positivity
  have hA0 : 0 ≤ A := by unfold A; positivity
  have hrad : 0 ≤ n ^ 2 - 1 := by nlinarith
  have hwpos : 0 < w := by
    unfold w
    exact Real.sqrt_pos.2 (by nlinarith)
  have hwLower : (4 / 5 : ℝ) * n ≤ w := by
    have hnm1 : 0 ≤ n - 1 := by nlinarith
    have hnm1w : n - 1 ≤ w := by
      unfold w
      apply (Real.le_sqrt hnm1 hrad).2
      nlinarith
    nlinarith
  have hpow : (1 / 10 : ℝ) ≤ (10 : ℝ) ^ (-s) := by
    have hexp : (-1 : ℝ) ≤ -s := by linarith
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 10) hexp
    rw [Real.rpow_neg_one] at hp
    norm_num at hp ⊢
    exact hp
  have htarget : n ^ 2 / 10 ≤ target := by
    unfold target
    have hsq0 : 0 ≤ n ^ 2 := sq_nonneg n
    calc
      n ^ 2 / 10 = n ^ 2 * (1 / 10 : ℝ) := by ring
      _ ≤ n ^ 2 * (10 : ℝ) ^ (-s) := by gcongr
      _ ≤ n + n ^ 2 * (10 : ℝ) ^ (-s) := by linarith
  have hpoly :
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          X h (4 * 2 ^ t + 1) ^ 2) -
          4 * ((4 * 2 ^ t + 1 : ℕ) - 1) *
            (∑ h ∈ Finset.Icc (1 : ℕ) 10,
              X h (4 * 2 ^ t + 1)) +
          20 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
          30 * (4 * 2 ^ t + 1 : ℕ) ≤
        (B + 4) * n ^ 3 := by
    have hF' : (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        X h (4 * 2 ^ t + 1) ^ 2) ≤ B * n ^ 3 := by
      simpa only [B, n] using hF
    change (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        X h (4 * 2 ^ t + 1) ^ 2) -
        4 * (n - 1) *
          (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1)) +
        20 * n ^ 2 - 30 * n ≤ (B + 4) * n ^ 3
    have hcoef : (0 : ℝ) ≤ 4 * (n - 1) := by nlinarith
    nlinarith [mul_nonneg hcoef hS0]
  change selectedDefectContribution Q0 t ≤
    10 * ((45 / 16 : ℝ) * K ^ 2 + 5) *
      ((4 * 2 ^ t + 1 : ℕ) +
        (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s))
  rw [selectedDefectContribution_exact Q0 t]
  apply (div_le_iff₀ hwpos).2
  calc
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        X h (4 * 2 ^ t + 1) ^ 2) -
        4 * ((4 * 2 ^ t + 1 : ℕ) - 1) *
          (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1)) +
        20 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
        30 * (4 * 2 ^ t + 1 : ℕ) ≤ (B + 4) * n ^ 3 := hpoly
    _ = 10 * A * (n ^ 2 / 10) * ((4 / 5 : ℝ) * n) := by
      unfold A B
      ring
    _ ≤ 10 * A * target * w := by gcongr
    _ = (10 * ((45 / 16 : ℝ) * K ^ 2 + 5) *
        ((4 * 2 ^ t + 1 : ℕ) +
          (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s))) *
            Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1) := by
      rfl

/-- Fully literal aggregate hypothesis and `N_t^3` consequence. -/
theorem literal_aggregate_implies_fourthMoment
    {K : ℝ} (hK : 0 ≤ K)
    (hAggregate : ∀ t : ℕ,
      10 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ) +
        2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          ∑ r ∈ Finset.Ico 1
              (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
            ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
              (∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I *
                    (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                      (Real.pi : ℂ))).re ≤
        K * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ))
    (t : ℕ) :
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
      X h (4 * 2 ^ t + 1) ^ 2) ≤
        (9 / 4 : ℝ) * K ^ 2 * (4 * 2 ^ t + 1 : ℕ) ^ 3 := by
  apply fourthMoment_le_of_aggregate
  refine ⟨hK, ?_⟩
  intro j
  rw [aggregateEnergy_literal]
  simpa only [N, H] using hAggregate j

/-- Fully literal aggregate hypothesis and conditional specialized
selected-plus-defect primitive-sector budget. -/
theorem literal_aggregate_implies_primitiveBudget
    {K : ℝ} (hK : 0 ≤ K)
    (hAggregate : ∀ t : ℕ,
      10 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ) +
        2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          ∑ r ∈ Finset.Ico 1
              (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
            ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
              (∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I *
                    (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                      (Real.pi : ℂ))).re ≤
        K * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ))
    (Q0 t : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (2 : ℝ) * (
      (∑ p ∈ selectedRecordDomain t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1)) +
      (∑ p ∈ unmatchedDefect Q0 t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤
      10 * ((45 / 16 : ℝ) * K ^ 2 + 5) *
        ((4 * 2 ^ t + 1 : ℕ) +
          (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s)) := by
  apply aggregate_implies_primitiveBudget
  · refine ⟨hK, ?_⟩
    intro j
    rw [aggregateEnergy_literal]
    simpa only [N, H] using hAggregate j
  · exact hs0
  · exact hs1

/-- Fully literal combined count, including the common half-open arc and the
complete `h/r/k` domains. -/
theorem combinedHalfArcCount_literal (t : ℕ) (y : UnitAddCircle) :
    combinedHalfArcCount t y =
      ∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
            (((@Finset.filter ℕ
              (fun k =>
                (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                  (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * Real.pi : ℝ) :
                    UnitAddCircle) - y) : ℝ) ∈
                  Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
              (Classical.decPred _)
              (Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))).card : ℕ) : ℝ) := by
  rfl

/-- Fully literal combined excess in the centered half-open half-arc. -/
theorem combinedHalfArcExcess_literal (t : ℕ) (y : UnitAddCircle) :
    combinedHalfArcExcess t y =
      ∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
            ((((@Finset.filter ℕ
                (fun k =>
                  (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                    (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * Real.pi : ℝ) :
                      UnitAddCircle) - y) : ℝ) ∈
                    Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
                (Classical.decPred _)
                (Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))).card : ℕ) : ℝ) -
              (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) / 2) := by
  rfl

/-- Fully literal exact total mass. -/
theorem combinedTotalMass_fully_literal (t : ℕ) :
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
      ∑ r ∈ Finset.Ico 1
          (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
        ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
          (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ)) =
      10 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
        ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) - 1) *
        (3 * ((4 * 2 ^ t + 1 : ℕ) : ℝ) -
          (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) - 1) / 6 := by
  simpa only [combinedTotalMass, N, H] using combinedTotalMass_exact t

/-- Fully literal displayed combined discrepancy implies the fully literal
aggregate threshold. -/
theorem literal_combinedDiscrepancy_implies_aggregate
    {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hDisc : ∀ t : ℕ, ∀ y : UnitAddCircle,
      abs (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
            ((((@Finset.filter ℕ
                (fun k =>
                  (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                    (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * Real.pi : ℝ) :
                      UnitAddCircle) - y) : ℝ) ∈
                    Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
                (Classical.decPred _)
                (Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))).card : ℕ) : ℝ) -
              (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) / 2)) ≤
        Delta * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ)) :
    0 ≤ 10 + 2 * Real.pi * Delta ∧
      ∀ t : ℕ,
        10 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
            (4 * 2 ^ t + 1 : ℕ) +
          2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
            ∑ r ∈ Finset.Ico 1
                (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
              ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
                (∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                  Complex.exp
                    (2 * (Real.pi : ℂ) * Complex.I *
                      (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                        (Real.pi : ℂ))).re ≤
          (10 + 2 * Real.pi * Delta) *
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
              (4 * 2 ^ t + 1 : ℕ) := by
  have hCombined : CombinedHalfArcDiscrepancy Delta := by
    refine ⟨hDelta, ?_⟩
    intro t y
    rw [combinedHalfArcExcess_literal]
    simpa only [N, H] using hDisc t y
  have hAggregate := combinedDiscrepancy_implies_aggregate hCombined
  refine ⟨hAggregate.1, ?_⟩
  intro t
  have ht := hAggregate.2 t
  rw [aggregateEnergy_literal] at ht
  simpa only [N, H] using ht

/-- Fully literal failure certificate: failure of every aggregate constant
forces one positive pooled excess in one explicit half-open half-arc. -/
theorem literal_aggregate_failure_implies_halfArcExcessCertificate
    (hFail : ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℕ,
      10 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ) +
        2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          ∑ r ∈ Finset.Ico 1
              (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
            ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
              (∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I *
                    (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                      (Real.pi : ℂ))).re ≤
        K * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ)) :
    ∀ Delta : ℝ, 0 < Delta →
      ∃ t : ℕ, ∃ A : HalfOpenHalfArc,
        Delta * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
            (4 * 2 ^ t + 1 : ℕ) <
          ∑ h ∈ Finset.Icc (1 : ℕ) 10,
            ∑ r ∈ Finset.Ico 1
                (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
              ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
                (((@Finset.filter ℕ
                    (fun k =>
                      match A with
                      | .centered y =>
                          (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                            (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) *
                              Real.pi : ℝ) : UnitAddCircle) - y) : ℝ) ∈
                            Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ)
                      | .complementary y =>
                          (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                            (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) *
                              Real.pi : ℝ) : UnitAddCircle) - y) : ℝ) ∉
                            Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
                    (Classical.decPred _)
                    (Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))).card : ℝ) -
                  (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) / 2) := by
  have hFail' : ¬ ∃ K : ℝ, AggregateShiftedCorrelation K := by
    intro hex
    apply hFail
    rcases hex with ⟨K, hK, hAggregate⟩
    refine ⟨K, hK, ?_⟩
    intro t
    have ht := hAggregate t
    rw [aggregateEnergy_literal] at ht
    simpa only [N, H] using ht
  simpa only [combinedExplicitHalfArcExcess, shiftedExplicitHalfArcExcess,
    explicitHalfArcExcess, explicitHalfArcCount, HalfOpenHalfArc.Contains,
    inHalfOpenHalfArc, inCenteredHalfArc, centeredRepresentative,
    shiftedOrbitPoint, shiftedFrequency, N, H] using
      aggregate_failure_implies_combinedHalfArcExcessCertificate hFail'

/-- T68's fully literal separate single-shift discrepancy hypothesis implies
the fully literal aggregate condition with constant `10*(1+pi*Delta)`. -/
theorem literal_T68_uniformDiscrepancy_implies_aggregate
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
              ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - 1 : ℕ) : ℝ)) :
    0 ≤ 10 * (1 + Real.pi * Delta) ∧
      ∀ t : ℕ,
        10 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
            (4 * 2 ^ t + 1 : ℕ) +
          2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
            ∑ r ∈ Finset.Ico 1
                (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
              ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
                (∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                  Complex.exp
                    (2 * (Real.pi : ℂ) * Complex.I *
                      (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                        (Real.pi : ℂ))).re ≤
          (10 * (1 + Real.pi * Delta)) *
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
              (4 * 2 ^ t + 1 : ℕ) := by
  have hUniform : UniformShiftedHalfArcDiscrepancy Delta := by
    refine ⟨hDelta, ?_⟩
    intro t h hh r hr y
    unfold shiftedHalfArcExcess shiftedHalfArcCount halfArcCount
      inHalfOpenHalfArc inCenteredHalfArc centeredRepresentative
      shiftedOrbitPoint shiftedFrequency N H
    convert hDisc t h hh r hr y using 1
  have hAggregate := T68_uniformDiscrepancy_implies_aggregate hUniform
  refine ⟨hAggregate.1, ?_⟩
  intro t
  have ht := hAggregate.2 t
  rw [aggregateEnergy_literal] at ht
  simpa only [N, H] using ht

end Theory.PiDigits.LongLagBlockCollisionDecay.T69

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.aggregateEnergy_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.summed_van_der_corput
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.literal_aggregate_implies_primitiveBudget
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.combinedHalfArc_fourierIdentity
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.combinedDiscrepancy_implies_aggregate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.aggregate_failure_implies_combinedHalfArcExcessCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.T68_uniformDiscrepancy_implies_aggregate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.selectedDefectContribution_exact
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.aggregate_implies_primitiveBudget
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.literal_aggregate_implies_fourthMoment
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.combinedHalfArcCount_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.combinedHalfArcExcess_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.combinedTotalMass_fully_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.literal_combinedDiscrepancy_implies_aggregate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.literal_aggregate_failure_implies_halfArcExcessCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T69.literal_T68_uniformDiscrepancy_implies_aggregate
