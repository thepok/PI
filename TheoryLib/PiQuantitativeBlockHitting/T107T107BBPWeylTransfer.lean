import TheoryLib.PiQuantitativeBlockHitting.T106T106BBPForcedOrbit

/-!
# T107: Weyl transfer for the seven-step BBP forced orbit

The canonical T106 BBP error and forcing tend to zero, and the forcing is
summable.  More importantly, at every fixed integer frequency the phase
discrepancy between the sevenfold-sampled BBP orbit and the unwrapped decimal
pi orbit is absolutely summable.  A generic summable-perturbation argument
therefore identifies real Weyl cancellation for the two orbits.

This module proves no cancellation, density, normality, digit occurrence, or
V1 statement unconditionally.  The final V1 implication retains Weyl
cancellation of the sampled BBP orbit as an explicit premise.
-/

noncomputable section

namespace Theory.PiDigits.T107BBPWeylTransfer

open Finset Filter
open scoped ComplexConjugate Real Topology
open Theory.PiDigits.T106BBPForcedOrbit

/-- The decimal-scaled BBP approximation error tends to zero. -/
theorem tendsto_sampledBBPError_zero :
    Tendsto sampledBBPError atTop (nhds 0) :=
  summable_sampledBBPError.tendsto_atTop_zero

/-- The positive forcing is bounded above by ten times the current scaled
BBP error. -/
theorem sampledBBPForcing_le_ten_mul_error (N : ℕ) :
    sampledBBPForcing N ≤ 10 * sampledBBPError N := by
  have hcoboundary := sampledBBPForcing_eq_error_coboundary N
  have hnext : 0 ≤ sampledBBPError (N + 1) := sampledBBPError_nonneg (N + 1)
  linarith

private theorem sampledBBPForcing_nonneg (N : ℕ) :
    0 ≤ sampledBBPForcing N :=
  (sampledBBPForcing_pos N).le

/-- The seven-step BBP forcing is summable. -/
theorem summable_sampledBBPForcing : Summable sampledBBPForcing := by
  refine Summable.of_nonneg_of_le sampledBBPForcing_nonneg
    sampledBBPForcing_le_ten_mul_error ?_
  exact Summable.mul_left 10 summable_sampledBBPError

/-- The seven-step BBP forcing tends to zero. -/
theorem tendsto_sampledBBPForcing_zero :
    Tendsto sampledBBPForcing atTop (nhds 0) :=
  summable_sampledBBPForcing.tendsto_atTop_zero

/-- At frequency `h`, the phase discrepancy is bounded by `2 * pi * |h|`
times the scaled BBP error. -/
theorem norm_phase_pi_sub_phase_sampledBBP_le (h : ℤ) (N : ℕ) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ N * Real.pi) -
        Theory.PiDigits.T27.phase h (sampledBBPOrbit N)‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) * sampledBBPError N := by
  have hphase :=
    DecimalFactorComplexity.FixedDecimalPeriodicBlocks.norm_phase_sub_phase_le
      h ((10 : ℝ) ^ N * Real.pi)
        ((10 : ℝ) ^ N * sampledBBPValue N)
  have horbit : Theory.PiDigits.T27.phase h (sampledBBPOrbit N) =
      Theory.PiDigits.T27.phase h
        ((10 : ℝ) ^ N * sampledBBPValue N) := by
    exact Theory.PiDigits.T29.phase_fract_eq_phase h
      ((10 : ℝ) ^ N * sampledBBPValue N)
  rw [horbit]
  have habs :
      |(10 : ℝ) ^ N * Real.pi -
          (10 : ℝ) ^ N * sampledBBPValue N| =
        sampledBBPError N := by
    rw [sampledBBPError]
    have hnonneg : 0 ≤ (10 : ℝ) ^ N *
        (Real.pi - sampledBBPValue N) := sampledBBPError_nonneg N
    rw [← abs_of_nonneg hnonneg]
    congr 1
    ring
  simpa only [habs] using hphase

/-- At every fixed integer frequency, the phase discrepancy between the
decimal pi orbit and the sampled BBP orbit is absolutely summable. -/
theorem summable_norm_phase_pi_sub_phase_sampledBBP (h : ℤ) :
    Summable (fun N : ℕ =>
      ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ N * Real.pi) -
        Theory.PiDigits.T27.phase h (sampledBBPOrbit N)‖) := by
  apply Summable.of_nonneg_of_le (fun N => norm_nonneg _)
    (fun N => norm_phase_pi_sub_phase_sampledBBP_le h N)
  exact Summable.mul_left (2 * Real.pi * (h.natAbs : ℝ))
    summable_sampledBBPError

private lemma norm_partialSum_difference_le_tsum
    (x y : ℕ → ℝ) (h : ℤ)
    (hs : Summable (fun n : ℕ =>
      ‖Theory.PiDigits.T27.phase h (x n) -
        Theory.PiDigits.T27.phase h (y n)‖))
    (M : ℕ) :
    ‖∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
      ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)‖ ≤
      ∑' n : ℕ,
        ‖Theory.PiDigits.T27.phase h (x n) -
          Theory.PiDigits.T27.phase h (y n)‖ := by
  rw [← sum_sub_distrib]
  calc
    ‖∑ k ∈ range M,
        (Theory.PiDigits.T27.phase h (x k) -
          Theory.PiDigits.T27.phase h (y k))‖ ≤
        ∑ k ∈ range M,
          ‖Theory.PiDigits.T27.phase h (x k) -
            Theory.PiDigits.T27.phase h (y k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑' n : ℕ,
        ‖Theory.PiDigits.T27.phase h (x n) -
          Theory.PiDigits.T27.phase h (y n)‖ :=
      hs.sum_le_tsum (range M) fun k _ => norm_nonneg _

private lemma norm_normalized_difference_le
    (x y : ℕ → ℝ) (h : ℤ)
    (hs : Summable (fun n : ℕ =>
      ‖Theory.PiDigits.T27.phase h (x n) -
        Theory.PiDigits.T27.phase h (y n)‖))
    (M : ℕ) :
    ‖(M : ℂ)⁻¹ *
        (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
          ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k))‖ ≤
      (M : ℝ)⁻¹ * (∑' n : ℕ,
          ‖Theory.PiDigits.T27.phase h (x n) -
            Theory.PiDigits.T27.phase h (y n)‖) := by
  calc
    ‖(M : ℂ)⁻¹ *
        (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
          ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k))‖ ≤
        ‖(M : ℂ)⁻¹‖ *
          ‖∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
            ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)‖ :=
      norm_mul_le _ _
    _ ≤ ‖(M : ℂ)⁻¹‖ *
        (∑' n : ℕ,
            ‖Theory.PiDigits.T27.phase h (x n) -
              Theory.PiDigits.T27.phase h (y n)‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_partialSum_difference_le_tsum x y h hs M) (norm_nonneg _)
    _ = (M : ℝ)⁻¹ * (∑' n : ℕ,
          ‖Theory.PiDigits.T27.phase h (x n) -
            Theory.PiDigits.T27.phase h (y n)‖) := by
      simp

private lemma tendsto_normalized_difference_zero
    (x y : ℕ → ℝ) (h : ℤ)
    (hs : Summable (fun n : ℕ =>
      ‖Theory.PiDigits.T27.phase h (x n) -
        Theory.PiDigits.T27.phase h (y n)‖)) :
    Tendsto
      (fun M : ℕ => (M : ℂ)⁻¹ *
        (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
          ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)))
      atTop (nhds 0) := by
  let C : ℝ := ∑' n : ℕ,
    ‖Theory.PiDigits.T27.phase h (x n) -
      Theory.PiDigits.T27.phase h (y n)‖
  have hbound (M : ℕ) :
      ‖(M : ℂ)⁻¹ *
        (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
          ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k))‖ ≤
        (M : ℝ)⁻¹ * C :=
    norm_normalized_difference_le x y h hs M
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun M => norm_nonneg _) (fun M => hbound M)
  simpa only [zero_mul] using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C

/-- For real sequences, summability of every fixed-frequency phase
discrepancy makes real Weyl cancellation invariant under the perturbation. -/
theorem realWeylCancellation_iff_of_summable_phase_discrepancy
    (x y : ℕ → ℝ)
    (hsummable : ∀ h : ℤ,
      Summable (fun n : ℕ =>
        ‖Theory.PiDigits.T27.phase h (x n) -
          Theory.PiDigits.T27.phase h (y n)‖)) :
    Theory.PiDigits.T26.RealWeylCancellation x ↔
      Theory.PiDigits.T26.RealWeylCancellation y := by
  have key : ∀ h : ℤ,
      Tendsto
        (fun M : ℕ => (M : ℂ)⁻¹ *
          (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
            ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)))
        atTop (nhds 0) := fun h =>
    tendsto_normalized_difference_zero x y h (hsummable h)
  constructor
  · intro hx h hh
    change Tendsto
      (fun M : ℕ => (M : ℂ)⁻¹ *
        ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k))
      atTop (nhds 0)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpt (M : ℕ) :
        (M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k) =
          (M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
            (M : ℂ)⁻¹ *
              (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
                ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)) := by
      ring
    have hnorm (M : ℕ) :
        ‖(M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)‖ ≤
          ‖(M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k)‖ +
            ‖(M : ℂ)⁻¹ *
              (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
                ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k))‖ := by
      rw [hpt M]
      exact norm_sub_le _ _
    refine squeeze_zero (fun M => norm_nonneg _) hnorm ?_
    have hxnorm := tendsto_zero_iff_norm_tendsto_zero.mp (hx h hh)
    have hdiffnorm := tendsto_zero_iff_norm_tendsto_zero.mp (key h)
    simpa using hxnorm.add hdiffnorm
  · intro hy h hh
    change Tendsto
      (fun M : ℕ => (M : ℂ)⁻¹ *
        ∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k))
      atTop (nhds 0)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpt (M : ℕ) :
        (M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) =
          (M : ℂ)⁻¹ *
              (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
                ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)) +
            (M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k) := by
      ring
    have hnorm (M : ℕ) :
        ‖(M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k)‖ ≤
          ‖(M : ℂ)⁻¹ *
              (∑ k ∈ range M, Theory.PiDigits.T27.phase h (x k) -
                ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k))‖ +
            ‖(M : ℂ)⁻¹ * ∑ k ∈ range M, Theory.PiDigits.T27.phase h (y k)‖ := by
      rw [hpt M]
      exact norm_add_le _ _
    refine squeeze_zero (fun M => norm_nonneg _) hnorm ?_
    have hdiffnorm := tendsto_zero_iff_norm_tendsto_zero.mp (key h)
    have hynorm := tendsto_zero_iff_norm_tendsto_zero.mp (hy h hh)
    simpa using hdiffnorm.add hynorm

/-- Real Weyl cancellation for the sampled BBP orbit is equivalent to real
Weyl cancellation for the ordinary unwrapped decimal pi orbit. -/
theorem realWeylCancellation_sampledBBP_iff_pi :
    Theory.PiDigits.T26.RealWeylCancellation sampledBBPOrbit ↔
      Theory.PiDigits.T26.RealWeylCancellation
        (fun N => (10 : ℝ) ^ N * Real.pi) := by
  exact (realWeylCancellation_iff_of_summable_phase_discrepancy
    (fun N => (10 : ℝ) ^ N * Real.pi) sampledBBPOrbit
    summable_norm_phase_pi_sub_phase_sampledBBP).symm

/-- Conditional endpoint: real Weyl cancellation for the sampled BBP orbit,
kept as an explicit premise, implies canonical V1. -/
theorem sampledBBP_weylCancellation_implies_canonicalV1
    (hcancel : Theory.PiDigits.T26.RealWeylCancellation sampledBBPOrbit) :
    Theory.PiDigits.V1 :=
  Theory.PiDigits.T26.pi_baseTen_weylCancellation_implies_canonicalV1
    (realWeylCancellation_sampledBBP_iff_pi.mp hcancel)

end Theory.PiDigits.T107BBPWeylTransfer
