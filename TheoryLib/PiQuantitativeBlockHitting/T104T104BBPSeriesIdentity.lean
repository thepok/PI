import TheoryLib.PiQuantitativeBlockHitting.T103T103BBPIntegralBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# T104: the classical BBP series identity

This module justifies the interchange of the canonical nonnegative kernel
series with its interval integral.  Together with T102 and T103, this proves
that the canonical real BBP series has sum `Real.pi`.
-/

noncomputable section

namespace Theory.PiDigits.T104BBPSeriesIdentity

open T100BBPRealBridge T102BBPKernelIntegral T103BBPIntegralBridge

private theorem bbpKernel_intervalIntegrable :
    IntervalIntegrable bbpKernel MeasureTheory.volume 0 bbpUpper := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le bbpUpper_nonneg] at hx
  have hxlt : x < 1 := lt_of_le_of_lt hx.2 bbpUpper_lt_one
  have hx8 : x ^ 8 < 1 := pow_lt_one₀ hx.1 hxlt (by norm_num)
  have hd : 1 - x ^ 8 ≠ 0 := by nlinarith
  apply ContinuousAt.continuousWithinAt
  unfold bbpKernel bbpKernelNumerator
  fun_prop

/-- The canonical nonnegative kernel series may be integrated term by term. -/
theorem hasSum_intervalIntegral_bbpKernelTerm :
    HasSum
      (fun k : ℕ ↦ ∫ x in (0 : ℝ)..bbpUpper, bbpKernelTerm k x)
      (∫ x in (0 : ℝ)..bbpUpper, bbpKernel x) := by
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun k x ↦ bbpKernelTerm k x)
    (f := bbpKernel)
    (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := bbpUpper)
    (fun k x ↦ bbpKernelTerm k x)
    (fun k ↦ (by
      exact (by
        unfold bbpKernelTerm bbpKernelNumerator
        fun_prop : Continuous (bbpKernelTerm k)).aestronglyMeasurable))
    (by
      intro k
      filter_upwards with x hx
      rw [Set.mem_uIoc] at hx
      have hbounds : 0 ≤ x ∧ x ≤ bbpUpper := by
        rcases hx with h | h
        · exact ⟨h.1.le, h.2⟩
        · exfalso
          nlinarith [bbpUpper_nonneg]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (bbpKernelTerm_nonneg_on k x hbounds)])
    (by
      filter_upwards with x hx
      rw [Set.mem_uIoc] at hx
      have hbounds : 0 ≤ x ∧ x < 1 := by
        rcases hx with h | h
        · exact ⟨h.1.le, lt_of_le_of_lt h.2 bbpUpper_lt_one⟩
        · exfalso
          nlinarith [bbpUpper_nonneg]
      exact (bbpKernelTerm_hasSum x hbounds.1 hbounds.2).summable)
    (by
      apply bbpKernel_intervalIntegrable.congr
      intro x hx
      have hbounds : 0 ≤ x ∧ x < 1 := by
        rw [Set.mem_uIoc] at hx
        rcases hx with h | h
        · exact ⟨h.1.le, lt_of_le_of_lt h.2 bbpUpper_lt_one⟩
        · exfalso
          nlinarith [bbpUpper_nonneg]
      exact (bbpKernelTerm_hasSum x hbounds.1 hbounds.2).tsum_eq.symm)
    (by
      filter_upwards with x hx
      rw [Set.mem_uIoc] at hx
      have hbounds : 0 ≤ x ∧ x < 1 := by
        rcases hx with h | h
        · exact ⟨h.1.le, lt_of_le_of_lt h.2 bbpUpper_lt_one⟩
        · exfalso
          nlinarith [bbpUpper_nonneg]
      exact bbpKernelTerm_hasSum x hbounds.1 hbounds.2)

/-- The canonical real BBP series has sum `Real.pi`. -/
theorem bbpRealTerm_hasSum_pi : HasSum bbpRealTerm Real.pi := by
  have hseries : HasSum bbpRealTerm
      (∫ x in (0 : ℝ)..bbpUpper, bbpKernel x) := by
    simpa only [intervalIntegral_bbpKernelTerm] using
      hasSum_intervalIntegral_bbpKernelTerm
  rw [intervalIntegral_bbpKernel] at hseries
  exact hseries

/-- T100's digit-stability bridge now needs only its stated source input. -/
theorem pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      Theory.PiDigits.OversampledBBPGridStability.decimalBlockCode
          (bbpRealPartial (7 * N)) N m =
        Theory.PiDigits.OversampledBBPGridStability.decimalBlockCode
          Real.pi N m :=
  T100BBPRealBridge.pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq
    hSource bbpRealTerm_hasSum_pi

end Theory.PiDigits.T104BBPSeriesIdentity
