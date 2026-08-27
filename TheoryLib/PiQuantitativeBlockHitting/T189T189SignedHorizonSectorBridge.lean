import TheoryLib.PiQuantitativeBlockHitting.T178T178SignedPredecessorRay
import TheoryLib.PiQuantitativeBlockHitting.T179T179PredecessorLagOneCorrelation

/-!
# T189: exact signed horizon-sector bridge

This module subtracts the T177 predecessor-sector identities at two horizons.
The resulting nonzero-sector increment is then rewritten by T179 as one
literal lag-one correlation over the new orbit block.  The final theorem is
the direct one-sided inequality sufficient for positive child surplus at the
larger horizon.  No cancellation estimate is asserted.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.SignedHorizonSectorBridge

open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PositiveLeftExtensionTransport
open Theory.PiDigits.PredecessorDigitDFT
open Theory.PiDigits.PredecessorLagOneCorrelation
open Theory.PiDigits.SignedBlockBellmanTransport
open Theory.PiDigits.SignedPredecessorRay

abbrev phase := Theory.PiDigits.T27.phase
abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- Increment of the transported zero predecessor sector between horizons
`N` and `H`. -/
def predecessorZeroBlockIncrement (q A N H : Nat) : Real :=
  (predecessorDigitSector q A H 0 -
    predecessorDigitSector q A N 0).re

/-- Increment of the nine digit-sensitive predecessor sectors for child
digit `d` between horizons `N` and `H`. -/
def predecessorNonzeroBlockIncrement (q A N H d : Nat) : Real :=
  predecessorNonzeroContribution q A H d -
    predecessorNonzeroContribution q A N d

/-- The zero-sector block is exactly the parent-score block plus the T172
transport-remainder block. -/
theorem predecessorZeroBlockIncrement_eq_parent_add_remainder
    (q A N H : Nat) :
    predecessorZeroBlockIncrement q A N H =
      ((primitiveBoundaryFourierSum q A H -
          primitiveBoundaryFourierSum q A N) +
        (leftExtensionRemainder q A H -
          leftExtensionRemainder q A N)).re := by
  unfold predecessorZeroBlockIncrement
  rw [predecessorDigitSector_zero, predecessorDigitSector_zero]
  congr 1
  ring

/-- Subtracting the two T177 child reconstructions splits the exact child
block score into its zero and nonzero predecessor sectors. -/
theorem ten_mul_childBlock_re_eq_zeroBlock_add_nonzeroBlock
    (q A N H d : Nat) (hd : d < 10) :
    10 * (primitiveBoundaryFourierSum (10 * q) (A + d * q) H -
      primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re =
        predecessorZeroBlockIncrement q A N H +
          predecessorNonzeroBlockIncrement q A N H d := by
  have hH := ten_mul_child_re_eq_zeroSector_add_nonzero q A H d hd
  have hN := ten_mul_child_re_eq_zeroSector_add_nonzero q A N d hd
  unfold predecessorZeroBlockIncrement predecessorNonzeroBlockIncrement
  simp only [Complex.sub_re]
  linarith

/-- The single shifted lag-one correlation that contains all nine nonzero
predecessor characters over orbit indices `N, ..., H - 1`. -/
def shiftedLagOneBlockCorrelation (q A N H d : Nat) : Complex :=
  ∑ n ∈ Ico N H,
    ∑ r ∈ (Icc 1 9 : Finset Nat),
      phase (-(r : Int)) ((d : Real) / 10) *
        (phase (r : Int) ((predecessorDigit n : Real) / 10) *
          predecessorSuffixKernel q r
            (piOrbit (n + 1) - decimalCylinderCenter q A))

/-- T179 turns the complete nonzero-sector block into the one shifted
lag-one correlation above. -/
theorem predecessorNonzeroBlockIncrement_eq_shiftedLagOneCorrelation_re
    (q A N H d : Nat) (hq : 0 < q) (hNH : N ≤ H) :
    predecessorNonzeroBlockIncrement q A N H d =
      (shiftedLagOneBlockCorrelation q A N H d).re := by
  have hsector (r : Nat) (hr : r ∈ (Icc 1 9 : Finset Nat)) :
      predecessorDigitSector q A H r - predecessorDigitSector q A N r =
        ∑ n ∈ Ico N H,
          phase (r : Int) ((predecessorDigit n : Real) / 10) *
            predecessorSuffixKernel q r
              (piOrbit (n + 1) - decimalCylinderCenter q A) := by
    have hr0 : 0 < r := by simpa using (mem_Icc.mp hr).1
    have hr9 : r ≤ 9 := (mem_Icc.mp hr).2
    have hr10 : r < 10 := by omega
    rw [predecessorDigitSector_eq_lagOneCorrelation q A H r hq hr0 hr10,
      predecessorDigitSector_eq_lagOneCorrelation q A N r hq hr0 hr10]
    exact (sum_Ico_eq_sub _ hNH).symm
  unfold predecessorNonzeroBlockIncrement predecessorNonzeroContribution
  rw [← Complex.sub_re, ← Finset.sum_sub_distrib]
  unfold shiftedLagOneBlockCorrelation
  rw [Finset.sum_comm]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro r hr
  rw [← mul_sub, hsector r hr, Finset.mul_sum]

/-- Exact one-sided horizon criterion.  If the old child score plus its zero
and nonzero sector increments dominates the larger-horizon potential, the
child has positive T178 signed prefix surplus at horizon `H`. -/
theorem signedPrefixSurplus_child_pos_of_horizon_sector_gt
    (q A N H d : Nat) (hq : 0 < q) (hNH : N ≤ H) (hd : d < 10)
    (hsector :
      H * signedBlockPotential (10 * q) <
        (10 * q : Nat) *
            (primitiveBoundaryFourierSum
              (10 * q) (A + d * q) N).re +
          q * (predecessorZeroBlockIncrement q A N H +
            (shiftedLagOneBlockCorrelation q A N H d).re)) :
    0 < signedPrefixSurplus (10 * q) (A + d * q) H := by
  have hnonzero :=
    predecessorNonzeroBlockIncrement_eq_shiftedLagOneCorrelation_re
      q A N H d hq hNH
  rw [← hnonzero] at hsector
  have hblock := ten_mul_childBlock_re_eq_zeroBlock_add_nonzeroBlock
    q A N H d hd
  have hscaled :
      (q : Real) * (predecessorZeroBlockIncrement q A N H +
          predecessorNonzeroBlockIncrement q A N H d) =
        ((10 * q : Nat) : Real) *
            (primitiveBoundaryFourierSum
              (10 * q) (A + d * q) H).re -
          ((10 * q : Nat) : Real) *
            (primitiveBoundaryFourierSum
              (10 * q) (A + d * q) N).re := by
    rw [← hblock]
    simp only [Complex.sub_re]
    push_cast
    ring
  unfold signedPrefixSurplus
  push_cast at hsector ⊢
  rw [hscaled] at hsector
  norm_num [Nat.cast_mul] at hsector ⊢
  nlinarith

end Theory.PiDigits.SignedHorizonSectorBridge

#print axioms Theory.PiDigits.SignedHorizonSectorBridge.predecessorZeroBlockIncrement_eq_parent_add_remainder
#print axioms Theory.PiDigits.SignedHorizonSectorBridge.ten_mul_childBlock_re_eq_zeroBlock_add_nonzeroBlock
#print axioms Theory.PiDigits.SignedHorizonSectorBridge.predecessorNonzeroBlockIncrement_eq_shiftedLagOneCorrelation_re
#print axioms Theory.PiDigits.SignedHorizonSectorBridge.signedPrefixSurplus_child_pos_of_horizon_sector_gt
