import TheoryLib.PiLongLagBlockCollisionDecay.T7T7FiniteBernoulliCollisions
import TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T12T12ScaleMatchedSpectralFrontier
import TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD

/-!
# T75: housekeeping bridges

Canonical local source: `problems/local/pi-long-lag-block-collision-decay.txt`
(this locally formulated problem has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module adds the direct composition missing from the earlier T11 telemetry.
Every fixed-`pi` estimate remains an explicit premise. In particular, neither
the scale-matched squared-energy predicate nor the canonical collision claim is
asserted unconditionally.

The other T75 telemetry entries are already covered by imported public
declarations or source-pinned artifacts. Their exact mappings are recorded in
`T75_HOUSEKEEPING_MAP.md`; they are not duplicated here.
-/

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T75

open Theory.PiDigits.LongLagBlockCollisionDecay
open Theory.PiDigits.LongLagBlockCollisionDecay.T2
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- T12's scale-dependent squared-energy premise implies the exact T2
residual predicate once T2's effective-irrationality premise is supplied.
The proof uses T12's public `B_s = sqrt A_s` conversion and retains T2's
quantifier order `forall s, exists C_s, forall positive m,N`. -/
theorem scaleMatchedSquaredEnergyBound_implies_T2
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (henergy : ScaleMatchedSquaredEnergyBound μ c Q0) :
    PiUniformLongLagResidualPairDecay μ c Q0 := by
  exact scaleMatchedL1Bound_implies_T2 hIrr
    (scaleMatchedSquaredEnergyBound_implies_L1 henergy)

/-- Conditional canonical transfer of the scale-dependent squared-energy
premise. This is only a bridge: `hIrr` and `henergy` remain hypotheses. -/
theorem scaleMatchedSquaredEnergyBound_implies_C1
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (henergy : ScaleMatchedSquaredEnergyBound μ c Q0) :
    PiLongLagBlockCollisionDecay := by
  exact piUniformLongLagResidualPairDecay_implies_C1
    (scaleMatchedSquaredEnergyBound_implies_T2 hIrr henergy)

end Theory.PiDigits.LongLagBlockCollisionDecay.T75

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T75.scaleMatchedSquaredEnergyBound_implies_T2
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T75.scaleMatchedSquaredEnergyBound_implies_C1
