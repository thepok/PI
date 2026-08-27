import TheoryLib.PiPositiveLowerBlockDensity.T25T25ResidualPairReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD
import TheoryLib.PiLongLagBlockCollisionDecay.T31T31CrossBlockAlmostEverywhere
import TheoryLib.PiLongLagBlockCollisionDecay.T32T32AllBlockFixedPiRange
import TheoryLib.PiLongLagBlockCollisionDecay.T36T36SubcriticalCancellationSaving
import TheoryLib.PiLongLagBlockCollisionDecay.T49T49PrimitiveIncidenceAssembly
import TheoryLib.PiLongLagBlockCollisionDecay.T53T53PrefixFaithfulFiniteWords

/-!
# T79: public housekeeping bridges

The canonical local question is
`problems/local/pi-long-lag-block-collision-decay.txt`; it has no external
source URL. Its SHA-256 is
`db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.

This module adds only two pieces of reusable infrastructure: an explicit
expansion of the transitive T25 arithmetic exclusion used by the sparse
Fourier modules, and public finite instances supporting the T51-to-T53
interval-event cardinality bridge. The fixed-`pi` incidence estimates remain
explicit hypotheses in T34, T36, and T49; no such hypothesis is asserted here.
-/

noncomputable section

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T79

/-- The exact T25 arithmetic exclusion, with its structured denominator
expanded. This removes the need for clients to discover the definition through
T36's transitive imports. -/
theorem arithmeticExcluded_iff_explicit
    (μ c : ℝ) (Q0 m n r : ℕ) :
    Theory.PiDigits.PositiveLowerBlockDensity.T25.ArithmeticExcluded
        μ c Q0 m n r ↔
      Q0 ≤ 10 ^ n * (10 ^ r - 1) ∧
        ((10 : ℝ) ^ m)⁻¹ ≤
          ((10 ^ n * (10 ^ r - 1) : ℕ) : ℝ) *
            (c / (((10 ^ n * (10 ^ r - 1) : ℕ) : ℝ) ^ μ)) := by
  rfl

/-- T51 interval events are finite via T51's injective finite-word code. -/
noncomputable instance t51IntervalWordEventFinite
    (n : ℕ) (a b : ℝ) :
    Finite (T51.IntervalWordEvent n a b) :=
  Finite.of_injective
    (fun w => T51.finiteWordCode w.1)
    (by
      intro w v hwv
      apply Subtype.ext
      apply T51.finiteWordCode_injective n
      exact hwv)

/-- T53 interval events inherit finiteness through their checked injection into
the corresponding T51 event. -/
noncomputable instance t53IntervalWordEventFinite
    (n : ℕ) (a b : ℝ) :
    Finite (T53.IntervalWordEvent n a b) :=
  Finite.of_injective T53.intervalEventToCompleted
    (T53.intervalEventToCompleted_injective n a b)

/-- The cardinality comparison whose external use previously failed because
the T51 target event had no synthesizable `Finite` instance. -/
theorem t53_intervalWordEvent_card_le_t51
    (n : ℕ) (a b : ℝ) :
    Nat.card (T53.IntervalWordEvent n a b) ≤
      Nat.card (T51.IntervalWordEvent n a b) :=
  Nat.card_le_card_of_injective T53.intervalEventToCompleted
    (T53.intervalEventToCompleted_injective n a b)

-- Compile-time checks for the accepted endpoints used by the coverage map.
#check T16.longDifferenceMultiplicityWeightedGCD_le
#check T31.crossBlockWeightedGCD_le_explicit
#check T32.fixedPi_partialRange
#check T34.abs_inclusiveRealKernel_le_height_mul_shellWeight
#check T34.cancellingSector_norm_le_weightedShellIncidence
#check T36.canonical_blockLength_weight_budget
#check T36.restrictedWeightedShellIncidence_eq_direct
#check T36.ARI_super_iff_quantifiers
#check T36.ARI_superAt_implies_ARI_cancelAt
#check T49.primitiveSector_abs_le_weightedShellIncidence
#check T49.widthWeightedSquareFunction_le_of_three_obstructions
#check T49.mem_cancellingBlockDifferenceDomain_iff_six_rows
#check T49.cancellingWitness_image_eq_domain
#check T49.blockCancellingPositiveSum_eq_rows
#check T51.finiteWordCode_injective
#check T53.intervalEventToCompleted_injective
#check T53.intervalWordEvent_card_le_three

#print axioms arithmeticExcluded_iff_explicit
#print axioms t51IntervalWordEventFinite
#print axioms t53IntervalWordEventFinite
#print axioms t53_intervalWordEvent_card_le_t51

end Theory.PiDigits.LongLagBlockCollisionDecay.T79
