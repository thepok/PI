import TheoryLib.PiQuantitativeBlockHitting.T70T70EmpiricalRigidityBridge

/-!
Independent type-surface checks for the 2026-08-13 infinite-support extension
of T70.  These restatements deliberately pin the direction of absolute
continuity and every unresolved hypothesis of the two V1 bridges.
-/

noncomputable section

open Set MeasureTheory

namespace UltraPiT70IndependentChecks

open DecimalFactorEntropy.T39ErgodicAffinityRigidity
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorEntropy.T77FixedWordCoreStabilization
open Theory.PiDigits.T69FixedSixteenReturn
open Theory.PiDigits.T70EmpiricalRigidityBridge

/-- Guard the one-sided support lemma: the pushforward is absolutely
continuous with respect to the original measure, not conversely. -/
example (f : UnitAddCircle → UnitAddCircle) (mu : Measure UnitAddCircle)
    (hf : Continuous f) (hac : Measure.map f mu ≪ mu) :
    MapsTo f mu.support mu.support := by
  exact support_mapsTo_of_continuous_map_absolutelyContinuous f mu hf hac

/-- Guard the compact-set theorem's exact source, compactness, infinitude,
and forward-invariance assumptions. -/
example (hF : FurstenbergSourcePremise)
    (K : Set UnitAddCircle) (hcompact : IsCompact K) (hinfinite : K.Infinite)
    (hTen : MapsTo timesTenMap K K)
    (hSixteen : MapsTo timesSixteenMap K K) :
    K = (Set.univ : Set UnitAddCircle) := by
  exact infinite_compact_common_invariant_eq_univ
    hF K hcompact hinfinite hTen hSixteen

/-- Guard the ergodic V1 interface, including probability, support inclusion,
non-mutual-singularity, and infinite support. -/
example (hF : FurstenbergSourcePremise)
    (mu : Measure UnitAddCircle) [IsProbabilityMeasure mu]
    (hTenErgodic : Ergodic timesTenMap mu)
    (hsupported : mu.support ⊆
      DecimalFactorEntropy.TransversalEntropy.piOrbitClosure)
    (hnonsingular : ¬ mu ⟂ₘ timesSixteenPushforward mu)
    (hinfinite : mu.support.Infinite) :
    timesSixteenPushforward mu = mu ∧
      mu.support = (Set.univ : Set UnitAddCircle) ∧
      DecimalFactorEntropy.TransversalEntropy.piOrbitClosure =
        (Set.univ : Set UnitAddCircle) ∧
      Theory.PiDigits.V1 := by
  exact pi_ergodic_infinite_support_bridge hF mu hTenErgodic
    hsupported hnonsingular hinfinite

/-- Guard the nonergodic interface.  In particular, this uses
`map T16 mu ≪ mu`; it neither assumes nor concludes equality of those
measures. -/
example (hF : FurstenbergSourcePremise)
    (mu : Measure UnitAddCircle)
    (hTenInvariant : Measure.map timesTenMap mu = mu)
    (hsupported : mu.support ⊆
      DecimalFactorEntropy.TransversalEntropy.piOrbitClosure)
    (hSixteenAc : timesSixteenPushforward mu ≪ mu)
    (hinfinite : mu.support.Infinite) :
    mu.support = (Set.univ : Set UnitAddCircle) ∧
      DecimalFactorEntropy.TransversalEntropy.piOrbitClosure =
        (Set.univ : Set UnitAddCircle) ∧
      Theory.PiDigits.V1 := by
  exact pi_absolutelyContinuous_infinite_support_bridge hF mu
    hTenInvariant hsupported hSixteenAc hinfinite

end UltraPiT70IndependentChecks

#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.support_mapsTo_of_continuous_map_absolutelyContinuous
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.infinite_compact_common_invariant_eq_univ
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.infinite_support_common_invariant_implies_support_eq_univ
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.pi_ergodic_infinite_support_bridge
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.pi_absolutelyContinuous_infinite_support_bridge
