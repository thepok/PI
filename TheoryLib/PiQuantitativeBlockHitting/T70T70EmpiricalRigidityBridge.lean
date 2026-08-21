import TheoryLib.PiQuantitativeBlockHitting.T69T69FixedSixteenReturn
import TheoryLib.PiPositiveDecimalFactorEntropy.T39T39ErgodicAffinityRigidity

/-!
# T70: entropy-free empirical rigidity bridge

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module formalizes the conditional measure-to-topology bridge isolated by
the BBP empirical-measure audit.  It does not construct an empirical limit for
pi, prove that such a limit is ergodic or has infinite support, or prove
nonsingularity with its times-sixteen pushforward.  The infinite-support forms
consume `FurstenbergSourcePremise` explicitly; this file constructs no
inhabitant of that source premise.
-/

noncomputable section

open Set MeasureTheory Topology

namespace Theory.PiDigits.T70EmpiricalRigidityBridge

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T39ErgodicAffinityRigidity
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorEntropy.T65RationalCoreCertificate
open DecimalFactorEntropy.T77FixedWordCoreStabilization
open Theory.PiDigits.T69FixedSixteenReturn

/-- A continuous self-map preserving a measure maps its topological support
forward into itself. -/
theorem support_mapsTo_of_continuous_map_eq_self
    (f : UnitAddCircle → UnitAddCircle) (μ : Measure UnitAddCircle)
    (hf : Continuous f) (hmap : Measure.map f μ = μ) :
    MapsTo f μ.support μ.support := by
  intro x hx
  have hx' : ∀ U : Set UnitAddCircle, x ∈ U → IsOpen U → 0 < μ U := by
    simpa only [Measure.support_eq_forall_isOpen, Set.mem_setOf_eq] using hx
  rw [Measure.support_eq_forall_isOpen]
  change ∀ U : Set UnitAddCircle, f x ∈ U → IsOpen U → 0 < μ U
  intro U hfx hU
  have hpre : 0 < μ (f ⁻¹' U) :=
    hx' (f ⁻¹' U) hfx (hU.preimage hf)
  calc
    0 < Measure.map f μ U := by
      rw [Measure.map_apply hf.measurable hU.measurableSet]
      exact hpre
    _ = μ U := by rw [hmap]

/-- Absolute continuity of a continuous pushforward is already enough to map
the original support forward into itself.  Equality of the two measures is not
needed. -/
theorem support_mapsTo_of_continuous_map_absolutelyContinuous
    (f : UnitAddCircle → UnitAddCircle) (μ : Measure UnitAddCircle)
    (hf : Continuous f) (hac : Measure.map f μ ≪ μ) :
    MapsTo f μ.support μ.support := by
  intro x hx
  have hx' : ∀ U : Set UnitAddCircle, x ∈ U → IsOpen U → 0 < μ U := by
    simpa only [Measure.support_eq_forall_isOpen, Set.mem_setOf_eq] using hx
  have hfx : f x ∈ (Measure.map f μ).support := by
    rw [Measure.support_eq_forall_isOpen]
    change ∀ U : Set UnitAddCircle, f x ∈ U → IsOpen U →
      0 < Measure.map f μ U
    intro U hmem hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    exact hx' (f ⁻¹' U) hmem (hU.preimage hf)
  exact hac.support_mono hfx

/-- Ergodicity for multiplication by ten includes invariance, so the support
is forward invariant under multiplication by ten. -/
theorem support_timesTen_mapsTo
    (μ : Measure UnitAddCircle) (hTenErgodic : Ergodic timesTenMap μ) :
    MapsTo timesTenMap μ.support μ.support := by
  apply support_mapsTo_of_continuous_map_eq_self timesTenMap μ
  · simpa only [timesTenMap] using circleMul_continuous 10
  · exact hTenErgodic.toMeasurePreserving.map_eq

/-- Equality with the times-sixteen pushforward makes the support forward
invariant under multiplication by sixteen. -/
theorem support_timesSixteen_mapsTo
    (μ : Measure UnitAddCircle)
    (hSixteen : timesSixteenPushforward μ = μ) :
    MapsTo timesSixteenMap μ.support μ.support := by
  apply support_mapsTo_of_continuous_map_eq_self timesSixteenMap μ
  · simpa only [timesSixteenMap] using circleMul_continuous 16
  · simpa only [timesSixteenPushforward] using hSixteen

/-- Nonsingularity in the one-sided absolute-continuity direction already
makes the support forward invariant under multiplication by sixteen. -/
theorem support_timesSixteen_mapsTo_of_absolutelyContinuous
    (μ : Measure UnitAddCircle)
    (hac : timesSixteenPushforward μ ≪ μ) :
    MapsTo timesSixteenMap μ.support μ.support := by
  apply support_mapsTo_of_continuous_map_absolutelyContinuous
    timesSixteenMap μ
  · simpa only [timesSixteenMap] using circleMul_continuous 16
  · simpa only [timesSixteenPushforward] using hac

/-- The T39 ergodic-measure dichotomy turns non-mutual-singularity into exact
times-sixteen invariance. -/
theorem notMutuallySingular_implies_timesSixteen_invariant
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (hTenErgodic : Ergodic timesTenMap μ)
    (hnonsingular : ¬ μ ⟂ₘ timesSixteenPushforward μ) :
    timesSixteenPushforward μ = μ := by
  letI : IsProbabilityMeasure (timesSixteenPushforward μ) :=
    timesSixteenPushforward_isProbability μ
  have hPushErgodic : Ergodic timesTenMap (timesSixteenPushforward μ) :=
    timesSixteenPushforward_ergodic μ hTenErgodic
  exact (common_ergodic_not_mutuallySingular_eq timesTenMap μ
    (timesSixteenPushforward μ) hTenErgodic hPushErgodic hnonsingular).symm

/-- Forward invariance under the two generators contains the complete
times-ten/times-sixteen semigroup orbit of every point of the set. -/
theorem tenSixteenOrbit_subset_of_mapsTo
    (K : Set UnitAddCircle) (z : UnitAddCircle)
    (hTen : MapsTo timesTenMap K K)
    (hSixteen : MapsTo timesSixteenMap K K)
    (hz : z ∈ K) :
    tenSixteenOrbit z ⊆ K := by
  rintro _ ⟨s, t, rfl⟩
  have ht : circleMul (16 ^ t) z ∈ K := by
    induction t with
    | zero => simpa [circleMul] using hz
    | succ t iht =>
        have hnext := hSixteen iht
        change circleMul 16 (circleMul (16 ^ t) z) ∈ K at hnext
        simpa [circleMul_comp, pow_succ, Nat.mul_comm, Nat.mul_assoc] using hnext
  have hs : circleMul (10 ^ s) (circleMul (16 ^ t) z) ∈ K := by
    induction s with
    | zero => simpa [circleMul] using ht
    | succ s ihs =>
        have hnext := hTen ihs
        change circleMul 10 (circleMul (10 ^ s)
          (circleMul (16 ^ t) z)) ∈ K at hnext
        simpa [circleMul_comp, pow_succ, Nat.mul_comm, Nat.mul_assoc] using hnext
  simpa [circleMul_comp] using hs

/-- If one support point has dense joint orbit and the support is forward
invariant under both generators, then the support is the whole circle. -/
theorem dense_support_orbit_implies_support_eq_univ
    (μ : Measure UnitAddCircle) (z : UnitAddCircle)
    (hTen : MapsTo timesTenMap μ.support μ.support)
    (hSixteen : MapsTo timesSixteenMap μ.support μ.support)
    (hz : z ∈ μ.support)
    (hdense : Dense (tenSixteenOrbit z)) :
    μ.support = (Set.univ : Set UnitAddCircle) := by
  apply Set.eq_univ_of_univ_subset
  rw [← hdense.closure_eq]
  exact closure_minimal
    (tenSixteenOrbit_subset_of_mapsTo μ.support z hTen hSixteen hz)
    Measure.isClosed_support

/-- A compact infinite circle set that is forward invariant under
multiplication by ten and sixteen is the whole circle, conditional only on
the two source-shaped Furstenberg conclusions already isolated in T77. -/
theorem infinite_compact_common_invariant_eq_univ
    (hF : FurstenbergSourcePremise)
    (K : Set UnitAddCircle) (hcompact : IsCompact K) (hinfinite : K.Infinite)
    (hTen : MapsTo timesTenMap K K)
    (hSixteen : MapsTo timesSixteenMap K K) :
    K = (Set.univ : Set UnitAddCircle) := by
  by_cases hall : ∀ x ∈ K, IsRationalCirclePoint x
  · have hDcompact : IsCompact (differenceSet K) :=
      differenceSet_isCompact hcompact
    have hDfull : differenceSet K = (Set.univ : Set UnitAddCircle) :=
      hF.zero_accumulation_forces_univ _ hDcompact.isClosed
        (differenceSet_timesTen_mapsTo (by
          simpa [timesTenMap] using hTen))
        (differenceSet_timesSixteen_mapsTo (by
          simpa [timesSixteenMap, timesSixteenPoint] using hSixteen))
        (zero_accPt_differenceSet_of_infinite_compact hcompact hinfinite)
    have hsqrt : ((Real.sqrt 2 : ℝ) : UnitAddCircle) ∈ differenceSet K := by
      rw [hDfull]
      trivial
    rcases hsqrt with ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
    exfalso
    apply sqrtTwo_not_rationalCirclePoint
    rw [← hxy]
    exact rationalCirclePoint_sub (hall x hx) (hall y hy)
  · push_neg at hall
    obtain ⟨x, hx, hirrational⟩ := hall
    rcases hF.orbit_dense_or_rational x with hrational | hdense
    · exact (hirrational hrational).elim
    · apply Set.eq_univ_of_univ_subset
      rw [← hdense.closure_eq]
      exact closure_minimal
        (tenSixteenOrbit_subset_of_mapsTo K x hTen hSixteen hx)
        hcompact.isClosed

/-- Infinite support replaces an explicitly supplied dense support point in
the topological part of the empirical bridge. -/
theorem infinite_support_common_invariant_implies_support_eq_univ
    (hF : FurstenbergSourcePremise)
    (μ : Measure UnitAddCircle) (hinfinite : μ.support.Infinite)
    (hTen : MapsTo timesTenMap μ.support μ.support)
    (hSixteen : MapsTo timesSixteenMap μ.support μ.support) :
    μ.support = (Set.univ : Set UnitAddCircle) := by
  exact infinite_compact_common_invariant_eq_univ hF μ.support
    Measure.isClosed_support.isCompact hinfinite hTen hSixteen

/-- Probability mass one on the closed decimal orbit closure implies that the
topological support lies in that closure. -/
theorem support_subset_piOrbitClosure_of_measure_eq_one
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (hsupported : μ piOrbitClosure = 1) :
    μ.support ⊆ piOrbitClosure := by
  apply Measure.support_subset_of_isClosed piOrbitClosure_isClosed
  rw [mem_ae_iff]
  rw [measure_compl piOrbitClosure_isClosed.measurableSet
    (measure_ne_top μ piOrbitClosure), measure_univ, hsupported]
  simp

/-- The entropy-free empirical rigidity bridge with the support hypothesis in
its most direct topological form.  Every unresolved premise is explicit.

In particular, the theorem does not assert that the required measure or dense
support point exists for pi. -/
theorem pi_empirical_rigidity_bridge
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (hTenErgodic : Ergodic timesTenMap μ)
    (hsupported : μ.support ⊆ piOrbitClosure)
    (hnonsingular : ¬ μ ⟂ₘ timesSixteenPushforward μ)
    (z : UnitAddCircle) (hz : z ∈ μ.support)
    (hdense : Dense (tenSixteenOrbit z)) :
    timesSixteenPushforward μ = μ ∧
      μ.support = (Set.univ : Set UnitAddCircle) ∧
      piOrbitClosure = (Set.univ : Set UnitAddCircle) ∧
      Theory.PiDigits.V1 := by
  have hSixteen : timesSixteenPushforward μ = μ :=
    notMutuallySingular_implies_timesSixteen_invariant μ hTenErgodic hnonsingular
  have hSupportFull : μ.support = (Set.univ : Set UnitAddCircle) :=
    dense_support_orbit_implies_support_eq_univ μ z
      (support_timesTen_mapsTo μ hTenErgodic)
      (support_timesSixteen_mapsTo μ hSixteen) hz hdense
  have hK : piOrbitClosure = (Set.univ : Set UnitAddCircle) := by
    apply Set.eq_univ_of_univ_subset
    rw [← hSupportFull]
    exact hsupported
  exact ⟨hSixteen, hSupportFull, hK,
    piOrbitClosure_eq_univ_implies_v1 hK⟩

/-- Measure-one support form matching empirical weak-limit statements. -/
theorem pi_empirical_rigidity_bridge_of_measure_eq_one
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (hTenErgodic : Ergodic timesTenMap μ)
    (hsupported : μ piOrbitClosure = 1)
    (hnonsingular : ¬ μ ⟂ₘ timesSixteenPushforward μ)
    (z : UnitAddCircle) (hz : z ∈ μ.support)
    (hdense : Dense (tenSixteenOrbit z)) :
    timesSixteenPushforward μ = μ ∧
      μ.support = (Set.univ : Set UnitAddCircle) ∧
      piOrbitClosure = (Set.univ : Set UnitAddCircle) ∧
      Theory.PiDigits.V1 := by
  exact pi_empirical_rigidity_bridge μ hTenErgodic
    (support_subset_piOrbitClosure_of_measure_eq_one μ hsupported)
    hnonsingular z hz hdense

/-- Ergodicity, nonsingularity, and infinite support imply canonical V1,
conditional on the explicit Furstenberg source premise.  Unlike the earlier
bridge, no dense support point is supplied as a separate hypothesis. -/
theorem pi_ergodic_infinite_support_bridge
    (hF : FurstenbergSourcePremise)
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (hTenErgodic : Ergodic timesTenMap μ)
    (hsupported : μ.support ⊆ piOrbitClosure)
    (hnonsingular : ¬ μ ⟂ₘ timesSixteenPushforward μ)
    (hinfinite : μ.support.Infinite) :
    timesSixteenPushforward μ = μ ∧
      μ.support = (Set.univ : Set UnitAddCircle) ∧
      piOrbitClosure = (Set.univ : Set UnitAddCircle) ∧
      Theory.PiDigits.V1 := by
  have hSixteen : timesSixteenPushforward μ = μ :=
    notMutuallySingular_implies_timesSixteen_invariant μ hTenErgodic hnonsingular
  have hSupportFull : μ.support = (Set.univ : Set UnitAddCircle) :=
    infinite_support_common_invariant_implies_support_eq_univ hF μ hinfinite
      (support_timesTen_mapsTo μ hTenErgodic)
      (support_timesSixteen_mapsTo μ hSixteen)
  have hK : piOrbitClosure = (Set.univ : Set UnitAddCircle) := by
    apply Set.eq_univ_of_univ_subset
    rw [← hSupportFull]
    exact hsupported
  exact ⟨hSixteen, hSupportFull, hK,
    piOrbitClosure_eq_univ_implies_v1 hK⟩

/-- The nonergodic, one-sided version needed by density-one bounded-congestion
matching: times-ten invariance, absolute continuity of the times-sixteen
pushforward, and infinite support suffice.  All three remain explicit
hypotheses. -/
theorem pi_absolutelyContinuous_infinite_support_bridge
    (hF : FurstenbergSourcePremise)
    (μ : Measure UnitAddCircle)
    (hTenInvariant : Measure.map timesTenMap μ = μ)
    (hsupported : μ.support ⊆ piOrbitClosure)
    (hSixteenAc : timesSixteenPushforward μ ≪ μ)
    (hinfinite : μ.support.Infinite) :
    μ.support = (Set.univ : Set UnitAddCircle) ∧
      piOrbitClosure = (Set.univ : Set UnitAddCircle) ∧
      Theory.PiDigits.V1 := by
  have hSupportFull : μ.support = (Set.univ : Set UnitAddCircle) :=
    infinite_support_common_invariant_implies_support_eq_univ hF μ hinfinite
      (support_mapsTo_of_continuous_map_eq_self timesTenMap μ
        (by simpa only [timesTenMap] using circleMul_continuous 10)
        hTenInvariant)
      (support_timesSixteen_mapsTo_of_absolutelyContinuous μ hSixteenAc)
  have hK : piOrbitClosure = (Set.univ : Set UnitAddCircle) := by
    apply Set.eq_univ_of_univ_subset
    rw [← hSupportFull]
    exact hsupported
  exact ⟨hSupportFull, hK, piOrbitClosure_eq_univ_implies_v1 hK⟩

end Theory.PiDigits.T70EmpiricalRigidityBridge

#print axioms Theory.PiDigits.T70EmpiricalRigidityBridge.support_mapsTo_of_continuous_map_eq_self
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.support_mapsTo_of_continuous_map_absolutelyContinuous
#print axioms Theory.PiDigits.T70EmpiricalRigidityBridge.support_timesTen_mapsTo
#print axioms Theory.PiDigits.T70EmpiricalRigidityBridge.support_timesSixteen_mapsTo
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.support_timesSixteen_mapsTo_of_absolutelyContinuous
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.notMutuallySingular_implies_timesSixteen_invariant
#print axioms Theory.PiDigits.T70EmpiricalRigidityBridge.tenSixteenOrbit_subset_of_mapsTo
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.dense_support_orbit_implies_support_eq_univ
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.infinite_compact_common_invariant_eq_univ
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.infinite_support_common_invariant_implies_support_eq_univ
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.support_subset_piOrbitClosure_of_measure_eq_one
#print axioms Theory.PiDigits.T70EmpiricalRigidityBridge.pi_empirical_rigidity_bridge
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.pi_empirical_rigidity_bridge_of_measure_eq_one
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.pi_ergodic_infinite_support_bridge
#print axioms
  Theory.PiDigits.T70EmpiricalRigidityBridge.pi_absolutelyContinuous_infinite_support_bridge
