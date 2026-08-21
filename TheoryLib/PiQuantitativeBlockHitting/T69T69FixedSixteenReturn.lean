import TheoryLib.PiQuantitativeBlockHitting.T68T68HuttonSimultaneousPrimary
import TheoryLib.PiPositiveDecimalFactorEntropy.T77T77FixedWordCoreStabilization

/-!
# T69: a fixed times-sixteen return is exactly the Furstenberg bottleneck

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module formalizes the topological reduction used by the resumed proof
search.  It does not prove the return.  Its reverse implication takes exactly
the density of the times-ten/times-sixteen orbit of pi as an explicit premise.
Furstenberg's source theorem supplies that premise informally, but it is not
formalized or introduced as an axiom here.
-/

noncomputable section

open Set Topology

namespace Theory.PiDigits.T69FixedSixteenReturn

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorEntropy.T65RationalCoreCertificate
open DecimalFactorEntropy.T77FixedWordCoreStabilization
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- The single cross-base return whose proof would settle canonical V1. -/
def FixedSixteenReturn : Prop :=
  circleMul 16 (piCircleOrbit 0) ∈ piOrbitClosure

/-- Metric sequential form of the fixed return.  The quantifier is over all
positive radii, so a finite computation cannot establish it. -/
theorem fixedSixteenReturn_iff_metric :
    FixedSixteenReturn ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ n : ℕ,
          dist (circleMul 16 (piCircleOrbit 0)) (piCircleOrbit n) < ε := by
  rw [FixedSixteenReturn, piOrbitClosure, Metric.mem_closure_range_iff]

/-- Every decimal orbit point is the corresponding power-of-ten multiple of
the initial circle point. -/
theorem piCircleOrbit_eq_circleMul_powTen (n : ℕ) :
    piCircleOrbit n = circleMul (10 ^ n) (piCircleOrbit 0) := by
  unfold piCircleOrbit circleMul
  rw [← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul, pow_zero, one_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- A fixed return makes the closed decimal orbit forward invariant under
multiplication by sixteen. -/
theorem piOrbitClosure_timesSixteen_mapsTo
    (hreturn : FixedSixteenReturn) :
    MapsTo (circleMul 16) piOrbitClosure piOrbitClosure := by
  have hrange : MapsTo (circleMul 16) (Set.range piCircleOrbit)
      piOrbitClosure := by
    rintro _ ⟨n, rfl⟩
    rw [piCircleOrbit_eq_circleMul_powTen, circleMul_commute]
    exact piOrbitClosure_timesTen_iterate _ hreturn n
  exact hrange.closure_left (circleMul_continuous 16) piOrbitClosure_isClosed

/-- Under the fixed return, the full forward times-ten/times-sixteen orbit of
the initial pi point stays inside the decimal orbit closure. -/
theorem tenSixteenOrbit_pi_subset_piOrbitClosure
    (hreturn : FixedSixteenReturn) :
    tenSixteenOrbit (piCircleOrbit 0) ⊆ piOrbitClosure := by
  rintro _ ⟨s, t, rfl⟩
  have ht : circleMul (16 ^ t) (piCircleOrbit 0) ∈ piOrbitClosure := by
    induction t with
    | zero =>
        simpa [circleMul] using
          (subset_closure (Set.mem_range_self 0) :
            piCircleOrbit 0 ∈ piOrbitClosure)
    | succ t iht =>
        have hnext := piOrbitClosure_timesSixteen_mapsTo hreturn iht
        change circleMul 16 (circleMul (16 ^ t) (piCircleOrbit 0)) ∈
          piOrbitClosure at hnext
        simpa [circleMul_comp, pow_succ, Nat.mul_comm, Nat.mul_assoc] using hnext
  have hs : circleMul (10 ^ s) (circleMul (16 ^ t) (piCircleOrbit 0)) ∈
      piOrbitClosure := piOrbitClosure_timesTen_iterate _ ht s
  simpa [circleMul_comp] using hs

/-- Density of the joint times-ten/times-sixteen pi orbit turns the one fixed
return into the whole circle.  This is the exact minimal topological premise
used by the proof. -/
theorem fixedSixteenReturn_implies_piOrbitClosure_eq_univ
    (hdense : Dense (tenSixteenOrbit (piCircleOrbit 0)))
    (hreturn : FixedSixteenReturn) :
    piOrbitClosure = (Set.univ : Set UnitAddCircle) := by
  apply Set.eq_univ_of_univ_subset
  rw [← hdense.closure_eq]
  exact closure_minimal
    (tenSixteenOrbit_pi_subset_piOrbitClosure hreturn)
    piOrbitClosure_isClosed

/-- A full decimal circle-orbit closure hits the explicit open inner ball of
every word cylinder and therefore proves the exact list-valued V1 statement. -/
theorem piOrbitClosure_eq_univ_implies_v1
    (hfull : piOrbitClosure = (Set.univ : Set UnitAddCircle)) :
    Theory.PiDigits.V1 := by
  intro w
  have hcenter : (decimalCylinderCenter w : UnitAddCircle) ∈ piOrbitClosure := by
    rw [hfull]
    trivial
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    (Metric.mem_closure_iff.mp hcenter)
      (decimalCylinderInnerRadius w)
      (decimalCylinderInnerRadius_pos w)
  have hball : piCircleOrbit n ∈
      Metric.ball (decimalCylinderCenter w : UnitAddCircle)
        (decimalCylinderInnerRadius w) := by
    simpa only [Metric.mem_ball, dist_comm] using hn
  refine ⟨n, ?_⟩
  intro i hi
  exact piCircleOrbit_mem_innerBall_implies_blockMatch w n hball ⟨i, hi⟩

/-- Canonical V1 itself supplies the fixed return, with no Furstenberg premise
needed in this direction. -/
theorem v1_implies_fixedSixteenReturn
    (hV1 : Theory.PiDigits.V1) : FixedSixteenReturn := by
  have hdense := Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense.mp hV1
  let y : ℝ := unitCoordinate (circleMul 16 (piCircleOrbit 0))
  have hy : y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨unitCoordinate_nonneg _, (unitCoordinate_lt_one _).le⟩
  rw [FixedSixteenReturn, piOrbitClosure, Metric.mem_closure_range_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := hdense y hy ε hε
  refine ⟨n, ?_⟩
  rw [← coe_unitCoordinate (circleMul 16 (piCircleOrbit 0))]
  change dist (y : UnitAddCircle)
    ((((10 : ℝ) ^ n * Real.pi : ℝ)) : UnitAddCircle) < ε
  rw [← AddCircle.coe_fract ((10 : ℝ) ^ n * Real.pi),
    dist_eq_norm, ← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm.trans_lt (by
    simpa [Real.norm_eq_abs, abs_sub_comm] using hn)

/-- Exact conditional equivalence under the one joint-orbit density statement
that Furstenberg's source theorem supplies for pi.  This theorem does not
formalize that source theorem or prove either side. -/
theorem v1_iff_fixedSixteenReturn
    (hdense : Dense (tenSixteenOrbit (piCircleOrbit 0))) :
    Theory.PiDigits.V1 ↔ FixedSixteenReturn := by
  constructor
  · exact v1_implies_fixedSixteenReturn
  · intro hreturn
    exact piOrbitClosure_eq_univ_implies_v1
      (fixedSixteenReturn_implies_piOrbitClosure_eq_univ hdense hreturn)

end Theory.PiDigits.T69FixedSixteenReturn

#print axioms Theory.PiDigits.T69FixedSixteenReturn.fixedSixteenReturn_iff_metric
#print axioms Theory.PiDigits.T69FixedSixteenReturn.piCircleOrbit_eq_circleMul_powTen
#print axioms Theory.PiDigits.T69FixedSixteenReturn.piOrbitClosure_timesSixteen_mapsTo
#print axioms Theory.PiDigits.T69FixedSixteenReturn.tenSixteenOrbit_pi_subset_piOrbitClosure
#print axioms Theory.PiDigits.T69FixedSixteenReturn.fixedSixteenReturn_implies_piOrbitClosure_eq_univ
#print axioms Theory.PiDigits.T69FixedSixteenReturn.piOrbitClosure_eq_univ_implies_v1
#print axioms Theory.PiDigits.T69FixedSixteenReturn.v1_implies_fixedSixteenReturn
#print axioms Theory.PiDigits.T69FixedSixteenReturn.v1_iff_fixedSixteenReturn
