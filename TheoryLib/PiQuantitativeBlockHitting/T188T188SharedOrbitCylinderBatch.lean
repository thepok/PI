import TheoryLib.PiQuantitativeBlockHitting.T186T186ReflectedTrigLeaf

/-!
# T188: share one certified orbit cylinder across several phase leaves

T184 deliberately makes a phase request self-contained.  In a production
kernel shard, however, three requests use the same `piOrbit n` cylinder.  A
literal batch of T186 leaves therefore recomputes the large T173 suffix
remainder three times.

This file factors that work at the checker boundary.  An orbit cylinder is
checked once.  Any number of phase requests are then checked against its
stored rational endpoints.  Soundness reconstructs the ordinary T184
validity proposition symbolically, so the existing T184 and T186 semantic
theorems are reused without executing their expensive original phase checker.
-/

namespace Theory.PiDigits.T188SharedOrbitCylinderBatch

open Theory.PiDigits.T171CompactFixedPointCertificate
open Theory.PiDigits.T173MachinIntegerCertificate10015
open Theory.PiDigits.T182ReflectedStackProgram
open Theory.PiDigits.T183ReflectedExpHorner
open Theory.PiDigits.T184CertifiedPiPhaseRequest
open Theory.PiDigits.T184CertifiedPiPhaseRequest.PhaseRequest
open Theory.PiDigits.T186ReflectedTrigLeaf

noncomputable section

/-- Cached T173 suffix data for one orbit index. -/
structure OrbitCylinderCertificate where
  orbitIndex : Nat
  denominator : Nat
  lowerNumerator : Nat
deriving DecidableEq, Repr

namespace OrbitCylinderCertificate

def lower (c : OrbitCylinderCertificate) : Rat :=
  c.lowerNumerator / c.denominator

def upper (c : OrbitCylinderCertificate) : Rat :=
  (c.lowerNumerator + 1) / c.denominator

end OrbitCylinderCertificate

/-- The only expensive suffix remainder is evaluated here, once per orbit
group. -/
def checkOrbitCylinder (c : OrbitCylinderCertificate) : Bool :=
  decide (c.orbitIndex ≤ certifiedPiPlaces) &&
  decide (c.denominator = 10 ^ (certifiedPiPlaces - c.orbitIndex)) &&
  decide (c.lowerNumerator = certifiedPiPrefix % c.denominator)

structure OrbitCylinderCertificate.Valid (c : OrbitCylinderCertificate) : Prop where
  index_le : c.orbitIndex ≤ certifiedPiPlaces
  denominator_eq : c.denominator = 10 ^ (certifiedPiPlaces - c.orbitIndex)
  numerator_eq : c.lowerNumerator = certifiedPiPrefix % c.denominator

theorem orbitCylinder_valid_of_check {c : OrbitCylinderCertificate}
    (hc : checkOrbitCylinder c = true) : c.Valid := by
  simp only [checkOrbitCylinder, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

/-- Cycle endpoints computed from the cached cylinder rather than from the
T173 prefix. -/
def cycleLowerAt (c : OrbitCylinderCertificate) (r : PhaseRequest) : Rat :=
  r.multiplier * c.lower + r.offset - r.centeredTurn

def cycleUpperAt (c : OrbitCylinderCertificate) (r : PhaseRequest) : Rat :=
  r.multiplier * c.upper + r.offset - r.centeredTurn

def angleCornersAt (c : OrbitCylinderCertificate) (r : PhaseRequest) : List Rat :=
  [2 * piLower * cycleLowerAt c r, 2 * piLower * cycleUpperAt c r,
    2 * piUpper * cycleLowerAt c r, 2 * piUpper * cycleUpperAt c r]

/-- Cheap per-phase geometry checker.  It contains no decimal-prefix modulo. -/
def checkPhaseAtCylinder (c : OrbitCylinderCertificate) (r : PhaseRequest) : Bool :=
  decide (r.orbitIndex = c.orbitIndex) &&
  decide (0 < r.multiplierDenominator) &&
  decide (0 < r.offsetDenominator) &&
  decide (0 < r.centerDenominator) &&
  decide (0 < r.radiusDenominator) &&
  decide ((-1 / 2 : Rat) ≤ cycleLowerAt c r) &&
  decide (cycleUpperAt c r ≤ (1 / 2 : Rat)) &&
  (angleCornersAt c r).all (fun z => decide
    (r.angleCenter - r.angleRadius ≤ z ∧
      z ≤ r.angleCenter + r.angleRadius)) &&
  decide (|r.angleCenter| ≤ 4)

private theorem checkPhaseRequest_of_valid {r : PhaseRequest} (hv : r.Valid) :
    checkPhaseRequest r = true := by
  rcases hv with ⟨hm, ho, hc, hr, hn, hcl, hcu, hcorners, hsmall⟩
  simp only [checkPhaseRequest, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hm, ho⟩, hc⟩, hr⟩, hn⟩, hcl⟩, hcu⟩, ?_⟩, hsmall⟩
  intro z hz
  exact hcorners z hz

/-- The cheap cached check implies the original self-contained T184 check,
but this implication is proved symbolically and does not form part of the
executable batch checker. -/
theorem checkPhaseRequest_of_checkAtCylinder
    {c : OrbitCylinderCertificate} {r : PhaseRequest}
    (hc : checkOrbitCylinder c = true)
    (hr : checkPhaseAtCylinder c r = true) :
    checkPhaseRequest r = true := by
  have cv := orbitCylinder_valid_of_check hc
  simp only [checkPhaseAtCylinder, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hr
  rcases hr with ⟨⟨⟨⟨⟨⟨⟨⟨hindex, hm⟩, ho⟩, hcenter⟩, hradius⟩,
    hcl⟩, hcu⟩, hcorners⟩, hsmall⟩
  have hscale : c.denominator = r.suffixScale := by
    rw [cv.denominator_eq]
    unfold suffixScale
    rw [hindex]
  have hlower : c.lower = r.orbitLower := by
    unfold OrbitCylinderCertificate.lower orbitLower suffixNumerator suffixScale
    rw [cv.numerator_eq, hscale]
    rfl
  have hupper : c.upper = r.orbitUpper := by
    unfold OrbitCylinderCertificate.upper orbitUpper suffixNumerator suffixScale
    rw [cv.numerator_eq, hscale]
    rfl
  have hcycleLower : cycleLowerAt c r = r.cycleLower := by
    unfold cycleLowerAt cycleLower
    rw [hlower]
  have hcycleUpper : cycleUpperAt c r = r.cycleUpper := by
    unfold cycleUpperAt cycleUpper
    rw [hupper]
  apply checkPhaseRequest_of_valid
  refine ⟨hm, ho, hcenter, hradius, ?_, ?_, ?_, ?_, hsmall⟩
  · simpa [hindex] using cv.index_le
  · rwa [← hcycleLower]
  · rwa [← hcycleUpper]
  · intro z hz
    apply hcorners z
    simpa [angleCornersAt, angleCorners, hcycleLower, hcycleUpper] using hz

/-- T186's leaf checker with its expensive T184 component replaced by the
cached-cylinder check. -/
def checkTrigLeafAtCylinder
    (c : OrbitCylinderCertificate) (leaf : TrigLeafCertificate) : Bool :=
  checkPhaseAtCylinder c leaf.request &&
  checkHorner leaf.horner &&
  decide (8 ≤ leaf.horner.terms) &&
  decide (leaf.horner.centerNumerator = leaf.request.centerNumerator) &&
  decide (leaf.horner.centerDenominator = leaf.request.centerDenominator) &&
  decide ((leaf.cosineLeaf.lower : Rat) / leaf.horner.scale ≤
    (leaf.horner.claimed.re.lower : Rat) / leaf.horner.scale - leaf.error) &&
  decide ((leaf.horner.claimed.re.upper : Rat) / leaf.horner.scale + leaf.error ≤
    (leaf.cosineLeaf.upper : Rat) / leaf.horner.scale) &&
  decide ((leaf.sineLeaf.lower : Rat) / leaf.horner.scale ≤
    (leaf.horner.claimed.im.lower : Rat) / leaf.horner.scale - leaf.error) &&
  decide ((leaf.horner.claimed.im.upper : Rat) / leaf.horner.scale + leaf.error ≤
    (leaf.sineLeaf.upper : Rat) / leaf.horner.scale)

theorem checkedTrigLeafAtCylinder_sound
    {c : OrbitCylinderCertificate} {leaf : TrigLeafCertificate}
    (hc : checkOrbitCylinder c = true)
    (hl : checkTrigLeafAtCylinder c leaf = true) :
    StackRel leaf.horner.scale leaf.rows leaf.values := by
  simp only [checkTrigLeafAtCylinder, Bool.and_eq_true, decide_eq_true_eq] at hl
  rcases hl with ⟨⟨⟨⟨⟨⟨⟨⟨hphase, hhorner⟩, hn⟩, hnum⟩, hden⟩,
    hcosL⟩, hcosU⟩, hsinL⟩, hsinU⟩
  have holdPhase := checkPhaseRequest_of_checkAtCylinder hc hphase
  apply checkedTrigLeaf_sound
  simp only [checkTrigLeaf, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨holdPhase, hhorner⟩, hn⟩, hnum⟩, hden⟩,
    hcosL⟩, hcosU⟩, hsinL⟩, hsinU⟩

/-- One orbit cylinder with all trigonometric leaves that reuse it. -/
structure OrbitTrigGroupCertificate where
  cylinder : OrbitCylinderCertificate
  scale : Nat
  leaves : List TrigLeafCertificate
deriving DecidableEq, Repr

namespace OrbitTrigGroupCertificate

def rows (g : OrbitTrigGroupCertificate) : List FixedInterval :=
  g.leaves.flatMap TrigLeafCertificate.rows

def values (g : OrbitTrigGroupCertificate) : List Real :=
  g.leaves.flatMap TrigLeafCertificate.values

end OrbitTrigGroupCertificate

def checkOrbitTrigGroup (g : OrbitTrigGroupCertificate) : Bool :=
  checkOrbitCylinder g.cylinder &&
  g.leaves.all (fun leaf =>
    checkTrigLeafAtCylinder g.cylinder leaf &&
      decide (leaf.horner.scale = g.scale))

private theorem checkedLeafListAtCylinder_sound
    {c : OrbitCylinderCertificate} {scale : Nat}
    {leaves : List TrigLeafCertificate}
    (hc : checkOrbitCylinder c = true)
    (hl : leaves.all (fun leaf =>
      checkTrigLeafAtCylinder c leaf &&
        decide (leaf.horner.scale = scale)) = true) :
    StackRel scale
      (leaves.flatMap TrigLeafCertificate.rows)
      (leaves.flatMap TrigLeafCertificate.values) := by
  induction leaves with
  | nil => exact .nil
  | cons leaf leaves ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
      rcases hl with ⟨⟨hleaf, hscale⟩, htail⟩
      have hhead := checkedTrigLeafAtCylinder_sound hc hleaf
      rw [hscale] at hhead
      simpa only [List.flatMap_cons] using List.rel_append hhead (ih htail)

/-- One cylinder check followed by one induction certifies all phase leaves
for that orbit index. -/
theorem checkedOrbitTrigGroup_sound {g : OrbitTrigGroupCertificate}
    (hg : checkOrbitTrigGroup g = true) :
    StackRel g.scale g.rows g.values := by
  simp only [checkOrbitTrigGroup, Bool.and_eq_true] at hg
  exact checkedLeafListAtCylinder_sound hg.1 hg.2

/-- A production batch of orbit groups sharing the fixed-point scale consumed
by one reflected stack program.  Each group still checks its expensive suffix
cylinder exactly once. -/
structure OrbitTrigGroupBatchCertificate where
  scale : Nat
  groups : List OrbitTrigGroupCertificate
deriving DecidableEq, Repr

namespace OrbitTrigGroupBatchCertificate

def rows (b : OrbitTrigGroupBatchCertificate) : List FixedInterval :=
  b.groups.flatMap OrbitTrigGroupCertificate.rows

def values (b : OrbitTrigGroupBatchCertificate) : List Real :=
  b.groups.flatMap OrbitTrigGroupCertificate.values

end OrbitTrigGroupBatchCertificate

/-- Executable production checker: check every cached-cylinder group and
align every group with the batch's single stack scale. -/
def checkOrbitTrigGroupBatch (b : OrbitTrigGroupBatchCertificate) : Bool :=
  b.groups.all fun g =>
    checkOrbitTrigGroup g && decide (g.scale = b.scale)

private theorem checkedOrbitTrigGroupList_sound {scale : Nat}
    {groups : List OrbitTrigGroupCertificate}
    (hcheck : groups.all (fun g =>
      checkOrbitTrigGroup g && decide (g.scale = scale)) = true) :
    StackRel scale
      (groups.flatMap OrbitTrigGroupCertificate.rows)
      (groups.flatMap OrbitTrigGroupCertificate.values) := by
  induction groups with
  | nil => exact .nil
  | cons group groups ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨hgroup, hscale⟩, htail⟩
      have hhead := checkedOrbitTrigGroup_sound hgroup
      rw [hscale] at hhead
      simpa only [List.flatMap_cons] using List.rel_append hhead (ih htail)

/-- One outer induction concatenates the group relations into the flat leaf
table expected by T182. -/
theorem checkedOrbitTrigGroupBatch_sound
    {b : OrbitTrigGroupBatchCertificate}
    (hb : checkOrbitTrigGroupBatch b = true) :
    StackRel b.scale b.rows b.values := by
  exact checkedOrbitTrigGroupList_sound hb

end

end Theory.PiDigits.T188SharedOrbitCylinderBatch

#print axioms Theory.PiDigits.T188SharedOrbitCylinderBatch.checkPhaseRequest_of_checkAtCylinder
#print axioms Theory.PiDigits.T188SharedOrbitCylinderBatch.checkedTrigLeafAtCylinder_sound
#print axioms Theory.PiDigits.T188SharedOrbitCylinderBatch.checkedOrbitTrigGroup_sound
#print axioms Theory.PiDigits.T188SharedOrbitCylinderBatch.checkedOrbitTrigGroupBatch_sound
