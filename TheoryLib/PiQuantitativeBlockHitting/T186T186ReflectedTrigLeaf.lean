import TheoryLib.PiQuantitativeBlockHitting.T184T184CertifiedPiPhaseRequest
import TheoryLib.PiQuantitativeBlockHitting.T182T182ReflectedStackProgram

/-!
# T186: checked trigonometric leaves for reflected stack programs

This module joins one checked T184 phase request to one checked T183 Horner
certificate.  The generated cosine and sine rows include the exact rational
input-radius and Taylor-remainder padding, and are returned directly in the
`StackRel` form consumed by T182.
-/

namespace Theory.PiDigits.T186ReflectedTrigLeaf

open Theory.PiDigits.T171CompactFixedPointCertificate
open Theory.PiDigits.T180ReflectedTrigIntervalCore
open Theory.PiDigits.T181ReflectedIntervalArithmetic
open Theory.PiDigits.T182ReflectedStackProgram
open Theory.PiDigits.T183ReflectedExpHorner
open Theory.PiDigits.T184CertifiedPiPhaseRequest
open Theory.PiDigits.T184CertifiedPiPhaseRequest.PhaseRequest

noncomputable section

/-- Exact rational form of T180's uniform Taylor remainder. -/
def rationalTrigRemainder (n : Nat) : Rat :=
  2 * 4 ^ n / n.factorial

theorem rationalTrigRemainder_cast (n : Nat) :
    (rationalTrigRemainder n : Real) = trigRemainder n := by
  unfold rationalTrigRemainder trigRemainder
  push_cast
  rfl

/-- One pair of reflected trigonometric leaves. -/
structure TrigLeafCertificate where
  request : PhaseRequest
  horner : HornerCertificate
  cosineLeaf : FixedInterval
  sineLeaf : FixedInterval
deriving DecidableEq, Repr

namespace TrigLeafCertificate

def error (c : TrigLeafCertificate) : Rat :=
  c.request.angleRadius + rationalTrigRemainder c.horner.terms

/-- Rows in the order expected by a generated T182 leaf table. -/
def rows (c : TrigLeafCertificate) : List FixedInterval :=
  [c.cosineLeaf, c.sineLeaf]

def values (c : TrigLeafCertificate) : List Real :=
  [Real.cos c.request.originalAngle, Real.sin c.request.originalAngle]

end TrigLeafCertificate

/-- The combined checker recomputes both component checks and all alignment
and padding comparisons. -/
def checkTrigLeaf (c : TrigLeafCertificate) : Bool :=
  checkPhaseRequest c.request &&
  checkHorner c.horner &&
  decide (8 ≤ c.horner.terms) &&
  decide (c.horner.centerNumerator = c.request.centerNumerator) &&
  decide (c.horner.centerDenominator = c.request.centerDenominator) &&
  decide ((c.cosineLeaf.lower : Rat) / c.horner.scale ≤
    (c.horner.claimed.re.lower : Rat) / c.horner.scale - c.error) &&
  decide ((c.horner.claimed.re.upper : Rat) / c.horner.scale + c.error ≤
    (c.cosineLeaf.upper : Rat) / c.horner.scale) &&
  decide ((c.sineLeaf.lower : Rat) / c.horner.scale ≤
    (c.horner.claimed.im.lower : Rat) / c.horner.scale - c.error) &&
  decide ((c.horner.claimed.im.upper : Rat) / c.horner.scale + c.error ≤
    (c.sineLeaf.upper : Rat) / c.horner.scale)

/-- A successful combined leaf certificate supplies exactly the pointwise
leaf relation required by T182. -/
theorem checkedTrigLeaf_sound {c : TrigLeafCertificate}
    (hc : checkTrigLeaf c = true) :
    StackRel c.horner.scale c.rows c.values := by
  simp only [checkTrigLeaf, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with
    ⟨⟨⟨⟨⟨⟨⟨⟨hrequest, hhorner⟩, hn⟩, hnum⟩, hden⟩, hcosL⟩, hcosU⟩,
      hsinL⟩, hsinU⟩
  have hphase := checkedPhaseRequest_trig_input hrequest
  have hcenterEq :
      (c.request.angleCenter : Real) =
        (c.horner.centerNumerator : Real) / c.horner.centerDenominator := by
    unfold angleCenter
    rw [hnum, hden]
    norm_cast
  have htrig := checkedHorner_trig_bounds hn hphase.2.1 hphase.1
    hhorner rfl hcenterEq
  have hsNat : 0 < c.horner.scale := by
    simp only [checkHorner, Bool.and_eq_true, decide_eq_true_eq] at hhorner
    exact hhorner.1.1.1
  have hs : (0 : Real) < c.horner.scale := by exact_mod_cast hsNat
  have herr : (c.error : Real) =
      (c.request.angleRadius : Real) + trigRemainder c.horner.terms := by
    unfold TrigLeafCertificate.error
    push_cast
    rw [rationalTrigRemainder_cast]
  have hcosLR : (c.cosineLeaf.lower : Real) / c.horner.scale ≤
      (c.horner.claimed.re.lower : Real) / c.horner.scale -
        ((c.request.angleRadius : Real) + trigRemainder c.horner.terms) := by
    have hcosLR' : (c.cosineLeaf.lower : Real) / c.horner.scale ≤
        (c.horner.claimed.re.lower : Real) / c.horner.scale - (c.error : Real) := by
      exact_mod_cast hcosL
    rwa [herr] at hcosLR'
  have hcosUR : (c.horner.claimed.re.upper : Real) / c.horner.scale +
      ((c.request.angleRadius : Real) + trigRemainder c.horner.terms) ≤
        (c.cosineLeaf.upper : Real) / c.horner.scale := by
    have hcosUR' : (c.horner.claimed.re.upper : Real) / c.horner.scale +
        (c.error : Real) ≤ (c.cosineLeaf.upper : Real) / c.horner.scale := by
      exact_mod_cast hcosU
    rwa [herr] at hcosUR'
  have hsinLR : (c.sineLeaf.lower : Real) / c.horner.scale ≤
      (c.horner.claimed.im.lower : Real) / c.horner.scale -
        ((c.request.angleRadius : Real) + trigRemainder c.horner.terms) := by
    have hsinLR' : (c.sineLeaf.lower : Real) / c.horner.scale ≤
        (c.horner.claimed.im.lower : Real) / c.horner.scale - (c.error : Real) := by
      exact_mod_cast hsinL
    rwa [herr] at hsinLR'
  have hsinUR : (c.horner.claimed.im.upper : Real) / c.horner.scale +
      ((c.request.angleRadius : Real) + trigRemainder c.horner.terms) ≤
        (c.sineLeaf.upper : Real) / c.horner.scale := by
    have hsinUR' : (c.horner.claimed.im.upper : Real) / c.horner.scale +
        (c.error : Real) ≤ (c.sineLeaf.upper : Real) / c.horner.scale := by
      exact_mod_cast hsinU
    rwa [herr] at hsinUR'
  have hcosNorm : (c.cosineLeaf.lower : Real) / c.horner.scale ≤
        Real.cos c.request.originalAngle ∧
      Real.cos c.request.originalAngle ≤
        (c.cosineLeaf.upper : Real) / c.horner.scale := by
    rw [hphase.2.2.1]
    exact ⟨hcosLR.trans htrig.1, htrig.2.1.trans hcosUR⟩
  have hsinNorm : (c.sineLeaf.lower : Real) / c.horner.scale ≤
        Real.sin c.request.originalAngle ∧
      Real.sin c.request.originalAngle ≤
        (c.sineLeaf.upper : Real) / c.horner.scale := by
    rw [hphase.2.2.2]
    exact ⟨hsinLR.trans htrig.2.2.1, htrig.2.2.2.trans hsinUR⟩
  unfold TrigLeafCertificate.rows TrigLeafCertificate.values StackRel
  constructor
  · unfold EnclosesReal
    constructor
    · simpa [mul_comm] using (div_le_iff₀ hs).mp hcosNorm.1
    · simpa [mul_comm] using (le_div_iff₀ hs).mp hcosNorm.2
  constructor
  · unfold EnclosesReal
    constructor
    · simpa [mul_comm] using (div_le_iff₀ hs).mp hsinNorm.1
    · simpa [mul_comm] using (le_div_iff₀ hs).mp hsinNorm.2
  · exact .nil

/-- The checked trigonometric pair can be prepended to any independently
related reflected leaf table. -/
theorem checkedTrigLeaf_cons {c : TrigLeafCertificate}
    {tailRows : List FixedInterval} {tailValues : List Real}
    (hc : checkTrigLeaf c = true)
    (htail : StackRel c.horner.scale tailRows tailValues) :
    StackRel c.horner.scale (c.rows ++ tailRows) (c.values ++ tailValues) := by
  exact List.rel_append (checkedTrigLeaf_sound hc) htail

/-- A batch of trigonometric leaves sharing the fixed-point scale consumed by
one reflected stack program. -/
structure TrigLeafBatchCertificate where
  scale : Nat
  leaves : List TrigLeafCertificate
deriving DecidableEq, Repr

namespace TrigLeafBatchCertificate

def rows (b : TrigLeafBatchCertificate) : List FixedInterval :=
  b.leaves.flatMap TrigLeafCertificate.rows

def values (b : TrigLeafBatchCertificate) : List Real :=
  b.leaves.flatMap TrigLeafCertificate.values

end TrigLeafBatchCertificate

/-- Executable batch check: every leaf is independently checked and uses the
single declared stack scale. -/
def checkTrigLeafBatch (b : TrigLeafBatchCertificate) : Bool :=
  b.leaves.all fun c =>
    checkTrigLeaf c && decide (c.horner.scale = b.scale)

private theorem checkedTrigLeafList_sound {scale : Nat}
    {leaves : List TrigLeafCertificate}
    (hcheck : leaves.all (fun c =>
      checkTrigLeaf c && decide (c.horner.scale = scale)) = true) :
    StackRel scale
      (leaves.flatMap TrigLeafCertificate.rows)
      (leaves.flatMap TrigLeafCertificate.values) := by
  induction leaves with
  | nil => exact .nil
  | cons c leaves ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨hc, hscale⟩, htail⟩
      have hhead := checkedTrigLeaf_sound hc
      rw [hscale] at hhead
      simpa only [List.flatMap_cons] using List.rel_append hhead (ih htail)

/-- One induction certifies all generated sine/cosine leaves in the batch. -/
theorem checkedTrigLeafBatch_sound {b : TrigLeafBatchCertificate}
    (hb : checkTrigLeafBatch b = true) :
    StackRel b.scale b.rows b.values := by
  exact checkedTrigLeafList_sound hb

#print axioms Theory.PiDigits.T186ReflectedTrigLeaf.rationalTrigRemainder_cast
#print axioms Theory.PiDigits.T186ReflectedTrigLeaf.checkedTrigLeaf_sound
#print axioms Theory.PiDigits.T186ReflectedTrigLeaf.checkedTrigLeaf_cons
#print axioms Theory.PiDigits.T186ReflectedTrigLeaf.checkedTrigLeafBatch_sound

end

end Theory.PiDigits.T186ReflectedTrigLeaf
