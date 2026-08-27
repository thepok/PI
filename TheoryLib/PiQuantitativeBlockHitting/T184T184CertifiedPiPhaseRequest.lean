import TheoryLib.PiQuantitativeBlockHitting.T183T183ReflectedExpHorner
import TheoryLib.PiQuantitativeBlockHitting.T175T175DecimalSuffixCylinder
import TheoryLib.PiQuantitativeBlockHitting.T139T139PrimitiveRayBoundaryConsumer

/-!
# T184: checked reduced-angle requests for the certified pi orbit

This file bridges T175 decimal suffix cylinders to the rational centres used
by T183.  A request describes an affine phase

`m * piOrbit n + b - turn`

with nonnegative rational multiplier `m`, rational target offset `b`, and an
integer centered-turn witness.  Its checker verifies denominator positivity,
the available T173 digit horizon, containment in the centered cycle interval,
and all four products of the pi and cycle endpoint intervals.  Checking all
four corners makes the certificate sound without trusting the sign of the
reduced cycle.

There is no large request payload here.
-/

namespace Theory.PiDigits.T184CertifiedPiPhaseRequest

open Theory.PiDigits.T173MachinIntegerCertificate10015
open Theory.PiDigits.T175DecimalSuffixCylinder
open Theory.PiDigits.PrimitiveRayBoundaryConsumer

noncomputable section

/-- Compact data for one affine orbit phase and its claimed rational angle
centre/radius.  Kernel requests use multipliers `1`, `1/2`, and `q/2`. -/
structure PhaseRequest where
  orbitIndex : Nat
  multiplierNumerator : Nat
  multiplierDenominator : Nat
  offsetNumerator : Int
  offsetDenominator : Nat
  centeredTurn : Int
  centerNumerator : Int
  centerDenominator : Nat
  radiusNumerator : Nat
  radiusDenominator : Nat
deriving DecidableEq, Repr

namespace PhaseRequest

def suffixScale (r : PhaseRequest) : Nat :=
  10 ^ (certifiedPiPlaces - r.orbitIndex)

def suffixNumerator (r : PhaseRequest) : Nat :=
  certifiedPiPrefix % r.suffixScale

def orbitLower (r : PhaseRequest) : Rat :=
  (r.suffixNumerator : Rat) / r.suffixScale

def orbitUpper (r : PhaseRequest) : Rat :=
  (r.suffixNumerator + 1 : Rat) / r.suffixScale

def multiplier (r : PhaseRequest) : Rat :=
  r.multiplierNumerator / r.multiplierDenominator

def offset (r : PhaseRequest) : Rat :=
  r.offsetNumerator / r.offsetDenominator

def cycleLower (r : PhaseRequest) : Rat :=
  r.multiplier * r.orbitLower + r.offset - r.centeredTurn

def cycleUpper (r : PhaseRequest) : Rat :=
  r.multiplier * r.orbitUpper + r.offset - r.centeredTurn

def piLower : Rat := (certifiedPiPrefix : Rat) / certifiedPiScale
def piUpper : Rat := (certifiedPiPrefix + 1 : Rat) / certifiedPiScale

def angleCenter (r : PhaseRequest) : Rat :=
  r.centerNumerator / r.centerDenominator

def angleRadius (r : PhaseRequest) : Rat :=
  r.radiusNumerator / r.radiusDenominator

/-- All endpoint products for `2*pi*u`. -/
def angleCorners (r : PhaseRequest) : List Rat :=
  [2 * piLower * r.cycleLower, 2 * piLower * r.cycleUpper,
    2 * piUpper * r.cycleLower, 2 * piUpper * r.cycleUpper]

/-- Proposition recomputed by the executable checker. -/
def Valid (r : PhaseRequest) : Prop :=
  0 < r.multiplierDenominator ∧
  0 < r.offsetDenominator ∧
  0 < r.centerDenominator ∧
  0 < r.radiusDenominator ∧
  r.orbitIndex ≤ certifiedPiPlaces ∧
  (-1 / 2 : Rat) ≤ r.cycleLower ∧
  r.cycleUpper ≤ (1 / 2 : Rat) ∧
  (∀ z ∈ r.angleCorners,
    r.angleCenter - r.angleRadius ≤ z ∧
      z ≤ r.angleCenter + r.angleRadius) ∧
  |r.angleCenter| ≤ 4

end PhaseRequest

open PhaseRequest

/-- The request checker uses only exact natural, integer, and rational
arithmetic. -/
def checkPhaseRequest (r : PhaseRequest) : Bool :=
  decide (0 < r.multiplierDenominator) &&
  decide (0 < r.offsetDenominator) &&
  decide (0 < r.centerDenominator) &&
  decide (0 < r.radiusDenominator) &&
  decide (r.orbitIndex ≤ certifiedPiPlaces) &&
  decide ((-1 / 2 : Rat) ≤ r.cycleLower) &&
  decide (r.cycleUpper ≤ (1 / 2 : Rat)) &&
  r.angleCorners.all (fun z => decide
    (r.angleCenter - r.angleRadius ≤ z ∧
      z ≤ r.angleCenter + r.angleRadius)) &&
  decide (|r.angleCenter| ≤ 4)

theorem valid_of_check {r : PhaseRequest} (h : checkPhaseRequest r = true) :
    r.Valid := by
  simp only [checkPhaseRequest, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hm, ho⟩, hc⟩, hr⟩, hn⟩, hcl⟩, hcu⟩,
    hcorners⟩, hsmall⟩
  refine ⟨hm, ho, hc, hr, hn, hcl, hcu, ?_, hsmall⟩
  intro z hz
  exact hcorners z hz

namespace PhaseRequest

/-- The unreduced affine cycle represented by a request. -/
def originalCycle (r : PhaseRequest) : Real :=
  (r.multiplier : Real) * piOrbit r.orbitIndex + (r.offset : Real)

/-- The unreduced affine angle whose sine and cosine occur in the root
payload. -/
def originalAngle (r : PhaseRequest) : Real :=
  2 * Real.pi * r.originalCycle

/-- The actual reduced cycle represented by a request. -/
def reducedCycle (r : PhaseRequest) : Real :=
  (r.multiplier : Real) * piOrbit r.orbitIndex +
    (r.offset : Real) - r.centeredTurn

/-- The actual reduced real angle consumed by a sine/cosine leaf. -/
def reducedAngle (r : PhaseRequest) : Real :=
  2 * Real.pi * r.reducedCycle

theorem originalAngle_eq_reducedAngle_add_turn (r : PhaseRequest) :
    r.originalAngle =
      r.reducedAngle + (r.centeredTurn : Real) * (2 * Real.pi) := by
  unfold originalAngle reducedAngle originalCycle reducedCycle
  ring

/-- Exact periodic transfer from the unreduced affine phase to its checked
centered representative. -/
theorem cos_originalAngle_eq_reducedAngle (r : PhaseRequest) :
    Real.cos r.originalAngle = Real.cos r.reducedAngle := by
  rw [r.originalAngle_eq_reducedAngle_add_turn]
  exact Real.cos_add_int_mul_two_pi r.reducedAngle r.centeredTurn

theorem sin_originalAngle_eq_reducedAngle (r : PhaseRequest) :
    Real.sin r.originalAngle = Real.sin r.reducedAngle := by
  rw [r.originalAngle_eq_reducedAngle_add_turn]
  exact Real.sin_add_int_mul_two_pi r.reducedAngle r.centeredTurn

end PhaseRequest

private theorem four_corners
    {a x b c y d : Real} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d)
    {L U : Real}
    (hLac : L ≤ a * c) (hLad : L ≤ a * d)
    (hLbc : L ≤ b * c) (hLbd : L ≤ b * d)
    (hUac : a * c ≤ U) (hUad : a * d ≤ U)
    (hUbc : b * c ≤ U) (hUbd : b * d ≤ U) :
    L ≤ x * y ∧ x * y ≤ U := by
  constructor
  · by_cases hx0 : 0 ≤ x
    · have hxy : x * c ≤ x * y := mul_le_mul_of_nonneg_left hy.1 hx0
      by_cases hc0 : 0 ≤ c
      · exact hLac.trans ((mul_le_mul_of_nonneg_right hx.1 hc0).trans hxy)
      · exact hLbc.trans
          ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hc0)).trans hxy)
    · have hxneg : x ≤ 0 := le_of_not_ge hx0
      have hxy : x * d ≤ x * y := mul_le_mul_of_nonpos_left hy.2 hxneg
      by_cases hd0 : 0 ≤ d
      · exact hLad.trans ((mul_le_mul_of_nonneg_right hx.1 hd0).trans hxy)
      · exact hLbd.trans
          ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hd0)).trans hxy)
  · by_cases hx0 : 0 ≤ x
    · have hxy : x * y ≤ x * d := mul_le_mul_of_nonneg_left hy.2 hx0
      by_cases hd0 : 0 ≤ d
      · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hd0).trans hUbd)
      · exact hxy.trans
          ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hd0)).trans hUad)
    · have hxneg : x ≤ 0 := le_of_not_ge hx0
      have hxy : x * y ≤ x * c := mul_le_mul_of_nonpos_left hy.1 hxneg
      by_cases hc0 : 0 ≤ c
      · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hc0).trans hUbc)
      · exact hxy.trans
          ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hc0)).trans hUac)

/-- A checked request encloses the actual reduced angle within its rational
radius, and its rational centre is in the `[-4,4]` range required by T180/T183.
The centered-turn witness also genuinely places the actual cycle in
`[-1/2,1/2]`. -/
theorem checkedPhaseRequest_sound {r : PhaseRequest}
    (hcheck : checkPhaseRequest r = true) :
    |r.reducedAngle - (r.angleCenter : Real)| ≤ (r.angleRadius : Real) ∧
      |(r.angleCenter : Real)| ≤ 4 ∧
      (-1 / 2 : Real) ≤ r.reducedCycle ∧
      r.reducedCycle ≤ (1 / 2 : Real) := by
  have hv := valid_of_check hcheck
  rcases hv with ⟨hmden, hoden, hcden, hrden, hn, hcentL, hcentU,
    hcorners, hcenterSmall⟩
  have horbit := piOrbit_mem_certified_suffixCylinder r.orbitIndex hn
  have horbit' : (r.orbitLower : Real) ≤ piOrbit r.orbitIndex ∧
      piOrbit r.orbitIndex ≤ (r.orbitUpper : Real) := by
    constructor
    · exact le_of_lt (by simpa [orbitLower, suffixNumerator, suffixScale, piOrbit] using horbit.1)
    · exact le_of_lt (by simpa [orbitUpper, suffixNumerator, suffixScale, piOrbit] using horbit.2)
  have hm : (0 : Real) ≤ ((r.multiplier : Rat) : Real) := by
    exact_mod_cast (show (0 : Rat) ≤ r.multiplier by
      unfold multiplier
      positivity)
  have hcycle : (r.cycleLower : Real) ≤ r.reducedCycle ∧
      r.reducedCycle ≤ (r.cycleUpper : Real) := by
    unfold cycleLower cycleUpper reducedCycle
    push_cast
    constructor
    · have hp := mul_le_mul_of_nonneg_left horbit'.1 hm
      linarith
    · have hp := mul_le_mul_of_nonneg_left horbit'.2 hm
      linarith
  have hpi0 := pi_mem_certified_decimalCylinder
  have hpiLowerCast : (piLower : Real) =
      (certifiedPiPrefix : Real) / certifiedPiScale := by
    unfold piLower
    push_cast
    rfl
  have hpiUpperCast : (piUpper : Real) =
      (certifiedPiPrefix + 1 : Real) / certifiedPiScale := by
    unfold piUpper
    push_cast
    rfl
  have hpi : (piLower : Real) ≤ Real.pi ∧ Real.pi ≤ (piUpper : Real) := by
    constructor
    · rw [hpiLowerCast]
      exact hpi0.1.le
    · rw [hpiUpperCast]
      exact hpi0.2.le
  simp [angleCorners] at hcorners
  rcases hcorners with ⟨hLL, hLU, hUL, hUU⟩
  have hLL' : (r.angleCenter : Real) ≤
      2 * (piLower : Real) * (r.cycleLower : Real) + (r.angleRadius : Real) ∧
      2 * (piLower : Real) * (r.cycleLower : Real) ≤
        (r.angleCenter : Real) + (r.angleRadius : Real) := by exact_mod_cast hLL
  have hLU' : (r.angleCenter : Real) ≤
      2 * (piLower : Real) * (r.cycleUpper : Real) + (r.angleRadius : Real) ∧
      2 * (piLower : Real) * (r.cycleUpper : Real) ≤
        (r.angleCenter : Real) + (r.angleRadius : Real) := by exact_mod_cast hLU
  have hUL' : (r.angleCenter : Real) ≤
      2 * (piUpper : Real) * (r.cycleLower : Real) + (r.angleRadius : Real) ∧
      2 * (piUpper : Real) * (r.cycleLower : Real) ≤
        (r.angleCenter : Real) + (r.angleRadius : Real) := by exact_mod_cast hUL
  have hUU' : (r.angleCenter : Real) ≤
      2 * (piUpper : Real) * (r.cycleUpper : Real) + (r.angleRadius : Real) ∧
      2 * (piUpper : Real) * (r.cycleUpper : Real) ≤
        (r.angleCenter : Real) + (r.angleRadius : Real) := by exact_mod_cast hUU
  have hLL : ((r.angleCenter - r.angleRadius : Rat) : Real) ≤
      2 * (piLower : Real) * (r.cycleLower : Real) ∧
      2 * (piLower : Real) * (r.cycleLower : Real) ≤
        ((r.angleCenter + r.angleRadius : Rat) : Real) := by
    norm_cast at ⊢
    constructor <;> linarith [hLL'.1, hLL'.2]
  have hLU : ((r.angleCenter - r.angleRadius : Rat) : Real) ≤
      2 * (piLower : Real) * (r.cycleUpper : Real) ∧
      2 * (piLower : Real) * (r.cycleUpper : Real) ≤
        ((r.angleCenter + r.angleRadius : Rat) : Real) := by
    norm_cast at ⊢
    constructor <;> linarith [hLU'.1, hLU'.2]
  have hUL : ((r.angleCenter - r.angleRadius : Rat) : Real) ≤
      2 * (piUpper : Real) * (r.cycleLower : Real) ∧
      2 * (piUpper : Real) * (r.cycleLower : Real) ≤
        ((r.angleCenter + r.angleRadius : Rat) : Real) := by
    norm_cast at ⊢
    constructor <;> linarith [hUL'.1, hUL'.2]
  have hUU : ((r.angleCenter - r.angleRadius : Rat) : Real) ≤
      2 * (piUpper : Real) * (r.cycleUpper : Real) ∧
      2 * (piUpper : Real) * (r.cycleUpper : Real) ≤
        ((r.angleCenter + r.angleRadius : Rat) : Real) := by
    norm_cast at ⊢
    constructor <;> linarith [hUU'.1, hUU'.2]
  have hproduct := four_corners
    (show (2 * (piLower : Real)) ≤ 2 * Real.pi ∧
      2 * Real.pi ≤ 2 * (piUpper : Real) by constructor <;> linarith [hpi.1, hpi.2])
    hcycle hLL.1 hLU.1 hUL.1 hUU.1 hLL.2 hLU.2 hUL.2 hUU.2
  have hangle :
      ((r.angleCenter - r.angleRadius : Rat) : Real) ≤ r.reducedAngle ∧
      r.reducedAngle ≤ ((r.angleCenter + r.angleRadius : Rat) : Real) := by
    simpa [reducedAngle, mul_assoc] using hproduct
  have hcenteredLower : (-1 / 2 : Real) ≤ r.reducedCycle := by
    have hc : ((-1 / 2 : Rat) : Real) ≤ (r.cycleLower : Real) := by
      exact_mod_cast hcentL
    norm_num at hc ⊢
    exact hc.trans hcycle.1
  have hcenteredUpper : r.reducedCycle ≤ (1 / 2 : Real) := by
    have hc : (r.cycleUpper : Real) ≤ ((1 / 2 : Rat) : Real) := by
      exact_mod_cast hcentU
    norm_num at hc ⊢
    exact hcycle.2.trans hc
  constructor
  · rw [abs_le]
    have hsub : ((r.angleCenter - r.angleRadius : Rat) : Real) =
        (r.angleCenter : Real) - (r.angleRadius : Real) := by norm_cast
    have hadd : ((r.angleCenter + r.angleRadius : Rat) : Real) =
        (r.angleCenter : Real) + (r.angleRadius : Real) := by norm_cast
    rw [hsub, hadd] at hangle
    constructor <;> linarith
  constructor
  · exact_mod_cast hcenterSmall
  · exact ⟨hcenteredLower, hcenteredUpper⟩

/-- T183-facing bundle: the checked centre/radius hypotheses and the exact
periodic rewrite back to the original affine phase are available together. -/
theorem checkedPhaseRequest_trig_input {r : PhaseRequest}
    (hcheck : checkPhaseRequest r = true) :
    |r.reducedAngle - (r.angleCenter : Real)| ≤ (r.angleRadius : Real) ∧
      |(r.angleCenter : Real)| ≤ 4 ∧
      Real.cos r.originalAngle = Real.cos r.reducedAngle ∧
      Real.sin r.originalAngle = Real.sin r.reducedAngle := by
  have hsound := checkedPhaseRequest_sound hcheck
  exact ⟨hsound.1, hsound.2.1,
    r.cos_originalAngle_eq_reducedAngle,
    r.sin_originalAngle_eq_reducedAngle⟩

end

end Theory.PiDigits.T184CertifiedPiPhaseRequest

#print axioms Theory.PiDigits.T184CertifiedPiPhaseRequest.checkedPhaseRequest_sound
#print axioms Theory.PiDigits.T184CertifiedPiPhaseRequest.checkedPhaseRequest_trig_input
