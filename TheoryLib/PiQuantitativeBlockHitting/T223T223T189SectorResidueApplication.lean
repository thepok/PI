import TheoryLib.PiQuantitativeBlockHitting.T189T189SignedHorizonSectorBridge
import Mathlib

/-!
# T223: T189 sector-residue application

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t223; each task compiled and
axiom-checked; assembled by Claude Opus 5

Tasks `pi-t223-sector-01`..`-05` share one starter; task `-06` uses a shorter
starter that opens `Theory.PiDigits.SignedPredecessorRay` and sets
`autoImplicit false`.  Both are kept: the superset starter appears once and the
sixth task's own `open` and option are scoped to that theorem alone.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Theory.PiDigits.T223T189SectorResidueApplication

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.SignedBlockBellmanTransport
open Theory.PiDigits.SignedHorizonSectorBridge

abbrev NonzeroDecimalSector := {r : Fin 10 // r ≠ 0}

noncomputable def T10 (x : ℝ) : ℝ := x - ⌊x⌋

noncomputable def trigPolynomial
    (S : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ S,
    a m * Complex.exp ((2 * Real.pi * m * x : ℝ) * Complex.I)

def CoefficientSupported (S : Finset ℤ) (a : ℤ → ℂ) : Prop :=
  ∀ m, m ∉ S → a m = 0

def Primitive10 (h : ℤ) : Prop :=
  h ≠ 0 ∧ ¬ (10 : ℤ) ∣ h

noncomputable def raySupport
    (S : Finset ℤ) (h : ℤ) : Finset ℤ := by
  classical
  exact S.filter fun m => ∃ k : ℕ, m = (10 : ℤ) ^ k * h

noncomputable def RaySum
    (S : Finset ℤ) (a : ℤ → ℂ) (h : ℤ) : ℂ :=
  ∑ m ∈ raySupport S h, a m

def L1Coboundary10 (f : ℝ → ℂ) : Prop :=
  ∃ g : ℝ → ℂ, IntegrableOn g (Set.Ico 0 1) ∧
    ∀ᵐ x ∂Measure.restrict volume (Set.Ico 0 1),
      f x = g x - g (T10 (10 * x))

def T222PrimitiveRayCriterionInput : Prop :=
  ∀ {S : Finset ℤ} {a : ℤ → ℂ},
    CoefficientSupported S a → a 0 = 0 →
      (L1Coboundary10 (trigPolynomial S a) ↔
        ∀ h : ℤ, Primitive10 h → RaySum S a h = 0)

def SectorFourierData
    (F : NonzeroDecimalSector → ℝ → ℂ)
    (S : NonzeroDecimalSector → Finset ℤ)
    (a : NonzeroDecimalSector → ℤ → ℂ) : Prop :=
  ∀ r,
    CoefficientSupported (S r) (a r) ∧
    a r 0 = 0 ∧
    F r = trigPolynomial (S r) (a r)

def T189SectorResiduePremise
    (S : NonzeroDecimalSector → Finset ℤ)
    (a : NonzeroDecimalSector → ℤ → ℂ) : Prop :=
  ∀ r, ∃ h : ℤ,
    Primitive10 h ∧ RaySum (S r) (a r) h ≠ 0

/-! ### Sector projections and the conditional coboundary obstruction

Tasks `pi-t223-sector-01-sector-coeff-supported`, `-02-sector-mean-zero`,
`-03-sector-eq-trig-polynomial`, `-04-sector-has-nonzero-primitive-residue`
and `-05-no-scalar-l1-coboundary-of-sector-residue`. -/

lemma sector_coeff_supported
    {F S a} (h : SectorFourierData F S a)
    (r : NonzeroDecimalSector) :
    CoefficientSupported (S r) (a r) :=
  (h r).1

lemma sector_mean_zero
    {F S a} (h : SectorFourierData F S a)
    (r : NonzeroDecimalSector) :
    a r 0 = 0 :=
  (h r).2.1

lemma sector_eq_trigPolynomial
    {F S a} (h : SectorFourierData F S a)
    (r : NonzeroDecimalSector) :
    F r = trigPolynomial (S r) (a r) :=
  (h r).2.2

lemma sector_has_nonzero_primitive_residue
    {S a} (h : T189SectorResiduePremise S a)
    (r : NonzeroDecimalSector) :
    ∃ h0 : ℤ, Primitive10 h0 ∧ RaySum (S r) (a r) h0 ≠ 0 :=
  h r

theorem no_scalar_L1_coboundary_of_sectorResidue
    (hR4 : T222PrimitiveRayCriterionInput)
    {F : NonzeroDecimalSector → ℝ → ℂ}
    {S : NonzeroDecimalSector → Finset ℤ}
    {a : NonzeroDecimalSector → ℤ → ℂ}
    (hdata : SectorFourierData F S a)
    (hres : T189SectorResiduePremise S a) :
    ∀ r, ¬ L1Coboundary10 (F r) := by
  intro r hcob
  have hiff := hR4 (sector_coeff_supported hdata r) (sector_mean_zero hdata r)
  rw [sector_eq_trigPolynomial hdata r] at hcob
  obtain ⟨h0, hprim, hne⟩ := sector_has_nonzero_primitive_residue hres r
  exact hne (hiff.mp hcob h0 hprim)

/-! ### Child surplus of a signed horizon sector

Task `pi-t223-sector-06-child-surplus-of-signed-horizon-sector`. -/

section
open Theory.PiDigits.SignedPredecessorRay

set_option autoImplicit false in
theorem child_surplus_of_signed_horizon_sector
    (q A N H d : ℕ) (hq : 0 < q) (hNH : N ≤ H) (hd : d < 10)
    (hsector :
      H * signedBlockPotential (10 * q) <
        (10 * q : ℕ) *
            (primitiveBoundaryFourierSum
              (10 * q) (A + d * q) N).re +
          q * (predecessorZeroBlockIncrement q A N H +
            (shiftedLagOneBlockCorrelation q A N H d).re)) :
    0 < signedPrefixSurplus (10 * q) (A + d * q) H :=
  signedPrefixSurplus_child_pos_of_horizon_sector_gt
    q A N H d hq hNH hd hsector

end

end Theory.PiDigits.T223T189SectorResidueApplication
