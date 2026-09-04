import TheoryLib.PiQuantitativeBlockHitting.T189T189SignedHorizonSectorBridge
import TheoryLib.PiQuantitativeBlockHitting.T192T192PrimitiveValuationShells
import TheoryLib.PiQuantitativeBlockHitting.T193T193PositiveValuationShellAggregate
import TheoryLib.PiQuantitativeBlockHitting.T228T228CentralReturnAppendix
import Mathlib

/-!
# T229: predecessor appendix

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t229; each task compiled and
axiom-checked; assembled by Claude Opus 5

Every task embedded the t228 starter definitions and, in task `-02`, the whole
t228 orbit and central-return development, because t228 was not yet promoted.
Those embedded copies are byte-identical to the promoted
`TheoryLib/PiQuantitativeBlockHitting/T228T228CentralReturnAppendix.lean`
declarations, so they are dropped here in favour of the import.
-/

noncomputable section
set_option autoImplicit false

namespace Theory.PiDigits.T229PredecessorAppendix

open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.LongLagBlockCollisionDecay.T4
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.SignedBlockBellmanTransport
open Theory.PiDigits.SignedHorizonSectorBridge
open Theory.PiDigits.SignedPredecessorRay
open Theory.PiDigits.T192PrimitiveValuationShells
open Theory.PiDigits.T193PositiveValuationShellAggregate
open Theory.PiDigits.T228CentralReturnAppendix

structure PredecessorWitness
    (x : ℝ) (k n A d C : ℕ) (y : ℝ) : Prop where
  parent : CentralWitness x k n A y
  hd : d < 10
  hC : C < 10 * 10 ^ k
  hdfloor : d = ⌊10 * decimalOrbit x (n - 1)⌋₊
  hCformula : C = A + d * 10 ^ k
  hCfloor :
    C = ⌊((10 * 10 ^ k : ℕ) : ℝ) * decimalOrbit x (n - 1)⌋₊
  hchildCoord :
    decimalOrbit x (n - 1) -
        decimalCylinderCenter (10 * 10 ^ k) C =
      y / (10 * 10 ^ k : ℕ)

def PredecessorPredicate (x : ℝ) : Prop :=
  ∃ k0 : ℕ, ∀ k : ℕ, max 3 k0 ≤ k →
    ∃ n A d C : ℕ, ∃ y : ℝ,
      PredecessorWitness x k n A d C y

/-! ### The predecessor lift

Tasks `pi-t229-predecessor-01-central-witness-predecessor-lift` and
`-02-measure-below-eight-implies-predecessor-predicate`. -/

lemma decimalOrbit_step_digit (x : ℝ) (n : ℕ) :
    10 * decimalOrbit x n =
      decimalOrbit x (n + 1) + (⌊10 * decimalOrbit x n⌋₊ : ℝ) := by
  have hnn : (0 : ℝ) ≤ 10 * decimalOrbit x n := by
    have := decimalOrbit_nonneg x n; linarith
  rw [decimalOrbit_succ, Int.fract, natCast_floor_eq_intCast_floor hnn]
  ring

theorem centralWitness_predecessor_lift
    {x y : ℝ} {k n A : ℕ}
    (h : CentralWitness x k n A y) :
    ∃ d C : ℕ, PredecessorWitness x k n A d C y := by
  have hpk : 0 < 10 ^ k := Nat.one_le_pow k 10 (by norm_num)
  have hn1 : 1 ≤ n := by have := h.hnLower; omega
  have hnsub : n - 1 + 1 = n := by omega
  set t : ℝ := decimalOrbit x (n - 1) with ht
  have ht0 : 0 ≤ t := decimalOrbit_nonneg x (n - 1)
  have ht1 : t < 1 := decimalOrbit_lt_one x (n - 1)
  set d : ℕ := ⌊10 * t⌋₊ with hdd
  have hstep : 10 * t = decimalOrbit x n + (d : ℝ) := by
    have hs := decimalOrbit_step_digit x (n - 1)
    rw [hnsub] at hs
    exact hs
  have hd10 : d < 10 := by
    rw [hdd]
    refine (Nat.floor_lt (by linarith)).2 ?_
    push_cast
    linarith
  refine ⟨d, A + d * 10 ^ k, ?_⟩
  have hAlt := h.hA
  have hpos : (0 : ℝ) < ((10 ^ k : ℕ) : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ ((10 ^ k : ℕ) : ℝ) * decimalOrbit x n :=
    mul_nonneg hpos.le (decimalOrbit_nonneg x n)
  have hmain : ((10 * 10 ^ k : ℕ) : ℝ) * t =
      ((10 ^ k : ℕ) : ℝ) * decimalOrbit x n + ((d * 10 ^ k : ℕ) : ℝ) := by
    push_cast
    push_cast at hstep
    linear_combination ((10 : ℝ) ^ k) * hstep
  refine
    { parent := h
      hd := hd10
      hC := ?_
      hdfloor := rfl
      hCformula := rfl
      hCfloor := ?_
      hchildCoord := ?_ }
  · have hb : d * 10 ^ k ≤ 9 * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hmain, Nat.floor_add_natCast hnn, ← h.hAfloor]
  · have hcoord := h.hCoord
    rw [decimalCylinderCenter] at hcoord
    rw [decimalCylinderCenter]
    have hinv : ((10 : ℝ) ^ k)⁻¹ * (10 : ℝ) ^ k = 1 :=
      inv_mul_cancel₀ (by positivity)
    push_cast at hcoord hstep ⊢
    linear_combination (1 / 10 : ℝ) * hcoord + (1 / 10 : ℝ) * hstep -
      ((d : ℝ) / 10) * hinv

theorem measureBelow_eight_implies_predecessorPredicate
    {x : ℝ} (hSource : IrrationalityMeasureBelow x 8) :
    PredecessorPredicate x := by
  obtain ⟨k0, hk0⟩ := measureBelow_eight_eventually_centralWitness hSource
  refine ⟨k0, ?_⟩
  intro k hk
  obtain ⟨n, A, y, hw⟩ := hk0 k hk
  obtain ⟨d, C, hpw⟩ := centralWitness_predecessor_lift hw
  exact ⟨n, A, d, C, y, hpw⟩

/-- Discharged form: the promoted T228 bridge
`badlyApproximable_implies_measureBelow_eight` supplies the named
exponent-eight premise. -/
theorem badlyApproximable_implies_predecessorPredicate
    {κ x : ℝ} (hBA : BAκ κ x) :
    PredecessorPredicate x :=
  measureBelow_eight_implies_predecessorPredicate
    (badlyApproximable_implies_measureBelow_eight hBA)

/-! ### Free-phase consequences at the parent and predecessor scales

Tasks `pi-t229-predecessor-03-parent-zero-shell-lower`,
`-04-parent-atom-lower`, `-05-parent-unit-block-surplus`,
`-06-predecessor-atom-lower`, `-07-predecessor-unit-block-surplus` and
`-08-predecessor-child-surplus-of-horizon-sector`. -/

lemma decimalCylinderCenter_eq (q A : ℕ) :
    decimalCylinderCenter q A =
      Theory.PiDigits.PrimitiveRayCoefficientGap.decimalCylinderCenter q A := rfl

lemma parent_zeroShell_lower
    {x y : ℝ} {k n A d C : ℕ}
    (h : PredecessorWitness x k n A d C y) :
    (9 / 20 : ℝ) * (4859 / 10000 : ℝ) <
      (primitiveValuationShellAt
        (10 ^ k) A (decimalOrbit x n) 0).re :=
  primitiveValuationShell_zero_re_gt_generic k A (decimalOrbit x n)
    h.parent.hk y h.parent.hy
    (by rw [← decimalCylinderCenter_eq]; exact h.parent.hCoord)

lemma parent_atom_lower
    {x y : ℝ} {k n A d C : ℕ}
    (h : PredecessorWitness x k n A d C y) :
    (7139 / 45000 : ℝ) <
      (primitiveBoundaryAtomAt
        (10 ^ k) A (decimalOrbit x n)).re :=
  primitiveBoundaryAtom_re_gt_7139_div_45000_generic k A (decimalOrbit x n)
    h.parent.hk y h.parent.hy
    (by rw [← decimalCylinderCenter_eq]; exact h.parent.hCoord)

lemma parent_unitBlock_surplus
    {x y : ℝ} {k n A d C : ℕ}
    (h : PredecessorWitness x k n A d C y) :
    (3 / 20 : ℝ) * (10 ^ k : ℕ) <
      (10 ^ k : ℕ) *
          (primitiveBoundaryAtomAt
            (10 ^ k) A (decimalOrbit x n)).re -
        signedBlockPotential (10 ^ k) :=
  central_unitBlock_surplus_gt_three_div_twenty_generic k A (decimalOrbit x n)
    h.parent.hk y h.parent.hy
    (by rw [← decimalCylinderCenter_eq]; exact h.parent.hCoord)

lemma predecessor_atom_lower
    {x y : ℝ} {k n A d C : ℕ}
    (h : PredecessorWitness x k n A d C y) :
    (7139 / 45000 : ℝ) <
      (primitiveBoundaryAtomAt
        (10 * 10 ^ k) C (decimalOrbit x (n - 1))).re := by
  have hk := h.parent.hk
  have hpow : (10 : ℕ) * 10 ^ k = 10 ^ (k + 1) := by ring
  have hgen := primitiveBoundaryAtom_re_gt_7139_div_45000_generic (k + 1) C
    (decimalOrbit x (n - 1)) (by omega) y h.parent.hy
    (by rw [← hpow, ← decimalCylinderCenter_eq]; exact h.hchildCoord)
  rw [← hpow] at hgen
  exact hgen

lemma predecessor_unitBlock_surplus
    {x y : ℝ} {k n A d C : ℕ}
    (h : PredecessorWitness x k n A d C y) :
    (3 / 2 : ℝ) * (10 ^ k : ℕ) <
      (10 * 10 ^ k : ℕ) *
          (primitiveBoundaryAtomAt
            (10 * 10 ^ k) C (decimalOrbit x (n - 1))).re -
        signedBlockPotential (10 * 10 ^ k) := by
  have hk := h.parent.hk
  have hpow : (10 : ℕ) * 10 ^ k = 10 ^ (k + 1) := by ring
  have hgen := central_unitBlock_surplus_gt_three_div_twenty_generic (k + 1) C
    (decimalOrbit x (n - 1)) (by omega) y h.parent.hy
    (by rw [← hpow, ← decimalCylinderCenter_eq]; exact h.hchildCoord)
  rw [← hpow] at hgen
  push_cast at hgen ⊢
  linarith

theorem predecessor_child_surplus_of_horizon_sector
    {x y : ℝ} {k n A d C : ℕ}
    (h : PredecessorWitness x k n A d C y)
    (N H : ℕ) (hNH : N ≤ H)
    (hsector :
      H * signedBlockPotential (10 * 10 ^ k) <
        (10 * 10 ^ k : ℕ) *
            (primitiveBoundaryFourierSum
              (10 * 10 ^ k) C N).re +
          (10 ^ k : ℕ) *
            (predecessorZeroBlockIncrement (10 ^ k) A N H +
              (shiftedLagOneBlockCorrelation
                (10 ^ k) A N H d).re)) :
    0 < signedPrefixSurplus (10 * 10 ^ k) C H := by
  have hCf := h.hCformula
  subst hCf
  exact signedPrefixSurplus_child_pos_of_horizon_sector_gt (10 ^ k) A N H d
    (by positivity) hNH h.hd hsector

end Theory.PiDigits.T229PredecessorAppendix
