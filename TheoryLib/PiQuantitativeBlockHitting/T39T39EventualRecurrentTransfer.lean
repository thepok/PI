import TheoryLib.PiQuantitativeBlockHitting.T38T38MachinForcedOrbit

/-!
# T39: exact recurrent-value transfer under eventual equality

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Two streams which agree from some point onward have exactly the same values
occurring arbitrarily late.  This elementary fact upgrades T34's lossy
two-cell shadow transfer to an exact recurrent-value transfer for T37's
eventually equal rational Machin code and symbolic pi-cylinder code.

Under the same explicit published hypothesis
`IrrationalityMeasureBelow pi 8` used in T36 and T37, the two code streams
therefore have identical recurrent-value sets and counts.  Combining this
with T31 and T34 gives at least `m + 1` recurrent values in the explicit
length-`m` Machin code for every positive `m`, with no factor-two loss.

These statements do not prove that all `10 ^ m` cells recur, nor do they
prove density, normality, or the canonical every-word conjecture.  The final
theorem below only says that all-cell recurrent coverage is equivalent for
the two eventually equal streams.
-/

noncomputable section

open Filter

namespace Theory.PiDigits.EventualRecurrentTransfer

open DecimalFactorComplexity
open DecimalFactorComplexity.FiniteCylinderEnergy
open Theory.PiDigits.RecurrentFactorComplexity
open Theory.PiDigits.RecurrentCellTransfer
open Theory.PiDigits.FloorSymbolicBridge

variable {α : Type*}

/-- Eventual equality preserves, in either direction, occurrence beyond every
cutoff of one fixed value. -/
theorem recurrentValue_iff_of_eventuallyEq
    (s t : Stream α) (h : s =ᶠ[atTop] t) (a : α) :
    RecurrentValue s a ↔ RecurrentValue t a := by
  obtain ⟨C, hC⟩ := eventually_atTop.mp h
  constructor
  · intro hs N
    obtain ⟨i, hi, hsi⟩ := hs (max N C)
    refine ⟨i, (Nat.le_max_left N C).trans hi, ?_⟩
    exact (hC i ((Nat.le_max_right N C).trans hi)).symm.trans hsi
  · intro ht N
    obtain ⟨i, hi, hti⟩ := ht (max N C)
    refine ⟨i, (Nat.le_max_left N C).trans hi, ?_⟩
    exact (hC i ((Nat.le_max_right N C).trans hi)).trans hti

/-- Eventual equality gives literal equality of the sets of recurrent
values. -/
theorem recurrentValueSet_eq_of_eventuallyEq
    (s t : Stream α) (h : s =ᶠ[atTop] t) :
    {a : α | RecurrentValue s a} = {a : α | RecurrentValue t a} := by
  ext a
  exact recurrentValue_iff_of_eventuallyEq s t h a

/-- The recurrent-value subtypes of eventually equal streams are canonically
equivalent by the identity on their underlying values. -/
def recurrentValuesEquivOfEventuallyEq
    (s t : Stream α) (h : s =ᶠ[atTop] t) :
    RecurrentValues s ≃ RecurrentValues t :=
  Equiv.subtypeEquivRight (fun a ↦ recurrentValue_iff_of_eventuallyEq s t h a)

/-- Eventual equality preserves the exact number of recurrent values. -/
theorem recurrentValueCount_eq_of_eventuallyEq
    (s t : Stream α) (h : s =ᶠ[atTop] t) :
    recurrentValueCount s = recurrentValueCount t :=
  Nat.card_congr (recurrentValuesEquivOfEventuallyEq s t h)

/-- Conditional pointwise recurrent-value equivalence for the explicit
rational Machin code and the symbolic pi-cylinder code. -/
theorem machinBlockCode_recurrentValue_iff_piCylinderCode
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8)
    (m : ℕ) (a : Fin (10 ^ m)) :
    RecurrentValue (machinBlockCode m) a ↔
      RecurrentValue (piCylinderCode m) a :=
  recurrentValue_iff_of_eventuallyEq
    (machinBlockCode m) (piCylinderCode m)
    (eventually_machinBlockCode_eq_piCylinderCode hSource m) a

/-- Conditional exact equality of the recurrent-value sets of the explicit
rational Machin code and the symbolic pi-cylinder code. -/
theorem machinBlockCode_recurrentValueSet_eq_piCylinderCode
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8)
    (m : ℕ) :
    {a : Fin (10 ^ m) | RecurrentValue (machinBlockCode m) a} =
      {a : Fin (10 ^ m) | RecurrentValue (piCylinderCode m) a} :=
  recurrentValueSet_eq_of_eventuallyEq
    (machinBlockCode m) (piCylinderCode m)
    (eventually_machinBlockCode_eq_piCylinderCode hSource m)

/-- Conditional exact equality of recurrent-value counts for the explicit
rational Machin code and the symbolic pi-cylinder code. -/
theorem machinBlockCode_recurrentValueCount_eq_piCylinderCode
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8)
    (m : ℕ) :
    recurrentValueCount (machinBlockCode m) =
      recurrentValueCount (piCylinderCode m) :=
  recurrentValueCount_eq_of_eventuallyEq
    (machinBlockCode m) (piCylinderCode m)
    (eventually_machinBlockCode_eq_piCylinderCode hSource m)

/-- T31's full recurrent Morse--Hedlund lower bound transfers to the explicit
rational Machin code with no factor-two loss.  The positivity assumption is
exactly T31's positive block-length scope. -/
theorem pi_length_add_one_le_machinBlockCode_recurrentValueCount
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8)
    (m : ℕ) (hm : 0 < m) :
    m + 1 ≤ recurrentValueCount (machinBlockCode m) := by
  have hpi : m + 1 ≤ recurrentValueCount (piCylinderCode m) :=
    (pi_recurrentFactorComplexity_lower_bound m hm).trans
      (pi_recurrentFactorComplexity_le_recurrentCylinderCount m)
  rw [machinBlockCode_recurrentValueCount_eq_piCylinderCode hSource m]
  exact hpi

/-- Because the two code streams are eventually equal, the assertion that
every finite cell recurs is exactly equivalent for them.  Neither side is
proved here. -/
theorem machinBlockCode_allCellsRecurrent_iff_piCylinderCode
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8)
    (m : ℕ) :
    (∀ a : Fin (10 ^ m), RecurrentValue (machinBlockCode m) a) ↔
      (∀ a : Fin (10 ^ m), RecurrentValue (piCylinderCode m) a) := by
  constructor
  · intro h a
    exact (machinBlockCode_recurrentValue_iff_piCylinderCode
      hSource m a).mp (h a)
  · intro h a
    exact (machinBlockCode_recurrentValue_iff_piCylinderCode
      hSource m a).mpr (h a)

end Theory.PiDigits.EventualRecurrentTransfer

#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.recurrentValue_iff_of_eventuallyEq
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.recurrentValueSet_eq_of_eventuallyEq
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.recurrentValuesEquivOfEventuallyEq
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.recurrentValueCount_eq_of_eventuallyEq
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.machinBlockCode_recurrentValue_iff_piCylinderCode
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.machinBlockCode_recurrentValueSet_eq_piCylinderCode
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.machinBlockCode_recurrentValueCount_eq_piCylinderCode
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.pi_length_add_one_le_machinBlockCode_recurrentValueCount
#print axioms
  Theory.PiDigits.EventualRecurrentTransfer.machinBlockCode_allCellsRecurrent_iff_piCylinderCode
