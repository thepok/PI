import TheoryLib.PiQuantitativeBlockHitting.T39T39EventualRecurrentTransfer
import TheoryLib.PiQuantitativeBlockHitting.T16T16DecimalBoundaryWordObstruction
import TheoryLib.PiDigits.T21PiDigitsV1V3Relationship

/-!
# T41: exact V1 reformulation by recurrent rational Machin cells

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For a decimal stream, occurrence of every finite word automatically means
occurrence arbitrarily late.  Using the exact value-preserving decimal
cylinder encoding, canonical V1 is therefore equivalent to recurrence of
every cell in every symbolic pi-cylinder stream.

T39 transfers that statement to the explicit rational Machin code under the
same published irrationality-measure premise used in the T36--T39 transfer
chain.  This is
an exact reformulation, not a proof of either side: no theorem here proves
all-cell recurrence, density, normality, or V1.
-/

noncomputable section

namespace Theory.PiDigits.MachinV1Equivalence

open DecimalFactorComplexity
open DecimalFactorComplexity.FiniteCylinderEnergy
open Theory.PiDigits.RecurrentCellTransfer
open Theory.PiDigits.FloorSymbolicBridge
open Theory.PiDigits.EventualRecurrentTransfer
open Theory.PiDigits.DecimalBoundaryWordObstruction

/-- List-valued occurrence is exactly equality with the list presentation of
the function-valued block at the same start. -/
theorem wordOccursAt_iff_listOfFn_blockAt_eq
    (s : Stream (Fin 10)) (w : List (Fin 10)) (n : ℕ) :
    Theory.PiDigits.T21.WordOccursAt s w n ↔
      List.ofFn (blockAt s w.length n) = w := by
  constructor
  · intro h
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      rw [List.getElem_ofFn]
      simpa [blockAt] using h i hi₂
  · intro h i hi
    have hget := congrArg (fun u : List (Fin 10) ↦ u[i]?) h
    simpa [hi, blockAt] using hget

/-- Canonical V1 is exactly recurrence of every canonical decimal cylinder
value at every block length.  This includes length zero and leading-zero
words. -/
theorem canonicalV1_iff_all_piCylinderCells_recurrent :
    Theory.PiDigits.V1 ↔
      ∀ m : ℕ, ∀ a : Fin (10 ^ m), RecurrentValue (piCylinderCode m) a := by
  rw [Theory.PiDigits.T21.canonicalV1_iff_everyFiniteWordOccurs_piDigit,
    Theory.PiDigits.T21.everyFiniteWordOccurs_iff_arbitrarilyLate]
  constructor
  · intro h m a N
    let w : List (Fin 10) := fixedWord m a.val
    have hwlen : w.length = m := fixedWord_length a.isLt
    obtain ⟨n, hn, hocc⟩ := h w N
    refine ⟨n, hn, ?_⟩
    apply Fin.ext
    rw [piCylinderCode_val_eq_blockAt_wordValue]
    have hword : List.ofFn (blockAt Theory.PiDigits.piDigit m n) = w := by
      simpa only [hwlen] using
        (wordOccursAt_iff_listOfFn_blockAt_eq
          Theory.PiDigits.piDigit w n).mp hocc
    rw [hword, fixedWord_value a.isLt]
  · intro h w N
    let a : Fin (10 ^ w.length) :=
      ⟨Theory.PiDigits.T20.wordValue w,
        Theory.PiDigits.T20.wordValue_lt_pow_length w⟩
    obtain ⟨n, hn, hcode⟩ := h w.length a N
    refine ⟨n, hn, ?_⟩
    apply (wordOccursAt_iff_listOfFn_blockAt_eq
      Theory.PiDigits.piDigit w n).mpr
    apply wordValue_injective_of_length
    · simp
    · have hval := congrArg Fin.val hcode
      rw [piCylinderCode_val_eq_blockAt_wordValue] at hval
      exact hval

/-- Under the explicit source-level irrationality-measure premise, canonical
V1 is exactly all-cell recurrence for the explicit rational Machin-code
streams.  Neither side is established here. -/
theorem canonicalV1_iff_all_machinBlockCells_recurrent
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) :
    Theory.PiDigits.V1 ↔
      ∀ m : ℕ, ∀ a : Fin (10 ^ m), RecurrentValue (machinBlockCode m) a := by
  rw [canonicalV1_iff_all_piCylinderCells_recurrent]
  constructor
  · intro h m a
    exact (machinBlockCode_recurrentValue_iff_piCylinderCode
      hSource m a).mpr (h m a)
  · intro h m a
    exact (machinBlockCode_recurrentValue_iff_piCylinderCode
      hSource m a).mp (h m a)

end Theory.PiDigits.MachinV1Equivalence

#print axioms
  Theory.PiDigits.MachinV1Equivalence.wordOccursAt_iff_listOfFn_blockAt_eq
#print axioms
  Theory.PiDigits.MachinV1Equivalence.canonicalV1_iff_all_piCylinderCells_recurrent
#print axioms
  Theory.PiDigits.MachinV1Equivalence.canonicalV1_iff_all_machinBlockCells_recurrent
