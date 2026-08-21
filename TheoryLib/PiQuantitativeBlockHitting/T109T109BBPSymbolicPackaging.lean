import TheoryLib.PiQuantitativeBlockHitting.T104T104BBPSeriesIdentity
import TheoryLib.PiQuantitativeBlockHitting.T37T37FloorSymbolicBridge

/-!
# T109: symbolic packaging of the seven-oversampled BBP block code

Under the explicit external hypothesis
`Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow Real.pi 8`,
the seven-oversampled BBP partial-sum floor code is eventually identified with
the repository's symbolic pi cylinder code and its same-position contiguous
block value.

These are eventual code identifications only.  They prove no prescribed-word
occurrence, density, normality, mixing, digit-distribution, or V1 statement.
-/

namespace Theory.PiDigits.T109BBPSymbolicPackaging

open Theory.PiDigits.T104BBPSeriesIdentity

/-- Under the explicit irrationality-measure hypothesis, the Fin-valued
seven-oversampled BBP block-code stream eventually equals the symbolic pi
cylinder stream at the same zero-based start. -/
theorem eventually_bbpBlockCode_eq_piCylinderCode
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) (m : ℕ) :
    (fun N : ℕ =>
        Theory.PiDigits.FloorSymbolicBridge.decimalBlockFinCode
          (Theory.PiDigits.T100BBPRealBridge.bbpRealPartial (7 * N)) N m)
      =ᶠ[Filter.atTop]
      DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m := by
  obtain ⟨C, hC⟩ :=
    pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq hSource m
  filter_upwards [Filter.eventually_ge_atTop C] with N hN
  apply Fin.ext
  have hcode := hC N hN
  rw [Theory.PiDigits.FloorSymbolicBridge.decimalBlockCode_eq_intCast_decimalBlockFinCode,
    Theory.PiDigits.FloorSymbolicBridge.decimalBlockCode_pi_eq_piCylinderCode_val] at hcode
  exact_mod_cast hcode

/-- Under the same explicit hypothesis, the integer seven-oversampled BBP
floor code eventually equals the value of the same-position contiguous
symbolic pi block. -/
theorem pi_eventually_bbpPartial_code_eq_blockAt_wordValue
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      Theory.PiDigits.OversampledBBPGridStability.decimalBlockCode
          (Theory.PiDigits.T100BBPRealBridge.bbpRealPartial (7 * N)) N m =
        (Theory.PiDigits.T20.wordValue
          (List.ofFn
            (DecimalFactorComplexity.blockAt Theory.PiDigits.piDigit m N)) : ℤ) :=
  fun m => by
    obtain ⟨C, hC⟩ :=
      pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq hSource m
    exact ⟨C, fun N hN ↦
      (hC N hN).trans
        (Theory.PiDigits.FloorSymbolicBridge.decimalBlockCode_pi_eq_blockAt_wordValue
          N m)⟩

end Theory.PiDigits.T109BBPSymbolicPackaging
