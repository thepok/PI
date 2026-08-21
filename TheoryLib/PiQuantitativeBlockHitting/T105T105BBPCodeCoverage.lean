import TheoryLib.PiQuantitativeBlockHitting.T104T104BBPSeriesIdentity

/-!
# T105: eventual transfer of fixed decimal block codes

This module packages the exact consequence of T104's eventual code equality:
arbitrarily-late occurrence of a fixed arithmetic code is invariant under
that equality.  It does not prove that any particular code occurs.
-/

noncomputable section

namespace Theory.PiDigits.T105BBPCodeCoverage

open Theory.PiDigits.OversampledBBPGridStability (decimalBlockCode)
open Theory.PiDigits.T100BBPRealBridge (bbpRealPartial)
open Theory.PiDigits.LongLagBlockCollisionDecay.T4
  (IrrationalityMeasureBelow)

/-- A sequence exhibits the fixed length-`m` code `b` arbitrarily late. -/
def ArbitrarilyLateCode (a : ℕ → ℝ) (m : ℕ) (b : ℤ) : Prop :=
  ∀ L : ℕ, ∃ N : ℕ, L ≤ N ∧ decimalBlockCode (a N) N m = b

/-- Eventual equality of code streams preserves fixed-code recurrence. -/
theorem arbitrarilyLateCode_iff_of_eventually_eq {a c : ℕ → ℝ}
    {m : ℕ} {b : ℤ}
    (hEventual : ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      decimalBlockCode (a N) N m = decimalBlockCode (c N) N m) :
    ArbitrarilyLateCode a m b ↔ ArbitrarilyLateCode c m b := by
  obtain ⟨C, hC⟩ := hEventual
  constructor
  · intro ha L
    obtain ⟨N, hN, hcode⟩ := ha (max L C)
    refine ⟨N, (le_max_left L C).trans hN, ?_⟩
    exact (hC N ((le_max_right L C).trans hN)).symm.trans hcode
  · intro hc L
    obtain ⟨N, hN, hcode⟩ := hc (max L C)
    refine ⟨N, (le_max_left L C).trans hN, ?_⟩
    exact (hC N ((le_max_right L C).trans hN)).trans hcode

/-- Under the explicit published source input, BBP and pi have the same
arbitrarily-late fixed arithmetic codes at every chosen block length. -/
theorem bbpPartial_arbitrarilyLateCode_iff_pi
    (hSource : IrrationalityMeasureBelow Real.pi 8)
    (m : ℕ) (b : ℤ) :
    ArbitrarilyLateCode (fun N ↦ bbpRealPartial (7 * N)) m b ↔
      ArbitrarilyLateCode (fun _ ↦ Real.pi) m b := by
  apply arbitrarilyLateCode_iff_of_eventually_eq
  exact
    Theory.PiDigits.T104BBPSeriesIdentity.pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq
      hSource m

end Theory.PiDigits.T105BBPCodeCoverage
