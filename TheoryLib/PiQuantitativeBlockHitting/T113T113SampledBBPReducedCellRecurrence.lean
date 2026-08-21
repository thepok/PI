import TheoryLib.PiQuantitativeBlockHitting.T106T106BBPForcedOrbit

/-!
# T113: exact sampled BBP successor and reduced cyclic cell

This module records exact rational bookkeeping for the sampled BBP orbit.  It
gives the base-ten successor recurrence, expands its forcing into seven single
fractions, and computes the orbit's cyclic cell from the actual reduced
numerator and denominator.  No density, coverage, cancellation, normality, or
V1 conclusion is claimed.
-/

namespace Theory.PiDigits.T113SampledBBPReducedCellRecurrence

open Theory.PiDigits.T106BBPForcedOrbit Theory.PiDigits.T98BBPArchimedeanTerm
  Theory.PiDigits.T77SelectedPadicDefectShell

/-- Exact base-ten successor recurrence for the scaled sampled BBP rational. -/
theorem scaledBBPPartialRat_succ (N : ℕ) :
    (10 : ℚ) ^ (N + 1) * bbpPartial (7 * (N + 1)) =
      10 * ((10 : ℚ) ^ N * bbpPartial (7 * N)) +
        sampledBBPForcingRat N := by
  simp only [sampledBBPForcingRat, pow_succ]
  ring

/-- The forcing is exactly seven single fractions over the four-pole denominator. -/
theorem sampledBBPForcingRat_eq_seven_singleFractions (N : ℕ) :
    sampledBBPForcingRat N =
      (10 : ℚ) ^ (N + 1) *
        ∑ j ∈ Finset.range 7,
          let k : ℕ := 7 * N + j + 1
          (120 * k ^ 2 + 151 * k + 47 : ℚ) /
            ((2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5) * 16 ^ k) := by
  rw [sampledBBPForcingRat_eq_sevenTerms]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact bbpCombinedTerm_eq (7 * N + j + 1)

private theorem floor_mul_fract_div_eq (q : ℕ) (m : ℤ) (d : ℕ) :
    ⌊(q : ℝ) * Int.fract ((m : ℝ) / (d : ℝ))⌋ =
      (q : ℤ) * (m % (d : ℤ)) / (d : ℤ) := by
  rw [Int.fract_div_intCast_eq_div_intCast_mod]
  have hcast :
      (q : ℝ) * (((m % (d : ℤ) : ℤ) : ℝ) / (d : ℝ)) =
        (((((q : ℤ) * (m % (d : ℤ)) : ℤ) : ℚ) / (d : ℚ) : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcast, Rat.floor_cast, Rat.floor_intCast_div_natCast]

private theorem cyclicCell_fract_rat_eq (q : ℕ) (x : ℚ) :
    DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (Int.fract (x : ℝ)) =
      (((q : ℤ) * (x.num % (x.den : ℤ))) / (x.den : ℤ) : ZMod q) := by
  have hxcast : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := Rat.cast_def x
  show ((⌊(q : ℝ) * Int.fract (Int.fract (x : ℝ))⌋ : ℤ) : ZMod q) = _
  rw [Int.fract_fract, hxcast]
  exact congrArg (fun z : ℤ => (z : ZMod q))
    (floor_mul_fract_div_eq q x.num x.den)

/-- The exact cyclic cell of the sampled orbit, computed from its reduced rational. -/
theorem cyclicCell_sampledBBPOrbit_eq_selectedCell (q N : ℕ) :
    let qN : ℚ := (10 : ℚ) ^ N * bbpPartial (7 * N)
    DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (sampledBBPOrbit N) =
      ((((q : ℤ) * (qN.num % (qN.den : ℤ))) / (qN.den : ℤ) : ℤ) :
        ZMod q) := by
  intro qN
  have horbit : sampledBBPOrbit N = Int.fract (qN : ℝ) := by
    change Int.fract ((10 : ℝ) ^ N * ((bbpPartial (7 * N) : ℚ) : ℝ)) = _
    congr 1
    simp only [qN]
    push_cast
    ring
  rw [horbit]
  exact cyclicCell_fract_rat_eq q qN

end Theory.PiDigits.T113SampledBBPReducedCellRecurrence
