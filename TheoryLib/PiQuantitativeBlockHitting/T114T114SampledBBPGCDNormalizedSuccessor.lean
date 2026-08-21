import TheoryLib.PiQuantitativeBlockHitting.T113T113SampledBBPReducedCellRecurrence

/-!
# T114: gcd-normalized sampled BBP successor

This module computes the actual reduced numerator and denominator after one
sampled BBP successor step and substitutes that pair into T113's exact cyclic
cell formula.  It is exact rational bookkeeping only: no gcd estimate, cell
occupancy, cancellation, density, normality, or V1 conclusion is claimed.
-/

namespace Theory.PiDigits.T114SampledBBPGCDNormalizedSuccessor

open scoped Rat

private theorem divInt_num_den_of_pos (U : ℤ) (V : ℕ) (hV : 0 < V) :
    (U /. (V : ℤ)).num = U / (Int.gcd U (V : ℤ) : ℤ) ∧
      (U /. (V : ℤ)).den = V / Int.gcd U (V : ℤ) := by
  have hVz : 0 < (V : ℤ) := by exact_mod_cast hV
  have hne : (V : ℤ) ≠ 0 := ne_of_gt hVz
  constructor
  · rw [Rat.num_divInt, Int.sign_eq_one_of_pos hVz, Int.one_mul, Int.gcd_comm]
  · rw [Rat.den_divInt, if_neg hne, Int.natAbs_natCast, Int.gcd_comm]

/-- The exact reduced successor pair, normalized by its full cross-product gcd. -/
theorem scaledBBPPartialRat_succ_num_den (N : ℕ) :
    let Q : ℚ := (10 : ℚ) ^ N *
      Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N)
    let F : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N
    let U : ℤ := 10 * Q.num * (F.den : ℤ) + F.num * (Q.den : ℤ)
    let V : ℕ := Q.den * F.den
    let g : ℕ := Int.gcd U (V : ℤ)
    ((10 : ℚ) ^ (N + 1) *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * (N + 1))).num =
      U / (g : ℤ) ∧
    ((10 : ℚ) ^ (N + 1) *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * (N + 1))).den =
      V / g := by
  intro Q F U V g
  have hQden : 0 < Q.den := Rat.den_pos _
  have hFden : 0 < F.den := Rat.den_pos _
  have hVpos : 0 < V := mul_pos hQden hFden
  have hforcing : F = (10 : ℚ) ^ (N + 1) *
      (Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * (N + 1)) -
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N)) := rfl
  have hsucc : (10 : ℚ) ^ (N + 1) *
      Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * (N + 1)) =
      10 * Q + F := by
    rw [hforcing, pow_succ']
    ring
  have hdiv : 10 * Q + F = U /. (V : ℤ) := by
    rw [← Rat.intCast_div_eq_divInt U (V : ℤ),
      ← Rat.num_div_den Q, ← Rat.num_div_den F]
    simp only [U, V]
    push_cast
    field_simp
  rw [hsucc, hdiv]
  exact divInt_num_den_of_pos U V hVpos

/-- T113's next orbit cell, expressed through the exact gcd-normalized pair. -/
theorem cyclicCell_sampledBBPOrbit_succ_eq_gcdNormalized (q N : ℕ) :
    let Q : ℚ := (10 : ℚ) ^ N *
      Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N)
    let F : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N
    let U : ℤ := 10 * Q.num * (F.den : ℤ) + F.num * (Q.den : ℤ)
    let V : ℕ := Q.den * F.den
    let g : ℕ := Int.gcd U (V : ℤ)
    DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit (N + 1)) =
      ((((q : ℤ) * ((U / (g : ℤ)) % ((V / g : ℕ) : ℤ))) /
        ((V / g : ℕ) : ℤ) : ℤ) : ZMod q) := by
  intro Q F U V g
  have hpair := scaledBBPPartialRat_succ_num_den N
  change DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
      (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit (N + 1)) = _
  rw [Theory.PiDigits.T113SampledBBPReducedCellRecurrence.cyclicCell_sampledBBPOrbit_eq_selectedCell]
  rw [hpair.1, hpair.2]

end Theory.PiDigits.T114SampledBBPGCDNormalizedSuccessor
