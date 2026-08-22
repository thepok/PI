import TheoryLib.PiQuantitativeBlockHitting.T118T118SampledBBPNormalizedExcessCell

/-!
# T119: same-cell cross-determinant inequality for sampled BBP successors

Pure representation consequence of canonical T118.  First, a generic integer
lemma: two fractions `R₁/W₁` and `R₂/W₂` lying in the same endpoint-exact
half-open `q`-cell (representative `a`) satisfy
`q * |R₁ * W₂ - R₂ * W₁| < W₁ * W₂`.  Then this lemma is specialized to two
sampled-BBP successors at indices `N` and `M`, using T118's exact
normalized-excess cell equivalence independently at each index.

No existence, recurrence, pair count, occupancy, density, cancellation,
normality, decimal-occurrence, V1, or Pi statement is made.
-/

namespace Theory.PiDigits.T119SampledBBPSameCellCrossDeterminant

/-- Two fractions in the same endpoint-exact half-open `q`-cell have a small
cross-determinant: `q * |R₁ * W₂ - R₂ * W₁| < W₁ * W₂`. -/
theorem sameHalfOpenCell_crossDeterminant :
    ∀ (q a R₁ R₂ W₁ W₂ : ℤ), 0 < q → 0 < W₁ → 0 < W₂ →
      a * W₁ ≤ q * R₁ → q * R₁ < (a + 1) * W₁ →
      a * W₂ ≤ q * R₂ → q * R₂ < (a + 1) * W₂ →
      q * |R₁ * W₂ - R₂ * W₁| < W₁ * W₂ := by
  intro q a R₁ R₂ W₁ W₂ hq hW₁ hW₂ h₁l h₁u h₂l h₂u
  have m₁ : a * (W₁ * W₂) ≤ q * R₁ * W₂ := by
    calc a * (W₁ * W₂) = a * W₁ * W₂ := by ring
      _ ≤ q * R₁ * W₂ := Int.mul_le_mul_of_nonneg_right h₁l hW₂.le
  have m₂ : q * R₁ * W₂ < a * (W₁ * W₂) + W₁ * W₂ := by
    calc q * R₁ * W₂ < (a + 1) * W₁ * W₂ := Int.mul_lt_mul_of_pos_right h₁u hW₂
      _ = a * (W₁ * W₂) + W₁ * W₂ := by ring
  have m₃ : a * (W₁ * W₂) ≤ q * R₂ * W₁ := by
    calc a * (W₁ * W₂) = a * W₂ * W₁ := by ring
      _ ≤ q * R₂ * W₁ := Int.mul_le_mul_of_nonneg_right h₂l hW₁.le
  have m₄ : q * R₂ * W₁ < a * (W₁ * W₂) + W₁ * W₂ := by
    calc q * R₂ * W₁ < (a + 1) * W₂ * W₁ := Int.mul_lt_mul_of_pos_right h₂u hW₁
      _ = a * (W₁ * W₂) + W₁ * W₂ := by ring
  have hexp : q * (R₁ * W₂ - R₂ * W₁) = q * R₁ * W₂ - q * R₂ * W₁ := by ring
  have habs : q * |R₁ * W₂ - R₂ * W₁| = |q * (R₁ * W₂ - R₂ * W₁)| := by
    rw [abs_mul, abs_of_nonneg hq.le]
  rw [habs, abs_lt, hexp]
  constructor <;> linarith

/-- Conditional specialization to two sampled BBP successors whose cyclic
cells are given to coincide in the explicitly named cell `a`. -/
theorem sampledBBPSuccessors_sameCell_crossDeterminant
    (N M q a : ℕ) (hq : 0 < q) (haq : a < q)
    (hN : DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit (N + 1)) = (a : ZMod q))
    (hM : DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit (M + 1)) = (a : ZMod q)) :
    (let QN : ℚ := (10 : ℚ) ^ N * Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N);
      let FN : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N;
      let HN : ℕ := Nat.gcd QN.den FN.den;
      let dN : ℕ := QN.den / HN;
      let eN : ℕ := FN.den / HN;
      let XN : ℤ := 10 * QN.num * (eN : ℤ) + FN.num * (dN : ℤ);
      let kN : ℕ := Int.gcd XN ((HN * dN : ℕ) : ℤ);
      let WN : ℕ := HN * dN * eN / kN;
      let RN : ℤ := (XN / (kN : ℤ)) % (WN : ℤ);
      let QM : ℚ := (10 : ℚ) ^ M * Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * M);
      let FM : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat M;
      let HM : ℕ := Nat.gcd QM.den FM.den;
      let dM : ℕ := QM.den / HM;
      let eM : ℕ := FM.den / HM;
      let XM : ℤ := 10 * QM.num * (eM : ℤ) + FM.num * (dM : ℤ);
      let kM : ℕ := Int.gcd XM ((HM * dM : ℕ) : ℤ);
      let WM : ℕ := HM * dM * eM / kM;
      let RM : ℤ := (XM / (kM : ℤ)) % (WM : ℤ);
      (q : ℤ) * |RN * (WM : ℤ) - RM * (WN : ℤ)| < (WN : ℤ) * (WM : ℤ)) := by
  intro QN FN HN dN eN XN kN WN RN QM FM HM dM eM XM kM WM RM
  have hwposN : 0 < WN :=
    (Theory.PiDigits.T118SampledBBPNormalizedExcessCell.sampledBBPSuccessor_normalizedExcess_num_den_pos N).2.2.2
  have hwposM : 0 < WM :=
    (Theory.PiDigits.T118SampledBBPNormalizedExcessCell.sampledBBPSuccessor_normalizedExcess_num_den_pos M).2.2.2
  have hintN :=
    Theory.PiDigits.T118SampledBBPNormalizedExcessCell.sampledBBPSuccessor_cell_eq_iff_normalizedExcess_interval N q a hq haq
  have hintM :=
    Theory.PiDigits.T118SampledBBPNormalizedExcessCell.sampledBBPSuccessor_cell_eq_iff_normalizedExcess_interval M q a hq haq
  have hlohiN : (a : ℤ) * (WN : ℤ) ≤ (q : ℤ) * RN ∧
      (q : ℤ) * RN < ((a + 1 : ℕ) : ℤ) * (WN : ℤ) := hintN.mp hN
  have hlohiM : (a : ℤ) * (WM : ℤ) ≤ (q : ℤ) * RM ∧
      (q : ℤ) * RM < ((a + 1 : ℕ) : ℤ) * (WM : ℤ) := hintM.mp hM
  exact sameHalfOpenCell_crossDeterminant (q : ℤ) a RN RM WN WM
    (by exact_mod_cast hq) (by exact_mod_cast hwposN) (by exact_mod_cast hwposM)
    hlohiN.1 hlohiN.2 hlohiM.1 hlohiM.2

end Theory.PiDigits.T119SampledBBPSameCellCrossDeterminant
