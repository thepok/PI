import TheoryLib.PiPositiveDecimalFactorEntropy.T69T69FiveCaseCharging

/-!
# T71: imported convention audit for the certified finite census

This file imports, rather than redeclares, the kernel-checked T56 and T69
definitions used by the accompanying finite experiment. It makes no universal
claim about pi and proves none of C7, C2, C1, or positive decimal factor
entropy.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.T71CertifiedCensus

open DecimalFactorComplexity
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T69FiveCaseCharging
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- T71 uses exactly T56's natural-division sample length. -/
theorem sampleLength_eq (n : ℕ) :
    t56SampleLength n = 10 ^ (n / 2) := by
  rfl

/-- T71 uses exactly the endpoint-safe T56/T69 short-lag domain. -/
theorem shortLag_mem_iff {n r : ℕ} :
    r ∈ shortResidualLags n (t56SampleLength n) ↔
      0 < r ∧ r < n ∧ r < t56SampleLength n :=
  mem_W5_lags_iff

/-- The five alternatives used by the replay are T69's literal relation. -/
theorem cyclicAdjacent_iff_five_cases (q a b : ℕ) :
    CyclicAdjacent q a b ↔
      b = a ∨ b + 1 = a ∨ a + 1 = b ∨
        (a = 0 ∧ b + 1 = q) ∨ (b = 0 ∧ a + 1 = q) := by
  rfl

/-- T71 reports T69's three-layer load as exactly three base loads. -/
theorem E3_eq_three_base_load (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) :
    E3 n x = 3 * equalityComponentLoad x :=
  E3_eq_three_mul n x

/-- T71 imports T69's uniform charging statement without strengthening it. -/
theorem imported_uniformCharging : UniformCharging :=
  uniformCharging

/-- If every containing raw near-return set is empty, then T56's parameterized
short residual is zero for every choice of arithmetic parameters. -/
theorem shortResidualPairCount_eq_zero_of_raw_empty
    (μ c : ℝ) (Q0 m N : ℕ)
    (hRaw : ∀ r ∈ shortResidualLags m N, nearReturnStarts m N r = ∅) :
    shortResidualPairCount μ c Q0 m N = 0 := by
  classical
  unfold shortResidualPairCount
  apply Nat.mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro r hr
  unfold residualNearReturnStarts
  rw [hRaw r hr]
  simp

end DecimalFactorComplexity.T71CertifiedCensus

#print axioms DecimalFactorComplexity.T71CertifiedCensus.sampleLength_eq
#print axioms DecimalFactorComplexity.T71CertifiedCensus.shortLag_mem_iff
#print axioms DecimalFactorComplexity.T71CertifiedCensus.cyclicAdjacent_iff_five_cases
#print axioms DecimalFactorComplexity.T71CertifiedCensus.E3_eq_three_base_load
#print axioms DecimalFactorComplexity.T71CertifiedCensus.imported_uniformCharging
#print axioms DecimalFactorComplexity.T71CertifiedCensus.shortResidualPairCount_eq_zero_of_raw_empty
