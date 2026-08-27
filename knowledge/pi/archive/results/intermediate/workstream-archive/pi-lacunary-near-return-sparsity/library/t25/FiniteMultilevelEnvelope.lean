import TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting
import TheoryLib.PiLacunaryNearReturnSparsity.T23FiniteSuccessorEnvelope

/-!
# Exact finite multilevel successor-splitting envelopes

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves a finite A14 sibling statement. It does not assert C2,
canonical A1, or any arithmetic meaning for residual dominant successors.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.FiniteMultilevelEnvelope

open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.FiniteSuccessorEnvelope

/-- The finite triangular range of checkpoint/depth pairs. Checkpoints satisfy
`k0 <= k <= k1`, depths satisfy `m0 <= m <= m1`, and `m <= k`. -/
def finiteTriangle (k0 k1 m0 m1 : ℕ) : Finset (ℕ × ℕ) :=
  (Icc k0 k1 ×ˢ Icc m0 m1).filter fun km => km.2 ≤ km.1

theorem mem_finiteTriangle_iff
    (k0 k1 m0 m1 k m : ℕ) :
    (k, m) ∈ finiteTriangle k0 k1 m0 m1 ↔
      k0 ≤ k ∧ k ≤ k1 ∧ m0 ≤ m ∧ m ≤ m1 ∧ m ≤ k := by
  simp [finiteTriangle, and_assoc]

/-- The union of all T23 row breakpoints used by the finite triangle. For
each `(k,m)` it includes exactly the rows `l < m` at cutoff `N k`. -/
def multilevelBreakpoints
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ) : Finset ℝ := by
  classical
  exact (finiteTriangle k0 k1 m0 m1).biUnion fun km =>
    (range km.2).biUnion fun l => piRowParameterBreakpoints l (N km.1)

/-- Membership in the multilevel breakpoint union exposes the checkpoint,
depth, row, finite endpoints, and the underlying T23 row breakpoint. -/
theorem mem_multilevelBreakpoints_iff
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ) (r : ℝ) :
    r ∈ multilevelBreakpoints k0 k1 m0 m1 N ↔
      ∃ k m l : ℕ,
        k0 ≤ k ∧ k ≤ k1 ∧ m0 ≤ m ∧ m ≤ m1 ∧ m ≤ k ∧ l < m ∧
          r ∈ piRowParameterBreakpoints l (N k) := by
  classical
  simp only [multilevelBreakpoints, mem_biUnion, mem_range]
  constructor
  · rintro ⟨⟨k, m⟩, hkm, l, hl, hr⟩
    obtain ⟨hk0, hk1, hm0, hm1, hmk⟩ :=
      (mem_finiteTriangle_iff k0 k1 m0 m1 k m).mp hkm
    exact ⟨k, m, l, hk0, hk1, hm0, hm1, hmk, hl, hr⟩
  · rintro ⟨k, m, l, hk0, hk1, hm0, hm1, hmk, hl, hr⟩
    exact ⟨(k, m),
      (mem_finiteTriangle_iff k0 k1 m0 m1 k m).mpr
        ⟨hk0, hk1, hm0, hm1, hmk⟩,
      l, hl, hr⟩

/-- T23's exact row inequality, deliberately written without division so it
also covers a zero-energy row. -/
def rowThreshold (l cutoff : ℕ) (eta mu : ℝ) : Prop :=
  mu * (piCylinderCollisionEnergy l cutoff : ℝ) ≤
    piRowSplitEnergy l cutoff eta

/-- A T14 splitting row is exactly its T23 finite threshold inequality. -/
theorem quantitativeSplittingLevel_iff_rowThreshold
    (l cutoff : ℕ) (eta mu : ℝ) :
    QuantitativeSplittingLevel l cutoff mu eta ↔
      rowThreshold l cutoff eta mu := by
  simpa [rowThreshold, piRowSplitEnergy, rowSplitEnergy,
    piSecondLargestSuccessor, pi_parentOccupancy_eq_fiber_card] using
      (pi_quantitativeSplittingLevel_iff_exact_envelope l cutoff mu eta)

/-- The exact cumulative number of row thresholds below depth `m`. This is a
finite collection of inequalities in `eta` and `mu`. -/
def cumulativeThresholdCount
    (m cutoff : ℕ) (eta mu : ℝ) : ℕ := by
  classical
  exact ((range m).filter fun l => rowThreshold l cutoff eta mu).card

/-- The explicit cumulative threshold count equals T14's splitting count. -/
theorem cumulativeThresholdCount_eq_piSplittingLevelCount
    (m cutoff : ℕ) (eta mu : ℝ) :
    cumulativeThresholdCount m cutoff eta mu =
      piSplittingLevelCount m cutoff mu eta := by
  classical
  unfold cumulativeThresholdCount piSplittingLevelCount piSplittingLevels
  apply congrArg card
  ext l
  simp only [mem_filter, mem_range]
  rw [quantitativeSplittingLevel_iff_rowThreshold]

/-- The finite T14 parameter region. Every endpoint and every affine
splitting-count inequality is part of the definition. -/
def MultilevelFeasible
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (eta mu d B : ℝ) : Prop :=
  k0 ≤ k1 ∧ m0 ≤ m1 ∧
    (∀ k ∈ Icc k0 k1, 1 ≤ N k) ∧
    0 < eta ∧ eta ≤ 1 / 10 ∧
    0 < mu ∧ mu < 1 ∧ 0 < d ∧ 0 ≤ B ∧
    ∀ km ∈ finiteTriangle k0 k1 m0 m1,
      d * (km.2 : ℝ) - B ≤
        (piSplittingLevelCount km.2 (N km.1) mu eta : ℝ)

/-- The same region expressed entirely by finitely many T23 row thresholds
and cumulative affine inequalities. -/
def ExactMultilevelEnvelope
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (eta mu d B : ℝ) : Prop :=
  k0 ≤ k1 ∧ m0 ≤ m1 ∧
    (∀ k ∈ Icc k0 k1, 1 ≤ N k) ∧
    0 < eta ∧ eta ≤ 1 / 10 ∧
    0 < mu ∧ mu < 1 ∧ 0 < d ∧ 0 ≤ B ∧
    ∀ km ∈ finiteTriangle k0 k1 m0 m1,
      d * (km.2 : ℝ) - B ≤
        (cumulativeThresholdCount km.2 (N km.1) eta mu : ℝ)

/-- Both directions of the exact finite multilevel characterization. The
right side consists only of endpoint conditions and finitely many explicit
row and cumulative affine thresholds. -/
theorem multilevelFeasible_iff_exactMultilevelEnvelope
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (eta mu d B : ℝ) :
    MultilevelFeasible k0 k1 m0 m1 N eta mu d B ↔
      ExactMultilevelEnvelope k0 k1 m0 m1 N eta mu d B := by
  unfold MultilevelFeasible ExactMultilevelEnvelope
  simp only [cumulativeThresholdCount_eq_piSplittingLevelCount]

/-- Fully expanded form of the multilevel envelope. It displays the finite
checkpoint, depth, and row ranges and every `eta`, `mu`, `d`, and `B`
inequality without requiring a reader to unfold the envelope definitions. -/
theorem multilevelFeasible_iff_explicit_thresholds
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (eta mu d B : ℝ) :
    MultilevelFeasible k0 k1 m0 m1 N eta mu d B ↔
      k0 ≤ k1 ∧ m0 ≤ m1 ∧
      (∀ k : ℕ, k0 ≤ k → k ≤ k1 → 1 ≤ N k) ∧
      0 < eta ∧ eta ≤ 1 / 10 ∧
      0 < mu ∧ mu < 1 ∧ 0 < d ∧ 0 ≤ B ∧
      ∀ k : ℕ, k0 ≤ k → k ≤ k1 →
        ∀ m : ℕ, m0 ≤ m → m ≤ m1 → m ≤ k →
          d * (m : ℝ) - B ≤
            (((range m).filter fun l =>
              mu * (piCylinderCollisionEnergy l (N k) : ℝ) ≤
                ∑ a : Fin (10 ^ l),
                  if eta * (piCylinderFiber l (N k) a).card ≤
                      piSecondLargestSuccessor l (N k) a then
                    ((piCylinderFiber l (N k) a).card : ℝ) ^ 2
                  else 0).card : ℝ) := by
  classical
  rw [multilevelFeasible_iff_exactMultilevelEnvelope]
  constructor
  · rintro ⟨hk, hm, hN, heta, hetaUpper, hmu, hmuUpper, hd, hB,
      henvelope⟩
    refine ⟨hk, hm, ?_, heta, hetaUpper, hmu, hmuUpper, hd, hB, ?_⟩
    · intro k hk0 hk1
      exact hN k (mem_Icc.mpr ⟨hk0, hk1⟩)
    · intro k hk0 hk1 m hm0 hm1 hmk
      have hkm : (k, m) ∈ finiteTriangle k0 k1 m0 m1 :=
        (mem_finiteTriangle_iff k0 k1 m0 m1 k m).mpr
          ⟨hk0, hk1, hm0, hm1, hmk⟩
      simpa [cumulativeThresholdCount, rowThreshold, piRowSplitEnergy,
        rowSplitEnergy, piSecondLargestSuccessor,
        pi_parentOccupancy_eq_fiber_card] using
        henvelope (k, m) hkm
  · rintro ⟨hk, hm, hN, heta, hetaUpper, hmu, hmuUpper, hd, hB,
      henvelope⟩
    refine ⟨hk, hm, ?_, heta, hetaUpper, hmu, hmuUpper, hd, hB, ?_⟩
    · intro k hkMem
      obtain ⟨hk0, hk1⟩ := mem_Icc.mp hkMem
      exact hN k hk0 hk1
    · rintro ⟨k, m⟩ hkm
      obtain ⟨hk0, hk1, hm0, hm1, hmk⟩ :=
        (mem_finiteTriangle_iff k0 k1 m0 m1 k m).mp hkm
      simpa [cumulativeThresholdCount, rowThreshold, piRowSplitEnergy,
        rowSplitEnergy, piSecondLargestSuccessor,
        pi_parentOccupancy_eq_fiber_card] using
        henvelope k hk0 hk1 m hm0 hm1 hmk

/-- If an interval contains no member of the finite breakpoint union, every
cumulative threshold count is unchanged on that interval. -/
theorem cumulativeThresholdCount_eq_of_no_multilevelBreakpoint
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (eta b mu : ℝ) (heta : 0 < eta) (hetab : eta ≤ b)
    (hb : b ≤ 1 / 10)
    (hgap : ∀ r ∈ multilevelBreakpoints k0 k1 m0 m1 N,
      eta ≤ r → ¬ r < b)
    (k m : ℕ) (hkm : (k, m) ∈ finiteTriangle k0 k1 m0 m1) :
    cumulativeThresholdCount m (N k) eta mu =
      cumulativeThresholdCount m (N k) b mu := by
  classical
  unfold cumulativeThresholdCount
  apply congrArg card
  ext l
  simp only [mem_filter, mem_range]
  apply and_congr_right
  intro hl
  have hrowGap : ∀ r ∈ piRowParameterBreakpoints l (N k),
      eta ≤ r → ¬ r < b := by
    intro r hr hetaR
    apply hgap r
    · apply (mem_multilevelBreakpoints_iff k0 k1 m0 m1 N r).mpr
      obtain ⟨hk0, hk1, hm0, hm1, hmk⟩ :=
        (mem_finiteTriangle_iff k0 k1 m0 m1 k m).mp hkm
      exact ⟨k, m, l, hk0, hk1, hm0, hm1, hmk, hl, hr⟩
    · exact hetaR
  have hsplit : piRowSplitEnergy l (N k) eta =
      piRowSplitEnergy l (N k) b := by
    exact rowSplitEnergy_eq_of_no_breakpoint
      (piSuccessorCount l (N k)) eta b heta hetab hb hrowGap
  simp only [rowThreshold, hsplit]

/-- Consequently the complete finite feasible region is constant as `eta`
moves through a left-open/right-closed cell cut out by the union of T23 row
breakpoints. The `mu`, `d`, and `B` thresholds remain literally displayed in
`ExactMultilevelEnvelope`. -/
theorem exactMultilevelEnvelope_iff_at_eta_cell_endpoint
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (eta b mu d B : ℝ) (heta : 0 < eta) (hetab : eta ≤ b)
    (hb : b ≤ 1 / 10)
    (hgap : ∀ r ∈ multilevelBreakpoints k0 k1 m0 m1 N,
      eta ≤ r → ¬ r < b) :
    ExactMultilevelEnvelope k0 k1 m0 m1 N eta mu d B ↔
      ExactMultilevelEnvelope k0 k1 m0 m1 N b mu d B := by
  constructor
  · rintro ⟨hk, hm, hN, _heta, _hetaUpper, hmu, hmuUpper, hd, hB,
      henvelope⟩
    refine ⟨hk, hm, hN, heta.trans_le hetab, hb, hmu, hmuUpper, hd, hB, ?_⟩
    intro km hkm
    rw [← cumulativeThresholdCount_eq_of_no_multilevelBreakpoint
      k0 k1 m0 m1 N eta b mu heta hetab hb hgap km.1 km.2 hkm]
    exact henvelope km hkm
  · rintro ⟨hk, hm, hN, _hbpos, _hbUpper, hmu, hmuUpper, hd, hB,
      henvelope⟩
    refine ⟨hk, hm, hN, heta, hetab.trans hb, hmu, hmuUpper, hd, hB, ?_⟩
    intro km hkm
    rw [cumulativeThresholdCount_eq_of_no_multilevelBreakpoint
      k0 k1 m0 m1 N eta b mu heta hetab hb hgap km.1 km.2 hkm]
    exact henvelope km hkm

/-- Explicit finite occupancy certificate on every row in the triangle.
It separates low occupancy from any interpretation of nonsplitting as an
arithmetic obstruction. -/
def FiniteOccupancyCertificate
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (R : ℕ) (kappa : ℝ) : Prop :=
  0 < kappa ∧
    ∀ km ∈ finiteTriangle k0 k1 m0 m1, ∀ l ∈ range km.2,
      kappa * (piCylinderCollisionEnergy l (N km.1) : ℝ) ≤
        lowMultiplicityEnergy
          (fun a : Fin (10 ^ l) => (piCylinderFiber l (N km.1) a).card) R

/-- A finite occupancy certificate gives the explicit T23 energy ceiling at
every checkpoint, depth, and row in the declared triangle. -/
theorem finite_occupancyCertificate_collisionEnergy_le
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (R : ℕ) (kappa : ℝ)
    (hcert : FiniteOccupancyCertificate k0 k1 m0 m1 N R kappa) :
    ∀ k ∈ Icc k0 k1, ∀ m ∈ Icc m0 m1, m ≤ k → ∀ l ∈ range m,
      (piCylinderCollisionEnergy l (N k) : ℝ) ≤ R * N k / kappa := by
  rintro k hk m hm hmk l hl
  rcases hcert with ⟨hkappa, hrows⟩
  apply pi_collisionEnergy_le_of_lowMultiplicity_dominates
    l (N k) R kappa hkappa
  apply hrows (k, m)
  · apply (mem_finiteTriangle_iff k0 k1 m0 m1 k m).mpr
    obtain ⟨hk0, hk1⟩ := (mem_Icc.mp hk)
    obtain ⟨hm0, hm1⟩ := (mem_Icc.mp hm)
    exact ⟨hk0, hk1, hm0, hm1, hmk⟩
  · exact hl

/-- Quantifier-expanded occupancy corollary. The premise and conclusion range
over the same explicit finite triangle and the same rows `l < m`. -/
theorem finite_occupancyCertificate_explicit
    (k0 k1 m0 m1 : ℕ) (N : ℕ → ℕ)
    (R : ℕ) (kappa : ℝ) (hkappa : 0 < kappa)
    (hdominates :
      ∀ k : ℕ, k0 ≤ k → k ≤ k1 →
        ∀ m : ℕ, m0 ≤ m → m ≤ m1 → m ≤ k →
          ∀ l : ℕ, l < m →
        kappa * (piCylinderCollisionEnergy l (N k) : ℝ) ≤
          lowMultiplicityEnergy
            (fun a : Fin (10 ^ l) => (piCylinderFiber l (N k) a).card) R) :
    ∀ k : ℕ, k0 ≤ k → k ≤ k1 →
      ∀ m : ℕ, m0 ≤ m → m ≤ m1 → m ≤ k →
        ∀ l : ℕ, l < m →
          (piCylinderCollisionEnergy l (N k) : ℝ) ≤ R * N k / kappa := by
  intro k hk0 hk1 m hm0 hm1 hmk l hl
  exact pi_collisionEnergy_le_of_lowMultiplicity_dominates
    l (N k) R kappa hkappa
      (hdominates k hk0 hk1 m hm0 hm1 hmk l hl)

end DecimalFactorComplexity.FiniteMultilevelEnvelope

#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.mem_multilevelBreakpoints_iff
#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.cumulativeThresholdCount_eq_piSplittingLevelCount
#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.multilevelFeasible_iff_exactMultilevelEnvelope
#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.multilevelFeasible_iff_explicit_thresholds
#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.cumulativeThresholdCount_eq_of_no_multilevelBreakpoint
#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.exactMultilevelEnvelope_iff_at_eta_cell_endpoint
#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.finite_occupancyCertificate_collisionEnergy_le
#print axioms DecimalFactorComplexity.FiniteMultilevelEnvelope.finite_occupancyCertificate_explicit
