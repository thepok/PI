import TheoryLib.PiLongLagBlockCollisionDecay.T90T90CenteredCriticalBandCore

/-!
# T97: exact variable-phase bridge to T31 CROSS

Canonical local source: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file concerns only the Lebesgue-variable-phase residual sibling A12. It
proves no statement at `Real.pi` and no instance of C1, C2, or C3.
-/

noncomputable section

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T97

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T87
open Theory.PiDigits.LongLagBlockCollisionDecay.T90
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- The lower-dimensional cosine sum when only the phase value is replaced by
the Lebesgue variable `alpha`. -/
def variableBlockCoreSum
    (m : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ blockCoreDomain m B,
    Real.cos (2 * Real.pi * α * (h : ℝ) * positiveDecimalFrequency p)

/-- The two imported Boolean orientations give exactly twice the real cosine
at an arbitrary phase. This is the variable-phase analogue of T90's fixed-pi
orientation identity, proved directly rather than inferred from that theorem. -/
theorem two_orientations_variablePhase_eq_cosine
    (h : ℕ) (p : LongPairCore) (α : ℝ) :
    Theory.PiDigits.T27.phase (h : ℤ)
          ((signedDecimalFrequency (false, p) : ℝ) * α) +
        Theory.PiDigits.T27.phase (h : ℤ)
          ((signedDecimalFrequency (true, p) : ℝ) * α) =
      ((2 * Real.cos (2 * Real.pi * α * (h : ℝ) *
        positiveDecimalFrequency p) : ℝ) : ℂ) := by
  simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte]
  unfold Theory.PiDigits.T27.phase
  let x : ℝ := 2 * Real.pi * α * (h : ℝ) * positiveDecimalFrequency p
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
          ((((↑(-(positiveDecimalFrequency p : ℤ)) : ℝ) * α : ℝ) : ℂ)) =
        ((-x : ℝ) : ℂ) * Complex.I := by
    dsimp [x]
    push_cast
    ring
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
          (((((positiveDecimalFrequency p : ℕ) : ℤ) : ℝ) * α : ℝ) : ℂ) =
        (x : ℂ) * Complex.I := by
    dsimp [x]
    push_cast
    ring
  rw [hneg, hpos, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg]
  push_cast
  dsimp [x]
  push_cast
  ring

/-- Exact arbitrary-phase block-vector reduction. It retains T90's core,
both orientations, both signs, and the factor two. -/
theorem canonicalBlockVector_eight_one_variable_eq_coreSum
    (Q0 m : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) (hm : 1 ≤ m) :
    canonicalBlockVector (8 : ℝ) 1 Q0 m B α h =
      ((2 * variableBlockCoreSum m B h α : ℝ) : ℂ) := by
  rw [canonicalBlockVector_eq_sum_blockRecords,
    blockRecordDomain_eight_one_eq_orientations Q0 m B hm,
    Finset.sum_product, Finset.sum_comm]
  calc
    (∑ p ∈ blockCoreDomain m B,
        ∑ b ∈ (Finset.univ : Finset Bool),
          Theory.PiDigits.T27.phase (h : ℤ)
            ((signedDecimalFrequency (b, p) : ℝ) * α)) =
        ∑ p ∈ blockCoreDomain m B,
          (Theory.PiDigits.T27.phase (h : ℤ)
              ((signedDecimalFrequency (false, p) : ℝ) * α) +
            Theory.PiDigits.T27.phase (h : ℤ)
              ((signedDecimalFrequency (true, p) : ℝ) * α)) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [Fintype.univ_bool, add_comm]
    _ = ∑ p ∈ blockCoreDomain m B,
          ((2 * Real.cos (2 * Real.pi * α * (h : ℝ) *
            positiveDecimalFrequency p) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact two_orientations_variablePhase_eq_cosine h p α
    _ = ((2 * variableBlockCoreSum m B h α : ℝ) : ℂ) := by
      unfold variableBlockCoreSum
      push_cast
      rw [Finset.mul_sum]

/-- T90's full square function with only the Fourier phase replaced by the
Lebesgue variable. Every canonical block, inclusive multiplier, literal width,
and the four ordered sign products remain visible. -/
theorem widthWeightedSquareFunction_eight_one_variable_eq_coreSum
    (Q0 m N : ℕ) (α : ℝ) (hm : 1 ≤ m) :
    widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N α =
      ((translatedCanonicalBlocks N).map fun B =>
        (4 * ∑ h ∈ Finset.Icc (1 : ℕ) (10 ^ m),
          (variableBlockCoreSum m B h α) ^ 2) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum := by
  unfold widthWeightedSquareFunction blockSquaredEnergy inclusiveFrequencies
    decimalFrequency
  congr 1
  apply List.map_congr_left
  intro B hB
  rw [widthWeight_eq_endpoints]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [canonicalBlockVector_eight_one_variable_eq_coreSum Q0 m B h α hm,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- The centered variable-phase observable appearing in T95/T96, defined
without importing either sketch. -/
def variableCenteredCriticalRemainder
    (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N α -
    recordDiagonal Q0 m N

/-- Fully literal centered formula. The first coefficient `4` is the four
ordered sign products; the diagonal coefficient `2` is the two orientations;
the multiplier interval is inclusive and every width is unchanged. -/
theorem variableCenteredCriticalRemainder_literal
    (Q0 m N : ℕ) (α : ℝ) (hm : 1 ≤ m) :
    variableCenteredCriticalRemainder Q0 m N α =
      ((translatedCanonicalBlocks N).map fun B =>
        (4 * ∑ h ∈ Finset.Icc (1 : ℕ) (10 ^ m),
          (∑ p ∈ blockCoreDomain m B,
            Real.cos (2 * Real.pi * α * (h : ℝ) *
              (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ))) ^ 2) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum -
        (10 ^ m : ℝ) *
          ((translatedCanonicalBlocks N).map fun B =>
            (2 * (blockCoreDomain m B).card : ℕ) /
              Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum := by
  unfold variableCenteredCriticalRemainder
  rw [widthWeightedSquareFunction_eight_one_variable_eq_coreSum Q0 m N α hm,
    recordDiagonal_eq_coreCard Q0 m N hm]
  simp only [variableBlockCoreSum, positiveDecimalFrequency_eq_mul]

/-- The proposed centered observable is definitionally the T31 centered
square function after T87 identifies each canonical block's endpoint-filtered
domain with the exact T90 record domain. -/
theorem variableCenteredCriticalRemainder_eq_T31
    (Q0 m N : ℕ) (α : ℝ) :
    variableCenteredCriticalRemainder Q0 m N α =
      centeredWidthWeightedSquareFunction (8 : ℝ) 1 Q0 m N α := by
  unfold variableCenteredCriticalRemainder centeredWidthWeightedSquareFunction
  congr 1
  unfold recordDiagonal recordDiagonalMass
  rw [← List.sum_toFinset
    (fun B => ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
      widthWeight B) (translatedCanonicalBlocks_nodup N)]
  unfold decimalFrequency
  congr 1
  · norm_num
  · apply Finset.sum_congr rfl
    intro B hB
    rw [blockOrderedDomain_eq_blockRecordDomain (8 : ℝ) 1 Q0 m N
      (by simpa using hB)]

/-- The exact variable-phase remainder is independent of the displayed `Q0`
only after applying T87's all-scale exclusion audit. -/
theorem variableCenteredCriticalRemainder_Q0_independent
    (Q0 Q1 m N : ℕ) (α : ℝ) (hm : 1 ≤ m) :
    variableCenteredCriticalRemainder Q0 m N α =
      variableCenteredCriticalRemainder Q1 m N α := by
  rw [variableCenteredCriticalRemainder_literal Q0 m N α hm,
    variableCenteredCriticalRemainder_literal Q1 m N α hm]

/-- Both signed records attached to a core belong to T31's exact block domain.
This retains the arbitrary `Q0` even though T87 proves that no exclusion
survives at `(mu,c)=(8,1)`. -/
theorem both_signed_records_mem_blockOrderedDomain
    (Q0 m N : ℕ) {B : DyadicBlock} {p : LongPairCore}
    (hm : 1 ≤ m) (hB : B ∈ translatedCanonicalBlocks N)
    (hp : p ∈ blockCoreDomain m B) :
    (false, p) ∈ blockOrderedDomain (8 : ℝ) 1 Q0 m N B ∧
      (true, p) ∈ blockOrderedDomain (8 : ℝ) 1 Q0 m N B := by
  rw [blockOrderedDomain_eq_blockRecordDomain (8 : ℝ) 1 Q0 m N hB,
    blockRecordDomain_eight_one_eq_orientations Q0 m B hm]
  simp [hp]

/-- Every core, including a core in a singleton block or the largest core in
its block, contributes exactly its positive double signed difference. -/
theorem signedDouble_occurrence_and_value
    (Q0 m N : ℕ) {B : DyadicBlock} {p : LongPairCore}
    (hm : 1 ≤ m) (hB : B ∈ translatedCanonicalBlocks N)
    (hp : p ∈ blockCoreDomain m B) :
    ((true, p), (false, p)) ∈
        blockPositiveDifferenceDomain (8 : ℝ) 1 Q0 m N B ∧
      (blockDifferenceValue ((true, p), (false, p)) : ℤ) =
        2 * positiveDecimalFrequency p := by
  have hpMem := both_signed_records_mem_blockOrderedDomain
    Q0 m N hm hB hp
  have hpPos : (0 : ℤ) < positiveDecimalFrequency p := by
    exact_mod_cast Nat.pos_of_ne_zero
      (positiveDecimalFrequency_ne_zero ((mem_blockCoreDomain_iff.mp hp).1))
  have hmem : ((true, p), (false, p)) ∈
      blockPositiveDifferenceDomain (8 : ℝ) 1 Q0 m N B := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hpMem.2, hpMem.1⟩, ?_⟩
    simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte]
    omega
  refine ⟨hmem, ?_⟩
  simpa [signedDecimalFrequency, two_mul] using
    blockPositiveDifferenceValue_cast hmem

/-- Exact signed-difference occurrence map when `d_p < d_q`. There is one
positive double occurrence, two positive difference occurrences, and two
positive sum occurrences. -/
theorem signedDifference_occurrence_map
    (Q0 m N : ℕ) {B : DyadicBlock} {p q : LongPairCore}
    (hm : 1 ≤ m) (hB : B ∈ translatedCanonicalBlocks N)
    (hp : p ∈ blockCoreDomain m B) (hq : q ∈ blockCoreDomain m B)
    (hpq : positiveDecimalFrequency p < positiveDecimalFrequency q) :
    ((true, p), (false, p)) ∈
        blockPositiveDifferenceDomain (8 : ℝ) 1 Q0 m N B ∧
      ((true, q), (true, p)) ∈
        blockPositiveDifferenceDomain (8 : ℝ) 1 Q0 m N B ∧
      ((false, p), (false, q)) ∈
        blockPositiveDifferenceDomain (8 : ℝ) 1 Q0 m N B ∧
      ((true, p), (false, q)) ∈
        blockPositiveDifferenceDomain (8 : ℝ) 1 Q0 m N B ∧
      ((true, q), (false, p)) ∈
        blockPositiveDifferenceDomain (8 : ℝ) 1 Q0 m N B := by
  have hpMem := both_signed_records_mem_blockOrderedDomain
    Q0 m N hm hB hp
  have hqMem := both_signed_records_mem_blockOrderedDomain
    Q0 m N hm hB hq
  repeat' apply And.intro
  all_goals
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨by aesop, by aesop⟩, ?_⟩
    simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte]
  · have hpPos : (0 : ℤ) < positiveDecimalFrequency p := by
      exact_mod_cast Nat.pos_of_ne_zero
        (positiveDecimalFrequency_ne_zero ((mem_blockCoreDomain_iff.mp hp).1))
    omega
  · exact_mod_cast hpq
  · exact neg_lt_neg (by exact_mod_cast hpq)
  · have hqPos : (0 : ℤ) < positiveDecimalFrequency q := by
      exact_mod_cast Nat.pos_of_ne_zero
        (positiveDecimalFrequency_ne_zero ((mem_blockCoreDomain_iff.mp hq).1))
    omega
  · have hpPos : (0 : ℤ) < positiveDecimalFrequency p := by
      exact_mod_cast Nat.pos_of_ne_zero
        (positiveDecimalFrequency_ne_zero ((mem_blockCoreDomain_iff.mp hp).1))
    omega

/-- Every factor in the occurrence map, expressed using T31's positive
natural difference value. Difference and sum events each arise twice. -/
theorem signedDifference_occurrence_values
    (Q0 m N : ℕ) {B : DyadicBlock} {p q : LongPairCore}
    (hm : 1 ≤ m) (hB : B ∈ translatedCanonicalBlocks N)
    (hp : p ∈ blockCoreDomain m B) (hq : q ∈ blockCoreDomain m B)
    (hpq : positiveDecimalFrequency p < positiveDecimalFrequency q) :
    (blockDifferenceValue ((true, p), (false, p)) : ℤ) =
        2 * positiveDecimalFrequency p ∧
      (blockDifferenceValue ((true, q), (true, p)) : ℤ) =
        positiveDecimalFrequency q - positiveDecimalFrequency p ∧
      (blockDifferenceValue ((false, p), (false, q)) : ℤ) =
        positiveDecimalFrequency q - positiveDecimalFrequency p ∧
      (blockDifferenceValue ((true, p), (false, q)) : ℤ) =
        positiveDecimalFrequency p + positiveDecimalFrequency q ∧
      (blockDifferenceValue ((true, q), (false, p)) : ℤ) =
        positiveDecimalFrequency p + positiveDecimalFrequency q := by
  have hmem := signedDifference_occurrence_map Q0 m N hm hB hp hq hpq
  rcases hmem with ⟨hD, hM1, hM2, hP1, hP2⟩
  repeat' apply And.intro
  · simpa [signedDecimalFrequency, two_mul] using
      blockPositiveDifferenceValue_cast hD
  · simpa [signedDecimalFrequency] using blockPositiveDifferenceValue_cast hM1
  · simpa [signedDecimalFrequency, sub_eq_add_neg, add_comm] using
      blockPositiveDifferenceValue_cast hM2
  · simpa [signedDecimalFrequency, add_comm] using
      blockPositiveDifferenceValue_cast hP1
  · simpa [signedDecimalFrequency, add_comm] using
      blockPositiveDifferenceValue_cast hP2

/-- T31's checked CROSS theorem gives the full second moment of the exact
variable-phase centered critical remainder, with no conjectural premise. -/
theorem variableCenteredCriticalRemainder_secondMoment_le
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    (∫ α, variableCenteredCriticalRemainder Q0 m N α ^ 2
      ∂Theory.PiDigits.LongLagBlockCollisionDecay.T18.phaseMeasure) ≤
      940452800 * (10 ^ m : ℕ) * (N : ℝ) ^ 2 * Real.log (2 * N) := by
  simp_rw [variableCenteredCriticalRemainder_eq_T31]
  simpa [decimalFrequency] using
    integral_centeredWidthWeightedSquareFunction_sq_le
      (8 : ℝ) 1 Q0 m N hm hN

end Theory.PiDigits.LongLagBlockCollisionDecay.T97

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockOffDiagonal_eq_orient_image
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.orientPositiveDifference_injOn_block
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockPhaseSum_norm_sq_sub_card
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.integral_centeredWidthWeightedSquareFunction_sq
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.crossBlockWeightedGCD_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.integral_centeredWidthWeightedSquareFunction_sq_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.not_arithmeticExcluded_eight_one
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.blockRecordDomain_both_orientations_eight_one
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.blockOrderedDomain_eq_blockRecordDomain
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.recordDiagonal_exact_formula_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.mem_blockCoreDomain_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.blockRecordDomain_eight_one_eq_orientations
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.blockCoreDomain_orientation_exclusion_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.recordDiagonal_eq_coreCard
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.two_orientations_variablePhase_eq_cosine
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.widthWeightedSquareFunction_eight_one_variable_eq_coreSum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.variableCenteredCriticalRemainder_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.variableCenteredCriticalRemainder_eq_T31
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.variableCenteredCriticalRemainder_Q0_independent
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.signedDouble_occurrence_and_value
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.signedDifference_occurrence_map
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.signedDifference_occurrence_values
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T97.variableCenteredCriticalRemainder_secondMoment_le
