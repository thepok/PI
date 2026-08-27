import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
import TheoryLib.PiLongLagBlockCollisionDecay.T87T87RecordDiagonalCriticalBand

/-!
# T90: deterministic centered critical-band core

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module independently formalizes the deterministic centered decomposition
specified by the unverified T89 note. It concerns only T29's residual sparse-
Fourier sibling A12. It does not prove `CORR_pi`, C1, C2, or C3.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T90

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T87
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- The exact lower-dimensional `(lag,start)` domain in one canonical block.
The range factors are finite envelopes; the filter displays the mathematical
domain after T87 removes every `(mu,c)=(8,1)` arithmetic exclusion. -/
def blockCoreDomain (m : ℕ) (B : DyadicBlock) : Finset LongPairCore :=
  ((Finset.range B.finish).sigma fun _ => Finset.range B.finish).filter fun p =>
    0 < p.1 ∧ m ≤ p.1 ∧ B.start ≤ frequencyEndpoint p ∧
      frequencyEndpoint p < B.finish

/-- Exact membership in the lower-dimensional block domain. -/
theorem mem_blockCoreDomain_iff
    {m : ℕ} {B : DyadicBlock} {p : LongPairCore} :
    p ∈ blockCoreDomain m B ↔
      0 < p.1 ∧ m ≤ p.1 ∧ B.start ≤ frequencyEndpoint p ∧
        frequencyEndpoint p < B.finish := by
  rw [blockCoreDomain, Finset.mem_filter, Finset.mem_sigma]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · simp only [Finset.mem_range]
      unfold frequencyEndpoint at h
      omega
    · simp only [Finset.mem_range]
      unfold frequencyEndpoint at h
      omega

/-- Fully literal endpoint form of the core domain. -/
theorem mem_blockCoreDomain_literal
    {m : ℕ} {B : DyadicBlock} {p : LongPairCore} :
    p ∈ blockCoreDomain m B ↔
      0 < p.1 ∧ m ≤ p.1 ∧ B.start ≤ p.2 + p.1 ∧
        p.2 + p.1 < B.finish := by
  simpa [frequencyEndpoint] using
    (mem_blockCoreDomain_iff (m := m) (B := B) (p := p))

/-- At `(mu,c)=(8,1)`, the exact T32 record domain is two copies of the
lower-dimensional core domain. This exposes both orientations and records the
fact that no arithmetic exclusion survives. -/
theorem blockRecordDomain_eight_one_eq_orientations
    (Q0 m : ℕ) (B : DyadicBlock) (hm : 1 ≤ m) :
    blockRecordDomain (8 : ℝ) 1 Q0 m B =
      (Finset.univ : Finset Bool) ×ˢ blockCoreDomain m B := by
  classical
  ext q
  rcases q with ⟨b, p⟩
  simp only [Finset.mem_product, Finset.mem_univ, true_and]
  rw [mem_blockCoreDomain_iff]
  have h := blockRecordDomain_both_orientations_eight_one Q0 m B p hm
  cases b
  · exact h.1.1
  · exact h.1.2

/-- Every explicit core retains both signs, the exact arithmetic exclusion,
and the weak/strict block endpoints in the imported record domain. -/
theorem blockCoreDomain_orientation_exclusion_audit
    (Q0 m : ℕ) (B : DyadicBlock) (p : LongPairCore) (hm : 1 ≤ m) :
    p ∈ blockCoreDomain m B ↔
      ((false, p) ∈ blockRecordDomain (8 : ℝ) 1 Q0 m B ∧
        (true, p) ∈ blockRecordDomain (8 : ℝ) 1 Q0 m B ∧
        ¬ ArithmeticExcluded (8 : ℝ) 1 Q0 m p.2 p.1 ∧
        signedDecimalFrequency (false, p) =
          -(10 ^ p.2 * (10 ^ p.1 - 1) : ℕ) ∧
        signedDecimalFrequency (true, p) =
          (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ)) := by
  rw [mem_blockCoreDomain_iff]
  have h := blockRecordDomain_both_orientations_eight_one Q0 m B p hm
  constructor
  · intro hp
    refine ⟨h.1.1.2 hp, h.1.2.2 hp,
      not_arithmeticExcluded_eight_one Q0 m p.2 p.1 hm hp.2.1, ?_, ?_⟩
    · rw [h.2.1, positiveDecimalFrequency_eq_mul]
    · rw [h.2.2, positiveDecimalFrequency_eq_mul]
  · rintro ⟨hf, _ht, _hex, _hsf, _hst⟩
    exact h.1.1.1 hf

/-- Exact record cardinality after quotienting the Boolean orientation. -/
theorem blockRecordDomain_card_eq_two_mul_coreCard
    (Q0 m : ℕ) (B : DyadicBlock) (hm : 1 ≤ m) :
    (blockRecordDomain (8 : ℝ) 1 Q0 m B).card =
      2 * (blockCoreDomain m B).card := by
  rw [blockRecordDomain_eight_one_eq_orientations Q0 m B hm,
    Finset.card_product]
  simp

/-- The real fixed-pi shifted-frequency sum after removing orientation. -/
def blockShiftedFrequencySum (m : ℕ) (B : DyadicBlock) (h : ℕ) : ℝ :=
  ∑ p ∈ blockCoreDomain m B,
    Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
      (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ))

/-- The two opposite orientations of one core give exactly twice its real
cosine, with the T27 phase sign convention and alpha=pi. -/
theorem two_orientations_phase_eq_cosine (h : ℕ) (p : LongPairCore) :
    Theory.PiDigits.T27.phase (h : ℤ)
          ((signedDecimalFrequency (false, p) : ℝ) * Real.pi) +
        Theory.PiDigits.T27.phase (h : ℤ)
          ((signedDecimalFrequency (true, p) : ℝ) * Real.pi) =
      ((2 * Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
        (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ)) : ℝ) : ℂ) := by
  simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte,
    positiveDecimalFrequency_eq_mul]
  unfold Theory.PiDigits.T27.phase
  let x : ℝ := 2 * Real.pi ^ 2 * (h : ℝ) *
    (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ)
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
          ((((↑(-(↑(10 ^ p.2 * (10 ^ p.1 - 1) : ℕ)) : ℤ) : ℝ) *
            Real.pi : ℝ) : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I := by
    dsimp [x]
    push_cast
    ring
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
          ((((↑(↑(10 ^ p.2 * (10 ^ p.1 - 1) : ℕ) : ℤ) : ℝ) *
            Real.pi : ℝ) : ℂ)) = (x : ℂ) * Complex.I := by
    dsimp [x]
    push_cast
    ring
  rw [hneg, hpos, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg]
  push_cast
  dsimp [x]
  push_cast
  ring

/-- Exact four-orientation alignment at one block and frequency. -/
theorem canonicalBlockVector_eight_one_pi_eq_coreSum
    (Q0 m : ℕ) (B : DyadicBlock) (h : ℕ) (hm : 1 ≤ m) :
    canonicalBlockVector (8 : ℝ) 1 Q0 m B Real.pi h =
      ((2 * blockShiftedFrequencySum m B h : ℝ) : ℂ) := by
  rw [canonicalBlockVector_eq_sum_blockRecords,
    blockRecordDomain_eight_one_eq_orientations Q0 m B hm,
    Finset.sum_product, Finset.sum_comm]
  calc
    (∑ p ∈ blockCoreDomain m B,
        ∑ b ∈ (Finset.univ : Finset Bool),
          Theory.PiDigits.T27.phase (h : ℤ)
            ((signedDecimalFrequency (b, p) : ℝ) * Real.pi)) =
        ∑ p ∈ blockCoreDomain m B,
          (Theory.PiDigits.T27.phase (h : ℤ)
              ((signedDecimalFrequency (false, p) : ℝ) * Real.pi) +
            Theory.PiDigits.T27.phase (h : ℤ)
              ((signedDecimalFrequency (true, p) : ℝ) * Real.pi)) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [Fintype.univ_bool, add_comm]
    _ = ∑ p ∈ blockCoreDomain m B,
          ((2 * Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ)) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact two_orientations_phase_eq_cosine h p
    _ = ((2 * blockShiftedFrequencySum m B h : ℝ) : ℂ) := by
      unfold blockShiftedFrequencySum
      push_cast
      rw [Finset.mul_sum]

/-- The exact block energy after all four orientation choices are combined. -/
theorem blockSquaredEnergy_eight_one_pi_eq_coreSum
    (Q0 m : ℕ) (B : DyadicBlock) (hm : 1 ≤ m) :
    blockSquaredEnergy (8 : ℝ) 1 Q0 m B Real.pi =
      4 * ∑ h ∈ Finset.Icc 1 (10 ^ m),
        (blockShiftedFrequencySum m B h) ^ 2 := by
  unfold blockSquaredEnergy inclusiveFrequencies decimalFrequency
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [canonicalBlockVector_eight_one_pi_eq_coreSum Q0 m B h hm,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- T29's complete nonnegative observable after the four orientations have
been combined, retaining every canonical block, inclusive frequency, and
literal square-root width. -/
theorem widthWeightedSquareFunction_eight_one_pi_eq_coreSum
    (Q0 m N : ℕ) (hm : 1 ≤ m) :
    widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N Real.pi =
      ((translatedCanonicalBlocks N).map fun B =>
        (4 * ∑ h ∈ Finset.Icc 1 (10 ^ m),
          (blockShiftedFrequencySum m B h) ^ 2) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum := by
  unfold widthWeightedSquareFunction
  congr 1
  apply List.map_congr_left
  intro B hB
  rw [blockSquaredEnergy_eight_one_pi_eq_coreSum Q0 m B hm,
    widthWeight_eq_endpoints]

/-- T87's exact record diagonal after the same orientation quotient. -/
theorem recordDiagonal_eq_coreCard
    (Q0 m N : ℕ) (hm : 1 ≤ m) :
    recordDiagonal Q0 m N =
      (10 ^ m : ℝ) *
        ((translatedCanonicalBlocks N).map fun B =>
          (2 * (blockCoreDomain m B).card : ℕ) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum := by
  unfold recordDiagonal recordDiagonalMass
  congr 2
  apply List.map_congr_left
  intro B hB
  rw [blockRecordDomain_card_eq_two_mul_coreCard Q0 m B hm,
    widthWeight_eq_endpoints]

/-- The complete centered signed remainder, with T87's exact record diagonal
subtracted from T29's full observable. -/
def centeredCriticalRemainder (Q0 m N : ℕ) : ℝ :=
  widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N Real.pi -
    recordDiagonal Q0 m N

/-- The termwise triangle majorant before any fixed-pi cancellation. The
factor `2*K_B` is the exact both-orientation record cardinality. -/
def triangleMajorant (m N : ℕ) : ℝ :=
  (10 ^ m : ℝ) *
    ((translatedCanonicalBlocks N).map fun B =>
      ((2 * (blockCoreDomain m B).card : ℕ) : ℝ) *
          (((2 * (blockCoreDomain m B).card : ℕ) : ℝ) - 1) /
        Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum

/-- The exact four-orientation alignment defect. Only `(lag,start)` cores and
their blockwise shifted-frequency sums remain. -/
def alignmentDefect (m N : ℕ) : ℝ :=
  4 * ((translatedCanonicalBlocks N).map fun B =>
    (∑ h ∈ Finset.Icc 1 (10 ^ m),
      (((blockCoreDomain m B).card : ℝ) ^ 2 -
        (blockShiftedFrequencySum m B h) ^ 2)) /
      Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum

/-- Exact cardinality of the literal inclusive frequency interval. -/
theorem critical_inclusiveFrequencies_card (m : ℕ) :
    (Finset.Icc 1 (10 ^ m)).card = 10 ^ m := by
  simp

/-- The alignment-defect identity on one literal block. -/
theorem block_centered_eq_triangle_sub_alignment
    (m : ℕ) (B : DyadicBlock) :
    (4 * ∑ h ∈ Finset.Icc 1 (10 ^ m),
          (blockShiftedFrequencySum m B h) ^ 2) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) -
        (10 ^ m : ℝ) *
          ((2 * (blockCoreDomain m B).card : ℕ) : ℝ) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) =
      (10 ^ m : ℝ) *
          (((2 * (blockCoreDomain m B).card : ℕ) : ℝ) *
            (((2 * (blockCoreDomain m B).card : ℕ) : ℝ) - 1)) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) -
        4 * (∑ h ∈ Finset.Icc 1 (10 ^ m),
          (((blockCoreDomain m B).card : ℝ) ^ 2 -
            (blockShiftedFrequencySum m B h) ^ 2)) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) := by
  have hsum :
      (∑ h ∈ Finset.Icc 1 (10 ^ m),
          (((blockCoreDomain m B).card : ℝ) ^ 2 -
            (blockShiftedFrequencySum m B h) ^ 2)) =
        (10 ^ m : ℝ) * ((blockCoreDomain m B).card : ℝ) ^ 2 -
          ∑ h ∈ Finset.Icc 1 (10 ^ m),
            (blockShiftedFrequencySum m B h) ^ 2 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul,
      critical_inclusiveFrequencies_card]
    norm_num
  push_cast
  linear_combination
    (4 / Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)) * hsum

/-- Full exact finite identity: the T29 observable minus T87's diagonal is the
termwise triangle majorant minus the four-orientation alignment defect. -/
theorem centeredCriticalRemainder_eq_triangle_sub_alignment
    (Q0 m N : ℕ) (hm : 1 ≤ m) :
    centeredCriticalRemainder Q0 m N =
      triangleMajorant m N - alignmentDefect m N := by
  unfold centeredCriticalRemainder
  rw [widthWeightedSquareFunction_eight_one_pi_eq_coreSum Q0 m N hm,
    recordDiagonal_eq_coreCard Q0 m N hm]
  unfold triangleMajorant alignmentDefect
  induction translatedCanonicalBlocks N with
  | nil => simp
  | cons B blocks ih =>
      simp only [List.map_cons, List.sum_cons]
      have hB := block_centered_eq_triangle_sub_alignment m B
      linear_combination hB + ih

/-- Fully unfolded exact finite identity. The left side visibly subtracts
T87's exact both-orientation record diagonal from T29's observable; the right
side visibly contains every block, width, inclusive frequency, core, sign-
combined shifted frequency, and coefficient `4`. -/
theorem full_four_orientation_alignment_defect_identity_literal
    (Q0 m N : ℕ) (hm : 1 ≤ m) :
    widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N Real.pi -
        (10 ^ m : ℝ) *
          ((translatedCanonicalBlocks N).map fun B =>
            ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
              Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum =
      (10 ^ m : ℝ) *
          ((translatedCanonicalBlocks N).map fun B =>
            ((2 * (blockCoreDomain m B).card : ℕ) : ℝ) *
                (((2 * (blockCoreDomain m B).card : ℕ) : ℝ) - 1) /
              Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum -
        4 * ((translatedCanonicalBlocks N).map fun B =>
          (∑ h ∈ Finset.Icc (1 : ℕ) (10 ^ m),
            (((blockCoreDomain m B).card : ℝ) ^ 2 -
              (∑ p ∈ blockCoreDomain m B,
                Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
                  (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ))) ^ 2)) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum := by
  simpa [centeredCriticalRemainder, triangleMajorant, alignmentDefect,
    recordDiagonal, recordDiagonalMass, widthWeight,
    blockShiftedFrequencySum] using
      centeredCriticalRemainder_eq_triangle_sub_alignment Q0 m N hm

/-- The non-circular fixed-pi correlation frontier. Its body contains only
explicit lower-dimensional core domains, shifted-frequency sums, canonical
blocks, literal widths, the inclusive frequency endpoints, the full critical
band, and the displayed target. It mentions no T29 predicate, collision count,
C1, C2, or C3. No theorem in this module proves this proposition. -/
def CORR_pi : Prop :=
  ∀ Q0 m N : ℕ, 1 ≤ m → 1 ≤ N →
    10 ^ m ≤ N ^ 2 → N ^ 2 ≤ 2 * 10 ^ m →
    (10 ^ m : ℝ) *
          ((translatedCanonicalBlocks N).map fun B =>
            ((2 * (blockCoreDomain m B).card : ℕ) : ℝ) *
                (((2 * (blockCoreDomain m B).card : ℕ) : ℝ) - 1) /
              Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum -
        ((10 ^ m : ℕ) : ℝ) *
          ((N : ℝ) + (N : ℝ) ^ 2 /
            Real.sqrt (((10 ^ m : ℕ) : ℝ))) ≤
      4 * ((translatedCanonicalBlocks N).map fun B =>
        (∑ h ∈ Finset.Icc (1 : ℕ) (10 ^ m),
          (((blockCoreDomain m B).card : ℝ) ^ 2 -
            (∑ p ∈ blockCoreDomain m B,
              Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
                (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ))) ^ 2)) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum

/-- The correlation hypothesis bounds the centered term. This is a derived
consequence of the exact identity, not a clause in `CORR_pi`. -/
theorem CORR_pi_implies_centeredCriticalRemainder_le
    (hcorr : CORR_pi) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    centeredCriticalRemainder Q0 m N ≤
      ((10 ^ m : ℕ) : ℝ) *
        ((N : ℝ) + (N : ℝ) ^ 2 /
          Real.sqrt (((10 ^ m : ℕ) : ℝ))) := by
  have hc := hcorr Q0 m N hm hN hlower hupper
  have hc' : triangleMajorant m N - criticalNormalization m N ≤
      alignmentDefect m N := by
    simpa [triangleMajorant, alignmentDefect, criticalNormalization,
      blockShiftedFrequencySum] using hc
  rw [centeredCriticalRemainder_eq_triangle_sub_alignment Q0 m N hm]
  unfold criticalNormalization at hc'
  linarith

/-- Exact displayed conditional constant after adding T87's diagonal upper
bound. Every critical-band quantifier remains explicit. -/
theorem CORR_pi_implies_criticalBand_T29_sharp
    (hcorr : CORR_pi) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N Real.pi ≤
      (7 / 4 + Real.sqrt 2 / 2) *
        (((10 ^ m : ℕ) : ℝ) *
          ((N : ℝ) + (N : ℝ) ^ 2 /
            Real.sqrt (((10 ^ m : ℕ) : ℝ)))) := by
  have hcenter := CORR_pi_implies_centeredCriticalRemainder_le
    hcorr Q0 m N hm hN hlower hupper
  have hdiagRatio :=
    (recordDiagonal_normalized_critical_bounds Q0 m N hm hN hlower hupper).2
  have hnormalization : 0 < criticalNormalization m N := by
    unfold criticalNormalization
    positivity
  have hdiag : recordDiagonal Q0 m N ≤
      (3 / 4 + Real.sqrt 2 / 2) * criticalNormalization m N :=
    (div_le_iff₀ hnormalization).mp hdiagRatio
  unfold centeredCriticalRemainder at hcenter
  unfold criticalNormalization at hdiag
  linarith

/-- The sharp displayed constant is strictly below the rational constant
`5/2`. -/
theorem sharpCriticalConstant_lt_five_halves :
    (7 / 4 + Real.sqrt 2 / 2 : ℝ) < 5 / 2 := by
  have hsquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- T87's displayed normalization is exactly T29's target at `s=1/2`. -/
theorem criticalNormalization_eq_T29_half (m N : ℕ) :
    criticalNormalization m N =
      (decimalFrequency m : ℝ) * scaleMatchedTarget (1 / 2 : ℝ) m N := by
  have hpowCast : (((10 ^ m : ℕ) : ℝ)) = (10 : ℝ) ^ m := by
    norm_num
  have hrpow : (10 : ℝ) ^ (-(1 / 2 : ℝ) * (m : ℝ)) =
      1 / Real.sqrt (((10 ^ m : ℕ) : ℝ)) := by
    rw [hpowCast, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    rw [show -(1 / 2 : ℝ) * (m : ℝ) =
      -((m : ℝ) * (1 / 2 : ℝ)) by ring]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
    exact (one_div _).symm
  unfold criticalNormalization scaleMatchedTarget decimalFrequency
  rw [hrpow]
  ring

/-- Rational displayed conditional T29 bound. The premise is exactly the
lower-dimensional `CORR_pi`; no width-weighted predicate or conclusion-shaped
estimate occurs in that premise. -/
theorem CORR_pi_implies_criticalBand_T29_five_halves
    (hcorr : CORR_pi) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N Real.pi ≤
      (5 / 2 : ℝ) *
        (((10 ^ m : ℕ) : ℝ) *
          ((N : ℝ) + (N : ℝ) ^ 2 /
            Real.sqrt (((10 ^ m : ℕ) : ℝ)))) := by
  have hsharp := CORR_pi_implies_criticalBand_T29_sharp
    hcorr Q0 m N hm hN hlower hupper
  have htarget : 0 ≤ (((10 ^ m : ℕ) : ℝ) *
      ((N : ℝ) + (N : ℝ) ^ 2 /
        Real.sqrt (((10 ^ m : ℕ) : ℝ)))) := by positivity
  exact hsharp.trans (mul_le_mul_of_nonneg_right
    sharpCriticalConstant_lt_five_halves.le htarget)

/-- The same conditional estimate in T29's exact `s=1/2` notation. -/
theorem CORR_pi_implies_criticalBand_T29_half_scaleMatchedTarget
    (hcorr : CORR_pi) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N Real.pi ≤
      (5 / 2 : ℝ) * (decimalFrequency m : ℝ) *
        scaleMatchedTarget (1 / 2 : ℝ) m N := by
  calc
    widthWeightedSquareFunction (8 : ℝ) 1 Q0 m N Real.pi ≤
        (5 / 2 : ℝ) * criticalNormalization m N := by
      simpa [criticalNormalization] using
        CORR_pi_implies_criticalBand_T29_five_halves
          hcorr Q0 m N hm hN hlower hupper
    _ = (5 / 2 : ℝ) * (decimalFrequency m : ℝ) *
        scaleMatchedTarget (1 / 2 : ℝ) m N := by
      rw [criticalNormalization_eq_T29_half]
      ring

end Theory.PiDigits.LongLagBlockCollisionDecay.T90

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.mem_blockCoreDomain_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.mem_blockCoreDomain_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.blockRecordDomain_eight_one_eq_orientations
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.blockCoreDomain_orientation_exclusion_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.two_orientations_phase_eq_cosine
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.canonicalBlockVector_eight_one_pi_eq_coreSum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.blockSquaredEnergy_eight_one_pi_eq_coreSum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.widthWeightedSquareFunction_eight_one_pi_eq_coreSum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.recordDiagonal_eq_coreCard
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.full_four_orientation_alignment_defect_identity_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.CORR_pi_implies_centeredCriticalRemainder_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.CORR_pi_implies_criticalBand_T29_sharp
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.sharpCriticalConstant_lt_five_halves
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.criticalNormalization_eq_T29_half
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.CORR_pi_implies_criticalBand_T29_five_halves
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T90.CORR_pi_implies_criticalBand_T29_half_scaleMatchedTarget
