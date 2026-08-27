import TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD
import TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff
import TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
import TheoryLib.PiLongLagBlockCollisionDecay.T32T32AllBlockFixedPiRange
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Nat.Log

/-!
# T34: cancelling repunit incidence reduction

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module formalizes only T33's cancelling off-diagonal sector of the
residual sparse-Fourier sibling.  Its final estimate is conditional on the
explicit `ARI_cancel` incidence hypothesis below.  It proves neither that
`ARI_cancel` holds at `Real.pi`, nor T29's all-scale square-function premise,
nor C2, nor the canonical collision estimate C1.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T34

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T32

abbrev RecordPair := OrderedLongPair × OrderedLongPair

/-- The six disjoint positive cancelling patterns from the T33 table. -/
inductive CancellingRow
  | positiveSameEndpoint
  | positiveSameStart
  | negativeSameEndpoint
  | negativeSameStart
  | mixedFirstEndpoint
  | mixedSecondEndpoint
  deriving DecidableEq, Fintype

/-- The ordered record having the specified orientation, start, and endpoint.
Invalid endpoint order gives lag zero and is rejected by `blockRecordDomain`. -/
def recordOfStartEndpoint
    (orientation : Bool) (start endpoint : ℕ) : OrderedLongPair :=
  (orientation, ⟨endpoint - start, start⟩)

/-- The unique ordered record pair represented by a row and `(v,rho,z)`. -/
def cancellingRowPair
    (row : CancellingRow) (v rho z : ℕ) : RecordPair :=
  match row with
  | .positiveSameEndpoint =>
      (recordOfStartEndpoint true (v + rho) z,
        recordOfStartEndpoint true v z)
  | .positiveSameStart =>
      (recordOfStartEndpoint true z v,
        recordOfStartEndpoint true z (v + rho))
  | .negativeSameEndpoint =>
      (recordOfStartEndpoint false v z,
        recordOfStartEndpoint false (v + rho) z)
  | .negativeSameStart =>
      (recordOfStartEndpoint false z (v + rho),
        recordOfStartEndpoint false z v)
  | .mixedFirstEndpoint =>
      (recordOfStartEndpoint false z (v + rho),
        recordOfStartEndpoint true v z)
  | .mixedSecondEndpoint =>
      (recordOfStartEndpoint false v z,
        recordOfStartEndpoint true z (v + rho))

/-- A row domain is a literal singleton record pair, retained exactly when
`rho > 0` and both records survive T32's full block domain. -/
def cancellingRowDomain
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock)
    (row : CancellingRow) (v rho z : ℕ) : Finset RecordPair :=
  ({cancellingRowPair row v rho z} : Finset RecordPair).filter fun qr =>
    0 < rho ∧
      qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
      qr.2 ∈ blockRecordDomain μ c Q0 m B

/-- Exact outer parameter range `rho >= 1` and `v+rho < N`. -/
def repunitParameterDomain (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter fun vr =>
    0 < vr.2 ∧ vr.1 + vr.2 < N

/-- The reduced repunit factor.  It is `9` times the usual decimal repunit. -/
def reducedRepunitFactor (rho : ℕ) : ℕ := 10 ^ rho - 1

/-- The exact positive difference attached to `(v,rho)`. -/
def cancellingValue (v rho : ℕ) : ℕ :=
  10 ^ v * reducedRepunitFactor rho

@[simp] theorem mem_cancellingRowDomain_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {row : CancellingRow} {v rho z : ℕ} {qr : RecordPair} :
    qr ∈ cancellingRowDomain μ c Q0 m B row v rho z ↔
      qr = cancellingRowPair row v rho z ∧ 0 < rho ∧
        qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B := by
  simp [cancellingRowDomain]

theorem mem_repunitParameterDomain_iff
    {N v rho : ℕ} :
    (v, rho) ∈ repunitParameterDomain N ↔
      v < N ∧ rho < N ∧ 0 < rho ∧ v + rho < N := by
  simp [repunitParameterDomain, and_assoc]

/-- Row 1: two positive records with common endpoint `z`. -/
theorem mem_positiveSameEndpoint_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} {qr : RecordPair} :
    qr ∈ cancellingRowDomain μ c Q0 m B
        .positiveSameEndpoint v rho z ↔
      qr = (recordOfStartEndpoint true (v + rho) z,
        recordOfStartEndpoint true v z) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B := by
  simp [cancellingRowPair]

/-- Row 2: two positive records with common start `z`. -/
theorem mem_positiveSameStart_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} {qr : RecordPair} :
    qr ∈ cancellingRowDomain μ c Q0 m B
        .positiveSameStart v rho z ↔
      qr = (recordOfStartEndpoint true z v,
        recordOfStartEndpoint true z (v + rho)) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B := by
  simp [cancellingRowPair]

/-- Row 3: two negative records with common endpoint `z`. -/
theorem mem_negativeSameEndpoint_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} {qr : RecordPair} :
    qr ∈ cancellingRowDomain μ c Q0 m B
        .negativeSameEndpoint v rho z ↔
      qr = (recordOfStartEndpoint false v z,
        recordOfStartEndpoint false (v + rho) z) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B := by
  simp [cancellingRowPair]

/-- Row 4: two negative records with common start `z`. -/
theorem mem_negativeSameStart_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} {qr : RecordPair} :
    qr ∈ cancellingRowDomain μ c Q0 m B
        .negativeSameStart v rho z ↔
      qr = (recordOfStartEndpoint false z (v + rho),
        recordOfStartEndpoint false z v) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B := by
  simp [cancellingRowPair]

/-- Row 5: a negative and a positive record with `E₁=n₀=z`. -/
theorem mem_mixedFirstEndpoint_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} {qr : RecordPair} :
    qr ∈ cancellingRowDomain μ c Q0 m B
        .mixedFirstEndpoint v rho z ↔
      qr = (recordOfStartEndpoint false z (v + rho),
        recordOfStartEndpoint true v z) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B := by
  simp [cancellingRowPair]

/-- Row 6: a negative and a positive record with `E₀=n₁=z`. -/
theorem mem_mixedSecondEndpoint_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} {qr : RecordPair} :
    qr ∈ cancellingRowDomain μ c Q0 m B
        .mixedSecondEndpoint v rho z ↔
      qr = (recordOfStartEndpoint false v z,
        recordOfStartEndpoint true z (v + rho)) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B := by
  simp [cancellingRowPair]

/-- Every active row has exactly the positive repunit difference
`10^v(10^rho-1)`. -/
theorem cancellingRow_difference
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {row : CancellingRow} {v rho z : ℕ} {qr : RecordPair}
    (hqr : qr ∈ cancellingRowDomain μ c Q0 m B row v rho z) :
    signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1 =
      (cancellingValue v rho : ℤ) := by
  rw [mem_cancellingRowDomain_iff] at hqr
  rcases hqr with ⟨rfl, hrho, hq0, hq1⟩
  have hp : 10 ^ v ≤ 10 ^ v * 10 ^ rho := by
    have hone : 1 ≤ 10 ^ rho := one_le_pow₀ (by norm_num)
    calc
      10 ^ v = 10 ^ v * 1 := by simp
      _ ≤ 10 ^ v * 10 ^ rho := Nat.mul_le_mul_left _ hone
  cases row <;>
    simp only [cancellingRowPair] at hq0 hq1 ⊢
  all_goals
    have hlag0 := (mem_blockRecordDomain_iff.mp hq0).1.1
    have hlag1 := (mem_blockRecordDomain_iff.mp hq1).1.1
    simp only [recordOfStartEndpoint] at hlag0 hlag1 ⊢
    simp only [signedDecimalFrequency, positiveDecimalFrequency]
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [cancellingValue, reducedRepunitFactor]
  case positiveSameEndpoint =>
    have hz0 : v + rho + (z - (v + rho)) = z := by omega
    have hz1 : v + (z - v) = z := by omega
    have hpv : 10 ^ v ≤ 10 ^ z := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpvr : 10 ^ (v + rho) ≤ 10 ^ z := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hz0, hz1, Nat.mul_sub_left_distrib,
      Nat.cast_sub hpv, Nat.cast_sub hpvr]
    simp only [mul_one]
    rw [Nat.cast_sub hp]
    push_cast
    rw [pow_add]
    ring
  case positiveSameStart =>
    have hv : z + (v - z) = v := by omega
    have hvr : z + (v + rho - z) = v + rho := by omega
    have hpv : 10 ^ z ≤ 10 ^ v := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpvr : 10 ^ z ≤ 10 ^ (v + rho) := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hv, hvr, Nat.mul_sub_left_distrib,
      Nat.cast_sub hpvr, Nat.cast_sub hpv]
    simp only [mul_one]
    rw [Nat.cast_sub hp]
    push_cast
    rw [pow_add]
    ring
  case negativeSameEndpoint =>
    have hz0 : v + (z - v) = z := by omega
    have hz1 : v + rho + (z - (v + rho)) = z := by omega
    have hpv : 10 ^ v ≤ 10 ^ z := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpvr : 10 ^ (v + rho) ≤ 10 ^ z := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hz0, hz1, Nat.mul_sub_left_distrib,
      Nat.cast_sub hpvr, Nat.cast_sub hpv]
    simp only [mul_one]
    rw [Nat.cast_sub hp]
    push_cast
    rw [pow_add]
    ring
  case negativeSameStart =>
    have hv : z + (v - z) = v := by omega
    have hvr : z + (v + rho - z) = v + rho := by omega
    have hpv : 10 ^ z ≤ 10 ^ v := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpvr : 10 ^ z ≤ 10 ^ (v + rho) := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hv, hvr, Nat.mul_sub_left_distrib,
      Nat.cast_sub hpv, Nat.cast_sub hpvr]
    simp only [mul_one]
    rw [Nat.cast_sub hp]
    push_cast
    rw [pow_add]
    ring
  case mixedFirstEndpoint =>
    have hz : v + (z - v) = z := by omega
    have hvr : z + (v + rho - z) = v + rho := by omega
    have hpv : 10 ^ v ≤ 10 ^ z := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpvr : 10 ^ z ≤ 10 ^ (v + rho) := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hz, hvr, Nat.mul_sub_left_distrib,
      Nat.cast_sub hpv, Nat.cast_sub hpvr]
    simp only [mul_one]
    rw [Nat.cast_sub hp]
    push_cast
    rw [pow_add]
    ring
  case mixedSecondEndpoint =>
    have hz : v + (z - v) = z := by omega
    have hvr : z + (v + rho - z) = v + rho := by omega
    have hpv : 10 ^ v ≤ 10 ^ z := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpvr : 10 ^ z ≤ 10 ^ (v + rho) := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hz, hvr, Nat.mul_sub_left_distrib,
      Nat.cast_sub hpvr, Nat.cast_sub hpv]
    simp only [mul_one]
    rw [Nat.cast_sub hp]
    push_cast
    rw [pow_add]
    ring

/-- The exact decimal valuation and primitive part of every active row. -/
theorem cancellingRow_valuation
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {row : CancellingRow} {v rho z : ℕ} {qr : RecordPair}
    (hqr : qr ∈ cancellingRowDomain μ c Q0 m B row v rho z) :
    tenValuation (cancellingValue v rho) = v ∧
      tenPrimitivePart (cancellingValue v rho) = reducedRepunitFactor rho := by
  have hrho := (mem_cancellingRowDomain_iff.mp hqr).2.1
  exact cancellationValue_ten_reduction v rho hrho

/-- Active row witnesses are unique.  Thus the hidden-exponent and six-row
cardinalities below are genuine record-pair multiplicities, not an overlapping
cover. -/
theorem cancellingRow_witness_unique
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {row row' : CancellingRow} {v rho z v' rho' z' : ℕ}
    (hrow : cancellingRowPair row v rho z ∈
      cancellingRowDomain μ c Q0 m B row v rho z)
    (hrow' : cancellingRowPair row' v' rho' z' ∈
      cancellingRowDomain μ c Q0 m B row' v' rho' z')
    (heq : cancellingRowPair row v rho z =
      cancellingRowPair row' v' rho' z') :
    row = row' ∧ v = v' ∧ rho = rho' ∧ z = z' := by
  have hdiff := cancellingRow_difference hrow
  have hdiff' := cancellingRow_difference hrow'
  have hdiffEq := congrArg
    (fun qr : RecordPair =>
      signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) heq
  dsimp only at hdiffEq
  rw [hdiff, hdiff'] at hdiffEq
  have hvalue : cancellingValue v rho = cancellingValue v' rho' := by
    exact_mod_cast hdiffEq
  have hval := cancellingRow_valuation hrow
  have hval' := cancellingRow_valuation hrow'
  have hv : v = v' := by
    rw [← hval.1, ← hval'.1, hvalue]
  have hprim : reducedRepunitFactor rho = reducedRepunitFactor rho' := by
    rw [← hval.2, ← hval'.2, hvalue]
  have hrhoeq : rho = rho' := by
    unfold reducedRepunitFactor at hprim
    have hpows : 10 ^ rho = 10 ^ rho' := by
      have hrho := (mem_cancellingRowDomain_iff.mp hrow).2.1
      have hrho' := (mem_cancellingRowDomain_iff.mp hrow').2.1
      have hp := one_le_pow₀ (a := 10) (n := rho) (by norm_num)
      have hp' := one_le_pow₀ (a := 10) (n := rho') (by norm_num)
      omega
    exact Nat.pow_right_injective (by norm_num) hpows
  subst v'
  subst rho'
  have hm := (mem_cancellingRowDomain_iff.mp hrow).2
  have hm' := (mem_cancellingRowDomain_iff.mp hrow').2
  rcases hm with ⟨hrho, hq0, hq1⟩
  rcases hm' with ⟨hrho', hq0', hq1'⟩
  have hlag0 := (mem_blockRecordDomain_iff.mp hq0).1.1
  have hlag1 := (mem_blockRecordDomain_iff.mp hq1).1.1
  have hlag0' := (mem_blockRecordDomain_iff.mp hq0').1.1
  have hlag1' := (mem_blockRecordDomain_iff.mp hq1').1.1
  have hq0eq := congrArg Prod.fst heq
  have hq1eq := congrArg Prod.snd heq
  have ho0 := congrArg (fun q : OrderedLongPair => q.1) hq0eq
  have ho1 := congrArg (fun q : OrderedLongPair => q.1) hq1eq
  have hn0 := congrArg (fun q : OrderedLongPair => q.2.2) hq0eq
  have hn1 := congrArg (fun q : OrderedLongPair => q.2.2) hq1eq
  have hE0 := congrArg (fun q : OrderedLongPair => frequencyEndpoint q.2) hq0eq
  have hE1 := congrArg (fun q : OrderedLongPair => frequencyEndpoint q.2) hq1eq
  cases row <;> cases row' <;>
    simp only [cancellingRowPair, recordOfStartEndpoint, frequencyEndpoint,
      Bool.true_eq_false, Bool.false_eq_true, reduceCtorEq] at hlag0 hlag1 hlag0' hlag1' ho0 ho1 hn0 hn1 hE0 hE1 ⊢ <;>
    simp only [true_and, false_and] <;>
    omega

/-! ## Exact finite cancelling contribution and regrouping -/

/-- T32's literal off-diagonal record-pair domain, named so membership can be
stated independently of the summand. -/
def offDiagonalRecordDomain
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) : Finset RecordPair :=
  (blockRecordDomain μ c Q0 m B ×ˢ
      blockRecordDomain μ c Q0 m B).filter fun qr => qr.1 ≠ qr.2

/-- Reversal supplies the negative difference paired with each positive row. -/
def reverseRecordPair (qr : RecordPair) : RecordPair := (qr.2, qr.1)

theorem cancellingRow_and_reverse_mem_offDiagonal
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {row : CancellingRow} {v rho z : ℕ} {qr : RecordPair}
    (hqr : qr ∈ cancellingRowDomain μ c Q0 m B row v rho z) :
    qr ∈ offDiagonalRecordDomain μ c Q0 m B ∧
      reverseRecordPair qr ∈ offDiagonalRecordDomain μ c Q0 m B := by
  have hmem := mem_cancellingRowDomain_iff.mp hqr
  have hdiff := cancellingRow_difference hqr
  have hvalue : 0 < cancellingValue v rho := by
    have hrho : 0 < rho := hmem.2.1
    unfold cancellingValue reducedRepunitFactor
    apply Nat.mul_pos
    · positivity
    · have : 1 < 10 ^ rho := Nat.one_lt_pow (Nat.ne_of_gt hrho) (by norm_num)
      omega
  have hne : qr.1 ≠ qr.2 := by
    intro heq
    have : signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1 = 0 := by
      rw [heq]
      simp
    rw [hdiff] at this
    exact (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hvalue)) this
  constructor
  · simp [offDiagonalRecordDomain, hmem.2.2.1, hmem.2.2.2, hne]
  · simp [offDiagonalRecordDomain, reverseRecordPair,
      hmem.2.2.1, hmem.2.2.2, Ne.symm hne]

/-- The exact number of row witnesses with fixed `(v,rho)` in one block.
The hidden exponent `z` and all six rows retain their multiplicities. -/
def blockRepunitMultiplicity
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (v rho : ℕ) : ℕ :=
  ∑ z ∈ Finset.range N, ∑ row : CancellingRow,
    (cancellingRowDomain μ c Q0 m B row v rho z).card

/-- The real part of T32's one-sided kernel, still on exactly
`h=1,...,10^m`. -/
def inclusiveRealKernel (m : ℕ) (d : ℕ) (α : ℝ) : ℝ :=
  (inclusiveDirichletKernel m (d : ℤ) α).re

/-- Audit of the exact inclusive endpoint range: zero is absent and
`h=10^m` is present. -/
theorem inclusiveRealKernel_frequency_audit (m d : ℕ) (α : ℝ) :
    inclusiveRealKernel m d α =
      (∑ h ∈ Finset.Icc (1 : ℕ) (10 ^ m),
        Theory.PiDigits.T27.phase ((h : ℤ) * (d : ℤ)) α).re := by
  unfold inclusiveRealKernel inclusiveDirichletKernel inclusiveFrequencies
    decimalFrequency
  rfl

theorem inclusiveDirichletKernel_neg
    (m : ℕ) (d : ℤ) (α : ℝ) :
    inclusiveDirichletKernel m (-d) α =
      conj (inclusiveDirichletKernel m d α) := by
  classical
  unfold inclusiveDirichletKernel
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Theory.PiDigits.T27.phase_neg]
  congr 2
  ring

/-- Pointwise swap/conjugation identity.  The factor two is only the reversal
factor; Bool orientations are already among the six rows. -/
theorem rowKernelPairSum_eq
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    (row : CancellingRow) (v rho z : ℕ) (α : ℝ) :
    (∑ qr ∈ cancellingRowDomain μ c Q0 m B row v rho z,
      (inclusiveDirichletKernel m
          (signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) α +
        inclusiveDirichletKernel m
          (signedDecimalFrequency qr.1 - signedDecimalFrequency qr.2) α)) =
      (2 : ℂ) *
        ((cancellingRowDomain μ c Q0 m B row v rho z).card : ℂ) *
        (inclusiveRealKernel m (cancellingValue v rho) α : ℂ) := by
  classical
  calc
    (∑ qr ∈ cancellingRowDomain μ c Q0 m B row v rho z,
      (inclusiveDirichletKernel m
          (signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) α +
        inclusiveDirichletKernel m
          (signedDecimalFrequency qr.1 - signedDecimalFrequency qr.2) α)) =
        ∑ _qr ∈ cancellingRowDomain μ c Q0 m B row v rho z,
          (2 : ℂ) * (inclusiveRealKernel m (cancellingValue v rho) α : ℂ) := by
      apply Finset.sum_congr rfl
      intro qr hqr
      have hdiff := cancellingRow_difference hqr
      have hneg : signedDecimalFrequency qr.1 - signedDecimalFrequency qr.2 =
          -(cancellingValue v rho : ℤ) := by omega
      rw [hdiff, hneg, inclusiveDirichletKernel_neg]
      simpa [inclusiveRealKernel] using
        (Complex.add_conj
          (inclusiveDirichletKernel m (cancellingValue v rho : ℤ) α))
    _ = _ := by
      simp
      ring

/-- The literal ordered cancelling contribution.  For each active positive
row it includes that T32 off-diagonal term and its reversed term. -/
def cancellingSectorContribution
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℂ :=
  ((translatedCanonicalBlocks N).map fun B =>
    (∑ vr ∈ repunitParameterDomain N,
      ∑ z ∈ Finset.range N, ∑ row : CancellingRow,
        ∑ qr ∈ cancellingRowDomain μ c Q0 m B row vr.1 vr.2 z,
          (inclusiveDirichletKernel m
              (signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) α +
            inclusiveDirichletKernel m
              (signedDecimalFrequency qr.1 - signedDecimalFrequency qr.2) α)) /
      (widthWeight B : ℂ)).sum

/-- Exact block-weighted regrouping by the valuation `v`, reduced repunit
parameter `rho`, hidden exponent, and all six rows. -/
def regroupedCancellingSector
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℂ :=
  (2 : ℂ) * ((translatedCanonicalBlocks N).map fun B =>
    (∑ vr ∈ repunitParameterDomain N,
      (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
        (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ)) /
      (widthWeight B : ℂ)).sum

theorem blockCancellingContribution_eq
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) :
    (∑ vr ∈ repunitParameterDomain N,
      ∑ z ∈ Finset.range N, ∑ row : CancellingRow,
        ∑ qr ∈ cancellingRowDomain μ c Q0 m B row vr.1 vr.2 z,
          (inclusiveDirichletKernel m
              (signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) α +
            inclusiveDirichletKernel m
              (signedDecimalFrequency qr.1 - signedDecimalFrequency qr.2) α)) /
        (widthWeight B : ℂ) =
      (2 : ℂ) *
        ((∑ vr ∈ repunitParameterDomain N,
          (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
            (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ)) /
          (widthWeight B : ℂ)) := by
  have hnum :
      (∑ vr ∈ repunitParameterDomain N,
        ∑ z ∈ Finset.range N, ∑ row : CancellingRow,
          ∑ qr ∈ cancellingRowDomain μ c Q0 m B row vr.1 vr.2 z,
            (inclusiveDirichletKernel m
                (signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) α +
              inclusiveDirichletKernel m
                (signedDecimalFrequency qr.1 - signedDecimalFrequency qr.2) α)) =
        (2 : ℂ) *
          ∑ vr ∈ repunitParameterDomain N,
            (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
              (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro vr hvr
    simp_rw [rowKernelPairSum_eq]
    unfold blockRepunitMultiplicity
    push_cast
    simp_rw [← Finset.sum_mul]
    simp_rw [← Finset.mul_sum]
    ring
  rw [hnum]
  ring

/-- Finite regrouping identity with no limiting rearrangement. -/
theorem cancellingSectorContribution_eq_regrouped
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    cancellingSectorContribution μ c Q0 m N α =
      regroupedCancellingSector μ c Q0 m N α := by
  unfold cancellingSectorContribution regroupedCancellingSector
  induction translatedCanonicalBlocks N with
  | nil => simp
  | cons B blocks ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      rw [blockCancellingContribution_eq]
      ring

/-! ## Endpoint-pinned dyadic shells and the incidence premise -/

/-- Distance to the nearest integer, attained by `round x`. -/
def nearestIntegerDistance (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

/-- The least `K >= 1` with `2^(K+1) >= 10^m`, for every positive `m`. -/
def shellDepth (m : ℕ) : ℕ :=
  Nat.clog 2 (10 ^ m) - 1

/-- Shell zero is closed at `1/10^m`; positive shells are open below and
closed above, and the final upper endpoint is capped at `1/2`. -/
def InDyadicShell (m j : ℕ) (x : ℝ) : Prop :=
  if j = 0 then
    0 ≤ nearestIntegerDistance x ∧
      nearestIntegerDistance x ≤ ((10 : ℝ) ^ m)⁻¹
  else
    (2 : ℝ) ^ (j - 1) / (10 : ℝ) ^ m < nearestIntegerDistance x ∧
      nearestIntegerDistance x ≤
        min ((2 : ℝ) ^ j / (10 : ℝ) ^ m) (1 / 2)

theorem shellDepth_spec (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ shellDepth m ∧
      10 ^ m ≤ 2 ^ (shellDepth m + 1) ∧
      2 ^ shellDepth m < 10 ^ m := by
  have hten : 10 ≤ 10 ^ m := by
    calc
      10 = 10 ^ (1 : ℕ) := by norm_num
      _ ≤ 10 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hH : 1 < 10 ^ m := by omega
  have hclog : 1 < Nat.clog 2 (10 ^ m) := by
    rw [Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)]
    norm_num
    omega
  have hone : 1 ≤ Nat.clog 2 (10 ^ m) := by omega
  have hpred : Nat.clog 2 (10 ^ m) - 1 + 1 = Nat.clog 2 (10 ^ m) :=
    Nat.sub_add_cancel hone
  refine ⟨?_, ?_, ?_⟩
  · unfold shellDepth
    omega
  · unfold shellDepth
    rw [hpred]
    exact Nat.le_pow_clog (by norm_num) _
  · exact Nat.pow_pred_clog_lt_self (by norm_num) hH

theorem shellDepth_real_endpoints (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (shellDepth m - 1) / (10 : ℝ) ^ m < 1 / 2 ∧
      1 / 2 ≤ (2 : ℝ) ^ shellDepth m / (10 : ℝ) ^ m := by
  obtain ⟨hK, hupper, hlower⟩ := shellDepth_spec m hm
  have hH : (0 : ℝ) < (10 : ℝ) ^ m := by positivity
  have hlowerR : (2 : ℝ) ^ shellDepth m < (10 : ℝ) ^ m := by
    exact_mod_cast hlower
  have hupperR : (10 : ℝ) ^ m ≤ (2 : ℝ) ^ (shellDepth m + 1) := by
    exact_mod_cast hupper
  have hpred : shellDepth m - 1 + 1 = shellDepth m :=
    Nat.sub_add_cancel hK
  constructor
  · apply (div_lt_iff₀ hH).2
    rw [← hpred, pow_succ] at hlowerR
    nlinarith
  · apply (le_div_iff₀ hH).2
    rw [pow_succ] at hupperR
    nlinarith

theorem nearestIntegerDistance_nonneg (x : ℝ) :
    0 ≤ nearestIntegerDistance x := by
  exact abs_nonneg _

theorem nearestIntegerDistance_le_half (x : ℝ) :
    nearestIntegerDistance x ≤ 1 / 2 := by
  simpa [nearestIntegerDistance] using (abs_sub_round x)

/-- Canonical shell assignment.  Outside shell zero it is the least dyadic
upper endpoint above `10^m * nearestIntegerDistance x`. -/
def shellIndex (m : ℕ) (x : ℝ) : ℕ :=
  if nearestIntegerDistance x ≤ ((10 : ℝ) ^ m)⁻¹ then 0
  else Nat.clog 2 (Nat.ceil ((10 : ℝ) ^ m * nearestIntegerDistance x))

theorem shellIndex_mem (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    shellIndex m x ∈ Finset.Icc 0 (shellDepth m) ∧
      InDyadicShell m (shellIndex m x) x := by
  classical
  let H : ℝ := (10 : ℝ) ^ m
  let delta : ℝ := nearestIntegerDistance x
  have hH : 0 < H := by positivity
  have hdelta0 : 0 ≤ delta := nearestIntegerDistance_nonneg x
  have hdeltahalf : delta ≤ 1 / 2 := nearestIntegerDistance_le_half x
  by_cases hnear : delta ≤ H⁻¹
  · have hindex : shellIndex m x = 0 := by
      simp [shellIndex, H, delta, hnear]
    rw [hindex]
    constructor
    · simp
    · simp [InDyadicShell, H, delta, hdelta0, hnear]
  · have hfar : H⁻¹ < delta := lt_of_not_ge hnear
    have hxone : 1 < H * delta := by
      calc
        1 = H * H⁻¹ := by field_simp
        _ < H * delta := mul_lt_mul_of_pos_left hfar hH
    let C : ℕ := Nat.ceil (H * delta)
    let j : ℕ := Nat.clog 2 C
    have hC : 1 < C := by
      apply (Nat.lt_ceil).2
      norm_num
      exact hxone
    have hjpos : 0 < j := Nat.clog_pos (by norm_num) hC
    have hendpoints := shellDepth_real_endpoints m hm
    have hxupper : H * delta ≤ (2 : ℝ) ^ shellDepth m := by
      have hscaled : H / 2 ≤ (2 : ℝ) ^ shellDepth m := by
        have he : 1 / 2 ≤ (2 : ℝ) ^ shellDepth m / H := by
          simpa [H] using hendpoints.2
        have he' := (le_div_iff₀ hH).mp he
        nlinarith
      nlinarith
    have hCupper : C ≤ 2 ^ shellDepth m := by
      apply (Nat.ceil_le).2
      simpa using hxupper
    have hjupper : j ≤ shellDepth m := by
      calc
        j = Nat.clog 2 C := rfl
        _ ≤ Nat.clog 2 (2 ^ shellDepth m) :=
          Nat.clog_monotone 2 hCupper
        _ = shellDepth m := Nat.clog_pow 2 _ (by norm_num)
    have hpowLowerNat : 2 ^ (j - 1) < C := by
      exact Nat.pow_pred_clog_lt_self (by norm_num) hC
    have hpowLower : (2 : ℝ) ^ (j - 1) < H * delta := by
      simpa using (Nat.lt_ceil).mp hpowLowerNat
    have hlower : (2 : ℝ) ^ (j - 1) / H < delta := by
      apply (div_lt_iff₀ hH).2
      nlinarith
    have hceilLower : H * delta ≤ (C : ℝ) := Nat.le_ceil _
    have hCpowNat : C ≤ 2 ^ j := Nat.le_pow_clog (by norm_num) C
    have hCpow : (C : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hCpowNat
    have hupper : delta ≤ (2 : ℝ) ^ j / H := by
      apply (le_div_iff₀ hH).2
      simpa [mul_comm] using hceilLower.trans hCpow
    have hindex : shellIndex m x = j := by
      simp [shellIndex, H, delta, hnear, C, j]
    rw [hindex]
    constructor
    · simp [hjupper]
    · rw [InDyadicShell, if_neg hjpos.ne']
      exact ⟨hlower, le_min hupper (by simpa [one_div] using hdeltahalf)⟩

/-- Literal block-weighted incidence in one endpoint-pinned shell. -/
def shellIncidence
    (μ c : ℝ) (Q0 m N j : ℕ) : ℝ := by
  classical
  exact ((translatedCanonicalBlocks N).map fun B =>
      ∑ vr ∈ repunitParameterDomain N,
        if InDyadicShell m j
            ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi) then
          (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
            widthWeight B
        else 0).sum

/-- T33's exact weighted shell expression
`I_0 + sum_(j=1)^K 2^(-j) I_j`. -/
def weightedShellIncidence
    (μ c : ℝ) (Q0 m N : ℕ) : ℝ :=
  shellIncidence μ c Q0 m N 0 +
    ∑ j ∈ Finset.Icc 1 (shellDepth m),
      ((2 : ℝ) ^ j)⁻¹ * shellIncidence μ c Q0 m N j

/-- The literal incidence assertion at fixed `s,C`. -/
def ARI_cancelAt (Q0 : ℕ) (s C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
    weightedShellIncidence 8 1 Q0 m N ≤
      C * scaleMatchedTarget s m N

/-- Quantifier order: `Q0` is fixed, then one `C_s` precedes every positive
`m,N`.  This proposition is defined, not asserted for `Real.pi`. -/
def ARI_cancel (Q0 : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ C : ℝ, ARI_cancelAt Q0 s C

theorem ARI_cancel_iff_quantifiers (Q0 : ℕ) :
    ARI_cancel Q0 ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          (shellIncidence 8 1 Q0 m N 0 +
            ∑ j ∈ Finset.Icc 1 (shellDepth m),
              ((2 : ℝ) ^ j)⁻¹ * shellIncidence 8 1 Q0 m N j) ≤
            C * ((N : ℝ) + (N : ℝ) ^ 2 *
              (10 : ℝ) ^ (-s * (m : ℝ))) := by
  rfl

/-! ## Elementary kernel and shell bounds -/

theorem two_mul_nearestIntegerDistance_le_abs_sin (x : ℝ) :
    2 * nearestIntegerDistance x ≤ |Real.sin (Real.pi * x)| := by
  let u : ℝ := x - (round x : ℝ)
  have hu : |u| = nearestIntegerDistance x := by
    rfl
  have hhalf := nearestIntegerDistance_le_half x
  by_cases hzero : nearestIntegerDistance x = 0
  · simp [hzero]
  have hL : 0 < 2 * nearestIntegerDistance x := by
    have := nearestIntegerDistance_nonneg x
    positivity
  have hsin := Theory.PiDigits.T27.abs_sin_pi_mul_lower
    (u := u) (L := 2 * nearestIntegerDistance x) hL
    (by rw [hu]; linarith)
    (by rw [hu]; linarith)
  have hx : Real.pi * x = Real.pi * u + (round x : ℝ) * Real.pi := by
    dsimp [u]
    ring
  have hperiod : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * u)| := by
    rw [hx, Real.sin_add_int_mul_pi, abs_mul]
    simp
  rwa [hperiod]

theorem inclusiveDirichletKernel_eq_phase_mul
    (m : ℕ) (d : ℤ) (α : ℝ) :
    inclusiveDirichletKernel m d α =
      Theory.PiDigits.T27.phase d α *
        Theory.PiDigits.T27.dirichletKernel (10 ^ m - 1) ((d : ℝ) * α) := by
  classical
  have hH : 1 ≤ 10 ^ m := one_le_pow₀ (by norm_num)
  have hsub : 10 ^ m - 1 + 1 = 10 ^ m := Nat.sub_add_cancel hH
  have hdomain : Finset.Icc 1 (10 ^ m) =
      (Finset.range (10 ^ m)).image (fun r => r + 1) := by
    ext h
    constructor
    · intro hh
      have hrange := Finset.mem_Icc.mp hh
      apply Finset.mem_image.mpr
      refine ⟨h - 1, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
    · intro hh
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hh
      have hrange := Finset.mem_range.mp hr
      exact Finset.mem_Icc.mpr (by omega)
  unfold inclusiveDirichletKernel inclusiveFrequencies decimalFrequency
  rw [Theory.PiDigits.T27.dirichletKernel, hsub, Finset.mul_sum, hdomain]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r hr
    calc
      Theory.PiDigits.T27.phase (((r + 1 : ℕ) : ℤ) * d) α =
          Theory.PiDigits.T27.phase (d + (r : ℤ) * d) α := by
            congr 2
            push_cast
            ring
      _ = Theory.PiDigits.T27.phase d α *
          Theory.PiDigits.T27.phase ((r : ℤ) * d) α := by
            rw [Theory.PiDigits.T27.phase_add]
      _ = Theory.PiDigits.T27.phase d α *
          Theory.PiDigits.T27.phase (r : ℤ) ((d : ℝ) * α) := by
            congr 1
            unfold Theory.PiDigits.T27.phase
            congr 1
            push_cast
            ring
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab

theorem abs_inclusiveRealKernel_le_height
    (m d : ℕ) (α : ℝ) :
    |inclusiveRealKernel m d α| ≤ (10 : ℝ) ^ m := by
  have hre : |inclusiveRealKernel m d α| ≤
      ‖inclusiveDirichletKernel m (d : ℤ) α‖ := by
    exact Complex.abs_re_le_norm _
  rw [inclusiveDirichletKernel_eq_phase_mul, norm_mul,
    Theory.PiDigits.T27.norm_phase, one_mul] at hre
  refine hre.trans ?_
  calc
    ‖Theory.PiDigits.T27.dirichletKernel (10 ^ m - 1) ((d : ℝ) * α)‖ ≤
        ∑ r ∈ Finset.range (10 ^ m - 1 + 1),
          ‖Theory.PiDigits.T27.phase (r : ℤ) ((d : ℝ) * α)‖ :=
      norm_sum_le _ _
    _ = (10 : ℝ) ^ m := by
      have hH : 1 ≤ 10 ^ m := one_le_pow₀ (by norm_num)
      rw [Nat.sub_add_cancel hH]
      simp [Theory.PiDigits.T27.norm_phase]

theorem abs_inclusiveRealKernel_le_inv_distance
    {m d : ℕ} {α : ℝ}
    (hdist : 0 < nearestIntegerDistance ((d : ℝ) * α)) :
    |inclusiveRealKernel m d α| ≤
      (2 * nearestIntegerDistance ((d : ℝ) * α))⁻¹ := by
  let x : ℝ := (d : ℝ) * α
  let delta : ℝ := nearestIntegerDistance x
  have hsin := two_mul_nearestIntegerDistance_le_abs_sin x
  have hsep : 2 * (2 * delta) ≤
      ‖1 - Theory.PiDigits.T27.phase 1 x‖ := by
    rw [Theory.PiDigits.T27.norm_one_sub_phase_one]
    dsimp [delta] at hsin ⊢
    nlinarith
  have hdir := Theory.PiDigits.T27.norm_dirichletKernel_le_inv
    (H := 10 ^ m - 1) (x := x) (L := 2 * delta)
    (by dsimp [delta, x]; positivity) hsep
  have hre : |inclusiveRealKernel m d α| ≤
      ‖inclusiveDirichletKernel m (d : ℤ) α‖ :=
    Complex.abs_re_le_norm _
  rw [inclusiveDirichletKernel_eq_phase_mul, norm_mul,
    Theory.PiDigits.T27.norm_phase, one_mul] at hre
  exact hre.trans (by simpa [x, delta] using hdir)

theorem abs_inclusiveRealKernel_lt_of_mem_positive_shell
    {m d j : ℕ} {α : ℝ} (hj : 1 ≤ j)
    (hshell : InDyadicShell m j ((d : ℝ) * α)) :
    |inclusiveRealKernel m d α| < (10 : ℝ) ^ m / (2 : ℝ) ^ j := by
  have hj0 : j ≠ 0 := Nat.ne_of_gt hj
  rw [InDyadicShell, if_neg hj0] at hshell
  let delta := nearestIntegerDistance ((d : ℝ) * α)
  let H : ℝ := (10 : ℝ) ^ m
  let P : ℝ := (2 : ℝ) ^ (j - 1)
  have hH : 0 < H := by positivity
  have hP : 0 < P := by positivity
  have hlower : P / H < delta := by
    simpa [P, H, delta] using hshell.1
  have hdelta : 0 < delta := (by positivity : 0 < P / H).trans hlower
  have hkernel := abs_inclusiveRealKernel_le_inv_distance
    (m := m) (d := d) (α := α) (by simpa [delta] using hdelta)
  have hscaled : 2 * P / H < 2 * delta := by
    calc
      2 * P / H = 2 * (P / H) := by ring
      _ < 2 * delta := mul_lt_mul_of_pos_left hlower (by norm_num)
  have hinv := one_div_lt_one_div_of_lt (by positivity : 0 < 2 * P / H) hscaled
  have hjpred : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hpowsucc : (2 : ℝ) ^ j = 2 * P := by
    rw [← hjpred, pow_succ]
    simp [P]
    ring
  have hrearrange : 1 / (2 * P / H) = H / (2 : ℝ) ^ j := by
    rw [hpowsucc]
    field_simp
  exact hkernel.trans_lt (by simpa [one_div, H, delta, hrearrange] using hinv)

/-- The exact shell coefficient attached to one repunit value.  Written this
way, exchanging finite sums recovers `I_0 + sum 2^(-j) I_j`. -/
def shellWeight (m : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (if InDyadicShell m 0 x then 1 else 0) +
      ∑ j ∈ Finset.Icc 1 (shellDepth m),
        if InDyadicShell m j x then ((2 : ℝ) ^ j)⁻¹ else 0

theorem shellWeight_nonneg (m : ℕ) (x : ℝ) :
    0 ≤ shellWeight m x := by
  classical
  unfold shellWeight
  positivity

theorem abs_inclusiveRealKernel_le_height_mul_shellWeight
    (m d : ℕ) (α : ℝ) (hm : 1 ≤ m) :
    |inclusiveRealKernel m d α| ≤
      (10 : ℝ) ^ m * shellWeight m ((d : ℝ) * α) := by
  classical
  let x : ℝ := (d : ℝ) * α
  obtain ⟨hjrange, hjshell⟩ := shellIndex_mem m hm x
  have hjle : shellIndex m x ≤ shellDepth m := Finset.mem_Icc.mp hjrange |>.2
  by_cases hj0 : shellIndex m x = 0
  · have hweight : 1 ≤ shellWeight m x := by
      unfold shellWeight
      rw [if_pos (by simpa [hj0] using hjshell)]
      have hsum : 0 ≤ ∑ j ∈ Finset.Icc 1 (shellDepth m),
          if InDyadicShell m j x then ((2 : ℝ) ^ j)⁻¹ else 0 := by positivity
      linarith
    calc
      |inclusiveRealKernel m d α| ≤ (10 : ℝ) ^ m :=
        abs_inclusiveRealKernel_le_height m d α
      _ ≤ (10 : ℝ) ^ m * shellWeight m x := by
        exact le_mul_of_one_le_right (by positivity) hweight
  · have hjpos : 1 ≤ shellIndex m x := Nat.one_le_iff_ne_zero.mpr hj0
    have hjmem : shellIndex m x ∈ Finset.Icc 1 (shellDepth m) :=
      Finset.mem_Icc.mpr ⟨hjpos, hjle⟩
    have hcoeff : ((2 : ℝ) ^ shellIndex m x)⁻¹ ≤ shellWeight m x := by
      unfold shellWeight
      have hsingle : ((2 : ℝ) ^ shellIndex m x)⁻¹ ≤
          ∑ j ∈ Finset.Icc 1 (shellDepth m),
            if InDyadicShell m j x then ((2 : ℝ) ^ j)⁻¹ else 0 := by
        have hsum := Finset.single_le_sum
          (s := Finset.Icc 1 (shellDepth m))
          (f := fun j => if InDyadicShell m j x then
            ((2 : ℝ) ^ j)⁻¹ else 0)
          (fun j hj => by positivity) hjmem
        simpa [hjshell] using hsum
      have hzero : 0 ≤ if InDyadicShell m 0 x then (1 : ℝ) else 0 := by positivity
      linarith
    have hkernel := abs_inclusiveRealKernel_lt_of_mem_positive_shell
      (m := m) (d := d) (j := shellIndex m x) (α := α) hjpos
      (by simpa [x] using hjshell)
    calc
      |inclusiveRealKernel m d α| ≤
          (10 : ℝ) ^ m * ((2 : ℝ) ^ shellIndex m x)⁻¹ := by
            simpa [div_eq_mul_inv] using hkernel.le
      _ ≤ (10 : ℝ) ^ m * shellWeight m x :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)

/-- The same literal incidence before exchanging the finite shell and record
sums.  It retains every block weight and every six-row hidden-exponent
multiplicity. -/
def directWeightedShellIncidence
    (μ c : ℝ) (Q0 m N : ℕ) : ℝ :=
  ((translatedCanonicalBlocks N).map fun B =>
    ∑ vr ∈ repunitParameterDomain N,
      (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
          widthWeight B *
        shellWeight m
          ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)).sum

theorem list_sum_finset_sum_comm
    {ι A : Type*} [DecidableEq ι]
    (xs : List A) (s : Finset ι) (f : A → ι → ℝ) :
    (xs.map fun a => ∑ i ∈ s, f a i).sum =
      ∑ i ∈ s, (xs.map fun a => f a i).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Finset.sum_add_distrib]

theorem directWeightedShellIncidence_eq_shell_sum
    (μ c : ℝ) (Q0 m N : ℕ) :
    directWeightedShellIncidence μ c Q0 m N =
      weightedShellIncidence μ c Q0 m N := by
  classical
  unfold directWeightedShellIncidence weightedShellIncidence shellIncidence
  simp_rw [shellWeight, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_comm (s := repunitParameterDomain N)
    (t := Finset.Icc 1 (shellDepth m))]
  rw [List.sum_map_add]
  apply congrArg₂ (· + ·)
  · rfl
  · rw [list_sum_finset_sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro B hB
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro vr hvr
    by_cases hs : InDyadicShell m j
        ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)
    · simp [hs]
      ring
    · simp [hs]

/-- Triangle-inequality envelope for the exact complex cancelling sector. -/
def cancellingSectorEnvelope
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  2 * ((translatedCanonicalBlocks N).map fun B =>
    ∑ vr ∈ repunitParameterDomain N,
      (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
          widthWeight B *
        |inclusiveRealKernel m (cancellingValue vr.1 vr.2) α|).sum

theorem blockRegrouped_norm_le_envelope
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N)
    (μ c : ℝ) (Q0 m : ℕ) (α : ℝ) :
    ‖((∑ vr ∈ repunitParameterDomain N,
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
          (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ)) /
        (widthWeight B : ℂ))‖ ≤
      ∑ vr ∈ repunitParameterDomain N,
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
            widthWeight B *
          |inclusiveRealKernel m (cancellingValue vr.1 vr.2) α| := by
  have hw : 0 < widthWeight B := canonical_widthWeight_pos hB
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  calc
    ‖∑ vr ∈ repunitParameterDomain N,
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
          (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ)‖ /
        widthWeight B ≤
      (∑ vr ∈ repunitParameterDomain N,
        ‖(blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
          (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ)‖) /
        widthWeight B := by
          apply div_le_div_of_nonneg_right (norm_sum_le _ _) hw.le
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro vr hvr
      rw [norm_mul]
      simp only [Complex.norm_natCast, Complex.norm_real]
      rw [Real.norm_eq_abs]
      ring

theorem cancellingSector_norm_le_envelope
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    ‖cancellingSectorContribution μ c Q0 m N α‖ ≤
      cancellingSectorEnvelope μ c Q0 m N α := by
  rw [cancellingSectorContribution_eq_regrouped]
  unfold regroupedCancellingSector cancellingSectorEnvelope
  rw [norm_mul]
  norm_num
  have hsum : ∀ blocks : List DyadicBlock,
      (∀ B ∈ blocks, B ∈ translatedCanonicalBlocks N) →
      ‖(blocks.map fun B =>
          (∑ vr ∈ repunitParameterDomain N,
            (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
              (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ)) /
            (widthWeight B : ℂ)).sum‖ ≤
        (blocks.map fun B =>
          ∑ vr ∈ repunitParameterDomain N,
            (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
                widthWeight B *
              |inclusiveRealKernel m (cancellingValue vr.1 vr.2) α|).sum := by
    intro blocks hsubset
    induction blocks with
    | nil => simp
    | cons B blocks ih =>
        simp only [List.map_cons, List.sum_cons]
        refine (norm_add_le _ _).trans ?_
        apply add_le_add
        · exact blockRegrouped_norm_le_envelope
            (hsubset B (by simp)) μ c Q0 m α
        · apply ih
          intro B' hB'
          exact hsubset B' (by simp [hB'])
  exact hsum (translatedCanonicalBlocks N) (fun _ h => h)

theorem cancellingSectorEnvelope_le_incidence
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) :
    cancellingSectorEnvelope μ c Q0 m N Real.pi ≤
      2 * (10 : ℝ) ^ m * directWeightedShellIncidence μ c Q0 m N := by
  unfold cancellingSectorEnvelope directWeightedShellIncidence
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ((translatedCanonicalBlocks N).map fun B =>
      ∑ vr ∈ repunitParameterDomain N,
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
            widthWeight B *
          |inclusiveRealKernel m (cancellingValue vr.1 vr.2) Real.pi|).sum ≤
        ((translatedCanonicalBlocks N).map fun B =>
          (10 : ℝ) ^ m *
            ∑ vr ∈ repunitParameterDomain N,
              (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
                  widthWeight B *
                shellWeight m
                  ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)).sum := by
      apply list_sum_map_le_sum_map
      intro B hB
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro vr hvr
      have hw : 0 < widthWeight B := canonical_widthWeight_pos hB
      have hcoeff : 0 ≤
          (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
            widthWeight B := div_nonneg (by positivity) hw.le
      have hkernel := abs_inclusiveRealKernel_le_height_mul_shellWeight
        m (cancellingValue vr.1 vr.2) Real.pi hm
      calc
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
              widthWeight B *
            |inclusiveRealKernel m (cancellingValue vr.1 vr.2) Real.pi| ≤
          (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
              widthWeight B *
            ((10 : ℝ) ^ m * shellWeight m
              ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)) :=
          mul_le_mul_of_nonneg_left hkernel hcoeff
        _ = (10 : ℝ) ^ m *
            ((blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
                widthWeight B *
              shellWeight m
                ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)) := by ring
    _ = (10 : ℝ) ^ m *
        ((translatedCanonicalBlocks N).map fun B =>
          ∑ vr ∈ repunitParameterDomain N,
            (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) /
                widthWeight B *
              shellWeight m
                ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)).sum := by
      rw [List.sum_map_mul_left]

/-- Constant-tracked finite estimate (T33 equation (6.7)). -/
theorem cancellingSector_norm_le_weightedShellIncidence
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) :
    ‖cancellingSectorContribution μ c Q0 m N Real.pi‖ ≤
      2 * (10 : ℝ) ^ m * weightedShellIncidence μ c Q0 m N := by
  calc
    _ ≤ cancellingSectorEnvelope μ c Q0 m N Real.pi :=
      cancellingSector_norm_le_envelope μ c Q0 m N Real.pi
    _ ≤ 2 * (10 : ℝ) ^ m * directWeightedShellIncidence μ c Q0 m N :=
      cancellingSectorEnvelope_le_incidence μ c Q0 m N hm
    _ = _ := by rw [directWeightedShellIncidence_eq_shell_sum]

/-- Literal fixed-scale implication from the displayed T33 incidence sum.
The premise contains `I_0 + sum_(j=1)^K 2^(-j) I_j` verbatim. -/
theorem cancellingSector_bound_of_literal_incidence
    {Q0 m N : ℕ} {s C : ℝ} (hm : 1 ≤ m)
    (hinc :
      shellIncidence 8 1 Q0 m N 0 +
        ∑ j ∈ Finset.Icc 1 (shellDepth m),
          ((2 : ℝ) ^ j)⁻¹ * shellIncidence 8 1 Q0 m N j ≤
        C * ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-s * (m : ℝ)))) :
    ‖cancellingSectorContribution 8 1 Q0 m N Real.pi‖ ≤
      2 * C * (10 : ℝ) ^ m *
        ((N : ℝ) + (N : ℝ) ^ 2 * (10 : ℝ) ^ (-s * (m : ℝ))) := by
  calc
    _ ≤ 2 * (10 : ℝ) ^ m * weightedShellIncidence 8 1 Q0 m N :=
      cancellingSector_norm_le_weightedShellIncidence 8 1 Q0 m N hm
    _ ≤ 2 * (10 : ℝ) ^ m *
        (C * ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-s * (m : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [weightedShellIncidence] using hinc
    _ = _ := by ring

/-- The sector-only implication at fixed `s,C`.  No assertion of the
incidence hypothesis is made. -/
theorem cancellingSector_bound_of_ARI_cancelAt
    {Q0 m N : ℕ} {s C : ℝ}
    (hARI : ARI_cancelAt Q0 s C) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    ‖cancellingSectorContribution 8 1 Q0 m N Real.pi‖ ≤
      2 * C * (10 : ℝ) ^ m *
        ((N : ℝ) + (N : ℝ) ^ 2 * (10 : ℝ) ^ (-s * (m : ℝ))) := by
  apply cancellingSector_bound_of_literal_incidence hm
  simpa [weightedShellIncidence, scaleMatchedTarget] using hARI.2 m N hm hN

/-- Final quantified frontier: `ARI_cancel Q0` conditionally supplies one
sector constant before every positive `m,N`.  This is not T29's complete
square-function predicate and has no C2 or C1 conclusion. -/
theorem ARI_cancel_implies_cancellingSectorBound
    {Q0 : ℕ} (hARI : ARI_cancel Q0) :
    ∀ s : ℝ, 0 < s → s < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        ‖cancellingSectorContribution 8 1 Q0 m N Real.pi‖ ≤
          2 * C * (10 : ℝ) ^ m *
            ((N : ℝ) + (N : ℝ) ^ 2 *
              (10 : ℝ) ^ (-s * (m : ℝ))) := by
  intro s hs hs1
  obtain ⟨C, hC⟩ := hARI s hs hs1
  refine ⟨C, hC.1, ?_⟩
  intro m N hm hN
  exact cancellingSector_bound_of_ARI_cancelAt hC hm hN

end Theory.PiDigits.LongLagBlockCollisionDecay.T34
