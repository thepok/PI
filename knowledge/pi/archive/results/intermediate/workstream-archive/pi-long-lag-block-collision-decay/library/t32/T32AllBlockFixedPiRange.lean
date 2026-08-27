import TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD
import TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff
import TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction

/-!
# T32: exact all-block fixed-phase partial range

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module formalizes only a restricted residual sparse-Fourier sibling of the
canonical collision question. It proves a finite identity and a phase-uniform
bound in the range `(L * (L + 1)) ^ 2 <= N`, where `L = N - m`. It does not
assert T29's all-scale premise at `Real.pi`, a collision estimate, or C1.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T32

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- Exact records whose strict frequency endpoint lies in the half-open block
`[B.start, B.finish)`. The subtraction of cutoffs retains both Bool
orientations and every arithmetic exclusion from T22. -/
def blockRecordDomain
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) : Finset OrderedLongPair :=
  orderedLongPairDomain μ c Q0 m B.finish \
    orderedLongPairDomain μ c Q0 m B.start

/-- Membership exposes admissibility, the weak left endpoint, and the strict
right endpoint. -/
theorem mem_blockRecordDomain_iff
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock} {q : OrderedLongPair} :
    q ∈ blockRecordDomain μ c Q0 m B ↔
      AdmissibleOrderedFrequency μ c Q0 m q ∧
        B.start ≤ frequencyEndpoint q.2 ∧
        frequencyEndpoint q.2 < B.finish := by
  classical
  rw [blockRecordDomain, Finset.mem_sdiff,
    mem_orderedLongPairDomain_iff_admissible_endpoint]
  constructor
  · rintro ⟨⟨hq, hfinish⟩, hnot⟩
    refine ⟨hq, ?_, hfinish⟩
    by_contra hstart
    apply hnot
    exact mem_orderedLongPairDomain_iff_admissible_endpoint.mpr
      ⟨hq, by omega⟩
  · rintro ⟨hq, hstart, hfinish⟩
    refine ⟨⟨hq, hfinish⟩, ?_⟩
    intro hqStart
    have hend :=
      (mem_orderedLongPairDomain_iff_admissible_endpoint.mp hqStart).2
    omega

/-- Reversing an ordered pair preserves its block and negates its signed
frequency. -/
theorem reverseOrientation_mem_blockRecordDomain_iff
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (q : OrderedLongPair) :
    reverseOrientation q ∈ blockRecordDomain μ c Q0 m B ↔
      q ∈ blockRecordDomain μ c Q0 m B := by
  rw [mem_blockRecordDomain_iff, mem_blockRecordDomain_iff,
    admissible_reverseOrientation_iff]
  rfl

/-- Both literal ordered orientations occur together, with coefficient one
and opposite nonzero signed frequencies, exactly under the displayed block,
lag, and arithmetic-survival conditions. -/
theorem blockRecordDomain_both_orientations
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (p : LongPairCore) :
    (((false, p) ∈ blockRecordDomain μ c Q0 m B ↔
        0 < p.1 ∧ m ≤ p.1 ∧
          ¬ArithmeticExcluded μ c Q0 m p.2 p.1 ∧
          B.start ≤ frequencyEndpoint p ∧ frequencyEndpoint p < B.finish) ∧
      ((true, p) ∈ blockRecordDomain μ c Q0 m B ↔
        0 < p.1 ∧ m ≤ p.1 ∧
          ¬ArithmeticExcluded μ c Q0 m p.2 p.1 ∧
          B.start ≤ frequencyEndpoint p ∧ frequencyEndpoint p < B.finish)) ∧
      signedDecimalFrequency (false, p) = -(positiveDecimalFrequency p : ℤ) ∧
      signedDecimalFrequency (true, p) = (positiveDecimalFrequency p : ℤ) := by
  constructor
  · constructor <;> rw [mem_blockRecordDomain_iff] <;>
      simp only [AdmissibleOrderedFrequency] <;> tauto
  · simp [signedDecimalFrequency]

/-- Earlier cutoffs are subsets of later cutoffs. -/
theorem orderedLongPairDomain_mono_endpoint
    (μ c : ℝ) (Q0 m a b : ℕ) (hab : a ≤ b) :
    orderedLongPairDomain μ c Q0 m a ⊆
      orderedLongPairDomain μ c Q0 m b := by
  intro q hq
  rw [mem_orderedLongPairDomain_iff_admissible_endpoint] at hq ⊢
  exact ⟨hq.1, hq.2.trans_le hab⟩

/-- The T29 block vector is the literal coefficient-one sum over the exact
block records. -/
theorem canonicalBlockVector_eq_sum_blockRecords
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) :
    canonicalBlockVector μ c Q0 m B α h =
      ∑ q ∈ blockRecordDomain μ c Q0 m B,
        Theory.PiDigits.T27.phase (h : ℤ)
          ((signedDecimalFrequency q : ℝ) * α) := by
  have hsubset : orderedLongPairDomain μ c Q0 m B.start ⊆
      orderedLongPairDomain μ c Q0 m B.finish :=
    orderedLongPairDomain_mono_endpoint μ c Q0 m _ _
      (by simp [DyadicBlock.finish])
  rw [canonicalBlockVector, ← orderedAlphaSum_eq_cutoffFourierSum,
    ← orderedAlphaSum_eq_cutoffFourierSum]
  unfold orderedAlphaSum blockRecordDomain
  symm
  rw [eq_sub_iff_add_eq]
  exact Finset.sum_sdiff hsubset

/-- One-sided Dirichlet kernel on exactly the inclusive frequencies
`h = 1,...,10^m`; frequency zero is absent and `h=10^m` is retained. -/
def inclusiveDirichletKernel (m : ℕ) (d : ℤ) (α : ℝ) : ℂ :=
  ∑ h ∈ inclusiveFrequencies m,
    Theory.PiDigits.T27.phase ((h : ℤ) * d) α

/-- The zero argument contributes exactly `10^m`, not `10^m+1`. -/
theorem inclusiveDirichletKernel_zero
    (m : ℕ) (α : ℝ) :
    inclusiveDirichletKernel m 0 α = (10 ^ m : ℕ) := by
  simp [inclusiveDirichletKernel, inclusiveFrequencies, decimalFrequency,
    Theory.PiDigits.T27.phase_zero]

/-- Pointwise squared-norm expansion over the exact block records. -/
theorem canonicalBlockVector_norm_sq_expansion
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) :
    ((‖canonicalBlockVector μ c Q0 m B α h‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ blockRecordDomain μ c Q0 m B,
        ∑ r ∈ blockRecordDomain μ c Q0 m B,
          Theory.PiDigits.T27.phase
            ((h : ℤ) *
              (signedDecimalFrequency r - signedDecimalFrequency q)) α := by
  rw [canonicalBlockVector_eq_sum_blockRecords,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  unfold Theory.PiDigits.T27.phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    map_intCast, Int.cast_sub, Int.cast_mul]
  push_cast
  ring

/-- Exact finite Dirichlet-kernel expansion, before separating diagonal and
off-diagonal record pairs. -/
theorem blockSquaredEnergy_eq_dirichletKernel
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (α : ℝ) :
    ((blockSquaredEnergy μ c Q0 m B α : ℝ) : ℂ) =
      ∑ q ∈ blockRecordDomain μ c Q0 m B,
        ∑ r ∈ blockRecordDomain μ c Q0 m B,
          inclusiveDirichletKernel m
            (signedDecimalFrequency r - signedDecimalFrequency q) α := by
  classical
  unfold blockSquaredEnergy inclusiveDirichletKernel
  calc
    ((↑(∑ h ∈ inclusiveFrequencies m,
        ‖canonicalBlockVector μ c Q0 m B α h‖ ^ 2) : ℂ)) =
        ∑ h ∈ inclusiveFrequencies m,
          ((‖canonicalBlockVector μ c Q0 m B α h‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = ∑ h ∈ inclusiveFrequencies m,
          ∑ q ∈ blockRecordDomain μ c Q0 m B,
            ∑ r ∈ blockRecordDomain μ c Q0 m B,
              Theory.PiDigits.T27.phase
                ((h : ℤ) *
                  (signedDecimalFrequency r - signedDecimalFrequency q)) α := by
      apply Finset.sum_congr rfl
      intro h hh
      exact canonicalBlockVector_norm_sq_expansion μ c Q0 m B h α
    _ = ∑ q ∈ blockRecordDomain μ c Q0 m B,
          ∑ r ∈ blockRecordDomain μ c Q0 m B,
            ∑ h ∈ inclusiveFrequencies m,
              Theory.PiDigits.T27.phase
                ((h : ℤ) *
                  (signedDecimalFrequency r - signedDecimalFrequency q)) α := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]

/-- Off-diagonal ordered record-pair contribution. Both orientations are
retained; no absolute value or fixed-phase cancellation is asserted. -/
def offDiagonalDirichletSum
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (α : ℝ) : ℂ :=
  ∑ qr ∈ (blockRecordDomain μ c Q0 m B ×ˢ
      blockRecordDomain μ c Q0 m B).filter (fun qr => qr.1 ≠ qr.2),
    inclusiveDirichletKernel m
      (signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) α

/-- Exact diagonal/off-diagonal expansion. There are exactly `M_B` diagonal
pairs, each contributing the inclusive endpoint count `10^m`. -/
theorem blockSquaredEnergy_eq_diagonal_add_offDiagonal
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (α : ℝ) :
    ((blockSquaredEnergy μ c Q0 m B α : ℝ) : ℂ) =
      ((10 ^ m : ℕ) * (blockRecordDomain μ c Q0 m B).card : ℕ) +
        offDiagonalDirichletSum μ c Q0 m B α := by
  classical
  let Q := blockRecordDomain μ c Q0 m B
  let P := Q ×ˢ Q
  let f : OrderedLongPair × OrderedLongPair → ℂ := fun qr =>
    inclusiveDirichletKernel m
      (signedDecimalFrequency qr.2 - signedDecimalFrequency qr.1) α
  have hdiag :
      (∑ qr ∈ P.filter (fun qr => ¬qr.1 ≠ qr.2), f qr) =
        (((10 ^ m : ℕ) * Q.card : ℕ) : ℂ) := by
    dsimp [P]
    rw [Finset.sum_filter, Finset.sum_product]
    simp only [not_not]
    calc
      (∑ q ∈ Q, ∑ r ∈ Q, if q = r then f (q, r) else 0) =
          ∑ _q ∈ Q, ((10 ^ m : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp [hq, f, inclusiveDirichletKernel_zero]
      _ = (((10 ^ m : ℕ) * Q.card : ℕ) : ℂ) := by
        simp
        ring
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun qr => qr.1 ≠ qr.2) f
  rw [blockSquaredEnergy_eq_dirichletKernel]
  change (∑ q ∈ Q, ∑ r ∈ Q, f (q, r)) = _
  rw [← Finset.sum_product]
  change (∑ qr ∈ P, f qr) = _
  calc
    (∑ qr ∈ P, f qr) =
        (∑ qr ∈ P.filter (fun qr => qr.1 ≠ qr.2), f qr) +
          ∑ qr ∈ P.filter (fun qr => ¬qr.1 ≠ qr.2), f qr := hsplit.symm
    _ = (∑ qr ∈ P.filter (fun qr => qr.1 ≠ qr.2), f qr) +
          (((10 ^ m : ℕ) * Q.card : ℕ) : ℂ) := by rw [hdiag]
    _ = (((10 ^ m : ℕ) * Q.card : ℕ) : ℂ) +
          ∑ qr ∈ P.filter (fun qr => qr.1 ≠ qr.2), f qr := add_comm _ _
    _ = _ := by rfl

/-- The exact all-block diagonal/off-diagonal identity with T24's canonical
blocks and T29's literal width weight in every denominator. -/
theorem widthWeightedSquareFunction_eq_diagonal_add_offDiagonal
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    ((widthWeightedSquareFunction μ c Q0 m N α : ℝ) : ℂ) =
      ((translatedCanonicalBlocks N).map fun B =>
        ((((10 ^ m : ℕ) * (blockRecordDomain μ c Q0 m B).card : ℕ) : ℂ) +
          offDiagonalDirichletSum μ c Q0 m B α) /
            (widthWeight B : ℂ)).sum := by
  unfold widthWeightedSquareFunction
  induction translatedCanonicalBlocks N with
  | nil => simp
  | cons B blocks ih =>
      simp only [List.map_cons, List.sum_cons]
      push_cast
      rw [blockSquaredEnergy_eq_diagonal_add_offDiagonal, ih]
      simp only [Nat.cast_mul]
      norm_num

/-! ## Complete imported valuation interfaces -/

/-- The inclusive frequency endpoint `h=10^m` is the unique case of
10-valuation `m`; every other retained positive frequency has smaller
valuation. -/
theorem inclusiveFrequency_valuation_cases
    {m h : ℕ} (hh : h ∈ inclusiveFrequencies m) :
    tenValuation h ≤ m ∧
      (tenValuation h = m ↔ h = 10 ^ m) ∧
      (tenValuation h < m ∨ h = 10 ^ m) := by
  apply decimalFrequency_valuation_cases
  simpa [inclusiveFrequencies, decimalFrequencyDomain, decimalFrequency] using hh

/-- Noncancelling lowest decimal coefficients are exactly the four possible
residues `+1,+2,-2,-1`, represented by `1,2,8,9` modulo ten. -/
theorem noncancellingLowestCoefficient_valuation
    (ell A coeff : ℕ)
    (hcoeff : coeff = 1 ∨ coeff = 2 ∨ coeff = 8 ∨ coeff = 9) :
    tenValuation (10 ^ ell * (coeff + 10 * A)) = ell :=
  tenValuation_lowDecimalCoefficient ell A coeff hcoeff

/-- Every cancelling two-token residual has the exact composite-base
valuation and primitive part shown here. -/
theorem cancellingDifference_valuation
    (v r : ℕ) (hr : 1 ≤ r) :
    tenValuation (10 ^ v * (10 ^ r - 1)) = v ∧
      tenPrimitivePart (10 ^ v * (10 ^ r - 1)) = 10 ^ r - 1 :=
  cancellationValue_ten_reduction v r hr

/-- T16's exhaustive primitive/cancelling partition applies to every exact
positive long-difference witness, with all four exponent domains and both
weak lag hypotheses retained by `longDifferenceDomain`. -/
theorem longDifference_primitive_or_cancelling
    {m N : ℕ} {a : BoundedExponentVector 4 N}
    (ha : a ∈ longDifferenceDomain m N) :
    a ∈ primitiveFourTokenDomain N ∨
      a ∈ cancellingFourTokenDomain N := by
  have hall := longDifferenceDomain_subset_allPositive m N ha
  rw [allPositiveFourTokenDomain_partition] at hall
  exact Finset.mem_union.mp hall

/-- The inherited full ordinary-GCD bound includes the primitive/primitive,
both mixed, and cancelling/cancelling valuation sectors. The numerical
constant is exposed and no estimate of a Dirichlet kernel at `Real.pi` is
deduced from it. -/
theorem inherited_longDifferenceWeightedGCD_le (m N : ℕ) :
    longDifferenceMultiplicityWeightedGCD m N ≤
      574913232 * (N : ℚ) ^ 4 :=
  longDifferenceMultiplicityWeightedGCD_le m N

/-! ## Exact record count -/

/-- Triangular endpoint envelope: orientation, shifted endpoint
`u=endpoint-m < N-m`, and start `n <= u`. -/
def endpointEnvelope (m N : ℕ) : Finset OrderedLongPair :=
  (Finset.univ : Finset Bool).product
    ((Finset.range (N - m)).sigma fun u => Finset.range (u + 1))

/-- Injective endpoint-envelope encoding of an ordered record. -/
def endpointEnvelopeCode (m : ℕ) (q : OrderedLongPair) : OrderedLongPair :=
  (q.1, ⟨frequencyEndpoint q.2 - m, q.2.2⟩)

theorem endpointEnvelopeCode_mem
    {μ c : ℝ} {Q0 m N : ℕ} {q : OrderedLongPair}
    (hq : q ∈ orderedLongPairDomain μ c Q0 m N) :
    endpointEnvelopeCode m q ∈ endpointEnvelope m N := by
  have hq' := mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_univ _, Finset.mem_sigma.mpr ?_⟩
  refine ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
  · have hmend : m ≤ frequencyEndpoint q.2 := by
      simp only [frequencyEndpoint]
      exact hq'.1.2.1.trans (Nat.le_add_left q.2.1 q.2.2)
    simp only [endpointEnvelopeCode]
    omega
  · simp only [endpointEnvelopeCode, frequencyEndpoint]
    have hmr := hq'.1.2.1
    omega

theorem endpointEnvelopeCode_injOn
    (μ c : ℝ) (Q0 m N : ℕ) :
    Set.InjOn (endpointEnvelopeCode m)
      (orderedLongPairDomain μ c Q0 m N : Set OrderedLongPair) := by
  intro q₁ hq₁ q₂ hq₂ heq
  rcases q₁ with ⟨b₁, ⟨r₁, n₁⟩⟩
  rcases q₂ with ⟨b₂, ⟨r₂, n₂⟩⟩
  have hb := congrArg (fun q : OrderedLongPair => q.1) heq
  have hu := congrArg (fun q : OrderedLongPair => q.2.1) heq
  have hn := congrArg (fun q : OrderedLongPair => q.2.2) heq
  simp only [endpointEnvelopeCode, frequencyEndpoint] at hb hu hn
  have hmem₁ := mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq₁
  have hmem₂ := mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq₂
  simp only [AdmissibleOrderedFrequency] at hmem₁ hmem₂
  have hr : r₁ = r₂ := by omega
  subst b₂
  subst n₂
  subst r₂
  rfl

theorem endpointEnvelope_card (m N : ℕ) :
    (endpointEnvelope m N).card = (N - m) * (N - m + 1) := by
  let L := N - m
  calc
    (endpointEnvelope m N).card =
        (Finset.univ : Finset Bool).card *
          ((Finset.range L).sigma fun u => Finset.range (u + 1)).card := by
      exact Finset.card_product _ _
    _ = 2 * (∑ u ∈ Finset.range L, (u + 1)) := by
      rw [Finset.card_sigma]
      simp
    _ = L * (L + 1) := by
      have hsum : (∑ u ∈ Finset.range L, (u + 1)) =
          (∑ u ∈ Finset.range L, u) + L := by
        rw [Finset.sum_add_distrib]
        simp
      rw [hsum]
      have hid := Finset.sum_range_id_mul_two L
      calc
        2 * ((∑ u ∈ Finset.range L, u) + L) =
            (∑ u ∈ Finset.range L, u) * 2 + 2 * L := by ring
        _ = L * (L - 1) + 2 * L := by rw [hid]
        _ = L * (L + 1) := by
          cases L with
          | zero => simp
          | succ k => simp; ring
    _ = (N - m) * (N - m + 1) := by rfl

/-- Exact sharper cardinal bound with both orientations. -/
theorem orderedLongPairDomain_card_le_width
    (μ c : ℝ) (Q0 m N : ℕ) :
    (orderedLongPairDomain μ c Q0 m N).card ≤
      (N - m) * (N - m + 1) := by
  classical
  let Q := orderedLongPairDomain μ c Q0 m N
  let code := endpointEnvelopeCode m
  have himage : Q.image code ⊆ endpointEnvelope m N := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    exact endpointEnvelopeCode_mem hq
  have hcard : (Q.image code).card = Q.card :=
    Finset.card_image_iff.mpr
      (endpointEnvelopeCode_injOn μ c Q0 m N)
  rw [← hcard, ← endpointEnvelope_card m N]
  exact Finset.card_le_card himage

theorem blockRecordDomain_card_eq_sub
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) :
    (blockRecordDomain μ c Q0 m B).card =
      (orderedLongPairDomain μ c Q0 m B.finish).card -
        (orderedLongPairDomain μ c Q0 m B.start).card := by
  classical
  rw [blockRecordDomain, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr]
  exact orderedLongPairDomain_mono_endpoint μ c Q0 m _ _
    (by simp [DyadicBlock.finish])

theorem orderedLongPairDomain_one_eq_empty
    (μ c : ℝ) (Q0 m : ℕ) (hm : 1 ≤ m) :
    orderedLongPairDomain μ c Q0 m 1 = ∅ := by
  ext q
  constructor
  · intro hq
    have hq' := mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq
    have hmend : m ≤ frequencyEndpoint q.2 := by
      simp only [frequencyEndpoint]
      exact hq'.1.2.1.trans (Nat.le_add_left q.2.1 q.2.2)
    omega
  · simp

/-- T24's canonical blocks partition all records with strict endpoint below
`N`; this cardinal identity includes both orientations and every exclusion. -/
theorem canonicalBlockRecord_card_sum
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    ((translatedCanonicalBlocks N).map fun B =>
      (blockRecordDomain μ c Q0 m B).card).sum =
        (orderedLongPairDomain μ c Q0 m N).card := by
  let F : ℕ → ℤ := fun K =>
    ((orderedLongPairDomain μ c Q0 m K).card : ℤ)
  have hpoint (B : DyadicBlock) :
      ((blockRecordDomain μ c Q0 m B).card : ℤ) =
        F B.finish - F B.start := by
    have hsubset := orderedLongPairDomain_mono_endpoint μ c Q0 m
      B.start B.finish (by simp [DyadicBlock.finish])
    have hcardle :
        (orderedLongPairDomain μ c Q0 m B.start).card ≤
          (orderedLongPairDomain μ c Q0 m B.finish).card :=
      Finset.card_le_card hsubset
    rw [blockRecordDomain_card_eq_sub]
    dsimp [F]
    rw [Nat.cast_sub hcardle]
  have htelescope := canonicalDyadicPartition_endpoint_telescope F hN
  have hsumZ :
      (((translatedCanonicalBlocks N).map fun B =>
        (blockRecordDomain μ c Q0 m B).card).sum : ℤ) =
          F N - F 1 := by
    calc
      (((translatedCanonicalBlocks N).map fun B =>
          (blockRecordDomain μ c Q0 m B).card).sum : ℤ) =
          ((translatedCanonicalBlocks N).map fun B =>
            ((blockRecordDomain μ c Q0 m B).card : ℤ)).sum := by
        induction translatedCanonicalBlocks N with
        | nil => simp
        | cons B blocks ih => simp [ih]
      _ = ((translatedCanonicalBlocks N).map fun B =>
            F B.finish - F B.start).sum := by
        simp_rw [hpoint]
      _ = F N - F 1 := htelescope
  have hQ1 := orderedLongPairDomain_one_eq_empty μ c Q0 m hm
  simp only [F, hQ1, Finset.card_empty, Nat.cast_zero, sub_zero] at hsumZ
  exact_mod_cast hsumZ

/-! ## Phase-uniform restricted bound -/

theorem canonicalBlockVector_norm_le_card
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) :
    ‖canonicalBlockVector μ c Q0 m B α h‖ ≤
      (blockRecordDomain μ c Q0 m B).card := by
  rw [canonicalBlockVector_eq_sum_blockRecords]
  calc
    ‖∑ q ∈ blockRecordDomain μ c Q0 m B,
        Theory.PiDigits.T27.phase (h : ℤ)
          ((signedDecimalFrequency q : ℝ) * α)‖ ≤
        ∑ q ∈ blockRecordDomain μ c Q0 m B,
          ‖Theory.PiDigits.T27.phase (h : ℤ)
            ((signedDecimalFrequency q : ℝ) * α)‖ := norm_sum_le _ _
    _ = (blockRecordDomain μ c Q0 m B).card := by
      simp [Theory.PiDigits.T27.norm_phase]

theorem blockSquaredEnergy_le_card_sq
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (α : ℝ) :
    blockSquaredEnergy μ c Q0 m B α ≤
      (10 ^ m : ℝ) * ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2 := by
  unfold blockSquaredEnergy
  calc
    (∑ h ∈ inclusiveFrequencies m,
        ‖canonicalBlockVector μ c Q0 m B α h‖ ^ 2) ≤
        ∑ _h ∈ inclusiveFrequencies m,
          ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro h hh
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
        (canonicalBlockVector_norm_le_card μ c Q0 m B h α)
    _ = (10 ^ m : ℝ) *
          ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2 := by
      simp [inclusiveFrequencies, decimalFrequency]

/-- Every canonical width is at least one. The literal weight remains
`sqrt(B.finish^2-B.start^2)`. -/
theorem canonical_widthWeight_one_le
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    1 ≤ widthWeight B := by
  have hstart := canonicalDyadicPartition_start_pos hB
  have hfinish : B.start < B.finish := by
    simp [DyadicBlock.finish, DyadicBlock.blockLength]
  have hstartR : (1 : ℝ) ≤ B.start := by exact_mod_cast hstart
  have hfinishR : (B.start : ℝ) + 1 ≤ B.finish := by
    exact_mod_cast (show B.start + 1 ≤ B.finish by omega)
  have hrad : (1 : ℝ) ≤
      (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2 := by
    nlinarith
  unfold widthWeight
  apply (Real.le_sqrt (by norm_num) (by linarith :
    0 ≤ (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).2
  simpa using hrad

/-- The sharp universal lower constant used by the T30 specification:
every nonempty canonical block has weight at least `sqrt 3`. -/
theorem canonical_sqrt_three_le_widthWeight
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    Real.sqrt 3 ≤ widthWeight B := by
  have hstart := canonicalDyadicPartition_start_pos hB
  have hfinish : B.start < B.finish := by
    simp [DyadicBlock.finish, DyadicBlock.blockLength]
  have hstartR : (1 : ℝ) ≤ B.start := by exact_mod_cast hstart
  have hfinishR : (B.start : ℝ) + 1 ≤ B.finish := by
    exact_mod_cast (show B.start + 1 ≤ B.finish by omega)
  have hrad : (3 : ℝ) ≤
      (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2 := by
    nlinarith
  unfold widthWeight
  apply (Real.le_sqrt (Real.sqrt_nonneg 3) (by linarith)).2
  rw [Real.sq_sqrt (by norm_num)]
  exact hrad

theorem list_sum_sq_le_sq_sum_nonneg (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map fun x => x ^ 2).sum ≤ xs.sum ^ 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hx0 : 0 ≤ x := hx x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := fun y hy => hx y (by simp [hy])
      have hsum0 : 0 ≤ xs.sum := List.sum_nonneg htail
      nlinarith [ih htail]

theorem list_natCast_sum (xs : List ℕ) :
    (List.map (fun n : ℕ => (n : ℝ)) xs).sum = (xs.sum : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

/-- Unconditional all-parameter triangle majorant, valid at every phase. -/
theorem widthWeightedSquareFunction_le_width_count
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    widthWeightedSquareFunction μ c Q0 m N α ≤
      (10 ^ m : ℝ) * (((N - m) * (N - m + 1) : ℕ) : ℝ) ^ 2 := by
  let blocks := translatedCanonicalBlocks N
  let counts : List ℝ := blocks.map fun B =>
    ((blockRecordDomain μ c Q0 m B).card : ℝ)
  have hpoint : ∀ B ∈ blocks,
      blockSquaredEnergy μ c Q0 m B α / widthWeight B ≤
        (10 ^ m : ℝ) * ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2 := by
    intro B hB
    have hw1 := canonical_widthWeight_one_le hB
    have hwpos : 0 < widthWeight B := lt_of_lt_of_le zero_lt_one hw1
    have henergy := blockSquaredEnergy_le_card_sq μ c Q0 m B α
    apply (div_le_iff₀ hwpos).2
    have htarget : 0 ≤
        (10 ^ m : ℝ) * ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2 := by
      positivity
    calc
      blockSquaredEnergy μ c Q0 m B α ≤
          (10 ^ m : ℝ) *
            ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2 := henergy
      _ ≤ ((10 ^ m : ℝ) *
            ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2) *
              widthWeight B := by nlinarith
  have hblocks :
      (blocks.map fun B =>
        blockSquaredEnergy μ c Q0 m B α / widthWeight B).sum ≤
        (blocks.map fun B =>
          (10 ^ m : ℝ) *
            ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2).sum :=
    list_sum_map_le_sum_map blocks _ _ hpoint
  have hfactor :
      (blocks.map fun B =>
        (10 ^ m : ℝ) *
          ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2).sum =
        (10 ^ m : ℝ) * (counts.map fun x => x ^ 2).sum := by
    dsimp [counts]
    rw [List.sum_map_mul_left]
    simp [List.map_map, Function.comp_def]
  have hcountsNonneg : ∀ x ∈ counts, 0 ≤ x := by
    intro x hx
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hx
    positivity
  have hcountSq := list_sum_sq_le_sq_sum_nonneg counts hcountsNonneg
  have hcountSum : counts.sum =
      ((orderedLongPairDomain μ c Q0 m N).card : ℝ) := by
    have hnat := canonicalBlockRecord_card_sum μ c Q0 m N hm hN
    dsimp [counts, blocks]
    rw [← hnat]
    simpa [List.map_map, Function.comp_def] using
      (list_natCast_sum
        ((translatedCanonicalBlocks N).map fun B =>
          (blockRecordDomain μ c Q0 m B).card))
  have hcardNat := orderedLongPairDomain_card_le_width μ c Q0 m N
  have hcard : ((orderedLongPairDomain μ c Q0 m N).card : ℝ) ≤
      (((N - m) * (N - m + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hH : (0 : ℝ) ≤ 10 ^ m := by positivity
  unfold widthWeightedSquareFunction
  change (blocks.map fun B =>
    blockSquaredEnergy μ c Q0 m B α / widthWeight B).sum ≤ _
  calc
    (blocks.map fun B =>
        blockSquaredEnergy μ c Q0 m B α / widthWeight B).sum ≤
        (blocks.map fun B =>
          (10 ^ m : ℝ) *
            ((blockRecordDomain μ c Q0 m B).card : ℝ) ^ 2).sum := hblocks
    _ = (10 ^ m : ℝ) * (counts.map fun x => x ^ 2).sum := hfactor
    _ ≤ (10 ^ m : ℝ) * counts.sum ^ 2 :=
      mul_le_mul_of_nonneg_left hcountSq hH
    _ = (10 ^ m : ℝ) *
          ((orderedLongPairDomain μ c Q0 m N).card : ℝ) ^ 2 := by rw [hcountSum]
    _ ≤ (10 ^ m : ℝ) *
          (((N - m) * (N - m + 1) : ℕ) : ℝ) ^ 2 := by
      gcongr

/-- Phase-uniform constant-one estimate on the exact partial range
`L=N-m`, `(L(L+1))^2 <= N`. -/
theorem phaseUniform_partialRange
    (μ c α : ℝ) (Q0 m N : ℕ)
    (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hrange : ((N - m) * (N - m + 1)) ^ 2 ≤ N) :
    widthWeightedSquareFunction μ c Q0 m N α ≤
      (10 ^ m : ℝ) * (N : ℝ) := by
  have hmajor := widthWeightedSquareFunction_le_width_count
    μ c Q0 m N α hm hN
  have hrange' :
      ((((N - m) * (N - m + 1) : ℕ) : ℝ) ^ 2) ≤ (N : ℝ) := by
    exact_mod_cast hrange
  nlinarith [show (0 : ℝ) ≤ 10 ^ m by positivity]

/-- The requested specialization to the fixed phase `alpha=pi`, still only
on the explicit partial range and with constant one. -/
theorem fixedPi_partialRange
    (μ c s : ℝ) (Q0 m N : ℕ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hs0 : 0 < s) (hs1 : s < 1)
    (hrange : ((N - m) * (N - m + 1)) ^ 2 ≤ N) :
    widthWeightedSquareFunction μ c Q0 m N Real.pi ≤
      (10 ^ m : ℝ) * scaleMatchedTarget s m N := by
  have hpartial := phaseUniform_partialRange μ c Real.pi Q0 m N hm hN hrange
  have hNtarget : (N : ℝ) ≤ scaleMatchedTarget s m N := by
    unfold scaleMatchedTarget
    have htail : 0 ≤ (N : ℝ) ^ 2 *
        (10 : ℝ) ^ (-s * (m : ℝ)) := by positivity
    linarith
  exact hpartial.trans (mul_le_mul_of_nonneg_left hNtarget (by positivity))

/-! ## Explicit unbounded-width family -/

/-- Exact schedule arithmetic for
`m=(t(t+1))^2`, `N=m+t`: its natural width is `t`, and the partial-range
hypothesis holds with left side exactly `m`. -/
theorem explicitSchedule_parameters (t : ℕ) :
    (((t * (t + 1)) ^ 2 + t) - (t * (t + 1)) ^ 2 = t) ∧
    (((((t * (t + 1)) ^ 2 + t) - (t * (t + 1)) ^ 2) *
        ((((t * (t + 1)) ^ 2 + t) - (t * (t + 1)) ^ 2) + 1)) ^ 2 ≤
      (t * (t + 1)) ^ 2 + t) := by
  constructor
  · omega
  · rw [Nat.add_sub_cancel_left]
    exact Nat.le_add_right ((t * (t + 1)) ^ 2) t

/-- The explicit schedule has no bounded-width restriction. -/
theorem explicitSchedule_unbounded_width :
    ∀ K : ℕ, ∃ t : ℕ, 1 ≤ t ∧
      K < ((t * (t + 1)) ^ 2 + t) - (t * (t + 1)) ^ 2 := by
  intro K
  refine ⟨K + 1, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  omega

/-- Phase-uniform application to every positive member of the explicit
unbounded-width family. -/
theorem phaseUniform_explicitSchedule
    (μ c α : ℝ) (Q0 t : ℕ) (ht : 1 ≤ t) :
    widthWeightedSquareFunction μ c Q0
        ((t * (t + 1)) ^ 2) ((t * (t + 1)) ^ 2 + t) α ≤
      (10 ^ ((t * (t + 1)) ^ 2) : ℝ) *
        (((t * (t + 1)) ^ 2 + t : ℕ) : ℝ) := by
  apply phaseUniform_partialRange
  · have hprod : 0 < t * (t + 1) := Nat.mul_pos (by omega) (by omega)
    have hpow : 0 < (t * (t + 1)) ^ 2 := pow_pos hprod 2
    omega
  · omega
  · exact (explicitSchedule_parameters t).2

/-- Fixed-`pi`, constant-one target-scale application to the same explicit
family. This remains a partial-range theorem and does not instantiate T29's
all-scale premise. -/
theorem fixedPi_explicitSchedule
    (μ c s : ℝ) (Q0 t : ℕ)
    (ht : 1 ≤ t) (hs0 : 0 < s) (hs1 : s < 1) :
    widthWeightedSquareFunction μ c Q0
        ((t * (t + 1)) ^ 2) ((t * (t + 1)) ^ 2 + t) Real.pi ≤
      (10 ^ ((t * (t + 1)) ^ 2) : ℝ) *
        scaleMatchedTarget s ((t * (t + 1)) ^ 2)
          ((t * (t + 1)) ^ 2 + t) := by
  apply fixedPi_partialRange μ c s Q0
  · have hprod : 0 < t * (t + 1) := Nat.mul_pos (by omega) (by omega)
    have hpow : 0 < (t * (t + 1)) ^ 2 := pow_pos hprod 2
    omega
  · omega
  · exact hs0
  · exact hs1
  · exact (explicitSchedule_parameters t).2

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.blockSquaredEnergy_eq_diagonal_add_offDiagonal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.widthWeightedSquareFunction_eq_diagonal_add_offDiagonal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.inclusiveFrequency_valuation_cases
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.longDifference_primitive_or_cancelling
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.widthWeightedSquareFunction_le_width_count
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.phaseUniform_partialRange
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.fixedPi_partialRange
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.explicitSchedule_unbounded_width
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T32.fixedPi_explicitSchedule

end Theory.PiDigits.LongLagBlockCollisionDecay.T32
