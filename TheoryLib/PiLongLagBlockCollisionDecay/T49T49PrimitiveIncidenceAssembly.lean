import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
import TheoryLib.PiLongLagBlockCollisionDecay.T32T32AllBlockFixedPiRange
import TheoryLib.PiLongLagBlockCollisionDecay.T34T34CancellingRepunitIncidence
import TheoryLib.PiLongLagBlockCollisionDecay.T36T36SubcriticalCancellationSaving

/-!
# T49: exact primitive incidence assembly

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module proves a conditional result for the residual sparse-Fourier
sibling A12. It does not assert the published estimate, either incidence
predicate, T29's premise at `Real.pi`, C2, C1, or the canonical collision
estimate. The unverified T47 note is not imported or used as a premise.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T49

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T34
open Theory.PiDigits.LongLagBlockCollisionDecay.T36

abbrev PrimitiveRecordPair := OrderedLongPair × OrderedLongPair

/-- T31's positive ordered-pair domain is exactly T32's record domain on a
canonical block. This bridge preserves both orientations, every arithmetic
exclusion, and the half-open endpoints. -/
theorem blockOrderedDomain_eq_blockRecordDomain
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) :
    blockOrderedDomain μ c Q0 m N B = blockRecordDomain μ c Q0 m B := by
  classical
  ext q
  rw [mem_blockRecordDomain_iff]
  simp only [blockOrderedDomain, Finset.mem_filter,
    mem_orderedLongPairDomain_iff_admissible_endpoint]
  constructor
  · rintro ⟨⟨hq, hN⟩, hstart, hfinish⟩
    exact ⟨hq, hstart, hfinish⟩
  · rintro ⟨hq, hstart, hfinish⟩
    exact ⟨⟨hq, hfinish.trans_le (canonical_finish_le hB)⟩, hstart, hfinish⟩

/-- The exact positive primitive record pairs in a canonical block. The
underlying records, strict orientation, and `(+,+,-,-)` noncancellation test
are all inherited literally from T31. -/
def primitiveRecordDomain
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Finset PrimitiveRecordPair :=
  primitiveBlockDifferenceDomain μ c Q0 m N B

/-- Decimal valuation fibers of the primitive record domain. -/
def primitiveValuationStratum
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (ell : ℕ) :
    Finset PrimitiveRecordPair :=
  (primitiveRecordDomain μ c Q0 m N B).filter fun p =>
    tenValuation (blockDifferenceValue p) = ell

/-- The exact finite set of realized primitive valuation parameters. -/
def primitiveValuationParameters
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) : Finset ℕ :=
  (primitiveRecordDomain μ c Q0 m N B).image fun p =>
    tenValuation (blockDifferenceValue p)

/-- One raw primitive record's contribution to one literal shell. -/
def primitiveShellTerm
    (m j : ℕ) (B : DyadicBlock) (p : PrimitiveRecordPair) : ℝ := by
  classical
  exact if InDyadicShell m j
      ((blockDifferenceValue p : ℝ) * Real.pi) then
    (1 : ℝ) / widthWeight B
  else 0

/-- Primitive records in one endpoint-pinned shell and one valuation stratum,
weighted only by T29's canonical width. -/
def primitiveStratumShellIncidence
    (μ c : ℝ) (Q0 m N ell j : ℕ) (B : DyadicBlock) : ℝ := by
  classical
  exact ∑ p ∈ primitiveValuationStratum μ c Q0 m N B ell,
    primitiveShellTerm m j B p

/-- Raw primitive incidence in shell `j`. Every canonical block, realized
valuation parameter, record pair, shell endpoint, and literal width remains
visible in the definition. -/
def primitiveShellIncidence
    (μ c : ℝ) (Q0 m N j : ℕ) : ℝ :=
  ((translatedCanonicalBlocks N).map fun B =>
    ∑ ell ∈ primitiveValuationParameters μ c Q0 m N B,
      primitiveStratumShellIncidence μ c Q0 m N ell j B).sum

/-- Shell zero plus the exact positive-shell weights `2^(-j)`, through the
terminal depth fixed by T34. -/
def primitiveWeightedShellIncidence
    (μ c : ℝ) (Q0 m N : ℕ) : ℝ :=
  primitiveShellIncidence μ c Q0 m N 0 +
    ∑ j ∈ Finset.Icc 1 (shellDepth m),
      ((2 : ℝ) ^ j)⁻¹ * primitiveShellIncidence μ c Q0 m N j

/-- Fixed-constant raw primitive incidence assertion. -/
def PrimitiveIncidenceAt
    (μ c : ℝ) (Q0 : ℕ) (s C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
    primitiveWeightedShellIncidence μ c Q0 m N ≤
      C * ((N : ℝ) + (N : ℝ) ^ 2 *
        (10 : ℝ) ^ (-s * (m : ℝ)))

/-- Quantifier order: one primitive constant follows `s` and precedes every
positive `m,N`. No assertion is made that this predicate holds. -/
def PrimitiveIncidence
    (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ C : ℝ, PrimitiveIncidenceAt μ c Q0 s C

/-- Membership audit for every primitive valuation stratum. The theorem type
displays both exact T32 record domains, the strict positive orientation,
T16's primitive parameters, and the decimal valuation. -/
theorem mem_primitiveValuationStratum_iff
    {μ c : ℝ} {Q0 m N ell : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N)
    {p : PrimitiveRecordPair} :
    p ∈ primitiveValuationStratum μ c Q0 m N B ell ↔
      p.1 ∈ blockRecordDomain μ c Q0 m B ∧
      p.2 ∈ blockRecordDomain μ c Q0 m B ∧
      signedDecimalFrequency p.2 < signedDecimalFrequency p.1 ∧
      Noncancelling fourTokenSign (blockDifferenceExponent p) ∧
      tenValuation (blockDifferenceValue p) = ell := by
  classical
  unfold primitiveValuationStratum primitiveRecordDomain
    primitiveBlockDifferenceDomain blockPositiveDifferenceDomain
  simp only [Finset.mem_filter, Finset.mem_product]
  rw [blockOrderedDomain_eq_blockRecordDomain hB]
  tauto

/-- Audit of shell zero, every positive shell, and the terminal endpoint used
by the primitive predicate. -/
theorem primitiveShellEndpoints_audit
    (m j : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (InDyadicShell m 0 x ↔
      0 ≤ nearestIntegerDistance x ∧
        nearestIntegerDistance x ≤ ((10 : ℝ) ^ m)⁻¹) ∧
    (j ≠ 0 → (InDyadicShell m j x ↔
      (2 : ℝ) ^ (j - 1) / (10 : ℝ) ^ m <
        nearestIntegerDistance x ∧
      nearestIntegerDistance x ≤
        min ((2 : ℝ) ^ j / (10 : ℝ) ^ m) (1 / 2))) ∧
    1 ≤ shellDepth m ∧
    10 ^ m ≤ 2 ^ (shellDepth m + 1) ∧
    2 ^ shellDepth m < 10 ^ m := by
  exact sourceExponent_shell_endpoint_audit m j hm x

theorem primitiveIncidence_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    PrimitiveIncidence μ c Q0 ↔
      ∀ s : ℝ, 0 < s → s < 1 → ∃ C : ℝ, 0 ≤ C ∧
        ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          (((canonicalDyadicPartition N).map fun B =>
            ∑ ell ∈ (primitiveBlockDifferenceDomain μ c Q0 m N B).image
                (fun p => tenValuation (blockDifferenceValue p)),
              ∑ p ∈ (primitiveBlockDifferenceDomain μ c Q0 m N B).filter
                  (fun p => tenValuation (blockDifferenceValue p) = ell),
                @ite ℝ (InDyadicShell m 0
                    ((blockDifferenceValue p : ℝ) * Real.pi))
                  (Classical.propDecidable _)
                  ((1 : ℝ) /
                    Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2))
                  0).sum +
            ∑ j ∈ Finset.Icc 1 (shellDepth m), ((2 : ℝ) ^ j)⁻¹ *
              ((canonicalDyadicPartition N).map fun B =>
                ∑ ell ∈ (primitiveBlockDifferenceDomain μ c Q0 m N B).image
                    (fun p => tenValuation (blockDifferenceValue p)),
                  ∑ p ∈ (primitiveBlockDifferenceDomain μ c Q0 m N B).filter
                      (fun p => tenValuation (blockDifferenceValue p) = ell),
                    @ite ℝ (InDyadicShell m j
                        ((blockDifferenceValue p : ℝ) * Real.pi))
                      (Classical.propDecidable _)
                      ((1 : ℝ) /
                        Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2))
                      0).sum) ≤
            C * ((N : ℝ) + (N : ℝ) ^ 2 *
              (10 : ℝ) ^ (-s * (m : ℝ))) := by
  rfl

/- The remaining declarations establish the exact primitive/cancelling
partition and the constant-tracked conditional assembly. -/

/-- Cancellation is exactly an opposite-sign equality in one of the two
record coordinates. This supplies the converse missing from T31's exported
one-way classification. -/
theorem mem_cancellingBlockDifferenceDomain_iff_cross
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : PrimitiveRecordPair} :
    p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B ↔
      p ∈ blockPositiveDifferenceDomain μ c Q0 m N B ∧
        (orderedFirst p.1 = orderedFirst p.2 ∨
          orderedSecond p.1 = orderedSecond p.2) := by
  classical
  constructor
  · intro hp
    exact ⟨cancellingBlockDifferenceDomain_subset hp,
      cancellingBlockDifference_cross_equality hp⟩
  · rintro ⟨hp, hcross⟩
    rw [cancellingBlockDifferenceDomain, Finset.mem_filter]
    refine ⟨hp, ?_⟩
    intro hnon
    rcases hcross with hfirst | hsecond
    · have hsign := hnon (0 : Fin 4) (3 : Fin 4) (by
        simpa [blockDifferenceExponent] using hfirst)
      simp [fourTokenSign] at hsign
    · have hsign := hnon (1 : Fin 4) (2 : Fin 4) (by
        simpa [blockDifferenceExponent] using hsecond.symm)
      simp [fourTokenSign] at hsign

theorem second_lt_of_positiveDifference_first_eq
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : PrimitiveRecordPair}
    (hp : p ∈ blockPositiveDifferenceDomain μ c Q0 m N B)
    (hfirst : orderedFirst p.1 = orderedFirst p.2) :
    orderedSecond p.1 < orderedSecond p.2 := by
  have hlt := (Finset.mem_filter.mp hp).2
  rw [signedDecimalFrequency_eq_orderedPhaseFrequency,
    signedDecimalFrequency_eq_orderedPhaseFrequency] at hlt
  unfold orderedPhaseFrequency at hlt
  rw [hfirst] at hlt
  have hpows : (10 : ℤ) ^ orderedSecond p.1 <
      (10 : ℤ) ^ orderedSecond p.2 := by omega
  have hpowsNat : 10 ^ orderedSecond p.1 < 10 ^ orderedSecond p.2 := by
    exact_mod_cast hpows
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpowsNat

theorem first_lt_of_positiveDifference_second_eq
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : PrimitiveRecordPair}
    (hp : p ∈ blockPositiveDifferenceDomain μ c Q0 m N B)
    (hsecond : orderedSecond p.1 = orderedSecond p.2) :
    orderedFirst p.2 < orderedFirst p.1 := by
  have hlt := (Finset.mem_filter.mp hp).2
  rw [signedDecimalFrequency_eq_orderedPhaseFrequency,
    signedDecimalFrequency_eq_orderedPhaseFrequency] at hlt
  unfold orderedPhaseFrequency at hlt
  rw [hsecond] at hlt
  have hpows : (10 : ℤ) ^ orderedFirst p.2 <
      (10 : ℤ) ^ orderedFirst p.1 := by omega
  have hpowsNat : 10 ^ orderedFirst p.2 < 10 ^ orderedFirst p.1 := by
    exact_mod_cast hpows
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpowsNat

@[simp] theorem recordOfStartEndpoint_true (r n : ℕ) :
    recordOfStartEndpoint true n (n + r) = (true, ⟨r, n⟩) := by
  simp [recordOfStartEndpoint]

@[simp] theorem recordOfStartEndpoint_false (r n : ℕ) :
    recordOfStartEndpoint false n (n + r) = (false, ⟨r, n⟩) := by
  simp [recordOfStartEndpoint]

theorem recordOfStartEndpoint_true_ordered
    (q : OrderedLongPair) (hq : q.1 = true) :
    recordOfStartEndpoint true (orderedSecond q) (orderedFirst q) = q := by
  rcases q with ⟨b, r, n⟩
  simp only at hq
  subst b
  simp [orderedFirst, orderedSecond]

theorem recordOfStartEndpoint_false_ordered
    (q : OrderedLongPair) (hq : q.1 = false) :
    recordOfStartEndpoint false (orderedFirst q) (orderedSecond q) = q := by
  rcases q with ⟨b, r, n⟩
  simp only at hq
  subst b
  simp [orderedFirst, orderedSecond]

/-- Exact six-row exhaustiveness for one canonical block. T31 stores the
positive-frequency record first; T34 stores the lower-frequency record first,
so the literal row witness is `reverseRecordPair p`. -/
theorem mem_cancellingBlockDifferenceDomain_iff_six_rows
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N)
    {p : PrimitiveRecordPair} :
    p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B ↔
      ∃ v rho : ℕ, (v, rho) ∈ repunitParameterDomain N ∧
        ∃ z ∈ Finset.range N, ∃ row : CancellingRow,
          reverseRecordPair p ∈
            cancellingRowDomain μ c Q0 m B row v rho z := by
  classical
  constructor
  · intro hp
    have hpPos := cancellingBlockDifferenceDomain_subset hp
    have hrecords := cancellingBlockDifference_records_mem hp
    have hplusQ := (Finset.mem_filter.mp hrecords.1).1
    have hminusQ := (Finset.mem_filter.mp hrecords.2).1
    have hplusBlock : p.1 ∈ blockRecordDomain μ c Q0 m B := by
      rw [← blockOrderedDomain_eq_blockRecordDomain hB]
      exact hrecords.1
    have hminusBlock : p.2 ∈ blockRecordDomain μ c Q0 m B := by
      rw [← blockOrderedDomain_eq_blockRecordDomain hB]
      exact hrecords.2
    have hplusCoords := ordered_coordinates_lt hplusQ
    have hminusCoords := ordered_coordinates_lt hminusQ
    rcases cancellingBlockDifference_cross_equality hp with hfirst | hsecond
    · have hslt := second_lt_of_positiveDifference_first_eq hpPos hfirst
      let v := orderedSecond p.1
      let rho := orderedSecond p.2 - orderedSecond p.1
      let z := orderedFirst p.1
      have hvr : (v, rho) ∈ repunitParameterDomain N := by
        rw [mem_repunitParameterDomain_iff]
        dsimp [v, rho]
        omega
      have hz : z ∈ Finset.range N := by
        rw [Finset.mem_range]
        exact hplusCoords.1
      refine ⟨v, rho, hvr, z, hz, ?_⟩
      have hvrho : v + rho = orderedSecond p.2 := by
        dsimp [v, rho]
        omega
      have hzminus : z = orderedFirst p.2 := by
        exact hfirst
      cases hplus : p.1.1 <;> cases hminus : p.2.1
      · refine ⟨.negativeSameStart, ?_⟩
        rw [mem_cancellingRowDomain_iff]
        refine ⟨?_, (mem_repunitParameterDomain_iff.mp hvr).2.2.1,
          hminusBlock, hplusBlock⟩
        simp only [reverseRecordPair, cancellingRowPair]
        apply Prod.ext
        · rw [hzminus, hvrho,
            recordOfStartEndpoint_false_ordered p.2 hminus]
        · dsimp [v, z]
          rw [recordOfStartEndpoint_false_ordered p.1 hplus]
      · have hplusFreq : (0 : ℤ) < positiveDecimalFrequency p.2.2 := by
          exact_mod_cast Nat.pos_of_ne_zero
            (positiveDecimalFrequency_ne_zero
              (mem_blockRecordDomain_iff.mp hminusBlock).1.1)
        have hminusFreq : (0 : ℤ) < positiveDecimalFrequency p.1.2 := by
          exact_mod_cast Nat.pos_of_ne_zero
            (positiveDecimalFrequency_ne_zero
              (mem_blockRecordDomain_iff.mp hplusBlock).1.1)
        have hord := (Finset.mem_filter.mp hpPos).2
        simp only [signedDecimalFrequency, hplus, hminus,
          Bool.false_eq_true, ↓reduceIte] at hord
        omega
      · refine ⟨.mixedFirstEndpoint, ?_⟩
        rw [mem_cancellingRowDomain_iff]
        refine ⟨?_, (mem_repunitParameterDomain_iff.mp hvr).2.2.1,
          hminusBlock, hplusBlock⟩
        simp only [reverseRecordPair, cancellingRowPair]
        apply Prod.ext
        · rw [hzminus, hvrho,
            recordOfStartEndpoint_false_ordered p.2 hminus]
        · dsimp [v, z]
          rw [recordOfStartEndpoint_true_ordered p.1 hplus]
      · refine ⟨.positiveSameEndpoint, ?_⟩
        rw [mem_cancellingRowDomain_iff]
        refine ⟨?_, (mem_repunitParameterDomain_iff.mp hvr).2.2.1,
          hminusBlock, hplusBlock⟩
        simp only [reverseRecordPair, cancellingRowPair]
        apply Prod.ext
        · rw [hzminus, hvrho,
            recordOfStartEndpoint_true_ordered p.2 hminus]
        · dsimp [v, z]
          rw [recordOfStartEndpoint_true_ordered p.1 hplus]
    · have hflt := first_lt_of_positiveDifference_second_eq hpPos hsecond
      let v := orderedFirst p.2
      let rho := orderedFirst p.1 - orderedFirst p.2
      let z := orderedSecond p.1
      have hvr : (v, rho) ∈ repunitParameterDomain N := by
        rw [mem_repunitParameterDomain_iff]
        dsimp [v, rho]
        omega
      have hz : z ∈ Finset.range N := by
        rw [Finset.mem_range]
        exact hplusCoords.2
      refine ⟨v, rho, hvr, z, hz, ?_⟩
      have hvrho : v + rho = orderedFirst p.1 := by
        dsimp [v, rho]
        omega
      have hzminus : z = orderedSecond p.2 := hsecond
      cases hplus : p.1.1 <;> cases hminus : p.2.1
      · refine ⟨.negativeSameEndpoint, ?_⟩
        rw [mem_cancellingRowDomain_iff]
        refine ⟨?_, (mem_repunitParameterDomain_iff.mp hvr).2.2.1,
          hminusBlock, hplusBlock⟩
        simp only [reverseRecordPair, cancellingRowPair]
        apply Prod.ext
        · dsimp [v, z]
          rw [hsecond, recordOfStartEndpoint_false_ordered p.2 hminus]
        · rw [hvrho]
          dsimp [z]
          rw [recordOfStartEndpoint_false_ordered p.1 hplus]
      · have hplusFreq : (0 : ℤ) < positiveDecimalFrequency p.2.2 := by
          exact_mod_cast Nat.pos_of_ne_zero
            (positiveDecimalFrequency_ne_zero
              (mem_blockRecordDomain_iff.mp hminusBlock).1.1)
        have hminusFreq : (0 : ℤ) < positiveDecimalFrequency p.1.2 := by
          exact_mod_cast Nat.pos_of_ne_zero
            (positiveDecimalFrequency_ne_zero
              (mem_blockRecordDomain_iff.mp hplusBlock).1.1)
        have hord := (Finset.mem_filter.mp hpPos).2
        simp only [signedDecimalFrequency, hplus, hminus,
          Bool.false_eq_true, ↓reduceIte] at hord
        omega
      · refine ⟨.mixedSecondEndpoint, ?_⟩
        rw [mem_cancellingRowDomain_iff]
        refine ⟨?_, (mem_repunitParameterDomain_iff.mp hvr).2.2.1,
          hminusBlock, hplusBlock⟩
        simp only [reverseRecordPair, cancellingRowPair]
        apply Prod.ext
        · dsimp [v, z]
          rw [hsecond, recordOfStartEndpoint_false_ordered p.2 hminus]
        · rw [hvrho]
          dsimp [z]
          rw [recordOfStartEndpoint_true_ordered p.1 hplus]
      · refine ⟨.positiveSameStart, ?_⟩
        rw [mem_cancellingRowDomain_iff]
        refine ⟨?_, (mem_repunitParameterDomain_iff.mp hvr).2.2.1,
          hminusBlock, hplusBlock⟩
        simp only [reverseRecordPair, cancellingRowPair]
        apply Prod.ext
        · dsimp [v, z]
          rw [hsecond, recordOfStartEndpoint_true_ordered p.2 hminus]
        · rw [hvrho]
          dsimp [z]
          rw [recordOfStartEndpoint_true_ordered p.1 hplus]
  · rintro ⟨v, rho, hvr, z, hz, row, hrow⟩
    have hmem := mem_cancellingRowDomain_iff.mp hrow
    have hplusBlock : p.1 ∈ blockRecordDomain μ c Q0 m B := hmem.2.2.2
    have hminusBlock : p.2 ∈ blockRecordDomain μ c Q0 m B := hmem.2.2.1
    have hplusOrdered : p.1 ∈ blockOrderedDomain μ c Q0 m N B := by
      rw [blockOrderedDomain_eq_blockRecordDomain hB]
      exact hplusBlock
    have hminusOrdered : p.2 ∈ blockOrderedDomain μ c Q0 m N B := by
      rw [blockOrderedDomain_eq_blockRecordDomain hB]
      exact hminusBlock
    have hdiff := cancellingRow_difference hrow
    have hvalue : 0 < cancellingValue v rho := by
      unfold cancellingValue reducedRepunitFactor
      apply Nat.mul_pos (by positivity)
      have : 1 < 10 ^ rho := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    have hlt : signedDecimalFrequency p.2 < signedDecimalFrequency p.1 := by
      have hdiff' : signedDecimalFrequency p.1 - signedDecimalFrequency p.2 =
          (cancellingValue v rho : ℤ) := by
        simpa [reverseRecordPair] using hdiff
      have hvalue' : (0 : ℤ) < cancellingValue v rho := by exact_mod_cast hvalue
      omega
    have hpPos : p ∈ blockPositiveDifferenceDomain μ c Q0 m N B := by
      rw [blockPositiveDifferenceDomain, Finset.mem_filter,
        Finset.mem_product]
      exact ⟨⟨hplusOrdered, hminusOrdered⟩, hlt⟩
    apply mem_cancellingBlockDifferenceDomain_iff_cross.mpr
    refine ⟨hpPos, ?_⟩
    have pinv : p = reverseRecordPair (reverseRecordPair p) := by
      rcases p with ⟨q, r⟩
      rfl
    rw [pinv, hmem.1]
    have hrow0 : (cancellingRowPair row v rho z).1 ∈
        blockRecordDomain μ c Q0 m B := by
      rw [← hmem.1]
      exact hmem.2.2.1
    have hrow1 : (cancellingRowPair row v rho z).2 ∈
        blockRecordDomain μ c Q0 m B := by
      rw [← hmem.1]
      exact hmem.2.2.2
    have hlag0 := (mem_blockRecordDomain_iff.mp hrow0).1.1
    have hlag1 := (mem_blockRecordDomain_iff.mp hrow1).1.1
    cases row <;>
      simp only [reverseRecordPair, cancellingRowPair, recordOfStartEndpoint,
        orderedFirst, orderedSecond, Bool.false_eq_true, ↓reduceIte] at hlag0 hlag1 ⊢
    case positiveSameEndpoint => omega
    case positiveSameStart => exact Or.inr trivial
    case negativeSameEndpoint => omega
    case negativeSameStart => exact Or.inl trivial
    case mixedFirstEndpoint =>
      left
      exact Nat.add_sub_of_le ((Nat.sub_pos_iff_lt).mp hlag1).le
    case mixedSecondEndpoint =>
      right
      exact (Nat.add_sub_of_le ((Nat.sub_pos_iff_lt).mp hlag0).le).symm

/-- The same primitive incidence before exchanging valuation and shell sums. -/
def directPrimitiveWeightedShellIncidence
    (μ c : ℝ) (Q0 m N : ℕ) : ℝ :=
  ((translatedCanonicalBlocks N).map fun B =>
    ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
      (1 : ℝ) / widthWeight B *
        shellWeight m ((blockDifferenceValue p : ℝ) * Real.pi)).sum

theorem primitiveShellIncidence_eq_direct
    (μ c : ℝ) (Q0 m N j : ℕ) :
    primitiveShellIncidence μ c Q0 m N j =
      ((translatedCanonicalBlocks N).map fun B =>
        ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
          primitiveShellTerm m j B p).sum := by
  classical
  unfold primitiveShellIncidence primitiveStratumShellIncidence
    primitiveValuationParameters primitiveValuationStratum
  apply congrArg List.sum
  apply List.map_congr_left
  intro B hB
  exact Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image_of_mem
      (fun q => tenValuation (blockDifferenceValue q)) hp)
    (fun p => primitiveShellTerm m j B p)

theorem primitiveWeightedShellIncidence_eq_direct
    (μ c : ℝ) (Q0 m N : ℕ) :
    primitiveWeightedShellIncidence μ c Q0 m N =
      directPrimitiveWeightedShellIncidence μ c Q0 m N := by
  classical
  rw [primitiveWeightedShellIncidence]
  simp_rw [primitiveShellIncidence_eq_direct]
  unfold directPrimitiveWeightedShellIncidence shellWeight primitiveShellTerm
  simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_comm
    (s := primitiveRecordDomain μ c Q0 m N _)
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
    intro p hp
    by_cases hs : InDyadicShell m j
        ((blockDifferenceValue p : ℝ) * Real.pi)
    · simp [hs]
      ring
    · simp [hs]

/-- The signed primitive part of the centered width-weighted square function.
The factor two is exactly T31's two ordered off-diagonal orientations. -/
def primitiveSectorContribution
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  2 * ((translatedCanonicalBlocks N).map fun B =>
    ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
      inclusiveRealKernel m (blockDifferenceValue p) α / widthWeight B).sum

def primitiveSectorEnvelope
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  2 * ((translatedCanonicalBlocks N).map fun B =>
    ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
      (1 : ℝ) / widthWeight B *
        |inclusiveRealKernel m (blockDifferenceValue p) α|).sum

theorem primitiveSector_abs_le_envelope
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    |primitiveSectorContribution μ c Q0 m N α| ≤
      primitiveSectorEnvelope μ c Q0 m N α := by
  unfold primitiveSectorContribution primitiveSectorEnvelope
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hsum : ∀ blocks : List DyadicBlock,
      (∀ B ∈ blocks, B ∈ translatedCanonicalBlocks N) →
      |(blocks.map fun B =>
          ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
            inclusiveRealKernel m (blockDifferenceValue p) α /
              widthWeight B).sum| ≤
        (blocks.map fun B =>
          ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
            (1 : ℝ) / widthWeight B *
              |inclusiveRealKernel m (blockDifferenceValue p) α|).sum := by
    intro blocks hsubset
    induction blocks with
    | nil => simp
    | cons B blocks ih =>
        simp only [List.map_cons, List.sum_cons]
        refine (abs_add_le _ _).trans ?_
        apply add_le_add
        · calc
            |∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
                inclusiveRealKernel m (blockDifferenceValue p) α /
                  widthWeight B| ≤
                ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
                  |inclusiveRealKernel m (blockDifferenceValue p) α /
                    widthWeight B| := by
              simpa using Finset.abs_sum_le_sum_abs
                (fun p => inclusiveRealKernel m (blockDifferenceValue p) α /
                  widthWeight B)
                (primitiveRecordDomain μ c Q0 m N B)
            _ = ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
                  (1 : ℝ) / widthWeight B *
                    |inclusiveRealKernel m (blockDifferenceValue p) α| := by
              apply Finset.sum_congr rfl
              intro p hp
              have hw := canonical_widthWeight_pos (hsubset B (by simp))
              rw [abs_div, abs_of_pos hw]
              ring
        · apply ih
          intro C hC
          exact hsubset C (by simp [hC])
  exact hsum _ (fun _ h => h)

theorem primitiveSectorEnvelope_le_incidence
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) :
    primitiveSectorEnvelope μ c Q0 m N Real.pi ≤
      2 * (10 : ℝ) ^ m *
        directPrimitiveWeightedShellIncidence μ c Q0 m N := by
  unfold primitiveSectorEnvelope directPrimitiveWeightedShellIncidence
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ((translatedCanonicalBlocks N).map fun B =>
      ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
        (1 : ℝ) / widthWeight B *
          |inclusiveRealKernel m (blockDifferenceValue p) Real.pi|).sum ≤
        ((translatedCanonicalBlocks N).map fun B =>
          (10 : ℝ) ^ m *
            ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
              (1 : ℝ) / widthWeight B *
                shellWeight m
                  ((blockDifferenceValue p : ℝ) * Real.pi)).sum := by
      apply list_sum_map_le_sum_map
      intro B hB
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hw := canonical_widthWeight_pos hB
      have hcoeff : 0 ≤ (1 : ℝ) / widthWeight B := by positivity
      have hkernel := abs_inclusiveRealKernel_le_height_mul_shellWeight
        m (blockDifferenceValue p) Real.pi hm
      calc
        (1 : ℝ) / widthWeight B *
              |inclusiveRealKernel m (blockDifferenceValue p) Real.pi| ≤
            (1 : ℝ) / widthWeight B *
              ((10 : ℝ) ^ m * shellWeight m
                ((blockDifferenceValue p : ℝ) * Real.pi)) :=
          mul_le_mul_of_nonneg_left hkernel hcoeff
        _ = (10 : ℝ) ^ m *
            ((1 : ℝ) / widthWeight B *
              shellWeight m
                ((blockDifferenceValue p : ℝ) * Real.pi)) := by ring
    _ = (10 : ℝ) ^ m *
        ((translatedCanonicalBlocks N).map fun B =>
          ∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
            (1 : ℝ) / widthWeight B *
              shellWeight m
                ((blockDifferenceValue p : ℝ) * Real.pi)).sum := by
      rw [List.sum_map_mul_left]

theorem primitiveSector_abs_le_weightedShellIncidence
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) :
    |primitiveSectorContribution μ c Q0 m N Real.pi| ≤
      2 * (10 : ℝ) ^ m *
        primitiveWeightedShellIncidence μ c Q0 m N := by
  calc
    _ ≤ primitiveSectorEnvelope μ c Q0 m N Real.pi :=
      primitiveSector_abs_le_envelope μ c Q0 m N Real.pi
    _ ≤ 2 * (10 : ℝ) ^ m *
        directPrimitiveWeightedShellIncidence μ c Q0 m N :=
      primitiveSectorEnvelope_le_incidence μ c Q0 m N hm
    _ = _ := by rw [primitiveWeightedShellIncidence_eq_direct]

/-! ## Exact finite cancelling witness regrouping -/

abbrev CancellingWitness := ((ℕ × ℕ) × ℕ) × CancellingRow

def cancellingWitnessPair (w : CancellingWitness) : RecordPair :=
  cancellingRowPair w.2 w.1.1.1 w.1.1.2 w.1.2

def cancellingWitnessValue (w : CancellingWitness) : ℕ :=
  cancellingValue w.1.1.1 w.1.1.2

def cancellingWitnessDomain
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Finset CancellingWitness :=
  (((repunitParameterDomain N ×ˢ Finset.range N) ×ˢ
      (Finset.univ : Finset CancellingRow))).filter fun w =>
    cancellingWitnessPair w ∈ cancellingRowDomain μ c Q0 m B
      w.2 w.1.1.1 w.1.1.2 w.1.2

def witnessToPositivePair (w : CancellingWitness) : PrimitiveRecordPair :=
  reverseRecordPair (cancellingWitnessPair w)

theorem cancellingWitnessPair_injectiveOn
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Set.InjOn witnessToPositivePair
      (cancellingWitnessDomain μ c Q0 m N B : Set CancellingWitness) := by
  intro w hw w' hw' heq
  have hwmem := (Finset.mem_filter.mp hw).2
  have hw'mem := (Finset.mem_filter.mp hw').2
  have hpairs : cancellingWitnessPair w = cancellingWitnessPair w' := by
    simpa [witnessToPositivePair, reverseRecordPair] using
      congrArg reverseRecordPair heq
  have hu := cancellingRow_witness_unique hwmem hw'mem hpairs
  rcases w with ⟨⟨⟨v, rho⟩, z⟩, row⟩
  rcases w' with ⟨⟨⟨v', rho'⟩, z'⟩, row'⟩
  rcases hu with ⟨rfl, rfl, rfl, rfl⟩
  rfl

theorem cancellingWitness_image_eq_domain
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) :
    (cancellingWitnessDomain μ c Q0 m N B).image witnessToPositivePair =
      cancellingBlockDifferenceDomain μ c Q0 m N B := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    have hbase := (Finset.mem_filter.mp hw).1
    have hactive := (Finset.mem_filter.mp hw).2
    have hprod := Finset.mem_product.mp hbase
    have hvrz := Finset.mem_product.mp hprod.1
    apply (mem_cancellingBlockDifferenceDomain_iff_six_rows hB).mpr
    exact ⟨w.1.1.1, w.1.1.2, hvrz.1, w.1.2, hvrz.2,
      w.2, by simpa [witnessToPositivePair] using hactive⟩
  · intro hp
    obtain ⟨v, rho, hvr, z, hz, row, hrow⟩ :=
      (mem_cancellingBlockDifferenceDomain_iff_six_rows hB).mp hp
    let w : CancellingWitness := (((v, rho), z), row)
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, ?_⟩
    · rw [cancellingWitnessDomain, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hvr, hz⟩, Finset.mem_univ _⟩, ?_⟩
      have hactive : cancellingRowPair row v rho z ∈
          cancellingRowDomain μ c Q0 m B row v rho z := by
        rw [← (mem_cancellingRowDomain_iff.mp hrow).1]
        exact hrow
      simpa [w, cancellingWitnessPair] using hactive
    · have heq := (mem_cancellingRowDomain_iff.mp hrow).1
      simpa [w, witnessToPositivePair, cancellingWitnessPair] using
        (congrArg reverseRecordPair heq).symm

theorem cancellingWitness_sum_eq
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N)
    (f : PrimitiveRecordPair → ℝ) :
    (∑ w ∈ cancellingWitnessDomain μ c Q0 m N B,
      f (witnessToPositivePair w)) =
      ∑ p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B, f p := by
  classical
  rw [← cancellingWitness_image_eq_domain hB]
  symm
  exact Finset.sum_image
    (fun a ha b hb hab => cancellingWitnessPair_injectiveOn
      μ c Q0 m N B ha hb hab)

theorem blockDifferenceValue_witness
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N)
    {w : CancellingWitness}
    (hw : w ∈ cancellingWitnessDomain μ c Q0 m N B) :
    blockDifferenceValue (witnessToPositivePair w) =
      cancellingWitnessValue w := by
  have hp : witnessToPositivePair w ∈
      cancellingBlockDifferenceDomain μ c Q0 m N B := by
    rw [← cancellingWitness_image_eq_domain hB]
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hcast := blockPositiveDifferenceValue_cast
    (cancellingBlockDifferenceDomain_subset hp)
  have hrow := (Finset.mem_filter.mp hw).2
  have hdiff := cancellingRow_difference hrow
  have heq : (blockDifferenceValue (witnessToPositivePair w) : ℤ) =
      (cancellingWitnessValue w : ℤ) := by
    rw [hcast]
    simpa [witnessToPositivePair, reverseRecordPair,
      cancellingWitnessValue] using hdiff
  exact_mod_cast heq

theorem cancellingRowDomain_card_indicator
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock)
    (row : CancellingRow) (v rho z : ℕ) :
    ((cancellingRowDomain μ c Q0 m B row v rho z).card : ℝ) =
      if cancellingRowPair row v rho z ∈
          cancellingRowDomain μ c Q0 m B row v rho z then 1 else 0 := by
  classical
  by_cases hactive : cancellingRowPair row v rho z ∈
      cancellingRowDomain μ c Q0 m B row v rho z
  · rw [if_pos hactive]
    have heq : cancellingRowDomain μ c Q0 m B row v rho z =
        {cancellingRowPair row v rho z} := by
      apply Finset.Subset.antisymm
      · intro qr hqr
        exact Finset.mem_singleton.mpr
          (mem_cancellingRowDomain_iff.mp hqr).1
      · intro qr hqr
        rw [Finset.mem_singleton] at hqr
        simpa [hqr] using hactive
    rw [heq]
    simp
  · rw [if_neg hactive]
    norm_num
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨qr, hqr⟩
    apply hactive
    have heq := (mem_cancellingRowDomain_iff.mp hqr).1
    simpa [heq] using hqr

theorem cancellingWitness_sum_eq_blockMultiplicity
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (f : ℕ → ℝ) :
    (∑ w ∈ cancellingWitnessDomain μ c Q0 m N B,
      f (cancellingWitnessValue w)) =
      ∑ vr ∈ repunitParameterDomain N,
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) *
          f (cancellingValue vr.1 vr.2) := by
  classical
  unfold cancellingWitnessDomain cancellingWitnessValue
  rw [Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_product]
  unfold blockRepunitMultiplicity
  push_cast
  apply Finset.sum_congr rfl
  intro vr hvr
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro row hrow
  rw [cancellingRowDomain_card_indicator]
  simp only [cancellingWitnessPair]
  by_cases hactive : cancellingRowPair row vr.1 vr.2 z ∈
      cancellingRowDomain μ c Q0 m B row vr.1 vr.2 z
  · simp [hactive]
  · simp [hactive]

theorem blockCancellingPositiveSum_eq_rows
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) (α : ℝ) :
    (∑ p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B,
      inclusiveRealKernel m (blockDifferenceValue p) α) =
      ∑ vr ∈ repunitParameterDomain N,
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) *
          inclusiveRealKernel m (cancellingValue vr.1 vr.2) α := by
  calc
    (∑ p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B,
        inclusiveRealKernel m (blockDifferenceValue p) α) =
        ∑ w ∈ cancellingWitnessDomain μ c Q0 m N B,
          inclusiveRealKernel m
            (blockDifferenceValue (witnessToPositivePair w)) α :=
      (cancellingWitness_sum_eq hB
        (fun p => inclusiveRealKernel m (blockDifferenceValue p) α)).symm
    _ = ∑ w ∈ cancellingWitnessDomain μ c Q0 m N B,
          inclusiveRealKernel m (cancellingWitnessValue w) α := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [blockDifferenceValue_witness hB hw]
    _ = ∑ vr ∈ repunitParameterDomain N,
        (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℝ) *
          inclusiveRealKernel m (cancellingValue vr.1 vr.2) α :=
      cancellingWitness_sum_eq_blockMultiplicity μ c Q0 m N B
        (fun d => inclusiveRealKernel m d α)

def cancellingPositiveSectorContribution
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  2 * ((translatedCanonicalBlocks N).map fun B =>
    ∑ p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B,
      inclusiveRealKernel m (blockDifferenceValue p) α / widthWeight B).sum

theorem cancellingSectorContribution_eq_positive
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    cancellingSectorContribution μ c Q0 m N α =
      (cancellingPositiveSectorContribution μ c Q0 m N α : ℂ) := by
  rw [cancellingSectorContribution_eq_regrouped]
  unfold regroupedCancellingSector cancellingPositiveSectorContribution
  push_cast
  apply congrArg ((2 : ℂ) * ·)
  have hsum : ∀ blocks : List DyadicBlock,
      (∀ B ∈ blocks, B ∈ translatedCanonicalBlocks N) →
      (blocks.map fun B =>
        (∑ vr ∈ repunitParameterDomain N,
          (blockRepunitMultiplicity μ c Q0 m N B vr.1 vr.2 : ℂ) *
            (inclusiveRealKernel m (cancellingValue vr.1 vr.2) α : ℂ)) /
          (widthWeight B : ℂ)).sum =
        ((blocks.map fun B =>
          ∑ p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B,
            inclusiveRealKernel m (blockDifferenceValue p) α /
              widthWeight B).sum : ℂ) := by
    intro blocks hsubset
    induction blocks with
    | nil => simp
    | cons B blocks ih =>
        simp only [List.map_cons, List.sum_cons]
        push_cast
        apply congrArg₂ (· + ·)
        · rw [← Finset.sum_div]
          exact_mod_cast
            congrArg (fun x : ℝ => x / widthWeight B)
              (blockCancellingPositiveSum_eq_rows
                (hsubset B (by simp)) α).symm
        · exact ih (fun C hC => hsubset C (by simp [hC]))
  exact hsum _ (fun _ h => h)

/-! ## Exact assembly with T29's square function -/

theorem blockSignedPairSum_eq_two_re
    (h d : ℕ) (α : ℝ) :
    blockSignedPairSum h d α =
      (2 : ℂ) *
        (Theory.PiDigits.T27.phase ((h : ℤ) * (d : ℤ)) α).re := by
  let z := Theory.PiDigits.T27.phase ((h : ℤ) * (d : ℤ)) α
  have hpos : blockCenteredAtom true h d α = z := by
    unfold blockCenteredAtom z Theory.PiDigits.T27.phase
    simp only [if_pos]
    congr 1
    push_cast
    ring
  have hneg : blockCenteredAtom false h d α = conj z := by
    unfold blockCenteredAtom z Theory.PiDigits.T27.phase
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      map_intCast]
    push_cast
    ring
  unfold blockSignedPairSum
  rw [Fintype.sum_bool, hneg, hpos]
  simpa [add_comm] using (Complex.add_conj z)

theorem sum_blockSignedPairSum_eq_realKernel
    (m d : ℕ) (α : ℝ) :
    (∑ h ∈ inclusiveFrequencies m, blockSignedPairSum h d α) =
      (2 : ℂ) * (inclusiveRealKernel m d α : ℂ) := by
  simp_rw [blockSignedPairSum_eq_two_re]
  rw [← Finset.mul_sum]
  unfold inclusiveRealKernel inclusiveDirichletKernel
  rw [Complex.re_sum]
  push_cast
  rfl

theorem blockCenteredEnergy_eq_positiveDifferences
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) :
    blockCenteredEnergy μ c Q0 m N B α =
      2 * ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
        inclusiveRealKernel m (blockDifferenceValue p) α := by
  have hcomplex : ((blockCenteredEnergy μ c Q0 m N B α : ℝ) : ℂ) =
      ((2 * ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
        inclusiveRealKernel m (blockDifferenceValue p) α : ℝ) : ℂ) := by
    rw [blockCenteredEnergy_eq_polynomial,
      blockCenteredPolynomial_eq_pairSums]
    rw [Finset.sum_comm]
    simp_rw [sum_blockSignedPairSum_eq_realKernel]
    push_cast
    rw [Finset.mul_sum]
  exact_mod_cast hcomplex

theorem blockCenteredEnergy_eq_primitive_add_cancelling
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) :
    blockCenteredEnergy μ c Q0 m N B α =
      2 * (∑ p ∈ primitiveRecordDomain μ c Q0 m N B,
          inclusiveRealKernel m (blockDifferenceValue p) α) +
      2 * (∑ p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B,
          inclusiveRealKernel m (blockDifferenceValue p) α) := by
  rw [blockCenteredEnergy_eq_positiveDifferences]
  rw [blockPositiveDifferenceDomain_partition]
  rw [Finset.sum_union
    (primitiveBlockDifferenceDomain_disjoint_cancelling μ c Q0 m N B)]
  unfold primitiveRecordDomain
  ring

theorem centeredWidthWeightedSquareFunction_eq_sectors
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    centeredWidthWeightedSquareFunction μ c Q0 m N α =
      primitiveSectorContribution μ c Q0 m N α +
        cancellingPositiveSectorContribution μ c Q0 m N α := by
  classical
  rw [centeredWidthWeightedSquareFunction_eq_sum]
  rw [List.sum_toFinset
    (fun B => blockCenteredEnergy μ c Q0 m N B α / widthWeight B)
    (translatedCanonicalBlocks_nodup N)]
  unfold primitiveSectorContribution cancellingPositiveSectorContribution
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro B hB
  rw [blockCenteredEnergy_eq_primitive_add_cancelling]
  rw [add_div]
  rw [← Finset.sum_div, ← Finset.sum_div]
  ring

/-- Fixed-scale assembly with every numerical constant displayed. The
diagonal contributes `3`, the primitive orientation pair contributes
`2*Cprim`, and T36 contributes
`2*(Csuper + finiteOnsetConstant Qstar + 12)`. -/
theorem widthWeightedSquareFunction_le_of_three_obstructions
    {Q0 Qstar m N : ℕ} {s Csuper Cprim : ℝ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hSuper : ARI_superAt Q0 Qstar s Csuper)
    (hPrimitive : PrimitiveIncidenceAt 8 1 Q0 s Cprim)
    (hm : 1 ≤ m) (hN : 1 ≤ N) :
    widthWeightedSquareFunction 8 1 Q0 m N Real.pi ≤
      (3 + 2 * Cprim +
          2 * (Csuper + finiteOnsetConstant Qstar + 12)) *
        (10 : ℝ) ^ m *
          ((N : ℝ) + (N : ℝ) ^ 2 *
            (10 : ℝ) ^ (-s * (m : ℝ))) := by
  let H : ℝ := (10 : ℝ) ^ m
  let T : ℝ := scaleMatchedTarget s m N
  let Ccancel : ℝ := Csuper + finiteOnsetConstant Qstar + 12
  let P : ℝ := primitiveSectorContribution 8 1 Q0 m N Real.pi
  let C : ℝ := cancellingPositiveSectorContribution 8 1 Q0 m N Real.pi
  let M : ℝ := (decimalFrequency m : ℝ) *
    ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((blockOrderedDomain 8 1 Q0 m N B).card : ℝ) / widthWeight B
  have hH : 0 ≤ H := by positivity
  have hT : 0 < T := scaleMatchedTarget_pos hN
  have hPrimInc := hPrimitive.2 m N hm hN
  have hPrimEnvelope := primitiveSector_abs_le_weightedShellIncidence
    8 1 Q0 m N hm
  have hP : P ≤ 2 * Cprim * H * T := by
    calc
      P ≤ |P| := le_abs_self P
      _ ≤ 2 * H * primitiveWeightedShellIncidence 8 1 Q0 m N := by
        simpa [P, H] using hPrimEnvelope
      _ ≤ 2 * H * (Cprim * T) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [T, scaleMatchedTarget] using hPrimInc
      _ = 2 * Cprim * H * T := by ring
  have hCancelARI : ARI_cancelAt Q0 s Ccancel := by
    dsimp [Ccancel]
    exact ARI_superAt_implies_ARI_cancelAt hPublished hSuper
  have hCancelNorm := cancellingSector_bound_of_ARI_cancelAt
    hCancelARI hm hN
  have hCabs : |C| ≤ 2 * Ccancel * H * T := by
    rw [cancellingSectorContribution_eq_positive] at hCancelNorm
    simpa [C, Ccancel, H, T, scaleMatchedTarget, Complex.norm_real,
      Real.norm_eq_abs] using hCancelNorm
  have hC : C ≤ 2 * Ccancel * H * T :=
    (le_abs_self C).trans hCabs
  have hmean := blockMeanWeight_sum_le (8 : ℝ) (1 : ℝ) Q0 m N hN
  have hNT := natCast_le_scaleMatchedTarget s m N
  have hM : M ≤ 3 * H * T := by
    dsimp [M]
    rw [show (decimalFrequency m : ℝ) = H by simp [decimalFrequency, H]]
    calc
      H * (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
          ((blockOrderedDomain 8 1 Q0 m N B).card : ℝ) / widthWeight B) ≤
          H * (3 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hmean hH
      _ ≤ H * (3 * T) := by gcongr
      _ = 3 * H * T := by ring
  have hW : widthWeightedSquareFunction 8 1 Q0 m N Real.pi =
      P + C + M := by
    have hcenter := centeredWidthWeightedSquareFunction_eq_sectors
      8 1 Q0 m N Real.pi
    unfold centeredWidthWeightedSquareFunction at hcenter
    dsimp [P, C, M]
    linarith
  rw [hW]
  change P + C + M ≤
    (3 + 2 * Cprim + 2 * Ccancel) * H * T
  calc
    P + C + M ≤
        2 * Cprim * H * T + 2 * Ccancel * H * T + 3 * H * T := by
      linarith
    _ = (3 + 2 * Cprim + 2 * Ccancel) * H * T := by ring

/-- Fixed-`s` T29 witness with its exact assembled constant. -/
theorem widthWeightedSquareFunctionAt_of_published_super_primitive
    {Q0 Qstar : ℕ} {s Csuper Cprim : ℝ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hSuper : ARI_superAt Q0 Qstar s Csuper)
    (hPrimitive : PrimitiveIncidenceAt 8 1 Q0 s Cprim) :
    WidthWeightedSquareFunctionAt 8 1 Q0 Real.pi s
      (3 + 2 * Cprim +
        2 * (Csuper + finiteOnsetConstant Qstar + 12)) := by
  refine ⟨?_, ?_⟩
  · have hfinite : 0 ≤ finiteOnsetConstant Qstar := by
      unfold finiteOnsetConstant
      positivity
    nlinarith [hSuper.1, hPrimitive.1]
  · intro m N hm hN
    simpa [decimalFrequency, scaleMatchedTarget] using
      widthWeightedSquareFunction_le_of_three_obstructions
        hPublished hSuper hPrimitive hm hN

/-- Exact quantified frontier. Both independent incidence predicates and the
published estimate remain hypotheses; none is asserted at `Real.pi`. -/
theorem published_super_primitive_implies_widthWeightedSquareFunction
    {Q0 Qstar : ℕ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hSuper : ARI_super Q0 Qstar)
    (hPrimitive : PrimitiveIncidence 8 1 Q0) :
    WidthWeightedSquareFunction 8 1 Q0 Real.pi := by
  intro s hs0 hs1
  obtain ⟨Csuper, hCsuper⟩ := hSuper s hs0 hs1
  obtain ⟨Cprim, hCprim⟩ := hPrimitive s hs0 hs1
  exact ⟨3 + 2 * Cprim +
      2 * (Csuper + finiteOnsetConstant Qstar + 12),
    widthWeightedSquareFunctionAt_of_published_super_primitive
      hPublished hCsuper hCprim⟩

/-- Existing T29-to-T12 consequence, with the same three unasserted
hypotheses and no C2 or C1 conclusion. -/
theorem published_super_primitive_implies_T12
    {Q0 Qstar : ℕ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hSuper : ARI_super Q0 Qstar)
    (hPrimitive : PrimitiveIncidence 8 1 Q0) :
    ScaleMatchedL1Bound 8 1 Q0 := by
  exact widthWeightedSquareFunction_pi_implies_T12 8 1 Q0
    (published_super_primitive_implies_widthWeightedSquareFunction
      hPublished hSuper hPrimitive)

end Theory.PiDigits.LongLagBlockCollisionDecay.T49

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.blockOrderedDomain_eq_blockRecordDomain
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.mem_primitiveValuationStratum_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.primitiveShellEndpoints_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.primitiveIncidence_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.mem_cancellingBlockDifferenceDomain_iff_six_rows
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.primitiveWeightedShellIncidence_eq_direct
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.primitiveSector_abs_le_weightedShellIncidence
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.cancellingWitness_image_eq_domain
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.cancellingSectorContribution_eq_positive
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.centeredWidthWeightedSquareFunction_eq_sectors
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.widthWeightedSquareFunction_le_of_three_obstructions
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.widthWeightedSquareFunctionAt_of_published_super_primitive
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.published_super_primitive_implies_widthWeightedSquareFunction
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T49.published_super_primitive_implies_T12
