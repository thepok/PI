import TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD
import TheoryLib.PiLongLagBlockCollisionDecay.T18T18AlmostEverywhereScaleMatchedL1
import TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff
import TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction

/-!
# T31: cross-block weighted GCD and the almost-everywhere sibling

Canonical local source: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file formalizes only the variable-phase Lebesgue-almost-everywhere
sibling specified by the unverified T28 note. It proves no estimate at
`Real.pi`, no assertion about the decimal digits of pi, and no conclusion
about C1.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Finset Set MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate Real

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T31

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- Exact admissible ordered records whose strict endpoint lies in the
canonical half-open block `[B.start,B.finish)`. -/
def blockOrderedDomain
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) : Finset OrderedLongPair :=
  (orderedLongPairDomain μ c Q0 m N).filter fun q =>
    B.start ≤ frequencyEndpoint q.2 ∧ frequencyEndpoint q.2 < B.finish

/-- Positive differences of two distinct signed frequencies in one block.
The strict inequality chooses exactly one orientation of each unordered pair. -/
def blockPositiveDifferenceDomain
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Finset (OrderedLongPair × OrderedLongPair) :=
  (blockOrderedDomain μ c Q0 m N B ×ˢ
      blockOrderedDomain μ c Q0 m N B).filter fun p =>
    signedDecimalFrequency p.2 < signedDecimalFrequency p.1

theorem signedDecimalFrequency_eq_orderedPhaseFrequency
    (q : OrderedLongPair) :
    signedDecimalFrequency q = orderedPhaseFrequency q := by
  rcases q with ⟨b, r, n⟩
  cases b
  · simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte,
      orderedPhaseFrequency, orderedFirst, orderedSecond]
    rw [positiveDecimalFrequency_int_eq n r]
    ring
  · simp only [signedDecimalFrequency, ↓reduceIte, orderedPhaseFrequency,
      orderedFirst, orderedSecond]
    exact positiveDecimalFrequency_int_eq n r

/-- A block difference, regarded as the corresponding T18 global positive
difference. This retains both T22 records and their arithmetic exclusions. -/
def blockDifferenceToRestricted
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) :
    ↥(restrictedPositiveDifferenceDomain μ c Q0 m N) := by
  refine ⟨p.1, ?_⟩
  rw [mem_restrictedPositiveDifferenceDomain_iff]
  have hp := Finset.mem_filter.mp p.2
  have hprod := Finset.mem_product.mp hp.1
  exact ⟨(Finset.mem_filter.mp hprod.1).1,
    (Finset.mem_filter.mp hprod.2).1, by
      simpa only [signedDecimalFrequency_eq_orderedPhaseFrequency] using hp.2⟩

/-- Exact labeled `(+,+,-,-)` T16 vector of a positive within-block
difference. -/
def blockDifferenceVector
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) :
    BoundedExponentVector 4 N :=
  restrictedDifferenceVector (blockDifferenceToRestricted p)

/-- Positive natural value represented by `blockDifferenceVector`. -/
def blockDifferenceValue (p : OrderedLongPair × OrderedLongPair) : ℕ :=
  restrictedPositiveDifferenceValue p

/-- Noncancelling T16 valuation sector. The lowest occupied coefficient is
one of `1,2,8,9` modulo ten. -/
def PrimitiveBlockDifference
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) : Prop :=
  Noncancelling fourTokenSign (exponentNat (blockDifferenceVector p))

/-- Opposite-sign cancellation sector, reducing to a positive two-token
decimal difference with one hidden exponent. -/
def CancellingBlockDifference
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) : Prop :=
  ¬PrimitiveBlockDifference p

/-- Every legal inclusive frequency has exactly T16's two valuation cases,
including the endpoint `h=10^m`. -/
theorem inclusiveFrequency_valuation_cases {m h : ℕ}
    (hh : h ∈ inclusiveFrequencies m) :
    tenValuation h ≤ m ∧
      (tenValuation h = m ↔ h = 10 ^ m) ∧
      (tenValuation h < m ∨ h = 10 ^ m) := by
  exact decimalFrequency_valuation_cases (by simpa
    [inclusiveFrequencies, decimalFrequencyDomain, decimalFrequency] using hh)

/-- Complete token-valuation split used in every GCD row. -/
theorem blockDifference_valuation_sectors
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) :
    PrimitiveBlockDifference p ∨ CancellingBlockDifference p := by
  exact em _

/-- Membership exposes the canonical block, strict endpoint convention,
positive lag, weak long-lag cutoff, arithmetic exclusion, both ordered
orientations, and strict positive-difference convention. -/
theorem mem_blockPositiveDifferenceDomain_iff
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair} :
    p ∈ blockPositiveDifferenceDomain μ c Q0 m N B ↔
      AdmissibleOrderedFrequency μ c Q0 m p.1 ∧
      frequencyEndpoint p.1.2 < N ∧
      B.start ≤ frequencyEndpoint p.1.2 ∧
      frequencyEndpoint p.1.2 < B.finish ∧
      AdmissibleOrderedFrequency μ c Q0 m p.2 ∧
      frequencyEndpoint p.2.2 < N ∧
      B.start ≤ frequencyEndpoint p.2.2 ∧
      frequencyEndpoint p.2.2 < B.finish ∧
      signedDecimalFrequency p.2 < signedDecimalFrequency p.1 := by
  simp only [blockPositiveDifferenceDomain, blockOrderedDomain,
    Finset.mem_filter, Finset.mem_product,
    mem_orderedLongPairDomain_iff_admissible_endpoint]
  tauto

theorem blockDifferenceVector_mem_longDifferenceDomain
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) :
    blockDifferenceVector p ∈ longDifferenceDomain m N := by
  exact restrictedDifferenceVector_mem_longDifferenceDomain
    (blockDifferenceToRestricted p)

theorem blockDifferenceVector_value
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) :
    longDifferenceValue (blockDifferenceVector p) =
      blockDifferenceValue p.1 := by
  exact restrictedDifferenceVector_value (blockDifferenceToRestricted p)

theorem blockDifferenceVector_injective
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock} :
    Function.Injective (blockDifferenceVector
      (μ := μ) (c := c) (Q0 := Q0) (m := m) (N := N) (B := B)) := by
  intro p q hpq
  change restrictedDifferenceVector (blockDifferenceToRestricted p) =
    restrictedDifferenceVector (blockDifferenceToRestricted q) at hpq
  have hrestricted : blockDifferenceToRestricted p =
      blockDifferenceToRestricted q :=
    restrictedDifferenceVector_injective hpq
  apply Subtype.ext
  simpa [blockDifferenceToRestricted] using
    congrArg Subtype.val hrestricted

/-- Literal width denominator `sqrt(B.finish^2-B.start^2)`. -/
def crossBlockWeight (B C : DyadicBlock) : ℝ :=
  widthWeight B * widthWeight C

/-- T28's exact width-normalized CROSS quantity. Blocks are T24's canonical
partition of `[1,N)`; each inner domain consists of positive differences of
the exact T22 records in that block. -/
def crossBlockWeightedGCD
    (μ c : ℝ) (Q0 m N : ℕ) : ℝ :=
  ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
    ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
        ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
          (gcdKernel (blockDifferenceValue p)
            (blockDifferenceValue q) : ℝ) / crossBlockWeight B C

/-- Explicit arithmetic constants for the four valuation sectors. -/
theorem crossSector_constants :
    (393380096 : ℕ) + 12 * 6400016 + 46112 = 470226400 := by
  norm_num

theorem dyadicPartitionFrom_start_ge
    {q : ℕ} {js : List ℕ} {B : DyadicBlock}
    (hB : B ∈ dyadicPartitionFrom q js) : q + 1 ≤ B.start := by
  induction js generalizing q with
  | nil => simp [dyadicPartitionFrom] at hB
  | cons j js ih =>
      simp only [dyadicPartitionFrom, List.mem_cons] at hB
      rcases hB with rfl | hB
      · rfl
      · exact (by
          have : 0 < 2 ^ j := pow_pos (by omega) _
          omega : q + 1 ≤ q + 2 ^ j + 1).trans (ih hB)

theorem dyadicPartitionFrom_interval_unique
    {q : ℕ} {js : List ℕ} {B C : DyadicBlock} {E : ℕ}
    (hB : B ∈ dyadicPartitionFrom q js)
    (hC : C ∈ dyadicPartitionFrom q js)
    (hEB : B.start ≤ E) (hEB' : E < B.finish)
    (hEC : C.start ≤ E) (hEC' : E < C.finish) : B = C := by
  induction js generalizing q B C with
  | nil => simp [dyadicPartitionFrom] at hB
  | cons j js ih =>
      simp only [dyadicPartitionFrom, List.mem_cons] at hB hC
      rcases hB with rfl | hB <;> rcases hC with rfl | hC
      · rfl
      · have htail := dyadicPartitionFrom_start_ge hC
        simp only [DyadicBlock.finish, DyadicBlock.blockLength] at hEB'
        omega
      · have htail := dyadicPartitionFrom_start_ge hB
        simp only [DyadicBlock.finish, DyadicBlock.blockLength] at hEC'
        omega
      · exact ih hB hC hEB hEB' hEC hEC'

theorem canonicalBlock_interval_unique
    {N : ℕ} {B C : DyadicBlock} {E : ℕ}
    (hB : B ∈ translatedCanonicalBlocks N)
    (hC : C ∈ translatedCanonicalBlocks N)
    (hEB : B.start ≤ E) (hEB' : E < B.finish)
    (hEC : C.start ≤ E) (hEC' : E < C.finish) : B = C := by
  exact dyadicPartitionFrom_interval_unique hB hC hEB hEB' hEC hEC'

theorem blockPositiveDifferenceDomains_pairwiseDisjoint
    (μ c : ℝ) (Q0 m N : ℕ) :
    ((translatedCanonicalBlocks N).toFinset : Set DyadicBlock).PairwiseDisjoint
      (blockPositiveDifferenceDomain μ c Q0 m N) := by
  intro B hB C hC hBC
  apply Finset.disjoint_left.mpr
  intro p hpB hpC
  have hmB := Finset.mem_filter.mp hpB
  have hmC := Finset.mem_filter.mp hpC
  have hqB := Finset.mem_filter.mp (Finset.mem_product.mp hmB.1).1
  have hqC := Finset.mem_filter.mp (Finset.mem_product.mp hmC.1).1
  apply hBC
  exact canonicalBlock_interval_unique
    (by simpa using hB) (by simpa using hC)
    hqB.2.1 hqB.2.2 hqC.2.1 hqC.2.2

theorem canonical_widthWeight_sq
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    widthWeight B ^ 2 = (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2 := by
  unfold widthWeight
  rw [Real.sq_sqrt]
  have hstart := canonicalDyadicPartition_start_pos hB
  have hfinish : B.start < B.finish := by
    simp [DyadicBlock.finish, DyadicBlock.blockLength]
  exact sub_nonneg.mpr (sq_le_sq₀ (by positivity) (by positivity) |>.2
    (by exact_mod_cast hfinish.le))

theorem canonical_widthWeight_one_lt
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    1 < widthWeight B := by
  have hsquare := canonical_widthWeight_sq hB
  have hstart := canonicalDyadicPartition_start_pos hB
  have hlength : 1 ≤ B.blockLength := by
    exact one_le_pow₀ (by norm_num)
  have hfinish : B.finish = B.start + B.blockLength := rfl
  have hsq : (1 : ℝ) < (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2 := by
    rw [hfinish]
    push_cast
    nlinarith [show (1 : ℝ) ≤ B.start by exact_mod_cast hstart,
      show (1 : ℝ) ≤ B.blockLength by exact_mod_cast hlength]
  have hw0 := canonical_widthWeight_pos hB
  nlinarith

theorem canonical_widthWeight_sq_sum
    {N : ℕ} (hN : 1 ≤ N) :
    ((translatedCanonicalBlocks N).map fun B => widthWeight B ^ 2).sum =
      (N : ℝ) ^ 2 - 1 := by
  calc
    ((translatedCanonicalBlocks N).map fun B => widthWeight B ^ 2).sum =
        ((canonicalDyadicPartition N).map fun B =>
          (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2).sum := by
      congr 1
      apply List.map_congr_left
      intro B hB
      exact canonical_widthWeight_sq hB
    _ = (N : ℝ) ^ 2 - (1 : ℝ) ^ 2 := by
      convert canonicalDyadicPartition_endpoint_telescope
        (fun K : ℕ => (K : ℝ) ^ 2) hN using 1 <;> norm_num
    _ = (N : ℝ) ^ 2 - 1 := by norm_num

theorem two_mul_sum_Ico_id_add_length (a L : ℕ) :
    2 * ∑ E ∈ Finset.Ico a (a + L), E + L = L * (2 * a + L) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [show a + (L + 1) = (a + L) + 1 by omega,
        Finset.sum_Ico_succ_top (by omega), Nat.mul_add]
      calc
        2 * (∑ k ∈ Finset.Ico a (a + L), k) + 2 * (a + L) + (L + 1) =
            (2 * (∑ k ∈ Finset.Ico a (a + L), k) + L) +
              (2 * a + 2 * L + 1) := by ring
        _ = L * (2 * a + L) + (2 * a + 2 * L + 1) := by rw [ih]
        _ = (L + 1) * (2 * a + (L + 1)) := by ring

theorem blockOrderedDomain_card_lt
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    (blockOrderedDomain μ c Q0 m N B).card <
      B.blockLength * (B.start + B.finish) := by
  classical
  let D := blockOrderedDomain μ c Q0 m N B
  have hmaps : Set.MapsTo (fun q : OrderedLongPair => frequencyEndpoint q.2)
      (D : Set OrderedLongPair) (Finset.Ico B.start B.finish : Set ℕ) := by
    intro q hq
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hq).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ E ∈ Finset.Ico B.start B.finish,
        #{q ∈ D | frequencyEndpoint q.2 = E}) ≤
        ∑ E ∈ Finset.Ico B.start B.finish, 2 * E := by
      apply Finset.sum_le_sum
      intro E hE
      let fiber := D.filter fun q => frequencyEndpoint q.2 = E
      let encode : OrderedLongPair → Bool × ℕ := fun q => (q.1, q.2.2)
      have hinj : Set.InjOn encode (fiber : Set OrderedLongPair) := by
        intro q hq r hr heq
        have hqE := (Finset.mem_filter.mp hq).2
        have hrE := (Finset.mem_filter.mp hr).2
        rcases q with ⟨bq, lq, nq⟩
        rcases r with ⟨br, lr, nr⟩
        simp only [encode, Prod.mk.injEq] at heq
        simp only [frequencyEndpoint] at hqE hrE
        cases heq.1
        cases heq.2
        have : lq = lr := by omega
        cases this
        rfl
      have himage : fiber.image encode ⊆
          (Finset.univ : Finset Bool) ×ˢ Finset.range E := by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
        have hqD := (Finset.mem_filter.mp hq).1
        have hqE := (Finset.mem_filter.mp hq).2
        have hpos := (Finset.mem_filter.mp hqD).1
        have hlag := (mem_orderedLongPairDomain_iff_admissible_endpoint.mp hpos).1.1
        apply Finset.mem_product.mpr
        refine ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩
        change q.2.2 < E
        change q.2.2 + q.2.1 = E at hqE
        omega
      calc
        fiber.card = (fiber.image encode).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ ((Finset.univ : Finset Bool) ×ˢ Finset.range E).card :=
          Finset.card_le_card himage
        _ = 2 * E := by simp
    _ = 2 * ∑ E ∈ Finset.Ico B.start B.finish, E := by
      rw [Finset.mul_sum]
    _ < B.blockLength * (B.start + B.finish) := by
      have hsum := two_mul_sum_Ico_id_add_length B.start B.blockLength
      have hlength : 0 < B.blockLength := by
        simp [DyadicBlock.blockLength]
      rw [show B.finish = B.start + B.blockLength by rfl]
      calc
        2 * ∑ E ∈ Finset.Ico B.start (B.start + B.blockLength), E <
            2 * ∑ E ∈ Finset.Ico B.start (B.start + B.blockLength), E +
              B.blockLength := Nat.lt_add_of_pos_right hlength
        _ = B.blockLength * (2 * B.start + B.blockLength) := hsum
        _ = B.blockLength * (B.start + (B.start + B.blockLength)) := by ring

theorem blockOrderedDomain_card_lt_width_sq
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) :
    ((blockOrderedDomain μ c Q0 m N B).card : ℝ) < widthWeight B ^ 2 := by
  have hcard := blockOrderedDomain_card_lt μ c Q0 m N B
  have hsquare := canonical_widthWeight_sq hB
  rw [hsquare]
  have hfinish : B.finish = B.start + B.blockLength := rfl
  have hcardR : ((blockOrderedDomain μ c Q0 m N B).card : ℝ) <
      (B.blockLength : ℝ) * (B.start + B.finish : ℕ) := by
    exact_mod_cast hcard
  rw [hfinish] at hcardR ⊢
  push_cast at hcardR ⊢
  nlinarith

theorem blockPositiveDifferenceDomain_card_two_le_sq
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    2 * (blockPositiveDifferenceDomain μ c Q0 m N B).card ≤
      (blockOrderedDomain μ c Q0 m N B).card ^ 2 := by
  classical
  let D := blockPositiveDifferenceDomain μ c Q0 m N B
  let Q := blockOrderedDomain μ c Q0 m N B
  let source := (Finset.univ : Finset Bool) ×ˢ D
  let orient : Bool × (OrderedLongPair × OrderedLongPair) →
      OrderedLongPair × OrderedLongPair := fun x => if x.1 then x.2.swap else x.2
  have hinj : Set.InjOn orient (source : Set (Bool × (OrderedLongPair × OrderedLongPair))) := by
    intro x hx y hy hxy
    have xmem := Finset.mem_filter.mp (Finset.mem_product.mp hx).2
    have ymem := Finset.mem_filter.mp (Finset.mem_product.mp hy).2
    rcases x with ⟨bx, x⟩
    rcases y with ⟨by', y⟩
    cases bx <;> cases by'
    · simp only [orient, Bool.false_eq_true, ↓reduceIte] at hxy
      simp [hxy]
    · simp only [orient, Bool.false_eq_true, ↓reduceIte] at hxy
      have : signedDecimalFrequency y.1 < signedDecimalFrequency y.2 := by
        simpa [hxy] using xmem.2
      exact (not_lt_of_ge ymem.2.le this).elim
    · simp only [orient, Bool.false_eq_true, ↓reduceIte] at hxy
      have : signedDecimalFrequency x.1 < signedDecimalFrequency x.2 := by
        simpa [← hxy] using ymem.2
      exact (not_lt_of_ge xmem.2.le this).elim
    · simp only [orient, ↓reduceIte] at hxy
      have : x = y := Prod.swap_injective hxy
      simp [this]
  have himage : source.image orient ⊆ Q ×ˢ Q := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hm := Finset.mem_filter.mp (Finset.mem_product.mp hy).2
    have hp := Finset.mem_product.mp hm.1
    rcases y with ⟨b, p⟩
    cases b
    · simpa [orient, Q] using hp
    · simpa [orient, Q] using And.intro hp.2 hp.1
  calc
    2 * D.card = source.card := by simp [source]
    _ = (source.image orient).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Q ×ˢ Q).card := Finset.card_le_card himage
    _ = Q.card ^ 2 := by simp [pow_two]

def blockDifferenceExponent
    (p : OrderedLongPair × OrderedLongPair) : Fin 4 → ℕ :=
  ![orderedFirst p.1, orderedSecond p.2,
    orderedSecond p.1, orderedFirst p.2]

theorem exponentNat_blockDifferenceVector
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (p : ↥(blockPositiveDifferenceDomain μ c Q0 m N B)) :
    exponentNat (blockDifferenceVector p) = blockDifferenceExponent p.1 := by
  funext i
  fin_cases i <;>
    simp [blockDifferenceVector, restrictedDifferenceVector,
      blockDifferenceToRestricted, restrictedFirstFin, restrictedSecondFin,
      exponentNat, blockDifferenceExponent]

def primitiveBlockDifferenceDomain
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Finset (OrderedLongPair × OrderedLongPair) := by
  classical
  exact (blockPositiveDifferenceDomain μ c Q0 m N B).filter fun p =>
    Noncancelling fourTokenSign (blockDifferenceExponent p)

def cancellingBlockDifferenceDomain
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Finset (OrderedLongPair × OrderedLongPair) := by
  classical
  exact (blockPositiveDifferenceDomain μ c Q0 m N B).filter fun p =>
    ¬Noncancelling fourTokenSign (blockDifferenceExponent p)

theorem blockPositiveDifferenceDomain_partition
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    blockPositiveDifferenceDomain μ c Q0 m N B =
      primitiveBlockDifferenceDomain μ c Q0 m N B ∪
        cancellingBlockDifferenceDomain μ c Q0 m N B := by
  classical
  ext p
  simp only [primitiveBlockDifferenceDomain, cancellingBlockDifferenceDomain,
    Finset.mem_union, Finset.mem_filter]
  tauto

theorem primitiveBlockDifferenceDomain_disjoint_cancelling
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Disjoint (primitiveBlockDifferenceDomain μ c Q0 m N B)
      (cancellingBlockDifferenceDomain μ c Q0 m N B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hc
  rw [primitiveBlockDifferenceDomain] at hp
  rw [cancellingBlockDifferenceDomain] at hc
  exact (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hp).2

theorem primitiveBlockDifferenceDomain_subset
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ primitiveBlockDifferenceDomain μ c Q0 m N B) :
    p ∈ blockPositiveDifferenceDomain μ c Q0 m N B := by
  classical
  rw [primitiveBlockDifferenceDomain] at hp
  exact (Finset.mem_filter.mp hp).1

theorem cancellingBlockDifferenceDomain_subset
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B) :
    p ∈ blockPositiveDifferenceDomain μ c Q0 m N B := by
  classical
  rw [cancellingBlockDifferenceDomain] at hp
  exact (Finset.mem_filter.mp hp).1

theorem primitiveBlockDifferenceVector_mem
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ primitiveBlockDifferenceDomain μ c Q0 m N B) :
    blockDifferenceVector
      ⟨p, primitiveBlockDifferenceDomain_subset hp⟩ ∈
        primitiveFourTokenDomain N := by
  classical
  rw [primitiveBlockDifferenceDomain] at hp
  have hlong := blockDifferenceVector_mem_longDifferenceDomain
    ⟨p, (Finset.mem_filter.mp hp).1⟩
  have hm := mem_longDifferenceDomain_iff.mp hlong
  exact mem_primitiveFourTokenDomain_iff.mpr
    ⟨hm.1, by
      rw [exponentNat_blockDifferenceVector]
      exact (Finset.mem_filter.mp hp).2, hm.2.2.2⟩

theorem cancellingBlockDifferenceVector_mem
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B) :
    blockDifferenceVector
      ⟨p, cancellingBlockDifferenceDomain_subset hp⟩ ∈
        cancellingFourTokenDomain N := by
  classical
  rw [cancellingBlockDifferenceDomain] at hp
  have hlong := blockDifferenceVector_mem_longDifferenceDomain
    ⟨p, (Finset.mem_filter.mp hp).1⟩
  have hm := mem_longDifferenceDomain_iff.mp hlong
  exact mem_cancellingFourTokenDomain_iff.mpr
    ⟨hm.1, hm.2.2.2, by
      rw [exponentNat_blockDifferenceVector]
      exact (Finset.mem_filter.mp hp).2⟩

theorem cancellingBlockDifference_cross_equality
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B) :
    orderedFirst p.1 = orderedFirst p.2 ∨
      orderedSecond p.1 = orderedSecond p.2 := by
  classical
  rw [cancellingBlockDifferenceDomain] at hp
  have hbase := (Finset.mem_filter.mp hp).1
  have hrecords := Finset.mem_product.mp (Finset.mem_filter.mp hbase).1
  have hp1 := (mem_orderedLongPairDomain_iff_admissible_endpoint.mp
    (Finset.mem_filter.mp hrecords.1).1).1.1
  have hp2 := (mem_orderedLongPairDomain_iff_admissible_endpoint.mp
    (Finset.mem_filter.mp hrecords.2).1).1.1
  have hne1 : orderedFirst p.1 ≠ orderedSecond p.1 := by
    intro heq
    have hdist := ordered_coordinates_dist p.1
    rw [heq, Nat.dist_self] at hdist
    omega
  have hne2 : orderedFirst p.2 ≠ orderedSecond p.2 := by
    intro heq
    have hdist := ordered_coordinates_dist p.2
    rw [heq, Nat.dist_self] at hdist
    omega
  have hcancel := (Finset.mem_filter.mp hp).2
  rw [Noncancelling] at hcancel
  push Not at hcancel
  obtain ⟨i, j, hij, hsign⟩ := hcancel
  fin_cases i <;> fin_cases j <;>
    simp [blockDifferenceExponent, fourTokenSign] at hij hsign ⊢ <;> aesop

theorem orderedPair_eq_of_coordinates
    {μ c : ℝ} {Q0 m N : ℕ} {q r : OrderedLongPair}
    (hq : q ∈ orderedLongPairDomain μ c Q0 m N)
    (hr : r ∈ orderedLongPairDomain μ c Q0 m N)
    (hfirst : orderedFirst q = orderedFirst r)
    (hsecond : orderedSecond q = orderedSecond r) : q = r := by
  apply orderedPhaseFrequency_injOn μ c Q0 m N hq hr
  simp [orderedPhaseFrequency, hfirst, hsecond]

theorem cancellingBlockDifference_records_mem
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B) :
    p.1 ∈ blockOrderedDomain μ c Q0 m N B ∧
      p.2 ∈ blockOrderedDomain μ c Q0 m N B := by
  classical
  rw [cancellingBlockDifferenceDomain] at hp
  exact Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

theorem cancellingBlockDifferenceDomain_card_le
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    (cancellingBlockDifferenceDomain μ c Q0 m N B).card ≤
      2 * N * (blockOrderedDomain μ c Q0 m N B).card := by
  classical
  let C := cancellingBlockDifferenceDomain μ c Q0 m N B
  let Q := blockOrderedDomain μ c Q0 m N B
  let side : OrderedLongPair × OrderedLongPair → Bool := fun p =>
    decide (orderedFirst p.1 = orderedFirst p.2)
  let other : (p : OrderedLongPair × OrderedLongPair) → p ∈ C → Fin N :=
    fun p hp => if side p then
      ⟨orderedSecond p.2, (ordered_coordinates_lt
        (Finset.mem_filter.mp (cancellingBlockDifference_records_mem
          (show p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B by
            simpa [C] using hp)).2).1).2⟩
    else
      ⟨orderedFirst p.2, (ordered_coordinates_lt
        (Finset.mem_filter.mp (cancellingBlockDifference_records_mem
          (show p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B by
            simpa [C] using hp)).2).1).1⟩
  let encode : ↥C → (OrderedLongPair × Fin N) × Bool := fun p =>
    ((p.1.1, other p.1 p.2), side p.1)
  have hinj : Function.Injective encode := by
    intro p q heq
    have hsource : p.1.1 = q.1.1 := congrArg (fun x => x.1.1) heq
    have hother : (other p.1 p.2).1 = (other q.1 q.2).1 :=
      congrArg (fun x => x.1.2.1) heq
    have hside : side p.1 = side q.1 := congrArg (fun x => x.2) heq
    have pC : p.1 ∈ cancellingBlockDifferenceDomain μ c Q0 m N B := by
      simpa [C] using p.2
    have qC : q.1 ∈ cancellingBlockDifferenceDomain μ c Q0 m N B := by
      simpa [C] using q.2
    have pp := cancellingBlockDifference_records_mem pC
    have qp := cancellingBlockDifference_records_mem qC
    have hpq1 : p.1.1 = q.1.1 := hsource
    have htarget : p.1.2 = q.1.2 := by
      by_cases hs : side p.1
      · have hs' : side q.1 := by simpa [hside] using hs
        have pfirst : orderedFirst p.1.1 = orderedFirst p.1.2 := by
          simpa [side, decide_eq_true_eq] using hs
        have qfirst : orderedFirst q.1.1 = orderedFirst q.1.2 := by
          simpa [side, decide_eq_true_eq] using hs'
        have hfirst : orderedFirst p.1.2 = orderedFirst q.1.2 := by
          rw [← pfirst, ← qfirst, hpq1]
        have hsecond : orderedSecond p.1.2 = orderedSecond q.1.2 := by
          simpa [other, hs, hs'] using hother
        exact orderedPair_eq_of_coordinates
          (Finset.mem_filter.mp pp.2).1 (Finset.mem_filter.mp qp.2).1
          hfirst hsecond
      · have hs' : ¬side q.1 := by simpa [hside] using hs
        have peq := cancellingBlockDifference_cross_equality pC
        have qeq := cancellingBlockDifference_cross_equality qC
        have psecond : orderedSecond p.1.1 = orderedSecond p.1.2 := by
          rcases peq with peq | peq
          · exact (hs (by simpa [side, decide_eq_true_eq] using peq)).elim
          · exact peq
        have qsecond : orderedSecond q.1.1 = orderedSecond q.1.2 := by
          rcases qeq with qeq | qeq
          · exact (hs' (by simpa [side, decide_eq_true_eq] using qeq)).elim
          · exact qeq
        have hfirst : orderedFirst p.1.2 = orderedFirst q.1.2 := by
          simpa [other, hs, hs'] using hother
        have hsecond : orderedSecond p.1.2 = orderedSecond q.1.2 := by
          rw [← psecond, ← qsecond, hpq1]
        exact orderedPair_eq_of_coordinates
          (Finset.mem_filter.mp pp.2).1 (Finset.mem_filter.mp qp.2).1
          hfirst hsecond
    apply Subtype.ext
    exact Prod.ext hpq1 htarget
  let target := (Q ×ˢ (Finset.univ : Finset (Fin N))) ×ˢ
    (Finset.univ : Finset Bool)
  have himage : (Finset.univ.image encode) ⊆ target := by
    intro x hx
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩
    exact (cancellingBlockDifference_records_mem
      (show p.1 ∈ cancellingBlockDifferenceDomain μ c Q0 m N B by
        simpa [C] using p.2)).1
  calc
    C.card = (Finset.univ.image encode).card := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    _ ≤ target.card := Finset.card_le_card himage
    _ = Q.card * N * 2 := by simp [target]
    _ = 2 * N * Q.card := by ring

theorem primitiveBlockDifferenceDomains_pairwiseDisjoint
    (μ c : ℝ) (Q0 m N : ℕ) :
    ((translatedCanonicalBlocks N).toFinset : Set DyadicBlock).PairwiseDisjoint
      (primitiveBlockDifferenceDomain μ c Q0 m N) := by
  intro B hB C hC hne
  exact (blockPositiveDifferenceDomains_pairwiseDisjoint μ c Q0 m N
    hB hC hne).mono
      (fun _ h => primitiveBlockDifferenceDomain_subset h)
      (fun _ h => primitiveBlockDifferenceDomain_subset h)

theorem cancellingBlockDifferenceDomains_pairwiseDisjoint
    (μ c : ℝ) (Q0 m N : ℕ) :
    ((translatedCanonicalBlocks N).toFinset : Set DyadicBlock).PairwiseDisjoint
      (cancellingBlockDifferenceDomain μ c Q0 m N) := by
  intro B hB C hC hne
  exact (blockPositiveDifferenceDomains_pairwiseDisjoint μ c Q0 m N
    hB hC hne).mono
      (fun _ h => cancellingBlockDifferenceDomain_subset h)
      (fun _ h => cancellingBlockDifferenceDomain_subset h)

def restrictedPrimitiveDifferenceDomain
    (μ c : ℝ) (Q0 m N : ℕ) : Finset (OrderedLongPair × OrderedLongPair) := by
  classical
  exact (restrictedPositiveDifferenceDomain μ c Q0 m N).filter fun p =>
    Noncancelling fourTokenSign (blockDifferenceExponent p)

def restrictedCancellingDifferenceDomain
    (μ c : ℝ) (Q0 m N : ℕ) : Finset (OrderedLongPair × OrderedLongPair) := by
  classical
  exact (restrictedPositiveDifferenceDomain μ c Q0 m N).filter fun p =>
    ¬Noncancelling fourTokenSign (blockDifferenceExponent p)

theorem primitiveBlockDifferenceDomain_subset_restricted
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock} :
    primitiveBlockDifferenceDomain μ c Q0 m N B ⊆
      restrictedPrimitiveDifferenceDomain μ c Q0 m N := by
  classical
  intro p hp
  rw [primitiveBlockDifferenceDomain] at hp
  rw [restrictedPrimitiveDifferenceDomain, Finset.mem_filter]
  exact ⟨(blockDifferenceToRestricted
    ⟨p, (Finset.mem_filter.mp hp).1⟩).2, (Finset.mem_filter.mp hp).2⟩

theorem cancellingBlockDifferenceDomain_subset_restricted
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock} :
    cancellingBlockDifferenceDomain μ c Q0 m N B ⊆
      restrictedCancellingDifferenceDomain μ c Q0 m N := by
  classical
  intro p hp
  rw [cancellingBlockDifferenceDomain] at hp
  rw [restrictedCancellingDifferenceDomain, Finset.mem_filter]
  exact ⟨(blockDifferenceToRestricted
    ⟨p, (Finset.mem_filter.mp hp).1⟩).2, (Finset.mem_filter.mp hp).2⟩

theorem exponentNat_restrictedDifferenceVector
    {μ c : ℝ} {Q0 m N : ℕ}
    (p : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N)) :
    exponentNat (restrictedDifferenceVector p) = blockDifferenceExponent p.1 := by
  funext i
  fin_cases i <;>
    simp [restrictedDifferenceVector, restrictedFirstFin, restrictedSecondFin,
      exponentNat, blockDifferenceExponent]

theorem restrictedPrimitiveDifferenceDomain_subset
    {μ c : ℝ} {Q0 m N : ℕ}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ restrictedPrimitiveDifferenceDomain μ c Q0 m N) :
    p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N := by
  classical
  rw [restrictedPrimitiveDifferenceDomain] at hp
  exact (Finset.mem_filter.mp hp).1

theorem restrictedCancellingDifferenceDomain_subset
    {μ c : ℝ} {Q0 m N : ℕ}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ restrictedCancellingDifferenceDomain μ c Q0 m N) :
    p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N := by
  classical
  rw [restrictedCancellingDifferenceDomain] at hp
  exact (Finset.mem_filter.mp hp).1

theorem restrictedPrimitiveDifferenceVector_mem
    {μ c : ℝ} {Q0 m N : ℕ}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ restrictedPrimitiveDifferenceDomain μ c Q0 m N) :
    restrictedDifferenceVector
      ⟨p, restrictedPrimitiveDifferenceDomain_subset hp⟩ ∈
        primitiveFourTokenDomain N := by
  classical
  rw [restrictedPrimitiveDifferenceDomain] at hp
  have hlong := restrictedDifferenceVector_mem_longDifferenceDomain
    ⟨p, (Finset.mem_filter.mp hp).1⟩
  have hm := mem_longDifferenceDomain_iff.mp hlong
  exact mem_primitiveFourTokenDomain_iff.mpr
    ⟨hm.1, by
      rw [exponentNat_restrictedDifferenceVector]
      exact (Finset.mem_filter.mp hp).2, hm.2.2.2⟩

theorem restrictedCancellingDifferenceVector_mem
    {μ c : ℝ} {Q0 m N : ℕ}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ restrictedCancellingDifferenceDomain μ c Q0 m N) :
    restrictedDifferenceVector
      ⟨p, restrictedCancellingDifferenceDomain_subset hp⟩ ∈
        cancellingFourTokenDomain N := by
  classical
  rw [restrictedCancellingDifferenceDomain] at hp
  have hlong := restrictedDifferenceVector_mem_longDifferenceDomain
    ⟨p, (Finset.mem_filter.mp hp).1⟩
  have hm := mem_longDifferenceDomain_iff.mp hlong
  exact mem_cancellingFourTokenDomain_iff.mpr
    ⟨hm.1, hm.2.2.2, by
      rw [exponentNat_restrictedDifferenceVector]
      exact (Finset.mem_filter.mp hp).2⟩

theorem primitiveBlockTargetRow_le
    {μ c : ℝ} {Q0 m N : ℕ}
    {B : DyadicBlock} {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ primitiveBlockDifferenceDomain μ c Q0 m N B) :
    (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ q ∈ primitiveBlockDifferenceDomain μ c Q0 m N C,
        (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℚ)) ≤
      393380096 := by
  classical
  let U := restrictedPrimitiveDifferenceDomain μ c Q0 m N
  let encode : ↥U → BoundedExponentVector 4 N := fun q =>
    restrictedDifferenceVector
      ⟨q.1, restrictedPrimitiveDifferenceDomain_subset q.2⟩
  have hinj : Function.Injective encode := by
    intro q r h
    apply Subtype.ext
    change q.1 = r.1
    exact congrArg
      (fun z : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N) => z.1)
      (restrictedDifferenceVector_injective h)
  have himage : U.attach.image encode ⊆ primitiveFourTokenDomain N := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact restrictedPrimitiveDifferenceVector_mem q.2
  let source := blockDifferenceVector
    ⟨p, primitiveBlockDifferenceDomain_subset hp⟩
  have hsource := primitiveBlockDifferenceVector_mem hp
  have hrow := sparseDecimalWeightedRow_four_four_le (N := N)
    fourTokenSign (exponentNat source) fourTokenSign
    (mem_primitiveFourTokenDomain_iff.mp hsource).2.1
    (mem_primitiveFourTokenDomain_iff.mp hsource).2.2
  calc
    (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ q ∈ primitiveBlockDifferenceDomain μ c Q0 m N C,
        gcdKernel (blockDifferenceValue p) (blockDifferenceValue q)) =
        ∑ q ∈ ((translatedCanonicalBlocks N).toFinset.biUnion fun C =>
          primitiveBlockDifferenceDomain μ c Q0 m N C),
          gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) := by
      symm
      exact Finset.sum_biUnion
        (primitiveBlockDifferenceDomains_pairwiseDisjoint μ c Q0 m N)
    _ ≤ ∑ q ∈ U, gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rw [Finset.mem_biUnion] at hq
        obtain ⟨C, hC, hq⟩ := hq
        exact primitiveBlockDifferenceDomain_subset_restricted hq
      · intro q _ _
        exact gcdKernel_nonneg _ _
    _ = ∑ a ∈ U.attach.image encode,
        gcdKernel (longDifferenceValue source) (longDifferenceValue a) := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      rw [← Finset.sum_attach U (fun q =>
        gcdKernel (blockDifferenceValue p) (blockDifferenceValue q))]
      apply Finset.sum_congr rfl
      intro q hq
      rw [restrictedDifferenceVector_value]
      exact congrArg (fun z => gcdKernel z (blockDifferenceValue q.1))
        (blockDifferenceVector_value
          ⟨p, primitiveBlockDifferenceDomain_subset hp⟩).symm
    _ ≤ ∑ a ∈ primitiveFourTokenDomain N,
        gcdKernel (longDifferenceValue source) (longDifferenceValue a) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun a _ _ => gcdKernel_nonneg _ _)
    _ = sparseDecimalWeightedRow fourTokenSign (exponentNat source)
        fourTokenSign N := by
      rfl
    _ ≤ 393380096 := hrow

theorem cancellingBlockPrimitiveTargetRow_le
    {μ c : ℝ} {Q0 m N : ℕ}
    {B : DyadicBlock} {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B) :
    (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ q ∈ primitiveBlockDifferenceDomain μ c Q0 m N C,
        (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℚ)) ≤
      6400016 := by
  classical
  let source := blockDifferenceVector
    ⟨p, cancellingBlockDifferenceDomain_subset hp⟩
  have hsource := cancellingBlockDifferenceVector_mem hp
  have hrow := cancellingFourTokenPrimitiveRow_le hsource
  let U := restrictedPrimitiveDifferenceDomain μ c Q0 m N
  let encode : ↥U → BoundedExponentVector 4 N := fun q =>
    restrictedDifferenceVector
      ⟨q.1, restrictedPrimitiveDifferenceDomain_subset q.2⟩
  have hinj : Function.Injective encode := by
    intro q r h
    apply Subtype.ext
    change q.1 = r.1
    exact congrArg
      (fun z : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N) => z.1)
      (restrictedDifferenceVector_injective h)
  have himage : U.attach.image encode ⊆ primitiveFourTokenDomain N := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact restrictedPrimitiveDifferenceVector_mem q.2
  calc
    (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ q ∈ primitiveBlockDifferenceDomain μ c Q0 m N C,
        gcdKernel (blockDifferenceValue p) (blockDifferenceValue q)) =
        ∑ q ∈ ((translatedCanonicalBlocks N).toFinset.biUnion fun C =>
          primitiveBlockDifferenceDomain μ c Q0 m N C),
          gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) := by
      symm
      exact Finset.sum_biUnion
        (primitiveBlockDifferenceDomains_pairwiseDisjoint μ c Q0 m N)
    _ ≤ ∑ q ∈ U, gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rw [Finset.mem_biUnion] at hq
        obtain ⟨C, hC, hq⟩ := hq
        exact primitiveBlockDifferenceDomain_subset_restricted hq
      · intro q _ _
        exact gcdKernel_nonneg _ _
    _ = ∑ a ∈ U.attach.image encode,
        gcdKernel (longDifferenceValue source) (longDifferenceValue a) := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      rw [← Finset.sum_attach U (fun q =>
        gcdKernel (blockDifferenceValue p) (blockDifferenceValue q))]
      apply Finset.sum_congr rfl
      intro q hq
      rw [restrictedDifferenceVector_value]
      exact congrArg (fun z => gcdKernel z (blockDifferenceValue q.1))
        (blockDifferenceVector_value
          ⟨p, cancellingBlockDifferenceDomain_subset hp⟩).symm
    _ ≤ ∑ a ∈ primitiveFourTokenDomain N,
        gcdKernel (longDifferenceValue source) (longDifferenceValue a) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun a _ _ => gcdKernel_nonneg _ _)
    _ = cancellingFourTokenPrimitiveRow source := rfl
    _ ≤ 6400016 := hrow

theorem cancellingBlockTargetRow_le
    {μ c : ℝ} {Q0 m N : ℕ}
    {B : DyadicBlock} {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ cancellingBlockDifferenceDomain μ c Q0 m N B) :
    (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ q ∈ cancellingBlockDifferenceDomain μ c Q0 m N C,
        (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℚ)) ≤
      23056 * N := by
  classical
  let source := blockDifferenceVector
    ⟨p, cancellingBlockDifferenceDomain_subset hp⟩
  have hsource := cancellingBlockDifferenceVector_mem hp
  have hrow := cancellingFourTokenRow_le hsource
  let U := restrictedCancellingDifferenceDomain μ c Q0 m N
  let encode : ↥U → BoundedExponentVector 4 N := fun q =>
    restrictedDifferenceVector
      ⟨q.1, restrictedCancellingDifferenceDomain_subset q.2⟩
  have hinj : Function.Injective encode := by
    intro q r h
    apply Subtype.ext
    change q.1 = r.1
    exact congrArg
      (fun z : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N) => z.1)
      (restrictedDifferenceVector_injective h)
  have himage : U.attach.image encode ⊆ cancellingFourTokenDomain N := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact restrictedCancellingDifferenceVector_mem q.2
  calc
    (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ q ∈ cancellingBlockDifferenceDomain μ c Q0 m N C,
        gcdKernel (blockDifferenceValue p) (blockDifferenceValue q)) =
        ∑ q ∈ ((translatedCanonicalBlocks N).toFinset.biUnion fun C =>
          cancellingBlockDifferenceDomain μ c Q0 m N C),
          gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) := by
      symm
      exact Finset.sum_biUnion
        (cancellingBlockDifferenceDomains_pairwiseDisjoint μ c Q0 m N)
    _ ≤ ∑ q ∈ U, gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rw [Finset.mem_biUnion] at hq
        obtain ⟨C, hC, hq⟩ := hq
        exact cancellingBlockDifferenceDomain_subset_restricted hq
      · intro q _ _
        exact gcdKernel_nonneg _ _
    _ = ∑ a ∈ U.attach.image encode,
        gcdKernel (longDifferenceValue source) (longDifferenceValue a) := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      rw [← Finset.sum_attach U (fun q =>
        gcdKernel (blockDifferenceValue p) (blockDifferenceValue q))]
      apply Finset.sum_congr rfl
      intro q hq
      rw [restrictedDifferenceVector_value]
      exact congrArg (fun z => gcdKernel z (blockDifferenceValue q.1))
        (blockDifferenceVector_value
          ⟨p, cancellingBlockDifferenceDomain_subset hp⟩).symm
    _ ≤ ∑ a ∈ cancellingFourTokenDomain N,
        gcdKernel (longDifferenceValue source) (longDifferenceValue a) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun a _ _ => gcdKernel_nonneg _ _)
    _ = cancellingFourTokenRow source := rfl
    _ ≤ 23056 * N := hrow

theorem canonical_widthWeight_sum_le_three
    {N : ℕ} (hN : 1 ≤ N) :
    ((translatedCanonicalBlocks N).map widthWeight).sum < 3 * (N : ℝ) := by
  have hsharp := canonical_widthWeight_sum_le_sharp hN
  have hsqrt : Real.sqrt 2 < (3 : ℝ) / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg 2
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ((translatedCanonicalBlocks N).map widthWeight).sum ≤
        ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) := hsharp
    _ < 3 * (N : ℝ) := by nlinarith

theorem canonicalBlocks_card_le_two_log
    {N : ℕ} (hN : 2 ≤ N) :
    (((translatedCanonicalBlocks N).toFinset.card : ℕ) : ℝ) ≤
      2 * Real.log (2 * N) := by
  let L := (N - 1).bitIndices
  have hNsub : N - 1 ≠ 0 := by omega
  have hsubset : L.toFinset ⊆ Finset.range (Nat.log 2 (N - 1) + 1) := by
    intro j hj
    rw [Finset.mem_range]
    have hjL : j ∈ L := by simpa [L] using hj
    have hp := Nat.two_pow_le_of_mem_bitIndices hjL
    have := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hNsub).2 hp
    omega
  have hcardNat : L.length ≤ Nat.log 2 (N - 1) + 1 := by
    rw [← L.toFinset_card_of_nodup (by simp [L])]
    exact (Finset.card_le_card hsubset).trans_eq (by simp)
  have hblocksCard : (translatedCanonicalBlocks N).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup (translatedCanonicalBlocks_nodup N)]
    simpa [translatedCanonicalBlocks, L] using congrArg List.length
      (canonicalDyadicPartition_levels N)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnatlog := Real.natLog_le_logb (N - 1) 2
  rw [Real.logb] at hnatlog
  have hsuble : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    have hsubposR : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < N - 1)
    have hNposR : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (by omega : 0 < N)
    have hleR : (((N - 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : N - 1 ≤ N)
    exact Real.strictMonoOn_log.monotoneOn
      hsubposR hNposR hleR
  have hmul : ((Nat.log 2 (N - 1) : ℕ) : ℝ) * Real.log 2 ≤
      Real.log N := by
    have := (le_div_iff₀ hlog2).mp hnatlog
    exact this.trans hsuble
  have hcardR : (((translatedCanonicalBlocks N).toFinset.card : ℕ) : ℝ) ≤
      (Nat.log 2 (N - 1) : ℝ) + 1 := by
    rw [hblocksCard]
    exact_mod_cast hcardNat
  have hlogmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (N : ℝ) ≠ 0)]
  have hhalf : (1 : ℝ) / 2 < Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).trans Real.log_two_gt_d9
  rw [hlogmul]
  have hnonneg : 0 ≤ ((translatedCanonicalBlocks N).toFinset.card : ℝ) := by
    positivity
  nlinarith

theorem one_le_two_log_two_mul (N : ℕ) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ 2 * Real.log (2 * N) := by
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).trans Real.log_two_gt_d9
  have harg : (2 : ℝ) ≤ 2 * N := by exact_mod_cast Nat.mul_le_mul_left 2 hN
  have hlog := Real.strictMonoOn_log.monotoneOn
    (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < 2 * N) harg
  nlinarith

theorem reciprocal_product_le_half_sq_sum
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 / (x * y) ≤ (1 / x ^ 2 + 1 / y ^ 2) / 2 := by
  have hsquare : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  field_simp [ne_of_gt hx, ne_of_gt hy]
  nlinarith

def blockSectorWeightedGCD
    (μ c : ℝ) (Q0 m N : ℕ)
    (D E : DyadicBlock → Finset (OrderedLongPair × OrderedLongPair)) : ℝ :=
  ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
    ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ p ∈ D B, ∑ q ∈ E C,
        (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ) /
          crossBlockWeight B C

theorem crossBlockWeightedGCD_eq_sectors
    (μ c : ℝ) (Q0 m N : ℕ) :
    crossBlockWeightedGCD μ c Q0 m N =
      blockSectorWeightedGCD μ c Q0 m N
        (primitiveBlockDifferenceDomain μ c Q0 m N)
        (primitiveBlockDifferenceDomain μ c Q0 m N) +
      blockSectorWeightedGCD μ c Q0 m N
        (primitiveBlockDifferenceDomain μ c Q0 m N)
        (cancellingBlockDifferenceDomain μ c Q0 m N) +
      blockSectorWeightedGCD μ c Q0 m N
        (cancellingBlockDifferenceDomain μ c Q0 m N)
        (primitiveBlockDifferenceDomain μ c Q0 m N) +
      blockSectorWeightedGCD μ c Q0 m N
        (cancellingBlockDifferenceDomain μ c Q0 m N)
        (cancellingBlockDifferenceDomain μ c Q0 m N) := by
  classical
  unfold crossBlockWeightedGCD blockSectorWeightedGCD
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro C hC
  rw [blockPositiveDifferenceDomain_partition μ c Q0 m N B,
    blockPositiveDifferenceDomain_partition μ c Q0 m N C,
    Finset.sum_union (primitiveBlockDifferenceDomain_disjoint_cancelling
      μ c Q0 m N B)]
  simp_rw [Finset.sum_union (primitiveBlockDifferenceDomain_disjoint_cancelling
    μ c Q0 m N C)]
  simp_rw [Finset.sum_add_distrib]
  ring

theorem primitive_weighted_card_sum_le
    (μ c : ℝ) (Q0 m N : ℕ) (hN : 1 ≤ N) :
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((primitiveBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
        widthWeight B ^ 2) ≤ ((N : ℝ) ^ 2 - 1) / 2 := by
  have hpoint : ∀ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((primitiveBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
          widthWeight B ^ 2 ≤ widthWeight B ^ 2 / 2 := by
    intro B hB
    have hw := canonical_widthWeight_pos (by simpa using hB)
    have hpD := Finset.card_le_card (fun _ h =>
      primitiveBlockDifferenceDomain_subset (μ := μ) (c := c)
        (Q0 := Q0) (m := m) (N := N) (B := B) h)
    have htwo := blockPositiveDifferenceDomain_card_two_le_sq μ c Q0 m N B
    have hM := blockOrderedDomain_card_lt_width_sq
      (μ := μ) (c := c) (Q0 := Q0) (m := m) (N := N)
      (B := B) (by simpa using hB)
    have hpR : 2 * ((primitiveBlockDifferenceDomain μ c Q0 m N B).card : ℝ) ≤
        ((blockOrderedDomain μ c Q0 m N B).card : ℝ) ^ 2 := by
      exact_mod_cast (Nat.mul_le_mul_left 2 hpD |>.trans htwo)
    have hsq : ((blockOrderedDomain μ c Q0 m N B).card : ℝ) ^ 2 ≤
        widthWeight B ^ 4 := by nlinarith
    apply (div_le_iff₀ (sq_pos_of_pos hw)).2
    nlinarith
  calc
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((primitiveBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
        widthWeight B ^ 2) ≤
        ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
          widthWeight B ^ 2 / 2 := by
      exact Finset.sum_le_sum fun B hB => hpoint B hB
    _ = (((translatedCanonicalBlocks N).map fun B => widthWeight B ^ 2).sum) / 2 := by
      rw [← Finset.sum_div, ← List.sum_toFinset (fun B => widthWeight B ^ 2)
        (translatedCanonicalBlocks_nodup N)]
    _ = ((N : ℝ) ^ 2 - 1) / 2 := by rw [canonical_widthWeight_sq_sum hN]

theorem cancelling_weighted_card_sum_le
    (μ c : ℝ) (Q0 m N : ℕ) (hN : 1 ≤ N) :
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((cancellingBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
        widthWeight B) ≤ 6 * (N : ℝ) ^ 2 := by
  have hpoint : ∀ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((cancellingBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
          widthWeight B ≤ 2 * (N : ℝ) * widthWeight B := by
    intro B hB
    have hw := canonical_widthWeight_pos (by simpa using hB)
    have hc := cancellingBlockDifferenceDomain_card_le μ c Q0 m N B
    have hcR : ((cancellingBlockDifferenceDomain μ c Q0 m N B).card : ℝ) ≤
        2 * (N : ℝ) *
          ((blockOrderedDomain μ c Q0 m N B).card : ℝ) := by exact_mod_cast hc
    have hM := blockOrderedDomain_card_lt_width_sq
      (μ := μ) (c := c) (Q0 := Q0) (m := m) (N := N)
      (B := B) (by simpa using hB)
    apply (div_le_iff₀ hw).2
    nlinarith
  have hsum := canonical_widthWeight_sum_le_three hN
  calc
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((cancellingBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
        widthWeight B) ≤
        ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
          2 * (N : ℝ) * widthWeight B := by
      exact Finset.sum_le_sum fun B hB => hpoint B hB
    _ = 2 * (N : ℝ) *
        ((translatedCanonicalBlocks N).map widthWeight).sum := by
      rw [← Finset.mul_sum, ← List.sum_toFinset widthWeight
        (translatedCanonicalBlocks_nodup N)]
    _ ≤ 6 * (N : ℝ) ^ 2 := by nlinarith

theorem cancelling_sqWeighted_card_sum_le
    (μ c : ℝ) (Q0 m N : ℕ) :
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((cancellingBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
        widthWeight B ^ 2) ≤
      2 * (N : ℝ) * (translatedCanonicalBlocks N).toFinset.card := by
  calc
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((cancellingBlockDifferenceDomain μ c Q0 m N B).card : ℝ) /
        widthWeight B ^ 2) ≤
        ∑ _B ∈ (translatedCanonicalBlocks N).toFinset, 2 * (N : ℝ) := by
      apply Finset.sum_le_sum
      intro B hB
      have hw := canonical_widthWeight_pos (by simpa using hB)
      have hc := cancellingBlockDifferenceDomain_card_le μ c Q0 m N B
      have hcR : ((cancellingBlockDifferenceDomain μ c Q0 m N B).card : ℝ) ≤
          2 * (N : ℝ) * ((blockOrderedDomain μ c Q0 m N B).card : ℝ) := by
        exact_mod_cast hc
      have hM := blockOrderedDomain_card_lt_width_sq
        (μ := μ) (c := c) (Q0 := Q0) (m := m) (N := N)
        (B := B) (by simpa using hB)
      apply (div_le_iff₀ (sq_pos_of_pos hw)).2
      nlinarith
    _ = 2 * (N : ℝ) * (translatedCanonicalBlocks N).toFinset.card := by
      simp
      ring

theorem blockSectorWeightedGCD_le_of_rows
    (μ c : ℝ) (Q0 m N : ℕ)
    (D E : DyadicBlock → Finset (OrderedLongPair × OrderedLongPair))
    (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ B ∈ (translatedCanonicalBlocks N).toFinset,
      ∀ p ∈ D B,
        (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
          ∑ q ∈ E C,
            (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ)) ≤ R) :
    blockSectorWeightedGCD μ c Q0 m N D E ≤
      R * ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        ((D B).card : ℝ) / widthWeight B := by
  unfold blockSectorWeightedGCD crossBlockWeight
  calc
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
        ∑ p ∈ D B, ∑ q ∈ E C,
          (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ) /
            (widthWeight B * widthWeight C)) =
        ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
          ∑ p ∈ D B,
            ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
              ∑ q ∈ E C,
                (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ) /
                  (widthWeight B * widthWeight C) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.sum_comm]
    _ ≤ ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
          ∑ _p ∈ D B, R / widthWeight B := by
      apply Finset.sum_le_sum
      intro B hB
      apply Finset.sum_le_sum
      intro p hp
      have hwB := canonical_widthWeight_pos (by simpa using hB)
      calc
        (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
          ∑ q ∈ E C,
            (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ) /
              (widthWeight B * widthWeight C)) ≤
            ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
              ∑ q ∈ E C,
                (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ) /
                  widthWeight B := by
          apply Finset.sum_le_sum
          intro C hC
          apply Finset.sum_le_sum
          intro q hq
          have hwC := canonical_widthWeight_one_lt (by simpa using hC)
          have hk : (0 : ℝ) ≤ gcdKernel (blockDifferenceValue p)
              (blockDifferenceValue q) := by exact_mod_cast gcdKernel_nonneg _ _
          exact div_le_div_of_nonneg_left hk hwB (by nlinarith)
        _ = (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
              ∑ q ∈ E C,
                (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ)) /
              widthWeight B := by
          simp_rw [Finset.sum_div]
        _ ≤ R / widthWeight B := div_le_div_of_nonneg_right (hrow B hB p hp) hwB.le
    _ = R * ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
          ((D B).card : ℝ) / widthWeight B := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      simp
      ring

theorem blockSectorWeightedGCD_comm
    (μ c : ℝ) (Q0 m N : ℕ)
    (D E : DyadicBlock → Finset (OrderedLongPair × OrderedLongPair)) :
    blockSectorWeightedGCD μ c Q0 m N D E =
      blockSectorWeightedGCD μ c Q0 m N E D := by
  unfold blockSectorWeightedGCD crossBlockWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [gcdKernel_comm]
  ring

theorem blockSectorWeightedGCD_self_le_of_rows
    (μ c : ℝ) (Q0 m N : ℕ)
    (D : DyadicBlock → Finset (OrderedLongPair × OrderedLongPair))
    (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ B ∈ (translatedCanonicalBlocks N).toFinset,
      ∀ p ∈ D B,
        (∑ C ∈ (translatedCanonicalBlocks N).toFinset,
          ∑ q ∈ D C,
            (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ)) ≤ R) :
    blockSectorWeightedGCD μ c Q0 m N D D ≤
      R * ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        ((D B).card : ℝ) / widthWeight B ^ 2 := by
  let S := (translatedCanonicalBlocks N).toFinset
  let K : (OrderedLongPair × OrderedLongPair) →
      (OrderedLongPair × OrderedLongPair) → ℝ := fun p q =>
    (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ)
  have hfirst :
      (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
        K p q / (2 * widthWeight B ^ 2)) ≤
        (R / 2) * ∑ B ∈ S, ((D B).card : ℝ) / widthWeight B ^ 2 := by
    calc
      (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
        K p q / (2 * widthWeight B ^ 2)) =
          ∑ B ∈ S, ∑ p ∈ D B,
            (∑ C ∈ S, ∑ q ∈ D C, K p q) / (2 * widthWeight B ^ 2) := by
        apply Finset.sum_congr rfl
        intro B hB
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        simp_rw [Finset.sum_div]
      _ ≤ ∑ B ∈ S, ∑ _p ∈ D B, R / (2 * widthWeight B ^ 2) := by
        apply Finset.sum_le_sum
        intro B hB
        apply Finset.sum_le_sum
        intro p hp
        exact div_le_div_of_nonneg_right (hrow B hB p hp) (by positivity)
      _ = (R / 2) * ∑ B ∈ S, ((D B).card : ℝ) / widthWeight B ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        simp
        ring
  have hsecond :
      (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
        K p q / (2 * widthWeight C ^ 2)) ≤
        (R / 2) * ∑ B ∈ S, ((D B).card : ℝ) / widthWeight B ^ 2 := by
    calc
      (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
        K p q / (2 * widthWeight C ^ 2)) =
          ∑ C ∈ S, ∑ q ∈ D C,
            (∑ B ∈ S, ∑ p ∈ D B, K q p) / (2 * widthWeight C ^ 2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro C hC
        calc
          (∑ B ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
            K p q / (2 * widthWeight C ^ 2)) =
              ∑ B ∈ S, ∑ q ∈ D C, ∑ p ∈ D B,
                K p q / (2 * widthWeight C ^ 2) := by
            apply Finset.sum_congr rfl
            intro B hB
            rw [Finset.sum_comm]
          _ = ∑ q ∈ D C, ∑ B ∈ S, ∑ p ∈ D B,
                K p q / (2 * widthWeight C ^ 2) := by rw [Finset.sum_comm]
          _ = ∑ q ∈ D C,
              (∑ B ∈ S, ∑ p ∈ D B, K q p) / (2 * widthWeight C ^ 2) := by
            apply Finset.sum_congr rfl
            intro q hq
            calc
              (∑ B ∈ S, ∑ p ∈ D B, K p q / (2 * widthWeight C ^ 2)) =
                  ∑ B ∈ S, (∑ p ∈ D B, K p q) /
                    (2 * widthWeight C ^ 2) := by
                apply Finset.sum_congr rfl
                intro B hB
                rw [Finset.sum_div]
              _ = (∑ B ∈ S, ∑ p ∈ D B, K p q) /
                    (2 * widthWeight C ^ 2) := by rw [Finset.sum_div]
              _ = (∑ B ∈ S, ∑ p ∈ D B, K q p) /
                    (2 * widthWeight C ^ 2) := by
                apply congrArg (fun z : ℝ => z / (2 * widthWeight C ^ 2))
                apply Finset.sum_congr rfl
                intro B hB
                apply Finset.sum_congr rfl
                intro p hp
                simp [K, gcdKernel_comm]
      _ ≤ ∑ C ∈ S, ∑ _q ∈ D C, R / (2 * widthWeight C ^ 2) := by
        apply Finset.sum_le_sum
        intro C hC
        apply Finset.sum_le_sum
        intro q hq
        exact div_le_div_of_nonneg_right (hrow C hC q hq) (by positivity)
      _ = (R / 2) * ∑ B ∈ S, ((D B).card : ℝ) / widthWeight B ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        simp
        ring
  unfold blockSectorWeightedGCD crossBlockWeight
  change (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
    K p q / (widthWeight B * widthWeight C)) ≤ _
  calc
    (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
      K p q / (widthWeight B * widthWeight C)) ≤
        (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
          K p q / (2 * widthWeight B ^ 2)) +
        (∑ B ∈ S, ∑ C ∈ S, ∑ p ∈ D B, ∑ q ∈ D C,
          K p q / (2 * widthWeight C ^ 2)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro B hB
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro C hC
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q hq
      have hk : 0 ≤ K p q := by
        dsimp [K]
        exact_mod_cast gcdKernel_nonneg _ _
      have hr := reciprocal_product_le_half_sq_sum
        (canonical_widthWeight_pos (by simpa [S] using hB))
        (canonical_widthWeight_pos (by simpa [S] using hC))
      calc
        K p q / (widthWeight B * widthWeight C) =
            K p q * (1 / (widthWeight B * widthWeight C)) := by ring
        _ ≤ K p q * ((1 / widthWeight B ^ 2 + 1 / widthWeight C ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hr hk
        _ = K p q / (2 * widthWeight B ^ 2) +
            K p q / (2 * widthWeight C ^ 2) := by ring
    _ ≤ (R / 2) * (∑ B ∈ S, ((D B).card : ℝ) / widthWeight B ^ 2) +
        (R / 2) * (∑ B ∈ S, ((D B).card : ℝ) / widthWeight B ^ 2) :=
      add_le_add hfirst hsecond
    _ = R * ∑ B ∈ S, ((D B).card : ℝ) / widthWeight B ^ 2 := by ring

/-- Width-sensitive CROSS estimate. Its theorem type exposes the exact block
domain, literal weights, both token-valuation cases, and the final constant. -/
theorem crossBlockWeightedGCD_le
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    (∀ h ∈ Finset.Icc 1 (10 ^ m),
      tenValuation h < m ∨ h = 10 ^ m) ∧
    (∀ B ∈ canonicalDyadicPartition N,
      1 ≤ B.start ∧ B.finish = B.start + 2 ^ B.level ∧
        2 ^ B.level ∣ B.start - 1) ∧
    crossBlockWeightedGCD μ c Q0 m N ≤
      470226400 * (N : ℝ) ^ 2 * Real.log (2 * N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    exact inclusiveFrequency_valuation_cases (by simpa [inclusiveFrequencies] using hh) |>.2.2
  · intro B hB
    exact translatedCanonicalBlock_spec hB
  · classical
    let P := primitiveBlockDifferenceDomain μ c Q0 m N
    let C := cancellingBlockDifferenceDomain μ c Q0 m N
    have hPProw : ∀ B ∈ (translatedCanonicalBlocks N).toFinset,
        ∀ p ∈ P B,
          (∑ D ∈ (translatedCanonicalBlocks N).toFinset,
            ∑ q ∈ P D,
              (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ)) ≤
            393380096 := by
      intro B hB p hp
      exact_mod_cast primitiveBlockTargetRow_le (μ := μ) (c := c)
        (Q0 := Q0) (m := m) (N := N) (B := B) (p := p) hp
    have hCProw : ∀ B ∈ (translatedCanonicalBlocks N).toFinset,
        ∀ p ∈ C B,
          (∑ D ∈ (translatedCanonicalBlocks N).toFinset,
            ∑ q ∈ P D,
              (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ)) ≤
            6400016 := by
      intro B hB p hp
      exact_mod_cast cancellingBlockPrimitiveTargetRow_le (μ := μ) (c := c)
        (Q0 := Q0) (m := m) (N := N) (B := B) (p := p) hp
    have hCCrow : ∀ B ∈ (translatedCanonicalBlocks N).toFinset,
        ∀ p ∈ C B,
          (∑ D ∈ (translatedCanonicalBlocks N).toFinset,
            ∑ q ∈ C D,
              (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ)) ≤
            23056 * (N : ℝ) := by
      intro B hB p hp
      exact_mod_cast cancellingBlockTargetRow_le (μ := μ) (c := c)
        (Q0 := Q0) (m := m) (N := N) (B := B) (p := p) hp
    have hPP : blockSectorWeightedGCD μ c Q0 m N P P ≤
        196690048 * ((N : ℝ) ^ 2 - 1) := by
      calc
        blockSectorWeightedGCD μ c Q0 m N P P ≤
            393380096 * ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
              ((P B).card : ℝ) / widthWeight B ^ 2 :=
          blockSectorWeightedGCD_self_le_of_rows μ c Q0 m N P
            393380096 (by norm_num) hPProw
        _ ≤ 393380096 * (((N : ℝ) ^ 2 - 1) / 2) := by
          gcongr
          exact primitive_weighted_card_sum_le μ c Q0 m N hN
        _ = 196690048 * ((N : ℝ) ^ 2 - 1) := by ring
    have hCP : blockSectorWeightedGCD μ c Q0 m N C P ≤
        38400096 * (N : ℝ) ^ 2 := by
      calc
        blockSectorWeightedGCD μ c Q0 m N C P ≤
            6400016 * ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
              ((C B).card : ℝ) / widthWeight B :=
          blockSectorWeightedGCD_le_of_rows μ c Q0 m N C P
            6400016 (by norm_num) hCProw
        _ ≤ 6400016 * (6 * (N : ℝ) ^ 2) := by
          gcongr
          exact cancelling_weighted_card_sum_le μ c Q0 m N hN
        _ = 38400096 * (N : ℝ) ^ 2 := by ring
    have hPC : blockSectorWeightedGCD μ c Q0 m N P C ≤
        38400096 * (N : ℝ) ^ 2 := by
      rw [blockSectorWeightedGCD_comm μ c Q0 m N P C]
      exact hCP
    have hCCbase : blockSectorWeightedGCD μ c Q0 m N C C ≤
        46112 * (N : ℝ) ^ 2 *
          ((translatedCanonicalBlocks N).toFinset.card : ℝ) := by
      calc
        blockSectorWeightedGCD μ c Q0 m N C C ≤
            (23056 * (N : ℝ)) *
              ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
                ((C B).card : ℝ) / widthWeight B ^ 2 :=
          blockSectorWeightedGCD_self_le_of_rows μ c Q0 m N C
            (23056 * (N : ℝ)) (by positivity) hCCrow
        _ ≤ (23056 * (N : ℝ)) *
            (2 * (N : ℝ) * (translatedCanonicalBlocks N).toFinset.card) := by
          gcongr
          exact cancelling_sqWeighted_card_sum_le μ c Q0 m N
        _ = 46112 * (N : ℝ) ^ 2 *
            ((translatedCanonicalBlocks N).toFinset.card : ℝ) := by ring
    have hCC : blockSectorWeightedGCD μ c Q0 m N C C ≤
        92224 * (N : ℝ) ^ 2 * Real.log (2 * N) := by
      by_cases hN1 : N = 1
      · subst N
        simp [translatedCanonicalBlocks, canonicalDyadicPartition,
          dyadicPartitionFrom, blockSectorWeightedGCD,
          Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      · have hN2 : 2 ≤ N := by omega
        calc
          blockSectorWeightedGCD μ c Q0 m N C C ≤
              46112 * (N : ℝ) ^ 2 *
                ((translatedCanonicalBlocks N).toFinset.card : ℝ) := hCCbase
          _ ≤ 46112 * (N : ℝ) ^ 2 * (2 * Real.log (2 * N)) := by
            exact mul_le_mul_of_nonneg_left
              (canonicalBlocks_card_le_two_log hN2) (by positivity)
          _ = 92224 * (N : ℝ) ^ 2 * Real.log (2 * N) := by ring
    rw [crossBlockWeightedGCD_eq_sectors]
    change blockSectorWeightedGCD μ c Q0 m N P P +
        blockSectorWeightedGCD μ c Q0 m N P C +
        blockSectorWeightedGCD μ c Q0 m N C P +
        blockSectorWeightedGCD μ c Q0 m N C C ≤ _
    have hlog69 : (69 : ℝ) / 100 ≤ Real.log (2 * N) := by
      have harg : (2 : ℝ) ≤ 2 * N := by exact_mod_cast Nat.mul_le_mul_left 2 hN
      have hlog := Real.strictMonoOn_log.monotoneOn
        (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < 2 * N) harg
      have hconst : (69 : ℝ) / 100 < Real.log 2 :=
        (by norm_num : (69 : ℝ) / 100 < 0.6931471803).trans Real.log_two_gt_d9
      linarith
    have hNnonneg : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
    nlinarith

/-- Fully unfolded acceptance-facing form of CROSS. The theorem type shows
the complete inclusive-frequency valuation split, T24's canonical half-open
blocks, T31's exact positive-difference domains, the literal square-root
widths, and the constant `470226400`. -/
theorem crossBlockWeightedGCD_le_explicit
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    (∀ h ∈ Finset.Icc 1 (10 ^ m),
      tenValuation h ≤ m ∧
        (tenValuation h = m ↔ h = 10 ^ m) ∧
        (tenValuation h < m ∨ h = 10 ^ m)) ∧
    (∀ B ∈ canonicalDyadicPartition N,
      1 ≤ B.start ∧ B.finish = B.start + 2 ^ B.level ∧
        2 ^ B.level ∣ B.start - 1) ∧
    (∑ B ∈ (canonicalDyadicPartition N).toFinset,
      ∑ C ∈ (canonicalDyadicPartition N).toFinset,
        ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
          ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
            (gcdKernel (blockDifferenceValue p)
              (blockDifferenceValue q) : ℝ) /
              (Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) *
                Real.sqrt ((C.finish : ℝ) ^ 2 - (C.start : ℝ) ^ 2))) ≤
      470226400 * (N : ℝ) ^ 2 * Real.log (2 * N) := by
  have hcross := crossBlockWeightedGCD_le μ c Q0 m N hm hN
  refine ⟨?_, hcross.2.1, ?_⟩
  · intro h hh
    exact inclusiveFrequency_valuation_cases
      (by simpa [inclusiveFrequencies] using hh)
  · simpa [crossBlockWeightedGCD, crossBlockWeight, widthWeight,
      translatedCanonicalBlocks] using hcross.2.2

/-- The exact width-weighted square function, centered at its blockwise
Lebesgue mean. -/
def centeredWidthWeightedSquareFunction
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  widthWeightedSquareFunction μ c Q0 m N α -
    (decimalFrequency m : ℝ) *
      ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        (blockOrderedDomain μ c Q0 m N B).card / widthWeight B

def blockPhaseSum
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) : ℂ :=
  ∑ q ∈ blockOrderedDomain μ c Q0 m N B,
    Theory.PiDigits.T27.phase (h : ℤ) ((signedDecimalFrequency q : ℝ) * α)

def blockPhaseEnergy
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) : ℝ :=
  ∑ h ∈ inclusiveFrequencies m, ‖blockPhaseSum μ c Q0 m N B h α‖ ^ 2

def blockCenteredEnergy
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) : ℝ :=
  blockPhaseEnergy μ c Q0 m N B α -
    (decimalFrequency m : ℝ) * (blockOrderedDomain μ c Q0 m N B).card

theorem orderedDomain_finish_eq_start_union_block
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) :
    orderedLongPairDomain μ c Q0 m B.finish =
      orderedLongPairDomain μ c Q0 m B.start ∪
        blockOrderedDomain μ c Q0 m N B := by
  classical
  ext q
  simp only [Finset.mem_union, blockOrderedDomain, Finset.mem_filter]
  rw [mem_orderedLongPairDomain_iff_admissible_endpoint,
    mem_orderedLongPairDomain_iff_admissible_endpoint,
    mem_orderedLongPairDomain_iff_admissible_endpoint]
  have hfinish := canonical_finish_le hB
  constructor
  · rintro ⟨hq, hend⟩
    by_cases hs : frequencyEndpoint q.2 < B.start
    · exact Or.inl ⟨hq, hs⟩
    · exact Or.inr ⟨⟨hq, hend.trans_le hfinish⟩, by omega⟩
  · rintro (⟨hq, hend⟩ | ⟨⟨hq, hendN⟩, hblock⟩)
    · exact ⟨hq, hend.trans_le (by simp [DyadicBlock.finish])⟩
    · exact ⟨hq, hblock.2⟩

theorem orderedDomain_start_disjoint_block
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Disjoint (orderedLongPairDomain μ c Q0 m B.start)
      (blockOrderedDomain μ c Q0 m N B) := by
  apply Finset.disjoint_left.mpr
  intro q hstart hblock
  have hs := (mem_orderedLongPairDomain_iff_admissible_endpoint.mp hstart).2
  have hb := (Finset.mem_filter.mp hblock).2.1
  omega

theorem canonicalBlockVector_eq_blockPhaseSum
    (μ c : ℝ) (Q0 m N : ℕ) {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) (h : ℕ) (α : ℝ) :
    canonicalBlockVector μ c Q0 m B α h =
      blockPhaseSum μ c Q0 m N B h α := by
  classical
  unfold canonicalBlockVector blockPhaseSum
  rw [← orderedAlphaSum_eq_cutoffFourierSum,
    ← orderedAlphaSum_eq_cutoffFourierSum]
  unfold orderedAlphaSum
  rw [orderedDomain_finish_eq_start_union_block hB,
    Finset.sum_union (orderedDomain_start_disjoint_block μ c Q0 m N B)]
  ring

theorem blockSquaredEnergy_eq_blockPhaseEnergy
    (μ c : ℝ) (Q0 m N : ℕ) {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) (α : ℝ) :
    blockSquaredEnergy μ c Q0 m B α = blockPhaseEnergy μ c Q0 m N B α := by
  unfold blockSquaredEnergy blockPhaseEnergy
  apply Finset.sum_congr rfl
  intro h hh
  rw [canonicalBlockVector_eq_blockPhaseSum μ c Q0 m N hB]

theorem centeredWidthWeightedSquareFunction_eq_sum
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    centeredWidthWeightedSquareFunction μ c Q0 m N α =
      ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        blockCenteredEnergy μ c Q0 m N B α / widthWeight B := by
  classical
  unfold centeredWidthWeightedSquareFunction widthWeightedSquareFunction
  rw [← List.sum_toFinset
    (fun B => blockSquaredEnergy μ c Q0 m B α / widthWeight B)
    (translatedCanonicalBlocks_nodup N)]
  have henergy :
      (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        blockSquaredEnergy μ c Q0 m B α / widthWeight B) =
      ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        blockPhaseEnergy μ c Q0 m N B α / widthWeight B := by
    apply Finset.sum_congr rfl
    intro B hB
    rw [blockSquaredEnergy_eq_blockPhaseEnergy μ c Q0 m N (by simpa using hB)]
  rw [henergy]
  unfold blockCenteredEnergy
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  ring

theorem continuous_blockPhaseSum
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (h : ℕ) :
    Continuous (blockPhaseSum μ c Q0 m N B h) := by
  unfold blockPhaseSum Theory.PiDigits.T27.phase
  fun_prop

theorem continuous_blockCenteredEnergy
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Continuous (blockCenteredEnergy μ c Q0 m N B) := by
  unfold blockCenteredEnergy blockPhaseEnergy
  apply Continuous.sub
  · apply continuous_finsetSum
    intro h hh
    exact (continuous_blockPhaseSum μ c Q0 m N B h).norm.pow 2
  · fun_prop

def blockCenteredPolynomial
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) : ℂ :=
  ∑ h ∈ inclusiveFrequencies m,
    ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
      (Theory.PiDigits.T27.phase (-(h : ℤ))
          ((blockDifferenceValue p : ℝ) * α) +
        Theory.PiDigits.T27.phase (h : ℤ)
          ((blockDifferenceValue p : ℝ) * α))

theorem signedDecimalFrequency_injOn_block
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Set.InjOn signedDecimalFrequency
      (blockOrderedDomain μ c Q0 m N B : Set OrderedLongPair) := by
  intro q hq r hr heq
  exact signedDecimalFrequency_injective_of_admissible
    (mem_orderedLongPairDomain_iff_admissible_endpoint.mp
      (Finset.mem_filter.mp hq).1).1
    (mem_orderedLongPairDomain_iff_admissible_endpoint.mp
      (Finset.mem_filter.mp hr).1).1 heq

theorem blockPhaseSum_norm_sq_expansion
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) :
    ((‖blockPhaseSum μ c Q0 m N B h α‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ blockOrderedDomain μ c Q0 m N B,
        ∑ r ∈ blockOrderedDomain μ c Q0 m N B,
          Theory.PiDigits.T27.phase
            ((h : ℤ) * (signedDecimalFrequency r - signedDecimalFrequency q)) α := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  unfold blockPhaseSum
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [conj_phase_mul_phase]
  congr 1
  ring

def blockOffDiagonalDomain
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Finset (OrderedLongPair × OrderedLongPair) :=
  ((blockOrderedDomain μ c Q0 m N B) ×ˢ
    blockOrderedDomain μ c Q0 m N B).filter fun p => p.1 ≠ p.2

theorem blockOffDiagonal_eq_orient_image
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    blockOffDiagonalDomain μ c Q0 m N B =
      ((Finset.univ : Finset Bool) ×ˢ
        blockPositiveDifferenceDomain μ c Q0 m N B).image
          orientPositiveDifference := by
  classical
  ext p
  constructor
  · intro hp
    have hm := Finset.mem_filter.mp hp
    have hq := Finset.mem_product.mp hm.1
    have hfreq : signedDecimalFrequency p.1 ≠ signedDecimalFrequency p.2 := by
      intro heq
      exact hm.2 (signedDecimalFrequency_injOn_block μ c Q0 m N B hq.1 hq.2 heq)
    rcases lt_or_gt_of_ne hfreq with hlt | hgt
    · refine Finset.mem_image.mpr ⟨(true, p.swap), ?_, by
        simp [orientPositiveDifference]⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq.2, hq.1⟩, hlt⟩⟩
    · refine Finset.mem_image.mpr ⟨(false, p), ?_, by
        simp [orientPositiveDifference]⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hm.1, hgt⟩⟩
  · intro hp
    obtain ⟨⟨b, p⟩, hb, rfl⟩ := Finset.mem_image.mp hp
    have hd := Finset.mem_filter.mp (Finset.mem_product.mp hb).2
    apply Finset.mem_filter.mpr
    cases b
    · exact ⟨hd.1, fun heq => (ne_of_lt hd.2)
        (congrArg signedDecimalFrequency heq).symm⟩
    · exact ⟨Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hd.1).2, (Finset.mem_product.mp hd.1).1⟩,
        fun heq => (ne_of_lt hd.2) (congrArg signedDecimalFrequency heq)⟩

theorem orientPositiveDifference_injOn_block
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    Set.InjOn orientPositiveDifference
      (↑((Finset.univ : Finset Bool) ×ˢ
        blockPositiveDifferenceDomain μ c Q0 m N B) :
          Set (Bool × (OrderedLongPair × OrderedLongPair))) := by
  intro p hp q hq hpq
  have pp := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
  have qp := Finset.mem_filter.mp (Finset.mem_product.mp hq).2
  rcases p with ⟨bp, p⟩
  rcases q with ⟨bq, q⟩
  cases bp <;> cases bq
  · simpa [orientPositiveDifference] using hpq
  · have heq : p = q.swap := by simpa [orientPositiveDifference] using hpq
    have : signedDecimalFrequency q.1 < signedDecimalFrequency q.2 := by
      simpa [heq] using pp.2
    exact (not_lt_of_ge qp.2.le this).elim
  · have heq : p.swap = q := by simpa [orientPositiveDifference] using hpq
    have : signedDecimalFrequency p.1 < signedDecimalFrequency p.2 := by
      simpa [← heq] using qp.2
    exact (not_lt_of_ge pp.2.le this).elim
  · have heq : p.swap = q.swap := by simpa [orientPositiveDifference] using hpq
    simp [Prod.swap_injective heq]

theorem sum_blockOffDiagonal_eq_orient
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock)
    (f : OrderedLongPair × OrderedLongPair → ℂ) :
    (∑ p ∈ blockOffDiagonalDomain μ c Q0 m N B, f p) =
      ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
        (f p + f p.swap) := by
  classical
  rw [blockOffDiagonal_eq_orient_image]
  rw [Finset.sum_image (fun a ha b hb h =>
    orientPositiveDifference_injOn_block μ c Q0 m N B ha hb h)]
  rw [Finset.sum_product]
  simp [orientPositiveDifference, add_comm, ← Finset.sum_add_distrib]

theorem blockPositiveDifferenceValue_cast
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ blockPositiveDifferenceDomain μ c Q0 m N B) :
    (blockDifferenceValue p : ℤ) =
      signedDecimalFrequency p.1 - signedDecimalFrequency p.2 := by
  simpa [blockDifferenceValue, signedDecimalFrequency_eq_orderedPhaseFrequency] using
    (restrictedPositiveDifferenceValue_cast
      (blockDifferenceToRestricted ⟨p, hp⟩).2)

theorem blockPhaseSum_norm_sq_sub_card
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) :
    ((‖blockPhaseSum μ c Q0 m N B h α‖ ^ 2 : ℝ) : ℂ) -
        (blockOrderedDomain μ c Q0 m N B).card =
      ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
        (Theory.PiDigits.T27.phase (-(h : ℤ))
            ((blockDifferenceValue p : ℝ) * α) +
          Theory.PiDigits.T27.phase (h : ℤ)
            ((blockDifferenceValue p : ℝ) * α)) := by
  classical
  let Q := blockOrderedDomain μ c Q0 m N B
  let P := Q ×ˢ Q
  let f : OrderedLongPair × OrderedLongPair → ℂ := fun p =>
    Theory.PiDigits.T27.phase
      ((h : ℤ) * (signedDecimalFrequency p.2 - signedDecimalFrequency p.1)) α
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p => p.1 ≠ p.2) f
  have hdiag : (P.filter fun p => ¬p.1 ≠ p.2) = P.filter fun p => p.1 = p.2 := by
    ext p
    simp
  have hdiagSum : (∑ p ∈ P.filter (fun p => ¬p.1 ≠ p.2), f p) = Q.card := by
    rw [hdiag]
    let diagonal := Q.image fun q => (q, q)
    have heq : P.filter (fun p => p.1 = p.2) = diagonal := by
      ext p
      constructor
      · intro hp
        have hm := Finset.mem_filter.mp hp
        have hparts := Finset.mem_product.mp hm.1
        exact Finset.mem_image.mpr ⟨p.1, hparts.1, Prod.ext rfl hm.2⟩
      · intro hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hq, hq⟩, rfl⟩
    rw [heq, Finset.sum_image (fun a _ b _ hab => congrArg Prod.fst hab)]
    simp [f, Theory.PiDigits.T27.phase_zero]
  rw [blockPhaseSum_norm_sq_expansion]
  have hprod : (∑ p ∈ P, f p) =
      ∑ q ∈ Q, ∑ r ∈ Q,
        Theory.PiDigits.T27.phase
          ((h : ℤ) * (signedDecimalFrequency r - signedDecimalFrequency q)) α := by
    simpa [P, Q, f] using Finset.sum_product Q Q f
  rw [← hprod]
  have htotal : (∑ p ∈ P, f p) - Q.card =
      ∑ p ∈ blockOffDiagonalDomain μ c Q0 m N B, f p := by
    change _ = ∑ p ∈ P.filter (fun p => p.1 ≠ p.2), f p
    rw [← hsplit, hdiagSum]
    ring
  rw [htotal, sum_blockOffDiagonal_eq_orient]
  apply Finset.sum_congr rfl
  intro p hp
  rcases p with ⟨q, r⟩
  have hcast := blockPositiveDifferenceValue_cast hp
  have hcastC : (blockDifferenceValue (q, r) : ℂ) =
      (signedDecimalFrequency q : ℂ) - (signedDecimalFrequency r : ℂ) := by
    exact_mod_cast hcast
  unfold f Theory.PiDigits.T27.phase
  simp only [Prod.swap_prod_mk]
  congr 1 <;> push_cast <;> rw [hcastC] <;> ring

theorem blockCenteredEnergy_eq_polynomial
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) :
    ((blockCenteredEnergy μ c Q0 m N B α : ℝ) : ℂ) =
      blockCenteredPolynomial μ c Q0 m N B α := by
  unfold blockCenteredEnergy blockPhaseEnergy blockCenteredPolynomial
  have hconst :
      (decimalFrequency m : ℂ) *
          ((blockOrderedDomain μ c Q0 m N B).card : ℂ) =
        ∑ _h ∈ inclusiveFrequencies m,
          ((blockOrderedDomain μ c Q0 m N B).card : ℂ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [inclusiveFrequencies, decimalFrequency]
  push_cast
  rw [hconst, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [Complex.ofReal_pow] using
    blockPhaseSum_norm_sq_sub_card μ c Q0 m N B h α

def blockCenteredAtom
    (b : Bool) (h d : ℕ) (α : ℝ) : ℂ :=
  Theory.PiDigits.T27.phase (if b then (h : ℤ) else -(h : ℤ)) ((d : ℝ) * α)

theorem blockCenteredPolynomial_eq_signedSum
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) :
    blockCenteredPolynomial μ c Q0 m N B α =
      ∑ h ∈ inclusiveFrequencies m,
        ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
          ∑ b : Bool, blockCenteredAtom b h (blockDifferenceValue p) α := by
  unfold blockCenteredPolynomial blockCenteredAtom
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro p hp
  simp [Fintype.sum_bool, add_comm]

def blockSignedPairSum (h d : ℕ) (α : ℝ) : ℂ :=
  ∑ b : Bool, blockCenteredAtom b h d α

theorem continuous_blockCenteredAtom (b : Bool) (h d : ℕ) :
    Continuous (blockCenteredAtom b h d) := by
  unfold blockCenteredAtom Theory.PiDigits.T27.phase
  fun_prop

theorem continuous_blockSignedPairSum (h d : ℕ) :
    Continuous (blockSignedPairSum h d) := by
  unfold blockSignedPairSum blockCenteredAtom Theory.PiDigits.T27.phase
  fun_prop

theorem integral_blockSignedPairSum_mul
    {h k d e : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hd : 0 < d) (he : 0 < e) :
    (∫ α, blockSignedPairSum h d α * blockSignedPairSum k e α ∂phaseMeasure) =
      if h * d = k * e then 2 else 0 := by
  change (∫ α, (∑ bh ∈ (Finset.univ : Finset Bool), blockCenteredAtom bh h d α) *
    (∑ bk ∈ (Finset.univ : Finset Bool), blockCenteredAtom bk k e α) ∂phaseMeasure) = _
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      (∑ bh : Bool, ∫ α, ∑ bk : Bool,
          blockCenteredAtom bh h d α * blockCenteredAtom bk k e α
          ∂phaseMeasure) =
          ∑ bh : Bool, ∑ bk : Bool,
            ∫ α, blockCenteredAtom bh h d α * blockCenteredAtom bk k e α
              ∂phaseMeasure := by
        apply Finset.sum_congr rfl
        intro bh hbh
        rw [MeasureTheory.integral_finsetSum]
        intro bk hbk
        rw [phaseMeasure]
        exact ((continuous_blockCenteredAtom bh h d).mul
          (continuous_blockCenteredAtom bk k e)).integrableOn_Icc.mono_set
              Set.Ico_subset_Icc_self
      _ = if h * d = k * e then 2 else 0 := by
        simpa [blockCenteredAtom] using sum_two_sign_integrals hh hk hd he
  · intro bh hbh
    apply integrable_finsetSum
    intro bk hbk
    rw [phaseMeasure]
    exact ((continuous_blockCenteredAtom bh h d).mul
      (continuous_blockCenteredAtom bk k e)).integrableOn_Icc.mono_set
        Set.Ico_subset_Icc_self

theorem blockCenteredPolynomial_eq_pairSums
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (α : ℝ) :
    blockCenteredPolynomial μ c Q0 m N B α =
      ∑ h ∈ inclusiveFrequencies m,
        ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
          blockSignedPairSum h (blockDifferenceValue p) α := by
  rw [blockCenteredPolynomial_eq_signedSum]
  rfl

theorem blockDifferenceValue_pos
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ blockPositiveDifferenceDomain μ c Q0 m N B) :
    0 < blockDifferenceValue p := by
  have hcast := blockPositiveDifferenceValue_cast hp
  have hlt := (Finset.mem_filter.mp hp).2
  have hz : (0 : ℤ) < (blockDifferenceValue p : ℤ) := by
    rw [hcast]
    exact sub_pos.mpr hlt
  exact_mod_cast hz

theorem integral_blockCenteredPolynomials_mul
    (μ c : ℝ) (Q0 m N : ℕ) (B C : DyadicBlock) :
    (∫ α, blockCenteredPolynomial μ c Q0 m N B α *
        blockCenteredPolynomial μ c Q0 m N C α ∂phaseMeasure) =
      ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
        ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
          2 * ((resonanceDomain (decimalFrequency m)
            (blockDifferenceValue p) (blockDifferenceValue q)).card : ℂ) := by
  classical
  simp_rw [blockCenteredPolynomial_eq_pairSums, Finset.sum_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      (∑ h ∈ inclusiveFrequencies m,
        ∫ α, ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
          ∑ k ∈ inclusiveFrequencies m,
            ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
              blockSignedPairSum h (blockDifferenceValue p) α *
                blockSignedPairSum k (blockDifferenceValue q) α
          ∂phaseMeasure) =
          ∑ h ∈ inclusiveFrequencies m,
            ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
              ∑ k ∈ inclusiveFrequencies m,
                ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
                  if h * blockDifferenceValue p = k * blockDifferenceValue q
                  then (2 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [MeasureTheory.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro p hp
          rw [MeasureTheory.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro k hk
            rw [MeasureTheory.integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro q hq
              exact integral_blockSignedPairSum_mul
                (mem_inclusiveFrequencies_iff.mp hh).1
                (mem_inclusiveFrequencies_iff.mp hk).1
                (blockDifferenceValue_pos hp) (blockDifferenceValue_pos hq)
            · intro q hq
              rw [phaseMeasure]
              exact ((continuous_blockSignedPairSum h (blockDifferenceValue p)).mul
                (continuous_blockSignedPairSum k
                  (blockDifferenceValue q))).integrableOn_Icc.mono_set
                    Set.Ico_subset_Icc_self
          · intro k hk
            apply integrable_finsetSum
            intro q hq
            rw [phaseMeasure]
            exact ((continuous_blockSignedPairSum h (blockDifferenceValue p)).mul
              (continuous_blockSignedPairSum k
                (blockDifferenceValue q))).integrableOn_Icc.mono_set
                  Set.Ico_subset_Icc_self
        · intro p hp
          apply integrable_finsetSum
          intro k hk
          apply integrable_finsetSum
          intro q hq
          rw [phaseMeasure]
          exact ((continuous_blockSignedPairSum h (blockDifferenceValue p)).mul
            (continuous_blockSignedPairSum k
              (blockDifferenceValue q))).integrableOn_Icc.mono_set
                Set.Ico_subset_Icc_self
      _ = ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
          ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
            2 * ((resonanceDomain (decimalFrequency m)
              (blockDifferenceValue p) (blockDifferenceValue q)).card : ℂ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        calc
          (∑ h ∈ inclusiveFrequencies m, ∑ k ∈ inclusiveFrequencies m,
            ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
              if h * blockDifferenceValue p = k * blockDifferenceValue q
              then (2 : ℂ) else 0) =
              ∑ h ∈ inclusiveFrequencies m,
                ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
                  ∑ k ∈ inclusiveFrequencies m,
                    if h * blockDifferenceValue p = k * blockDifferenceValue q
                    then (2 : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [Finset.sum_comm]
          _ = ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
                ∑ h ∈ inclusiveFrequencies m, ∑ k ∈ inclusiveFrequencies m,
                  if h * blockDifferenceValue p = k * blockDifferenceValue q
                  then (2 : ℂ) else 0 := by rw [Finset.sum_comm]
          _ = ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
              2 * ((resonanceDomain (decimalFrequency m)
                (blockDifferenceValue p) (blockDifferenceValue q)).card : ℂ) := by
            apply Finset.sum_congr rfl
            intro q hq
            unfold resonanceDomain
            simp only [inclusiveFrequencies]
            rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product,
              Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro h hh
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            by_cases heq : h * blockDifferenceValue p = k * blockDifferenceValue q
            · simp [heq]
            · simp [heq]
  · intro h hh
    apply integrable_finsetSum
    intro p hp
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro q hq
    rw [phaseMeasure]
    exact ((continuous_blockSignedPairSum h (blockDifferenceValue p)).mul
      (continuous_blockSignedPairSum k
        (blockDifferenceValue q))).integrableOn_Icc.mono_set
          Set.Ico_subset_Icc_self

theorem integral_blockCenteredEnergies_mul
    (μ c : ℝ) (Q0 m N : ℕ) (B C : DyadicBlock) :
    (∫ α, blockCenteredEnergy μ c Q0 m N B α *
        blockCenteredEnergy μ c Q0 m N C α ∂phaseMeasure) =
      ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
        ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
          2 * ((resonanceDomain (decimalFrequency m)
            (blockDifferenceValue p) (blockDifferenceValue q)).card : ℝ) := by
  have hcomplex := integral_blockCenteredPolynomials_mul μ c Q0 m N B C
  have hrewrite :
      (∫ α, blockCenteredPolynomial μ c Q0 m N B α *
          blockCenteredPolynomial μ c Q0 m N C α ∂phaseMeasure) =
        ∫ α, ((blockCenteredEnergy μ c Q0 m N B α *
          blockCenteredEnergy μ c Q0 m N C α : ℝ) : ℂ) ∂phaseMeasure := by
    apply integral_congr_ae
    filter_upwards [] with α
    rw [← blockCenteredEnergy_eq_polynomial,
      ← blockCenteredEnergy_eq_polynomial]
    norm_cast
  rw [hrewrite, integral_complex_ofReal] at hcomplex
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_sum,
    Complex.ofReal_mul, Nat.cast_ofNat, Nat.cast_id] using hcomplex)

theorem continuous_centeredWidthWeightedSquareFunction
    (μ c : ℝ) (Q0 m N : ℕ) :
    Continuous (centeredWidthWeightedSquareFunction μ c Q0 m N) := by
  rw [show centeredWidthWeightedSquareFunction μ c Q0 m N = fun α =>
      ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        blockCenteredEnergy μ c Q0 m N B α / widthWeight B by
    funext α
    exact centeredWidthWeightedSquareFunction_eq_sum μ c Q0 m N α]
  apply continuous_finsetSum
  intro B hB
  exact (continuous_blockCenteredEnergy μ c Q0 m N B).div_const _

theorem integral_centeredWidthWeightedSquareFunction_sq
    (μ c : ℝ) (Q0 m N : ℕ) :
    (∫ α, centeredWidthWeightedSquareFunction μ c Q0 m N α ^ 2
      ∂phaseMeasure) =
      ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
          ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
            ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
              2 * ((resonanceDomain (decimalFrequency m)
                (blockDifferenceValue p) (blockDifferenceValue q)).card : ℝ) /
                crossBlockWeight B C := by
  rw [integral_congr_ae (ae_of_all phaseMeasure fun α =>
    congrArg (fun z : ℝ => z ^ 2)
      (centeredWidthWeightedSquareFunction_eq_sum μ c Q0 m N α))]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro B hB
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro C hC
      calc
        (∫ α, blockCenteredEnergy μ c Q0 m N B α / widthWeight B *
            (blockCenteredEnergy μ c Q0 m N C α / widthWeight C)
            ∂phaseMeasure) =
            (∫ α, blockCenteredEnergy μ c Q0 m N B α *
              blockCenteredEnergy μ c Q0 m N C α ∂phaseMeasure) /
                crossBlockWeight B C := by
          rw [← integral_div]
          apply integral_congr_ae
          filter_upwards [] with α
          unfold crossBlockWeight
          ring
        _ = _ := by
          rw [integral_blockCenteredEnergies_mul]
          simp_rw [Finset.sum_div]
    · intro C _
      rw [phaseMeasure]
      exact (((continuous_blockCenteredEnergy μ c Q0 m N B).div_const _).mul
        ((continuous_blockCenteredEnergy μ c Q0 m N C).div_const _)).integrableOn_Icc.mono_set
          Set.Ico_subset_Icc_self
  · intro B _
    apply integrable_finsetSum
    intro C _
    rw [phaseMeasure]
    exact (((continuous_blockCenteredEnergy μ c Q0 m N B).div_const _).mul
      ((continuous_blockCenteredEnergy μ c Q0 m N C).div_const _)).integrableOn_Icc.mono_set
        Set.Ico_subset_Icc_self

/-- Exact bad event used for Borel-Cantelli. -/
def widthWeightedBadSet
    (μ c : ℝ) (Q0 : ℕ) (s : ℝ) (m N : ℕ) : Set ℝ :=
  Set.Ico (0 : ℝ) 1 ∩
    {α | 4 * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N <
      widthWeightedSquareFunction μ c Q0 m N α}

/-- Phases lying in infinitely many positive-integer bad events. -/
def widthWeightedTailExceptionalSet
    (μ c : ℝ) (Q0 : ℕ) (s : ℝ) : Set ℝ :=
  {α | {z : ℕ × ℕ |
    α ∈ widthWeightedBadSet μ c Q0 s (z.1 + 1) (z.2 + 1)}.Infinite}

/-- Countable union of rational-exponent exceptional sets. -/
def widthWeightedExceptionalSet
    (μ c : ℝ) (Q0 : ℕ) : Set ℝ :=
  ⋃ s : ℚ, if 0 < s ∧ s < 1 then
    widthWeightedTailExceptionalSet μ c Q0 (s : ℝ) else ∅

/-- Explicit measurable full-measure phase set. -/
def widthWeightedFullMeasureSet
    (μ c : ℝ) (Q0 : ℕ) : Set ℝ :=
  Set.Ico (0 : ℝ) 1 \
    toMeasurable phaseMeasure (widthWeightedExceptionalSet μ c Q0)

/-- CROSS supplies the variance estimate for the centered width-weighted
square function. -/
theorem integral_centeredWidthWeightedSquareFunction_sq_le
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    (∫ α, centeredWidthWeightedSquareFunction μ c Q0 m N α ^ 2
      ∂phaseMeasure) ≤
      940452800 * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2 *
        Real.log (2 * N) := by
  rw [integral_centeredWidthWeightedSquareFunction_sq]
  have hres :
      (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
        ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
          ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
            ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
              2 * ((resonanceDomain (decimalFrequency m)
                (blockDifferenceValue p) (blockDifferenceValue q)).card : ℝ) /
                crossBlockWeight B C) ≤
        2 * (decimalFrequency m : ℝ) * crossBlockWeightedGCD μ c Q0 m N := by
    unfold crossBlockWeightedGCD
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B hB
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C hC
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hcount := resonanceDomain_card_le_gcdKernel (H := decimalFrequency m)
      (blockDifferenceValue_pos hp) (blockDifferenceValue_pos hq)
    have hcountR :
        ((resonanceDomain (decimalFrequency m)
          (blockDifferenceValue p) (blockDifferenceValue q)).card : ℝ) ≤
          (decimalFrequency m : ℝ) *
            (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ) := by
      exact_mod_cast hcount
    have hw : 0 < crossBlockWeight B C :=
      mul_pos (canonical_widthWeight_pos (by simpa using hB))
        (canonical_widthWeight_pos (by simpa using hC))
    calc
      2 * ((resonanceDomain (decimalFrequency m)
          (blockDifferenceValue p) (blockDifferenceValue q)).card : ℝ) /
          crossBlockWeight B C ≤
        (2 * ((decimalFrequency m : ℝ) *
          (gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ))) /
            crossBlockWeight B C :=
          div_le_div_of_nonneg_right (by nlinarith) hw.le
      _ = 2 * (decimalFrequency m : ℝ) *
          ((gcdKernel (blockDifferenceValue p) (blockDifferenceValue q) : ℝ) /
            crossBlockWeight B C) := by ring
  have hcross := (crossBlockWeightedGCD_le μ c Q0 m N hm hN).2.2
  calc
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ∑ C ∈ (translatedCanonicalBlocks N).toFinset,
        ∑ p ∈ blockPositiveDifferenceDomain μ c Q0 m N B,
          ∑ q ∈ blockPositiveDifferenceDomain μ c Q0 m N C,
            2 * ((resonanceDomain (decimalFrequency m)
              (blockDifferenceValue p) (blockDifferenceValue q)).card : ℝ) /
              crossBlockWeight B C) ≤
        2 * (decimalFrequency m : ℝ) * crossBlockWeightedGCD μ c Q0 m N := hres
    _ ≤ 2 * (decimalFrequency m : ℝ) *
        (470226400 * (N : ℝ) ^ 2 * Real.log (2 * N)) := by
      gcongr
    _ = 940452800 * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2 *
        Real.log (2 * N) := by ring

theorem blockMeanWeight_sum_le
    (μ c : ℝ) (Q0 m N : ℕ) (hN : 1 ≤ N) :
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((blockOrderedDomain μ c Q0 m N B).card : ℝ) / widthWeight B) ≤
        3 * (N : ℝ) := by
  calc
    (∑ B ∈ (translatedCanonicalBlocks N).toFinset,
      ((blockOrderedDomain μ c Q0 m N B).card : ℝ) / widthWeight B) ≤
        ∑ B ∈ (translatedCanonicalBlocks N).toFinset, widthWeight B := by
      apply Finset.sum_le_sum
      intro B hB
      have hw := canonical_widthWeight_pos (by simpa using hB)
      apply (div_le_iff₀ hw).2
      simpa [pow_two] using (blockOrderedDomain_card_lt_width_sq
        (μ := μ) (c := c) (Q0 := Q0) (m := m) (N := N)
        (B := B) (by simpa using hB)).le
    _ = ((translatedCanonicalBlocks N).map widthWeight).sum := by
      rw [List.sum_toFinset widthWeight (translatedCanonicalBlocks_nodup N)]
    _ ≤ 3 * (N : ℝ) := (canonical_widthWeight_sum_le_three hN).le

theorem scaleMatchedTarget_pos
    {s : ℝ} {m N : ℕ} (hN : 1 ≤ N) :
    0 < scaleMatchedTarget s m N := by
  unfold scaleMatchedTarget
  positivity

theorem natCast_le_scaleMatchedTarget (s : ℝ) (m N : ℕ) :
    (N : ℝ) ≤ scaleMatchedTarget s m N := by
  unfold scaleMatchedTarget
  exact le_add_of_nonneg_right (by positivity)

theorem scaleMatchedTarget_antitone
    {s t : ℝ} (hst : s ≤ t) (m N : ℕ) :
    scaleMatchedTarget t m N ≤ scaleMatchedTarget s m N := by
  unfold scaleMatchedTarget
  have hexp : -t * (m : ℝ) ≤ -s * (m : ℝ) :=
    mul_le_mul_of_nonneg_right (neg_le_neg hst) (Nat.cast_nonneg m)
  have hrpow : (10 : ℝ) ^ (-t * (m : ℝ)) ≤
      (10 : ℝ) ^ (-s * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  gcongr

theorem widthWeightedBadSet_subset_centeredDeviation
    {μ c s : ℝ} {Q0 m N : ℕ} (hN : 1 ≤ N) :
    widthWeightedBadSet μ c Q0 s m N ⊆
      {α | (decimalFrequency m : ℝ) ^ 2 * scaleMatchedTarget s m N ^ 2 ≤
        centeredWidthWeightedSquareFunction μ c Q0 m N α ^ 2} := by
  intro α hα
  let H : ℝ := decimalFrequency m
  let T : ℝ := scaleMatchedTarget s m N
  let W : ℝ := widthWeightedSquareFunction μ c Q0 m N α
  let M : ℝ := H * ∑ B ∈ (translatedCanonicalBlocks N).toFinset,
    ((blockOrderedDomain μ c Q0 m N B).card : ℝ) / widthWeight B
  have hH : 0 < H := by
    dsimp [H, decimalFrequency]
    positivity
  have hT : 0 < T := scaleMatchedTarget_pos hN
  have hmean := blockMeanWeight_sum_le μ c Q0 m N hN
  have hM : M ≤ 3 * H * T := by
    dsimp [M]
    have hNT := natCast_le_scaleMatchedTarget s m N
    nlinarith [mul_le_mul_of_nonneg_left hmean hH.le,
      mul_le_mul_of_nonneg_left hNT hH.le]
  have hW : 4 * H * T < W := by
    simpa [H, T, W] using hα.2
  have hcenter : H * T < W - M := by linarith
  have hcenter0 : 0 ≤ W - M := (mul_pos hH hT).le.trans hcenter.le
  change H ^ 2 * T ^ 2 ≤ (W - M) ^ 2
  calc
    H ^ 2 * T ^ 2 = (H * T) ^ 2 := by ring
    _ ≤ (W - M) ^ 2 :=
      (sq_le_sq₀ (mul_pos hH hT).le hcenter0).2 hcenter.le

theorem widthWeighted_tail_estimate
    (μ c : ℝ) (Q0 : ℕ) (s : ℝ) (m N : ℕ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) :
    phaseMeasure.real (widthWeightedBadSet μ c Q0 s m N) ≤
      940452800 * Real.log (2 * N) /
        ((decimalFrequency m : ℝ) *
          (1 + (N : ℝ) * (10 : ℝ) ^ (-s * (m : ℝ))) ^ 2) := by
  let H : ℝ := decimalFrequency m
  let T : ℝ := scaleMatchedTarget s m N
  let ε : ℝ := H ^ 2 * T ^ 2
  let deviation : Set ℝ :=
    {α | ε ≤ centeredWidthWeightedSquareFunction μ c Q0 m N α ^ 2}
  have hH : 0 < H := by
    dsimp [H, decimalFrequency]
    positivity
  have hT : 0 < T := scaleMatchedTarget_pos hN
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hsubset : widthWeightedBadSet μ c Q0 s m N ⊆ deviation := by
    simpa [deviation, ε, H, T] using
      (widthWeightedBadSet_subset_centeredDeviation
        (μ := μ) (c := c) (s := s) (Q0 := Q0) (m := m) (N := N) hN)
  have hint : Integrable
      (fun α => centeredWidthWeightedSquareFunction μ c Q0 m N α ^ 2)
        phaseMeasure := by
    rw [phaseMeasure]
    exact ((continuous_centeredWidthWeightedSquareFunction μ c Q0 m N).pow 2).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  have hmarkov : ε * phaseMeasure.real deviation ≤
      ∫ α, centeredWidthWeightedSquareFunction μ c Q0 m N α ^ 2
        ∂phaseMeasure :=
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all phaseMeasure fun α => sq_nonneg
        (centeredWidthWeightedSquareFunction μ c Q0 m N α)) hint ε
  have hmono : phaseMeasure.real (widthWeightedBadSet μ c Q0 s m N) ≤
      phaseMeasure.real deviation := measureReal_mono hsubset
  have hvariance := integral_centeredWidthWeightedSquareFunction_sq_le
    μ c Q0 m N hm hN
  have hscaled : ε * phaseMeasure.real (widthWeightedBadSet μ c Q0 s m N) ≤
      940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N) := by
    calc
      ε * phaseMeasure.real (widthWeightedBadSet μ c Q0 s m N) ≤
          ε * phaseMeasure.real deviation := mul_le_mul_of_nonneg_left hmono hε.le
      _ ≤ ∫ α, centeredWidthWeightedSquareFunction μ c Q0 m N α ^ 2
          ∂phaseMeasure := hmarkov
      _ ≤ 940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N) := by
        simpa [H] using hvariance
  have hraw : phaseMeasure.real (widthWeightedBadSet μ c Q0 s m N) ≤
      (940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N)) / ε :=
    (le_div_iff₀ hε).2 (by simpa [mul_comm] using hscaled)
  calc
    phaseMeasure.real (widthWeightedBadSet μ c Q0 s m N) ≤
        (940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N)) / ε := hraw
    _ = 940452800 * Real.log (2 * N) /
        ((decimalFrequency m : ℝ) *
          (1 + (N : ℝ) * (10 : ℝ) ^ (-s * (m : ℝ))) ^ 2) := by
      dsimp [ε, H, T]
      unfold scaleMatchedTarget
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < N))
      field_simp [hNR, show (decimalFrequency m : ℝ) ≠ 0 by positivity,
        show 1 + (N : ℝ) * (10 : ℝ) ^ (-s * (m : ℝ)) ≠ 0 by positivity]

theorem summable_widthWeighted_tail_majorant
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Summable (fun z : ℕ × ℕ =>
      (940452800 : ℝ) * Real.log (2 * ((z.2 + 1 : ℕ) : ℝ)) /
        ((10 : ℝ) ^ (z.1 + 1) *
          (1 + ((z.2 + 1 : ℕ) : ℝ) *
            (10 : ℝ) ^ (-s * ((z.1 + 1 : ℕ) : ℝ))) ^ 2)) := by
  let ε : ℝ := (1 - s) / 4
  let p : ℝ := 1 + ε
  let r : ℝ := p + ε
  let q : ℝ := (10 : ℝ) ^ (s * r - 1)
  let C : ℝ := 940452800 * (2 : ℝ) ^ ε / ε
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hp1 : 1 < p := by
    dsimp [p]
    linarith
  have hp0 : 0 ≤ p := hp1.le.trans' zero_le_one
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith
  have hr2 : r ≤ 2 := by
    dsimp [r, p, ε]
    linarith
  have hsr : s * r < 1 := by
    dsimp [r, p, ε]
    nlinarith [mul_pos hs0 (sub_pos.mpr hs1)]
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsr)
  have hqm : Summable (fun m : ℕ => q ^ (m + 1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq0 hq1)
  have hm : Summable (fun m : ℕ =>
      C * (10 : ℝ) ^ ((s * r - 1) * ((m + 1 : ℕ) : ℝ))) := by
    apply (hqm.mul_left C).congr
    intro m
    rw [show q = (10 : ℝ) ^ (s * r - 1) by rfl,
      ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hn : Summable (fun N : ℕ =>
      1 / (((N + 1 : ℕ) : ℝ) ^ p)) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff
        (f := fun n : ℕ => 1 / (n : ℝ) ^ p) 1).2
        (Real.summable_one_div_nat_rpow.mpr hp1)
  have hprod : Summable (fun z : ℕ × ℕ =>
      (C * (10 : ℝ) ^
        ((s * r - 1) * ((z.1 + 1 : ℕ) : ℝ))) *
          (1 / (((z.2 + 1 : ℕ) : ℝ) ^ p))) :=
    hm.mul_of_nonneg hn (fun _ => by positivity) (fun _ => by positivity)
  apply hprod.of_nonneg_of_le
    (fun z => div_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ 2 * (z.2 + 1) by omega)))) (by positivity))
  intro z
  let M : ℕ := z.1 + 1
  let K : ℕ := z.2 + 1
  let a : ℝ := (10 : ℝ) ^ (-s * (M : ℝ))
  let x : ℝ := (K : ℝ) * a
  have hK : 0 < (K : ℝ) := by exact_mod_cast Nat.succ_pos z.2
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hx : 0 ≤ x := (mul_pos hK ha).le
  have hxr : x ^ r ≤ (1 + x) ^ 2 := by
    calc
      x ^ r ≤ (1 + x) ^ r := Real.rpow_le_rpow hx (by linarith) hr0
      _ ≤ (1 + x) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hr2
      _ = (1 + x) ^ 2 := Real.rpow_natCast _ 2
  have hlog : Real.log (2 * (K : ℝ)) ≤
      (2 : ℝ) ^ ε * (K : ℝ) ^ ε / ε := by
    calc
      Real.log (2 * (K : ℝ)) ≤ (2 * (K : ℝ)) ^ ε / ε :=
        Real.log_le_rpow_div (by positivity) hε
      _ = (2 : ℝ) ^ ε * (K : ℝ) ^ ε / ε := by
        rw [Real.mul_rpow (by positivity) hK.le]
  have htenM : 0 < (10 : ℝ) ^ M := by positivity
  have hden : (10 : ℝ) ^ M * x ^ r ≤
      (10 : ℝ) ^ M * (1 + x) ^ 2 :=
    mul_le_mul_of_nonneg_left hxr htenM.le
  have hfirst :
      (940452800 : ℝ) * Real.log (2 * (K : ℝ)) /
          ((10 : ℝ) ^ M * (1 + x) ^ 2) ≤
        C * (K : ℝ) ^ ε /
          ((10 : ℝ) ^ M * x ^ r) := by
    have hnum : (940452800 : ℝ) * Real.log (2 * (K : ℝ)) ≤
        C * (K : ℝ) ^ ε := by
      calc
        (940452800 : ℝ) * Real.log (2 * (K : ℝ)) ≤
            940452800 * ((2 : ℝ) ^ ε * (K : ℝ) ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog (by norm_num)
        _ = C * (K : ℝ) ^ ε := by
          dsimp [C]
          ring
    calc
      (940452800 : ℝ) * Real.log (2 * (K : ℝ)) /
          ((10 : ℝ) ^ M * (1 + x) ^ 2) ≤
        (C * (K : ℝ) ^ ε) /
          ((10 : ℝ) ^ M * (1 + x) ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ C * (K : ℝ) ^ ε / ((10 : ℝ) ^ M * x ^ r) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  change (940452800 : ℝ) * Real.log (2 * (K : ℝ)) /
      ((10 : ℝ) ^ M * (1 + x) ^ 2) ≤ _
  refine hfirst.trans_eq ?_
  dsimp [x]
  rw [Real.mul_rpow hK.le ha.le]
  dsimp [a]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)
    (-s * (M : ℝ)) r]
  have hcombine :
      (10 : ℝ) ^ M *
          ((K : ℝ) ^ r * (10 : ℝ) ^ (-s * (M : ℝ) * r)) =
        (K : ℝ) ^ r *
          (10 : ℝ) ^ ((M : ℝ) + (-s * (M : ℝ) * r)) := by
    rw [← Real.rpow_natCast, Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
    ring
  rw [hcombine]
  have heq : (s * r - 1) * (M : ℝ) =
      -((M : ℝ) + (-s * (M : ℝ) * r)) := by ring
  have hKr : (K : ℝ) ^ r = (K : ℝ) ^ p * (K : ℝ) ^ ε := by
    rw [show r = p + ε by rfl, Real.rpow_add hK]
  rw [heq, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10), hKr]
  field_simp [ne_of_gt hK, ne_of_gt (Real.rpow_pos_of_pos hK p),
    ne_of_gt (Real.rpow_pos_of_pos hK ε)]
  simp [K]

/-- The exact exceptional set is null for each fixed exponent. -/
theorem phaseMeasure_widthWeightedTailExceptionalSet_eq_zero
    (μ c : ℝ) (Q0 : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    phaseMeasure (widthWeightedTailExceptionalSet μ c Q0 s) = 0 := by
  have hreal : Summable (fun z : ℕ × ℕ =>
      phaseMeasure.real
        (widthWeightedBadSet μ c Q0 s (z.1 + 1) (z.2 + 1))) := by
    apply (summable_widthWeighted_tail_majorant s hs0 hs1).of_nonneg_of_le
      (fun _ => measureReal_nonneg)
    intro z
    simpa [decimalFrequency, Nat.cast_pow, Nat.cast_add] using
      widthWeighted_tail_estimate μ c Q0 s (z.1 + 1) (z.2 + 1)
        (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero _))
        (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero _))
  have heq :
      (fun z : ℕ × ℕ => ENNReal.ofReal
        (phaseMeasure.real
          (widthWeightedBadSet μ c Q0 s (z.1 + 1) (z.2 + 1)))) =
      (fun z : ℕ × ℕ => phaseMeasure
        (widthWeightedBadSet μ c Q0 s (z.1 + 1) (z.2 + 1))) := by
    funext z
    exact ofReal_measureReal
  have hsum :
      (∑' z : ℕ × ℕ,
        phaseMeasure
          (widthWeightedBadSet μ c Q0 s (z.1 + 1) (z.2 + 1))) ≠ ∞ := by
    rw [← heq]
    exact hreal.tsum_ofReal_ne_top
  have hfinite : ∀ᵐ α ∂phaseMeasure,
      {z : ℕ × ℕ |
        α ∈ widthWeightedBadSet μ c Q0 s (z.1 + 1) (z.2 + 1)}.Finite :=
    ae_finite_setOf_mem hsum
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hfinite] with α hα
  change ¬{z : ℕ × ℕ |
    α ∈ widthWeightedBadSet μ c Q0 s (z.1 + 1) (z.2 + 1)}.Infinite
  exact fun hinfinite => hinfinite hα

/-- The explicit countable union of rational-exponent exceptional tails is
null for the restricted Lebesgue probability measure. -/
theorem phaseMeasure_widthWeightedExceptionalSet_eq_zero
    (μ c : ℝ) (Q0 : ℕ) :
    phaseMeasure (widthWeightedExceptionalSet μ c Q0) = 0 := by
  rw [widthWeightedExceptionalSet]
  apply measure_iUnion_null
  intro s
  by_cases hs : 0 < s ∧ s < 1
  · rw [if_pos hs]
    exact phaseMeasure_widthWeightedTailExceptionalSet_eq_zero
      μ c Q0 (s : ℝ) (by exact_mod_cast hs.1) (by exact_mod_cast hs.2)
  · simp [hs]

/-- The chosen set is measurable, lies in `[0,1)`, has full restricted
Lebesgue measure, and avoids every rational exceptional tail. -/
theorem phaseMeasure_widthWeightedFullMeasureSet
    (μ c : ℝ) (Q0 : ℕ) :
    MeasurableSet (widthWeightedFullMeasureSet μ c Q0) ∧
    phaseMeasure (widthWeightedFullMeasureSet μ c Q0) = 1 ∧
    widthWeightedFullMeasureSet μ c Q0 ⊆ Set.Ico (0 : ℝ) 1 := by
  refine ⟨measurableSet_Ico.diff (measurableSet_toMeasurable _ _), ?_, Set.diff_subset⟩
  rw [widthWeightedFullMeasureSet, measure_diff_null]
  · simp [phaseMeasure]
  · rw [measure_toMeasurable]
    exact phaseMeasure_widthWeightedExceptionalSet_eq_zero μ c Q0

theorem finite_widthWeighted_violations_uniform_bound
    (μ c : ℝ) (Q0 : ℕ) (t : ℝ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hfinite : {z : ℕ × ℕ |
      α ∈ widthWeightedBadSet μ c Q0 t (z.1 + 1) (z.2 + 1)}.Finite) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        widthWeightedSquareFunction μ c Q0 m N α ≤
          A * (decimalFrequency m : ℝ) * scaleMatchedTarget t m N := by
  let E : Set (ℕ × ℕ) := {z : ℕ × ℕ |
    α ∈ widthWeightedBadSet μ c Q0 t (z.1 + 1) (z.2 + 1)}
  have hE : E.Finite := by simpa [E] using hfinite
  let ratio : ℕ × ℕ → ℝ := fun z =>
    widthWeightedSquareFunction μ c Q0 (z.1 + 1) (z.2 + 1) α /
      ((decimalFrequency (z.1 + 1) : ℝ) *
        scaleMatchedTarget t (z.1 + 1) (z.2 + 1))
  let A : ℝ := 4 + ∑ z ∈ hE.toFinset, ratio z
  have hratio_nonneg : ∀ z, 0 ≤ ratio z := by
    intro z
    dsimp [ratio]
    exact div_nonneg
      (widthWeightedSquareFunction_nonneg μ c Q0 (z.1 + 1) (z.2 + 1) α)
      (mul_nonneg (by positivity)
        (scaleMatchedTarget_pos
          (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero _))).le)
  have hsum_nonneg : 0 ≤ ∑ z ∈ hE.toFinset, ratio z :=
    Finset.sum_nonneg fun z _ => hratio_nonneg z
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith
  have hfourA : (4 : ℝ) ≤ A := by
    dsimp [A]
    linarith
  refine ⟨A, hA, ?_⟩
  intro m N hm hN
  let z : ℕ × ℕ := (m - 1, N - 1)
  have hzm : z.1 + 1 = m := by
    dsimp [z]
    omega
  have hzN : z.2 + 1 = N := by
    dsimp [z]
    omega
  have hden : 0 < (decimalFrequency m : ℝ) * scaleMatchedTarget t m N :=
    mul_pos (by unfold decimalFrequency; positivity) (scaleMatchedTarget_pos hN)
  by_cases hzbad : z ∈ E
  · have hzmem : z ∈ hE.toFinset := by simpa using hzbad
    have hsingle : ratio z ≤ ∑ w ∈ hE.toFinset, ratio w :=
      Finset.single_le_sum (f := ratio) (fun w _ => hratio_nonneg w) hzmem
    have hratioA : ratio z ≤ A := by
      dsimp [A]
      linarith
    have hdiv : widthWeightedSquareFunction μ c Q0 m N α /
        ((decimalFrequency m : ℝ) * scaleMatchedTarget t m N) ≤ A := by
      simpa [ratio, hzm, hzN] using hratioA
    simpa [mul_assoc] using (div_le_iff₀ hden).mp hdiv
  · have hnotBad : α ∉ widthWeightedBadSet μ c Q0 t m N := by
      simpa [E, hzm, hzN] using hzbad
    have hthreshold : widthWeightedSquareFunction μ c Q0 m N α ≤
        4 * (decimalFrequency m : ℝ) * scaleMatchedTarget t m N := by
      exact le_of_not_gt fun hgt => hnotBad ⟨hα, hgt⟩
    calc
      widthWeightedSquareFunction μ c Q0 m N α ≤
          4 * (decimalFrequency m : ℝ) * scaleMatchedTarget t m N := hthreshold
      _ ≤ A * (decimalFrequency m : ℝ) * scaleMatchedTarget t m N := by
        gcongr
        exact (scaleMatchedTarget_pos hN).le

theorem sum_int_Icc_eq_sum_nat_Icc
    (H : ℕ) (f : ℤ → ℝ) :
    (∑ h ∈ Finset.Icc (1 : ℤ) (H : ℤ), f h) =
      ∑ h ∈ Finset.Icc 1 H, f (h : ℤ) := by
  have heq : (Finset.Icc 1 H).map Nat.castEmbedding =
      Finset.Icc (1 : ℤ) (H : ℤ) := by
    ext z
    simp only [Finset.mem_map, Finset.mem_Icc, Nat.castEmbedding_apply]
    constructor
    · rintro ⟨n, ⟨hn1, hnH⟩, rfl⟩
      exact ⟨by exact_mod_cast hn1, by exact_mod_cast hnH⟩
    · intro hz
      have hz0 : 0 ≤ z := (by omega : (0 : ℤ) ≤ z)
      refine ⟨z.toNat, ⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast (show (1 : ℤ) ≤ (z.toNat : ℤ) by
          simpa [Int.toNat_of_nonneg hz0] using hz.1)
      · exact_mod_cast (show (z.toNat : ℤ) ≤ (H : ℤ) by
          simpa [Int.toNat_of_nonneg hz0] using hz.2)
      · exact Int.toNat_of_nonneg hz0
  rw [← heq, Finset.sum_map]
  simp [Nat.castEmbedding_apply]

/-- Main T31 sibling. The full-measure set may depend on `μ,c,Q0`; on that
set every real `0<s<1` receives one constant before all positive `m,N`.
This statement deliberately contains no fixed-`pi` or C1 conclusion. -/
theorem almostEverywhere_widthWeightedSquareFunction_sibling
    (μ c : ℝ) (Q0 : ℕ) :
    MeasurableSet (widthWeightedFullMeasureSet μ c Q0) ∧
    phaseMeasure (widthWeightedFullMeasureSet μ c Q0) = 1 ∧
    widthWeightedFullMeasureSet μ c Q0 ⊆ Set.Ico (0 : ℝ) 1 ∧
    ∀ α ∈ widthWeightedFullMeasureSet μ c Q0,
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ A : ℝ, 0 ≤ A ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            (((canonicalDyadicPartition N).map fun B =>
              (∑ h ∈ Finset.Icc 1 (10 ^ m),
                ‖cutoffFourierSum μ c Q0 m B.finish (h : ℤ) α -
                  cutoffFourierSum μ c Q0 m B.start (h : ℤ) α‖ ^ 2) /
                Real.sqrt ((B.finish : ℝ) ^ 2 -
                  (B.start : ℝ) ^ 2)).sum) ≤
              A * (10 ^ m : ℕ) *
                ((N : ℝ) + (N : ℝ) ^ 2 *
                  (10 : ℝ) ^ (-s * (m : ℝ))) := by
  obtain ⟨hmeas, hmeasure, hsubset⟩ :=
    phaseMeasure_widthWeightedFullMeasureSet μ c Q0
  refine ⟨hmeas, hmeasure, hsubset, ?_⟩
  intro α hα s hs0 hs1
  obtain ⟨t : ℚ, hst, ht1⟩ := exists_rat_btwn hs1
  have ht0 : (0 : ℝ) < (t : ℝ) := hs0.trans hst
  have htRat0 : (0 : ℚ) < t := by exact_mod_cast ht0
  have htRat1 : t < (1 : ℚ) := by exact_mod_cast ht1
  have hnotAll : α ∉ widthWeightedExceptionalSet μ c Q0 := by
    intro hmem
    exact hα.2 (subset_toMeasurable phaseMeasure _ hmem)
  have hnotTail : α ∉ widthWeightedTailExceptionalSet μ c Q0 (t : ℝ) := by
    intro hmem
    apply hnotAll
    rw [widthWeightedExceptionalSet]
    refine Set.mem_iUnion.2 ⟨t, ?_⟩
    simpa [htRat0, htRat1] using hmem
  have hfinite : {z : ℕ × ℕ |
      α ∈ widthWeightedBadSet μ c Q0 (t : ℝ)
        (z.1 + 1) (z.2 + 1)}.Finite := by
    by_contra hnotFinite
    apply hnotTail
    exact hnotFinite
  obtain ⟨A, hA, hbound⟩ :=
    finite_widthWeighted_violations_uniform_bound μ c Q0 (t : ℝ) α
      (hsubset hα) hfinite
  refine ⟨A, hA, ?_⟩
  intro m N hm hN
  have hfinal : widthWeightedSquareFunction μ c Q0 m N α ≤
      A * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
    calc
      widthWeightedSquareFunction μ c Q0 m N α ≤
          A * (decimalFrequency m : ℝ) * scaleMatchedTarget (t : ℝ) m N :=
        hbound m N hm hN
      _ ≤ A * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
        gcongr
        exact scaleMatchedTarget_antitone hst.le m N
  have hleft :
      (((canonicalDyadicPartition N).map fun B =>
        (∑ h ∈ Finset.Icc (1 : ℤ) (10 ^ m : ℤ),
          ‖cutoffFourierSum μ c Q0 m B.finish h α -
            cutoffFourierSum μ c Q0 m B.start h α‖ ^ 2) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum) =
        widthWeightedSquareFunction μ c Q0 m N α := by
    unfold widthWeightedSquareFunction translatedCanonicalBlocks blockSquaredEnergy
      canonicalBlockVector inclusiveFrequencies widthWeight
    apply congrArg List.sum
    apply List.map_congr_left
    intro B hB
    congr 1
    exact sum_int_Icc_eq_sum_nat_Icc (10 ^ m) (fun h =>
      ‖cutoffFourierSum μ c Q0 m B.finish h α -
        cutoffFourierSum μ c Q0 m B.start h α‖ ^ 2)
  rw [hleft]
  simpa [decimalFrequency, scaleMatchedTarget] using hfinal

/-- Literal almost-everywhere form of the T31 sibling. The theorem displays
the null exceptional set and the `∀ᵐ α, ∀ s, ∃ A, ∀ m,N` quantifier order;
the exact block domain and weights are exposed by the preceding main theorem. -/
theorem almostEverywhere_widthWeightedSquareFunction_ae
    (μ c : ℝ) (Q0 : ℕ) :
    phaseMeasure (widthWeightedExceptionalSet μ c Q0) = 0 ∧
    ∀ᵐ α ∂phaseMeasure,
      α ∈ widthWeightedFullMeasureSet μ c Q0 ∧
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ A : ℝ, 0 ≤ A ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            (((canonicalDyadicPartition N).map fun B =>
              (∑ h ∈ Finset.Icc 1 (10 ^ m),
                ‖cutoffFourierSum μ c Q0 m B.finish (h : ℤ) α -
                  cutoffFourierSum μ c Q0 m B.start (h : ℤ) α‖ ^ 2) /
                Real.sqrt ((B.finish : ℝ) ^ 2 -
                  (B.start : ℝ) ^ 2)).sum) ≤
              A * (10 ^ m : ℕ) *
                ((N : ℝ) + (N : ℝ) ^ 2 *
                  (10 : ℝ) ^ (-s * (m : ℝ))) := by
  have hmain := almostEverywhere_widthWeightedSquareFunction_sibling μ c Q0
  have hmem : ∀ᵐ α ∂phaseMeasure,
      α ∈ widthWeightedFullMeasureSet μ c Q0 := by
    apply (ae_mem_iff_measure_eq hmain.1.nullMeasurableSet).2
    rw [hmain.2.1, phaseMeasure_univ]
  refine ⟨phaseMeasure_widthWeightedExceptionalSet_eq_zero μ c Q0, ?_⟩
  filter_upwards [hmem] with α hα
  refine ⟨hα, ?_⟩
  intro s hs0 hs1
  obtain ⟨A, hA, hbound⟩ := hmain.2.2.2 α hα s hs0 hs1
  refine ⟨A, hA, ?_⟩
  intro m N hm hN
  exact hbound m N hm hN

end Theory.PiDigits.LongLagBlockCollisionDecay.T31

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.crossBlockWeightedGCD_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.crossBlockWeightedGCD_le_explicit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.integral_centeredWidthWeightedSquareFunction_sq_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.phaseMeasure_widthWeightedTailExceptionalSet_eq_zero
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.phaseMeasure_widthWeightedFullMeasureSet
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.almostEverywhere_widthWeightedSquareFunction_sibling
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T31.almostEverywhere_widthWeightedSquareFunction_ae
