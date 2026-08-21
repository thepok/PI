import TheoryLib.PiLongLagBlockCollisionDecay.T59T59CompleteSignedPrimitivePartition

/-!
# T60: the unmatched-defect Laurent polynomial

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module concerns only the residual sparse-Fourier sibling A12. It imports
T59's exact defect without restating its partition. It proves no estimate at
`pi`, no width-weighted square-function bound, C2, C1, or canonical collision
estimate.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T60

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T49
open Theory.PiDigits.LongLagBlockCollisionDecay.T56
open Theory.PiDigits.LongLagBlockCollisionDecay.T59

/-- A labeled term retains the positive T59 defect record, its swap Boolean,
and one literal inclusive frequency. -/
abbrev DefectCharacterRecord := (PrimitiveRecordPair × Bool) × ℕ

/-- Every literal T59 unmatched-defect record, both signed orientations, and
all ten inclusive frequencies. No image or deduplication is taken. -/
def defectCharacterDomain (Q0 t : ℕ) : Finset DefectCharacterRecord :=
  (unmatchedDefect Q0 t ×ˢ (Finset.univ : Finset Bool)) ×ˢ
    Finset.Icc 1 10

/-- The ordered signed record pair represented by one labeled term. -/
def defectOrientedPair (x : DefectCharacterRecord) : PrimitiveRecordPair :=
  orientPositiveDifference (x.1.2, x.1.1)

/-- The exact integer Fourier character of one record-frequency term. -/
def defectCharacterExponent (x : DefectCharacterRecord) : ℤ :=
  (x.2 : ℤ) *
    (signedDecimalFrequency (defectOrientedPair x).1 -
      signedDecimalFrequency (defectOrientedPair x).2)

/-- The literal T29 block weight attached to every term. -/
def defectTermWeight (t : ℕ) : ℝ :=
  1 / widthWeight (boxBlock t)

/-- T59's full formal defect as a real-coefficient Laurent polynomial, encoded
as the group algebra `ℤ →₀ ℝ`. -/
def defectLaurent (Q0 t : ℕ) : ℤ →₀ ℝ :=
  ∑ x ∈ defectCharacterDomain Q0 t,
    Finsupp.single (defectCharacterExponent x) (defectTermWeight t)

/-- The requested `D_t`; the later `defectLaurent_independent_Q0` theorem
shows that choosing onset parameter zero loses no T59 record at `m = 1`. -/
def D (t : ℕ) : ℤ →₀ ℝ := defectLaurent 0 t

/-- Coefficient notation before eliminating the inessential `Q0`. -/
def defectCoefficient (Q0 t : ℕ) (n : ℤ) : ℝ :=
  defectLaurent Q0 t n

/-- Coefficients of the requested polynomial `D_t`. -/
def a (t : ℕ) (n : ℤ) : ℝ := D t n

/-- Full membership audit: the T59 primitive domain, both selected-value
exclusions, and the inclusive endpoints `1` and `10` are all explicit. -/
theorem mem_defectCharacterDomain_iff
    (Q0 t : ℕ) (x : DefectCharacterRecord) :
    x ∈ defectCharacterDomain Q0 t ↔
      x.1.1 ∈ primitiveRecordDomain 8 1 Q0 1
        (boxEndpoint t) (boxBlock t) ∧
      (∀ y ∈ boxQuartetDomain t,
        blockDifferenceValue x.1.1 ≠ residueOneValue y ∧
        blockDifferenceValue x.1.1 ≠ residueNineValue y) ∧
      1 ≤ x.2 ∧ x.2 ≤ 10 := by
  rw [defectCharacterDomain, Finset.mem_product, Finset.mem_product,
    mem_unmatchedDefect_iff]
  simp only [Finset.mem_univ, Finset.mem_Icc]
  tauto

/-- Every labeled term lies in the unique literal T59
valuation-value-record-orientation fiber indexed by its own data. -/
theorem defectCharacter_mem_exact_T59_fiber
    {Q0 t : ℕ} {x : DefectCharacterRecord}
    (hx : x ∈ defectCharacterDomain Q0 t) :
    x.1.1 ∈ defectOrientationFiber Q0 t
      (tenValuation (blockDifferenceValue x.1.1))
      (blockDifferenceValue x.1.1) (recordOrientation x.1.1) := by
  rw [mem_defectOrientationFiber_iff]
  have h := (mem_defectCharacterDomain_iff Q0 t x).mp hx
  exact ⟨h.1, h.2.1, rfl, rfl, rfl⟩

/-- On the exact domain, the character visibly retains T59's swap sign,
literal frequency, and positive primitive value. -/
theorem defectCharacterExponent_eq
    {Q0 t : ℕ} {x : DefectCharacterRecord}
    (hx : x ∈ defectCharacterDomain Q0 t) :
    defectCharacterExponent x =
      phaseOrientationSign x.1.2 * (x.2 : ℤ) *
        (blockDifferenceValue x.1.1 : ℤ) := by
  unfold defectCharacterExponent defectOrientedPair
  rw [orientPositiveDifference_sign
    ((mem_defectCharacterDomain_iff Q0 t x).mp hx).1]
  ring

/-- Coefficientwise expansion: every contribution is present with the exact
block weight, and only terms with the displayed integer character contribute. -/
theorem defectCoefficient_eq_filter_sum (Q0 t : ℕ) (n : ℤ) :
    defectCoefficient Q0 t n =
      ∑ x ∈ (defectCharacterDomain Q0 t).filter
        (fun x => defectCharacterExponent x = n),
          (fun _ => defectTermWeight t) x := by
  classical
  unfold defectCoefficient defectLaurent
  change (Finsupp.applyAddHom n : (ℤ →₀ ℝ) →+ ℝ)
    (∑ x ∈ defectCharacterDomain Q0 t,
      Finsupp.single (defectCharacterExponent x) (defectTermWeight t)) = _
  rw [map_sum (Finsupp.applyAddHom n : (ℤ →₀ ℝ) →+ ℝ)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  change (Finsupp.single (defectCharacterExponent x) (defectTermWeight t) :
    ℤ →₀ ℝ) n =
      if defectCharacterExponent x = n then defectTermWeight t else 0
  exact Finsupp.single_apply

/-- The largest orbit exponent below `N = 4*2^t+1`. -/
def topExponent (t : ℕ) : ℕ := 4 * boxLength t

/-- The largest positive signed record in the one-block domain. -/
def topRecord (t : ℕ) : OrderedLongPair :=
  coordinateRecord (topExponent t) 0

/-- The smallest negative signed record in the one-block domain. -/
def bottomRecord (t : ℕ) : OrderedLongPair :=
  coordinateRecord 0 (topExponent t)

/-- The extremal positive primitive record pair. -/
def topDefectPair (t : ℕ) : PrimitiveRecordPair :=
  (topRecord t, bottomRecord t)

/-- Its exact positive primitive difference. -/
def topDefectValue (t : ℕ) : ℕ :=
  2 * (10 ^ topExponent t - 1)

/-- The explicit surviving Fourier mode, valid from onset `t = 0`. -/
def nMax (t : ℕ) : ℤ := 10 * (topDefectValue t : ℤ)

/-- Closed formula for the surviving mode at every dyadic exponent. -/
theorem nMax_formula (t : ℕ) :
    nMax t = 20 * ((10 : ℤ) ^ (4 * 2 ^ t) - 1) := by
  unfold nMax topDefectValue topExponent boxLength
  push_cast [one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 10)]
  ring

/-- The only labeled contributor proposed for `nMax t`. -/
def topCharacterRecord (t : ℕ) : DefectCharacterRecord :=
  ((topDefectPair t, false), 10)

/-- Exact T49 membership of the extremal pair, including both half-open block
record conditions, strict positive orientation, and noncancellation. -/
theorem topDefectPair_mem_primitive (Q0 t : ℕ) :
    topDefectPair t ∈ primitiveRecordDomain 8 1 Q0 1
      (boxEndpoint t) (boxBlock t) := by
  classical
  have hk : 0 < topExponent t := by
    simp [topExponent, boxLength]
  have htop : topRecord t = (true, ⟨topExponent t, 0⟩) := by
    simp [topRecord, coordinateRecord, hk]
  have hbottom : bottomRecord t = (false, ⟨topExponent t, 0⟩) := by
    simp [bottomRecord, coordinateRecord]
  have hN : boxEndpoint t = topExponent t + 1 := by
    simp [boxEndpoint, topExponent]
  have hgap : 0 < 10 ^ topExponent t - 1 := by
    have : 1 < 10 ^ topExponent t :=
      one_lt_pow₀ (by norm_num) hk.ne'
    omega
  rw [topDefectPair, htop, hbottom]
  unfold primitiveRecordDomain primitiveBlockDifferenceDomain
  rw [Finset.mem_filter]
  constructor
  · rw [mem_blockPositiveDifferenceDomain_iff]
    have hexcl := not_arithmeticExcluded_eight_one_at_one Q0 0
      (topExponent t) hk
    have hend := boxBlock_endpoints t
    simp only [AdmissibleOrderedFrequency, frequencyEndpoint,
      signedDecimalFrequency, positiveDecimalFrequency,
      ↓reduceIte, Bool.false_eq_true, Nat.zero_add]
    rw [hend.1, hend.2, hN]
    exact ⟨⟨hk, by omega, hexcl⟩, by omega, by omega, by omega,
      ⟨hk, by omega, hexcl⟩, by omega, by omega, by omega, by omega⟩
  · unfold Noncancelling
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [blockDifferenceExponent, orderedFirst, orderedSecond,
        fourTokenSign] at hij ⊢ <;> omega

/-- The extremal pair is outside both complete T56 selected value images. -/
theorem topDefectPair_mem_unmatched (Q0 t : ℕ) :
    topDefectPair t ∈ unmatchedDefect Q0 t := by
  classical
  rw [unmatchedDefect, Finset.mem_sdiff]
  refine ⟨topDefectPair_mem_primitive Q0 t, ?_⟩
  intro hsel
  rw [selectedRecordDomain, Finset.mem_union] at hsel
  rcases hsel with hsel | hsel
  · obtain ⟨x, hx, row, heq⟩ :=
      residueOneRecordDomain_mem_iff.mp hsel
    have hbox := mem_boxQuartetDomain_iff.mp hx
    cases row <;>
      simp only [topDefectPair, topRecord, bottomRecord, residueOnePair,
        Prod.mk.injEq, coordinateRecord_eq_iff] at heq <;> omega
  · obtain ⟨x, hx, row, heq⟩ :=
      residueNineRecordDomain_mem_iff.mp hsel
    have hbox := mem_boxQuartetDomain_iff.mp hx
    cases row <;>
      simp only [topDefectPair, topRecord, bottomRecord, residueNinePair,
        Prod.mk.injEq, coordinateRecord_eq_iff] at heq <;> omega

/-- Exact value of the extremal positive pair. -/
theorem topDefectPair_value (t : ℕ) :
    blockDifferenceValue (topDefectPair t) = topDefectValue t := by
  have hk : 0 < topExponent t := by
    simp [topExponent, boxLength]
  have htop : topRecord t = (true, ⟨topExponent t, 0⟩) := by
    simp [topRecord, coordinateRecord, hk]
  have hbottom : bottomRecord t = (false, ⟨topExponent t, 0⟩) := by
    simp [bottomRecord, coordinateRecord]
  have hp := primitiveBlockDifferenceDomain_subset
    (topDefectPair_mem_primitive 0 t)
  have hcast := blockPositiveDifferenceValue_cast hp
  simp [topDefectPair, htop, hbottom, signedDecimalFrequency,
    positiveDecimalFrequency] at hcast
  rw [topDefectPair, htop, hbottom]
  apply Nat.cast_injective (R := ℤ)
  rw [hcast]
  unfold topDefectValue
  push_cast [one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ))]
  ring

/-- Every primitive value in the exact one-block domain is at most the
displayed extremal value. -/
theorem blockDifferenceValue_le_top
    {Q0 t : ℕ} {p : PrimitiveRecordPair}
    (hp : p ∈ primitiveRecordDomain 8 1 Q0 1
      (boxEndpoint t) (boxBlock t)) :
    blockDifferenceValue p ≤ topDefectValue t := by
  have hpPos : p ∈ blockPositiveDifferenceDomain 8 1 Q0 1
      (boxEndpoint t) (boxBlock t) :=
    primitiveBlockDifferenceDomain_subset hp
  rcases (mem_blockPositiveDifferenceDomain_iff.mp hpPos) with
    ⟨hp1, hp1N, _, _, hp2, hp2N, _, _, _⟩
  have record_bounds {q : OrderedLongPair}
      (hq : AdmissibleOrderedFrequency 8 1 Q0 1 q)
      (hqN : frequencyEndpoint q.2 < boxEndpoint t) :
      -((10 : ℤ) ^ topExponent t - 1) ≤ signedDecimalFrequency q ∧
        signedDecimalFrequency q ≤ (10 : ℤ) ^ topExponent t - 1 := by
    have hqDom : q ∈ orderedLongPairDomain 8 1 Q0 1 (boxEndpoint t) :=
      mem_orderedLongPairDomain_iff_admissible_endpoint.mpr ⟨hq, hqN⟩
    have hcoords :=
      (mem_orderedLongPairDomain_eight_one_one_iff Q0
        (boxEndpoint t) q).mp hqDom
    have hendpoint : boxEndpoint t = topExponent t + 1 := by
      simp [boxEndpoint, topExponent]
    rw [hendpoint] at hcoords
    have hfirst : orderedFirst q ≤ topExponent t := by omega
    have hsecond : orderedSecond q ≤ topExponent t := by omega
    have hpowFirst : (10 : ℤ) ^ orderedFirst q ≤
        (10 : ℤ) ^ topExponent t := by
      exact_mod_cast
        (pow_le_pow_right' (by norm_num : 0 < (10 : ℕ)) hfirst)
    have hpowSecond : (10 : ℤ) ^ orderedSecond q ≤
        (10 : ℤ) ^ topExponent t := by
      exact_mod_cast
        (pow_le_pow_right' (by norm_num : 0 < (10 : ℕ)) hsecond)
    have hpowFirstOne : (1 : ℤ) ≤ (10 : ℤ) ^ orderedFirst q :=
      one_le_pow₀ (by norm_num)
    have hpowSecondOne : (1 : ℤ) ≤ (10 : ℤ) ^ orderedSecond q :=
      one_le_pow₀ (by norm_num)
    rw [signedDecimalFrequency_eq_orderedPhaseFrequency]
    unfold orderedPhaseFrequency
    constructor <;> omega
  have hp1Bounds := record_bounds hp1 hp1N
  have hp2Bounds := record_bounds hp2 hp2N
  have hcast := blockPositiveDifferenceValue_cast hpPos
  have htopCast : (topDefectValue t : ℤ) =
      2 * ((10 : ℤ) ^ topExponent t - 1) := by
    unfold topDefectValue
    push_cast [one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 10)]
    rfl
  have hz : (blockDifferenceValue p : ℤ) ≤
      (topDefectValue t : ℤ) := by
    rw [hcast, htopCast]
    omega
  exact_mod_cast hz

/-- Equality in the preceding bound exhaustively determines both records. -/
theorem blockDifferenceValue_eq_top_iff
    {Q0 t : ℕ} {p : PrimitiveRecordPair}
    (hp : p ∈ primitiveRecordDomain 8 1 Q0 1
      (boxEndpoint t) (boxBlock t)) :
    blockDifferenceValue p = topDefectValue t ↔ p = topDefectPair t := by
  have hpPos : p ∈ blockPositiveDifferenceDomain 8 1 Q0 1
      (boxEndpoint t) (boxBlock t) :=
    primitiveBlockDifferenceDomain_subset hp
  rcases (mem_blockPositiveDifferenceDomain_iff.mp hpPos) with
    ⟨hp1, hp1N, _, _, hp2, hp2N, _, _, _⟩
  have record_bounds {q : OrderedLongPair}
      (hq : AdmissibleOrderedFrequency 8 1 Q0 1 q)
      (hqN : frequencyEndpoint q.2 < boxEndpoint t) :
      -((10 : ℤ) ^ topExponent t - 1) ≤ signedDecimalFrequency q ∧
        signedDecimalFrequency q ≤ (10 : ℤ) ^ topExponent t - 1 := by
    have hqDom : q ∈ orderedLongPairDomain 8 1 Q0 1 (boxEndpoint t) :=
      mem_orderedLongPairDomain_iff_admissible_endpoint.mpr ⟨hq, hqN⟩
    have hcoords :=
      (mem_orderedLongPairDomain_eight_one_one_iff Q0
        (boxEndpoint t) q).mp hqDom
    have hendpoint : boxEndpoint t = topExponent t + 1 := by
      simp [boxEndpoint, topExponent]
    rw [hendpoint] at hcoords
    have hfirst : orderedFirst q ≤ topExponent t := by omega
    have hsecond : orderedSecond q ≤ topExponent t := by omega
    have hpowFirst : (10 : ℤ) ^ orderedFirst q ≤
        (10 : ℤ) ^ topExponent t := by
      exact_mod_cast
        (pow_le_pow_right' (by norm_num : 0 < (10 : ℕ)) hfirst)
    have hpowSecond : (10 : ℤ) ^ orderedSecond q ≤
        (10 : ℤ) ^ topExponent t := by
      exact_mod_cast
        (pow_le_pow_right' (by norm_num : 0 < (10 : ℕ)) hsecond)
    have hpowFirstOne : (1 : ℤ) ≤ (10 : ℤ) ^ orderedFirst q :=
      one_le_pow₀ (by norm_num)
    have hpowSecondOne : (1 : ℤ) ≤ (10 : ℤ) ^ orderedSecond q :=
      one_le_pow₀ (by norm_num)
    rw [signedDecimalFrequency_eq_orderedPhaseFrequency]
    unfold orderedPhaseFrequency
    constructor <;> omega
  have hp1Bounds := record_bounds hp1 hp1N
  have hp2Bounds := record_bounds hp2 hp2N
  have hcast := blockPositiveDifferenceValue_cast hpPos
  have htopCast : (topDefectValue t : ℤ) =
      2 * ((10 : ℤ) ^ topExponent t - 1) := by
    unfold topDefectValue
    push_cast [one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 10)]
    rfl
  constructor
  · intro heq
    have heqZ : (blockDifferenceValue p : ℤ) =
        (topDefectValue t : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) heq
    rw [hcast, htopCast] at heqZ
    have hp1eq : signedDecimalFrequency p.1 =
        (10 : ℤ) ^ topExponent t - 1 := by omega
    have hp2eq : signedDecimalFrequency p.2 =
        -((10 : ℤ) ^ topExponent t - 1) := by omega
    have hMpos : 0 < topExponent t := by
      simp [topExponent, boxLength]
    have htopFreq : signedDecimalFrequency (topRecord t) =
        (10 : ℤ) ^ topExponent t - 1 := by
      unfold topRecord
      simpa using
        (coordinateRecord_audit (by omega : topExponent t ≠ 0)).2.2
    have hbottomFreq : signedDecimalFrequency (bottomRecord t) =
        -((10 : ℤ) ^ topExponent t - 1) := by
      unfold bottomRecord
      have h := (coordinateRecord_audit
        (by omega : (0 : ℕ) ≠ topExponent t)).2.2
      simpa using h
    have htopPrim := topDefectPair_mem_primitive Q0 t
    have htopPos :
        topDefectPair t ∈ blockPositiveDifferenceDomain 8 1 Q0 1
          (boxEndpoint t) (boxBlock t) :=
      primitiveBlockDifferenceDomain_subset htopPrim
    rcases (mem_blockPositiveDifferenceDomain_iff.mp htopPos) with
      ⟨htop, _, _, _, hbottom, _, _, _, _⟩
    have hp1top : p.1 = topRecord t :=
      signedDecimalFrequency_injective_of_admissible hp1 htop
        (hp1eq.trans htopFreq.symm)
    have hp2bottom : p.2 = bottomRecord t :=
      signedDecimalFrequency_injective_of_admissible hp2 hbottom
        (hp2eq.trans hbottomFreq.symm)
    exact Prod.ext hp1top hp2bottom
  · intro heq
    subst p
    exact topDefectPair_value t

/-- Exhaustive fiber calculation: this singleton is every defect
record-orientation-frequency term, not a partial contributor list. -/
theorem nMax_fiber_eq_singleton (Q0 t : ℕ) :
    (defectCharacterDomain Q0 t).filter
        (fun x => defectCharacterExponent x = nMax t) =
      {topCharacterRecord t} := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hexp⟩
    rcases x with ⟨⟨p, b⟩, h⟩
    have hmem :=
      (mem_defectCharacterDomain_iff Q0 t ((p, b), h)).mp hx
    have hp := hmem.1
    have hh_le : h ≤ 10 := hmem.2.2.2
    have hd_le : blockDifferenceValue p ≤ topDefectValue t :=
      blockDifferenceValue_le_top hp
    have hpPos : p ∈ blockPositiveDifferenceDomain 8 1 Q0 1
        (boxEndpoint t) (boxBlock t) :=
      primitiveBlockDifferenceDomain_subset
        (show p ∈ primitiveBlockDifferenceDomain 8 1 Q0 1
          (boxEndpoint t) (boxBlock t) from hp)
    have hd_pos : 0 < blockDifferenceValue p :=
      blockDifferenceValue_pos hpPos
    have htopPrim := topDefectPair_mem_primitive Q0 t
    have htopPosDomain :
        topDefectPair t ∈ blockPositiveDifferenceDomain 8 1 Q0 1
          (boxEndpoint t) (boxBlock t) :=
      primitiveBlockDifferenceDomain_subset
        (show topDefectPair t ∈ primitiveBlockDifferenceDomain 8 1 Q0 1
          (boxEndpoint t) (boxBlock t) from htopPrim)
    have htop_pos : 0 < topDefectValue t := by
      rw [← topDefectPair_value]
      exact blockDifferenceValue_pos htopPosDomain
    have heq : phaseOrientationSign b * (h : ℤ) *
        (blockDifferenceValue p : ℤ) = nMax t :=
      (defectCharacterExponent_eq hx).symm.trans hexp
    cases b with
    | false =>
        simp [phaseOrientationSign, nMax] at heq
        have hmul :
            h * blockDifferenceValue p = 10 * topDefectValue t := by
          exact_mod_cast heq
        have hd_eq : blockDifferenceValue p = topDefectValue t := by
          nlinarith
        have hh_eq : h = 10 := by
          nlinarith
        have hp_eq : p = topDefectPair t :=
          (blockDifferenceValue_eq_top_iff hp).mp hd_eq
        subst p
        subst h
        rfl
    | true =>
        simp [phaseOrientationSign, nMax] at heq
        nlinarith
  · intro hx
    subst x
    have hmem :
        topCharacterRecord t ∈ defectCharacterDomain Q0 t := by
      simp [topCharacterRecord, defectCharacterDomain,
        topDefectPair_mem_unmatched]
    refine ⟨hmem, ?_⟩
    rw [defectCharacterExponent_eq hmem]
    simp [topCharacterRecord, phaseOrientationSign, nMax,
      topDefectPair_value]

/-- The full formal coefficient at the surviving mode. -/
theorem defectCoefficient_nMax (Q0 t : ℕ) :
    defectCoefficient Q0 t (nMax t) =
      1 / widthWeight (boxBlock t) := by
  rw [defectCoefficient_eq_filter_sum, nMax_fiber_eq_singleton]
  simp [defectTermWeight]

/-- The displayed coefficient is nonzero at every scale `t`, so the onset is
exactly zero. -/
theorem defectCoefficient_nMax_ne_zero (Q0 t : ℕ) :
    defectCoefficient Q0 t (nMax t) ≠ 0 := by
  rw [defectCoefficient_nMax]
  exact one_div_ne_zero (ne_of_gt (boxWidth_pos t))

/-- At the exact scale `m=1`, admissibility has no dependence on `Q0`. -/
theorem admissible_eight_one_one_iff (Q0 : ℕ) (q : OrderedLongPair) :
    AdmissibleOrderedFrequency 8 1 Q0 1 q ↔ 1 ≤ q.2.1 := by
  unfold AdmissibleOrderedFrequency
  constructor
  · intro h
    exact h.2.1
  · intro hr
    exact ⟨by omega, hr,
      not_arithmeticExcluded_eight_one_at_one Q0 q.2.2 q.2.1 hr⟩

/-- Consequently the exact positive primitive record domain is independent of
the onset parameter, while every other membership condition remains literal. -/
theorem primitiveRecordDomain_independent_Q0 (Q0 Q1 t : ℕ) :
    primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) =
      primitiveRecordDomain 8 1 Q1 1 (boxEndpoint t) (boxBlock t) := by
  classical
  ext p
  simp only [primitiveRecordDomain, primitiveBlockDifferenceDomain,
    Finset.mem_filter, mem_blockPositiveDifferenceDomain_iff,
    admissible_eight_one_one_iff]

/-- T59's literal finite complement is therefore also independent of `Q0`. -/
theorem unmatchedDefect_independent_Q0 (Q0 Q1 t : ℕ) :
    unmatchedDefect Q0 t = unmatchedDefect Q1 t := by
  rw [unmatchedDefect, unmatchedDefect,
    primitiveRecordDomain_independent_Q0 Q0 Q1 t]

/-- The fully labeled record-orientation-frequency domain is independent of
`Q0`; no quotient or image is used in this transfer. -/
theorem defectCharacterDomain_independent_Q0 (Q0 Q1 t : ℕ) :
    defectCharacterDomain Q0 t = defectCharacterDomain Q1 t := by
  rw [defectCharacterDomain, defectCharacterDomain,
    unmatchedDefect_independent_Q0 Q0 Q1 t]

/-- At `m=1`, the imported arithmetic exclusion is impossible; hence the full
T59 defect and its Laurent polynomial do not depend on `Q0`. -/
theorem defectLaurent_independent_Q0 (Q0 t : ℕ) :
    defectLaurent Q0 t = D t := by
  unfold D defectLaurent
  rw [defectCharacterDomain_independent_Q0 Q0 0 t]

/-- Final requested coefficient statement for `D_t`. -/
theorem a_nMax (t : ℕ) :
    a t (nMax t) = 1 / widthWeight (boxBlock t) ∧
      a t (nMax t) ≠ 0 := by
  change defectCoefficient 0 t (nMax t) =
      1 / widthWeight (boxBlock t) ∧
    defectCoefficient 0 t (nMax t) ≠ 0
  exact ⟨defectCoefficient_nMax 0 t,
    defectCoefficient_nMax_ne_zero 0 t⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T60

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.mem_defectCharacterDomain_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.defectCharacter_mem_exact_T59_fiber
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.defectCharacterExponent_eq
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.defectCoefficient_eq_filter_sum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.topDefectPair_mem_unmatched
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.blockDifferenceValue_le_top
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.blockDifferenceValue_eq_top_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.nMax_fiber_eq_singleton
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.defectLaurent_independent_Q0
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T60.a_nMax
