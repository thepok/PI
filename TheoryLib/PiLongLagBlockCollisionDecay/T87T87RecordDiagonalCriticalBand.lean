import TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff
import TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
import TheoryLib.PiLongLagBlockCollisionDecay.T31T31CrossBlockAlmostEverywhere
import TheoryLib.PiLongLagBlockCollisionDecay.T32T32AllBlockFixedPiRange
import TheoryLib.PiLongLagBlockCollisionDecay.T79T79HousekeepingBridges

/-!
# T87: kernel-checked record diagonal in the critical band

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file independently formalizes the record-diagonal analysis suggested by
the unverified T86 note.  It concerns T29's residual sparse-Fourier sibling
A12 only.  It proves no estimate for the centered off-diagonal term and no
instance of C1, C2, or C3.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T87

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- The exact number of both-orientation records with strict endpoint below
`K`, after the all-scale `(mu,c)=(8,1)` exclusion audit. -/
def endpointPrefixCount (m K : ℕ) : ℕ :=
  (K - m) * (K - m + 1)

/-- Distance of a canonical block's right endpoint from the strict cutoff. -/
def endpointDepth (N : ℕ) (B : DyadicBlock) : ℕ :=
  N - B.finish

/-- The positive record-diagonal mass after dividing by the exact inclusive
frequency cardinality `10^m`. -/
def recordDiagonalMass (Q0 m N : ℕ) : ℝ :=
  ((translatedCanonicalBlocks N).map fun B =>
    ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) / widthWeight B).sum

/-- The literal record diagonal, including every frequency `1 <= h <= 10^m`. -/
def recordDiagonal (Q0 m N : ℕ) : ℝ :=
  (10 ^ m : ℝ) * recordDiagonalMass Q0 m N

/-- Canonical terminal blocks whose exact dyadic length is at most `2^q`. -/
def terminalSuffixBlocks (N q : ℕ) : List DyadicBlock :=
  (translatedCanonicalBlocks N).filter fun B => B.blockLength ≤ 2 ^ q

/-- Record-diagonal mass in the arbitrary level-`q` terminal suffix. -/
def terminalSuffixMass (Q0 m N q : ℕ) : ℝ :=
  ((terminalSuffixBlocks N q).map fun B =>
    ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) / widthWeight B).sum

/-- The displayed T86 suffix factor. -/
def suffixFactor (P q : ℕ) : ℝ :=
  (32 * (2 + Real.sqrt 2) / 9) *
    Real.sqrt (((2 ^ q : ℕ) : ℝ) / (P : ℝ))

/-- For every positive scale and every admissible lag, T22's literal
arithmetic exclusion is false at `(mu,c)=(8,1)`, independently of `Q0`. -/
theorem not_arithmeticExcluded_eight_one
    (Q0 m n r : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r) :
    ¬ ArithmeticExcluded (8 : ℝ) 1 Q0 m n r := by
  intro hExcluded
  rw [Theory.PiDigits.LongLagBlockCollisionDecay.T79.arithmeticExcluded_iff_explicit]
    at hExcluded
  rcases hExcluded with ⟨_, hIneq⟩
  let H : ℕ := 10 ^ m
  let X : ℕ := 10 ^ r
  let d : ℕ := 10 ^ n * (10 ^ r - 1)
  have hHten : 10 ≤ H := by
    dsimp [H]
    simpa using pow_le_pow_right' (a := (10 : ℕ)) (by norm_num) hm
  have hHX : H ≤ X := by
    dsimp [H, X]
    exact pow_le_pow_right' (by norm_num) hmr
  have hXten : 10 ≤ X := hHten.trans hHX
  have hn : 1 ≤ 10 ^ n := one_le_pow₀ (by norm_num)
  have hdNat : X - 1 ≤ d := by
    dsimp [X, d]
    nlinarith [Nat.mul_le_mul_right (10 ^ r - 1) hn]
  have hdNine : 9 ≤ d := by omega
  have hquadNat : X < (X - 1) ^ 2 := by
    have hsub : X - 1 + 1 = X := Nat.sub_add_cancel (by omega)
    nlinarith
  have hHltD2Nat : H < d ^ 2 := by
    calc
      H ≤ X := hHX
      _ < (X - 1) ^ 2 := hquadNat
      _ ≤ d ^ 2 := Nat.pow_le_pow_left hdNat 2
  have hdPow : d ^ 2 ≤ d ^ 7 := by
    calc
      d ^ 2 = d ^ 2 * 1 := by simp
      _ ≤ d ^ 2 * d ^ 5 := by
        gcongr
        exact one_le_pow₀ (by omega)
      _ = d ^ 7 := by ring
  have hlargeNat : H < d ^ 7 := hHltD2Nat.trans_le hdPow
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hdPos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrewrite : (d : ℝ) * (1 / (d : ℝ) ^ (8 : ℝ)) =
      1 / (d : ℝ) ^ 7 := by
    have h8 : (8 : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
    rw [h8, Real.rpow_natCast]
    field_simp [ne_of_gt hdPos]
  have hIneq' : ((H : ℝ))⁻¹ ≤
      (d : ℝ) * (1 / (d : ℝ) ^ (8 : ℝ)) := by
    simpa [H, d] using hIneq
  rw [hrewrite] at hIneq'
  have hsmall := (le_div_iff₀ (pow_pos hdPos 7)).mp hIneq'
  have hsmall' : (d : ℝ) ^ 7 / (H : ℝ) ≤ 1 := by
    simpa [div_eq_mul_inv, mul_comm] using hsmall
  have hleReal : (d : ℝ) ^ 7 ≤ (H : ℝ) := by
    nlinarith [(div_le_iff₀ hHpos).mp hsmall']
  have hlargeReal : (H : ℝ) < (d : ℝ) ^ 7 := by exact_mod_cast hlargeNat
  linarith

/-- Exact T22 domain after the exclusion audit.  The untouched Boolean field
is the literal ordered orientation. -/
theorem mem_orderedLongPairDomain_eight_one_iff
    (Q0 m K : ℕ) (hm : 1 ≤ m) (q : OrderedLongPair) :
    q ∈ orderedLongPairDomain (8 : ℝ) 1 Q0 m K ↔
      0 < q.2.1 ∧ m ≤ q.2.1 ∧ frequencyEndpoint q.2 < K := by
  rw [mem_orderedLongPairDomain_iff_admissible_endpoint]
  simp only [AdmissibleOrderedFrequency]
  constructor
  · rintro ⟨⟨hr, hmr, _⟩, hend⟩
    exact ⟨hr, hmr, hend⟩
  · rintro ⟨hr, hmr, hend⟩
    exact ⟨⟨hr, hmr, not_arithmeticExcluded_eight_one Q0 m q.2.2 q.2.1 hm hmr⟩,
      hend⟩

/-- Both literal ordered orientations survive exactly on the displayed block,
lag, and strict endpoint range. -/
theorem blockRecordDomain_both_orientations_eight_one
    (Q0 m : ℕ) (B : DyadicBlock) (p : LongPairCore) (hm : 1 ≤ m) :
    (((false, p) ∈ blockRecordDomain (8 : ℝ) 1 Q0 m B ↔
        0 < p.1 ∧ m ≤ p.1 ∧ B.start ≤ frequencyEndpoint p ∧
          frequencyEndpoint p < B.finish) ∧
      ((true, p) ∈ blockRecordDomain (8 : ℝ) 1 Q0 m B ↔
        0 < p.1 ∧ m ≤ p.1 ∧ B.start ≤ frequencyEndpoint p ∧
          frequencyEndpoint p < B.finish)) ∧
      signedDecimalFrequency (false, p) = -(positiveDecimalFrequency p : ℤ) ∧
      signedDecimalFrequency (true, p) = (positiveDecimalFrequency p : ℤ) := by
  have h := blockRecordDomain_both_orientations (8 : ℝ) 1 Q0 m B p
  rcases h with ⟨⟨hf, ht⟩, hsigned⟩
  refine ⟨⟨?_, ?_⟩, hsigned⟩
  · rw [hf]
    constructor
    · rintro ⟨hr, hmr, _, ha, hb⟩
      exact ⟨hr, hmr, ha, hb⟩
    · rintro ⟨hr, hmr, ha, hb⟩
      exact ⟨hr, hmr, not_arithmeticExcluded_eight_one Q0 m p.2 p.1 hm hmr,
        ha, hb⟩
  · rw [ht]
    constructor
    · rintro ⟨hr, hmr, _, ha, hb⟩
      exact ⟨hr, hmr, ha, hb⟩
    · rintro ⟨hr, hmr, ha, hb⟩
      exact ⟨hr, hmr, not_arithmeticExcluded_eight_one Q0 m p.2 p.1 hm hmr,
        ha, hb⟩

/-- Once exclusions vanish, T32's injective endpoint code is onto its complete
both-orientation triangular envelope. -/
theorem endpointEnvelopeCode_image_eq
    (Q0 m K : ℕ) (hm : 1 ≤ m) :
    (orderedLongPairDomain (8 : ℝ) 1 Q0 m K).image
        (endpointEnvelopeCode m) = endpointEnvelope m K := by
  classical
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    exact endpointEnvelopeCode_mem hq
  · intro z hz
    rcases z with ⟨orientation, ⟨u, n⟩⟩
    rw [endpointEnvelope] at hz
    rcases Finset.mem_product.mp hz with ⟨_, hz⟩
    rw [Finset.mem_sigma] at hz
    rcases hz with ⟨hu, hn⟩
    simp only [Finset.mem_range] at hu hn
    let r := m + u - n
    let q : OrderedLongPair := (orientation, ⟨r, n⟩)
    have hnm : n ≤ m + u := by omega
    have hrm : m ≤ r := by dsimp [r]; omega
    have hr0 : 0 < r := hm.trans hrm
    have hend : frequencyEndpoint q.2 < K := by
      dsimp [q, r, frequencyEndpoint]
      omega
    have hq : q ∈ orderedLongPairDomain (8 : ℝ) 1 Q0 m K :=
      (mem_orderedLongPairDomain_eight_one_iff Q0 m K hm q).2
        ⟨hr0, hrm, hend⟩
    apply Finset.mem_image.mpr
    refine ⟨q, hq, ?_⟩
    dsimp [q, endpointEnvelopeCode, frequencyEndpoint, r]
    congr
    omega

/-- Exact both-orientation prefix count, including every strict endpoint and
independent of `Q0`. -/
theorem orderedLongPairDomain_card_eight_one
    (Q0 m K : ℕ) (hm : 1 ≤ m) :
    (orderedLongPairDomain (8 : ℝ) 1 Q0 m K).card = endpointPrefixCount m K := by
  classical
  have hinj := endpointEnvelopeCode_injOn (8 : ℝ) 1 Q0 m K
  rw [← Finset.card_image_of_injOn hinj,
    endpointEnvelopeCode_image_eq Q0 m K hm, endpointEnvelope_card]
  rfl

/-- Exact record count in every half-open block `[B.start,B.finish)`. -/
theorem blockRecordDomain_card_eight_one
    (Q0 m : ℕ) (B : DyadicBlock) (hm : 1 ≤ m) :
    (blockRecordDomain (8 : ℝ) 1 Q0 m B).card =
      endpointPrefixCount m B.finish - endpointPrefixCount m B.start := by
  rw [blockRecordDomain_card_eq_sub,
    orderedLongPairDomain_card_eight_one Q0 m B.finish hm,
    orderedLongPairDomain_card_eight_one Q0 m B.start hm]

/-- The exact inclusive frequency range has cardinality `10^m`, retaining the
upper endpoint and excluding frequency zero. -/
theorem inclusiveFrequencies_card_exact (m : ℕ) :
    (inclusiveFrequencies m).card = 10 ^ m := by
  simp [inclusiveFrequencies, decimalFrequency]

/-- Exact finite diagonal formula with every canonical block, both ordered
orientations, inclusive frequency endpoint, strict block endpoint, and T29's
literal width visible in the theorem type. -/
theorem recordDiagonal_exact_formula
    (Q0 m N : ℕ) (hm : 1 ≤ m) :
    recordDiagonal Q0 m N =
      ((translatedCanonicalBlocks N).map fun B =>
        ((inclusiveFrequencies m).card : ℝ) *
          ((endpointPrefixCount m B.finish -
            endpointPrefixCount m B.start : ℕ) : ℝ) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum := by
  unfold recordDiagonal recordDiagonalMass
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro B hB
  rw [blockRecordDomain_card_eight_one Q0 m B hm,
    inclusiveFrequencies_card_exact, widthWeight_eq_endpoints]
  norm_num
  ring

/-! ## Exact endpoint-depth decomposition -/

/-- In a decreasing dyadic partition, the remaining endpoint depth after any
block is strictly smaller than that block's exact length. -/
theorem dyadicPartitionFrom_finish_depth_lt
    (q : ℕ) (js : List ℕ) (B : DyadicBlock)
    (hdesc : js.Pairwise fun j k => k < j)
    (hB : B ∈ dyadicPartitionFrom q js) :
    B.finish ≤ q + dyadicLevelSum js + 1 ∧
      q + dyadicLevelSum js + 1 - B.finish < B.blockLength := by
  induction js generalizing q with
  | nil => simp [dyadicPartitionFrom] at hB
  | cons j js ih =>
      rw [List.pairwise_cons] at hdesc
      simp only [dyadicPartitionFrom, List.mem_cons] at hB
      rcases hB with rfl | hB
      · have htail : dyadicLevelSum js < 2 ^ j :=
          dyadicLevelSum_lt_two_pow hdesc.2.nodup hdesc.1
        simp only [DyadicBlock.finish, DyadicBlock.blockLength,
          dyadicLevelSum, List.map_cons, List.sum_cons] at htail ⊢
        omega
      · have ht := ih (q + 2 ^ j) hdesc.2 hB
        simp only [dyadicLevelSum, List.map_cons, List.sum_cons] at ht ⊢
        convert ht using 1 <;> omega

/-- Every literal canonical block has endpoint depth in the exact range
`0 <= d <= 2^level-1`, and its endpoints and width radicand have the displayed
depth coordinates. -/
theorem canonicalBlock_endpointDepth_spec
    {N : ℕ} {B : DyadicBlock} (hN : 1 ≤ N)
    (hB : B ∈ translatedCanonicalBlocks N) :
    B.finish = N - endpointDepth N B ∧
      B.start = N - endpointDepth N B - B.blockLength ∧
      endpointDepth N B < B.blockLength ∧
      endpointDepth N B ≤ B.blockLength - 1 ∧
      ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) =
        (B.blockLength : ℝ) *
          (2 * (N : ℝ) - 2 * (endpointDepth N B : ℝ) -
            (B.blockLength : ℝ)) := by
  let levels := (N - 1).bitIndices.reverse
  have hdesc : levels.Pairwise fun j k => k < j :=
    Nat.bitIndices_sorted.pairwise.reverse
  have hsum : dyadicLevelSum levels = N - 1 := by
    simp [levels, dyadicLevelSum]
  have ht := dyadicPartitionFrom_finish_depth_lt 0 levels B hdesc hB
  have hend : 0 + dyadicLevelSum levels + 1 = N := by
    rw [hsum]
    omega
  rw [hend] at ht
  have hfinish : B.finish ≤ N := ht.1
  have hdepth : endpointDepth N B < B.blockLength := by
    exact ht.2
  have hstartFinish : B.start + B.blockLength = B.finish := by rfl
  have hfinishEq : B.finish = N - endpointDepth N B := by
    simp only [endpointDepth]
    omega
  have hstartEq : B.start = N - endpointDepth N B - B.blockLength := by
    omega
  refine ⟨hfinishEq, hstartEq, hdepth, by omega, ?_⟩
  rw [hfinishEq, hstartEq]
  push_cast [show endpointDepth N B ≤ N by simp [endpointDepth],
    show B.blockLength ≤ N - endpointDepth N B by omega]
  ring

/-- The exact diagonal formula in endpoint-depth coordinates.  Every block,
depth range, exact width, and inclusive frequency endpoint remains visible. -/
theorem recordDiagonal_endpointDepth_decomposition
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    recordDiagonal Q0 m N =
      ((translatedCanonicalBlocks N).map fun B =>
        ((Finset.Icc 1 (10 ^ m)).card : ℝ) *
          ((endpointPrefixCount m (N - endpointDepth N B) -
            endpointPrefixCount m
              (N - endpointDepth N B - B.blockLength) : ℕ) : ℝ) /
          Real.sqrt ((B.blockLength : ℝ) *
            (2 * (N : ℝ) - 2 * (endpointDepth N B : ℝ) -
              (B.blockLength : ℝ)))).sum := by
  rw [recordDiagonal_exact_formula Q0 m N hm]
  congr 1
  apply List.map_congr_left
  intro B hB
  have hs := canonicalBlock_endpointDepth_spec hN hB
  have hrad := hs.2.2.2.2
  rw [hs.1, hs.2.1] at hrad ⊢
  rw [hrad]
  simp only [inclusiveFrequencies, decimalFrequency]

/-! ## Explicit critical-band mass bounds -/

/-- On a canonical block, T31's endpoint-filtered domain is exactly T32's
literal cutoff difference. -/
theorem blockOrderedDomain_eq_blockRecordDomain
    (μ c : ℝ) (Q0 m N : ℕ) {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) :
    Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockOrderedDomain
        μ c Q0 m N B = blockRecordDomain μ c Q0 m B := by
  classical
  ext q
  rw [Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockOrderedDomain,
    Finset.mem_filter, mem_blockRecordDomain_iff]
  constructor
  · rintro ⟨hq, ha, hb⟩
    exact ⟨(mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq).1, ha, hb⟩
  · rintro ⟨hq, ha, hb⟩
    refine ⟨mem_orderedLongPairDomain_iff_admissible_endpoint.mpr ⟨hq, ?_⟩,
      ha, hb⟩
    exact hb.trans_le (canonical_finish_le hB)

/-- Each exact record-cardinality summand divided by its literal T29 width is
at most that width. -/
theorem blockRecordMass_le_width
    (Q0 m N : ℕ) {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) :
    ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) / widthWeight B ≤
      widthWeight B := by
  have hcard :=
    Theory.PiDigits.LongLagBlockCollisionDecay.T31.blockOrderedDomain_card_lt_width_sq
      (μ := (8 : ℝ)) (c := 1) (Q0 := Q0) (m := m) (N := N) hB
  rw [blockOrderedDomain_eq_blockRecordDomain (8 : ℝ) 1 Q0 m N hB] at hcard
  have hw := canonical_widthWeight_pos hB
  apply (div_le_iff₀ hw).2
  simpa [pow_two] using hcard.le

/-- The literal width of every canonical block is at most the cutoff `N`. -/
theorem canonical_widthWeight_le_cutoff
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    widthWeight B ≤ (N : ℝ) := by
  have hsquare :=
    Theory.PiDigits.LongLagBlockCollisionDecay.T31.canonical_widthWeight_sq hB
  have hfinish : (B.finish : ℝ) ≤ N := by
    exact_mod_cast canonical_finish_le hB
  have hw : 0 ≤ widthWeight B := widthWeight_nonneg B
  apply (sq_le_sq₀ hw (by positivity)).mp
  rw [hsquare]
  have hstart : (0 : ℝ) ≤ B.start := by positivity
  nlinarith

/-- The exact normalized diagonal mass has T29's displayed sharp upper
The constant. -/
theorem recordDiagonalMass_upper
    (Q0 m N : ℕ) (hN : 1 ≤ N) :
    recordDiagonalMass Q0 m N ≤
      ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) := by
  unfold recordDiagonalMass
  calc
    ((translatedCanonicalBlocks N).map fun B =>
        ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
          widthWeight B).sum ≤
        ((translatedCanonicalBlocks N).map widthWeight).sum := by
      apply list_sum_map_le_sum_map
      intro B hB
      exact blockRecordMass_le_width Q0 m N hB
    _ ≤ ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) :=
      canonical_widthWeight_sum_le_sharp hN

/-- Before critical-band simplification, the exact prefix count divided by
`N` is a lower bound for the literal diagonal mass. -/
theorem endpointPrefixCount_div_le_recordDiagonalMass
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    (endpointPrefixCount m N : ℝ) / (N : ℝ) ≤
      recordDiagonalMass Q0 m N := by
  let blocks := translatedCanonicalBlocks N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpoint : ∀ B ∈ blocks,
      ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) / (N : ℝ) ≤
        ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) / widthWeight B := by
    intro B hB
    exact div_le_div_of_nonneg_left (by positivity)
      (canonical_widthWeight_pos hB)
      (canonical_widthWeight_le_cutoff hB)
  have hsum := list_sum_map_le_sum_map blocks _ _ hpoint
  have hfactor :
      (blocks.map fun B =>
        ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) / (N : ℝ)).sum =
      ((blocks.map fun B =>
        ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ)).sum) / (N : ℝ) := by
    induction blocks with
    | nil => simp
    | cons B blocks ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  have hcards := canonicalBlockRecord_card_sum (8 : ℝ) 1 Q0 m N hm hN
  have hcast :
      (blocks.map fun B =>
        ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ)).sum =
      ((orderedLongPairDomain (8 : ℝ) 1 Q0 m N).card : ℝ) := by
    dsimp [blocks]
    rw [← hcards]
    induction translatedCanonicalBlocks N with
    | nil => simp
    | cons B blocks ih => simp [ih]
  rw [hfactor, hcast,
    orderedLongPairDomain_card_eight_one Q0 m N hm] at hsum
  exact hsum

/-- Elementary decimal growth needed by every positive critical-band pair. -/
theorem sixteen_mul_sq_le_ten_pow
    {m : ℕ} (hm : 2 ≤ m) : 16 * m ^ 2 ≤ 10 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hmul := Nat.mul_le_mul_left 10 ih
      calc
        16 * (m + 1) ^ 2 ≤ 10 * (16 * m ^ 2) := by nlinarith
        _ ≤ 10 * 10 ^ m := hmul
        _ = 10 ^ (m + 1) := by rw [pow_succ]; ring

/-- The lower critical-band hypothesis forces the explicit range `4m <= N`. -/
theorem four_mul_m_le_of_criticalLower
    {m N : ℕ} (hm : 1 ≤ m) (hlower : 10 ^ m ≤ N ^ 2) :
    4 * m ≤ N := by
  by_cases hm1 : m = 1
  · subst m
    norm_num at hlower ⊢
    nlinarith
  · have hm2 : 2 ≤ m := by omega
    have hgrowth := sixteen_mul_sq_le_ten_pow hm2
    nlinarith

/-- Explicit two-sided mass bounds for every positive pair in the full
critical band `10^m <= N^2 <= 2*10^m`. -/
theorem recordDiagonalMass_critical_bounds
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    (9 / 16 : ℝ) * (N : ℝ) ≤ recordDiagonalMass Q0 m N ∧
      recordDiagonalMass Q0 m N ≤
        ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) := by
  have _hupperAudit : N ^ 2 ≤ 2 * 10 ^ m := hupper
  have h4 := four_mul_m_le_of_criticalLower hm hlower
  have hmN : m ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hLnat : 3 * N ≤ 4 * (N - m) := by omega
  let L : ℝ := (N - m : ℕ)
  have hLcast : (3 * N : ℕ) ≤ 4 * (N - m) := hLnat
  have hLcast' : (3 * N : ℝ) ≤ (4 * (N - m) : ℕ) := by
    exact_mod_cast hLcast
  have hL : (3 : ℝ) / 4 * (N : ℝ) ≤ (N - m : ℕ) := by
    push_cast [hmN]
    push_cast [hmN] at hLcast'
    nlinarith
  have hsq := (sq_le_sq₀ (by positivity)
    (show (0 : ℝ) ≤ (N - m : ℕ) by positivity)).2 hL
  have hprod : (9 / 16 : ℝ) * (N : ℝ) ^ 2 ≤ L * (L + 1) := by
    dsimp [L]
    nlinarith [hsq, show (0 : ℝ) ≤ (N - m : ℕ) by positivity]
  have hprefix : (9 / 16 : ℝ) * (N : ℝ) ≤
      (endpointPrefixCount m N : ℝ) / (N : ℝ) := by
    apply (le_div_iff₀ hNpos).2
    unfold endpointPrefixCount
    push_cast [hmN]
    dsimp [L] at hprod
    push_cast [hmN] at hprod
    nlinarith
  exact ⟨hprefix.trans
      (endpointPrefixCount_div_le_recordDiagonalMass Q0 m N hm hN),
    recordDiagonalMass_upper Q0 m N hN⟩

/-- The explicit `s=1/2` normalization appearing in the critical-band
analysis, written without hiding either endpoint or square root. -/
def criticalNormalization (m N : ℕ) : ℝ :=
  ((10 ^ m : ℕ) : ℝ) *
    ((N : ℝ) + (N : ℝ) ^ 2 / Real.sqrt (((10 ^ m : ℕ) : ℝ)))

/-- The critical band pins the inner normalized target between the two
displayed multiples of `N`. -/
theorem critical_innerNormalization_bounds
    (m N : ℕ) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    2 * (N : ℝ) ≤
        (N : ℝ) + (N : ℝ) ^ 2 /
          Real.sqrt (((10 ^ m : ℕ) : ℝ)) ∧
      (N : ℝ) + (N : ℝ) ^ 2 /
          Real.sqrt (((10 ^ m : ℕ) : ℝ)) ≤
        (1 + Real.sqrt 2) * (N : ℝ) := by
  let H : ℝ := ((10 ^ m : ℕ) : ℝ)
  have hHpos : 0 < H := by positivity
  have hsqrtH : 0 < Real.sqrt H := Real.sqrt_pos.2 hHpos
  have hsqrtHSq : (Real.sqrt H) ^ 2 = H := Real.sq_sqrt hHpos.le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlowerR : H ≤ (N : ℝ) ^ 2 := by
    dsimp [H]
    exact_mod_cast hlower
  have hupperR : (N : ℝ) ^ 2 ≤ 2 * H := by
    dsimp [H]
    exact_mod_cast hupper
  have hsqrtHleN : Real.sqrt H ≤ (N : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg H) hNpos.le).mp
    rw [hsqrtHSq]
    exact hlowerR
  have hNleTail : (N : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt H := by
    apply (le_div_iff₀ hsqrtH).2
    nlinarith
  have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hNleSqrt : (N : ℝ) ≤ Real.sqrt 2 * Real.sqrt H := by
    apply (sq_le_sq₀ hNpos.le (by positivity)).mp
    rw [mul_pow, hsqrtTwoSq, hsqrtHSq]
    exact hupperR
  have htailUpper : (N : ℝ) ^ 2 / Real.sqrt H ≤
      Real.sqrt 2 * (N : ℝ) := by
    apply (div_le_iff₀ hsqrtH).2
    have hmul := mul_le_mul_of_nonneg_left hNleSqrt hNpos.le
    nlinarith
  dsimp [H] at hNleTail htailUpper ⊢
  constructor <;> nlinarith

/-- Exact normalized two-sided record-diagonal bounds.  The theorem exposes
the full critical band and both displayed irrational constants. -/
theorem recordDiagonal_normalized_critical_bounds
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    9 / (16 * (1 + Real.sqrt 2)) ≤
        recordDiagonal Q0 m N / criticalNormalization m N ∧
      recordDiagonal Q0 m N / criticalNormalization m N ≤
        3 / 4 + Real.sqrt 2 / 2 := by
  let H : ℝ := ((10 ^ m : ℕ) : ℝ)
  let T : ℝ := (N : ℝ) + (N : ℝ) ^ 2 / Real.sqrt H
  let M : ℝ := recordDiagonalMass Q0 m N
  have hH : 0 < H := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass := recordDiagonalMass_critical_bounds Q0 m N hm hN hlower hupper
  have htarget := critical_innerNormalization_bounds m N hN hlower hupper
  have hTpos : 0 < T := by dsimp [T, H]; positivity
  have hsqrtTwo : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have honeSqrt : 0 < 1 + Real.sqrt 2 := by positivity
  have hratio : recordDiagonal Q0 m N / criticalNormalization m N = M / T := by
    dsimp [recordDiagonal, criticalNormalization, M, T, H]
    norm_num
    field_simp
  rw [hratio]
  constructor
  · apply (le_div_iff₀ hTpos).2
    have hconstant :
        (9 / (16 * (1 + Real.sqrt 2))) *
            ((1 + Real.sqrt 2) * (N : ℝ)) =
          (9 / 16 : ℝ) * (N : ℝ) := by
      field_simp
    calc
      (9 / (16 * (1 + Real.sqrt 2))) * T ≤
          (9 / (16 * (1 + Real.sqrt 2))) *
            ((1 + Real.sqrt 2) * (N : ℝ)) := by
        gcongr
        exact htarget.2
      _ = (9 / 16 : ℝ) * (N : ℝ) := hconstant
      _ ≤ M := hmass.1
  · apply (div_le_iff₀ hTpos).2
    calc
      M ≤ ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) := hmass.2
      _ = (3 / 4 + Real.sqrt 2 / 2) * (2 * (N : ℝ)) := by ring
      _ ≤ (3 / 4 + Real.sqrt 2 / 2) * T := by
        exact mul_le_mul_of_nonneg_left htarget.1 (by positivity)

/-- The rationally weakened strict constants are an explicit corollary, not a
claim about T29's centered off-diagonal square function. -/
theorem recordDiagonal_normalized_rational_bounds
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    (1 / 5 : ℝ) < recordDiagonal Q0 m N / criticalNormalization m N ∧
      recordDiagonal Q0 m N / criticalNormalization m N < (3 / 2 : ℝ) := by
  have hbounds := recordDiagonal_normalized_critical_bounds
    Q0 m N hm hN hlower hupper
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtUpper : Real.sqrt 2 < (3 / 2 : ℝ) := by nlinarith
  have hlowerConstant : (1 / 5 : ℝ) <
      9 / (16 * (1 + Real.sqrt 2)) := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 5)
      (by positivity : (0 : ℝ) < 16 * (1 + Real.sqrt 2))]
    nlinarith
  constructor
  · exact hlowerConstant.trans_le hbounds.1
  · exact hbounds.2.trans_lt (by nlinarith)

/-! ## Arbitrary terminal-suffix mass -/

/-- Filtering a dyadic partition by literal length filters exactly the same
levels by `2^j <= 2^q`. -/
theorem dyadicPartitionFrom_terminal_levels
    (a q : ℕ) (js : List ℕ) :
    ((dyadicPartitionFrom a js).filter fun B => B.blockLength ≤ 2 ^ q).map
        DyadicBlock.level =
      js.filter fun j => 2 ^ j ≤ 2 ^ q := by
  induction js generalizing a with
  | nil => simp [dyadicPartitionFrom]
  | cons j js ih =>
      have ih' := ih (a + 2 ^ j)
      simp only [DyadicBlock.blockLength] at ih'
      simp only [dyadicPartitionFrom, List.filter_cons, DyadicBlock.blockLength]
      split <;> simp_all

/-- The exact levels of the arbitrary level-`q` terminal suffix. -/
theorem terminalSuffixBlocks_levels (N q : ℕ) :
    (terminalSuffixBlocks N q).map DyadicBlock.level =
      ((N - 1).bitIndices.reverse).filter fun j => 2 ^ j ≤ 2 ^ q := by
  unfold terminalSuffixBlocks translatedCanonicalBlocks canonicalDyadicPartition
  exact dyadicPartitionFrom_terminal_levels 0 q _

/-- The literal width mass of all canonical blocks of length at most `2^q`
has the displayed finite geometric bound. -/
theorem terminalSuffix_width_sum_le
    (N q : ℕ) :
    ((terminalSuffixBlocks N q).map widthWeight).sum ≤
      2 * (1 + Real.sqrt 2) * Real.sqrt (N : ℝ) *
        Real.sqrt ((2 ^ q : ℕ) : ℝ) := by
  let blocks := terminalSuffixBlocks N q
  let levels := blocks.map DyadicBlock.level
  have hpoint :
      (blocks.map widthWeight).sum ≤
        (blocks.map fun B =>
          Real.sqrt (2 * (N : ℝ)) *
            Real.sqrt (B.blockLength : ℝ)).sum := by
    apply list_sum_map_le_sum_map
    intro B hB
    apply canonical_widthWeight_le
    exact List.mem_of_mem_filter hB
  have hfactor :
      (blocks.map fun B =>
        Real.sqrt (2 * (N : ℝ)) *
          Real.sqrt (B.blockLength : ℝ)).sum =
        Real.sqrt (2 * (N : ℝ)) *
          (levels.map fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)).sum := by
    rw [List.sum_map_mul_left]
    dsimp [levels]
    simp [List.map_map, Function.comp_def, DyadicBlock.blockLength]
  have hlevels : levels =
      ((N - 1).bitIndices.reverse).filter fun j => 2 ^ j ≤ 2 ^ q := by
    exact terminalSuffixBlocks_levels N q
  have hdescAll : ((N - 1).bitIndices.reverse).Pairwise fun j k => k < j :=
    Nat.bitIndices_sorted.pairwise.reverse
  have hdesc : levels.Pairwise fun j k => k < j := by
    rw [hlevels]
    exact hdescAll.filter _
  have hlevelLt : ∀ j ∈ levels, j < q + 1 := by
    intro j hj
    rw [hlevels, List.mem_filter] at hj
    have hjq : j ≤ q :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
        (of_decide_eq_true hj.2)
    omega
  have hsumLt : dyadicLevelSum levels < 2 ^ (q + 1) :=
    dyadicLevelSum_lt_two_pow hdesc.nodup hlevelLt
  have hgeom := descending_levelSqrtSum_le levels hdesc
  have hsqrtSum : Real.sqrt (dyadicLevelSum levels : ℝ) ≤
      Real.sqrt ((2 ^ (q + 1) : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hsumLt.le
  have hlevelsBound :
      (levels.map fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)).sum ≤
        (1 + Real.sqrt 2) * Real.sqrt ((2 ^ (q + 1) : ℕ) : ℝ) :=
    hgeom.trans (mul_le_mul_of_nonneg_left hsqrtSum (by positivity))
  have hsqrtTwoN : Real.sqrt (2 * (N : ℝ)) =
      Real.sqrt 2 * Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtSucc : Real.sqrt ((2 ^ (q + 1) : ℕ) : ℝ) =
      Real.sqrt 2 * Real.sqrt ((2 ^ q : ℕ) : ℝ) := by
    rw [pow_succ]
    push_cast
    rw [mul_comm, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  calc
    (blocks.map widthWeight).sum ≤
        (blocks.map fun B => Real.sqrt (2 * (N : ℝ)) *
          Real.sqrt (B.blockLength : ℝ)).sum := hpoint
    _ = Real.sqrt (2 * (N : ℝ)) *
          (levels.map fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)).sum := hfactor
    _ ≤ Real.sqrt (2 * (N : ℝ)) *
          ((1 + Real.sqrt 2) *
            Real.sqrt ((2 ^ (q + 1) : ℕ) : ℝ)) := by
      gcongr
    _ = 2 * (1 + Real.sqrt 2) * Real.sqrt (N : ℝ) *
          Real.sqrt ((2 ^ q : ℕ) : ℝ) := by
      rw [hsqrtTwoN, hsqrtSucc]
      calc
        Real.sqrt 2 * Real.sqrt (N : ℝ) *
            ((1 + Real.sqrt 2) *
              (Real.sqrt 2 * Real.sqrt ((2 ^ q : ℕ) : ℝ))) =
            (Real.sqrt 2) ^ 2 * (1 + Real.sqrt 2) *
              Real.sqrt (N : ℝ) * Real.sqrt ((2 ^ q : ℕ) : ℝ) := by ring
        _ = 2 * (1 + Real.sqrt 2) * Real.sqrt (N : ℝ) *
              Real.sqrt ((2 ^ q : ℕ) : ℝ) := by rw [hsqrtTwoSq]

/-- The arbitrary terminal-suffix record mass is bounded by the same explicit
dyadic geometric expression, with all blocks and the suffix parameter retained. -/
theorem terminalSuffixMass_upper
    (Q0 m N q : ℕ) :
    terminalSuffixMass Q0 m N q ≤
      2 * (1 + Real.sqrt 2) * Real.sqrt (N : ℝ) *
        Real.sqrt ((2 ^ q : ℕ) : ℝ) := by
  unfold terminalSuffixMass
  calc
    ((terminalSuffixBlocks N q).map fun B =>
        ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
          widthWeight B).sum ≤
        ((terminalSuffixBlocks N q).map widthWeight).sum := by
      apply list_sum_map_le_sum_map
      intro B hB
      exact blockRecordMass_le_width Q0 m N (List.mem_of_mem_filter hB)
    _ ≤ 2 * (1 + Real.sqrt 2) * Real.sqrt (N : ℝ) *
          Real.sqrt ((2 ^ q : ℕ) : ℝ) :=
      terminalSuffix_width_sum_le N q

/-- Every nonempty binary expansion exposes its unique largest first block. -/
theorem critical_canonicalLevels_cons
    {m N : ℕ} (hm : 1 ≤ m) (hlower : 10 ^ m ≤ N ^ 2) :
    ∃ j₀ js, (N - 1).bitIndices.reverse = j₀ :: js := by
  have hN : 2 ≤ N := by
    by_contra h
    have hNle : N ≤ 1 := by omega
    have hten : 10 ≤ 10 ^ m := by
      simpa using pow_le_pow_right' (a := (10 : ℕ)) (by norm_num) hm
    nlinarith
  cases hlevels : (N - 1).bitIndices.reverse with
  | nil =>
      have : N - 1 = 0 := by
        have hsum := Nat.sum_map_two_pow_bitIndices (N - 1)
        have horig : (N - 1).bitIndices = [] := by
          simpa using congrArg List.reverse hlevels
        simpa [horig] using hsum.symm
      omega
  | cons j js => exact ⟨j, js, rfl⟩

/-- For an arbitrary suffix level `q`, the exact terminal-suffix mass is at
most T86's displayed factor times the full record diagonal.  No off-diagonal,
C2, C3, or C1 conclusion is involved. -/
theorem terminalSuffixMass_le_displayed_fraction
    (Q0 m N j₀ q : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m)
    {js : List ℕ}
    (hlevels : (N - 1).bitIndices.reverse = j₀ :: js) :
    terminalSuffixMass Q0 m N q ≤
      ((32 * (2 + Real.sqrt 2) / 9) *
        Real.sqrt (((2 ^ q : ℕ) : ℝ) / ((2 ^ j₀ : ℕ) : ℝ))) *
          recordDiagonalMass Q0 m N := by
  let P : ℕ := 2 ^ j₀
  let R : ℕ := 2 ^ q
  have hfirst : (⟨1, j₀⟩ : DyadicBlock) ∈ translatedCanonicalBlocks N := by
    unfold translatedCanonicalBlocks canonicalDyadicPartition
    rw [hlevels]
    simp [dyadicPartitionFrom]
  have hPleN : P ≤ N := by
    have hf := canonical_finish_le hfirst
    dsimp [P, DyadicBlock.finish, DyadicBlock.blockLength] at hf
    omega
  have hPpos : (0 : ℝ) < P := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrtP : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.2 hPpos
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hsqrtPle : Real.sqrt (P : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hPleN
  have hsqrtNSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hNpos.le
  have hrootProduct : Real.sqrt (N : ℝ) * Real.sqrt (R : ℝ) ≤
      (N : ℝ) * Real.sqrt ((R : ℝ) / (P : ℝ)) := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ R)]
    rw [show (N : ℝ) * (Real.sqrt (R : ℝ) / Real.sqrt (P : ℝ)) =
      ((N : ℝ) * Real.sqrt (R : ℝ)) / Real.sqrt (P : ℝ) by ring]
    apply (le_div_iff₀ hsqrtP).2
    have hNP : Real.sqrt (N : ℝ) * Real.sqrt (P : ℝ) ≤ (N : ℝ) := by
      calc
        Real.sqrt (N : ℝ) * Real.sqrt (P : ℝ) ≤
            Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrtPle (Real.sqrt_nonneg _)
        _ = (N : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hNP (Real.sqrt_nonneg (R : ℝ))
    nlinarith
  have hmass := recordDiagonalMass_critical_bounds Q0 m N hm hN hlower hupper
  have hsuffix := terminalSuffixMass_upper Q0 m N q
  have hsqrtTwo : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  dsimp [P, R] at hrootProduct ⊢
  calc
    terminalSuffixMass Q0 m N q ≤
        2 * (1 + Real.sqrt 2) * Real.sqrt (N : ℝ) *
          Real.sqrt ((2 ^ q : ℕ) : ℝ) := hsuffix
    _ ≤ 2 * (2 + Real.sqrt 2) * (N : ℝ) *
          Real.sqrt (((2 ^ q : ℕ) : ℝ) / ((2 ^ j₀ : ℕ) : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hrootProduct
        (by positivity : (0 : ℝ) ≤ 2 * (1 + Real.sqrt 2))
      have hright : 0 ≤ (N : ℝ) *
          Real.sqrt (((2 ^ q : ℕ) : ℝ) / ((2 ^ j₀ : ℕ) : ℝ)) := by positivity
      nlinarith
    _ = ((32 * (2 + Real.sqrt 2) / 9) *
          Real.sqrt (((2 ^ q : ℕ) : ℝ) / ((2 ^ j₀ : ℕ) : ℝ))) *
            ((9 / 16 : ℝ) * (N : ℝ)) := by ring
    _ ≤ ((32 * (2 + Real.sqrt 2) / 9) *
          Real.sqrt (((2 ^ q : ℕ) : ℝ) / ((2 ^ j₀ : ℕ) : ℝ))) *
            recordDiagonalMass Q0 m N := by
      gcongr
      exact hmass.1

/-- Ratio form of the arbitrary suffix estimate, with the suffix parameter,
largest canonical block, critical band, and displayed constant explicit. -/
theorem terminalSuffixMass_ratio_le_displayed
    (Q0 m N j₀ q : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m)
    {js : List ℕ}
    (hlevels : (N - 1).bitIndices.reverse = j₀ :: js) :
    terminalSuffixMass Q0 m N q / recordDiagonalMass Q0 m N ≤
      (32 * (2 + Real.sqrt 2) / 9) *
        Real.sqrt (((2 ^ q : ℕ) : ℝ) / ((2 ^ j₀ : ℕ) : ℝ)) := by
  have hmass := recordDiagonalMass_critical_bounds Q0 m N hm hN hlower hupper
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiag : 0 < recordDiagonalMass Q0 m N := by
    nlinarith
  exact (div_le_iff₀ hdiag).2
    (terminalSuffixMass_le_displayed_fraction
      Q0 m N j₀ q hm hN hlower hupper hlevels)

/-! ## Fully literal theorem-type audits -/

/-- Fully unfolded exact formula: T32's record domain on every T29 canonical
block, both orientations audited above, exactly `h=1,...,10^m`, strict
frequency endpoints, and the literal square-root width all appear in the type. -/
theorem recordDiagonal_exact_formula_literal
    (Q0 m N : ℕ) (hm : 1 ≤ m) :
    (10 ^ m : ℝ) *
        ((translatedCanonicalBlocks N).map fun B =>
          ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum =
      ((translatedCanonicalBlocks N).map fun B =>
        ((Finset.Icc 1 (10 ^ m)).card : ℝ) *
          (((B.finish - m) * (B.finish - m + 1) -
            (B.start - m) * (B.start - m + 1) : ℕ) : ℝ) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum := by
  have h := recordDiagonal_exact_formula Q0 m N hm
  simpa [recordDiagonal, recordDiagonalMass, endpointPrefixCount,
    widthWeight, inclusiveFrequencies, decimalFrequency] using h

/-- Fully unfolded normalized bounds with every critical-band hypothesis,
literal block width, inclusive-frequency factor, and displayed constant. -/
theorem recordDiagonal_normalized_critical_bounds_literal
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    9 / (16 * (1 + Real.sqrt 2)) ≤
        ((10 ^ m : ℝ) *
          ((translatedCanonicalBlocks N).map fun B =>
            ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
              Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum) /
          ((((10 ^ m : ℕ) : ℝ) *
            ((N : ℝ) + (N : ℝ) ^ 2 /
              Real.sqrt (((10 ^ m : ℕ) : ℝ))))) ∧
      ((10 ^ m : ℝ) *
          ((translatedCanonicalBlocks N).map fun B =>
            ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
              Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum) /
          ((((10 ^ m : ℕ) : ℝ) *
            ((N : ℝ) + (N : ℝ) ^ 2 /
              Real.sqrt (((10 ^ m : ℕ) : ℝ))))) ≤
        3 / 4 + Real.sqrt 2 / 2 := by
  simpa [recordDiagonal, recordDiagonalMass, criticalNormalization, widthWeight]
    using recordDiagonal_normalized_critical_bounds
      Q0 m N hm hN hlower hupper

/-- Fully unfolded arbitrary suffix ratio: the filter `length <= 2^q`, every
canonical block, exact record domain, literal width, largest-level parameter,
critical band, and displayed constant all occur in the theorem type. -/
theorem terminalSuffixMass_ratio_le_displayed_literal
    (Q0 m N j₀ q : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m)
    {js : List ℕ}
    (hlevels : (N - 1).bitIndices.reverse = j₀ :: js) :
    (((translatedCanonicalBlocks N).filter fun B =>
        B.blockLength ≤ 2 ^ q).map fun B =>
          ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum /
      ((translatedCanonicalBlocks N).map fun B =>
        ((blockRecordDomain (8 : ℝ) 1 Q0 m B).card : ℝ) /
          Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum ≤
        (32 * (2 + Real.sqrt 2) / 9) *
          Real.sqrt (((2 ^ q : ℕ) : ℝ) / ((2 ^ j₀ : ℕ) : ℝ)) := by
  simpa [terminalSuffixMass, terminalSuffixBlocks, recordDiagonalMass,
    widthWeight] using terminalSuffixMass_ratio_le_displayed
      Q0 m N j₀ q hm hN hlower hupper hlevels

end Theory.PiDigits.LongLagBlockCollisionDecay.T87

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.not_arithmeticExcluded_eight_one
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.blockRecordDomain_both_orientations_eight_one
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.blockRecordDomain_card_eight_one
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.recordDiagonal_exact_formula_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.canonicalBlock_endpointDepth_spec
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.recordDiagonal_endpointDepth_decomposition
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.recordDiagonal_normalized_critical_bounds_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T87.terminalSuffixMass_ratio_le_displayed_literal
