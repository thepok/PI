import TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff
import TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction

/-!
# T29: deterministic width-weighted square-function reduction

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module independently formalizes the deterministic implication suggested
by the unverified T27 note. It assumes, but does not establish, the new
width-weighted condition at a specified phase. In particular it proves no
estimate at `Real.pi`, no almost-everywhere statement, and no instance of C1.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T29

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24

/-- The exact strict-cutoff endpoint layer `P_(E+1)-P_E`, represented on the
inclusive positive frequency range by `endpointLayerVector` below. -/
def endpointLayer
    (μ c : ℝ) (Q0 m E : ℕ) (h : ℕ) (α : ℝ) : ℂ :=
  cutoffFourierSum μ c Q0 m (E + 1) (h : ℤ) α -
    cutoffFourierSum μ c Q0 m E (h : ℤ) α

/-- Exact endpoint-layer vector, whose relevant coordinates are selected by
`inclusiveFrequencies m = {1,...,10^m}`. -/
def endpointLayerVector
    (μ c : ℝ) (Q0 m E : ℕ) (α : ℝ) : ℕ → ℂ :=
  fun h => endpointLayer μ c Q0 m E h α

/-- The exact inclusive frequency domain `1 <= h <= 10^m`. -/
def inclusiveFrequencies (m : ℕ) : Finset ℕ :=
  Finset.Icc 1 (decimalFrequency m)

/-- T24's translated-grid canonical binary blocks partitioning `[1,N)`. -/
def translatedCanonicalBlocks (N : ℕ) : List DyadicBlock :=
  canonicalDyadicPartition N

/-- The exact vector increment across the half-open endpoint block `[a,b)`. -/
def canonicalBlockVector
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (α : ℝ) : ℕ → ℂ :=
  fun h => cutoffFourierSum μ c Q0 m B.finish (h : ℤ) α -
    cutoffFourierSum μ c Q0 m B.start (h : ℤ) α

/-- Width weight `w([a,b)) = sqrt(b^2-a^2)`. -/
def widthWeight (B : DyadicBlock) : ℝ :=
  Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)

/-- Squared complex L2 energy on exactly `1 <= h <= 10^m`. -/
def blockSquaredEnergy
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (α : ℝ) : ℝ :=
  ∑ h ∈ inclusiveFrequencies m, ‖canonicalBlockVector μ c Q0 m B α h‖ ^ 2

/-- Width-normalized square function over exactly T24's canonical blocks. -/
def widthWeightedSquareFunction
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  ((translatedCanonicalBlocks N).map fun B =>
    blockSquaredEnergy μ c Q0 m B α / widthWeight B).sum

/-- The new premise at fixed `s,A`: one nonnegative constant controls every
positive integer scale `m` and cutoff `N`. -/
def WidthWeightedSquareFunctionAt
    (μ c : ℝ) (Q0 : ℕ) (α s A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
    widthWeightedSquareFunction μ c Q0 m N α ≤
      A * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N

/-- Quantifier order: `forall s, exists A_s, forall positive m,N`. The witness
may depend on `μ,c,Q0,α,s`, but not on a block or frequency. -/
def WidthWeightedSquareFunction
    (μ c : ℝ) (Q0 : ℕ) (α : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ A : ℝ, WidthWeightedSquareFunctionAt μ c Q0 α s A

theorem endpointLayer_eq_T24_endpointIncrement
    (μ c : ℝ) (Q0 m E h : ℕ) (α : ℝ) :
    endpointLayer μ c Q0 m E h α =
      endpointIncrement μ c Q0 m E (h : ℤ) α := by
  rfl

theorem mem_exact_successorEndpointLayer_iff
    {μ c : ℝ} {Q0 m E : ℕ} {k : ℤ} :
    k ∈ sparseFrequencyCutoff μ c Q0 m (E + 1) ∧
        k ∉ sparseFrequencyCutoff μ c Q0 m E ↔
      ∃ q : OrderedLongPair,
        AdmissibleOrderedFrequency μ c Q0 m q ∧
          frequencyEndpoint q.2 = E ∧ signedDecimalFrequency q = k := by
  exact mem_cutoff_succ_not_cutoff_iff_endpoint

theorem mem_inclusiveFrequencies_iff
    {m h : ℕ} : h ∈ inclusiveFrequencies m ↔
      1 ≤ h ∧ h ≤ 10 ^ m := by
  simp [inclusiveFrequencies, decimalFrequency]

theorem translatedCanonicalBlock_spec
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    1 ≤ B.start ∧ B.finish = B.start + 2 ^ B.level ∧
      2 ^ B.level ∣ B.start - 1 := by
  have hB' : B ∈ canonicalDyadicPartition N := hB
  exact ⟨canonicalDyadicPartition_start_pos hB', rfl,
    canonicalDyadicPartition_aligned hB'⟩

theorem widthWeight_eq_endpoints (B : DyadicBlock) :
    widthWeight B =
      Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) := by
  rfl

theorem canonicalBlockVector_eq_sum_endpointLayer
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (h : ℕ) (α : ℝ) :
    canonicalBlockVector μ c Q0 m B α h =
      ∑ E ∈ Finset.Ico B.start B.finish,
        endpointLayer μ c Q0 m E h α := by
  simpa only [canonicalBlockVector, endpointLayer,
    endpointIncrement, dyadicBlockIncrement] using
      dyadicBlockIncrement_eq_sum_endpointIncrement
        μ c Q0 m B (h : ℤ) α

theorem widthWeightedSquareFunctionAt_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) (α s A : ℝ) :
    WidthWeightedSquareFunctionAt μ c Q0 α s A ↔
      0 ≤ A ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        (((canonicalDyadicPartition N).map fun B =>
          (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖cutoffFourierSum μ c Q0 m B.finish (h : ℤ) α -
              cutoffFourierSum μ c Q0 m B.start (h : ℤ) α‖ ^ 2) /
            Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum) ≤
          A * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
  rfl

theorem widthWeightedSquareFunction_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) (α : ℝ) :
    WidthWeightedSquareFunction μ c Q0 α ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ A : ℝ, 0 ≤ A ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          (((canonicalDyadicPartition N).map fun B =>
            (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
              ‖cutoffFourierSum μ c Q0 m B.finish (h : ℤ) α -
                cutoffFourierSum μ c Q0 m B.start (h : ℤ) α‖ ^ 2) /
              Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum) ≤
            A * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
  rfl

/- The remaining lemmas prove the deterministic binary weight budget and the
weighted Cauchy--Schwarz implication. -/

theorem widthWeight_nonneg (B : DyadicBlock) : 0 ≤ widthWeight B := by
  exact Real.sqrt_nonneg _

theorem canonical_widthWeight_pos
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    0 < widthWeight B := by
  have hstart : 1 ≤ B.start := canonicalDyadicPartition_start_pos hB
  have hlength : 0 < B.blockLength := by
    simp [DyadicBlock.blockLength]
  have hfinish : B.start < B.finish := by
    simp only [DyadicBlock.finish]
    omega
  unfold widthWeight
  apply Real.sqrt_pos.2
  have hstart' : (0 : ℝ) ≤ B.start := by positivity
  have hfinish' : (B.start : ℝ) < B.finish := by exact_mod_cast hfinish
  nlinarith

theorem dyadicPartitionFrom_finish_le
    {q : ℕ} {js : List ℕ} {B : DyadicBlock}
    (hB : B ∈ dyadicPartitionFrom q js) :
    B.finish ≤ q + dyadicLevelSum js + 1 := by
  induction js generalizing q with
  | nil => simp [dyadicPartitionFrom] at hB
  | cons j js ih =>
      simp only [dyadicPartitionFrom, List.mem_cons] at hB
      rcases hB with rfl | hB
      · simp only [DyadicBlock.finish, DyadicBlock.blockLength,
          dyadicLevelSum, List.map_cons, List.sum_cons]
        omega
      · have htail := ih (q := q + 2 ^ j) hB
        simp only [dyadicLevelSum, List.map_cons, List.sum_cons] at htail ⊢
        omega

theorem canonical_finish_le
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    B.finish ≤ N := by
  cases N with
  | zero => simp [translatedCanonicalBlocks, canonicalDyadicPartition,
      dyadicPartitionFrom] at hB
  | succ N =>
      have hfinish := dyadicPartitionFrom_finish_le (q := 0)
        (js := N.bitIndices.reverse) hB
      simp only [dyadicLevelSum] at hfinish
      simpa using hfinish

theorem sum_range_two_pow (j : ℕ) :
    ∑ k ∈ Finset.range j, 2 ^ k = 2 ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have : 1 ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      omega

theorem dyadicLevelSum_lt_two_pow
    {j : ℕ} {js : List ℕ} (hjs : js.Nodup)
    (hlt : ∀ k ∈ js, k < j) :
    dyadicLevelSum js < 2 ^ j := by
  have hsubset : js.toFinset ⊆ Finset.range j := by
    intro k hk
    rw [List.mem_toFinset] at hk
    exact Finset.mem_range.2 (hlt k hk)
  have hsum_le : (js.toFinset.sum fun k => 2 ^ k) ≤
      ∑ k ∈ Finset.range j, 2 ^ k :=
    Finset.sum_le_sum_of_subset hsubset
  rw [List.sum_toFinset (fun k => 2 ^ k) hjs] at hsum_le
  rw [sum_range_two_pow] at hsum_le
  have hpow : 0 < 2 ^ j := pow_pos (by omega) _
  simp only [dyadicLevelSum]
  omega

theorem sqrt_add_geometric_step
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hRM : R ≤ M) :
    Real.sqrt M + (1 + Real.sqrt 2) * Real.sqrt R ≤
      (1 + Real.sqrt 2) * Real.sqrt (M + R) := by
  have hsqrt_le : Real.sqrt R ≤ Real.sqrt M := Real.sqrt_le_sqrt hRM
  have hxy : Real.sqrt M * Real.sqrt R ≤ M := by
    calc
      Real.sqrt M * Real.sqrt R ≤ Real.sqrt M * Real.sqrt M :=
        mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)
      _ = M := Real.mul_self_sqrt hM
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have htwo : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hMsq : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM
  have hRsq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
  have hsumSq : (Real.sqrt (M + R)) ^ 2 = M + R :=
    Real.sq_sqrt (add_nonneg hM hR)
  have hC : 0 ≤ 1 + Real.sqrt 2 := by positivity
  calc
    (Real.sqrt M + (1 + Real.sqrt 2) * Real.sqrt R) ^ 2 =
        M + (1 + Real.sqrt 2) ^ 2 * R +
          2 * (1 + Real.sqrt 2) * (Real.sqrt M * Real.sqrt R) := by
      rw [add_sq, mul_pow, hMsq, hRsq]
      ring
    _ ≤ M + (1 + Real.sqrt 2) ^ 2 * R +
          2 * (1 + Real.sqrt 2) * M := by
      gcongr
    _ = (1 + Real.sqrt 2) ^ 2 * (M + R) := by
      nlinarith
    _ = ((1 + Real.sqrt 2) * Real.sqrt (M + R)) ^ 2 := by
      rw [mul_pow, hsumSq]

theorem descending_levelSqrtSum_le
    (js : List ℕ) (hdesc : js.Pairwise fun j k => k < j) :
    (js.map fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)).sum ≤
      (1 + Real.sqrt 2) * Real.sqrt (dyadicLevelSum js : ℝ) := by
  induction js with
  | nil => simp [dyadicLevelSum]
  | cons j js ih =>
      rw [List.pairwise_cons] at hdesc
      have hRltNat : dyadicLevelSum js < 2 ^ j :=
        dyadicLevelSum_lt_two_pow hdesc.2.nodup hdesc.1
      have hRle : (dyadicLevelSum js : ℝ) ≤ (2 ^ j : ℕ) := by
        exact_mod_cast hRltNat.le
      calc
        ((j :: js).map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum =
            Real.sqrt ((2 ^ j : ℕ) : ℝ) +
              (js.map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum := by simp
        _ ≤ Real.sqrt ((2 ^ j : ℕ) : ℝ) +
              (1 + Real.sqrt 2) * Real.sqrt (dyadicLevelSum js : ℝ) :=
          add_le_add le_rfl (ih hdesc.2)
        _ ≤ (1 + Real.sqrt 2) *
              Real.sqrt ((2 ^ j : ℕ) + dyadicLevelSum js : ℝ) :=
          sqrt_add_geometric_step (by positivity) (by positivity) hRle
        _ = (1 + Real.sqrt 2) *
              Real.sqrt (dyadicLevelSum (j :: js) : ℝ) := by
          simp [dyadicLevelSum]

theorem canonical_widthWeight_le
    {N : ℕ} {B : DyadicBlock} (hB : B ∈ translatedCanonicalBlocks N) :
    widthWeight B ≤
      Real.sqrt (2 * (N : ℝ)) * Real.sqrt (B.blockLength : ℝ) := by
  have hfinish := canonical_finish_le hB
  have hstartFinish : B.start ≤ B.finish := by
    simp [DyadicBlock.finish]
  have hfinishEq : (B.finish : ℝ) = B.start + B.blockLength := by
    simp [DyadicBlock.finish]
  have hfinish' : (B.finish : ℝ) ≤ N := by exact_mod_cast hfinish
  have hstartFinish' : (B.start : ℝ) ≤ B.finish := by
    exact_mod_cast hstartFinish
  unfold widthWeight
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * (N : ℝ))]
  apply Real.sqrt_le_sqrt
  nlinarith

theorem canonical_widthWeight_sum_le
    {N : ℕ} (hN : 1 ≤ N) :
    ((translatedCanonicalBlocks N).map widthWeight).sum ≤
      (2 + Real.sqrt 2) * (N : ℝ) := by
  let blocks := translatedCanonicalBlocks N
  let levels := (N - 1).bitIndices.reverse
  have hpoint : (blocks.map widthWeight).sum ≤
      (blocks.map fun B =>
        Real.sqrt (2 * (N : ℝ)) * Real.sqrt (B.blockLength : ℝ)).sum := by
    apply list_sum_map_le_sum_map
    intro B hB
    exact canonical_widthWeight_le hB
  have hfactor :
      (blocks.map fun B =>
        Real.sqrt (2 * (N : ℝ)) * Real.sqrt (B.blockLength : ℝ)).sum =
      Real.sqrt (2 * (N : ℝ)) *
        (blocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum := by
    rw [List.sum_map_mul_left]
  have hlevels : (blocks.map DyadicBlock.level) = levels := by
    exact canonicalDyadicPartition_levels N
  have hsqrtLevels :
      (blocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum =
        (levels.map fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)).sum := by
    have := congrArg
      (fun xs : List ℕ => (xs.map fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)).sum)
      hlevels
    simpa [DyadicBlock.blockLength, List.map_map] using this
  have hdesc : levels.Pairwise fun j k => k < j := by
    exact Nat.bitIndices_sorted.pairwise.reverse
  have hlevelBound := descending_levelSqrtSum_le levels hdesc
  have hlevelSum : dyadicLevelSum levels = N - 1 := by
    simp [levels, dyadicLevelSum]
  rw [hlevelSum] at hlevelBound
  have hsqrtSub : Real.sqrt ((N - 1 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le N 1
  have hsqrtTwoN : Real.sqrt (2 * (N : ℝ)) =
      Real.sqrt 2 * Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtNSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  calc
    (blocks.map widthWeight).sum ≤
        (blocks.map fun B => Real.sqrt (2 * (N : ℝ)) *
          Real.sqrt (B.blockLength : ℝ)).sum := hpoint
    _ = Real.sqrt (2 * (N : ℝ)) *
          (blocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum := hfactor
    _ = Real.sqrt (2 * (N : ℝ)) *
          (levels.map fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)).sum := by rw [hsqrtLevels]
    _ ≤ Real.sqrt (2 * (N : ℝ)) *
          ((1 + Real.sqrt 2) * Real.sqrt ((N - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlevelBound (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 * (N : ℝ)) *
          ((1 + Real.sqrt 2) * Real.sqrt (N : ℝ)) := by
      gcongr
    _ = (2 + Real.sqrt 2) * (N : ℝ) := by
      rw [hsqrtTwoN]
      calc
        Real.sqrt 2 * Real.sqrt (N : ℝ) *
            ((1 + Real.sqrt 2) * Real.sqrt (N : ℝ)) =
            (Real.sqrt 2 * (1 + Real.sqrt 2)) *
              (Real.sqrt (N : ℝ)) ^ 2 := by ring
        _ = (2 + Real.sqrt 2) * (N : ℝ) := by
          rw [hsqrtNSq]
          nlinarith

/-- The sharper T27 geometric constant. The preceding bound is a reusable
one-line consequence of the whole binary expansion; this proof separates the
largest block and retains the negative tail-width term. -/
theorem canonical_widthWeight_sum_le_sharp
    {N : ℕ} (hN : 1 ≤ N) :
    ((translatedCanonicalBlocks N).map widthWeight).sum ≤
      ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) := by
  let blocks := translatedCanonicalBlocks N
  let levels := (N - 1).bitIndices.reverse
  change (blocks.map widthWeight).sum ≤
    ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ)
  have hlevels : blocks.map DyadicBlock.level = levels :=
    canonicalDyadicPartition_levels N
  have hlevelSum : dyadicLevelSum levels = N - 1 := by
    simp [levels, dyadicLevelSum]
  have hdesc : levels.Pairwise fun j k => k < j := by
    exact Nat.bitIndices_sorted.pairwise.reverse
  cases hjs : levels with
  | nil =>
      have hlen : blocks.length = 0 := by
        have := congrArg List.length hlevels
        simpa [hjs] using this
      have hblocks : blocks = [] := by
        cases hb : blocks with
        | nil => rfl
        | cons B bs => simp [hb] at hlen
      rw [hblocks]
      simp
      positivity
  | cons j js =>
      let M : ℕ := 2 ^ j
      let R : ℕ := dyadicLevelSum js
      let tailBlocks : List DyadicBlock := dyadicPartitionFrom M js
      have hsource : (N - 1).bitIndices.reverse = j :: js := by
        simpa [levels] using hjs
      have hblocks : blocks = ⟨1, j⟩ :: tailBlocks := by
        dsimp [blocks, translatedCanonicalBlocks, canonicalDyadicPartition,
          tailBlocks, M]
        rw [hsource]
        simp [dyadicPartitionFrom]
      have hdescCons : (j :: js).Pairwise fun u v => v < u := by
        simpa [hjs] using hdesc
      rw [List.pairwise_cons] at hdescCons
      have hRlt : R < M := by
        exact dyadicLevelSum_lt_two_pow hdescCons.2.nodup hdescCons.1
      have hsumNat : M + R = N - 1 := by
        simpa [hjs, M, R, dyadicLevelSum] using hlevelSum
      have hNdecomp : N = M + R + 1 := by
        omega
      have hfirst : widthWeight (⟨1, j⟩ : DyadicBlock) ≤ (M : ℝ) + 1 := by
        unfold widthWeight
        apply (Real.sqrt_le_iff).2
        constructor
        · positivity
        · simp only [DyadicBlock.finish, DyadicBlock.blockLength, M]
          push_cast
          ring_nf
          nlinarith [show (0 : ℝ) ≤ M by positivity]
      have htailPoint : (tailBlocks.map widthWeight).sum ≤
          (tailBlocks.map fun B =>
            Real.sqrt (2 * (N : ℝ)) * Real.sqrt (B.blockLength : ℝ)).sum := by
        apply list_sum_map_le_sum_map
        intro B hB
        apply canonical_widthWeight_le
        change B ∈ blocks
        rw [hblocks]
        simp [hB]
      have htailFactor :
          (tailBlocks.map fun B =>
            Real.sqrt (2 * (N : ℝ)) * Real.sqrt (B.blockLength : ℝ)).sum =
          Real.sqrt (2 * (N : ℝ)) *
            (tailBlocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum := by
        rw [List.sum_map_mul_left]
      have htailLevels : tailBlocks.map DyadicBlock.level = js := by
        exact dyadicPartitionFrom_levels M js
      have htailSqrt :
          (tailBlocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum =
            (js.map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum := by
        have := congrArg
          (fun xs : List ℕ =>
            (xs.map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum)
          htailLevels
        simpa [DyadicBlock.blockLength, List.map_map] using this
      have hlevelBound := descending_levelSqrtSum_le js hdescCons.2
      have htail : (tailBlocks.map widthWeight).sum ≤
          Real.sqrt (2 * (N : ℝ)) *
            ((1 + Real.sqrt 2) * Real.sqrt (R : ℝ)) := by
        calc
          (tailBlocks.map widthWeight).sum ≤
              (tailBlocks.map fun B => Real.sqrt (2 * (N : ℝ)) *
                Real.sqrt (B.blockLength : ℝ)).sum := htailPoint
          _ = Real.sqrt (2 * (N : ℝ)) *
                (tailBlocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum :=
            htailFactor
          _ = Real.sqrt (2 * (N : ℝ)) *
                (js.map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum := by
            rw [htailSqrt]
          _ ≤ Real.sqrt (2 * (N : ℝ)) *
                ((1 + Real.sqrt 2) * Real.sqrt (R : ℝ)) := by
            gcongr
      have htwoR : 2 * R ≤ N := by omega
      have hsqrtConstraint :
          Real.sqrt 2 * Real.sqrt (R : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have hcast : (2 : ℝ) * R ≤ N := by exact_mod_cast htwoR
        have hsqrt := Real.sqrt_le_sqrt hcast
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hsqrt
        exact hsqrt
      have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      have hsqrtRSq : (Real.sqrt (R : ℝ)) ^ 2 = (R : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hsqrtNSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hfactorNonneg : 0 ≤
          (Real.sqrt (N : ℝ) - Real.sqrt 2 * Real.sqrt (R : ℝ)) *
            (((3 : ℝ) / 2 - 1 + Real.sqrt 2) * Real.sqrt (N : ℝ) -
              (Real.sqrt 2 / 2) * Real.sqrt (R : ℝ)) := by
        apply mul_nonneg
        · linarith
        · have hsqrtR : 0 ≤ Real.sqrt (R : ℝ) := Real.sqrt_nonneg _
          have hcoef : Real.sqrt 2 / 2 ≤
              ((3 : ℝ) / 2 - 1 + Real.sqrt 2) * Real.sqrt 2 := by
            nlinarith [hsqrtTwoSq, Real.sqrt_nonneg 2]
          have hleft := mul_le_mul_of_nonneg_right hcoef hsqrtR
          have hright := mul_le_mul_of_nonneg_left hsqrtConstraint
            (by positivity : 0 ≤ (3 : ℝ) / 2 - 1 + Real.sqrt 2)
          linarith
      have hfactorIdentity :
          (Real.sqrt (N : ℝ) - Real.sqrt 2 * Real.sqrt (R : ℝ)) *
              (((3 : ℝ) / 2 - 1 + Real.sqrt 2) * Real.sqrt (N : ℝ) -
                (Real.sqrt 2 / 2) * Real.sqrt (R : ℝ)) =
            (((3 : ℝ) / 2 + Real.sqrt 2) - 1) *
                (Real.sqrt (N : ℝ)) ^ 2 +
              (Real.sqrt (R : ℝ)) ^ 2 -
                (2 + Real.sqrt 2) *
                  (Real.sqrt (N : ℝ) * Real.sqrt (R : ℝ)) := by
        calc
          (Real.sqrt (N : ℝ) - Real.sqrt 2 * Real.sqrt (R : ℝ)) *
              (((3 : ℝ) / 2 - 1 + Real.sqrt 2) * Real.sqrt (N : ℝ) -
                (Real.sqrt 2 / 2) * Real.sqrt (R : ℝ)) =
              ((3 : ℝ) / 2 - 1 + Real.sqrt 2) *
                  (Real.sqrt (N : ℝ)) ^ 2 -
                (Real.sqrt 2 + (Real.sqrt 2) ^ 2) *
                  (Real.sqrt (N : ℝ) * Real.sqrt (R : ℝ)) +
                ((Real.sqrt 2) ^ 2 / 2) *
                  (Real.sqrt (R : ℝ)) ^ 2 := by ring
          _ = (((3 : ℝ) / 2 + Real.sqrt 2) - 1) *
                (Real.sqrt (N : ℝ)) ^ 2 +
              (Real.sqrt (R : ℝ)) ^ 2 -
                (2 + Real.sqrt 2) *
                  (Real.sqrt (N : ℝ) * Real.sqrt (R : ℝ)) := by
            rw [hsqrtTwoSq]
            ring
      have hanalytic :
          ((N : ℝ) - R) + (2 + Real.sqrt 2) *
              (Real.sqrt (N : ℝ) * Real.sqrt (R : ℝ)) ≤
            ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) := by
        rw [hfactorIdentity] at hfactorNonneg
        rw [hsqrtNSq, hsqrtRSq] at hfactorNonneg
        nlinarith
      have hsqrtTwoN : Real.sqrt (2 * (N : ℝ)) =
          Real.sqrt 2 * Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hblocks]
      simp only [List.map_cons, List.sum_cons]
      calc
        widthWeight (⟨1, j⟩ : DyadicBlock) +
            (tailBlocks.map widthWeight).sum ≤
            ((M : ℝ) + 1) + Real.sqrt (2 * (N : ℝ)) *
              ((1 + Real.sqrt 2) * Real.sqrt (R : ℝ)) :=
          add_le_add hfirst htail
        _ = ((N : ℝ) - R) + (2 + Real.sqrt 2) *
              (Real.sqrt (N : ℝ) * Real.sqrt (R : ℝ)) := by
          rw [hsqrtTwoN]
          have hdecompReal : (N : ℝ) = M + R + 1 := by
            exact_mod_cast hNdecomp
          nlinarith [hsqrtTwoSq]
        _ ≤ ((3 : ℝ) / 2 + Real.sqrt 2) * (N : ℝ) := hanalytic

theorem nodup_of_map_nodup
    {ι κ : Type*} {f : ι → κ} {xs : List ι} (h : (xs.map f).Nodup) :
    xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at h ⊢
      exact ⟨fun hx => h.1 (List.mem_map.2 ⟨x, hx, rfl⟩), ih h.2⟩

theorem translatedCanonicalBlocks_nodup (N : ℕ) :
    (translatedCanonicalBlocks N).Nodup := by
  apply nodup_of_map_nodup (f := DyadicBlock.level)
  unfold translatedCanonicalBlocks
  rw [canonicalDyadicPartition_levels]
  simp

theorem cutoff_L1_sq_le_width_product
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) :
    (∑ h ∈ inclusiveFrequencies m,
        ‖cutoffFourierSum μ c Q0 m N (h : ℤ) α‖) ^ 2 ≤
      (decimalFrequency m : ℝ) *
        ((translatedCanonicalBlocks N).map widthWeight).sum *
          widthWeightedSquareFunction μ c Q0 m N α := by
  let blocks := translatedCanonicalBlocks N
  let blockSet := blocks.toFinset
  let frequencies := inclusiveFrequencies m
  let blockNorm : DyadicBlock → ℕ → ℝ := fun B h =>
    ‖canonicalBlockVector μ c Q0 m B α h‖
  have hblocksNodup : blocks.Nodup := translatedCanonicalBlocks_nodup N
  have hcard : (frequencies.card : ℝ) = (decimalFrequency m : ℝ) := by
    dsimp [frequencies, inclusiveFrequencies]
    norm_cast
    simp
  have htriangle := canonicalDyadicPartition_cutoff_L1_le
    μ c Q0 m N α hm hN
  have htriangle' :
      (∑ h ∈ frequencies,
          ‖cutoffFourierSum μ c Q0 m N (h : ℤ) α‖) ≤
        ∑ B ∈ blockSet, ∑ h ∈ frequencies, blockNorm B h := by
    have hblockSum :
        ((blocks.map fun B => dyadicBlockL1 μ c Q0 m B α).sum) =
          ∑ B ∈ blockSet, ∑ h ∈ frequencies, blockNorm B h := by
      calc
        ((blocks.map fun B => dyadicBlockL1 μ c Q0 m B α).sum) =
            ∑ B ∈ blocks.toFinset, dyadicBlockL1 μ c Q0 m B α :=
          (List.sum_toFinset
            (fun B => dyadicBlockL1 μ c Q0 m B α) hblocksNodup).symm
        _ = ∑ B ∈ blockSet, ∑ h ∈ frequencies, blockNorm B h := by
          apply Finset.sum_congr (by rfl)
          intro B hB
          rfl
    unfold vectorL1 at htriangle
    simpa only [frequencies, inclusiveFrequencies, blocks,
      translatedCanonicalBlocks] using htriangle.trans_eq hblockSum
  have hsumNonneg : 0 ≤ ∑ B ∈ blockSet, ∑ h ∈ frequencies, blockNorm B h := by
    positivity
  have hsquareTriangle :
      (∑ h ∈ frequencies,
          ‖cutoffFourierSum μ c Q0 m N (h : ℤ) α‖) ^ 2 ≤
        (∑ B ∈ blockSet, ∑ h ∈ frequencies, blockNorm B h) ^ 2 := by
    exact sq_le_sq₀ (by positivity) hsumNonneg |>.2 htriangle'
  let pairs := blockSet ×ˢ frequencies
  let f : DyadicBlock × ℕ → ℝ := fun x => Real.sqrt (widthWeight x.1)
  let g : DyadicBlock × ℕ → ℝ := fun x =>
    blockNorm x.1 x.2 / Real.sqrt (widthWeight x.1)
  have hproductSum :
      ∑ x ∈ pairs, f x * g x =
        ∑ B ∈ blockSet, ∑ h ∈ frequencies, blockNorm B h := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro B hB
    apply Finset.sum_congr rfl
    intro h hh
    have hBlist : B ∈ blocks := by
      simpa [blockSet] using hB
    have hw : 0 < widthWeight B := canonical_widthWeight_pos hBlist
    dsimp [f, g]
    field_simp
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq pairs f g
  rw [hproductSum] at hCS
  have hfSum :
      ∑ x ∈ pairs, f x ^ 2 =
        (decimalFrequency m : ℝ) *
          ∑ B ∈ blockSet, widthWeight B := by
    rw [Finset.sum_product]
    simp only [f, Real.sq_sqrt (widthWeight_nonneg _),
      Finset.sum_const, nsmul_eq_mul, hcard]
    rw [Finset.mul_sum]
  have hgSum :
      ∑ x ∈ pairs, g x ^ 2 =
        ∑ B ∈ blockSet,
          blockSquaredEnergy μ c Q0 m B α / widthWeight B := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro B hB
    have hBlist : B ∈ blocks := by simpa [blockSet] using hB
    have hw : 0 < widthWeight B := canonical_widthWeight_pos hBlist
    dsimp [g]
    calc
      (∑ y ∈ frequencies,
          (blockNorm B y / Real.sqrt (widthWeight B)) ^ 2) =
          ∑ y ∈ frequencies, blockNorm B y ^ 2 / widthWeight B := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [div_pow, Real.sq_sqrt hw.le]
      _ = (∑ y ∈ frequencies, blockNorm B y ^ 2) / widthWeight B := by
        rw [Finset.sum_div]
      _ = blockSquaredEnergy μ c Q0 m B α / widthWeight B := by
        rfl
  rw [hfSum, hgSum] at hCS
  have hweightList :
      ∑ B ∈ blockSet, widthWeight B =
        (blocks.map widthWeight).sum := by
    exact List.sum_toFinset widthWeight hblocksNodup
  have henergyList :
      ∑ B ∈ blockSet,
          blockSquaredEnergy μ c Q0 m B α / widthWeight B =
        widthWeightedSquareFunction μ c Q0 m N α := by
    unfold widthWeightedSquareFunction
    exact List.sum_toFinset
      (fun B => blockSquaredEnergy μ c Q0 m B α / widthWeight B)
      hblocksNodup
  rw [hweightList, henergyList] at hCS
  exact hsquareTriangle.trans hCS

theorem widthWeightedSquareFunction_nonneg
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    0 ≤ widthWeightedSquareFunction μ c Q0 m N α := by
  unfold widthWeightedSquareFunction
  induction translatedCanonicalBlocks N with
  | nil => simp
  | cons B blocks ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg
        (div_nonneg (by unfold blockSquaredEnergy; positivity)
          (widthWeight_nonneg B)) ih

/-- Fixed-constant deterministic transfer. Every domain, endpoint, weight,
frequency bound, and positivity condition is explicit in the premise above. -/
theorem widthWeightedSquareFunctionAt_implies_cutoff
    (μ c : ℝ) (Q0 : ℕ) (α s A : ℝ)
    (hweighted : WidthWeightedSquareFunctionAt μ c Q0 α s A) :
    ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
      (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
          ‖cutoffFourierSum μ c Q0 m N (h : ℤ) α‖) ≤
        Real.sqrt (((3 : ℝ) / 2 + Real.sqrt 2) * A) *
          (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
  intro m N hm hN
  let H : ℝ := decimalFrequency m
  let T : ℝ := scaleMatchedTarget s m N
  let C : ℝ := (3 : ℝ) / 2 + Real.sqrt 2
  let L : ℝ := ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ‖cutoffFourierSum μ c Q0 m N (h : ℤ) α‖
  have hA : 0 ≤ A := hweighted.1
  have hH : 0 ≤ H := by positivity
  have hTpos : 0 < T := by
    dsimp [T]
    unfold scaleMatchedTarget
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCA : 0 ≤ C * A := mul_nonneg hC hA
  have hX : 0 ≤ widthWeightedSquareFunction μ c Q0 m N α :=
    widthWeightedSquareFunction_nonneg μ c Q0 m N α
  have hweight := canonical_widthWeight_sum_le_sharp hN
  have hweightedAt := hweighted.2 m N hm hN
  have hsq := cutoff_L1_sq_le_width_product μ c Q0 m N α hm hN
  have hNT : (N : ℝ) ≤ T := by
    dsimp [T]
    unfold scaleMatchedTarget
    have htail : 0 ≤ (N : ℝ) ^ 2 * (10 : ℝ) ^ (-s * (m : ℝ)) := by
      positivity
    linarith
  have hsqFinal : L ^ 2 ≤ (Real.sqrt (C * A) * H * T) ^ 2 := by
    calc
      L ^ 2 ≤ H * ((translatedCanonicalBlocks N).map widthWeight).sum *
          widthWeightedSquareFunction μ c Q0 m N α := by
        simpa only [L, H, inclusiveFrequencies] using hsq
      _ ≤ H * (C * (N : ℝ)) *
          widthWeightedSquareFunction μ c Q0 m N α := by
        gcongr
      _ ≤ H * (C * (N : ℝ)) * (A * H * T) := by
        gcongr
      _ = (C * A * H ^ 2) * ((N : ℝ) * T) := by ring
      _ ≤ (C * A * H ^ 2) * (T ^ 2) := by
        gcongr
        nlinarith [mul_nonneg (sub_nonneg.mpr hNT) hTpos.le]
      _ = (Real.sqrt (C * A) * H * T) ^ 2 := by
        calc
          C * A * H ^ 2 * T ^ 2 = (C * A) * H ^ 2 * T ^ 2 := by ring
          _ = (Real.sqrt (C * A)) ^ 2 * H ^ 2 * T ^ 2 := by
            rw [Real.sq_sqrt hCA]
          _ = (Real.sqrt (C * A) * H * T) ^ 2 := by ring
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hright : 0 ≤ Real.sqrt (C * A) * H * T := by positivity
  have hfinal := (sq_le_sq₀ hL hright).mp hsqFinal
  simpa only [L, H, T, C] using hfinal

/-- Conditional specialization to `alpha=pi`. This theorem does not assert
that the width-weighted premise holds there. -/
theorem widthWeightedSquareFunction_pi_implies_T22
    (μ c : ℝ) (Q0 : ℕ)
    (hweighted : WidthWeightedSquareFunction μ c Q0 Real.pi) :
    CutoffScaleMatchedL1Bound μ c Q0 := by
  intro s hs0 hs1
  obtain ⟨A, hA⟩ := hweighted s hs0 hs1
  refine ⟨Real.sqrt (((3 : ℝ) / 2 + Real.sqrt 2) * A),
    Real.sqrt_nonneg _, ?_⟩
  exact widthWeightedSquareFunctionAt_implies_cutoff
    μ c Q0 Real.pi s A hA

/-- Final implication to T12, conditional only on the new width-weighted
premise. It proves neither that premise for `pi` nor C1. -/
theorem widthWeightedSquareFunction_pi_implies_T12
    (μ c : ℝ) (Q0 : ℕ)
    (hweighted : WidthWeightedSquareFunction μ c Q0 Real.pi) :
    ScaleMatchedL1Bound μ c Q0 := by
  exact (cutoffScaleMatchedL1Bound_iff_T12 μ c Q0).mp
    (widthWeightedSquareFunction_pi_implies_T22 μ c Q0 hweighted)

end Theory.PiDigits.LongLagBlockCollisionDecay.T29

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.mem_exact_successorEndpointLayer_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.mem_inclusiveFrequencies_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.translatedCanonicalBlock_spec
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.canonicalBlockVector_eq_sum_endpointLayer
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.widthWeightedSquareFunction_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.canonical_widthWeight_sum_le_sharp
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.cutoff_L1_sq_le_width_product
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.widthWeightedSquareFunctionAt_implies_cutoff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.widthWeightedSquareFunction_pi_implies_T22
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T29.widthWeightedSquareFunction_pi_implies_T12
