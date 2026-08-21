import TheoryLib.PiLacunaryNearReturnSparsity.T29FiniteCountTreeLeakage
import TheoryLib.PiLacunaryNearReturnSparsity.T33MovingRootTangent
import TheoryLib.PiPositiveLowerBlockDensity.T19T19MinimalDeBruijnFlow
import TheoryLib.PiDigits.T22ChampernowneDisjunctive

/-!
# An artificial single-stream moving-root obstruction

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module concerns an artificial base-10 stream (recorded ambiguity A14),
not the decimal expansion of `Real.pi`.  It makes no assertion of C2 or of
canonical A1.

It formalizes T35's staged single-stream mechanism with an equivalent
kernel-friendly stage realization: every fixed-length decimal seed is given a
long periodic segment.  This replaces T35's unformalized de Bruijn-cycle stage;
the proved conclusions and all count/error interfaces are stated directly for
the stream defined below.

Counts use overlapping first-start occurrences: a word may extend beyond the
sampled prefix, and only its start is required to be below the checkpoint.
-/

noncomputable section

open Finset Filter

namespace DecimalFactorComplexity.ArtificialStreamObstruction

open DecimalFactorComplexity.FiniteCountTreeLeakage
open DecimalFactorComplexity.MovingRootTangent
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T19
open Theory.PiDigits.T22

abbrev Digit := Fin 10
abbrev Word := List Digit
abbrev Stream := ℕ → Digit

/-- The overlapping first-`N`-starts count used throughout this module. -/
def firstStartCount (x : Stream) (N : ℕ) (w : Word) : ℕ :=
  blockCount x w N

/-- The occurrence indicator at one unrestricted start. -/
def startHit (x : Stream) (w : Word) (j : ℕ) : ℕ :=
  if ∀ i : Fin w.length, x (j + i) = w.get i then 1 else 0

/-- New occurrences contributed when the sampled-start checkpoint increases
from `N` to `M`. -/
def checkpointIncrement (x : Stream) (w : Word) (N M : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico N M, startHit x w j

/-- The cardinality definition of `blockCount`, rewritten as a sum over
ordinary natural-number starts. -/
theorem firstStartCount_eq_sum_startHit (x : Stream) (N : ℕ) (w : Word) :
    firstStartCount x N w = ∑ j ∈ Finset.range N, startHit x w j := by
  unfold firstStartCount blockCount startHit
  calc
    _ = ∑ n : Fin N,
        if ∀ i : Fin w.length, x (n.val + i) = w.get i then 1 else 0 := by
      exact (Finset.sum_boole
        (fun n : Fin N => ∀ i : Fin w.length, x (n.val + i) = w.get i)
        Finset.univ).symm
    _ = _ := by
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ =>
          if ∀ i : Fin w.length, x (j + i) = w.get i then 1 else 0) N

/-- Exact compatibility between two prefix checkpoints. -/
theorem firstStartCount_checkpoint_add (x : Stream) (w : Word) {N M : ℕ}
    (hNM : N ≤ M) :
    firstStartCount x M w =
      firstStartCount x N w + checkpointIncrement x w N M := by
  rw [firstStartCount_eq_sum_startHit, firstStartCount_eq_sum_startHit,
    checkpointIncrement]
  exact (Finset.sum_range_add_sum_Ico (fun j => startHit x w j) hNM).symm

/-- A prefix through `N + w.length` determines the overlapping first-start
count, including every factor that extends past start checkpoint `N`. -/
theorem firstStartCount_congr_prefix (x y : Stream) (N : ℕ) (w : Word)
    (hxy : ∀ k, k < N + w.length → x k = y k) :
    firstStartCount x N w = firstStartCount y N w := by
  rw [firstStartCount_eq_sum_startHit, firstStartCount_eq_sum_startHit]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  unfold startHit
  congr 1
  apply propext
  constructor
  · intro hx i
    rw [← hxy (j + i) (by omega)]
    exact hx i
  · intro hy i
    rw [hxy (j + i) (by omega)]
    exact hy i

/-- T29 encodes an appended digit as the low base-10 digit. -/
def decodedTuple : (n : ℕ) → Fin (10 ^ n) → DecimalWord n
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, a => Fin.snoc
      (decodedTuple n ((decimalAppendEquiv n).symm a).1)
      ((decimalAppendEquiv n).symm a).2

/-- List form of `decodedTuple`.  Decimal children become literal list
append, matching overlapping right extension. -/
def decodedWord (n : ℕ) (a : Fin (10 ^ n)) : Word :=
  List.ofFn (decodedTuple n a)

@[simp] theorem decodedWord_length (n : ℕ) (a : Fin (10 ^ n)) :
    (decodedWord n a).length = n := by simp [decodedWord]

@[simp] theorem decodedTuple_decimalChild (n : ℕ) (a : Fin (10 ^ n))
    (d : Digit) :
    decodedTuple (n + 1) (decimalChild n a d) =
      Fin.snoc (decodedTuple n a) d := by
  simp [decodedTuple, decimalChild]

theorem decodedTuple_injective (n : ℕ) :
    Function.Injective (decodedTuple n) := by
  induction n with
  | zero =>
      intro a b _
      apply Fin.ext
      omega
  | succ n ih =>
      intro a b hab
      let pa := (decimalAppendEquiv n).symm a
      let pb := (decimalAppendEquiv n).symm b
      have hparent : pa.1 = pb.1 := ih (by
        simpa [decodedTuple, pa, pb] using congrArg Fin.init hab)
      have hdigit : pa.2 = pb.2 := by
        simpa [decodedTuple, pa, pb] using congrFun hab (Fin.last n)
      have hp : pa = pb := Prod.ext hparent hdigit
      exact (decimalAppendEquiv n).symm.injective hp

/-- The recursive T29 decoding enumerates every decimal tuple exactly once. -/
def decodedTupleEquiv (n : ℕ) : Fin (10 ^ n) ≃ DecimalWord n :=
  Equiv.ofBijective (decodedTuple n)
    ((Fintype.bijective_iff_injective_and_card (decodedTuple n)).2
      ⟨decodedTuple_injective n, by simp⟩)

@[simp] theorem decodedTupleEquiv_apply (n : ℕ) (a : Fin (10 ^ n)) :
    decodedTupleEquiv n a = decodedTuple n a := rfl

@[simp] theorem decodedWord_decimalChild (n : ℕ) (a : Fin (10 ^ n))
    (d : Digit) :
    decodedWord (n + 1) (decimalChild n a d) = decodedWord n a ++ [d] := by
  have ht : decodedTuple (n + 1) (decimalChild n a d) =
      Fin.snoc (decodedTuple n a) d := by
    simp [decodedTuple, decimalChild]
  rw [decodedWord, decodedWord, ht, ofFn_snoc]

/-- The natural count tree cut from one stream at one sampled-start
checkpoint. -/
def streamCountTree (x : Stream) (N : ℕ) : NaturalDecimalCounts :=
  fun n a => firstStartCount x N (decodedWord n a)

/-- Every start contributes to exactly one length-`n` word. -/
theorem firstStartCount_total (x : Stream) (n N : ℕ) :
    ∑ u : DecimalWord n, firstStartCount x N (List.ofFn u) = N := by
  exact sum_blockCount_all_words x n N

/-- Exact outgoing conservation.  There is no endpoint loss because the
stream is infinite and only the start is restricted. -/
theorem firstStartCount_snoc (x : Stream) (n N : ℕ)
    (u : DecimalWord n) :
    ∑ d : Digit, firstStartCount x N (List.ofFn (Fin.snoc u d)) =
      firstStartCount x N (List.ofFn u) := by
  exact sum_snoc_blockCount x n N u

/-- Exact incoming endpoint identity. -/
theorem firstStartCount_cons_endpoint (x : Stream) (n N : ℕ)
    (u : DecimalWord n) :
    (∑ d : Digit, firstStartCount x N (List.ofFn (Fin.cons d u))) +
        blockHit x u 0 =
      firstStartCount x N (List.ofFn u) + blockHit x u N := by
  exact sum_cons_blockCount_endpoint x n N u

/-- The outgoing conservation identity in T29's numeric word encoding. -/
theorem streamCountTree_conservation (x : Stream) (N n : ℕ)
    (a : Fin (10 ^ n)) :
    streamCountTree x N n a =
      ∑ d : Digit, streamCountTree x N (n + 1) (decimalChild n a d) := by
  change firstStartCount x N (decodedWord n a) =
    ∑ d : Digit, firstStartCount x N
      (decodedWord (n + 1) (decimalChild n a d))
  simp_rw [decodedWord_decimalChild]
  have h := firstStartCount_snoc x n N (decodedTuple n a)
  rw [decodedWord]
  simpa only [ofFn_snoc] using h.symm

/-- Every stream prefix is literally a finite T29 base-10 count tree. -/
theorem streamCountTree_isFinite (x : Stream) (N depth : ℕ) :
    IsFiniteBase10CountTree (streamCountTree x N) depth := by
  intro n _ a
  exact streamCountTree_conservation x N n a

/-! ## One explicit staged stream -/

/-- Stage `q` uses words of positive length `q+1`. -/
def stageOrder (q : ℕ) : ℕ := q + 1

/-- Starts not lying safely inside the current repeated-seed segments are
charged to this error budget. -/
def stageErrorBudget (A q : ℕ) : ℕ :=
  A + 2 * stageOrder q * 10 ^ stageOrder q

/-- Each seed is repeated enough times to dominate every earlier and boundary
start.  The final `+3` leaves a nonempty two-word-safe core. -/
def stageRepetitions (A q : ℕ) : ℕ :=
  stageOrder q ^ 3 * (stageErrorBudget A q + 1) + 3

/-- Length of one repeated-seed segment. -/
def seedSegmentLength (A q : ℕ) : ℕ :=
  stageRepetitions A q * stageOrder q

/-- Total length of stage `q`, one segment for every length-`q+1` decimal
seed. -/
def stageLength (A q : ℕ) : ℕ :=
  10 ^ stageOrder q * seedSegmentLength A q

/-- Digit at a local stage coordinate.  The quotient chooses the seed and the
residue chooses a cyclic coordinate in that seed. -/
def stageDigit (A q : ℕ) (i : Fin (stageLength A q)) : Digit :=
  let segmentLength := seedSegmentLength A q
  let seed : Fin (10 ^ stageOrder q) :=
    ⟨i.val / segmentLength, by
      have hseg : 0 < segmentLength := by
        dsimp only [segmentLength]
        unfold seedSegmentLength stageRepetitions stageOrder
        positivity
      have hi := i.isLt
      unfold stageLength at hi
      exact (Nat.div_lt_iff_lt_mul hseg).2 (by simpa [Nat.mul_comm] using hi)⟩
  let phase : Fin (stageOrder q) :=
    ⟨i.val % segmentLength % stageOrder q, by
      unfold stageOrder
      exact Nat.mod_lt _ (by omega)⟩
  decodedTuple (stageOrder q) seed phase

/-- The finite block appended at stage `q`. -/
def stageBlockFrom (A q : ℕ) : Word :=
  List.ofFn (stageDigit A q)

/-- Absolute starts of stages. -/
def stageStart : ℕ → ℕ
  | 0 => 0
  | q + 1 => stageStart q + stageLength (stageStart q) q

/-- The actual blocks of the one-stream construction. -/
def stageBlock (q : ℕ) : Word := stageBlockFrom (stageStart q) q

/-- One infinite decimal stream, fixed before every checkpoint quantifier. -/
def artificialStream : Stream := concatStream stageBlock

/-- The sampled-start checkpoint is the end of stage `q`. -/
def sampledCheckpoint (q : ℕ) : ℕ := stageStart (q + 1)

/-- A finite prefix this long determines all counts through twice the stage
order. -/
def inspectionCheckpoint (q : ℕ) : ℕ :=
  sampledCheckpoint q + 2 * stageOrder q

@[simp] theorem stageBlockFrom_length (A q : ℕ) :
    (stageBlockFrom A q).length = stageLength A q := by
  simp [stageBlockFrom]

@[simp] theorem stageBlock_length (q : ℕ) :
    (stageBlock q).length = stageLength (stageStart q) q := by
  simp [stageBlock]

theorem stageLength_pos (A q : ℕ) : 0 < stageLength A q := by
  unfold stageLength seedSegmentLength stageRepetitions stageOrder
  positivity

theorem stageBlock_ne_nil (q : ℕ) : stageBlock q ≠ [] := by
  intro h
  have hlen := stageBlock_length q
  rw [h] at hlen
  have hpos := stageLength_pos (stageStart q) q
  simp only [List.length_nil] at hlen
  omega

@[simp] theorem stageStart_succ (q : ℕ) :
    stageStart (q + 1) = stageStart q + stageLength (stageStart q) q := rfl

theorem stageStart_strictMono : StrictMono stageStart := by
  apply strictMono_nat_of_lt_succ
  intro q
  rw [stageStart_succ]
  exact Nat.lt_add_of_pos_right (stageLength_pos _ _)

theorem finiteConcat_stageBlock_length (q : ℕ) :
    (finiteConcat stageBlock q).length = stageStart q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [finiteConcat_succ, List.length_append, ih, stageBlock_length,
        stageStart_succ]

theorem sampledCheckpoint_strictMono : StrictMono sampledCheckpoint := by
  intro i j hij
  exact stageStart_strictMono (Nat.add_lt_add_right hij 1)

theorem sampledCheckpoint_lt_inspectionCheckpoint (q : ℕ) :
    sampledCheckpoint q < inspectionCheckpoint q := by
  unfold inspectionCheckpoint stageOrder
  omega

theorem inspectionCheckpoint_strictMono : StrictMono inspectionCheckpoint := by
  apply strictMono_nat_of_lt_succ
  intro q
  have hs : sampledCheckpoint q < sampledCheckpoint (q + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      sampledCheckpoint_strictMono (Nat.lt_succ_self q)
  unfold inspectionCheckpoint stageOrder
  omega

/-- The displayed inspection prefix determines every row entry through twice
the moving-root depth. -/
theorem inspectionCheckpoint_determines_row (q : ℕ) (x : Stream) (w : Word)
    (hw : w.length ≤ 2 * stageOrder q)
    (hx : ∀ j, j < inspectionCheckpoint q → x j = artificialStream j) :
    firstStartCount x (sampledCheckpoint q) w =
      firstStartCount artificialStream (sampledCheckpoint q) w := by
  apply firstStartCount_congr_prefix
  intro k hk
  apply hx k
  unfold inspectionCheckpoint
  omega

/-- Exact access to every digit of every finite stage inside the single
stream. -/
theorem artificialStream_stage_digit (q i : ℕ)
    (hi : i < stageLength (stageStart q) q) :
    artificialStream (stageStart q + i) =
      stageDigit (stageStart q) q ⟨i, hi⟩ := by
  have h := enumeratedBlock_occursAt_concatStream stageBlock stageBlock_ne_nil
    q i (by simpa using hi)
  rw [finiteConcat_stageBlock_length] at h
  simpa [artificialStream, stageBlock, stageBlockFrom] using h

/-! ## Safe starts and the exact stage error budget -/

/-- The stage has enough repetitions to leave two full stage orders after
every safe start. -/
theorem twice_stageOrder_le_seedSegmentLength (A q : ℕ) :
    2 * stageOrder q ≤ seedSegmentLength A q := by
  have hrep : 3 ≤ stageRepetitions A q := by
    unfold stageRepetitions
    omega
  have hm : 2 * stageOrder q ≤ 3 * stageOrder q := by
    exact Nat.mul_le_mul_right (stageOrder q) (by omega)
  exact hm.trans (Nat.mul_le_mul_right (stageOrder q) hrep)

/-- Absolute starts represented by a seed-segment number and an offset that
leaves at least two stage orders before the segment boundary. -/
def stageSafeStarts (q : ℕ) : Finset ℕ :=
  let A := stageStart q
  let m := stageOrder q
  let L := seedSegmentLength A q
  (Finset.univ : Finset (Fin (10 ^ m) × Fin (L - 2 * m))).image
    (fun st => A + st.1.val * L + st.2.val)

theorem stageSafeCoordinate_injective (q : ℕ) :
    Function.Injective
      (fun st : Fin (10 ^ stageOrder q) ×
          Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q) =>
        stageStart q + st.1.val * seedSegmentLength (stageStart q) q +
          st.2.val) := by
  intro a b hab
  dsimp only at hab
  have hab' :
      a.1.val * seedSegmentLength (stageStart q) q + a.2.val =
        b.1.val * seedSegmentLength (stageStart q) q + b.2.val :=
    by omega
  let L := seedSegmentLength (stageStart q) q
  have haL : a.2.val < L :=
    a.2.isLt.trans_le (Nat.sub_le L (2 * stageOrder q))
  have hbL : b.2.val < L :=
    b.2.isLt.trans_le (Nat.sub_le L (2 * stageOrder q))
  have hoff : a.2.val = b.2.val := by
    have hmod := congrArg (fun z => z % L) hab'
    simpa [L, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt haL,
      Nat.mod_eq_of_lt hbL] using hmod
  have hseg : a.1.val = b.1.val := by
    rw [hoff] at hab'
    have hmul := Nat.add_right_cancel hab'
    have hLpos : 0 < seedSegmentLength (stageStart q) q := by
      unfold seedSegmentLength stageRepetitions stageOrder
      positivity
    exact Nat.eq_of_mul_eq_mul_right hLpos hmul
  exact Prod.ext (Fin.ext hseg) (Fin.ext hoff)

theorem stageSafeStarts_card (q : ℕ) :
    (stageSafeStarts q).card =
      10 ^ stageOrder q *
        (seedSegmentLength (stageStart q) q - 2 * stageOrder q) := by
  rw [stageSafeStarts, Finset.card_image_of_injective _
    (stageSafeCoordinate_injective q), Finset.card_univ, Fintype.card_prod]
  simp

theorem stageSafeStarts_subset_checkpoint (q : ℕ) :
    stageSafeStarts q ⊆ Finset.range (sampledCheckpoint q) := by
  intro j hj
  rw [stageSafeStarts, Finset.mem_image] at hj
  obtain ⟨st, _, rfl⟩ := hj
  rw [Finset.mem_range, sampledCheckpoint, stageStart_succ]
  have hoff : st.2.val < seedSegmentLength (stageStart q) q :=
    st.2.isLt.trans_le
      (Nat.sub_le (seedSegmentLength (stageStart q) q) (2 * stageOrder q))
  have hseg := st.1.isLt
  unfold stageLength
  have hmul := Nat.mul_le_mul_right (seedSegmentLength (stageStart q) q)
    (Nat.succ_le_iff.mpr hseg)
  have hlocal :
      st.1.val * seedSegmentLength (stageStart q) q + st.2.val <
        (st.1.val + 1) * seedSegmentLength (stageStart q) q := by
    rw [Nat.add_mul]
    omega
  simpa [Nat.add_assoc] using
    Nat.add_lt_add_left (hlocal.trans_le hmul) (stageStart q)

/-- Every sampled start not in the safe repeated-seed core.  This includes
all starts before stage `q` and the final `2 * stageOrder q` starts of each
seed segment. -/
def stageErrorStarts (q : ℕ) : Finset ℕ :=
  Finset.range (sampledCheckpoint q) \ stageSafeStarts q

theorem stageErrorStarts_card (q : ℕ) :
    (stageErrorStarts q).card = stageErrorBudget (stageStart q) q := by
  rw [stageErrorStarts, Finset.card_sdiff_of_subset
    (stageSafeStarts_subset_checkpoint q), Finset.card_range,
    stageSafeStarts_card]
  have htwo := twice_stageOrder_le_seedSegmentLength (stageStart q) q
  rw [sampledCheckpoint, stageStart_succ, stageLength, stageErrorBudget,
    Nat.mul_sub_left_distrib]
  have hprod :
      10 ^ stageOrder q * (2 * stageOrder q) ≤
        10 ^ stageOrder q * seedSegmentLength (stageStart q) q :=
    Nat.mul_le_mul_left _ htwo
  rw [Nat.add_sub_assoc (Nat.sub_le _ _) (stageStart q),
    Nat.sub_sub_self hprod]
  ac_rfl

/-- Count contributed by safe starts of stage `q`. -/
def stageCoreCount (q : ℕ) (w : Word) : ℕ :=
  ∑ j ∈ stageSafeStarts q, startHit artificialStream w j

/-- Count contributed by all starts charged to the stage error budget. -/
def stageErrorCount (q : ℕ) (w : Word) : ℕ :=
  ∑ j ∈ stageErrorStarts q, startHit artificialStream w j

/-- Actual overlapping counts split exactly into the repeated-seed core and
the earlier/boundary error, with no condition on factors crossing old stages. -/
theorem firstStartCount_sampledCheckpoint_eq_core_add_error (q : ℕ)
    (w : Word) :
    firstStartCount artificialStream (sampledCheckpoint q) w =
      stageCoreCount q w + stageErrorCount q w := by
  rw [firstStartCount_eq_sum_startHit]
  unfold stageCoreCount stageErrorCount stageErrorStarts
  have h := Finset.sum_sdiff (f := fun j => startHit artificialStream w j)
    (stageSafeStarts_subset_checkpoint q)
  simpa [add_comm] using h.symm

theorem stageErrorCount_le_budget (q : ℕ) (w : Word) :
    stageErrorCount q w ≤ stageErrorBudget (stageStart q) q := by
  calc
    stageErrorCount q w ≤ (stageErrorStarts q).card := by
      unfold stageErrorCount
      simpa using Finset.sum_le_card_nsmul (stageErrorStarts q)
        (fun j => startHit artificialStream w j) 1 (by
          intro j hj
          simp only [startHit]
          split <;> simp)
    _ = stageErrorBudget (stageStart q) q := stageErrorStarts_card q

/-- At one fixed start, exactly one length-`n` tuple occurs. -/
theorem sum_startHit_all_words (x : Stream) (j n : ℕ) :
    ∑ u : DecimalWord n, startHit x (List.ofFn u) j = 1 := by
  let target : DecimalWord n := wordAt x j n
  have hhit (u : DecimalWord n) :
      startHit x (List.ofFn u) j = if target = u then 1 else 0 := by
    unfold startHit
    congr 1
    apply propext
    constructor
    · intro h
      funext i
      simpa [target, wordAt] using h (Fin.cast (by simp) i)
    · intro h i
      simpa [target, wordAt] using congrFun h (Fin.cast (by simp) i)
  simp_rw [hhit]
  simp

/-- Summed over all words, the error counts equal the number of charged
starts, rather than one error budget per word. -/
theorem sum_stageErrorCount_all_words (q n : ℕ) :
    ∑ a : Fin (10 ^ n), stageErrorCount q (decodedWord n a) =
      stageErrorBudget (stageStart q) q := by
  calc
    (∑ a : Fin (10 ^ n), stageErrorCount q (decodedWord n a)) =
        ∑ u : DecimalWord n, stageErrorCount q (List.ofFn u) := by
      exact Fintype.sum_equiv (decodedTupleEquiv n)
        (fun a => stageErrorCount q (decodedWord n a))
        (fun u => stageErrorCount q (List.ofFn u)) (fun _ => rfl)
    _ = (stageErrorStarts q).card := by
      unfold stageErrorCount
      rw [Finset.sum_comm]
      simp_rw [sum_startHit_all_words]
      simp
    _ = stageErrorBudget (stageStart q) q := stageErrorStarts_card q

/-! ## Periodicity and deterministic successors on the safe core -/

theorem stageOrder_pos (q : ℕ) : 0 < stageOrder q := by
  unfold stageOrder
  omega

/-- Cyclic addition by a phase, viewed as a permutation of stage positions. -/
noncomputable def cyclicIndexEquiv (q : ℕ) (phase : Fin (stageOrder q)) :
    Fin (stageOrder q) ≃ Fin (stageOrder q) := by
  letI : NeZero (stageOrder q) := ⟨(stageOrder_pos q).ne'⟩
  exact (ZMod.finEquiv (stageOrder q)).toEquiv |>.trans
    ((Equiv.addLeft ((ZMod.finEquiv (stageOrder q)) phase)).trans
      (ZMod.finEquiv (stageOrder q)).toEquiv.symm)

@[simp] theorem cyclicIndexEquiv_val (q : ℕ)
    (phase i : Fin (stageOrder q)) :
    (cyclicIndexEquiv q phase i).val =
      (phase.val + i.val) % stageOrder q := by
  letI : NeZero (stageOrder q) := ⟨(stageOrder_pos q).ne'⟩
  simp [cyclicIndexEquiv]
  exact Fin.val_add phase i

/-- Rotate a decimal tuple so that `phase` becomes coordinate zero. -/
noncomputable def rotateDecimalEquiv (q : ℕ) (phase : Fin (stageOrder q)) :
    DecimalWord (stageOrder q) ≃ DecimalWord (stageOrder q) :=
  (cyclicIndexEquiv q phase).symm.arrowCongr (Equiv.refl Digit)

@[simp] theorem rotateDecimalEquiv_apply (q : ℕ)
    (phase : Fin (stageOrder q)) (u : DecimalWord (stageOrder q))
    (i : Fin (stageOrder q)) :
    rotateDecimalEquiv q phase u i = u (cyclicIndexEquiv q phase i) := by
  simp [rotateDecimalEquiv]

/-- Split the first `n` coordinates from a tuple of length `m`. -/
noncomputable def splitDecimalEquiv (m n : ℕ) (h : n ≤ m) :
    DecimalWord m ≃ DecimalWord n × DecimalWord (m - n) :=
  ((finCongr (Nat.add_sub_of_le h)).arrowCongr (Equiv.refl Digit)).symm.trans
    (Fin.appendEquiv n (m - n)).symm

@[simp] theorem splitDecimalEquiv_fst (m n : ℕ) (h : n ≤ m)
    (u : DecimalWord m) (i : Fin n) :
    (splitDecimalEquiv m n h u).1 i = u (Fin.castLE h i) := by
  simp only [splitDecimalEquiv, Equiv.trans_apply, Fin.appendEquiv_symm_apply]
  congr 1

/-- A seed code is equivalently its cyclic length-`n` prefix at a fixed phase
and the remaining `m-n` digits. -/
noncomputable def cyclicSeedSplitEquiv (q n : ℕ) (h : n ≤ stageOrder q)
    (phase : Fin (stageOrder q)) :
    Fin (10 ^ stageOrder q) ≃
      DecimalWord n × DecimalWord (stageOrder q - n) :=
  (decodedTupleEquiv (stageOrder q)).trans
    ((rotateDecimalEquiv q phase).trans
      (splitDecimalEquiv (stageOrder q) n h))

@[simp] theorem cyclicSeedSplitEquiv_fst (q n : ℕ)
    (h : n ≤ stageOrder q) (phase : Fin (stageOrder q))
    (a : Fin (10 ^ stageOrder q)) (i : Fin n) :
    (cyclicSeedSplitEquiv q n h phase a).1 i =
      decodedTuple (stageOrder q) a
        ⟨(phase.val + i.val) % stageOrder q,
          Nat.mod_lt _ (stageOrder_pos q)⟩ := by
  rw [cyclicSeedSplitEquiv, Equiv.trans_apply, Equiv.trans_apply,
    splitDecimalEquiv_fst, rotateDecimalEquiv_apply]
  congr 1

/-- The periodic digit attached to a safe coordinate, at a relative
lookahead `k`. -/
def safePeriodicDigit (q : ℕ)
    (st : Fin (10 ^ stageOrder q) ×
      Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q))
    (k : ℕ) : Digit :=
  decodedTuple (stageOrder q) st.1
    ⟨(st.2.val + k) % stageOrder q, Nat.mod_lt _ (stageOrder_pos q)⟩

/-- Every lookahead through two stage orders from a safe start remains in
one repeated seed segment and reads the corresponding periodic seed digit. -/
theorem artificialStream_safeCoordinate_digit (q : ℕ)
    (st : Fin (10 ^ stageOrder q) ×
      Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q))
    (k : ℕ) (hk : k ≤ 2 * stageOrder q) :
    artificialStream
        (stageStart q +
          (st.1.val * seedSegmentLength (stageStart q) q + st.2.val) + k) =
      safePeriodicDigit q st k := by
  let L := seedSegmentLength (stageStart q) q
  have htwo : 2 * stageOrder q ≤ L := by
    exact twice_stageOrder_le_seedSegmentLength (stageStart q) q
  have hoff : st.2.val + k < L := by
    have ht := st.2.isLt
    omega
  have hseg := st.1.isLt
  have hlocal : st.1.val * L + st.2.val + k < 10 ^ stageOrder q * L := by
    have hinside : st.1.val * L + (st.2.val + k) < (st.1.val + 1) * L := by
      rw [Nat.add_mul]
      omega
    have hsegments : (st.1.val + 1) * L ≤ 10 ^ stageOrder q * L := by
      exact Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr hseg)
    have hinside' :
        st.1.val * L + st.2.val + k < (st.1.val + 1) * L := by
      simpa [Nat.add_assoc] using hinside
    exact hinside'.trans_le hsegments
  rw [Nat.add_assoc]
  change artificialStream
    (stageStart q + (st.1.val * L + st.2.val + k)) = safePeriodicDigit q st k
  rw [artificialStream_stage_digit q
    (st.1.val * L + st.2.val + k) (by simpa [stageLength, L] using hlocal)]
  unfold stageDigit safePeriodicDigit
  dsimp only
  have hdiv : (st.1.val * L + st.2.val + k) / L = st.1.val := by
    rw [show st.1.val * L + st.2.val + k = L * st.1.val + (st.2.val + k) by
      simp [Nat.mul_comm, Nat.add_assoc]]
    rw [Nat.mul_add_div (by
      unfold L seedSegmentLength stageRepetitions stageOrder
      positivity), Nat.div_eq_of_lt hoff]
    omega
  have hmod : (st.1.val * L + st.2.val + k) % L = st.2.val + k := by
    rw [show st.1.val * L + st.2.val + k = st.1.val * L + (st.2.val + k) by
      omega]
    exact Nat.mul_add_mod_of_lt hoff
  apply congrArg₂
    (fun (seed : Fin (10 ^ stageOrder q)) (phase : Fin (stageOrder q)) =>
      decodedTuple (stageOrder q) seed phase)
  · apply Fin.ext
    simpa [L] using hdiv
  · apply Fin.ext
    simpa [L] using congrArg (fun z => z % stageOrder q) hmod

/-- At a fixed safe offset, `startHit` is exactly the condition that the
cyclic prefix of the seed equals the requested word. -/
theorem startHit_safeCoordinate_eq_cyclicSeedPrefix (q : ℕ)
    (t : Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q))
    (a : Fin (10 ^ stageOrder q)) (w : Word)
    (hw : w.length ≤ stageOrder q) :
    startHit artificialStream w
        (stageStart q +
          a.val * seedSegmentLength (stageStart q) q + t.val) =
      if (cyclicSeedSplitEquiv q w.length hw
          ⟨t.val % stageOrder q, Nat.mod_lt _ (stageOrder_pos q)⟩ a).1 =
          (fun i : Fin w.length => w.get i) then 1 else 0 := by
  let phase : Fin (stageOrder q) :=
    ⟨t.val % stageOrder q, Nat.mod_lt _ (stageOrder_pos q)⟩
  have hcoordinate (i : Fin w.length) :
      (cyclicSeedSplitEquiv q w.length hw phase a).1 i =
        artificialStream
          ((stageStart q +
            a.val * seedSegmentLength (stageStart q) q + t.val) + i.val) := by
    have hi : i.val ≤ 2 * stageOrder q := by
      have hilength := i.isLt.le
      omega
    rw [show stageStart q +
          a.val * seedSegmentLength (stageStart q) q + t.val =
        stageStart q +
          (a.val * seedSegmentLength (stageStart q) q + t.val) by omega]
    rw [artificialStream_safeCoordinate_digit q (a, t) i.val hi]
    rw [cyclicSeedSplitEquiv_fst]
    unfold safePeriodicDigit phase
    congr 2
    simp [Nat.add_mod]
  unfold startHit
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    rw [hcoordinate]
    exact h i
  · intro h i
    rw [← hcoordinate]
    exact congrFun h i

/-- For one phase, fixing a cyclic length-`n` prefix leaves exactly
`10^(m-n)` exhaustive seeds. -/
theorem sum_seed_startHit_safeOffset (q : ℕ)
    (t : Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q))
    (w : Word) (hw : w.length ≤ stageOrder q) :
    (∑ a : Fin (10 ^ stageOrder q),
      startHit artificialStream w
        (stageStart q +
          a.val * seedSegmentLength (stageStart q) q + t.val)) =
      10 ^ (stageOrder q - w.length) := by
  classical
  let phase : Fin (stageOrder q) :=
    ⟨t.val % stageOrder q, Nat.mod_lt _ (stageOrder_pos q)⟩
  let target : DecimalWord w.length := fun i => w.get i
  let e := cyclicSeedSplitEquiv q w.length hw phase
  calc
    (∑ a : Fin (10 ^ stageOrder q),
        startHit artificialStream w
          (stageStart q +
            a.val * seedSegmentLength (stageStart q) q + t.val)) =
        ∑ p : DecimalWord w.length ×
            DecimalWord (stageOrder q - w.length),
          if p.1 = target then 1 else 0 := by
      exact Fintype.sum_equiv e _ _ (fun a => by
        simpa only [e, phase, target] using
          startHit_safeCoordinate_eq_cyclicSeedPrefix q t a w hw)
    _ = 10 ^ (stageOrder q - w.length) := by
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_eq_single target]
      · simp
      · intro u hu
        simp [hu]

/-- Exact core count for every word no longer than the current exhaustive
seed order.  The safe offsets are the `(R-2)` full periods. -/
theorem stageCoreCount_eq_coreSize_mul_pow (q : ℕ) (w : Word)
    (hw : w.length ≤ stageOrder q) :
    stageCoreCount q w =
      (seedSegmentLength (stageStart q) q - 2 * stageOrder q) *
        10 ^ (stageOrder q - w.length) := by
  classical
  unfold stageCoreCount stageSafeStarts
  rw [Finset.sum_image (stageSafeCoordinate_injective q).injOn]
  change (∑ st : Fin (10 ^ stageOrder q) ×
      Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q),
        startHit artificialStream w
          (stageStart q +
            st.1.val * seedSegmentLength (stageStart q) q + st.2.val)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [sum_seed_startHit_safeOffset q _ w hw]
  simp

/-- The safe offsets comprise exactly `R-2` complete periods of length `m`. -/
theorem stageSafeOffsetCount_eq_repetitionPeriods (q : ℕ) :
    seedSegmentLength (stageStart q) q - 2 * stageOrder q =
      (stageRepetitions (stageStart q) q - 2) * stageOrder q := by
  unfold seedSegmentLength
  rw [Nat.mul_sub_right_distrib]

theorem stageCoreCount_eq_repetitionPeriods_mul_pow (q : ℕ) (w : Word)
    (hw : w.length ≤ stageOrder q) :
    stageCoreCount q w =
      (stageRepetitions (stageStart q) q - 2) * stageOrder q *
        10 ^ (stageOrder q - w.length) := by
  rw [stageCoreCount_eq_coreSize_mul_pow q w hw,
    stageSafeOffsetCount_eq_repetitionPeriods]

/-- For every shallow right extension, the exhaustive core child count is
exactly one tenth of its parent count. -/
theorem ten_mul_stageCoreCount_child_eq_parent (q : ℕ) (w : Word) (d : Digit)
    (hw : w.length + 1 ≤ stageOrder q) :
    10 * stageCoreCount q (w ++ [d]) = stageCoreCount q w := by
  have hwParent : w.length ≤ stageOrder q := by omega
  rw [stageCoreCount_eq_coreSize_mul_pow q (w ++ [d]) (by simpa using hw),
    stageCoreCount_eq_coreSize_mul_pow q w hwParent]
  simp only [List.length_append, List.length_singleton]
  have hexponent : stageOrder q - w.length =
      (stageOrder q - (w.length + 1)) + 1 := by omega
  rw [hexponent, pow_succ]
  ring

/-- Safe stage digits depend only on the lookahead residue modulo the stage
order. -/
theorem artificialStream_safeCoordinate_periodic (q : ℕ)
    (st : Fin (10 ^ stageOrder q) ×
      Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q))
    (k l : ℕ) (hk : k ≤ 2 * stageOrder q) (hl : l ≤ 2 * stageOrder q)
    (hkl : k % stageOrder q = l % stageOrder q) :
    artificialStream
        (stageStart q +
          (st.1.val * seedSegmentLength (stageStart q) q + st.2.val) + k) =
      artificialStream
        (stageStart q +
          (st.1.val * seedSegmentLength (stageStart q) q + st.2.val) + l) := by
  rw [artificialStream_safeCoordinate_digit q st k hk,
    artificialStream_safeCoordinate_digit q st l hl]
  unfold safePeriodicDigit
  congr 2
  calc
    (st.2.val + k) % stageOrder q =
        (st.2.val % stageOrder q + k % stageOrder q) % stageOrder q :=
      Nat.add_mod _ _ _
    _ = (st.2.val % stageOrder q + l % stageOrder q) % stageOrder q := by
      rw [hkl]
    _ = (st.2.val + l) % stageOrder q := (Nat.add_mod _ _ _).symm

theorem exists_safeCoordinate_of_mem {q j : ℕ} (hj : j ∈ stageSafeStarts q) :
    ∃ st : Fin (10 ^ stageOrder q) ×
        Fin (seedSegmentLength (stageStart q) q - 2 * stageOrder q),
      j = stageStart q +
        (st.1.val * seedSegmentLength (stageStart q) q + st.2.val) := by
  rw [stageSafeStarts, Finset.mem_image] at hj
  obtain ⟨st, _, rfl⟩ := hj
  exact ⟨st, by omega⟩

/-- Periodicity stated for an arbitrary member of the public safe-start
finset. -/
theorem artificialStream_stageSafeStart_periodic {q j : ℕ}
    (hj : j ∈ stageSafeStarts q) (k l : ℕ)
    (hk : k ≤ 2 * stageOrder q) (hl : l ≤ 2 * stageOrder q)
    (hkl : k % stageOrder q = l % stageOrder q) :
    artificialStream (j + k) = artificialStream (j + l) := by
  obtain ⟨st, rfl⟩ := exists_safeCoordinate_of_mem hj
  simpa [Nat.add_assoc] using
    artificialStream_safeCoordinate_periodic q st k l hk hl hkl

/-- At levels at least the stage order, choose the digit whose position in
the parent is congruent to the next position modulo that order. -/
def stageSelectedSuccessor (q n : ℕ) (a : Fin (10 ^ n)) : Digit :=
  if h : stageOrder q ≤ n then
    decodedTuple n a
      ⟨n % stageOrder q,
        (Nat.mod_lt n (stageOrder_pos q)).trans_le h⟩
  else 0

/-- A safe occurrence has the deterministic selected successor throughout
the full length band from one through two stage orders. -/
theorem stageSelectedSuccessor_eq_stream_of_safe_hit (q n : ℕ)
    (a : Fin (10 ^ n)) (j : ℕ) (hj : j ∈ stageSafeStarts q)
    (hlower : stageOrder q ≤ n) (hupper : n < 2 * stageOrder q)
    (hhit : startHit artificialStream (decodedWord n a) j = 1) :
    artificialStream (j + n) = stageSelectedSuccessor q n a := by
  let r := n % stageOrder q
  have hrm : r < stageOrder q := Nat.mod_lt n (stageOrder_pos q)
  have hrn : r < n := hrm.trans_le hlower
  have hnperiod : n % stageOrder q = r % stageOrder q := by
    dsimp only [r]
    rw [Nat.mod_mod]
  have hperiod := artificialStream_stageSafeStart_periodic hj n r
    (Nat.le_of_lt hupper) (by omega) hnperiod
  have hparent : ∀ i : Fin (decodedWord n a).length,
      artificialStream (j + i) = (decodedWord n a).get i := by
    by_contra hnot
    simp [startHit] at hhit
    exact hnot hhit
  have hat := hparent
    ⟨r, by simpa only [decodedWord_length] using hrn⟩
  rw [stageSelectedSuccessor, dif_pos hlower]
  rw [hperiod]
  simpa [r, decodedWord] using hat

theorem startHit_selectedChild_eq_one_of_safe (q n : ℕ)
    (a : Fin (10 ^ n)) (j : ℕ) (hj : j ∈ stageSafeStarts q)
    (hlower : stageOrder q ≤ n) (hupper : n < 2 * stageOrder q)
    (hhit : startHit artificialStream (decodedWord n a) j = 1) :
    startHit artificialStream
      (decodedWord (n + 1)
        (decimalChild n a (stageSelectedSuccessor q n a))) j = 1 := by
  have hparent : ∀ i : Fin n,
      artificialStream (j + i) = decodedTuple n a i := by
    have hp : ∀ i : Fin (decodedWord n a).length,
        artificialStream (j + i) = (decodedWord n a).get i := by
      by_contra hnot
      simp [startHit] at hhit
      exact hnot hhit
    intro i
    simpa [decodedWord] using hp (Fin.cast (decodedWord_length n a).symm i)
  have hlast : artificialStream (j + n) = stageSelectedSuccessor q n a :=
    stageSelectedSuccessor_eq_stream_of_safe_hit q n a j hj hlower hupper hhit
  have hchild : ∀ i : Fin (n + 1),
      artificialStream (j + i) =
        decodedTuple (n + 1)
          (decimalChild n a (stageSelectedSuccessor q n a)) i := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa using hlast
    · simpa using hparent k
  unfold startHit
  rw [if_pos]
  intro i
  change artificialStream (j + i) =
    (List.ofFn (decodedTuple (n + 1)
      (decimalChild n a (stageSelectedSuccessor q n a)))).get i
  rw [List.get_ofFn]
  simpa using hchild ⟨i.val, by simpa using i.isLt⟩

theorem stageCoreCount_le_selectedChildCoreCount (q n : ℕ)
    (a : Fin (10 ^ n)) (hlower : stageOrder q ≤ n)
    (hupper : n < 2 * stageOrder q) :
    stageCoreCount q (decodedWord n a) ≤
      stageCoreCount q
        (decodedWord (n + 1)
          (decimalChild n a (stageSelectedSuccessor q n a))) := by
  unfold stageCoreCount
  apply Finset.sum_le_sum
  intro j hj
  by_cases hparent : ∀ i : Fin (decodedWord n a).length,
      artificialStream (j + i) = (decodedWord n a).get i
  · have hhit : startHit artificialStream (decodedWord n a) j = 1 := by
      simp [startHit, hparent]
    rw [hhit, startHit_selectedChild_eq_one_of_safe q n a j hj hlower hupper hhit]
  · unfold startHit
    rw [if_neg hparent]
    exact Nat.zero_le _

/-- The selected child loses at most the error part of its parent count. -/
theorem firstStartCount_le_selectedChild_add_error (q n : ℕ)
    (a : Fin (10 ^ n)) (hlower : stageOrder q ≤ n)
    (hupper : n < 2 * stageOrder q) :
    firstStartCount artificialStream (sampledCheckpoint q) (decodedWord n a) ≤
      firstStartCount artificialStream (sampledCheckpoint q)
          (decodedWord (n + 1)
            (decimalChild n a (stageSelectedSuccessor q n a))) +
        stageErrorCount q (decodedWord n a) := by
  have hparent := firstStartCount_sampledCheckpoint_eq_core_add_error q
    (decodedWord n a)
  have hchild := firstStartCount_sampledCheckpoint_eq_core_add_error q
    (decodedWord (n + 1)
      (decimalChild n a (stageSelectedSuccessor q n a)))
  have hcore := stageCoreCount_le_selectedChildCoreCount q n a hlower hupper
  omega

theorem firstStartCount_le_selectedChild_add_budget (q n : ℕ)
    (a : Fin (10 ^ n)) (hlower : stageOrder q ≤ n)
    (hupper : n < 2 * stageOrder q) :
    firstStartCount artificialStream (sampledCheckpoint q) (decodedWord n a) ≤
      firstStartCount artificialStream (sampledCheckpoint q)
          (decodedWord (n + 1)
            (decimalChild n a (stageSelectedSuccessor q n a))) +
        stageErrorBudget (stageStart q) q := by
  exact (firstStartCount_le_selectedChild_add_error q n a hlower hupper).trans
    (Nat.add_le_add_left (stageErrorCount_le_budget q (decodedWord n a)) _)

/-! ## T29 full leakage -/

/-- Every parent is retained in the full selected-edge comparison. -/
def stageDominant (_q : ℕ) : (n : ℕ) → Fin (10 ^ n) → Prop :=
  fun _ _ => True

/-- The level-indexed T29 choice function supplied by periodicity. -/
def stageSuccessorChoice (q : ℕ) :
    (n : ℕ) → Fin (10 ^ n) → Digit :=
  fun n a => stageSelectedSuccessor q n a

theorem streamCountTree_child_le (x : Stream) (N n : ℕ)
    (a : Fin (10 ^ n)) (d : Digit) :
    streamCountTree x N (n + 1) (decimalChild n a d) ≤
      streamCountTree x N n a := by
  rw [streamCountTree_conservation x N n a]
  exact Finset.single_le_sum
    (f := fun z => streamCountTree x N (n + 1) (decimalChild n a z))
    (fun z _ => Nat.zero_le _)
    (Finset.mem_univ d)

/-- Quantitative full leakage at every edge level in the safe periodic band.
The bound includes both discarded parents and loss along retained parents. -/
theorem stageLeakage_le (q n : ℕ) (hlower : stageOrder q ≤ n)
    (hupper : n < 2 * stageOrder q) :
    leakage
        (streamCountTree artificialStream (sampledCheckpoint q)).toReal
        (stageDominant q) (stageSuccessorChoice q) n ≤
      2 * (sampledCheckpoint q : ℝ) *
        stageErrorBudget (stageStart q) q := by
  unfold FiniteCountTreeLeakage.leakage
    FiniteCountTreeLeakage.collisionEnergy retainedEdgeEnergy stageDominant
    stageSuccessorChoice NaturalDecimalCounts.toReal
  simp only [if_true]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ a : Fin (10 ^ n), (
        (streamCountTree artificialStream (sampledCheckpoint q) n a : ℝ) ^ 2 -
          (streamCountTree artificialStream (sampledCheckpoint q) (n + 1)
            (decimalChild n a (stageSelectedSuccessor q n a)) : ℝ) ^ 2)) ≤
        ∑ a : Fin (10 ^ n),
          2 * (sampledCheckpoint q : ℝ) *
            stageErrorCount q (decodedWord n a) := by
      apply Finset.sum_le_sum
      intro a _
      have hparentBound :
          streamCountTree artificialStream (sampledCheckpoint q) n a ≤
            sampledCheckpoint q := by
        exact blockCount_le artificialStream (decodedWord n a)
          (sampledCheckpoint q)
      have hchildParent := streamCountTree_child_le artificialStream
        (sampledCheckpoint q) n a (stageSelectedSuccessor q n a)
      have hloss := firstStartCount_le_selectedChild_add_error q n a
        hlower hupper
      change streamCountTree artificialStream (sampledCheckpoint q) n a ≤
          streamCountTree artificialStream (sampledCheckpoint q) (n + 1)
              (decimalChild n a (stageSelectedSuccessor q n a)) +
            stageErrorCount q (decodedWord n a) at hloss
      have hparentBoundReal :
          (streamCountTree artificialStream (sampledCheckpoint q) n a : ℝ) ≤
            sampledCheckpoint q := by exact_mod_cast hparentBound
      have hchildParentReal :
          (streamCountTree artificialStream (sampledCheckpoint q) (n + 1)
              (decimalChild n a (stageSelectedSuccessor q n a)) : ℝ) ≤
            streamCountTree artificialStream (sampledCheckpoint q) n a := by
        exact_mod_cast hchildParent
      have hlossReal :
          (streamCountTree artificialStream (sampledCheckpoint q) n a : ℝ) ≤
            streamCountTree artificialStream (sampledCheckpoint q) (n + 1)
                (decimalChild n a (stageSelectedSuccessor q n a)) +
              stageErrorCount q (decodedWord n a) := by
        exact_mod_cast hloss
      nlinarith [sq_nonneg
        ((streamCountTree artificialStream (sampledCheckpoint q) n a : ℝ) -
          (streamCountTree artificialStream (sampledCheckpoint q) (n + 1)
            (decimalChild n a (stageSelectedSuccessor q n a)) : ℝ))]
    _ = 2 * (sampledCheckpoint q : ℝ) *
        stageErrorBudget (stageStart q) q := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast sum_stageErrorCount_all_words q n

theorem stageLeakage_nonneg (q n : ℕ) :
    0 ≤ leakage
      (streamCountTree artificialStream (sampledCheckpoint q)).toReal
      (stageDominant q) (stageSuccessorChoice q) n := by
  unfold FiniteCountTreeLeakage.leakage
    FiniteCountTreeLeakage.collisionEnergy retainedEdgeEnergy stageDominant
    stageSuccessorChoice NaturalDecimalCounts.toReal
  simp only [if_true]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro a _
  have hchild := streamCountTree_child_le artificialStream
    (sampledCheckpoint q) n a (stageSelectedSuccessor q n a)
  have hchildReal :
      (streamCountTree artificialStream (sampledCheckpoint q) (n + 1)
          (decimalChild n a (stageSelectedSuccessor q n a)) : ℝ) ≤
        streamCountTree artificialStream (sampledCheckpoint q) n a := by
    exact_mod_cast hchild
  nlinarith

theorem streamCountTree_total (x : Stream) (N n : ℕ) :
    ∑ a : Fin (10 ^ n), streamCountTree x N n a = N := by
  calc
    (∑ a : Fin (10 ^ n), streamCountTree x N n a) =
        ∑ u : DecimalWord n, firstStartCount x N (List.ofFn u) := by
      exact Fintype.sum_equiv (decodedTupleEquiv n)
        (fun a => streamCountTree x N n a)
        (fun u => firstStartCount x N (List.ofFn u)) (fun _ => rfl)
    _ = N := firstStartCount_total x n N

/-- Cauchy lower bound for the actual stream collision energy at every
checkpoint and every factor length. -/
theorem sampledCheckpoint_sq_le_card_mul_collisionEnergy (q n : ℕ) :
    (sampledCheckpoint q : ℝ) ^ 2 ≤
      (10 ^ n : ℝ) *
        FiniteCountTreeLeakage.collisionEnergy
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal n := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin (10 ^ n))))
    (f := fun a =>
      (streamCountTree artificialStream (sampledCheckpoint q) n a : ℝ))
  have hsum :
      (∑ a : Fin (10 ^ n),
        (streamCountTree artificialStream (sampledCheckpoint q) n a : ℝ)) =
          sampledCheckpoint q := by
    exact_mod_cast streamCountTree_total artificialStream (sampledCheckpoint q) n
  rw [hsum] at h
  simpa [FiniteCountTreeLeakage.collisionEnergy,
    NaturalDecimalCounts.toReal] using h

/-- The whole `stageOrder q`-edge T29 window has an explicit cumulative
full-leakage bound. -/
theorem stageCumulativeLeakage_le (q : ℕ) :
    (∑ i ∈ Finset.range (stageOrder q),
        leakage
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          (stageDominant q) (stageSuccessorChoice q) (stageOrder q + i)) ≤
      (stageOrder q : ℝ) *
        (2 * (sampledCheckpoint q : ℝ) *
          stageErrorBudget (stageStart q) q) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range (stageOrder q),
        2 * (sampledCheckpoint q : ℝ) *
          stageErrorBudget (stageStart q) q := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      exact stageLeakage_le q (stageOrder q + i) (by omega) (by omega)
    _ = _ := by simp

/-- Cumulative T29 full leakage normalized by the collision energy at the
moving root `stageOrder q`. -/
def normalizedStageLeakage (q : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (stageOrder q),
      leakage
        (streamCountTree artificialStream (sampledCheckpoint q)).toReal
        (stageDominant q) (stageSuccessorChoice q) (stageOrder q + i)) /
    FiniteCountTreeLeakage.collisionEnergy
      (streamCountTree artificialStream (sampledCheckpoint q)).toReal
      (stageOrder q)

theorem sampledCheckpoint_pos (q : ℕ) : 0 < sampledCheckpoint q := by
  rw [sampledCheckpoint, stageStart_succ]
  exact Nat.add_pos_right (stageStart q) (stageLength_pos (stageStart q) q)

theorem sampledCollisionEnergy_pos (q : ℕ) :
    0 < FiniteCountTreeLeakage.collisionEnergy
      (streamCountTree artificialStream (sampledCheckpoint q)).toReal
      (stageOrder q) := by
  have h := sampledCheckpoint_sq_le_card_mul_collisionEnergy q (stageOrder q)
  have hN : 0 < (sampledCheckpoint q : ℝ) := by
    exact_mod_cast sampledCheckpoint_pos q
  have hcard : 0 < (10 ^ stageOrder q : ℝ) := by positivity
  nlinarith

/-- The explicit repetition count forces normalized cumulative full leakage
to decay cubically in the moving root. -/
theorem normalizedStageLeakage_le (q : ℕ) :
    normalizedStageLeakage q ≤ 2 / (stageOrder q : ℝ) ^ 3 := by
  let m := stageOrder q
  let B := stageErrorBudget (stageStart q) q
  let S := 10 ^ m
  let R := stageRepetitions (stageStart q) q
  let N := sampledCheckpoint q
  let E := FiniteCountTreeLeakage.collisionEnergy
    (streamCountTree artificialStream N).toReal m
  let L := ∑ i ∈ Finset.range m,
    leakage (streamCountTree artificialStream N).toReal
      (stageDominant q) (stageSuccessorChoice q) (m + i)
  have hmNat : 0 < m := stageOrder_pos q
  have hRnat : m ^ 3 * B ≤ R := by
    dsimp only [m, B, R]
    unfold stageRepetitions
    exact (Nat.mul_le_mul_left (stageOrder q ^ 3)
      (Nat.le_add_right (stageErrorBudget (stageStart q) q) 1)).trans
      (Nat.le_add_right _ 3)
  have hNnat : S * m * R ≤ N := by
    dsimp only [S, m, R, N]
    rw [sampledCheckpoint, stageStart_succ, stageLength,
      seedSegmentLength]
    have heq :
        10 ^ stageOrder q * stageOrder q *
            stageRepetitions (stageStart q) q =
          10 ^ stageOrder q *
            (stageRepetitions (stageStart q) q * stageOrder q) := by
      ring
    rw [heq]
    exact Nat.le_add_left _ _
  have hL : L ≤ (m : ℝ) * (2 * (N : ℝ) * (B : ℝ)) := by
    simpa only [L, m, B, N] using stageCumulativeLeakage_le q
  have hE : (N : ℝ) ^ 2 ≤ (S : ℝ) * E := by
    simpa only [N, S, m, E, Nat.cast_pow, Nat.cast_ofNat] using
      sampledCheckpoint_sq_le_card_mul_collisionEnergy q (stageOrder q)
  have hR : (m : ℝ) ^ 3 * (B : ℝ) ≤ R := by exact_mod_cast hRnat
  have hN : (S : ℝ) * m * R ≤ N := by exact_mod_cast hNnat
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hS : 0 < (S : ℝ) := by
    dsimp only [S]
    positivity
  have hNpos : 0 < (N : ℝ) := by
    dsimp only [N]
    exact_mod_cast sampledCheckpoint_pos q
  have hEpos : 0 < E := by
    nlinarith
  have hcore : (S : ℝ) * m * ((B : ℝ) * (m : ℝ) ^ 3) ≤ N := by
    calc
      (S : ℝ) * m * ((B : ℝ) * (m : ℝ) ^ 3) =
          (S : ℝ) * m * ((m : ℝ) ^ 3 * B) := by ring
      _ ≤ (S : ℝ) * m * R := by
        exact mul_le_mul_of_nonneg_left hR (mul_nonneg hS.le hm.le)
      _ ≤ N := hN
  have hscaledLeak : L * (m : ℝ) ^ 3 ≤
      ((m : ℝ) * (2 * (N : ℝ) * (B : ℝ))) * (m : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right hL (by positivity)
  have hscaledCore :
      2 * (N : ℝ) * ((S : ℝ) * m * ((B : ℝ) * (m : ℝ) ^ 3)) ≤
        2 * (N : ℝ) * N :=
    mul_le_mul_of_nonneg_left hcore (mul_nonneg (by norm_num) hNpos.le)
  have henergy : 2 * (N : ℝ) * N ≤ 2 * ((S : ℝ) * E) := by
    nlinarith
  have hcrossScaled :
      (S : ℝ) * (L * (m : ℝ) ^ 3) ≤ (S : ℝ) * (2 * E) := by
    calc
      (S : ℝ) * (L * (m : ℝ) ^ 3) ≤
          (S : ℝ) *
            (((m : ℝ) * (2 * (N : ℝ) * (B : ℝ))) * (m : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hscaledLeak hS.le
      _ = 2 * (N : ℝ) *
          ((S : ℝ) * m * ((B : ℝ) * (m : ℝ) ^ 3)) := by ring
      _ ≤ 2 * (N : ℝ) * N := hscaledCore
      _ ≤ 2 * ((S : ℝ) * E) := henergy
      _ = (S : ℝ) * (2 * E) := by ring
  have hcross : L * (m : ℝ) ^ 3 ≤ 2 * E := by
    nlinarith
  unfold normalizedStageLeakage
  change L / E ≤ 2 / (m : ℝ) ^ 3
  exact (div_le_div_iff₀ hEpos (pow_pos hm 3)).2 (by simpa [mul_comm] using hcross)

theorem normalizedStageLeakage_nonneg (q : ℕ) :
    0 ≤ normalizedStageLeakage q := by
  unfold normalizedStageLeakage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact stageLeakage_nonneg q (stageOrder q + i)
  · exact (sampledCollisionEnergy_pos q).le

/-- The normalized cumulative T29 full leakage along the explicit sampled
checkpoints tends to zero. -/
theorem normalizedStageLeakage_tendsto_zero :
    Tendsto normalizedStageLeakage Filter.atTop (nhds 0) := by
  have hm : Tendsto (fun q : ℕ => (stageOrder q : ℝ))
      Filter.atTop Filter.atTop := by
    simpa [stageOrder, Nat.cast_add, Nat.cast_one] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun q : ℕ => (q : ℝ)) Filter.atTop Filter.atTop))
  have hcube : Tendsto (fun q : ℕ => (stageOrder q : ℝ) ^ 3)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono
      (f := fun q : ℕ => (stageOrder q : ℝ))
    · intro q
      have hmq : 1 ≤ (stageOrder q : ℝ) := by
        exact_mod_cast (stageOrder_pos q)
      nlinarith [sq_nonneg ((stageOrder q : ℝ) - 1)]
    · exact hm
  have hupper : Tendsto (fun q : ℕ => 2 / (stageOrder q : ℝ) ^ 3)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hcube
  exact squeeze_zero normalizedStageLeakage_nonneg normalizedStageLeakage_le hupper

/-- The moving-window statement with the stream, checkpoints, window levels,
T29 full leakage, and normalization all visible in its type. -/
theorem artificialStream_arbitrarilyLong_lowLeakage_windows :
    StrictMono sampledCheckpoint ∧
    StrictMono inspectionCheckpoint ∧
    (∀ H : ℕ, ∀ᶠ q in atTop, H ≤ stageOrder q) ∧
    Tendsto
      (fun q =>
        (∑ i ∈ Finset.range (stageOrder q),
            leakage
              (streamCountTree artificialStream (sampledCheckpoint q)).toReal
              (stageDominant q) (stageSuccessorChoice q) (stageOrder q + i)) /
          FiniteCountTreeLeakage.collisionEnergy
            (streamCountTree artificialStream (sampledCheckpoint q)).toReal
            (stageOrder q))
      atTop (nhds 0) := by
  refine ⟨sampledCheckpoint_strictMono, inspectionCheckpoint_strictMono, ?_, ?_⟩
  · intro H
    filter_upwards [eventually_ge_atTop H] with q hq
    unfold stageOrder
    omega
  · exact normalizedStageLeakage_tendsto_zero

/-! ## Explicit zero roots for moving windows -/

/-- Numeric code of the all-zero decimal word. -/
def zeroCode (n : ℕ) : Fin (10 ^ n) :=
  (decodedTupleEquiv n).symm (fun _ => 0)

@[simp] theorem decodedTuple_zeroCode (n : ℕ) :
    decodedTuple n (zeroCode n) = fun _ => 0 := by
  exact (decodedTupleEquiv n).apply_eq_iff_eq_symm_apply.mpr rfl

@[simp] theorem decodedWord_zeroCode (n : ℕ) :
    decodedWord n (zeroCode n) = List.replicate n (0 : Digit) := by
  apply List.ext_get
  · simp
  · intro i hi hi'
    simp [decodedWord]

theorem firstStartCount_snoc_le (x : Stream) (N : ℕ) (w : Word) (d : Digit) :
    firstStartCount x N (w ++ [d]) ≤ firstStartCount x N w := by
  let u : DecimalWord w.length := fun i => w.get i
  have hu : List.ofFn u = w := by
    apply List.ext_get
    · simp [u]
    · intro i hi hi'
      simp [u]
  have hterm : firstStartCount x N (List.ofFn (Fin.snoc u d)) ≤
      ∑ z : Digit, firstStartCount x N (List.ofFn (Fin.snoc u z)) :=
    Finset.single_le_sum
      (f := fun z : Digit => firstStartCount x N (List.ofFn (Fin.snoc u z)))
      (fun z _ => Nat.zero_le _) (Finset.mem_univ d)
  have husnoc : List.ofFn (Fin.snoc u d) = w ++ [d] := by
    rw [ofFn_snoc, hu]
  rw [firstStartCount_snoc x w.length N u] at hterm
  rw [husnoc, hu] at hterm
  exact hterm

theorem firstStartCount_append_le (x : Stream) (N : ℕ) (w v : Word) :
    firstStartCount x N (w ++ v) ≤ firstStartCount x N w := by
  induction v using List.reverseRecOn generalizing w with
  | nil => simp
  | append_singleton v d ih =>
      rw [← List.append_assoc]
      exact (firstStartCount_snoc_le x N (w ++ v) d).trans (ih w)

/-- Number of safe offsets in the all-zero seed segment. -/
def zeroSeedCoreSize (q : ℕ) : ℕ :=
  seedSegmentLength (stageStart q) q - 2 * stageOrder q

/-- Safe starts belonging to the all-zero seed. -/
def zeroSeedSafeStarts (q : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin (zeroSeedCoreSize q))).image
    (fun t => stageStart q +
      (zeroCode (stageOrder q)).val * seedSegmentLength (stageStart q) q + t.val)

theorem zeroSeedSafeStarts_card (q : ℕ) :
    (zeroSeedSafeStarts q).card = zeroSeedCoreSize q := by
  rw [zeroSeedSafeStarts, Finset.card_image_of_injective _ (by
    intro a b hab
    apply Fin.ext
    dsimp only at hab ⊢
    omega)]
  simp

theorem zeroSeedSafeStarts_subset (q : ℕ) :
    zeroSeedSafeStarts q ⊆ stageSafeStarts q := by
  intro j hj
  rw [zeroSeedSafeStarts, Finset.mem_image] at hj
  obtain ⟨t, _, rfl⟩ := hj
  rw [stageSafeStarts, Finset.mem_image]
  refine ⟨(zeroCode (stageOrder q), t), Finset.mem_univ _, ?_⟩
  rfl

theorem zeroSeedSafeStart_digit {q j : ℕ} (hj : j ∈ zeroSeedSafeStarts q)
    (k : ℕ) (hk : k ≤ 2 * stageOrder q) :
    artificialStream (j + k) = 0 := by
  rw [zeroSeedSafeStarts, Finset.mem_image] at hj
  obtain ⟨t, _, rfl⟩ := hj
  let st : Fin (10 ^ stageOrder q) × Fin (zeroSeedCoreSize q) :=
    (zeroCode (stageOrder q), t)
  have hdigit := artificialStream_safeCoordinate_digit q st k hk
  simpa [st, zeroSeedCoreSize, safePeriodicDigit, Nat.add_assoc] using hdigit

theorem zeroSeedSafeStart_hit {q j n : ℕ} (hj : j ∈ zeroSeedSafeStarts q)
    (hn : n ≤ 2 * stageOrder q) :
    startHit artificialStream (List.replicate n (0 : Digit)) j = 1 := by
  unfold startHit
  rw [if_pos]
  intro i
  have hi : i.val ≤ 2 * stageOrder q := by
    have hilength := i.isLt.le
    simp only [List.length_replicate] at hilength
    exact hilength.trans hn
  simpa using zeroSeedSafeStart_digit hj i.val hi

/-- Every zero word through twice the stage order has all safe starts from the
all-zero repeated seed. -/
theorem zeroSeedCoreSize_le_stageCoreCount (q n : ℕ)
    (hn : n ≤ 2 * stageOrder q) :
    zeroSeedCoreSize q ≤
      stageCoreCount q (List.replicate n (0 : Digit)) := by
  rw [← zeroSeedSafeStarts_card q]
  have hones : (zeroSeedSafeStarts q).card =
      ∑ j ∈ zeroSeedSafeStarts q,
        startHit artificialStream (List.replicate n (0 : Digit)) j := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro j hj
    exact (zeroSeedSafeStart_hit hj hn).symm
  rw [hones]
  unfold stageCoreCount
  exact Finset.sum_le_sum_of_subset_of_nonneg (zeroSeedSafeStarts_subset q)
    (fun _ _ _ => Nat.zero_le _)

@[simp] theorem stageSelectedSuccessor_zeroCode (q n : ℕ)
    (h : stageOrder q ≤ n) :
    stageSelectedSuccessor q n (zeroCode n) = 0 := by
  simp [stageSelectedSuccessor, h]

theorem zeroSeedCoreSize_pos (q : ℕ) : 0 < zeroSeedCoreSize q := by
  have hm := stageOrder_pos q
  have hrep : 3 ≤ stageRepetitions (stageStart q) q := by
    unfold stageRepetitions
    omega
  rw [show zeroSeedCoreSize q =
      (stageRepetitions (stageStart q) q - 2) * stageOrder q by
    unfold zeroSeedCoreSize seedSegmentLength
    rw [Nat.mul_sub_right_distrib]]
  exact Nat.mul_pos (by omega) hm

theorem stageErrorBudget_mul_stageOrder_le_zeroSeedCoreSize (q : ℕ) :
    stageErrorBudget (stageStart q) q * stageOrder q ≤ zeroSeedCoreSize q := by
  let m := stageOrder q
  let B := stageErrorBudget (stageStart q) q
  let R := stageRepetitions (stageStart q) q
  have hm : 1 ≤ m := stageOrder_pos q
  have hcube : 1 ≤ m ^ 3 := by
    have := Nat.pow_le_pow_left hm 3
    simpa using this
  have hB : B ≤ m ^ 3 * (B + 1) := by
    calc
      B ≤ B + 1 := by omega
      _ = 1 * (B + 1) := by omega
      _ ≤ m ^ 3 * (B + 1) := Nat.mul_le_mul_right _ hcube
  have hR : B + 2 ≤ R := by
    change B + 2 ≤ m ^ 3 * (B + 1) + 3
    omega
  have hsub : B ≤ R - 2 := by omega
  have hcore : zeroSeedCoreSize q = (R - 2) * m := by
    dsimp only [R, m]
    unfold zeroSeedCoreSize seedSegmentLength
    rw [Nat.mul_sub_right_distrib]
  rw [hcore]
  exact Nat.mul_le_mul_right m hsub

theorem stageErrorBudget_le_zeroSeedCoreSize (q : ℕ) :
    stageErrorBudget (stageStart q) q ≤ zeroSeedCoreSize q := by
  have hm : 1 ≤ stageOrder q := stageOrder_pos q
  have hmul : stageErrorBudget (stageStart q) q ≤
      stageErrorBudget (stageStart q) q * stageOrder q := by
    nth_rewrite 1 [← Nat.mul_one (stageErrorBudget (stageStart q) q)]
    exact Nat.mul_le_mul_left _ hm
  exact hmul.trans (stageErrorBudget_mul_stageOrder_le_zeroSeedCoreSize q)

theorem zeroSeedCoreSize_le_shallowChildCoreCount (q : ℕ) (w : Word)
    (d : Digit) (hw : w.length + 1 ≤ stageOrder q) :
    zeroSeedCoreSize q ≤ stageCoreCount q (w ++ [d]) := by
  rw [stageCoreCount_eq_coreSize_mul_pow q (w ++ [d]) (by simpa using hw)]
  change zeroSeedCoreSize q ≤ zeroSeedCoreSize q *
    10 ^ (stageOrder q - (w ++ [d]).length)
  exact Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)

/-- At every stage where the fixed child is shallow, even the full error
budget cannot prevent strict one-half sparsity of its actual count. -/
theorem two_mul_firstStartCount_child_lt_parent_of_shallow (q : ℕ)
    (w : Word) (d : Digit) (hw : w.length + 1 ≤ stageOrder q) :
    2 * firstStartCount artificialStream (sampledCheckpoint q) (w ++ [d]) <
      firstStartCount artificialStream (sampledCheckpoint q) w := by
  have hparentSplit :=
    firstStartCount_sampledCheckpoint_eq_core_add_error q w
  have hchildSplit :=
    firstStartCount_sampledCheckpoint_eq_core_add_error q (w ++ [d])
  have hcoreRatio := ten_mul_stageCoreCount_child_eq_parent q w d hw
  have hchildError := stageErrorCount_le_budget q (w ++ [d])
  have hbudgetCore := stageErrorBudget_le_zeroSeedCoreSize q
  have hzeroChild := zeroSeedCoreSize_le_shallowChildCoreCount q w d hw
  have hchildCorePos : 0 < stageCoreCount q (w ++ [d]) :=
    (zeroSeedCoreSize_pos q).trans_le hzeroChild
  omega

/-- A concrete threshold increasing to one. -/
def movingThreshold (q : ℕ) : ℝ :=
  1 - 1 / (stageOrder q : ℝ)

theorem movingThreshold_tendsto_one :
    Tendsto movingThreshold atTop (nhds 1) := by
  have hm : Tendsto (fun q : ℕ => (stageOrder q : ℝ)) atTop atTop := by
    simpa [stageOrder, Nat.cast_add, Nat.cast_one] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun q : ℕ => (q : ℝ)) Filter.atTop Filter.atTop))
  simpa [movingThreshold] using tendsto_const_nhds.sub
    (tendsto_const_nhds.div_atTop hm)

theorem zeroPath_movingThreshold_dominant (q i : ℕ)
    (hi : i < stageOrder q) :
    movingThreshold q *
        (firstStartCount artificialStream (sampledCheckpoint q)
          (List.replicate (stageOrder q + i) (0 : Digit)) : ℝ) ≤
      firstStartCount artificialStream (sampledCheckpoint q)
        (List.replicate (stageOrder q + (i + 1)) (0 : Digit)) := by
  let m := stageOrder q
  let n := m + i
  let P := firstStartCount artificialStream (sampledCheckpoint q)
    (List.replicate n (0 : Digit))
  let C := firstStartCount artificialStream (sampledCheckpoint q)
    (List.replicate n (0 : Digit) ++ [0])
  let B := stageErrorBudget (stageStart q) q
  have hmNat : 0 < m := stageOrder_pos q
  have hnLower : stageOrder q ≤ n := by simp [n, m]
  have hnUpper : n < 2 * stageOrder q := by
    dsimp only [n, m]
    omega
  have hloss := firstStartCount_le_selectedChild_add_error q n (zeroCode n)
    hnLower hnUpper
  have hloss' : P ≤ C + stageErrorCount q (List.replicate n (0 : Digit)) := by
    simpa [P, C, decodedWord_zeroCode, hnLower] using hloss
  have hbudget : stageErrorCount q (List.replicate n (0 : Digit)) ≤ B := by
    exact stageErrorCount_le_budget q _
  have hcore : zeroSeedCoreSize q ≤ P := by
    have hcore' := zeroSeedCoreSize_le_stageCoreCount q n (by
      dsimp only [n, m]
      omega)
    have hsplit := firstStartCount_sampledCheckpoint_eq_core_add_error q
      (List.replicate n (0 : Digit))
    dsimp only [P]
    omega
  have hmB : B * m ≤ P :=
    (stageErrorBudget_mul_stageOrder_le_zeroSeedCoreSize q).trans hcore
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hlossBudget : P ≤ C + B :=
    hloss'.trans (Nat.add_le_add_left hbudget C)
  have hlossReal : (P : ℝ) ≤ C + B := by exact_mod_cast hlossBudget
  have hmBReal : (B : ℝ) * m ≤ P := by exact_mod_cast hmB
  have hBdiv : (B : ℝ) ≤ P / m := (le_div_iff₀ hm).2 hmBReal
  have hraw : (1 - 1 / (m : ℝ)) * P ≤ C := by
    calc
      (1 - 1 / (m : ℝ)) * P = P - P / m := by field_simp
      _ ≤ P - B := sub_le_sub_left hBdiv P
      _ ≤ C := by linarith
  have hCword : List.replicate n (0 : Digit) ++ [0] =
      List.replicate (stageOrder q + (i + 1)) (0 : Digit) := by
    have hindex : n + 1 = stageOrder q + (i + 1) := by
      dsimp only [n, m]
      omega
    calc
      List.replicate n (0 : Digit) ++ [0] =
          List.replicate n (0 : Digit) ++ List.replicate 1 0 := by simp
      _ = List.replicate (n + 1) 0 := (List.replicate_add _ _ _).symm
      _ = List.replicate (stageOrder q + (i + 1)) 0 := by rw [hindex]
  rw [movingThreshold]
  change (1 - 1 / (m : ℝ)) * P ≤
    firstStartCount artificialStream (sampledCheckpoint q)
      (List.replicate (stageOrder q + (i + 1)) (0 : Digit))
  rw [← hCword]
  exact hraw

theorem zeroRoot_firstStartCount_pos (q : ℕ) :
    0 < firstStartCount artificialStream (sampledCheckpoint q)
      (List.replicate (stageOrder q) (0 : Digit)) := by
  have hcore := zeroSeedCoreSize_le_stageCoreCount q (stageOrder q) (by omega)
  have hsplit := firstStartCount_sampledCheckpoint_eq_core_add_error q
    (List.replicate (stageOrder q) (0 : Digit))
  have hpos := zeroSeedCoreSize_pos q
  omega

/-- The actual count row rooted at the all-zero word of the current stage
order.  Its window has the same length as its moving root. -/
def artificialMovingRootRow (q : ℕ) : MovingRootRow where
  count := fun w => (firstStartCount artificialStream (sampledCheckpoint q) w : ℝ)
  root := List.replicate (stageOrder q) (0 : Digit)
  startDepth := stageOrder q
  windowLength := stageOrder q
  digit := fun _ => 0
  threshold := movingThreshold q
  root_length := by simp
  root_pos := by exact_mod_cast zeroRoot_firstStartCount_pos q
  normalized_nonneg := by
    intro v _
    positivity
  normalized_le_one := by
    intro v _
    apply div_le_one_of_le₀
    · exact_mod_cast firstStartCount_append_le artificialStream
        (sampledCheckpoint q) (List.replicate (stageOrder q) (0 : Digit)) v
    · positivity
  normalized_conservation := by
    intro v _
    let w := List.replicate (stageOrder q) (0 : Digit) ++ v
    have h := firstStartCount_snoc artificialStream
      w.length (sampledCheckpoint q) (fun i => w.get i)
    have hu : List.ofFn (fun i => w.get i) = w := by
      apply List.ext_get
      · simp
      · intro i hi hi'
        simp
    have husnoc (d : Digit) :
        List.ofFn (Fin.snoc (fun i => w.get i) d) = w ++ [d] := by
      rw [ofFn_snoc, hu]
    rw [hu] at h
    simp_rw [husnoc] at h
    have hreal :
        (firstStartCount artificialStream (sampledCheckpoint q) w : ℝ) =
          ∑ d : Digit,
            (firstStartCount artificialStream (sampledCheckpoint q)
              (w ++ [d]) : ℝ) := by
      exact_mod_cast h.symm
    dsimp only [w] at hreal
    simp only [List.append_assoc] at hreal
    rw [hreal, Finset.sum_div]
  normalized_dominant := by
    intro i hi
    simp only [pathWord_zero_eq_replicate, ← List.replicate_add]
    rw [← mul_div_assoc]
    rw [div_le_div_iff_of_pos_right (by
      exact_mod_cast zeroRoot_firstStartCount_pos q)]
    simpa [Nat.add_assoc] using zeroPath_movingThreshold_dominant q i hi

theorem artificialMovingRootRow_windows :
    ∀ H : ℕ, ∀ᶠ q in atTop, H ≤ (artificialMovingRootRow q).windowLength := by
  intro H
  filter_upwards [eventually_ge_atTop H] with q hq
  dsimp only [artificialMovingRootRow]
  unfold stageOrder
  omega

/-- T33 compactness applied to the explicit all-zero moving roots in the
actual artificial-stream count rows. -/
theorem exists_artificialStream_movingRoot_tangent_branch :
    (∀ q, (artificialMovingRootRow q).count =
      fun w => (firstStartCount artificialStream (sampledCheckpoint q) w : ℝ)) ∧
    (∀ q, (artificialMovingRootRow q).root =
      List.replicate (stageOrder q) (0 : Digit)) ∧
    (∀ q, (artificialMovingRootRow q).windowLength = stageOrder q) ∧
    Tendsto (fun q => (artificialMovingRootRow q).threshold) atTop (nhds 1) ∧
    Tendsto normalizedStageLeakage atTop (nhds 0) ∧
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ tangent : Word → ℝ, ∃ branch : ℕ → Digit,
        tangent [] = 1 ∧
        (∀ v, 0 ≤ tangent v ∧ tangent v ≤ 1) ∧
        (∀ v, tangent v = ∑ d : Digit, tangent (v ++ [d])) ∧
        (∀ v, Tendsto
          (fun j => normalizedProfile (artificialMovingRootRow (subseq j)) v)
          atTop (nhds (tangent v))) ∧
        (∀ i, ∀ᶠ j in atTop,
          (artificialMovingRootRow (subseq j)).digit i = branch i) ∧
        (∀ i, 0 < tangent (pathWord branch i)) ∧
        (∀ i, tangent (pathWord branch i) ≤
          tangent (pathWord branch (i + 1))) := by
  refine ⟨fun q => rfl, fun q => rfl, fun q => rfl, ?_,
    normalizedStageLeakage_tendsto_zero, ?_⟩
  · simpa only [artificialMovingRootRow] using movingThreshold_tendsto_one
  · simpa using exists_movingRoot_tangent_branch artificialMovingRootRow 1
      (by norm_num) artificialMovingRootRow_windows (by
        simpa only [artificialMovingRootRow] using movingThreshold_tendsto_one)

/-! ## The literal T29 telescope on the stream count tree -/

/-- Starting from the unique level-zero node, retain exactly the children
selected by the repeated-seed periodicity. -/
def stageSurvivors (q : ℕ) : (n : ℕ) → Finset (Fin (10 ^ n))
  | 0 => Finset.univ
  | n + 1 => (stageSurvivors q n).image
      (fun a => decimalChild n a (stageSuccessorChoice q n a))

theorem stageSurvivors_step (q n : ℕ) :
    SurvivorStep (stageDominant q) (stageSuccessorChoice q)
      (stageSurvivors q) n := by
  simp [SurvivorStep, stageSurvivors, stageDominant]

theorem stageSurvivors_startMass (q : ℕ) :
    survivorEnergy
        (streamCountTree artificialStream (sampledCheckpoint q)).toReal
        (stageSurvivors q) 0 =
      FiniteCountTreeLeakage.collisionEnergy
        (streamCountTree artificialStream (sampledCheckpoint q)).toReal 0 := by
  simp [survivorEnergy, FiniteCountTreeLeakage.collisionEnergy, stageSurvivors]

/-- T29 applied, rather than reproved, to the natural count tree cut from the
actual artificial stream with overlapping first-start counts. -/
theorem artificialStream_finite_base10_countTree_leakage (q h : ℕ) :
    FiniteCountTreeLeakage.collisionEnergy
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal 0 -
        survivorEnergy
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          (stageSurvivors q) h ≤
      ∑ i ∈ Finset.range h,
        leakage
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          (stageDominant q) (stageSuccessorChoice q) i := by
  simpa only [Nat.zero_add] using
    finite_base10_countTree_leakage
      (streamCountTree artificialStream (sampledCheckpoint q))
      (stageDominant q) (stageSuccessorChoice q) (stageSurvivors q) 0 h
      (by simpa using
        streamCountTree_isFinite artificialStream (sampledCheckpoint q) h)
      (stageSurvivors_startMass q)
      (fun i _ => by simpa using stageSurvivors_step q i)

/-- T29's telescope applied at the actual moving root
`stageOrder q`, over exactly the `stageOrder q` edge levels used above.
The survivor compatibility hypotheses are explicit because T29, correctly,
does not infer a coherent survivor family from small full leakage alone. -/
theorem artificialStream_movingWindow_t29_leakage (q : ℕ)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n)))
    (hstart :
      survivorEnergy
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          survivors (stageOrder q) =
        FiniteCountTreeLeakage.collisionEnergy
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          (stageOrder q))
    (hsteps : ∀ i, i < stageOrder q →
      SurvivorStep (stageDominant q) (stageSuccessorChoice q) survivors
        (stageOrder q + i)) :
    FiniteCountTreeLeakage.collisionEnergy
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          (stageOrder q) -
        survivorEnergy
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          survivors (stageOrder q + stageOrder q) ≤
      ∑ i ∈ Finset.range (stageOrder q),
        leakage
          (streamCountTree artificialStream (sampledCheckpoint q)).toReal
          (stageDominant q) (stageSuccessorChoice q) (stageOrder q + i) := by
  exact finite_base10_countTree_leakage
    (streamCountTree artificialStream (sampledCheckpoint q))
    (stageDominant q) (stageSuccessorChoice q) survivors
    (stageOrder q) (stageOrder q)
    (streamCountTree_isFinite artificialStream (sampledCheckpoint q)
      (stageOrder q + stageOrder q)) hstart hsteps

/-! ## Stable branches in the original coordinates -/

/-- Equation (33)'s quantifier order.  The absolute root, continuation, and
`beta` are fixed.  Each depth may have its own eventual row cutoff. -/
def StableOriginalBranch (beta : ℝ) : Prop :=
  ∃ root : Word, ∃ continuation : ℕ → Digit,
    ∀ i : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      beta *
          (firstStartCount artificialStream (sampledCheckpoint q)
            (root ++ pathWord continuation i) : ℝ) ≤
        firstStartCount artificialStream (sampledCheckpoint q)
          (root ++ pathWord continuation (i + 1)) ∧
      0 < beta *
        (firstStartCount artificialStream (sampledCheckpoint q)
          (root ++ pathWord continuation i) : ℝ)

/-- The precise actual-count estimate still needed to rule out a stable
original-coordinate half-dominant edge. -/
def EventuallyShallowHalfSparse : Prop :=
  ∀ w : Word, ∀ d : Digit, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
    2 * firstStartCount artificialStream (sampledCheckpoint q) (w ++ [d]) <
      firstStartCount artificialStream (sampledCheckpoint q) w

/-- The repeated exhaustive seeds unconditionally satisfy the isolated
shallow sparsity estimate. -/
theorem eventuallyShallowHalfSparse : EventuallyShallowHalfSparse := by
  intro w d
  refine ⟨w.length, fun q hq => ?_⟩
  exact two_mul_firstStartCount_child_lt_parent_of_shallow q w d (by
    unfold stageOrder
    omega)

/-- A uniform shallow successor estimate on the actual repeated-seed stream
immediately negates equation (33), already at its first edge. -/
theorem not_stableOriginalBranch_half_of_eventuallyShallowHalfSparse
    (hshallow : EventuallyShallowHalfSparse) :
    ¬ StableOriginalBranch (1 / 2 : ℝ) := by
  rintro ⟨root, continuation, hstable⟩
  obtain ⟨Qstable, hQstable⟩ := hstable 0
  obtain ⟨Qsparse, hQsparse⟩ := hshallow root (continuation 0)
  let q := max Qstable Qsparse
  have hstableq := hQstable q (le_max_left _ _)
  have hsparseq := hQsparse q (le_max_right _ _)
  simp only [pathWord, List.append_nil] at hstableq
  have hhalf :
      (1 / 2 : ℝ) *
          firstStartCount artificialStream (sampledCheckpoint q) root ≤
        firstStartCount artificialStream (sampledCheckpoint q)
          (root ++ [continuation 0]) := hstableq.1
  have hsparseReal :
      2 * (firstStartCount artificialStream (sampledCheckpoint q)
          (root ++ [continuation 0]) : ℝ) <
        firstStartCount artificialStream (sampledCheckpoint q) root := by
    exact_mod_cast hsparseq
  norm_num at hhalf
  linarith

theorem not_stableOriginalBranch_half :
    ¬ StableOriginalBranch (1 / 2 : ℝ) :=
  not_stableOriginalBranch_half_of_eventuallyShallowHalfSparse
    eventuallyShallowHalfSparse

/-- No fixed original-coordinate root and continuation is eventually
half-dominant.  Every branch and row-cutoff quantifier is expanded here. -/
theorem no_original_halfDominant_branch_explicit :
    ¬ ∃ root : Word, ∃ continuation : ℕ → Digit,
      ∀ i : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
        (1 / 2 : ℝ) *
              firstStartCount artificialStream (sampledCheckpoint q)
                (root ++ pathWord continuation i) ≤
            firstStartCount artificialStream (sampledCheckpoint q)
              (root ++ pathWord continuation (i + 1)) ∧
          0 < (1 / 2 : ℝ) *
            firstStartCount artificialStream (sampledCheckpoint q)
              (root ++ pathWord continuation i) := by
  simpa only [StableOriginalBranch] using not_stableOriginalBranch_half

/-- Combined end-to-end certificate, conditional only on the isolated shallow
count estimate `EventuallyShallowHalfSparse`.  All other components are proved
above for the literal stream. -/
theorem artificialStream_obstruction_of_eventuallyShallowHalfSparse
    (hshallow : EventuallyShallowHalfSparse) :
    artificialStream = concatStream stageBlock ∧
    (∀ q, sampledCheckpoint q = stageStart (q + 1)) ∧
    (∀ q, inspectionCheckpoint q =
      sampledCheckpoint q + 2 * stageOrder q) ∧
    (∀ N w, firstStartCount artificialStream N w =
      blockCount artificialStream w N) ∧
    (∀ q h,
      FiniteCountTreeLeakage.collisionEnergy
            (streamCountTree artificialStream (sampledCheckpoint q)).toReal 0 -
          survivorEnergy
            (streamCountTree artificialStream (sampledCheckpoint q)).toReal
            (stageSurvivors q) h ≤
        ∑ i ∈ Finset.range h,
          leakage
            (streamCountTree artificialStream (sampledCheckpoint q)).toReal
            (stageDominant q) (stageSuccessorChoice q) i) ∧
    Tendsto (fun q => (artificialMovingRootRow q).threshold) atTop (nhds 1) ∧
    Tendsto normalizedStageLeakage atTop (nhds 0) ∧
    (∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ tangent : Word → ℝ, ∃ branch : ℕ → Digit,
        tangent [] = 1 ∧
        (∀ v, 0 ≤ tangent v ∧ tangent v ≤ 1) ∧
        (∀ v, tangent v = ∑ d : Digit, tangent (v ++ [d])) ∧
        (∀ v, Tendsto
          (fun j => normalizedProfile (artificialMovingRootRow (subseq j)) v)
          atTop (nhds (tangent v))) ∧
        (∀ i, ∀ᶠ j in atTop,
          (artificialMovingRootRow (subseq j)).digit i = branch i) ∧
        (∀ i, 0 < tangent (pathWord branch i)) ∧
        (∀ i, tangent (pathWord branch i) ≤
          tangent (pathWord branch (i + 1)))) ∧
    ¬ StableOriginalBranch (1 / 2 : ℝ) := by
  have htangent := exists_artificialStream_movingRoot_tangent_branch
  refine ⟨rfl, fun q => rfl, fun q => rfl, fun N w => rfl,
    artificialStream_finite_base10_countTree_leakage, ?_,
    normalizedStageLeakage_tendsto_zero, htangent.2.2.2.2.2,
    not_stableOriginalBranch_half_of_eventuallyShallowHalfSparse hshallow⟩
  simpa only [artificialMovingRootRow] using movingThreshold_tendsto_one

/-- Unconditional end-to-end certificate for the explicit artificial stream. -/
theorem artificialStream_obstruction :
    artificialStream = concatStream stageBlock ∧
    (∀ q, sampledCheckpoint q = stageStart (q + 1)) ∧
    (∀ q, inspectionCheckpoint q =
      sampledCheckpoint q + 2 * stageOrder q) ∧
    (∀ N w, firstStartCount artificialStream N w =
      blockCount artificialStream w N) ∧
    (∀ q h,
      FiniteCountTreeLeakage.collisionEnergy
            (streamCountTree artificialStream (sampledCheckpoint q)).toReal 0 -
          survivorEnergy
            (streamCountTree artificialStream (sampledCheckpoint q)).toReal
            (stageSurvivors q) h ≤
        ∑ i ∈ Finset.range h,
          leakage
            (streamCountTree artificialStream (sampledCheckpoint q)).toReal
            (stageDominant q) (stageSuccessorChoice q) i) ∧
    Tendsto (fun q => (artificialMovingRootRow q).threshold) atTop (nhds 1) ∧
    Tendsto normalizedStageLeakage atTop (nhds 0) ∧
    (∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ tangent : Word → ℝ, ∃ branch : ℕ → Digit,
        tangent [] = 1 ∧
        (∀ v, 0 ≤ tangent v ∧ tangent v ≤ 1) ∧
        (∀ v, tangent v = ∑ d : Digit, tangent (v ++ [d])) ∧
        (∀ v, Tendsto
          (fun j => normalizedProfile (artificialMovingRootRow (subseq j)) v)
          atTop (nhds (tangent v))) ∧
        (∀ i, ∀ᶠ j in atTop,
          (artificialMovingRootRow (subseq j)).digit i = branch i) ∧
        (∀ i, 0 < tangent (pathWord branch i)) ∧
        (∀ i, tangent (pathWord branch i) ≤
          tangent (pathWord branch (i + 1)))) ∧
    ¬ StableOriginalBranch (1 / 2 : ℝ) :=
  artificialStream_obstruction_of_eventuallyShallowHalfSparse
    eventuallyShallowHalfSparse

end DecimalFactorComplexity.ArtificialStreamObstruction

#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.firstStartCount_total
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.firstStartCount_snoc
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.firstStartCount_cons_endpoint
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.firstStartCount_checkpoint_add
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.streamCountTree_isFinite
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.stageErrorStarts_card
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.artificialStream_stageSafeStart_periodic
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.stageLeakage_le
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.normalizedStageLeakage_tendsto_zero
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.artificialStream_arbitrarilyLong_lowLeakage_windows
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.exists_artificialStream_movingRoot_tangent_branch
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.artificialStream_finite_base10_countTree_leakage
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.artificialStream_movingWindow_t29_leakage
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.stageCoreCount_eq_coreSize_mul_pow
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.eventuallyShallowHalfSparse
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.not_stableOriginalBranch_half
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.no_original_halfDominant_branch_explicit
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.not_stableOriginalBranch_half_of_eventuallyShallowHalfSparse
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.artificialStream_obstruction_of_eventuallyShallowHalfSparse
#print axioms DecimalFactorComplexity.ArtificialStreamObstruction.artificialStream_obstruction
