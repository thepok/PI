import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiPositiveLowerBlockDensity.T2StrictHierarchyWitnesses
import TheoryLib.PiDigits.T25ChampernowneNormality

/-!
# T4: normality, positive lower density, and a balanced separator

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module concerns generic streams and one explicit artificial balanced
stream. It proves nothing about the decimal digits of pi and does not resolve
the canonical open question.

The normality predicate below uses occurrences wholly contained in the first
`N` stream entries. T1's positive-lower-density predicate instead tests every
start `n < N`, even if the word extends beyond that prefix.
-/

noncomputable section

open Filter Finset Topology

namespace Theory.PiDigits.PositiveLowerBlockDensity.T4

open Theory.PiDigits.T22 Theory.PiDigits.T23 Theory.PiDigits.T25
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T2

/-- Frequency of occurrences wholly contained in the first `N` entries. -/
def containedPrefixFrequency
    (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) : ℝ :=
  (finiteContiguousOccurrenceCount w
      (List.ofFn fun i : Fin N => s i) : ℝ) / N

/-- Generic base-10 normality in the contained-prefix convention used by T25.
All nonempty lists are quantified, including lists beginning with zero. -/
def HasContainedPrefixBaseTenNormality (s : ℕ → Fin 10) : Prop :=
  ∀ w : List (Fin 10), w ≠ [] →
    Tendsto (containedPrefixFrequency s w) atTop
      (𝓝 ((10 : ℝ) ^ (-(w.length : ℤ))))

/-- Contained-prefix frequency is bounded above by T1's exact frequency. -/
lemma containedPrefixFrequency_le_blockFrequency
    (s : ℕ → Fin 10) (w : List (Fin 10)) (hw : w ≠ []) (N : ℕ) :
    containedPrefixFrequency s w N ≤ blockFrequency s w N := by
  unfold containedPrefixFrequency blockFrequency
  apply div_le_div_of_nonneg_right
  · exact_mod_cast finitePrefixOccurrenceCount_le_blockCount s w hw N
  · positivity

/-- Generic base-10 normality implies T1 positive lower block density. -/
theorem containedPrefixNormality_implies_hasPositiveLowerBlockDensity
    (s : ℕ → Fin 10) (hnormal : HasContainedPrefixBaseTenNormality s) :
    HasPositiveLowerBlockDensity s := by
  intro w hw
  let c : ℝ := (10 : ℝ) ^ (-(w.length : ℤ))
  have hc : 0 < c := by positivity
  have ht := hnormal w hw
  have hnear : ∀ᶠ N : ℕ in atTop,
      c / 2 < containedPrefixFrequency s w N := by
    have hopen : Set.Ioi (c / 2) ∈ 𝓝 c := Ioi_mem_nhds (by linarith)
    exact ht.eventually hopen
  have hlower : ∀ᶠ N : ℕ in atTop,
      c / 2 ≤ blockFrequency s w N := by
    filter_upwards [hnear] with N hN
    exact hN.le.trans (containedPrefixFrequency_le_blockFrequency s w hw N)
  have hcobound : atTop.IsCoboundedUnder (· ≥ ·) (blockFrequency s w) :=
    Filter.isCoboundedUnder_ge_of_le atTop (blockFrequency_le_one s w)
  have hliminf : c / 2 ≤ liminf (blockFrequency s w) atTop :=
    le_liminf_of_le hcobound hlower
  exact (div_pos hc (by norm_num)).trans_le hliminf

/-! ## The artificial balanced stream -/

/-- Stage `m` is exactly the length-`3^m` Champernowne prefix followed by
`3^m` zeros. -/
def balancedBlocks (m : ℕ) : List (Fin 10) :=
  List.ofFn (fun i : Fin (3 ^ m) => champernowneDigit i) ++
    List.replicate (3 ^ m) 0

@[simp] theorem balancedBlocks_length (m : ℕ) :
    (balancedBlocks m).length = 2 * 3 ^ m := by
  simp [balancedBlocks, two_mul]

lemma balancedBlocks_ne_nil (m : ℕ) : balancedBlocks m ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp [balancedBlocks_length] at hlen

/-- Infinite concatenation of the balanced stages. -/
def balancedStream : ℕ → Fin 10 :=
  concatStream balancedBlocks

/-- The first `m` stages have total length `3^m - 1`. -/
theorem finiteConcat_balancedBlocks_length (m : ℕ) :
    (finiteConcat balancedBlocks m).length = 3 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [finiteConcat_succ, List.length_append, ih, balancedBlocks_length,
        pow_succ]
      have hpow : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      omega

/-- Every cutoff belongs to some geometric stage. -/
lemma exists_balancedStageIndex (N : ℕ) :
    ∃ m : ℕ, N < 3 ^ (m + 1) := by
  have hpow : Tendsto (fun m : ℕ => 3 ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ m : ℕ in atTop, N + 1 ≤ 3 ^ m :=
    hpow.eventually (eventually_ge_atTop (N + 1))
  obtain ⟨m, hm⟩ := hevent.exists
  exact ⟨m, lt_of_lt_of_le (Nat.lt_succ_self N) hm |>.trans_le
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))⟩

/-- The first stage whose endpoint is at or beyond cutoff `N`. -/
noncomputable def balancedStageIndex (N : ℕ) : ℕ :=
  Nat.find (exists_balancedStageIndex N)

theorem balancedStageIndex_spec (N : ℕ) :
    N < 3 ^ (balancedStageIndex N + 1) := by
  exact Nat.find_spec (exists_balancedStageIndex N)

/-- A positive selected stage starts strictly before the cutoff. -/
theorem balancedStageIndex_start_le {N : ℕ}
    (hm : 0 < balancedStageIndex N) :
    3 ^ balancedStageIndex N ≤ N := by
  let h := exists_balancedStageIndex N
  have hpred : balancedStageIndex N - 1 < balancedStageIndex N :=
    Nat.sub_one_lt hm.ne'
  have hminimal := Nat.find_min h hpred
  have hsub : balancedStageIndex N - 1 + 1 = balancedStageIndex N :=
    Nat.sub_add_cancel hm
  rw [hsub] at hminimal
  omega

/-- The selected stage index tends to infinity with the cutoff. -/
theorem tendsto_balancedStageIndex_atTop :
    Tendsto balancedStageIndex atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (3 ^ b)] with N hN
  by_contra hnot
  have hidx : balancedStageIndex N < b := by omega
  have hpow : 3 ^ (balancedStageIndex N + 1) ≤ 3 ^ b :=
    Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_iff.mpr hidx)
  have hspec := balancedStageIndex_spec N
  omega

theorem tendsto_balancedStageIndex_sub_one_atTop :
    Tendsto (fun N => balancedStageIndex N - 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have h := tendsto_balancedStageIndex_atTop.eventually
    (eventually_ge_atTop (b + 1))
  filter_upwards [h] with N hN
  omega

/-- A contained occurrence in a copied finite segment contributes to T1's
exact global count. -/
lemma finiteSegmentOccurrenceCount_le_blockCount
    (s : ℕ → Fin 10) (w E : List (Fin 10)) (hw : w ≠ [])
    (offset N : ℕ)
    (hsegment : ∀ i : ℕ, ∀ hi : i < E.length, s (offset + i) = E[i])
    (hend : offset + E.length ≤ N) :
    finiteContiguousOccurrenceCount w E ≤ blockCount s w N := by
  classical
  by_cases hN : N = 0
  · subst N
    have hE : E = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hE, finiteContiguousOccurrenceCount, blockCount, hw]
  unfold finiteContiguousOccurrenceCount blockCount
  apply Finset.card_le_card_of_injOn
      (fun i : ℕ =>
        (⟨(offset + i) % N, Nat.mod_lt _ (Nat.pos_of_ne_zero hN)⟩ : Fin N))
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
    have hijE : i + j.val < E.length := by omega
    have hiN : offset + i < N := by omega
    rw [Nat.mod_eq_of_lt hiN, Nat.add_assoc]
    rw [hsegment (i + j.val) hijE]
    have hget := congrArg (fun L : List (Fin 10) => L[j.val]?) hi.2
    simp [j.isLt, hijE] at hget
    exact hget
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
    have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
    have hiN : offset + i < N := by omega
    have hjN : offset + j < N := by omega
    have hsum : offset + i = offset + j := by
      simpa [Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hjN] using congrArg Fin.val hij
    omega

/-- The Champernowne half of a balanced stage is copied verbatim. -/
theorem balancedStream_eq_champernowne_on_stage_prefix
    (m i : ℕ) (hi : i < 3 ^ m) :
    balancedStream ((finiteConcat balancedBlocks m).length + i) =
      champernowneDigit i := by
  have hinside : i < (balancedBlocks m).length := by
    rw [balancedBlocks_length]
    omega
  have hcoverage := enumeratedBlock_occursAt_concatStream
    balancedBlocks balancedBlocks_ne_nil m i hinside
  simpa [balancedStream, balancedBlocks, hi] using hcoverage

/-- T25 normality gives a positive contained-prefix count along powers of
three. -/
lemma champernowne_pow_eventually_contained_lower_bound
    (w : List (Fin 10)) (hw : w ≠ []) :
    ∀ᶠ m : ℕ in atTop,
      ((10 : ℝ) ^ (-(w.length : ℤ))) / 2 ≤
        (finiteContiguousOccurrenceCount w
          (List.ofFn fun i : Fin (3 ^ m) => champernowneDigit i) : ℝ) /
            ((3 ^ m : ℕ) : ℝ) := by
  let c : ℝ := (10 : ℝ) ^ (-(w.length : ℤ))
  have hc : 0 < c := by positivity
  have ht := champernowne_full_baseTen_normality w hw
  have hnear : ∀ᶠ N : ℕ in atTop,
      c / 2 ≤
        (finiteContiguousOccurrenceCount w
          (List.ofFn fun i : Fin N => champernowneDigit i) : ℝ) / N := by
    have hopen : Set.Ioi (c / 2) ∈ 𝓝 c := Ioi_mem_nhds (by linarith)
    exact (ht.eventually hopen).mono fun _ hN => hN.le
  have hpow : Tendsto (fun m : ℕ => 3 ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact hpow.eventually hnear

/-- Occurrences wholly contained in a stage's Champernowne half contribute to
the balanced stream's exact T1 count after that stage is complete. -/
lemma balancedStage_champernowneCount_le_blockCount
    (w : List (Fin 10)) (hw : w ≠ []) (m N : ℕ)
    (hend : (finiteConcat balancedBlocks (m + 1)).length ≤ N) :
    finiteContiguousOccurrenceCount w
        (List.ofFn fun i : Fin (3 ^ m) => champernowneDigit i) ≤
      blockCount balancedStream w N := by
  let E := List.ofFn fun i : Fin (3 ^ m) => champernowneDigit i
  apply finiteSegmentOccurrenceCount_le_blockCount balancedStream w E hw
      (finiteConcat balancedBlocks m).length N
  · intro i hi
    have hipow : i < 3 ^ m := by simpa [E] using hi
    have hstream := balancedStream_eq_champernowne_on_stage_prefix m i hipow
    simpa [E, hipow] using hstream
  · have hprefix :
        (finiteConcat balancedBlocks m).length + E.length ≤
          (finiteConcat balancedBlocks (m + 1)).length := by
      rw [finiteConcat_succ, List.length_append]
      simp [E, balancedBlocks_length]
    exact hprefix.trans hend

/-- Every nonempty word has an eventual explicit positive lower bound in the
balanced stream. -/
lemma balancedStream_eventually_frequency_lower_bound
    (w : List (Fin 10)) (hw : w ≠ []) :
    ∀ᶠ N : ℕ in atTop,
      ((10 : ℝ) ^ (-(w.length : ℤ))) / 18 ≤
        blockFrequency balancedStream w N := by
  let c : ℝ := (10 : ℝ) ^ (-(w.length : ℤ))
  have hc : 0 < c := by positivity
  have hlocal :=
    tendsto_balancedStageIndex_sub_one_atTop.eventually
      (champernowne_pow_eventually_contained_lower_bound w hw)
  have hstage := tendsto_balancedStageIndex_atTop.eventually
    (eventually_ge_atTop 1)
  filter_upwards [hlocal, hstage] with N hlocalN hstageN
  let m := balancedStageIndex N
  let j := m - 1
  have hm : 1 ≤ m := hstageN
  have hjm : j + 1 = m := by
    dsimp [j]
    omega
  have hstart : 3 ^ m ≤ N := balancedStageIndex_start_le (by omega)
  have hend : (finiteConcat balancedBlocks (j + 1)).length ≤ N := by
    rw [hjm, finiteConcat_balancedBlocks_length]
    omega
  have hcount := balancedStage_champernowneCount_le_blockCount w hw j N hend
  have hspec := balancedStageIndex_spec N
  have hmj : m + 1 = j + 2 := by omega
  have hpowEq : 3 ^ (m + 1) = 9 * 3 ^ j := by
    rw [hmj, pow_add]
    norm_num [Nat.mul_comm]
  have hNbound : N ≤ 9 * 3 ^ j := by
    rw [hpowEq] at hspec
    omega
  have hPpos : (0 : ℝ) < (3 ^ j : ℕ) := by positivity
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast lt_of_lt_of_le (pow_pos (by norm_num) m) hstart
  have hlocalMul :
      c / 2 * (3 ^ j : ℕ) ≤
        (finiteContiguousOccurrenceCount w
          (List.ofFn fun i : Fin (3 ^ j) => champernowneDigit i) : ℝ) := by
    apply (le_div_iff₀ hPpos).mp
    simpa [c, j, m] using hlocalN
  have htargetMul :
      c / 18 * N ≤ (blockCount balancedStream w N : ℝ) := by
    calc
      c / 18 * N ≤ c / 18 * (9 * (3 ^ j : ℕ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hNbound
        · positivity
      _ = c / 2 * (3 ^ j : ℕ) := by ring
      _ ≤ (finiteContiguousOccurrenceCount w
          (List.ofFn fun i : Fin (3 ^ j) => champernowneDigit i) : ℝ) := hlocalMul
      _ ≤ (blockCount balancedStream w N : ℝ) := by exact_mod_cast hcount
  unfold blockFrequency
  exact (le_div_iff₀ hNpos).2 htargetMul

/-- The artificial balanced stream satisfies the exact T1 liminf predicate
for every nonempty decimal word, including words with leading zeros. -/
theorem balancedStream_hasPositiveLowerBlockDensity :
    HasPositiveLowerBlockDensity balancedStream := by
  intro w hw
  let c : ℝ := ((10 : ℝ) ^ (-(w.length : ℤ))) / 18
  have hc : 0 < c := by positivity
  have hcobound : atTop.IsCoboundedUnder (· ≥ ·)
      (blockFrequency balancedStream w) :=
    Filter.isCoboundedUnder_ge_of_le atTop
      (blockFrequency_le_one balancedStream w)
  have hliminf : c ≤ liminf (blockFrequency balancedStream w) atTop :=
    le_liminf_of_le hcobound
      (balancedStream_eventually_frequency_lower_bound w hw)
  exact hc.trans_le hliminf

/-- The exact T1 quantifiers and liminf expression for the balanced stream. -/
theorem balancedStream_every_nonempty_word_positive_liminf :
    ∀ w : List (Fin 10), w ≠ [] →
      0 < liminf (blockFrequency balancedStream w) atTop :=
  balancedStream_hasPositiveLowerBlockDensity

/-! ## Failure of normality -/

/-- The zero half of stage `m` is copied verbatim. -/
theorem balancedStream_eq_zero_on_stage_suffix
    (m i : ℕ) (hi : i < 3 ^ m) :
    balancedStream
        ((finiteConcat balancedBlocks m).length + 3 ^ m + i) = 0 := by
  have hinside : 3 ^ m + i < (balancedBlocks m).length := by
    rw [balancedBlocks_length]
    omega
  have hcoverage := enumeratedBlock_occursAt_concatStream
    balancedBlocks balancedBlocks_ne_nil m (3 ^ m + i) hinside
  simpa [balancedStream, balancedBlocks, hi, Nat.add_assoc] using hcoverage

/-- Cutoff immediately after stage `m`. -/
def balancedStageEndpoint (m : ℕ) : ℕ :=
  (finiteConcat balancedBlocks (m + 1)).length

@[simp] theorem balancedStageEndpoint_eq (m : ℕ) :
    balancedStageEndpoint m = 3 ^ (m + 1) - 1 := by
  exact finiteConcat_balancedBlocks_length (m + 1)

theorem tendsto_balancedStageEndpoint_atTop :
    Tendsto balancedStageEndpoint atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hpow : Tendsto (fun m : ℕ => 3 ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ m : ℕ in atTop, b + 1 ≤ 3 ^ m :=
    hpow.eventually (eventually_ge_atTop (b + 1))
  filter_upwards [hevent] with m hm
  rw [balancedStageEndpoint_eq]
  have hpmono : 3 ^ m ≤ 3 ^ (m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
  omega

/-- The final zero half of stage `m` supplies at least `3^m` contained
singleton-zero occurrences at the stage endpoint. -/
lemma pow_le_zero_containedCount_at_balancedStageEndpoint (m : ℕ) :
    3 ^ m ≤ finiteContiguousOccurrenceCount [0]
      (List.ofFn fun i : Fin (balancedStageEndpoint m) => balancedStream i) := by
  classical
  let E := List.ofFn fun i : Fin (balancedStageEndpoint m) => balancedStream i
  let offset := (finiteConcat balancedBlocks m).length + 3 ^ m
  unfold finiteContiguousOccurrenceCount
  calc
    3 ^ m = (Finset.range (3 ^ m)).card := by simp
    _ ≤ ((Finset.range (E.length + 1 - [0].length)).filter fun n =>
        (E.drop n).take [0].length = [0]).card := by
      apply Finset.card_le_card_of_injOn (fun i : ℕ => offset + i)
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_range] at hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        have hpos : offset + i < E.length := by
          dsimp [offset, E]
          rw [List.length_ofFn, balancedStageEndpoint_eq,
            finiteConcat_balancedBlocks_length]
          rw [pow_succ]
          have hpow : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
          omega
        refine ⟨by simpa [E] using hpos, ?_⟩
        change (E.drop (offset + i)).take 1 = [0]
        rw [List.take_one_drop_eq_of_lt_length hpos]
        have hzero := balancedStream_eq_zero_on_stage_suffix m i hi
        simpa [E, offset] using hzero
      · intro i hi j hj hij
        dsimp [offset] at hij
        omega
    _ = finiteContiguousOccurrenceCount [0] E := rfl

/-- Along every complete-stage endpoint, at least one third of the contained
singleton starts carry zero. -/
theorem balancedStageEndpoint_zero_containedFrequency_ge (m : ℕ) :
    (1 / 3 : ℝ) ≤
      containedPrefixFrequency balancedStream [0] (balancedStageEndpoint m) := by
  have hcount := pow_le_zero_containedCount_at_balancedStageEndpoint m
  have hendpointPos : (0 : ℝ) < balancedStageEndpoint m := by
    have hpow : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hnat : 0 < balancedStageEndpoint m := by
      rw [balancedStageEndpoint_eq, pow_succ]
      omega
    exact_mod_cast hnat
  have hendpointBound : balancedStageEndpoint m ≤ 3 * 3 ^ m := by
    rw [balancedStageEndpoint_eq, pow_succ]
    omega
  unfold containedPrefixFrequency
  apply (le_div_iff₀ hendpointPos).2
  calc
    (1 / 3 : ℝ) * balancedStageEndpoint m ≤
        (1 / 3 : ℝ) * (3 * ((3 ^ m : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hendpointBound
      · norm_num
    _ = ((3 ^ m : ℕ) : ℝ) := by ring
    _ ≤ (finiteContiguousOccurrenceCount [0]
        (List.ofFn fun i : Fin (balancedStageEndpoint m) => balancedStream i) : ℝ) := by
      exact_mod_cast hcount

/-- The singleton-zero contained-prefix frequency cannot converge to `1/10`.
This is an explicit witness that the balanced artificial stream is not
base-10 normal. -/
theorem balancedStream_zero_frequency_not_tendsto_one_tenth :
    ¬ Tendsto (containedPrefixFrequency balancedStream [0]) atTop
      (𝓝 (1 / 10 : ℝ)) := by
  intro hnormalZero
  have hsub := hnormalZero.comp tendsto_balancedStageEndpoint_atTop
  have hsmall : ∀ᶠ m : ℕ in atTop,
      containedPrefixFrequency balancedStream [0] (balancedStageEndpoint m) <
        (1 / 5 : ℝ) := by
    exact hsub.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨m, hm⟩ := hsmall.exists
  have hlarge := balancedStageEndpoint_zero_containedFrequency_ge m
  linarith

theorem balancedStream_not_containedPrefixBaseTenNormal :
    ¬ HasContainedPrefixBaseTenNormality balancedStream := by
  intro hnormal
  have hzero := hnormal [0] (by simp)
  apply balancedStream_zero_frequency_not_tendsto_one_tenth
  simpa using hzero

/-- Exact strict separator within the artificial-stream hierarchy. It makes
no assertion about pi. -/
theorem balancedStream_strict_separator :
    HasPositiveLowerBlockDensity balancedStream ∧
      ¬ HasContainedPrefixBaseTenNormality balancedStream :=
  ⟨balancedStream_hasPositiveLowerBlockDensity,
    balancedStream_not_containedPrefixBaseTenNormal⟩

end Theory.PiDigits.PositiveLowerBlockDensity.T4

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T4.containedPrefixNormality_implies_hasPositiveLowerBlockDensity
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T4.balancedStream_every_nonempty_word_positive_liminf
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T4.balancedStream_zero_frequency_not_tendsto_one_tenth
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T4.balancedStream_strict_separator
