import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiDigits.T25ChampernowneNormality
import TheoryLib.PiQuantitativeBlockHitting.T2ChampernowneQuantitativeCover

/-!
# T2: strict hierarchy witnesses for positive lower block density

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This file concerns two explicit artificial decimal streams.  It transfers T25's
normality theorem to the exact occurrence-count and liminf predicate from T1,
and constructs a disjunctive sparse-island stream for which one word has
liminf frequency zero.  It proves nothing about the decimal digits of pi and
does not resolve the canonical open question.
-/

noncomputable section

open Filter Finset Topology

namespace Theory.PiDigits.PositiveLowerBlockDensity.T2

open Theory.PiDigits.T21 Theory.PiDigits.T22 Theory.PiDigits.T23
open Theory.PiDigits.T25
open Theory.PiDigits.QuantitativeChampernowneCover
open Theory.PiDigits.PositiveLowerBlockDensity

/-- A match wholly contained in a finite prefix is also counted by T1's exact
count, whose starts range over all `n < N`. -/
lemma finitePrefixOccurrenceCount_le_blockCount
    (s : ℕ → Fin 10) (w : List (Fin 10)) (hw : w ≠ []) (N : ℕ) :
    finiteContiguousOccurrenceCount w (List.ofFn fun i : Fin N => s i) ≤
      blockCount s w N := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [finiteContiguousOccurrenceCount, blockCount, hw]
  unfold finiteContiguousOccurrenceCount blockCount
  apply Finset.card_le_card_of_injOn
      (fun i : ℕ => (⟨i % N, Nat.mod_lt i (Nat.pos_of_ne_zero hN)⟩ : Fin N))
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    simp only [List.length_ofFn] at hi
    have hiN : i < N := by
      have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
      omega
    have hmod : i % N = i := Nat.mod_eq_of_lt hiN
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    rw [hmod]
    have hijN : i + j.val < N := by
      have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
      omega
    have hget := congrArg (fun L : List (Fin 10) => L[j.val]?) hi.2
    simp [j.isLt, hijN] at hget
    exact hget
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
    simp only [List.length_ofFn] at hi hj
    have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
    have hiN : i < N := by omega
    have hjN : j < N := by omega
    simpa [Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hjN] using congrArg Fin.val hij

/-- T25's finite-prefix frequency is bounded above by T1's exact frequency. -/
lemma t25_blockFrequency_le_exact_blockFrequency
    (w : List (Fin 10)) (hw : w ≠ []) (N : ℕ) :
    Theory.PiDigits.T25.blockFrequency w N ≤
      blockFrequency champernowneDigit w N := by
  unfold Theory.PiDigits.T25.blockFrequency blockFrequency streamPrefix
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      (finitePrefixOccurrenceCount_le_blockCount champernowneDigit w hw N)
  · positivity

/-- The exact T1 frequency of a Champernowne word is eventually bounded below
by half of its positive T25 normality limit. -/
lemma champernowne_eventually_frequency_lower_bound
    (w : List (Fin 10)) (hw : w ≠ []) :
    ∀ᶠ N : ℕ in atTop,
      ((10 : ℝ) ^ (-(w.length : ℤ))) / 2 ≤
        blockFrequency champernowneDigit w N := by
  let c : ℝ := (10 : ℝ) ^ (-(w.length : ℤ))
  have hc : 0 < c := by positivity
  have ht := champernowne_full_baseTen_normality w hw
  have hnear : ∀ᶠ N : ℕ in atTop,
      c / 2 < Theory.PiDigits.T25.blockFrequency w N := by
    have hopen : Set.Ioi (c / 2) ∈ 𝓝 c := Ioi_mem_nhds (by linarith)
    exact ht.eventually hopen
  filter_upwards [hnear] with N hN
  exact (le_of_lt hN).trans (t25_blockFrequency_le_exact_blockFrequency w hw N)

/-- T22's artificial Champernowne stream satisfies T1's exact positive-lower
block-density predicate.  This is the solved analogue, not a theorem about pi. -/
theorem champernowne_hasPositiveLowerBlockDensity :
    HasPositiveLowerBlockDensity champernowneDigit := by
  intro w hw
  let c : ℝ := ((10 : ℝ) ^ (-(w.length : ℤ))) / 2
  have hc : 0 < c := by positivity
  have hb : atTop.IsCoboundedUnder (· ≥ ·)
      (blockFrequency champernowneDigit w) :=
    Filter.isCoboundedUnder_ge_of_le atTop
      (blockFrequency_le_one champernowneDigit w)
  have hliminf : c ≤ liminf (blockFrequency champernowneDigit w) atTop :=
    le_liminf_of_le hb (champernowne_eventually_frequency_lower_bound w hw)
  exact hc.trans_le hliminf

/-! ## A sparse-island disjunctive stream -/

/-- Stage `k` consists of a long zero sea followed by the `k`th finite
Champernowne block.  The fourth-power gaps make the islands density zero. -/
def sparseIslandBlocks (k : ℕ) : List (Fin 10) :=
  List.replicate ((k + 1) ^ 4) 0 ++ champernowneBlocks k

lemma sparseIslandBlocks_ne_nil (k : ℕ) : sparseIslandBlocks k ≠ [] := by
  simp [sparseIslandBlocks]

/-- The explicit zero-padded concatenation used for the separator. -/
def sparseIslandStream : ℕ → Fin 10 :=
  concatStream sparseIslandBlocks

/-- Every Champernowne block occurs in the sparse stream after its zero gap. -/
lemma champernowneBlock_occursAt_sparseIslandStream (k : ℕ) :
    WordOccursAt sparseIslandStream (champernowneBlocks k)
      ((finiteConcat sparseIslandBlocks k).length + (k + 1) ^ 4) := by
  intro i hi
  have hinside : (k + 1) ^ 4 + i < (sparseIslandBlocks k).length := by
    simp [sparseIslandBlocks]
    omega
  have hcoverage := enumeratedBlock_occursAt_concatStream
    sparseIslandBlocks sparseIslandBlocks_ne_nil k ((k + 1) ^ 4 + i) hinside
  simpa [sparseIslandStream, sparseIslandBlocks, WordOccursAt,
    Nat.add_assoc] using hcoverage

/-- The sparse-island stream has T21's exact generic V1 property. -/
theorem sparseIslandStream_everyFiniteWordOccurs :
    EveryFiniteWordOccurs sparseIslandStream := by
  intro w
  let v := prefixedValue w
  let k := v - 1
  have hvpos : 0 < v := prefixedValue_pos w
  have hk : k + 1 = v := by
    dsimp [k]
    omega
  have hblock : champernowneBlocks k = 1 :: w := by
    unfold champernowneBlocks
    rw [hk]
    exact decimalDigits_prefixedValue w
  refine ⟨(finiteConcat sparseIslandBlocks k).length + (k + 1) ^ 4 + 1, ?_⟩
  intro i hi
  have hocc := champernowneBlock_occursAt_sparseIslandStream k
    (i + 1) (by simp [hblock]; omega)
  simpa [WordOccursAt, hblock, Nat.add_assoc, Nat.add_comm] using hocc

/- The remaining lemmas bound singleton-one occurrences at endpoints inside
the long zero gaps. -/

/-- The `k`th Champernowne island has at most `k + 1` digits. -/
lemma champernowneBlocks_length_le_index_succ (k : ℕ) :
    (champernowneBlocks k).length ≤ k + 1 := by
  unfold champernowneBlocks
  apply decimalDigits_length_le_of_lt_ten_pow
  exact Nat.lt_pow_self (by norm_num)

/-- The first `k` sparse blocks contain at most `k * (k + 1)` copies of digit
one.  The deliberately coarse bound avoids any assumptions about their actual
decimal digit distribution. -/
lemma sparse_prefix_one_count_le (k : ℕ) :
    (finiteConcat sparseIslandBlocks k).count 1 ≤ k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [finiteConcat_succ, List.count_append]
      have hisland : (champernowneBlocks k).count 1 ≤ k + 1 :=
        List.count_le_length.trans
          (champernowneBlocks_length_le_index_succ k)
      have hblock : (sparseIslandBlocks k).count 1 ≤ k + 1 := by
        have hrep : (List.replicate ((k + 1) ^ 4) (0 : Fin 10)).count 1 = 0 := by
          induction ((k + 1) ^ 4) with
          | zero => simp
          | succ n ih => simp [List.replicate_succ, ih]
        rw [sparseIslandBlocks, List.count_append, hrep, zero_add]
        exact hisland
      calc
        (finiteConcat sparseIslandBlocks k).count 1 +
            (sparseIslandBlocks k).count 1 ≤ k * (k + 1) + (k + 1) :=
          Nat.add_le_add ih hblock
        _ ≤ (k + 1) * (k + 1 + 1) := by nlinarith

/-- Endpoint immediately after the zero gap of stage `k`. -/
def sparseGapEndpoint (k : ℕ) : ℕ :=
  (finiteConcat sparseIslandBlocks k).length + (k + 1) ^ 4

/-- Before the end of a finite concatenation, `concatStream` agrees with that
finite list.  This public bridge is useful for later sparse concatenations. -/
lemma concatStream_eq_getElem_finiteConcat {α : Type*} [Inhabited α]
    (blocks : ℕ → List α) (hne : ∀ k, blocks k ≠ [])
    (k n : ℕ) (hn : n < (finiteConcat blocks k).length) :
    concatStream blocks n = (finiteConcat blocks k)[n] := by
  induction k with
  | zero => simp at hn
  | succ k ih =>
      have hnappend : n < (finiteConcat blocks k ++ blocks k).length := by
        simpa only [finiteConcat_succ] using hn
      simp only [List.length_append] at hnappend
      have hgoal :
          concatStream blocks n = (finiteConcat blocks k ++ blocks k)[n] := by
        by_cases hprev : n < (finiteConcat blocks k).length
        · have hstream := ih hprev
          rw [List.getElem_append_left hprev]
          exact hstream
        · let i := n - (finiteConcat blocks k).length
          have hi : i < (blocks k).length := by
            dsimp [i]
            omega
          have hn_eq : n = (finiteConcat blocks k).length + i := by
            dsimp [i]
            omega
          have hcoverage := enumeratedBlock_occursAt_concatStream blocks hne k i hi
          have hget : (finiteConcat blocks k ++ blocks k)[n] = (blocks k)[i] := by
            rw [List.getElem_append_right (Nat.le_of_not_gt hprev)]
          calc
            concatStream blocks n =
                concatStream blocks ((finiteConcat blocks k).length + i) := by rw [← hn_eq]
            _ = (blocks k)[i] := hcoverage
            _ = (finiteConcat blocks k ++ blocks k)[n] := hget.symm
      simpa only [finiteConcat_succ] using hgoal

/-- Every position in the current gap is zero. -/
lemma sparseIslandStream_eq_zero_on_gap (k i : ℕ) (hi : i < (k + 1) ^ 4) :
    sparseIslandStream ((finiteConcat sparseIslandBlocks k).length + i) = 0 := by
  have hinside : i < (sparseIslandBlocks k).length := by
    simp [sparseIslandBlocks]
    omega
  have hcoverage := enumeratedBlock_occursAt_concatStream
    sparseIslandBlocks sparseIslandBlocks_ne_nil k i hinside
  simpa [sparseIslandStream, sparseIslandBlocks, hi] using hcoverage

/-- Up to a gap endpoint, singleton-one starts are supported only on earlier
finite islands. -/
lemma blockCount_one_sparseGapEndpoint_le (k : ℕ) :
    blockCount sparseIslandStream [1] (sparseGapEndpoint k) ≤ k * (k + 1) := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [blockCount, sparseGapEndpoint, sparseIslandStream,
      concatStream, finiteConcat, sparseIslandBlocks]
    rfl
  let L := (finiteConcat sparseIslandBlocks k).length
  have hLpos : 0 < L := by
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hlen := index_le_finiteConcat_length sparseIslandBlocks
      sparseIslandBlocks_ne_nil k
    omega
  let S : Finset (Fin L) := Finset.univ.filter fun n =>
    (finiteConcat sparseIslandBlocks k).get n = 1
  have hcard : blockCount sparseIslandStream [1] (sparseGapEndpoint k) ≤ S.card := by
    unfold blockCount
    apply Finset.card_le_card_of_injOn
      (fun n : Fin (sparseGapEndpoint k) =>
        (⟨n.val % L, Nat.mod_lt n.val hLpos⟩ : Fin L))
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hn
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      have hstream : sparseIslandStream n.val = 1 := by
        simpa using hn (0 : Fin 1)
      have hnL : n.val < L := by
        by_contra hnot
        have hnend : n.val < L + (k + 1) ^ 4 := by
          simpa [sparseGapEndpoint, L] using n.isLt
        let i := n.val - L
        have hi : i < (k + 1) ^ 4 := by
          dsimp [i]
          omega
        have hn_eq : n.val = L + i := by
          dsimp [i]
          omega
        have hzero := sparseIslandStream_eq_zero_on_gap k i hi
        rw [← hn_eq, hstream] at hzero
        norm_num at hzero
      have hfin :
          (⟨n.val % L, Nat.mod_lt n.val hLpos⟩ : Fin L) = ⟨n.val, hnL⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hnL
      rw [hfin]
      have hpref := concatStream_eq_getElem_finiteConcat sparseIslandBlocks
        sparseIslandBlocks_ne_nil k n.val hnL
      exact hpref.symm.trans hstream
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have haStream : sparseIslandStream a.val = 1 := by
        simpa using ha (0 : Fin 1)
      have hbStream : sparseIslandStream b.val = 1 := by
        simpa using hb (0 : Fin 1)
      have haL : a.val < L := by
        by_contra hnot
        have haend : a.val < L + (k + 1) ^ 4 := by
          simpa [sparseGapEndpoint, L] using a.isLt
        let i := a.val - L
        have hi : i < (k + 1) ^ 4 := by dsimp [i]; omega
        have ha_eq : a.val = L + i := by dsimp [i]; omega
        have hzero := sparseIslandStream_eq_zero_on_gap k i hi
        rw [← ha_eq, haStream] at hzero
        norm_num at hzero
      have hbL : b.val < L := by
        by_contra hnot
        have hbend : b.val < L + (k + 1) ^ 4 := by
          simpa [sparseGapEndpoint, L] using b.isLt
        let i := b.val - L
        have hi : i < (k + 1) ^ 4 := by dsimp [i]; omega
        have hb_eq : b.val = L + i := by dsimp [i]; omega
        have hzero := sparseIslandStream_eq_zero_on_gap k i hi
        rw [← hb_eq, hbStream] at hzero
        norm_num at hzero
      apply Fin.ext
      simpa [Nat.mod_eq_of_lt haL, Nat.mod_eq_of_lt hbL] using congrArg Fin.val hab
  calc
    blockCount sparseIslandStream [1] (sparseGapEndpoint k) ≤ S.card := hcard
    _ = (finiteConcat sparseIslandBlocks k).count 1 := by
      simpa [S] using
        (Fin.card_filter_univ_eq_vector_get_eq_count
          (a := (1 : Fin 10))
          (v := ⟨finiteConcat sparseIslandBlocks k, rfl⟩))
    _ ≤ k * (k + 1) := sparse_prefix_one_count_le k

/-- The exact T1 singleton-one frequencies tend to zero along gap endpoints. -/
lemma tendsto_sparseGapEndpoint_one_frequency :
    Tendsto (fun k => blockFrequency sparseIslandStream [1] (sparseGapEndpoint k))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun k =>
      blockFrequency_nonneg sparseIslandStream [1] (sparseGapEndpoint k)
  · exact Eventually.of_forall fun k => by
      have hcount := blockCount_one_sparseGapEndpoint_le k
      have hendpoint : (k + 1) ^ 4 ≤ sparseGapEndpoint k := by
        simp [sparseGapEndpoint]
      have hendpointPos : (0 : ℝ) < sparseGapEndpoint k := by
        exact_mod_cast lt_of_lt_of_le (by positivity : 0 < (k + 1) ^ 4) hendpoint
      unfold blockFrequency
      calc
        (blockCount sparseIslandStream [1] (sparseGapEndpoint k) : ℝ) /
            sparseGapEndpoint k ≤ ((k * (k + 1) : ℕ) : ℝ) / sparseGapEndpoint k := by
          apply div_le_div_of_nonneg_right
          · exact_mod_cast hcount
          · exact hendpointPos.le
        _ ≤ ((k * (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) ^ 4) := by
          apply div_le_div_of_nonneg_left
          · positivity
          · positivity
          · exact_mod_cast hendpoint
        _ ≤ (1 : ℝ) / (k + 1) := by
          norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (k + 1) ^ 4)
            (by positivity : (0 : ℝ) < k + 1)]
          nlinarith [sq_nonneg (k : ℝ), sq_nonneg ((k : ℝ) + 1)]
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Gap endpoints tend to infinity, so they are a valid subsequence for
bounding the exact liminf. -/
lemma tendsto_sparseGapEndpoint_atTop :
    Tendsto sparseGapEndpoint atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  calc
    b ≤ k := hk
    _ ≤ k + 1 := Nat.le_succ k
    _ ≤ (k + 1) ^ 4 := Nat.le_self_pow (by norm_num) (k + 1)
    _ ≤ sparseGapEndpoint k := by simp [sparseGapEndpoint]

/-- The exact T1 liminf for the word `[1]` in the sparse stream is zero. -/
theorem sparseIslandStream_one_liminf_eq_zero :
    liminf (blockFrequency sparseIslandStream [1]) atTop = 0 := by
  apply le_antisymm
  · calc
      liminf (blockFrequency sparseIslandStream [1]) atTop ≤
          liminf
            ((blockFrequency sparseIslandStream [1]) ∘ sparseGapEndpoint)
            atTop := by
        exact tendsto_sparseGapEndpoint_atTop.liminf_le_liminf_comp
          (hvf := Filter.isCoboundedUnder_ge_of_le _
            (blockFrequency_le_one sparseIslandStream [1]))
          (hg := Filter.isBoundedUnder_of_eventually_ge
            (Eventually.of_forall fun N =>
              blockFrequency_nonneg sparseIslandStream [1] N))
      _ = 0 := by
        apply Filter.Tendsto.liminf_eq
        simpa [Function.comp_def] using tendsto_sparseGapEndpoint_one_frequency
  · apply le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_le atTop
        (blockFrequency_le_one sparseIslandStream [1]))
    exact Eventually.of_forall fun N => blockFrequency_nonneg sparseIslandStream [1] N

/-- A single theorem exposing the exact occurrence and liminf claims of the
sparse counterexample. -/
theorem sparseIslandStream_exact_separator :
    EveryFiniteWordOccurs sparseIslandStream ∧
      liminf (blockFrequency sparseIslandStream [1]) atTop = 0 :=
  ⟨sparseIslandStream_everyFiniteWordOccurs,
    sparseIslandStream_one_liminf_eq_zero⟩

/-- Exact strict separator: generic V1 does not imply the canonical generic
positive-lower-density property.  Both predicates concern the explicit
artificial stream above, never the digits of pi. -/
theorem genericV1_does_not_imply_positiveLowerBlockDensity :
    EveryFiniteWordOccurs sparseIslandStream ∧
      ¬ HasPositiveLowerBlockDensity sparseIslandStream := by
  refine ⟨sparseIslandStream_everyFiniteWordOccurs, ?_⟩
  intro h
  have hone := h [1] (by simp)
  rw [sparseIslandStream_one_liminf_eq_zero] at hone
  exact lt_irrefl 0 hone

/-- Literal non-implication form of the separator, quantified over all generic
decimal streams. -/
theorem not_everyFiniteWordOccurs_implies_hasPositiveLowerBlockDensity :
    ¬ ∀ s : ℕ → Fin 10,
      EveryFiniteWordOccurs s → HasPositiveLowerBlockDensity s := by
  intro h
  exact genericV1_does_not_imply_positiveLowerBlockDensity.2
    (h sparseIslandStream
      genericV1_does_not_imply_positiveLowerBlockDensity.1)

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T2.champernowne_hasPositiveLowerBlockDensity
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T2.sparseIslandStream_one_liminf_eq_zero
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T2.sparseIslandStream_exact_separator
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T2.genericV1_does_not_imply_positiveLowerBlockDensity
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T2.not_everyFiniteWordOccurs_implies_hasPositiveLowerBlockDensity

end Theory.PiDigits.PositiveLowerBlockDensity.T2
