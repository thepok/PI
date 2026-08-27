import TheoryLib.PiPositiveDecimalFactorEntropy.T72T72ProjectedPeriodicity
import TheoryLib.PiPositiveDecimalFactorEntropy.T78T78SquareSparseProjectedPhaseObstruction
import TheoryLib.PiPositiveDecimalFactorEntropy.T80T80IntervalProjectedPhaseSelector

/-!
# T81: fixed-refinement aligned selector obstruction

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
Original source URL: none; the canonical question was formulated locally.

This is a sibling construction. It makes no assertion about pi and neither
proves nor disproves C6 or C1.

Normalized sibling statement: for fixed `s`, `L`, and `C` with `0 ≤ L`, all
sufficiently large parent lengths `m` have an aligned block of `10^s`
descendants absent from `observedPrefixes (m+s) (2^m)`. The depth bound uses
the parent length `m`, T80's `R` is common to every parent at that length, and
the T78 irrational witness is common to every descendant of the selected
parent but is allowed to vary with `m`.
-/

noncomputable section

open Finset Set

namespace DecimalFactorEntropy.T81AlignedSelectorObstruction

open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorEntropy.T48EndpointCarryKMP
open DecimalFactorEntropy.T57MovingWordCoreObstruction
open DecimalFactorEntropy.T65RationalCoreCertificate
open DecimalFactorEntropy.T72ProjectedPeriodicity
open DecimalFactorEntropy.T72ProjectedPeriodicity.T48
open DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction
open DecimalFactorEntropy.T80IntervalProjectedPhaseSelector
open DecimalFactorComplexity
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- Length-indexed decimal words, named locally to keep the T80 import explicit. -/
abbrev Word (m : ℕ) := Fin m → Fin 10

@[simp] theorem descendant_family_card (s : ℕ) :
    Fintype.card (Word s) = 10 ^ s := by
  simp

theorem append_descendants_injective {m s : ℕ} (u : Word m) :
    Function.Injective (fun v : Word s => Fin.append u v) := by
  intro v w h
  have hpair : (u, v) = (u, w) := (Fin.appendEquiv m s).injective h
  exact congrArg Prod.snd hpair

/-- The parent of a refined word is its first `m` digits. -/
def parentPrefix {m s : ℕ} (w : Word (m + s)) : Word m :=
  fun i => w (Fin.castAdd s i)

@[simp] theorem parentPrefix_append {m s : ℕ} (u : Word m) (v : Word s) :
    parentPrefix (Fin.append u v) = u := by
  funext i
  simp [parentPrefix]

/-- A strengthened form of T57's count, with room for a fixed refinement. -/
theorem doubled_inclusive_prefix_count_lt_ten_pow (m : ℕ) (hm : 2 ≤ m) :
    (2 ^ m + 1) * (2 * m + 2 ^ m + 2) < 10 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hR : 4 ≤ 2 ^ m := by
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
      have hfive :
          (2 ^ (m + 1) + 1) * (2 * (m + 1) + 2 ^ (m + 1) + 2) ≤
            5 * ((2 ^ m + 1) * (2 * m + 2 ^ m + 2)) := by
        rw [pow_succ]
        nlinarith
      rw [pow_succ]
      calc
        (2 ^ (m + 1) + 1) * (2 * (m + 1) + 2 ^ (m + 1) + 2) ≤
            5 * ((2 ^ m + 1) * (2 * m + 2 ^ m + 2)) := hfive
        _ < 5 * 10 ^ m := by nlinarith
        _ < 10 ^ m * 10 := by nlinarith [show 0 < 10 ^ m by positivity]

/-- Through depth `2^m`, fewer than `10^m` length-`m+s` words are observed
once `s ≤ m`. This is the exact pigeonhole bound used below. -/
theorem observedPrefixes_refinement_card_lt_parent_count
    (s m : ℕ) (hs : s ≤ m) (hm : 2 ≤ m) :
    (observedPrefixes (m + s) (2 ^ m)).card < 10 ^ m := by
  calc
    (observedPrefixes (m + s) (2 ^ m)).card ≤
        (2 ^ m + 1) * (m + s + 2 ^ m + 2) := by
      rw [← inclusive_prefix_count_closed_form]
      exact observedPrefixes_card_le_prefix_count (m + s) (2 ^ m)
    _ ≤ (2 ^ m + 1) * (2 * m + 2 ^ m + 2) := by
      gcongr
      omega
    _ < 10 ^ m := doubled_inclusive_prefix_count_lt_ten_pow m hm

/-- Exact index count, observed-family upper bound, and strict parent-count
bound, with the inclusive depth `2^m` visible in every expression. -/
theorem refinement_observed_factor_bound
    (s m : ℕ) (hs : s ≤ m) (hm : 2 ≤ m) :
    Fintype.card (PrefixIndex (m + s) (2 ^ m)) =
        (2 ^ m + 1) * (m + s + 2 ^ m + 2) ∧
      (observedPrefixes (m + s) (2 ^ m)).card ≤
        (2 ^ m + 1) * (m + s + 2 ^ m + 2) ∧
      (2 ^ m + 1) * (m + s + 2 ^ m + 2) < 10 ^ m := by
  have hcard := prefixIndex_card (m + s) (2 ^ m)
  rw [inclusive_prefix_count_closed_form] at hcard
  have hobs := observedPrefixes_card_le_prefix_count (m + s) (2 ^ m)
  rw [inclusive_prefix_count_closed_form] at hobs
  have hlt : (2 ^ m + 1) * (m + s + 2 ^ m + 2) < 10 ^ m := by
    calc
      (2 ^ m + 1) * (m + s + 2 ^ m + 2) ≤
          (2 ^ m + 1) * (2 * m + 2 ^ m + 2) := by
        gcongr
        omega
      _ < 10 ^ m := doubled_inclusive_prefix_count_lt_ten_pow m hm
  exact ⟨hcard, hobs, hlt⟩

/-- There is an aligned parent block none of whose `10^s` descendants occurs
in the common T78 observed-factor family through depth `2^m`. -/
theorem exists_aligned_parent_all_descendants_unobserved
    (s m : ℕ) (hs : s ≤ m) (hm : 2 ≤ m) :
    ∃ u : Word m, ∀ v : Word s,
      Fin.append u v ∉ observedPrefixes (m + s) (2 ^ m) := by
  classical
  by_contra hnone
  push Not at hnone
  let parents : Finset (Word m) :=
    (observedPrefixes (m + s) (2 ^ m)).image parentPrefix
  have hfull : (Finset.univ : Finset (Word m)) ⊆ parents := by
    intro u _hu
    obtain ⟨v, hv⟩ := hnone u
    apply Finset.mem_image.mpr
    exact ⟨Fin.append u v, hv, parentPrefix_append u v⟩
  have hparents_le : parents.card ≤ (observedPrefixes (m + s) (2 ^ m)).card := by
    exact Finset.card_image_le
  have hall_le : 10 ^ m ≤ (observedPrefixes (m + s) (2 ^ m)).card := by
    calc
      10 ^ m = (Finset.univ : Finset (Word m)).card := by simp
      _ ≤ parents.card := Finset.card_le_card hfull
      _ ≤ (observedPrefixes (m + s) (2 ^ m)).card := hparents_le
  exact (Nat.not_le_of_lt (observedPrefixes_refinement_card_lt_parent_count s m hs hm))
    hall_le

/-! ## T78 windows at a longer fixed refinement -/

/-- A length-`n` window meets one reserved square block. -/
def WindowMeetsBlockAtLength (n p j start t : ℕ) : Prop :=
  ∃ i : Fin n, InBlockInterval p j t (start + i.val)

/-- Uniqueness of the reserved block met by a length-`n` window. -/
theorem window_meets_unique_at_length
    {n p j start a b : ℕ}
    (hspace : n + blockWidth j ≤ spacing p)
    (ha : WindowMeetsBlockAtLength n p j start a)
    (hb : WindowMeetsBlockAtLength n p j start b) : a = b := by
  rcases ha with ⟨i, hi⟩
  rcases hb with ⟨k, hk⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hsep := blockEnd_add_spacing_le (m := p) hab
    have hfar : blockEnd p a + n ≤ blockEnd p b - blockWidth j := by
      apply Nat.le_sub_of_add_le
      simpa [Nat.add_assoc] using
        (Nat.add_le_add_left hspace (blockEnd p a)).trans hsep
    have hia : start + i.val < blockEnd p a := hi.2
    have hbk : blockEnd p b - blockWidth j ≤ start + k.val := hk.1
    omega
  · have hsep := blockEnd_add_spacing_le (m := p) hba
    have hfar : blockEnd p b + n ≤ blockEnd p a - blockWidth j := by
      apply Nat.le_sub_of_add_le
      simpa [Nat.add_assoc] using
        (Nat.add_le_add_left hspace (blockEnd p b)).trans hsep
    have hkb : start + k.val < blockEnd p b := hk.2
    have hai : blockEnd p a - blockWidth j ≤ start + i.val := hi.1
    omega

theorem scaledExpansion_window_eq_singleBlock_at_length
    {n p j start t : ℕ} (hj : j ≤ radius p)
    (hspace : n + blockWidth j ≤ spacing p)
    (ht : 1 ≤ t) (hmeet : WindowMeetsBlockAtLength n p j start t) :
    ∀ i : Fin n,
      scaledExpansion p j (start + i.val) =
        imageExpansion j (reciprocalPoint (blockEnd p t - 1)) (start + i.val) := by
  intro i
  by_cases hi : ∃ q : ℕ, 1 ≤ q ∧ InBlockInterval p j q (start + i.val)
  · obtain ⟨q, hq, hqi⟩ := hi
    have hqt : q = t :=
      window_meets_unique_at_length hspace ⟨i, hqi⟩ hmeet
    subst q
    exact scaledExpansion_eq_singleBlock hj ht hqi
  · have hscaled : scaledExpansion p j (start + i.val) = 0 := by
      apply scaledExpansion_eq_zero_of_no_interval
      intro q hq hqi
      exact hi ⟨q, hq, hqi⟩
    rw [hscaled]
    have hout : start + i.val < blockEnd p t - blockWidth j ∨
        blockEnd p t ≤ start + i.val := by
      by_contra hinside
      push Not at hinside
      exact hi ⟨t, ht, hinside⟩
    rcases hout with hbefore | hafter
    · exact (singleBlock_eq_zero_before hj ht hbefore).symm
    · exact (singleBlock_eq_zero_after ht hafter).symm

/-- Every length-`n` factor of a T78 scaled expansion belongs to the same
finite observed family, provided the square spacing accommodates the window. -/
theorem windowVector_mem_observedPrefixes_at_length
    {n p j start : ℕ} (hj : j ≤ radius p)
    (hspace : n + blockWidth j ≤ spacing p) :
    (fun i : Fin n => scaledExpansion p j (start + i.val)) ∈
      observedPrefixes n (radius p) := by
  by_cases hmeet : ∃ t : ℕ, 1 ≤ t ∧ WindowMeetsBlockAtLength n p j start t
  · let t : ℕ := Classical.choose hmeet
    have ht : 1 ≤ t := (Classical.choose_spec hmeet).1
    have htm := (Classical.choose_spec hmeet).2
    rcases htm with ⟨i, hi⟩
    have hstart : start < blockEnd p t :=
      lt_of_le_of_lt (Nat.le_add_right start i.val) hi.2
    let k := blockEnd p t - start - 1
    have hklt : k < n + 2 * j + 2 := by
      dsimp [k, t] at hstart hi ⊢
      simp only [InBlockInterval, blockWidth] at hi
      have hir := i.isLt
      omega
    have hvec : (fun r : Fin n => scaledExpansion p j (start + r.val)) =
        imagePrefix n j (reciprocalPoint k) := by
      funext r
      rw [scaledExpansion_window_eq_singleBlock_at_length hj hspace ht ⟨i, hi⟩ r]
      exact imageExpansion_shift_reciprocalPoint hstart r.val
    rw [hvec]
    exact imagePrefix_mem_observedPrefixes n (radius p) j hj
      (reciprocalPoint k) (Set.mem_insert_of_mem 0 (Set.mem_range_self k))
  · let k := n + 2 * j + 1
    have hzero : (fun i : Fin n => scaledExpansion p j (start + i.val)) =
        fun _ => 0 := by
      funext i
      apply scaledExpansion_eq_zero_of_no_interval
      intro t ht hi
      exact hmeet ⟨t, ht, ⟨i, hi⟩⟩
    have hprefix : imagePrefix n j (reciprocalPoint k) = fun _ => 0 := by
      apply imagePrefix_reciprocal_eq_zero_of_deep
      simp [k]
    rw [hzero, ← hprefix]
    exact imagePrefix_mem_observedPrefixes n (radius p) j hj
      (reciprocalPoint k) (Set.mem_insert_of_mem 0 (Set.mem_range_self k))

/-- T78's square spacing accommodates every length-`m+s` descendant window
when `s ≤ m`, uniformly through the inclusive depth `2^m`. -/
theorem refinement_window_fits
    {s m j : ℕ} (hs : s ≤ m) (hj : j ≤ 2 ^ m) :
    (m + s) + blockWidth j ≤ spacing m := by
  simp only [blockWidth, spacing, radius]
  omega

theorem refinedWord_nonempty {s m : ℕ} (hm : 0 < m) (w : Word (m + s)) :
    List.ofFn w ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp at hlen
  omega

/-- Absence from the common observed family makes the corresponding word
absent from every scaled expansion of the same T78 square witness. -/
theorem scaledExpansion_avoids_unobserved_refinement
    {s m j : ℕ} (hs : s ≤ m) (hj : j ≤ 2 ^ m)
    (w : Word (m + s))
    (hw : w ∉ observedPrefixes (m + s) (2 ^ m)) :
    AvoidsWord (List.ofFn w) (scaledExpansion m j) := by
  intro start hocc
  apply hw
  have hmem := windowVector_mem_observedPrefixes_at_length
    (n := m + s) (p := m) (j := j) (start := start)
    (by simpa [radius] using hj) (refinement_window_fits hs hj)
  have heq : (fun i : Fin (m + s) => scaledExpansion m j (start + i.val)) = w := by
    funext i
    have hi : i.val < (List.ofFn w).length := by simp
    have hdigit := hocc ⟨i.val, hi⟩
    simpa [List.get_eq_getElem] using hdigit
  rwa [heq] at hmem

/-- One and the same irrational T78 point belongs to the depth-`2^m` Core of
every unobserved length-`m+s` descendant. -/
theorem squarePoint_mem_unobserved_refinement_Core
    {s m : ℕ} (hs : s ≤ m)
    (w : Word (m + s))
    (hw : w ∉ observedPrefixes (m + s) (2 ^ m)) :
    squarePoint m ∈ Core (List.ofFn w) (2 ^ m) := by
  intro n j hj
  let a : DecimalStream := streamShift n (scaledExpansion m j)
  refine ⟨a, avoidsWord_streamShift (List.ofFn w) (scaledExpansion m j) n
    (scaledExpansion_avoids_unobserved_refinement hs hj w hw), ?_⟩
  rw [circleValue_streamShift,
    scaledExpansion_circleValue (by simpa [radius] using hj)]
  exact circleMul_commute (10 ^ n) (16 ^ j) (squarePoint m)

/-- T72's rational-core implication contradicts the common irrational witness,
so every unobserved descendant fails at every inclusive depth `r ≤ 2^m`. -/
theorem projectedPhase_fails_for_unobserved_refinement
    {s m : ℕ} (hs : s ≤ m) (hm : 0 < m)
    (w : Word (m + s))
    (hw : w ∉ observedPrefixes (m + s) (2 ^ m))
    (r : ℕ) (hr : r ≤ 2 ^ m) :
    ¬ Graph.GlobalPrimitivePhaseCriterion
      (carryKMPGraph (List.ofFn w) (refinedWord_nonempty hm w) r)
      coordinateZeroProjection := by
  intro hgraph
  have hrat := endpointComplete_globalProjectedPhase_implies_rationalCore
    (List.ofFn w) (refinedWord_nonempty hm w) r hgraph
  apply squarePoint_not_rational m
  exact hrat (squarePoint m)
    (core_antitone_radius (List.ofFn w) hr
      (squarePoint_mem_unobserved_refinement_Core hs w hw))

/-! ## Eventual affine domination and selector negations -/

/-- A uniform eventual version of T57's exponential-versus-affine lemma. The
threshold also forces `2 ≤ m` and the fixed refinement inequality `s ≤ m`. -/
theorem exists_eventual_two_pow_dominates_affine
    (s : ℕ) (L C : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, 2 ≤ M ∧ s ≤ M ∧
      ∀ m : ℕ, M ≤ m → L * (m : ℝ) + C ≤ (2 ^ m : ℕ) := by
  have hSlope : 0 ≤ 2 * L + 1 := by linarith
  obtain ⟨M, hM, hbig⟩ := exists_two_pow_dominates_affine
    (2 * L + 1) (C + |C| + (2 ^ s : ℕ)) hSlope
  have hCabs : 0 ≤ C + |C| := by linarith [neg_le_abs C]
  have hMnonneg : (0 : ℝ) ≤ (M : ℕ) := by positivity
  have hpowSMreal : ((2 ^ s : ℕ) : ℝ) ≤ (2 ^ M : ℕ) := by
    nlinarith [mul_nonneg hSlope hMnonneg]
  have hpowSM : 2 ^ s ≤ 2 ^ M := by exact_mod_cast hpowSMreal
  have hsM : s ≤ M := by
    by_contra hnot
    have hMs : M < s := by omega
    have hp_lt : 2 ^ M < 2 ^ s :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 hMs
    omega
  have hbase : L * (M : ℝ) + C ≤ (2 ^ M : ℕ) := by
    nlinarith [mul_nonneg hL hMnonneg, abs_nonneg C]
  have hLM : L ≤ (2 ^ M : ℕ) := by
    have hMtwo : (2 : ℝ) ≤ (M : ℕ) := by exact_mod_cast hM
    nlinarith [mul_nonneg hSlope hMnonneg, abs_nonneg C]
  refine ⟨M, hM, hsM, ?_⟩
  intro m hMm
  induction m, hMm using Nat.le_induction with
  | base => exact hbase
  | succ n hMn ih =>
      have hpowmono : 2 ^ M ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hMn
      have hLn : L ≤ ((2 ^ n : ℕ) : ℝ) := by
        calc
          L ≤ ((2 ^ M : ℕ) : ℝ) := hLM
          _ ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hpowmono
      calc
        L * ((n + 1 : ℕ) : ℝ) + C = (L * (n : ℝ) + C) + L := by
          push_cast
          ring
        _ ≤ ((2 ^ n : ℕ) : ℝ) + ((2 ^ n : ℕ) : ℝ) := add_le_add ih hLn
        _ = ((2 ^ (n + 1) : ℕ) : ℝ) := by
          rw [pow_succ]
          push_cast
          ring

/-- Every sufficiently large parent length has one aligned block all of whose
descendants share the displayed irrational Core witness and fail throughout
the full affine depth range. -/
theorem sufficiently_large_aligned_obstruction
    (s : ℕ) (L C : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, 2 ≤ M ∧ s ≤ M ∧
      ∀ m : ℕ, M ≤ m →
        ∃ hm0 : 0 < m, ∃ u : Word m,
          L * (m : ℝ) + C ≤ (2 ^ m : ℕ) ∧
          Fintype.card (PrefixIndex (m + s) (2 ^ m)) =
              (2 ^ m + 1) * (m + s + 2 ^ m + 2) ∧
          (observedPrefixes (m + s) (2 ^ m)).card ≤
              (2 ^ m + 1) * (m + s + 2 ^ m + 2) ∧
          (2 ^ m + 1) * (m + s + 2 ^ m + 2) < 10 ^ m ∧
          Fintype.card (Word s) = 10 ^ s ∧
          Irrational (squareReal m) ∧
          ∀ v : Word s,
            InLexRun ((wordIndex (wordList u)).val * 10 ^ s) (10 ^ s)
                (wordIndex (wordList (appendWord u v))) ∧
            wordCell (wordList (appendWord u v)) ⊆ wordCell (wordList u) ∧
            Fin.append u v ∉ observedPrefixes (m + s) (2 ^ m) ∧
            squarePoint m ∈ Core (List.ofFn (Fin.append u v)) (2 ^ m) ∧
            ∀ r : ℕ, (r : ℝ) ≤ L * (m : ℝ) + C →
              r ≤ 2 ^ m ∧
              ¬ Graph.GlobalPrimitivePhaseCriterion
                (carryKMPGraph (List.ofFn (Fin.append u v))
                  (refinedWord_nonempty hm0 (Fin.append u v)) r)
                coordinateZeroProjection := by
  obtain ⟨M, hM, hsM, hdepth⟩ :=
    exists_eventual_two_pow_dominates_affine s L C hL
  refine ⟨M, hM, hsM, ?_⟩
  intro m hMm
  have hm : 2 ≤ m := hM.trans hMm
  have hs : s ≤ m := hsM.trans hMm
  have hbound := hdepth m hMm
  obtain ⟨u, hu⟩ := exists_aligned_parent_all_descendants_unobserved s m hs hm
  obtain ⟨hcard, hobs, hlt⟩ := refinement_observed_factor_bound s m hs hm
  have hm0 : 0 < m := by omega
  refine ⟨hm0, u, hbound, hcard, hobs, hlt, descendant_family_card s,
    squareReal_irrational m, ?_⟩
  intro v
  have huv := hu v
  refine ⟨appendWord_index_in_parent_run u v, appendWord_wordCell_subset u v,
    huv, squarePoint_mem_unobserved_refinement_Core hs (Fin.append u v) huv, ?_⟩
  intro r hr
  have hrreal : (r : ℝ) ≤ (2 ^ m : ℕ) := hr.trans hbound
  have hrpow : r ≤ 2 ^ m := by exact_mod_cast hrreal
  exact ⟨hrpow, projectedPhase_fails_for_unobserved_refinement
    hs hm0 (Fin.append u v) huv r hrpow⟩

/-- The aligned logical selector underlying T80, before its executable SCC
certificate and interval-containment data are added. Its quantifier order is
fixed refinement, affine constants, parent length, common depth, every parent,
and one descendant. -/
def AlignedProjectedPhaseSelectorHypothesis : Prop :=
  ∃ s : ℕ, 0 < s ∧ ∃ L C : ℝ, 0 ≤ L ∧
    ∀ m : ℕ, ∀ hm : 0 < m,
      ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
        ∀ u : Word m,
          ∃ v : Word s,
            Graph.GlobalPrimitivePhaseCriterion
              (carryKMPGraph
                (wordList (appendWord u v)) (appendWord_nonempty hm u v) R)
              coordinateZeroProjection

theorem alignedProjectedPhaseSelectorHypothesis_iff_quantifiers :
    AlignedProjectedPhaseSelectorHypothesis ↔
      ∃ s : ℕ, 0 < s ∧ ∃ L C : ℝ, 0 ≤ L ∧
        ∀ m : ℕ, ∀ hm : 0 < m,
          ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
            ∀ u : Word m,
              ∃ v : Word s,
                Graph.GlobalPrimitivePhaseCriterion
                  (carryKMPGraph
                    (wordList (appendWord u v))
                      (appendWord_nonempty hm u v) R)
                  coordinateZeroProjection := by
  rfl

/-- Expanded negated selector quantifiers. A single aligned parent defeats
every affine-bounded common depth and every one of its descendants. -/
theorem not_alignedProjectedPhaseSelectorHypothesis_quantifiers :
    ∀ s : ℕ, 0 < s → ∀ L C : ℝ, 0 ≤ L →
      ∃ m : ℕ, ∃ hm : 0 < m, ∃ u : Word m,
        ∀ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C →
          ∀ v : Word s,
            ¬ Graph.GlobalPrimitivePhaseCriterion
              (carryKMPGraph
                (wordList (appendWord u v)) (appendWord_nonempty hm u v) R)
              coordinateZeroProjection := by
  intro s _hspos L C hL
  obtain ⟨M, _hM, _hsM, hlarge⟩ := sufficiently_large_aligned_obstruction s L C hL
  obtain ⟨hm, u, _hbound, _hcard, _hobs, _hlt, _hdescCard, _hirr, hdesc⟩ :=
    hlarge M le_rfl
  refine ⟨M, hm, u, ?_⟩
  intro R hR v
  have hfail := (hdesc v).2.2.2.2 R hR
  simpa [wordList, appendWord] using hfail.2

/-- Literal negation of the aligned projected-phase selector. -/
theorem not_alignedProjectedPhaseSelectorHypothesis :
    ¬ AlignedProjectedPhaseSelectorHypothesis := by
  rintro ⟨s, hs, L, C, hL, hselector⟩
  obtain ⟨m, hm, u, hbad⟩ :=
    not_alignedProjectedPhaseSelectorHypothesis_quantifiers s hs L C hL
  obtain ⟨R, hR, hparent⟩ := hselector m hm
  obtain ⟨v, hgood⟩ := hparent u
  exact hbad R hR v hgood

/-- Literal negation of T80's stronger fixed-refinement interval selector,
with its common depth, SCC certificate, aligned run, cell containment, and
executable goodness quantifiers used without weakening. -/
theorem not_T80_intervalSelectorHypothesis :
    ¬ IntervalSelectorHypothesis := by
  rintro ⟨s, hs, L, C, hL, hselector⟩
  obtain ⟨m, hm, u, hbad⟩ :=
    not_alignedProjectedPhaseSelectorHypothesis_quantifiers s hs L C hL
  obtain ⟨R, hR, hparent⟩ := hselector m hm
  obtain ⟨v, cert, _hlex, _hcell, hgood⟩ := hparent u
  have hcriterion := goodAtDepth_implies_globalCriterion
    (wordList (appendWord u v)) (appendWord_nonempty hm u v) R cert hgood
  exact hbad R hR v hcriterion

/-- T80's literal quantifier-expanded statement is false. This theorem keeps
the executable SCC certificate, aligned-run membership, parent-cell
containment, and `GoodAtDepth` conjuncts exactly as T80 states them. -/
theorem not_T80_intervalSelectorHypothesis_quantifiers :
    ¬ (∃ s : ℕ, 0 < s ∧ ∃ L C : ℝ, 0 ≤ L ∧
      ∀ m : ℕ, ∀ hm : 0 < m,
        ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
          ∀ u : DecimalWord m,
            ∃ v : DecimalWord s,
              ∃ cert : (carryKMPGraph
                  (wordList (appendWord u v))
                    (appendWord_nonempty hm u v) R).SCCCertificate,
                InLexRun ((wordIndex (wordList u)).val * 10 ^ s) (10 ^ s)
                    (wordIndex (wordList (appendWord u v))) ∧
                  wordCell (wordList (appendWord u v)) ⊆ wordCell (wordList u) ∧
                  GoodAtDepth (wordList (appendWord u v))
                    (appendWord_nonempty hm u v) R cert) := by
  simpa [IntervalSelectorHypothesis] using not_T80_intervalSelectorHypothesis

structure ScopeStatus where
  fixedRefinementAlignedSelectorRefuted : Bool
  T80IntervalSelectorRefuted : Bool
  commonWitnessDependsOnM : Bool
  provesC6 : Bool
  disprovesC6 : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  concernsPi : Bool
  deriving DecidableEq, Repr

def scopeStatus : ScopeStatus where
  fixedRefinementAlignedSelectorRefuted := true
  T80IntervalSelectorRefuted := true
  commonWitnessDependsOnM := true
  provesC6 := false
  disprovesC6 := false
  provesC1 := false
  disprovesC1 := false
  concernsPi := false

/-- Formal scope marker: T81 closes only the fixed-refinement sibling selector
routes. The common square witness may vary with the parent length `m`. -/
theorem exact_scope :
    scopeStatus.fixedRefinementAlignedSelectorRefuted = true ∧
      scopeStatus.T80IntervalSelectorRefuted = true ∧
      scopeStatus.commonWitnessDependsOnM = true ∧
      scopeStatus.provesC6 = false ∧
      scopeStatus.disprovesC6 = false ∧
      scopeStatus.provesC1 = false ∧
      scopeStatus.disprovesC1 = false ∧
      scopeStatus.concernsPi = false := by
  norm_num [scopeStatus]

end DecimalFactorEntropy.T81AlignedSelectorObstruction

#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.descendant_family_card
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.append_descendants_injective
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.refinement_observed_factor_bound
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.exists_aligned_parent_all_descendants_unobserved
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.windowVector_mem_observedPrefixes_at_length
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.squarePoint_mem_unobserved_refinement_Core
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.projectedPhase_fails_for_unobserved_refinement
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.exists_eventual_two_pow_dominates_affine
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.sufficiently_large_aligned_obstruction
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.alignedProjectedPhaseSelectorHypothesis_iff_quantifiers
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.not_alignedProjectedPhaseSelectorHypothesis_quantifiers
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.not_alignedProjectedPhaseSelectorHypothesis
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.not_T80_intervalSelectorHypothesis
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.not_T80_intervalSelectorHypothesis_quantifiers
#print axioms DecimalFactorEntropy.T81AlignedSelectorObstruction.exact_scope
