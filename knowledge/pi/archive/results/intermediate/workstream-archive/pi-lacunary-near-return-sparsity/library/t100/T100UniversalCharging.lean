import TheoryLib.PiLacunaryNearReturnSparsity.T83T83LiteralStatisticAudit
import TheoryLib.PiLacunaryNearReturnSparsity.T92T92ConstantRunDiscriminator
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# T100: universal exact-word charging

This file formalizes only the arbitrary finite-word sibling isolated in the
T95 note. It makes no claim about `Real.pi`, T56/C7, C1, or C2.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T100UniversalCharging

open DecimalFactorComplexity

/-- The prescribed number of block starts, with natural-number division. -/
def sampleLength (b n : ℕ) : ℕ := b ^ (n / 2)

/-- A finite word has enough symbols for all `L = b^(n/2)` length-`n` blocks. -/
def LegalWordLength (b n wordLength : ℕ) : Prop :=
  sampleLength b n + n - 1 ≤ wordLength

/-- Extend a finite word after its endpoint. Legal block starts never inspect
the extension, as recorded by `finiteBlock_eq` below. -/
def extendFiniteWord {b wordLength : ℕ} (hb : 1 ≤ b)
    (x : Fin wordLength → Fin b) : Stream (Fin b) :=
  fun i => if hi : i < wordLength then x ⟨i, hi⟩ else ⟨0, hb⟩

/-- The length-`n` block at a natural start in the extended finite word. -/
def finiteBlock {b wordLength : ℕ} (hb : 1 ≤ b)
    (x : Fin wordLength → Fin b) (n i : ℕ) : Block (Fin b) n :=
  blockAt (extendFiniteWord hb x) n i

/-- Every coordinate of a legal block is read before the finite endpoint. -/
theorem finiteBlock_apply {b n wordLength : ℕ} (hb : 1 ≤ b)
    (x : Fin wordLength → Fin b) (hlegal : LegalWordLength b n wordLength)
    {i : ℕ} (hi : i < sampleLength b n) (t : Fin n) :
    finiteBlock hb x n i t = x ⟨i + t, by
      unfold LegalWordLength at hlegal
      have ht : t.val < n := t.isLt
      omega⟩ := by
  unfold finiteBlock blockAt extendFiniteWord
  rw [dif_pos]

/-- Starts carrying a fixed length-`n` block label. -/
def occurrenceStarts {b : ℕ} (y : Stream (Fin b)) (n L : ℕ)
    (u : Block (Fin b) n) : Finset ℕ :=
  (Finset.range L).filter fun i => blockAt y n i = u

/-- Ordered off-diagonal equal-block pairs at strict positive lag below `n`.
The use of `offDiag` records both orientations and excludes the diagonal. -/
def shortPairsFor {b : ℕ} (y : Stream (Fin b)) (n L : ℕ)
    (u : Block (Fin b) n) : ℕ :=
  ∑ i ∈ occurrenceStarts y n L u,
    ((occurrenceStarts y n L u).filter fun j =>
      j ≠ i ∧ Nat.dist i j < n).card

/-- Ordered off-diagonal equal-block pairs at lag at least `n`; in particular,
lag exactly `n` is remote. -/
def remotePairsFor {b : ℕ} (y : Stream (Fin b)) (n L : ℕ)
    (u : Block (Fin b) n) : ℕ :=
  ∑ i ∈ occurrenceStarts y n L u,
    ((occurrenceStarts y n L u).filter fun j =>
      j ≠ i ∧ n ≤ Nat.dist i j).card

/-- The block labels that actually occur at one of the `L` starts. -/
def occurringBlocks {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    Finset (Block (Fin b) n) :=
  (Finset.range L).image (blockAt y n)

/-- Total ordered off-diagonal strict-short count. -/
def exactShortPairCount {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) : ℕ :=
  ∑ u ∈ occurringBlocks y n L, shortPairsFor y n L u

/-- Total ordered off-diagonal remote count, including lag `n`. -/
def exactRemotePairCount {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) : ℕ :=
  ∑ u ∈ occurringBlocks y n L, remotePairsFor y n L u

/-- The finite-word strict-short statistic with exactly `b^(n/2)` starts. -/
def finiteExactShortPairCount {b wordLength : ℕ} (hb : 1 ≤ b)
    (x : Fin wordLength → Fin b) (n : ℕ) : ℕ :=
  exactShortPairCount (extendFiniteWord hb x) n (sampleLength b n)

/-- The finite-word remote statistic with exactly `b^(n/2)` starts. -/
def finiteExactRemotePairCount {b wordLength : ℕ} (hb : 1 ≤ b)
    (x : Fin wordLength → Fin b) (n : ℕ) : ℕ :=
  exactRemotePairCount (extendFiniteWord hb x) n (sampleLength b n)

/-- The strict and remote predicates partition every ordered off-diagonal
pair carrying a fixed label. -/
theorem shortPairsFor_add_remotePairsFor {b : ℕ} (y : Stream (Fin b))
    (n L : ℕ) (u : Block (Fin b) n) :
    shortPairsFor y n L u + remotePairsFor y n L u =
      (occurrenceStarts y n L u).card *
        ((occurrenceStarts y n L u).card - 1) := by
  classical
  let A := occurrenceStarts y n L u
  have hpoint (i : ℕ) (hi : i ∈ A) :
      (A.filter fun j => j ≠ i ∧ Nat.dist i j < n).card +
          (A.filter fun j => j ≠ i ∧ n ≤ Nat.dist i j).card =
        A.card - 1 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := A.filter fun j => j ≠ i)
      (p := fun j => Nat.dist i j < n)
    have herase : (A.filter fun j => j ≠ i).card = A.card - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem hi]
    simpa only [Finset.filter_filter, and_assoc, not_lt, herase] using hpartition
  unfold shortPairsFor remotePairsFor
  change (∑ i ∈ A, _) + (∑ i ∈ A, _) = _
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i ∈ A,
        ((A.filter fun j => j ≠ i ∧ Nat.dist i j < n).card +
          (A.filter fun j => j ≠ i ∧ n ≤ Nat.dist i j).card)) =
        ∑ _i ∈ A, (A.card - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i hi
    _ = A.card * (A.card - 1) := by simp

/-- An occurring label has at least one start. -/
theorem occurrenceStarts_nonempty_of_mem_occurringBlocks {b : ℕ}
    (y : Stream (Fin b)) (n L : ℕ) {u : Block (Fin b) n}
    (hu : u ∈ occurringBlocks y n L) :
    (occurrenceStarts y n L u).Nonempty := by
  classical
  rw [occurringBlocks, Finset.mem_image] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  refine ⟨i, ?_⟩
  simp [occurrenceStarts, hi]

/-- The number of labels represented among `L` starts is at most `L`. -/
theorem occurringBlocks_card_le {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    (occurringBlocks y n L).card ≤ L := by
  classical
  calc
    (occurringBlocks y n L).card ≤ (Finset.range L).card := by
      exact Finset.card_image_le
    _ = L := Finset.card_range L

/-- The real algebraic charging step for one block label. -/
theorem local_charging_of_short_bound
    {s r m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    (hpartition : s + r = m * (m - 1))
    (hshort : s ≤ 2 * m * (q - 1)) :
    (2 : ℝ) * s ≤ 3 * r + (25 / 3 : ℝ) * q ^ 2 := by
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]
    norm_num
  have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq]
    norm_num
  have hpartition' : (s : ℝ) + r = m * ((m : ℝ) - 1) := by
    exact_mod_cast hpartition
  have hshort' : (s : ℝ) ≤ 2 * m * ((q : ℝ) - 1) := by
    exact_mod_cast hshort
  have hsquare : 0 ≤ ((5 : ℝ) * q - 3 * m) ^ 2 := sq_nonneg _
  nlinarith

/-- A finite `p`-separated set in an interval of `n` consecutive naturals has
at most `1 + floor((n-1)/p)` elements. -/
theorem card_le_one_add_div_of_separated
    (A : Finset ℕ) {a n p : ℕ} (hp : 0 < p)
    (hwindow : ∀ i ∈ A, a ≤ i ∧ i < a + n)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → p ≤ Nat.dist i j) :
    A.card ≤ 1 + (n - 1) / p := by
  let f : ℕ → ℕ := fun i => (i - a) / p
  have hmaps : Set.MapsTo f (A : Set ℕ)
      (Finset.range (1 + (n - 1) / p) : Set ℕ) := by
    intro i hi
    rw [Finset.coe_range, Set.mem_Iio]
    have hiwindow := hwindow i hi
    have hisub : i - a ≤ n - 1 := by omega
    have hdiv : (i - a) / p ≤ (n - 1) / p := Nat.div_le_div_right hisub
    simpa [f, Nat.succ_eq_add_one, add_comm] using Nat.lt_succ_of_le hdiv
  have hinj : Set.InjOn f (A : Set ℕ) := by
    intro i hi j hj hf
    by_contra hne
    have hsepij := hsep i hi j hj hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hdist : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le hij.le
      have hia := (hwindow i hi).1
      have hja := (hwindow j hj).1
      have himod := Nat.mod_lt (i - a) hp
      have hjmod := Nat.mod_lt (j - a) hp
      have hieq := Nat.mod_add_div (i - a) p
      have hjeq := Nat.mod_add_div (j - a) p
      dsimp [f] at hf
      have hmul : p * ((i - a) / p) = p * ((j - a) / p) :=
        congrArg (fun q => p * q) hf
      rw [hdist] at hsepij
      omega
    · have hdist : Nat.dist i j = i - j := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji.le]
      have hia := (hwindow i hi).1
      have hja := (hwindow j hj).1
      have himod := Nat.mod_lt (i - a) hp
      have hjmod := Nat.mod_lt (j - a) hp
      have hieq := Nat.mod_add_div (i - a) p
      have hjeq := Nat.mod_add_div (j - a) p
      dsimp [f] at hf
      have hmul : p * ((i - a) / p) = p * ((j - a) / p) :=
        congrArg (fun q => p * q) hf
      rw [hdist] at hsepij
      omega
  calc
    A.card ≤ (Finset.range (1 + (n - 1) / p)).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = 1 + (n - 1) / p := Finset.card_range _

/-- A positive period of a fixed-length block, allowing the vacuous period
equal to its length. -/
def IsBlockPeriod {b n : ℕ} (u : Block (Fin b) n) (p : ℕ) : Prop :=
  0 < p ∧ p ≤ n ∧
    ∀ t : ℕ, ∀ ht : t + p < n,
      u ⟨t, Nat.lt_of_le_of_lt (Nat.le_add_right t p) ht⟩ = u ⟨t + p, ht⟩

theorem isBlockPeriod_length {b n : ℕ} (u : Block (Fin b) n) (hn : 0 < n) :
    IsBlockPeriod u n := by
  refine ⟨hn, le_rfl, ?_⟩
  intro t ht
  omega

/-- The least positive period. -/
def leastBlockPeriod {b n : ℕ} (u : Block (Fin b) n) (hn : 0 < n) : ℕ :=
  by
    classical
    exact Nat.find ⟨n, isBlockPeriod_length u hn⟩

theorem leastBlockPeriod_spec {b n : ℕ} (u : Block (Fin b) n) (hn : 0 < n) :
    IsBlockPeriod u (leastBlockPeriod u hn) :=
  by
    classical
    exact Nat.find_spec ⟨n, isBlockPeriod_length u hn⟩

theorem leastBlockPeriod_le {b n : ℕ} (u : Block (Fin b) n) (hn : 0 < n)
    {p : ℕ} (hp : IsBlockPeriod u p) : leastBlockPeriod u hn ≤ p :=
  by
    classical
    exact Nat.find_min' ⟨n, isBlockPeriod_length u hn⟩ hp

/-- Equal overlapping copies force their positive start-distance to be a
period of the common block. -/
theorem overlap_forces_period {b n : ℕ} (y : Stream (Fin b))
    (u : Block (Fin b) n) {i j : ℕ} (hij : i < j)
    (hoverlap : j - i < n) (hi : blockAt y n i = u)
    (hj : blockAt y n j = u) : IsBlockPeriod u (j - i) := by
  have hgap : 0 < j - i := Nat.sub_pos_of_lt hij
  refine ⟨hgap, Nat.le_of_lt hoverlap, ?_⟩
  intro t ht
  have hji : i + (j - i) = j := Nat.add_sub_of_le hij.le
  have heval_i := congrFun hi ⟨t, Nat.lt_of_le_of_lt (Nat.le_add_right t (j - i)) ht⟩
  have heval_j := congrFun hj ⟨t, Nat.lt_of_le_of_lt (Nat.le_add_right t (j - i)) ht⟩
  have heval_i' := congrFun hi ⟨t + (j - i), ht⟩
  simp only [blockAt] at heval_i heval_j heval_i'
  calc
    u ⟨t, Nat.lt_of_le_of_lt (Nat.le_add_right t (j - i)) ht⟩ = y (i + t) := heval_i.symm
    _ = y (j + t) := heval_i.trans heval_j.symm
    _ = y (i + (t + (j - i))) := by congr 1 <;> omega
    _ = u ⟨t + (j - i), ht⟩ := heval_i'

/-- Occurrences of one block label in any interval of `n` starts obey the
least-period occupancy bound. -/
theorem occurrence_window_card_le {b n L a : ℕ} (y : Stream (Fin b))
    (u : Block (Fin b) n) (hn : 0 < n) :
    ((occurrenceStarts y n L u).filter fun i => a ≤ i ∧ i < a + n).card ≤
      1 + (n - 1) / leastBlockPeriod u hn := by
  classical
  let A := (occurrenceStarts y n L u).filter fun i => a ≤ i ∧ i < a + n
  apply card_le_one_add_div_of_separated A (leastBlockPeriod_spec u hn).1
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hne
    have hiOcc := (Finset.mem_filter.mp hi).1
    have hjOcc := (Finset.mem_filter.mp hj).1
    have hiBlock := (Finset.mem_filter.mp hiOcc).2
    have hjBlock := (Finset.mem_filter.mp hjOcc).2
    have hiWindow := (Finset.mem_filter.mp hi).2
    have hjWindow := (Finset.mem_filter.mp hj).2
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hdist : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le hij.le
      have hoverlap : j - i < n := by omega
      rw [hdist]
      exact leastBlockPeriod_le u hn
        (overlap_forces_period y u hij hoverlap hiBlock hjBlock)
    · have hdist : Nat.dist i j = i - j := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji.le]
      have hoverlap : i - j < n := by omega
      rw [hdist]
      exact leastBlockPeriod_le u hn
        (overlap_forces_period y u hji hoverlap hjBlock hiBlock)

/-- At a fixed occurrence, short neighbors on each side fit into one
least-period-controlled window. -/
theorem short_neighbors_card_le {b n L i : ℕ} (y : Stream (Fin b))
    (u : Block (Fin b) n) (hn : 0 < n)
    (hi : i ∈ occurrenceStarts y n L u) :
    ((occurrenceStarts y n L u).filter fun j =>
        j ≠ i ∧ Nat.dist i j < n).card ≤
      2 * ((n - 1) / leastBlockPeriod u hn) := by
  classical
  let A := occurrenceStarts y n L u
  let left := A.filter fun j => j < i ∧ Nat.dist i j < n
  let right := A.filter fun j => i < j ∧ Nat.dist i j < n
  let p := leastBlockPeriod u hn
  let d := (n - 1) / p
  have hleft : left.card ≤ d := by
    let a := i + 1 - n
    let W := A.filter fun j => a ≤ j ∧ j < a + n
    have hsubset : insert i left ⊆ W := by
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with hjEq | hj
      · subst j
        have hia : a ≤ i := by dsimp [a]; omega
        have hib : i < a + n := by dsimp [a]; omega
        exact Finset.mem_filter.mpr ⟨hi, hia, hib⟩
      · have hjA := (Finset.mem_filter.mp hj).1
        have hjlt := (Finset.mem_filter.mp hj).2.1
        have hjdist := (Finset.mem_filter.mp hj).2.2
        have hdist : Nat.dist i j = i - j := by
          rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hjlt.le]
        have hja : a ≤ j := by dsimp [a]; rw [hdist] at hjdist; omega
        have hjb : j < a + n := by dsimp [a]; omega
        exact Finset.mem_filter.mpr ⟨hjA, hja, hjb⟩
    have hnot : i ∉ left := by simp [left]
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hnot] at hcard
    have hW := occurrence_window_card_le (L := L) y u hn (a := a)
    change W.card ≤ 1 + d at hW
    omega
  have hright : right.card ≤ d := by
    let W := A.filter fun j => i ≤ j ∧ j < i + n
    have hsubset : insert i right ⊆ W := by
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with hjEq | hj
      · subst j
        exact Finset.mem_filter.mpr ⟨hi, le_rfl, by omega⟩
      · have hjA := (Finset.mem_filter.mp hj).1
        have hjlt := (Finset.mem_filter.mp hj).2.1
        have hjdist := (Finset.mem_filter.mp hj).2.2
        have hdist : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le hjlt.le
        have hjb : j < i + n := by rw [hdist] at hjdist; omega
        exact Finset.mem_filter.mpr ⟨hjA, hjlt.le, hjb⟩
    have hnot : i ∉ right := by simp [right]
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hnot] at hcard
    have hW := occurrence_window_card_le (L := L) y u hn (a := i)
    change W.card ≤ 1 + d at hW
    omega
  have hneighbors :
      A.filter (fun j => j ≠ i ∧ Nat.dist i j < n) ⊆ left ∪ right := by
    intro j hj
    have hjA := (Finset.mem_filter.mp hj).1
    have hne := (Finset.mem_filter.mp hj).2.1
    have hdist := (Finset.mem_filter.mp hj).2.2
    rcases lt_or_gt_of_ne hne with hji | hij
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjA, hji, hdist⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjA, hij, hdist⟩)
  change (A.filter fun j => j ≠ i ∧ Nat.dist i j < n).card ≤ 2 * d
  calc
    (A.filter fun j => j ≠ i ∧ Nat.dist i j < n).card ≤
        (left ∪ right).card := Finset.card_le_card hneighbors
    _ ≤ left.card + right.card := Finset.card_union_le left right
    _ ≤ d + d := Nat.add_le_add hleft hright
    _ = 2 * d := by omega

/-- The ordered short load of one label is at most twice its multiplicity
times the least-period occupancy excess. -/
theorem shortPairsFor_le_period_bound {b n L : ℕ} (y : Stream (Fin b))
    (u : Block (Fin b) n) (hn : 0 < n) :
    shortPairsFor y n L u ≤
      2 * (occurrenceStarts y n L u).card *
        ((1 + (n - 1) / leastBlockPeriod u hn) - 1) := by
  classical
  unfold shortPairsFor
  calc
    (∑ i ∈ occurrenceStarts y n L u,
        ((occurrenceStarts y n L u).filter fun j =>
          j ≠ i ∧ Nat.dist i j < n).card) ≤
        ∑ _i ∈ occurrenceStarts y n L u,
          2 * ((n - 1) / leastBlockPeriod u hn) := by
      apply Finset.sum_le_sum
      intro i hi
      exact short_neighbors_card_le y u hn hi
    _ = 2 * (occurrenceStarts y n L u).card *
        ((1 + (n - 1) / leastBlockPeriod u hn) - 1) := by
      simp
      ac_rfl

/-- Restrict a length-`n` block to its first `p ≤ n` symbols. -/
def blockPrefix {b n p : ℕ} (hp : p ≤ n) (u : Block (Fin b) n) :
    Fin p → Fin b :=
  fun t => u ⟨t, t.isLt.trans_le hp⟩

/-- A positive period and the first `p` symbols determine the whole block. -/
theorem eq_of_isBlockPeriod_of_blockPrefix_eq {b n p : ℕ}
    {u v : Block (Fin b) n} (hu : IsBlockPeriod u p)
    (hv : IsBlockPeriod v p)
    (hprefix : blockPrefix hu.2.1 u = blockPrefix hv.2.1 v) : u = v := by
  funext t
  have hrec : ∀ q : ℕ, ∀ hq : q < n,
      u ⟨q, hq⟩ = v ⟨q, hq⟩ := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hq
        by_cases hqp : q < p
        · have heval := congrFun hprefix ⟨q, hqp⟩
          exact heval
        · have hpq : p ≤ q := Nat.le_of_not_gt hqp
          have hq0 : 0 < q := hu.1.trans_le hpq
          have hsub : q - p < q := Nat.sub_lt hq0 hu.1
          have hsubn : q - p < n := hsub.trans hq
          have hstep : q - p + p = q := Nat.sub_add_cancel hpq
          have huStep := hu.2.2 (q - p) (by omega)
          have hvStep := hv.2.2 (q - p) (by omega)
          calc
            u ⟨q, hq⟩ = u ⟨q - p, hsubn⟩ := by
              simpa only [hstep] using huStep.symm
            _ = v ⟨q - p, hsubn⟩ := ih (q - p) hsub hsubn
            _ = v ⟨q, hq⟩ := by
              simpa only [hstep] using hvStep
  exact hrec t t.isLt

/-- All length-`n` blocks having positive period `p`. -/
def periodicBlocks (b n p : ℕ) : Finset (Block (Fin b) n) := by
  classical
  exact (Finset.univ : Finset (Block (Fin b) n)).filter fun u =>
    IsBlockPeriod u p

/-- At most `b^p` length-`n` blocks have a specified positive period `p`. -/
theorem periodicBlocks_card_le {b n p : ℕ} (hp0 : 0 < p) (hpn : p ≤ n) :
    (periodicBlocks b n p).card ≤ b ^ p := by
  classical
  let P := periodicBlocks b n p
  let f : Block (Fin b) n → (Fin p → Fin b) := blockPrefix hpn
  have hmaps : Set.MapsTo f (P : Set (Block (Fin b) n))
      (Finset.univ : Finset (Fin p → Fin b)) := by
    intro u hu
    simp
  have hinj : Set.InjOn f (P : Set (Block (Fin b) n)) := by
    intro u hu v hv huv
    have huPeriod : IsBlockPeriod u p := by
      simpa [P, periodicBlocks] using (Finset.mem_filter.mp hu).2
    have hvPeriod : IsBlockPeriod v p := by
      simpa [P, periodicBlocks] using (Finset.mem_filter.mp hv).2
    exact eq_of_isBlockPeriod_of_blockPrefix_eq huPeriod hvPeriod huv
  calc
    P.card ≤ (Finset.univ : Finset (Fin p → Fin b)).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = b ^ p := by simp

/-- Any collection of labels having least period exactly `p` has cardinality
at most `b^p`. -/
theorem leastPeriodClass_card_le {b n L p : ℕ} (y : Stream (Fin b))
    (hn : 0 < n) (hp0 : 0 < p) (hpn : p ≤ n) :
    ((occurringBlocks y n L).filter fun u => leastBlockPeriod u hn = p).card ≤
      b ^ p := by
  classical
  calc
    ((occurringBlocks y n L).filter fun u => leastBlockPeriod u hn = p).card ≤
        (periodicBlocks b n p).card := by
      apply Finset.card_le_card
      intro u hu
      have hperiod := leastBlockPeriod_spec u hn
      have heq := (Finset.mem_filter.mp hu).2
      simp only [periodicBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
      exact heq ▸ hperiod
    _ ≤ b ^ p := periodicBlocks_card_le hp0 hpn

/-- Closed form for the square-weighted geometric series used in T95's
period-class count. -/
theorem hasSum_succ_sq_geometric {z : ℝ} (hz : |z| < 1) :
    HasSum (fun d : ℕ => ((d + 1 : ℕ) : ℝ) ^ 2 * z ^ d)
      ((1 + z) / (1 - z) ^ 3) := by
  have hz' : ‖z‖ < 1 := by simpa [Real.norm_eq_abs]
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hz'
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hz'
  have h := (h2.mul_left 2).sub h1
  convert h using 1
  · funext d
    norm_num [Nat.cast_choose_two]
    ring
  · have hne : 1 - z ≠ 0 := by
      have : z < 1 := lt_of_abs_lt hz
      linarith
    field_simp
    ring

/-- T95's finite period sum is bounded by its explicit infinite geometric
majorant. -/
theorem weighted_period_sum_le (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) :
    (∑ p ∈ Finset.Icc 1 k,
      (b : ℝ) ^ p * (((k : ℝ) / p) ^ 2)) ≤
      (b : ℝ) ^ k *
        (((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3) := by
  let B : ℝ := b
  let z : ℝ := 1 / B
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast (show 0 < b by omega)
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hz0 : 0 ≤ z := by positivity
  have hz1 : |z| < 1 := by
    rw [abs_of_nonneg hz0]
    dsimp [z]
    exact (div_lt_one hB).2 (by
      dsimp [B]
      exact_mod_cast hb)
  have hseries := hasSum_succ_sq_geometric hz1
  have hprefix :
      (∑ d ∈ Finset.range k, ((d + 1 : ℕ) : ℝ) ^ 2 * z ^ d) ≤
        (1 + z) / (1 - z) ^ 3 := by
    exact sum_le_hasSum (Finset.range k)
      (fun d _ => mul_nonneg (sq_nonneg _) (pow_nonneg hz0 _)) hseries
  have hreindex :
      (∑ p ∈ Finset.Icc 1 k,
          (((k - p + 1 : ℕ) : ℝ) ^ 2 * z ^ (k - p))) =
        ∑ d ∈ Finset.range k, (((d + 1 : ℕ) : ℝ) ^ 2 * z ^ d) := by
    apply Finset.sum_bij (fun p _ => k - p)
    · intro p hp
      rw [Finset.mem_range]
      have := (Finset.mem_Icc.mp hp).1
      omega
    · intro p₁ hp₁ p₂ hp₂ heq
      have h₁ := (Finset.mem_Icc.mp hp₁).2
      have h₂ := (Finset.mem_Icc.mp hp₂).2
      omega
    · intro d hd
      rw [Finset.mem_range] at hd
      refine ⟨k - d, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro p hp
      rfl
  have hterm (p : ℕ) (hp : p ∈ Finset.Icc 1 k) :
      B ^ p * (((k : ℝ) / p) ^ 2) ≤
        B ^ k * (((k - p + 1 : ℕ) : ℝ) ^ 2 * z ^ (k - p)) := by
    have hp1 := (Finset.mem_Icc.mp hp).1
    have hpk := (Finset.mem_Icc.mp hp).2
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp1
    have hratio : (k : ℝ) / p ≤ (k - p + 1 : ℕ) := by
      rw [div_le_iff₀ hpR]
      rw [Nat.cast_add, Nat.cast_sub hpk]
      push_cast
      have hpkR : (p : ℝ) ≤ k := by exact_mod_cast hpk
      have hp1R : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      have hkpR : (0 : ℝ) ≤ (k : ℝ) - p := sub_nonneg.mpr hpkR
      have hponeR : (0 : ℝ) ≤ (p : ℝ) - 1 := sub_nonneg.mpr hp1R
      nlinarith [mul_nonneg hkpR hponeR]
    have hratio0 : 0 ≤ (k : ℝ) / p := by positivity
    have hsq : ((k : ℝ) / p) ^ 2 ≤ ((k - p + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (((k - p + 1 : ℕ) : ℝ) - (k : ℝ) / p)]
    have hpow : B ^ k * z ^ (k - p) = B ^ p := by
      dsimp [z]
      rw [one_div, inv_pow, pow_sub₀ B hB0 hpk]
      field_simp
    calc
      B ^ p * (((k : ℝ) / p) ^ 2) =
          (B ^ k * z ^ (k - p)) * (((k : ℝ) / p) ^ 2) := by rw [hpow]
      _ ≤ (B ^ k * z ^ (k - p)) * (((k - p + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = B ^ k * (((k - p + 1 : ℕ) : ℝ) ^ 2 * z ^ (k - p)) := by ring
  calc
    (∑ p ∈ Finset.Icc 1 k, (b : ℝ) ^ p * (((k : ℝ) / p) ^ 2)) =
        ∑ p ∈ Finset.Icc 1 k, B ^ p * (((k : ℝ) / p) ^ 2) := by rfl
    _ ≤ ∑ p ∈ Finset.Icc 1 k,
        B ^ k * (((k - p + 1 : ℕ) : ℝ) ^ 2 * z ^ (k - p)) := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = B ^ k * (∑ p ∈ Finset.Icc 1 k,
        (((k - p + 1 : ℕ) : ℝ) ^ 2 * z ^ (k - p))) := by
      rw [Finset.mul_sum]
    _ = B ^ k * (∑ d ∈ Finset.range k,
        (((d + 1 : ℕ) : ℝ) ^ 2 * z ^ d)) := by rw [hreindex]
    _ ≤ B ^ k * ((1 + z) / (1 - z) ^ 3) := by gcongr
    _ = (b : ℝ) ^ k *
        (((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3) := by
      dsimp [B, z]
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hb1 : (b : ℝ) - 1 ≠ 0 := by linarith
      field_simp

/-- The occupancy majorant attached to a block's least period. -/
def periodOccupancyBound {b n : ℕ} (u : Block (Fin b) n) (hn : 0 < n) : ℕ :=
  1 + (n - 1) / leastBlockPeriod u hn

/-- Least period above `floor(n/2)` forces occupancy majorant at most two. -/
theorem periodOccupancyBound_le_two_of_half_lt {b n : ℕ}
    (u : Block (Fin b) n) (hn : 0 < n)
    (hlarge : n / 2 < leastBlockPeriod u hn) :
    periodOccupancyBound u hn ≤ 2 := by
  have hp0 := (leastBlockPeriod_spec u hn).1
  have hnupper : n - 1 ≤ 2 * (n / 2) := by omega
  have hlt : n - 1 < 2 * leastBlockPeriod u hn := by omega
  have hdiv : (n - 1) / leastBlockPeriod u hn < 2 :=
    (Nat.div_lt_iff_lt_mul hp0).2 hlt
  unfold periodOccupancyBound
  omega

/-- For period at most `k=floor(n/2)`, the occupancy majorant is at most
`3k/p` in the reals. -/
theorem periodOccupancyBound_le_three_mul_half_div {b n : ℕ}
    (u : Block (Fin b) n) (hn : 0 < n)
    (hsmall : leastBlockPeriod u hn ≤ n / 2) :
    (periodOccupancyBound u hn : ℝ) ≤
      3 * (n / 2 : ℕ) / leastBlockPeriod u hn := by
  let p := leastBlockPeriod u hn
  let k := n / 2
  have hp0 : 0 < p := (leastBlockPeriod_spec u hn).1
  have hpk : p ≤ k := hsmall
  have hk0 : 0 < k := hp0.trans_le hpk
  have hnupper : n - 1 ≤ 2 * k := by dsimp [k]; omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
  have hkR : (p : ℝ) ≤ k := by exact_mod_cast hpk
  have hcastDiv : (((n - 1) / p : ℕ) : ℝ) ≤ (n - 1 : ℕ) / (p : ℝ) :=
    Nat.cast_div_le
  have hnR : ((n - 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hnupper
  have hdiv : (n - 1 : ℕ) / (p : ℝ) ≤ 2 * (k : ℝ) / p := by
    exact div_le_div_of_nonneg_right hnR hpR.le
  have hone : (1 : ℝ) ≤ (k : ℝ) / p := (le_div_iff₀ hpR).2 (by simpa using hkR)
  unfold periodOccupancyBound
  dsimp [p, k] at *
  push_cast
  ring_nf at hcastDiv hdiv hone ⊢
  linarith

/-- Summed squared occupancy bounds over all labels occurring among the
prescribed `b^(n/2)` starts. -/
theorem sum_periodOccupancyBound_sq_le {b n : ℕ} (hb : 2 ≤ b) (hn : 2 ≤ n)
    (y : Stream (Fin b)) :
    (∑ u ∈ occurringBlocks y n (sampleLength b n),
        (periodOccupancyBound u (by omega) : ℝ) ^ 2) ≤
      (4 + 9 * (((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3)) *
        sampleLength b n := by
  classical
  let k := n / 2
  let L := sampleLength b n
  let B := occurringBlocks y n L
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hpoint (u : Block (Fin b) n) (hu : u ∈ B) :
      (periodOccupancyBound u (by omega) : ℝ) ^ 2 ≤
        4 + if leastBlockPeriod u (by omega) ≤ k then
          9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2) else 0 := by
    by_cases hsmall : leastBlockPeriod u (by omega) ≤ k
    · rw [if_pos hsmall]
      have hq := periodOccupancyBound_le_three_mul_half_div u (by omega)
        (by simpa [k] using hsmall)
      have hq0 : (0 : ℝ) ≤ periodOccupancyBound u (by omega) := by positivity
      have hratio0 : (0 : ℝ) ≤ 3 * (k : ℝ) /
          leastBlockPeriod u (by omega) := by positivity
      have hsq : (periodOccupancyBound u (by omega) : ℝ) ^ 2 ≤
          (3 * (k : ℝ) / leastBlockPeriod u (by omega)) ^ 2 :=
        (sq_le_sq₀ hq0 hratio0).2 (by simpa [k] using hq)
      ring_nf at hsq ⊢
      linarith
    · rw [if_neg hsmall, add_zero]
      have hqNat := periodOccupancyBound_le_two_of_half_lt u (by omega)
        (by simpa [k] using Nat.lt_of_not_ge hsmall)
      have hq : (periodOccupancyBound u (by omega) : ℝ) ≤ 2 := by
        exact_mod_cast hqNat
      have hq0 : (0 : ℝ) ≤ periodOccupancyBound u (by omega) := by positivity
      nlinarith [sq_nonneg ((periodOccupancyBound u (by omega) : ℝ) - 2)]
  have hsumPoint :
      (∑ u ∈ B, (periodOccupancyBound u (by omega) : ℝ) ^ 2) ≤
        ∑ u ∈ B, (4 + if leastBlockPeriod u (by omega) ≤ k then
          9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2) else 0) := by
    exact Finset.sum_le_sum fun u hu => hpoint u hu
  let low := B.filter fun u => leastBlockPeriod u (by omega) ≤ k
  have hlowIdentity :
      (∑ u ∈ B, (if leastBlockPeriod u (by omega) ≤ k then
          9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2) else 0)) =
        ∑ u ∈ low, 9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2) := by
    simp [low, Finset.sum_filter]
  have hmaps : ∀ u ∈ low,
      leastBlockPeriod u (by omega) ∈ Finset.Icc 1 k := by
    intro u hu
    have hsmall := (Finset.mem_filter.mp hu).2
    exact Finset.mem_Icc.mpr ⟨(leastBlockPeriod_spec u (by omega)).1, hsmall⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun u : Block (Fin b) n =>
      9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2))
  have hlow :
      (∑ u ∈ low, 9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2)) ≤
        9 * (∑ p ∈ Finset.Icc 1 k,
          (b : ℝ) ^ p * (((k : ℝ) / p) ^ 2)) := by
    rw [← hfiber]
    calc
      (∑ p ∈ Finset.Icc 1 k,
          ∑ u ∈ low with leastBlockPeriod u (by omega) = p,
            9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2)) ≤
          ∑ p ∈ Finset.Icc 1 k,
            (b : ℝ) ^ p * (9 * (((k : ℝ) / p) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 := (Finset.mem_Icc.mp hp).1
        have hpk := (Finset.mem_Icc.mp hp).2
        let C := low.filter fun u => leastBlockPeriod u (by omega) = p
        have hclass : C.card ≤ b ^ p := by
          calc
            C.card ≤ ((occurringBlocks y n L).filter fun u =>
                leastBlockPeriod u (by omega) = p).card := by
              apply Finset.card_le_card
              intro u hu
              have huLow := (Finset.mem_filter.mp hu).1
              have huB := (Finset.mem_filter.mp huLow).1
              exact Finset.mem_filter.mpr ⟨by simpa [B] using huB,
                (Finset.mem_filter.mp hu).2⟩
            _ ≤ b ^ p := leastPeriodClass_card_le y (by omega) hp0
              (hpk.trans (Nat.div_le_self n 2))
        have hclassR : (C.card : ℝ) ≤ b ^ p := by exact_mod_cast hclass
        have hsumClass :
            (∑ u ∈ low with leastBlockPeriod u (by omega) = p,
              9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2)) =
              C.card * (9 * (((k : ℝ) / p) ^ 2)) := by
          change (∑ u ∈ C,
              9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2)) = _
          calc
            (∑ u ∈ C,
                9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2)) =
                ∑ _u ∈ C, 9 * (((k : ℝ) / p) ^ 2) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [(Finset.mem_filter.mp hu).2]
            _ = C.card * (9 * (((k : ℝ) / p) ^ 2)) := by simp
        rw [hsumClass]
        gcongr
      _ = 9 * (∑ p ∈ Finset.Icc 1 k,
          (b : ℝ) ^ p * (((k : ℝ) / p) ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hweighted := weighted_period_sum_le b k hb hk
  have hlabels : (B.card : ℝ) ≤ L := by
    exact_mod_cast (by simpa [B] using occurringBlocks_card_le y n L)
  have hL : (L : ℝ) = (b : ℝ) ^ k := by
    simp [L, sampleLength, k]
  change (∑ u ∈ B, (periodOccupancyBound u (by omega) : ℝ) ^ 2) ≤ _
  calc
    (∑ u ∈ B, (periodOccupancyBound u (by omega) : ℝ) ^ 2) ≤
        ∑ u ∈ B, (4 + if leastBlockPeriod u (by omega) ≤ k then
          9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2) else 0) := hsumPoint
    _ = 4 * B.card +
        (∑ u ∈ B, (if leastBlockPeriod u (by omega) ≤ k then
          9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2) else 0)) := by
      simp [Finset.sum_add_distrib]
      ring
    _ = 4 * B.card +
        (∑ u ∈ low, 9 * (((k : ℝ) / leastBlockPeriod u (by omega)) ^ 2)) := by
      rw [hlowIdentity]
    _ ≤ 4 * L + 9 * (∑ p ∈ Finset.Icc 1 k,
          (b : ℝ) ^ p * (((k : ℝ) / p) ^ 2)) := by gcongr
    _ ≤ 4 * L + 9 * ((b : ℝ) ^ k *
        (((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3)) := by gcongr
    _ = (4 + 9 * (((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3)) * L := by
      rw [hL]
      ring

/-- The explicit finite T95 constant. -/
def chargingConstant (b : ℕ) : ℝ :=
  (25 / 6 : ℝ) *
    (4 + 9 * ((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3)

/-- Universal stream form. The finite-word theorem below is its literal
finite-prefix specialization. -/
theorem universal_stream_charging
    {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∀ y : Stream (Fin b),
      (2 : ℝ) * exactShortPairCount y n (sampleLength b n) ≤
        3 * exactRemotePairCount y n (sampleLength b n) +
          2 * chargingConstant b * sampleLength b n := by
  intro y
  by_cases hn1 : n = 1
  · subst n
    have hB : occurringBlocks y 1 (sampleLength b 1) = {blockAt y 1 0} := by
      ext u
      simp [occurringBlocks, sampleLength]
    have hOcc : occurrenceStarts y 1 (sampleLength b 1) (blockAt y 1 0) = {0} := by
      ext i
      simp only [occurrenceStarts, sampleLength, Nat.reduceDiv, pow_zero,
        Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · intro hi
        omega
      · intro hi
        subst i
        simp
    have hs : shortPairsFor y 1 (sampleLength b 1) (blockAt y 1 0) = 0 := by
      simp [shortPairsFor, hOcc]
    have hr : remotePairsFor y 1 (sampleLength b 1) (blockAt y 1 0) = 0 := by
      simp [remotePairsFor, hOcc]
    have hC : 0 ≤ chargingConstant b := by
      unfold chargingConstant
      have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hbsub : 0 < (b : ℝ) - 1 := by linarith
      have hden : 0 < ((b : ℝ) - 1) ^ 3 := pow_pos hbsub 3
      have hfrac : 0 ≤ ((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3 := by
        exact div_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) hden.le
      have hsum : 0 ≤ 4 + 9 *
          (((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3) := by positivity
      convert mul_nonneg (by norm_num : (0 : ℝ) ≤ 25 / 6) hsum using 1 <;> ring
    unfold exactShortPairCount exactRemotePairCount
    rw [hB]
    simp only [Finset.sum_singleton]
    rw [hs, hr]
    norm_num [sampleLength]
    positivity
  · have hn2 : 2 ≤ n := by omega
    let L := sampleLength b n
    let B := occurringBlocks y n L
    have hlocal (u : Block (Fin b) n) (hu : u ∈ B) :
        (2 : ℝ) * shortPairsFor y n L u ≤
          3 * remotePairsFor y n L u +
            (25 / 3 : ℝ) * (periodOccupancyBound u (by omega) : ℝ) ^ 2 := by
      let m := (occurrenceStarts y n L u).card
      let q := periodOccupancyBound u (by omega)
      have hm : 1 ≤ m := by
        have hnonempty := occurrenceStarts_nonempty_of_mem_occurringBlocks y n L
          (by simpa [B] using hu)
        simpa [m, Finset.one_le_card] using hnonempty
      have hq : 1 ≤ q := by simp [q, periodOccupancyBound]
      have hpartition := shortPairsFor_add_remotePairsFor y n L u
      have hshort := shortPairsFor_le_period_bound y u (by omega) (L := L)
      exact local_charging_of_short_bound hm hq
        (by simpa [m] using hpartition) (by simpa [m, q, periodOccupancyBound] using hshort)
    have hsumLocal :
        (∑ u ∈ B, (2 : ℝ) * shortPairsFor y n L u) ≤
          ∑ u ∈ B, (3 * remotePairsFor y n L u +
            (25 / 3 : ℝ) * (periodOccupancyBound u (by omega) : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun u hu => hlocal u hu
    have hoccupancy := sum_periodOccupancyBound_sq_le hb hn2 y
    change (∑ u ∈ B, (periodOccupancyBound u (by omega) : ℝ) ^ 2) ≤ _ at hoccupancy
    change (2 : ℝ) * (∑ u ∈ B, shortPairsFor y n L u) ≤
      3 * (∑ u ∈ B, remotePairsFor y n L u) +
        2 * chargingConstant b * L
    calc
      (2 : ℝ) * (∑ u ∈ B, shortPairsFor y n L u) =
          ∑ u ∈ B, (2 : ℝ) * shortPairsFor y n L u := by
        push_cast
        rw [Finset.mul_sum]
      _ ≤ ∑ u ∈ B, (3 * remotePairsFor y n L u +
          (25 / 3 : ℝ) * (periodOccupancyBound u (by omega) : ℝ) ^ 2) := hsumLocal
      _ = 3 * (∑ u ∈ B, remotePairsFor y n L u) +
          (25 / 3 : ℝ) *
            (∑ u ∈ B, (periodOccupancyBound u (by omega) : ℝ) ^ 2) := by
        push_cast
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 3 * (∑ u ∈ B, remotePairsFor y n L u) +
          (25 / 3 : ℝ) *
            ((4 + 9 * (((b : ℝ) ^ 2 * (b + 1)) / ((b : ℝ) - 1) ^ 3)) * L) := by
        gcongr
      _ = 3 * (∑ u ∈ B, remotePairsFor y n L u) +
          2 * chargingConstant b * L := by
        unfold chargingConstant
        ring

/-- T100's literal arbitrary-finite-word charging theorem. Every range and
endpoint convention occurs in the definitions in its type. -/
theorem universal_finite_word_charging
    {b n wordLength : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n)
    (x : Fin wordLength → Fin b)
    (hlegal : LegalWordLength b n wordLength) :
    (2 : ℝ) * finiteExactShortPairCount (by omega) x n ≤
      3 * finiteExactRemotePairCount (by omega) x n +
        2 * chargingConstant b * sampleLength b n := by
  have _ := hlegal
  exact universal_stream_charging hb hn (extendFiniteWord (by omega) x)

end DecimalFactorComplexity.T100UniversalCharging

#print axioms DecimalFactorComplexity.T100UniversalCharging.overlap_forces_period
#print axioms DecimalFactorComplexity.T100UniversalCharging.periodicBlocks_card_le
#print axioms DecimalFactorComplexity.T100UniversalCharging.weighted_period_sum_le
#print axioms DecimalFactorComplexity.T100UniversalCharging.sum_periodOccupancyBound_sq_le
#print axioms DecimalFactorComplexity.T100UniversalCharging.universal_stream_charging
#print axioms DecimalFactorComplexity.T100UniversalCharging.universal_finite_word_charging
