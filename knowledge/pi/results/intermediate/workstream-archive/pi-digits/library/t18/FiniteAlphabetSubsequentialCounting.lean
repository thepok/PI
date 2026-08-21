import TheoryLib.PiDigits.T7Statements
import Mathlib.Combinatorics.Pigeonhole

/-!
# Finite-alphabet subsequential counting

This file proves a finite-alphabet counting lemma and a conditional
specialization to the decimal digit stream of pi. The condition called `hT14`
is exactly the logarithmic digit-change estimate established in the
source-pinned T14 proof note; that external estimate is not reproved in Lean.

The conclusion is explicitly subsequential: one fixed unequal directed pair
works beyond every threshold. It is not an eventual assertion. It is partial
information related to sibling V3 and proves neither V3 nor canonical V1.
-/

namespace Theory.PiDigits.T18

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An ordered pair of distinct alphabet symbols. -/
abbrev UnequalPair (α : Type*) := {p : α × α // p.1 ≠ p.2}

/-- Positions of changes among the first `N` symbols. -/
def changePositions (s : ℕ → α) (N : ℕ) : Finset ℕ :=
  (Finset.range (N - 1)).filter fun i ↦ s i ≠ s (i + 1)

/-- Number of changes among the first `N` symbols. -/
def changeCount (s : ℕ → α) (N : ℕ) : ℕ :=
  (changePositions s N).card

/-- Number of occurrences of `a` among the first `N` symbols. -/
def occurrenceCount (s : ℕ → α) (a : α) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun i ↦ s i = a).card

/-- Number of occurrences of the directed bigram `(a,b)` wholly contained in
the first `N` symbols. -/
def directedBigramCount (s : ℕ → α) (a b : α) (N : ℕ) : ℕ :=
  ((Finset.range (N - 1)).filter fun i ↦ s i = a ∧ s (i + 1) = b).card

/-- At each prefix, one unequal directed pair receives at least the floor of
the average number of changes. -/
lemma exists_frequent_unequal_pair [Nontrivial α] (s : ℕ → α) (N : ℕ) :
    ∃ a b : α, a ≠ b ∧
      changeCount s N / ((Finset.univ : Finset α).offDiag.card) ≤
        directedBigramCount s a b N := by
  classical
  let changes := changePositions s N
  let pairs := (Finset.univ : Finset α).offDiag
  let edge : ℕ → α × α := fun i ↦ (s i, s (i + 1))
  have hpairs : pairs.Nonempty := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    exact ⟨(a, b), by simp [pairs, hab]⟩
  have hmaps : ∀ i ∈ changes, edge i ∈ pairs := by
    intro i hi
    simp only [changes, changePositions, Finset.mem_filter,
      Finset.mem_range] at hi
    simp [edge, pairs, hi.2]
  obtain ⟨p, hp, havg⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := edge) (s := changes) (t := pairs) hmaps hpairs
      (Nat.mul_div_le changes.card pairs.card)
  have hpne : p.1 ≠ p.2 := by
    simpa [pairs] using hp
  refine ⟨p.1, p.2, hpne, ?_⟩
  have hfiber :
      (changes.filter fun i ↦ edge i = p).card =
        directedBigramCount s p.1 p.2 N := by
    congr 1
    ext i
    simp only [changes, changePositions, edge,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hi, _⟩, hedge⟩
      exact ⟨hi, congrArg Prod.fst hedge, congrArg Prod.snd hedge⟩
    · rintro ⟨hi, hia, hib⟩
      refine ⟨⟨hi, ?_⟩, Prod.ext hia hib⟩
      intro heq
      apply hpne
      exact hia.symm.trans (heq.trans hib)
  simpa [changeCount, changes, pairs] using havg.trans_eq hfiber

/-- Subtype-packaged form of `exists_frequent_unequal_pair`. -/
lemma exists_frequent_pair [Nontrivial α] (s : ℕ → α) (N : ℕ) :
    ∃ p : UnequalPair α,
      changeCount s N / ((Finset.univ : Finset α).offDiag.card) ≤
        directedBigramCount s p.1.1 p.1.2 N := by
  obtain ⟨a, b, hab, hcount⟩ := exists_frequent_unequal_pair s N
  exact ⟨⟨(a, b), hab⟩, hcount⟩

/-- A chosen pair receiving at least the floor-average number of changes. -/
noncomputable def frequentPair [Nontrivial α] (s : ℕ → α) (N : ℕ) :
    UnequalPair α :=
  Classical.choose (exists_frequent_pair s N)

lemma frequentPair_spec [Nontrivial α] (s : ℕ → α) (N : ℕ) :
    changeCount s N / ((Finset.univ : Finset α).offDiag.card) ≤
      directedBigramCount s (frequentPair s N).1.1
        (frequentPair s N).1.2 N :=
  Classical.choose_spec (exists_frequent_pair s N)

omit [Fintype α] in
/-- Each directed `(a,b)` bigram contributes a distinct occurrence of `a`. -/
lemma directedBigramCount_le_occurrenceCount_left
    (s : ℕ → α) (a b : α) (N : ℕ) :
    directedBigramCount s a b N ≤ occurrenceCount s a N := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hi.2.1⟩

omit [Fintype α] in
/-- Each directed `(a,b)` bigram contributes a distinct occurrence of `b`. -/
lemma directedBigramCount_le_occurrenceCount_right
    (s : ℕ → α) (a b : α) (N : ℕ) :
    directedBigramCount s a b N ≤ occurrenceCount s b N := by
  change
    ((Finset.range (N - 1)).filter fun i ↦ s i = a ∧ s (i + 1) = b).card ≤
      ((Finset.range N).filter fun i ↦ s i = b).card
  apply Finset.card_le_card_of_injOn (fun i ↦ i + 1)
  · intro i hi
    change i ∈
      (Finset.range (N - 1)).filter (fun j ↦ s j = a ∧ s (j + 1) = b) at hi
    change i + 1 ∈ (Finset.range N).filter (fun j ↦ s j = b)
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, hi.2.2⟩
  · intro i hi j hj hij
    exact Nat.add_right_cancel hij

/-- One fixed unequal directed pair receives the floor-average number of
changes along an unbounded set of prefix lengths. Both endpoint symbols occur
at least as often on those prefixes. The quantifier is `∀ B, ∃ N ≥ B`, not an
eventual claim about all `N`. -/
theorem exists_fixed_pair_on_unbounded_prefixes [Nontrivial α] (s : ℕ → α) :
    ∃ a b : α, a ≠ b ∧ ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧
      changeCount s N / ((Finset.univ : Finset α).offDiag.card) ≤
        directedBigramCount s a b N ∧
      directedBigramCount s a b N ≤ occurrenceCount s a N ∧
      directedBigramCount s a b N ≤ occurrenceCount s b N := by
  let winner : ℕ → UnequalPair α := frequentPair s
  obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber winner
  have hinfinite : Set.Infinite (winner ⁻¹' {p}) :=
    Set.infinite_coe_iff.mp hp
  refine ⟨p.1.1, p.1.2, p.2, fun B ↦ ?_⟩
  obtain ⟨N, hNmem, hNB⟩ := hinfinite.exists_gt B
  have hwinner : winner N = p := by simpa using hNmem
  refine ⟨N, hNB.le, ?_,
    directedBigramCount_le_occurrenceCount_left s p.1.1 p.1.2 N,
    directedBigramCount_le_occurrenceCount_right s p.1.1 p.1.2 N⟩
  simpa [winner, hwinner] using frequentPair_spec s N

/-- Taking a natural-number quotient loses less than one after casting to the
reals. -/
lemma natCast_div_lower (n q : ℕ) (hq : 0 < q) :
    (n : ℝ) / (q : ℝ) - 1 < ((n / q : ℕ) : ℝ) := by
  have hnat : n < q * (n / q + 1) := Nat.lt_mul_div_succ n hq
  have hreal : (n : ℝ) < (q : ℝ) * ((n / q : ℕ) + 1) := by
    exact_mod_cast hnat
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hquot : (n : ℝ) / (q : ℝ) < ((n / q : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hqreal).2
    simpa [mul_comm] using hreal
  linarith

/-- Conditional pi specialization of the finite-alphabet theorem. The
hypothesis is T14's explicit bound with `c = 1 / log 8`, `N₀ = 1`, and its
additive constant `C14`. The explicit positive output coefficient is
`(1 / log 8) / 90`; the output additive constant is `C14 / 90 + 1`.

The same fixed unequal pair works along an unbounded set of prefix lengths for
the directed-bigram count and for both endpoint digit counts. This is not an
eventual fixed-pair claim. -/
theorem pi_fixed_pair_log_lower_bound_of_T14 (C14 : ℝ)
    (hT14 : ∀ N : ℕ, 1 ≤ N →
      (1 / Real.log 8) * Real.log N - C14 ≤
        (changeCount Theory.PiDigits.piDigit N : ℝ)) :
    ∃ a b : Fin 10, a ≠ b ∧ 0 < (1 / Real.log 8) / 90 ∧
      ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) ≤
          (directedBigramCount Theory.PiDigits.piDigit a b N : ℝ) ∧
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) ≤
          (occurrenceCount Theory.PiDigits.piDigit a N : ℝ) ∧
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) ≤
          (occurrenceCount Theory.PiDigits.piDigit b N : ℝ) := by
  obtain ⟨a, b, hab, hpairs⟩ :=
    exists_fixed_pair_on_unbounded_prefixes Theory.PiDigits.piDigit
  refine ⟨a, b, hab, ?_, fun B ↦ ?_⟩
  · exact div_pos (one_div_pos.mpr (Real.log_pos (by norm_num))) (by norm_num)
  · obtain ⟨N, hBN, hfloor, hleft, hright⟩ := hpairs (max B 1)
    have hNpos : 1 ≤ N := (le_max_right B 1).trans hBN
    have hfloor' :
        changeCount Theory.PiDigits.piDigit N / 90 ≤
          directedBigramCount Theory.PiDigits.piDigit a b N := by
      norm_num [Finset.offDiag_card] at hfloor ⊢
      exact hfloor
    have hscaled :
        ((1 / Real.log 8) * Real.log N - C14) / 90 ≤
          (changeCount Theory.PiDigits.piDigit N : ℝ) / 90 := by
      exact (div_le_div_iff_of_pos_right (by norm_num)).2 (hT14 N hNpos)
    have hlower :
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) ≤
          (directedBigramCount Theory.PiDigits.piDigit a b N : ℝ) := by
      calc
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) =
            ((1 / Real.log 8) * Real.log N - C14) / 90 - 1 := by ring
        _ ≤ (changeCount Theory.PiDigits.piDigit N : ℝ) / 90 - 1 :=
          sub_le_sub_right hscaled 1
        _ ≤ ((changeCount Theory.PiDigits.piDigit N / 90 : ℕ) : ℝ) :=
          (natCast_div_lower _ 90 (by norm_num)).le
        _ ≤ (directedBigramCount Theory.PiDigits.piDigit a b N : ℝ) := by
          exact_mod_cast hfloor'
    refine ⟨N, (le_max_left B 1).trans hBN, hlower,
      hlower.trans ?_, hlower.trans ?_⟩
    · exact_mod_cast hleft
    · exact_mod_cast hright

#print axioms Theory.PiDigits.T18.exists_frequent_unequal_pair
#print axioms Theory.PiDigits.T18.exists_fixed_pair_on_unbounded_prefixes
#print axioms Theory.PiDigits.T18.pi_fixed_pair_log_lower_bound_of_T14

end Theory.PiDigits.T18
