import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Factor complexity of one-sided streams

Source: `problems/local/pi-decimal-factor-complexity.txt`
SHA-256: `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`

Positions are zero-based. A factor is a contiguous block beginning at an
arbitrary stream position. The definitions do not include prefixes only,
noncontiguous subsequences, or the integer part of a decimal expansion.

`ComplexityData s` presents the finite type of factors of each length by an
explicit equivalence with `Fin (p n)`. Thus `p n` is certified as the exact
number of distinct factors. `canonicalComplexityData` supplies this data
noncomputably; `morse_hedlund` also accepts explicit data so its constructive
core can be audited separately from that classical presentation step.

The results concern arbitrary streams. They assert nothing about the decimal
digits of pi.
-/

namespace DecimalFactorComplexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An infinite one-sided stream over an alphabet. -/
abbrev Stream (α : Type*) := ℕ → α

/-- A block of length `n`. -/
abbrev Block (α : Type*) (n : ℕ) := Fin n → α

/-- `w` agrees with the contiguous length-`n` block of `s` starting at `i`. -/
def OccursAt (s : Stream α) (w : Block α n) (i : ℕ) : Prop :=
  ∀ j, w j = s (i + j)

instance occursAtDecidable (s : Stream α) (w : Block α n) :
    DecidablePred (OccursAt s w) := fun _ => by
  unfold OccursAt
  infer_instance

/-- `w` occurs contiguously at some position of `s`. -/
def Occurs (s : Stream α) (w : Block α n) : Prop :=
  ∃ i, OccursAt s w i

/-- The set of distinct contiguous length-`n` factors occurring in `s`. -/
def factorSet (s : Stream α) (n : ℕ) : Set (Block α n) :=
  {w | Occurs s w}

/-- The type corresponding to the factor set. -/
def Factor (s : Stream α) (n : ℕ) := {w : Block α n // w ∈ factorSet s n}

/-- The length-`n` block beginning at position `i`. -/
def blockAt (s : Stream α) (n i : ℕ) : Block α n :=
  fun j => s (i + j)

/-- The factor beginning at `i`, carrying its occurrence witness. -/
def factorAt (s : Stream α) (n i : ℕ) : Factor s n :=
  ⟨blockAt s n i, i, fun _ => rfl⟩

/-- Delete the last letter of a block. -/
def initial (w : Block α (n + 1)) : Block α n :=
  fun j => w j.castSucc

/-- Delete the last letter of an occurring factor. -/
def initialFactor (s : Stream α) (n : ℕ) : Factor s (n + 1) → Factor s n :=
  fun w => ⟨initial w.1, by
    obtain ⟨i, hi⟩ := w.2
    exact ⟨i, fun j => hi j.castSucc⟩⟩

lemma initial_factorAt (s : Stream α) (n i : ℕ) :
    initialFactor s n (factorAt s (n + 1) i) = factorAt s n i := by
  rfl

/-- The least position at which an occurring factor appears. -/
def firstOccurrence {s : Stream α} {n : ℕ} (w : Factor s n) : ℕ :=
  Nat.find w.2

lemma firstOccurrence_spec {s : Stream α} {n : ℕ} (w : Factor s n) :
    OccursAt s w.1 (firstOccurrence w) := by
  exact Nat.find_spec w.2

/-- Extend a factor by reading one more stream symbol at its first occurrence. -/
def extendFactor (s : Stream α) (n : ℕ) (w : Factor s n) : Factor s (n + 1) :=
  factorAt s (n + 1) (firstOccurrence w)

lemma initial_extendFactor (s : Stream α) (n : ℕ) (w : Factor s n) :
    initialFactor s n (extendFactor s n w) = w := by
  apply Subtype.ext
  funext j
  exact (firstOccurrence_spec w j).symm

/-- Exact finite presentations of all factor sets, together with the elementary finite
cardinality laws used by Morse--Hedlund. These laws are bundled so the bridge can remain
choice-free; `canonicalComplexityData` below constructs the package for every finite alphabet. -/
structure ComplexityData (s : Stream α) where
  value : ℕ → ℕ
  classify : ∀ n, Factor s n ≃ Fin (value n)
  zero : value 0 = 1
  mono : ∀ n, value n ≤ value (n + 1)
  initial_injective_of_flat : ∀ n, value (n + 1) = value n →
    Function.Injective (initialFactor s n)
  collision : ∀ n, ∃ a b : Fin (value n + 1),
    a ≠ b ∧ factorAt s n a = factorAt s n b

instance factorFinite (s : Stream α) (n : ℕ) : Finite (Factor s n) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- A canonical, noncomputable presentation of factor complexity. Its construction uses
mathlib's permitted classical choice, while the bridge theorems below accept explicit
presentations and therefore do not inherit that dependency. -/
noncomputable def canonicalComplexityData (s : Stream α) : ComplexityData s where
  value n := Nat.card (Factor s n)
  classify n := Finite.equivFin (Factor s n)
  zero := by
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨factorAt s 0 0⟩⟩
  mono n := by
    apply Nat.card_le_card_of_surjective (initialFactor s n)
    intro w
    exact ⟨extendFactor s n w, initial_extendFactor s n w⟩
  initial_injective_of_flat n hflat := by
    have hsurj : Function.Surjective (initialFactor s n) := by
      intro w
      exact ⟨extendFactor s n w, initial_extendFactor s n w⟩
    exact ((Nat.bijective_iff_surjective_and_card (initialFactor s n)).2
      ⟨hsurj, hflat⟩).1
  collision n := by
    let f : Fin (Nat.card (Factor s n) + 1) → Fin (Nat.card (Factor s n)) :=
      fun i => Finite.equivFin (Factor s n) (factorAt s n i)
    obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    exact ⟨a, b, hab, (Finite.equivFin (Factor s n)).injective heq⟩

/-- Factor complexity supplied by an exact finite presentation. -/
def factorComplexity {s : Stream α} (P : ComplexityData s) (n : ℕ) : ℕ :=
  P.value n

/-- Canonical factor complexity: the finite cardinality of the factor set. -/
noncomputable def canonicalFactorComplexity (s : Stream α) (n : ℕ) : ℕ :=
  Nat.card (Factor s n)

@[simp] lemma canonical_factorComplexity (s : Stream α) (n : ℕ) :
    factorComplexity (canonicalComplexityData s) n = canonicalFactorComplexity s n := rfl

/-- Exact factor complexity does not depend on the chosen finite presentation. -/
lemma complexityData_value_eq {s : Stream α} (P Q : ComplexityData s) (n : ℕ) :
    P.value n = Q.value n := by
  have hcard := Fintype.card_congr ((P.classify n).symm.trans (Q.classify n))
  simpa using hcard

/-- A stream is eventually periodic after a finite prefix, with positive period. -/
def EventuallyPeriodic (s : Stream α) : Prop :=
  ∃ start period : ℕ, 0 < period ∧ ∀ i, s (start + i + period) = s (start + i)

/-- A1 (canonical): `p(n) / n` tends to infinity, with every quantifier explicit. -/
def A1 (s : Stream α) (P : ComplexityData s) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → C * (n : ℝ) < (factorComplexity P n : ℝ)

/-- A2: the natural-number excess `p(n) - n` tends to infinity. -/
def A2 (s : Stream α) (P : ComplexityData s) : Prop :=
  ∀ B : ℕ, ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → B ≤ factorComplexity P n - n

/-- A3: `p(n) / n` is unbounded along arbitrarily late lengths. -/
def A3 (s : Stream α) (P : ComplexityData s) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ N : ℕ, ∃ n : ℕ,
    max 1 N ≤ n ∧ C * (n : ℝ) < (factorComplexity P n : ℝ)

/-- A4: the Morse--Hedlund linear baseline at every positive length. -/
def A4 (s : Stream α) (P : ComplexityData s) : Prop :=
  ∀ n : ℕ, 0 < n → n + 1 ≤ factorComplexity P n

/-- A stream is disjunctive when every finite block occurs contiguously. -/
def Disjunctive (s : Stream α) : Prop :=
  ∀ n (w : Block α n), Occurs s w

/-- A5: every positive-length factor set has the full alphabetic cardinality. -/
def A5 (s : Stream α) (P : ComplexityData s) : Prop :=
  ∀ n : ℕ, 0 < n → factorComplexity P n = Fintype.card (Block α n)

lemma factorComplexity_zero (s : Stream α) (P : ComplexityData s) :
    factorComplexity P 0 = 1 := by
  exact P.zero

lemma factorComplexity_mono (s : Stream α) (P : ComplexityData s) (n : ℕ) :
    factorComplexity P n ≤ factorComplexity P (n + 1) := by
  exact P.mono n

lemma exists_flat_step_of_le (p : ℕ → ℕ) (hzero : p 0 = 1)
    (hmono : ∀ n, p n ≤ p (n + 1)) {n : ℕ} (hle : p n ≤ n) :
    ∃ k < n, p k = p (k + 1) := by
  have hmain : ∀ m : ℕ, (∃ k < m, p k = p (k + 1)) ∨ m + 1 ≤ p m := by
    intro m
    induction m with
    | zero =>
        right
        omega
    | succ m ih =>
        rcases ih with hflat | hlower
        · left
          obtain ⟨k, hk, heq⟩ := hflat
          exact ⟨k, by omega, heq⟩
        · by_cases heq : p m = p (m + 1)
          · left
            exact ⟨m, by omega, heq⟩
          · right
            have := hmono m
            omega
  rcases hmain n with hflat | hlower
  · exact hflat
  · omega

lemma initialFactor_injective_of_flat (s : Stream α) (P : ComplexityData s) (n : ℕ)
    (hflat : factorComplexity P (n + 1) = factorComplexity P n) :
    Function.Injective (initialFactor s n) := by
  exact P.initial_injective_of_flat n hflat

lemma next_letter_eq_of_flat (s : Stream α) (P : ComplexityData s) (n : ℕ)
    (hflat : factorComplexity P (n + 1) = factorComplexity P n)
    {i j : ℕ} (hblocks : blockAt s n i = blockAt s n j) :
    s (i + n) = s (j + n) := by
  have hinj := initialFactor_injective_of_flat s P n hflat
  have hshort :
      initialFactor s n (factorAt s (n + 1) i) =
        initialFactor s n (factorAt s (n + 1) j) := by
    rw [initial_factorAt, initial_factorAt]
    exact Subtype.ext hblocks
  have hlong := congrArg Subtype.val (hinj hshort)
  simpa [factorAt, blockAt] using congrFun hlong (Fin.last n)

lemma blockAt_step_eq_of_flat (s : Stream α) (P : ComplexityData s) (n : ℕ)
    (hflat : factorComplexity P (n + 1) = factorComplexity P n)
    {i j : ℕ} (hblocks : blockAt s n i = blockAt s n j) :
    blockAt s n (i + 1) = blockAt s n (j + 1) := by
  have hnext := next_letter_eq_of_flat s P n hflat hblocks
  have hinj := initialFactor_injective_of_flat s P n hflat
  have hshort :
      initialFactor s n (factorAt s (n + 1) i) =
        initialFactor s n (factorAt s (n + 1) j) := by
    rw [initial_factorAt, initial_factorAt]
    exact Subtype.ext hblocks
  have hlong := congrArg Subtype.val (hinj hshort)
  funext r
  change s ((i + 1) + r) = s ((j + 1) + r)
  rw [show (i + 1) + (r : ℕ) = i + ((r : ℕ) + 1) by omega]
  rw [show (j + 1) + (r : ℕ) = j + ((r : ℕ) + 1) by omega]
  exact congrFun hlong r.succ

lemma blockAt_add_eq_of_flat (s : Stream α) (P : ComplexityData s) (n : ℕ)
    (hflat : factorComplexity P (n + 1) = factorComplexity P n)
    {i j : ℕ} (hblocks : blockAt s n i = blockAt s n j) :
    ∀ t : ℕ, blockAt s n (i + t) = blockAt s n (j + t) := by
  intro t
  induction t with
  | zero => simpa using hblocks
  | succ t ih =>
      have hstep := blockAt_step_eq_of_flat s P n hflat ih
      simpa [Nat.add_assoc] using hstep

lemma eventuallyPeriodic_of_flat (s : Stream α) (P : ComplexityData s) (n : ℕ)
    (hflat : factorComplexity P (n + 1) = factorComplexity P n) :
    EventuallyPeriodic s := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨0, 1, by omega, ?_⟩
    intro i
    have hblocks : blockAt s 0 (i + 1) = blockAt s 0 i := Subsingleton.elim _ _
    simpa using next_letter_eq_of_flat s P 0 hflat hblocks
  · obtain ⟨a, b, hab, hfactor⟩ := P.collision n
    have hblocks : blockAt s n a = blockAt s n b := congrArg Subtype.val hfactor
    have habNat : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    rcases lt_or_gt_of_ne habNat with hablt | hbalt
    · refine ⟨a, b - a, Nat.sub_pos_of_lt hablt, ?_⟩
      intro t
      have hiter := blockAt_add_eq_of_flat s P n hflat hblocks t
      calc
        s ((a : ℕ) + t + ((b : ℕ) - a)) = s ((b : ℕ) + t) := by
          congr 1
          omega
        _ = s ((a : ℕ) + t) := by
          simpa [blockAt] using (congrFun hiter ⟨0, Nat.pos_of_ne_zero hn⟩).symm
    · refine ⟨b, a - b, Nat.sub_pos_of_lt hbalt, ?_⟩
      intro t
      have hiter := blockAt_add_eq_of_flat s P n hflat hblocks.symm t
      calc
        s ((b : ℕ) + t + ((a : ℕ) - b)) = s ((a : ℕ) + t) := by
          congr 1
          omega
        _ = s ((b : ℕ) + t) := by
          simpa [blockAt] using (congrFun hiter ⟨0, Nat.pos_of_ne_zero hn⟩).symm

lemma eventuallyPeriodic_of_complexity_le (s : Stream α) (P : ComplexityData s) {n : ℕ}
    (hle : factorComplexity P n ≤ n) : EventuallyPeriodic s := by
  obtain ⟨k, hk, hflat⟩ := exists_flat_step_of_le (factorComplexity P)
    (factorComplexity_zero s P) (factorComplexity_mono s P) hle
  exact eventuallyPeriodic_of_flat s P k hflat.symm

/-- Morse--Hedlund for one-sided streams, using an explicit exact presentation of factor
cardinalities. The theorem itself requires no choice axiom. -/
theorem morse_hedlund (s : Stream α) (P : ComplexityData s)
    (haperiodic : ¬ EventuallyPeriodic s) : A4 s P := by
  intro n hn
  by_contra h
  have hle : factorComplexity P n ≤ n := by omega
  exact haperiodic (eventuallyPeriodic_of_complexity_le s P hle)

/-- Canonical Morse--Hedlund consequence, stated directly using the cardinality of the
factor set. The classical dependency is exactly the finite-cardinality presentation. -/
theorem morse_hedlund_canonical (s : Stream α) (haperiodic : ¬ EventuallyPeriodic s) :
    ∀ n : ℕ, 0 < n → n + 1 ≤ canonicalFactorComplexity s n := by
  simpa only [canonical_factorComplexity] using
    morse_hedlund s (canonicalComplexityData s) haperiodic

/-- Maximal factor complexity is equivalent to disjunctivity. -/
theorem disjunctive_iff_A5 (s : Stream α) (P : ComplexityData s) :
    Disjunctive s ↔ A5 s P := by
  constructor
  · intro h n hn
    let e : Factor s n ≃ Block α n :=
      { toFun := Subtype.val
        invFun := fun w => ⟨w, h n w⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hcard := Fintype.card_congr ((P.classify n).symm.trans e)
    simpa [factorComplexity] using hcard
  · intro h n w
    by_cases hn : n = 0
    · subst hn
      refine ⟨0, ?_⟩
      intro j
      exact Fin.elim0 j
    · have hcard := h n (Nat.pos_of_ne_zero hn)
      let f : Fin (P.value n) → Block α n :=
        fun i => ((P.classify n).symm i).1
      have hinj : Function.Injective f := by
        intro i j hij
        apply (P.classify n).symm.injective
        exact Subtype.ext hij
      have hcard' : Fintype.card (Fin (P.value n)) = Fintype.card (Block α n) := by
        simpa [factorComplexity] using hcard
      have hsurj : Function.Surjective f :=
        ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard'⟩).2
      obtain ⟨i, hi⟩ := hsurj w
      have hocc := ((P.classify n).symm i).2
      change Occurs s (((P.classify n).symm i).1) at hocc
      simpa [f] using hi ▸ hocc

/-- Decimal specialization: disjunctivity is equivalent to `p(n) = 10^n` at every
natural length. The zero-length case is included and follows from `p(0) = 1`. -/
theorem decimal_disjunctive_iff_A5 (s : Stream (Fin 10)) (P : ComplexityData s) :
    Disjunctive s ↔ ∀ n : ℕ, factorComplexity P n = 10 ^ n := by
  constructor
  · intro h n
    by_cases hn : n = 0
    · subst hn
      simpa using factorComplexity_zero s P
    · have hmax := (disjunctive_iff_A5 s P).mp h n (Nat.pos_of_ne_zero hn)
      simpa using hmax
  · intro h
    apply (disjunctive_iff_A5 s P).mpr
    intro n hn
    simpa using h n

/-- The decimal endpoint stated directly for canonical factor-set cardinality. -/
theorem decimal_disjunctive_iff_canonical_factorComplexity (s : Stream (Fin 10)) :
    Disjunctive s ↔ ∀ n : ℕ, canonicalFactorComplexity s n = 10 ^ n := by
  simpa only [canonical_factorComplexity] using
    decimal_disjunctive_iff_A5 s (canonicalComplexityData s)

end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.morse_hedlund
#print axioms DecimalFactorComplexity.morse_hedlund_canonical
#print axioms DecimalFactorComplexity.disjunctive_iff_A5
#print axioms DecimalFactorComplexity.decimal_disjunctive_iff_A5
#print axioms DecimalFactorComplexity.decimal_disjunctive_iff_canonical_factorComplexity
