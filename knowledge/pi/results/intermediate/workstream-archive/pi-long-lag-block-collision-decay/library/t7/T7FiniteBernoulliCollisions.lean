import Mathlib

/-!
# T7: finite Bernoulli decimal block collisions

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
Canonical SHA-256:
`db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
Original source URL: none; the canonical file records a local formulation on 2026-07-23.

This file proves only the finite uniform base-ten sibling requested by T7.
It contains no infinite stream, almost-sure assertion, or statement about pi.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T7

/-- Number of outcomes in a finite event. -/
def eventCard {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

/-- Event counting agrees with the cardinality of the corresponding subtype. -/
theorem eventCard_eq_natCard {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    eventCard P = Nat.card {ω : Ω // P ω} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- Probability under the uniform law on a nonempty finite type. -/
def uniformProbability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  (eventCard P : ℝ) / Fintype.card Ω

/-- Expectation under the uniform law on a nonempty finite type. -/
def uniformExpectation {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

/-- Covariance of event indicators under the finite uniform law. -/
def eventCovariance {Ω : Type*} [Fintype Ω]
    (P Q : Ω → Prop) : ℝ :=
  uniformProbability (fun ω => P ω ∧ Q ω) -
    uniformProbability P * uniformProbability Q

/-- Variance under the finite uniform law, in the `E[X²] - E[X]²` form. -/
def uniformVariance {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  uniformExpectation (fun ω => (X ω) ^ 2) - (uniformExpectation X) ^ 2

/-- Equality constraints pairing two embedded coordinate families. -/
def PairEq {κ α β : Type*} (left right : κ ↪ α) (x : α → β) : Prop :=
  ∀ k, x (left k) = x (right k)

/-- Assignments satisfying disjoint coordinate-pair equalities are equivalent
to arbitrary assignments away from the right-hand coordinates. -/
def pairEqEquiv {κ α β : Type*} [Fintype κ] [Fintype α]
    (left right : κ ↪ α) (hdisj : Disjoint (Set.range left) (Set.range right)) :
    {x : α → β // PairEq left right x} ≃
      ({a : α // a ∉ Set.range right} → β) := by
  classical
  let fill : ({a : α // a ∉ Set.range right} → β) → α → β := fun g a =>
    if ha : a ∈ Set.range right then
      g ⟨left (right.invOfMemRange ⟨a, ha⟩), by
        intro hmem
        exact Set.disjoint_left.1 hdisj (Set.mem_range_self _) hmem⟩
    else g ⟨a, ha⟩
  refine
    { toFun := fun x a => x.1 a.1
      invFun := fun g => ⟨fill g, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro k
    have hright : right k ∈ Set.range right := Set.mem_range_self k
    have hleft : left k ∉ Set.range right := by
      intro hmem
      exact Set.disjoint_left.1 hdisj (Set.mem_range_self k) hmem
    simp only [fill, dif_pos hright, dif_neg hleft]
    rw [right.right_inv_of_invOfMemRange k]
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ Set.range right
    · let k := right.invOfMemRange ⟨a, ha⟩
      have hright : right k = a := by
        simp [k]
      have hleft : left k ∉ Set.range right := by
        intro hmem
        exact Set.disjoint_left.1 hdisj (Set.mem_range_self k) hmem
      simp only [fill, dif_pos ha]
      change x (left k) = x a
      rw [← hright]
      exact hx k
    · simp only [fill]
      split
      · rename_i hmem
        exact (ha hmem).elim
      · rfl
  · intro g
    funext a
    simp only [fill]
    split
    · rename_i hmem
      exact (a.2 hmem).elim
    · rfl

/-- A family of disjoint equality constraints removes exactly one free
coordinate per constraint. -/
theorem card_pairEq {κ α β : Type*} [Fintype κ] [Fintype α] [Fintype β]
    (left right : κ ↪ α) (hdisj : Disjoint (Set.range left) (Set.range right)) :
    Nat.card {x : α → β // PairEq left right x} =
      Fintype.card β ^ (Fintype.card α - Fintype.card κ) := by
  classical
  rw [Nat.card_congr (pairEqEquiv left right hdisj), Nat.card_fun]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  congr 2
  exact (Fintype.card_congr right.toEquivRange).symm

/-- The exact uniform probability of disjoint coordinate-pair equalities. -/
theorem uniformProbability_pairEq {κ α β : Type*} [Fintype κ] [Fintype α]
    [Fintype β] [DecidableEq α] [Nonempty β]
    (left right : κ ↪ α) (hdisj : Disjoint (Set.range left) (Set.range right)) :
    uniformProbability (PairEq left right : (α → β) → Prop) =
      (Fintype.card β : ℝ) ^ (-(Fintype.card κ : ℤ)) := by
  classical
  let a := Fintype.card α
  let b := Fintype.card β
  let k := Fintype.card κ
  have hk : k ≤ a := Fintype.card_le_of_embedding right
  have hb : (0 : ℝ) < b := by
    exact_mod_cast Fintype.card_pos
  rw [uniformProbability, eventCard_eq_natCard,
    card_pairEq left right hdisj, Fintype.card_fun]
  simp only [Nat.cast_pow]
  change (b ^ (a - k) : ℝ) / b ^ a = (b : ℝ) ^ (-(k : ℤ))
  rw [show a = (a - k) + k by omega, pow_add]
  rw [zpow_neg, zpow_natCast]
  field_simp
  congr 1
  omega

/-- The minimal finite decimal word containing every length-`m` block whose
start lies in `Fin N`. -/
abbrev DecimalWord (m N : ℕ) := Fin (N + m - 1) → Fin 10

/-- The displayed sample space consists of all base-ten words of the minimal
length needed by the allowed starts. -/
theorem decimalWord_card (m N : ℕ) :
    Fintype.card (DecimalWord m N) = 10 ^ (N + m - 1) := by
  simp [DecimalWord]

/-- The coordinates of the length-`m` block starting at `i`. -/
def blockEmbedding {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (i : Fin N) :
    Fin m ↪ Fin (N + m - 1) where
  toFun k := ⟨i + k, by omega⟩
  inj' := by
    intro k l h
    apply Fin.ext
    simpa using congrArg Fin.val h

/-- The exact canonical weak lag cutoff on ordered starts. -/
def AdmissiblePair (m N : ℕ) (e : Fin N × Fin N) : Prop :=
  m ≤ Nat.dist (e.1 : ℕ) (e.2 : ℕ)

/-- Ordered admissible start pairs: both orientations are retained. -/
def orderedPairs (m N : ℕ) : Finset (Fin N × Fin N) :=
  by
    classical
    exact Finset.univ.filter (AdmissiblePair m N)

/-- Membership audit: starts are an ordered pair in `Fin N × Fin N`, and the
cutoff is the weak inequality `m ≤ |i-j|`. -/
theorem mem_orderedPairs_iff {m N : ℕ} (e : Fin N × Fin N) :
    e ∈ orderedPairs m N ↔ m ≤ Nat.dist (e.1 : ℕ) (e.2 : ℕ) := by
  simp [orderedPairs, AdmissiblePair]

/-- Collision of the two length-`m` blocks selected by an ordered pair. -/
def Collision {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (e : Fin N × Fin N) (x : DecimalWord m N) : Prop :=
  PairEq (blockEmbedding hm hN e.1) (blockEmbedding hm hN e.2) x

/-- The coordinate support of one ordered collision event. -/
def eventSupport {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (e : Fin N × Fin N) : Set (Fin (N + m - 1)) :=
  Set.range (blockEmbedding hm hN e.1) ∪ Set.range (blockEmbedding hm hN e.2)

/-- The lag cutoff says exactly that the two blocks in one collision event
have disjoint coordinate supports. -/
theorem blockEmbedding_ranges_disjoint {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (e : Fin N × Fin N) (he : AdmissiblePair m N e) :
    Disjoint (Set.range (blockEmbedding hm hN e.1))
      (Set.range (blockEmbedding hm hN e.2)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨k, hk⟩
  rcases hy with ⟨l, hl⟩
  have hcoord : (e.1 : ℕ) + (k : ℕ) = (e.2 : ℕ) + (l : ℕ) := by
    exact congrArg Fin.val (hk.trans hl.symm)
  change m ≤ Nat.dist (e.1 : ℕ) (e.2 : ℕ) at he
  by_cases hij : (e.1 : ℕ) ≤ (e.2 : ℕ)
  · rw [Nat.dist_eq_sub_of_le hij] at he
    omega
  · have hji : (e.2 : ℕ) ≤ (e.1 : ℕ) := Nat.le_of_not_ge hij
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji] at he
    omega

/-- Every admissible ordered collision event has exact probability `10⁻ᵐ`
on the displayed finite uniform decimal-word space. -/
theorem collision_probability {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (e : Fin N × Fin N) (he : AdmissiblePair m N e) :
    uniformProbability (Collision hm hN e) = (10 : ℝ) ^ (-(m : ℤ)) := by
  simpa [Collision] using
    (uniformProbability_pairEq
      (blockEmbedding hm hN e.1) (blockEmbedding hm hN e.2)
      (blockEmbedding_ranges_disjoint hm hN e he))

/-- Combine embeddings whose ranges are disjoint. -/
def sumEmbedding {κ ι α : Type*} (f : κ ↪ α) (g : ι ↪ α)
    (h : Disjoint (Set.range f) (Set.range g)) : κ ⊕ ι ↪ α :=
  Equiv.sumEmbeddingEquivProdEmbeddingDisjoint.symm ⟨(f, g), h⟩

@[simp] theorem sumEmbedding_inl {κ ι α : Type*} (f : κ ↪ α) (g : ι ↪ α)
    (h : Disjoint (Set.range f) (Set.range g)) (k : κ) :
    sumEmbedding f g h (Sum.inl k) = f k := rfl

@[simp] theorem sumEmbedding_inr {κ ι α : Type*} (f : κ ↪ α) (g : ι ↪ α)
    (h : Disjoint (Set.range f) (Set.range g)) (k : ι) :
    sumEmbedding f g h (Sum.inr k) = g k := rfl

theorem range_sumEmbedding {κ ι α : Type*} (f : κ ↪ α) (g : ι ↪ α)
    (h : Disjoint (Set.range f) (Set.range g)) :
    Set.range (sumEmbedding f g h) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | inl k => exact Or.inl (Set.mem_range_self k)
    | inr k => exact Or.inr (Set.mem_range_self k)
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨Sum.inl k, rfl⟩
    · exact ⟨Sum.inr k, rfl⟩

theorem pairEq_sumEmbedding {κ ι α β : Type*}
    (l₁ r₁ : κ ↪ α) (l₂ r₂ : ι ↪ α)
    (hleft : Disjoint (Set.range l₁) (Set.range l₂))
    (hright : Disjoint (Set.range r₁) (Set.range r₂)) (x : α → β) :
    PairEq (sumEmbedding l₁ l₂ hleft) (sumEmbedding r₁ r₂ hright) x ↔
      PairEq l₁ r₁ x ∧ PairEq l₂ r₂ x := by
  constructor
  · intro h
    exact ⟨fun k => h (Sum.inl k), fun k => h (Sum.inr k)⟩
  · rintro ⟨h₁, h₂⟩ (k | k)
    · exact h₁ k
    · exact h₂ k

/-- Two events with disjoint four-block supports have joint probability
`10⁻²ᵐ`; this is the finite independence statement needed below. -/
theorem disjoint_collision_joint_probability {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (e f : Fin N × Fin N)
    (he : AdmissiblePair m N e) (hf : AdmissiblePair m N f)
    (hdisj : Disjoint (eventSupport hm hN e) (eventSupport hm hN f)) :
    uniformProbability (fun x : DecimalWord m N =>
      Collision hm hN e x ∧ Collision hm hN f x) =
        (10 : ℝ) ^ (-(2 * m : ℤ)) := by
  let eL := blockEmbedding hm hN e.1
  let eR := blockEmbedding hm hN e.2
  let fL := blockEmbedding hm hN f.1
  let fR := blockEmbedding hm hN f.2
  have heLR : Disjoint (Set.range eL) (Set.range eR) :=
    blockEmbedding_ranges_disjoint hm hN e he
  have hfLR : Disjoint (Set.range fL) (Set.range fR) :=
    blockEmbedding_ranges_disjoint hm hN f hf
  have hLL : Disjoint (Set.range eL) (Set.range fL) :=
    hdisj.mono Set.subset_union_left Set.subset_union_left
  have hRR : Disjoint (Set.range eR) (Set.range fR) :=
    hdisj.mono Set.subset_union_right Set.subset_union_right
  have hLfR : Disjoint (Set.range eL) (Set.range fR) :=
    hdisj.mono Set.subset_union_left Set.subset_union_right
  have hfLeR : Disjoint (Set.range fL) (Set.range eR) :=
    hdisj.symm.mono Set.subset_union_left Set.subset_union_right
  have hcombined :
      Disjoint (Set.range (sumEmbedding eL fL hLL))
        (Set.range (sumEmbedding eR fR hRR)) := by
    rw [range_sumEmbedding, range_sumEmbedding, Set.disjoint_left]
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Set.disjoint_left.1 heLR hx hy
    · exact Set.disjoint_left.1 hLfR hx hy
    · exact Set.disjoint_left.1 hfLeR hx hy
    · exact Set.disjoint_left.1 hfLR hx hy
  have hpred :
      (fun x : DecimalWord m N => Collision hm hN e x ∧ Collision hm hN f x) =
        PairEq (sumEmbedding eL fL hLL) (sumEmbedding eR fR hRR) := by
    funext x
    apply propext
    simpa [Collision, eL, eR, fL, fR] using
      (pairEq_sumEmbedding eL eR fL fR hLL hRR x).symm
  rw [hpred]
  rw [uniformProbability_pairEq
      (β := Fin 10)
      (sumEmbedding eL fL hLL) (sumEmbedding eR fR hRR) hcombined]
  congr 1
  norm_num
  ring

/-- Collision indicators whose four coordinate blocks are disjoint have zero
covariance under the finite uniform law. -/
theorem disjoint_collision_covariance_zero {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (e f : Fin N × Fin N)
    (he : AdmissiblePair m N e) (hf : AdmissiblePair m N f)
    (hdisj : Disjoint (eventSupport hm hN e) (eventSupport hm hN f)) :
    eventCovariance (Collision hm hN e) (Collision hm hN f) = 0 := by
  rw [eventCovariance,
    disjoint_collision_joint_probability hm hN e f he hf hdisj,
    collision_probability hm hN e he, collision_probability hm hN f hf]
  have hexp : (-(2 * m : ℤ)) = -(m : ℤ) + -(m : ℤ) := by
    ring
  rw [hexp, zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0)]
  ring

/-- Starts whose length-`m` coordinate blocks can overlap a fixed start. -/
def nearStarts (m N : ℕ) (a : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun b => Nat.dist (a : ℕ) (b : ℕ) < m

/-- A nearby start is encoded by its side and its distance from the fixed
start. This is the `2m` dependency-window count. -/
def nearStartCode {m N : ℕ} (a : Fin N)
    (b : {b : Fin N // Nat.dist (a : ℕ) (b : ℕ) < m}) : Fin m ⊕ Fin m := by
  by_cases hba : (b.1 : ℕ) ≤ (a : ℕ)
  · exact Sum.inl ⟨(a : ℕ) - (b.1 : ℕ), by
      have hb := b.2
      rw [Nat.dist_eq_sub_of_le_right hba] at hb
      exact hb⟩
  · have hab : (a : ℕ) ≤ (b.1 : ℕ) := Nat.le_of_not_ge hba
    exact Sum.inr ⟨(b.1 : ℕ) - (a : ℕ), by
      have hb := b.2
      rw [Nat.dist_eq_sub_of_le hab] at hb
      exact hb⟩

theorem nearStartCode_injective {m N : ℕ} (a : Fin N) :
    Function.Injective (nearStartCode (m := m) a) := by
  intro b c h
  by_cases hb : (b.1 : ℕ) ≤ (a : ℕ) <;>
    by_cases hc : (c.1 : ℕ) ≤ (a : ℕ)
  · simp only [nearStartCode, dif_pos hb, dif_pos hc, Sum.inl.injEq,
      Fin.mk.injEq] at h
    apply Subtype.ext
    apply Fin.ext
    omega
  · simp only [nearStartCode, dif_pos hb, dif_neg hc, reduceCtorEq] at h
  · simp only [nearStartCode, dif_neg hb, dif_pos hc, reduceCtorEq] at h
  · simp only [nearStartCode, dif_neg hb, dif_neg hc, Sum.inr.injEq,
      Fin.mk.injEq] at h
    apply Subtype.ext
    apply Fin.ext
    omega

/-- At most `2m` starts have blocks intersecting a fixed length-`m` block. -/
theorem nearStarts_card_le (m N : ℕ) (a : Fin N) :
    (nearStarts m N a).card ≤ 2 * m := by
  classical
  let emb : {b : Fin N // Nat.dist (a : ℕ) (b : ℕ) < m} ↪ Fin m ⊕ Fin m :=
    ⟨nearStartCode a, nearStartCode_injective a⟩
  calc
    (nearStarts m N a).card =
        Fintype.card {b : Fin N // Nat.dist (a : ℕ) (b : ℕ) < m} := by
      rw [Fintype.card_subtype]
      rfl
    _ ≤ Fintype.card (Fin m ⊕ Fin m) := Fintype.card_le_of_embedding emb
    _ = 2 * m := by simp [two_mul]

/-- The possible starts whose blocks can meet either block of `e`. -/
def nearPool (m N : ℕ) (e : Fin N × Fin N) : Finset (Fin N) :=
  nearStarts m N e.1 ∪ nearStarts m N e.2

theorem nearPool_card_le (m N : ℕ) (e : Fin N × Fin N) :
    (nearPool m N e).card ≤ 4 * m := by
  calc
    (nearPool m N e).card ≤
        (nearStarts m N e.1).card + (nearStarts m N e.2).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * m + 2 * m := Nat.add_le_add
      (nearStarts_card_le m N e.1) (nearStarts_card_le m N e.2)
    _ = 4 * m := by omega

/-- Admissible ordered events whose coordinate supports meet that of `e`. -/
def overlappingPairs {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (e : Fin N × Fin N) : Finset (Fin N × Fin N) := by
  classical
  exact (orderedPairs m N).filter fun f =>
    ¬Disjoint (eventSupport hm hN e) (eventSupport hm hN f)

/-- If neither endpoint of `f` lies in the dependency window of either
endpoint of `e`, then the two event supports are disjoint. -/
theorem eventSupport_disjoint_of_endpoints_far {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (e f : Fin N × Fin N)
    (h11 : m ≤ Nat.dist (e.1 : ℕ) (f.1 : ℕ))
    (h12 : m ≤ Nat.dist (e.1 : ℕ) (f.2 : ℕ))
    (h21 : m ≤ Nat.dist (e.2 : ℕ) (f.1 : ℕ))
    (h22 : m ≤ Nat.dist (e.2 : ℕ) (f.2 : ℕ)) :
    Disjoint (eventSupport hm hN e) (eventSupport hm hN f) := by
  have hd11 := blockEmbedding_ranges_disjoint hm hN (e.1, f.1) h11
  have hd12 := blockEmbedding_ranges_disjoint hm hN (e.1, f.2) h12
  have hd21 := blockEmbedding_ranges_disjoint hm hN (e.2, f.1) h21
  have hd22 := blockEmbedding_ranges_disjoint hm hN (e.2, f.2) h22
  rw [eventSupport, eventSupport, Set.disjoint_left]
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Set.disjoint_left.1 hd11 hx hy
  · exact Set.disjoint_left.1 hd12 hx hy
  · exact Set.disjoint_left.1 hd21 hx hy
  · exact Set.disjoint_left.1 hd22 hx hy

/-- Support overlap forces at least one endpoint of the second ordered pair
into the explicit `4m` pool around the first pair. -/
theorem support_overlap_implies_endpoint_mem_nearPool {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (e f : Fin N × Fin N)
    (hoverlap : ¬Disjoint (eventSupport hm hN e) (eventSupport hm hN f)) :
    f.1 ∈ nearPool m N e ∨ f.2 ∈ nearPool m N e := by
  classical
  by_contra h
  push Not at h
  have h11 : m ≤ Nat.dist (e.1 : ℕ) (f.1 : ℕ) := by
    have := h.1
    simp only [nearPool, Finset.mem_union, nearStarts, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or] at this
    omega
  have h12 : m ≤ Nat.dist (e.1 : ℕ) (f.2 : ℕ) := by
    have := h.2
    simp only [nearPool, Finset.mem_union, nearStarts, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or] at this
    omega
  have h21 : m ≤ Nat.dist (e.2 : ℕ) (f.1 : ℕ) := by
    have := h.1
    simp only [nearPool, Finset.mem_union, nearStarts, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or] at this
    omega
  have h22 : m ≤ Nat.dist (e.2 : ℕ) (f.2 : ℕ) := by
    have := h.2
    simp only [nearPool, Finset.mem_union, nearStarts, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or] at this
    omega
  exact hoverlap (eventSupport_disjoint_of_endpoints_far hm hN e f h11 h12 h21 h22)

/-- Explicit overlap dependency bound for the ordered-pair convention. -/
theorem overlappingPairs_card_le {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (e : Fin N × Fin N) :
    (overlappingPairs hm hN e).card ≤ 8 * m * N := by
  classical
  let A := nearPool m N e
  let U : Finset (Fin N) := Finset.univ
  have hsubset : overlappingPairs hm hN e ⊆ (A ×ˢ U) ∪ (U ×ˢ A) := by
    intro f hf
    have hoverlap := (Finset.mem_filter.mp hf).2
    have hend := support_overlap_implies_endpoint_mem_nearPool hm hN e f hoverlap
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true,
      true_and, A, U]
    exact hend
  calc
    (overlappingPairs hm hN e).card ≤ ((A ×ˢ U) ∪ (U ×ˢ A)).card :=
      Finset.card_le_card hsubset
    _ ≤ (A ×ˢ U).card + (U ×ˢ A).card := Finset.card_union_le _ _
    _ = 2 * A.card * N := by simp [U]; ring
    _ ≤ 2 * (4 * m) * N := Nat.mul_le_mul_right N
      (Nat.mul_le_mul_left 2 (nearPool_card_le m N e))
    _ = 8 * m * N := by ring

/-- The exact ordered collision count on a finite decimal word. -/
def R (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) (x : DecimalWord m N) : ℕ :=
  by
    classical
    exact ((orderedPairs m N).filter fun e => Collision hm hN e x).card

/-- Real-valued indicator of a finite event. -/
def eventIndicator {Ω : Type*} (P : Ω → Prop) (ω : Ω) : ℝ :=
  by
    classical
    exact if P ω then 1 else 0

theorem uniformExpectation_eventIndicator {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) :
    uniformExpectation (eventIndicator P) = uniformProbability P := by
  classical
  unfold uniformExpectation uniformProbability eventCard eventIndicator
  congr 1
  norm_cast
  simp

theorem uniformExpectation_sum {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (X : ι → Ω → ℝ) :
    uniformExpectation (fun ω => ∑ i ∈ s, X i ω) =
      ∑ i ∈ s, uniformExpectation (X i) := by
  classical
  unfold uniformExpectation
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

theorem eventIndicator_mul {Ω : Type*} (P Q : Ω → Prop) (ω : Ω) :
    eventIndicator P ω * eventIndicator Q ω = eventIndicator (fun x => P x ∧ Q x) ω := by
  simp only [eventIndicator]
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

/-- Variance of a finite sum of indicators is the double sum of their event
covariances. -/
theorem uniformVariance_sum_indicators {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (P : ι → Ω → Prop) :
    uniformVariance (fun ω => ∑ i ∈ s, eventIndicator (P i) ω) =
      ∑ i ∈ s, ∑ j ∈ s, eventCovariance (P i) (P j) := by
  classical
  let I : ι → Ω → ℝ := fun i ω => eventIndicator (P i) ω
  have hsq : (fun ω => (∑ i ∈ s, I i ω) ^ 2) =
      (fun ω => ∑ i ∈ s, ∑ j ∈ s,
        eventIndicator (fun x => P i x ∧ P j x) ω) := by
    funext ω
    calc
      (∑ i ∈ s, I i ω) ^ 2 = (∑ i ∈ s, I i ω) * (∑ j ∈ s, I j ω) := by ring
      _ = ∑ i ∈ s, ∑ j ∈ s, I i ω * I j ω := by
        rw [Finset.sum_mul_sum]
      _ = ∑ i ∈ s, ∑ j ∈ s,
          eventIndicator (fun x => P i x ∧ P j x) ω := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact eventIndicator_mul (P i) (P j) ω
  have hE : uniformExpectation (fun ω => ∑ i ∈ s, I i ω) =
      ∑ i ∈ s, uniformExpectation (I i) := uniformExpectation_sum s I
  have hE2 : uniformExpectation (fun ω => ∑ i ∈ s, ∑ j ∈ s,
      eventIndicator (fun x => P i x ∧ P j x) ω) =
      ∑ i ∈ s, ∑ j ∈ s,
        uniformExpectation (eventIndicator (fun x => P i x ∧ P j x)) := by
    rw [uniformExpectation_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact uniformExpectation_sum s
      (fun j ω => eventIndicator (fun x => P i x ∧ P j x) ω)
  unfold uniformVariance
  rw [show (fun ω => ∑ i ∈ s, eventIndicator (P i) ω) =
      (fun ω => ∑ i ∈ s, I i ω) by rfl,
    hsq, hE, hE2, pow_two, Finset.sum_mul_sum]
  unfold eventCovariance
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hIij := uniformExpectation_eventIndicator (fun x => P i x ∧ P j x)
  have hIi : uniformExpectation (I i) = uniformProbability (P i) := by
    dsimp [I]
    exact uniformExpectation_eventIndicator (P i)
  have hIj : uniformExpectation (I j) = uniformProbability (P j) := by
    dsimp [I]
    exact uniformExpectation_eventIndicator (P j)
  rw [hIij, hIi, hIj]

theorem uniformProbability_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : 0 ≤ uniformProbability P := by
  unfold uniformProbability
  positivity

theorem uniformProbability_inter_le_left {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P Q : Ω → Prop) :
    uniformProbability (fun ω => P ω ∧ Q ω) ≤ uniformProbability P := by
  classical
  unfold uniformProbability eventCard
  apply div_le_div_of_nonneg_right
  · norm_cast
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  · positivity

/-- Crude covariance bound used for support-overlapping events. -/
theorem eventCovariance_le_probability_left {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P Q : Ω → Prop) : eventCovariance P Q ≤ uniformProbability P := by
  unfold eventCovariance
  have hinter := uniformProbability_inter_le_left P Q
  have hP := uniformProbability_nonneg P
  have hQ := uniformProbability_nonneg Q
  nlinarith

/-- The natural count `R` is exactly the sum of the ordered event indicators. -/
theorem R_cast_eq_sum_indicators {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (x : DecimalWord m N) :
    (R m N hm hN x : ℝ) =
      ∑ e ∈ orderedPairs m N, eventIndicator (Collision hm hN e) x := by
  classical
  unfold R eventIndicator
  norm_cast
  simp

theorem orderedPairs_card_le (m N : ℕ) : (orderedPairs m N).card ≤ N ^ 2 := by
  classical
  calc
    (orderedPairs m N).card ≤ (Finset.univ : Finset (Fin N × Fin N)).card :=
      Finset.card_le_card (by simp [orderedPairs])
    _ = N ^ 2 := by simp [pow_two]

/-- For one admissible event, only the explicitly counted support-overlapping
events can contribute nonzero covariance. -/
theorem covariance_sum_le_overlap_count {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (e : Fin N × Fin N)
    (he : e ∈ orderedPairs m N) :
    (∑ f ∈ orderedPairs m N,
      eventCovariance (Collision hm hN e) (Collision hm hN f)) ≤
        ((overlappingPairs hm hN e).card : ℝ) * (10 : ℝ) ^ (-(m : ℤ)) := by
  classical
  have he' : AdmissiblePair m N e := by
    simpa [orderedPairs] using he
  calc
    (∑ f ∈ orderedPairs m N,
        eventCovariance (Collision hm hN e) (Collision hm hN f)) ≤
        ∑ f ∈ orderedPairs m N,
          if ¬Disjoint (eventSupport hm hN e) (eventSupport hm hN f) then
            (10 : ℝ) ^ (-(m : ℤ)) else 0 := by
      apply Finset.sum_le_sum
      intro f hf
      have hf' : AdmissiblePair m N f := by
        simpa [orderedPairs] using hf
      by_cases hoverlap :
          ¬Disjoint (eventSupport hm hN e) (eventSupport hm hN f)
      · rw [if_pos hoverlap]
        calc
          eventCovariance (Collision hm hN e) (Collision hm hN f) ≤
              uniformProbability (Collision hm hN e) :=
            eventCovariance_le_probability_left _ _
          _ = (10 : ℝ) ^ (-(m : ℤ)) := collision_probability hm hN e he'
      · rw [if_neg hoverlap,
          disjoint_collision_covariance_zero hm hN e f he' hf' (not_not.mp hoverlap)]
    _ = ((overlappingPairs hm hN e).card : ℝ) * (10 : ℝ) ^ (-(m : ℤ)) := by
      unfold overlappingPairs
      rw [Finset.natCast_card_filter]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hoverlap :
          ¬Disjoint (eventSupport hm hN e) (eventSupport hm hN f)
      · simp [hoverlap]
      · simp [hoverlap]

/-- Stronger displayed finite variance bound for the exact ordered count. -/
theorem variance_R_le_eight_mul {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    uniformVariance (fun x : DecimalWord m N => (R m N hm hN x : ℝ)) ≤
      8 * (m : ℝ) * (N : ℝ) ^ 3 * (10 : ℝ) ^ (-(m : ℤ)) := by
  classical
  rw [show (fun x : DecimalWord m N => (R m N hm hN x : ℝ)) =
      (fun x => ∑ e ∈ orderedPairs m N,
        eventIndicator (Collision hm hN e) x) by
      funext x
      exact R_cast_eq_sum_indicators hm hN x]
  rw [uniformVariance_sum_indicators]
  calc
    (∑ e ∈ orderedPairs m N, ∑ f ∈ orderedPairs m N,
        eventCovariance (Collision hm hN e) (Collision hm hN f)) ≤
        ∑ e ∈ orderedPairs m N,
          ((overlappingPairs hm hN e).card : ℝ) * (10 : ℝ) ^ (-(m : ℤ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact covariance_sum_le_overlap_count hm hN e he
    _ ≤ ∑ _e ∈ orderedPairs m N,
          (((8 * m * N : ℕ) : ℝ) * (10 : ℝ) ^ (-(m : ℤ))) := by
      apply Finset.sum_le_sum
      intro e he
      have hover := overlappingPairs_card_le hm hN e
      have hp : 0 ≤ (10 : ℝ) ^ (-(m : ℤ)) := le_of_lt (zpow_pos (by norm_num) _)
      gcongr
    _ = ((orderedPairs m N).card : ℝ) *
          ((8 * m * N : ℕ) : ℝ) * (10 : ℝ) ^ (-(m : ℤ)) := by
      simp
      ring
    _ ≤ ((N ^ 2 : ℕ) : ℝ) * ((8 * m * N : ℕ) : ℝ) *
          (10 : ℝ) ^ (-(m : ℤ)) := by
      have hp : 0 ≤ (10 : ℝ) ^ (-(m : ℤ)) := le_of_lt (zpow_pos (by norm_num) _)
      have hcard := orderedPairs_card_le m N
      gcongr
    _ = 8 * (m : ℝ) * (N : ℝ) ^ 3 * (10 : ℝ) ^ (-(m : ℤ)) := by
      push_cast
      ring

/-- The requested explicit T7 constant, as a direct corollary of the stronger
constant-eight estimate. -/
theorem variance_R_le_ten_mul {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    uniformVariance (fun x : DecimalWord m N => (R m N hm hN x : ℝ)) ≤
      10 * (m : ℝ) * (N : ℝ) ^ 3 * (10 : ℝ) ^ (-(m : ℤ)) := by
  have h := variance_R_le_eight_mul hm hN
  have hp : 0 ≤ (10 : ℝ) ^ (-(m : ℤ)) := le_of_lt (zpow_pos (by norm_num) _)
  have hfac : 0 ≤ (m : ℝ) * (N : ℝ) ^ 3 * (10 : ℝ) ^ (-(m : ℤ)) := by
    positivity
  nlinarith

end Theory.PiDigits.LongLagBlockCollisionDecay.T7

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T7.decimalWord_card
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T7.mem_orderedPairs_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T7.collision_probability
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T7.disjoint_collision_covariance_zero
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T7.overlappingPairs_card_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T7.variance_R_le_eight_mul
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T7.variance_R_le_ten_mul
