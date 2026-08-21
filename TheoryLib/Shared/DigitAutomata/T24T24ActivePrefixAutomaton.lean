import Mathlib

/-!
# T24: active-prefix automata for one or two forbidden words

Canonical source: `problems/local/multiplicative-avoidance-gap.txt`
SHA-256: `05d09b6edb60fa060cc952fc5b2fad9dea75c20d84ac628d86f1b6dd6b0ab7c8`
Relevance URL preserved from the source:
<https://arxiv.org/pdf/2606.06655v1>

This is a narrow combinatorial precursor to the canonical question. It proves
no statement about entropy, residual supersolutions, `Gamma`, or C1.

Normalized scope: the alphabet is `Fin b`, with `2 ≤ b`. A reduced forbidden
family contains exactly one or two nonempty words, and no distinct member is
an infix of another. States are the empty word and all proper prefixes of
forbidden words. A live transition uses the longest state which is a suffix
after appending one digit. The rational adjacency matrix counts digit labels.

The words "reduced family" and "one or two" are otherwise potentially
ambiguous; the preceding infix-antichain and exact-cardinality conventions are
the meanings used throughout this module.
-/

noncomputable section

open Finset
open scoped BigOperators Matrix

namespace Theory.Shared.DigitAutomata.T24

abbrev Digit (b : ℕ) := Fin b

/-- A reduced family of exactly one or two nonempty forbidden words. -/
structure ForbiddenFamily (b : ℕ) where
  base_ge_two : 2 ≤ b
  words : Finset (List (Digit b))
  card_one_or_two : words.card = 1 ∨ words.card = 2
  words_nonempty : ∀ w ∈ words, w ≠ []
  reduced : ∀ u ∈ words, ∀ v ∈ words, u ≠ v → ¬u <:+: v

namespace ForbiddenFamily

variable {b : ℕ} (F : ForbiddenFamily b)

/-- The proper prefixes of a word. -/
def properPrefixes (w : List (Digit b)) : Finset (List (Digit b)) :=
  w.inits.toFinset.erase w

theorem mem_properPrefixes_iff {p w : List (Digit b)} :
    p ∈ properPrefixes w ↔ p <+: w ∧ p ≠ w := by
  simp [properPrefixes, List.mem_inits, and_comm]

/-- The empty word together with all proper forbidden-word prefixes. -/
def activePrefixes : Finset (List (Digit b)) :=
  insert [] (F.words.biUnion properPrefixes)

theorem mem_activePrefixes_iff {p : List (Digit b)} :
    p ∈ F.activePrefixes ↔
      p = [] ∨ ∃ w ∈ F.words, p <+: w ∧ p ≠ w := by
  simp [activePrefixes, mem_properPrefixes_iff]

/-- A state is literally an active proper prefix. -/
def State := {p : List (Digit b) // p ∈ F.activePrefixes}

instance : DecidableEq F.State := Classical.decEq _
instance : Fintype F.State := Fintype.ofFinset F.activePrefixes (fun _ ↦ Iff.rfl)

/-- The initial empty-prefix state. -/
def initialState : F.State := ⟨[], by simp [activePrefixes]⟩

/-- `q` is the longest active prefix which is a suffix of `w`. -/
def IsActiveState (w : List (Digit b)) (q : F.State) : Prop :=
  q.1 <:+ w ∧ ∀ r : F.State, r.1 <:+ w → r.1.length ≤ q.1.length

/-- A longest active suffix exists for every finite word. -/
theorem exists_isActiveState (w : List (Digit b)) :
    ∃ q : F.State, F.IsActiveState w q := by
  classical
  let candidates : Finset F.State := Finset.univ.filter fun q ↦ q.1 <:+ w
  have hempty : F.initialState ∈ candidates := by
    simp [candidates, initialState]
  obtain ⟨q, hq, hmax⟩ :=
    candidates.exists_max_image (fun r ↦ r.1.length) ⟨F.initialState, hempty⟩
  refine ⟨q, ?_, ?_⟩
  · simpa [candidates] using hq
  · intro r hr
    exact hmax r (by simpa [candidates] using hr)

/-- Longest active suffixes are unique. -/
theorem isActiveState_unique {w : List (Digit b)} {q r : F.State}
    (hq : F.IsActiveState w q) (hr : F.IsActiveState w r) : q = r := by
  apply Subtype.ext
  have hlen : q.1.length = r.1.length :=
    Nat.le_antisymm (hr.2 q hq.1) (hq.2 r hr.1)
  exact (List.suffix_of_suffix_length_le hq.1 hr.1 hlen.le).eq_of_length hlen

/-- The canonical longest active suffix of a word. -/
def activeState (w : List (Digit b)) : F.State :=
  Classical.choose (F.exists_isActiveState w)

theorem activeState_spec (w : List (Digit b)) :
    F.IsActiveState w (F.activeState w) :=
  Classical.choose_spec (F.exists_isActiveState w)

/-- Appending `d` to `p` falls back to `q` exactly when `q` is the longest
active suffix of the appended word. -/
def IsFallback (p : F.State) (d : Digit b) (q : F.State) : Prop :=
  q.1 <:+ p.1 ++ [d] ∧
    ∀ r : F.State, r.1 <:+ p.1 ++ [d] → r.1.length ≤ q.1.length

/-- The deterministic longest-live-suffix fallback. -/
def fallback (p : F.State) (d : Digit b) : F.State :=
  F.activeState (p.1 ++ [d])

/-- The fallback function is characterized exactly, and only, by the suffix
and maximal-length relation in `IsFallback`. -/
theorem fallback_eq_iff_isFallback (p : F.State) (d : Digit b) (q : F.State) :
    F.fallback p d = q ↔ F.IsFallback p d q := by
  constructor
  · rintro rfl
    exact F.activeState_spec (p.1 ++ [d])
  · intro hq
    exact F.isActiveState_unique (F.activeState_spec (p.1 ++ [d])) hq

/-- Appending `d` completes a forbidden word when one is a suffix. -/
def Completes (p : F.State) (d : Digit b) : Prop :=
  ∃ f ∈ F.words, f <:+ p.1 ++ [d]

instance (p : F.State) (d : Digit b) : Decidable (F.Completes p d) :=
  Classical.propDecidable _

/-- Live labelled transitions are precisely non-completing suffix fallbacks. -/
def Step (p : F.State) (d : Digit b) (q : F.State) : Prop :=
  ¬F.Completes p d ∧ F.IsFallback p d q

instance (p : F.State) (d : Digit b) (q : F.State) : Decidable (F.Step p d q) :=
  Classical.propDecidable _

/-- A digit has a unique live successor exactly when it does not complete a
forbidden word. -/
theorem existsUnique_step_iff_not_completes (p : F.State) (d : Digit b) :
    (∃! q : F.State, F.Step p d q) ↔ ¬F.Completes p d := by
  constructor
  · rintro ⟨q, hq, _⟩
    exact hq.1
  · intro hcomplete
    refine ⟨F.fallback p d, ⟨hcomplete, ?_⟩, ?_⟩
    · exact (F.fallback_eq_iff_isFallback p d _).mp rfl
    · intro q hq
      exact ((F.fallback_eq_iff_isFallback p d q).mpr hq.2).symm

/-- Exact pointwise partition of every outgoing digit: it either completes a
forbidden word or has one unique live target, but never both. -/
theorem outgoingDigit_partition (p : F.State) (d : Digit b) :
    (F.Completes p d ∨ ∃! q : F.State, F.Step p d q) ∧
      ¬(F.Completes p d ∧ ∃! q : F.State, F.Step p d q) := by
  by_cases h : F.Completes p d
  · refine ⟨Or.inl h, ?_⟩
    rintro ⟨_, hstep⟩
    rw [F.existsUnique_step_iff_not_completes] at hstep
    exact hstep h
  · refine ⟨Or.inr ((F.existsUnique_step_iff_not_completes p d).mpr h), ?_⟩
    exact fun hboth ↦ h hboth.1

/-- Generic finite labelled paths, with labels in chronological order. -/
def LabelledPath {α σ : Type} (step : σ → α → σ → Prop) :
    ℕ → σ → σ → Type
  | 0, i, j => PLift (i = j)
  | n + 1, i, k => Σ j : σ, LabelledPath step n i j × {a : α // step j a k}

/-- The word read along a labelled path. -/
def pathWord {α σ : Type} {step : σ → α → σ → Prop} :
    {n : ℕ} → {i j : σ} → LabelledPath step n i j → List α
  | 0, _, _, _ => []
  | _ + 1, _, _, ⟨_, p, a⟩ => pathWord p ++ [a.1]

theorem pathWord_length {α σ : Type} {step : σ → α → σ → Prop}
    {n : ℕ} {i j : σ} (p : LabelledPath step n i j) :
    (pathWord p).length = n := by
  induction n generalizing i j with
  | zero => simp [pathWord]
  | succ n ih =>
      obtain ⟨k, p, a⟩ := p
      simp [pathWord, ih p]

instance labelledPath_finite {α σ : Type} [Finite α] [Finite σ]
    (step : σ → α → σ → Prop) (n : ℕ) (i j : σ) :
    Finite (LabelledPath step n i j) := by
  classical
  induction n generalizing i j with
  | zero => simp [LabelledPath]; infer_instance
  | succ n ih =>
      letI (k : σ) : Finite (LabelledPath step n i k) := ih i k
      simp only [LabelledPath]
      infer_instance

/-- The rational adjacency matrix counts digit labels on live transitions. -/
def rationalAdjacency : Matrix F.State F.State ℚ :=
  fun p q ↦ Nat.card {d : Digit b // F.Step p d q}

/-- Matrix powers count labelled paths, with no transition-partition
hypothesis supplied to the theorem. -/
theorem labelledPath_card_eq_rationalAdjacency_pow
    (n : ℕ) (p q : F.State) :
    (Nat.card (LabelledPath F.Step n p q) : ℚ) =
      (F.rationalAdjacency ^ n) p q := by
  induction n generalizing q with
  | zero =>
      by_cases h : p = q
      · subst q
        simp [LabelledPath]
      · simp [LabelledPath, h]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl, pow_succ, Matrix.mul_apply]
      simp only [LabelledPath, Nat.card_sigma, Nat.card_prod, Nat.cast_sum,
        Nat.cast_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [ih]
      rfl

/-- A finite word avoids the family when no forbidden word occurs as an
infix. -/
def Avoids (w : List (Digit b)) : Prop :=
  ∀ f ∈ F.words, ¬f <:+: w

/-- The automaton accepts a word if some path from the empty state reads it. -/
def Accepts (w : List (Digit b)) : Prop :=
  ∃ q : F.State,
    ∃ p : LabelledPath F.Step w.length F.initialState q, pathWord p = w

theorem dropLast_mem_activePrefixes {f : List (Digit b)}
    (hf : f ∈ F.words) : f.dropLast ∈ F.activePrefixes := by
  rw [F.mem_activePrefixes_iff]
  right
  refine ⟨f, hf, f.dropLast_prefix, ?_⟩
  intro heq
  have hne := F.words_nonempty f hf
  have hlen := congrArg List.length heq
  cases f with
  | nil => exact hne rfl
  | cons a l => simp at hlen

theorem dropLast_mem_activePrefixes_of_mem {u : List (Digit b)}
    (hu : u ∈ F.activePrefixes) : u.dropLast ∈ F.activePrefixes := by
  rw [F.mem_activePrefixes_iff] at hu ⊢
  rcases hu with rfl | ⟨f, hf, hprefix, hne⟩
  · simp
  by_cases hunil : u = []
  · simp [hunil]
  · right
    refine ⟨f, hf, u.dropLast_prefix.trans hprefix, ?_⟩
    intro heq
    have hproper : u.length < f.length :=
      lt_of_le_of_ne hprefix.length_le (fun h ↦ hne (hprefix.eq_of_length h))
    have hdrop : u.dropLast.length < u.length := by
      cases u with
      | nil => exact False.elim (hunil rfl)
      | cons a l => simp
    have hlen := congrArg List.length heq
    omega

/-- A longest active suffix controls every one-letter extension of an active
prefix. This is the KMP summary lemma used for both fallback and completion. -/
theorem suffix_append_of_isActiveState {w : List (Digit b)} {p : F.State}
    (hp : F.IsActiveState w p) (r : F.State) (a d : Digit b)
    (h : r.1 ++ [a] <:+ w ++ [d]) :
    r.1 ++ [a] <:+ p.1 ++ [d] := by
  rcases h with ⟨z, hz⟩
  have hz' : (z ++ r.1) ++ [a] = w ++ [d] := by
    simpa only [List.append_assoc] using hz
  have hlen : (z ++ r.1).length = w.length := by
    have htotal := congrArg List.length hz'
    exact Nat.add_right_cancel (by
      simpa only [List.length_append, List.length_singleton] using htotal)
  have hsplit := List.append_inj hz' hlen
  have hrw : r.1 <:+ w := ⟨z, hsplit.1⟩
  have hrp : r.1 <:+ p.1 :=
    List.suffix_of_suffix_length_le hrw hp.1 (hp.2 r hrw)
  rcases hrp with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have had : a = d := by simpa using hsplit.2
  subst a
  simpa only [List.append_assoc] using congrArg (fun l ↦ l ++ [d]) hy

theorem activeState_append (w : List (Digit b)) (d : Digit b) :
    F.fallback (F.activeState w) d = F.activeState (w ++ [d]) := by
  apply F.isActiveState_unique
  · constructor
    · have hq := (F.activeState_spec ((F.activeState w).1 ++ [d])).1
      have hp := (F.activeState_spec w).1
      rcases hp with ⟨z, hz⟩
      apply hq.trans
      refine ⟨z, ?_⟩
      simpa only [List.append_assoc] using congrArg (fun l ↦ l ++ [d]) hz
    · intro r hr
      by_cases hrnil : r.1 = []
      · simp [hrnil]
      · let s : F.State :=
          ⟨r.1.dropLast, F.dropLast_mem_activePrefixes_of_mem r.2⟩
        let a : Digit b := r.1.getLast hrnil
        have hra : s.1 ++ [a] = r.1 := by
          exact List.dropLast_append_getLast hrnil
        have hsuffix : s.1 ++ [a] <:+ w ++ [d] := by simpa [hra] using hr
        have hcontrolled := F.suffix_append_of_isActiveState
          (F.activeState_spec w) s a d hsuffix
        exact (F.activeState_spec ((F.activeState w).1 ++ [d])).2 r
          (by simpa [hra] using hcontrolled)
  · exact F.activeState_spec (w ++ [d])

theorem completes_activeState_iff (w : List (Digit b)) (d : Digit b)
    (hw : F.Avoids w) :
    F.Completes (F.activeState w) d ↔ ¬F.Avoids (w ++ [d]) := by
  constructor
  · rintro ⟨f, hf, hsuffix⟩ havoid
    apply havoid f hf
    rcases (F.activeState_spec w).1 with ⟨z, hz⟩
    have hstateSuffix : (F.activeState w).1 ++ [d] <:+ w ++ [d] :=
      ⟨z, by
        simpa only [List.append_assoc] using congrArg (fun l ↦ l ++ [d]) hz⟩
    exact (hsuffix.trans hstateSuffix).isInfix
  · intro hnot
    by_contra hcomplete
    apply hnot
    intro f hf hinfix
    have hnew : f <:+ w ++ [d] :=
      (List.infix_concat_iff.mp hinfix).resolve_right (hw f hf)
    have hfne := F.words_nonempty f hf
    let s : F.State := ⟨f.dropLast, F.dropLast_mem_activePrefixes hf⟩
    let a : Digit b := f.getLast hfne
    have hfa : s.1 ++ [a] = f := List.dropLast_append_getLast hfne
    have hcontrolled := F.suffix_append_of_isActiveState
      (F.activeState_spec w) s a d (by simpa [hfa] using hnew)
    exact hcomplete ⟨f, hf, by simpa [hfa] using hcontrolled⟩

theorem initialState_eq_activeState : F.initialState = F.activeState [] := by
  apply F.isActiveState_unique (w := [])
  · constructor
    · simp [initialState]
    · intro r hr
      have hnil : r.1 = [] := by simpa using hr
      simp [initialState, hnil]
  · exact F.activeState_spec []

theorem step_activeState_iff (w : List (Digit b)) (d : Digit b)
    (q : F.State) (hw : F.Avoids w) :
    F.Step (F.activeState w) d q ↔
      F.Avoids (w ++ [d]) ∧ q = F.activeState (w ++ [d]) := by
  constructor
  · intro hstep
    have havoid : F.Avoids (w ++ [d]) := by
      by_contra hnot
      exact hstep.1 ((F.completes_activeState_iff w d hw).mpr hnot)
    have hfallback : F.fallback (F.activeState w) d = q :=
      (F.fallback_eq_iff_isFallback _ _ _).mpr hstep.2
    exact ⟨havoid, hfallback.symm.trans (F.activeState_append w d)⟩
  · rintro ⟨havoid, rfl⟩
    constructor
    · intro hcomplete
      exact ((F.completes_activeState_iff w d hw).mp hcomplete) havoid
    · exact (F.fallback_eq_iff_isFallback _ _ _).mp (F.activeState_append w d)

/-- Semantic invariant for paths beginning in the active state of an already
avoiding prefix. -/
theorem labelledPath_semantic (u : List (Digit b)) (hu : F.Avoids u)
    {n : ℕ} {s t : F.State} (hs : s = F.activeState u)
    (p : LabelledPath F.Step n s t) :
    F.Avoids (u ++ pathWord p) ∧
      t = F.activeState (u ++ pathWord p) := by
  induction n generalizing u s t with
  | zero =>
      obtain ⟨hst⟩ := p
      constructor
      · simpa [pathWord] using hu
      · simpa [pathWord] using hst.symm.trans hs
  | succ n ih =>
      obtain ⟨j, p, a⟩ := p
      obtain ⟨hpavoid, hj⟩ := ih u hu hs p
      have hstep : F.Step (F.activeState (u ++ pathWord p)) a.1 t := by
        rw [← hj]
        exact a.2
      have ha := (F.step_activeState_iff (u ++ pathWord p) a.1 t hpavoid).mp hstep
      simpa only [pathWord, List.append_assoc] using ha

theorem exists_path_to_activeState_of_avoids (w : List (Digit b))
    (hw : F.Avoids w) :
    ∃ p : LabelledPath F.Step w.length F.initialState (F.activeState w),
      pathWord p = w := by
  induction w using List.reverseRecOn with
  | nil =>
      exact ⟨PLift.up F.initialState_eq_activeState, rfl⟩
  | append_singleton w d ih =>
      have hw0 : F.Avoids w := by
        intro f hf hinfix
        exact hw f hf (hinfix.trans List.infix_append_left)
      obtain ⟨p, hp⟩ := ih hw0
      have hstep : F.Step (F.activeState w) d (F.activeState (w ++ [d])) :=
        (F.step_activeState_iff w d _ hw0).mpr ⟨hw, rfl⟩
      rw [List.length_append, List.length_singleton]
      refine ⟨⟨F.activeState w, p, ⟨d, hstep⟩⟩, ?_⟩
      simp [pathWord, hp]

/-- Finite paths from the empty state read exactly the words avoiding the
forbidden family. -/
theorem accepts_iff_avoids (w : List (Digit b)) :
    F.Accepts w ↔ F.Avoids w := by
  constructor
  · rintro ⟨q, p, hp⟩
    have hempty : F.Avoids [] := by
      intro f hf
      simp [F.words_nonempty f hf]
    have hsem := (F.labelledPath_semantic [] hempty
      F.initialState_eq_activeState p).1
    simpa [hp] using hsem
  · intro hw
    obtain ⟨p, hp⟩ := F.exists_path_to_activeState_of_avoids w hw
    exact ⟨F.activeState w, p, hp⟩

end ForbiddenFamily

/-! ## Compiled `011` suffix regression -/

def regression011Family : ForbiddenFamily 2 where
  base_ge_two := by omega
  words := {[(0 : Fin 2), 1, 1]}
  card_one_or_two := Or.inl (by simp)
  words_nonempty := by simp
  reduced := by simp

def regression01State : regression011Family.State :=
  ⟨[(0 : Fin 2), 1], by
    simp [ForbiddenFamily.activePrefixes, ForbiddenFamily.properPrefixes,
      regression011Family]⟩

def regression0State : regression011Family.State :=
  ⟨[(0 : Fin 2)], by
    simp [ForbiddenFamily.activePrefixes, ForbiddenFamily.properPrefixes,
      regression011Family]⟩

theorem regression011_activePrefixes :
    regression011Family.activePrefixes =
      {[], [(0 : Fin 2)], [(0 : Fin 2), 1]} := by
  decide

/-- For forbidden word `011`, state `01`, and appended digit `0`, the longest
active suffix is `0`, not `01`. -/
theorem regression_011_state01_append0 :
    regression011Family.fallback regression01State 0 = regression0State := by
  rw [regression011Family.fallback_eq_iff_isFallback]
  constructor
  · exact ⟨[0, 1], rfl⟩
  · intro r hr
    have hstates : r.1 = [] ∨ r.1 = [0] ∨ r.1 = [0, 1] := by
      have hm := r.2
      simpa only [regression011_activePrefixes, Finset.mem_insert,
        Finset.mem_singleton] using hm
    rcases hstates with hnil | hzero | hzeroOne
    · rw [hnil]
      simp [regression0State]
    · rw [hzero]
      simp [regression0State]
    · rw [hzeroOne] at hr
      exact False.elim ((by decide : ¬([(0 : Fin 2), 1] <:+ [0, 1, 0]))
        (by simpa [regression01State] using hr))

theorem regression_011_state01_append0_not_state01 :
    regression011Family.fallback regression01State 0 ≠ regression01State := by
  rw [regression_011_state01_append0]
  intro h
  have hval := congrArg Subtype.val h
  simp [regression0State, regression01State] at hval

#print axioms Theory.Shared.DigitAutomata.T24.ForbiddenFamily.fallback_eq_iff_isFallback
#print axioms Theory.Shared.DigitAutomata.T24.ForbiddenFamily.existsUnique_step_iff_not_completes
#print axioms Theory.Shared.DigitAutomata.T24.ForbiddenFamily.outgoingDigit_partition
#print axioms Theory.Shared.DigitAutomata.T24.ForbiddenFamily.labelledPath_card_eq_rationalAdjacency_pow
#print axioms Theory.Shared.DigitAutomata.T24.ForbiddenFamily.accepts_iff_avoids
#print axioms Theory.Shared.DigitAutomata.T24.regression_011_state01_append0
#print axioms Theory.Shared.DigitAutomata.T24.regression_011_state01_append0_not_state01

end Theory.Shared.DigitAutomata.T24

