import Mathlib.Computability.DFA
import Mathlib.Data.Matrix.Mul
import TheoryLib.PiPositiveLowerBlockDensity.T13T13ForbiddenLanguageEntropy

/-!
# T14: finite-state certificates for forbidden decimal words

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

Every conclusion involving pi is a necessary consequence of the literal
negation of canonical C1. Nothing here asserts that C1 fails for pi.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

namespace Theory.PiDigits.PositiveLowerBlockDensity.T14

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open Theory.PiDigits.PositiveLowerBlockDensity.T10
open Theory.PiDigits.PositiveLowerBlockDensity.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T13

abbrev DecimalDigit := Fin (10 ^ 1)

/-- The list underlying a fixed-length decimal word. -/
def wordList {n : ℕ} (w : DecimalWord n) : List DecimalDigit :=
  List.ofFn w

/-- A state records exactly which proper prefixes of the forbidden word are
currently suffixes. The empty prefix is always active. -/
def PrefixState (ell : ℕ) (hell : 0 < ell) :=
  {s : Finset (Fin ell) // (⟨0, hell⟩ : Fin ell) ∈ s}

instance (ell : ℕ) (hell : 0 < ell) : Finite (PrefixState ell hell) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance (ell : ℕ) (hell : 0 < ell) : Fintype (PrefixState ell hell) :=
  Fintype.ofFinite _

instance (ell : ℕ) (hell : 0 < ell) : DecidableEq (PrefixState ell hell) :=
  Classical.decEq _

/-- The active proper-prefix set after reading `w`. Reversal turns the suffix
condition into an ordinary prefix condition. -/
def activePrefixSet {ell : ℕ} (v : DecimalWord ell) (w : List DecimalDigit) :
    Finset (Fin ell) :=
  Finset.univ.filter fun q => ((wordList v).take q.val).reverse <+: w.reverse

theorem zero_mem_activePrefixSet {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (w : List DecimalDigit) :
    (⟨0, hell⟩ : Fin ell) ∈ activePrefixSet v w := by
  simp [activePrefixSet]

/-- The canonical proper-prefix state after reading `w`. -/
def activeState {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (w : List DecimalDigit) : PrefixState ell hell :=
  ⟨activePrefixSet v w, zero_mem_activePrefixSet hell v w⟩

/-- Reading `d` completes the forbidden word from one of the currently active
proper prefixes. -/
def completesWord {ell : ℕ} (v : DecimalWord ell) (s : Finset (Fin ell))
    (d : DecimalDigit) : Prop :=
  ∃ q ∈ s, q.val + 1 = ell ∧ d = v q

instance {ell : ℕ} (v : DecimalWord ell) (s : Finset (Fin ell))
    (d : DecimalDigit) : Decidable (completesWord v s d) :=
  Classical.propDecidable _

/-- One transition of the active-prefix subset construction. -/
def nextPrefixSet {ell : ℕ} (v : DecimalWord ell) (s : Finset (Fin ell))
    (d : DecimalDigit) : Finset (Fin ell) :=
  Finset.univ.filter fun q =>
    q.val = 0 ∨ ∃ p ∈ s, q.val = p.val + 1 ∧ d = v p

theorem zero_mem_nextPrefixSet {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (s : Finset (Fin ell)) (d : DecimalDigit) :
    (⟨0, hell⟩ : Fin ell) ∈ nextPrefixSet v s d := by
  simp [nextPrefixSet]

/-- The deterministic successor state, defined only when the new digit does
not complete the forbidden word. -/
def nextState {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (s : PrefixState ell hell) (d : DecimalDigit) : PrefixState ell hell :=
  ⟨nextPrefixSet v s.1 d, zero_mem_nextPrefixSet hell v s.1 d⟩

/-- The partial transition relation of the proper-prefix automaton. -/
def PrefixStep {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (s : PrefixState ell hell) (d : DecimalDigit)
    (t : PrefixState ell hell) : Prop :=
  ¬completesWord v s.1 d ∧ t = nextState hell v s d

instance {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (s : PrefixState ell hell) (d : DecimalDigit) (t : PrefixState ell hell) :
    Decidable (PrefixStep hell v s d t) := Classical.propDecidable _

/-- Empty-prefix initial state. -/
def initialState {ell : ℕ} (hell : 0 < ell) : PrefixState ell hell :=
  ⟨{⟨0, hell⟩}, by simp⟩

/-- Generic finite labelled paths. This recursive sigma presentation makes
the matrix-power count transparent. -/
def LabelledPath {α σ : Type} (step : σ → α → σ → Prop) :
    ℕ → σ → σ → Type
  | 0, i, j => PLift (i = j)
  | n + 1, i, k => Σ j : σ, LabelledPath step n i j × {a : α // step j a k}

/-- The labels read along a path, in chronological order. -/
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

def castLabelledPath {α σ : Type} {step : σ → α → σ → Prop}
    {m n : ℕ} (h : m = n) {i j : σ} (p : LabelledPath step m i j) :
    LabelledPath step n i j := h ▸ p

theorem pathWord_castLabelledPath {α σ : Type}
    {step : σ → α → σ → Prop} {m n : ℕ} (h : m = n) {i j : σ}
    (p : LabelledPath step m i j) :
    pathWord (castLabelledPath h p) = pathWord p := by
  subst n
  rfl

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

/-- The nonnegative transition-count matrix. -/
def transitionCountMatrix {α σ : Type*} [Fintype α]
    (step : σ → α → σ → Prop) : Matrix σ σ ℕ :=
  fun i j => Nat.card {a : α // step i a j}

/-- The transition-count matrix of the proper-prefix forbidden-word
automaton. -/
def forbiddenTransitionMatrix {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) : Matrix (PrefixState ell hell) (PrefixState ell hell) ℕ :=
  transitionCountMatrix (PrefixStep hell v)

/-- Matrix powers count finite labelled paths between two states. -/
theorem labelledPath_card_eq_matrix_pow {α σ : Type} [Fintype α]
    [Fintype σ] [DecidableEq σ] (step : σ → α → σ → Prop)
    (n : ℕ) (i j : σ) :
    Nat.card (LabelledPath step n i j) =
      (transitionCountMatrix step ^ n) i j := by
  induction n generalizing j with
  | zero =>
      by_cases h : i = j
      · subst j
        simp [LabelledPath]
      · simp [LabelledPath, h]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl, pow_succ, Matrix.mul_apply]
      simp only [LabelledPath, Nat.card_sigma, Nat.card_prod]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [ih]
      rfl

/-- Summing over terminal states gives the row sum of the matrix power. -/
theorem labelledPath_rowSum_eq_matrix_pow {α σ : Type} [Fintype α]
    [Fintype σ] [DecidableEq σ] (step : σ → α → σ → Prop)
    (n : ℕ) (i : σ) :
    Nat.card (Σ j : σ, LabelledPath step n i j) =
      ∑ j : σ, (transitionCountMatrix step ^ n) i j := by
  rw [Nat.card_sigma]
  exact Finset.sum_congr rfl fun j _ => labelledPath_card_eq_matrix_pow step n i j

theorem forbiddenAutomaton_path_count {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (n : ℕ) :
    Nat.card (Σ j : PrefixState ell hell,
        LabelledPath (PrefixStep hell v) n (initialState hell) j) =
      ∑ j : PrefixState ell hell,
        (forbiddenTransitionMatrix hell v ^ n) (initialState hell) j :=
  labelledPath_rowSum_eq_matrix_pow (PrefixStep hell v) n (initialState hell)

theorem activePrefixSet_append {ell : ℕ} (v : DecimalWord ell)
    (w : List DecimalDigit) (d : DecimalDigit) :
    activePrefixSet v (w ++ [d]) =
      nextPrefixSet v (activePrefixSet v w) d := by
  classical
  ext q
  simp only [activePrefixSet, nextPrefixSet, Finset.mem_filter,
    Finset.mem_univ, true_and, List.reverse_append, List.reverse_singleton,
    List.singleton_append]
  by_cases hq : q.val = 0
  · simp [hq]
  · let p : Fin ell := ⟨q.val - 1,
      lt_of_le_of_lt (Nat.sub_le q.val 1) q.isLt⟩
    have hqp : q.val = p.val + 1 := by simp [p]; omega
    have hpList : p.val < (wordList v).length := by
      simpa only [wordList, List.length_ofFn] using p.isLt
    rw [hqp, ← List.take_append_getElem hpList, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.cons_prefix_cons]
    have hget : (wordList v)[p.val] = v p := by
      simp [wordList, p]
    rw [hget]
    constructor
    · rintro ⟨hd, hsuffix⟩
      right
      exact ⟨p, hsuffix, rfl, hd.symm⟩
    · rintro (hzero | ⟨p', hp', hq', hd⟩)
      · omega
      · have hpp : p' = p := by
          apply Fin.ext
          exact (Nat.succ.inj hq').symm
        subst p'
        exact ⟨hd.symm, hp'⟩

/-- Completion in the active-prefix state is exactly a new suffix occurrence
of the forbidden word. -/
theorem completesWord_activePrefixSet_iff {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (w : List DecimalDigit) (d : DecimalDigit) :
    completesWord v (activePrefixSet v w) d ↔
      wordList v <:+ w ++ [d] := by
  classical
  constructor
  · rintro ⟨q, hq, hlast, hd⟩
    have hactive : ((wordList v).take q.val).reverse <+: w.reverse := by
      simpa [activePrefixSet] using hq
    have hqList : q.val < (wordList v).length := by
      simpa only [wordList, List.length_ofFn] using q.isLt
    have hwhole : (wordList v).take q.val ++ [(wordList v)[q.val]] =
        wordList v := by
      rw [List.take_append_getElem hqList]
      apply List.take_of_length_le
      simp only [wordList, List.length_ofFn]
      omega
    have hget : (wordList v)[q.val] = v q := by simp [wordList]
    rw [hget] at hwhole
    apply List.reverse_prefix.mp
    rw [← hwhole, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    exact List.cons_prefix_cons.mpr ⟨hd.symm, hactive⟩
  · intro hsuffix
    let q : Fin ell := ⟨ell - 1, by omega⟩
    have hqList : q.val < (wordList v).length := by
      simpa only [wordList, List.length_ofFn] using q.isLt
    have hwhole : (wordList v).take q.val ++ [(wordList v)[q.val]] =
        wordList v := by
      rw [List.take_append_getElem hqList]
      apply List.take_of_length_le
      simp only [wordList, List.length_ofFn]
      simp only [q]
      omega
    have hget : (wordList v)[q.val] = v q := by simp [wordList]
    rw [hget] at hwhole
    have hrev : (wordList v).reverse <+: (w ++ [d]).reverse :=
      List.reverse_prefix.mpr hsuffix
    rw [← hwhole, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_prefix_cons] at hrev
    refine ⟨q, ?_, by simp [q]; omega, hrev.1.symm⟩
    simpa [activePrefixSet] using hrev.2

theorem initialState_eq_activeState {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) : initialState hell = activeState hell v [] := by
  apply Subtype.ext
  ext q
  simp [initialState, activeState, activePrefixSet, wordList, Fin.ext_iff,
    hell.ne']

theorem nextState_activeState {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (w : List DecimalDigit) (d : DecimalDigit) :
    nextState hell v (activeState hell v w) d =
      activeState hell v (w ++ [d]) := by
  apply Subtype.ext
  exact (activePrefixSet_append v w d).symm

/-- One-step semantic correctness of the proper-prefix automaton. -/
theorem prefixStep_activeState_iff {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (w : List DecimalDigit) (d : DecimalDigit)
    (t : PrefixState ell hell) :
    PrefixStep hell v (activeState hell v w) d t ↔
      ¬wordList v <:+ w ++ [d] ∧ t = activeState hell v (w ++ [d]) := by
  change (¬completesWord v (activePrefixSet v w) d ∧
      t = nextState hell v (activeState hell v w) d) ↔ _
  rw [completesWord_activePrefixSet_iff hell v w d,
    nextState_activeState]

theorem infix_append_singleton_iff {α : Type*} {u w : List α} {d : α}
    (hu : u ≠ []) :
    u <:+: w ++ [d] ↔ u <:+: w ∨ u <:+ w ++ [d] := by
  constructor
  · intro h
    by_cases hsuffix : u <:+ w ++ [d]
    · exact Or.inr hsuffix
    · left
      obtain ⟨a, b, hab⟩ := h
      have hb : b ≠ [] := by
        intro hnil
        subst b
        apply hsuffix
        exact ⟨a, by simpa using hab⟩
      refine ⟨a, b.dropLast, ?_⟩
      have hdrop := congrArg List.dropLast hab
      simpa [List.dropLast_append, hb, hu] using hdrop
  · rintro (hinfix | hsuffix)
    · exact hinfix.trans List.infix_append_left
    · exact hsuffix.isInfix

/-- Acceptance means that a labelled path exists from the empty-prefix state
whose labels are exactly the supplied word. -/
def ProperPrefixAutomatonAccepts {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (w : List DecimalDigit) : Prop :=
  ∃ t : PrefixState ell hell,
    ∃ p : LabelledPath (PrefixStep hell v) w.length (initialState hell) t,
      pathWord p = w

/-- Semantic invariant for every labelled path: its endpoint is the active
proper-prefix set of the accumulated labels, and no forbidden occurrence was
created. -/
theorem labelledPath_semantic {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (u : List DecimalDigit)
    (hu : ¬wordList v <:+: u) {n : ℕ} {s t : PrefixState ell hell}
    (hs : s = activeState hell v u)
    (p : LabelledPath (PrefixStep hell v) n s t) :
    ¬wordList v <:+: u ++ pathWord p ∧
      t = activeState hell v (u ++ pathWord p) := by
  induction n generalizing u s t with
  | zero =>
      obtain ⟨ht⟩ := p
      constructor
      · simpa [pathWord] using hu
      · simpa [pathWord] using ht.symm.trans hs
  | succ n ih =>
      obtain ⟨j, p, a⟩ := p
      obtain ⟨hpavoid, hj⟩ := ih u hu hs p
      have haStep : PrefixStep hell v (activeState hell v (u ++ pathWord p))
          a.1 t := by
        rw [← hj]
        exact a.2
      have ha := (prefixStep_activeState_iff hell v
        (u ++ pathWord p) a.1 t).mp haStep
      have havoid : ¬wordList v <:+: (u ++ pathWord p) ++ [a.1] := by
        intro hinfix
        rw [infix_append_singleton_iff (by simp [wordList, hell.ne'])] at hinfix
        exact hinfix.elim hpavoid ha.1
      simpa only [pathWord, List.append_assoc] using And.intro havoid ha.2

theorem exists_path_to_activeState_of_not_infix {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (w : List DecimalDigit)
    (hw : ¬wordList v <:+: w) :
    ∃ p : LabelledPath (PrefixStep hell v) w.length (initialState hell)
        (activeState hell v w), pathWord p = w := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨PLift.up (initialState_eq_activeState hell v), rfl⟩
  | append_singleton w d ih =>
      have hvne : wordList v ≠ [] := by simp [wordList, hell.ne']
      have hparts := (not_or.mp (mt (infix_append_singleton_iff hvne).mpr hw))
      obtain ⟨p, hpword⟩ := ih hparts.1
      have hstep : PrefixStep hell v (activeState hell v w) d
          (activeState hell v (w ++ [d])) :=
        (prefixStep_activeState_iff hell v w d _).mpr ⟨hparts.2, rfl⟩
      rw [List.length_append, List.length_singleton]
      refine ⟨⟨activeState hell v w, (p, ⟨d, hstep⟩)⟩, ?_⟩
      simp [pathWord, hpword]

/-- The proper-prefix automaton accepts exactly the words with no contiguous
copy of `v`. -/
theorem properPrefixAutomaton_accepts_iff_not_infix {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) (w : List DecimalDigit) :
    ProperPrefixAutomatonAccepts hell v w ↔ ¬wordList v <:+: w := by
  constructor
  · rintro ⟨t, p, hpword⟩
    have hnil : ¬wordList v <:+: ([] : List DecimalDigit) := by
      simp [wordList, hell.ne']
    have hsem := (labelledPath_semantic hell v [] hnil
      (initialState_eq_activeState hell v) p).1
    rw [hpword] at hsem
    simpa using hsem
  · intro hw
    obtain ⟨p, hp⟩ := exists_path_to_activeState_of_not_infix hell v w hw
    exact ⟨activeState hell v w, p, hp⟩

/-- T12's indexed occurrence predicate is exactly ordinary list infix. -/
theorem exists_occursAt_iff_list_infix {ell n : ℕ}
    (v : DecimalWord ell) (w : DecimalWord n) :
    (∃ r : ℕ, OccursAt v w r) ↔ wordList v <:+: wordList w := by
  constructor
  · rintro ⟨r, hrange, hmatch⟩
    have hmid : ((wordList w).drop r).take ell = wordList v := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, wordList,
          List.length_ofFn]
        omega
      · intro j hj₁ hj₂
        rw [List.getElem_take, List.getElem_drop]
        simpa only [wordList, List.getElem_ofFn] using
          hmatch (⟨j, by simpa [wordList] using hj₂⟩ : Fin ell)
    refine ⟨(wordList w).take r, (wordList w).drop (r + ell), ?_⟩
    rw [← hmid, List.append_assoc, List.drop_take_append_drop,
      List.take_append_drop]
  · rintro ⟨a, b, hab⟩
    refine ⟨a.length, ?_, ?_⟩
    · have hlen := congrArg List.length hab
      simp only [List.length_append, wordList, List.length_ofFn] at hlen
      omega
    · intro j
      have hindex : a.length + j.val < (wordList w).length := by
        simp only [wordList, List.length_ofFn]
        have hlen := congrArg List.length hab
        simp only [List.length_append, wordList, List.length_ofFn] at hlen
        omega
      have hjList : j.val < (wordList v).length := by
        simpa only [wordList, List.length_ofFn] using j.isLt
      have hget : (wordList w)[a.length + j.val] =
          (wordList v)[j.val]'hjList := by
        have hindexA : a.length + j.val <
            (a ++ wordList v ++ b).length := by
          simp only [List.length_append, wordList, List.length_ofFn]
          omega
        have hleft : (a ++ wordList v ++ b)[a.length + j.val]'hindexA =
            (wordList v)[j.val]'hjList := by
          simp [hjList]
        have hopt := congrArg
          (fun L : List DecimalDigit => L[a.length + j.val]?) hab
        change (a ++ wordList v ++ b)[a.length + j.val]? =
          (wordList w)[a.length + j.val]? at hopt
        rw [List.getElem?_eq_getElem hindexA,
          List.getElem?_eq_getElem hindex] at hopt
        exact (Option.some.inj hopt).symm.trans hleft
      simpa only [wordList, List.getElem_ofFn] using hget

/-- Named automaton-language equivalence with T13's exact finite language. -/
theorem properPrefixAutomaton_language_equivalence {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) {n : ℕ} (w : DecimalWord n) :
    ProperPrefixAutomatonAccepts hell v (wordList w) ↔
      ∀ r : Fin (n + 1), ¬OccursAt v w r.val := by
  rw [properPrefixAutomaton_accepts_iff_not_infix]
  constructor
  · intro havoid r hocc
    exact havoid ((exists_occursAt_iff_list_infix v w).mp ⟨r.val, hocc⟩)
  · intro havoid hinfix
    obtain ⟨r, hocc⟩ := (exists_occursAt_iff_list_infix v w).mpr hinfix
    have hr : r < n + 1 := by
      obtain ⟨hrange, _⟩ := hocc
      omega
    exact havoid ⟨r, hr⟩ hocc

theorem prefixStep_right_unique {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (s : PrefixState ell hell) (d : DecimalDigit)
    {t u : PrefixState ell hell} (ht : PrefixStep hell v s d t)
    (hu : PrefixStep hell v s d u) : t = u := by
  rw [ht.2, hu.2]

/-- For a deterministic partial automaton, the label word uniquely determines
the complete path, including its terminal state. -/
theorem fullPath_word_injective {α σ : Type} [Fintype α] [Fintype σ]
    (step : σ → α → σ → Prop)
    (hdet : ∀ s a t u, step s a t → step s a u → t = u)
    (n : ℕ) (i : σ) :
    Function.Injective (fun p : Σ j : σ, LabelledPath step n i j =>
      pathWord p.2) := by
  induction n with
  | zero =>
      rintro ⟨j, p⟩ ⟨k, q⟩ _
      obtain ⟨hj⟩ := p
      obtain ⟨hk⟩ := q
      subst j
      subst k
      rfl
  | succ n ih =>
      rintro ⟨k, j, p, a⟩ ⟨k', j', q, b⟩ hword
      have hsplit := List.append_inj hword
        ((pathWord_length p).trans (pathWord_length q).symm)
      have hpq : (⟨j, p⟩ : Σ z : σ, LabelledPath step n i z) = ⟨j', q⟩ :=
        ih hsplit.1
      cases hpq
      have hab : a.1 = b.1 := by simpa using hsplit.2
      have hkk : k = k' := hdet j a.1 k k' a.2 (by simpa [hab] using b.2)
      subst k'
      have hab' : a = b := Subtype.ext hab
      subst b
      rfl

/-- Turn a list of known length back into T12's fixed-length word. -/
def listToWord {n : ℕ} (w : List DecimalDigit) (hw : w.length = n) :
    DecimalWord n := fun i => w.get ⟨i.val, by omega⟩

theorem wordList_listToWord {n : ℕ} (w : List DecimalDigit)
    (hw : w.length = n) : wordList (listToWord w hw) = w := by
  apply List.ext_getElem
  · simp [wordList, hw]
  · intro i hi₁ hi₂
    simp [wordList, listToWord]

/-- A complete automaton path canonically yields a member of T13's exact
forbidden language. -/
def pathToForbiddenWord {ell n : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell)
    (p : Σ j : PrefixState ell hell,
      LabelledPath (PrefixStep hell v) n (initialState hell) j) :
    ForbiddenLanguage v n := by
  let w : DecimalWord n := listToWord (pathWord p.2) (pathWord_length p.2)
  refine ⟨w, ?_⟩
  rw [← properPrefixAutomaton_language_equivalence hell v w]
  change ProperPrefixAutomatonAccepts hell v
    (wordList (listToWord (pathWord p.2) (pathWord_length p.2)))
  rw [wordList_listToWord]
  unfold ProperPrefixAutomatonAccepts
  rw [pathWord_length]
  exact ⟨p.1, p.2, rfl⟩

theorem pathToForbiddenWord_bijective {ell n : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) :
    Function.Bijective (pathToForbiddenWord hell v :
      (Σ j : PrefixState ell hell,
        LabelledPath (PrefixStep hell v) n (initialState hell) j) →
          ForbiddenLanguage v n) := by
  constructor
  · intro p q hpq
    apply fullPath_word_injective (PrefixStep hell v)
      (fun s d t u => prefixStep_right_unique hell v s d) n (initialState hell)
    have hword := congrArg (fun z : ForbiddenLanguage v n => wordList z.1) hpq
    simpa only [pathToForbiddenWord, wordList_listToWord] using hword
  · intro w
    have haccept : ProperPrefixAutomatonAccepts hell v (wordList w.1) :=
      (properPrefixAutomaton_language_equivalence hell v w.1).mpr w.2
    obtain ⟨t, p, hp⟩ := haccept
    have hlen : (wordList w.1).length = n := by simp [wordList]
    let p' := castLabelledPath hlen p
    have hp' : pathWord p' = wordList w.1 :=
      (pathWord_castLabelledPath hlen p).trans hp
    refine ⟨⟨t, p'⟩, ?_⟩
    apply Subtype.ext
    apply List.ofFn_injective
    change wordList (listToWord (pathWord p') (pathWord_length p')) = wordList w.1
    rw [wordList_listToWord]
    exact hp'

/-- T13's forbidden-word count is the empty-state row sum of the `n`th matrix
power. -/
theorem forbiddenWordCount_eq_matrix_rowSum {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (n : ℕ) :
    forbiddenWordCount v n =
      ∑ j : PrefixState ell hell,
        (forbiddenTransitionMatrix hell v ^ n) (initialState hell) j := by
  rw [forbiddenWordCount]
  calc
    Nat.card (ForbiddenLanguage v n) =
        Nat.card (Σ j : PrefixState ell hell,
          LabelledPath (PrefixStep hell v) n (initialState hell) j) :=
      (Nat.card_congr (Equiv.ofBijective (pathToForbiddenWord hell v)
        (pathToForbiddenWord_bijective hell v))).symm
    _ = _ := forbiddenAutomaton_path_count hell v n

/-- Iterating a coordinatewise weighted supersolution bounds every weighted
row of every matrix power. -/
theorem weightedMatrixPower_bound {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : Matrix σ σ ℕ) (x : σ → ℚ) (lambda : ℚ)
    (hlambda : 0 ≤ lambda)
    (hcert : ∀ i, ∑ j : σ, (M i j : ℚ) * x j ≤ lambda * x i)
    (n : ℕ) (i : σ) :
    ∑ j : σ, ((M ^ n) i j : ℚ) * x j ≤ lambda ^ n * x i := by
  induction n generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
      calc
        ∑ j : σ, ((M ^ (n + 1)) i j : ℚ) * x j =
            ∑ k : σ, (M i k : ℚ) *
              (∑ j : σ, ((M ^ n) k j : ℚ) * x j) := by
          rw [pow_succ']
          simp only [Matrix.mul_apply, Nat.cast_sum, Nat.cast_mul]
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring
        _ ≤ ∑ k : σ, (M i k : ℚ) * (lambda ^ n * x k) := by
          apply Finset.sum_le_sum
          intro k _hk
          exact mul_le_mul_of_nonneg_left (ih k) (by positivity)
        _ = lambda ^ n * (∑ k : σ, (M i k : ℚ) * x k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
        _ ≤ lambda ^ n * (lambda * x i) :=
          mul_le_mul_of_nonneg_left (hcert i) (pow_nonneg hlambda n)
        _ = lambda ^ (n + 1) * x i := by rw [pow_succ]; ring

theorem forbiddenWordCount_weighted_bound {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (x : PrefixState ell hell → ℚ) (lambda : ℚ)
    (hlambda : 0 ≤ lambda) (hx : ∀ i, 1 ≤ x i)
    (hcert : ∀ i, ∑ j : PrefixState ell hell,
      (forbiddenTransitionMatrix hell v i j : ℚ) * x j ≤ lambda * x i)
    (n : ℕ) :
    (forbiddenWordCount v n : ℚ) ≤ lambda ^ n * x (initialState hell) := by
  rw [forbiddenWordCount_eq_matrix_rowSum hell v n]
  push_cast
  calc
    ∑ j : PrefixState ell hell,
        ((forbiddenTransitionMatrix hell v ^ n) (initialState hell) j : ℚ) ≤
        ∑ j : PrefixState ell hell,
          ((forbiddenTransitionMatrix hell v ^ n) (initialState hell) j : ℚ) *
            x j := by
      apply Finset.sum_le_sum
      intro j _hj
      nth_rw 1 [← mul_one
        ((forbiddenTransitionMatrix hell v ^ n) (initialState hell) j : ℚ)]
      exact mul_le_mul_of_nonneg_left (hx j) (by positivity)
    _ ≤ lambda ^ n * x (initialState hell) :=
      weightedMatrixPower_bound (forbiddenTransitionMatrix hell v) x lambda
        hlambda hcert n (initialState hell)

/-- A rational weighted supersolution normalized by `1 ≤ x` certifies the
logarithmic entropy bound. In particular, this normalization makes every
coordinate positive. -/
theorem weighted_entropy_certificate {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (x : PrefixState ell hell → ℚ) (lambda : ℚ)
    (hlambda : 1 ≤ lambda) (hx : ∀ i, 1 ≤ x i)
    (hcert : ∀ i, ∑ j : PrefixState ell hell,
      (forbiddenTransitionMatrix hell v i j : ℚ) * x j ≤ lambda * x i) :
    forbiddenEntropy v ≤ Real.log (lambda : ℝ) := by
  have hratio (n : ℕ) (hn : 0 < n) :
      forbiddenLogRatio v n ≤
        Real.log (lambda : ℝ) +
          Real.log (x (initialState hell) : ℝ) / (n : ℝ) := by
    have hcountQ := forbiddenWordCount_weighted_bound hell v x lambda
      (zero_le_one.trans hlambda) hx hcert n
    have hcount : (forbiddenWordCount v n : ℝ) ≤
        (lambda : ℝ) ^ n * (x (initialState hell) : ℝ) := by
      exact_mod_cast hcountQ
    have hcountPos : (0 : ℝ) < forbiddenWordCount v n := by
      exact_mod_cast forbiddenWordCount_pos v hell n
    have hlambdaPosQ : (0 : ℚ) < lambda := lt_of_lt_of_le zero_lt_one hlambda
    have hxPosQ : (0 : ℚ) < x (initialState hell) :=
      lt_of_lt_of_le zero_lt_one (hx _)
    have hlog : Real.log (forbiddenWordCount v n : ℝ) ≤
        Real.log ((lambda : ℝ) ^ n * (x (initialState hell) : ℝ)) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr hcountPos
      · exact Set.mem_Ioi.mpr (mul_pos (pow_pos (by exact_mod_cast hlambdaPosQ) n)
          (by exact_mod_cast hxPosQ))
      · exact hcount
    rw [Real.log_mul (pow_ne_zero n (by exact_mod_cast hlambdaPosQ.ne'))
      (by exact_mod_cast hxPosQ.ne'), Real.log_pow] at hlog
    unfold forbiddenLogRatio
    calc
      Real.log (forbiddenWordCount v n : ℝ) / (n : ℝ) ≤
          ((n : ℝ) * Real.log (lambda : ℝ) +
            Real.log (x (initialState hell) : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
      _ = Real.log (lambda : ℝ) +
          Real.log (x (initialState hell) : ℝ) / (n : ℝ) := by
        field_simp
  have htend : Tendsto (fun n : ℕ =>
      Real.log (lambda : ℝ) +
        Real.log (x (initialState hell) : ℝ) / (n : ℝ)) atTop
      (𝓝 (Real.log (lambda : ℝ))) := by
    have hdiv : Tendsto (fun n : ℕ =>
        Real.log (x (initialState hell) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add hdiv
  apply le_of_tendsto_of_tendsto (forbiddenLogRatio_tendsto_entropy v hell) htend
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hratio n hn

def zeroZeroWord : DecimalWord 2 := fun _ => 0

theorem zeroZeroLength_pos : 0 < 2 := by omega

def zeroZeroEmptyState : PrefixState 2 zeroZeroLength_pos :=
  ⟨{⟨0, by omega⟩}, by simp⟩

def zeroZeroZeroState : PrefixState 2 zeroZeroLength_pos :=
  ⟨Finset.univ, by simp⟩

def zeroZeroOne : Fin 2 := ⟨1, by omega⟩

theorem zeroZero_state_ext {s t : PrefixState 2 zeroZeroLength_pos}
    (h : zeroZeroOne ∈ s.1 ↔ zeroZeroOne ∈ t.1) : s = t := by
  apply Subtype.ext
  ext q
  fin_cases q
  · exact iff_of_true s.2 t.2
  · simpa [zeroZeroOne] using h

theorem zeroZero_state_ne {s t : PrefixState 2 zeroZeroLength_pos}
    (h : ¬(zeroZeroOne ∈ s.1 ↔ zeroZeroOne ∈ t.1)) : s ≠ t := by
  intro hst
  apply h
  rw [hst]

theorem zeroZero_states (s : PrefixState 2 zeroZeroLength_pos) :
    s = zeroZeroEmptyState ∨ s = zeroZeroZeroState := by
  by_cases h : (⟨1, by omega⟩ : Fin 2) ∈ s.1
  · right
    apply Subtype.ext
    ext q
    fin_cases q
    · simpa [zeroZeroZeroState] using s.2
    · simpa [zeroZeroZeroState] using h
  · left
    apply Subtype.ext
    ext q
    fin_cases q
    · simpa [zeroZeroEmptyState] using s.2
    · simpa [zeroZeroEmptyState] using h

theorem zeroZero_states_ne : zeroZeroEmptyState ≠ zeroZeroZeroState := by
  intro h
  have hm := congrArg
    (fun s : PrefixState 2 zeroZeroLength_pos =>
      (⟨1, by omega⟩ : Fin 2) ∈ s.1) h
  simpa [zeroZeroEmptyState, zeroZeroZeroState] using hm

@[simp] theorem zeroZero_eq_empty_iff
    (s : PrefixState 2 zeroZeroLength_pos) :
    s = zeroZeroEmptyState ↔ (⟨1, by omega⟩ : Fin 2) ∉ s.1 := by
  constructor
  · rintro rfl
    simp [zeroZeroEmptyState]
  · intro h
    exact (zeroZero_states s).resolve_right fun hs => by
      subst s
      simpa [zeroZeroZeroState] using h

@[simp] theorem zeroZero_empty_eq_iff
    (s : PrefixState 2 zeroZeroLength_pos) :
    zeroZeroEmptyState = s ↔ (⟨1, by omega⟩ : Fin 2) ∉ s.1 := by
  rw [eq_comm, zeroZero_eq_empty_iff]

@[simp] theorem zeroZero_eq_zero_iff
    (s : PrefixState 2 zeroZeroLength_pos) :
    s = zeroZeroZeroState ↔ (⟨1, by omega⟩ : Fin 2) ∈ s.1 := by
  constructor
  · rintro rfl
    simp [zeroZeroZeroState]
  · intro h
    exact (zeroZero_states s).resolve_left fun hs => by
      subst s
      simpa [zeroZeroEmptyState] using h

@[simp] theorem zeroZero_zero_eq_iff
    (s : PrefixState 2 zeroZeroLength_pos) :
    zeroZeroZeroState = s ↔ (⟨1, by omega⟩ : Fin 2) ∈ s.1 := by
  rw [eq_comm, zeroZero_eq_zero_iff]

theorem zeroZero_step_empty_empty (d : DecimalDigit) :
    PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroEmptyState d
      zeroZeroEmptyState ↔ d ≠ 0 := by
  fin_cases d <;> norm_num [PrefixStep, completesWord, nextState,
    nextPrefixSet, zeroZeroWord, zeroZeroEmptyState,
    zeroZero_eq_empty_iff, zeroZero_empty_eq_iff]
  all_goals
    first
    | exact zeroZero_state_ext (by simp [zeroZeroOne])
    | exact zeroZero_state_ne (by simp [zeroZeroOne])

theorem zeroZero_step_empty_zero (d : DecimalDigit) :
    PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroEmptyState d
      zeroZeroZeroState ↔ d = 0 := by
  fin_cases d <;> norm_num [PrefixStep, completesWord, nextState,
    nextPrefixSet, zeroZeroWord, zeroZeroEmptyState, zeroZeroZeroState,
    zeroZero_eq_zero_iff, zeroZero_zero_eq_iff]
  all_goals
    first
    | exact zeroZero_state_ext (by simp [zeroZeroOne])
    | exact zeroZero_state_ne (by simp [zeroZeroOne])

theorem zeroZero_step_zero_empty (d : DecimalDigit) :
    PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroZeroState d
      zeroZeroEmptyState ↔ d ≠ 0 := by
  fin_cases d <;> norm_num [PrefixStep, completesWord, nextState,
    nextPrefixSet, zeroZeroWord, zeroZeroEmptyState, zeroZeroZeroState,
    zeroZero_eq_empty_iff, zeroZero_empty_eq_iff]
  all_goals exact zeroZero_state_ext (by simp [zeroZeroOne])

theorem zeroZero_step_zero_zero (d : DecimalDigit) :
    ¬PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroZeroState d
      zeroZeroZeroState := by
  fin_cases d <;> norm_num [PrefixStep, completesWord, nextState,
    nextPrefixSet, zeroZeroWord, zeroZeroEmptyState, zeroZeroZeroState,
    zeroZero_eq_zero_iff, zeroZero_zero_eq_iff]
  all_goals
    first
    | exact zeroZero_state_ext (by simp [zeroZeroOne])
    | exact zeroZero_state_ne (by simp [zeroZeroOne])

theorem natCard_subtype_congr_iff {α : Type*} [Finite α]
    (p q : α → Prop) (h : ∀ a, p a ↔ q a) :
    Nat.card {a : α // p a} = Nat.card {a : α // q a} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl α) h)

theorem decimalDigit_ne_zero_card :
    Nat.card {d : DecimalDigit // d ≠ 0} = 9 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  norm_num

@[simp] theorem zeroZero_matrix_empty_empty :
    forbiddenTransitionMatrix zeroZeroLength_pos zeroZeroWord
      zeroZeroEmptyState zeroZeroEmptyState = 9 := by
  unfold forbiddenTransitionMatrix transitionCountMatrix
  calc
    Nat.card {d : DecimalDigit //
        PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroEmptyState d
          zeroZeroEmptyState} =
        Nat.card {d : DecimalDigit // d ≠ 0} :=
      natCard_subtype_congr_iff _ _ zeroZero_step_empty_empty
    _ = 9 := decimalDigit_ne_zero_card

@[simp] theorem zeroZero_matrix_empty_zero :
    forbiddenTransitionMatrix zeroZeroLength_pos zeroZeroWord
      zeroZeroEmptyState zeroZeroZeroState = 1 := by
  unfold forbiddenTransitionMatrix transitionCountMatrix
  calc
    Nat.card {d : DecimalDigit //
        PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroEmptyState d
          zeroZeroZeroState} =
        Nat.card {d : DecimalDigit // d = 0} :=
      natCard_subtype_congr_iff _ _ zeroZero_step_empty_zero
    _ = 1 := by simp

@[simp] theorem zeroZero_matrix_zero_empty :
    forbiddenTransitionMatrix zeroZeroLength_pos zeroZeroWord
      zeroZeroZeroState zeroZeroEmptyState = 9 := by
  unfold forbiddenTransitionMatrix transitionCountMatrix
  calc
    Nat.card {d : DecimalDigit //
        PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroZeroState d
          zeroZeroEmptyState} =
        Nat.card {d : DecimalDigit // d ≠ 0} :=
      natCard_subtype_congr_iff _ _ zeroZero_step_zero_empty
    _ = 9 := decimalDigit_ne_zero_card

@[simp] theorem zeroZero_matrix_zero_zero :
    forbiddenTransitionMatrix zeroZeroLength_pos zeroZeroWord
      zeroZeroZeroState zeroZeroZeroState = 0 := by
  unfold forbiddenTransitionMatrix transitionCountMatrix
  have hiff (d : DecimalDigit) :
      PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroZeroState d
        zeroZeroZeroState ↔ False := iff_false_intro (zeroZero_step_zero_zero d)
  calc
    Nat.card {d : DecimalDigit //
        PrefixStep zeroZeroLength_pos zeroZeroWord zeroZeroZeroState d
          zeroZeroZeroState} =
        Nat.card {d : DecimalDigit // False} :=
      natCard_subtype_congr_iff _ _ hiff
    _ = 0 := by simp

def zeroZeroWeight (s : PrefixState 2 zeroZeroLength_pos) : ℚ :=
  if s = zeroZeroEmptyState then 100 else 91

theorem zeroZero_state_univ :
    (Finset.univ : Finset (PrefixState 2 zeroZeroLength_pos)) =
      {zeroZeroEmptyState, zeroZeroZeroState} := by
  ext s
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact zeroZero_states s

theorem zeroZero_sum (f : PrefixState 2 zeroZeroLength_pos → ℕ) :
    ∑ s, f s = f zeroZeroEmptyState + f zeroZeroZeroState := by
  rw [zeroZero_state_univ]
  have hmem : zeroZeroEmptyState ∉ ({zeroZeroZeroState} :
      Finset (PrefixState 2 zeroZeroLength_pos)) := by
    simpa only [Finset.mem_singleton] using zeroZero_states_ne
  rw [Finset.sum_insert hmem, Finset.sum_singleton]

theorem zeroZero_initialState :
    initialState zeroZeroLength_pos = zeroZeroEmptyState := by
  apply zeroZero_state_ext
  simp [initialState, zeroZeroEmptyState, zeroZeroOne]

theorem zeroZero_weight_ge_one
    (s : PrefixState 2 zeroZeroLength_pos) : 1 ≤ zeroZeroWeight s := by
  unfold zeroZeroWeight
  split <;> norm_num

/-- Exact rational certificate for the matrix `[[9,1],[9,0]]`: the positive
weight vector `(100,91)` is sent coordinatewise below `991/100` times itself. -/
theorem zeroZero_weighted_matrix_certificate
    (s : PrefixState 2 zeroZeroLength_pos) :
    ∑ t : PrefixState 2 zeroZeroLength_pos,
        (forbiddenTransitionMatrix zeroZeroLength_pos zeroZeroWord s t : ℚ) *
          zeroZeroWeight t ≤ (991 / 100 : ℚ) * zeroZeroWeight s := by
  rw [zeroZero_state_univ]
  have hmem : zeroZeroEmptyState ∉ ({zeroZeroZeroState} :
      Finset (PrefixState 2 zeroZeroLength_pos)) := by
    simpa only [Finset.mem_singleton] using zeroZero_states_ne
  rw [Finset.sum_insert hmem, Finset.sum_singleton]
  rcases zeroZero_states s with rfl | rfl
  · simp only [zeroZeroWeight,
      if_neg zeroZero_states_ne.symm, zeroZero_matrix_empty_empty,
      zeroZero_matrix_empty_zero, Nat.cast_ofNat]
    norm_num
  · simp only [zeroZeroWeight,
      if_neg zeroZero_states_ne.symm, zeroZero_matrix_zero_empty,
      zeroZero_matrix_zero_zero, Nat.cast_ofNat]
    norm_num

/-- Concrete weighted entropy certificate for `v = 00`. -/
theorem zeroZero_forbiddenEntropy_le :
    forbiddenEntropy zeroZeroWord ≤ Real.log (991 / 100 : ℚ) := by
  exact weighted_entropy_certificate zeroZeroLength_pos zeroZeroWord
    zeroZeroWeight (991 / 100) (by norm_num) zeroZero_weight_ge_one
    zeroZero_weighted_matrix_certificate

theorem zeroZero_forbiddenWordCount_four :
    forbiddenWordCount zeroZeroWord 4 = 9720 := by
  rw [forbiddenWordCount_eq_matrix_rowSum zeroZeroLength_pos zeroZeroWord 4,
    zeroZero_initialState]
  norm_num [pow_succ, Matrix.mul_apply, zeroZero_sum, zeroZero_states_ne]

theorem zeroZero_forbiddenQ : forbiddenQ zeroZeroWord = 9720 := by
  simpa [forbiddenQ, forbiddenWordCount] using zeroZero_forbiddenWordCount_four

/-- `991/100` is strictly below T12's normalized length-four growth bound
for `00`; equivalently, its fourth power is strictly below the exact count
`9720`. -/
theorem zeroZero_rate_strictly_improves_T12 :
    Real.log (991 / 100 : ℝ) <
      Real.log (forbiddenQ zeroZeroWord : ℝ) / ((2 * 2 : ℕ) : ℝ) := by
  have hbase : (0 : ℝ) < 991 / 100 := by norm_num
  have hpow : (991 / 100 : ℝ) ^ 4 < (9720 : ℝ) := by norm_num
  have hlog : Real.log ((991 / 100 : ℝ) ^ 4) < Real.log (9720 : ℝ) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr (pow_pos hbase 4)
    · exact Set.mem_Ioi.mpr (by norm_num)
    · exact hpow
  rw [zeroZero_forbiddenQ]
  norm_num only [Nat.cast_ofNat, Nat.reduceMul]
  calc
    Real.log (991 / 100 : ℝ) =
        Real.log ((991 / 100 : ℝ) ^ 4) / 4 := by
      rw [Real.log_pow]
      ring
    _ < Real.log (9720 : ℝ) / 4 := div_lt_div_of_pos_right hlog (by norm_num)

/-- Necessary-only T14 conclusion. Under literal failure of canonical C1,
T13 supplies an invariant pi empirical cluster and a forbidden word. Any
positive rational finite-state certificate for that word transfers to both
its intrinsic entropy and T13's full-mass Hausdorff-dimension bound. -/
theorem not_piPositiveLowerBlockDensity_implies_weighted_certificate_transfer
    (hnot : ¬PiPositiveLowerBlockDensity) :
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure ∧ timesTenMap ν = ν ∧
      ∃ ell : ℕ, ∃ hell : 0 < ell, ∃ v : DecimalWord ell,
        (ν : Measure UnitAddCircle)
            (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0 ∧
        ∃ E : Set UnitAddCircle,
          MeasurableSet E ∧ (ν : Measure UnitAddCircle) E = 1 ∧
          ∀ (x : PrefixState ell hell → ℚ) (lambda : ℚ),
            1 ≤ lambda → (∀ i, 1 ≤ x i) →
            (∀ i, ∑ j : PrefixState ell hell,
              (forbiddenTransitionMatrix hell v i j : ℚ) * x j ≤
                lambda * x i) →
            forbiddenEntropy v ≤ Real.log (lambda : ℝ) ∧
              dimH E ≤ ENNReal.ofReal (Real.log (lambda : ℝ) / Real.log 10) := by
  obtain ⟨ν, hcluster, hinvariant, ell, hell, v, hzero,
      _htend, _hinf, E, hmeas, hfull, hdim, _hq, _hstrict⟩ :=
    T13.not_piPositiveLowerBlockDensity_implies_intrinsic_entropy_bound hnot
  refine ⟨ν, hcluster, hinvariant, ell, hell, v, hzero, E, hmeas, hfull, ?_⟩
  intro x lambda hlambda hx hcert
  have hent := weighted_entropy_certificate hell v x lambda hlambda hx hcert
  refine ⟨hent, hdim.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right hent (Real.log_nonneg (by norm_num))

end Theory.PiDigits.PositiveLowerBlockDensity.T14

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.properPrefixAutomaton_language_equivalence
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.forbiddenAutomaton_path_count
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.forbiddenWordCount_eq_matrix_rowSum
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.weighted_entropy_certificate
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.zeroZero_weighted_matrix_certificate
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.zeroZero_forbiddenEntropy_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.zeroZero_rate_strictly_improves_T12
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T14.not_piPositiveLowerBlockDensity_implies_weighted_certificate_transfer
