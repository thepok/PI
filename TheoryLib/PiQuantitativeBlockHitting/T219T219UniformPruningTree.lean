import Mathlib

/-!
# T219: uniform pruning tree

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t219; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Theory.PiDigits.T219UniformPruningTree

open scoped BigOperators

abbrev Digit := Fin 10

abbrev CausalRule := List Digit → Finset Digit

def Compatible (A : CausalRule) (u : List Digit) : Prop :=
  ∀ i : Fin u.length, u.get i ∈ A (u.take i.1)

def Avoids (w u : List Digit) : Prop :=
  ∀ i : Fin (u.length + 1), i.1 + w.length ≤ u.length →
    u.extract i.1 (i.1 + w.length) ≠ w

def dangerousDigits (w u : List Digit) : Finset Digit :=
  Finset.univ.filter fun d => ¬ Avoids w (u ++ [d])

def safeChildren (A : CausalRule) (w u : List Digit) : Finset Digit :=
  (A u).filter fun d => Avoids w (u ++ [d])

def BinarySelectorData (A : CausalRule) (w : List Digit)
    (child : List Digit → Finset Digit) : Prop :=
  ∀ u, Compatible A u → Avoids w u →
    (child u).card = 2 ∧ child u ⊆ A u ∧
      ∀ d ∈ child u, Avoids w (u ++ [d])

def selectedLevel (child : List Digit → Finset Digit) :
    ℕ → Finset (List Digit)
  | 0 => {[]}
  | n + 1 =>
      (selectedLevel child n).biUnion fun u =>
        (child u).image fun d => u ++ [d]

def PeriodicSelectorData (A : CausalRule) (δ : Digit) (ell : ℕ)
    (child : ℕ → List Digit → Finset Digit) : Prop :=
  ∀ n u, u.length = n → Compatible A u →
    child n u ⊆ A u ∧
      (child n u).card = (if ell ∣ n + 1 then 1 else 2) ∧
      (ell ∣ n + 1 → ∀ d ∈ child n u, d ≠ δ)

def guardedSelectedLevel (child : ℕ → List Digit → Finset Digit) :
    ℕ → Finset (List Digit)
  | 0 => {[]}
  | n + 1 =>
      (guardedSelectedLevel child n).biUnion fun u =>
        (child n u).image fun d => u ++ [d]

lemma dangerous_shape {w : List Digit} (hw : w ≠ []) {u : List Digit}
    (hu : Avoids w u) {d : Digit} (hd : ¬ Avoids w (u ++ [d])) :
    w = u.drop (u.length + 1 - w.length) ++ [d] := by
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hw
  rw [Avoids] at hd
  push_neg at hd
  obtain ⟨i, hi, heq⟩ := hd
  have hi' : (i : ℕ) + w.length ≤ u.length + 1 := by simpa using hi
  have hi := hi'
  have hile : i.1 ≤ u.length := by omega
  have hdrop : (u ++ [d]).drop i.1 = u.drop i.1 ++ [d] :=
    List.drop_append_of_le_length hile
  have hdroplen : (u.drop i.1).length = u.length - i.1 := by simp
  rcases Nat.lt_or_ge (i.1 + w.length) (u.length + 1) with hcase | hcase
  · exfalso
    have hle : i.1 + w.length ≤ u.length := by omega
    have : u.extract i.1 (i.1 + w.length) = w := by
      rw [List.extract_eq_take_drop] at heq ⊢
      simp only [Nat.add_sub_cancel_left] at heq ⊢
      rw [hdrop] at heq
      rw [List.take_append_of_le_length (by omega)] at heq
      exact heq
    exact hu ⟨i.1, by omega⟩ hle this
  · have hcase' : i.1 + w.length = u.length + 1 := by omega
    rw [List.extract_eq_take_drop, Nat.add_sub_cancel_left, hdrop] at heq
    have : (u.drop i.1 ++ [d]).length = w.length := by
      simp [hdroplen]; omega
    rw [List.take_of_length_le (le_of_eq this)] at heq
    have hi_eq : i.1 = u.length + 1 - w.length := by omega
    rw [hi_eq] at heq
    exact heq.symm

lemma atMostOneDangerousDigit
    (w : List Digit) (hw : w ≠ []) (u : List Digit) (hu : Avoids w u) :
    (dangerousDigits w u).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [dangerousDigits, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h1 := dangerous_shape hw hu ha
  have h2 := dangerous_shape hw hu hb
  have h3 := h1.symm.trans h2
  simpa using List.append_cancel_left h3

lemma safeChildren_card {A : CausalRule} {w : List Digit} (hw : w ≠ [])
    (hA : ∀ u, Compatible A u → 3 ≤ (A u).card) {u : List Digit}
    (hcu : Compatible A u) (hau : Avoids w u) :
    2 ≤ (safeChildren A w u).card := by
  classical
  have hsplit :
      ((A u).filter fun d => Avoids w (u ++ [d])).card
        + ((A u).filter fun d => ¬ Avoids w (u ++ [d])).card = (A u).card :=
    Finset.card_filter_add_card_filter_not _
  have hsub : ((A u).filter fun d => ¬ Avoids w (u ++ [d])) ⊆ dangerousDigits w u := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    simp only [dangerousDigits, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hd.2
  have hbad : ((A u).filter fun d => ¬ Avoids w (u ++ [d])).card ≤ 1 :=
    le_trans (Finset.card_le_card hsub) (atMostOneDangerousDigit w hw u hau)
  have h3 := hA u hcu
  have : (safeChildren A w u).card = ((A u).filter fun d => Avoids w (u ++ [d])).card := rfl
  omega

lemma chooseTwoSafe
    {A : CausalRule} {w : List Digit} (hw : w ≠ [])
    (hA : ∀ u, Compatible A u → 3 ≤ (A u).card) :
    ∃ child : List Digit → Finset Digit, BinarySelectorData A w child := by
  classical
  refine ⟨fun u =>
    if h : ∃ t : Finset Digit, t ⊆ safeChildren A w u ∧ t.card = 2 then h.choose else ∅, ?_⟩
  intro u hcu hau
  have hex : ∃ t : Finset Digit, t ⊆ safeChildren A w u ∧ t.card = 2 := by
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq (safeChildren_card hw hA hcu hau)
    exact ⟨t, ht, htc⟩
  simp only [dif_pos hex]
  obtain ⟨hsub, hcard⟩ := hex.choose_spec
  refine ⟨hcard, ?_, ?_⟩
  · intro d hd
    have := hsub hd
    simp only [safeChildren, Finset.mem_filter] at this
    exact this.1
  · intro d hd
    have := hsub hd
    simp only [safeChildren, Finset.mem_filter] at this
    exact this.2

lemma compatible_iff {A : CausalRule} {u : List Digit} :
    Compatible A u ↔ ∀ (i : ℕ) (h : i < u.length), u[i] ∈ A (u.take i) := by
  constructor
  · intro h i hi
    simpa using h ⟨i, hi⟩
  · intro h i
    simpa using h i.1 i.2

lemma compatible_nil {A : CausalRule} : Compatible A ([] : List Digit) := by
  rw [compatible_iff]
  intro i hi
  simp at hi

lemma compatible_append {A : CausalRule} {u : List Digit} {d : Digit}
    (hu : Compatible A u) (hd : d ∈ A u) : Compatible A (u ++ [d]) := by
  rw [compatible_iff] at hu ⊢
  intro i hi
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  have hile : i ≤ u.length := by omega
  rw [List.take_append_of_le_length hile]
  rcases Nat.lt_or_ge i u.length with h | h
  · rw [List.getElem_append_left h]
    exact hu i h
  · have hiu : i = u.length := by omega
    subst hiu
    rw [List.take_length]
    simpa using hd

lemma avoids_nil {w : List Digit} (hw : w ≠ []) : Avoids w ([] : List Digit) := by
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hw
  intro i hi
  simp only [List.length_nil] at hi
  omega

lemma selectedLevel_mem {A : CausalRule} {w : List Digit} (hw : w ≠ [])
    {child : List Digit → Finset Digit} (hc : BinarySelectorData A w child) :
    ∀ (n : ℕ), ∀ u ∈ selectedLevel child n, u.length = n ∧ Compatible A u ∧ Avoids w u := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simp only [selectedLevel, Finset.mem_singleton] at hu
      subst hu
      exact ⟨rfl, compatible_nil, avoids_nil hw⟩
  | succ n ih =>
      intro x hx
      simp only [selectedLevel, Finset.mem_biUnion, Finset.mem_image] at hx
      obtain ⟨u, hu, d, hd, rfl⟩ := hx
      obtain ⟨hlen, hcu, hau⟩ := ih u hu
      obtain ⟨_, hsub, hsafe⟩ := hc u hcu hau
      refine ⟨by simp [hlen], compatible_append hcu (hsub hd), hsafe d hd⟩

lemma binaryLevel_card
    {A : CausalRule} {w : List Digit} (hw : w ≠ [])
    {child : List Digit → Finset Digit}
    (hc : BinarySelectorData A w child) (n : ℕ) :
    (selectedLevel child n).card = 2 ^ n := by
  induction n with
  | zero => simp [selectedLevel]
  | succ n ih =>
      have hcard : ∀ u ∈ selectedLevel child n,
          ((child u).image fun d => u ++ [d]).card = 2 := by
        intro u hu
        obtain ⟨hlen, hcu, hau⟩ := selectedLevel_mem hw hc n u hu
        rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
        exact (hc u hcu hau).1
      have hdisj : ∀ u ∈ selectedLevel child n, ∀ v ∈ selectedLevel child n, u ≠ v →
          Disjoint ((child u).image fun d => u ++ [d])
            ((child v).image fun d => v ++ [d]) := by
        intro u hu v hv huv
        rw [Finset.disjoint_left]
        rintro x hx hx'
        simp only [Finset.mem_image] at hx hx'
        obtain ⟨d, -, rfl⟩ := hx
        obtain ⟨e, -, he⟩ := hx'
        obtain ⟨hlu, -, -⟩ := selectedLevel_mem hw hc n u hu
        obtain ⟨hlv, -, -⟩ := selectedLevel_mem hw hc n v hv
        exact huv (List.append_inj he.symm (by omega)).1
      calc (selectedLevel child (n + 1)).card
          = ((selectedLevel child n).biUnion fun u =>
              (child u).image fun d => u ++ [d]).card := by
            simp only [selectedLevel]
        _ = ∑ u ∈ selectedLevel child n, ((child u).image fun d => u ++ [d]).card :=
            Finset.card_biUnion hdisj
        _ = ∑ _u ∈ selectedLevel child n, 2 := Finset.sum_congr rfl hcard
        _ = (selectedLevel child n).card * 2 := by
            simp [Finset.sum_const]
        _ = 2 ^ (n + 1) := by rw [ih]; ring

lemma guardedLevel_mem {A : CausalRule} {δ : Digit} {ell : ℕ}
    {child : ℕ → List Digit → Finset Digit} (hc : PeriodicSelectorData A δ ell child) :
    ∀ (n : ℕ), ∀ u ∈ guardedSelectedLevel child n, u.length = n ∧ Compatible A u := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simp only [guardedSelectedLevel, Finset.mem_singleton] at hu
      subst hu
      exact ⟨rfl, compatible_nil⟩
  | succ n ih =>
      intro x hx
      simp only [guardedSelectedLevel, Finset.mem_biUnion, Finset.mem_image] at hx
      obtain ⟨u, hu, d, hd, rfl⟩ := hx
      obtain ⟨hlen, hcu⟩ := ih u hu
      obtain ⟨hsub, -, -⟩ := hc n u hlen hcu
      exact ⟨by simp [hlen], compatible_append hcu (hsub hd)⟩

lemma periodicGuardLevel_card
    {A : CausalRule} {δ : Digit} {ell : ℕ} (hell : 2 ≤ ell)
    {child : ℕ → List Digit → Finset Digit}
    (hc : PeriodicSelectorData A δ ell child) (n : ℕ) :
    (guardedSelectedLevel child n).card = 2 ^ (n - n / ell) := by
  have hell2 : 2 ≤ ell := hell
  clear hell
  induction n with
  | zero => simp [guardedSelectedLevel]
  | succ n ih =>
      have hcard : ∀ u ∈ guardedSelectedLevel child n,
          ((child n u).image fun d => u ++ [d]).card = (if ell ∣ n + 1 then 1 else 2) := by
        intro u hu
        obtain ⟨hlen, hcu⟩ := guardedLevel_mem hc n u hu
        rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
        exact (hc n u hlen hcu).2.1
      have hdisj : ∀ u ∈ guardedSelectedLevel child n, ∀ v ∈ guardedSelectedLevel child n,
          u ≠ v → Disjoint ((child n u).image fun d => u ++ [d])
            ((child n v).image fun d => v ++ [d]) := by
        intro u hu v hv huv
        rw [Finset.disjoint_left]
        rintro x hx hx'
        simp only [Finset.mem_image] at hx hx'
        obtain ⟨d, -, rfl⟩ := hx
        obtain ⟨e, -, he⟩ := hx'
        obtain ⟨hlu, -⟩ := guardedLevel_mem hc n u hu
        obtain ⟨hlv, -⟩ := guardedLevel_mem hc n v hv
        exact huv (List.append_inj he.symm (by omega)).1
      have hstep : (guardedSelectedLevel child (n + 1)).card
          = (guardedSelectedLevel child n).card * (if ell ∣ n + 1 then 1 else 2) := by
        calc (guardedSelectedLevel child (n + 1)).card
            = ((guardedSelectedLevel child n).biUnion fun u =>
                (child n u).image fun d => u ++ [d]).card := by
              simp only [guardedSelectedLevel]
          _ = ∑ u ∈ guardedSelectedLevel child n,
                ((child n u).image fun d => u ++ [d]).card := Finset.card_biUnion hdisj
          _ = ∑ _u ∈ guardedSelectedLevel child n, (if ell ∣ n + 1 then 1 else 2) :=
              Finset.sum_congr rfl hcard
          _ = (guardedSelectedLevel child n).card * (if ell ∣ n + 1 then 1 else 2) := by
              simp [Finset.sum_const]
      have hdiv : (n + 1) / ell = n / ell + if ell ∣ n + 1 then 1 else 0 := Nat.succ_div
      have hle : n / ell ≤ n := Nat.div_le_self n ell
      rw [hstep, ih]
      by_cases hd : ell ∣ n + 1
      · simp only [if_pos hd] at hdiv ⊢
        have : n + 1 - (n + 1) / ell = n - n / ell := by omega
        rw [this, Nat.mul_one]
      · simp only [if_neg hd] at hdiv ⊢
        have : n + 1 - (n + 1) / ell = (n - n / ell) + 1 := by omega
        rw [this, pow_succ]

end Theory.PiDigits.T219UniformPruningTree
