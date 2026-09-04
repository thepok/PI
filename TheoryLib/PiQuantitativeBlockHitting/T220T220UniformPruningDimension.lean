import TheoryLib.PiQuantitativeBlockHitting.T219T219UniformPruningTree
import TheoryLib.PiPositiveLowerBlockDensity.T21T21FinitePrefixFrostman
import Mathlib

/-!
# T220: uniform pruning dimension

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t220; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Theory.PiDigits.T220UniformPruningDimension

open scoped BigOperators
open Theory.PiDigits.T219UniformPruningTree

def streamPrefix (a : ℕ → Digit) (n : ℕ) : List Digit :=
  List.ofFn fun i : Fin n => a i.1

noncomputable def decimalValue (a : ℕ → Digit) : ℝ :=
  ∑' n : ℕ, ((a n).1 : ℝ) / (10 : ℝ) ^ (n + 1)

def RuleCompatible (A : CausalRule) (a : ℕ → Digit) : Prop :=
  ∀ n, Compatible A (streamPrefix a n)

def StreamAvoids (w : List Digit) (a : ℕ → Digit) : Prop :=
  ∀ n, Avoids w (streamPrefix a n)

def EventuallyConstantDigit (δ : Digit) (a : ℕ → Digit) : Prop :=
  ∃ N, ∀ n ≥ N, a n = δ

def EndpointStream (a : ℕ → Digit) : Prop :=
  EventuallyConstantDigit (0 : Digit) a ∨
    EventuallyConstantDigit (9 : Digit) a

def GreedyStream (a : ℕ → Digit) : Prop :=
  ¬ EventuallyConstantDigit (9 : Digit) a

noncomputable def RuleCompatibleAvoider
    (A : CausalRule) (w : List Digit) : Set ℝ :=
  decimalValue '' {a |
    RuleCompatible A a ∧ StreamAvoids w a ∧ GreedyStream a}

def SelectedBranch (child : List Digit → Finset Digit)
    (a : ℕ → Digit) : Prop :=
  ∀ n, streamPrefix a n ∈ selectedLevel child n

noncomputable def selectedRealSet
    (child : List Digit → Finset Digit) : Set ℝ :=
  decimalValue '' {a | SelectedBranch child a ∧ ¬ EndpointStream a}

def GuardedBranch (child : ℕ → List Digit → Finset Digit)
    (a : ℕ → Digit) : Prop :=
  ∀ n, streamPrefix a n ∈ guardedSelectedLevel child n

noncomputable def guardedRealSet
    (child : ℕ → List Digit → Finset Digit) : Set ℝ :=
  decimalValue '' {a | GuardedBranch child a ∧ ¬ EndpointStream a}

def BinaryDimensionInput (A : CausalRule) (w : List Digit) : Prop :=
  ∀ child, BinarySelectorData A w child →
    dimH (selectedRealSet child) =
      ENNReal.ofReal (Real.log 2 / Real.log 10)

def PeriodicDimensionInput
    (A : CausalRule) (δ : Digit) (ell : ℕ) : Prop :=
  ∀ child, PeriodicSelectorData A δ ell child →
    dimH (guardedRealSet child) =
      ENNReal.ofReal
        ((((ell - 1 : ℕ) : ℝ) / (ell : ℝ)) *
          (Real.log 2 / Real.log 10))

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
      obtain ⟨-, hsub, hsafe⟩ := hc u hcu hau
      refine ⟨by simp [hlen], compatible_append hcu (hsub hd), hsafe d hd⟩

theorem R3_word_dimension
    {A : CausalRule} {w : List Digit} (hw : w ≠ [])
    (hchoices : ∀ u, Compatible A u → 3 ≤ (A u).card)
    (hselect : ∃ child, BinarySelectorData A w child)
    (hdim : BinaryDimensionInput A w) :
    ∃ E : Set ℝ,
      E ⊆ RuleCompatibleAvoider A w ∧
      dimH E = ENNReal.ofReal (Real.log 2 / Real.log 10) := by
  have _hchoices : ∀ u, Compatible A u → 3 ≤ (A u).card := hchoices
  obtain ⟨child, hchild⟩ := hselect
  refine ⟨selectedRealSet child, ?_, hdim child hchild⟩
  apply Set.image_mono
  rintro a ⟨hbranch, hend⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (selectedLevel_mem hw hchild n _ (hbranch n)).2.1
  · intro n
    exact (selectedLevel_mem hw hchild n _ (hbranch n)).2.2
  · intro h9
    exact hend (Or.inr h9)

lemma streamPrefix_length (a : ℕ → Digit) (n : ℕ) : (streamPrefix a n).length = n := by
  simp [streamPrefix]

lemma streamPrefix_succ (a : ℕ → Digit) (n : ℕ) :
    streamPrefix a (n + 1) = streamPrefix a n ++ [a n] := by
  show List.ofFn (fun i : Fin (n + 1) => a i.1) = _
  rw [List.ofFn_succ']
  simp [streamPrefix, List.concat_eq_append]

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

lemma guard_digit_ne {A : CausalRule} {δ : Digit} {ell : ℕ}
    {child : ℕ → List Digit → Finset Digit} (hc : PeriodicSelectorData A δ ell child)
    {a : ℕ → Digit} (hb : GuardedBranch child a) :
    ∀ n, ell ∣ n + 1 → a n ≠ δ := by
  intro n hdvd
  have hx := hb (n + 1)
  simp only [guardedSelectedLevel, Finset.mem_biUnion, Finset.mem_image] at hx
  obtain ⟨u, hu, d, hd, hud⟩ := hx
  obtain ⟨hlen, hcu⟩ := guardedLevel_mem hc n u hu
  have hsp : u ++ [d] = streamPrefix a n ++ [a n] := by
    rw [hud, streamPrefix_succ]
  have hlensp : u.length = (streamPrefix a n).length := by
    rw [hlen, streamPrefix_length]
  obtain ⟨-, htail⟩ := List.append_inj hsp hlensp
  have hda : d = a n := by simpa using htail
  have := (hc n u hlen hcu).2.2 hdvd d hd
  rw [hda] at this
  exact this

lemma extract_streamPrefix (a : ℕ → Digit) (m i len : ℕ) (h : i + len ≤ m) :
    (streamPrefix a m).extract i (i + len) = List.ofFn (fun k : Fin len => a (i + k.1)) := by
  apply List.ext_getElem
  · simp [streamPrefix]
    omega
  · intro n h1 h2
    simp [streamPrefix]

lemma streamAvoids_replicate {δ : Digit} {ell : ℕ} (hell : 2 ≤ ell) {a : ℕ → Digit}
    (hguard : ∀ n, ell ∣ n + 1 → a n ≠ δ) :
    StreamAvoids (List.replicate ell δ) a := by
  intro m i hi
  have hi' : (i : ℕ) + ell ≤ m := by
    simpa [streamPrefix_length] using hi
  intro heq
  rw [List.length_replicate] at heq
  rw [extract_streamPrefix a m i.1 ell hi'] at heq
  rw [← List.ofFn_const ell δ] at heq
  have hfun := List.ofFn_inj.mp heq
  have hq : ell * (i.1 / ell) + i.1 % ell = i.1 := Nat.div_add_mod _ _
  have hmlt : i.1 % ell < ell := Nat.mod_lt _ (by omega)
  set j : ℕ := ell - 1 - i.1 % ell with hjdef
  have hj : j < ell := by omega
  have hjval : i.1 + j + 1 = ell * (i.1 / ell) + ell := by omega
  have hdvd : ell ∣ i.1 + j + 1 := ⟨i.1 / ell + 1, by rw [Nat.mul_add, Nat.mul_one]; exact hjval⟩
  have := congrFun hfun ⟨j, hj⟩
  simp only at this
  exact hguard (i.1 + j) hdvd this

theorem R3_constantRun_dimension
    {A : CausalRule} {δ : Digit} {ell : ℕ} (hell : 2 ≤ ell)
    (hchoices : ∀ u, Compatible A u → 2 ≤ (A u).card)
    (hselect : ∃ child, PeriodicSelectorData A δ ell child)
    (hdim : PeriodicDimensionInput A δ ell) :
    ∃ E : Set ℝ,
      E ⊆ RuleCompatibleAvoider A (List.replicate ell δ) ∧
      dimH E = ENNReal.ofReal
        ((((ell - 1 : ℕ) : ℝ) / (ell : ℝ)) *
          (Real.log 2 / Real.log 10)) := by
  have _hchoices : ∀ u, Compatible A u → 2 ≤ (A u).card := hchoices
  obtain ⟨child, hchild⟩ := hselect
  refine ⟨guardedRealSet child, ?_, hdim child hchild⟩
  apply Set.image_mono
  rintro a ⟨hbranch, hend⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (guardedLevel_mem hchild n _ (hbranch n)).2
  · exact streamAvoids_replicate hell (guard_digit_ne hchild hbranch)
  · intro h9
    exact hend (Or.inr h9)

def algebraicSet : Set ℝ := {x | IsAlgebraic ℚ x}

def transcendentalSet : Set ℝ := {x | ¬ IsAlgebraic ℚ x}

def liouvilleSet : Set ℝ := {x : ℝ | Liouville x}

def finiteIrrationalityExponentSet : Set ℝ :=
  {x : ℝ | ¬ Liouville x}

def JarnikLiouvilleZero : Prop :=
  dimH liouvilleSet = 0

theorem R3_trans_finiteExponent
    (hJ : JarnikLiouvilleZero) {E : Set ℝ} (hE : 0 < dimH E) :
    dimH (E ∩ transcendentalSet ∩ finiteIrrationalityExponentSet) =
      dimH E := by
  have _hE : 0 < dimH E := hE
  have hJ' : dimH liouvilleSet = 0 := hJ
  have halg : dimH algebraicSet = 0 := (Algebraic.countable ℚ ℝ).dimH_zero
  refine le_antisymm (dimH_mono (fun x hx => hx.1.1)) ?_
  have hcover : E ⊆ (E ∩ transcendentalSet ∩ finiteIrrationalityExponentSet)
      ∪ (algebraicSet ∪ liouvilleSet) := by
    intro x hx
    by_cases h1 : x ∈ transcendentalSet
    · by_cases h2 : x ∈ finiteIrrationalityExponentSet
      · exact Or.inl ⟨⟨hx, h1⟩, h2⟩
      · refine Or.inr (Or.inr ?_)
        simpa [finiteIrrationalityExponentSet, liouvilleSet] using h2
    · refine Or.inr (Or.inl ?_)
      simpa [transcendentalSet, algebraicSet] using h1
  calc dimH E
      ≤ dimH ((E ∩ transcendentalSet ∩ finiteIrrationalityExponentSet)
          ∪ (algebraicSet ∪ liouvilleSet)) := dimH_mono hcover
    _ = max (dimH (E ∩ transcendentalSet ∩ finiteIrrationalityExponentSet))
          (max (dimH algebraicSet) (dimH liouvilleSet)) := by
        rw [dimH_union, dimH_union]
    _ = dimH (E ∩ transcendentalSet ∩ finiteIrrationalityExponentSet) := by
        rw [halg, hJ']
        simp

end Theory.PiDigits.T220UniformPruningDimension
