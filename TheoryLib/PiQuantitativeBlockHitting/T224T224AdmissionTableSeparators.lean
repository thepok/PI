import TheoryLib.PiQuantitativeBlockHitting.T204T204ConstantRunBound
import TheoryLib.PiQuantitativeBlockHitting.T206T206EndpointBridge
import Mathlib

/-!
# T224: admission-table separators

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t224; each task compiled and
axiom-checked; assembled by Claude Opus 5

All eight tasks share one byte-identical starter; the later tasks embedded the
earlier lemmas verbatim, so each lemma appears once here.
-/

noncomputable section

namespace Theory.PiDigits.T224AdmissionTableSeparators

abbrev Digit := Fin 10

open Theory.PiDigits.T206EndpointBridge

def deletedDigitSet (δ : Digit) : Set ℝ :=
  {x | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∀ n : ℕ, greedyStream x n ≠ δ}

def BAκ (κ x : ℝ) : Prop :=
  0 < κ ∧ ∀ p : ℤ, ∀ q : ℕ, 0 < q →
    κ / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / (q : ℝ)|

def BadlyApproximable (x : ℝ) : Prop :=
  ∃ κ : ℝ, BAκ κ x

def FiniteIrrationalityExponent (x : ℝ) : Prop :=
  Irrational x ∧ ∃ M : ℝ, 2 ≤ M ∧
    Theory.PiDigits.T204ConstantRunBound.IrrationalityExponentAtMost x M

def IrrationalityExponentExactlyTwo (x : ℝ) : Prop :=
  Irrational x ∧
  Theory.PiDigits.T204ConstantRunBound.IrrationalityExponentAtMost x 2 ∧
  ∀ μ : ℝ, 0 < μ → μ < 2 → ∀ Q : ℕ,
    ∃ q : ℕ, Q ≤ q ∧ 0 < q ∧
      ∃ p : ℤ,
        0 < |x - (p : ℝ) / (q : ℝ)| ∧
        |x - (p : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ μ

def DeletedDigitTranscendentalBAInput : Prop :=
  ∀ δ : Digit, ∃ x : ℝ,
    x ∈ deletedDigitSet δ ∧
    Transcendental ℚ x ∧
    BadlyApproximable x

def BadlyApproximableImpliesExactTwoInput : Prop :=
  ∀ x : ℝ, BadlyApproximable x →
    IrrationalityExponentExactlyTwo x

def IrrationalSeparator (w : List Digit) : Prop :=
  ∃ x : ℝ, x ∈ CWord w ∧ Irrational x

def TranscendentalSeparator (w : List Digit) : Prop :=
  ∃ x : ℝ, x ∈ CWord w ∧ Transcendental ℚ x

def FiniteExponentSeparator (w : List Digit) : Prop :=
  ∃ x : ℝ, x ∈ CWord w ∧ FiniteIrrationalityExponent x

def BadlyApproximableSeparator (w : List Digit) : Prop :=
  ∃ x : ℝ, x ∈ CWord w ∧ BadlyApproximable x

def ExactExponentTwoSeparator (w : List Digit) : Prop :=
  ∃ x : ℝ, x ∈ CWord w ∧ IrrationalityExponentExactlyTwo x

/-! ### Deleted-digit avoidance and the two elementary projections

Tasks `pi-t224-admission-01-deleted-digit-set-subset-cword`,
`-02-transcendental-is-irrational` and `-03-exact-exponent-two-finite`. -/

lemma deletedDigitSet_subset_CWord
    {w : List Digit} (hw : w ≠ [])
    {δ : Digit} (hδ : δ ∈ w) :
    deletedDigitSet δ ⊆ CWord w := by
  intro x hx
  obtain ⟨hxIco, hxavoid⟩ := hx
  refine ⟨hxIco, ?_⟩
  intro start hocc
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hδ
  have := hocc ⟨i, hi⟩
  simp only [List.get_eq_getElem, hget] at this
  exact hxavoid (start + i) this

lemma transcendental_is_irrational
    {x : ℝ} (hx : Transcendental ℚ x) :
    Irrational x :=
  Transcendental.irrational hx

lemma exactExponentTwo_finite
    {x : ℝ} (hx : IrrationalityExponentExactlyTwo x) :
    FiniteIrrationalityExponent x :=
  ⟨hx.1, 2, le_refl 2, hx.2.1⟩

/-! ### The five separator rows

Tasks `pi-t224-admission-04-irrational-separator-exists`,
`-05-transcendental-separator-exists`, `-06-finite-exponent-separator-exists`,
`-07-badly-approximable-separator-exists` and
`-08-exact-exponent-two-separator-exists`.  The deleted-digit literature
instance `DeletedDigitTranscendentalBAInput` and the badly-approximable to
exact-exponent-two input `BadlyApproximableImpliesExactTwoInput` stay explicit
hypotheses throughout. -/

theorem irrational_separator_exists
    (hLit : DeletedDigitTranscendentalBAInput)
    {w : List Digit} (hw : w ≠ [])
    (δ : Digit) (hδ : δ ∈ w) :
    IrrationalSeparator w := by
  obtain ⟨x, hxmem, hxtr, _⟩ := hLit δ
  exact ⟨x, deletedDigitSet_subset_CWord hw hδ hxmem,
    transcendental_is_irrational hxtr⟩


theorem transcendental_separator_exists
    (hLit : DeletedDigitTranscendentalBAInput)
    {w : List Digit} (hw : w ≠ [])
    (δ : Digit) (hδ : δ ∈ w) :
    TranscendentalSeparator w := by
  obtain ⟨x, hxmem, hxtr, _⟩ := hLit δ
  exact ⟨x, deletedDigitSet_subset_CWord hw hδ hxmem, hxtr⟩

theorem finiteExponent_separator_exists
    (hLit : DeletedDigitTranscendentalBAInput)
    (hBA2 : BadlyApproximableImpliesExactTwoInput)
    {w : List Digit} (hw : w ≠ [])
    (δ : Digit) (hδ : δ ∈ w) :
    FiniteExponentSeparator w := by
  obtain ⟨x, hxmem, _, hxba⟩ := hLit δ
  exact ⟨x, deletedDigitSet_subset_CWord hw hδ hxmem,
    exactExponentTwo_finite (hBA2 x hxba)⟩


theorem badlyApproximable_separator_exists
    (hLit : DeletedDigitTranscendentalBAInput)
    {w : List Digit} (hw : w ≠ [])
    (δ : Digit) (hδ : δ ∈ w) :
    BadlyApproximableSeparator w := by
  obtain ⟨x, hxmem, _, hxba⟩ := hLit δ
  exact ⟨x, deletedDigitSet_subset_CWord hw hδ hxmem, hxba⟩

theorem exactExponentTwo_separator_exists
    (hLit : DeletedDigitTranscendentalBAInput)
    (hBA2 : BadlyApproximableImpliesExactTwoInput)
    {w : List Digit} (hw : w ≠ [])
    (δ : Digit) (hδ : δ ∈ w) :
    ExactExponentTwoSeparator w := by
  obtain ⟨x, hxmem, _, hxba⟩ := hLit δ
  exact ⟨x, deletedDigitSet_subset_CWord hw hδ hxmem, hBA2 x hxba⟩


end Theory.PiDigits.T224AdmissionTableSeparators
