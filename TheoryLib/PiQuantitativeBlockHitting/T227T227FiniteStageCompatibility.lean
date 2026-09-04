import TheoryLib.PiQuantitativeBlockHitting.T206T206EndpointBridge
import Mathlib

/-!
# T227: finite-stage compatibility

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t227; each task compiled and
axiom-checked; assembled by Claude Opus 5

All seven tasks share one byte-identical starter; tasks `-06` and `-07`
embedded the earlier lemmas verbatim, so each lemma appears once here.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace Theory.PiDigits.T227FiniteStageCompatibility

abbrev Digit := Fin 10
open Theory.PiDigits.T206EndpointBridge

def PrefixCylinder (P : List Digit) : Set ℝ :=
  {x | x ∈ Set.Ico (0 : ℝ) 1 ∧
    ∀ i : Fin P.length, greedyStream x i.val = P.get i}

def AvoidingPrefixSet (w P : List Digit) : Set ℝ :=
  CWord w ∩ PrefixCylinder P

def BAκ (κ x : ℝ) : Prop :=
  0 < κ ∧ ∀ p : ℤ, ∀ q : ℕ, 0 < q →
    κ / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / (q : ℝ)|

def BadlyApproximableSet : Set ℝ := {x | ∃ κ : ℝ, BAκ κ x}
def TranscendentalSet : Set ℝ := {x | Transcendental ℚ x}

def SeparatedSet (w P : List Digit) : Set ℝ :=
  AvoidingPrefixSet w P ∩ BadlyApproximableSet ∩ TranscendentalSet

def Extends (P Q : List Digit) : Prop := ∃ R : List Digit, Q = P ++ R
def EndsWith (Q g : List Digit) : Prop := ∃ R : List Digit, Q = R ++ g
def Admissible (w P : List Digit) : Prop := (AvoidingPrefixSet w P).Nonempty

def AdmissibleExtension (w P Q : List Digit) : Prop :=
  Extends P Q ∧ Admissible w Q

def SafeGuardFor (w g : List Digit) : Prop :=
  w ≠ [] ∧ g ≠ [] ∧
  ∃ β firstDigit lastDigit : Digit, ∃ initialDigits tailDigits : List Digit,
    w = firstDigit :: tailDigits ∧
    w = initialDigits ++ [lastDigit] ∧
    1 ≤ β.val ∧ β.val ≤ 8 ∧
    β ≠ firstDigit ∧ β ≠ lastDigit ∧
    g = List.replicate w.length β

def ProperAlphabetFor
    (w : List Digit) (A : Finset Digit) (c : Digit) : Prop :=
  A.card = 9 ∧ c ∈ A ∧ 1 ≤ c.val ∧ c.val ≤ 8 ∧
  ∃ δ : Digit, δ ∈ w ∧ δ ∉ A

def WordOver {k : ℕ} (A : Finset Digit) (u : Fin k → Digit) : Prop :=
  ∀ i, u i ∈ A

def MarkedOccurrenceAt {k : ℕ}
    (u : Fin k → Digit) (c : Digit) (x : ℝ) (n : ℕ) : Prop :=
  (∀ i : Fin k, greedyStream x (n + i.val) = u i) ∧
  greedyStream x (n + k) = c

def AllLabelObligation
    (A : Finset Digit) (c : Digit) (k : ℕ) (x : ℝ) : Prop :=
  ∀ u : Fin k → Digit, WordOver A u →
    ∃ n : ℕ, 10 ^ k + 1 ≤ n ∧ n < 10 ^ (k + 1) ∧
      MarkedOccurrenceAt u c x n

def FinitePacketConstructionInput : Prop :=
  ∀ (w P g : List Digit) (A : Finset Digit) (c : Digit),
    w ≠ [] → Admissible w P → SafeGuardFor w g →
    ProperAlphabetFor w A c →
    ∃ k0 : ℕ, ∀ S : Finset ℕ,
      (∀ k ∈ S, k0 ≤ k) →
      ∃ Q : List Digit,
        AdmissibleExtension w P Q ∧ EndsWith Q g ∧
        ∀ x ∈ AvoidingPrefixSet w Q,
          ∀ k ∈ S, AllLabelObligation A c k x

def DocumentATheoremAInput : Prop :=
  ∀ (w Q : List Digit), w ≠ [] → Admissible w Q →
    dimH (SeparatedSet w Q) = dimH (AvoidingPrefixSet w Q)

def EdgeParryPrefixDimensionInput : Prop :=
  ∀ (w g Q : List Digit),
    w ≠ [] → SafeGuardFor w g → Admissible w Q → EndsWith Q g →
    dimH (AvoidingPrefixSet w Q) = dimH (CWord w)

structure FutureCoordinateObligation where
  start : ℕ
  length : ℕ
  accept : (Fin length → Digit) → Prop

def FutureCoordinateObligation.Holds
    (o : FutureCoordinateObligation) (x : ℝ) : Prop :=
  o.accept (fun i => greedyStream x (o.start + i.val))

def SupportedAfter
    (P : List Digit) (O : List FutureCoordinateObligation) : Prop :=
  ∀ o ∈ O, P.length ≤ o.start

def FeasibleRelative
    (w P : List Digit) (O : List FutureCoordinateObligation) : Prop :=
  ∃ R : List Digit,
    AdmissibleExtension w P R ∧
    ∀ x ∈ AvoidingPrefixSet w R, ∀ o ∈ O, o.Holds x

def FeasibleGuardExtensionInput : Prop :=
  ∀ (w P g : List Digit) (O : List FutureCoordinateObligation),
    w ≠ [] → Admissible w P → SafeGuardFor w g →
    SupportedAfter P O → FeasibleRelative w P O →
    ∃ Q : List Digit,
      AdmissibleExtension w P Q ∧ EndsWith Q g ∧
      ∀ x ∈ AvoidingPrefixSet w Q, ∀ o ∈ O, o.Holds x

/-! ### The extension relation

Tasks `pi-t227-finite-stage-01-extends-refl`, `-02-extends-trans` and
`-03-admissible-extension-is-admissible`. -/

lemma extends_refl (P : List Digit) : Extends P P :=
  ⟨[], by simp⟩

lemma extends_trans {P Q R : List Digit} :
    Extends P Q → Extends Q R → Extends P R := by
  rintro ⟨R1, rfl⟩ ⟨R2, rfl⟩
  exact ⟨R1 ++ R2, by rw [List.append_assoc]⟩

lemma admissibleExtension_is_admissible
    {w P Q : List Digit} (h : AdmissibleExtension w P Q) :
    Admissible w Q := h.2

/-! ### Conditional dimension transfer and finite packets

Tasks `pi-t227-finite-stage-04-doca-edge-parry-dimension`,
`-05-finite-packet-exists`, `-06-finite-stage-compatibility` and
`-07-future-finite-coordinate-compatibility`.  The packet construction
`FinitePacketConstructionInput`, the Document A theorem
`DocumentATheoremAInput`, the edge-Parry package
`EdgeParryPrefixDimensionInput` and the guard completion
`FeasibleGuardExtensionInput` all stay explicit hypotheses. -/

lemma docA_edgeParry_dimension
    (hA : DocumentATheoremAInput)
    (hEdge : EdgeParryPrefixDimensionInput)
    {w g Q : List Digit}
    (hw : w ≠ []) (hguard : SafeGuardFor w g)
    (hQ : Admissible w Q) (hend : EndsWith Q g) :
    dimH (SeparatedSet w Q) = dimH (CWord w) :=
  (hA w Q hw hQ).trans (hEdge w g Q hw hguard hQ hend)

lemma finite_packet_exists
    (hPacket : FinitePacketConstructionInput)
    {w P g : List Digit} {A : Finset Digit} {c : Digit}
    (hw : w ≠ []) (hP : Admissible w P)
    (hguard : SafeGuardFor w g)
    (hproper : ProperAlphabetFor w A c) :
    ∃ k0 : ℕ, ∀ S : Finset ℕ,
      (∀ k ∈ S, k0 ≤ k) →
      ∃ Q : List Digit,
        AdmissibleExtension w P Q ∧ EndsWith Q g ∧
        ∀ x ∈ AvoidingPrefixSet w Q,
          ∀ k ∈ S, AllLabelObligation A c k x :=
  hPacket w P g A c hw hP hguard hproper

theorem finite_stage_compatibility
    (hPacket : FinitePacketConstructionInput)
    (hA : DocumentATheoremAInput)
    (hEdge : EdgeParryPrefixDimensionInput)
    {w P g : List Digit} {A : Finset Digit} {c : Digit}
    (hw : w ≠ []) (hP : Admissible w P)
    (hguard : SafeGuardFor w g)
    (hproper : ProperAlphabetFor w A c) :
    ∃ k0 : ℕ, ∀ S : Finset ℕ,
      (∀ k ∈ S, k0 ≤ k) →
      ∃ Q : List Digit,
        AdmissibleExtension w P Q ∧ EndsWith Q g ∧
        (∀ x ∈ AvoidingPrefixSet w Q,
          ∀ k ∈ S, AllLabelObligation A c k x) ∧
        dimH (SeparatedSet w Q) = dimH (CWord w) := by
  obtain ⟨k0, hk0⟩ :=
    finite_packet_exists hPacket hw hP hguard hproper
  refine ⟨k0, ?_⟩
  intro S hS
  obtain ⟨Q, hext, hend, hobl⟩ := hk0 S hS
  exact ⟨Q, hext, hend, hobl,
    docA_edgeParry_dimension hA hEdge hw hguard
      (admissibleExtension_is_admissible hext) hend⟩

theorem future_finite_coordinate_compatibility
    (hFuture : FeasibleGuardExtensionInput)
    (hA : DocumentATheoremAInput)
    (hEdge : EdgeParryPrefixDimensionInput)
    {w P g : List Digit}
    (hw : w ≠ []) (hP : Admissible w P)
    (hguard : SafeGuardFor w g)
    (O : List FutureCoordinateObligation)
    (hSupported : SupportedAfter P O)
    (hFeasible : FeasibleRelative w P O) :
    ∃ Q : List Digit,
      AdmissibleExtension w P Q ∧ EndsWith Q g ∧
      (∀ x ∈ AvoidingPrefixSet w Q, ∀ o ∈ O, o.Holds x) ∧
      dimH (SeparatedSet w Q) = dimH (CWord w) := by
  obtain ⟨Q, hext, hend, hobl⟩ :=
    hFuture w P g O hw hP hguard hSupported hFeasible
  exact ⟨Q, hext, hend, hobl,
    docA_edgeParry_dimension hA hEdge hw hguard
      (admissibleExtension_is_admissible hext) hend⟩

end Theory.PiDigits.T227FiniteStageCompatibility
