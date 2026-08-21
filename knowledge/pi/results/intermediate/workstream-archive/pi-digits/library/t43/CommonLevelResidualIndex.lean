import TheoryLib.PiDigits.T37CrossBaseCarry
import TheoryLib.PiDigits.T39BalancedCarryMyhillNerode
import TheoryLib.PiDigits.T41ExternallyClockedResidualQuotients
import Mathlib.Data.Fintype.Pigeonhole

/-!
# T43: common-level index of the externally clocked residual system

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file concerns only T37/T39/T41's exact base-16/base-10 carry system under
avoidance of decimal digit `2`.  The external clock supplies the absolute
level, scale context, and future schedule increments.  Persistent state is
only T41's reduced carry and decimal suffix: no absolute schedule position is
retained in it.  Accordingly, the finite-code theorem below does not apply to
schedule-aware controllers that retain the level or other clock information.

The result proves nothing about the digits of `Real.pi`, does not prove or
assume `T37.JMix Real.pi`, and proves neither canonical V1 nor sibling V3.
-/

namespace Theory.PiDigits.T43

open Theory.PiDigits

/-- A concrete balanced state is reachable at external clock level `N`. -/
def ReachableAt (N : ℕ) (q : T39.State) : Prop :=
  T39.Reachable q ∧ q.level = N

/-- Packet widths follow the one actual future schedule tail beginning at `N`.
All states compared at level `N` are tested against this same predicate. -/
def TailLegal : ℕ → List T41.Packet → Prop
  | _, [] => True
  | N, p :: w =>
      p.width = T39.scheduleIncrement N ∧ TailLegal (N + 1) w

/-- The finite continuation language of a persistent residual state when the
external clock currently reads `N`. -/
def ContinuationLanguageAt (N r : ℕ) (q : T41.ResidualState) :
    Set (List T41.Packet) :=
  {w | TailLegal N w ∧ T41.Accepted (T41.balancedContext N) r q w}

/-- Right-language equivalence with one shared external level and schedule. -/
def RightLanguageEquivalentAt (N r : ℕ)
    (q q' : T41.ResidualState) : Prop :=
  ContinuationLanguageAt N r q = ContinuationLanguageAt N r q'

/-- A persistent state is reachable at level `N` when it is induced by a
concrete T39 state reachable at exactly that external level. -/
def PersistentReachableAt (N : ℕ) (q : T41.ResidualState) : Prop :=
  ∃ source : T39.State, ReachableAt N source ∧ T41.residualOf 1 source = q

/-- A persistent-state code preserves all common-level externally clocked
languages when every same-level reachable collision has equal languages. -/
def LanguagePreservingCode {Q : Type*}
    (code : T41.ResidualState → Q) : Prop :=
  ∀ (N : ℕ) (q q' : T41.ResidualState),
    PersistentReachableAt N q → PersistentReachableAt N q' →
      code q = code q' → RightLanguageEquivalentAt N 1 q q'

/-- T39 legality implies that the corresponding packets follow the actual
future external-clock schedule. -/
theorem tailLegal_packetsOfSymbols_of_legal {q : T39.State}
    {w : List T39.Symbol} (hlegal : T39.LegalContinuation q w) :
    TailLegal q.level (T41.packetsOfSymbols w) := by
  induction w generalizing q with
  | nil => simp [TailLegal, T41.packetsOfSymbols]
  | cons a w ih =>
      rw [T39.LegalContinuation] at hlegal
      simp only [T41.packetsOfSymbols, List.map_cons, TailLegal]
      exact ⟨hlegal.1.1, ih hlegal.2⟩

/-- The common external level used for the `K+1` witness family. -/
def familyLevel (K : ℕ) : ℕ := T41.witnessLevel K 1

/-- Concrete reachable source states for the persistent witness family. -/
def familyState (K : ℕ) (j : Fin (K + 1)) : T39.State :=
  T41.witnessState K 1 j

/-- The persistent state stores no `familyLevel`; that level remains external. -/
def familyResidual (K : ℕ) (j : Fin (K + 1)) : T41.ResidualState :=
  T41.residualOf 1 (familyState K j)

/-- The explicit continuation oriented from witness `j`. -/
def familySeparator (K : ℕ) (j : Fin (K + 1)) : List T41.Packet :=
  T41.distinguishingContinuation K 1 j

/-- Every source state in the family is reachable at the same external level. -/
theorem family_reachableAt (K : ℕ) (j : Fin (K + 1)) :
    ReachableAt (familyLevel K) (familyState K j) := by
  exact ⟨T41.witnessState_reachable j, rfl⟩

/-- Every persistent witness is induced by a concrete state reachable at the
common external level. -/
theorem family_persistent_reachableAt (K : ℕ) (j : Fin (K + 1)) :
    PersistentReachableAt (familyLevel K) (familyResidual K j) := by
  exact ⟨familyState K j, family_reachableAt K j, rfl⟩

/-- The explicit separator follows the common future external-clock tail, is
accepted from its oriented witness, and is rejected from every other witness. -/
theorem family_explicit_distinguishingContinuation (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    TailLegal (familyLevel K) (familySeparator K u) ∧
      T41.Accepted (T41.balancedContext (familyLevel K)) 1
        (familyResidual K u) (familySeparator K u) ∧
      ¬ T41.Accepted (T41.balancedContext (familyLevel K)) 1
        (familyResidual K v) (familySeparator K u) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [familyLevel, familySeparator, T41.distinguishingContinuation] using
      tailLegal_packetsOfSymbols_of_legal
        (T41.distinguishingSymbols_legal (M := K) (r := 1) u)
  · simpa [familyLevel, familyResidual, familyState, familySeparator] using
      (T41.distinguishingContinuation_accepted (M := K) (r := 1) u)
  · simpa [familyLevel, familyResidual, familyState, familySeparator] using
      (T41.distinguishingContinuation_rejected_of_ne
        (M := K) (r := 1) huv)

/-- Distinct members of the common-level persistent family have distinct
right languages. -/
theorem family_pairwise_rightLanguage_inequivalent (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ RightLanguageEquivalentAt (familyLevel K) 1
      (familyResidual K u) (familyResidual K v) := by
  intro hequiv
  have hseparator := family_explicit_distinguishingContinuation K huv
  have hmemu : familySeparator K u ∈
      ContinuationLanguageAt (familyLevel K) 1 (familyResidual K u) :=
    ⟨hseparator.1, hseparator.2.1⟩
  have hmemv : familySeparator K u ∈
      ContinuationLanguageAt (familyLevel K) 1 (familyResidual K v) := by
    rw [← hequiv]
    exact hmemu
  exact hseparator.2.2 hmemv.2

/-- Pairwise language separation in particular makes the persistent witness
family an injective family of states. -/
theorem familyResidual_injective (K : ℕ) :
    Function.Injective (familyResidual K) := by
  intro u v hresidual
  by_contra huv
  apply family_pairwise_rightLanguage_inequivalent K huv
  rw [hresidual]
  rfl

/-- For every positive `K`, one common external level contains more than `K`
reachable persistent states with pairwise distinct right languages. -/
theorem commonLevel_moreThan_pairwise_rightLanguage_inequivalent
    (K : ℕ) (_hK : 0 < K) :
    K < Fintype.card (Fin (K + 1)) ∧
      Function.Injective (familyResidual K) ∧
      (∀ j : Fin (K + 1),
        PersistentReachableAt (familyLevel K) (familyResidual K j)) ∧
      ∀ u v : Fin (K + 1), u ≠ v →
        ¬ RightLanguageEquivalentAt (familyLevel K) 1
          (familyResidual K u) (familyResidual K v) := by
  exact ⟨by simp, familyResidual_injective K, family_persistent_reachableAt K,
    fun _ _ huv => family_pairwise_rightLanguage_inequivalent K huv⟩

/-- No map from persistent residual states to any finite type preserves all
common-level continuation languages under the external-clock semantics. -/
theorem no_finite_languagePreserving_persistentStateCode
    {Q : Type*} [Finite Q] (code : T41.ResidualState → Q) :
    ¬ LanguagePreservingCode code := by
  classical
  letI := Fintype.ofFinite Q
  let K := Fintype.card Q
  let f : Fin (K + 1) → Q := fun j => code (familyResidual K j)
  obtain ⟨u, v, huv, hcode⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp [K])
  intro hpreserves
  rw [LanguagePreservingCode] at hpreserves
  have hequiv := hpreserves (familyLevel K) (familyResidual K u) (familyResidual K v)
    (family_persistent_reachableAt K u) (family_persistent_reachableAt K v) (by
      simpa [f] using hcode)
  exact family_pairwise_rightLanguage_inequivalent K huv hequiv

/-- Cardinality-indexed form: in particular, no code into a finite type of
cardinality `K` preserves all externally clocked continuation languages. -/
theorem no_cardinalityK_languagePreserving_persistentStateCode
    {Q : Type*} [Fintype Q] (K : ℕ) (_hcard : Fintype.card Q = K)
    (code : T41.ResidualState → Q) :
    ¬ LanguagePreservingCode code := by
  exact no_finite_languagePreserving_persistentStateCode code

end Theory.PiDigits.T43

#print axioms Theory.PiDigits.T43.tailLegal_packetsOfSymbols_of_legal
#print axioms Theory.PiDigits.T43.family_reachableAt
#print axioms Theory.PiDigits.T43.family_persistent_reachableAt
#print axioms Theory.PiDigits.T43.family_explicit_distinguishingContinuation
#print axioms Theory.PiDigits.T43.family_pairwise_rightLanguage_inequivalent
#print axioms Theory.PiDigits.T43.familyResidual_injective
#print axioms Theory.PiDigits.T43.commonLevel_moreThan_pairwise_rightLanguage_inequivalent
#print axioms Theory.PiDigits.T43.no_finite_languagePreserving_persistentStateCode
#print axioms Theory.PiDigits.T43.no_cardinalityK_languagePreserving_persistentStateCode
