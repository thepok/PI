import TheoryLib.PiDigits.T50BackgroundMarkerZero
import TheoryLib.PiDigits.T51ArbitraryWordResidualIndex
import Mathlib.Data.Fintype.Pigeonhole

/-!
# T52: simultaneous finite-family externally clocked residual index

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file treats a finite nonempty family `F` of nonempty decimal words under
the explicit hypothesis that one digit occurs in every member of `F`.  It does
not cover the empty word or families with no common digit.

The external level and future schedule are shared language parameters, not
fields available to a persistent-state code.  Hence the finite-code theorem
does not cover schedule-aware controllers retaining the level, scale context,
or schedule tail.  Nothing here concerns the decimal digits of `Real.pi`,
`T37.JMix Real.pi`, canonical V1, or sibling V3.
-/

namespace Theory.PiDigits.T52

open Theory.PiDigits

noncomputable section

abbrev DecimalWord := List (Fin 10)

/-- Simultaneous avoidance of every word in a finite family. -/
def AvoidsFamily (F : Finset DecimalWord) (digits : DecimalWord) : Prop :=
  ∀ w ∈ F, T51.AvoidsWord w digits

/-- The common-digit condition used by the shared witness construction. -/
def HasCommonDigit (F : Finset DecimalWord) : Prop :=
  ∃ d : Fin 10, ∀ w ∈ F, d ∈ w

theorem avoidsFamily_of_avoidsDigit {F : Finset DecimalWord} {d : Fin 10}
    (hdF : ∀ w ∈ F, d ∈ w) {digits : DecimalWord}
    (hdigits : T46.AvoidsDigit d digits) : AvoidsFamily F digits := by
  intro w hw
  exact T51.avoidsWord_of_avoidsDigit (hdF w hw) hdigits

/-- Persistent simultaneous state: one exact carry coordinate and the T51
boundary required by each member of `F`. -/
structure FamilyResidualState (F : Finset DecimalWord) where
  carry : T41.ResidualState
  boundary : ∀ _w : {w // w ∈ F}, DecimalWord

/-- Simultaneous persistent state induced by one concrete source. -/
def familyResidualOf (F : Finset DecimalWord) (source : T39.State) :
    FamilyResidualState F where
  carry := T41.residualOf 1 source
  boundary := fun w => T51.trailingBoundary w.1 source.decimalPrefix

/-- Exact family-language acceptance.  Each indexed boundary checks internal
continuation occurrences and occurrences crossing that source boundary. -/
def AcceptedForFamily (F : Finset DecimalWord) (c : T41.ClockContext)
    (q : FamilyResidualState F) (packets : List T41.Packet) : Prop :=
  T51.CarryAccepted c q.carry packets ∧
    ∀ w : {w // w ∈ F},
      T51.AvoidsWord w.1 (q.boundary w ++ T51.packetDigits packets)

/-- For sources already avoiding every nonempty member, the retained family
boundaries give exactly full-source simultaneous avoidance. -/
theorem acceptedForFamily_sourceBoundary_iff
    {F : Finset DecimalWord} (hwords : ∀ w ∈ F, w ≠ [])
    {source : T39.State} (hsource : AvoidsFamily F source.decimalPrefix)
    (c : T41.ClockContext) (packets : List T41.Packet) :
    AcceptedForFamily F c (familyResidualOf F source) packets ↔
      T51.CarryAccepted c (T41.residualOf 1 source) packets ∧
        AvoidsFamily F
          (source.decimalPrefix ++ T51.packetDigits packets) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro w hw
    let wi : {w // w ∈ F} := ⟨w, hw⟩
    have hboundary := h.2 wi
    exact (T51.trailingBoundary_exact (hwords w hw) (hsource w hw)).mp
      (by simpa [familyResidualOf, wi] using hboundary)
  · intro h
    refine ⟨h.1, ?_⟩
    intro wi
    have hfull := h.2 wi.1 wi.2
    exact (T51.trailingBoundary_exact (hwords wi.1 wi.2)
      (hsource wi.1 wi.2)).mpr hfull

/-- Externally clocked continuation language for simultaneous avoidance. -/
def ContinuationLanguageAt (F : Finset DecimalWord) (N : ℕ)
    (q : FamilyResidualState F) : Set (List T41.Packet) :=
  {packets | T46.TailLegal N packets ∧
    AcceptedForFamily F (T41.balancedContext N) q packets}

def RightLanguageEquivalentAt (F : Finset DecimalWord) (N : ℕ)
    (q q' : FamilyResidualState F) : Prop :=
  ContinuationLanguageAt F N q = ContinuationLanguageAt F N q'

/-- Concrete reachability while simultaneously avoiding all source words. -/
def ReachableAtForFamily (F : Finset DecimalWord) (N : ℕ)
    (source : T39.State) : Prop :=
  T51.CarryReachable source ∧ source.level = N ∧
    AvoidsFamily F source.decimalPrefix

def PersistentReachableAt (F : Finset DecimalWord) (N : ℕ)
    (q : FamilyResidualState F) : Prop :=
  ∃ source : T39.State,
    ReachableAtForFamily F N source ∧ familyResidualOf F source = q

/-- The T51 common-digit package viewed as a simultaneous-family residual. -/
def packageFamilyResidual {d : Fin 10} (P : T51.DigitWitnessPackage d)
    (F : Finset DecimalWord) (K : ℕ) (j : Fin (K + 1)) :
    FamilyResidualState F :=
  familyResidualOf F (P.source K j)

theorem packageFamilyResidual_injective {d : Fin 10}
    (P : T51.DigitWitnessPackage d) (F : Finset DecimalWord) (K : ℕ) :
    Function.Injective (packageFamilyResidual P F K) := by
  intro u v huv
  apply P.residual_injective K
  have hcarry := congrArg (FamilyResidualState.carry) huv
  simpa [packageFamilyResidual, familyResidualOf, P.residual_eq] using hcarry

theorem package_source_avoidsFamily {F : Finset DecimalWord} {d : Fin 10}
    (hdF : ∀ w ∈ F, d ∈ w) (P : T51.DigitWitnessPackage d)
    (K : ℕ) (j : Fin (K + 1)) :
    AvoidsFamily F (P.source K j).decimalPrefix :=
  avoidsFamily_of_avoidsDigit hdF (T51.package_source_avoidsDigit P K j)

theorem package_persistentReachableAt {F : Finset DecimalWord} {d : Fin 10}
    (hdF : ∀ w ∈ F, d ∈ w) (P : T51.DigitWitnessPackage d)
    (K : ℕ) (j : Fin (K + 1)) :
    PersistentReachableAt F (P.level K) (packageFamilyResidual P F K j) := by
  refine ⟨P.source K j, ⟨?_, (P.reachable K j).2,
    package_source_avoidsFamily hdF P K j⟩, rfl⟩
  exact T51.carryReachable_of_reachableFor (P.reachable K j).1

/-- The complete shared source-continuation path avoids the common digit and
hence simultaneously avoids every word in `F`, including boundary crossings. -/
theorem package_fullSourceContinuation_avoidsFamily
    {F : Finset DecimalWord} {d : Fin 10} (hdF : ∀ w ∈ F, d ∈ w)
    (P : T51.DigitWitnessPackage d) (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit d
        ((P.source K j).decimalPrefix ++
          T51.packetDigits (P.separator K j)) ∧
      AvoidsFamily F
        ((P.source K j).decimalPrefix ++
          T51.packetDigits (P.separator K j)) := by
  have hdigit := T51.package_fullSourceContinuation_avoidsDigit P K j
  exact ⟨hdigit, avoidsFamily_of_avoidsDigit hdF hdigit⟩

theorem package_separator_acceptedForFamily
    {F : Finset DecimalWord} {d : Fin 10} (hdF : ∀ w ∈ F, d ∈ w)
    (P : T51.DigitWitnessPackage d) (K : ℕ) (j : Fin (K + 1)) :
    AcceptedForFamily F (T41.balancedContext (P.level K))
      (packageFamilyResidual P F K j) (P.separator K j) := by
  constructor
  · simpa [packageFamilyResidual, familyResidualOf, P.residual_eq] using
      T51.acceptedFor_implies_carryAccepted (P.accepted K j)
  · intro wi
    apply T51.avoidsWord_of_avoidsDigit (hdF wi.1 wi.2)
    simpa [packageFamilyResidual, familyResidualOf] using
      (T51.package_sourceContinuation_avoidsDigit
        (w := wi.1) P K j)

/-- Avoidance-independent one-sided rejection: the paired state fails the
pure carry/cylinder predicate before any family-word test is consulted. -/
theorem package_separator_rejectedByCarry {d : Fin 10}
    (P : T51.DigitWitnessPackage d) (K : ℕ) {u v : Fin (K + 1)}
    (huv : u ≠ v) :
    ¬ T51.CarryAccepted (T41.balancedContext (P.level K))
      (P.residual K v) (P.separator K u) :=
  T51.package_separator_rejectedByCarry P K huv

theorem package_separator_rejectedForFamily
    {F : Finset DecimalWord} {d : Fin 10}
    (P : T51.DigitWitnessPackage d) (K : ℕ) {u v : Fin (K + 1)}
    (huv : u ≠ v) :
    ¬ AcceptedForFamily F (T41.balancedContext (P.level K))
      (packageFamilyResidual P F K v) (P.separator K u) := by
  intro haccepted
  apply package_separator_rejectedByCarry P K huv
  simpa [packageFamilyResidual, familyResidualOf, P.residual_eq] using
    haccepted.1

theorem package_pairwise_rightLanguage_inequivalent
    {F : Finset DecimalWord} {d : Fin 10} (hdF : ∀ w ∈ F, d ∈ w)
    (P : T51.DigitWitnessPackage d) (K : ℕ) {u v : Fin (K + 1)}
    (huv : u ≠ v) :
    ¬ RightLanguageEquivalentAt F (P.level K)
      (packageFamilyResidual P F K u) (packageFamilyResidual P F K v) := by
  intro hequiv
  have hu : P.separator K u ∈
      ContinuationLanguageAt F (P.level K) (packageFamilyResidual P F K u) :=
    ⟨P.tailLegal K u, package_separator_acceptedForFamily hdF P K u⟩
  have hv : P.separator K u ∈
      ContinuationLanguageAt F (P.level K) (packageFamilyResidual P F K v) := by
    rw [← hequiv]
    exact hu
  exact package_separator_rejectedForFamily P K huv hv.2

/-- Fully exposed simultaneous separator certificate.  One selected package
supplies all sources and continuations for the whole finite family. -/
theorem commonDigitFamily_exactSeparatorCertificate
    (F : Finset DecimalWord) (hF : F.Nonempty)
    (hwords : ∀ w ∈ F, w ≠ []) (d : Fin 10)
    (hdF : ∀ w ∈ F, d ∈ w) (K : ℕ) :
    ∃ N : ℕ, ∃ source : Fin (K + 1) → T39.State,
      ∃ f : Fin (K + 1) → FamilyResidualState F,
      ∃ separator : Fin (K + 1) → List T41.Packet,
      F.Nonempty ∧ (∀ w ∈ F, w ≠ []) ∧
      (∀ j, f j = familyResidualOf F (source j)) ∧
      Function.Injective f ∧
      (∀ j, PersistentReachableAt F N (f j)) ∧
      ∀ u v, u ≠ v →
        T46.AvoidsDigit d
          ((source u).decimalPrefix ++ T51.packetDigits (separator u)) ∧
        AvoidsFamily F
          ((source u).decimalPrefix ++ T51.packetDigits (separator u)) ∧
        T46.TailLegal N (separator u) ∧
        AcceptedForFamily F (T41.balancedContext N) (f u) (separator u) ∧
        ¬ T51.CarryAccepted (T41.balancedContext N) (f v).carry
          (separator u) ∧
        ¬ AcceptedForFamily F (T41.balancedContext N) (f v)
          (separator u) := by
  let P := T51.packageForDigit d
  refine ⟨P.level K, P.source K, packageFamilyResidual P F K,
    P.separator K, hF, hwords, fun _ => rfl,
    packageFamilyResidual_injective P F K,
    package_persistentReachableAt hdF P K, ?_⟩
  intro u v huv
  have havoid := package_fullSourceContinuation_avoidsFamily hdF P K u
  refine ⟨havoid.1, havoid.2, P.tailLegal K u,
    package_separator_acceptedForFamily hdF P K u, ?_,
    package_separator_rejectedForFamily P K huv⟩
  simpa [packageFamilyResidual, familyResidualOf, P.residual_eq] using
    package_separator_rejectedByCarry P K huv

/-- The carry-only oriented separator statement, with every family-domain
hypothesis explicit in the theorem signature. -/
theorem commonDigitFamily_carryOnly_oneSidedSeparators
    (F : Finset DecimalWord) (hF : F.Nonempty)
    (hwords : ∀ w ∈ F, w ≠ []) (d : Fin 10)
    (hdF : ∀ w ∈ F, d ∈ w) (K : ℕ) :
    ∃ N : ℕ, ∃ f : Fin (K + 1) → FamilyResidualState F,
      ∃ separator : Fin (K + 1) → List T41.Packet,
      Function.Injective f ∧
      (∀ j, PersistentReachableAt F N (f j)) ∧
      ∀ u v, u ≠ v →
        T46.TailLegal N (separator u) ∧
        AcceptedForFamily F (T41.balancedContext N) (f u) (separator u) ∧
        ¬ T51.CarryAccepted (T41.balancedContext N) (f v).carry
          (separator u) := by
  obtain ⟨N, source, f, separator, _hF, _hwords, _hsource,
    hinjective, hreachable, hseparator⟩ :=
    commonDigitFamily_exactSeparatorCertificate F hF hwords d hdF K
  refine ⟨N, f, separator, hinjective, hreachable, ?_⟩
  intro u v huv
  have h := hseparator u v huv
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Arbitrarily large pairwise inequivalent reachable families occur at one
shared external level. -/
theorem commonDigitFamily_commonLevel_moreThan_pairwise_inequivalent
    (F : Finset DecimalWord) (hF : F.Nonempty)
    (hwords : ∀ w ∈ F, w ≠ []) (d : Fin 10)
    (hdF : ∀ w ∈ F, d ∈ w) (K : ℕ) :
    ∃ N : ℕ, ∃ f : Fin (K + 1) → FamilyResidualState F,
      K < Fintype.card (Fin (K + 1)) ∧
      Function.Injective f ∧
      (∀ j, PersistentReachableAt F N (f j)) ∧
      ∀ u v, u ≠ v → ¬ RightLanguageEquivalentAt F N (f u) (f v) := by
  obtain ⟨N, source, f, separator, _hF, _hwords, _hsource,
    hinjective, hreachable, hseparator⟩ :=
    commonDigitFamily_exactSeparatorCertificate F hF hwords d hdF K
  refine ⟨N, f, by simp, hinjective, hreachable, ?_⟩
  intro u v huv hequiv
  have hsep := hseparator u v huv
  have hu : separator u ∈ ContinuationLanguageAt F N (f u) :=
    ⟨hsep.2.2.1, hsep.2.2.2.1⟩
  have hv : separator u ∈ ContinuationLanguageAt F N (f v) := by
    rw [← hequiv]
    exact hu
  exact hsep.2.2.2.2.2 hv.2

def InfiniteContinuationLanguageIndex (F : Finset DecimalWord) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, ∃ f : Fin (K + 1) → FamilyResidualState F,
    K < Fintype.card (Fin (K + 1)) ∧
    Function.Injective f ∧
    (∀ j, PersistentReachableAt F N (f j)) ∧
    ∀ u v, u ≠ v → ¬ RightLanguageEquivalentAt F N (f u) (f v)

/-- Every finite nonempty family of nonempty words sharing a digit has
infinite externally clocked simultaneous continuation-language index. -/
theorem commonDigitFamily_infiniteContinuationLanguageIndex
    (F : Finset DecimalWord) (hF : F.Nonempty)
    (hwords : ∀ w ∈ F, w ≠ []) (hcommon : HasCommonDigit F) :
    InfiniteContinuationLanguageIndex F := by
  obtain ⟨d, hdF⟩ := hcommon
  intro K
  exact commonDigitFamily_commonLevel_moreThan_pairwise_inequivalent
    F hF hwords d hdF K

def LanguagePreservingPersistentStateCode (F : Finset DecimalWord)
    {Q : Type*} (code : FamilyResidualState F → Q) : Prop :=
  ∀ (N : ℕ) (q q' : FamilyResidualState F),
    PersistentReachableAt F N q → PersistentReachableAt F N q' →
      code q = code q' → RightLanguageEquivalentAt F N q q'

/-- No code into a finite type preserves all simultaneous family languages of
reachable persistent states under the shared external clock. -/
theorem commonDigitFamily_no_finite_languagePreserving_persistentStateCode
    (F : Finset DecimalWord) (hF : F.Nonempty)
    (hwords : ∀ w ∈ F, w ≠ []) (hcommon : HasCommonDigit F)
    {Q : Type*} [Finite Q] (code : FamilyResidualState F → Q) :
    ¬ LanguagePreservingPersistentStateCode F code := by
  classical
  letI := Fintype.ofFinite Q
  let K := Fintype.card Q
  obtain ⟨N, f, hcard, _hinjective, hreachable, hinequivalent⟩ :=
    commonDigitFamily_infiniteContinuationLanguageIndex F hF hwords hcommon K
  let coded : Fin (K + 1) → Q := fun j => code (f j)
  obtain ⟨u, v, huv, hcode⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt coded hcard
  intro hpreserves
  have hequiv := hpreserves N (f u) (f v) (hreachable u) (hreachable v) (by
    simpa [coded] using hcode)
  exact hinequivalent u v huv hequiv

end

end Theory.PiDigits.T52

#print axioms Theory.PiDigits.T52.acceptedForFamily_sourceBoundary_iff
#print axioms Theory.PiDigits.T52.package_fullSourceContinuation_avoidsFamily
#print axioms Theory.PiDigits.T52.package_separator_rejectedByCarry
#print axioms Theory.PiDigits.T52.commonDigitFamily_exactSeparatorCertificate
#print axioms Theory.PiDigits.T52.commonDigitFamily_carryOnly_oneSidedSeparators
#print axioms Theory.PiDigits.T52.commonDigitFamily_commonLevel_moreThan_pairwise_inequivalent
#print axioms Theory.PiDigits.T52.commonDigitFamily_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T52.commonDigitFamily_no_finite_languagePreserving_persistentStateCode
