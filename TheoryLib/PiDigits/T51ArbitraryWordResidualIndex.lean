import TheoryLib.PiDigits.T50BackgroundMarkerZero
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Infix

/-!
# T51: arbitrary nonempty-word externally clocked residual index

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file treats one parameter word `w : List (Fin 10)` and requires `w ≠ []`.
It defines exact contiguous avoidance for that one word.  It does not treat the
empty word or a finite set of forbidden words.

The external level and future schedule are shared language parameters, not
fields available to a persistent-state code.  Hence the finite-code theorem
does not cover schedule-aware controllers retaining the level, scale context,
or schedule tail.  Nothing here concerns the decimal digits of `Real.pi`,
`T37.JMix Real.pi`, canonical V1, or sibling V3.
-/

namespace Theory.PiDigits.T51

open Theory.PiDigits

noncomputable section

/-- Exact avoidance of one contiguous finite word. -/
def AvoidsWord (w digits : List (Fin 10)) : Prop := ¬ w <:+: digits

/-- A word containing `d` cannot occur in a digit-`d`-free list. -/
theorem avoidsWord_of_avoidsDigit {w digits : List (Fin 10)} {d : Fin 10}
    (hdw : d ∈ w) (hdigits : T46.AvoidsDigit d digits) :
    AvoidsWord w digits := by
  intro hinfix
  exact hdigits (hinfix.sublist.subset hdw)

/-- The trailing boundary retained to detect occurrences crossing a source /
continuation boundary. -/
def trailingBoundary (w digits : List (Fin 10)) : List (Fin 10) :=
  digits.drop (digits.length - (w.length - 1))

theorem trailingBoundary_subset (w digits : List (Fin 10)) :
    ∀ x ∈ trailingBoundary w digits, x ∈ digits := by
  intro x hx
  exact List.mem_of_mem_drop hx

/-- Retaining the final `|w|-1` source digits loses no possible occurrence:
once the source itself avoids nonempty `w`, the boundary test is equivalent to
testing the complete source followed by the continuation. -/
theorem trailingBoundary_exact {w source continuation : List (Fin 10)}
    (hw : w ≠ []) (hsource : AvoidsWord w source) :
    AvoidsWord w (trailingBoundary w source ++ continuation) ↔
      AvoidsWord w (source ++ continuation) := by
  constructor
  · intro hboundary hocc
    rcases hocc with ⟨a, b, hab⟩
    by_cases hlen : a.length + w.length ≤ source.length
    · apply hsource
      have hpref : a ++ w <+: source ++ continuation := ⟨b, hab⟩
      have hprefSource : a ++ w <+: source :=
        (List.isPrefix_append_of_length (l₁ := a ++ w)
          (l₂ := source) (l₃ := continuation) (by simpa using hlen)).mp hpref
      exact List.infix_append_right.trans hprefSource.isInfix
    · apply hboundary
      have hwlen : 0 < w.length := List.length_pos_iff.mpr hw
      have hk : source.length - (w.length - 1) ≤ a.length := by omega
      refine ⟨a.drop (source.length - (w.length - 1)), b, ?_⟩
      unfold trailingBoundary
      calc
        a.drop (source.length - (w.length - 1)) ++ w ++ b =
            (a ++ (w ++ b)).drop (source.length - (w.length - 1)) := by
              rw [List.drop_append_of_le_length hk, List.append_assoc]
        _ = (source ++ continuation).drop
            (source.length - (w.length - 1)) := by
              apply congrArg
              simpa [List.append_assoc] using hab
        _ = source.drop (source.length - (w.length - 1)) ++ continuation := by
              rw [List.drop_append_of_le_length (Nat.sub_le _ _)]
  · intro hfull hocc
    apply hfull
    apply hocc.trans
    apply List.IsSuffix.isInfix
    refine ⟨source.take (source.length - (w.length - 1)), ?_⟩
    unfold trailingBoundary
    rw [← List.append_assoc, List.take_append_drop]

/-- Persistent word state: T41's exact carry coordinate together with the
finite decimal boundary needed by the one forbidden word. -/
structure WordResidualState where
  carry : T41.ResidualState
  boundary : List (Fin 10)
deriving DecidableEq

/-- Persistent state induced by a concrete source. -/
def wordResidualOf (w : List (Fin 10)) (q : T39.State) : WordResidualState where
  carry := T41.residualOf 1 q
  boundary := trailingBoundary w q.decimalPrefix

/-- Decimal digits supplied by a packet continuation. -/
def packetDigits (packets : List T41.Packet) : List (Fin 10) :=
  packets.flatMap T41.Packet.decimal

/-- The avoidance-independent retained-packet predicate. -/
def RetainedCarryPacket (c : T41.ClockContext) (q : T41.ResidualState)
    (p : T41.Packet) : Prop :=
  T41.packetClockWidth p ∧
    -((T41.nextContext c p.width).a : ℤ) <
      (T41.nextResidual 1 c q p).reducedCarry ∧
    (T41.nextResidual 1 c q p).reducedCarry <
      ((T41.nextContext c p.width).b : ℤ)

/-- Carry/cylinder acceptance with no digit- or word-avoidance test. -/
def CarryAccepted : T41.ClockContext → T41.ResidualState →
    List T41.Packet → Prop
  | _, _, [] => True
  | c, q, p :: packets =>
      RetainedCarryPacket c q p ∧
        CarryAccepted (T41.nextContext c p.width)
          (T41.nextResidual 1 c q p) packets

/-- Exact word-language acceptance from a persistent boundary state.  The
second conjunct checks all occurrences internal to the continuation and all
occurrences crossing its source boundary. -/
def AcceptedForWord (w : List (Fin 10)) (c : T41.ClockContext)
    (q : WordResidualState) (packets : List T41.Packet) : Prop :=
  CarryAccepted c q.carry packets ∧
    AvoidsWord w (q.boundary ++ packetDigits packets)

/-- For a reachable source that already avoids nonempty `w`, residual
acceptance is exactly carry acceptance plus avoidance by the complete source
prefix followed by all continuation digits. -/
theorem acceptedForWord_wordAvoidance_iff
    {w : List (Fin 10)} (hw : w ≠ []) {source : T39.State}
    (hsource : AvoidsWord w source.decimalPrefix)
    (c : T41.ClockContext) (packets : List T41.Packet) :
    AcceptedForWord w c (wordResidualOf w source) packets ↔
      CarryAccepted c (T41.residualOf 1 source) packets ∧
        AvoidsWord w (source.decimalPrefix ++ packetDigits packets) := by
  simp only [AcceptedForWord, wordResidualOf]
  rw [trailingBoundary_exact hw hsource]

/-- Externally clocked continuation language for avoidance of `w`. -/
def ContinuationLanguageAt (w : List (Fin 10)) (N : ℕ)
    (q : WordResidualState) : Set (List T41.Packet) :=
  {packets | T46.TailLegal N packets ∧
    AcceptedForWord w (T41.balancedContext N) q packets}

def RightLanguageEquivalentAt (w : List (Fin 10)) (N : ℕ)
    (q q' : WordResidualState) : Prop :=
  ContinuationLanguageAt w N q = ContinuationLanguageAt w N q'

/-- Arithmetic/cylinder balance with no avoidance condition. -/
def CarryBalanced (q : T39.State) : Prop :=
  q.hexPrefix.length = q.level ∧
  q.decimalPrefix.length = T39.decimalLevel q.level ∧
  T37.ValidPrefix 16 q.level (T37.wordValue q.hexPrefix) ∧
  T37.ValidPrefix 10 (T39.decimalLevel q.level)
    (T37.wordValue q.decimalPrefix) ∧
  (T37.prefixCylinder 16 q.level (T37.wordValue q.hexPrefix) ∩
    T37.prefixCylinder 10 (T39.decimalLevel q.level)
      (T37.wordValue q.decimalPrefix)).Nonempty

def RetainedCarryStep (q : T39.State) (a : T39.Symbol) : Prop :=
  a.decimal.1.length = T39.scheduleIncrement q.level ∧
    CarryBalanced (T39.appendSymbol q a)

def LegalCarryContinuation : T39.State → List T39.Symbol → Prop
  | q, [] => CarryBalanced q
  | q, a :: path => RetainedCarryStep q a ∧
      LegalCarryContinuation (T39.appendSymbol q a) path

def CarryReachable (q : T39.State) : Prop :=
  ∃ path : List T39.Symbol,
    LegalCarryContinuation T39.initialState path ∧
      T39.run T39.initialState path = q

/-- Exact concrete reachability for one forbidden word.  Since every
intermediate decimal prefix is a prefix of the endpoint, endpoint avoidance is
equivalent to avoidance throughout the append-only path. -/
def ReachableAtForWord (w : List (Fin 10)) (N : ℕ) (q : T39.State) : Prop :=
  CarryReachable q ∧ q.level = N ∧ AvoidsWord w q.decimalPrefix

def PersistentReachableAt (w : List (Fin 10)) (N : ℕ)
    (q : WordResidualState) : Prop :=
  ∃ source : T39.State,
    ReachableAtForWord w N source ∧ wordResidualOf w source = q

theorem carryBalanced_of_balancedFor {d : Fin 10} {q : T39.State}
    (hq : T46.BalancedFor d q) : CarryBalanced q := by
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.2⟩

theorem legalCarryContinuation_of_legalFor {d : Fin 10} {q : T39.State}
    {path : List T39.Symbol} (hpath : T46.LegalContinuationFor d q path) :
    LegalCarryContinuation q path := by
  induction path generalizing q with
  | nil =>
      exact carryBalanced_of_balancedFor hpath
  | cons a path ih =>
      rw [T46.LegalContinuationFor] at hpath
      exact ⟨⟨hpath.1.1, carryBalanced_of_balancedFor hpath.1.2⟩,
        ih hpath.2⟩

theorem carryReachable_of_reachableFor {d : Fin 10} {q : T39.State}
    (hq : T46.ReachableFor d q) : CarryReachable q := by
  obtain ⟨path, hlegal, hrun⟩ := hq
  exact ⟨path, legalCarryContinuation_of_legalFor hlegal, hrun⟩

theorem acceptedFor_implies_carryAccepted {d : Fin 10}
    {c : T41.ClockContext} {q : T41.ResidualState}
    {packets : List T41.Packet} (haccepted : T46.AcceptedFor d c 1 q packets) :
    CarryAccepted c q packets := by
  induction packets generalizing c q with
  | nil => trivial
  | cons p packets ih =>
      rw [T46.AcceptedFor] at haccepted
      exact ⟨⟨haccepted.1.1, haccepted.1.2.2⟩, ih haccepted.2⟩

theorem acceptedFor_all_packets_avoid {d : Fin 10}
    {c : T41.ClockContext} {q : T41.ResidualState}
    {packets : List T41.Packet} (haccepted : T46.AcceptedFor d c 1 q packets) :
    ∀ p ∈ packets, T46.PacketAvoidsDigit d p := by
  induction packets generalizing c q with
  | nil => simp
  | cons p packets ih =>
      rw [T46.AcceptedFor] at haccepted
      intro p' hp'
      simp only [List.mem_cons] at hp'
      rcases hp' with rfl | hp'
      · exact haccepted.1.2.1
      · exact ih haccepted.2 p' hp'

theorem acceptedFor_of_carryAccepted_of_packets_avoid {d : Fin 10}
    {c : T41.ClockContext} {q : T41.ResidualState}
    {packets : List T41.Packet} (hcarry : CarryAccepted c q packets)
    (havoid : ∀ p ∈ packets, T46.PacketAvoidsDigit d p) :
    T46.AcceptedFor d c 1 q packets := by
  induction packets generalizing c q with
  | nil => trivial
  | cons p packets ih =>
      rw [CarryAccepted] at hcarry
      rw [T46.AcceptedFor]
      refine ⟨⟨hcarry.1.1, havoid p (by simp), hcarry.1.2⟩, ?_⟩
      exact ih hcarry.2 (fun p' hp' => havoid p' (by simp [hp']))

theorem packetDigits_avoidsDigit {d : Fin 10} {packets : List T41.Packet}
    (havoid : ∀ p ∈ packets, T46.PacketAvoidsDigit d p) :
    T46.AvoidsDigit d (packetDigits packets) := by
  intro hd
  simp only [packetDigits, List.mem_flatMap] at hd
  obtain ⟨p, hp, hdp⟩ := hd
  exact havoid p hp hdp

/-- Data exported by each kernel-checked single-digit witness family. -/
structure DigitWitnessPackage (d : Fin 10) where
  level : ℕ → ℕ
  source : (K : ℕ) → Fin (K + 1) → T39.State
  residual : (K : ℕ) → Fin (K + 1) → T41.ResidualState
  separator : (K : ℕ) → Fin (K + 1) → List T41.Packet
  reachable : ∀ K j, T46.ReachableAtFor d (level K) (source K j)
  residual_eq : ∀ K j, T41.residualOf 1 (source K j) = residual K j
  residual_injective : ∀ K, Function.Injective (residual K)
  tailLegal : ∀ K j, T46.TailLegal (level K) (separator K j)
  accepted : ∀ K j,
    T46.AcceptedFor d (T41.balancedContext (level K)) 1
      (residual K j) (separator K j)
  rejected : ∀ K {u v}, u ≠ v →
    ¬ T46.AcceptedFor d (T41.balancedContext (level K)) 1
      (residual K v) (separator K u)

def zeroPackage : DigitWitnessPackage (0 : Fin 10) where
  level := T50.familyLevel
  source := T50.familyState
  residual := T50.familyResidual
  separator := T50.familySeparator
  reachable := T50.family_reachableAt
  residual_eq := fun _ _ => rfl
  residual_injective := T50.familyResidual_injective
  tailLegal := T50.familySeparator_tailLegal
  accepted := T50.familySeparator_accepted
  rejected := fun K _ _ huv => T50.familySeparator_rejected_of_ne K huv

def onePackage : DigitWitnessPackage (1 : Fin 10) where
  level := T48.familyLevel
  source := T48.familyState
  residual := T48.familyResidual
  separator := T48.familySeparator
  reachable := T48.family_reachableAt
  residual_eq := fun _ _ => rfl
  residual_injective := T48.familyResidual_injective
  tailLegal := T48.familySeparator_tailLegal
  accepted := T48.familySeparator_accepted
  rejected := fun K _ _ huv => T48.familySeparator_rejected_of_ne K huv

def safePackage (d : Fin 10) (hd : T46.SafeSupport d) :
    DigitWitnessPackage d where
  level := T46.familyLevel
  source := T46.familyState
  residual := T46.familyResidual
  separator := T46.familySeparator
  reachable := T46.family_reachableAt_of_safeSupport hd
  residual_eq := fun _ _ => rfl
  residual_injective := T46.familyResidual_injective
  tailLegal := fun K j => by
    simpa [T46.familyLevel, T46.familySeparator,
      T41.distinguishingContinuation] using
      T46.tailLegal_packetsOfSymbols_of_legalFor
        (T46.distinguishingSymbols_legalFor_of_safeSupport
          (M := K) (r := 1) hd j)
  accepted := fun K j =>
    T46.distinguishingContinuation_acceptedFor_of_safeSupport
      (M := K) (r := 1) hd j
  rejected := fun K _ _ huv =>
    T46.distinguishingContinuation_rejectedFor_of_ne
      (d := d) (M := K) (r := 1) huv

/-- Uniform selection of the corresponding checked T50 witness family. -/
def packageForDigit (d : Fin 10) : DigitWitnessPackage d := by
  by_cases hzero : d = 0
  · subst d
    exact zeroPackage
  by_cases hone : d = 1
  · subst d
    exact onePackage
  exact safePackage d ⟨hzero, hone⟩

theorem package_source_avoidsDigit {d : Fin 10} (P : DigitWitnessPackage d)
    (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit d (P.source K j).decimalPrefix := by
  exact (T46.reachableFor_balanced (P.reachable K j).1).2.2.2.2.1

theorem package_boundary_avoidsDigit {w : List (Fin 10)} {d : Fin 10}
    (P : DigitWitnessPackage d) (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit d
      (trailingBoundary w (P.source K j).decimalPrefix) := by
  intro hd
  exact package_source_avoidsDigit P K j
    (trailingBoundary_subset w (P.source K j).decimalPrefix d hd)

theorem package_separator_packetDigits_avoidsDigit {d : Fin 10}
    (P : DigitWitnessPackage d) (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit d (packetDigits (P.separator K j)) := by
  exact packetDigits_avoidsDigit
    (acceptedFor_all_packets_avoid (P.accepted K j))

theorem package_sourceContinuation_avoidsDigit {w : List (Fin 10)}
    {d : Fin 10} (P : DigitWitnessPackage d) (K : ℕ)
    (j : Fin (K + 1)) :
    T46.AvoidsDigit d
      (trailingBoundary w (P.source K j).decimalPrefix ++
        packetDigits (P.separator K j)) := by
  intro hd
  rw [List.mem_append] at hd
  exact hd.elim (package_boundary_avoidsDigit P K j)
    (package_separator_packetDigits_avoidsDigit P K j)

/-- The entire concrete source prefix followed by the continuation is
digit-`d`-free.  This statement uses the full source, not merely its retained
boundary. -/
theorem package_fullSourceContinuation_avoidsDigit {d : Fin 10}
    (P : DigitWitnessPackage d) (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit d
      ((P.source K j).decimalPrefix ++ packetDigits (P.separator K j)) := by
  intro hd
  rw [List.mem_append] at hd
  exact hd.elim (package_source_avoidsDigit P K j)
    (package_separator_packetDigits_avoidsDigit P K j)

/-- The entire accepted source-continuation path is directly digit-`d`-free
and therefore `w`-free, including every occurrence crossing the source /
continuation boundary. -/
theorem package_fullSourceContinuation_avoidsWord {w : List (Fin 10)}
    {d : Fin 10} (hdw : d ∈ w) (P : DigitWitnessPackage d)
    (K : ℕ) (j : Fin (K + 1)) :
    AvoidsWord w
      ((P.source K j).decimalPrefix ++ packetDigits (P.separator K j)) :=
  avoidsWord_of_avoidsDigit hdw
    (package_fullSourceContinuation_avoidsDigit P K j)

/-- The retained source boundary followed by the continuation is word-free;
this is the exact avoidance conjunct used by the residual language. -/
theorem package_sourceContinuation_avoidsWord {w : List (Fin 10)}
    {d : Fin 10} (hdw : d ∈ w) (P : DigitWitnessPackage d)
    (K : ℕ) (j : Fin (K + 1)) :
    AvoidsWord w
      (trailingBoundary w (P.source K j).decimalPrefix ++
        packetDigits (P.separator K j)) :=
  avoidsWord_of_avoidsDigit hdw
    (package_sourceContinuation_avoidsDigit P K j)

def packageWordResidual {d : Fin 10} (P : DigitWitnessPackage d)
    (w : List (Fin 10)) (K : ℕ) (j : Fin (K + 1)) : WordResidualState :=
  wordResidualOf w (P.source K j)

theorem packageWordResidual_injective {d : Fin 10}
    (P : DigitWitnessPackage d) (w : List (Fin 10)) (K : ℕ) :
    Function.Injective (packageWordResidual P w K) := by
  intro u v huv
  apply P.residual_injective K
  have hcarry := congrArg WordResidualState.carry huv
  simpa [packageWordResidual, wordResidualOf, P.residual_eq] using hcarry

theorem package_persistentReachableAt {w : List (Fin 10)} {d : Fin 10}
    (hdw : d ∈ w) (P : DigitWitnessPackage d) (K : ℕ)
    (j : Fin (K + 1)) :
    PersistentReachableAt w (P.level K) (packageWordResidual P w K j) := by
  refine ⟨P.source K j, ⟨?_, (P.reachable K j).2,
    avoidsWord_of_avoidsDigit hdw (package_source_avoidsDigit P K j)⟩, rfl⟩
  exact carryReachable_of_reachableFor (P.reachable K j).1

theorem package_separator_acceptedForWord {w : List (Fin 10)} {d : Fin 10}
    (hdw : d ∈ w) (P : DigitWitnessPackage d) (K : ℕ)
    (j : Fin (K + 1)) :
    AcceptedForWord w (T41.balancedContext (P.level K))
      (packageWordResidual P w K j) (P.separator K j) := by
  constructor
  · simpa [packageWordResidual, wordResidualOf, P.residual_eq] using
      acceptedFor_implies_carryAccepted (P.accepted K j)
  · exact package_sourceContinuation_avoidsWord hdw P K j

/-- Avoidance-independent rejection: the other witness fails even the pure
carry/cylinder predicate.  No word- or digit-avoidance premise occurs here. -/
theorem package_separator_rejectedByCarry {d : Fin 10}
    (P : DigitWitnessPackage d) (K : ℕ) {u v : Fin (K + 1)}
    (huv : u ≠ v) :
    ¬ CarryAccepted (T41.balancedContext (P.level K))
      (P.residual K v) (P.separator K u) := by
  intro hcarry
  apply P.rejected K huv
  exact acceptedFor_of_carryAccepted_of_packets_avoid hcarry
    (acceptedFor_all_packets_avoid (P.accepted K u))

theorem package_separator_rejectedForWord {w : List (Fin 10)}
    {d : Fin 10} (P : DigitWitnessPackage d) (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ AcceptedForWord w (T41.balancedContext (P.level K))
      (packageWordResidual P w K v) (P.separator K u) := by
  intro haccepted
  apply package_separator_rejectedByCarry P K huv
  simpa [packageWordResidual, wordResidualOf, P.residual_eq] using haccepted.1

theorem package_pairwise_rightLanguage_inequivalent
    {w : List (Fin 10)} {d : Fin 10} (hdw : d ∈ w)
    (P : DigitWitnessPackage d) (K : ℕ) {u v : Fin (K + 1)}
    (huv : u ≠ v) :
    ¬ RightLanguageEquivalentAt w (P.level K)
      (packageWordResidual P w K u) (packageWordResidual P w K v) := by
  intro hequiv
  have hu : P.separator K u ∈
      ContinuationLanguageAt w (P.level K) (packageWordResidual P w K u) :=
    ⟨P.tailLegal K u, package_separator_acceptedForWord hdw P K u⟩
  have hv : P.separator K u ∈
      ContinuationLanguageAt w (P.level K) (packageWordResidual P w K v) := by
    rw [← hequiv]
    exact hu
  exact package_separator_rejectedForWord P K huv hv.2

/-- Exact one-sided separators for every nonempty decimal word. -/
theorem everyNonemptyWord_explicit_oneSidedSeparators
    (w : List (Fin 10)) (hw : w ≠ []) (K : ℕ) :
    ∃ N : ℕ, ∃ f : Fin (K + 1) → WordResidualState,
      ∃ separator : Fin (K + 1) → List T41.Packet,
      Function.Injective f ∧
      (∀ j, PersistentReachableAt w N (f j)) ∧
      ∀ u v, u ≠ v →
        T46.TailLegal N (separator u) ∧
        AcceptedForWord w (T41.balancedContext N) (f u) (separator u) ∧
        ¬ AcceptedForWord w (T41.balancedContext N) (f v) (separator u) := by
  let d := w.head hw
  have hdw : d ∈ w := List.head_mem hw
  let P := packageForDigit d
  refine ⟨P.level K, packageWordResidual P w K, P.separator K,
    packageWordResidual_injective P w K,
    package_persistentReachableAt hdw P K, ?_⟩
  intro u v huv
  exact ⟨P.tailLegal K u, package_separator_acceptedForWord hdw P K u,
    package_separator_rejectedForWord P K huv⟩

/-- Fully exposed separator certificate for every nonempty word: a selected
digit in `w`, concrete source states, full-path digit and word avoidance,
exact word-language acceptance, and avoidance-independent carry rejection. -/
theorem everyNonemptyWord_exactSeparatorCertificate
    (w : List (Fin 10)) (hw : w ≠ []) (K : ℕ) :
    ∃ d : Fin 10, d ∈ w ∧ ∃ N : ℕ,
      ∃ source : Fin (K + 1) → T39.State,
      ∃ f : Fin (K + 1) → WordResidualState,
      ∃ separator : Fin (K + 1) → List T41.Packet,
      (∀ j, f j = wordResidualOf w (source j)) ∧
      Function.Injective f ∧
      (∀ j, PersistentReachableAt w N (f j)) ∧
      ∀ u v, u ≠ v →
        T46.AvoidsDigit d
          ((source u).decimalPrefix ++ packetDigits (separator u)) ∧
        AvoidsWord w
          ((source u).decimalPrefix ++ packetDigits (separator u)) ∧
        T46.TailLegal N (separator u) ∧
        AcceptedForWord w (T41.balancedContext N) (f u) (separator u) ∧
        ¬ CarryAccepted (T41.balancedContext N) (f v).carry (separator u) ∧
        ¬ AcceptedForWord w (T41.balancedContext N) (f v) (separator u) := by
  let d := w.head hw
  have hdw : d ∈ w := List.head_mem hw
  let P := packageForDigit d
  refine ⟨d, hdw, P.level K, P.source K, packageWordResidual P w K,
    P.separator K, fun _ => rfl, packageWordResidual_injective P w K,
    package_persistentReachableAt hdw P K, ?_⟩
  intro u v huv
  refine ⟨package_fullSourceContinuation_avoidsDigit P K u,
    package_fullSourceContinuation_avoidsWord hdw P K u,
    P.tailLegal K u, package_separator_acceptedForWord hdw P K u, ?_,
    package_separator_rejectedForWord P K huv⟩
  simpa [packageWordResidual, wordResidualOf, P.residual_eq] using
    package_separator_rejectedByCarry P K huv

/-- Arbitrarily large pairwise continuation-language-inequivalent families at
one common external level, for every nonempty forbidden word. -/
theorem everyNonemptyWord_commonLevel_moreThan_pairwise_inequivalent
    (w : List (Fin 10)) (hw : w ≠ []) (K : ℕ) :
    ∃ N : ℕ, ∃ f : Fin (K + 1) → WordResidualState,
      K < Fintype.card (Fin (K + 1)) ∧
      Function.Injective f ∧
      (∀ j, PersistentReachableAt w N (f j)) ∧
      ∀ u v, u ≠ v → ¬ RightLanguageEquivalentAt w N (f u) (f v) := by
  let d := w.head hw
  have hdw : d ∈ w := List.head_mem hw
  let P := packageForDigit d
  exact ⟨P.level K, packageWordResidual P w K, by simp,
    packageWordResidual_injective P w K,
    package_persistentReachableAt hdw P K,
    fun _ _ huv => package_pairwise_rightLanguage_inequivalent hdw P K huv⟩

def InfiniteContinuationLanguageIndex (w : List (Fin 10)) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, ∃ f : Fin (K + 1) → WordResidualState,
    K < Fintype.card (Fin (K + 1)) ∧
    Function.Injective f ∧
    (∀ j, PersistentReachableAt w N (f j)) ∧
    ∀ u v, u ≠ v → ¬ RightLanguageEquivalentAt w N (f u) (f v)

/-- Every nonempty decimal word has infinite externally clocked continuation-
language index. -/
theorem everyNonemptyWord_infiniteContinuationLanguageIndex
    (w : List (Fin 10)) (hw : w ≠ []) :
    InfiniteContinuationLanguageIndex w := by
  intro K
  exact everyNonemptyWord_commonLevel_moreThan_pairwise_inequivalent w hw K

def LanguagePreservingPersistentStateCode (w : List (Fin 10)) {Q : Type*}
    (code : WordResidualState → Q) : Prop :=
  ∀ (N : ℕ) (q q' : WordResidualState),
    PersistentReachableAt w N q → PersistentReachableAt w N q' →
      code q = code q' → RightLanguageEquivalentAt w N q q'

/-- No code into a finite type preserves the exact word-avoidance continuation
languages of all reachable persistent states, for any nonempty word. -/
theorem everyNonemptyWord_no_finite_languagePreserving_persistentStateCode
    (w : List (Fin 10)) (hw : w ≠ []) {Q : Type*} [Finite Q]
    (code : WordResidualState → Q) :
    ¬ LanguagePreservingPersistentStateCode w code := by
  classical
  letI := Fintype.ofFinite Q
  let K := Fintype.card Q
  obtain ⟨N, f, hcard, _hinjective, hreachable, hinequivalent⟩ :=
    everyNonemptyWord_infiniteContinuationLanguageIndex w hw K
  let coded : Fin (K + 1) → Q := fun j => code (f j)
  obtain ⟨u, v, huv, hcode⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt coded hcard
  intro hpreserves
  have hequiv := hpreserves N (f u) (f v) (hreachable u) (hreachable v) (by
    simpa [coded] using hcode)
  exact hinequivalent u v huv hequiv

end

end Theory.PiDigits.T51

#print axioms Theory.PiDigits.T51.everyNonemptyWord_explicit_oneSidedSeparators
#print axioms Theory.PiDigits.T51.acceptedForWord_wordAvoidance_iff
#print axioms Theory.PiDigits.T51.everyNonemptyWord_exactSeparatorCertificate
#print axioms Theory.PiDigits.T51.package_fullSourceContinuation_avoidsWord
#print axioms Theory.PiDigits.T51.package_separator_rejectedByCarry
#print axioms Theory.PiDigits.T51.everyNonemptyWord_commonLevel_moreThan_pairwise_inequivalent
#print axioms Theory.PiDigits.T51.everyNonemptyWord_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T51.everyNonemptyWord_no_finite_languagePreserving_persistentStateCode
