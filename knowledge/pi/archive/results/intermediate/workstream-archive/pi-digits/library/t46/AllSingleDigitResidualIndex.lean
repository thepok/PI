import TheoryLib.PiDigits.T37CrossBaseCarry
import TheoryLib.PiDigits.T43CommonLevelResidualIndex

/-!
# T46: all safe single-digit externally clocked residual systems

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file studies only the abstract externally clocked base-16/base-10 carry
system obtained by forbidding one fixed decimal digit.  It imports the
kernel-checked T37 and T43 modules, but does not use the unverified T45 note as
a premise.  The external level, scale context, and schedule tail are not
persistent-state fields.

The infinite-index conclusion below is restricted to forbidden digits 2
through 9.  No such conclusion is made for digits 0 or 1.  The digit-1 result
only says that T43's unchanged one-hot source witnesses are not reachable; it
does not say that the digit-1 system has finite index.  Nothing here concerns
arbitrary forbidden words, the digits of `Real.pi`, `T37.JMix Real.pi`,
canonical V1, or sibling V3.
-/

namespace Theory.PiDigits.T46

open Theory.PiDigits

noncomputable section

/-- Avoidance of one fixed decimal digit. -/
def AvoidsDigit (d : Fin 10) (digits : List (Fin 10)) : Prop := d ∉ digits

/-- T39 balance with digit-2 avoidance replaced by avoidance of `d`. -/
def BalancedFor (d : Fin 10) (q : T39.State) : Prop :=
  q.hexPrefix.length = q.level ∧
  q.decimalPrefix.length = T39.decimalLevel q.level ∧
  T37.ValidPrefix 16 q.level (T37.wordValue q.hexPrefix) ∧
  T37.ValidPrefix 10 (T39.decimalLevel q.level)
    (T37.wordValue q.decimalPrefix) ∧
  AvoidsDigit d q.decimalPrefix ∧
  (T37.prefixCylinder 16 q.level (T37.wordValue q.hexPrefix) ∩
    T37.prefixCylinder 10 (T39.decimalLevel q.level)
      (T37.wordValue q.decimalPrefix)).Nonempty

/-- A schedule-legal transition whose target avoids `d`. -/
def RetainedStepFor (d : Fin 10) (q : T39.State) (a : T39.Symbol) : Prop :=
  a.decimal.1.length = T39.scheduleIncrement q.level ∧
    BalancedFor d (T39.appendSymbol q a)

/-- Concrete finite paths in the digit-`d` system. -/
def LegalContinuationFor (d : Fin 10) : T39.State → List T39.Symbol → Prop
  | q, [] => BalancedFor d q
  | q, a :: w => RetainedStepFor d q a ∧
      LegalContinuationFor d (T39.appendSymbol q a) w

/-- Reachability from T39's empty source in the digit-`d` system. -/
def ReachableFor (d : Fin 10) (q : T39.State) : Prop :=
  ∃ w : List T39.Symbol,
    LegalContinuationFor d T39.initialState w ∧
      T39.run T39.initialState w = q

/-- Common-level concrete reachability. -/
def ReachableAtFor (d : Fin 10) (N : ℕ) (q : T39.State) : Prop :=
  ReachableFor d q ∧ q.level = N

/-- A packet avoids the parameter digit. -/
def PacketAvoidsDigit (d : Fin 10) (p : T41.Packet) : Prop :=
  AvoidsDigit d p.decimal

/-- T41's exact packet transition with only its avoidance test replaced. -/
def RetainedPacketFor (d : Fin 10) (r : ℕ) (c : T41.ClockContext)
    (q : T41.ResidualState) (p : T41.Packet) : Prop :=
  T41.packetClockWidth p ∧ PacketAvoidsDigit d p ∧
    -((T41.nextContext c p.width).a : ℤ) <
      (T41.nextResidual r c q p).reducedCarry ∧
    (T41.nextResidual r c q p).reducedCarry <
      ((T41.nextContext c p.width).b : ℤ)

/-- Finite packet acceptance for the digit-`d` residual system. -/
def AcceptedFor (d : Fin 10) :
    T41.ClockContext → ℕ → T41.ResidualState → List T41.Packet → Prop
  | _, _, _, [] => True
  | c, r, q, p :: w => RetainedPacketFor d r c q p ∧
      AcceptedFor d (T41.nextContext c p.width) r
        (T41.nextResidual r c q p) w

/-- Packet widths follow the one actual future external-clock schedule. -/
def TailLegal : ℕ → List T41.Packet → Prop
  | _, [] => True
  | N, p :: w => p.width = T39.scheduleIncrement N ∧ TailLegal (N + 1) w

/-- Digit-`d` finite continuation language at one shared external level. -/
def ContinuationLanguageAt (d : Fin 10) (N r : ℕ)
    (q : T41.ResidualState) : Set (List T41.Packet) :=
  {w | TailLegal N w ∧ AcceptedFor d (T41.balancedContext N) r q w}

/-- Common-level right-language equivalence for the digit-`d` system. -/
def RightLanguageEquivalentAt (d : Fin 10) (N r : ℕ)
    (q q' : T41.ResidualState) : Prop :=
  ContinuationLanguageAt d N r q = ContinuationLanguageAt d N r q'

/-- A residual is induced by a digit-`d` reachable concrete source at level `N`. -/
def PersistentReachableAt (d : Fin 10) (N : ℕ)
    (q : T41.ResidualState) : Prop :=
  ∃ source : T39.State,
    ReachableAtFor d N source ∧ T41.residualOf 1 source = q

/-- The exact safe-support criterion for T43's unchanged zero/one data. -/
def SafeSupport (d : Fin 10) : Prop :=
  d ≠ (0 : Fin 10) ∧ d ≠ (1 : Fin 10)

/-- Every decimal digit of value at least two satisfies the safe-support
criterion. -/
theorem safeSupport_of_two_le_val {d : Fin 10} (hd : 2 ≤ d.val) :
    SafeSupport d := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    norm_num at hv
    omega

/-- Any zero/one-supported word avoids a digit satisfying `SafeSupport`. -/
theorem safeSupport_avoidsDigit {d : Fin 10} (hd : SafeSupport d)
    {w : List (Fin 10)} (hw : ∀ x ∈ w, x = 0 ∨ x = 1) :
    AvoidsDigit d w := by
  intro hmem
  rcases hw d hmem with hzero | hone
  · exact hd.1 hzero
  · exact hd.2 hone

/-- T41's unchanged one-hot word is supported on zero and one. -/
theorem oneHotWord_zero_one_support (length k : ℕ) (x : Fin 10)
    (hx : x ∈ T41.oneHotWord length k) : x = 0 ∨ x = 1 := by
  simp only [T41.oneHotWord, List.mem_append, List.mem_replicate,
    List.mem_singleton] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · exact Or.inl hx.2
    · exact Or.inr hx
  · exact Or.inl hx.2

/-- Safe digits are avoided by every unchanged one-hot word. -/
theorem oneHotWord_avoids_of_safeSupport {d : Fin 10} (hd : SafeSupport d)
    (length k : ℕ) : AvoidsDigit d (T41.oneHotWord length k) :=
  safeSupport_avoidsDigit hd (oneHotWord_zero_one_support length k)

/-- Replace T39's digit-2 conjunct while retaining all arithmetic conjuncts. -/
theorem balancedFor_of_balanced_of_avoids {d : Fin 10} {q : T39.State}
    (hq : T39.Balanced q) (hd : AvoidsDigit d q.decimalPrefix) :
    BalancedFor d q := by
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hd, hq.2.2.2.2.2⟩

/-- A legal digit-`d` path ends in a digit-`d` balanced state. -/
theorem legalContinuationFor_run_balanced {d : Fin 10} {q : T39.State}
    {w : List T39.Symbol} (hw : LegalContinuationFor d q w) :
    BalancedFor d (T39.run q w) := by
  induction w generalizing q with
  | nil => simpa [T39.run, LegalContinuationFor] using hw
  | cons a w ih =>
      rw [LegalContinuationFor] at hw
      simp only [T39.run, List.foldl_cons]
      exact ih hw.2

/-- Reachability entails final digit-specific balance. -/
theorem reachableFor_balanced {d : Fin 10} {q : T39.State}
    (hq : ReachableFor d q) : BalancedFor d q := by
  obtain ⟨w, hw, hr⟩ := hq
  rw [← hr]
  exact legalContinuationFor_run_balanced hw

/-- The empty source is balanced for every forbidden digit. -/
theorem initialState_balancedFor (d : Fin 10) :
    BalancedFor d T39.initialState := by
  apply balancedFor_of_balanced_of_avoids
  · simpa [T39.initialState, T39.zeroState] using T39.zeroState_balanced 0
  · simp [AvoidsDigit, T39.initialState]

/-- T41's rational-prefix construction remains balanced after replacing the
avoidance conjunct, provided the full decimal endpoint avoids both digits. -/
theorem rationalState_all_prefixes_balancedFor {d : Fin 10} {n D : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n)
    (havoidTwo : T39.avoidsTwo (T41.fixedWord 10 (T39.decimalLevel n) D))
    (havoidD : AvoidsDigit d (T41.fixedWord 10 (T39.decimalLevel n) D))
    {i : ℕ} (hin : i ≤ n) :
    BalancedFor d (T41.prefixState (T41.rationalState n D) i) := by
  apply balancedFor_of_balanced_of_avoids
  · exact T41.rationalState_all_prefixes_balanced hD havoidTwo hin
  · intro hmem
    apply havoidD
    exact List.mem_of_mem_take hmem

/-- Append one retained digit-specific transition to a legal path. -/
theorem legalContinuationFor_append_one {d : Fin 10} {q : T39.State}
    {w : List T39.Symbol} {a : T39.Symbol}
    (hw : LegalContinuationFor d q w)
    (ha : RetainedStepFor d (T39.run q w) a) :
    LegalContinuationFor d q (w ++ [a]) := by
  induction w generalizing q with
  | nil =>
      simp only [T39.run, List.foldl_nil] at ha
      simpa [LegalContinuationFor] using ⟨ha, ha.2⟩
  | cons b w ih =>
      rw [LegalContinuationFor] at hw
      simp only [T39.run, List.foldl_cons] at ha
      rw [List.cons_append, LegalContinuationFor]
      exact ⟨hw.1, ih hw.2 ha⟩

/-- Reachability is closed under one retained digit-specific transition. -/
theorem reachableFor_step {d : Fin 10} {q : T39.State}
    (hq : ReachableFor d q) {a : T39.Symbol}
    (ha : RetainedStepFor d q a) :
    ReachableFor d (T39.appendSymbol q a) := by
  obtain ⟨w, hw, hr⟩ := hq
  refine ⟨w ++ [a], legalContinuationFor_append_one hw ?_, ?_⟩
  · simpa [hr] using ha
  · rw [T41.run_append_one, hr]

/-- The endpoint-prefix construction gives reachability for the parameterized
system when every scheduled prefix is digit-specifically balanced. -/
theorem reachableFor_of_all_prefixes_balanced (d : Fin 10) (q : T39.State)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level)
    (hbalanced : ∀ i ≤ q.level,
      BalancedFor d (T41.prefixState q i)) : ReachableFor d q := by
  induction hlevel : q.level generalizing q with
  | zero =>
      have hq : q = T39.initialState := by
        apply T39.state_ext
        · simpa using hlevel
        · apply List.eq_nil_of_length_eq_zero
          omega
        · apply List.eq_nil_of_length_eq_zero
          simpa [hlevel, T39.decimalLevel] using hdecimal
      rw [hq]
      exact ⟨[], by simpa [LegalContinuationFor] using initialState_balancedFor d,
        by simp [T39.run]⟩
  | succ i ih =>
      have hi : i < q.level := by omega
      let qprev := T41.prefixState q i
      let a := T41.endpointSymbol q i hi hhex hdecimal
      have happend : T39.appendSymbol qprev a = T41.prefixState q (i + 1) :=
        T41.append_prefixState_endpointSymbol q i hi hhex hdecimal
      have hqeq : T41.prefixState q (i + 1) = q := by
        apply T39.state_ext
        · simpa using hlevel.symm
        · simp [T41.prefixState, hhex, hlevel]
        · have hm : T39.decimalLevel (i + 1) = T39.decimalLevel q.level := by
            rw [hlevel]
          simp [T41.prefixState, hdecimal, hm]
      have hprevhex : qprev.hexPrefix.length = qprev.level := by
        simp [qprev, T41.prefixState, hhex, hi.le]
      have hprevdec : qprev.decimalPrefix.length =
          T39.decimalLevel qprev.level := by
        have hm := T41.decimalLevel_mono_of_le hi.le
        simp [qprev, T41.prefixState, hdecimal, hm]
      have hprevbalanced : ∀ k ≤ qprev.level,
          BalancedFor d (T41.prefixState qprev k) := by
        intro k hk
        have hki : k ≤ i := by simpa [qprev, T41.prefixState] using hk
        have heq : T41.prefixState qprev k = T41.prefixState q k := by
          apply T39.state_ext <;>
            simp [qprev, T41.prefixState, List.take_take, hki,
              T41.decimalLevel_mono_of_le hki]
        rw [heq]
        exact hbalanced k (hki.trans hi.le)
      have hreach : ReachableFor d qprev :=
        ih qprev hprevhex hprevdec hprevbalanced rfl
      have hstep : RetainedStepFor d qprev a := by
        constructor
        · dsimp [a, qprev, T41.prefixState, T41.endpointSymbol]
          simp only [List.length_take, List.length_drop]
          rw [Nat.min_eq_left]
          have hm := T41.decimalLevel_mono_of_le
            (show i + 1 ≤ q.level by omega)
          rw [hdecimal]
          have hs := T39.decimalLevel_succ i
          omega
        · rw [happend]
          exact hbalanced (i + 1) (by omega)
      rw [← hqeq, ← happend]
      exact reachableFor_step hreach hstep

/-- Endpoint slicing is a legal digit-specific continuation whenever all
scheduled prefixes are digit-specifically balanced. -/
theorem legal_endpointContinuationFor (d : Fin 10) (q : T39.State)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level)
    (hbalanced : ∀ i ≤ q.level, BalancedFor d (T41.prefixState q i))
    (start t : ℕ) (hle : start + t ≤ q.level) :
    LegalContinuationFor d (T41.prefixState q start)
      (T41.endpointContinuation q hhex hdecimal start t hle) := by
  induction t generalizing start with
  | zero =>
      simp only [T41.endpointContinuation, LegalContinuationFor]
      exact hbalanced start (by omega)
  | succ t ih =>
      simp only [T41.endpointContinuation, LegalContinuationFor]
      let a := T41.endpointSymbol q start (by omega) hhex hdecimal
      have happend := T41.append_prefixState_endpointSymbol q start
        (by omega) hhex hdecimal
      constructor
      · constructor
        · dsimp [a, T41.endpointSymbol, T41.prefixState]
          simp only [List.length_take, List.length_drop]
          rw [Nat.min_eq_left]
          have hm := T41.decimalLevel_mono_of_le
            (show start + 1 ≤ q.level by omega)
          rw [hdecimal]
          have hs := T39.decimalLevel_succ start
          omega
        · rw [happend]
          exact hbalanced (start + 1) (by omega)
      · rw [happend]
        exact ih (start + 1) (by omega)

/-- The unchanged T41 witness decimal endpoint avoids every safe digit. -/
theorem witnessEndpoint_avoids_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) {M r : ℕ} (j : Fin (M + 1)) :
    AvoidsDigit d
      (T41.fixedWord 10 (T39.decimalLevel (T41.witnessLevel M r))
        (T41.witnessDecimalValue r j)) := by
  have hk : r + (j : ℕ) < T39.decimalLevel (T41.witnessLevel M r) := by
    simpa [T41.witnessDecimalLength] using T41.witness_digit_position_lt j
  rw [show T41.witnessDecimalValue r j = 10 ^ (r + (j : ℕ)) by rfl,
    T41.fixedWord_oneHot hk]
  exact oneHotWord_avoids_of_safeSupport hd _ _

/-- Generic safe-support witness criterion: every unchanged T43/T41 source
witness is reachable in the digit-`d` concrete system. -/
theorem witnessState_reachable_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) {M r : ℕ} (j : Fin (M + 1)) :
    ReachableFor d (T41.witnessState M r j) := by
  rw [T41.witnessState_eq_rationalState]
  have hD : T41.witnessDecimalValue r j <
      10 ^ T39.decimalLevel (T41.witnessLevel M r) :=
    Nat.pow_lt_pow_right (by norm_num) (T41.witness_digit_position_lt j)
  apply reachableFor_of_all_prefixes_balanced
  · exact T41.fixedWord_length (by norm_num) (T41.rationalHexValue_lt_pow hD)
  · exact T41.fixedWord_length (by norm_num) hD
  · intro i hi
    have hi' : i ≤ T41.witnessLevel M r := by
      simpa [T41.rationalState] using hi
    exact rationalState_all_prefixes_balancedFor hD
      (by
        have hk : r + (j : ℕ) < T39.decimalLevel (T41.witnessLevel M r) := by
          simpa [T41.witnessDecimalLength] using T41.witness_digit_position_lt j
        rw [show T41.witnessDecimalValue r j = 10 ^ (r + (j : ℕ)) by rfl,
          T41.fixedWord_oneHot hk]
        exact T41.oneHotWord_avoidsTwo _ _)
      (witnessEndpoint_avoids_of_safeSupport hd j) hi'

/-- The extended one-hot endpoint used by the separator avoids every safe digit. -/
theorem extendedWitness_avoidsDigit_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) {M r : ℕ} (j : Fin (M + 1)) :
    AvoidsDigit d (T41.extendedWitnessState M r j).decimalPrefix := by
  let S := T39.incrementSum (T41.witnessLevel M r) (T41.separationSteps M r)
  have hk : r + (j : ℕ) + S <
      T39.decimalLevel (T41.witnessLevel M r + T41.separationSteps M r) := by
    rw [T39.decimalLevel_add_eq]
    have h := T41.witness_digit_position_lt (M := M) (r := r) j
    simp only [T41.witnessDecimalLength] at h
    dsimp [S]
    omega
  have hvalue : T41.extensionValue (T41.witnessLevel M r)
      (T41.separationSteps M r) (T41.witnessDecimalValue r j) =
      10 ^ (r + (j : ℕ) + S) := by
    simp [T41.extensionValue, T41.witnessDecimalValue, S, pow_add]
  simp only [T41.extendedWitnessState, T41.rationalState]
  rw [hvalue, T41.fixedWord_oneHot hk]
  exact oneHotWord_avoids_of_safeSupport hd _ _

set_option maxHeartbeats 2000000 in
/-- T41's exact separator symbols form a legal path in every safe digit system. -/
theorem distinguishingSymbols_legalFor_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) {M r : ℕ} (j : Fin (M + 1)) :
    LegalContinuationFor d (T41.witnessState M r j)
      (T41.distinguishingSymbols M r j) := by
  let qf := T41.extendedWitnessState M r j
  have hbalanced : ∀ i ≤ qf.level,
      BalancedFor d (T41.prefixState qf i) := by
    intro i hi
    change i ≤ T41.witnessLevel M r + T41.separationSteps M r at hi
    change BalancedFor d (T41.prefixState
      (T41.rationalState (T41.witnessLevel M r + T41.separationSteps M r)
        (T41.extensionValue (T41.witnessLevel M r) (T41.separationSteps M r)
          (T41.witnessDecimalValue r j))) i)
    exact rationalState_all_prefixes_balancedFor
      (T41.extendedWitnessValue_lt_pow j) (T41.extendedWitness_avoidsTwo j)
      (extendedWitness_avoidsDigit_of_safeSupport hd j) hi
  have hlegal := legal_endpointContinuationFor d qf
    (T41.extendedWitness_hex_length j) (T41.extendedWitness_decimal_length j)
    hbalanced (T41.witnessLevel M r) (T41.separationSteps M r) (by rfl)
  have hprefix : T41.prefixState qf (T41.witnessLevel M r) =
      T41.witnessState M r j := by
    change T41.prefixState
      (T41.rationalState (T41.witnessLevel M r + T41.separationSteps M r)
        (T41.extensionValue (T41.witnessLevel M r) (T41.separationSteps M r)
          (T41.witnessDecimalValue r j))) (T41.witnessLevel M r) = _
    calc
      _ = T41.rationalState (T41.witnessLevel M r)
          (T41.witnessDecimalValue r j) :=
        T41.rationalExtension_prefixState
          (Nat.pow_lt_pow_right (by norm_num)
            (T41.witness_digit_position_lt (M := M) (r := r) j))
      _ = T41.witnessState M r j := (T41.witnessState_eq_rationalState j).symm
  rw [hprefix] at hlegal
  exact hlegal

/-- Digit-specific legality entails the one shared external schedule tail. -/
theorem tailLegal_packetsOfSymbols_of_legalFor {d : Fin 10} {q : T39.State}
    {w : List T39.Symbol} (hlegal : LegalContinuationFor d q w) :
    TailLegal q.level (T41.packetsOfSymbols w) := by
  induction w generalizing q with
  | nil => simp [TailLegal, T41.packetsOfSymbols]
  | cons a w ih =>
      rw [LegalContinuationFor] at hlegal
      simp only [T41.packetsOfSymbols, List.map_cons, TailLegal]
      exact ⟨hlegal.1.1, ih hlegal.2⟩

/-- A retained concrete step induces a retained residual packet in the
parameterized system. -/
theorem retainedPacketFor_packetOfSymbol_of_retainedStepFor
    (d : Fin 10) (r : ℕ) (q : T39.State) (a : T39.Symbol)
    (hstep : RetainedStepFor d q a) :
    RetainedPacketFor d r (T41.balancedContext q.level) (T41.residualOf r q)
      (T41.packetOfSymbol a) := by
  have hnext := T41.nextResidual_packetOfSymbol r q a hstep.1
  have hbalanced := hstep.2
  have havTarget : AvoidsDigit d (T39.appendSymbol q a).decimalPrefix :=
    hbalanced.2.2.2.2.1
  have havPacket : PacketAvoidsDigit d (T41.packetOfSymbol a) := by
    intro hmem
    apply havTarget
    simp only [T39.appendSymbol, T41.packetOfSymbol] at hmem ⊢
    exact List.mem_append_right _ hmem
  have hclock : T41.packetClockWidth (T41.packetOfSymbol a) := by
    simpa [T41.packetClockWidth, T41.packetOfSymbol, hstep.1] using
      T39.scheduleIncrement_one_or_two q.level
  have hbounds := (T41.overlap_iff_reducedCarry_bounds
    (T39.appendSymbol q a).level
    (T37.wordValue (T39.appendSymbol q a).hexPrefix)
    (T37.wordValue (T39.appendSymbol q a).decimalPrefix)).mp
      hbalanced.2.2.2.2.2
  have hcontext : T41.nextContext (T41.balancedContext q.level)
      (T41.packetOfSymbol a).width =
      T41.balancedContext (T39.appendSymbol q a).level := by
    calc
      T41.nextContext (T41.balancedContext q.level)
          (T41.packetOfSymbol a).width =
          T41.nextContext (T41.balancedContext q.level)
            (T39.scheduleIncrement q.level) :=
        congrArg (T41.nextContext (T41.balancedContext q.level)) hstep.1
      _ = T41.balancedContext (q.level + 1) := T41.nextContext_balanced q.level
      _ = T41.balancedContext (T39.appendSymbol q a).level := rfl
  refine ⟨hclock, havPacket, ?_⟩
  rw [hcontext, hnext]
  simpa [T41.residualOf] using hbounds

/-- Every legal concrete digit-specific path is accepted by its residual system. -/
theorem acceptedFor_packetsOfSymbols_of_legalFor (d : Fin 10) (r : ℕ)
    {q : T39.State} {w : List T39.Symbol}
    (hlegal : LegalContinuationFor d q w) :
    AcceptedFor d (T41.balancedContext q.level) r (T41.residualOf r q)
      (T41.packetsOfSymbols w) := by
  induction w generalizing q with
  | nil => simp [AcceptedFor, T41.packetsOfSymbols]
  | cons a w ih =>
      rw [LegalContinuationFor] at hlegal
      simp only [T41.packetsOfSymbols, List.map_cons, AcceptedFor]
      refine ⟨retainedPacketFor_packetOfSymbol_of_retainedStepFor
        d r q a hlegal.1, ?_⟩
      have hc : T41.nextContext (T41.balancedContext q.level)
          (T41.packetOfSymbol a).width =
          T41.balancedContext (T39.appendSymbol q a).level := by
        calc
          T41.nextContext (T41.balancedContext q.level)
              (T41.packetOfSymbol a).width =
              T41.nextContext (T41.balancedContext q.level)
                (T39.scheduleIncrement q.level) :=
            congrArg (T41.nextContext (T41.balancedContext q.level)) hlegal.1.1
          _ = T41.balancedContext (q.level + 1) :=
            T41.nextContext_balanced q.level
          _ = T41.balancedContext (T39.appendSymbol q a).level := rfl
      rw [hc, T41.nextResidual_packetOfSymbol r q a hlegal.1.1]
      exact ih hlegal.2

/-- Nonempty digit-specific acceptance supplies the same final strict carry
bounds as T41 acceptance. -/
theorem acceptedFor_final_bounds {d : Fin 10} {r : ℕ}
    {c : T41.ClockContext} {q : T41.ResidualState} {w : List T41.Packet}
    (hw : w ≠ []) (haccepted : AcceptedFor d c r q w) :
    -((T41.advanceContext c w).a : ℤ) <
        (T41.runResidual r c q w).reducedCarry ∧
      (T41.runResidual r c q w).reducedCarry <
        ((T41.advanceContext c w).b : ℤ) := by
  induction w generalizing c q with
  | nil => exact (hw rfl).elim
  | cons p w ih =>
      rw [AcceptedFor] at haccepted
      cases w with
      | nil =>
          simpa [T41.advanceContext, T41.runResidual, RetainedPacketFor] using
            haccepted.1.2.2
      | cons p' w => exact ih (by simp) haccepted.2

/-- The exact T41 continuation is accepted from its oriented witness in every
safe digit system. -/
theorem distinguishingContinuation_acceptedFor_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) {M r : ℕ} (j : Fin (M + 1)) :
    AcceptedFor d (T41.balancedContext (T41.witnessLevel M r)) r
      (T41.residualOf r (T41.witnessState M r j))
      (T41.distinguishingContinuation M r j) := by
  exact acceptedFor_packetsOfSymbols_of_legalFor d r
    (distinguishingSymbols_legalFor_of_safeSupport hd j)

/-- The exact T41 continuation is rejected from every other one-hot witness;
the proof uses only common strict carry bounds after the acceptance hypotheses. -/
theorem distinguishingContinuation_rejectedFor_of_ne {d : Fin 10}
    {M r : ℕ} {u v : Fin (M + 1)} (huv : u ≠ v) :
    ¬ AcceptedFor d (T41.balancedContext (T41.witnessLevel M r)) r
      (T41.residualOf r (T41.witnessState M r v))
      (T41.distinguishingContinuation M r u) := by
  intro hvAccepted
  let c := T41.balancedContext (T41.witnessLevel M r)
  let qu := T41.residualOf r (T41.witnessState M r u)
  let qv := T41.residualOf r (T41.witnessState M r v)
  let w := T41.distinguishingContinuation M r u
  let xu := (T41.runResidual r c qu w).reducedCarry
  let xv := (T41.runResidual r c qv w).reducedCarry
  let cf := T41.advanceContext c w
  have hwne : w ≠ [] := T41.distinguishingContinuation_ne_nil M r u
  have huAccepted : T41.Accepted c r qu w :=
    T41.distinguishingContinuation_accepted u
  have hbu : -((cf.a : ℕ) : ℤ) < xu ∧ xu < ((cf.b : ℕ) : ℤ) :=
    T41.accepted_final_bounds hwne huAccepted
  have hbv : -((cf.a : ℕ) : ℤ) < xv ∧ xv < ((cf.b : ℕ) : ℤ) :=
    acceptedFor_final_bounds hwne hvAccepted
  have hctx : cf = T41.balancedContext
      (T41.witnessLevel M r + T41.separationSteps M r) :=
    T41.advanceContext_distinguishingContinuation M r u
  have hbten : cf.b < 10 * cf.a := by
    rw [hctx]
    exact T41.balancedContext_b_lt_ten_a _
  have habsUpper : |xu - xv| < (11 * cf.a : ℕ) := by
    have hab : |xu - xv| < ((cf.a + cf.b : ℕ) : ℤ) := by
      rw [abs_lt]
      push_cast
      constructor <;> omega
    exact_mod_cast (show |xu - xv| < (11 * cf.a : ℕ) by
      exact_mod_cast (by
        push_cast at hab
        omega : |xu - xv| < ((11 * cf.a : ℕ) : ℤ)))
  have hcarryNe : qu.reducedCarry ≠ qv.reducedCarry := by
    intro hcarry
    exact huv (T41.witness_reducedCarry_injective hcarry)
  have hdeltaPos : (0 : ℤ) < |qu.reducedCarry - qv.reducedCarry| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hcarryNe)
  have hsub := T41.runResidual_carry_sub r c qu qv w
  have habsEq : |xu - xv| =
      (T41.carryMultiplier w : ℤ) * |qu.reducedCarry - qv.reducedCarry| := by
    rw [show xu - xv = (T41.carryMultiplier w : ℤ) *
      (qu.reducedCarry - qv.reducedCarry) from hsub]
    rw [abs_mul]
    simp
  have hlower : (T41.carryMultiplier w : ℤ) ≤ |xu - xv| := by
    rw [habsEq]
    have hm : (0 : ℤ) ≤ T41.carryMultiplier w := by positivity
    nlinarith
  have hproduct : T41.carryMultiplier w < 11 * cf.a := by
    exact_mod_cast lt_of_le_of_lt hlower habsUpper
  have hwlen : w.length = T41.separationSteps M r :=
    T41.distinguishingContinuation_length M r u
  rw [T41.carryMultiplier_eq, hwlen, T41.advanceContext_a] at hproduct
  have hsmall : 16 ^ T41.separationSteps M r < 11 * c.a := by
    apply (Nat.mul_lt_mul_right (T41.fiveMultiplier_pos w)).mp
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hproduct
  have hlarge := T41.eleven_mul_lt_sixteen_pow (T41.separationSteps_pos M r)
  have hca : c.a = T41.separationSteps M r := rfl
  rw [hca] at hsmall
  omega

/-- Common external level of the unchanged `K+1` witness family. -/
def familyLevel (K : ℕ) : ℕ := T41.witnessLevel K 1

/-- Unchanged one-hot concrete source witness. -/
def familyState (K : ℕ) (j : Fin (K + 1)) : T39.State :=
  T41.witnessState K 1 j

/-- Persistent residual of the unchanged source witness. -/
def familyResidual (K : ℕ) (j : Fin (K + 1)) : T41.ResidualState :=
  T41.residualOf 1 (familyState K j)

/-- Unchanged explicit endpoint continuation oriented from witness `j`. -/
def familySeparator (K : ℕ) (j : Fin (K + 1)) : List T41.Packet :=
  T41.distinguishingContinuation K 1 j

/-- Safe support supplies common-level concrete reachability. -/
theorem family_reachableAt_of_safeSupport {d : Fin 10} (hd : SafeSupport d)
    (K : ℕ) (j : Fin (K + 1)) :
    ReachableAtFor d (familyLevel K) (familyState K j) := by
  exact ⟨witnessState_reachable_of_safeSupport hd j, rfl⟩

/-- Safe support supplies common-level persistent reachability. -/
theorem family_persistent_reachableAt_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) (K : ℕ) (j : Fin (K + 1)) :
    PersistentReachableAt d (familyLevel K) (familyResidual K j) := by
  exact ⟨familyState K j, family_reachableAt_of_safeSupport hd K j, rfl⟩

/-- The unchanged separator follows the shared schedule, is accepted from its
oriented safe witness, and is rejected from every other witness. -/
theorem family_explicit_separator_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) (K : ℕ) {u v : Fin (K + 1)} (huv : u ≠ v) :
    TailLegal (familyLevel K) (familySeparator K u) ∧
      AcceptedFor d (T41.balancedContext (familyLevel K)) 1
        (familyResidual K u) (familySeparator K u) ∧
      ¬ AcceptedFor d (T41.balancedContext (familyLevel K)) 1
        (familyResidual K v) (familySeparator K u) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [familyLevel, familySeparator, T41.distinguishingContinuation] using
      tailLegal_packetsOfSymbols_of_legalFor
        (distinguishingSymbols_legalFor_of_safeSupport
          (M := K) (r := 1) hd u)
  · simpa [familyLevel, familyResidual, familyState, familySeparator] using
      (distinguishingContinuation_acceptedFor_of_safeSupport
        (M := K) (r := 1) hd u)
  · simpa [familyLevel, familyResidual, familyState, familySeparator] using
      (distinguishingContinuation_rejectedFor_of_ne
        (d := d) (M := K) (r := 1) huv)

/-- Safe-support witnesses have pairwise distinct continuation languages. -/
theorem family_pairwise_rightLanguage_inequivalent_of_safeSupport
    {d : Fin 10} (hd : SafeSupport d) (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ RightLanguageEquivalentAt d (familyLevel K) 1
      (familyResidual K u) (familyResidual K v) := by
  intro hequiv
  have hseparator := family_explicit_separator_of_safeSupport hd K huv
  have hmemu : familySeparator K u ∈
      ContinuationLanguageAt d (familyLevel K) 1 (familyResidual K u) :=
    ⟨hseparator.1, hseparator.2.1⟩
  have hmemv : familySeparator K u ∈
      ContinuationLanguageAt d (familyLevel K) 1 (familyResidual K v) := by
    rw [← hequiv]
    exact hmemu
  exact hseparator.2.2 hmemv.2

/-- The unchanged persistent witness family is injective. -/
theorem familyResidual_injective (K : ℕ) :
    Function.Injective (familyResidual K) := by
  intro u v huv
  apply T41.witness_reducedCarry_injective
  exact congrArg T41.ResidualState.reducedCarry huv

/-- Named generic witness criterion, packaging both required consequences:
common-level reachability and explicit pairwise language separation. -/
theorem safeSupport_witnessCriterion {d : Fin 10} (hd : SafeSupport d)
    (K : ℕ) :
    (∀ j : Fin (K + 1),
      PersistentReachableAt d (familyLevel K) (familyResidual K j)) ∧
    ∀ u v : Fin (K + 1), u ≠ v →
      ¬ RightLanguageEquivalentAt d (familyLevel K) 1
        (familyResidual K u) (familyResidual K v) := by
  exact ⟨family_persistent_reachableAt_of_safeSupport hd K,
    fun _ _ huv =>
      family_pairwise_rightLanguage_inequivalent_of_safeSupport hd K huv⟩

/-- Unbounded common-level continuation-language index for one forbidden digit. -/
def InfiniteContinuationLanguageIndex (d : Fin 10) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, ∃ f : Fin (K + 1) → T41.ResidualState,
    K < Fintype.card (Fin (K + 1)) ∧
    Function.Injective f ∧
    (∀ j : Fin (K + 1), PersistentReachableAt d N (f j)) ∧
    ∀ u v : Fin (K + 1), u ≠ v →
      ¬ RightLanguageEquivalentAt d N 1 (f u) (f v)

/-- The safe-support criterion implies infinite continuation-language index. -/
theorem infiniteContinuationLanguageIndex_of_safeSupport {d : Fin 10}
    (hd : SafeSupport d) : InfiniteContinuationLanguageIndex d := by
  intro K
  refine ⟨familyLevel K, familyResidual K, by simp,
    familyResidual_injective K, ?_, ?_⟩
  · exact family_persistent_reachableAt_of_safeSupport hd K
  · intro u v huv
    exact family_pairwise_rightLanguage_inequivalent_of_safeSupport hd K huv

/-- Forbidden digit 2 has infinite continuation-language index. -/
theorem digitTwo_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (2 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Forbidden digit 3 has infinite continuation-language index. -/
theorem digitThree_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (3 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Forbidden digit 4 has infinite continuation-language index. -/
theorem digitFour_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (4 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Forbidden digit 5 has infinite continuation-language index. -/
theorem digitFive_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (5 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Forbidden digit 6 has infinite continuation-language index. -/
theorem digitSix_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (6 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Forbidden digit 7 has infinite continuation-language index. -/
theorem digitSeven_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (7 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Forbidden digit 8 has infinite continuation-language index. -/
theorem digitEight_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (8 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Forbidden digit 9 has infinite continuation-language index. -/
theorem digitNine_infiniteContinuationLanguageIndex :
    InfiniteContinuationLanguageIndex (9 : Fin 10) :=
  infiniteContinuationLanguageIndex_of_safeSupport
    (safeSupport_of_two_le_val (by norm_num))

/-- Every unchanged one-hot source witness contains digit 1. -/
theorem digitOne_mem_familyState_decimalPrefix (K : ℕ)
    (j : Fin (K + 1)) :
    (1 : Fin 10) ∈ (familyState K j).decimalPrefix := by
  simp [familyState, T41.witnessState, T41.oneHotWord]

/-- Exact digit-1 failure: T43's unchanged one-hot source witness is not
reachable in the digit-1 concrete system, for every family size and member. -/
theorem digitOne_unchangedWitness_not_reachable (K : ℕ)
    (j : Fin (K + 1)) :
    ¬ ReachableFor (1 : Fin 10) (familyState K j) := by
  intro hreach
  have hbalanced := reachableFor_balanced hreach
  exact hbalanced.2.2.2.2.1 (digitOne_mem_familyState_decimalPrefix K j)

end

end Theory.PiDigits.T46

#print axioms Theory.PiDigits.T46.safeSupport_witnessCriterion
#print axioms Theory.PiDigits.T46.family_reachableAt_of_safeSupport
#print axioms Theory.PiDigits.T46.family_pairwise_rightLanguage_inequivalent_of_safeSupport
#print axioms Theory.PiDigits.T46.infiniteContinuationLanguageIndex_of_safeSupport
#print axioms Theory.PiDigits.T46.digitTwo_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitThree_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitFour_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitFive_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitSix_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitSeven_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitEight_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitNine_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T46.digitOne_unchangedWitness_not_reachable
