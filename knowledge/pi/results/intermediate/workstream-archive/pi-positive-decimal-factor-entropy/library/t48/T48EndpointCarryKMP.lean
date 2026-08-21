import TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore
import TheoryLib.PiPositiveDecimalFactorEntropy.T46T46T46LiveSCC
import TheoryLib.MultiplicativeAvoidanceGap.T13T13T6ArithmeticBridge
import TheoryLib.MultiplicativeAvoidanceGap.T24T24ActivePrefixAutomaton

/-!
# T48: endpoint-complete carry/KMP graph

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The source is locally formulated and has no external source URL.  This module
constructs and analyzes one finite graph for each nonempty decimal word and
each finite times-16 depth.  It proves no uniform extinction statement, C6,
C1, or unconditional statement about pi.
-/

noncomputable section

open Finset Set

namespace DecimalFactorEntropy.T48EndpointCarryKMP

/-- The singleton forbidden family used by the KMP coordinates. -/
def singletonFamily (w : List (Fin 10)) (hw : w ≠ []) :
    MultiplicativeAvoidanceGap.T24.ForbiddenFamily 10 where
  base_ge_two := by omega
  words := {w}
  card_one_or_two := Or.inl (by simp)
  words_nonempty := by simpa
  reduced := by simp

/-- Endpoint-complete carries, literally the integers from `-1` through `16`. -/
def Carry := {c : ℤ // c ∈ Finset.Icc (-1) 16}

instance : DecidableEq Carry := Subtype.instDecidableEq

instance : Fintype Carry := Fintype.ofFinset (Finset.Icc (-1) 16) (fun _ => Iff.rfl)

@[simp] theorem carry_lower (c : Carry) : (-1 : ℤ) ≤ c.1 := by
  simpa [Carry] using (Finset.mem_Icc.mp c.2).1

@[simp] theorem carry_upper (c : Carry) : c.1 ≤ (16 : ℤ) := by
  simpa [Carry] using (Finset.mem_Icc.mp c.2).2

/-- The simultaneous KMP states and carries before one digit column is read. -/
structure RawState (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) where
  kmp : Fin (R + 1) → (singletonFamily w hw).State
  carry : Fin R → Carry

instance rawStateDecidableEq (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    DecidableEq (RawState w hw R) := Classical.decEq _

instance rawStateFintype (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    Fintype (RawState w hw R) :=
  Fintype.ofEquiv
    ((Fin (R + 1) → (singletonFamily w hw).State) × (Fin R → Carry))
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun q => ⟨q.kmp, q.carry⟩
      left_inv := by intro q; cases q; rfl
      right_inv := by intro q; cases q; rfl }

/-- One column of decimal digits for `x,16x,...,16^R x`. -/
abbrev DigitColumn (R : ℕ) := Fin (R + 1) → Fin 10

/-- The exact most-significant-first KMP/carry transition. -/
def RawStep {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : RawState w hw R) (d : DigitColumn R) (q' : RawState w hw R) : Prop :=
  (∀ i, (singletonFamily w hw).Step (q.kmp i) (d i) (q'.kmp i)) ∧
    ∀ j : Fin R,
      16 * (d j.castSucc).val + (q'.carry j).1 =
        (d j.succ).val + 10 * (q.carry j).1

instance rawStepDecidable {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : RawState w hw R) (d : DigitColumn R) (q' : RawState w hw R) :
    Decidable (RawStep q d q') := Classical.propDecidable _

/-- A full digit column has at most one raw successor. -/
theorem rawStep_rightUnique {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q q₁ q₂ : RawState w hw R} {d : DigitColumn R}
    (h₁ : RawStep q d q₁) (h₂ : RawStep q d q₂) : q₁ = q₂ := by
  cases q₁ with
  | mk k₁ c₁ =>
    cases q₂ with
    | mk k₂ c₂ =>
      have hk : k₁ = k₂ := by
        funext i
        exact (singletonFamily w hw).isActiveState_unique (h₁.1 i).2 (h₂.1 i).2
      have hc : c₁ = c₂ := by
        funext j
        apply Subtype.ext
        have h1 := h₁.2 j
        have h2 := h₂.2 j
        dsimp at h1 h2 ⊢
        omega
      subst k₂
      subst c₂
      rfl

/-- Initial raw state with empty KMP states and a chosen endpoint carry tuple. -/
def initialRaw (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (c : Fin R → Carry) : RawState w hw R where
  kmp := fun _ => (singletonFamily w hw).initialState
  carry := c

theorem initialRaw_carry_eq_of_kmp
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : RawState w hw R)
    (hq : ∀ i, q.kmp i = (singletonFamily w hw).initialState) :
    initialRaw w hw R q.carry = q := by
  cases q with
  | mk k c =>
      have hk : (fun _ : Fin (R + 1) => (singletonFamily w hw).initialState) = k := by
        funext i
        exact (hq i).symm
      cases hk
      rfl

/-- The partial deterministic raw transition obtained from `RawStep`. -/
def rawNext {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : RawState w hw R) (d : DigitColumn R) : Option (RawState w hw R) :=
  if h : ∃ q', RawStep q d q' then some (Classical.choose h) else none

theorem rawNext_eq_some_iff {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q q' : RawState w hw R} {d : DigitColumn R} :
    rawNext q d = some q' ↔ RawStep q d q' := by
  unfold rawNext
  split_ifs with h
  · constructor
    · intro heq
      have hchosen : Classical.choose h = q' := Option.some.inj heq
      simpa [hchosen] using Classical.choose_spec h
    · intro hstep
      congr
      exact rawStep_rightUnique (Classical.choose_spec h) hstep
  · constructor
    · simp
    · exact fun hstep => (h ⟨q', hstep⟩).elim

/-- Labels expose all digit coordinates; the first label also chooses one of
the finitely many endpoint carry starts. -/
inductive Label (R : ℕ)
  | initial (carry : Fin R → Carry) (digits : DigitColumn R)
  | next (digits : DigitColumn R)
  deriving DecidableEq, Fintype

/-- The digit column carried by either kind of graph label. -/
def Label.digits {R : ℕ} : Label R → DigitColumn R
  | .initial _ d => d
  | .next d => d

/-- Add the synthetic start around a successful raw transition. -/
def liftRawNext {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : RawState w hw R) (d : DigitColumn R) : Option (Option (RawState w hw R)) :=
  (rawNext q d).map some

/-- The finite, endpoint-complete, right-resolving carry/KMP graph. -/
def carryKMPGraph (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    DecimalFactorEntropy.T46LiveSCC.Graph where
  State := Option (RawState w hw R)
  Label := Label R
  stateFintype := inferInstance
  stateDecEq := inferInstance
  labelFintype := inferInstance
  labelDecEq := inferInstance
  start := none
  transition q a :=
    match q, a with
    | none, .initial c d => liftRawNext (initialRaw w hw R c) d
    | some q, .next d => liftRawNext q d
    | _, _ => none

theorem transition_initial_eq_some_iff
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {c : Fin R → Carry} {d : DigitColumn R} {q : RawState w hw R} :
    (carryKMPGraph w hw R).transition none (.initial c d) = some (some q) ↔
      RawStep (initialRaw w hw R c) d q := by
  change (rawNext (initialRaw w hw R c) d).map some = some (some q) ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨q', hq', hsome⟩
    have heq : q' = q := Option.some.inj hsome
    subst q'
    exact rawNext_eq_some_iff.mp hq'
  · intro h
    exact ⟨q, rawNext_eq_some_iff.mpr h, rfl⟩

theorem transition_next_eq_some_iff
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q q' : RawState w hw R} {d : DigitColumn R} :
    (carryKMPGraph w hw R).transition (some q) (.next d) = some (some q') ↔
      RawStep q d q' := by
  change (rawNext q d).map some = some (some q') ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨r, hr, hsome⟩
    have heq : r = q' := Option.some.inj hsome
    subst r
    exact rawNext_eq_some_iff.mp hr
  · intro h
    exact ⟨q', rawNext_eq_some_iff.mpr h, rfl⟩

/-! ## Endpoint-inclusive decimal fibers -/

/-- The length-`m` most-significant-first numeral of a decimal stream. -/
def prefixCode (a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream)
    (m : ℕ) : Fin (10 ^ m) :=
  MultiplicativeAvoidanceGap.T13.blockCode (fun i : Fin m => a i.val)

/-- Equal real values force fixed-length decimal numerals to differ by at most
one.  This is the closed-cylinder source of the usual two-expansion bound. -/
theorem prefixCode_le_add_one_of_realValue_eq
    (a b : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream) (m : ℕ)
    (hab : Real.ofDigits a = Real.ofDigits b) :
    (prefixCode a m).val ≤ (prefixCode b m).val + 1 := by
  have ha := MultiplicativeAvoidanceGap.T13.ofDigits_mem_cylinder 10 m (by omega) a
  have hb := MultiplicativeAvoidanceGap.T13.ofDigits_mem_cylinder 10 m (by omega) b
  have hp : (0 : ℝ) < (10 : ℝ) ^ m := by positivity
  have hle : ((prefixCode a m).val : ℝ) / (10 : ℝ) ^ m ≤
      (((prefixCode b m).val : ℝ) + 1) / (10 : ℝ) ^ m := by
    calc
      ((prefixCode a m).val : ℝ) / (10 : ℝ) ^ m ≤ Real.ofDigits a := ha.1
      _ = Real.ofDigits b := hab
      _ ≤ (((prefixCode b m).val : ℝ) + 1) / (10 : ℝ) ^ m := by
        simpa [prefixCode] using hb.2
  have : ((prefixCode a m).val : ℝ) ≤ (prefixCode b m).val + 1 :=
    (div_le_div_iff_of_pos_right hp).mp (by simpa [prefixCode] using hle)
  exact_mod_cast this

/-- Three pairwise distinct decimal streams cannot evaluate to the same real
number. -/
theorem not_three_pairwise_distinct_of_realValue_eq
    (a b c : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream)
    (hab : Real.ofDigits a = Real.ofDigits b)
    (hac : Real.ofDigits a = Real.ofDigits c)
    (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c) : False := by
  obtain ⟨iab, hiab⟩ := Function.ne_iff.mp habne
  obtain ⟨iac, hiac⟩ := Function.ne_iff.mp hacne
  obtain ⟨ibc, hibc⟩ := Function.ne_iff.mp hbcne
  let m := max iab (max iac ibc) + 1
  have hAB : prefixCode a m ≠ prefixCode b m := by
    intro h
    have hp := congrFun (MultiplicativeAvoidanceGap.T13.blockCode_injective 10 m h)
      (⟨iab, by simp [m]⟩ : Fin m)
    exact hiab hp
  have hAC : prefixCode a m ≠ prefixCode c m := by
    intro h
    have hp := congrFun (MultiplicativeAvoidanceGap.T13.blockCode_injective 10 m h)
      (⟨iac, by simp [m]⟩ : Fin m)
    exact hiac hp
  have hBC : prefixCode b m ≠ prefixCode c m := by
    intro h
    have hp := congrFun (MultiplicativeAvoidanceGap.T13.blockCode_injective 10 m h)
      (⟨ibc, by simp [m]⟩ : Fin m)
    exact hibc hp
  have hABle := prefixCode_le_add_one_of_realValue_eq a b m hab
  have hBAle := prefixCode_le_add_one_of_realValue_eq b a m hab.symm
  have hACle := prefixCode_le_add_one_of_realValue_eq a c m hac
  have hCAle := prefixCode_le_add_one_of_realValue_eq c a m hac.symm
  have hBCle := prefixCode_le_add_one_of_realValue_eq b c m (hab.symm.trans hac)
  have hCBle := prefixCode_le_add_one_of_realValue_eq c b m (hac.symm.trans hab)
  have hvAB : (prefixCode a m).val ≠ (prefixCode b m).val := by
    exact fun h => hAB (Fin.ext h)
  have hvAC : (prefixCode a m).val ≠ (prefixCode c m).val := by
    exact fun h => hAC (Fin.ext h)
  have hvBC : (prefixCode b m).val ≠ (prefixCode c m).val := by
    exact fun h => hBC (Fin.ext h)
  omega

/-- The real endpoint zero has only its all-zero decimal stream. -/
theorem decimalStream_eq_of_realValue_eq_zero
    {a b : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream}
    (ha : Real.ofDigits a = 0) (hb : Real.ofDigits b = 0) : a = b := by
  funext n
  let m := n + 1
  have hca := MultiplicativeAvoidanceGap.T13.ofDigits_mem_cylinder 10 m (by omega) a
  have hcb := MultiplicativeAvoidanceGap.T13.ofDigits_mem_cylinder 10 m (by omega) b
  have hp : (0 : ℝ) < (10 : ℝ) ^ m := by positivity
  have ha0 : (prefixCode a m).val = 0 := by
    have hle : ((prefixCode a m).val : ℝ) ≤ 0 := by
      have := hca.1
      rw [ha] at this
      have hmul := (div_le_iff₀ hp).mp (by simpa [prefixCode] using this)
      simpa using hmul
    exact_mod_cast (le_antisymm hle (Nat.cast_nonneg _))
  have hb0 : (prefixCode b m).val = 0 := by
    have hle : ((prefixCode b m).val : ℝ) ≤ 0 := by
      have := hcb.1
      rw [hb] at this
      have hmul := (div_le_iff₀ hp).mp (by simpa [prefixCode] using this)
      simpa using hmul
    exact_mod_cast (le_antisymm hle (Nat.cast_nonneg _))
  have hcode : prefixCode a m = prefixCode b m := Fin.ext (ha0.trans hb0.symm)
  have hprefix := MultiplicativeAvoidanceGap.T13.blockCode_injective 10 m hcode
  exact congrFun hprefix (⟨n, by simp [m]⟩ : Fin m)

/-- The real endpoint one has only its all-nine decimal stream. -/
theorem decimalStream_eq_of_realValue_eq_one
    {a b : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream}
    (ha : Real.ofDigits a = 1) (hb : Real.ofDigits b = 1) : a = b := by
  funext n
  let m := n + 1
  have hca := MultiplicativeAvoidanceGap.T13.ofDigits_mem_cylinder 10 m (by omega) a
  have hcb := MultiplicativeAvoidanceGap.T13.ofDigits_mem_cylinder 10 m (by omega) b
  have hp : (0 : ℝ) < (10 : ℝ) ^ m := by positivity
  have hpow : 0 < 10 ^ m := pow_pos (by omega) _
  have code_eq_top
      (x : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream)
      (hx : Real.ofDigits x = 1)
      (hc := MultiplicativeAvoidanceGap.T13.ofDigits_mem_cylinder 10 m (by omega) x) :
      (prefixCode x m).val = 10 ^ m - 1 := by
    have hden : ((10 : ℝ) ^ m) ≤ (prefixCode x m).val + 1 := by
      have hu := hc.2
      rw [hx] at hu
      have := (le_div_iff₀ hp).mp (by simpa [prefixCode] using hu)
      simpa using this
    have hdenNat : 10 ^ m ≤ (prefixCode x m).val + 1 := by exact_mod_cast hden
    have hlt := (prefixCode x m).isLt
    omega
  have haTop := code_eq_top a ha hca
  have hbTop := code_eq_top b hb hcb
  have hcode : prefixCode a m = prefixCode b m := Fin.ext (haTop.trans hbTop.symm)
  have hprefix := MultiplicativeAvoidanceGap.T13.blockCode_injective 10 m hcode
  exact congrFun hprefix (⟨n, by simp [m]⟩ : Fin m)

/-- Endpoint-inclusive decimal evaluation on the circle has fibers of extended
cardinality at most two.  Using `encard`, rather than only `ncard`, also proves
that every fiber is finite. -/
theorem circleValue_fiber_encard_le_two (x : UnitAddCircle) :
    {a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream |
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a = x}.encard ≤ 2 := by
  by_contra hle
  have hthree : (3 : ℕ∞) ≤
      {a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream |
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a = x}.encard := by
    have hlt := not_le.mp (show ¬({a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream |
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a = x}.encard ≤
        (2 : ℕ∞)) from hle)
    simpa using (ENat.add_one_le_iff (m := (2 : ℕ∞)) (n :=
      {a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream |
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a = x}.encard)
      (by simp)).mpr hlt
  obtain ⟨s, hs, hsCard⟩ := Set.exists_subset_encard_eq hthree
  obtain ⟨a, b, c, hab, hac, hbc, hsabc⟩ := Set.encard_eq_three.mp hsCard
  have ha : DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a = x :=
    hs (by rw [hsabc]; simp)
  have hb : DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue b = x :=
    hs (by rw [hsabc]; simp)
  have hc : DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue c = x :=
    hs (by rw [hsabc]; simp)
  have aIcc : Real.ofDigits a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.ofDigits_nonneg a, Real.ofDigits_le_one a⟩
  have bIcc : Real.ofDigits b ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.ofDigits_nonneg b, Real.ofDigits_le_one b⟩
  have cIcc : Real.ofDigits c ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.ofDigits_nonneg c, Real.ofDigits_le_one c⟩
  have habEnd :=
    (MultiplicativeAvoidanceGap.T13.unitAddCircle_eq_iff_endpointEq aIcc bIcc).mp
      (ha.trans hb.symm)
  have hacEnd :=
    (MultiplicativeAvoidanceGap.T13.unitAddCircle_eq_iff_endpointEq aIcc cIcc).mp
      (ha.trans hc.symm)
  rcases habEnd with habv | ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
  · rcases hacEnd with hacv | ⟨ha0, hc1⟩ | ⟨ha1, hc0⟩
    · exact not_three_pairwise_distinct_of_realValue_eq a b c habv hacv hab hac hbc
    · exact hab (decimalStream_eq_of_realValue_eq_zero ha0 (habv ▸ ha0))
    · exact hab (decimalStream_eq_of_realValue_eq_one ha1 (habv ▸ ha1))
  · rcases hacEnd with hacv | ⟨_ha0, hc1⟩ | ⟨ha1, _hc0⟩
    · exact hac (decimalStream_eq_of_realValue_eq_zero ha0 (hacv ▸ ha0))
    · exact hbc (decimalStream_eq_of_realValue_eq_one hb1 hc1)
    · norm_num [ha0] at ha1
  · rcases hacEnd with hacv | ⟨ha0, _hc1⟩ | ⟨_ha1, hc0⟩
    · exact hac (decimalStream_eq_of_realValue_eq_one ha1 (hacv ▸ ha1))
    · norm_num [ha1] at ha0
    · exact hbc (decimalStream_eq_of_realValue_eq_zero hb0 hc0)

/-! ## Graph paths and simultaneous raw runs -/

/-- A coherent infinite raw run.  Its KMP coordinates start empty; its initial
carry tuple is arbitrary in the endpoint-complete finite range. -/
def IsRawRun {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R) : Prop :=
  (∀ i, (q 0).kmp i = (singletonFamily w hw).initialState) ∧
    ∀ n, RawStep (q n) (d n) (q (n + 1))

/-- Encode a raw run as graph labels, using the first label to record its
finite start carry tuple. -/
def encodeLabels {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R) : ℕ → Label R
  | 0 => .initial (q 0).carry (d 0)
  | n + 1 => .next (d (n + 1))

theorem transition_ne_some_none
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (s : (carryKMPGraph w hw R).State) (a : Label R) :
    (carryKMPGraph w hw R).transition s a ≠ some none := by
  cases s with
  | none =>
      cases a with
      | initial c d => simp [carryKMPGraph, liftRawNext]
      | next d => simp [carryKMPGraph]
  | some q =>
      cases a with
      | initial c d => simp [carryKMPGraph]
      | next d => simp [carryKMPGraph, liftRawNext]

theorem transition_from_root
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {a : Label R} {s : (carryKMPGraph w hw R).State}
    (h : (carryKMPGraph w hw R).transition none a = some s) :
    ∃ c d q, a = .initial c d ∧ s = some q ∧
      RawStep (initialRaw w hw R c) d q := by
  cases a with
  | next d => simp [carryKMPGraph] at h
  | initial c d =>
      have hs : s ≠ none := by
        rintro rfl
        exact transition_ne_some_none none (.initial c d) h
      obtain ⟨q, rfl⟩ := Option.ne_none_iff_exists'.mp hs
      exact ⟨c, d, q, rfl, rfl, transition_initial_eq_some_iff.mp h⟩

theorem transition_from_raw
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : RawState w hw R} {a : Label R}
    {s : (carryKMPGraph w hw R).State}
    (h : (carryKMPGraph w hw R).transition (some q) a = some s) :
    ∃ d q', a = .next d ∧ s = some q' ∧ RawStep q d q' := by
  cases a with
  | initial c d => simp [carryKMPGraph] at h
  | next d =>
      have hs : s ≠ none := by
        rintro rfl
        exact transition_ne_some_none (some q) (.next d) h
      obtain ⟨q', rfl⟩ := Option.ne_none_iff_exists'.mp hs
      exact ⟨d, q', rfl, rfl, transition_next_eq_some_iff.mp h⟩

/-- Edges canonically generated by a raw run. -/
def rawRunEdges {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R) :
    ℕ → (carryKMPGraph w hw R).Edge
  | 0 => ⟨none, .initial (q 0).carry (d 0), some (q 1)⟩
  | n + 1 => ⟨some (q (n + 1)), .next (d (n + 1)), some (q (n + 2))⟩

theorem rawRunEdges_isInfiniteWalk
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) :
    (carryKMPGraph w hw R).IsInfiniteWalk none (rawRunEdges q d) := by
  constructor
  · rfl
  · intro n
    constructor
    · cases n with
      | zero =>
          apply transition_initial_eq_some_iff.mpr
          have h0 := hqd.2 0
          simpa [initialRaw_carry_eq_of_kmp (q 0) hqd.1] using h0
      | succ n =>
          exact transition_next_eq_some_iff.mpr (hqd.2 (n + 1))
    · cases n <;> rfl

@[simp] theorem rawRunEdges_label
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R) (n : ℕ) :
    (rawRunEdges q d n).label = encodeLabels q d n := by
  cases n <;> rfl

/-- T46's infinite graph language is exactly the encoded raw-run language. -/
theorem mem_graphLanguage_iff_exists_rawRun
    {w : List (Fin 10)} (hw : w ≠ []) (R : ℕ) (x : ℕ → Label R) :
    x ∈ (carryKMPGraph w hw R).InfiniteLabelLanguage ↔
      ∃ (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R),
        IsRawRun q d ∧ x = encodeLabels q d := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hv0 := (hz.2 0).1
    change (carryKMPGraph w hw R).transition (z 0).src (z 0).label =
      some (z 0).dst at hv0
    rw [hz.1] at hv0
    have hroot := transition_from_root hv0
    obtain ⟨c, d0, q1, hlabel0, hdst0, hstep0⟩ := hroot
    have hdst (n : ℕ) : ∃ q', (z n).dst = some q' := by
      have hv := (hz.2 n).1
      cases htarget : (z n).dst with
      | none =>
          have hv' : (carryKMPGraph w hw R).transition (z n).src (z n).label =
              some none := by
            change (carryKMPGraph w hw R).transition (z n).src (z n).label =
              some (z n).dst at hv
            simpa [htarget] using hv
          exact (transition_ne_some_none (z n).src (z n).label hv').elim
      | some q' => exact ⟨q', rfl⟩
    let q : ℕ → RawState w hw R
      | 0 => initialRaw w hw R c
      | n + 1 => Classical.choose (hdst n)
    let d : ℕ → DigitColumn R := fun n => (z n).label.digits
    have hq1 : q 1 = q1 := by
      dsimp [q]
      apply Option.some.inj
      rw [← Classical.choose_spec (hdst 0), hdst0]
    have hrun : IsRawRun q d := by
      constructor
      · intro i
        rfl
      · intro n
        cases n with
        | zero =>
            simpa [q, d, hlabel0, hq1] using hstep0
        | succ n =>
            have hsrc : (z (n + 1)).src = some (q (n + 1)) := by
              calc
                (z (n + 1)).src = (z n).dst := (hz.2 n).2.symm
                _ = some (q (n + 1)) := by
                  change (z n).dst = some (Classical.choose (hdst n))
                  exact Classical.choose_spec (hdst n)
            have hnext := transition_from_raw (q := q (n + 1))
              (show (carryKMPGraph w hw R).transition (some (q (n + 1)))
                  (z (n + 1)).label = some (z (n + 1)).dst by
                rw [← hsrc]
                exact (hz.2 (n + 1)).1)
            obtain ⟨dn, qn, hlabel, hdstn, hstep⟩ := hnext
            have hqnext : q (n + 2) = qn := by
              change Classical.choose (hdst (n + 1)) = qn
              apply Option.some.inj
              rw [← Classical.choose_spec (hdst (n + 1)), hdstn]
            simpa [d, hlabel, hqnext] using hstep
    refine ⟨q, d, hrun, ?_⟩
    funext n
    cases n with
    | zero =>
        simp only [encodeLabels, q, d, initialRaw, hlabel0, Label.digits]
    | succ n =>
        have hsrc : (z (n + 1)).src = some (q (n + 1)) := by
          calc
            (z (n + 1)).src = (z n).dst := (hz.2 n).2.symm
            _ = some (q (n + 1)) := by
              change (z n).dst = some (Classical.choose (hdst n))
              exact Classical.choose_spec (hdst n)
        obtain ⟨dn, qn, hlabel, _, _⟩ := transition_from_raw (q := q (n + 1))
          (show (carryKMPGraph w hw R).transition (some (q (n + 1)))
              (z (n + 1)).label = some (z (n + 1)).dst by
            rw [← hsrc]
            exact (hz.2 (n + 1)).1)
        simp only [encodeLabels, d, hlabel, Label.digits]
  · rintro ⟨q, d, hrun, hx⟩
    rw [hx]
    exact ⟨rawRunEdges q d, rawRunEdges_isInfiniteWalk hrun, by
      funext n
      exact (rawRunEdges_label q d n).symm⟩

/-! ## KMP and carry semantics of raw runs -/

/-- Decimal stream in coordinate `i` of a digit-column stream. -/
def componentStream {R : ℕ} (d : ℕ → DigitColumn R) (i : Fin (R + 1)) :
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream :=
  fun n => d n i

/-- The finite KMP path cut out by the first `n` columns of a raw run. -/
def kmpPathOfRawRun
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) (i : Fin (R + 1)) :
    (n : ℕ) → MultiplicativeAvoidanceGap.T24.ForbiddenFamily.LabelledPath
      (singletonFamily w hw).Step n (singletonFamily w hw).initialState ((q n).kmp i)
  | 0 => PLift.up (hqd.1 i).symm
  | n + 1 =>
      ⟨(q n).kmp i, kmpPathOfRawRun hqd i n,
        ⟨d n i, (hqd.2 n).1 i⟩⟩

theorem pathWord_kmpPathOfRawRun
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) (i : Fin (R + 1)) (n : ℕ) :
    MultiplicativeAvoidanceGap.T24.ForbiddenFamily.pathWord
        (kmpPathOfRawRun hqd i n) =
      List.ofFn (fun k : Fin n => d k.val i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [kmpPathOfRawRun,
        MultiplicativeAvoidanceGap.T24.ForbiddenFamily.pathWord, ih]
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]

theorem finitePrefix_avoids_of_rawRun
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) (i : Fin (R + 1)) (n : ℕ) :
    (singletonFamily w hw).Avoids
      (List.ofFn (fun k : Fin n => d k.val i)) := by
  rw [← (singletonFamily w hw).accepts_iff_avoids]
  unfold MultiplicativeAvoidanceGap.T24.ForbiddenFamily.Accepts
  refine ⟨(q n).kmp i, ?_⟩
  rw [List.length_ofFn]
  exact ⟨kmpPathOfRawRun hqd i n, pathWord_kmpPathOfRawRun hqd i n⟩

/-- Every KMP coordinate of a raw run avoids the forbidden word forever. -/
theorem componentStream_avoidsWord_of_rawRun
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) (i : Fin (R + 1)) :
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord w
      (componentStream d i) := by
  intro start hocc
  let n := start + w.length
  have havoid := finitePrefix_avoids_of_rawRun hqd i n
  apply havoid w (by simp [singletonFamily])
  apply List.infix_iff_getElem?.mpr
  refine ⟨start, by simp [n]; omega, ?_⟩
  intro k hk
  have hkocc := hocc ⟨k, hk⟩
  simpa [componentStream, n, List.getElem?_eq_getElem, Nat.add_comm] using
    And.intro (by omega : k + start < start + w.length) hkocc

/-- Absolutely summable real carry series used to telescope the finite carry
recurrence without choosing half-open decimal representatives. -/
def carryTerm {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (j : Fin R) (n : ℕ) : ℝ :=
  ((q n).carry j).1 * (1 / 10 : ℝ) ^ n

theorem summable_carryTerm
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (j : Fin R) :
    Summable (carryTerm q j) := by
  have hgeom : Summable (fun n : ℕ => (16 : ℝ) * (1 / 10 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 10 : ℝ)‖ < 1)).mul_left 16
  apply Summable.of_norm_bounded hgeom
  intro n
  have habs : |(((q n).carry j).1 : ℝ)| ≤ 16 := by
    rw [abs_le]
    constructor
    · exact_mod_cast (show (-16 : ℤ) ≤ ((q n).carry j).1 by
        linarith [carry_lower ((q n).carry j)])
    · exact_mod_cast carry_upper ((q n).carry j)
  rw [carryTerm, Real.norm_eq_abs, abs_mul]
  have hpow : 0 ≤ (1 / 10 : ℝ) ^ n := pow_nonneg (by norm_num) _
  rw [abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_right habs hpow

/-- The carry equations of a raw run imply the exact adjacent real-value
identity; the bounded carry series telescopes completely. -/
theorem rawRun_adjacent_realValue
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) (j : Fin R) :
    16 * Real.ofDigits (componentStream d j.castSucc) =
      Real.ofDigits (componentStream d j.succ) + (((q 0).carry j).1 : ℝ) := by
  let a := componentStream d j.castSucc
  let b := componentStream d j.succ
  have hterm (n : ℕ) :
      16 * Real.ofDigitsTerm a n + carryTerm q j (n + 1) =
        Real.ofDigitsTerm b n + carryTerm q j n := by
    have hc := congrArg (fun z : ℤ => (z : ℝ)) ((hqd.2 n).2 j)
    push_cast at hc
    simp only [a, b, Real.ofDigitsTerm, componentStream, carryTerm]
    norm_num only [Nat.cast_ofNat]
    have hpow : ((10 : ℝ) ^ (n + 1))⁻¹ = (1 / 10 : ℝ) ^ (n + 1) := by
      rw [one_div, inv_pow]
    rw [hpow]
    have hshift : (1 / 10 : ℝ) ^ (n + 1) = (1 / 10 : ℝ) ^ n / 10 := by
      rw [pow_succ]
      ring
    rw [hshift]
    field_simp
    linarith
  have hDigitA : Summable (fun n => 16 * Real.ofDigitsTerm a n) :=
    Real.summable_ofDigitsTerm.mul_left 16
  have hDigitB : Summable (Real.ofDigitsTerm b) := Real.summable_ofDigitsTerm
  have hCarry : Summable (carryTerm q j) := summable_carryTerm q j
  have hCarryShift : Summable (fun n => carryTerm q j (n + 1)) :=
    (summable_nat_add_iff 1).2 hCarry
  have hsum : (∑' n : ℕ,
      (16 * Real.ofDigitsTerm a n + carryTerm q j (n + 1))) =
      ∑' n : ℕ, (Real.ofDigitsTerm b n + carryTerm q j n) := by
    exact tsum_congr hterm
  rw [hDigitA.tsum_add hCarryShift, hDigitB.tsum_add hCarry] at hsum
  have hDigitA_sum : (∑' n, 16 * Real.ofDigitsTerm a n) = 16 * Real.ofDigits a := by
    simpa [Real.ofDigits] using
      (Real.summable_ofDigitsTerm (digits := a)).tsum_mul_left 16
  have hCarry_split : (∑' n, carryTerm q j n) =
      carryTerm q j 0 + ∑' n, carryTerm q j (n + 1) := by
    simpa using (hCarry.sum_add_tsum_nat_add 1).symm
  rw [hDigitA_sum, hCarry_split] at hsum
  have hmain : 16 * Real.ofDigits a =
      Real.ofDigits b + (((q 0).carry j).1 : ℝ) := by
    rw [show (∑' n, Real.ofDigitsTerm b n) = Real.ofDigits b by rfl] at hsum
    dsimp [carryTerm] at hsum
    norm_num only [pow_zero, mul_one] at hsum
    linarith
  simpa [a, b] using hmain

/-- Adjacent components of a raw run represent multiplication by sixteen on
the circle. -/
theorem rawRun_adjacent_circleValue
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) (j : Fin R) :
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
        (componentStream d j.succ) =
      DecimalFactorEntropy.TransversalEntropy.circleMul 16
        (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
          (componentStream d j.castSucc)) := by
  have hreal := rawRun_adjacent_realValue hqd j
  change (Real.ofDigits (componentStream d j.succ) : UnitAddCircle) =
    16 • (Real.ofDigits (componentStream d j.castSucc) : UnitAddCircle)
  rw [← AddCircle.coe_nsmul (p := (1 : ℝ))]
  simp only [nsmul_eq_mul]
  change (Real.ofDigits (componentStream d j.succ) : UnitAddCircle) =
    ((16 * Real.ofDigits (componentStream d j.castSucc) : ℝ) : UnitAddCircle)
  rw [hreal]
  simp only [AddCircle.coe_add]
  have hcarry : ((((q 0).carry j).1 : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2
    exact ⟨((q 0).carry j).1, by simp⟩
  rw [hcarry, add_zero]

/-- Every coordinate of a raw run is the corresponding power-of-sixteen image
of coordinate zero. -/
theorem rawRun_component_circleValue
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    {q : ℕ → RawState w hw R} {d : ℕ → DigitColumn R}
    (hqd : IsRawRun q d) (n : ℕ) (hn : n ≤ R) :
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
        (componentStream d ⟨n, by omega⟩) =
      DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ n)
        (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
          (componentStream d ⟨0, by omega⟩)) := by
  induction n with
  | zero =>
      change _ = 1 • _
      rw [one_nsmul]
  | succ n ih =>
      let j : Fin R := ⟨n, by omega⟩
      have hadj := rawRun_adjacent_circleValue hqd j
      have hprev := ih (by omega)
      calc
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
            (componentStream d ⟨n + 1, by omega⟩) =
            DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
              (componentStream d j.succ) := by rfl
        _ = DecimalFactorEntropy.TransversalEntropy.circleMul 16
              (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
                (componentStream d j.castSucc)) := hadj
        _ = DecimalFactorEntropy.TransversalEntropy.circleMul 16
              (DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ n)
                (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
                  (componentStream d ⟨0, by omega⟩))) := by
                    rw [show componentStream d j.castSucc =
                      componentStream d ⟨n, by omega⟩ by rfl, hprev]
        _ = DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ (n + 1))
              (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
                (componentStream d ⟨0, by omega⟩)) := by
                  rw [DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleMul_comp]
                  congr 1
                  simp [pow_succ, Nat.mul_comm]

/-- Evaluate a graph label stream through its coordinate-zero decimal digits. -/
def graphEvaluation {R : ℕ} (x : ℕ → Label R) : UnitAddCircle :=
  DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
    (fun n => (x n).digits ⟨0, by omega⟩)

theorem graphEvaluation_encodeLabels
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R) :
    graphEvaluation (encodeLabels q d) =
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
        (componentStream d ⟨0, by omega⟩) := by
  unfold graphEvaluation componentStream
  apply congrArg DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
  funext n
  cases n <;> rfl

/-- Every infinite graph label stream evaluates into T44's endpoint-safe core. -/
theorem graphEvaluation_mem_core_of_mem_language
    {w : List (Fin 10)} (hw : w ≠ []) (R : ℕ)
    {x : ℕ → Label R}
    (hx : x ∈ (carryKMPGraph w hw R).InfiniteLabelLanguage) :
    graphEvaluation x ∈
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.Core w R := by
  obtain ⟨q, d, hrun, rfl⟩ :=
    (mem_graphLanguage_iff_exists_rawRun hw R x).mp hx
  rw [graphEvaluation_encodeLabels,
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.core_eq_finiteAvoidanceIntersection]
  intro j hj
  rw [← rawRun_component_circleValue hrun j hj]
  exact ⟨componentStream d ⟨j, by omega⟩,
    componentStream_avoidsWord_of_rawRun hrun ⟨j, by omega⟩, rfl⟩

/-- Every finite prefix of a T44-avoiding stream is accepted by the singleton
KMP family. -/
theorem singletonFamily_avoids_prefix_of_avoidsWord
    {w : List (Fin 10)} (hw : w ≠ [])
    {a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream}
    (ha : DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord w a)
    (n : ℕ) :
    (singletonFamily w hw).Avoids (List.ofFn fun i : Fin n => a i.val) := by
  intro u hu hinfix
  have huEq : u = w := by simpa [singletonFamily] using hu
  subst u
  obtain ⟨start, hlen, hget⟩ := List.infix_iff_getElem?.mp hinfix
  apply ha start
  intro i
  have hi := hget i.val i.isLt
  have hi' : i.val + start < n ∧ w.get i = a (i.val + start) := by
    simpa [List.getElem?_eq_getElem] using hi.symm
  simpa [Nat.add_comm] using hi'.2.symm

/-- Adjacent endpoint-inclusive decimal expansions have an integer carry in
the complete range `[-1,16]` at every tail. -/
theorem exists_endpointCarry
    (a b : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream)
    (hab : DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue b =
      DecimalFactorEntropy.TransversalEntropy.circleMul 16
        (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a))
    (n : ℕ) :
    ∃ c : Carry,
      ((c.1 : ℤ) : ℝ) =
        16 * Real.ofDigits
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n a) -
        Real.ofDigits
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n b) := by
  have hshift :
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n b) =
        DecimalFactorEntropy.TransversalEntropy.circleMul 16
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
            (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n a)) := by
    calc
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n b) =
          DecimalFactorEntropy.TransversalEntropy.circleMul (10 ^ n)
            (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue b) :=
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue_streamShift b n
      _ = DecimalFactorEntropy.TransversalEntropy.circleMul (10 ^ n)
            (DecimalFactorEntropy.TransversalEntropy.circleMul 16
              (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a)) := by rw [hab]
      _ = DecimalFactorEntropy.TransversalEntropy.circleMul 16
            (DecimalFactorEntropy.TransversalEntropy.circleMul (10 ^ n)
              (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a)) :=
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleMul_commute _ _ _
      _ = DecimalFactorEntropy.TransversalEntropy.circleMul 16
            (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
              (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n a)) := by
        rw [DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue_streamShift]
  let A := Real.ofDigits
    (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n a)
  let B := Real.ofDigits
    (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n b)
  have hzero : (((16 : ℝ) * A - B : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    rw [show (16 : ℝ) * A = 16 • A by simp [nsmul_eq_mul],
      AddCircle.coe_nsmul]
    have hs : (B : UnitAddCircle) = 16 • (A : UnitAddCircle) := by
      simpa [A, B,
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue] using hshift
    rw [hs]
    simp
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero
  have hzreal : (z : ℝ) = 16 * A - B := by
    simpa [zsmul_eq_mul] using hz
  have hA0 : 0 ≤ A := Real.ofDigits_nonneg _
  have hA1 : A ≤ 1 := Real.ofDigits_le_one _
  have hB0 : 0 ≤ B := Real.ofDigits_nonneg _
  have hB1 : B ≤ 1 := Real.ofDigits_le_one _
  have hzlow : (-1 : ℤ) ≤ z := by
    exact_mod_cast (show (-1 : ℝ) ≤ (z : ℝ) by rw [hzreal]; linarith)
  have hzhigh : z ≤ (16 : ℤ) := by
    exact_mod_cast (show (z : ℝ) ≤ 16 by rw [hzreal]; linarith)
  exact ⟨⟨z, Finset.mem_Icc.mpr ⟨hzlow, hzhigh⟩⟩, by simpa [A, B] using hzreal⟩

/-- One-step real recurrence for a shifted decimal expansion. -/
theorem ten_mul_tailValue
    (a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream)
    (n : ℕ) :
    10 * Real.ofDigits
        (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n a) =
      (a n).val + Real.ofDigits
        (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift (n + 1) a) := by
  have h := Real.ofDigits_eq_sum_add_ofDigits
    (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n a) 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Real.ofDigitsTerm, pow_one] at h
  have hshift : (fun i =>
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n a (i + 1)) =
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift (n + 1) a := by
    funext i
    simp [DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift,
      Nat.add_comm, Nat.add_left_comm]
  rw [hshift] at h
  dsimp [DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift] at h
  field_simp at h
  simpa [mul_comm] using h

/-- Every point of T44's core supplies a coherent endpoint-complete raw run. -/
theorem exists_rawRun_of_mem_core
    {w : List (Fin 10)} (hw : w ≠ []) (R : ℕ) (x : UnitAddCircle)
    (hx : x ∈ DecimalFactorEntropy.T44EndpointSafeInvariantCore.Core w R) :
    ∃ (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R),
      IsRawRun q d ∧
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
        (componentStream d ⟨0, by omega⟩) = x := by
  rw [DecimalFactorEntropy.T44EndpointSafeInvariantCore.core_eq_finiteAvoidanceIntersection] at hx
  have hexp (i : Fin (R + 1)) :
      ∃ a : DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream,
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord w a ∧
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a =
          DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ i.val) x := by
    exact (DecimalFactorEntropy.T44EndpointSafeInvariantCore.mem_KWord_iff_exists_avoiding_expansion
      w _).mp (hx i.val (by omega))
  let a : Fin (R + 1) →
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream :=
    fun i => Classical.choose (hexp i)
  have haAvoid (i : Fin (R + 1)) :
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord w (a i) :=
    (Classical.choose_spec (hexp i)).1
  have haValue (i : Fin (R + 1)) :
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue (a i) =
        DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ i.val) x :=
    (Classical.choose_spec (hexp i)).2
  have haAdjacent (j : Fin R) :
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue (a j.succ) =
        DecimalFactorEntropy.TransversalEntropy.circleMul 16
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
            (a j.castSucc)) := by
    rw [haValue, haValue,
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleMul_comp]
    congr 1
    simp [pow_succ, Nat.mul_comm]
  have hcarry (n : ℕ) (j : Fin R) :
      ∃ c : Carry,
        ((c.1 : ℤ) : ℝ) =
          16 * Real.ofDigits
            (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n (a j.castSucc)) -
          Real.ofDigits
            (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n (a j.succ)) :=
    exists_endpointCarry (a j.castSucc) (a j.succ) (haAdjacent j) n
  let c : ℕ → Fin R → Carry := fun n j => Classical.choose (hcarry n j)
  have hc (n : ℕ) (j : Fin R) :
      (((c n j).1 : ℤ) : ℝ) =
        16 * Real.ofDigits
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n (a j.castSucc)) -
        Real.ofDigits
          (DecimalFactorEntropy.T44EndpointSafeInvariantCore.streamShift n (a j.succ)) :=
    Classical.choose_spec (hcarry n j)
  let d : ℕ → DigitColumn R := fun n i => a i n
  let q : ℕ → RawState w hw R := fun n =>
    { kmp := fun i => (singletonFamily w hw).activeState
        (List.ofFn fun k : Fin n => a i k.val)
      carry := c n }
  have hrun : IsRawRun q d := by
    constructor
    · intro i
      dsimp [q]
      exact (singletonFamily w hw).initialState_eq_activeState.symm
    · intro n
      constructor
      · intro i
        let p := List.ofFn fun k : Fin n => a i k.val
        let p' := List.ofFn fun k : Fin (n + 1) => a i k.val
        have hp : (singletonFamily w hw).Avoids p := by
          exact singletonFamily_avoids_prefix_of_avoidsWord hw (haAvoid i) n
        have hp' : (singletonFamily w hw).Avoids p' := by
          exact singletonFamily_avoids_prefix_of_avoidsWord hw (haAvoid i) (n + 1)
        have happend : p ++ [a i n] = p' := by
          dsimp [p, p']
          rw [List.ofFn_succ']
          simp [List.concat_eq_append]
        have hstep := ((singletonFamily w hw).step_activeState_iff p (a i n)
          ((singletonFamily w hw).activeState p') hp).mpr
            ⟨by simpa [happend] using hp', by rw [happend]⟩
        simpa [q, d, p, p'] using hstep
      · intro j
        have hcn := hc n j
        have hcnext := hc (n + 1) j
        have htenA := ten_mul_tailValue (a j.castSucc) n
        have htenB := ten_mul_tailValue (a j.succ) n
        have hreal :
            16 * ((a j.castSucc n).val : ℝ) + (((c (n + 1) j).1 : ℤ) : ℝ) =
              ((a j.succ n).val : ℝ) + 10 * (((c n j).1 : ℤ) : ℝ) := by
          rw [hcn, hcnext]
          linarith
        dsimp [q, d]
        exact_mod_cast hreal
  refine ⟨q, d, hrun, ?_⟩
  rw [show componentStream d (⟨0, by omega⟩ : Fin (R + 1)) =
      a (⟨0, by omega⟩ : Fin (R + 1)) by
    funext n
    rfl]
  rw [haValue]
  change 1 • x = x
  exact one_nsmul x

/-- Every core point is the evaluation of an infinite path in the constructed
finite graph. -/
theorem mem_graphEvaluation_image_of_mem_core
    {w : List (Fin 10)} (hw : w ≠ []) (R : ℕ) (x : UnitAddCircle)
    (hx : x ∈ DecimalFactorEntropy.T44EndpointSafeInvariantCore.Core w R) :
    x ∈ graphEvaluation '' (carryKMPGraph w hw R).InfiniteLabelLanguage := by
  obtain ⟨q, d, hrun, heval⟩ := exists_rawRun_of_mem_core hw R x hx
  refine ⟨encodeLabels q d, ?_, ?_⟩
  · exact (mem_graphLanguage_iff_exists_rawRun hw R _).mpr ⟨q, d, hrun, rfl⟩
  · rw [graphEvaluation_encodeLabels, heval]

/-- Named exact graph-image theorem, quantified over every nonempty word and
every finite depth. -/
theorem graphEvaluation_image_eq_core
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    graphEvaluation '' (carryKMPGraph w hw R).InfiniteLabelLanguage =
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.Core w R := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact graphEvaluation_mem_core_of_mem_language hw R hx
  · intro x hx
    exact mem_graphEvaluation_image_of_mem_core hw R x hx

/-! ## Finite graph-evaluation fibers and the T46 criterion -/

/-- All component decimal streams exposed by a graph label stream. -/
def allComponents {R : ℕ} (x : ℕ → Label R) :
    Fin (R + 1) → DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream :=
  fun i n => (x n).digits i

theorem allComponents_encodeLabels
    {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R) :
    allComponents (encodeLabels q d) = fun i => componentStream d i := by
  funext i n
  cases n <;> rfl

theorem circleValue_allComponents_of_mem_language
    {w : List (Fin 10)} (hw : w ≠ []) (R : ℕ)
    {x : ℕ → Label R}
    (hx : x ∈ (carryKMPGraph w hw R).InfiniteLabelLanguage)
    (i : Fin (R + 1)) :
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
        (allComponents x i) =
      DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ i.val)
        (graphEvaluation x) := by
  obtain ⟨q, d, hrun, rfl⟩ :=
    (mem_graphLanguage_iff_exists_rawRun hw R x).mp hx
  rw [allComponents_encodeLabels, graphEvaluation_encodeLabels]
  exact rawRun_component_circleValue hrun i.val (by omega)

/-- On the infinite graph language, the tuple of all component digit streams
is injective.  The initial carries are recovered from adjacent real values. -/
theorem allComponents_injOn_graphLanguage
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    Set.InjOn allComponents
      (carryKMPGraph w hw R).InfiniteLabelLanguage := by
  intro x hx y hy hxy
  obtain ⟨qx, dx, hrx, hxEq⟩ :=
    (mem_graphLanguage_iff_exists_rawRun hw R x).mp hx
  obtain ⟨qy, dy, hry, hyEq⟩ :=
    (mem_graphLanguage_iff_exists_rawRun hw R y).mp hy
  rw [hxEq, hyEq] at hxy ⊢
  rw [allComponents_encodeLabels, allComponents_encodeLabels] at hxy
  have hd : dx = dy := by
    funext n i
    exact congrFun (congrFun hxy i) n
  subst dy
  have hc : (qx 0).carry = (qy 0).carry := by
    funext j
    apply Subtype.ext
    have hxreal := rawRun_adjacent_realValue hrx j
    have hyreal := rawRun_adjacent_realValue hry j
    have hcast : ((((qx 0).carry j).1 : ℤ) : ℝ) =
        (((qy 0).carry j).1 : ℤ) := by linarith
    exact_mod_cast hcast
  funext n
  cases n with
  | zero => simp [encodeLabels, hc]
  | succ n => rfl

/-- Fibers of graph evaluation restricted to the graph language are finite.
The coordinate-zero two-expansion theorem is strengthened here by recording
all `R+1` component streams; each coordinate still has at most two choices. -/
theorem graphEvaluation_language_fiber_finite
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) (y : UnitAddCircle) :
    ((carryKMPGraph w hw R).InfiniteLabelLanguage ∩
      graphEvaluation ⁻¹' {y}).Finite := by
  let fiber : Fin (R + 1) →
      Set DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream :=
    fun i => {a | DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a =
      DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ i.val) y}
  have hfiber (i : Fin (R + 1)) : (fiber i).Finite := by
    apply Set.finite_of_encard_le_coe
    exact circleValue_fiber_encard_le_two
      (DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ i.val) y)
  have hpi : (Set.univ.pi fiber).Finite := Set.Finite.pi fun i => hfiber i
  let s : Set (ℕ → Label R) :=
    (carryKMPGraph w hw R).InfiniteLabelLanguage ∩ graphEvaluation ⁻¹' {y}
  have himage : allComponents '' s ⊆ Set.univ.pi fiber := by
    rintro A ⟨x, hx, rfl⟩
    rw [Set.mem_pi]
    intro i _hi
    change DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
      (allComponents x i) =
        DecimalFactorEntropy.TransversalEntropy.circleMul (16 ^ i.val) y
    rw [circleValue_allComponents_of_mem_language hw R hx.1]
    have heval : graphEvaluation x = y := hx.2
    rw [heval]
  have hinj : Set.InjOn allComponents s :=
    (allComponents_injOn_graphLanguage w hw R).mono (inter_subset_left)
  exact (hpi.subset himage).of_finite_image hinj

/-- The graph language is finite exactly when its evaluated core image is
finite. -/
theorem graphLanguage_finite_iff_core_finite
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    (carryKMPGraph w hw R).InfiniteLabelLanguage.Finite ↔
      (DecimalFactorEntropy.T44EndpointSafeInvariantCore.Core w R).Finite := by
  rw [← graphEvaluation_image_eq_core w hw R]
  exact DecimalFactorEntropy.T46LiveSCC.Graph.finite_iff_finite_image_of_finite_fibers
    graphEvaluation _ (fun y _hy => graphEvaluation_language_fiber_finite w hw R y)

/-- Named exact equivalence between core finiteness and T46's reachable-live
SCC criterion. -/
theorem core_finite_iff_liveSCCCriterion
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    (DecimalFactorEntropy.T44EndpointSafeInvariantCore.Core w R).Finite ↔
      (carryKMPGraph w hw R).LiveSCCCriterion := by
  rw [← graphLanguage_finite_iff_core_finite w hw R]
  exact (carryKMPGraph w hw R).infiniteLabelLanguage_finite_iff_liveSCCCriterion

/-- A supplied finite SCC table gives an executable Boolean checker for core
finiteness, with no universal extinction assertion. -/
theorem core_finite_iff_sccCertificate_decide_eq_true
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (cert : (carryKMPGraph w hw R).SCCCertificate) :
    (DecimalFactorEntropy.T44EndpointSafeInvariantCore.Core w R).Finite ↔
      @decide (carryKMPGraph w hw R).LiveSCCCriterion
        ((carryKMPGraph w hw R).liveSCCCriterion_decidable_of_certificate cert) = true := by
  rw [core_finite_iff_liveSCCCriterion w hw R]
  exact (carryKMPGraph w hw R).liveSCCCriterion_decide_eq_true_iff cert |>.symm

end DecimalFactorEntropy.T48EndpointCarryKMP

#print axioms DecimalFactorEntropy.T48EndpointCarryKMP.graphEvaluation_image_eq_core
#print axioms DecimalFactorEntropy.T48EndpointCarryKMP.circleValue_fiber_encard_le_two
#print axioms DecimalFactorEntropy.T48EndpointCarryKMP.graphEvaluation_language_fiber_finite
#print axioms DecimalFactorEntropy.T48EndpointCarryKMP.graphLanguage_finite_iff_core_finite
#print axioms DecimalFactorEntropy.T48EndpointCarryKMP.core_finite_iff_liveSCCCriterion
#print axioms DecimalFactorEntropy.T48EndpointCarryKMP.core_finite_iff_sccCertificate_decide_eq_true
