import TheoryLib.PiDigits.T37CrossBaseCarry
import TheoryLib.PiDigits.T39BalancedCarryMyhillNerode
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# T41: externally clocked residual congruence-and-suffix quotients

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This module concerns only the quotient family that records gcd-reduced carry
modulo a positive `M` and the last positive `r` decimal digits in the exact
externally clocked residual base-16/base-10 carry system for avoiding decimal
digit `2`. It does not rule out arbitrary finite quotients, proves nothing
about the digits of `Real.pi`, does not prove `T37.JMix Real.pi`, and proves
neither canonical V1 nor sibling V3.
-/

namespace Theory.PiDigits.T41

open Theory.PiDigits

noncomputable section

/-- A fixed-width base-`base` representation, most significant digit first. -/
def fixedWord (base length value : ℕ) [NeZero base] : List (Fin base) :=
  (Nat.digitsAppend base length value).reverse.map (Fin.ofNat base)

/-- T37's most-significant-first value is `Nat.ofDigits` of the reversal. -/
theorem wordValue_eq_ofDigits {base : ℕ} (w : List (Fin base)) :
    T37.wordValue w = Nat.ofDigits base (w.map Fin.val).reverse := by
  induction w with
  | nil => rfl
  | cons d w ih =>
      rw [T37.wordValue, List.map_cons, List.reverse_cons,
        Nat.ofDigits_append, ih]
      simp
      ring

theorem fixedWord_length {base length value : ℕ} [NeZero base] (hb : 1 < base)
    (hv : value < base ^ length) :
    (fixedWord base length value).length = length := by
  simp [fixedWord, Nat.length_digitsAppend hb length hv]

theorem fixedWord_map_val {base length value : ℕ} [NeZero base] (hb : 1 < base)
    (hv : value < base ^ length) :
    (fixedWord base length value).map Fin.val =
      (Nat.digitsAppend base length value).reverse := by
  unfold fixedWord
  rw [List.map_map]
  calc
    List.map (Fin.val ∘ Fin.ofNat base)
        (Nat.digitsAppend base length value).reverse =
        List.map id (Nat.digitsAppend base length value).reverse := by
      apply List.map_congr_left
      intro d hd
      rw [List.mem_reverse] at hd
      have hdlt := Nat.lt_of_mem_digitsAppend hb length d hd
      exact Nat.mod_eq_of_lt hdlt
    _ = (Nat.digitsAppend base length value).reverse := by simp

theorem fixedWord_value {base length value : ℕ} [NeZero base] (hb : 1 < base)
    (hv : value < base ^ length) :
    T37.wordValue (fixedWord base length value) = value := by
  rw [wordValue_eq_ofDigits, fixedWord_map_val hb hv, List.reverse_reverse]
  exact (Nat.setInvOn_digitsAppend_ofDigits hb length).2 hv

theorem wordValue_lt_pow {base : ℕ} (hb : 1 < base)
    (w : List (Fin base)) : T37.wordValue w < base ^ w.length := by
  rw [wordValue_eq_ofDigits]
  have h := Nat.ofDigits_lt_base_pow_length (b := base)
    (l := (w.map Fin.val).reverse) hb (by
      intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      exact x.isLt)
  simpa using h

theorem word_eq_of_length_value {base : ℕ} (hb : 1 < base)
    {u v : List (Fin base)} (hlen : u.length = v.length)
    (hvalue : T37.wordValue u = T37.wordValue v) : u = v := by
  rw [wordValue_eq_ofDigits, wordValue_eq_ofDigits] at hvalue
  have hrev : (u.map Fin.val).reverse = (v.map Fin.val).reverse := by
    apply Nat.ofDigits_inj_of_len_eq hb
    · simpa using hlen
    · intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
      exact x.isLt
    · intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
      exact x.isLt
    · exact hvalue
  have hmap : u.map Fin.val = v.map Fin.val := by
    simpa using congrArg List.reverse hrev
  apply List.ext_get
  · exact hlen
  · intro i hiu hiv
    apply Fin.ext
    have h := congrArg (fun l : List ℕ => l[i]?) hmap
    simpa [hiu, hiv] using h

theorem fixedWord_take_value {base length value i : ℕ} [NeZero base] (hb : 1 < base)
    (hv : value < base ^ length) (hi : i ≤ length) :
    T37.wordValue ((fixedWord base length value).take i) =
      value / base ^ (length - i) := by
  let w := fixedWord base length value
  have hlen : w.length = length := fixedWord_length hb hv
  have hdrop : (w.drop i).length = length - i := by simp [hlen]
  have hrest : T37.wordValue (w.drop i) < base ^ (length - i) := by
    simpa [hdrop] using wordValue_lt_pow hb (w.drop i)
  have hfull : value =
      T37.wordValue (w.take i) * base ^ (length - i) +
        T37.wordValue (w.drop i) := by
    calc
      value = T37.wordValue w := (fixedWord_value hb hv).symm
      _ = T37.wordValue (w.take i ++ w.drop i) := by
        rw [List.take_append_drop]
      _ = T37.wordValue (w.take i) * base ^ (length - i) +
          T37.wordValue (w.drop i) := by
        rw [T39.wordValue_append, hdrop]
  change T37.wordValue (w.take i) = _
  rw [hfull, Nat.mul_comm (T37.wordValue (w.take i)),
    Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hrest, add_zero]

/-- The balanced external scale at hexadecimal level `n`. -/
structure ClockContext where
  level : ℕ
  decimalLength : ℕ
  a : ℕ
  b : ℕ

@[ext] theorem ClockContext.ext {c d : ClockContext}
    (hlevel : c.level = d.level)
    (hdecimalLength : c.decimalLength = d.decimalLength)
    (ha : c.a = d.a) (hb : c.b = d.b) : c = d := by
  cases c
  cases d
  simp_all

def balancedContext (n : ℕ) : ClockContext where
  level := n
  decimalLength := T39.decimalLevel n
  a := 5 ^ T39.decimalLevel n
  b := 2 ^ (4 * n - T39.decimalLevel n)

/-- Persistent controller data: exact reduced carry and a decimal suffix. -/
structure ResidualState where
  reducedCarry : ℤ
  suffix : ℕ
deriving DecidableEq

@[ext] theorem ResidualState.ext {q q' : ResidualState}
    (hcarry : q.reducedCarry = q'.reducedCarry)
    (hsuffix : q.suffix = q'.suffix) : q = q' := by
  cases q
  cases q'
  simp_all

/-- One payload packet. Its decimal width is supplied by the external clock. -/
structure Packet where
  width : ℕ
  hex : Fin 16
  decimal : List (Fin 10)
  decimal_length : decimal.length = width

def packetDecimalValue (p : Packet) : ℕ := T37.wordValue p.decimal

def packetOfSymbol (a : T39.Symbol) : Packet where
  width := a.decimal.1.length
  hex := a.hex
  decimal := a.decimal.1
  decimal_length := rfl

def packetsOfSymbols (w : List T39.Symbol) : List Packet := w.map packetOfSymbol

def nextContext (c : ClockContext) (s : ℕ) : ClockContext where
  level := c.level + 1
  decimalLength := c.decimalLength + s
  a := 5 ^ s * c.a
  b := 2 ^ (4 - s) * c.b

def nextResidual (r : ℕ) (c : ClockContext) (q : ResidualState)
    (p : Packet) : ResidualState where
  reducedCarry :=
    (16 * 5 ^ p.width : ℕ) * q.reducedCarry +
      (nextContext c p.width).a * p.hex.val -
      (nextContext c p.width).b * packetDecimalValue p
  suffix := (10 ^ p.width * q.suffix + packetDecimalValue p) % 10 ^ r

def packetAvoidsTwo (p : Packet) : Prop := T39.avoidsTwo p.decimal

def packetClockWidth (p : Packet) : Prop := p.width = 1 ∨ p.width = 2

def RetainedPacket (r : ℕ) (c : ClockContext) (q : ResidualState)
    (p : Packet) : Prop :=
  packetClockWidth p ∧ packetAvoidsTwo p ∧
    -((nextContext c p.width).a : ℤ) <
      (nextResidual r c q p).reducedCarry ∧
    (nextResidual r c q p).reducedCarry <
      ((nextContext c p.width).b : ℤ)

def Accepted : ClockContext → ℕ → ResidualState → List Packet → Prop
  | _, _, _, [] => True
  | c, r, q, p :: w =>
      RetainedPacket r c q p ∧ Accepted (nextContext c p.width) r
        (nextResidual r c q p) w

def advanceContext : ClockContext → List Packet → ClockContext
  | c, [] => c
  | c, p :: w => advanceContext (nextContext c p.width) w

def runResidual (r : ℕ) : ClockContext → ResidualState → List Packet → ResidualState
  | _, q, [] => q
  | c, q, p :: w => runResidual r (nextContext c p.width)
      (nextResidual r c q p) w

def fiveMultiplier : List Packet → ℕ
  | [] => 1
  | p :: w => 5 ^ p.width * fiveMultiplier w

def carryMultiplier : List Packet → ℕ
  | [] => 1
  | p :: w => (16 * 5 ^ p.width) * carryMultiplier w

theorem carryMultiplier_eq (w : List Packet) :
    carryMultiplier w = 16 ^ w.length * fiveMultiplier w := by
  induction w with
  | nil => simp [carryMultiplier, fiveMultiplier]
  | cons p w ih =>
      simp only [carryMultiplier, fiveMultiplier, List.length_cons, pow_succ, ih]
      ring

theorem advanceContext_a (c : ClockContext) (w : List Packet) :
    (advanceContext c w).a = fiveMultiplier w * c.a := by
  induction w generalizing c with
  | nil => simp [advanceContext, fiveMultiplier]
  | cons p w ih =>
      simp only [advanceContext, fiveMultiplier, ih, nextContext]
      ring

theorem runResidual_carry_sub (r : ℕ) (c : ClockContext)
    (q q' : ResidualState) (w : List Packet) :
    (runResidual r c q w).reducedCarry -
        (runResidual r c q' w).reducedCarry =
      (carryMultiplier w : ℤ) * (q.reducedCarry - q'.reducedCarry) := by
  induction w generalizing c q q' with
  | nil => simp [runResidual, carryMultiplier]
  | cons p w ih =>
      simp only [runResidual, carryMultiplier, ih, nextResidual]
      push_cast
      ring

theorem accepted_final_bounds {r : ℕ} {c : ClockContext} {q : ResidualState}
    {w : List Packet} (hw : w ≠ []) (haccepted : Accepted c r q w) :
    -((advanceContext c w).a : ℤ) < (runResidual r c q w).reducedCarry ∧
      (runResidual r c q w).reducedCarry < ((advanceContext c w).b : ℤ) := by
  induction w generalizing c q with
  | nil => exact (hw rfl).elim
  | cons p w ih =>
      rw [Accepted] at haccepted
      cases w with
      | nil => simpa [advanceContext, runResidual, RetainedPacket] using haccepted.1.2.2
      | cons p' w =>
          exact ih (by simp) haccepted.2

/-- The natural finite observation code tested by T41. -/
def quotientCode (M r : ℕ) (q : ResidualState) : ZMod M × Fin (10 ^ r) :=
  (q.reducedCarry, ⟨q.suffix % 10 ^ r, Nat.mod_lt _ (by positivity)⟩)

theorem decimalLevel_le_four_mul (n : ℕ) : T39.decimalLevel n ≤ 4 * n := by
  apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
  calc
    2 ^ T39.decimalLevel n ≤ 10 ^ T39.decimalLevel n :=
      Nat.pow_le_pow_left (by norm_num) _
    _ ≤ 16 ^ n := T39.decimalLevel_lower n
    _ = 2 ^ (4 * n) := by rw [show 16 = 2 ^ 4 by norm_num, ← pow_mul]

theorem ten_pow_factor (n : ℕ) :
    10 ^ T39.decimalLevel n =
      2 ^ T39.decimalLevel n * (balancedContext n).a := by
  simp [balancedContext, ← mul_pow]

theorem sixteen_pow_factor (n : ℕ) :
    16 ^ n = 2 ^ T39.decimalLevel n * (balancedContext n).b := by
  rw [show 16 = 2 ^ 4 by norm_num, ← pow_mul]
  simp only [balancedContext]
  rw [← pow_add, Nat.add_sub_of_le (decimalLevel_le_four_mul n)]

/-- At a balanced level the removed power of two is the full gcd, not merely
a common divisor. -/
theorem balanced_gcd (n : ℕ) :
    Nat.gcd (10 ^ T39.decimalLevel n) (16 ^ n) =
      2 ^ T39.decimalLevel n := by
  rw [ten_pow_factor, sixteen_pow_factor, Nat.gcd_mul_left]
  have hcop : Nat.Coprime (balancedContext n).a (balancedContext n).b := by
    simpa [balancedContext] using
      (by norm_num : Nat.Coprime 5 2).pow (T39.decimalLevel n)
        (4 * n - T39.decimalLevel n)
  rw [hcop.gcd_eq_one, Nat.mul_one]

/-- The signed T37 carry divided by its full common power of two. -/
def reducedCarryAt (n A D : ℕ) : ℤ :=
  ((balancedContext n).a : ℤ) * A - ((balancedContext n).b : ℤ) * D

theorem carry_eq_pow_two_mul_reducedCarryAt (n A D : ℕ) :
    T37.carry n (T39.decimalLevel n) A D =
      (2 ^ T39.decimalLevel n : ℕ) * reducedCarryAt n A D := by
  rw [T37.carry]
  rw [ten_pow_factor, sixteen_pow_factor]
  simp only [reducedCarryAt]
  push_cast
  ring

/-- T37 cylinder compatibility in exact gcd-reduced coordinates. -/
theorem overlap_iff_reducedCarry_bounds (n A D : ℕ) :
    (T37.prefixCylinder 16 n A ∩
      T37.prefixCylinder 10 (T39.decimalLevel n) D).Nonempty ↔
      -((balancedContext n).a : ℤ) < reducedCarryAt n A D ∧
        reducedCarryAt n A D < ((balancedContext n).b : ℤ) := by
  rw [T37.cylinders_overlap_iff_carry_bounds,
    carry_eq_pow_two_mul_reducedCarryAt]
  rw [ten_pow_factor, sixteen_pow_factor]
  push_cast
  let p : ℤ := (2 ^ T39.decimalLevel n : ℕ)
  have hp : 0 < p := by positivity
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · apply lt_of_mul_lt_mul_left (a := p) ?_ hp.le
      simpa [mul_neg] using hl
    · exact lt_of_mul_lt_mul_left hr hp.le
  · rintro ⟨hl, hr⟩
    constructor
    · simpa [mul_neg] using mul_lt_mul_of_pos_left hl hp
    · exact mul_lt_mul_of_pos_left hr hp

def residualOf (r : ℕ) (q : T39.State) : ResidualState where
  reducedCarry := reducedCarryAt q.level (T37.wordValue q.hexPrefix)
    (T37.wordValue q.decimalPrefix)
  suffix := T37.wordValue q.decimalPrefix % 10 ^ r

theorem nextContext_balanced (n : ℕ) :
    nextContext (balancedContext n) (T39.scheduleIncrement n) =
      balancedContext (n + 1) := by
  have hs := T39.scheduleIncrement_one_or_two n
  have hm := decimalLevel_le_four_mul n
  ext <;> simp only [nextContext, balancedContext, T39.decimalLevel_succ]
  · rw [Nat.mul_comm, ← pow_add]
  · rw [← pow_add]
    congr 1
    rcases hs with hs | hs <;> omega

theorem nextResidual_residualOf_appendSymbol (r : ℕ) (q : T39.State)
    (p : Packet) (hwidth : p.width = T39.scheduleIncrement q.level) :
    nextResidual r (balancedContext q.level) (residualOf r q) p =
      residualOf r (T39.appendSymbol q
        { hex := p.hex, decimal := ⟨p.decimal, by
            simpa [p.decimal_length, hwidth] using T39.scheduleIncrement_one_or_two q.level⟩ }) := by
  apply ResidualState.ext
  · simp only [nextResidual, residualOf, T39.appendSymbol, reducedCarryAt,
      packetDecimalValue]
    rw [T39.wordValue_append, T39.wordValue_append]
    simp only [List.length_singleton, pow_one, T37.wordValue]
    rw [p.decimal_length, hwidth, ← nextContext_balanced q.level]
    rcases T39.scheduleIncrement_one_or_two q.level with hs | hs <;>
      simp [nextContext, hs] <;> push_cast <;> ring
  · simp only [nextResidual, residualOf, T39.appendSymbol, packetDecimalValue]
    rw [T39.wordValue_append, p.decimal_length]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mul_comm]

theorem nextResidual_packetOfSymbol (r : ℕ) (q : T39.State) (a : T39.Symbol)
    (hwidth : a.decimal.1.length = T39.scheduleIncrement q.level) :
    nextResidual r (balancedContext q.level) (residualOf r q) (packetOfSymbol a) =
      residualOf r (T39.appendSymbol q a) := by
  simpa [packetOfSymbol] using
    nextResidual_residualOf_appendSymbol r q (packetOfSymbol a) hwidth

theorem retainedPacket_packetOfSymbol_of_retainedStep (r : ℕ) (q : T39.State)
    (a : T39.Symbol) (hstep : T39.RetainedStep q a) :
    RetainedPacket r (balancedContext q.level) (residualOf r q) (packetOfSymbol a) := by
  have hnext := nextResidual_packetOfSymbol r q a hstep.1
  have hbalanced := hstep.2
  have havTarget : T39.avoidsTwo (T39.appendSymbol q a).decimalPrefix :=
    hbalanced.2.2.2.2.1
  have havPacket : packetAvoidsTwo (packetOfSymbol a) := by
    intro hmem
    apply havTarget
    simp only [T39.appendSymbol, packetAvoidsTwo, packetOfSymbol, T39.avoidsTwo] at hmem ⊢
    exact List.mem_append_right _ hmem
  have hclock : packetClockWidth (packetOfSymbol a) := by
    simpa [packetClockWidth, packetOfSymbol, hstep.1] using
      T39.scheduleIncrement_one_or_two q.level
  have hbounds := (overlap_iff_reducedCarry_bounds
    (T39.appendSymbol q a).level
    (T37.wordValue (T39.appendSymbol q a).hexPrefix)
    (T37.wordValue (T39.appendSymbol q a).decimalPrefix)).mp hbalanced.2.2.2.2.2
  have hcontext : nextContext (balancedContext q.level) (packetOfSymbol a).width =
      balancedContext (T39.appendSymbol q a).level := by
    calc
      nextContext (balancedContext q.level) (packetOfSymbol a).width =
          nextContext (balancedContext q.level) (T39.scheduleIncrement q.level) :=
        congrArg (nextContext (balancedContext q.level)) hstep.1
      _ = balancedContext (q.level + 1) := nextContext_balanced q.level
      _ = balancedContext (T39.appendSymbol q a).level := rfl
  refine ⟨hclock, havPacket, ?_⟩
  rw [hcontext, hnext]
  simpa [residualOf] using hbounds

/-- Every T39 legal word is accepted by the exact externally clocked residual system. -/
theorem accepted_packetsOfSymbols_of_legal (r : ℕ) {q : T39.State}
    {w : List T39.Symbol} (hlegal : T39.LegalContinuation q w) :
    Accepted (balancedContext q.level) r (residualOf r q) (packetsOfSymbols w) := by
  induction w generalizing q with
  | nil => simp [Accepted, packetsOfSymbols]
  | cons a w ih =>
      rw [T39.LegalContinuation] at hlegal
      simp only [packetsOfSymbols, List.map_cons, Accepted]
      refine ⟨retainedPacket_packetOfSymbol_of_retainedStep r q a hlegal.1, ?_⟩
      have hc : nextContext (balancedContext q.level) (packetOfSymbol a).width =
          balancedContext (T39.appendSymbol q a).level := by
        calc
          nextContext (balancedContext q.level) (packetOfSymbol a).width =
              nextContext (balancedContext q.level) (T39.scheduleIncrement q.level) :=
            congrArg (nextContext (balancedContext q.level)) hlegal.1.1
          _ = balancedContext (q.level + 1) := nextContext_balanced q.level
          _ = balancedContext (T39.appendSymbol q a).level := rfl
      rw [hc, nextResidual_packetOfSymbol r q a hlegal.1.1]
      exact ih hlegal.2

theorem advanceContext_packetsOfSymbols_of_legal {q : T39.State}
    {w : List T39.Symbol} (hlegal : T39.LegalContinuation q w) :
    advanceContext (balancedContext q.level) (packetsOfSymbols w) =
      balancedContext (q.level + w.length) := by
  induction w generalizing q with
  | nil => simp [advanceContext, packetsOfSymbols]
  | cons a w ih =>
      rw [T39.LegalContinuation] at hlegal
      simp only [packetsOfSymbols, List.map_cons, advanceContext, List.length_cons]
      have hc : nextContext (balancedContext q.level) (packetOfSymbol a).width =
          balancedContext (T39.appendSymbol q a).level := by
        calc
          nextContext (balancedContext q.level) (packetOfSymbol a).width =
              nextContext (balancedContext q.level) (T39.scheduleIncrement q.level) :=
            congrArg (nextContext (balancedContext q.level)) hlegal.1.1
          _ = balancedContext (q.level + 1) := nextContext_balanced q.level
          _ = balancedContext (T39.appendSymbol q a).level := rfl
      rw [hc]
      have hiw := ih hlegal.2
      simp only [packetsOfSymbols] at hiw
      rw [hiw]
      congr 1
      simp [T39.appendSymbol]
      omega

theorem balancedContext_b_lt_ten_a (n : ℕ) :
    (balancedContext n).b < 10 * (balancedContext n).a := by
  have h := T39.decimalLevel_upper n
  rw [sixteen_pow_factor, pow_succ, ten_pow_factor] at h
  have hp : 0 < 2 ^ T39.decimalLevel n := by positivity
  apply (Nat.mul_lt_mul_left hp).mp
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem eleven_mul_lt_sixteen_pow {a : ℕ} (ha : 0 < a) : 11 * a < 16 ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      calc
        11 * (k + 1 + 1) ≤ 16 * (11 * (k + 1)) := by omega
        _ < 16 * 16 ^ (k + 1) :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 16)).2 (ih (by omega))
        _ = 16 ^ (k + 1) * 16 := by ring

/-- A decimal word with one `1`, followed by `k` zeroes. -/
def oneHotWord (length k : ℕ) : List (Fin 10) :=
  List.replicate (length - (k + 1)) 0 ++ [1] ++ List.replicate k 0

theorem oneHotWord_length {length k : ℕ} (hk : k < length) :
    (oneHotWord length k).length = length := by
  simp [oneHotWord]
  omega

theorem oneHotWord_value {length k : ℕ} (hk : k < length) :
    T37.wordValue (oneHotWord length k) = 10 ^ k := by
  simp [oneHotWord, T39.wordValue_append, T37.wordValue,
    T39.wordValue_replicate_zero]

theorem oneHotWord_avoidsTwo (length k : ℕ) :
    T39.avoidsTwo (oneHotWord length k) := by
  simp [T39.avoidsTwo, oneHotWord]

def witnessScale (M r : ℕ) : ℕ := M + r + 1
def witnessLevel (M r : ℕ) : ℕ := 2 * witnessScale M r
def witnessDecimalLength (M r : ℕ) : ℕ := T39.decimalLevel (witnessLevel M r)
def witnessDecimalValue (r j : ℕ) : ℕ := 10 ^ (r + j)

def rationalHexValue (n D : ℕ) : ℕ :=
  (16 ^ n * D) / 10 ^ T39.decimalLevel n

def rationalState (n D : ℕ) : T39.State where
  level := n
  hexPrefix := fixedWord 16 n (rationalHexValue n D)
  decimalPrefix := fixedWord 10 (T39.decimalLevel n) D

def prefixState (q : T39.State) (i : ℕ) : T39.State where
  level := i
  hexPrefix := q.hexPrefix.take i
  decimalPrefix := q.decimalPrefix.take (T39.decimalLevel i)

theorem decimalLevel_mono_of_le {i n : ℕ} (hin : i ≤ n) :
    T39.decimalLevel i ≤ T39.decimalLevel n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hin
  rw [T39.decimalLevel_add_eq]
  omega

theorem rationalHexValue_lt_pow {n D : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n) : rationalHexValue n D < 16 ^ n := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  dsimp [rationalHexValue]
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 16 ^ n)).2 hD

theorem fixedWord_oneHot {length k : ℕ} (hk : k < length) :
    fixedWord 10 length (10 ^ k) = oneHotWord length k := by
  apply word_eq_of_length_value (by norm_num)
  · rw [fixedWord_length (by norm_num) (Nat.pow_lt_pow_right (by norm_num) hk),
      oneHotWord_length hk]
  · rw [fixedWord_value (by norm_num) (Nat.pow_lt_pow_right (by norm_num) hk),
      oneHotWord_value hk]

/-- A floor-selected prefix cylinder contains the represented rational point. -/
theorem natDiv_mem_prefixCylinder (base length N Q : ℕ) (hbase : 0 < base)
    (hQ : 0 < Q) :
    (N : ℝ) / Q ∈ T37.prefixCylinder base length ((base ^ length * N) / Q) := by
  rw [T37.prefixCylinder, Set.mem_Ico]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hQ)]
    have h := Nat.div_mul_le_self (base ^ length * N) Q
    exact_mod_cast (by simpa [Nat.mul_comm] using h)
  · rw [div_lt_div_iff₀ (by exact_mod_cast hQ) (by positivity)]
    have h := Nat.lt_mul_div_succ (base ^ length * N) hQ
    exact_mod_cast (by simpa [Nat.mul_comm, Nat.mul_left_comm] using h)

theorem rationalHexValue_div_pow {n D i : ℕ} (hin : i ≤ n) :
    rationalHexValue n D / 16 ^ (n - i) =
      (16 ^ i * D) / 10 ^ T39.decimalLevel n := by
  rw [rationalHexValue, Nat.div_div_eq_div_mul]
  conv_lhs =>
    congr
    · rw [show n = i + (n - i) by omega, pow_add]
    · skip
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_div_mul_right (16 ^ i * D) (10 ^ T39.decimalLevel n)
      (by positivity : 0 < 16 ^ (n - i))

theorem decimal_div_pow_eq_scaled_div {m k D : ℕ} (hkm : k ≤ m) :
    D / 10 ^ (m - k) = (10 ^ k * D) / 10 ^ m := by
  conv_rhs =>
    congr
    · skip
    · rw [show m = k + (m - k) by omega, pow_add]
  symm
  exact Nat.mul_div_mul_left D (10 ^ (m - k)) (by positivity)

theorem rationalState_hexPrefix_value {n D i : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n) (hin : i ≤ n) :
    T37.wordValue ((rationalState n D).hexPrefix.take i) =
      (16 ^ i * D) / 10 ^ T39.decimalLevel n := by
  change T37.wordValue ((fixedWord 16 n (rationalHexValue n D)).take i) = _
  rw [fixedWord_take_value (by norm_num) (rationalHexValue_lt_pow hD) hin]
  exact rationalHexValue_div_pow hin

theorem rationalState_decimalPrefix_value {n D i : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n) (hin : i ≤ n) :
    T37.wordValue
        ((rationalState n D).decimalPrefix.take (T39.decimalLevel i)) =
      (10 ^ T39.decimalLevel i * D) / 10 ^ T39.decimalLevel n := by
  have hm := decimalLevel_mono_of_le hin
  change T37.wordValue
      ((fixedWord 10 (T39.decimalLevel n) D).take (T39.decimalLevel i)) = _
  rw [fixedWord_take_value (by norm_num) hD hm]
  exact decimal_div_pow_eq_scaled_div hm

theorem rationalState_all_prefixes_balanced {n D : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n)
    (havoid : T39.avoidsTwo (fixedWord 10 (T39.decimalLevel n) D))
    {i : ℕ} (hin : i ≤ n) : T39.Balanced (prefixState (rationalState n D) i) := by
  have hA := rationalHexValue_lt_pow hD
  have hm := decimalLevel_mono_of_le hin
  have hhexlen : (rationalState n D).hexPrefix.length = n :=
    fixedWord_length (by norm_num) hA
  have hdeclen : (rationalState n D).decimalPrefix.length = T39.decimalLevel n :=
    fixedWord_length (by norm_num) hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [prefixState, hhexlen, hin]
  · simp [prefixState, hdeclen, hm]
  · have h := wordValue_lt_pow (by norm_num)
      ((rationalState n D).hexPrefix.take i)
    simpa [T37.ValidPrefix, prefixState, hhexlen, hin] using h
  · have h := wordValue_lt_pow (by norm_num)
      ((rationalState n D).decimalPrefix.take (T39.decimalLevel i))
    simpa [T37.ValidPrefix, prefixState, hdeclen, hm] using h
  · intro hmem
    apply havoid
    exact List.mem_of_mem_take hmem
  · refine ⟨(D : ℝ) / 10 ^ T39.decimalLevel n, ?_, ?_⟩
    · simp only [prefixState]
      rw [rationalState_hexPrefix_value hD hin]
      simpa using natDiv_mem_prefixCylinder 16 i D (10 ^ T39.decimalLevel n)
        (by norm_num) (by positivity)
    · simp only [prefixState]
      rw [rationalState_decimalPrefix_value hD hin]
      simpa using natDiv_mem_prefixCylinder 10 (T39.decimalLevel i) D
        (10 ^ T39.decimalLevel n) (by norm_num) (by positivity)

def endpointSymbol (q : T39.State) (i : ℕ) (hi : i < q.level)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level) : T39.Symbol where
  hex := q.hexPrefix.get ⟨i, by simpa [hhex] using hi⟩
  decimal := ⟨(q.decimalPrefix.drop (T39.decimalLevel i)).take
      (T39.scheduleIncrement i), by
    have hnext : i + 1 ≤ q.level := by omega
    have hm := decimalLevel_mono_of_le hnext
    have hsucc := T39.decimalLevel_succ i
    rcases T39.scheduleIncrement_one_or_two i with hs | hs <;>
      simp [List.length_take, List.length_drop, hdecimal, hs] <;> omega⟩

theorem append_prefixState_endpointSymbol (q : T39.State) (i : ℕ)
    (hi : i < q.level) (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level) :
    T39.appendSymbol (prefixState q i) (endpointSymbol q i hi hhex hdecimal) =
      prefixState q (i + 1) := by
  apply T39.state_ext
  · rfl
  · simp only [T39.appendSymbol, prefixState, endpointSymbol]
    rw [List.take_succ]
    simp [List.getElem?_eq_getElem, hi, hhex]
  · simp only [T39.appendSymbol, prefixState, endpointSymbol]
    rw [← List.take_add, ← T39.decimalLevel_succ]

theorem legalContinuation_append_one {q : T39.State} {w : List T39.Symbol}
    {a : T39.Symbol} (hw : T39.LegalContinuation q w)
    (ha : T39.RetainedStep (T39.run q w) a) :
    T39.LegalContinuation q (w ++ [a]) := by
  induction w generalizing q with
  | nil =>
      simp only [T39.run, List.foldl_nil] at ha
      simpa [T39.LegalContinuation] using ⟨ha, ha.2⟩
  | cons b w ih =>
      rw [T39.LegalContinuation] at hw
      simp only [T39.run, List.foldl_cons] at ha
      rw [List.cons_append, T39.LegalContinuation]
      exact ⟨hw.1, ih hw.2 ha⟩

theorem run_append_one (q : T39.State) (w : List T39.Symbol) (a : T39.Symbol) :
    T39.run q (w ++ [a]) = T39.appendSymbol (T39.run q w) a := by
  simp [T39.run, List.foldl_append]

theorem reachable_step {q : T39.State} (hq : T39.Reachable q)
    {a : T39.Symbol} (ha : T39.RetainedStep q a) :
    T39.Reachable (T39.appendSymbol q a) := by
  obtain ⟨w, hw, hr⟩ := hq
  refine ⟨w ++ [a], legalContinuation_append_one hw ?_, ?_⟩
  · simpa [hr] using ha
  · rw [run_append_one, hr]

def endpointContinuation (q : T39.State)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level) :
    (start t : ℕ) → start + t ≤ q.level → List T39.Symbol
  | _, 0, _ => []
  | start, t + 1, hle =>
      endpointSymbol q start (by omega) hhex hdecimal ::
        endpointContinuation q hhex hdecimal (start + 1) t (by omega)

theorem endpointContinuation_length (q : T39.State)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level)
    (start t : ℕ) (hle : start + t ≤ q.level) :
    (endpointContinuation q hhex hdecimal start t hle).length = t := by
  induction t generalizing start with
  | zero => rfl
  | succ t ih =>
      simp only [endpointContinuation, List.length_cons]
      rw [ih]

theorem legal_endpointContinuation (q : T39.State)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level)
    (hbalanced : ∀ i ≤ q.level, T39.Balanced (prefixState q i))
    (start t : ℕ) (hle : start + t ≤ q.level) :
    T39.LegalContinuation (prefixState q start)
      (endpointContinuation q hhex hdecimal start t hle) := by
  induction t generalizing start with
  | zero =>
      simp only [endpointContinuation, T39.LegalContinuation]
      exact hbalanced start (by omega)
  | succ t ih =>
      simp only [endpointContinuation, T39.LegalContinuation]
      let a := endpointSymbol q start (by omega) hhex hdecimal
      have happend := append_prefixState_endpointSymbol q start (by omega) hhex hdecimal
      constructor
      · constructor
        · dsimp [a, endpointSymbol, prefixState]
          simp only [List.length_take, List.length_drop]
          rw [Nat.min_eq_left]
          have hm := decimalLevel_mono_of_le
            (show start + 1 ≤ q.level by omega)
          rw [hdecimal]
          have hs := T39.decimalLevel_succ start
          omega
        · rw [happend]
          exact hbalanced (start + 1) (by omega)
      · rw [happend]
        exact ih (start + 1) (by omega)

/-- Slicing any endpoint whose scheduled prefixes are balanced gives a T39 path. -/
theorem reachable_of_all_prefixes_balanced (q : T39.State)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level)
    (hbalanced : ∀ i ≤ q.level, T39.Balanced (prefixState q i)) :
    T39.Reachable q := by
  induction hlevel : q.level generalizing q with
  | zero =>
      have hq : q = T39.zeroState 0 := by
        apply T39.state_ext
        · simpa using hlevel
        · apply List.eq_nil_of_length_eq_zero
          omega
        · apply List.eq_nil_of_length_eq_zero
          simpa [hlevel, T39.decimalLevel] using hdecimal
      rw [hq]
      exact T39.zeroFamily_reachable 0
  | succ i ih =>
      have hi : i < q.level := by omega
      let qprev := prefixState q i
      let a := endpointSymbol q i hi hhex hdecimal
      have happend : T39.appendSymbol qprev a = prefixState q (i + 1) :=
        append_prefixState_endpointSymbol q i hi hhex hdecimal
      have hqeq : prefixState q (i + 1) = q := by
        apply T39.state_ext
        · simpa using hlevel.symm
        · simp [prefixState, hhex, hlevel]
        · have hm : T39.decimalLevel (i + 1) = T39.decimalLevel q.level := by
            rw [hlevel]
          simp [prefixState, hdecimal, hm]
      have hprevhex : qprev.hexPrefix.length = qprev.level := by
        simp [qprev, prefixState, hhex, hi.le]
      have hprevdec : qprev.decimalPrefix.length = T39.decimalLevel qprev.level := by
        have hm := decimalLevel_mono_of_le hi.le
        simp [qprev, prefixState, hdecimal, hm]
      have hprevbalanced : ∀ k ≤ qprev.level, T39.Balanced (prefixState qprev k) := by
        intro k hk
        have hki : k ≤ i := by simpa [qprev, prefixState] using hk
        have heq : prefixState qprev k = prefixState q k := by
          apply T39.state_ext <;> simp [qprev, prefixState, List.take_take, hki,
            decimalLevel_mono_of_le hki]
        rw [heq]
        exact hbalanced k (hki.trans hi.le)
      have hreach : T39.Reachable qprev :=
        ih qprev hprevhex hprevdec hprevbalanced rfl
      have hstep : T39.RetainedStep qprev a := by
        constructor
        · dsimp [a, qprev, prefixState, endpointSymbol]
          simp only [List.length_take, List.length_drop]
          change min (T39.scheduleIncrement i)
              (q.decimalPrefix.length - T39.decimalLevel i) =
              T39.scheduleIncrement i
          rw [Nat.min_eq_left]
          have hm := decimalLevel_mono_of_le (show i + 1 ≤ q.level by omega)
          rw [hdecimal]
          have hs := T39.decimalLevel_succ i
          omega
        · rw [happend]
          exact hbalanced (i + 1) (by omega)
      rw [← hqeq, ← happend]
      exact reachable_step hreach hstep

def witnessState (M r : ℕ) (j : Fin (M + 1)) : T39.State where
  level := witnessLevel M r
  hexPrefix := fixedWord 16 (witnessLevel M r)
    (rationalHexValue (witnessLevel M r) (witnessDecimalValue r j))
  decimalPrefix := oneHotWord (witnessDecimalLength M r) (r + j)

theorem decimalLevel_self_le (n : ℕ) : n ≤ T39.decimalLevel n := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 10)
  exact Nat.pow_le_pow_left (by norm_num) n

theorem witness_digit_position_lt {M r : ℕ} (j : Fin (M + 1)) :
    r + j < witnessDecimalLength M r := by
  have hlevel := decimalLevel_self_le (witnessLevel M r)
  have hj : r + (j : ℕ) < witnessLevel M r := by
    simp only [witnessLevel, witnessScale]
    omega
  exact hj.trans_le hlevel

theorem witnessState_eq_rationalState {M r : ℕ} (j : Fin (M + 1)) :
    witnessState M r j =
      rationalState (witnessLevel M r) (witnessDecimalValue r j) := by
  apply T39.state_ext
  · rfl
  · rfl
  · simpa only [witnessState, rationalState, witnessDecimalLength,
      witnessDecimalValue] using
      (fixedWord_oneHot (witness_digit_position_lt j)).symm

theorem witnessDecimalValue_lt_fiveScale {M r : ℕ} (j : Fin (M + 1)) :
    witnessDecimalValue r j < (balancedContext (witnessLevel M r)).a := by
  let N := witnessScale M r
  have hN : 0 < N := by simp [N, witnessScale]
  have hjexp : r + (j : ℕ) < N := by
    dsimp [N, witnessScale]
    omega
  have hm : 2 * N ≤ T39.decimalLevel (witnessLevel M r) := by
    simpa [witnessLevel, N] using decimalLevel_self_le (witnessLevel M r)
  calc
    witnessDecimalValue r j = 10 ^ (r + (j : ℕ)) := rfl
    _ < 10 ^ N := Nat.pow_lt_pow_right (by norm_num) hjexp
    _ < 25 ^ N := Nat.pow_lt_pow_left (by norm_num) hN.ne'
    _ = 5 ^ (2 * N) := by rw [show 25 = 5 ^ 2 by norm_num, ← pow_mul]
    _ ≤ 5 ^ T39.decimalLevel (witnessLevel M r) :=
      Nat.pow_le_pow_right (by norm_num) hm
    _ = (balancedContext (witnessLevel M r)).a := rfl

def extensionValue (n t D : ℕ) : ℕ := D * 10 ^ T39.incrementSum n t

theorem extensionValue_lt_pow {n t D : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n) :
    extensionValue n t D < 10 ^ T39.decimalLevel (n + t) := by
  rw [T39.decimalLevel_add_eq, pow_add]
  exact (Nat.mul_lt_mul_right (by positivity : 0 < 10 ^ T39.incrementSum n t)).2 hD

theorem rationalExtension_prefixState {n t D : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n) :
    prefixState (rationalState (n + t) (extensionValue n t D)) n =
      rationalState n D := by
  have hExt := extensionValue_lt_pow (t := t) hD
  have hn : n ≤ n + t := Nat.le_add_right n t
  apply T39.state_ext
  · rfl
  · simp only [prefixState]
    change (fixedWord 16 (n + t)
      (rationalHexValue (n + t) (extensionValue n t D))).take n =
        fixedWord 16 n (rationalHexValue n D)
    apply word_eq_of_length_value (by norm_num)
    · rw [List.length_take_of_le]
      · exact (fixedWord_length (by norm_num) (rationalHexValue_lt_pow hD)).symm
      · rw [fixedWord_length (by norm_num) (rationalHexValue_lt_pow hExt)]
        omega
    · rw [fixedWord_take_value (by norm_num) (rationalHexValue_lt_pow hExt) hn,
        rationalHexValue_div_pow hn,
        fixedWord_value (by norm_num) (rationalHexValue_lt_pow hD)]
      rw [T39.decimalLevel_add_eq]
      simp only [extensionValue, rationalHexValue]
      simpa [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_div_mul_right (16 ^ n * D) (10 ^ T39.decimalLevel n)
          (by positivity : 0 < 10 ^ T39.incrementSum n t)
  · simp only [prefixState]
    change (fixedWord 10 (T39.decimalLevel (n + t))
      (extensionValue n t D)).take (T39.decimalLevel n) =
        fixedWord 10 (T39.decimalLevel n) D
    apply word_eq_of_length_value (by norm_num)
    · rw [List.length_take_of_le]
      · exact (fixedWord_length (by norm_num) hD).symm
      · rw [fixedWord_length (by norm_num) hExt]
        exact decimalLevel_mono_of_le hn
    · have hm := decimalLevel_mono_of_le hn
      rw [fixedWord_take_value (by norm_num) hExt hm,
        decimal_div_pow_eq_scaled_div hm,
        fixedWord_value (by norm_num) hD, T39.decimalLevel_add_eq]
      simp [extensionValue, pow_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]

theorem rationalHexValue_eq_scale_div (n D : ℕ) :
    rationalHexValue n D = (balancedContext n).b * D / (balancedContext n).a := by
  rw [rationalHexValue, ten_pow_factor, sixteen_pow_factor]
  simp only [Nat.mul_assoc]
  exact Nat.mul_div_mul_left ((balancedContext n).b * D) (balancedContext n).a
    (by positivity)

theorem reducedCarryAt_rationalHexValue (n D : ℕ) :
    reducedCarryAt n (rationalHexValue n D) D =
      -(((balancedContext n).b * D % (balancedContext n).a : ℕ) : ℤ) := by
  rw [rationalHexValue_eq_scale_div]
  have hdiv := Nat.mod_add_div ((balancedContext n).b * D) (balancedContext n).a
  simp only [reducedCarryAt]
  push_cast at hdiv ⊢
  nlinarith

theorem witness_reducedCarry_eq {M r : ℕ} (j : Fin (M + 1)) :
    (residualOf r (witnessState M r j)).reducedCarry =
      -(((balancedContext (witnessLevel M r)).b * witnessDecimalValue r j %
          (balancedContext (witnessLevel M r)).a : ℕ) : ℤ) := by
  have hD : witnessDecimalValue r j <
      10 ^ T39.decimalLevel (witnessLevel M r) :=
    Nat.pow_lt_pow_right (by norm_num) (witness_digit_position_lt j)
  rw [witnessState_eq_rationalState]
  simp only [residualOf, rationalState]
  rw [fixedWord_value (by norm_num)
      (rationalHexValue_lt_pow hD), fixedWord_value (by norm_num) hD]
  exact reducedCarryAt_rationalHexValue _ _

theorem witness_suffix_eq_zero {M r : ℕ} (j : Fin (M + 1)) :
    (residualOf r (witnessState M r j)).suffix = 0 := by
  have hD : witnessDecimalValue r j <
      10 ^ T39.decimalLevel (witnessLevel M r) :=
    Nat.pow_lt_pow_right (by norm_num) (witness_digit_position_lt j)
  rw [witnessState_eq_rationalState]
  simp only [residualOf, rationalState]
  rw [fixedWord_value (by norm_num) hD]
  apply Nat.mod_eq_zero_of_dvd
  exact pow_dvd_pow 10 (Nat.le_add_right r j)

theorem witness_reducedCarry_injective {M r : ℕ} :
    Function.Injective (fun j : Fin (M + 1) =>
      (residualOf r (witnessState M r j)).reducedCarry) := by
  intro u v huv
  change (residualOf r (witnessState M r u)).reducedCarry =
    (residualOf r (witnessState M r v)).reducedCarry at huv
  rw [witness_reducedCarry_eq, witness_reducedCarry_eq] at huv
  have hrem :
      (balancedContext (witnessLevel M r)).b * witnessDecimalValue r u %
          (balancedContext (witnessLevel M r)).a =
        (balancedContext (witnessLevel M r)).b * witnessDecimalValue r v %
          (balancedContext (witnessLevel M r)).a := by
    exact_mod_cast neg_inj.mp huv
  have hcop : Nat.gcd (balancedContext (witnessLevel M r)).a
      (balancedContext (witnessLevel M r)).b = 1 := by
    simpa [balancedContext] using
      ((by norm_num : Nat.Coprime 5 2).pow
        (T39.decimalLevel (witnessLevel M r))
        (4 * witnessLevel M r - T39.decimalLevel (witnessLevel M r))).gcd_eq_one
  have hmul :
      (balancedContext (witnessLevel M r)).b * witnessDecimalValue r u ≡
        (balancedContext (witnessLevel M r)).b * witnessDecimalValue r v
          [MOD (balancedContext (witnessLevel M r)).a] := hrem
  have hDmod := hmul.cancel_left_of_coprime hcop
  have hD : witnessDecimalValue r u = witnessDecimalValue r v :=
    hDmod.eq_of_lt_of_lt (witnessDecimalValue_lt_fiveScale u)
      (witnessDecimalValue_lt_fiveScale v)
  have hexp : r + (u : ℕ) = r + (v : ℕ) :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 10) hD
  apply Fin.ext
  omega

def separationSteps (M r : ℕ) : ℕ :=
  (balancedContext (witnessLevel M r)).a

theorem separationSteps_pos (M r : ℕ) : 0 < separationSteps M r := by
  simp [separationSteps, balancedContext]

def extendedWitnessState (M r : ℕ) (j : Fin (M + 1)) : T39.State :=
  rationalState (witnessLevel M r + separationSteps M r)
    (extensionValue (witnessLevel M r) (separationSteps M r)
      (witnessDecimalValue r j))

theorem extendedWitnessValue_lt_pow {M r : ℕ} (j : Fin (M + 1)) :
    extensionValue (witnessLevel M r) (separationSteps M r)
        (witnessDecimalValue r j) <
      10 ^ T39.decimalLevel (witnessLevel M r + separationSteps M r) := by
  apply extensionValue_lt_pow
  exact Nat.pow_lt_pow_right (by norm_num) (witness_digit_position_lt j)

theorem extendedWitness_hex_length {M r : ℕ} (j : Fin (M + 1)) :
    (extendedWitnessState M r j).hexPrefix.length =
      (extendedWitnessState M r j).level := by
  exact fixedWord_length (by norm_num)
    (rationalHexValue_lt_pow (extendedWitnessValue_lt_pow j))

theorem extendedWitness_decimal_length {M r : ℕ} (j : Fin (M + 1)) :
    (extendedWitnessState M r j).decimalPrefix.length =
      T39.decimalLevel (extendedWitnessState M r j).level := by
  exact fixedWord_length (by norm_num) (extendedWitnessValue_lt_pow j)

def distinguishingSymbols (M r : ℕ) (j : Fin (M + 1)) : List T39.Symbol :=
  endpointContinuation (extendedWitnessState M r j)
    (extendedWitness_hex_length j) (extendedWitness_decimal_length j)
    (witnessLevel M r) (separationSteps M r) (by rfl)

/-- The explicit common externally clocked continuation used for separation. -/
def distinguishingContinuation (M r : ℕ) (j : Fin (M + 1)) : List Packet :=
  packetsOfSymbols (distinguishingSymbols M r j)

theorem distinguishingSymbols_length (M r : ℕ) (j : Fin (M + 1)) :
    (distinguishingSymbols M r j).length = separationSteps M r := by
  apply endpointContinuation_length

theorem extendedWitness_avoidsTwo {M r : ℕ} (j : Fin (M + 1)) :
    T39.avoidsTwo (extendedWitnessState M r j).decimalPrefix := by
  let S := T39.incrementSum (witnessLevel M r) (separationSteps M r)
  have hk : r + (j : ℕ) + S <
      T39.decimalLevel (witnessLevel M r + separationSteps M r) := by
    rw [T39.decimalLevel_add_eq]
    have h := witness_digit_position_lt (M := M) (r := r) j
    simp only [witnessDecimalLength] at h
    dsimp [S]
    omega
  have hvalue : extensionValue (witnessLevel M r) (separationSteps M r)
      (witnessDecimalValue r j) = 10 ^ (r + (j : ℕ) + S) := by
    simp [extensionValue, witnessDecimalValue, S, pow_add]
  simp only [extendedWitnessState, rationalState]
  rw [hvalue, fixedWord_oneHot hk]
  exact oneHotWord_avoidsTwo _ _

set_option maxHeartbeats 800000 in
theorem distinguishingSymbols_legal {M r : ℕ} (j : Fin (M + 1)) :
    T39.LegalContinuation (witnessState M r j) (distinguishingSymbols M r j) := by
  let qf := extendedWitnessState M r j
  have hbalanced : ∀ i ≤ qf.level, T39.Balanced (prefixState qf i) := by
    intro i hi
    change i ≤ witnessLevel M r + separationSteps M r at hi
    change T39.Balanced (prefixState
      (rationalState (witnessLevel M r + separationSteps M r)
        (extensionValue (witnessLevel M r) (separationSteps M r)
          (witnessDecimalValue r j))) i)
    exact rationalState_all_prefixes_balanced (extendedWitnessValue_lt_pow j)
      (extendedWitness_avoidsTwo j) hi
  have hlegal := legal_endpointContinuation qf
    (extendedWitness_hex_length j) (extendedWitness_decimal_length j)
    hbalanced (witnessLevel M r) (separationSteps M r) (by rfl)
  have hprefix : prefixState qf (witnessLevel M r) = witnessState M r j := by
    change prefixState
      (rationalState (witnessLevel M r + separationSteps M r)
        (extensionValue (witnessLevel M r) (separationSteps M r)
          (witnessDecimalValue r j))) (witnessLevel M r) = _
    calc
      _ = rationalState (witnessLevel M r) (witnessDecimalValue r j) :=
        rationalExtension_prefixState
          (Nat.pow_lt_pow_right (by norm_num)
            (witness_digit_position_lt (M := M) (r := r) j))
      _ = witnessState M r j := (witnessState_eq_rationalState j).symm
  rw [hprefix] at hlegal
  exact hlegal

/-- The named one-sided acceptance theorem for the explicit continuation. -/
theorem distinguishingContinuation_accepted {M r : ℕ} (j : Fin (M + 1)) :
    Accepted (balancedContext (witnessLevel M r)) r
      (residualOf r (witnessState M r j)) (distinguishingContinuation M r j) := by
  exact accepted_packetsOfSymbols_of_legal r (distinguishingSymbols_legal j)

theorem distinguishingContinuation_length (M r : ℕ) (j : Fin (M + 1)) :
    (distinguishingContinuation M r j).length = separationSteps M r := by
  simp [distinguishingContinuation, packetsOfSymbols, distinguishingSymbols_length]

theorem distinguishingContinuation_ne_nil (M r : ℕ) (j : Fin (M + 1)) :
    distinguishingContinuation M r j ≠ [] := by
  intro hnil
  have hlen := distinguishingContinuation_length M r j
  rw [hnil] at hlen
  simp at hlen
  exact (separationSteps_pos M r).ne' hlen.symm

theorem advanceContext_distinguishingContinuation (M r : ℕ) (j : Fin (M + 1)) :
    advanceContext (balancedContext (witnessLevel M r))
        (distinguishingContinuation M r j) =
      balancedContext (witnessLevel M r + separationSteps M r) := by
  have h := advanceContext_packetsOfSymbols_of_legal
    (distinguishingSymbols_legal (M := M) (r := r) j)
  rw [distinguishingSymbols_length] at h
  exact h

theorem fiveMultiplier_pos (w : List Packet) : 0 < fiveMultiplier w := by
  induction w with
  | nil => simp [fiveMultiplier]
  | cons p w ih => simp [fiveMultiplier, ih]

/-- The explicit continuation is rejected from every other one-hot witness. -/
theorem distinguishingContinuation_rejected_of_ne {M r : ℕ}
    {u v : Fin (M + 1)} (huv : u ≠ v) :
    ¬ Accepted (balancedContext (witnessLevel M r)) r
      (residualOf r (witnessState M r v)) (distinguishingContinuation M r u) := by
  intro hvAccepted
  let c := balancedContext (witnessLevel M r)
  let qu := residualOf r (witnessState M r u)
  let qv := residualOf r (witnessState M r v)
  let w := distinguishingContinuation M r u
  let xu := (runResidual r c qu w).reducedCarry
  let xv := (runResidual r c qv w).reducedCarry
  let cf := advanceContext c w
  have hwne : w ≠ [] := distinguishingContinuation_ne_nil M r u
  have huAccepted : Accepted c r qu w := distinguishingContinuation_accepted u
  have hbu : -((cf.a : ℕ) : ℤ) < xu ∧ xu < ((cf.b : ℕ) : ℤ) :=
    accepted_final_bounds hwne huAccepted
  have hbv : -((cf.a : ℕ) : ℤ) < xv ∧ xv < ((cf.b : ℕ) : ℤ) :=
    accepted_final_bounds hwne hvAccepted
  have hctx : cf = balancedContext (witnessLevel M r + separationSteps M r) :=
    advanceContext_distinguishingContinuation M r u
  have hbten : cf.b < 10 * cf.a := by
    rw [hctx]
    exact balancedContext_b_lt_ten_a _
  have habsUpper : |xu - xv| < (11 * cf.a : ℕ) := by
    have hab : |xu - xv| < ((cf.a + cf.b : ℕ) : ℤ) := by
      rw [abs_lt]
      push_cast
      constructor <;> omega
    exact_mod_cast (show |xu - xv| < (11 * cf.a : ℕ) by
      exact_mod_cast (by push_cast at hab; omega : |xu - xv| < ((11 * cf.a : ℕ) : ℤ)))
  have hcarryNe : qu.reducedCarry ≠ qv.reducedCarry := by
    intro hcarry
    exact huv (witness_reducedCarry_injective hcarry)
  have hdeltaPos : (0 : ℤ) < |qu.reducedCarry - qv.reducedCarry| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hcarryNe)
  have hsub := runResidual_carry_sub r c qu qv w
  have habsEq : |xu - xv| =
      (carryMultiplier w : ℤ) * |qu.reducedCarry - qv.reducedCarry| := by
    rw [show xu - xv = (carryMultiplier w : ℤ) *
      (qu.reducedCarry - qv.reducedCarry) from hsub]
    rw [abs_mul]
    simp
  have hlower : (carryMultiplier w : ℤ) ≤ |xu - xv| := by
    rw [habsEq]
    have hm : (0 : ℤ) ≤ carryMultiplier w := by positivity
    nlinarith
  have hproduct : carryMultiplier w < 11 * cf.a := by
    exact_mod_cast lt_of_le_of_lt hlower habsUpper
  have hwlen : w.length = separationSteps M r :=
    distinguishingContinuation_length M r u
  rw [carryMultiplier_eq, hwlen, advanceContext_a] at hproduct
  have hsmall : 16 ^ separationSteps M r < 11 * c.a := by
    apply (Nat.mul_lt_mul_right (fiveMultiplier_pos w)).mp
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hproduct
  have hlarge := eleven_mul_lt_sixteen_pow (separationSteps_pos M r)
  have hca : c.a = separationSteps M r := rfl
  rw [hca] at hsmall
  omega

theorem witnessState_reachable {M r : ℕ} (j : Fin (M + 1)) :
    T39.Reachable (witnessState M r j) := by
  rw [witnessState_eq_rationalState]
  have hD : witnessDecimalValue r j <
      10 ^ T39.decimalLevel (witnessLevel M r) :=
    Nat.pow_lt_pow_right (by norm_num) (witness_digit_position_lt j)
  apply reachable_of_all_prefixes_balanced
  · exact fixedWord_length (by norm_num) (rationalHexValue_lt_pow hD)
  · exact fixedWord_length (by norm_num) hD
  · intro i hi
    have hi' : i ≤ witnessLevel M r := by simpa [rationalState] using hi
    have hav : T39.avoidsTwo
        (fixedWord 10 (T39.decimalLevel (witnessLevel M r))
          (witnessDecimalValue r j)) := by
      have hk : r + (j : ℕ) < T39.decimalLevel (witnessLevel M r) := by
        simpa [witnessDecimalLength] using witness_digit_position_lt j
      rw [show witnessDecimalValue r j = 10 ^ (r + (j : ℕ)) by rfl,
        fixedWord_oneHot hk]
      exact oneHotWord_avoidsTwo _ _
    exact rationalState_all_prefixes_balanced hD hav hi'

/-- Pigeonhole collision among `M+1` reachable one-hot states. -/
theorem exists_reachable_same_quotientCode {M r : ℕ} (hM : 0 < M) :
    ∃ u v : Fin (M + 1), u ≠ v ∧
      T39.Reachable (witnessState M r u) ∧
      T39.Reachable (witnessState M r v) ∧
      quotientCode M r (residualOf r (witnessState M r u)) =
        quotientCode M r (residualOf r (witnessState M r v)) := by
  letI : NeZero M := ⟨hM.ne'⟩
  let f : Fin (M + 1) → ZMod M := fun j =>
    (residualOf r (witnessState M r j)).reducedCarry
  obtain ⟨u, v, huv, hres⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simp [hM.ne'])
  refine ⟨u, v, huv, witnessState_reachable u, witnessState_reachable v, ?_⟩
  apply Prod.ext
  · exact hres
  · apply Fin.ext
    simp [quotientCode, witness_suffix_eq_zero]

def externalContinuationLanguage (r : ℕ) (q : T39.State) : Set (List Packet) :=
  {w | Accepted (balancedContext q.level) r (residualOf r q) w}

/-- Equal natural quotient codes preserve languages if every reachable pair at
one common external clock level has equal externally clocked languages. -/
def QuotientLanguagePreserving (M r : ℕ) : Prop :=
  ∀ q q' : T39.State,
    T39.Reachable q → T39.Reachable q' → q.level = q'.level →
      quotientCode M r (residualOf r q) = quotientCode M r (residualOf r q') →
        externalContinuationLanguage r q = externalContinuationLanguage r q'

/-- For every positive `M,r`, named witnesses are reachable, share one clock
context and one `Q_(M,r)` code, and the displayed continuation is accepted
from exactly the first witness. -/
theorem exists_reachable_sameCode_oneSidedContinuation
    {M r : ℕ} (hM : 0 < M) (hr : 0 < r) :
    ∃ u v : Fin (M + 1),
      u ≠ v ∧
      T39.Reachable (witnessState M r u) ∧
      T39.Reachable (witnessState M r v) ∧
      (witnessState M r u).level = (witnessState M r v).level ∧
      quotientCode M r (residualOf r (witnessState M r u)) =
        quotientCode M r (residualOf r (witnessState M r v)) ∧
      Accepted (balancedContext (witnessLevel M r)) r
        (residualOf r (witnessState M r u)) (distinguishingContinuation M r u) ∧
      ¬ Accepted (balancedContext (witnessLevel M r)) r
        (residualOf r (witnessState M r v)) (distinguishingContinuation M r u) := by
  obtain ⟨u, v, huv, hru, hrv, hcode⟩ := exists_reachable_same_quotientCode hM
  exact ⟨u, v, huv, hru, hrv, rfl, hcode,
    distinguishingContinuation_accepted u,
    distinguishingContinuation_rejected_of_ne huv⟩

/-- No positive modulus and positive suffix length in the family `Q_(M,r)`
preserves externally clocked continuation languages. -/
theorem quotientCode_fails_to_preserve_languages
    {M r : ℕ} (hM : 0 < M) (hr : 0 < r) :
    ¬ QuotientLanguagePreserving M r := by
  intro hpreserves
  obtain ⟨u, v, huv, hru, hrv, hlevel, hcode, haccept, hreject⟩ :=
    exists_reachable_sameCode_oneSidedContinuation hM hr
  have hlanguage := hpreserves (witnessState M r u) (witnessState M r v)
    hru hrv hlevel hcode
  apply hreject
  change distinguishingContinuation M r u ∈
    externalContinuationLanguage r (witnessState M r v)
  rw [← hlanguage]
  exact haccept

end

end Theory.PiDigits.T41

#print axioms Theory.PiDigits.T41.witnessState_reachable
#print axioms Theory.PiDigits.T41.exists_reachable_same_quotientCode
#print axioms Theory.PiDigits.T41.distinguishingContinuation_accepted
#print axioms Theory.PiDigits.T41.distinguishingContinuation_rejected_of_ne
#print axioms Theory.PiDigits.T41.exists_reachable_sameCode_oneSidedContinuation
#print axioms Theory.PiDigits.T41.quotientCode_fails_to_preserve_languages
