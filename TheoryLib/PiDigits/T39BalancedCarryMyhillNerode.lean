import TheoryLib.PiDigits.T37CrossBaseCarry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log

/-!
# T39: the schedule-tagged balanced carry system

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file formalizes the exact level-tagged T38 balanced base-16/base-10
continuation system for decimal digit-`2` avoidance.  The decimal block length
(one or two) is part of every continuation symbol, so schedule legality is
observable by the right language.

Scope exclusions: this result does not address a carry-only controller supplied
with the level or future schedule by an external clock.  It proves nothing
about the digits of `Real.pi`, does not prove `T37.JMix Real.pi`, and proves
neither canonical V1 nor sibling V3.
-/

namespace Theory.PiDigits.T39

open Filter

/-- The balanced decimal length at hexadecimal level `n`. -/
def decimalLevel (n : ℕ) : ℕ := Nat.log 10 (16 ^ n)

/-- The number of decimal digits appended at hexadecimal level `n`. -/
def scheduleIncrement (n : ℕ) : ℕ := decimalLevel (n + 1) - decimalLevel n

theorem decimalLevel_lower (n : ℕ) :
    10 ^ decimalLevel n ≤ 16 ^ n := by
  exact Nat.pow_log_le_self 10 (pow_ne_zero n (by norm_num))

theorem decimalLevel_upper (n : ℕ) :
    16 ^ n < 10 ^ (decimalLevel n + 1) := by
  simpa [decimalLevel, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) (16 ^ n)

/-- The chosen decimal level is the unique natural satisfying the balanced
base-10/base-16 power bounds. -/
theorem decimalLevel_unique {n m : ℕ}
    (hlower : 10 ^ m ≤ 16 ^ n) (hupper : 16 ^ n < 10 ^ (m + 1)) :
    decimalLevel n = m := by
  exact Nat.log_eq_of_pow_le_of_lt_pow hlower hupper

theorem decimalLevel_succ_lower (n : ℕ) :
    decimalLevel n + 1 ≤ decimalLevel (n + 1) := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 10)
  calc
    10 ^ (decimalLevel n + 1) = 10 ^ decimalLevel n * 10 := by rw [pow_succ]
    _ ≤ 16 ^ n * 10 := Nat.mul_le_mul_right 10 (decimalLevel_lower n)
    _ ≤ 16 ^ n * 16 := Nat.mul_le_mul_left _ (by norm_num)
    _ = 16 ^ (n + 1) := by rw [pow_succ]

theorem decimalLevel_succ_upper (n : ℕ) :
    decimalLevel (n + 1) < decimalLevel n + 3 := by
  apply Nat.log_lt_of_lt_pow (pow_ne_zero (n + 1) (by norm_num : 16 ≠ 0))
  calc
    16 ^ (n + 1) = 16 ^ n * 16 := by rw [pow_succ]
    _ < 10 ^ (decimalLevel n + 1) * 16 :=
      Nat.mul_lt_mul_of_pos_right (decimalLevel_upper n) (by norm_num)
    _ ≤ 10 ^ (decimalLevel n + 1) * 100 :=
      Nat.mul_le_mul_left _ (by norm_num)
    _ = 10 ^ (decimalLevel n + 3) := by
      rw [show decimalLevel n + 3 = (decimalLevel n + 1) + 2 by omega, pow_add]
      norm_num only [pow_two]
      ring

theorem scheduleIncrement_one_or_two (n : ℕ) :
    scheduleIncrement n = 1 ∨ scheduleIncrement n = 2 := by
  have hlo := decimalLevel_succ_lower n
  have hhi := decimalLevel_succ_upper n
  simp only [scheduleIncrement]
  omega

theorem decimalLevel_succ (n : ℕ) :
    decimalLevel (n + 1) = decimalLevel n + scheduleIncrement n := by
  have hle : decimalLevel n ≤ decimalLevel (n + 1) :=
    (Nat.le_add_right (decimalLevel n) 1).trans (decimalLevel_succ_lower n)
  rw [scheduleIncrement, Nat.add_sub_of_le hle]

/-- Sum of the scheduled decimal-length increments over `r` steps. -/
def incrementSum (n r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, scheduleIncrement (n + i)

theorem decimalLevel_add_eq (n r : ℕ) :
    decimalLevel (n + r) = decimalLevel n + incrementSum n r := by
  induction r with
  | zero => simp [incrementSum]
  | succ r ih =>
      rw [Nat.add_succ, decimalLevel_succ, ih]
      simp [incrementSum, Finset.sum_range_succ, Nat.add_comm]
      ring

theorem increment_period_iterate {n d : ℕ}
    (hperiod : ∀ j : ℕ,
      scheduleIncrement (n + j) = scheduleIncrement (n + d + j))
    (r j : ℕ) :
    scheduleIncrement (n + j) = scheduleIncrement (n + r * d + j) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hstep : scheduleIncrement (n + j) =
          scheduleIncrement (n + (r * d + d) + j) := by
        calc
          scheduleIncrement (n + j) = scheduleIncrement (n + r * d + j) := ih
          _ = scheduleIncrement (n + (r * d + d) + j) := by
            have hp := hperiod (r * d + j)
            convert hp using 1 <;> congr 1 <;> omega
      simpa [Nat.succ_mul, Nat.add_assoc] using hstep

theorem incrementSum_period_iterate {n d : ℕ}
    (hperiod : ∀ j : ℕ,
      scheduleIncrement (n + j) = scheduleIncrement (n + d + j))
    (r : ℕ) :
    incrementSum (n + r * d) d = incrementSum n d := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  exact (increment_period_iterate hperiod r j).symm

theorem decimalLevel_periodic_affine {n d : ℕ}
    (hperiod : ∀ j : ℕ,
      scheduleIncrement (n + j) = scheduleIncrement (n + d + j))
    (r : ℕ) :
    decimalLevel (n + r * d) =
      decimalLevel n + r * incrementSum n d := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.succ_mul]
      calc
        decimalLevel (n + (r * d + d)) =
            decimalLevel (n + r * d) + incrementSum (n + r * d) d := by
              simpa [Nat.add_assoc] using decimalLevel_add_eq (n + r * d) d
        _ = decimalLevel n + r * incrementSum n d + incrementSum n d := by
              rw [ih, incrementSum_period_iterate hperiod r]
        _ = decimalLevel n + (r + 1) * incrementSum n d := by ring

/-- Two positive integer bases whose powers stay within fixed positive
multiplicative bounds must be equal. -/
theorem powerBases_eq_of_cross_bounds (A B x y : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) (hy : 0 < y)
    (hlow : ∀ r : ℕ, x * A ^ r ≤ y * B ^ r)
    (hhigh : ∀ r : ℕ, y * B ^ r < 10 * x * A ^ r) :
    A = B := by
  rcases lt_trichotomy A B with hAB | hAB | hAB
  · have hratio : (1 : ℝ) < (B : ℝ) / A := by
      rw [one_lt_div₀ (by positivity)]
      exact_mod_cast hAB
    have htend := tendsto_pow_atTop_atTop_of_one_lt hratio
    obtain ⟨r, hr⟩ :=
      Filter.Eventually.exists
        (htend.eventually_gt_atTop (((10 * x : ℕ) : ℝ) / y))
    have hcast : ((y * B ^ r : ℕ) : ℝ) < ((10 * x * A ^ r : ℕ) : ℝ) :=
      by exact_mod_cast hhigh r
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_pow] at hcast
    rw [div_pow] at hr
    field_simp at hr
    norm_num at hcast hr
    linarith
  · exact hAB
  · have hratio : (1 : ℝ) < (A : ℝ) / B := by
      rw [one_lt_div₀ (by positivity)]
      exact_mod_cast hAB
    have htend := tendsto_pow_atTop_atTop_of_one_lt hratio
    obtain ⟨r, hr⟩ := Filter.Eventually.exists
      (htend.eventually_gt_atTop ((y : ℝ) / x))
    have hcast : ((x * A ^ r : ℕ) : ℝ) ≤ ((y * B ^ r : ℕ) : ℝ) :=
      by exact_mod_cast hlow r
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow] at hcast
    rw [div_pow] at hr
    field_simp at hr
    linarith

theorem no_equal_schedule_tails_of_lt {n k : ℕ} (hnk : n < k) :
    ¬ ∀ j : ℕ,
      scheduleIncrement (n + j) = scheduleIncrement (k + j) := by
  intro hequal
  let d := k - n
  have hd : 0 < d := Nat.sub_pos_of_lt hnk
  have hk : k = n + d := by omega
  have hperiod : ∀ j : ℕ,
      scheduleIncrement (n + j) = scheduleIncrement (n + d + j) := by
    intro j
    simpa [hk, Nat.add_assoc] using hequal j
  let S := incrementSum n d
  have haffine (r : ℕ) :
      decimalLevel (n + r * d) = decimalLevel n + r * S :=
    decimalLevel_periodic_affine hperiod r
  let A := 10 ^ S
  let B := 16 ^ d
  let x := 10 ^ decimalLevel n
  let y := 16 ^ n
  have hlow (r : ℕ) : x * A ^ r ≤ y * B ^ r := by
    have h := decimalLevel_lower (n + r * d)
    rw [haffine] at h
    calc
      x * A ^ r = 10 ^ (decimalLevel n + r * S) := by
        dsimp [A, x]
        rw [pow_add, Nat.mul_comm r S, pow_mul]
      _ ≤ 16 ^ (n + r * d) := h
      _ = y * B ^ r := by
        dsimp [B, y]
        rw [pow_add, Nat.mul_comm r d, pow_mul]
  have hhigh (r : ℕ) : y * B ^ r < 10 * x * A ^ r := by
    have h := decimalLevel_upper (n + r * d)
    rw [haffine] at h
    calc
      y * B ^ r = 16 ^ (n + r * d) := by
        dsimp [B, y]
        rw [pow_add, Nat.mul_comm r d, pow_mul]
      _ < 10 ^ (decimalLevel n + r * S + 1) := h
      _ = 10 * x * A ^ r := by
        rw [Nat.mul_comm r S]
        rw [show decimalLevel n + S * r + 1 =
          1 + decimalLevel n + S * r by omega, pow_add, pow_add, pow_mul]
        simp [A, x]
  have hAB : A = B := powerBases_eq_of_cross_bounds A B x y
    (by positivity) (by positivity) (by positivity) (by positivity) hlow hhigh
  have hS : S ≠ 0 := by
    intro hzero
    have hpow : 10 ^ S = 16 ^ d := hAB
    simp [hzero] at hpow
    have hone : 1 < 16 ^ d := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hd)
    omega
  have hfiveA : 5 ∣ A := by
    dsimp [A]
    exact dvd_pow (by norm_num : 5 ∣ 10) hS
  have hfiveB : 5 ∣ B := hAB ▸ hfiveA
  have hfive16 : 5 ∣ 16 := by
    exact Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) (by simpa [B] using hfiveB)
  norm_num at hfive16

/-- Every two different levels have different future schedule tails. -/
theorem exists_scheduleIncrement_ne {n k : ℕ} (hnk : n ≠ k) :
    ∃ j : ℕ,
      scheduleIncrement (n + j) ≠ scheduleIncrement (k + j) := by
  by_contra hnone
  push Not at hnone
  rcases lt_or_gt_of_ne hnk with hlt | hgt
  · exact no_equal_schedule_tails_of_lt hlt hnone
  · exact no_equal_schedule_tails_of_lt hgt (fun j => (hnone j).symm)

/-- A fixed-length decimal block.  The disjunction retains the one/two tag. -/
def DecimalBlock :=
  {digits : List (Fin 10) // digits.length = 1 ∨ digits.length = 2}

structure Symbol where
  hex : Fin 16
  decimal : DecimalBlock

structure State where
  level : ℕ
  hexPrefix : List (Fin 16)
  decimalPrefix : List (Fin 10)
deriving DecidableEq

theorem state_ext {q q' : State}
    (hlevel : q.level = q'.level)
    (hhex : q.hexPrefix = q'.hexPrefix)
    (hdecimal : q.decimalPrefix = q'.decimalPrefix) : q = q' := by
  cases q
  cases q'
  simp_all

def avoidsTwo (digits : List (Fin 10)) : Prop :=
  (⟨2, by norm_num⟩ : Fin 10) ∉ digits

/-- Exact T38 state validity: fixed lengths, valid numeric prefixes,
digit-`2` avoidance, and nonempty T37 cylinder intersection. -/
def Balanced (q : State) : Prop :=
  q.hexPrefix.length = q.level ∧
  q.decimalPrefix.length = decimalLevel q.level ∧
  Theory.PiDigits.T37.ValidPrefix 16 q.level
    (Theory.PiDigits.T37.wordValue q.hexPrefix) ∧
  Theory.PiDigits.T37.ValidPrefix 10 (decimalLevel q.level)
    (Theory.PiDigits.T37.wordValue q.decimalPrefix) ∧
  avoidsTwo q.decimalPrefix ∧
  (Theory.PiDigits.T37.prefixCylinder 16 q.level
      (Theory.PiDigits.T37.wordValue q.hexPrefix) ∩
    Theory.PiDigits.T37.prefixCylinder 10 (decimalLevel q.level)
      (Theory.PiDigits.T37.wordValue q.decimalPrefix)).Nonempty

def appendSymbol (q : State) (a : Symbol) : State where
  level := q.level + 1
  hexPrefix := q.hexPrefix ++ [a.hex]
  decimalPrefix := q.decimalPrefix ++ a.decimal.1

/-- A retained transition is schedule-legal and has a balanced target. -/
def RetainedStep (q : State) (a : Symbol) : Prop :=
  a.decimal.1.length = scheduleIncrement q.level ∧
    Balanced (appendSymbol q a)

/-- Legal finite continuations check every retained transition. -/
def LegalContinuation : State → List Symbol → Prop
  | q, [] => Balanced q
  | q, a :: w => RetainedStep q a ∧ LegalContinuation (appendSymbol q a) w

def run : State → List Symbol → State := List.foldl appendSymbol

def initialState : State where
  level := 0
  hexPrefix := []
  decimalPrefix := []

/-- Reachability from the empty state by a legal finite continuation. -/
def Reachable (q : State) : Prop :=
  ∃ w : List Symbol, LegalContinuation initialState w ∧ run initialState w = q

def continuationLanguage (q : State) : Set (List Symbol) :=
  {w | LegalContinuation q w}

/-- Myhill-Nerode right-language equivalence for the exact tagged system. -/
def RightLanguageEquivalent (q q' : State) : Prop :=
  continuationLanguage q = continuationLanguage q'

theorem wordValue_append {base : ℕ} (u v : List (Fin base)) :
    Theory.PiDigits.T37.wordValue (u ++ v) =
      Theory.PiDigits.T37.wordValue u * base ^ v.length +
        Theory.PiDigits.T37.wordValue v := by
  induction u with
  | nil => simp [Theory.PiDigits.T37.wordValue]
  | cons d u ih =>
      simp only [List.cons_append, Theory.PiDigits.T37.wordValue,
        List.length_append, ih]
      rw [pow_add]
      ring

theorem wordValue_replicate_zero {base n : ℕ} (z : Fin base) (hz : z.val = 0) :
    Theory.PiDigits.T37.wordValue (List.replicate n z) = 0 := by
  induction n with
  | zero => simp [Theory.PiDigits.T37.wordValue]
  | succ n ih =>
      rw [List.replicate_succ, Theory.PiDigits.T37.wordValue]
      simp [hz, ih]

def zeroState (n : ℕ) : State where
  level := n
  hexPrefix := List.replicate n ⟨0, by norm_num⟩
  decimalPrefix := List.replicate (decimalLevel n) ⟨0, by norm_num⟩

theorem zeroState_balanced (n : ℕ) : Balanced (zeroState n) := by
  refine ⟨by simp [zeroState], by simp [zeroState], ?_, ?_, ?_, ?_⟩
  · simp only [zeroState]
    rw [wordValue_replicate_zero _ rfl]
    simp [Theory.PiDigits.T37.ValidPrefix]
  · simp only [zeroState]
    rw [wordValue_replicate_zero _ rfl]
    simp [Theory.PiDigits.T37.ValidPrefix]
  · simp [avoidsTwo, zeroState]
  · rw [Theory.PiDigits.T37.cylinders_overlap_iff_carry_bounds]
    simp only [zeroState]
    rw [wordValue_replicate_zero _ rfl, wordValue_replicate_zero _ rfl]
    simp [Theory.PiDigits.T37.carry]

def zeroBlock (n : ℕ) : DecimalBlock :=
  ⟨List.replicate (scheduleIncrement n) ⟨0, by norm_num⟩, by
    simpa using scheduleIncrement_one_or_two n⟩

def zeroSymbol (n : ℕ) : Symbol where
  hex := ⟨0, by norm_num⟩
  decimal := zeroBlock n

theorem appendSymbol_zeroState_zeroSymbol_of_increment_eq
    {n k : ℕ} (h : scheduleIncrement n = scheduleIncrement k) :
    appendSymbol (zeroState k) (zeroSymbol n) = zeroState (k + 1) := by
  apply state_ext
  · rfl
  · change List.replicate k (⟨0, by norm_num⟩ : Fin 16) ++ [⟨0, by norm_num⟩] =
      List.replicate (k + 1) ⟨0, by norm_num⟩
    rw [show ([⟨0, by norm_num⟩] : List (Fin 16)) =
      List.replicate 1 ⟨0, by norm_num⟩ by rfl, ← List.replicate_add]
  · simp [appendSymbol, zeroState, zeroSymbol, zeroBlock, h, decimalLevel_succ]

theorem zeroStep_iff {n k : ℕ} :
    RetainedStep (zeroState k) (zeroSymbol n) ↔
      scheduleIncrement n = scheduleIncrement k := by
  constructor
  · intro h
    simpa [RetainedStep, zeroSymbol, zeroBlock] using h.1
  · intro h
    refine ⟨by simpa [zeroSymbol, zeroBlock, zeroState] using h, ?_⟩
    rw [appendSymbol_zeroState_zeroSymbol_of_increment_eq h]
    exact zeroState_balanced (k + 1)

def zeroContinuation : ℕ → ℕ → List Symbol
  | _, 0 => []
  | n, r + 1 => zeroSymbol n :: zeroContinuation (n + 1) r

theorem legal_zeroContinuation_iff (n k r : ℕ) :
    LegalContinuation (zeroState k) (zeroContinuation n r) ↔
      ∀ i < r,
        scheduleIncrement (n + i) = scheduleIncrement (k + i) := by
  induction r generalizing n k with
  | zero => simp [zeroContinuation, LegalContinuation, zeroState_balanced]
  | succ r ih =>
      rw [zeroContinuation, LegalContinuation, zeroStep_iff]
      constructor
      · rintro ⟨hfirst, htail⟩ i hi
        rw [appendSymbol_zeroState_zeroSymbol_of_increment_eq hfirst] at htail
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · simpa using hfirst
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hipos)
          have hj : j < r := by omega
          have := (ih (n + 1) (k + 1)).mp htail j hj
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · intro hall
        have hfirst : scheduleIncrement n = scheduleIncrement k := by
          simpa using hall 0 (by omega)
        refine ⟨hfirst, ?_⟩
        rw [appendSymbol_zeroState_zeroSymbol_of_increment_eq hfirst]
        apply (ih (n + 1) (k + 1)).mpr
        intro i hi
        have := hall (i + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem legal_zeroContinuation (n r : ℕ) :
    LegalContinuation (zeroState n) (zeroContinuation n r) := by
  apply (legal_zeroContinuation_iff n n r).mpr
  simp

theorem run_zeroContinuation (n r : ℕ) :
    run (zeroState n) (zeroContinuation n r) = zeroState (n + r) := by
  induction r generalizing n with
  | zero => simp [run, zeroContinuation]
  | succ r ih =>
      simp only [run, zeroContinuation, List.foldl_cons]
      rw [appendSymbol_zeroState_zeroSymbol_of_increment_eq rfl]
      change run (zeroState (n + 1)) (zeroContinuation (n + 1) r) =
        zeroState (n + (r + 1))
      rw [ih]
      congr 1
      omega

/-- Every member of the infinite all-zero family is reachable. -/
theorem zeroFamily_reachable (n : ℕ) : Reachable (zeroState n) := by
  refine ⟨zeroContinuation 0 n, legal_zeroContinuation 0 n, ?_⟩
  simpa [initialState, zeroState] using run_zeroContinuation 0 n

/-- The concrete all-zero continuation ending at a schedule mismatch is legal
from one zero state and illegal from the other. -/
theorem zeroFamily_explicit_distinguishingContinuation
    {n k : ℕ} (hnk : n ≠ k) :
    ∃ j : ℕ,
      LegalContinuation (zeroState n) (zeroContinuation n (j + 1)) ∧
        ¬ LegalContinuation (zeroState k) (zeroContinuation n (j + 1)) := by
  obtain ⟨j, hj⟩ := exists_scheduleIncrement_ne hnk
  refine ⟨j, legal_zeroContinuation n (j + 1), ?_⟩
  intro hlegal
  have hall := (legal_zeroContinuation_iff n k (j + 1)).mp hlegal
  exact hj (hall j (by omega))

/-- Every two different all-zero states have different right languages, with
an all-zero continuation ending at a schedule-length mismatch. -/
theorem zeroFamily_pairwise_rightLanguage_inequivalent
    {n k : ℕ} (hnk : n ≠ k) :
    ¬ RightLanguageEquivalent (zeroState n) (zeroState k) := by
  obtain ⟨j, hlegaln, hillegalk⟩ :=
    zeroFamily_explicit_distinguishingContinuation hnk
  intro hequiv
  have hmemn : zeroContinuation n (j + 1) ∈ continuationLanguage (zeroState n) :=
    hlegaln
  have hmemk : zeroContinuation n (j + 1) ∈ continuationLanguage (zeroState k) := by
    rw [← hequiv]
    exact hmemn
  exact hillegalk hmemk

/-- A state code is exact behavior-preserving when equal codes force equality
of complete continuation languages. -/
def ExactBehaviorPreserving {Q : Type*} (code : State → Q) : Prop :=
  ∀ q q' : State,
    Reachable q → Reachable q' → code q = code q' →
      RightLanguageEquivalent q q'

/-- No finite exact behavior-preserving quotient exists for the exact
schedule-tagged T38 system. -/
theorem no_finite_exactBehaviorPreserving_quotient
    {Q : Type*} [Finite Q] (code : State → Q) :
    ¬ ExactBehaviorPreserving code := by
  intro hexact
  obtain ⟨n, k, hnk, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => code (zeroState i))
  exact zeroFamily_pairwise_rightLanguage_inequivalent hnk
    (hexact (zeroState n) (zeroState k)
      (zeroFamily_reachable n) (zeroFamily_reachable k) heq)

end Theory.PiDigits.T39

#print axioms Theory.PiDigits.T39.zeroFamily_reachable
#print axioms Theory.PiDigits.T39.exists_scheduleIncrement_ne
#print axioms Theory.PiDigits.T39.zeroFamily_explicit_distinguishingContinuation
#print axioms Theory.PiDigits.T39.zeroFamily_pairwise_rightLanguage_inequivalent
#print axioms Theory.PiDigits.T39.no_finite_exactBehaviorPreserving_quotient
