import TheoryLib.PiDigits.T37CrossBaseCarry
import TheoryLib.PiDigits.T43CommonLevelResidualIndex
import TheoryLib.PiDigits.T46AllSingleDigitResidualIndex
import TheoryLib.PiDigits.T48ScaledOneHotDigitOne
import Mathlib.Data.Fintype.Pigeonhole

/-!
# T50: background-marker residual index for forbidden digit zero

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file independently formalizes the fixed `(marker, background) = (2, 1)`
construction in T46's externally clocked base-16/base-10 residual system with
decimal digit `0` forbidden. It imports no claim from the unverified T49 note.

The external level and future schedule remain shared test parameters, not
fields of the persistent residual. Thus the finite-code theorem does not apply
to schedule-aware controllers retaining that clock data. Nothing here concerns
arbitrary forbidden words or digit sets, the digits of `Real.pi`,
`T37.JMix Real.pi`, canonical V1, or sibling V3.
-/

namespace Theory.PiDigits.T50

open Theory.PiDigits

noncomputable section

/-- A decimal word with background digit `1` and one marker digit `2`. -/
def backgroundMarkerWord (length k : ℕ) : List (Fin 10) :=
  List.replicate (length - (k + 1)) 1 ++ [2] ++ List.replicate k 1

theorem backgroundMarkerWord_length {length k : ℕ} (hk : k < length) :
    (backgroundMarkerWord length k).length = length := by
  simp [backgroundMarkerWord]
  omega

theorem backgroundMarkerWord_avoids_zero (length k : ℕ) :
    T46.AvoidsDigit (0 : Fin 10) (backgroundMarkerWord length k) := by
  simp [T46.AvoidsDigit, backgroundMarkerWord]

/-- Numeric value of the background-marker word. -/
def backgroundMarkerValue (length k : ℕ) : ℕ :=
  T37.wordValue (backgroundMarkerWord length k)

theorem backgroundMarkerValue_eq {length k : ℕ} (hk : k < length) :
    backgroundMarkerValue length k =
      T37.wordValue (List.replicate length (1 : Fin 10)) + 10 ^ k := by
  have hrep : List.replicate length (1 : Fin 10) =
      List.replicate (length - (k + 1)) 1 ++ [1] ++ List.replicate k 1 := by
    change List.replicate length (1 : Fin 10) =
      List.replicate (length - (k + 1)) 1 ++
        List.replicate 1 1 ++ List.replicate k 1
    rw [← List.replicate_add, ← List.replicate_add]
    congr 1
    omega
  rw [hrep]
  simp only [backgroundMarkerValue, backgroundMarkerWord, T39.wordValue_append,
    T37.wordValue, List.length_replicate, List.length_singleton]
  norm_num
  ring

theorem backgroundMarkerValue_lt_pow {length k : ℕ} (hk : k < length) :
    backgroundMarkerValue length k < 10 ^ length := by
  simpa [backgroundMarkerValue, backgroundMarkerWord_length hk] using
    T41.wordValue_lt_pow (by norm_num) (backgroundMarkerWord length k)

theorem fixedWord_backgroundMarker {length k : ℕ} (hk : k < length) :
    T41.fixedWord 10 length (backgroundMarkerValue length k) =
      backgroundMarkerWord length k := by
  apply T41.word_eq_of_length_value (by norm_num)
  · rw [T41.fixedWord_length (by norm_num) (backgroundMarkerValue_lt_pow hk),
      backgroundMarkerWord_length hk]
  · rw [T41.fixedWord_value (by norm_num) (backgroundMarkerValue_lt_pow hk)]
    rfl

/-- Base-`base` prefix selected by the rational point `P / Q`. -/
def fractionPrefixValue (base length P Q : ℕ) : ℕ :=
  (base ^ length * P) / Q

/-- Simultaneous base-16/base-10 prefixes selected by one rational point. -/
def fractionState (n P Q : ℕ) : T39.State where
  level := n
  hexPrefix := T41.fixedWord 16 n (fractionPrefixValue 16 n P Q)
  decimalPrefix := T41.fixedWord 10 (T39.decimalLevel n)
    (fractionPrefixValue 10 (T39.decimalLevel n) P Q)

theorem fractionPrefixValue_lt_pow {base length P Q : ℕ}
    (hbase : 0 < base) (hQ : 0 < Q) (hPQ : P < Q) :
    fractionPrefixValue base length P Q < base ^ length := by
  apply (Nat.div_lt_iff_lt_mul hQ).2
  exact (Nat.mul_lt_mul_left (by positivity : 0 < base ^ length)).2 hPQ

theorem fractionPrefixValue_div_pow {base n i P Q : ℕ} (hbase : 0 < base)
    (hi : i ≤ n) :
    fractionPrefixValue base n P Q / base ^ (n - i) =
      fractionPrefixValue base i P Q := by
  rw [fractionPrefixValue, fractionPrefixValue, Nat.div_div_eq_div_mul]
  conv_lhs =>
    congr
    · rw [show n = i + (n - i) by omega, pow_add]
    · skip
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_div_mul_right (base ^ i * P) Q
      (by positivity : 0 < base ^ (n - i))

theorem fractionState_hexPrefix_value {n P Q i : ℕ}
    (hQ : 0 < Q) (hPQ : P < Q) (hi : i ≤ n) :
    T37.wordValue ((fractionState n P Q).hexPrefix.take i) =
      fractionPrefixValue 16 i P Q := by
  change T37.wordValue
      ((T41.fixedWord 16 n (fractionPrefixValue 16 n P Q)).take i) = _
  rw [T41.fixedWord_take_value (by norm_num)
      (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ) hi,
    fractionPrefixValue_div_pow (by norm_num) hi]

theorem fractionState_decimalPrefix_value {n P Q i : ℕ}
    (hQ : 0 < Q) (hPQ : P < Q) (hi : i ≤ n) :
    T37.wordValue
        ((fractionState n P Q).decimalPrefix.take (T39.decimalLevel i)) =
      fractionPrefixValue 10 (T39.decimalLevel i) P Q := by
  have hm := T41.decimalLevel_mono_of_le hi
  change T37.wordValue
      ((T41.fixedWord 10 (T39.decimalLevel n)
        (fractionPrefixValue 10 (T39.decimalLevel n) P Q)).take
          (T39.decimalLevel i)) = _
  rw [T41.fixedWord_take_value (by norm_num)
      (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ) hm,
    fractionPrefixValue_div_pow (by norm_num) hm]

/-- One rational point witnesses all scheduled prefix overlaps. -/
theorem fractionState_all_prefixes_balancedFor
    {d : Fin 10} {n P Q : ℕ} (hQ : 0 < Q) (hPQ : P < Q)
    (havoid : T46.AvoidsDigit d (fractionState n P Q).decimalPrefix)
    {i : ℕ} (hi : i ≤ n) :
    T46.BalancedFor d (T41.prefixState (fractionState n P Q) i) := by
  have hhex := fractionPrefixValue_lt_pow (base := 16) (length := n)
    (by norm_num) hQ hPQ
  have hdec := fractionPrefixValue_lt_pow (base := 10)
    (length := T39.decimalLevel n) (by norm_num) hQ hPQ
  have hm := T41.decimalLevel_mono_of_le hi
  have hhexlen : (fractionState n P Q).hexPrefix.length = n :=
    T41.fixedWord_length (by norm_num) hhex
  have hdeclen : (fractionState n P Q).decimalPrefix.length =
      T39.decimalLevel n := T41.fixedWord_length (by norm_num) hdec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [T41.prefixState, hhexlen, hi]
  · simp [T41.prefixState, hdeclen, hm]
  · have h := T41.wordValue_lt_pow (by norm_num)
      ((fractionState n P Q).hexPrefix.take i)
    simpa [T37.ValidPrefix, T41.prefixState, hhexlen, hi] using h
  · have h := T41.wordValue_lt_pow (by norm_num)
      ((fractionState n P Q).decimalPrefix.take (T39.decimalLevel i))
    simpa [T37.ValidPrefix, T41.prefixState, hdeclen, hm] using h
  · intro hmem
    apply havoid
    exact List.mem_of_mem_take hmem
  · refine ⟨(P : ℝ) / Q, ?_, ?_⟩
    · simp only [T41.prefixState]
      rw [fractionState_hexPrefix_value hQ hPQ hi]
      simpa [fractionPrefixValue] using
        T41.natDiv_mem_prefixCylinder 16 i P Q (by norm_num) hQ
    · simp only [T41.prefixState]
      rw [fractionState_decimalPrefix_value hQ hPQ hi]
      simpa [fractionPrefixValue] using
        T41.natDiv_mem_prefixCylinder 10 (T39.decimalLevel i) P Q
          (by norm_num) hQ

theorem fractionState_prefixState {n t P Q : ℕ}
    (hQ : 0 < Q) (hPQ : P < Q) :
    T41.prefixState (fractionState (n + t) P Q) n = fractionState n P Q := by
  have hn : n ≤ n + t := Nat.le_add_right n t
  have hhexLong := fractionPrefixValue_lt_pow (base := 16)
    (length := n + t) (by norm_num) hQ hPQ
  have hhexShort := fractionPrefixValue_lt_pow (base := 16)
    (length := n) (by norm_num) hQ hPQ
  have hdecLong := fractionPrefixValue_lt_pow (base := 10)
    (length := T39.decimalLevel (n + t)) (by norm_num) hQ hPQ
  have hdecShort := fractionPrefixValue_lt_pow (base := 10)
    (length := T39.decimalLevel n) (by norm_num) hQ hPQ
  apply T39.state_ext
  · rfl
  · simp only [T41.prefixState, fractionState]
    apply T41.word_eq_of_length_value (by norm_num)
    · rw [List.length_take_of_le]
      · exact (T41.fixedWord_length (by norm_num) hhexShort).symm
      · rw [T41.fixedWord_length (by norm_num) hhexLong]
        omega
    · rw [T41.fixedWord_take_value (by norm_num) hhexLong hn,
        fractionPrefixValue_div_pow (by norm_num) hn,
        T41.fixedWord_value (by norm_num) hhexShort]
  · simp only [T41.prefixState, fractionState]
    have hm := T41.decimalLevel_mono_of_le hn
    apply T41.word_eq_of_length_value (by norm_num)
    · rw [List.length_take_of_le]
      · exact (T41.fixedWord_length (by norm_num) hdecShort).symm
      · rw [T41.fixedWord_length (by norm_num) hdecLong]
        exact hm
    · rw [T41.fixedWord_take_value (by norm_num) hdecLong hm,
        fractionPrefixValue_div_pow (by norm_num) hm,
        T41.fixedWord_value (by norm_num) hdecShort]

/-- Common hexadecimal level for the `K+1` background-marker witnesses. -/
def familyLevel (K : ℕ) : ℕ := 2 * (K + 1)

def familyLength (K : ℕ) : ℕ := T39.decimalLevel (familyLevel K)

theorem family_position_lt {K : ℕ} (j : Fin (K + 1)) :
    (j : ℕ) < familyLength K := by
  have hlevel := T41.decimalLevel_self_le (familyLevel K)
  have hKN : K + 1 ≤ familyLevel K := by simp [familyLevel]
  exact j.isLt.trans_le (hKN.trans hlevel)

def familyDecimalValue (K : ℕ) (j : Fin (K + 1)) : ℕ :=
  backgroundMarkerValue (familyLength K) j

def familyNumerator (K : ℕ) (j : Fin (K + 1)) : ℕ :=
  9 * familyDecimalValue K j + 1

def familyDenominator (K : ℕ) : ℕ := 9 * 10 ^ familyLength K

theorem familyDecimalValue_lt_pow {K : ℕ} (j : Fin (K + 1)) :
    familyDecimalValue K j < 10 ^ familyLength K :=
  backgroundMarkerValue_lt_pow (family_position_lt j)

theorem familyDenominator_pos (K : ℕ) : 0 < familyDenominator K := by
  simp [familyDenominator]

theorem familyNumerator_lt_denominator {K : ℕ} (j : Fin (K + 1)) :
    familyNumerator K j < familyDenominator K := by
  have h := familyDecimalValue_lt_pow j
  simp only [familyNumerator, familyDenominator]
  omega

theorem family_fractionDecimalValue_eq {K : ℕ} (j : Fin (K + 1)) :
    fractionPrefixValue 10 (familyLength K) (familyNumerator K j)
      (familyDenominator K) = familyDecimalValue K j := by
  let D := familyDecimalValue K j
  change (10 ^ familyLength K * (9 * D + 1)) /
      (9 * 10 ^ familyLength K) = D
  calc
    (10 ^ familyLength K * (9 * D + 1)) /
          (9 * 10 ^ familyLength K) =
        ((9 * D + 1) * 10 ^ familyLength K) /
          (9 * 10 ^ familyLength K) := by
      congr 1
      ring
    _ = (9 * D + 1) / 9 := by
      exact Nat.mul_div_mul_right (9 * D + 1) 9 (by positivity)
    _ = D := by omega

/-- Concrete source selected by the nonterminating decimal point
`0.(background-marker)111...`. -/
def familyState (K : ℕ) (j : Fin (K + 1)) : T39.State :=
  fractionState (familyLevel K) (familyNumerator K j) (familyDenominator K)

def familyResidual (K : ℕ) (j : Fin (K + 1)) : T41.ResidualState :=
  T41.residualOf 1 (familyState K j)

theorem family_decimalPrefix_eq (K : ℕ) (j : Fin (K + 1)) :
    (familyState K j).decimalPrefix =
      backgroundMarkerWord (familyLength K) j := by
  change T41.fixedWord 10 (familyLength K)
      (fractionPrefixValue 10 (familyLength K) (familyNumerator K j)
        (familyDenominator K)) = _
  rw [family_fractionDecimalValue_eq]
  simpa [familyDecimalValue] using
    fixedWord_backgroundMarker (family_position_lt j)

theorem family_decimalPrefix_avoids_zero (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit (0 : Fin 10) (familyState K j).decimalPrefix := by
  rw [family_decimalPrefix_eq]
  exact backgroundMarkerWord_avoids_zero _ _

theorem family_reachableFor (K : ℕ) (j : Fin (K + 1)) :
    T46.ReachableFor (0 : Fin 10) (familyState K j) := by
  have hQ := familyDenominator_pos K
  have hPQ := familyNumerator_lt_denominator j
  apply T46.reachableFor_of_all_prefixes_balanced
  · exact T41.fixedWord_length (by norm_num)
      (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ)
  · exact T41.fixedWord_length (by norm_num)
      (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ)
  · intro i hi
    exact fractionState_all_prefixes_balancedFor hQ hPQ
      (family_decimalPrefix_avoids_zero K j) hi

/-- Every source belongs to one common external level. -/
theorem family_reachableAt (K : ℕ) (j : Fin (K + 1)) :
    T46.ReachableAtFor (0 : Fin 10) (familyLevel K) (familyState K j) := by
  exact ⟨family_reachableFor K j, rfl⟩

/-- Every residual is induced by a digit-0 source at that common level. -/
theorem family_persistent_reachableAt (K : ℕ) (j : Fin (K + 1)) :
    T46.PersistentReachableAt (0 : Fin 10) (familyLevel K)
      (familyResidual K j) := by
  exact ⟨familyState K j, family_reachableAt K j, rfl⟩

theorem family_hexPrefix_value (K : ℕ) (j : Fin (K + 1)) :
    T37.wordValue (familyState K j).hexPrefix =
      fractionPrefixValue 16 (familyLevel K) (familyNumerator K j)
        (familyDenominator K) := by
  have hQ := familyDenominator_pos K
  have hPQ := familyNumerator_lt_denominator j
  change T37.wordValue (T41.fixedWord 16 (familyLevel K)
    (fractionPrefixValue 16 (familyLevel K) (familyNumerator K j)
      (familyDenominator K))) = _
  rw [T41.fixedWord_value (by norm_num)
    (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ)]

theorem family_decimalPrefix_value (K : ℕ) (j : Fin (K + 1)) :
    T37.wordValue (familyState K j).decimalPrefix = familyDecimalValue K j := by
  rw [family_decimalPrefix_eq]
  rfl

theorem family_reducedCarry_eq (K : ℕ) (j : Fin (K + 1)) :
    (familyResidual K j).reducedCarry =
      ((T41.balancedContext (familyLevel K)).a : ℤ) *
          fractionPrefixValue 16 (familyLevel K) (familyNumerator K j)
            (familyDenominator K) -
        ((T41.balancedContext (familyLevel K)).b : ℤ) *
          familyDecimalValue K j := by
  have hQ := familyDenominator_pos K
  have hPQ := familyNumerator_lt_denominator j
  have hdecval : fractionPrefixValue 10 (T39.decimalLevel (familyLevel K))
      (familyNumerator K j) (familyDenominator K) = familyDecimalValue K j := by
    simpa [familyLength] using family_fractionDecimalValue_eq j
  simp only [familyResidual, T41.residualOf, familyState, fractionState,
    T41.reducedCarryAt]
  rw [T41.fixedWord_value (by norm_num)
      (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ),
    T41.fixedWord_value (by norm_num)
      (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ),
    hdecval]

theorem markerPower_lt_fiveScale {K : ℕ} (j : Fin (K + 1)) :
    10 ^ (j : ℕ) < (T41.balancedContext (familyLevel K)).a := by
  have hexp : 2 * ((j : ℕ) + 1) ≤ familyLength K := by
    have hj : (j : ℕ) + 1 ≤ K + 1 := j.isLt
    have hlevel := T41.decimalLevel_self_le (familyLevel K)
    dsimp [familyLength]
    have : 2 * ((j : ℕ) + 1) ≤ familyLevel K := by
      dsimp [familyLevel]
      omega
    exact this.trans hlevel
  calc
    10 ^ (j : ℕ) < 25 ^ ((j : ℕ) + 1) := by
      exact (Nat.pow_le_pow_left (by norm_num : 10 ≤ 25) (j : ℕ)).trans_lt
        (Nat.pow_lt_pow_right (by norm_num : 1 < 25) (Nat.lt_succ_self (j : ℕ)))
    _ = 5 ^ (2 * ((j : ℕ) + 1)) := by
      rw [show 25 = 5 ^ 2 by norm_num, ← pow_mul]
    _ ≤ 5 ^ familyLength K := Nat.pow_le_pow_right (by norm_num) hexp
    _ = (T41.balancedContext (familyLevel K)).a := rfl

/-- The reduced carry already distinguishes every background-marker witness. -/
theorem family_reducedCarry_injective (K : ℕ) :
    Function.Injective (fun j : Fin (K + 1) =>
      (familyResidual K j).reducedCarry) := by
  intro u v huv
  change (familyResidual K u).reducedCarry =
    (familyResidual K v).reducedCarry at huv
  rw [family_reducedCarry_eq, family_reducedCarry_eq] at huv
  let a := (T41.balancedContext (familyLevel K)).a
  let b := (T41.balancedContext (familyLevel K)).b
  let Au := fractionPrefixValue 16 (familyLevel K) (familyNumerator K u)
    (familyDenominator K)
  let Av := fractionPrefixValue 16 (familyLevel K) (familyNumerator K v)
    (familyDenominator K)
  let Du := familyDecimalValue K u
  let Dv := familyDecimalValue K v
  have hz : (a : ℤ) * Au + (b : ℤ) * Dv =
      (a : ℤ) * Av + (b : ℤ) * Du := by
    change (a : ℤ) * Au - (b : ℤ) * Du =
      (a : ℤ) * Av - (b : ℤ) * Dv at huv
    omega
  have hnat : a * Au + b * Dv = a * Av + b * Du := by
    exact_mod_cast hz
  have hrem := congrArg (fun x : ℕ => x % a) hnat
  have hmul : b * Dv ≡ b * Du [MOD a] := by
    simpa [Nat.add_mod] using hrem
  have hcop : Nat.gcd a b = 1 := by
    simpa [a, b, T41.balancedContext] using
      ((by norm_num : Nat.Coprime 5 2).pow
        (T39.decimalLevel (familyLevel K))
        (4 * familyLevel K - T39.decimalLevel (familyLevel K))).gcd_eq_one
  have hDmod : Dv ≡ Du [MOD a] := hmul.cancel_left_of_coprime hcop
  change familyDecimalValue K v ≡ familyDecimalValue K u [MOD a] at hDmod
  rw [familyDecimalValue, backgroundMarkerValue_eq (family_position_lt v),
    familyDecimalValue, backgroundMarkerValue_eq (family_position_lt u)] at hDmod
  have hpmod : 10 ^ (v : ℕ) ≡ 10 ^ (u : ℕ) [MOD a] :=
    Nat.ModEq.add_left_cancel'
      (T37.wordValue (List.replicate (familyLength K) (1 : Fin 10))) hDmod
  have hp : 10 ^ (v : ℕ) = 10 ^ (u : ℕ) :=
    hpmod.eq_of_lt_of_lt (markerPower_lt_fiveScale v)
      (markerPower_lt_fiveScale u)
  have huvval : (v : ℕ) = (u : ℕ) :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 10) hp
  apply Fin.ext
  exact huvval.symm

/-- Residual-state injectivity follows from reduced-carry injectivity. -/
theorem familyResidual_injective (K : ℕ) :
    Function.Injective (familyResidual K) := by
  intro u v huv
  apply family_reducedCarry_injective K
  exact congrArg T41.ResidualState.reducedCarry huv

theorem nine_mul_replicateOne_value_add_one (s : ℕ) :
    9 * T37.wordValue (List.replicate s (1 : Fin 10)) + 1 = 10 ^ s := by
  induction s with
  | zero => simp [T37.wordValue]
  | succ s ih =>
      rw [List.replicate_succ, T37.wordValue, List.length_replicate, pow_succ]
      norm_num
      omega

/-- The separator length is the current power-of-five scale. -/
def familySteps (K : ℕ) : ℕ :=
  (T41.balancedContext (familyLevel K)).a

theorem familySteps_pos (K : ℕ) : 0 < familySteps K := by
  simp [familySteps, T41.balancedContext]

def familyExtraDigits (K : ℕ) : ℕ :=
  T39.incrementSum (familyLevel K) (familySteps K)

def extendedState (K : ℕ) (j : Fin (K + 1)) : T39.State :=
  fractionState (familyLevel K + familySteps K) (familyNumerator K j)
    (familyDenominator K)

theorem extended_decimalLevel_eq (K : ℕ) :
    T39.decimalLevel (familyLevel K + familySteps K) =
      familyLength K + familyExtraDigits K := by
  exact T39.decimalLevel_add_eq (familyLevel K) (familySteps K)

theorem extended_fractionDecimalValue_eq (K : ℕ) (j : Fin (K + 1)) :
    fractionPrefixValue 10
        (T39.decimalLevel (familyLevel K + familySteps K))
        (familyNumerator K j) (familyDenominator K) =
      familyDecimalValue K j * 10 ^ familyExtraDigits K +
        T37.wordValue (List.replicate (familyExtraDigits K) (1 : Fin 10)) := by
  let D := familyDecimalValue K j
  let S := familyExtraDigits K
  let R := T37.wordValue (List.replicate S (1 : Fin 10))
  have hR : 9 * R + 1 = 10 ^ S := nine_mul_replicateOne_value_add_one S
  change (10 ^ T39.decimalLevel (familyLevel K + familySteps K) *
      (9 * D + 1)) / (9 * 10 ^ familyLength K) = D * 10 ^ S + R
  rw [extended_decimalLevel_eq]
  change (10 ^ (familyLength K + S) * (9 * D + 1)) /
      (9 * 10 ^ familyLength K) = D * 10 ^ S + R
  rw [pow_add]
  calc
    (10 ^ familyLength K * 10 ^ S * (9 * D + 1)) /
          (9 * 10 ^ familyLength K) =
        (10 ^ familyLength K * (10 ^ S * (9 * D + 1))) /
          (10 ^ familyLength K * 9) := by congr 1 <;> ring
    _ = (10 ^ S * (9 * D + 1)) / 9 := by
      exact Nat.mul_div_mul_left (10 ^ S * (9 * D + 1)) 9 (by positivity)
    _ = D * 10 ^ S + R := by
      have hnum : 10 ^ S * (9 * D + 1) = 9 * (D * 10 ^ S + R) + 1 := by
        rw [← hR]
        ring
      rw [hnum]
      omega

theorem extendedState_hex_length {K : ℕ} (j : Fin (K + 1)) :
    (extendedState K j).hexPrefix.length = (extendedState K j).level := by
  have hQ := familyDenominator_pos K
  have hPQ := familyNumerator_lt_denominator j
  exact T41.fixedWord_length (by norm_num)
    (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ)

theorem extendedState_decimal_length {K : ℕ} (j : Fin (K + 1)) :
    (extendedState K j).decimalPrefix.length =
      T39.decimalLevel (extendedState K j).level := by
  have hQ := familyDenominator_pos K
  have hPQ := familyNumerator_lt_denominator j
  exact T41.fixedWord_length (by norm_num)
    (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ)

theorem extendedState_decimalPrefix_eq (K : ℕ) (j : Fin (K + 1)) :
    (extendedState K j).decimalPrefix =
      backgroundMarkerWord (familyLength K) j ++
        List.replicate (familyExtraDigits K) 1 := by
  have hQ := familyDenominator_pos K
  have hPQ := familyNumerator_lt_denominator j
  apply T41.word_eq_of_length_value (by norm_num)
  · rw [extendedState_decimal_length]
    simp only [List.length_append, List.length_replicate,
      backgroundMarkerWord_length (family_position_lt j)]
    exact extended_decimalLevel_eq K
  · change T37.wordValue (T41.fixedWord 10
      (T39.decimalLevel (familyLevel K + familySteps K))
      (fractionPrefixValue 10
        (T39.decimalLevel (familyLevel K + familySteps K))
        (familyNumerator K j) (familyDenominator K))) = _
    rw [T41.fixedWord_value (by norm_num)
      (fractionPrefixValue_lt_pow (by norm_num) hQ hPQ),
      extended_fractionDecimalValue_eq, T39.wordValue_append,
      List.length_replicate]
    rfl

theorem extendedState_decimalPrefix_avoids_zero
    (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit (0 : Fin 10) (extendedState K j).decimalPrefix := by
  rw [extendedState_decimalPrefix_eq]
  simp [T46.AvoidsDigit, backgroundMarkerWord]

theorem extendedState_all_prefixes_balancedFor
    (K : ℕ) (j : Fin (K + 1)) {i : ℕ}
    (hi : i ≤ (extendedState K j).level) :
    T46.BalancedFor (0 : Fin 10) (T41.prefixState (extendedState K j) i) := by
  exact fractionState_all_prefixes_balancedFor (familyDenominator_pos K)
    (familyNumerator_lt_denominator j)
    (extendedState_decimalPrefix_avoids_zero K j) hi

theorem extendedState_prefix_eq_familyState (K : ℕ) (j : Fin (K + 1)) :
    T41.prefixState (extendedState K j) (familyLevel K) = familyState K j := by
  exact fractionState_prefixState (familyDenominator_pos K)
    (familyNumerator_lt_denominator j)

/-- Endpoint slices forming the explicit oriented continuation. -/
def familySymbols (K : ℕ) (j : Fin (K + 1)) : List T39.Symbol :=
  T41.endpointContinuation (extendedState K j) (extendedState_hex_length j)
    (extendedState_decimal_length j) (familyLevel K) (familySteps K) (by rfl)

def familySeparator (K : ℕ) (j : Fin (K + 1)) : List T41.Packet :=
  T41.packetsOfSymbols (familySymbols K j)

theorem familySymbols_length (K : ℕ) (j : Fin (K + 1)) :
    (familySymbols K j).length = familySteps K := by
  exact T41.endpointContinuation_length (extendedState K j)
    (extendedState_hex_length j) (extendedState_decimal_length j)
    (familyLevel K) (familySteps K) (by rfl)

theorem familySeparator_length (K : ℕ) (j : Fin (K + 1)) :
    (familySeparator K j).length = familySteps K := by
  simpa [familySeparator, T41.packetsOfSymbols] using familySymbols_length K j

theorem familySeparator_ne_nil (K : ℕ) (j : Fin (K + 1)) :
    familySeparator K j ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [familySeparator_length] at hlen
  simp only [List.length_nil] at hlen
  exact (Nat.ne_of_gt (familySteps_pos K)) hlen

theorem familySymbols_legalFor (K : ℕ) (j : Fin (K + 1)) :
    T46.LegalContinuationFor (0 : Fin 10) (familyState K j)
      (familySymbols K j) := by
  have hlegal := T46.legal_endpointContinuationFor (0 : Fin 10)
    (extendedState K j) (extendedState_hex_length j)
    (extendedState_decimal_length j)
    (fun _ hi => extendedState_all_prefixes_balancedFor K j hi)
    (familyLevel K) (familySteps K) (by rfl)
  rw [extendedState_prefix_eq_familyState K j] at hlegal
  exact hlegal

theorem familySeparator_tailLegal (K : ℕ) (j : Fin (K + 1)) :
    T46.TailLegal (familyLevel K) (familySeparator K j) :=
  T46.tailLegal_packetsOfSymbols_of_legalFor (familySymbols_legalFor K j)

theorem familySeparator_accepted (K : ℕ) (j : Fin (K + 1)) :
    T46.AcceptedFor (0 : Fin 10) (T41.balancedContext (familyLevel K)) 1
      (familyResidual K j) (familySeparator K j) :=
  T46.acceptedFor_packetsOfSymbols_of_legalFor (0 : Fin 10) 1
    (familySymbols_legalFor K j)

theorem extendedState_decimalTail_eq (K : ℕ) (j : Fin (K + 1)) :
    (extendedState K j).decimalPrefix.drop (familyLength K) =
      List.replicate (familyExtraDigits K) 1 := by
  rw [extendedState_decimalPrefix_eq]
  simp [backgroundMarkerWord_length (family_position_lt j)]

theorem mem_decimalTail_of_mem_endpointContinuation
    (q : T39.State)
    (hhex : q.hexPrefix.length = q.level)
    (hdecimal : q.decimalPrefix.length = T39.decimalLevel q.level)
    (start t : ℕ) (hle : start + t ≤ q.level)
    {a : T39.Symbol}
    (ha : a ∈ T41.endpointContinuation q hhex hdecimal start t hle)
    {x : Fin 10} (hx : x ∈ a.decimal.1) :
    x ∈ q.decimalPrefix.drop (T39.decimalLevel start) := by
  induction t generalizing start with
  | zero => simp [T41.endpointContinuation] at ha
  | succ t ih =>
      simp only [T41.endpointContinuation, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact List.mem_of_mem_take hx
      · have hnext := ih (start := start + 1) (hle := by omega) ha
        have hdrop :
            q.decimalPrefix.drop (T39.decimalLevel (start + 1)) =
              (q.decimalPrefix.drop (T39.decimalLevel start)).drop
                (T39.scheduleIncrement start) := by
          rw [List.drop_drop, T39.decimalLevel_succ]
        rw [hdrop] at hnext
        exact List.mem_of_mem_drop hnext

/-- Every decimal digit in every packet of a continuation is `1`. -/
def AllOnesContinuation (w : List T41.Packet) : Prop :=
  ∀ p ∈ w, ∀ x ∈ p.decimal, x = (1 : Fin 10)

theorem familySymbols_decimal_digits_eq_one (K : ℕ) (j : Fin (K + 1))
    {a : T39.Symbol} (ha : a ∈ familySymbols K j)
    {x : Fin 10} (hx : x ∈ a.decimal.1) : x = (1 : Fin 10) := by
  have htail := mem_decimalTail_of_mem_endpointContinuation
    (extendedState K j) (extendedState_hex_length j)
    (extendedState_decimal_length j) (familyLevel K) (familySteps K)
    (by rfl) ha hx
  have htail' : x ∈ (extendedState K j).decimalPrefix.drop (familyLength K) := by
    simpa [familyLength] using htail
  rw [extendedState_decimalTail_eq] at htail'
  simp only [List.mem_replicate] at htail'
  exact htail'.2

/-- The explicit separator appends only background digit `1`. -/
theorem familySeparator_allOnes (K : ℕ) (j : Fin (K + 1)) :
    AllOnesContinuation (familySeparator K j) := by
  intro p hp x hx
  rw [familySeparator, T41.packetsOfSymbols] at hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  exact familySymbols_decimal_digits_eq_one K j ha hx

theorem advanceContext_familySeparator (K : ℕ) (j : Fin (K + 1)) :
    T41.advanceContext (T41.balancedContext (familyLevel K))
        (familySeparator K j) =
      T41.balancedContext (familyLevel K + familySteps K) := by
  rw [T48.advanceContext_eq_of_tailLegal (familySeparator_tailLegal K j),
    familySeparator_length]

theorem familySeparator_rejected_of_ne (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ T46.AcceptedFor (0 : Fin 10) (T41.balancedContext (familyLevel K)) 1
      (familyResidual K v) (familySeparator K u) := by
  intro hvAccepted
  let c := T41.balancedContext (familyLevel K)
  let qu := familyResidual K u
  let qv := familyResidual K v
  let w := familySeparator K u
  let xu := (T41.runResidual 1 c qu w).reducedCarry
  let xv := (T41.runResidual 1 c qv w).reducedCarry
  let cf := T41.advanceContext c w
  have hwne : w ≠ [] := familySeparator_ne_nil K u
  have huAccepted : T46.AcceptedFor (0 : Fin 10) c 1 qu w :=
    familySeparator_accepted K u
  have hbu : -((cf.a : ℕ) : ℤ) < xu ∧ xu < ((cf.b : ℕ) : ℤ) :=
    T46.acceptedFor_final_bounds hwne huAccepted
  have hbv : -((cf.a : ℕ) : ℤ) < xv ∧ xv < ((cf.b : ℕ) : ℤ) :=
    T46.acceptedFor_final_bounds hwne hvAccepted
  have hctx : cf = T41.balancedContext (familyLevel K + familySteps K) :=
    advanceContext_familySeparator K u
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
    exact huv (family_reducedCarry_injective K hcarry)
  have hdeltaPos : (0 : ℤ) < |qu.reducedCarry - qv.reducedCarry| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hcarryNe)
  have hsub := T41.runResidual_carry_sub 1 c qu qv w
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
  have hwlen : w.length = familySteps K := familySeparator_length K u
  rw [T41.carryMultiplier_eq, hwlen, T41.advanceContext_a] at hproduct
  have hsmall : 16 ^ familySteps K < 11 * c.a := by
    apply (Nat.mul_lt_mul_right (T41.fiveMultiplier_pos w)).mp
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hproduct
  have hlarge := T41.eleven_mul_lt_sixteen_pow (familySteps_pos K)
  have hca : c.a = familySteps K := rfl
  rw [hca] at hsmall
  omega

/-- An explicit all-ones continuation is accepted from `u` and rejected from
every distinct `v`, while following their shared future schedule. -/
theorem family_explicit_allOnes_distinguishingContinuation (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    T46.TailLegal (familyLevel K) (familySeparator K u) ∧
      AllOnesContinuation (familySeparator K u) ∧
      T46.AcceptedFor (0 : Fin 10) (T41.balancedContext (familyLevel K)) 1
        (familyResidual K u) (familySeparator K u) ∧
      ¬ T46.AcceptedFor (0 : Fin 10) (T41.balancedContext (familyLevel K)) 1
        (familyResidual K v) (familySeparator K u) := by
  exact ⟨familySeparator_tailLegal K u, familySeparator_allOnes K u,
    familySeparator_accepted K u, familySeparator_rejected_of_ne K huv⟩

/-- Distinct background-marker residuals have distinct digit-0 languages. -/
theorem family_pairwise_rightLanguage_inequivalent (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ T46.RightLanguageEquivalentAt (0 : Fin 10) (familyLevel K) 1
      (familyResidual K u) (familyResidual K v) := by
  intro hequiv
  have hseparator := family_explicit_allOnes_distinguishingContinuation K huv
  have hmemu : familySeparator K u ∈
      T46.ContinuationLanguageAt (0 : Fin 10) (familyLevel K) 1
        (familyResidual K u) := ⟨hseparator.1, hseparator.2.2.1⟩
  have hmemv : familySeparator K u ∈
      T46.ContinuationLanguageAt (0 : Fin 10) (familyLevel K) 1
        (familyResidual K v) := by
    rw [← hequiv]
    exact hmemu
  exact hseparator.2.2.2 hmemv.2

/-- Every `K` admits `K+1` reachable digit-0 residuals at one external level,
with injective states and pairwise distinct continuation languages. -/
theorem commonLevel_moreThan_pairwise_rightLanguage_inequivalent (K : ℕ) :
    K < Fintype.card (Fin (K + 1)) ∧
      Function.Injective (familyResidual K) ∧
      (∀ j : Fin (K + 1),
        T46.PersistentReachableAt (0 : Fin 10) (familyLevel K)
          (familyResidual K j)) ∧
      ∀ u v : Fin (K + 1), u ≠ v →
        ¬ T46.RightLanguageEquivalentAt (0 : Fin 10) (familyLevel K) 1
          (familyResidual K u) (familyResidual K v) := by
  exact ⟨by simp, familyResidual_injective K, family_persistent_reachableAt K,
    fun _ _ huv => family_pairwise_rightLanguage_inequivalent K huv⟩

/-- Forbidden digit zero has infinite externally clocked continuation-language
index under the persistent residual semantics. -/
theorem digitZero_infiniteContinuationLanguageIndex :
    T46.InfiniteContinuationLanguageIndex (0 : Fin 10) := by
  intro K
  refine ⟨familyLevel K, familyResidual K, by simp, familyResidual_injective K,
    family_persistent_reachableAt K, ?_⟩
  intro u v huv
  exact family_pairwise_rightLanguage_inequivalent K huv

/-- A code preserves the digit-`d` languages when every same-level reachable
collision has equal externally clocked continuation languages. -/
def LanguagePreservingPersistentStateCode (d : Fin 10) {Q : Type*}
    (code : T41.ResidualState → Q) : Prop :=
  ∀ (N : ℕ) (q q' : T41.ResidualState),
    T46.PersistentReachableAt d N q →
      T46.PersistentReachableAt d N q' →
      code q = code q' →
      T46.RightLanguageEquivalentAt d N 1 q q'

theorem no_finite_languagePreserving_persistentStateCode_of_infiniteIndex
    {d : Fin 10} (hindex : T46.InfiniteContinuationLanguageIndex d)
    {Q : Type*} [Finite Q] (code : T41.ResidualState → Q) :
    ¬ LanguagePreservingPersistentStateCode d code := by
  classical
  letI := Fintype.ofFinite Q
  let K := Fintype.card Q
  obtain ⟨N, f, hcard, _hinjective, hreachable, hinequivalent⟩ := hindex K
  let coded : Fin (K + 1) → Q := fun j => code (f j)
  obtain ⟨u, v, huv, hcode⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt coded hcard
  intro hpreserves
  rw [LanguagePreservingPersistentStateCode] at hpreserves
  have hequiv := hpreserves N (f u) (f v) (hreachable u) (hreachable v) (by
    simpa [coded] using hcode)
  exact hinequivalent u v huv hequiv

/-- No code into any finite type preserves all digit-0 continuation languages
of reachable persistent residuals under the shared external clock. -/
theorem no_finite_languagePreserving_persistentStateCode
    {Q : Type*} [Finite Q] (code : T41.ResidualState → Q) :
    ¬ LanguagePreservingPersistentStateCode (0 : Fin 10) code :=
  no_finite_languagePreserving_persistentStateCode_of_infiniteIndex
    digitZero_infiniteContinuationLanguageIndex code

/-- Complete classification for the ten one-digit forbidden sets: every
single decimal digit gives infinite continuation-language index. -/
theorem allTenSingleDigits_infiniteContinuationLanguageIndex (d : Fin 10) :
    T46.InfiniteContinuationLanguageIndex d := by
  fin_cases d
  · exact digitZero_infiniteContinuationLanguageIndex
  · exact T48.digitOne_infiniteContinuationLanguageIndex
  · exact T46.digitTwo_infiniteContinuationLanguageIndex
  · exact T46.digitThree_infiniteContinuationLanguageIndex
  · exact T46.digitFour_infiniteContinuationLanguageIndex
  · exact T46.digitFive_infiniteContinuationLanguageIndex
  · exact T46.digitSix_infiniteContinuationLanguageIndex
  · exact T46.digitSeven_infiniteContinuationLanguageIndex
  · exact T46.digitEight_infiniteContinuationLanguageIndex
  · exact T46.digitNine_infiniteContinuationLanguageIndex

end

end Theory.PiDigits.T50

#print axioms Theory.PiDigits.T50.family_reachableAt
#print axioms Theory.PiDigits.T50.family_persistent_reachableAt
#print axioms Theory.PiDigits.T50.family_reducedCarry_injective
#print axioms Theory.PiDigits.T50.familyResidual_injective
#print axioms Theory.PiDigits.T50.familySeparator_allOnes
#print axioms Theory.PiDigits.T50.family_explicit_allOnes_distinguishingContinuation
#print axioms Theory.PiDigits.T50.family_pairwise_rightLanguage_inequivalent
#print axioms Theory.PiDigits.T50.commonLevel_moreThan_pairwise_rightLanguage_inequivalent
#print axioms Theory.PiDigits.T50.digitZero_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T50.no_finite_languagePreserving_persistentStateCode
#print axioms Theory.PiDigits.T50.allTenSingleDigits_infiniteContinuationLanguageIndex
