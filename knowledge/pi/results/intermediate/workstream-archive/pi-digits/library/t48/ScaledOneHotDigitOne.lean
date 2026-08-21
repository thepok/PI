import TheoryLib.PiDigits.T37CrossBaseCarry
import TheoryLib.PiDigits.T43CommonLevelResidualIndex
import TheoryLib.PiDigits.T46AllSingleDigitResidualIndex
import Mathlib.Data.Fintype.Pigeonhole

/-!
# T48: scaled one-hot residual index for forbidden digit 1

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file independently formalizes the coefficient-`2` scaled one-hot
construction in T46's externally clocked base-16/base-10 residual system with
decimal digit `1` forbidden. It does not use the unverified T47 note as a
premise.

The external level and future schedule are shared test parameters, not fields
of the persistent residual state. Consequently the finite-code result concerns
only language-preserving persistent-state codes under these externally clocked
semantics. It says nothing about schedule-aware controllers retaining the
external level.

Nothing here concerns forbidden digit `0`, arbitrary forbidden words, the
digits of `Real.pi`, `T37.JMix Real.pi`, canonical V1, or sibling V3.
-/

namespace Theory.PiDigits.T48

open Theory.PiDigits

noncomputable section

/-- A fixed-width decimal word with one digit `2` and all other digits zero. -/
def twoHotWord (length k : ℕ) : List (Fin 10) :=
  List.replicate (length - (k + 1)) 0 ++ [2] ++ List.replicate k 0

theorem twoHotWord_length {length k : ℕ} (hk : k < length) :
    (twoHotWord length k).length = length := by
  simp [twoHotWord]
  omega

theorem twoHotWord_value {length k : ℕ} (_hk : k < length) :
    T37.wordValue (twoHotWord length k) = 2 * 10 ^ k := by
  simp [twoHotWord, T39.wordValue_append, T37.wordValue,
    T39.wordValue_replicate_zero]

theorem twoHotWord_avoids_one (length k : ℕ) :
    T46.AvoidsDigit (1 : Fin 10) (twoHotWord length k) := by
  simp [T46.AvoidsDigit, twoHotWord]

theorem two_mul_pow_lt_pow_of_lt {k length : ℕ} (hk : k < length) :
    2 * 10 ^ k < 10 ^ length := by
  calc
    2 * 10 ^ k < 10 * 10 ^ k := by
      exact (Nat.mul_lt_mul_right (by positivity : 0 < 10 ^ k)).2 (by norm_num)
    _ = 10 ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ 10 ^ length := Nat.pow_le_pow_right (by norm_num) hk

theorem fixedWord_twoHot {length k : ℕ} (hk : k < length) :
    T41.fixedWord 10 length (2 * 10 ^ k) = twoHotWord length k := by
  apply T41.word_eq_of_length_value (by norm_num)
  · rw [T41.fixedWord_length (by norm_num) (two_mul_pow_lt_pow_of_lt hk),
      twoHotWord_length hk]
  · rw [T41.fixedWord_value (by norm_num) (two_mul_pow_lt_pow_of_lt hk),
      twoHotWord_value hk]

/-- Coefficient-`2` replacement for T41's coefficient-`1` decimal value. -/
def scaledDecimalValue (j : ℕ) : ℕ := 2 * 10 ^ (1 + j)

/-- The family uses T46's common external level but different decimal values. -/
def familyLevel (K : ℕ) : ℕ := T41.witnessLevel K 1

theorem scaled_position_lt {K : ℕ} (j : Fin (K + 1)) :
    1 + (j : ℕ) < T39.decimalLevel (familyLevel K) := by
  simpa [familyLevel, T41.witnessDecimalLength] using
    (T41.witness_digit_position_lt (M := K) (r := 1) j)

theorem scaledDecimalValue_lt_pow {K : ℕ} (j : Fin (K + 1)) :
    scaledDecimalValue j < 10 ^ T39.decimalLevel (familyLevel K) := by
  exact two_mul_pow_lt_pow_of_lt (scaled_position_lt j)

theorem scaledDecimalValue_lt_fiveScale {K : ℕ} (j : Fin (K + 1)) :
    scaledDecimalValue j < (T41.balancedContext (familyLevel K)).a := by
  let N := T41.witnessScale K 1
  have hN : 0 < N := by simp [N, T41.witnessScale]
  have hjexp : 1 + (j : ℕ) < N := by
    dsimp [N, T41.witnessScale]
    omega
  have hm : 2 * N ≤ T39.decimalLevel (familyLevel K) := by
    simpa [familyLevel, T41.witnessLevel, N] using
      T41.decimalLevel_self_le (T41.witnessLevel K 1)
  calc
    scaledDecimalValue j = 2 * 10 ^ (1 + (j : ℕ)) := rfl
    _ < 10 ^ ((1 + (j : ℕ)) + 1) := by
      rw [pow_succ]
      have hp : 0 < 10 ^ (1 + (j : ℕ)) := by positivity
      nlinarith
    _ ≤ 10 ^ N := Nat.pow_le_pow_right (by norm_num) hjexp
    _ < 25 ^ N := Nat.pow_lt_pow_left (by norm_num) hN.ne'
    _ = 5 ^ (2 * N) := by rw [show 25 = 5 ^ 2 by norm_num, ← pow_mul]
    _ ≤ 5 ^ T39.decimalLevel (familyLevel K) :=
      Nat.pow_le_pow_right (by norm_num) hm
    _ = (T41.balancedContext (familyLevel K)).a := rfl

/-- The scaled concrete source at the common external level. -/
def familyState (K : ℕ) (j : Fin (K + 1)) : T39.State :=
  T41.rationalState (familyLevel K) (scaledDecimalValue j)

/-- The persistent residual stores no external level. -/
def familyResidual (K : ℕ) (j : Fin (K + 1)) : T41.ResidualState :=
  T41.residualOf 1 (familyState K j)

/-- Direct digit-specific rational-prefix balance. Unlike T46's earlier helper,
this lemma has no digit-2-avoidance premise. -/
theorem rationalState_all_prefixes_balancedFor
    {d : Fin 10} {n D : ℕ}
    (hD : D < 10 ^ T39.decimalLevel n)
    (havoid : T46.AvoidsDigit d
      (T41.fixedWord 10 (T39.decimalLevel n) D))
    {i : ℕ} (hin : i ≤ n) :
    T46.BalancedFor d (T41.prefixState (T41.rationalState n D) i) := by
  have hA := T41.rationalHexValue_lt_pow hD
  have hm := T41.decimalLevel_mono_of_le hin
  have hhexlen : (T41.rationalState n D).hexPrefix.length = n :=
    T41.fixedWord_length (by norm_num) hA
  have hdeclen : (T41.rationalState n D).decimalPrefix.length =
      T39.decimalLevel n := T41.fixedWord_length (by norm_num) hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [T41.prefixState, hhexlen, hin]
  · simp [T41.prefixState, hdeclen, hm]
  · have h := T41.wordValue_lt_pow (by norm_num)
      ((T41.rationalState n D).hexPrefix.take i)
    simpa [T37.ValidPrefix, T41.prefixState, hhexlen, hin] using h
  · have h := T41.wordValue_lt_pow (by norm_num)
      ((T41.rationalState n D).decimalPrefix.take (T39.decimalLevel i))
    simpa [T37.ValidPrefix, T41.prefixState, hdeclen, hm] using h
  · intro hmem
    apply havoid
    exact List.mem_of_mem_take hmem
  · refine ⟨(D : ℝ) / 10 ^ T39.decimalLevel n, ?_, ?_⟩
    · simp only [T41.prefixState]
      rw [T41.rationalState_hexPrefix_value hD hin]
      simpa using T41.natDiv_mem_prefixCylinder 16 i D
        (10 ^ T39.decimalLevel n) (by norm_num) (by positivity)
    · simp only [T41.prefixState]
      rw [T41.rationalState_decimalPrefix_value hD hin]
      simpa using T41.natDiv_mem_prefixCylinder 10 (T39.decimalLevel i) D
        (10 ^ T39.decimalLevel n) (by norm_num) (by positivity)

theorem family_decimalPrefix_avoids_one (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit (1 : Fin 10) (familyState K j).decimalPrefix := by
  rw [familyState]
  change T46.AvoidsDigit (1 : Fin 10)
    (T41.fixedWord 10 (T39.decimalLevel (familyLevel K))
      (scaledDecimalValue j))
  rw [show scaledDecimalValue j = 2 * 10 ^ (1 + (j : ℕ)) by rfl,
    fixedWord_twoHot (scaled_position_lt j)]
  exact twoHotWord_avoids_one _ _

/-- Every coefficient-`2` source is reachable in the digit-1 concrete system. -/
theorem family_reachableFor (K : ℕ) (j : Fin (K + 1)) :
    T46.ReachableFor (1 : Fin 10) (familyState K j) := by
  apply T46.reachableFor_of_all_prefixes_balanced
  · exact T41.fixedWord_length (by norm_num)
      (T41.rationalHexValue_lt_pow (scaledDecimalValue_lt_pow j))
  · exact T41.fixedWord_length (by norm_num) (scaledDecimalValue_lt_pow j)
  · intro i hi
    exact rationalState_all_prefixes_balancedFor
      (scaledDecimalValue_lt_pow j) (family_decimalPrefix_avoids_one K j) hi

/-- Every source is reachable at the same external level. -/
theorem family_reachableAt (K : ℕ) (j : Fin (K + 1)) :
    T46.ReachableAtFor (1 : Fin 10) (familyLevel K) (familyState K j) := by
  exact ⟨family_reachableFor K j, rfl⟩

/-- Every scaled residual is induced by a digit-1 reachable source at the
common external level. -/
theorem family_persistent_reachableAt (K : ℕ) (j : Fin (K + 1)) :
    T46.PersistentReachableAt (1 : Fin 10) (familyLevel K)
      (familyResidual K j) := by
  exact ⟨familyState K j, family_reachableAt K j, rfl⟩

/-- Exact reduced carry of a scaled rational source. -/
theorem family_reducedCarry_eq {K : ℕ} (j : Fin (K + 1)) :
    (familyResidual K j).reducedCarry =
      -(((T41.balancedContext (familyLevel K)).b * scaledDecimalValue j %
        (T41.balancedContext (familyLevel K)).a : ℕ) : ℤ) := by
  have hD := scaledDecimalValue_lt_pow j
  simp only [familyResidual, familyState, T41.residualOf, T41.rationalState]
  rw [T41.fixedWord_value (by norm_num) (T41.rationalHexValue_lt_pow hD),
    T41.fixedWord_value (by norm_num) hD]
  exact T41.reducedCarryAt_rationalHexValue _ _

/-- The reduced carries of the coefficient-`2` family are injective. -/
theorem family_reducedCarry_injective (K : ℕ) :
    Function.Injective (fun j : Fin (K + 1) =>
      (familyResidual K j).reducedCarry) := by
  intro u v huv
  change (familyResidual K u).reducedCarry =
    (familyResidual K v).reducedCarry at huv
  rw [family_reducedCarry_eq, family_reducedCarry_eq] at huv
  have hrem :
      (T41.balancedContext (familyLevel K)).b * scaledDecimalValue u %
          (T41.balancedContext (familyLevel K)).a =
        (T41.balancedContext (familyLevel K)).b * scaledDecimalValue v %
          (T41.balancedContext (familyLevel K)).a := by
    exact_mod_cast neg_inj.mp huv
  have hcop : Nat.gcd (T41.balancedContext (familyLevel K)).a
      (T41.balancedContext (familyLevel K)).b = 1 := by
    simpa [T41.balancedContext] using
      ((by norm_num : Nat.Coprime 5 2).pow
        (T39.decimalLevel (familyLevel K))
        (4 * familyLevel K - T39.decimalLevel (familyLevel K))).gcd_eq_one
  have hmul :
      (T41.balancedContext (familyLevel K)).b * scaledDecimalValue u ≡
        (T41.balancedContext (familyLevel K)).b * scaledDecimalValue v
          [MOD (T41.balancedContext (familyLevel K)).a] := hrem
  have hDmod := hmul.cancel_left_of_coprime hcop
  have hD : scaledDecimalValue u = scaledDecimalValue v :=
    hDmod.eq_of_lt_of_lt (scaledDecimalValue_lt_fiveScale u)
      (scaledDecimalValue_lt_fiveScale v)
  have hp : 10 ^ (1 + (u : ℕ)) = 10 ^ (1 + (v : ℕ)) := by
    simpa [scaledDecimalValue] using hD
  have hexp : 1 + (u : ℕ) = 1 + (v : ℕ) :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 10) hp
  apply Fin.ext
  omega

/-- Residual-state injectivity follows already from reduced-carry injectivity. -/
theorem familyResidual_injective (K : ℕ) :
    Function.Injective (familyResidual K) := by
  intro u v huv
  apply family_reducedCarry_injective K
  exact congrArg T41.ResidualState.reducedCarry huv

/-- The number of continuation packets used for separation. -/
def familySteps (K : ℕ) : ℕ :=
  (T41.balancedContext (familyLevel K)).a

theorem familySteps_pos (K : ℕ) : 0 < familySteps K := by
  simp [familySteps, T41.balancedContext]

/-- Decimal numerator for the same rational point at the extended level. -/
def extendedValue (K : ℕ) (j : Fin (K + 1)) : ℕ :=
  T41.extensionValue (familyLevel K) (familySteps K) (scaledDecimalValue j)

/-- Endpoint whose slices define the explicit oriented continuation. -/
def extendedState (K : ℕ) (j : Fin (K + 1)) : T39.State :=
  T41.rationalState (familyLevel K + familySteps K) (extendedValue K j)

theorem extendedValue_lt_pow {K : ℕ} (j : Fin (K + 1)) :
    extendedValue K j <
      10 ^ T39.decimalLevel (familyLevel K + familySteps K) := by
  exact T41.extensionValue_lt_pow (scaledDecimalValue_lt_pow j)

theorem extendedState_hex_length {K : ℕ} (j : Fin (K + 1)) :
    (extendedState K j).hexPrefix.length = (extendedState K j).level := by
  simpa [extendedState] using T41.fixedWord_length (by norm_num)
    (T41.rationalHexValue_lt_pow (extendedValue_lt_pow j))

set_option maxHeartbeats 2000000 in
theorem extendedState_decimal_length {K : ℕ} (j : Fin (K + 1)) :
    (extendedState K j).decimalPrefix.length =
      T39.decimalLevel (extendedState K j).level := by
  simpa [extendedState] using
    T41.fixedWord_length (by norm_num) (extendedValue_lt_pow j)

theorem extendedValue_eq {K : ℕ} (j : Fin (K + 1)) :
    extendedValue K j =
      2 * 10 ^ (1 + (j : ℕ) + T39.incrementSum (familyLevel K) (familySteps K)) := by
  simp [extendedValue, T41.extensionValue, scaledDecimalValue, pow_add]
  ring

theorem extended_position_lt {K : ℕ} (j : Fin (K + 1)) :
    1 + (j : ℕ) + T39.incrementSum (familyLevel K) (familySteps K) <
      T39.decimalLevel (familyLevel K + familySteps K) := by
  rw [T39.decimalLevel_add_eq]
  have h := scaled_position_lt j
  omega

theorem extendedState_decimalPrefix_avoids_one
    (K : ℕ) (j : Fin (K + 1)) :
    T46.AvoidsDigit (1 : Fin 10) (extendedState K j).decimalPrefix := by
  simp only [extendedState, T41.rationalState]
  change T46.AvoidsDigit (1 : Fin 10)
    (T41.fixedWord 10 (T39.decimalLevel (familyLevel K + familySteps K))
      (extendedValue K j))
  rw [extendedValue_eq j, fixedWord_twoHot (extended_position_lt j)]
  exact twoHotWord_avoids_one _ _

set_option maxHeartbeats 2000000 in
theorem extendedState_all_prefixes_balancedFor
    (K : ℕ) (j : Fin (K + 1)) {i : ℕ}
    (hi : i ≤ (extendedState K j).level) :
    T46.BalancedFor (1 : Fin 10) (T41.prefixState (extendedState K j) i) := by
  simpa [extendedState] using rationalState_all_prefixes_balancedFor
    (d := (1 : Fin 10)) (n := familyLevel K + familySteps K)
    (D := extendedValue K j) (extendedValue_lt_pow j)
    (extendedState_decimalPrefix_avoids_one K j) hi

theorem extendedState_prefix_eq_familyState
    (K : ℕ) (j : Fin (K + 1)) :
    T41.prefixState (extendedState K j) (familyLevel K) = familyState K j := by
  exact T41.rationalExtension_prefixState (scaledDecimalValue_lt_pow j)

/-- Concrete endpoint slices forming the oriented digit-1 continuation. -/
def familySymbols (K : ℕ) (j : Fin (K + 1)) : List T39.Symbol :=
  T41.endpointContinuation (extendedState K j) (extendedState_hex_length j)
    (extendedState_decimal_length j) (familyLevel K) (familySteps K) (by rfl)

/-- The explicit persistent-state packet continuation oriented from `j`. -/
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
  have hzero := congrArg List.length h
  rw [familySeparator_length K j] at hzero
  simp only [List.length_nil] at hzero
  have hp := familySteps_pos K
  omega

/-- The explicit concrete path is digit-1 legal from its oriented source. -/
theorem familySymbols_legalFor (K : ℕ) (j : Fin (K + 1)) :
    T46.LegalContinuationFor (1 : Fin 10) (familyState K j)
      (familySymbols K j) := by
  have hlegal := T46.legal_endpointContinuationFor (1 : Fin 10)
    (extendedState K j) (extendedState_hex_length j)
    (extendedState_decimal_length j)
    (fun _ hi => extendedState_all_prefixes_balancedFor K j hi)
    (familyLevel K) (familySteps K) (by rfl)
  rw [extendedState_prefix_eq_familyState K j] at hlegal
  exact hlegal

/-- The separator follows the one shared future schedule. -/
theorem familySeparator_tailLegal (K : ℕ) (j : Fin (K + 1)) :
    T46.TailLegal (familyLevel K) (familySeparator K j) := by
  exact T46.tailLegal_packetsOfSymbols_of_legalFor (familySymbols_legalFor K j)

/-- The separator is accepted from its oriented scaled residual. -/
theorem familySeparator_accepted (K : ℕ) (j : Fin (K + 1)) :
    T46.AcceptedFor (1 : Fin 10) (T41.balancedContext (familyLevel K)) 1
      (familyResidual K j) (familySeparator K j) := by
  exact T46.acceptedFor_packetsOfSymbols_of_legalFor (1 : Fin 10) 1
    (familySymbols_legalFor K j)

/-- Tail legality alone determines the final balanced clock context. -/
theorem advanceContext_eq_of_tailLegal {N : ℕ} {w : List T41.Packet}
    (hw : T46.TailLegal N w) :
    T41.advanceContext (T41.balancedContext N) w =
      T41.balancedContext (N + w.length) := by
  induction w generalizing N with
  | nil => simp [T41.advanceContext]
  | cons p w ih =>
      rw [T46.TailLegal] at hw
      simp only [T41.advanceContext, List.length_cons]
      have hnext : T41.nextContext (T41.balancedContext N) p.width =
          T41.balancedContext (N + 1) := by
        rw [hw.1]
        exact T41.nextContext_balanced N
      rw [hnext, ih hw.2]
      congr 1
      omega

theorem advanceContext_familySeparator (K : ℕ) (j : Fin (K + 1)) :
    T41.advanceContext (T41.balancedContext (familyLevel K))
        (familySeparator K j) =
      T41.balancedContext (familyLevel K + familySteps K) := by
  rw [advanceContext_eq_of_tailLegal (familySeparator_tailLegal K j),
    familySeparator_length]

/-- Carry growth makes the oriented separator fail from every other scaled
residual. -/
theorem familySeparator_rejected_of_ne (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ T46.AcceptedFor (1 : Fin 10) (T41.balancedContext (familyLevel K)) 1
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
  have huAccepted : T46.AcceptedFor (1 : Fin 10) c 1 qu w :=
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

/-- Named explicit separator theorem: one concrete continuation follows the
shared schedule, is accepted from `u`, and rejected from every distinct `v`. -/
theorem family_explicit_distinguishingContinuation (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    T46.TailLegal (familyLevel K) (familySeparator K u) ∧
      T46.AcceptedFor (1 : Fin 10) (T41.balancedContext (familyLevel K)) 1
        (familyResidual K u) (familySeparator K u) ∧
      ¬ T46.AcceptedFor (1 : Fin 10) (T41.balancedContext (familyLevel K)) 1
        (familyResidual K v) (familySeparator K u) := by
  exact ⟨familySeparator_tailLegal K u, familySeparator_accepted K u,
    familySeparator_rejected_of_ne K huv⟩

/-- Distinct scaled residuals have distinct digit-1 continuation languages. -/
theorem family_pairwise_rightLanguage_inequivalent (K : ℕ)
    {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ T46.RightLanguageEquivalentAt (1 : Fin 10) (familyLevel K) 1
      (familyResidual K u) (familyResidual K v) := by
  intro hequiv
  have hseparator := family_explicit_distinguishingContinuation K huv
  have hmemu : familySeparator K u ∈
      T46.ContinuationLanguageAt (1 : Fin 10) (familyLevel K) 1
        (familyResidual K u) := ⟨hseparator.1, hseparator.2.1⟩
  have hmemv : familySeparator K u ∈
      T46.ContinuationLanguageAt (1 : Fin 10) (familyLevel K) 1
        (familyResidual K v) := by
    rw [← hequiv]
    exact hmemu
  exact hseparator.2.2 hmemv.2

/-- For every `K`, one common level contains `K+1` reachable, injective,
pairwise continuation-language-distinct persistent residuals. -/
theorem commonLevel_moreThan_pairwise_rightLanguage_inequivalent (K : ℕ) :
    K < Fintype.card (Fin (K + 1)) ∧
      Function.Injective (familyResidual K) ∧
      (∀ j : Fin (K + 1),
        T46.PersistentReachableAt (1 : Fin 10) (familyLevel K)
          (familyResidual K j)) ∧
      ∀ u v : Fin (K + 1), u ≠ v →
        ¬ T46.RightLanguageEquivalentAt (1 : Fin 10) (familyLevel K) 1
          (familyResidual K u) (familyResidual K v) := by
  exact ⟨by simp, familyResidual_injective K, family_persistent_reachableAt K,
    fun _ _ huv => family_pairwise_rightLanguage_inequivalent K huv⟩

/-- The coefficient-`2` family gives infinite continuation-language index for
the structural system with forbidden digit `1`. -/
theorem digitOne_infiniteContinuationLanguageIndex :
    T46.InfiniteContinuationLanguageIndex (1 : Fin 10) := by
  intro K
  refine ⟨familyLevel K, familyResidual K, by simp, familyResidual_injective K,
    family_persistent_reachableAt K, ?_⟩
  intro u v huv
  exact family_pairwise_rightLanguage_inequivalent K huv

/-- A persistent-state code preserves the digit-1 languages when every
same-level reachable collision has equal externally clocked languages. -/
def LanguagePreservingCode {Q : Type*} (code : T41.ResidualState → Q) : Prop :=
  ∀ (N : ℕ) (q q' : T41.ResidualState),
    T46.PersistentReachableAt (1 : Fin 10) N q →
      T46.PersistentReachableAt (1 : Fin 10) N q' →
      code q = code q' →
      T46.RightLanguageEquivalentAt (1 : Fin 10) N 1 q q'

/-- No code into any finite type preserves all digit-1 continuation languages
of reachable persistent residuals under the shared external clock. -/
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
  have hequiv := hpreserves (familyLevel K) (familyResidual K u)
    (familyResidual K v) (family_persistent_reachableAt K u)
    (family_persistent_reachableAt K v) (by simpa [f] using hcode)
  exact family_pairwise_rightLanguage_inequivalent K huv hequiv

/-- Cardinality-indexed finite-quotient impossibility. -/
theorem no_cardinalityK_languagePreserving_persistentStateCode
    {Q : Type*} [Fintype Q] (K : ℕ) (_hcard : Fintype.card Q = K)
    (code : T41.ResidualState → Q) :
    ¬ LanguagePreservingCode code := by
  exact no_finite_languagePreserving_persistentStateCode code

end

end Theory.PiDigits.T48

#print axioms Theory.PiDigits.T48.family_reachableAt
#print axioms Theory.PiDigits.T48.family_persistent_reachableAt
#print axioms Theory.PiDigits.T48.family_reducedCarry_injective
#print axioms Theory.PiDigits.T48.familyResidual_injective
#print axioms Theory.PiDigits.T48.family_explicit_distinguishingContinuation
#print axioms Theory.PiDigits.T48.family_pairwise_rightLanguage_inequivalent
#print axioms Theory.PiDigits.T48.commonLevel_moreThan_pairwise_rightLanguage_inequivalent
#print axioms Theory.PiDigits.T48.digitOne_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T48.no_finite_languagePreserving_persistentStateCode
#print axioms Theory.PiDigits.T48.no_cardinalityK_languagePreserving_persistentStateCode
