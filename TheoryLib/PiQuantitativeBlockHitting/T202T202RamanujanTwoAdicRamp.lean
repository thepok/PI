import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# T202: Ramanujan two-adic valuation and denominator ramp

produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-03 (wave E2, one task per lemma, four parallel), against the contracted
signatures of AllMath task pack t202; gate-checked per task; assembled by Codex
-/

namespace Theory.PiDigits.T202RamanujanDyadicRamp

def binaryDigitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

def centralCube (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

def lambda (n : ℕ) : ℕ :=
  12 * n + 4 - 3 * binaryDigitSum n


lemma digits_two_two_mul_sum (n : ℕ) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have h : Nat.digits 2 (2 * n) = 0 :: Nat.digits 2 n :=
      Nat.digits_base_mul (by norm_num) hpos
    rw [h, List.sum_cons, Nat.zero_add]

theorem centralBinomial_twoAdic (n : ℕ) :
    padicValNat 2 (Nat.choose (2 * n) n) = binaryDigitSum n := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hle : n ≤ 2 * n := by omega
  have key :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n)
      (n := 2 * n) hle
  have hsub : 2 * n - n = n := by omega
  have hdig : (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum :=
    digits_two_two_mul_sum n
  have hone : (2 : ℕ) - 1 = 1 := rfl
  rw [hone, one_mul, hsub, hdig] at key
  have hcancel :
      (Nat.digits 2 n).sum + (Nat.digits 2 n).sum - (Nat.digits 2 n).sum =
        (Nat.digits 2 n).sum := by omega
  rw [hcancel] at key
  simpa [binaryDigitSum] using key

theorem binaryDigitSum_succ (n : ℕ) :
    (binaryDigitSum (n + 1) : ℤ) =
      (binaryDigitSum n : ℤ) + 1 -
        (padicValNat 2 (n + 1) : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hLeg_n : padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum := by
    have h := sub_one_mul_padicValNat_factorial (p := 2) n
    simpa using h
  have hLeg_succ : padicValNat 2 (Nat.factorial (n + 1)) = (n + 1) - (Nat.digits 2 (n + 1)).sum := by
    have h := sub_one_mul_padicValNat_factorial (p := 2) (n + 1)
    simpa using h
  have hfact : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := Nat.factorial_succ n
  have hmul : padicValNat 2 ((n + 1) * Nat.factorial n) =
      padicValNat 2 (n + 1) + padicValNat 2 (Nat.factorial n) :=
    padicValNat.mul (by omega) (Nat.factorial_ne_zero n)
  have hval : padicValNat 2 (Nat.factorial (n + 1)) =
      padicValNat 2 (n + 1) + padicValNat 2 (Nat.factorial n) := by
    rw [hfact] at hLeg_succ ⊢
    -- rewrite goal using hmul; keep hLeg_succ for the value
    exact hmul
  have hle_n : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  have hle_succ : (Nat.digits 2 (n + 1)).sum ≤ n + 1 := Nat.digit_sum_le 2 (n + 1)
  have hs_n : binaryDigitSum n = (Nat.digits 2 n).sum := rfl
  have hs_succ : binaryDigitSum (n + 1) = (Nat.digits 2 (n + 1)).sum := rfl
  rw [hs_n, hs_succ]
  omega

namespace HypothesisForms

theorem centralCube_twoAdic
    (hCentral : ∀ m : ℕ,
      padicValNat 2 (Nat.choose (2 * m) m) = binaryDigitSum m)
    (n : ℕ) :
    padicValNat 2 (centralCube n) = 3 * binaryDigitSum n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
  unfold centralCube
  rw [padicValNat.pow 3 hne, hCentral n]

theorem digitSum_le_self (k : ℕ) : binaryDigitSum k ≤ k := by
  unfold binaryDigitSum
  exact Nat.digit_sum_le 2 k

theorem three_digitSum_le (k : ℕ) : 3 * binaryDigitSum k ≤ 12 * k + 4 := by
  have h := digitSum_le_self k
  omega

theorem lambda_succ
    (hDigitSum : ∀ m : ℕ,
      (binaryDigitSum (m + 1) : ℤ) =
        (binaryDigitSum m : ℤ) + 1 -
          (padicValNat 2 (m + 1) : ℤ))
    (n : ℕ) :
    lambda (n + 1) =
      lambda n + 9 + 3 * padicValNat 2 (n + 1) := by
  have hB1 : 3 * binaryDigitSum n ≤ 12 * n + 4 := three_digitSum_le n
  have hB2 : 3 * binaryDigitSum (n + 1) ≤ 12 * (n + 1) + 4 :=
    three_digitSum_le (n + 1)
  have hInt := hDigitSum n
  have hLam_n : ((lambda n : ℕ) : ℤ) =
      12 * (n : ℤ) + 4 - 3 * (binaryDigitSum n : ℤ) := by
    unfold lambda
    rw [Nat.cast_sub hB1]
    push_cast
    ring
  have hLam_s : ((lambda (n + 1) : ℕ) : ℤ) =
      12 * ((n : ℤ) + 1) + 4 - 3 * ((binaryDigitSum (n + 1) : ℤ)) := by
    unfold lambda
    rw [Nat.cast_sub hB2]
    push_cast
    ring
  have hEq : ((lambda (n + 1) : ℕ) : ℤ) =
      ((lambda n : ℕ) : ℤ) + 9 + 3 * ((padicValNat 2 (n + 1) : ℕ) : ℤ) := by
    rw [hLam_n, hLam_s, hInt]
    ring
  have hCastRHS : ((((lambda n + 9 + 3 * padicValNat 2 (n + 1) : ℕ)) : ℤ) =
      ((lambda n : ℕ) : ℤ) + 9 + 3 * ((padicValNat 2 (n + 1) : ℕ) : ℤ)) := by
    push_cast
    ring
  apply Nat.cast_injective (R := ℤ)
  rw [hCastRHS]
  exact hEq

theorem lambda_strictMono
    (hLambdaSucc : ∀ n : ℕ,
      lambda (n + 1) = lambda n + 9 + 3 * padicValNat 2 (n + 1)) :
    StrictMono lambda := by
  have step : ∀ n : ℕ, lambda n < lambda (n + 1) := by
    intro n
    have h := hLambdaSucc n
    omega
  have ramp : ∀ (d a : ℕ), lambda a < lambda (a + (d + 1)) := by
    intro d
    induction d with
    | zero =>
      intro a
      have h0 : a + (0 + 1) = a + 1 := by omega
      rw [h0]
      exact step a
    | succ d ih =>
      intro a
      have h1 : lambda a < lambda (a + (d + 1)) := ih a
      have h2 : lambda (a + (d + 1)) < lambda (a + (d + 1) + 1) := step _
      have heq : a + (d + 1 + 1) = (a + (d + 1)) + 1 := by omega
      rw [heq]
      exact lt_trans h1 h2
  intro a b hab
  have hle : a ≤ b := Nat.le_of_lt hab
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hkpos : 0 < k := by
    have hlt : a < a + k := hab
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hkpos)
  exact ramp d a

theorem lambda_prefix_ramp
    (hStrict : StrictMono lambda) {m n : ℕ} (hmn : m ≤ n) :
    lambda m ≤ lambda n :=
  hStrict.monotone hmn

end HypothesisForms

theorem centralCube_twoAdic (n : ℕ) :
    padicValNat 2 (centralCube n) = 3 * binaryDigitSum n :=
  HypothesisForms.centralCube_twoAdic centralBinomial_twoAdic n

theorem lambda_succ (n : ℕ) :
    lambda (n + 1) =
      lambda n + 9 + 3 * padicValNat 2 (n + 1) :=
  HypothesisForms.lambda_succ binaryDigitSum_succ n

theorem lambda_strictMono :
    StrictMono lambda :=
  HypothesisForms.lambda_strictMono lambda_succ

theorem lambda_prefix_ramp {m n : ℕ} (hmn : m ≤ n) :
    lambda m ≤ lambda n :=
  HypothesisForms.lambda_prefix_ramp lambda_strictMono hmn

end Theory.PiDigits.T202RamanujanDyadicRamp
