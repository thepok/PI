import TheoryLib.PiQuantitativeBlockHitting.T202T202RamanujanTwoAdicRamp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# T203: failure of the direct Ramanujan positive-tail carry criterion

produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-04 (wave E3 rerun, one task per lemma), against the contracted
signatures of AllMath task pack t203; gate-checked per task; assembled by Codex
-/

noncomputable section
namespace Theory.PiDigits.T203RamanujanCarryFailure

open T202RamanujanDyadicRamp

def ramanujanTerm (n : ℕ) : ℝ :=
  ((centralCube n : ℕ) : ℝ) * (42 * n + 5) /
    (2 : ℝ) ^ (12 * n + 4)

def IsInteger (x : ℝ) : Prop := ∃ z : ℤ, x = z

theorem sum_range_choose_aux (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose n m = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfront := Finset.sum_range_succ' (fun k => Nat.choose (n + 1) k) (n + 1)
    simp only at hfront
    have hpascal : (∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1) (k + 1))
        = (∑ k ∈ Finset.range (n + 1), Nat.choose n k)
          + (∑ k ∈ Finset.range (n + 1), Nat.choose n (k + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      exact Nat.choose_succ_succ' n k
    have hback := Finset.sum_range_succ' (fun k => Nat.choose n k) (n + 1)
    simp only at hback
    have hpop := Finset.sum_range_succ (fun k => Nat.choose n k) (n + 1)
    simp only at hpop
    have h0 : Nat.choose n 0 = 1 := Nat.choose_zero_right n
    have h0' : Nat.choose (n + 1) 0 = 1 := Nat.choose_zero_right (n + 1)
    have hlast : Nat.choose n (n + 1) = 0 := by simp
    have hS2 : (∑ k ∈ Finset.range (n + 1), Nat.choose n (k + 1)) + 1 = 2 ^ n := by
      have hback' : (∑ k ∈ Finset.range (n + 1), Nat.choose n (k + 1))
          + Nat.choose n 0
          = ∑ k ∈ Finset.range (n + 1 + 1), Nat.choose n k := hback.symm
      rw [h0] at hback'
      rw [hpop, hlast, add_zero, ih] at hback'
      exact hback'
    have hpow : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ, mul_two]
    have hgoal : ∑ m ∈ Finset.range (n + 1 + 1), Nat.choose (n + 1) m
        = (∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1) (k + 1))
          + Nat.choose (n + 1) 0 := hfront
    rw [hgoal, hpascal, h0', ih, hpow]
    omega

theorem pow_four_le_card_mul_centralBinom (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * Nat.choose (2 * n) n := by
  have hsum : ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m
      = 2 ^ (2 * n) := sum_range_choose_aux (2 * n)
  have hhalf : (2 * n) / 2 = n := by omega
  have hle : ∀ k ∈ Finset.range (2 * n + 1),
      Nat.choose (2 * n) k ≤ Nat.choose (2 * n) n := by
    intro k _
    have h := Nat.choose_le_middle k (2 * n)
    rwa [hhalf] at h
  have hbound : ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m
      ≤ (Finset.range (2 * n + 1)).card • Nat.choose (2 * n) n :=
    Finset.sum_le_card_nsmul _ _ _ hle
  rw [Finset.card_range] at hbound
  rw [hsum] at hbound
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4]
  simpa [nsmul_eq_mul] using hbound

theorem ramanujanTerm_nonneg (n : ℕ) :
    0 ≤ ramanujanTerm n := by
  unfold ramanujanTerm
  apply div_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg _
    · positivity
  · positivity

lemma centralCube_le (n : ℕ) : centralCube n ≤ 2 ^ (6 * n) := by
  have hC : Nat.choose (2 * n) n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
  have h := Nat.pow_le_pow_left hC 3
  have hexp : (2 * n) * 3 = 6 * n := by ring
  have heq : ((2 ^ (2 * n)) ^ 3 : ℕ) = 2 ^ (6 * n) := by rw [← pow_mul, hexp]
  unfold centralCube
  rwa [heq] at h

lemma centralCube_real_le (n : ℕ) : ((centralCube n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (6 * n) := by
  have h := centralCube_le n
  have h2 : ((centralCube n : ℕ) : ℝ) ≤ (((2 ^ (6 * n) : ℕ)) : ℝ) := by
    exact_mod_cast h
  simpa using h2

lemma linear_le (n : ℕ) : 42 * (n : ℝ) + 5 ≤ 47 * (2 : ℝ) ^ n := by
  have h1 : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    have h : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : ((n : ℕ) : ℝ) ≤ (((2 ^ n : ℕ)) : ℝ) := by exact_mod_cast h.le
    simpa using h2
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : ((1 : ℕ) : ℝ) ≤ (((2 ^ n : ℕ)) : ℝ) := by exact_mod_cast h
    simpa using h2
  have hmul : 42 * (n : ℝ) ≤ 42 * (2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hfive : (5 : ℝ) ≤ 5 * (2 : ℝ) ^ n := by
    calc (5 : ℝ) = 5 * 1 := by ring
    _ ≤ 5 * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left h3 (by norm_num)
  linarith

lemma term_nonneg (n : ℕ) : 0 ≤ ramanujanTerm n := by
  unfold ramanujanTerm
  apply div_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg _
    · positivity
  · exact le_of_lt (pow_pos (by norm_num) _)

lemma term_le_major (n : ℕ) :
    ramanujanTerm n ≤ (47 / 16 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
  have hC := centralCube_real_le n
  have hL := linear_le n
  have hLnn : (0 : ℝ) ≤ 42 * (n : ℝ) + 5 := by positivity
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (12 * n + 4) := pow_pos (by norm_num) _
  have hnum : ((centralCube n : ℕ) : ℝ) * (42 * (n : ℝ) + 5)
      ≤ (2 : ℝ) ^ (6 * n) * (47 * (2 : ℝ) ^ n) :=
    mul_le_mul hC hL hLnn (pow_nonneg (by norm_num) _)
  have hfrac : ramanujanTerm n
      ≤ ((2 : ℝ) ^ (6 * n) * (47 * (2 : ℝ) ^ n)) / (2 : ℝ) ^ (12 * n + 4) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hpos)
  have e1 : 6 * n + n = 7 * n := by ring
  have e2 : 7 * n + (5 * n + 4) = 12 * n + 4 := by ring
  have hA : (2 : ℝ) ^ (6 * n) * (2 : ℝ) ^ n = (2 : ℝ) ^ (7 * n) := by
    rw [← pow_add, e1]
  have hB : (2 : ℝ) ^ (7 * n) * (2 : ℝ) ^ (5 * n + 4) = (2 : ℝ) ^ (12 * n + 4) := by
    rw [← pow_add, e2]
  have hnum2 : (2 : ℝ) ^ (6 * n) * (47 * (2 : ℝ) ^ n) = 47 * (2 : ℝ) ^ (7 * n) := by
    calc (2 : ℝ) ^ (6 * n) * (47 * (2 : ℝ) ^ n)
        = 47 * ((2 : ℝ) ^ (6 * n) * (2 : ℝ) ^ n) := by ring
    _ = 47 * (2 : ℝ) ^ (7 * n) := by rw [hA]
  have hX : (2 : ℝ) ^ (7 * n) ≠ 0 := ne_of_gt (pow_pos (by norm_num) _)
  have hcancel : (47 * (2 : ℝ) ^ (7 * n)) / ((2 : ℝ) ^ (7 * n) * (2 : ℝ) ^ (5 * n + 4))
      = 47 / (2 : ℝ) ^ (5 * n + 4) := by
    rw [mul_comm (47 : ℝ) _, mul_div_mul_left _ _ hX]
  have hmid : ramanujanTerm n ≤ 47 / (2 : ℝ) ^ (5 * n + 4) := by
    rw [hnum2, ← hB] at hfrac
    rwa [hcancel] at hfrac
  have hRHS : (47 / 16 : ℝ) * ((1 / 2 : ℝ) ^ n) = 47 / (16 * (2 : ℝ) ^ n) := by
    rw [one_div_pow, div_mul_div_comm, mul_one]
  have hpowmono : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (5 * n) := by
    have h : (2 : ℕ) ^ n ≤ (2 : ℕ) ^ (5 * n) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (((2 ^ n : ℕ)) : ℝ) ≤ (((2 ^ (5 * n) : ℕ)) : ℝ) := by
      exact_mod_cast h
    simpa using h2
  have hsplit : (2 : ℝ) ^ (5 * n + 4) = 16 * (2 : ℝ) ^ (5 * n) := by
    have h16 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
    have hpa : (2 : ℝ) ^ (5 * n + 4) = (2 : ℝ) ^ (5 * n) * (2 : ℝ) ^ 4 := by
      rw [pow_add]
    rw [hpa, h16]
    ring
  have hden : (16 : ℝ) * (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (5 * n + 4) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hpowmono (by norm_num)
  have hsmall : (0 : ℝ) < 16 * (2 : ℝ) ^ n :=
    mul_pos (by norm_num) (pow_pos (by norm_num) _)
  have hfin : (47 : ℝ) / (2 : ℝ) ^ (5 * n + 4)
      ≤ (47 / 16 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
    have h1 : (1 : ℝ) / (2 : ℝ) ^ (5 * n + 4) ≤ 1 / (16 * (2 : ℝ) ^ n) :=
      one_div_le_one_div_of_le hsmall hden
    have h2 : (47 : ℝ) * (1 / (2 : ℝ) ^ (5 * n + 4))
        ≤ 47 * (1 / (16 * (2 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    rw [hRHS, div_eq_mul_one_div (47 : ℝ) _, div_eq_mul_one_div (47 : ℝ) _]
    exact h2
  exact le_trans hmid hfin

lemma half_sum_eq (n : ℕ) :
    ∑ i ∈ Finset.range n, ((1 / 2 : ℝ) ^ i) = 2 - 2 * ((1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, pow_zero]
    norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma half_le (n : ℕ) : ∑ i ∈ Finset.range n, ((1 / 2 : ℝ) ^ i) ≤ 2 := by
  rw [half_sum_eq]
  have hnn : (0 : ℝ) ≤ 2 * ((1 / 2 : ℝ) ^ n) :=
    mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
  linarith

lemma summable_half : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) :=
  summable_of_sum_range_le (fun n => pow_nonneg (by norm_num) n) (fun n => half_le n)

lemma summable_major :
    Summable (fun n : ℕ => (47 / 16 : ℝ) * ((1 / 2 : ℝ) ^ n)) :=
  Summable.mul_left _ summable_half

theorem summable_ramanujanTerm :
    Summable ramanujanTerm :=
  Summable.of_nonneg_of_le (fun n => term_nonneg n) (fun n => term_le_major n)
    summable_major

lemma digitSum_le (k : ℕ) : binaryDigitSum k ≤ k :=
  HypothesisForms.digitSum_le_self k

lemma three_digitSum_le' (k : ℕ) : 3 * binaryDigitSum k ≤ 12 * k + 4 :=
  HypothesisForms.three_digitSum_le k

lemma lambda_add_three (N : ℕ) :
    lambda N + 3 * binaryDigitSum N = 12 * N + 4 := by
  have h := three_digitSum_le' N
  unfold lambda
  omega

lemma lambda_add_split (N : ℕ) :
    lambda N + (12 + 3 * binaryDigitSum N) = 12 * (N + 1) + 4 := by
  have h := lambda_add_three N
  omega

lemma lin_le_pow_of_ge (n : ℕ) (hn : 5 ≤ n) : 2 * n + 3 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hmul : 2 * (2 * m + 3) ≤ 2 * (2 ^ m) :=
      Nat.mul_le_mul_left 2 ih
    have hpow : 2 ^ (m + 1) = 2 * (2 ^ m) := by
      rw [pow_succ, Nat.mul_comm]
    omega

lemma lin_le_pow {N : ℕ} (hN : 10 ≤ N) : 2 * N + 3 ≤ 2 ^ N :=
  lin_le_pow_of_ge N (by omega)

namespace HypothesisForms

theorem cleared_first_omitted_gt_one
    (hBinom : ∀ n : ℕ,
      4 ^ n ≤ (2 * n + 1) * Nat.choose (2 * n) n)
    {N : ℕ} (hN : 10 ≤ N) :
    1 < (2 : ℝ) ^ (lambda N) * ramanujanTerm (N + 1) := by
  set s : ℕ := binaryDigitSum N with hs
  set C : ℕ := Nat.choose (2 * (N + 1)) (N + 1) with hC
  set B : ℕ := 2 * N + 3 with hB
  set L : ℝ := 42 * ((N + 1 : ℕ) : ℝ) + 5 with hL
  have hsN : s ≤ N := digitSum_le N
  have hlam : lambda N + (12 + 3 * s) = 12 * (N + 1) + 4 :=
    lambda_add_split N
  have hlin : B ≤ 2 ^ N := lin_le_pow hN
  have hB_eq : 2 * (N + 1) + 1 = B := by omega
  have hbinomN := hBinom (N + 1)
  rw [hB_eq] at hbinomN
  have hbinomR : ((4 ^ (N + 1) : ℕ) : ℝ) ≤ (B : ℝ) * (C : ℝ) := by
    have h : ((4 ^ (N + 1) : ℕ) : ℝ) ≤ (((B * C : ℕ)) : ℝ) := by
      exact_mod_cast hbinomN
    push_cast at h ⊢
    linarith
  have hBposR : (0 : ℝ) < (B : ℝ) := by
    have hBpos : 0 < B := by omega
    exact_mod_cast hBpos
  have hCposN : 0 < C := by
    rw [hC]
    exact Nat.choose_pos (by omega : N + 1 ≤ 2 * (N + 1))
  have hCposR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCposN
  have hLpos : (0 : ℝ) < L := by
    have hcast : ((N + 1 : ℕ) : ℝ) = ((N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hL, hcast]
    have h10 : (10 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
    linarith
  have hL64 : (64 : ℝ) < L := by
    have hcast : ((N + 1 : ℕ) : ℝ) = ((N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hL, hcast]
    have h10 : (10 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
    linarith
  have hB_le_pow : (B : ℝ) ≤ (2 : ℝ) ^ N := by
    have h : ((B : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast hlin
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have hB3_le : (B : ℝ) ^ 3 ≤ (2 : ℝ) ^ (3 * N) := by
    have h1 : (B : ℝ) ^ 3 ≤ ((2 : ℝ) ^ N) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hB_le_pow 3
    have h2 : ((2 : ℝ) ^ N) ^ 3 = (2 : ℝ) ^ (3 * N) := by
      rw [← pow_mul, Nat.mul_comm]
    rwa [h2] at h1
  have hexp_le : 12 + 3 * s ≤ 12 + 3 * N := by omega
  have h2pow_le : (2 : ℝ) ^ (12 + 3 * s) ≤ (2 : ℝ) ^ (12 + 3 * N) :=
    pow_le_pow_right₀ (by norm_num) hexp_le
  have h1 : (2 : ℝ) ^ (12 + 3 * s) * (B : ℝ) ^ 3
      < (2 : ℝ) ^ (6 * N + 6) * L := by
    have hprod : (2 : ℝ) ^ (12 + 3 * s) * (B : ℝ) ^ 3
        ≤ (2 : ℝ) ^ (12 + 3 * N) * (2 : ℝ) ^ (3 * N) :=
      mul_le_mul h2pow_le hB3_le (by positivity) (by positivity)
    have hpow_eq : (2 : ℝ) ^ (12 + 3 * N) * (2 : ℝ) ^ (3 * N)
        = (2 : ℝ) ^ (6 * N + 6) * 64 := by
      have e1 : 12 + 3 * N + 3 * N = (6 * N + 6) + 6 := by omega
      have hsplit : (2 : ℝ) ^ (12 + 3 * N) * (2 : ℝ) ^ (3 * N)
          = (2 : ℝ) ^ (12 + 3 * N + 3 * N) := by rw [← pow_add]
      rw [hsplit, e1, pow_add]
      norm_num
    have h64 : (2 : ℝ) ^ (6 * N + 6) * 64 < (2 : ℝ) ^ (6 * N + 6) * L :=
      mul_lt_mul_of_pos_left hL64 (by positivity)
    linarith [hprod, hpow_eq, h64]
  have h2 : (2 : ℝ) ^ (6 * N + 6) ≤ (B : ℝ) ^ 3 * (C : ℝ) ^ 3 := by
    have hcube : ((4 ^ (N + 1) : ℕ) : ℝ) ^ 3 ≤ ((B : ℝ) * (C : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hbinomR 3
    have hLHS : ((4 ^ (N + 1) : ℕ) : ℝ) ^ 3 = (2 : ℝ) ^ (6 * N + 6) := by
      have h4 : ((4 ^ (N + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (N + 1)) := by
        rw [Nat.cast_pow]
        have h42 : ((4 : ℕ) : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        rw [h42, ← pow_mul]
      rw [h4, ← pow_mul]
      congr 1
      omega
    have hRHS : ((B : ℝ) * (C : ℝ)) ^ 3 = (B : ℝ) ^ 3 * (C : ℝ) ^ 3 := by
      ring
    linarith [hcube, hLHS, hRHS]
  have hB3pos : (0 : ℝ) < (B : ℝ) ^ 3 := by positivity
  have h3 : (2 : ℝ) ^ (12 + 3 * s) < (C : ℝ) ^ 3 * L := by
    have h2L : (2 : ℝ) ^ (6 * N + 6) * L ≤ (B : ℝ) ^ 3 * (C : ℝ) ^ 3 * L :=
      mul_le_mul_of_nonneg_right h2 hLpos.le
    have hmul : (B : ℝ) ^ 3 * ((C : ℝ) ^ 3 * L)
        = (B : ℝ) ^ 3 * (C : ℝ) ^ 3 * L := by ring
    have hlt : (B : ℝ) ^ 3 * ((2 : ℝ) ^ (12 + 3 * s))
        < (B : ℝ) ^ 3 * ((C : ℝ) ^ 3 * L) := by
      have h1' : (2 : ℝ) ^ (12 + 3 * s) * (B : ℝ) ^ 3
          < (B : ℝ) ^ 3 * (C : ℝ) ^ 3 * L := by linarith [h1, h2L]
      have hcomm : (2 : ℝ) ^ (12 + 3 * s) * (B : ℝ) ^ 3
          = (B : ℝ) ^ 3 * ((2 : ℝ) ^ (12 + 3 * s)) := by ring
      linarith [h1', hmul, hcomm]
    exact (mul_lt_mul_iff_right₀ hB3pos).mp hlt
  have hD_eq : (2 : ℝ) ^ (12 * (N + 1) + 4)
      = (2 : ℝ) ^ (lambda N) * (2 : ℝ) ^ (12 + 3 * s) := by
    rw [← pow_add, hlam]
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ (12 * (N + 1) + 4) := by positivity
  have h2lam_pos : (0 : ℝ) < (2 : ℝ) ^ (lambda N) := by positivity
  have hcc : ((centralCube (N + 1) : ℕ) : ℝ) = (C : ℝ) ^ 3 := by
    rw [hC]
    unfold centralCube
    push_cast
    ring
  have hterm : ramanujanTerm (N + 1)
      = (C : ℝ) ^ 3 * L / (2 : ℝ) ^ (12 * (N + 1) + 4) := by
    have hbase : ramanujanTerm (N + 1)
        = ((centralCube (N + 1) : ℕ) : ℝ) * (42 * (((N + 1 : ℕ)) : ℝ) + 5)
          / (2 : ℝ) ^ (12 * (N + 1) + 4) := rfl
    rw [hbase, hcc, hL]
  have hDlt : (2 : ℝ) ^ (12 * (N + 1) + 4)
      < (2 : ℝ) ^ (lambda N) * ((C : ℝ) ^ 3 * L) := by
    rw [hD_eq]
    exact mul_lt_mul_of_pos_left h3 h2lam_pos
  have hgoal : 1 < (2 : ℝ) ^ (lambda N) * ramanujanTerm (N + 1) := by
    rw [hterm]
    have hC3L_pos : (0 : ℝ) < (C : ℝ) ^ 3 * L :=
      mul_pos (pow_pos hCposR 3) hLpos
    have hnum_pos : (0 : ℝ) < (2 : ℝ) ^ (lambda N) * ((C : ℝ) ^ 3 * L) :=
      mul_pos h2lam_pos hC3L_pos
    have h_eq : (2 : ℝ) ^ (lambda N) * ((C : ℝ) ^ 3 * L / (2 : ℝ) ^ (12 * (N + 1) + 4))
        = ((2 : ℝ) ^ (lambda N) * ((C : ℝ) ^ 3 * L)) / (2 : ℝ) ^ (12 * (N + 1) + 4) := by
      ring
    rw [h_eq, one_lt_div hDpos]
    exact hDlt
  exact hgoal

end HypothesisForms

theorem cleared_first_omitted_gt_one
    {N : ℕ} (hN : 10 ≤ N) :
    1 < (2 : ℝ) ^ (lambda N) * ramanujanTerm (N + 1) :=
  HypothesisForms.cleared_first_omitted_gt_one
    pow_four_le_card_mul_centralBinom hN

theorem dvd_of_mul_odd (a M W : ℕ) (hW : Odd W) (h : 2 ^ a ∣ M * W) :
    2 ^ a ∣ M := by
  induction a generalizing M with
  | zero => exact one_dvd M
  | succ a ih =>
    have hprime : Prime (2 : ℕ) := Nat.prime_two.prime
    have h2dvd : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (Nat.succ_ne_zero a)
    have h2m : 2 ∣ M * W := dvd_trans h2dvd h
    have hor := hprime.dvd_mul.mp h2m
    have hnotW : ¬ 2 ∣ W := by
      rintro ⟨k, hk⟩
      obtain ⟨j, hj⟩ := hW
      omega
    have h2M : 2 ∣ M := by
      rcases hor with hMl | hWr
      · exact hMl
      · exact absurd hWr hnotW
    obtain ⟨M', rfl⟩ := h2M
    obtain ⟨k, hk⟩ := h
    have hk2 : 2 * (M' * W) = 2 * (2 ^ a * k) := by
      have e1 : 2 * (M' * W) = (2 * M') * W := by ring
      have e2 : (2 * M') * W = 2 ^ (a + 1) * k := hk
      have e3 : 2 ^ (a + 1) * k = 2 * (2 ^ a * k) := by rw [pow_succ]; ring
      rw [e1, e2, e3]
    have hred : 2 ^ a ∣ M' * W := by
      have hcancel : M' * W = 2 ^ a * k :=
        mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hk2
      exact ⟨k, hcancel⟩
    obtain ⟨t, ht⟩ := ih M' hred
    exact ⟨t, by rw [ht, pow_succ]; ring⟩

theorem prefix_integral_implies_dyadic_divisibility
    {M N : ℕ}
    (hInt : ∀ n : ℕ, n ≤ N →
      IsInteger ((M : ℝ) * ramanujanTerm n)) :
    2 ^ (lambda N) ∣ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCube : padicValNat 2 (centralCube N) = 3 * binaryDigitSum N :=
    centralCube_twoAdic N
  have hB := HypothesisForms.three_digitSum_le N
  have hE : lambda N + 3 * binaryDigitSum N = 12 * N + 4 := by
    unfold lambda
    omega
  have hc_ne : centralCube N ≠ 0 := by
    unfold centralCube
    apply pow_ne_zero
    exact (Nat.choose_pos (by omega : N ≤ 2 * N)).ne'
  have h2pow : 2 ^ (3 * binaryDigitSum N) ∣ centralCube N := by
    have h := pow_padicValNat_dvd (p := 2) (n := centralCube N)
    rw [hCube] at h
    exact h
  obtain ⟨t, ht⟩ := h2pow
  have ht_notdvd : ¬ 2 ∣ t := by
    intro hd
    obtain ⟨k, hk⟩ := hd
    have hdiv : 2 ^ (3 * binaryDigitSum N + 1) ∣ centralCube N := by
      have heq : centralCube N = 2 ^ (3 * binaryDigitSum N + 1) * k := by
        rw [ht, hk, pow_succ]
        ring
      exact ⟨k, heq⟩
    have hle : 3 * binaryDigitSum N + 1 ≤ padicValNat 2 (centralCube N) :=
      (padicValNat_dvd_iff_le hc_ne).mp hdiv
    rw [hCube] at hle
    omega
  have ht_odd : Odd t := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have ho_odd : Odd (42 * N + 5) := ⟨21 * N + 2, by ring⟩
  have hWodd : Odd (t * (42 * N + 5)) := ht_odd.mul ho_odd
  have hNatDvd : 2 ^ (12 * N + 4) ∣ M * centralCube N * (42 * N + 5) := by
    obtain ⟨z, hz⟩ := hInt N le_rfl
    unfold ramanujanTerm at hz
    have hPowNe : (2 : ℝ) ^ (12 * N + 4) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hz2 : ((M : ℝ) * (((centralCube N : ℕ) : ℝ) * (42 * (N : ℝ) + 5))) /
        (2 : ℝ) ^ (12 * N + 4) = (z : ℝ) := by
      have h := hz
      rwa [← mul_div_assoc] at h
    have hz3 : (M : ℝ) * (((centralCube N : ℕ) : ℝ) * (42 * (N : ℝ) + 5)) =
        (z : ℝ) * (2 : ℝ) ^ (12 * N + 4) := by
      rw [← hz2, div_mul_cancel₀ _ hPowNe]
    have hcastL : ((M * centralCube N * (42 * N + 5) : ℕ) : ℝ) =
        (M : ℝ) * (((centralCube N : ℕ) : ℝ) * (42 * (N : ℝ) + 5)) := by
      push_cast
      ring
    have hcastR : ((2 ^ (12 * N + 4) : ℕ) : ℝ) = (2 : ℝ) ^ (12 * N + 4) := by
      simp
    have hEq : ((M * centralCube N * (42 * N + 5) : ℕ) : ℝ) =
        (z : ℝ) * ((2 ^ (12 * N + 4) : ℕ) : ℝ) := by
      rw [hcastL, hcastR, hz3]
    have hDpos : (0 : ℝ) < ((2 ^ (12 * N + 4) : ℕ) : ℝ) := by
      rw [hcastR]
      positivity
    have hProd_nonneg : (0 : ℝ) ≤ (z : ℝ) * ((2 ^ (12 * N + 4) : ℕ) : ℝ) := by
      rw [← hEq]
      exact Nat.cast_nonneg _
    have hzR_nonneg : (0 : ℝ) ≤ (z : ℝ) := by
      by_contra hneg
      have hneg' : (z : ℝ) < 0 := lt_of_not_ge hneg
      have hlt : (z : ℝ) * ((2 ^ (12 * N + 4) : ℕ) : ℝ) < 0 :=
        mul_neg_of_neg_of_pos hneg' hDpos
      linarith
    have hz_nonneg : 0 ≤ z := by exact_mod_cast hzR_nonneg
    have hz_eq : (z : ℝ) = ((z.natAbs : ℕ) : ℝ) := by
      have h1 : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg hz_nonneg
      rw [← h1]
      simp
    have hEqNat : ((M * centralCube N * (42 * N + 5) : ℕ) : ℝ) =
        ((2 ^ (12 * N + 4) * z.natAbs : ℕ) : ℝ) := by
      rw [hEq, hz_eq, Nat.cast_mul]
      ring
    have hNatEq : M * centralCube N * (42 * N + 5) = 2 ^ (12 * N + 4) * z.natAbs :=
      Nat.cast_injective hEqNat
    exact ⟨z.natAbs, hNatEq⟩
  have hEqExp : 12 * N + 4 = lambda N + 3 * binaryDigitSum N := by omega
  have hRed : 2 ^ (lambda N) ∣ M * (t * (42 * N + 5)) := by
    rw [hEqExp, pow_add] at hNatDvd
    have hMC : M * centralCube N * (42 * N + 5) =
        2 ^ (3 * binaryDigitSum N) * (M * (t * (42 * N + 5))) := by
      rw [ht]
      ring
    rw [hMC] at hNatDvd
    obtain ⟨k, hk⟩ := hNatDvd
    have h1 : 2 ^ (3 * binaryDigitSum N) * (M * (t * (42 * N + 5))) =
        2 ^ (3 * binaryDigitSum N) * (2 ^ (lambda N) * k) := by
      rw [hk]
      ring
    have hcancel : M * (t * (42 * N + 5)) = 2 ^ (lambda N) * k :=
      mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) h1
    exact ⟨k, hcancel⟩
  exact dvd_of_mul_odd _ _ _ hWodd hRed

namespace HypothesisForms

theorem cleared_positive_tail_not_small
    (hNonneg : ∀ n : ℕ, 0 ≤ ramanujanTerm n)
    (hSummable : Summable ramanujanTerm)
    (hFirst : ∀ {K : ℕ}, 10 ≤ K →
      1 < (2 : ℝ) ^ (lambda K) * ramanujanTerm (K + 1))
    (hDiv : ∀ {M K : ℕ},
      (∀ n : ℕ, n ≤ K → IsInteger ((M : ℝ) * ramanujanTerm n)) →
      2 ^ (lambda K) ∣ M)
    {M N : ℕ} (hN : 10 ≤ N) (hM : 0 < M)
    (hInt : ∀ n : ℕ, n ≤ N →
      IsInteger ((M : ℝ) * ramanujanTerm n)) :
    1 < (M : ℝ) *
      ∑' j : ℕ, ramanujanTerm (N + 1 + j) := by
  obtain ⟨c, hc⟩ := hDiv hInt
  have hcpos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos h
    subst hc0
    simp at hc
    omega
  have hM_eq : (M : ℝ) = ((2 ^ lambda N : ℕ) : ℝ) * (c : ℝ) := by
    have hcon := congrArg (Nat.cast : ℕ → ℝ) hc
    simpa [Nat.cast_mul] using hcon
  have hpow_eq : ((2 ^ lambda N : ℕ) : ℝ) = (2 : ℝ) ^ lambda N := by
    push_cast
    ring
  have hMge_pow : (2 : ℝ) ^ lambda N ≤ (M : ℝ) := by
    have h1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcpos
    rw [hM_eq, hpow_eq]
    calc (2 : ℝ) ^ lambda N = (2 : ℝ) ^ lambda N * 1 := by ring
      _ ≤ (2 : ℝ) ^ lambda N * (c : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
  have hFirstN : 1 < (2 : ℝ) ^ lambda N * ramanujanTerm (N + 1) :=
    hFirst (K := N) hN
  have hMono : (2 : ℝ) ^ lambda N * ramanujanTerm (N + 1)
      ≤ (M : ℝ) * ramanujanTerm (N + 1) :=
    mul_le_mul_of_nonneg_right hMge_pow (hNonneg _)
  have hinj : Function.Injective (fun j : ℕ => N + 1 + j) := by
    intro a b h
    dsimp only at h
    omega
  have hShift : Summable (fun j : ℕ => ramanujanTerm (N + 1 + j)) :=
    hSummable.comp_injective hinj
  have hTail : ramanujanTerm (N + 1)
      ≤ ∑' j : ℕ, ramanujanTerm (N + 1 + j) := by
    have h0 := hShift.le_tsum (0 : ℕ) (fun j _ => hNonneg _)
    simpa using h0
  have hMnonneg : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hTailM : (M : ℝ) * ramanujanTerm (N + 1)
      ≤ (M : ℝ) * ∑' j : ℕ, ramanujanTerm (N + 1 + j) :=
    mul_le_mul_of_nonneg_left hTail hMnonneg
  calc (1 : ℝ) < (2 : ℝ) ^ lambda N * ramanujanTerm (N + 1) := hFirstN
    _ ≤ (M : ℝ) * ramanujanTerm (N + 1) := hMono
    _ ≤ (M : ℝ) * ∑' j : ℕ, ramanujanTerm (N + 1 + j) := hTailM

end HypothesisForms

theorem cleared_positive_tail_not_small
    {M N : ℕ} (hN : 10 ≤ N) (hM : 0 < M)
    (hInt : ∀ n : ℕ, n ≤ N →
      IsInteger ((M : ℝ) * ramanujanTerm n)) :
    1 < (M : ℝ) *
      ∑' j : ℕ, ramanujanTerm (N + 1 + j) :=
  HypothesisForms.cleared_positive_tail_not_small
    ramanujanTerm_nonneg summable_ramanujanTerm
    cleared_first_omitted_gt_one prefix_integral_implies_dyadic_divisibility
    hN hM hInt

end Theory.PiDigits.T203RamanujanCarryFailure
