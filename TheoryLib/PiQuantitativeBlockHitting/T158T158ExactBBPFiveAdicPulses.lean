import TheoryLib.PiQuantitativeBlockHitting.T157T157ExactBBPFiveAdicShell
import TheoryLib.PiQuantitativeBlockHitting.T106T106BBPForcedOrbit

/-!
# T158: exact five-adic pulses of the seven-term BBP forcing

The exact shell unit from T157 is transported to the actual seven-new-term
forcing.  Shell jumps and secondary-pole activations have the minimum possible
valuation exactly; quiet shells gain at least one additional factor of five.
-/

namespace Theory.PiDigits.T158ExactBBPFiveAdicPulses

open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.T106BBPForcedOrbit
open Theory.PiDigits.T157ExactBBPFiveAdicShell
open T77SelectedPadicDefectShell
open T115SampledBBPCellDefectPhase

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private lemma padicValRat_five_two : padicValRat 5 (2 : ℚ) = 0 :=
  padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)

private lemma padicValRat_five_five : padicValRat 5 (5 : ℚ) = 1 :=
  padicValRat.self (by norm_num)

private lemma padicValRat_five_ten : padicValRat 5 (10 : ℚ) = 1 := by
  rw [show (10 : ℚ) = 5 * 2 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num),
    padicValRat_five_five, padicValRat_five_two]
  norm_num

/-- The seven-term forcing is exactly the difference of consecutive actual
scaled BBP rationals. -/
theorem sampledBBPForcingRat_eq_scaledBBPRat_sub (m : ℕ) :
    sampledBBPForcingRat m = scaledBBPRat (m + 1) - 10 * scaledBBPRat m := by
  unfold sampledBBPForcingRat scaledBBPRat
  rw [pow_succ]
  ring

private lemma fiveShellLog_mono_succ (m : ℕ) :
    fiveShellLog m ≤ fiveShellLog (m + 1) := by
  exact Nat.log_mono_right (by omega)

private lemma fiveShellLog_succ_le (m : ℕ) :
    fiveShellLog (m + 1) ≤ fiveShellLog m + 1 := by
  have hT : 3 ≤ fiveShellScale m := by
    have : 5 ≤ fiveShellScale m := by
      unfold fiveShellScale fiveShellLog
      have hlog : 1 ≤ Nat.log 5 (56 * m + 5) := by
        exact (Nat.le_log_iff_pow_le (b := 5) (by norm_num) (by omega)).2
          (by norm_num)
      exact Nat.pow_le_pow_right (by norm_num : 0 < 5) hlog
    omega
  have hnext : 56 * (m + 1) + 5 < 25 * fiveShellScale m := by
    have hcur := linear_lt_five_mul_shellScale m
    omega
  have hpow :
      56 * (m + 1) + 5 < 5 ^ (fiveShellLog m + 2) := by
    calc
      56 * (m + 1) + 5 < 25 * fiveShellScale m := hnext
      _ = 5 ^ (fiveShellLog m + 2) := by
        simp [fiveShellScale, pow_add]
        ring
  exact Nat.lt_succ_iff.mp
    ((Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).2 hpow)

/-- Between consecutive sampled depths the maximal five-primary shell either
stays fixed or jumps by exactly one. -/
theorem fiveShellLog_succ_eq_or (m : ℕ) :
    fiveShellLog (m + 1) = fiveShellLog m ∨
      fiveShellLog (m + 1) = fiveShellLog m + 1 := by
  have hlo := fiveShellLog_mono_succ m
  have hhi := fiveShellLog_succ_le m
  omega

private lemma forcingRat_ne_zero (m : ℕ) : sampledBBPForcingRat m ≠ 0 :=
  ne_of_gt (sampledBBPForcingRat_pos m)

/-- Entering a new largest-power-of-five shell produces an exact minimum
valuation pulse in the actual seven-term forcing. -/
theorem sampledBBPForcingRat_five_val_eq_of_shell_jump
    (m : ℕ) (hjump : fiveShellLog (m + 1) = fiveShellLog m + 1) :
    padicValRat 5 (sampledBBPForcingRat m) =
      ((m + 1 : ℕ) : ℤ) - fiveShellLog (m + 1) := by
  rw [sampledBBPForcingRat_eq_scaledBBPRat_sub]
  have hq1 := scaledBBPRat_five_val_eq (m + 1)
  have hq0 := scaledBBPRat_five_val_eq m
  have h10q : padicValRat 5 (10 * scaledBBPRat m) =
      1 + ((m : ℤ) - fiveShellLog m) := by
    rw [padicValRat.mul (by norm_num) (scaledBBPRat_ne_zero m),
      padicValRat_five_ten, hq0]
  have hsum0 : scaledBBPRat (m + 1) + -(10 * scaledBBPRat m) ≠ 0 := by
    intro hz
    apply forcingRat_ne_zero m
    rw [sampledBBPForcingRat_eq_scaledBBPRat_sub, sub_eq_add_neg]
    exact hz
  rw [sub_eq_add_neg]
  calc
    padicValRat 5 (scaledBBPRat (m + 1) + -(10 * scaledBBPRat m)) =
        padicValRat 5 (scaledBBPRat (m + 1)) := by
      apply padicValRat.add_eq_of_lt
      · exact hsum0
      · exact scaledBBPRat_ne_zero (m + 1)
      · exact neg_ne_zero.mpr
          (mul_ne_zero (by norm_num) (scaledBBPRat_ne_zero m))
      · rw [padicValRat.neg, h10q, hq1]
        omega
    _ = ((m + 1 : ℕ) : ℤ) - fiveShellLog (m + 1) := hq1

/-- The common-shell normalized forcing unit. -/
def commonShellForcingUnit (m : ℕ) : ℚ :=
  scaledBBPFiveUnit (m + 1) - 2 * scaledBBPFiveUnit m

lemma FiveCongruent.neg {x y : ℚ} (h : FiveCongruent x y) :
    FiveCongruent (-x) (-y) := by
  unfold FiveCongruent at h ⊢
  rcases h with rfl | h
  · left; rfl
  · right
    rw [show -x - -y = -(x - y) by ring, padicValRat.neg]
    exact h

lemma FiveCongruent.sub {x y a b : ℚ}
    (hx : FiveCongruent x a) (hy : FiveCongruent y b) :
    FiveCongruent (x - y) (a - b) := by
  simpa [sub_eq_add_neg] using hx.add (FiveCongruent.neg hy)

private lemma commonShellForcingUnit_congruent (m : ℕ) :
    FiveCongruent (commonShellForcingUnit m)
      ((2 : ℚ) ^ (m + 1) *
        ((4 + 2 * secondaryPoleIndicator (m + 1)) -
          (4 + 2 * secondaryPoleIndicator m))) := by
  have h2 : padicValRat 5 (2 : ℚ) = 0 := padicValRat_five_two
  have hm := (scaledBBPFiveUnit_five_congruent m).mul_left_of_val_zero
    (by norm_num) h2
  have hs := FiveCongruent.sub (scaledBBPFiveUnit_five_congruent (m + 1)) hm
  unfold commonShellForcingUnit
  convert hs using 1 <;> rw [pow_succ] <;> ring

private lemma indicator_activation_direction
    (m : ℕ) (hshell : fiveShellLog (m + 1) = fiveShellLog m)
    (hchange : secondaryPoleIndicator (m + 1) ≠ secondaryPoleIndicator m) :
    secondaryPoleIndicator m = 0 ∧ secondaryPoleIndicator (m + 1) = 1 := by
  have hscale : fiveShellScale (m + 1) = fiveShellScale m := by
    simp [fiveShellScale, hshell]
  by_cases h0 : fiveShellScale m ≤ 14 * m + 1
  · have h1 : fiveShellScale (m + 1) ≤ 14 * (m + 1) + 1 := by omega
    have hi0 : secondaryPoleIndicator m = 1 := by
      simp [secondaryPoleIndicator, h0]
    have hi1 : secondaryPoleIndicator (m + 1) = 1 := by
      simp [secondaryPoleIndicator, h1]
    exact (hchange (hi1.trans hi0.symm)).elim
  · have hi0 : secondaryPoleIndicator m = 0 := by
      simp [secondaryPoleIndicator, h0]
    have hi1 : secondaryPoleIndicator (m + 1) = 1 := by
      have hne0 : secondaryPoleIndicator (m + 1) ≠ 0 := by
        intro hz
        exact hchange (hz.trans hi0.symm)
      have hle := secondaryPoleIndicator_le_one (m + 1)
      omega
    exact ⟨hi0, hi1⟩

private lemma commonShellForcingUnit_val_activation
    (m : ℕ) (hshell : fiveShellLog (m + 1) = fiveShellLog m)
    (hchange : secondaryPoleIndicator (m + 1) ≠ secondaryPoleIndicator m) :
    padicValRat 5 (commonShellForcingUnit m) = 0 := by
  rcases indicator_activation_direction m hshell hchange with ⟨h0, h1⟩
  have hcong := commonShellForcingUnit_congruent m
  have hrhs :
      (2 : ℚ) ^ (m + 1) *
          ((4 + 2 * secondaryPoleIndicator (m + 1)) -
            (4 + 2 * secondaryPoleIndicator m)) =
        (2 : ℚ) ^ (m + 1) * 2 := by
    rw [h0, h1]
    norm_num
  rw [hrhs] at hcong
  have hmodel : padicValRat 5 ((2 : ℚ) ^ (m + 1) * 2) = 0 := by
    rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (by norm_num),
      padicValRat.pow (by norm_num), padicValRat_five_two]
    norm_num
  have hmodel0 : (2 : ℚ) ^ (m + 1) * 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)
  exact padicVal_eq_zero_of_fiveCongruent_unit hmodel0 hmodel hcong

private lemma log_linear_le (n : ℕ) (hn : 2 ≤ n) : fiveShellLog n ≤ n := by
  have hpow : 56 * n + 5 < 5 ^ (n + 1) := by
    induction n, hn using Nat.le_induction with
    | base => norm_num [fiveShellLog]
    | succ n hn ih =>
        rw [show n + 1 + 1 = (n + 1) + 1 by rfl, pow_succ]
        calc
          56 * (n + 1) + 5 < 5 * (56 * n + 5) := by omega
          _ < 5 * 5 ^ (n + 1) :=
            (Nat.mul_lt_mul_left (by norm_num : 0 < 5)).2 ih
          _ = 5 ^ (n + 1) * 5 := by ring
  exact Nat.lt_succ_iff.mp
    ((Nat.log_lt_iff_lt_pow (by norm_num) (by positivity)).2 hpow)

private lemma commonShell_forcing_factorization
    (m : ℕ) (hm : 1 ≤ m)
    (hshell : fiveShellLog (m + 1) = fiveShellLog m) :
    sampledBBPForcingRat m =
      (5 : ℚ) ^ ((m + 1) - fiveShellLog (m + 1)) *
        commonShellForcingUnit m := by
  have hlog : fiveShellLog (m + 1) ≤ m + 1 :=
    log_linear_le (m + 1) (by omega)
  have hscale : fiveShellScale (m + 1) = fiveShellScale m := by
    simp [fiveShellScale, hshell]
  have hpow :
      (5 : ℚ) ^ ((m + 1) - fiveShellLog (m + 1)) *
          (fiveShellScale (m + 1) : ℚ) = 5 ^ (m + 1) := by
    simpa [fiveShellScale] using
      (pow_sub_mul_pow (5 : ℚ) hlog)
  rw [hscale] at hpow
  unfold commonShellForcingUnit scaledBBPFiveUnit sampledBBPForcingRat
  rw [hscale]
  rw [show (10 : ℚ) ^ (m + 1) =
      (2 : ℚ) ^ (m + 1) * (5 : ℚ) ^ (m + 1) by
        rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]]
  rw [← hpow]
  rw [pow_succ]
  ring

private lemma commonShell_requires_positive_index
    (m : ℕ) (hshell : fiveShellLog (m + 1) = fiveShellLog m) : 1 ≤ m := by
  by_contra h
  have : m = 0 := by omega
  subst m
  norm_num [fiveShellLog] at hshell

/-- Activation of the second BBP pole inside a fixed shell is another exact
minimum-valuation pulse. -/
theorem sampledBBPForcingRat_five_val_eq_of_secondary_activation
    (m : ℕ) (hshell : fiveShellLog (m + 1) = fiveShellLog m)
    (hchange : secondaryPoleIndicator (m + 1) ≠ secondaryPoleIndicator m) :
    padicValRat 5 (sampledBBPForcingRat m) =
      ((m + 1 : ℕ) : ℤ) - fiveShellLog (m + 1) := by
  have hm := commonShell_requires_positive_index m hshell
  have hfactor := commonShell_forcing_factorization m hm hshell
  have hunit0 : commonShellForcingUnit m ≠ 0 := by
    intro hz
    apply forcingRat_ne_zero m
    rw [hfactor, hz, mul_zero]
  rw [commonShell_forcing_factorization m hm hshell,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hunit0,
    padicValRat.pow (by norm_num), padicValRat_five_five,
    commonShellForcingUnit_val_activation m hshell hchange]
  have hlog := log_linear_le (m + 1) (by omega)
  rw [Nat.cast_sub hlog]
  ring

/-- Between shell jumps and secondary-pole activations, the actual forcing
gains at least one extra factor of five. -/
theorem sampledBBPForcingRat_five_val_ge_of_quiet_shell
    (m : ℕ) (hshell : fiveShellLog (m + 1) = fiveShellLog m)
    (hquiet : secondaryPoleIndicator (m + 1) = secondaryPoleIndicator m) :
    ((m + 1 : ℕ) : ℤ) - fiveShellLog (m + 1) + 1 ≤
      padicValRat 5 (sampledBBPForcingRat m) := by
  have hm := commonShell_requires_positive_index m hshell
  have hfactor := commonShell_forcing_factorization m hm hshell
  have hunit0 : commonShellForcingUnit m ≠ 0 := by
    intro hz
    apply forcingRat_ne_zero m
    rw [hfactor, hz, mul_zero]
  have hcong := commonShellForcingUnit_congruent m
  rw [hquiet] at hcong
  have hunitVal : (1 : ℤ) ≤ padicValRat 5 (commonShellForcingUnit m) := by
    unfold FiveCongruent at hcong
    rcases hcong with heq | hv
    · exfalso
      apply hunit0
      simpa using heq
    · simpa using hv
  rw [hfactor,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hunit0,
    padicValRat.pow (by norm_num), padicValRat_five_five]
  have hlog := log_linear_le (m + 1) (by omega)
  rw [Nat.cast_sub hlog]
  omega

#print axioms Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_eq_scaledBBPRat_sub
#print axioms Theory.PiDigits.T158ExactBBPFiveAdicPulses.fiveShellLog_succ_eq_or
#print axioms Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_five_val_eq_of_shell_jump
#print axioms Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_five_val_eq_of_secondary_activation
#print axioms Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_five_val_ge_of_quiet_shell

end Theory.PiDigits.T158ExactBBPFiveAdicPulses
