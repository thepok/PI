import TheoryLib.PiPositiveDecimalFactorEntropy.T8T8DyadicShellFejer
import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T2T2ExponentialCollisionCriterion
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy
import TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting

/-!
# T9: a mesoscopic pair-count frontier for the decimal orbit of pi

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file formalizes C5 as an explicit unproved hypothesis.  Ordered pairs
include the diagonal, every distance cutoff is strict, and the complete range
`4^k <= M_n` is retained.  C5 is not pair correlation C3.

The only scale not directly covered by C5 is T8's terminal shell.  A finite
decimal-cylinder comparison bounds doubling a circle radius by the explicit
factor `300`.  Thus C5 supplies T8 with constant `150*A`; imported T8 then
gives C4 with constant `750*A+1`, imported T7 gives C2, and imported T2 gives
canonical C1.  No fixed-pi estimate is asserted without C5.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace DecimalFactorComplexity.MesoscopicFrontier

open DecimalFactorComplexity
open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.CylinderCollision
open DecimalFactorComplexity.DyadicShellFejer
open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.CoherentSuccessorSplitting
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- The agenda's sample size `M_n = 10^n`. -/
def mesoscopicSampleSize (n : ℕ) : ℕ := 10 ^ n

/-- The Fejer bandwidth `H_n = M_n/2`. -/
def mesoscopicBandwidth (n : ℕ) : ℕ := mesoscopicSampleSize n / 2

/-- Ordered pairs, including the diagonal, below the strict radius
`2^k/M_n`. -/
def piMesoscopicNearPairs (n k : ℕ) : Finset
    (Fin (mesoscopicSampleSize n) × Fin (mesoscopicSampleSize n)) :=
  Finset.univ.filter fun ij =>
    circleDistance
        (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
      (2 : ℝ) ^ k / (mesoscopicSampleSize n : ℝ)

/-- C5, left explicitly unproved for pi.  One positive constant controls all
large `n` and every integer `k >= 0` in the complete range `4^k <= M_n`. -/
def PiMesoscopicPairCountC5 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ mesoscopicSampleSize n →
      ((piMesoscopicNearPairs n k).card : ℝ) ≤
        A * ((2 : ℝ) ^ k + 1) * (mesoscopicSampleSize n : ℝ)

/-- Full theorem-level expansion of C5, exposing `M_n=10^n`, every index,
the strict cutoff, and the ordered-pair normalization. -/
theorem piMesoscopicPairCountC5_iff_quantifiers :
    PiMesoscopicPairCountC5 ↔
      ∃ A : ℝ, 0 < A ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
        ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ 10 ^ n →
          ((Finset.univ.filter
            (fun ij : Fin (10 ^ n) × Fin (10 ^ n) =>
              circleDistance
                  (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
                (2 : ℝ) ^ k / ((10 ^ n : ℕ) : ℝ))).card : ℝ) ≤
            A * ((2 : ℝ) ^ k + 1) * ((10 ^ n : ℕ) : ℝ) := by
  rfl

/-- The agenda parameters are literally `M_n=10^n` and `H_n=M_n/2`. -/
theorem mesoscopic_parameters (n : ℕ) :
    mesoscopicSampleSize n = 10 ^ n ∧
      mesoscopicBandwidth n = 10 ^ n / 2 := by
  exact ⟨rfl, rfl⟩

/-- At the agenda parameters, T8's dyadic cutoff is exactly C5's strict
radius `2^k/M_n`. -/
theorem dyadicCutoff_mesoscopicBandwidth (n k : ℕ) (hn : 1 ≤ n) :
    dyadicCutoff (mesoscopicBandwidth n) k =
      (2 : ℝ) ^ k / (mesoscopicSampleSize n : ℝ) := by
  have hdouble := two_mul_half_ten_pow n hn
  have hdoubleR :
      2 * (mesoscopicBandwidth n : ℝ) =
        (mesoscopicSampleSize n : ℝ) := by
    exact_mod_cast hdouble
  unfold dyadicCutoff
  rw [hdoubleR]

/-- C5's cumulative pair set is exactly T8's strict dyadic near set. -/
theorem piMesoscopicNearPairs_eq_dyadicNearPairs
    (n k : ℕ) (hn : 1 ≤ n) :
    piMesoscopicNearPairs n k =
      dyadicNearPairs
        (fun j : Fin (mesoscopicSampleSize n) => piDecimalShiftOrbit j)
        (mesoscopicBandwidth n) k := by
  ext ij
  simp only [piMesoscopicNearPairs, dyadicNearPairs, Finset.mem_filter,
    Finset.mem_univ, true_and, pairCircleDistance]
  rw [dyadicCutoff_mesoscopicBandwidth n k hn]

/-- T8 shell `k` is contained in C5's cumulative strict set at scale `k+1`.
The lower endpoint of the shell remains closed and its upper endpoint strict. -/
theorem dyadicShellPairs_subset_piMesoscopicNearPairs_succ
    (n k : ℕ) (hn : 1 ≤ n) :
    dyadicShellPairs
        (fun j : Fin (mesoscopicSampleSize n) => piDecimalShiftOrbit j)
        (mesoscopicBandwidth n) k ⊆
      piMesoscopicNearPairs n (k + 1) := by
  intro ij hij
  simp only [dyadicShellPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    pairCircleDistance] at hij
  simp only [piMesoscopicNearPairs, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [← dyadicCutoff_mesoscopicBandwidth n (k + 1) hn]
  exact hij.2

/-- Two decimal refinements retain at least one hundredth of the coarser
ordered cylinder-collision energy. -/
theorem one_hundredth_energy_le_energy_add_two (m N : ℕ) :
    (1 / 100 : ℝ) * (piCylinderCollisionEnergy m N : ℝ) ≤
      piCylinderCollisionEnergy (m + 2) N := by
  have h₁ := one_tenth_energy_le_energy_succ m N
  have h₂ := one_tenth_energy_le_energy_succ (m + 1) N
  norm_num at h₁ h₂ ⊢
  nlinarith

/-- At radii at most one half, doubling the strict pi-orbit pair-count radius
costs at most the explicit factor `300`.  The proof brackets `2r` by a decimal
radius, uses T7FiniteCylinderEnergy's factor `3`, and pays `100` for two
decimal refinements. -/
theorem piMesoscopicNearPairs_succ_card_le_three_hundred
    (n k : ℕ)
    (hrange : 2 * ((2 : ℝ) ^ k / (mesoscopicSampleSize n : ℝ)) ≤ 1) :
    ((piMesoscopicNearPairs n (k + 1)).card : ℝ) ≤
      300 * ((piMesoscopicNearPairs n k).card : ℝ) := by
  let r : ℝ := (2 : ℝ) ^ k / (mesoscopicSampleSize n : ℝ)
  have hMpos : (0 : ℝ) < mesoscopicSampleSize n := by
    simp only [mesoscopicSampleSize]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have htwoR : 0 < 2 * r := by positivity
  obtain ⟨m, hmFine, hmCoarse⟩ :=
    exists_decimalRadius_bracket htwoR (by simpa only [r] using hrange)
  have hsuccRadius :
      (2 : ℝ) ^ (k + 1) / (mesoscopicSampleSize n : ℝ) = 2 * r := by
    dsimp [r]
    rw [pow_succ]
    ring
  have hnextSubset :
      piMesoscopicNearPairs n (k + 1) ⊆
        piNearReturnPairs m (mesoscopicSampleSize n) := by
    intro ij hij
    rw [mem_piNearReturnPairs_iff]
    rw [← circleDistance_piShift_sub_eq_powerDifference]
    have hnear := (Finset.mem_filter.mp hij).2
    rw [hsuccRadius] at hnear
    simpa only [decimalRadius] using hnear.trans_le hmCoarse
  have hnext :
      ((piMesoscopicNearPairs n (k + 1)).card : ℝ) ≤
        (Q_pi m (mesoscopicSampleSize n) : ℝ) := by
    exact_mod_cast Finset.card_le_card hnextSubset
  have hfineRadius : decimalRadius (m + 2) < r := by
    rw [show m + 2 = (m + 1) + 1 by omega,
      decimalRadius_succ_eq_div_ten]
    nlinarith
  have hfineSubset :
      piNearReturnPairs (m + 2) (mesoscopicSampleSize n) ⊆
        piMesoscopicNearPairs n k := by
    intro ij hij
    simp only [piMesoscopicNearPairs, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [circleDistance_piShift_sub_eq_powerDifference]
    have hnear := (mem_piNearReturnPairs_iff
      (m + 2) (mesoscopicSampleSize n) ij).mp hij
    have hnear' :
        circleDistance
            (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
          decimalRadius (m + 2) := by
      simpa only [decimalRadius] using hnear
    exact hnear'.trans hfineRadius
  have hfine :
      (Q_pi (m + 2) (mesoscopicSampleSize n) : ℝ) ≤
        ((piMesoscopicNearPairs n k).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hfineSubset
  have hcoarseNat :=
    (piCylinderCollisionEnergy_le_Q_pi_le_three_mul
      m (mesoscopicSampleSize n)).2
  have hcoarse :
      (Q_pi m (mesoscopicSampleSize n) : ℝ) ≤
        3 * (piCylinderCollisionEnergy m (mesoscopicSampleSize n) : ℝ) := by
    exact_mod_cast hcoarseNat
  have hrefine :=
    one_hundredth_energy_le_energy_add_two m (mesoscopicSampleSize n)
  have hfineEnergyNat :=
    (piCylinderCollisionEnergy_le_Q_pi_le_three_mul
      (m + 2) (mesoscopicSampleSize n)).1
  have hfineEnergy :
      (piCylinderCollisionEnergy (m + 2) (mesoscopicSampleSize n) : ℝ) ≤
        (Q_pi (m + 2) (mesoscopicSampleSize n) : ℝ) := by
    exact_mod_cast hfineEnergyNat
  calc
    ((piMesoscopicNearPairs n (k + 1)).card : ℝ) ≤
        (Q_pi m (mesoscopicSampleSize n) : ℝ) := hnext
    _ ≤ 3 * (piCylinderCollisionEnergy m (mesoscopicSampleSize n) : ℝ) :=
      hcoarse
    _ ≤ 300 *
        (piCylinderCollisionEnergy (m + 2) (mesoscopicSampleSize n) : ℝ) := by
      nlinarith
    _ ≤ 300 * (Q_pi (m + 2) (mesoscopicSampleSize n) : ℝ) := by
      gcongr
    _ ≤ 300 * ((piMesoscopicNearPairs n k).card : ℝ) := by
      gcongr

/-- Real arithmetic converting a direct C5 shell count into T8's raw shell
normalization with witness `150*A`. -/
theorem c5_shell_arithmetic
    {A M H p count : ℝ} (hA : 0 ≤ A) (hM : 0 < M)
    (hhalf : 2 * H = M) (hp : 1 ≤ p)
    (hcount : count ≤ A * (p + 1) * M) :
    count ≤ (150 * A) * M ^ 2 * p / H := by
  have hH : 0 < H := by nlinarith
  apply (le_div_iff₀ hH).2
  calc
    count * H ≤ (A * (p + 1) * M) * H :=
      mul_le_mul_of_nonneg_right hcount hH.le
    _ = (A * M ^ 2 / 2) * (p + 1) := by
      have : H = M / 2 := by nlinarith
      rw [this]
      ring
    _ ≤ (A * M ^ 2 / 2) * (300 * p) := by
      gcongr
      nlinarith
    _ = (150 * A) * M ^ 2 * p := by ring

/-- Real arithmetic for the one terminal shell after the factor-`300`
radius-doubling estimate. -/
theorem c5_terminal_shell_arithmetic
    {A M H p count : ℝ} (hA : 0 ≤ A) (hM : 0 < M)
    (hhalf : 2 * H = M) (hp : 1 ≤ p)
    (hcount : count ≤ 300 * (A * (p + 1) * M)) :
    count ≤ (150 * A) * M ^ 2 * (2 * p) / H := by
  have hH : 0 < H := by nlinarith
  apply (le_div_iff₀ hH).2
  calc
    count * H ≤ (300 * (A * (p + 1) * M)) * H :=
      mul_le_mul_of_nonneg_right hcount hH.le
    _ = (150 * A * M ^ 2) * (p + 1) := by
      have : H = M / 2 := by nlinarith
      rw [this]
      ring
    _ ≤ (150 * A * M ^ 2) * (2 * p) := by
      gcongr
      nlinarith
    _ = (150 * A) * M ^ 2 * (2 * p) := by ring

/-- Explicit bridge from exact C5 to T8's raw bounds with witness `150*A`.
For each `n`, set `L=log_4(M_n)` and `K=L+1`.  C5 controls shells below `L`;
the named factor-`300` lemma controls the single terminal shell. -/
theorem piMesoscopicPairCountC5_implies_dyadicBounds_explicit
    (hC5 : PiMesoscopicPairCountC5) :
    ∃ A : ℝ, 0 < A ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ K : ℕ,
        DyadicPairCountBounds
          (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
          (10 ^ n / 2) K (150 * A) := by
  obtain ⟨A, hA, n0, hn0, hcounts⟩ := hC5
  refine ⟨A, hA, max n0 2, hn0.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hnC5 : n0 ≤ n := (le_max_left n0 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right n0 2).trans hn
  have hn1 : 1 ≤ n := one_le_two.trans hn2
  let M : ℕ := mesoscopicSampleSize n
  let H : ℕ := mesoscopicBandwidth n
  let L : ℕ := Nat.log 4 M
  have hMposNat : 0 < M := by
    simp only [M, mesoscopicSampleSize]
    positivity
  have hMne : M ≠ 0 := hMposNat.ne'
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposNat
  have hhalfNat : 2 * H = M := by
    simpa only [H, M, mesoscopicBandwidth, mesoscopicSampleSize] using
      two_mul_half_ten_pow n hn1
  have hhalf : 2 * (H : ℝ) = (M : ℝ) := by exact_mod_cast hhalfNat
  have hHposNat : 0 < H := by omega
  have hH : 1 ≤ H := hHposNat
  have hLlower : 4 ^ L ≤ M := by
    exact Nat.pow_log_le_self 4 hMne
  have hLupper : M < 4 ^ (L + 1) := by
    simpa only [L, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 4) (by norm_num) M
  have hfour_le_M : 4 ≤ M := by
    calc
      4 ≤ 10 ^ 2 := by norm_num
      _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      _ = M := by rfl
  have hLpos : 1 ≤ L := by
    apply (Nat.le_log_iff_pow_le (by norm_num) hMne).2
    simpa using hfour_le_M
  have htwoPow : 2 * 2 ^ L ≤ M := by
    calc
      2 * 2 ^ L = 2 ^ (L + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2 * L) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 ^ L := by
        rw [pow_mul]
        norm_num
      _ ≤ M := hLlower
  have hrange : 2 * ((2 : ℝ) ^ L / (M : ℝ)) ≤ 1 := by
    have hnum : 2 * (2 : ℝ) ^ L ≤ (M : ℝ) := by
      exact_mod_cast htwoPow
    calc
      2 * ((2 : ℝ) ^ L / (M : ℝ)) =
          (2 * (2 : ℝ) ^ L) / (M : ℝ) := by ring
      _ ≤ 1 := (div_le_one hMpos).2 hnum
  refine ⟨L + 1, ?_⟩
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · exact (Nat.div_le_self M 2).trans hLupper.le
  · have hC5core := hcounts n hnC5 0 (by simpa using hMposNat)
    have hcoreCount :
        (((dyadicNearPairs
          (fun j : Fin M => piDecimalShiftOrbit j) H 0).card : ℝ)) ≤
          A * ((1 : ℝ) + 1) * (M : ℝ) := by
      rw [← piMesoscopicNearPairs_eq_dyadicNearPairs n 0 hn1]
      simpa only [M, pow_zero] using hC5core
    simpa only [pow_zero, mul_one] using
      c5_shell_arithmetic hA.le hMpos hhalf (p := (1 : ℝ))
        (by norm_num) hcoreCount
  · intro k hk
    have hkL : k ≤ L := by omega
    by_cases hklt : k < L
    · have hscale : 4 ^ (k + 1) ≤ M := by
        exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hLlower
      have hC5next := hcounts n hnC5 (k + 1) (by simpa only [M] using hscale)
      have hsubset :=
        dyadicShellPairs_subset_piMesoscopicNearPairs_succ n k hn1
      have hshellToNear :
          (((dyadicShellPairs
            (fun j : Fin M => piDecimalShiftOrbit j) H k).card : ℝ)) ≤
            ((piMesoscopicNearPairs n (k + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hraw :
          (((dyadicShellPairs
            (fun j : Fin M => piDecimalShiftOrbit j) H k).card : ℝ)) ≤
            A * ((2 : ℝ) ^ (k + 1) + 1) * (M : ℝ) := by
        exact hshellToNear.trans (by simpa only [M] using hC5next)
      exact c5_shell_arithmetic hA.le hMpos hhalf
        (one_le_pow₀ (by norm_num)) hraw
    · have hkeq : k = L := by omega
      subst k
      have hC5last := hcounts n hnC5 L (by simpa only [M] using hLlower)
      have hsubset :=
        dyadicShellPairs_subset_piMesoscopicNearPairs_succ n L hn1
      have hshellToNear :
          (((dyadicShellPairs
            (fun j : Fin M => piDecimalShiftOrbit j) H L).card : ℝ)) ≤
            ((piMesoscopicNearPairs n (L + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hdouble :=
        piMesoscopicNearPairs_succ_card_le_three_hundred n L
          (by simpa only [M] using hrange)
      have hraw :
          (((dyadicShellPairs
            (fun j : Fin M => piDecimalShiftOrbit j) H L).card : ℝ)) ≤
            300 * (A * ((2 : ℝ) ^ L + 1) * (M : ℝ)) := by
        calc
          (((dyadicShellPairs
              (fun j : Fin M => piDecimalShiftOrbit j) H L).card : ℝ)) ≤
              ((piMesoscopicNearPairs n (L + 1)).card : ℝ) := hshellToNear
          _ ≤ 300 * ((piMesoscopicNearPairs n L).card : ℝ) := hdouble
          _ ≤ 300 * (A * ((2 : ℝ) ^ L + 1) * (M : ℝ)) := by
            gcongr
      have hpow : (2 : ℝ) ^ (L + 1) = 2 * (2 : ℝ) ^ L := by
        rw [pow_succ]
        ring
      rw [hpow]
      exact c5_terminal_shell_arithmetic hA.le hMpos hhalf
        (one_le_pow₀ (by norm_num)) hraw

/-- Exact C5 implies T8's fixed-pi dyadic multiscale hypothesis, with the
The constant change `A ↦ 150*A` exposed by the preceding theorem. -/
theorem piMesoscopicPairCountC5_implies_piDyadicMultiscaleHypothesis
    (hC5 : PiMesoscopicPairCountC5) : PiDyadicMultiscaleHypothesis := by
  obtain ⟨A, hA, n0, hn0, hbounds⟩ :=
    piMesoscopicPairCountC5_implies_dyadicBounds_explicit hC5
  exact ⟨150 * A, by positivity, n0, hn0, hbounds⟩

/-- C5 conditionally implies C4 through imported T8, with the displayed
Fejer-energy constant `5*(150*A)+1 = 750*A+1`. -/
theorem piMesoscopicPairCountC5_implies_C4_explicit
    (hC5 : PiMesoscopicPairCountC5) :
    ∃ A : ℝ, 0 < A ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      (∀ n : ℕ, n0 ≤ n →
        piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
          (750 * A + 1) * ((10 ^ n : ℕ) : ℝ) ^ 2) := by
  obtain ⟨A, hA, n0, hn0, hbounds⟩ :=
    piMesoscopicPairCountC5_implies_dyadicBounds_explicit hC5
  refine ⟨A, hA, n0, hn0, ?_⟩
  intro n hn
  obtain ⟨K, hbound⟩ := hbounds n hn
  have hn1 : 1 ≤ n := hn0.trans hn
  have hH : 1 ≤ 10 ^ n / 2 := by
    have hpowpos : 0 < 10 ^ n := pow_pos (by norm_num) n
    have hdouble := two_mul_half_ten_pow n hn1
    omega
  have hgeneric := finiteFejerEnergy_le_of_dyadicPairCountBounds
    (10 ^ n)
    (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
    (10 ^ n / 2) K (150 * A) hH hbound
  rw [← orderedPair_fejerKernel_eq_piFejerEnergy
    (10 ^ n / 2) (10 ^ n) hH]
  convert hgeneric using 1 <;> ring

/-- Definition-level C4 follows from C5 only through imported T8. -/
theorem piMesoscopicPairCountC5_implies_C4
    (hC5 : PiMesoscopicPairCountC5) : PiFejerSpectralHypothesis := by
  exact piDyadicMultiscaleHypothesis_implies_C4
    (piMesoscopicPairCountC5_implies_piDyadicMultiscaleHypothesis hC5)

/-- Imported T7 makes the collision constant explicit: C5 supplies
`M=10^n` and the fixed decay exponent `eta=1/2` at every large `n`. -/
theorem piMesoscopicPairCountC5_implies_explicit_collision_bound
    (hC5 : PiMesoscopicPairCountC5) :
    ∃ nstar : ℕ, 1 ≤ nstar ∧ ∀ n : ℕ, nstar ≤ n →
      (E_pi n (10 ^ n) : ℝ) ≤
        ((10 ^ n : ℕ) : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
  exact piFejerSpectralHypothesis_implies_explicit_collision_bound
    (piMesoscopicPairCountC5_implies_C4 hC5)

/-- C2 follows from C5 by the imported T8-to-C4 result and imported T7. -/
theorem piMesoscopicPairCountC5_implies_C2
    (hC5 : PiMesoscopicPairCountC5) : PiExponentialCollisionC2 := by
  exact piFejerSpectralHypothesis_implies_C2
    (piMesoscopicPairCountC5_implies_C4 hC5)

/-- Imported T2 converts the displayed `eta=1/2`, `M=10^n` collision bound
into the corresponding explicit canonical factor-complexity lower bound. -/
theorem piMesoscopicPairCountC5_implies_C1_explicit
    (hC5 : PiMesoscopicPairCountC5) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) ≤
        (canonicalFactorComplexity piDecimalStream n : ℝ) := by
  obtain ⟨N, hN, hcollision⟩ :=
    piMesoscopicPairCountC5_implies_explicit_collision_bound hC5
  refine ⟨N, hN, ?_⟩
  intro n hn
  exact factorComplexity_ge_rpow_of_E_pi_le
    (1 / 2 : ℝ) n (10 ^ n) (one_le_pow₀ (by norm_num)) (hcollision n hn)

/-- Canonical C1 follows from C5 through imported T8, T7, and finally T2. -/
theorem piMesoscopicPairCountC5_implies_C1
    (hC5 : PiMesoscopicPairCountC5) : PiPositiveFactorEntropyC1 := by
  exact piExponentialCollisionC2_implies_C1
    (piMesoscopicPairCountC5_implies_C2 hC5)

end DecimalFactorComplexity.MesoscopicFrontier

#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_iff_quantifiers
#print axioms DecimalFactorComplexity.MesoscopicFrontier.mesoscopic_parameters
#print axioms DecimalFactorComplexity.MesoscopicFrontier.dyadicCutoff_mesoscopicBandwidth
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicNearPairs_eq_dyadicNearPairs
#print axioms DecimalFactorComplexity.MesoscopicFrontier.dyadicShellPairs_subset_piMesoscopicNearPairs_succ
#print axioms DecimalFactorComplexity.MesoscopicFrontier.one_hundredth_energy_le_energy_add_two
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicNearPairs_succ_card_le_three_hundred
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_dyadicBounds_explicit
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_piDyadicMultiscaleHypothesis
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_C4_explicit
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_C4
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_explicit_collision_bound
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_C2
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_C1_explicit
#print axioms DecimalFactorComplexity.MesoscopicFrontier.piMesoscopicPairCountC5_implies_C1
