import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T9T9MesoscopicFrontier

/-!
# T10: scale-adaptive ordinary-orbit Fourier criterion

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The generic theorem uses the integer bandwidth `H = M / 2^(k+1)`.  Ordered
pairs include the diagonal and the distance cutoff is strict.  The zero
Fourier mode is handled exactly; cancellation is assumed only for nonzero
frequencies with `|h| < H`.

The pi conclusions are conditional on the displayed ordinary-orbit sum
estimate.  The inverse theorem assumes the literal negation of canonical C1
and asserts only the resulting existence of a large ordinary orbit sum.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace DecimalFactorComplexity.ScaleAdaptiveOrbitFourier

open DecimalFactorComplexity
open DecimalFactorComplexity.DyadicShellFejer
open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.MesoscopicFrontier
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.WeightedFourierReduction
open Theory.PiDigits.BoundaryRobustFejerDichotomy

abbrev phase := Theory.PiDigits.T27.phase
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-- The ordinary unnormalized exponential sum of a finite sequence. -/
def ordinaryOrbitSum {M : ℕ} (x : Fin M → ℝ) (h : ℤ) : ℂ :=
  ∑ j : Fin M, phase h (x j)

/-- The integer bandwidth used at pair-count scale `2^k/M`. -/
def adaptiveBandwidth (M k : ℕ) : ℕ := M / 2 ^ (k + 1)

/-- Ordered pairs, including the diagonal, below the strict radius `2^k/M`. -/
def scaleNearPairs {M : ℕ} (x : Fin M → ℝ) (k : ℕ) :
    Finset (Fin M × Fin M) :=
  Finset.univ.filter fun ij =>
    circleDistance (x ij.2 - x ij.1) < (2 : ℝ) ^ k / (M : ℝ)

/-- The generic weighted Fourier energy with strict frequency cutoff `|h|<H`. -/
def ordinaryFejerEnergy {M : ℕ} (x : Fin M → ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ fejerFrequencies H,
    fejerWeight H h * ‖ordinaryOrbitSum x h‖ ^ 2

/-- The C5 range and `M ≥ 2` make the rounded bandwidth positive. -/
theorem adaptiveBandwidth_pos (M k : ℕ) (hM : 2 ≤ M) (hscale : 4 ^ k ≤ M) :
    1 ≤ adaptiveBandwidth M k := by
  have hd : 2 ^ (k + 1) ≤ M := by
    by_cases hk : k = 0
    · subst k
      norm_num at hM ⊢
      exact hM
    · calc
        2 ^ (k + 1) ≤ 2 ^ (2 * k) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 ^ k := by rw [pow_mul]; norm_num
        _ ≤ M := hscale
  unfold adaptiveBandwidth
  exact Nat.div_pos hd (by positivity)

/-- Rounding down makes the C5 radius no larger than the Fejer core radius. -/
theorem scaleRadius_le_fejerRadius (M k : ℕ) (hM : 2 ≤ M)
    (hscale : 4 ^ k ≤ M) :
    (2 : ℝ) ^ k / (M : ℝ) ≤
      (2 * (adaptiveBandwidth M k : ℝ))⁻¹ := by
  have hH := adaptiveBandwidth_pos M k hM hscale
  have hdivNat : adaptiveBandwidth M k * 2 ^ (k + 1) ≤ M := by
    exact Nat.div_mul_le_self M (2 ^ (k + 1))
  have hdiv :
      (2 : ℝ) ^ k * (2 * (adaptiveBandwidth M k : ℝ)) ≤ (M : ℝ) := by
    exact_mod_cast (by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdivNat)
  have hMreal : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hHreal : (0 : ℝ) < 2 * (adaptiveBandwidth M k : ℝ) := by positivity
  rw [inv_eq_one_div, div_le_div_iff₀ hMreal hHreal]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- The floor in `H=M/2^(k+1)` loses less than one further factor of two. -/
theorem sampleSize_lt_four_mul_scale_mul_bandwidth
    (M k : ℕ) (hM : 2 ≤ M) (hscale : 4 ^ k ≤ M) :
    (M : ℝ) < 4 * (2 : ℝ) ^ k * (adaptiveBandwidth M k : ℝ) := by
  have hH := adaptiveBandwidth_pos M k hM hscale
  have hdpos : 0 < 2 ^ (k + 1) := by positivity
  have hfloor :
      M < (adaptiveBandwidth M k + 1) * 2 ^ (k + 1) := by
    unfold adaptiveBandwidth
    exact (Nat.div_lt_iff_lt_mul hdpos).1 (Nat.lt_succ_self _)
  have hround :
      M < 2 * adaptiveBandwidth M k * 2 ^ (k + 1) := by
    calc
      M < (adaptiveBandwidth M k + 1) * 2 ^ (k + 1) := hfloor
      _ ≤ (2 * adaptiveBandwidth M k) * 2 ^ (k + 1) := by
        gcongr
        omega
  have hroundReal :
      (M : ℝ) < 2 * (adaptiveBandwidth M k : ℝ) * (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast hround
  convert hroundReal using 1 <;> rw [pow_succ] <;> ring

/-- Exact generic Fejer expansion.  Both pair orders and all diagonal pairs
are present, and the zero mode is included. -/
theorem orderedPair_fejerKernel_eq_ordinaryFejerEnergy
    {M : ℕ} (x : Fin M → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (∑ ij : Fin M × Fin M,
        fejerKernel (H - 1) (x ij.2 - x ij.1)) =
      ordinaryFejerEnergy x H := by
  classical
  have hexpand (y : ℝ) :
      (fejerKernel (H - 1) y : ℂ) =
        ∑ h ∈ fejerFrequencies H,
          (fejerWeight H h : ℂ) * phase h y := by
    rw [fejerKernel_eq_aggregated]
    apply sum_congr rfl
    intro h hh
    rw [triangularCoefficient_pred_eq_fejerWeight H h hH]
  have hcomplex :
      ((∑ ij : Fin M × Fin M,
          fejerKernel (H - 1) (x ij.2 - x ij.1) : ℝ) : ℂ) =
        (ordinaryFejerEnergy x H : ℂ) := by
    push_cast
    simp_rw [hexpand]
    rw [sum_comm]
    simp_rw [← Finset.mul_sum]
    unfold ordinaryFejerEnergy
    push_cast
    apply sum_congr rfl
    intro h hh
    rw [orderedPair_phase_identity x h]
    unfold ordinaryOrbitSum
    push_cast
    rfl
  exact_mod_cast hcomplex

/-- The zero ordinary orbit sum is exactly the sample size. -/
theorem ordinaryOrbitSum_zero {M : ℕ} (x : Fin M → ℝ) :
    ‖ordinaryOrbitSum x 0‖ ^ 2 = (M : ℝ) ^ 2 := by
  classical
  simp [ordinaryOrbitSum, Theory.PiDigits.T27.phase_zero]

/-- There are exactly `2H-1` signed integer frequencies under `|h|<H`. -/
theorem fejerFrequencies_card (H : ℕ) (hH : 1 ≤ H) :
    (fejerFrequencies H).card = 2 * H - 1 := by
  unfold fejerFrequencies signedFrequenciesZero
  rw [Int.card_Icc]
  simp
  omega

/-- Uniform nonzero square-root cancellation bounds the complete Fejer
energy; `M^2` is the exact zero-mode contribution and `2*H*B*M` is an
explicit upper bound for all nonzero signed frequencies. -/
theorem ordinaryFejerEnergy_le_of_nonzero_orbitSum_bound
    {M : ℕ} (x : Fin M → ℝ) (H : ℕ) (B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hfourier : ∀ h : ℤ, h ≠ 0 → h.natAbs < H →
      ‖ordinaryOrbitSum x h‖ ^ 2 ≤ B * (M : ℝ)) :
    ordinaryFejerEnergy x H ≤
      (M : ℝ) ^ 2 + 2 * (H : ℝ) * B * (M : ℝ) := by
  classical
  have hzero : (0 : ℤ) ∈ fejerFrequencies H := by
    rw [mem_fejerFrequencies_iff hH]
    simpa using Nat.zero_lt_of_lt hH
  have hBM : 0 ≤ B * (M : ℝ) := mul_nonneg hB (by positivity)
  unfold ordinaryFejerEnergy
  calc
    (∑ h ∈ fejerFrequencies H,
        fejerWeight H h * ‖ordinaryOrbitSum x h‖ ^ 2) ≤
        ∑ h ∈ fejerFrequencies H,
          ((if h = 0 then (M : ℝ) ^ 2 else 0) + B * (M : ℝ)) := by
      apply sum_le_sum
      intro h hh
      have habs : h.natAbs < H := (mem_fejerFrequencies_iff hH).mp hh
      have hHnat : 0 < H := Nat.zero_lt_of_lt hH
      have hHreal : (0 : ℝ) < H := by exact_mod_cast hHnat
      have habsReal : (h.natAbs : ℝ) ≤ (H : ℝ) := by
        exact_mod_cast (Nat.le_of_lt habs)
      have hw0 : 0 ≤ fejerWeight H h := by
        unfold fejerWeight
        exact sub_nonneg.mpr ((div_le_one hHreal).2 habsReal)
      have hw1 : fejerWeight H h ≤ 1 := by
        unfold fejerWeight
        exact sub_le_self 1 (div_nonneg (by positivity) hHreal.le)
      by_cases hz : h = 0
      · subst h
        simp only [if_pos, ordinaryOrbitSum_zero, fejerWeight,
          Int.natAbs_zero, Nat.cast_zero, zero_div, sub_zero, one_mul]
        exact le_add_of_nonneg_right hBM
      · simp only [if_neg hz, zero_add]
        calc
          fejerWeight H h * ‖ordinaryOrbitSum x h‖ ^ 2 ≤
              1 * ‖ordinaryOrbitSum x h‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw1 (sq_nonneg _)
          _ ≤ B * (M : ℝ) := by simpa using hfourier h hz habs
    _ = (M : ℝ) ^ 2 +
        ((fejerFrequencies H).card : ℝ) * (B * (M : ℝ)) := by
      rw [Finset.sum_add_distrib]
      simp [hzero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) ^ 2 + 2 * (H : ℝ) * B * (M : ℝ) := by
      have hcardNat : (fejerFrequencies H).card ≤ 2 * H := by
        rw [fejerFrequencies_card H hH]
        omega
      have hcard : ((fejerFrequencies H).card : ℝ) ≤ 2 * (H : ℝ) := by
        exact_mod_cast hcardNat
      have hinner :
          ((fejerFrequencies H).card : ℝ) * (B * (M : ℝ)) ≤
            2 * (H : ℝ) * B * (M : ℝ) := by
        calc
        ((fejerFrequencies H).card : ℝ) * (B * (M : ℝ)) ≤
            (2 * (H : ℝ)) * (B * (M : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard hBM
        _ = 2 * (H : ℝ) * B * (M : ℝ) := by ring
      exact add_le_add_right hinner _

/-- Generic scale-adaptive criterion.  Every parameter, rounding choice,
strict cutoff, and constant is displayed. -/
theorem scaleNearPairs_card_le_of_nonzero_orbitSum_bound
    {M : ℕ} (x : Fin M → ℝ) (k H : ℕ) (B : ℝ)
    (hHdef : H = M / 2 ^ (k + 1))
    (hM : 2 ≤ M) (hscale : 4 ^ k ≤ M) (hB : 0 ≤ B)
    (hfourier : ∀ h : ℤ, h ≠ 0 → h.natAbs < H →
      ‖ordinaryOrbitSum x h‖ ^ 2 ≤ B * (M : ℝ)) :
    ((Finset.univ.filter (fun ij : Fin M × Fin M =>
      circleDistance (x ij.2 - x ij.1) <
        (2 : ℝ) ^ k / (M : ℝ))).card : ℝ) ≤
      Real.pi ^ 2 * (1 + B / 2) * ((2 : ℝ) ^ k + 1) * (M : ℝ) := by
  classical
  subst H
  change ((scaleNearPairs x k).card : ℝ) ≤ _
  let H := adaptiveBandwidth M k
  have hH : 1 ≤ H := adaptiveBandwidth_pos M k hM hscale
  have hMposNat : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hHreal : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have hcard :
      ((scaleNearPairs x k).card : ℝ) =
        ∑ ij : Fin M × Fin M,
          if circleDistance (x ij.2 - x ij.1) <
              (2 : ℝ) ^ k / (M : ℝ) then 1 else 0 := by
    unfold scaleNearPairs
    norm_cast
    simp
  have hscaled :
      (4 * (H : ℝ) / Real.pi ^ 2) * ((scaleNearPairs x k).card : ℝ) ≤
        ∑ ij : Fin M × Fin M,
          fejerKernel (H - 1) (x ij.2 - x ij.1) := by
    rw [hcard, Finset.mul_sum]
    apply sum_le_sum
    intro ij hij
    split_ifs with hnear
    · simp only [mul_one]
      apply fejerKernel_pred_lower_of_circleDistance_lt H hH
      exact hnear.trans_le (scaleRadius_le_fejerRadius M k hM hscale)
    · simp only [mul_zero]
      exact Theory.PiDigits.T27.fejerKernel_nonneg _ _
  rw [orderedPair_fejerKernel_eq_ordinaryFejerEnergy x H hH] at hscaled
  have henergy := ordinaryFejerEnergy_le_of_nonzero_orbitSum_bound
    x H B hH hB (by simpa only [H] using hfourier)
  have hround :=
    (sampleSize_lt_four_mul_scale_mul_bandwidth M k hM hscale).le
  have hMtwo :
      (M : ℝ) ^ 2 ≤
        (4 * (2 : ℝ) ^ k * (H : ℝ)) * (M : ℝ) := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hround hMnonneg
  have hextra :
      0 ≤ 4 * (H : ℝ) * (M : ℝ) +
        2 * (H : ℝ) * (M : ℝ) * B * (2 : ℝ) ^ k := by
    positivity
  have hrough :
      (M : ℝ) ^ 2 + 2 * (H : ℝ) * B * (M : ℝ) ≤
        4 * (H : ℝ) * (1 + B / 2) * ((2 : ℝ) ^ k + 1) * (M : ℝ) := by
    calc
      (M : ℝ) ^ 2 + 2 * (H : ℝ) * B * (M : ℝ) ≤
          (4 * (2 : ℝ) ^ k * (H : ℝ)) * (M : ℝ) +
            2 * (H : ℝ) * B * (M : ℝ) := add_le_add_left hMtwo _
      _ ≤ 4 * (H : ℝ) * (1 + B / 2) *
          ((2 : ℝ) ^ k + 1) * (M : ℝ) := by
        nlinarith
  have henergyTarget :
      ordinaryFejerEnergy x H ≤
        4 * (H : ℝ) * (1 + B / 2) * ((2 : ℝ) ^ k + 1) * (M : ℝ) :=
    henergy.trans hrough
  have htargetNonneg :
      0 ≤ Real.pi ^ 2 * (1 + B / 2) *
        ((2 : ℝ) ^ k + 1) * (M : ℝ) := by positivity
  have hcoefficient : 0 < 4 * (H : ℝ) / Real.pi ^ 2 := by positivity
  have hmul :
      (4 * (H : ℝ) / Real.pi ^ 2) * ((scaleNearPairs x k).card : ℝ) ≤
        (4 * (H : ℝ) / Real.pi ^ 2) *
          (Real.pi ^ 2 * (1 + B / 2) *
            ((2 : ℝ) ^ k + 1) * (M : ℝ)) := by
    calc
      (4 * (H : ℝ) / Real.pi ^ 2) * ((scaleNearPairs x k).card : ℝ) ≤
          ordinaryFejerEnergy x H := hscaled
      _ ≤ 4 * (H : ℝ) * (1 + B / 2) *
          ((2 : ℝ) ^ k + 1) * (M : ℝ) := henergyTarget
      _ = (4 * (H : ℝ) / Real.pi ^ 2) *
          (Real.pi ^ 2 * (1 + B / 2) *
            ((2 : ℝ) ^ k + 1) * (M : ℝ)) := by
        field_simp [Real.pi_ne_zero]
  exact le_of_mul_le_mul_left hmul hcoefficient

/-- The scale-adaptive ordinary-orbit estimate left unproved for pi.  One
nonnegative normalization constant controls every large `n`, every complete
C5 scale `k`, and every nonzero frequency in the rounded bandwidth. -/
def PiScaleAdaptiveOrbitBound : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ 10 ^ n →
      ∀ h : ℤ, h ≠ 0 → h.natAbs < adaptiveBandwidth (10 ^ n) k →
        ‖piOrbitSum h (10 ^ n)‖ ^ 2 ≤ B * ((10 ^ n : ℕ) : ℝ)

/-- Literal expansion of the unproved pi orbit-sum hypothesis. -/
theorem piScaleAdaptiveOrbitBound_iff_quantifiers :
    PiScaleAdaptiveOrbitBound ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
        ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ 10 ^ n →
          ∃ M H : ℕ, M = 10 ^ n ∧ H = M / 2 ^ (k + 1) ∧
            ∀ h : ℤ, h ≠ 0 → h.natAbs < H →
              ‖piOrbitSum h M‖ ^ 2 ≤ B * (M : ℝ) := by
  constructor
  · rintro ⟨B, hB, n0, hn0, hfourier⟩
    refine ⟨B, hB, n0, hn0, ?_⟩
    intro n hn k hk
    exact ⟨10 ^ n, adaptiveBandwidth (10 ^ n) k, rfl, rfl,
      hfourier n hn k hk⟩
  · rintro ⟨B, hB, n0, hn0, hfourier⟩
    refine ⟨B, hB, n0, hn0, ?_⟩
    intro n hn k hk h hh0 hhH
    obtain ⟨M, H, hM, hH, hbound⟩ := hfourier n hn k hk
    subst M
    subst H
    exact hbound h hh0 hhH

/-- The pi orbit-sum hypothesis gives C5 with the explicit constant
`A = pi^2*(1+B/2)`, sample size `M=10^n`, rounded bandwidth
`H=M/2^(k+1)`, strict cutoff, and complete range `4^k≤M`. -/
theorem piScaleAdaptiveOrbitBound_implies_C5_explicit
    (horbit : PiScaleAdaptiveOrbitBound) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ 10 ^ n →
        ((Finset.univ.filter
          (fun ij : Fin (10 ^ n) × Fin (10 ^ n) =>
            circleDistance
                (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
              (2 : ℝ) ^ k / ((10 ^ n : ℕ) : ℝ))).card : ℝ) ≤
          (Real.pi ^ 2 * (1 + B / 2)) *
            ((2 : ℝ) ^ k + 1) * ((10 ^ n : ℕ) : ℝ) := by
  obtain ⟨B, hB, n0, hn0, hfourier⟩ := horbit
  refine ⟨B, hB, n0, hn0, ?_⟩
  intro n hn k hk
  have hn1 : 1 ≤ n := hn0.trans hn
  have hM : 2 ≤ 10 ^ n := by
    calc
      2 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hgeneric := scaleNearPairs_card_le_of_nonzero_orbitSum_bound
    (x := fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
    k (adaptiveBandwidth (10 ^ n) k) B rfl hM hk hB (by
      intro h hh0 hhH
      simpa only [ordinaryOrbitSum, piOrbitSum] using
        hfourier n hn k hk h hh0 hhH)
  exact hgeneric

/-- The fixed-pi C5 statement follows only from the displayed orbit-sum
hypothesis. -/
theorem piScaleAdaptiveOrbitBound_implies_C5
    (horbit : PiScaleAdaptiveOrbitBound) : PiMesoscopicPairCountC5 := by
  obtain ⟨B, hB, n0, hn0, hpairs⟩ :=
    piScaleAdaptiveOrbitBound_implies_C5_explicit horbit
  refine ⟨Real.pi ^ 2 * (1 + B / 2), by positivity, n0, hn0, ?_⟩
  intro n hn k hk
  simpa only [piMesoscopicNearPairs, mesoscopicSampleSize] using hpairs n hn k hk

/-- C4 follows conditionally through imported T9. -/
theorem piScaleAdaptiveOrbitBound_implies_C4
    (horbit : PiScaleAdaptiveOrbitBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n →
        piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
          C * ((10 ^ n : ℕ) : ℝ) ^ 2 := by
  simpa only [PiFejerSpectralHypothesis] using
    piMesoscopicPairCountC5_implies_C4
      (piScaleAdaptiveOrbitBound_implies_C5 horbit)

/-- C2 follows conditionally through imported T9 and T7. -/
theorem piScaleAdaptiveOrbitBound_implies_C2
    (horbit : PiScaleAdaptiveOrbitBound) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ M : ℕ, 1 ≤ M ∧
        (E_pi n M : ℝ) ≤
          (M : ℝ) ^ 2 * (10 : ℝ) ^ (-eta * (n : ℝ)) := by
  simpa only [PiExponentialCollisionC2] using
    piMesoscopicPairCountC5_implies_C2
      (piScaleAdaptiveOrbitBound_implies_C5 horbit)

/-- Canonical C1 follows only from the ordinary-orbit hypothesis. -/
theorem piScaleAdaptiveOrbitBound_implies_C1
    (horbit : PiScaleAdaptiveOrbitBound) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (10 : ℝ) ^ (eta * (n : ℝ)) ≤
          (canonicalFactorComplexity piDecimalStream n : ℝ) := by
  simpa only [PiPositiveFactorEntropyC1] using
    piMesoscopicPairCountC5_implies_C1
      (piScaleAdaptiveOrbitBound_implies_C5 horbit)

/-- The exact logical negation of canonical C1, with every quantifier and
strict reverse inequality visible. -/
theorem piFailureC1_iff_literal_quantifiers :
    (¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (10 : ℝ) ^ (eta * (n : ℝ)) ≤
          (canonicalFactorComplexity piDecimalStream n : ℝ)) ↔
      ∀ eta : ℝ, 0 < eta → ∀ N : ℕ, 1 ≤ N →
        ∃ n : ℕ, N ≤ n ∧
          (canonicalFactorComplexity piDecimalStream n : ℝ) <
            (10 : ℝ) ^ (eta * (n : ℝ)) := by
  push Not
  rfl

/-- Quantitative contrapositive.  Literal failure of C1 forces arbitrarily
late scales and arbitrarily large nonnegative normalizations to exhibit a
nonzero ordinary-orbit resonance.  No cancellation or entropy conclusion is
asserted. -/
theorem piFailureC1_implies_arbitrarily_large_scale_resonance
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ B : ℝ, 0 ≤ B → ∀ N : ℕ, 1 ≤ N →
      ∃ n k M H : ℕ, ∃ h : ℤ,
        N ≤ n ∧ M = 10 ^ n ∧ 4 ^ k ≤ M ∧
          H = M / 2 ^ (k + 1) ∧ h ≠ 0 ∧ h.natAbs < H ∧
            B * (M : ℝ) < ‖piOrbitSum h M‖ ^ 2 := by
  have hnotOrbit : ¬ PiScaleAdaptiveOrbitBound := by
    intro horbit
    apply hfailure
    exact piScaleAdaptiveOrbitBound_implies_C1 horbit
  unfold PiScaleAdaptiveOrbitBound at hnotOrbit
  push Not at hnotOrbit
  intro B hB N hN
  obtain ⟨n, hn, k, hk, h, hh0, hhH, hlarge⟩ := hnotOrbit B hB N hN
  refine ⟨n, k, 10 ^ n, adaptiveBandwidth (10 ^ n) k, h,
    hn, rfl, hk, rfl, hh0, hhH, ?_⟩
  simpa only using hlarge

end DecimalFactorComplexity.ScaleAdaptiveOrbitFourier

#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.adaptiveBandwidth_pos
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.scaleRadius_le_fejerRadius
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.sampleSize_lt_four_mul_scale_mul_bandwidth
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.orderedPair_fejerKernel_eq_ordinaryFejerEnergy
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.ordinaryOrbitSum_zero
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.fejerFrequencies_card
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.ordinaryFejerEnergy_le_of_nonzero_orbitSum_bound
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.scaleNearPairs_card_le_of_nonzero_orbitSum_bound
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piScaleAdaptiveOrbitBound_iff_quantifiers
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piScaleAdaptiveOrbitBound_implies_C5_explicit
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piScaleAdaptiveOrbitBound_implies_C5
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piScaleAdaptiveOrbitBound_implies_C4
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piScaleAdaptiveOrbitBound_implies_C2
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piScaleAdaptiveOrbitBound_implies_C1
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piFailureC1_iff_literal_quantifiers
#print axioms DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.piFailureC1_implies_arbitrarily_large_scale_resonance
