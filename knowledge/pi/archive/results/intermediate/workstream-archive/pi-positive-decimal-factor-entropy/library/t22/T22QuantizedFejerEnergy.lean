import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T10T10ScaleAdaptiveOrbitFourier
import TheoryLib.PiPositiveDecimalFactorEntropy.T16T16MicroscopicFullEntropy
import TheoryLib.PiPositiveDecimalFactorEntropy.T18T18FiniteCircleQuantization

/-!
# T22: aggregate finite-circle quantization of adaptive Fejer energy

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The generic part of this file compares the complete ordinary and floor-quantized
Fejer bands. Every theorem specialized to pi assumes the literal negation of
canonical C1. Their quantifiers are ordered `B`, `N`, ordinary witnesses
`n,k,M,H`, and then (in the finite-model theorem) the modulus `q`; neither
theorem asserts that C1 fails.

The final declaration records the bounded T15 literature audit. The aggregate
witness below supplies neither a uniform positive-density large spectrum in one
common modulus nor scale-uniform energy normalized by that modulus. Therefore
it asserts no applicability of an inverse theorem audited in T15.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.QuantizedFejerEnergy

open DecimalFactorComplexity
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.FiniteCircleQuantization
open DecimalFactorComplexity.MicroscopicFullEntropy
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.ScaleAdaptiveOrbitFourier
open DecimalFactorEntropy.FiniteFourierObstruction

/-- Complete Fejer-weighted energy of the floor-quantized orbit in `ZMod q`.
The range is the signed band `|h| < H`, including zero, and every triangular
weight `1 - |h|/H` is visible. -/
def quantizedFejerEnergy {M : ℕ} (x : Fin M → ℝ) (H q : ℕ) [NeZero q] : ℝ :=
  ∑ h ∈ fejerFrequencies H,
    fejerWeight H h * ‖quantizedOrbitSum x q h‖ ^ 2

/-- Literal expansion of the complete quantized band. -/
theorem quantizedFejerEnergy_eq_complete_band {M : ℕ} (x : Fin M → ℝ)
    (H q : ℕ) [NeZero q] :
    quantizedFejerEnergy x H q =
      ∑ h ∈ fejerFrequencies H,
        (1 - (h.natAbs : ℝ) / (H : ℝ)) *
          ‖∑ j : Fin M,
            quantizedCharacter q h (quantizedOrbit x q j)‖ ^ 2 := by
  rfl

/-- Every ordinary orbit sum has the trivial bound by its sample size. -/
theorem norm_ordinaryOrbitSum_le {M : ℕ} (x : Fin M → ℝ) (h : ℤ) :
    ‖ordinaryOrbitSum x h‖ ≤ M := by
  unfold ordinaryOrbitSum
  calc
    ‖∑ j : Fin M, Theory.PiDigits.T27.phase h (x j)‖ ≤
        ∑ j : Fin M, ‖Theory.PiDigits.T27.phase h (x j)‖ := norm_sum_le _ _
    _ = M := by simp [Theory.PiDigits.T27.norm_phase]

/-- Every quantized character sum has the same trivial sample-size bound. -/
theorem norm_quantizedOrbitSum_le {M : ℕ} (x : Fin M → ℝ) (q : ℕ)
    [NeZero q] (h : ℤ) : ‖quantizedOrbitSum x q h‖ ≤ M := by
  unfold quantizedOrbitSum
  calc
    ‖∑ j : Fin M, quantizedCharacter q h (quantizedOrbit x q j)‖ ≤
        ∑ j : Fin M,
          ‖quantizedCharacter q h (quantizedOrbit x q j)‖ := norm_sum_le _ _
    _ = M := by simp [AddChar.norm_apply]

/-- Squaring two complex norms costs their sum in the reverse triangle
inequality. This public helper is independent of quantization. -/
theorem abs_norm_sq_sub_norm_sq_le (z w : ℂ) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ ‖z - w‖ * (‖z‖ + ‖w‖) := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w)
      (show (0 : ℝ) ≤ ‖z‖ + ‖w‖ by positivity))

/-- T18's pointwise one-cell estimate summed over the complete sample. Unlike
alias prevention, this approximation does not require `2H < q`. -/
theorem quantizedOrbitSum_error {M : ℕ} (x : Fin M → ℝ) (q : ℕ)
    [NeZero q] (h : ℤ) :
    ‖quantizedOrbitSum x q h - ordinaryOrbitSum x h‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) * M / q := by
  rw [quantizedOrbitSum, ordinaryOrbitSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j : Fin M,
        (quantizedCharacter q h (quantizedOrbit x q j) -
          Theory.PiDigits.T27.phase h (x j))‖ ≤
        ∑ j : Fin M,
          ‖quantizedCharacter q h (quantizedOrbit x q j) -
            Theory.PiDigits.T27.phase h (x j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin M, 2 * Real.pi * (h.natAbs : ℝ) / q := by
      apply Finset.sum_le_sum
      intro j _hj
      exact norm_quantizedCharacter_sub_phase_le x j h
    _ = 2 * Real.pi * (h.natAbs : ℝ) * M / q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- T18's one-cell floor error, after weighted squaring at one frequency.
The constant is exactly `4*pi*|h|*M^2/q`. -/
theorem weighted_sq_perturbation_le {M : ℕ} (x : Fin M → ℝ)
    (H q : ℕ) [NeZero q] (h : ℤ) (hh : h ∈ fejerFrequencies H)
    (hH : 1 ≤ H) :
    |fejerWeight H h * ‖quantizedOrbitSum x q h‖ ^ 2 -
        fejerWeight H h * ‖ordinaryOrbitSum x h‖ ^ 2| ≤
      fejerWeight H h *
        (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q) := by
  have habs : h.natAbs < H := (mem_fejerFrequencies_iff hH).mp hh
  have hHreal : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have habsReal : (h.natAbs : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (Nat.le_of_lt habs)
  have hw0 : 0 ≤ fejerWeight H h := by
    unfold fejerWeight
    exact sub_nonneg.mpr ((div_le_one hHreal).2 habsReal)
  have hsquare := abs_norm_sq_sub_norm_sq_le
    (quantizedOrbitSum x q h) (ordinaryOrbitSum x h)
  have herror := quantizedOrbitSum_error x q h
  have hquant := norm_quantizedOrbitSum_le x q h
  have hord := norm_ordinaryOrbitSum_le x h
  have hsquare' :
      |‖quantizedOrbitSum x q h‖ ^ 2 - ‖ordinaryOrbitSum x h‖ ^ 2| ≤
        4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q := by
    calc
      |‖quantizedOrbitSum x q h‖ ^ 2 - ‖ordinaryOrbitSum x h‖ ^ 2| ≤
          ‖quantizedOrbitSum x q h - ordinaryOrbitSum x h‖ *
            (‖quantizedOrbitSum x q h‖ + ‖ordinaryOrbitSum x h‖) := hsquare
      _ ≤ (2 * Real.pi * (h.natAbs : ℝ) * M / q) *
            ((M : ℝ) + M) := by gcongr
      _ = 4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q := by ring
  rw [← mul_sub, abs_mul, abs_of_nonneg hw0]
  exact mul_le_mul_of_nonneg_left hsquare' hw0

/-- Exact aggregate perturbation bound over the complete signed Fejer band.
No frequency or triangular weight is suppressed. -/
theorem abs_quantizedFejerEnergy_sub_ordinaryFejerEnergy_le_weightedLoss
    {M : ℕ} (x : Fin M → ℝ) (H q : ℕ) [NeZero q] (hH : 1 ≤ H) :
    |quantizedFejerEnergy x H q - ordinaryFejerEnergy x H| ≤
      ∑ h ∈ fejerFrequencies H,
        fejerWeight H h *
          (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q) := by
  unfold quantizedFejerEnergy ordinaryFejerEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ h ∈ fejerFrequencies H,
        (fejerWeight H h * ‖quantizedOrbitSum x q h‖ ^ 2 -
          fejerWeight H h * ‖ordinaryOrbitSum x h‖ ^ 2)| ≤
        ∑ h ∈ fejerFrequencies H,
          |fejerWeight H h * ‖quantizedOrbitSum x q h‖ ^ 2 -
            fejerWeight H h * ‖ordinaryOrbitSum x h‖ ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ fejerFrequencies H,
        fejerWeight H h *
          (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q) := by
      apply Finset.sum_le_sum
      intro h hh
      exact weighted_sq_perturbation_le x H q h hh hH

/-- A closed-form aggregate loss. It retains all parameters and uses only
`|h| < H`, weight at most one, and at most `2H` signed frequencies. -/
theorem abs_quantizedFejerEnergy_sub_ordinaryFejerEnergy_le
    {M : ℕ} (x : Fin M → ℝ) (H q : ℕ) [NeZero q] (hH : 1 ≤ H) :
    |quantizedFejerEnergy x H q - ordinaryFejerEnergy x H| ≤
      8 * Real.pi * (H : ℝ) ^ 2 * (M : ℝ) ^ 2 / q := by
  have hexact :=
    abs_quantizedFejerEnergy_sub_ordinaryFejerEnergy_le_weightedLoss
      x H q hH
  have hHreal : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have hqNat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hqNat
  have hterm :
      (∑ h ∈ fejerFrequencies H,
        fejerWeight H h *
          (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q)) ≤
        ∑ _h ∈ fejerFrequencies H,
          (4 * Real.pi * (H : ℝ) * (M : ℝ) ^ 2 / q) := by
    apply Finset.sum_le_sum
    intro h hh
    have habs : h.natAbs < H := (mem_fejerFrequencies_iff hH).mp hh
    have habsReal : (h.natAbs : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast (Nat.le_of_lt habs)
    have hw0 : 0 ≤ fejerWeight H h := by
      unfold fejerWeight
      exact sub_nonneg.mpr ((div_le_one hHreal).2 habsReal)
    have hw1 : fejerWeight H h ≤ 1 := by
      unfold fejerWeight
      exact sub_le_self 1 (div_nonneg (by positivity) hHreal.le)
    have hinner0 :
        0 ≤ 4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q := by
      positivity
    have hfactor0 : 0 ≤ 4 * Real.pi * (M : ℝ) ^ 2 / q := by positivity
    calc
      fejerWeight H h *
          (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q) ≤
          1 * (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q) :=
        mul_le_mul_of_nonneg_right hw1 hinner0
      _ = (h.natAbs : ℝ) * (4 * Real.pi * (M : ℝ) ^ 2 / q) := by ring
      _ ≤ (H : ℝ) * (4 * Real.pi * (M : ℝ) ^ 2 / q) :=
        mul_le_mul_of_nonneg_right habsReal hfactor0
      _ = 4 * Real.pi * (H : ℝ) * (M : ℝ) ^ 2 / q := by ring
  have hcardNat : (fejerFrequencies H).card ≤ 2 * H := by
    rw [fejerFrequencies_card H hH]
    omega
  have hcard : ((fejerFrequencies H).card : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast hcardNat
  calc
    |quantizedFejerEnergy x H q - ordinaryFejerEnergy x H| ≤
        ∑ h ∈ fejerFrequencies H,
          fejerWeight H h *
            (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q) := hexact
    _ ≤ ∑ _h ∈ fejerFrequencies H,
          (4 * Real.pi * (H : ℝ) * (M : ℝ) ^ 2 / q) := hterm
    _ = ((fejerFrequencies H).card : ℝ) *
          (4 * Real.pi * (H : ℝ) * (M : ℝ) ^ 2 / q) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (H : ℝ)) *
          (4 * Real.pi * (H : ℝ) * (M : ℝ) ^ 2 / q) := by
      gcongr
    _ = 8 * Real.pi * (H : ℝ) ^ 2 * (M : ℝ) ^ 2 / q := by ring

/-- Literal failure of canonical C1 makes T7's ordinary Fejer energy,
normalized by `M^2`, arbitrarily large. The complete adaptive band is exposed
as the `k = 0` instance `H = M / 2^(k+1)`. The order `B`, `N`, then
`n,k,M,H` matches the universal-before-witness order isolated in T10. -/
theorem piFailureC1_implies_arbitrarily_large_normalized_ordinaryFejerEnergy
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ B : ℝ, 0 ≤ B → ∀ N : ℕ, 1 ≤ N →
      ∃ n k M H : ℕ,
        N ≤ n ∧ k = 0 ∧ M = 10 ^ n ∧ 4 ^ k ≤ M ∧
          H = M / 2 ^ (k + 1) ∧
          (B + 1) * (M : ℝ) ^ 2 <
            ordinaryFejerEnergy
              (fun j : Fin M => piDecimalShiftOrbit j) H := by
  have hnotC4 : ¬ PiFejerSpectralHypothesis := by
    intro hC4
    apply hfailure
    exact piFejerSpectralHypothesis_implies_C1 hC4
  unfold PiFejerSpectralHypothesis at hnotC4
  push Not at hnotC4
  intro B hB N hN
  obtain ⟨n, hn, hlarge⟩ := hnotC4 (B + 1) (by linarith) N hN
  refine ⟨n, 0, 10 ^ n, 10 ^ n / 2, hn, rfl, rfl, ?_, ?_, ?_⟩
  · exact one_le_pow₀ (by norm_num)
  · norm_num
  · simpa [ordinaryFejerEnergy, piFejerEnergy, ordinaryOrbitSum, piOrbitSum]
      using hlarge

/-- Literal failure of C1 conditionally gives arbitrarily large `M^2`-
normalized energy in one finite cyclic model. Every range, weight, modulus,
rounding loss, and growth quantifier is displayed. In particular `q` is chosen
only after `n,k,M,H`, preserving T10's witness order. -/
theorem piFailureC1_implies_arbitrarily_large_normalized_quantizedFejerEnergy
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ B : ℝ, 0 ≤ B → ∀ N : ℕ, 1 ≤ N →
      ∃ n k M H : ℕ,
        N ≤ n ∧ k = 0 ∧ M = 10 ^ n ∧ 4 ^ k ≤ M ∧
          H = M / 2 ^ (k + 1) ∧
          ∃ q : ℕ, ∃ _hq0 : NeZero q,
            2 * H < q ∧
            (∀ h : ℤ, h ≠ 0 → h.natAbs < H →
              quantizedCharacter q h ≠ 0) ∧
            IsProbability
              (orbitCellMeasure
                (fun j : Fin M => piDecimalShiftOrbit j) : ZMod q → ℝ) ∧
            |quantizedFejerEnergy
                (fun j : Fin M => piDecimalShiftOrbit j) H q -
              ordinaryFejerEnergy
                (fun j : Fin M => piDecimalShiftOrbit j) H| ≤
              ∑ h ∈ fejerFrequencies H,
                fejerWeight H h *
                  (4 * Real.pi * (h.natAbs : ℝ) * (M : ℝ) ^ 2 / q) ∧
            |quantizedFejerEnergy
                (fun j : Fin M => piDecimalShiftOrbit j) H q -
              ordinaryFejerEnergy
                (fun j : Fin M => piDecimalShiftOrbit j) H| ≤
              8 * Real.pi * (H : ℝ) ^ 2 * (M : ℝ) ^ 2 / q ∧
            8 * Real.pi * (H : ℝ) ^ 2 * (M : ℝ) ^ 2 / q <
              (M : ℝ) ^ 2 ∧
            B * (M : ℝ) ^ 2 <
              quantizedFejerEnergy
                (fun j : Fin M => piDecimalShiftOrbit j) H q ∧
            B < quantizedFejerEnergy
                (fun j : Fin M => piDecimalShiftOrbit j) H q /
              (M : ℝ) ^ 2 := by
  intro B hB N hN
  obtain ⟨n, k, M, H, hn, hk, hM, hscale, hH, hlarge⟩ :=
    piFailureC1_implies_arbitrarily_large_normalized_ordinaryFejerEnergy
      hfailure B hB N hN
  have hn1 : 1 ≤ n := hN.trans hn
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hpowpos : 0 < 10 ^ n := by positivity
  have hhalf : 1 ≤ 10 ^ n / 2 := by
    have hten : 2 ≤ 10 ^ n := by
      calc
        2 ≤ 10 ^ 1 := by norm_num
        _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hHpos : 1 ≤ H := by simpa [hH, hM, hk] using hhalf
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt
    (max (((2 * H : ℕ) : ℝ))
      (8 * Real.pi * (H : ℝ) ^ 2))
  have hqAliasReal : ((2 * H : ℕ) : ℝ) < q :=
    (le_max_left _ _).trans_lt hq
  have hqAlias : 2 * H < q := by exact_mod_cast hqAliasReal
  have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hqAlias
  letI : NeZero q := ⟨hqPos.ne'⟩
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hqPos
  have hcoefficient : 8 * Real.pi * (H : ℝ) ^ 2 < (q : ℝ) :=
    (le_max_right _ _).trans_lt hq
  let x : Fin M → ℝ := fun j => piDecimalShiftOrbit j
  have hexact :=
    abs_quantizedFejerEnergy_sub_ordinaryFejerEnergy_le_weightedLoss
      x H q hHpos
  have hcoarse :=
    abs_quantizedFejerEnergy_sub_ordinaryFejerEnergy_le x H q hHpos
  have hsmall :
      8 * Real.pi * (H : ℝ) ^ 2 * (M : ℝ) ^ 2 / q <
        (M : ℝ) ^ 2 := by
    rw [div_lt_iff₀ hqReal]
    nlinarith [sq_pos_of_pos hMreal]
  have hdiff :
      ordinaryFejerEnergy x H - quantizedFejerEnergy x H q <
        (M : ℝ) ^ 2 := by
    calc
      ordinaryFejerEnergy x H - quantizedFejerEnergy x H q =
          -(quantizedFejerEnergy x H q - ordinaryFejerEnergy x H) := by ring
      _ ≤ |quantizedFejerEnergy x H q - ordinaryFejerEnergy x H| :=
        neg_le_abs _
      _ ≤ 8 * Real.pi * (H : ℝ) ^ 2 * (M : ℝ) ^ 2 / q := hcoarse
      _ < (M : ℝ) ^ 2 := hsmall
  have hlargeX :
      (B + 1) * (M : ℝ) ^ 2 < ordinaryFejerEnergy x H := by
    simpa only [x] using hlarge
  have hquantized :
      B * (M : ℝ) ^ 2 < quantizedFejerEnergy x H q := by
    nlinarith
  have hnormalized :
      B < quantizedFejerEnergy x H q / (M : ℝ) ^ 2 := by
    exact (lt_div_iff₀ (sq_pos_of_pos hMreal)).2 hquantized
  refine ⟨n, k, M, H, hn, hk, hM, hscale, hH, q, inferInstance,
    hqAlias, ?_, ?_, ?_, ?_, hsmall, ?_, ?_⟩
  · intro h hh0 hhH
    exact lowFrequency_quantizedCharacter_ne_zero q H hqAlias h hh0 hhH
  · simpa only [x] using orbitCellMeasure_isProbability x hMpos
  · simpa only [x] using hexact
  · simpa only [x] using hcoarse
  · simpa only [x] using hquantized
  · simpa only [x] using hnormalized

/-- The two precise kinds of uniform input that remain absent after T22.

`commonPositiveDensityFixedThresholdSpectrum` means fixed `delta,rho > 0`,
independent of `B,N` and of the witnesses, with at least `rho*q` characters
above the normalized threshold `delta` in one finite model. T22 gives only an
aggregate whose band and modulus follow the requested bound.

`scaleUniformEnergyPerModulus` means a fixed `epsilon > 0`, independent of all
witnesses, lower-bounding quantized energy divided by `q*M^2` (or an equivalent
positive-density normalization). T22 only lower-bounds energy divided by
`M^2`, while `q` is chosen after `M,H` to absorb rounding, so it supplies no
such modulus normalization. -/
inductive MissingT15Hypothesis where
  | commonPositiveDensityFixedThresholdSpectrum
  | scaleUniformEnergyPerModulus
  deriving DecidableEq, Repr

/-- Machine-readable status for the bounded, source-pinned T15 corpus only.
It is not a claim that no other inverse theorem exists. -/
structure T15ApplicabilityComparison where
  auditedInverseTheoremApplies : Bool
  missingHypotheses : List MissingT15Hypothesis
  deriving DecidableEq, Repr

/-- Comparison source: `library/t15/T15_INVERSE_STRUCTURE_AUDIT.md`, SHA-256
`d68e9b853a4628a01252834178c2b1dc8a9dc2c113135491543579569796cb01`.
T15 audited T10/T13, not T22. Since T22 still supplies neither datum named
here, this declaration deliberately records no new applicability claim. -/
def t15ApplicabilityComparison : T15ApplicabilityComparison where
  auditedInverseTheoremApplies := false
  missingHypotheses :=
    [.commonPositiveDensityFixedThresholdSpectrum, .scaleUniformEnergyPerModulus]

/-- Exact T15 comparison: no audited inverse-theorem applicability is asserted,
and both unavailable normalization hypotheses are named. -/
theorem t15_no_inverse_theorem_applicability :
    t15ApplicabilityComparison.auditedInverseTheoremApplies = false ∧
      t15ApplicabilityComparison.missingHypotheses =
        [.commonPositiveDensityFixedThresholdSpectrum,
          .scaleUniformEnergyPerModulus] := by
  constructor <;> rfl

end DecimalFactorComplexity.QuantizedFejerEnergy

#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.quantizedFejerEnergy_eq_complete_band
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.norm_ordinaryOrbitSum_le
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.norm_quantizedOrbitSum_le
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.abs_norm_sq_sub_norm_sq_le
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.quantizedOrbitSum_error
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.weighted_sq_perturbation_le
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.abs_quantizedFejerEnergy_sub_ordinaryFejerEnergy_le_weightedLoss
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.abs_quantizedFejerEnergy_sub_ordinaryFejerEnergy_le
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.piFailureC1_implies_arbitrarily_large_normalized_ordinaryFejerEnergy
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.piFailureC1_implies_arbitrarily_large_normalized_quantizedFejerEnergy
#print axioms DecimalFactorComplexity.QuantizedFejerEnergy.t15_no_inverse_theorem_applicability
