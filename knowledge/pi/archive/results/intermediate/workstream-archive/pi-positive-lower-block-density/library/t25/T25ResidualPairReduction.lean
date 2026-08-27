import TheoryLib.PiPositiveLowerBlockDensity.T23T23FiniteCylinderEnergyCriterion
import TheoryLib.PiLacunaryNearReturnSparsity.T1LagDecomposition
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy

/-!
# T25: effective irrationality and the residual collision region

Canonical question: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module is conditional. In particular, the pinned T24 source estimate is
an explicit premise, residual-pair decay is not proved for pi, and no
unconditional claim about pi or positive lower block density is made.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.PositiveLowerBlockDensity.T25

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T23
open DecimalFactorComplexity
open DecimalFactorComplexity.LagDecomposition
open DecimalFactorComplexity.FiniteCylinderEnergy

/-- The structured denominator attached to starts `n` and `n + r`. -/
def structuredDenominator (n r : ℕ) : ℕ := 10 ^ n * (10 ^ r - 1)

/-- An effective irrationality premise in the source theorem's rational form.
The constants and denominator onset are all explicit. -/
def EffectiveIrrationality
    (x μ c : ℝ) (Q0 : ℕ) : Prop :=
  0 < c ∧ 1 < μ ∧
    ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ p : ℤ,
      c / (q : ℝ) ^ μ < |x - (p : ℝ) / q|

/-- Quantifier audit for the effective irrationality premise. -/
theorem effectiveIrrationality_iff_quantifiers
    (x μ c : ℝ) (Q0 : ℕ) :
    EffectiveIrrationality x μ c Q0 ↔
      0 < c ∧ 1 < μ ∧
        ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ p : ℤ,
          c / (q : ℝ) ^ μ < |x - (p : ℝ) / q| := by
  rfl

/-- The exact arithmetic region in which the irrationality premise excludes
the strict decimal near return. Equality at the decimal radius is included
because the near-return inequality itself is strict. -/
def ArithmeticExcluded
    (μ c : ℝ) (Q0 m n r : ℕ) : Prop :=
  Q0 ≤ structuredDenominator n r ∧
    ((10 : ℝ) ^ m)⁻¹ ≤
      (structuredDenominator n r : ℝ) *
        (c / (structuredDenominator n r : ℝ) ^ μ)

/-- Upper-triangular starts at lag `r` satisfying the strict near-return
condition in T1's accepted lag decomposition. -/
def nearReturnStarts (m N r : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (N - r)).filter fun n =>
      circleDistance
        ((10 : ℝ) ^ n * ((10 : ℝ) ^ r - 1) * Real.pi) <
          ((10 : ℝ) ^ m)⁻¹

/-- Near-return starts lying in the arithmetic exclusion region. -/
def excludedNearReturnStarts
    (μ c : ℝ) (Q0 m N r : ℕ) : Finset ℕ := by
  classical
  exact (nearReturnStarts m N r).filter fun n =>
      ArithmeticExcluded μ c Q0 m n r

/-- The complementary near-return starts not controlled by the effective
irrationality premise. -/
def residualNearReturnStarts
    (μ c : ℝ) (Q0 m N r : ℕ) : Finset ℕ := by
  classical
  exact (nearReturnStarts m N r).filter fun n =>
      ¬ ArithmeticExcluded μ c Q0 m n r

/-- Ordered off-diagonal contribution of the excluded upper-triangular pairs.
The factor two restores both orientations. -/
def excludedPairCount
    (μ c : ℝ) (Q0 m N : ℕ) : ℕ :=
  2 * ∑ r ∈ Finset.Icc 1 (N - 1),
    (excludedNearReturnStarts μ c Q0 m N r).card

/-- Ordered off-diagonal contribution left unresolved by arithmetic
separation. -/
def residualPairCount
    (μ c : ℝ) (Q0 m N : ℕ) : ℕ :=
  2 * ∑ r ∈ Finset.Icc 1 (N - 1),
    (residualNearReturnStarts μ c Q0 m N r).card

/-- Strict circle distance is witnessed by an integer translate. -/
theorem exists_int_abs_sub_lt_of_circleDistance_lt
    {x ρ : ℝ} (h : circleDistance x < ρ) :
    ∃ p : ℤ, |x - p| < ρ := by
  unfold circleDistance at h
  obtain ⟨v, ⟨p, rfl⟩, hp⟩ :=
    exists_lt_of_csInf_lt (Set.range_nonempty fun p : ℤ => |x - (p : ℝ)|) h
  exact ⟨p, hp⟩

/-- The real lacunary multiplier is exactly the structured natural
denominator. -/
theorem structuredDenominator_cast (n r : ℕ) :
    (structuredDenominator n r : ℝ) =
      (10 : ℝ) ^ n * ((10 : ℝ) ^ r - 1) := by
  unfold structuredDenominator
  push_cast
  rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))]
  norm_num

/-- Equal length-`m` decimal blocks at starts `n` and `n+r` force the strict
near-integer relation at `q = 10^n(10^r-1)`. The strict boundary is inherited
from the accepted half-open decimal-cylinder theorem. -/
theorem equal_decimalBlocks_implies_structured_nearInteger
    (m n r : ℕ) (_hr : 0 < r)
    (hblocks : factorAt piDecimalStream m n =
      factorAt piDecimalStream m (n + r)) :
    circleDistance
        ((structuredDenominator n r : ℝ) * Real.pi) <
      ((10 : ℝ) ^ m)⁻¹ := by
  have hnear := pi_factor_eq_implies_circleDistance_lt m hblocks
  rw [pow_lag_factorization] at hnear
  rw [structuredDenominator_cast]
  exact hnear

/-- Integer-witness form of the same strict decimal-boundary relation. -/
theorem equal_decimalBlocks_implies_exists_integer_relation
    (m n r : ℕ) (hr : 0 < r)
    (hblocks : factorAt piDecimalStream m n =
      factorAt piDecimalStream m (n + r)) :
    ∃ p : ℤ,
      |(structuredDenominator n r : ℝ) * Real.pi - p| <
        ((10 : ℝ) ^ m)⁻¹ := by
  exact exists_int_abs_sub_lt_of_circleDistance_lt
    (equal_decimalBlocks_implies_structured_nearInteger m n r hr hblocks)

/-- In the explicit arithmetic range, the effective irrationality premise
excludes the strict structured near return. -/
theorem effectiveIrrationality_excludes_structured_nearReturn
    {x μ c : ℝ} {Q0 m n r : ℕ} (hr : 0 < r)
    (hIrr : EffectiveIrrationality x μ c Q0)
    (hExcluded : ArithmeticExcluded μ c Q0 m n r) :
    ¬ circleDistance
        ((structuredDenominator n r : ℝ) * x) <
      ((10 : ℝ) ^ m)⁻¹ := by
  intro hnear
  obtain ⟨p, hp⟩ := exists_int_abs_sub_lt_of_circleDistance_lt hnear
  have hpow : 1 < 10 ^ r := one_lt_pow₀ (by norm_num) hr.ne'
  have hqNat : 0 < structuredDenominator n r := by
    unfold structuredDenominator
    exact Nat.mul_pos (by positivity) (by omega)
  have hqReal : (0 : ℝ) < structuredDenominator n r := by
    exact_mod_cast hqNat
  have hlower := hIrr.2.2 (structuredDenominator n r)
    hExcluded.1 hqNat p
  have hscaled := mul_lt_mul_of_pos_left hlower hqReal
  have habs :
      (structuredDenominator n r : ℝ) *
          |x - (p : ℝ) / (structuredDenominator n r : ℝ)| =
        |(structuredDenominator n r : ℝ) * x - p| := by
    calc
      (structuredDenominator n r : ℝ) *
          |x - (p : ℝ) / (structuredDenominator n r : ℝ)| =
          |(structuredDenominator n r : ℝ)| *
            |x - (p : ℝ) / (structuredDenominator n r : ℝ)| := by
              rw [abs_of_pos hqReal]
      _ = |(structuredDenominator n r : ℝ) *
          (x - (p : ℝ) / (structuredDenominator n r : ℝ))| := by
            rw [abs_mul]
      _ = |(structuredDenominator n r : ℝ) * x - p| := by
            congr 1
            field_simp
  rw [habs] at hscaled
  linarith [hExcluded.2]

/-- Consequently, equal pi blocks are impossible in the excluded range. -/
theorem effectiveIrrationality_excludes_equal_decimalBlocks
    {μ c : ℝ} {Q0 m n r : ℕ} (hr : 0 < r)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hExcluded : ArithmeticExcluded μ c Q0 m n r) :
    ¬ factorAt piDecimalStream m n =
      factorAt piDecimalStream m (n + r) := by
  intro hblocks
  exact effectiveIrrationality_excludes_structured_nearReturn hr hIrr hExcluded
    (equal_decimalBlocks_implies_structured_nearInteger m n r hr hblocks)

/-- At each lag, strict near returns partition exactly into the arithmetic
excluded region and its residual complement. -/
theorem nearReturnStarts_card_eq_excluded_add_residual
    (μ c : ℝ) (Q0 m N r : ℕ) :
    (nearReturnStarts m N r).card =
      (excludedNearReturnStarts μ c Q0 m N r).card +
        (residualNearReturnStarts μ c Q0 m N r).card := by
  classical
  unfold excludedNearReturnStarts residualNearReturnStarts
  exact (Finset.card_filter_add_card_filter_not
    (s := nearReturnStarts m N r)
    (p := fun n => ArithmeticExcluded μ c Q0 m n r)).symm

/-- T1's ordered near-return count is exactly diagonal plus excluded plus
residual ordered pairs. -/
theorem Q_pi_eq_diagonal_add_excluded_add_residual
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    Q_pi m N =
      N + excludedPairCount μ c Q0 m N +
        residualPairCount μ c Q0 m N := by
  rw [Q_pi_orderedPair_lag_decomposition m N hm hN]
  change N + 2 * ∑ r ∈ Finset.Icc 1 (N - 1),
      (nearReturnStarts m N r).card = _
  have hsum :
      (∑ r ∈ Finset.Icc 1 (N - 1), (nearReturnStarts m N r).card) =
        (∑ r ∈ Finset.Icc 1 (N - 1),
            (excludedNearReturnStarts μ c Q0 m N r).card) +
          ∑ r ∈ Finset.Icc 1 (N - 1),
            (residualNearReturnStarts μ c Q0 m N r).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [nearReturnStarts_card_eq_excluded_add_residual]
  rw [hsum]
  unfold excludedPairCount residualPairCount
  omega

/-- Under effective irrationality, every pair assigned to the excluded region
is absent. -/
theorem excludedPairCount_eq_zero
    {μ c : ℝ} {Q0 m N : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0) :
    excludedPairCount μ c Q0 m N = 0 := by
  classical
  unfold excludedPairCount
  apply Nat.mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro r hr
  unfold excludedNearReturnStarts
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hnNear hExcluded
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hnot := effectiveIrrationality_excludes_structured_nearReturn
    hrpos hIrr hExcluded
  rw [structuredDenominator_cast] at hnot
  have hnData : n < N - r ∧
      circleDistance
          ((10 : ℝ) ^ n * ((10 : ℝ) ^ r - 1) * Real.pi) <
        ((10 : ℝ) ^ m)⁻¹ := by
    simpa [nearReturnStarts] using hnNear
  exact hnot hnData.2

/-- T23's energy is bounded by the normalized diagonal/excluded/residual
partition. This theorem states the pair partition at the energy interface. -/
theorem E_pi_le_partitioned_pair_count
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    T23.E_pi m N ≤
      ((N + excludedPairCount μ c Q0 m N +
        residualPairCount μ c Q0 m N : ℕ) : ℝ) / (N : ℝ) ^ 2 := by
  rw [E_pi_eq_normalizedPiCylinderCollisionEnergy]
  calc
    normalizedPiCylinderCollisionEnergy m N ≤
        (Q_pi m N : ℝ) / (N : ℝ) ^ 2 :=
      (normalizedPiCylinderCollisionEnergy_Q_pi_comparison m N hN).1
    _ = ((N + excludedPairCount μ c Q0 m N +
          residualPairCount μ c Q0 m N : ℕ) : ℝ) / (N : ℝ) ^ 2 := by
      rw [Q_pi_eq_diagonal_add_excluded_add_residual μ c Q0 m N hm hN]

/-- Under the arithmetic premise only the diagonal and residual pair counts
remain in the energy upper bound. -/
theorem E_pi_le_diagonal_add_residual
    {μ c : ℝ} {Q0 m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0) :
    T23.E_pi m N ≤
      ((N + residualPairCount μ c Q0 m N : ℕ) : ℝ) /
        (N : ℝ) ^ 2 := by
  have hbound := E_pi_le_partitioned_pair_count μ c Q0 m N hm hN
  rw [excludedPairCount_eq_zero hIrr] at hbound
  simpa using hbound

/-- The unresolved aggregate hypothesis. It retains T23's exact every-`s<1`,
all-later-`N`, and all-positive-`m` quantifiers. The diagonal is displayed
separately from the residual off-diagonal contribution. -/
def PiResidualPairDecay (μ c : ℝ) (Q0 : ℕ) : Prop :=
  EffectiveIrrationality Real.pi μ c Q0 ∧
    ∀ s : ℝ, 0 < s → s < 1 →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N → ∀ m : ℕ, 1 ≤ m →
          ((N + residualPairCount μ c Q0 m N : ℕ) : ℝ) /
              (N : ℝ) ^ 2 ≤
            C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (N : ℝ))

/-- Quantifier audit for the residual hypothesis. -/
theorem piResidualPairDecay_iff_quantifiers (μ c : ℝ) (Q0 : ℕ) :
    PiResidualPairDecay μ c Q0 ↔
      EffectiveIrrationality Real.pi μ c Q0 ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧
            ∀ N : ℕ, N0 ≤ N → ∀ m : ℕ, 1 ≤ m →
              ((N + residualPairCount μ c Q0 m N : ℕ) : ℝ) /
                  (N : ℝ) ^ 2 ≤
                C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (N : ℝ)) := by
  rfl

/-- Residual-pair decay supplies T23's full-dimensional energy hypothesis. -/
theorem piResidualPairDecay_implies_T23
    {μ c : ℝ} {Q0 : ℕ} (hResidual : PiResidualPairDecay μ c Q0) :
    PiFullDimensionalCylinderEnergyDecay := by
  rcases hResidual with ⟨hIrr, hdecay⟩
  intro s hs0 hs1
  obtain ⟨C, hC, N0, hN0, hall⟩ := hdecay s hs0 hs1
  refine ⟨C, hC, N0, ?_⟩
  intro N hN m hm
  exact (E_pi_le_diagonal_add_residual hm (hN0.trans hN) hIrr).trans
    (hall N hN m hm)

/-- The residual-pair hypothesis conditionally implies T1's unchanged
canonical positive-lower-block-density predicate. -/
theorem piResidualPairDecay_implies_piPositiveLowerBlockDensity
    {μ c : ℝ} {Q0 : ℕ} (hResidual : PiResidualPairDecay μ c Q0) :
    PiPositiveLowerBlockDensity := by
  exact piFullDimensionalCylinderEnergyDecay_implies_piPositiveLowerBlockDensity
    (piResidualPairDecay_implies_T23 hResidual)

/-- Exact rational encoding of T24's strongest pinned exponent `7.104`. -/
def t24StrongestMu : ℝ := 888 / 125

/-- The corresponding near-integer exponent loss `7.104 - 1 = 6.104`. -/
def t24StrongestLoss : ℝ := 763 / 125

theorem t24StrongestMu_eq_decimal : t24StrongestMu = 7.104 := by
  norm_num [t24StrongestMu]

theorem t24StrongestLoss_eq_decimal : t24StrongestLoss = 6.104 := by
  norm_num [t24StrongestLoss]

theorem t24StrongestMu_sub_one : t24StrongestMu - 1 = t24StrongestLoss := by
  norm_num [t24StrongestMu, t24StrongestLoss]

/-- The rational-approximation lower bound at exponent `7.104` becomes the
near-integer lower bound at the displayed loss exponent `6.104`. -/
theorem t24Strongest_scaled_rationalBound_eq_loss
    {q : ℕ} (hq : 0 < q) :
    (q : ℝ) * (1 / (q : ℝ) ^ t24StrongestMu) =
      (q : ℝ) ^ (-t24StrongestLoss) := by
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (q : ℝ) * (1 / (q : ℝ) ^ t24StrongestMu) =
        (q : ℝ) ^ (1 : ℝ) / (q : ℝ) ^ t24StrongestMu := by
      rw [Real.rpow_one]
      ring
    _ = (q : ℝ) ^ ((1 : ℝ) - t24StrongestMu) := by
      rw [Real.rpow_sub hqReal]
    _ = (q : ℝ) ^ (-t24StrongestLoss) := by
      congr 1
      norm_num [t24StrongestMu, t24StrongestLoss]

/-- T24's strongest pinned row, specialized without asserting its source
theorem. The effective `7.104` estimate and its unspecified onset `Q0` remain
an explicit external premise. -/
theorem t24StrongestPinnedRow_excludes_equal_decimalBlocks
    (Q0 m n r : ℕ) (hr : 0 < r)
    (hSource : EffectiveIrrationality Real.pi t24StrongestMu 1 Q0)
    (hQ0 : Q0 ≤ structuredDenominator n r)
    (hBoundary : ((10 : ℝ) ^ m)⁻¹ ≤
      (structuredDenominator n r : ℝ) ^ (-t24StrongestLoss)) :
    ¬ factorAt piDecimalStream m n =
      factorAt piDecimalStream m (n + r) := by
  apply effectiveIrrationality_excludes_equal_decimalBlocks hr hSource
  refine ⟨hQ0, ?_⟩
  rw [t24Strongest_scaled_rationalBound_eq_loss
    (show 0 < structuredDenominator n r by
      unfold structuredDenominator
      exact Nat.mul_pos (by positivity)
        (by have := one_lt_pow₀ (by norm_num : (1 : ℕ) < 10) hr.ne'; omega))]
  exact hBoundary

end Theory.PiDigits.PositiveLowerBlockDensity.T25

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.equal_decimalBlocks_implies_structured_nearInteger
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.equal_decimalBlocks_implies_exists_integer_relation
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.effectiveIrrationality_iff_quantifiers
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.effectiveIrrationality_excludes_structured_nearReturn
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.nearReturnStarts_card_eq_excluded_add_residual
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.Q_pi_eq_diagonal_add_excluded_add_residual
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.E_pi_le_partitioned_pair_count
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.piResidualPairDecay_iff_quantifiers
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.piResidualPairDecay_implies_T23
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.piResidualPairDecay_implies_piPositiveLowerBlockDensity
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.t24Strongest_scaled_rationalBound_eq_loss
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T25.t24StrongestPinnedRow_excludes_equal_decimalBlocks
