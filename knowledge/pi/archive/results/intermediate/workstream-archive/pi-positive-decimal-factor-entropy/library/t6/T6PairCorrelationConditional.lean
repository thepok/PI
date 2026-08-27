import TheoryLib.PiPositiveDecimalFactorEntropy.T2T2ExponentialCollisionCriterion
import TheoryLib.PiLacunaryNearReturnSparsity.T2NormalOrbitNearReturns

/-!
# T6: fixed-pi pair correlation as an explicit conditional frontier

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file does not assert pair correlation for pi. It defines the agenda's C3
as an unproved hypothesis about the zero-based decimal shift orbit
`x_i = fract (10^i * pi)`, then proves C3 implies the accepted T2 near-return
criterion and hence canonical C1. Counts are ordered. C3 omits the diagonal;
the exact transfer to `Q_pi` restores its `M` diagonal pairs separately.
-/

noncomputable section

namespace DecimalFactorComplexity.PairCorrelationConditional

open Filter
open DecimalFactorComplexity.ExponentialCollisionCriterion

/-- The zero-based decimal shift orbit from C3: `x_i = frac(10^i * pi)`. -/
abbrev piDecimalShiftOrbit (i : ℕ) : ℝ :=
  Theory.PiDigits.T20.baseTenOrbit Real.pi i

/-- Ordered off-diagonal pairs at microscopic scale `s / M`. -/
noncomputable def piOffDiagonalPairs (s : ℝ) (M : ℕ) :
    Finset (Fin M × Fin M) := by
  classical
  exact Finset.univ.filter fun ij =>
    ij.1 ≠ ij.2 ∧
      circleDistance
          (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
        s / (M : ℝ)

/-- Cardinality of the ordered off-diagonal microscopic pair set. -/
noncomputable def piOffDiagonalCount (s : ℝ) (M : ℕ) : ℕ :=
  (piOffDiagonalPairs s M).card

@[simp] theorem mem_piOffDiagonalPairs_iff (s : ℝ) (M : ℕ)
    (ij : Fin M × Fin M) :
    ij ∈ piOffDiagonalPairs s M ↔
      ij.1 ≠ ij.2 ∧
        circleDistance
            (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
          s / (M : ℝ) := by
  classical
  simp [piOffDiagonalPairs]

/-- C3, retained only as an explicit unproved fixed-pi hypothesis. -/
def PiDecimalShiftPairCorrelationC3 : Prop :=
  ∀ s : ℝ, 0 < s →
    Tendsto
      (fun M : ℕ => (piOffDiagonalCount s M : ℝ) / (M : ℝ))
      atTop (nhds (2 * s))

/-- The named theorem exposes every limit quantifier in C3. -/
theorem piDecimalShiftPairCorrelationC3_iff_quantifiers :
    PiDecimalShiftPairCorrelationC3 ↔
      ∀ s : ℝ, 0 < s →
        Tendsto
          (fun M : ℕ => (piOffDiagonalCount s M : ℝ) / (M : ℝ))
          atTop (nhds (2 * s)) :=
  Iff.rfl

/-- Fractional-part orbit differences and T2's power differences have the
same circle distance. -/
theorem circleDistance_piShift_sub_eq_powerDifference (i j : ℕ) :
    circleDistance (piDecimalShiftOrbit j - piDecimalShiftOrbit i) =
      circleDistance
        (((10 : ℝ) ^ j - (10 : ℝ) ^ i) * Real.pi) := by
  let z : ℤ :=
    ⌊(10 : ℝ) ^ j * Real.pi⌋ - ⌊(10 : ℝ) ^ i * Real.pi⌋
  have hdifference :
      piDecimalShiftOrbit j - piDecimalShiftOrbit i =
        (((10 : ℝ) ^ j - (10 : ℝ) ^ i) * Real.pi) - z := by
    dsimp [piDecimalShiftOrbit, Theory.PiDigits.T20.baseTenOrbit, z]
    rw [Int.cast_sub]
    simp only [Int.fract]
    ring
  rw [hdifference,
    DecimalFactorComplexity.NormalOrbitNearReturns.circleDistance_sub_int]

/-- At `M = 10^n`, T2's count is exactly the C3 off-diagonal count plus the
`M` diagonal pairs omitted by C3. -/
theorem Q_pi_pow_ten_eq_offDiagonal_add_diagonal (n : ℕ) :
    Q_pi n (10 ^ n) =
      piOffDiagonalCount 1 (10 ^ n) + 10 ^ n := by
  classical
  let M : ℕ := 10 ^ n
  have hradius : (1 : ℝ) / (M : ℝ) = ((10 : ℝ) ^ n)⁻¹ := by
    simp [M]
  have hsets :
      piNearReturnPairs n M =
        (Finset.univ : Finset (Fin M)).diag ∪ piOffDiagonalPairs 1 M := by
    ext ij
    rw [mem_piNearReturnPairs_iff]
    simp only [Finset.mem_union, Finset.mem_diag,
      mem_piOffDiagonalPairs_iff]
    constructor
    · intro hnear
      by_cases hij : ij.1 = ij.2
      · exact Or.inl ⟨Finset.mem_univ _, hij⟩
      · refine Or.inr ⟨hij, ?_⟩
        rw [circleDistance_piShift_sub_eq_powerDifference, hradius]
        exact hnear
    · rintro (hij | ⟨_, hnear⟩)
      · have hdiag := (mem_piNearReturnPairs_iff n M (ij.1, ij.1)).mp
          (diagonal_mem_piNearReturnPairs n M ij.1)
        simpa [hij.2] using hdiag
      · rw [circleDistance_piShift_sub_eq_powerDifference, hradius] at hnear
        exact hnear
  have hdisjoint :
      Disjoint (Finset.univ : Finset (Fin M)).diag
        (piOffDiagonalPairs 1 M) := by
    rw [Finset.disjoint_left]
    intro ij hdiag hoff
    rw [Finset.mem_diag] at hdiag
    rw [mem_piOffDiagonalPairs_iff] at hoff
    exact hoff.1 hdiag.2
  change (piNearReturnPairs n M).card =
    piOffDiagonalCount 1 M + M
  rw [hsets, Finset.card_union_of_disjoint hdisjoint,
    Finset.diag_card, Finset.card_univ, Fintype.card_fin]
  exact Nat.add_comm _ _

/-- C3 at `s = 1` gives the concrete eventual off-diagonal bound used below. -/
theorem c3_eventually_offDiagonal_lt_three_mul
    (hC3 : PiDecimalShiftPairCorrelationC3) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
      (piOffDiagonalCount 1 M : ℝ) < 3 * (M : ℝ) := by
  have hlim := hC3 1 (by norm_num)
  have heventual :
      ∀ᶠ M : ℕ in atTop,
        (piOffDiagonalCount 1 M : ℝ) / (M : ℝ) < 3 :=
    (tendsto_order.1 hlim).2 3 (by norm_num)
  rw [eventually_atTop] at heventual
  obtain ⟨M1, hM1⟩ := heventual
  refine ⟨max 1 M1, le_max_left _ _, ?_⟩
  intro M hM
  have hM1le : M1 ≤ M := (le_max_right 1 M1).trans hM
  have hMposNat : 0 < M := (le_max_left 1 M1).trans hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMposNat
  exact (div_lt_iff₀ hMpos).mp (hM1 M hM1le)

/-- A convenient elementary bound for converting C3's sample-size cutoff to
the exponent cutoff used with `M = 10^n`. -/
theorem nat_le_ten_pow (n : ℕ) : n ≤ 10 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 0 < 10 ^ n := pow_pos (by norm_num) n
      omega

/-- The full quantitative transfer. The cutoff `max 2 M0`, the fixed choice
`M = 10^n`, and exponent `eta = 1/2` are visible in the theorem type. -/
theorem c3_implies_explicit_pow_ten_nearReturn_bound
    (hC3 : PiDecimalShiftPairCorrelationC3) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧
      ∀ n : ℕ, max 2 M0 ≤ n →
        (Q_pi n (10 ^ n) : ℝ) ≤
          ((10 ^ n : ℕ) : ℝ) ^ 2 *
            (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
  obtain ⟨M0, hM0, hoff⟩ :=
    c3_eventually_offDiagonal_lt_three_mul hC3
  refine ⟨M0, hM0, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left 2 M0).trans hn
  have hM0n : M0 ≤ n := (le_max_right 2 M0).trans hn
  have hM0pow : M0 ≤ 10 ^ n := hM0n.trans (nat_le_ten_pow n)
  have hoffPow := hoff (10 ^ n) hM0pow
  have hQcast :
      (Q_pi n (10 ^ n) : ℝ) =
        (piOffDiagonalCount 1 (10 ^ n) : ℝ) +
          ((10 ^ n : ℕ) : ℝ) := by
    exact_mod_cast Q_pi_pow_ten_eq_offDiagonal_add_diagonal n
  have hQlinear :
      (Q_pi n (10 ^ n) : ℝ) < 4 * ((10 ^ n : ℕ) : ℝ) := by
    rw [hQcast]
    linarith
  have hn2real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hexponent : (1 : ℝ) ≤ (1 / 2 : ℝ) * (n : ℝ) := by
    linarith
  have hfour :
      (4 : ℝ) ≤ (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
    calc
      (4 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hpowCast :
      ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ (n : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hright :
      ((10 ^ n : ℕ) : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) =
        ((10 ^ n : ℕ) : ℝ) *
          (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
    calc
      ((10 ^ n : ℕ) : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) =
          (((10 : ℝ) ^ (n : ℝ)) * (10 : ℝ) ^ (n : ℝ)) *
            (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
              rw [hpowCast, pow_two]
      _ = (10 : ℝ) ^ ((n : ℝ) + (n : ℝ)) *
            (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
              rw [Real.rpow_add (by norm_num)]
      _ = (10 : ℝ) ^
            (((n : ℝ) + (n : ℝ)) + (-(1 / 2 : ℝ) * (n : ℝ))) := by
              rw [← Real.rpow_add (by norm_num)]
      _ = (10 : ℝ) ^
            ((n : ℝ) + (1 / 2 : ℝ) * (n : ℝ)) := by
              congr 1
              ring
      _ = (10 : ℝ) ^ (n : ℝ) *
            (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
              rw [Real.rpow_add (by norm_num)]
      _ = ((10 ^ n : ℕ) : ℝ) *
            (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
              rw [hpowCast]
  have hlinearToTarget :
      4 * ((10 ^ n : ℕ) : ℝ) ≤
        ((10 ^ n : ℕ) : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
    rw [hright]
    have hnonneg : (0 : ℝ) ≤ ((10 ^ n : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le (10 ^ n)
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hfour hnonneg
  exact (le_of_lt hQlinear).trans hlinearToTarget

/-- C3 supplies T2's near-return C2 with the explicit exponent `eta = 1/2`
and the sample size `M = 10^n` at every length beyond the displayed cutoff. -/
theorem c3_implies_piExponentialNearReturnC2
    (hC3 : PiDecimalShiftPairCorrelationC3) :
    PiExponentialNearReturnC2 := by
  obtain ⟨M0, hM0, hbound⟩ :=
    c3_implies_explicit_pow_ten_nearReturn_bound hC3
  refine ⟨(1 / 2 : ℝ), by norm_num, max 2 M0, ?_, ?_⟩
  · omega
  · intro n hn
    refine ⟨10 ^ n, one_le_pow₀ (by norm_num), ?_⟩
    exact hbound n hn

/-- Canonical C1 follows only under the explicit fixed-pi C3 hypothesis, by
invoking the accepted T2 implication. -/
theorem c3_implies_piPositiveFactorEntropyC1
    (hC3 : PiDecimalShiftPairCorrelationC3) :
    PiPositiveFactorEntropyC1 := by
  exact piExponentialNearReturnC2_implies_C1
    (c3_implies_piExponentialNearReturnC2 hC3)

end DecimalFactorComplexity.PairCorrelationConditional

#print axioms DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftPairCorrelationC3_iff_quantifiers
#print axioms DecimalFactorComplexity.PairCorrelationConditional.circleDistance_piShift_sub_eq_powerDifference
#print axioms DecimalFactorComplexity.PairCorrelationConditional.Q_pi_pow_ten_eq_offDiagonal_add_diagonal
#print axioms DecimalFactorComplexity.PairCorrelationConditional.c3_eventually_offDiagonal_lt_three_mul
#print axioms DecimalFactorComplexity.PairCorrelationConditional.c3_implies_explicit_pow_ten_nearReturn_bound
#print axioms DecimalFactorComplexity.PairCorrelationConditional.c3_implies_piExponentialNearReturnC2
#print axioms DecimalFactorComplexity.PairCorrelationConditional.c3_implies_piPositiveFactorEntropyC1
