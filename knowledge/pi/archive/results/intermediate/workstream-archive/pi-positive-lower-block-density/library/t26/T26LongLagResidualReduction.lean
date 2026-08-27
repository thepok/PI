import TheoryLib.PiPositiveLowerBlockDensity.T23T23FiniteCylinderEnergyCriterion
import TheoryLib.PiPositiveLowerBlockDensity.T25T25ResidualPairReduction
import TheoryLib.PiPositiveLowerBlockDensity.T13T13ForbiddenLanguageEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T15T15FinitePrefixIntrinsicEntropy
import TheoryLib.PiLacunaryNearReturnSparsity.T1LagDecomposition

/-!
# T26: remove positive short lags from the residual hypothesis

Canonical question: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

The C2 condition below is explicit and unproved for pi.  It includes T25's
effective-irrationality premise: decay of the residual class alone would not
exclude T25's complementary arithmetic class.  Thus this module proves only a
conditional implication to the unchanged canonical T1 predicate.
-/

noncomputable section

open Filter Finset

namespace Theory.PiDigits.PositiveLowerBlockDensity.T26

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T9
open Theory.PiDigits.PositiveLowerBlockDensity.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T13
open Theory.PiDigits.PositiveLowerBlockDensity.T15
open Theory.PiDigits.PositiveLowerBlockDensity.T23
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- Positive residual lags below the block length.  The ambient interval
retains T25's endpoint `r ≤ N - 1`. -/
def shortResidualLags (m N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter fun r => r < m

/-- Residual lags at least the block length.  The ambient interval retains
T25's endpoint `r ≤ N - 1`. -/
def longResidualLags (m N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter fun r => m ≤ r

/-- Ordered residual pairs at positive short lags `0 < r < m`.  The factor
two restores both orientations; diagonal pairs are not included. -/
def shortResidualPairCount
    (μ c : ℝ) (Q0 m N : ℕ) : ℕ :=
  2 * ∑ r ∈ shortResidualLags m N,
    (residualNearReturnStarts μ c Q0 m N r).card

/-- Ordered residual pairs at long lags `r ≥ m`.  The factor two restores
both orientations; diagonal pairs are not included. -/
def longResidualPairCount
    (μ c : ℝ) (Q0 m N : ℕ) : ℕ :=
  2 * ∑ r ∈ longResidualLags m N,
    (residualNearReturnStarts μ c Q0 m N r).card

/-- Exact endpoint audit for the positive short-lag interval. -/
theorem mem_shortResidualLags_iff {m N r : ℕ} :
    r ∈ shortResidualLags m N ↔ 0 < r ∧ r < m ∧ r < N := by
  simp only [shortResidualLags, Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Exact endpoint audit for the long-lag interval. -/
theorem mem_longResidualLags_iff {m N r : ℕ} :
    r ∈ longResidualLags m N ↔ 0 < r ∧ m ≤ r ∧ r < N := by
  simp only [longResidualLags, Finset.mem_filter, Finset.mem_Icc]
  omega

/-- T25's positive residual lags partition exactly at `m`; no diagonal is
present in either summand. -/
theorem residualPairCount_eq_short_add_long
    (μ c : ℝ) (Q0 m N : ℕ) :
    residualPairCount μ c Q0 m N =
      shortResidualPairCount μ c Q0 m N +
        longResidualPairCount μ c Q0 m N := by
  classical
  have hcover : Finset.Icc 1 (N - 1) =
      shortResidualLags m N ∪ longResidualLags m N := by
    ext r
    simp only [shortResidualLags, longResidualLags, Finset.mem_Icc,
      Finset.mem_union, Finset.mem_filter]
    omega
  have hdisjoint : Disjoint (shortResidualLags m N) (longResidualLags m N) := by
    refine Finset.disjoint_left.mpr ?_
    intro r hrShort hrLong
    rw [mem_shortResidualLags_iff] at hrShort
    rw [mem_longResidualLags_iff] at hrLong
    omega
  unfold residualPairCount shortResidualPairCount longResidualPairCount
  rw [hcover, Finset.sum_union hdisjoint]
  omega

/-- Every residual fiber at lag `r` has at most `N` possible first starts. -/
theorem residualNearReturnStarts_card_le_N
    (μ c : ℝ) (Q0 m N r : ℕ) :
    (residualNearReturnStarts μ c Q0 m N r).card ≤ N := by
  classical
  unfold residualNearReturnStarts nearReturnStarts
  calc
    (((Finset.range (N - r)).filter fun n =>
          DecimalFactorComplexity.circleDistance
            ((10 : ℝ) ^ n * ((10 : ℝ) ^ r - 1) * Real.pi) <
              ((10 : ℝ) ^ m)⁻¹).filter fun n =>
        ¬ArithmeticExcluded μ c Q0 m n r).card ≤
        ((Finset.range (N - r)).filter fun n =>
          DecimalFactorComplexity.circleDistance
            ((10 : ℝ) ^ n * ((10 : ℝ) ^ r - 1) * Real.pi) <
              ((10 : ℝ) ^ m)⁻¹).card := Finset.card_filter_le _ _
    _ ≤ (Finset.range (N - r)).card := Finset.card_filter_le _ _
    _ = N - r := Finset.card_range _
    _ ≤ N := Nat.sub_le N r

/-- There are at most `m` positive short lags. -/
theorem shortResidualLags_card_le (m N : ℕ) :
    (shortResidualLags m N).card ≤ m := by
  calc
    (shortResidualLags m N).card ≤ (Finset.range m).card := by
      apply Finset.card_le_card
      intro r hr
      rw [Finset.mem_range]
      exact (mem_shortResidualLags_iff.mp hr).2.1
    _ = m := Finset.card_range m

/-- Universal ordered short-lag estimate.  It excludes all `N` diagonal
pairs and counts both orientations of each `0 < r < m` pair. -/
theorem shortResidualPairCount_le_two_mul
    (μ c : ℝ) (Q0 m N : ℕ) :
    shortResidualPairCount μ c Q0 m N ≤ 2 * N * m := by
  have hsum :
      (∑ r ∈ shortResidualLags m N,
          (residualNearReturnStarts μ c Q0 m N r).card) ≤
        ∑ _r ∈ shortResidualLags m N, N := by
    apply Finset.sum_le_sum
    intro r _hr
    exact residualNearReturnStarts_card_le_N μ c Q0 m N r
  unfold shortResidualPairCount
  calc
    2 * ∑ r ∈ shortResidualLags m N,
        (residualNearReturnStarts μ c Q0 m N r).card ≤
        2 * ∑ _r ∈ shortResidualLags m N, N :=
      Nat.mul_le_mul_left 2 hsum
    _ = 2 * ((shortResidualLags m N).card * N) := by simp
    _ ≤ 2 * (m * N) := by
      exact Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_right N (shortResidualLags_card_le m N))
    _ = 2 * N * m := by ac_rfl

/-- Full T25 count with every convention visible: `N` ordered diagonal pairs,
then excluded pairs, positive short residual lags, and long residual lags. -/
theorem Q_pi_eq_diagonal_add_excluded_add_short_add_long
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    DecimalFactorComplexity.Q_pi m N =
      N + excludedPairCount μ c Q0 m N +
        shortResidualPairCount μ c Q0 m N +
          longResidualPairCount μ c Q0 m N := by
  have hpartition := Q_pi_eq_diagonal_add_excluded_add_residual
    μ c Q0 m N hm hN
  rw [residualPairCount_eq_short_add_long] at hpartition
  simpa [Nat.add_assoc] using hpartition

/-- Under T25's arithmetic premise, T23's energy is bounded by the displayed
diagonal, short-lag, and long-lag contributions. -/
theorem E_pi_le_diagonal_add_short_add_long
    {μ c : ℝ} {Q0 m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0) :
    E_pi m N ≤
      ((N + shortResidualPairCount μ c Q0 m N +
        longResidualPairCount μ c Q0 m N : ℕ) : ℝ) /
          (N : ℝ) ^ 2 := by
  have hbound := E_pi_le_diagonal_add_residual hm hN hIrr
  rw [residualPairCount_eq_short_add_long] at hbound
  simpa [Nat.add_assoc] using hbound

/-- T23's slow-cutoff selection strengthened by the exact normalized upper
bound for the diagonal plus the universal `2 * M * m` short-lag contribution,
where `M = N + 1 - m` is the retained sample size. -/
theorem zeroLiminf_exists_slowCutoff_shortLag_negligible
    {ell : ℕ} (v : Fin ell → Fin 10)
    (hzero : liminf
      (blockFrequency Theory.PiDigits.piDigit (List.ofFn v)) atTop = 0)
    (C : ℝ) (hC : 0 < C) (N0 m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ,
      2 * m ≤ N ∧
      N0 ≤ N + 1 - m ∧
      2 * (m + 1) *
          blockFrequency Theory.PiDigits.piDigit (List.ofFn v) N ≤
        (1 : ℝ) / 2 ∧
      (forbiddenWordCount v m : ℝ) *
          (((N + 1 - m + 2 * (N + 1 - m) * m : ℕ) : ℝ) /
            ((N + 1 - m : ℕ) : ℝ) ^ 2) <
        (1 : ℝ) / 16 ∧
      C * (forbiddenWordCount v m : ℝ) *
          (1 / ((N + 1 - m : ℕ) : ℝ)) <
        (1 : ℝ) / 16 := by
  let D : ℝ := C + (1 + 2 * (m : ℝ))
  have hD : 0 < D := by
    dsimp [D]
    positivity
  obtain ⟨N, hroom, hN0, hrare, hDsmall⟩ :=
    zeroLiminf_exists_slowCutoff_inverse_negligible
      v hzero D hD N0 m hm
  refine ⟨N, hroom, hN0, hrare, ?_, ?_⟩
  · let M : ℕ := N + 1 - m
    have hMnat : 0 < M := by
      dsimp [M]
      omega
    have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
    have hF : (0 : ℝ) ≤ forbiddenWordCount v m := by positivity
    have hcoef : (1 : ℝ) + 2 * (m : ℝ) ≤ D := by
      dsimp [D]
      linarith
    have hcompare :
        ((1 : ℝ) + 2 * (m : ℝ)) *
            ((forbiddenWordCount v m : ℝ) * (1 / (M : ℝ))) ≤
          D * ((forbiddenWordCount v m : ℝ) * (1 / (M : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hcoef (mul_nonneg hF (by positivity))
    have heq :
        (forbiddenWordCount v m : ℝ) *
            (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) =
          ((1 : ℝ) + 2 * (m : ℝ)) *
            ((forbiddenWordCount v m : ℝ) * (1 / (M : ℝ))) := by
      push_cast
      field_simp [ne_of_gt hM]
    change (forbiddenWordCount v m : ℝ) *
        (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) < (1 : ℝ) / 16
    rw [heq]
    exact hcompare.trans_lt (by simpa [M, mul_assoc] using hDsmall)
  · have hF : (0 : ℝ) ≤ forbiddenWordCount v m := by positivity
    have hCD : C ≤ D := by
      dsimp [D]
      linarith
    have hcompare :
        C * ((forbiddenWordCount v m : ℝ) *
            (1 / ((N + 1 - m : ℕ) : ℝ))) ≤
          D * ((forbiddenWordCount v m : ℝ) *
            (1 / ((N + 1 - m : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hCD
        (mul_nonneg hF (by positivity))
    have hcompare' :
        C * (forbiddenWordCount v m : ℝ) *
            (1 / ((N + 1 - m : ℕ) : ℝ)) ≤
          D * (forbiddenWordCount v m : ℝ) *
            (1 / ((N + 1 - m : ℕ) : ℝ)) := by
      simpa [mul_assoc] using hcompare
    exact hcompare'.trans_lt hDsmall

/-- C2: T25's arithmetic premise together with decay of only the exact
long-lag residual class.  Constants may depend on `s`, and the estimate is
uniform in every later `N` and every positive `m`. -/
def PiLongLagResidualPairDecay (μ c : ℝ) (Q0 : ℕ) : Prop :=
  EffectiveIrrationality Real.pi μ c Q0 ∧
    ∀ s : ℝ, 0 < s → s < 1 →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ,
        ∀ N : ℕ, N0 ≤ N → ∀ m : ℕ, 1 ≤ m →
          (longResidualPairCount μ c Q0 m N : ℝ) ≤
            C * (N : ℝ) ^ 2 *
              ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (N : ℝ))

/-- Quantifier audit for C2, including the inherited T25 arithmetic premise. -/
theorem piLongLagResidualPairDecay_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    PiLongLagResidualPairDecay μ c Q0 ↔
      EffectiveIrrationality Real.pi μ c Q0 ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ,
            ∀ N : ℕ, N0 ≤ N → ∀ m : ℕ, 1 ≤ m →
              (longResidualPairCount μ c Q0 m N : ℝ) ≤
                C * (N : ℝ) ^ 2 *
                  ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (N : ℝ)) := by
  rfl

/-- C2 conditionally implies T1's unchanged canonical C1 predicate. -/
theorem piLongLagResidualPairDecay_implies_piPositiveLowerBlockDensity
    {μ c : ℝ} {Q0 : ℕ}
    (hC2 : PiLongLagResidualPairDecay μ c Q0) :
    PiPositiveLowerBlockDensity := by
  rcases hC2 with ⟨hIrr, hdecay⟩
  by_contra hnot
  obtain ⟨ell, hell, v, hzero⟩ := not_C1_exists_zero_liminf hnot
  let s := forbiddenDecayExponent v
  have hs : 0 < s ∧ s < 1 := by
    simpa [s] using forbiddenDecayExponent_pos_lt_one hell v
  obtain ⟨C, hC, N0, hlongBound⟩ :=
    hdecay s hs.1 hs.2
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨j, hj, hdecaySmall⟩ :=
    exists_twoBlockScale_forbidden_energy_small hell v C hCpos
  let m := (2 * ell) * j
  have hm : 0 < m := by
    dsimp [m]
    positivity
  obtain ⟨N, hroom, hN0, hrare, hshortSmall, hinverse⟩ :=
    zeroLiminf_exists_slowCutoff_shortLag_negligible
      v hzero C hCpos N0 m hm
  let M : ℕ := N + 1 - m
  change N0 ≤ M at hN0
  change (forbiddenWordCount v m : ℝ) *
      (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) <
        (1 : ℝ) / 16 at hshortSmall
  change C * (forbiddenWordCount v m : ℝ) * (1 / (M : ℝ)) <
      (1 : ℝ) / 16 at hinverse
  have hMposNat : 1 ≤ M := by
    dsimp [M]
    omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposNat
  have hlower := contaminatedForbiddenSupport_collision_lower_bound
    hell hm hroom v hrare
  change (1 : ℝ) / 4 ≤
      (forbiddenWordCount v m : ℝ) * E_pi m M at hlower
  have henergy := E_pi_le_diagonal_add_short_add_long
    (μ := μ) (c := c) (Q0 := Q0) hm hMposNat hIrr
  have hshortNat := shortResidualPairCount_le_two_mul μ c Q0 m M
  have hlong := hlongBound M hN0 m hm
  have hshortNumerator :
      (((M + shortResidualPairCount μ c Q0 m M : ℕ) : ℝ) /
          (M : ℝ) ^ 2) ≤
        (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.add_le_add_left hshortNat M
  have hlongNormalized :
      (longResidualPairCount μ c Q0 m M : ℝ) / (M : ℝ) ^ 2 ≤
        C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := by
    calc
      (longResidualPairCount μ c Q0 m M : ℝ) / (M : ℝ) ^ 2 ≤
          (C * (M : ℝ) ^ 2 *
            ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ))) /
              (M : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hlong (by positivity)
      _ = C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := by
        field_simp [ne_of_gt hMpos]
  have hsplit :
      (((M + shortResidualPairCount μ c Q0 m M +
          longResidualPairCount μ c Q0 m M : ℕ) : ℝ) /
            (M : ℝ) ^ 2) =
        (((M + shortResidualPairCount μ c Q0 m M : ℕ) : ℝ) /
            (M : ℝ) ^ 2) +
          (longResidualPairCount μ c Q0 m M : ℝ) / (M : ℝ) ^ 2 := by
    push_cast
    ring
  have henergyUpper :
      E_pi m M ≤
        (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) +
          C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := by
    calc
      E_pi m M ≤
          (((M + shortResidualPairCount μ c Q0 m M +
            longResidualPairCount μ c Q0 m M : ℕ) : ℝ) /
              (M : ℝ) ^ 2) := henergy
      _ = (((M + shortResidualPairCount μ c Q0 m M : ℕ) : ℝ) /
              (M : ℝ) ^ 2) +
            (longResidualPairCount μ c Q0 m M : ℝ) / (M : ℝ) ^ 2 := hsplit
      _ ≤ (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) +
            C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) :=
        add_le_add hshortNumerator hlongNormalized
  have hcountNat := forbiddenWordCount_twoBlock_mul_le_pow v j
  have hcount : (forbiddenWordCount v m : ℝ) ≤
      (forbiddenQ v : ℝ) ^ j := by
    dsimp [m]
    exact_mod_cast hcountNat
  have hdecayNonneg : 0 ≤
      (10 : ℝ) ^ (-s * (m : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hfirst : C * (forbiddenWordCount v m : ℝ) *
      (10 : ℝ) ^ (-s * (m : ℝ)) < (1 : ℝ) / 16 := by
    apply lt_of_le_of_lt _ hdecaySmall
    have hmul := mul_le_mul_of_nonneg_left hcount hCpos.le
    exact mul_le_mul_of_nonneg_right hmul hdecayNonneg
  have hF : (0 : ℝ) ≤ forbiddenWordCount v m := by positivity
  have henergySmall :
      (forbiddenWordCount v m : ℝ) * E_pi m M < (1 : ℝ) / 4 := by
    calc
      (forbiddenWordCount v m : ℝ) * E_pi m M ≤
          (forbiddenWordCount v m : ℝ) *
            ((((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) +
              C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ))) :=
        mul_le_mul_of_nonneg_left henergyUpper hF
      _ = (forbiddenWordCount v m : ℝ) *
              (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) +
            C * (forbiddenWordCount v m : ℝ) *
              (10 : ℝ) ^ (-s * (m : ℝ)) +
            C * (forbiddenWordCount v m : ℝ) * (1 / (M : ℝ)) := by
        ring
      _ < (1 : ℝ) / 16 + (1 : ℝ) / 16 + (1 : ℝ) / 16 :=
        add_lt_add (add_lt_add hshortSmall hfirst) hinverse
      _ < (1 : ℝ) / 4 := by norm_num
  exact (not_lt_of_ge hlower) henergySmall

end Theory.PiDigits.PositiveLowerBlockDensity.T26

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.mem_shortResidualLags_iff
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.mem_longResidualLags_iff
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.residualPairCount_eq_short_add_long
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.shortResidualPairCount_le_two_mul
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.Q_pi_eq_diagonal_add_excluded_add_short_add_long
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.E_pi_le_diagonal_add_short_add_long
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.zeroLiminf_exists_slowCutoff_shortLag_negligible
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.piLongLagResidualPairDecay_iff_quantifiers
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T26.piLongLagResidualPairDecay_implies_piPositiveLowerBlockDensity
