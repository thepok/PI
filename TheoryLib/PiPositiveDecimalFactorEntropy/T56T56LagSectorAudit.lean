import TheoryLib.PiPositiveDecimalFactorEntropy.T27T27SparseMicroscopicEquivalence
import TheoryLib.PiPositiveLowerBlockDensity.T26T26LongLagResidualReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T12T12ScaleMatchedSpectralFrontier

/-!
# T56: exact sparse lag sectors and the retained short-sector budget

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file imports T27 but does not assert its equivalent unproved conditions.
It specializes the accepted lag decomposition at `L_n = 10^(n/2)`, where
`/` is natural-number division, and exposes the complete T25/T26 partition.
All near-return cutoffs remain strict.  The effective-irrationality and
long-sector estimates below remain explicit hypotheses.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.T56LagSectorAudit

open DecimalFactorComplexity
open DecimalFactorComplexity.LagDecomposition
open DecimalFactorComplexity.SparseLongBandFejer
open DecimalFactorComplexity.SparseMicroscopicEquivalence
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The requested sparse sample length.  The exponent uses natural division. -/
abbrev t56SampleLength (n : ℕ) : ℕ := 10 ^ (n / 2)

/-- Exact ordered, diagonal-inclusive decomposition at the T56 sample length.
The outer range is precisely `1 ≤ r ≤ L_n-1`; for each lag the starts are
precisely `0 ≤ j < L_n-r`. -/
theorem sparse_Q_exact_lag_decomposition (n : ℕ) (hn : 1 ≤ n) :
    Q_pi n (t56SampleLength n) =
      t56SampleLength n +
        2 * ∑ r ∈ Finset.Icc 1 (t56SampleLength n - 1),
          ((Finset.range (t56SampleLength n - r)).filter fun j =>
            circleDistance
              ((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi) <
                ((10 : ℝ) ^ n)⁻¹).card := by
  exact Q_pi_orderedPair_lag_decomposition n (t56SampleLength n) hn
    (one_le_pow₀ (by norm_num))

/-- The repunit multiplier in the lag identity is exactly T25's structured
natural denominator after coercion to the reals. -/
theorem sparse_repunit_eq_structuredDenominator_cast (j r : ℕ) :
    (structuredDenominator j r : ℝ) =
      (10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) := by
  exact structuredDenominator_cast j r

/-- Complete incidence partition: diagonal, arithmetic-excluded near returns,
residual short lags `0 < r < n`, and residual long lags `n ≤ r < L_n`.
No assertion is made that any non-diagonal sector is small. -/
theorem sparse_Q_exact_sector_partition
    (μ c : ℝ) (Q0 n : ℕ) (hn : 1 ≤ n) :
    Q_pi n (t56SampleLength n) =
      t56SampleLength n +
        excludedPairCount μ c Q0 n (t56SampleLength n) +
          shortResidualPairCount μ c Q0 n (t56SampleLength n) +
            longResidualPairCount μ c Q0 n (t56SampleLength n) := by
  exact Q_pi_eq_diagonal_add_excluded_add_short_add_long
    μ c Q0 n (t56SampleLength n) hn (one_le_pow₀ (by norm_num))

/-- Endpoint audit for the sparse short sector. -/
theorem mem_sparse_short_sector_iff {n r : ℕ} :
    r ∈ shortResidualLags n (t56SampleLength n) ↔
      0 < r ∧ r < n ∧ r < t56SampleLength n := by
  exact mem_shortResidualLags_iff

/-- Endpoint audit for the sparse long sector. -/
theorem mem_sparse_long_sector_iff {n r : ℕ} :
    r ∈ longResidualLags n (t56SampleLength n) ↔
      0 < r ∧ n ≤ r ∧ r < t56SampleLength n := by
  exact mem_longResidualLags_iff

/-- Under the explicitly supplied arithmetic premise, the excluded sector is
empty and the exact identity retains only diagonal, short, and long residual
incidences. -/
theorem sparse_Q_eq_diagonal_add_short_add_long
    {μ c : ℝ} {Q0 n : ℕ} (hn : 1 ≤ n)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0) :
    Q_pi n (t56SampleLength n) =
      t56SampleLength n +
        shortResidualPairCount μ c Q0 n (t56SampleLength n) +
          longResidualPairCount μ c Q0 n (t56SampleLength n) := by
  rw [sparse_Q_exact_sector_partition μ c Q0 n hn,
    excludedPairCount_eq_zero hIrr]
  omega

/-- The strongest unconditional accepted short-sector estimate specializes to
`2*L_n*n`.  This is the factor that is not summable to a uniform multiple of
`L_n` by the retained sectorwise bounds alone. -/
theorem sparse_short_sector_le_two_mul_length_mul_n
    (μ c : ℝ) (Q0 n : ℕ) :
    shortResidualPairCount μ c Q0 n (t56SampleLength n) ≤
      2 * t56SampleLength n * n := by
  exact shortResidualPairCount_le_two_mul μ c Q0 n (t56SampleLength n)

/-- Exact consequence of the accepted partition, arithmetic exclusion, the
unconditional short-sector estimate, and any supplied long-sector budget `B`.
The theorem deliberately leaves the nonuniform term `2*L_n*n` visible. -/
theorem sparse_Q_le_retained_sector_budget
    {μ c : ℝ} {Q0 n B : ℕ} (hn : 1 ≤ n)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hLong : longResidualPairCount μ c Q0 n (t56SampleLength n) ≤ B) :
    Q_pi n (t56SampleLength n) ≤
      t56SampleLength n + 2 * t56SampleLength n * n + B := by
  rw [sparse_Q_eq_diagonal_add_short_add_long hn hIrr]
  have hShort := sparse_short_sector_le_two_mul_length_mul_n μ c Q0 n
  omega

/-- A precise name for the missing weighted repunit-incidence estimate.  Its
left side is twice the sum of the residual strict repunit incidences over all
`0 < r < n`, with the triangular start range `j < L_n-r`. -/
def SparseShortRepunitIncidenceBound (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      (shortResidualPairCount μ c Q0 n (t56SampleLength n) : ℝ) ≤
        A * (t56SampleLength n : ℝ)

/-- Literal quantifier audit for the missing estimate. -/
theorem sparseShortRepunitIncidenceBound_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    SparseShortRepunitIncidenceBound μ c Q0 ↔
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (shortResidualPairCount μ c Q0 n (t56SampleLength n) : ℝ) ≤
            A * (t56SampleLength n : ℝ) := by
  rfl

/-- The matching eventual linear statement for the long residual sector.  The
adjacent long-lag program supplies this only under one of its explicit,
currently unproved decay or spectral premises. -/
def SparseLongResidualLinearBound (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      (longResidualPairCount μ c Q0 n (t56SampleLength n) : ℝ) ≤
        B * (t56SampleLength n : ℝ)

/-- With arithmetic exclusion and linear estimates for both residual sectors,
the exact partition yields T27's sparse microscopic `Q_pi=O(L_n)` predicate,
with the explicit constant `1+A+B`. -/
theorem sparse_sector_linear_bounds_imply_QBound
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hShort : SparseShortRepunitIncidenceBound μ c Q0)
    (hLong : SparseLongResidualLinearBound μ c Q0) :
    PiSparseMicroscopicQBound := by
  obtain ⟨A, hA, NA, hNA, hallA⟩ := hShort
  obtain ⟨B, hB, NB, hNB, hallB⟩ := hLong
  refine ⟨1 + A + B, by positivity, max NA NB, ?_, ?_⟩
  · exact hNA.trans (Nat.le_max_left NA NB)
  · intro n hn
    have hnA : NA ≤ n := (Nat.le_max_left NA NB).trans hn
    have hnB : NB ≤ n := (Nat.le_max_right NA NB).trans hn
    have hnpos : 1 ≤ n := hNA.trans hnA
    have hEq := sparse_Q_eq_diagonal_add_short_add_long hnpos hIrr
    have hEqReal :
        (Q_pi n (t56SampleLength n) : ℝ) =
          (t56SampleLength n : ℝ) +
            (shortResidualPairCount μ c Q0 n (t56SampleLength n) : ℝ) +
              (longResidualPairCount μ c Q0 n (t56SampleLength n) : ℝ) := by
      exact_mod_cast hEq
    change (Q_pi n (t56SampleLength n) : ℝ) ≤
      (1 + A + B) * (t56SampleLength n : ℝ)
    rw [hEqReal]
    calc
      (t56SampleLength n : ℝ) +
            (shortResidualPairCount μ c Q0 n (t56SampleLength n) : ℝ) +
              (longResidualPairCount μ c Q0 n (t56SampleLength n) : ℝ) ≤
          (t56SampleLength n : ℝ) +
            A * (t56SampleLength n : ℝ) +
              B * (t56SampleLength n : ℝ) := by
        gcongr
        · exact hallA n hnA
        · exact hallB n hnB
      _ = (1 + A + B) * (t56SampleLength n : ℝ) := by ring

/-- The same hypotheses imply C7 only through T27's kernel-checked reverse
implication.  This remains a conditional theorem and asserts none of them. -/
theorem sparse_sector_linear_bounds_imply_C7
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hShort : SparseShortRepunitIncidenceBound μ c Q0)
    (hLong : SparseLongResidualLinearBound μ c Q0) :
    PiSparseLongBandC7 :=
  piSparseMicroscopicQBound_implies_C7
    (sparse_sector_linear_bounds_imply_QBound hIrr hShort hLong)

/-! ## Abstract finite obstruction to summing the retained budgets -/

/-- In the obstruction, each of the `n-1` positive short lags retains exactly
`L-n` upper-triangular starts, and both orientations are counted. -/
def abstractShortIncidenceCount (n L : ℕ) : ℕ :=
  2 * (n - 1) * (L - n)

/-- Add the `L` diagonal incidences and set all excluded and long sectors to
zero. -/
def abstractTotalIncidenceCount (n L : ℕ) : ℕ :=
  L + abstractShortIncidenceCount n L

/-- The abstract short sector obeys the accepted coarse `2*L*n` budget. -/
theorem abstractShortIncidenceCount_le_retained_budget (n L : ℕ) :
    abstractShortIncidenceCount n L ≤ 2 * L * n := by
  unfold abstractShortIncidenceCount
  have h₁ : n - 1 ≤ n := Nat.sub_le n 1
  have h₂ : L - n ≤ L := Nat.sub_le L n
  calc
    2 * (n - 1) * (L - n) ≤ 2 * n * L := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 h₁) h₂
    _ = 2 * L * n := by ring

/-- At the finite choice `L=2n`, the abstract family has exact ratio `n` to
the sample length. -/
theorem abstractTotalIncidenceCount_two_mul (n : ℕ) (hn : 1 ≤ n) :
    abstractTotalIncidenceCount n (2 * n) = n * (2 * n) := by
  unfold abstractTotalIncidenceCount abstractShortIncidenceCount
  have hsub : 2 * n - n = n := by omega
  rw [hsub]
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  nlinarith

/-- Hence every proposed natural constant has a replayable finite abstract
counter-instance satisfying the retained short and zero long/excluded budgets. -/
theorem exists_abstract_obstruction_above_constant (C : ℕ) :
    ∃ n L : ℕ,
      abstractShortIncidenceCount n L ≤ 2 * L * n ∧
      C * L < abstractTotalIncidenceCount n L := by
  let n := C + 1
  let L := 2 * n
  refine ⟨n, L, abstractShortIncidenceCount_le_retained_budget n L, ?_⟩
  rw [show abstractTotalIncidenceCount n L = n * L by
    simpa [L] using abstractTotalIncidenceCount_two_mul n (by simp [n])]
  have hCL : C * L < n * L := by
    apply Nat.mul_lt_mul_of_pos_right
    · simp [n]
    · simp [L, n]
  exact hCL

/-- The obstruction also defeats every proposed real big-O constant.  Choose
a larger natural constant and use positivity of the finite sample length. -/
theorem exists_abstract_obstruction_above_real_constant (C : ℝ) :
    ∃ n L : ℕ,
      abstractShortIncidenceCount n L ≤ 2 * L * n ∧
      C * (L : ℝ) < (abstractTotalIncidenceCount n L : ℝ) := by
  obtain ⟨K, hCK⟩ := exists_nat_gt C
  obtain ⟨n, L, hBudget, hKL⟩ :=
    exists_abstract_obstruction_above_constant K
  refine ⟨n, L, hBudget, ?_⟩
  have hL : 0 < L := by
    by_contra hnot
    have hzero : L = 0 := Nat.eq_zero_of_not_pos hnot
    subst L
    simp [abstractTotalIncidenceCount, abstractShortIncidenceCount] at hKL
  have hLReal : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    C * (L : ℝ) < (K : ℝ) * (L : ℝ) :=
      mul_lt_mul_of_pos_right hCK hLReal
    _ < (abstractTotalIncidenceCount n L : ℝ) := by exact_mod_cast hKL

end DecimalFactorComplexity.T56LagSectorAudit

#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_exact_lag_decomposition
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_repunit_eq_structuredDenominator_cast
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_exact_sector_partition
#print axioms DecimalFactorComplexity.T56LagSectorAudit.mem_sparse_short_sector_iff
#print axioms DecimalFactorComplexity.T56LagSectorAudit.mem_sparse_long_sector_iff
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_eq_diagonal_add_short_add_long
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_short_sector_le_two_mul_length_mul_n
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_le_retained_sector_budget
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparseShortRepunitIncidenceBound_iff_quantifiers
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_sector_linear_bounds_imply_QBound
#print axioms DecimalFactorComplexity.T56LagSectorAudit.sparse_sector_linear_bounds_imply_C7
#print axioms DecimalFactorComplexity.T56LagSectorAudit.abstractShortIncidenceCount_le_retained_budget
#print axioms DecimalFactorComplexity.T56LagSectorAudit.abstractTotalIncidenceCount_two_mul
#print axioms DecimalFactorComplexity.T56LagSectorAudit.exists_abstract_obstruction_above_constant
#print axioms DecimalFactorComplexity.T56LagSectorAudit.exists_abstract_obstruction_above_real_constant
