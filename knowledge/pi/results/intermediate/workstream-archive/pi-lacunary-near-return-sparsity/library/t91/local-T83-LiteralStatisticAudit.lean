import TheoryLib.PiPositiveDecimalFactorEntropy.T20T20TransversalEntropy
import TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit
import TheoryLib.PiLongLagBlockCollisionDecay.T1T1LongLagBlockCollisionDecay

/-!
# T83: literal T56/C7 statistic and short-sector audit

This file distinguishes the strict circle-near-return statistic used by the
positive-decimal-factor-entropy program's T56/C7 from exact block equality.
All conclusions about pi retain explicit unproved long-sector premises.
-/

noncomputable section

open Filter Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T83LiteralStatisticAudit

open DecimalFactorComplexity
open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.SparseLongBandFejer
open DecimalFactorComplexity.SparseMicroscopicEquivalence
open DecimalFactorComplexity.T56LagSectorAudit
open Theory.PiDigits.LongLagBlockCollisionDecay
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The program-qualified T56 sample scale, with natural-number division. -/
abbrev sampleLength (n : ℕ) : ℕ := t56SampleLength n

/-- C7 with its complete eventual quantifiers and normalization exposed. -/
theorem literal_C7_iff_quantifiers :
    PiSparseLongBandC7 ↔
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          completePiFejerEnergy (10 ^ (n / 2)) (10 ^ n / 2) ≤
            C * ((10 ^ n / 2 : ℕ) : ℝ) *
              ((10 ^ (n / 2) : ℕ) : ℝ) := by
  exact piSparseLongBandC7_iff_quantifiers

/-- C7 is exactly an eventual linear bound for the ordered,
diagonal-inclusive strict near-return count, not for exact block equality. -/
theorem literal_C7_iff_nearReturn_linear :
    PiSparseLongBandC7 ↔
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (Q_pi n (10 ^ (n / 2)) : ℝ) ≤
            A * ((10 ^ (n / 2) : ℕ) : ℝ) := by
  exact piSparseLongBandC7_iff_Q_linear_quantifiers

/-- The literal residual short sector has exactly these lag endpoints. -/
theorem literal_short_sector_range {n r : ℕ} :
    r ∈ shortResidualLags n (sampleLength n) ↔
      0 < r ∧ r < n ∧ r < sampleLength n := by
  exact mem_sparse_short_sector_iff

/-- The checked unconditional T56 short-sector budget is `2 L_n n`. -/
theorem literal_short_sector_coarse_bound (μ c : ℝ) (Q0 n : ℕ) :
    shortResidualPairCount μ c Q0 n (sampleLength n) ≤
      2 * sampleLength n * n := by
  exact sparse_short_sector_le_two_mul_length_mul_n μ c Q0 n

/-- An all-rates meaning of `a_n ≤ L_n 10^{o(n)}`. -/
def SparseScaleSubexponential (a : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      (a n : ℝ) ≤ (sampleLength n : ℝ) *
        (10 : ℝ) ^ (ε * (n : ℝ))

/-- A linear polynomial is eventually below `10^(n/16)`. -/
theorem eventually_one_add_two_mul_le_ten_rpow_sixteenth :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 + 2 * (n : ℝ) ≤ (10 : ℝ) ^ ((1 / 16 : ℝ) * (n : ℝ)) := by
  let ε : ℝ := 1 / 16
  have hε : 0 < ε := by norm_num [ε]
  have hb : 0 < ε * Real.log 10 :=
    mul_pos hε (Real.log_pos (by norm_num))
  have ht :=
    DecimalFactorEntropy.TransversalEntropy.tendsto_affine_mul_exp_neg_nat
      2 1 (ε * Real.log 10) hb
  have hevent : ∀ᶠ n : ℕ in atTop,
      (2 * (n : ℝ) + 1) *
          Real.exp (-(ε * Real.log 10) * (n : ℝ)) ≤ 1 :=
    ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 N0, le_max_left _ _, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := (le_max_right 1 N0).trans hn
  have hbound := hN0 n hn0
  have hpos : 0 ≤ Real.exp ((ε * Real.log 10) * (n : ℝ)) :=
    (Real.exp_pos _).le
  have hexp : Real.exp (-(ε * Real.log 10) * (n : ℝ)) *
      Real.exp ((ε * Real.log 10) * (n : ℝ)) = 1 := by
    rw [← Real.exp_add]
    have hzero : -(ε * Real.log 10) * (n : ℝ) +
        ε * Real.log 10 * (n : ℝ) = 0 := by ring
    rw [hzero, Real.exp_zero]
  calc
    1 + 2 * (n : ℝ) = (2 * (n : ℝ) + 1) * 1 := by ring
    _ = (2 * (n : ℝ) + 1) *
        (Real.exp (-(ε * Real.log 10) * (n : ℝ)) *
          Real.exp ((ε * Real.log 10) * (n : ℝ))) := by rw [hexp]
    _ = ((2 * (n : ℝ) + 1) *
          Real.exp (-(ε * Real.log 10) * (n : ℝ))) *
        Real.exp ((ε * Real.log 10) * (n : ℝ)) := by ring
    _ ≤ 1 * Real.exp ((ε * Real.log 10) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hbound hpos
    _ = (10 : ℝ) ^ ((1 / 16 : ℝ) * (n : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
      dsimp [ε]
      ring

/-- The elementary absorption behind the one-scale entropy implication.
The summands are respectively long sector, diagonal, and both short-lag
orientations. -/
theorem sparse_subexponential_budget_implies_exponential_decay
    {a : ℕ → ℕ} (ha : SparseScaleSubexponential a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ((a n + sampleLength n + 2 * sampleLength n * n : ℕ) : ℝ) ≤
        (sampleLength n : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ)) := by
  obtain ⟨Na, hNa, hlong⟩ := ha (1 / 16) (by norm_num)
  obtain ⟨Np, hNp, hpoly⟩ :=
    eventually_one_add_two_mul_le_ten_rpow_sixteenth
  refine ⟨max (max Na Np) 2, by omega, ?_⟩
  intro n hn
  have hna : Na ≤ n := (le_max_left Na Np).trans
    ((le_max_left (max Na Np) 2).trans hn)
  have hnp : Np ≤ n := (le_max_right Na Np).trans
    ((le_max_left (max Na Np) 2).trans hn)
  have hn2 : 2 ≤ n := (le_max_right (max Na Np) 2).trans hn
  let L : ℝ := sampleLength n
  let p : ℝ := (10 : ℝ) ^ ((1 / 16 : ℝ) * (n : ℝ))
  have hL : 0 ≤ L := by positivity
  have hp : 0 ≤ p := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hlong' : (a n : ℝ) ≤ L * p := by
    simpa [L, p] using hlong n hna
  have hpoly' : 1 + 2 * (n : ℝ) ≤ p := by
    simpa [p] using hpoly n hnp
  have htwo : (2 : ℝ) ≤ p := by
    have hn2Real : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hLcast : L = (10 : ℝ) ^ (((n / 2 : ℕ) : ℝ)) := by
    dsimp [L, sampleLength, t56SampleLength]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hquarter : (1 / 4 : ℝ) * (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
    have hnat : n ≤ 4 * (n / 2) := by omega
    have hnatReal : (n : ℝ) ≤ 4 * ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hquarterPow :
      (10 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) ≤ L := by
    rw [hLcast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hquarter
  have hbudget :
      (a n : ℝ) + L + 2 * L * (n : ℝ) ≤
        L * (10 : ℝ) ^ ((1 / 8 : ℝ) * (n : ℝ)) := by
    calc
      (a n : ℝ) + L + 2 * L * (n : ℝ) =
          (a n : ℝ) + L * (1 + 2 * (n : ℝ)) := by ring
      _ ≤ L * p + L * p := by gcongr
      _ = L * (2 * p) := by ring
      _ ≤ L * (p * p) := by
        gcongr
      _ = L * (10 : ℝ) ^ ((1 / 8 : ℝ) * (n : ℝ)) := by
        dsimp [p]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
        congr 2
        ring
  calc
    ((a n + sampleLength n + 2 * sampleLength n * n : ℕ) : ℝ) =
        (a n : ℝ) + L + 2 * L * (n : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_mul]
      rfl
    _ ≤ L * (10 : ℝ) ^ ((1 / 8 : ℝ) * (n : ℝ)) := hbudget
    _ = L * ((10 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) *
          (10 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
      congr 2
      ring
    _ = (10 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) *
          (L * (10 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ))) := by ring
    _ ≤ L * (L * (10 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ))) := by
      gcongr
    _ = (sampleLength n : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ)) := by
      dsimp [L]
      ring

/-- Review A's exact-equality long-sector premise, with `o(n)` quantified. -/
def ExactLongSectorSubexponential : Prop :=
  SparseScaleSubexponential (fun n => R_pi n (sampleLength n))

/-- The feedback's exact-equality one-scale implication is valid under the
literal all-rates premise above. -/
theorem exactLongSectorSubexponential_implies_C2
    (hLong : ExactLongSectorSubexponential) :
    PiExponentialCollisionC2 := by
  obtain ⟨N, hN, hbudget⟩ :=
    sparse_subexponential_budget_implies_exponential_decay hLong
  refine ⟨1 / 8, by norm_num, N, hN, ?_⟩
  intro n hn
  refine ⟨sampleLength n, one_le_pow₀ (by norm_num), ?_⟩
  have hfinite :=
    piCylinderCollisionEnergy_le_R_pi_add_diagonal_add_short
      (N := sampleLength n) (hN.trans hn)
  rw [piCylinderCollisionEnergy_eq_E_pi] at hfinite
  have hfiniteReal :
      (E_pi n (sampleLength n) : ℝ) ≤
        ((R_pi n (sampleLength n) + sampleLength n +
          2 * sampleLength n * n : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  exact hfiniteReal.trans (hbudget n hn)

/-- Hence the exact-equality `L_n 10^{o(n)}` long-sector estimate implies
positive decimal factor entropy, conditionally and with exponent `1/8`. -/
theorem exactLongSectorSubexponential_implies_C1
    (hLong : ExactLongSectorSubexponential) :
    PiPositiveFactorEntropyC1 :=
  piExponentialCollisionC2_implies_C1
    (exactLongSectorSubexponential_implies_C2 hLong)

/-- The analogous all-rates premise for T56's literal residual long sector. -/
def ResidualLongSectorSubexponential (μ c : ℝ) (Q0 : ℕ) : Prop :=
  SparseScaleSubexponential (fun n =>
    longResidualPairCount μ c Q0 n (sampleLength n))

/-- On the literal T56 near-return statistic, the same elementary implication
requires the displayed arithmetic exclusion and residual long-sector premise. -/
theorem residualLongSectorSubexponential_implies_nearReturn_C2
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hLong : ResidualLongSectorSubexponential μ c Q0) :
    PiExponentialNearReturnC2 := by
  obtain ⟨N, hN, hbudget⟩ :=
    sparse_subexponential_budget_implies_exponential_decay hLong
  refine ⟨1 / 8, by norm_num, N, hN, ?_⟩
  intro n hn
  refine ⟨sampleLength n, one_le_pow₀ (by norm_num), ?_⟩
  have hEq : Q_pi n (sampleLength n) =
      sampleLength n + shortResidualPairCount μ c Q0 n (sampleLength n) +
        longResidualPairCount μ c Q0 n (sampleLength n) := by
    simpa using sparse_Q_eq_diagonal_add_short_add_long (hN.trans hn) hIrr
  have hShort : shortResidualPairCount μ c Q0 n (sampleLength n) ≤
      2 * sampleLength n * n :=
    literal_short_sector_coarse_bound μ c Q0 n
  have hfiniteNat :
      Q_pi n (sampleLength n) ≤
        longResidualPairCount μ c Q0 n (sampleLength n) +
          sampleLength n + 2 * sampleLength n * n := by
    omega
  have hfiniteReal :
      (Q_pi n (sampleLength n) : ℝ) ≤
        ((longResidualPairCount μ c Q0 n (sampleLength n) +
          sampleLength n + 2 * sampleLength n * n : ℕ) : ℝ) := by
    exact_mod_cast hfiniteNat
  exact hfiniteReal.trans (hbudget n hn)

/-- Conditional entropy conclusion for the literal T56 statistic. -/
theorem residualLongSectorSubexponential_implies_C1
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hLong : ResidualLongSectorSubexponential μ c Q0) :
    PiPositiveFactorEntropyC1 :=
  piExponentialNearReturnC2_implies_C1
    (residualLongSectorSubexponential_implies_nearReturn_C2 hIrr hLong)

/-- Ordered off-diagonal short equalities in a constant finite run. -/
def constantRunExactShortPairCount (n L : ℕ) : ℕ :=
  2 * ((Finset.Icc 1 (L - 1)).filter (fun r => r < n)).sum (fun r => L - r)

/-- Ordered off-diagonal short equal-block pairs for an arbitrary decimal
stream, written in the same positive-lag normalization as T1. -/
def exactShortPairCount (x : Stream (Fin 10)) (n L : ℕ) : ℕ :=
  by
    classical
    exact 2 * ∑ r ∈ (Finset.Icc 1 (L - 1)).filter (fun r => r < n),
      ((Finset.range (L - r)).filter fun i =>
        factorAt x n i = factorAt x n (i + r)).card

/-- A legal infinite decimal stream whose every digit is zero. -/
def constantDecimalStream : Stream (Fin 10) := fun _ => 0

/-- The numerical constant-run count above is the literal exact-equality
short-sector count of `constantDecimalStream`. -/
theorem exactShortPairCount_constantDecimalStream (n L : ℕ) :
    exactShortPairCount constantDecimalStream n L =
      constantRunExactShortPairCount n L := by
  classical
  unfold exactShortPairCount constantRunExactShortPairCount
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.card_filter_eq_iff.mpr]
  · simp
  · intro i _hi
    apply Subtype.ext
    funext j
    rfl

/-- A constant run contains the explicit `2(n-1)(L-n)` short-pair core.
This certifies Review A's order-`nL` existential mechanism. -/
theorem abstractShortIncidenceCount_le_constantRunExactShortPairCount
    {n L : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L) :
    abstractShortIncidenceCount n L ≤
      constantRunExactShortPairCount n L := by
  unfold abstractShortIncidenceCount constantRunExactShortPairCount
  have hset :
      (Finset.Icc 1 (L - 1)).filter (fun r => r < n) =
        Finset.Icc 1 (n - 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset]
  have hsum :
      (n - 1) * (L - n) ≤ ∑ r ∈ Finset.Icc 1 (n - 1), (L - r) := by
    calc
      (n - 1) * (L - n) = ∑ _r ∈ Finset.Icc 1 (n - 1), (L - n) := by
        simp [Nat.card_Icc, hn]
      _ ≤ ∑ r ∈ Finset.Icc 1 (n - 1), (L - r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrn : r ≤ n := by
          have := (Finset.mem_Icc.mp hr).2
          omega
        exact Nat.sub_le_sub_left hrn L
  simpa [mul_assoc] using Nat.mul_le_mul_left 2 hsum

/-- At `L=2n`, the certified constant-run core is `(n-1)L`. -/
theorem constantRun_short_core_order_nL (n : ℕ) (hn : 1 ≤ n) :
    (n - 1) * (2 * n) ≤ constantRunExactShortPairCount n (2 * n) := by
  have hcore := abstractShortIncidenceCount_le_constantRunExactShortPairCount
    hn (by omega : n ≤ 2 * n)
  have hsub : 2 * n - n = n := by omega
  have heq : abstractShortIncidenceCount n (2 * n) = (n - 1) * (2 * n) := by
    unfold abstractShortIncidenceCount
    rw [hsub]
    ring
  rw [← heq]
  exact hcore

/-- Whenever the sample has room for twice the block length, constant-run
short equalities already contribute at least `(n-1)L` ordered pairs. -/
theorem constantRun_short_pairs_ge_pred_mul_length
    {n L : ℕ} (hn : 1 ≤ n) (hroom : 2 * n ≤ L) :
    (n - 1) * L ≤ constantRunExactShortPairCount n L := by
  have hcore := abstractShortIncidenceCount_le_constantRunExactShortPairCount
    hn (by omega : n ≤ L)
  have hlength : L ≤ 2 * (L - n) := by omega
  have hlower : (n - 1) * L ≤ 2 * (n - 1) * (L - n) := by
    calc
      (n - 1) * L ≤ (n - 1) * (2 * (L - n)) :=
        Nat.mul_le_mul_left (n - 1) hlength
      _ = 2 * (n - 1) * (L - n) := by ring
  exact hlower.trans hcore

/-- The sparse sample `L_n=10^(floor(n/2))` eventually has room for `2n`. -/
theorem eventually_two_mul_le_sampleLength :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 2 * n ≤ sampleLength n := by
  obtain ⟨N0, hN0, hpoly⟩ :=
    eventually_one_add_two_mul_le_ten_rpow_sixteenth
  refine ⟨max N0 2, hN0.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := (le_max_left N0 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N0 2).trans hn
  have hexponent : (1 / 16 : ℝ) * (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
    have hnat : n ≤ 16 * (n / 2) := by omega
    have hnatReal : (n : ℝ) ≤ 16 * ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hpow : (10 : ℝ) ^ ((1 / 16 : ℝ) * (n : ℝ)) ≤
      (10 : ℝ) ^ ((n / 2 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hLcast : (sampleLength n : ℝ) =
      (10 : ℝ) ^ ((n / 2 : ℕ) : ℝ) := by
    dsimp [sampleLength, t56SampleLength]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hreal : ((2 * n : ℕ) : ℝ) ≤ (sampleLength n : ℝ) := by
    calc
      ((2 * n : ℕ) : ℝ) ≤ 1 + 2 * (n : ℝ) := by
        push_cast
        linarith
      _ ≤ (10 : ℝ) ^ ((1 / 16 : ℝ) * (n : ℝ)) := hpoly n hn0
      _ ≤ (10 : ℝ) ^ ((n / 2 : ℕ) : ℝ) := hpow
      _ = (sampleLength n : ℝ) := hLcast.symm
  exact_mod_cast hreal

/-- Review A's order-`nL_n` mechanism holds on the requested sparse scale for
the legal constant decimal stream. -/
theorem constantDecimalStream_sparse_short_pairs_order_nL :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (n - 1) * sampleLength n ≤
        exactShortPairCount constantDecimalStream n (sampleLength n) := by
  obtain ⟨N, hN, hroom⟩ := eventually_two_mul_le_sampleLength
  refine ⟨N, hN, ?_⟩
  intro n hn
  rw [exactShortPairCount_constantDecimalStream]
  exact constantRun_short_pairs_ge_pred_mul_length
    (hN.trans hn) (hroom n hn)

end DecimalFactorComplexity.T83LiteralStatisticAudit

#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.literal_C7_iff_quantifiers
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.literal_C7_iff_nearReturn_linear
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.literal_short_sector_range
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.literal_short_sector_coarse_bound
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.sparse_subexponential_budget_implies_exponential_decay
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.exactLongSectorSubexponential_implies_C1
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.residualLongSectorSubexponential_implies_C1
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.exactShortPairCount_constantDecimalStream
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.abstractShortIncidenceCount_le_constantRunExactShortPairCount
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.constantRun_short_core_order_nL
#print axioms DecimalFactorComplexity.T83LiteralStatisticAudit.constantDecimalStream_sparse_short_pairs_order_nL
