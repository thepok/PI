import TheoryLib.PiPositiveDecimalFactorEntropy.T61T61VaalerAnalytic
import TheoryLib.PiPositiveDecimalFactorEntropy.T86T86GroupedSquareBound

/-!
# T88: exact start truncation for the T61 signed short residual

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The exponent `888/125` remains an explicit effective-irrationality premise.
The late distinct-frequency covariance and T56 long-sector estimate also
remain explicit premises.  No unconditional assertion about `Real.pi`, C7,
C2, C1, or positive decimal factor entropy is made.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T88StartTruncation

open DecimalFactorComplexity
open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.SparseLongBandFejer
open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T61VaalerAnalytic
open DecimalFactorComplexity.T86GroupedSquareBound
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- The source-shaped exponent, kept as the exact rational `888/125`. -/
abbrev sourceMu : ℝ := 888 / 125

/-- The loss exponent is `sourceMu - 1 = 763/125`. -/
abbrev sourceLoss : ℝ := 763 / 125

/-- The optimized natural start cutoff `J_n = floor(125*n/763)`. -/
def startCutoff (n : ℕ) : ℕ := 125 * n / 763

/-- The effective irrationality input, including the source onset convention. -/
def SourceEffectiveIrrationality (Q0 : ℕ) : Prop :=
  2 ≤ Q0 ∧ EffectiveIrrationality Real.pi sourceMu 1 Q0

/-- The exact masked T61 residual labels whose starts precede `J_n`. -/
def earlyResidualRectangle (Q0 n : ℕ) : Finset (ℕ × ℕ) :=
  (residualShortRectangle sourceMu 1 Q0 n).filter fun p =>
    p.2 < startCutoff n

/-- The exact complementary masked late-start labels. -/
def lateResidualRectangle (Q0 n : ℕ) : Finset (ℕ × ℕ) :=
  (residualShortRectangle sourceMu 1 Q0 n).filter fun p =>
    startCutoff n ≤ p.2

/-- T86's exact tuple domain, filtered only by the strict early-start cutoff. -/
def earlyTupleDomain (Q0 n : ℕ) : Finset ResidualTuple :=
  (residualTupleDomain sourceMu 1 Q0 n).filter fun a =>
    a.2.2 < startCutoff n

/-- T86's exact tuple domain, filtered only by the complementary late cutoff. -/
def lateTupleDomain (Q0 n : ℕ) : Finset ResidualTuple :=
  (residualTupleDomain sourceMu 1 Q0 n).filter fun a =>
    startCutoff n ≤ a.2.2

/-- A frequency fiber inside an arbitrary finite tuple subset. -/
def restrictedFrequencyFiber (s : Finset ResidualTuple) (q : ℕ) :
    Finset ResidualTuple :=
  s.filter fun a => tupleFrequency a = q

/-- The exact positive-frequency support of a finite tuple subset. -/
def restrictedFrequencySupport (s : Finset ResidualTuple) : Finset ℕ :=
  s.image tupleFrequency

/-- The exact `2/L_n` grouped coefficient on a finite tuple subset. -/
def restrictedGroupedCoefficient
    (n : ℕ) (s : Finset ResidualTuple) (q : ℕ) : ℝ :=
  (2 : ℝ) / (sampleLength n : ℝ) *
    ∑ a ∈ restrictedFrequencyFiber s q, tupleWeight n a

/-- The signed positive-frequency cosine sum on a finite tuple subset. -/
def restrictedTupleCosineSum
    (n : ℕ) (s : Finset ResidualTuple) (x : ℝ) : ℝ :=
  2 * ∑ a ∈ s,
    tupleWeight n a *
      Real.cos (2 * Real.pi * (tupleFrequency a : ℝ) * x)

/-- The one-scale equal-frequency grouped square on a finite tuple subset. -/
def restrictedOneScaleEnergy (n : ℕ) (s : Finset ResidualTuple) : ℝ :=
  ∑ q ∈ restrictedFrequencySupport s,
    |restrictedGroupedCoefficient n s q| ^ 2

/-- The late coefficient, with the `2/L_n` normalization already included. -/
abbrev lateGroupedCoefficient (Q0 n q : ℕ) : ℝ :=
  restrictedGroupedCoefficient n (lateTupleDomain Q0 n) q

/-- The ordered off-diagonal contribution after grouping by distinct integers. -/
def normalizedLateDistinctCovariance (Q0 n : ℕ) : ℝ :=
  ∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
    ∑ q' ∈ (restrictedFrequencySupport (lateTupleDomain Q0 n)).erase q,
      lateGroupedCoefficient Q0 n q * lateGroupedCoefficient Q0 n q' *
        Real.cos (2 * Real.pi * (q : ℝ) * Real.pi) *
          Real.cos (2 * Real.pi * (q' : ℝ) * Real.pi)

/-- The sole new fixed-pi premise.  It concerns only ordered pairs of
distinct integer frequencies and is already normalized by `4/L_n^2`. -/
def PiLateDistinctCovarianceBound (Q0 : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
    ∀ n : ℕ, N0 ≤ n → |normalizedLateDistinctCovariance Q0 n| ≤ C

theorem startCutoff_and_source_constants (n : ℕ) :
    startCutoff n = 125 * n / 763 ∧
      sourceMu = (888 / 125 : ℝ) ∧
      sourceLoss = (763 / 125 : ℝ) ∧
      sourceMu - 1 = sourceLoss := by
  norm_num [startCutoff, sourceMu, sourceLoss]

theorem sourceEffectiveIrrationality_iff_quantifiers (Q0 : ℕ) :
    SourceEffectiveIrrationality Q0 ↔
      2 ≤ Q0 ∧ 0 < (1 : ℝ) ∧ 1 < (888 / 125 : ℝ) ∧
        ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ p : ℤ,
          1 / (q : ℝ) ^ (888 / 125 : ℝ) <
            |Real.pi - (p : ℝ) / q| := by
  rfl

theorem mem_earlyTupleDomain_iff
    {Q0 n : ℕ} {a : ResidualTuple} :
    a ∈ earlyTupleDomain Q0 n ↔
      1 ≤ a.1 ∧ a.1 < shortBandwidth n ∧
      0 < a.2.1 ∧ a.2.1 < n ∧
      a.2.1 < sampleLength n ∧
      a.2.2 < sampleLength n - a.2.1 ∧
      ¬ ArithmeticExcluded sourceMu 1 Q0 n a.2.2 a.2.1 ∧
      a.2.2 < startCutoff n := by
  rw [earlyTupleDomain, Finset.mem_filter, mem_residualTupleDomain_iff]
  tauto

theorem mem_lateTupleDomain_iff
    {Q0 n : ℕ} {a : ResidualTuple} :
    a ∈ lateTupleDomain Q0 n ↔
      1 ≤ a.1 ∧ a.1 < shortBandwidth n ∧
      0 < a.2.1 ∧ a.2.1 < n ∧
      a.2.1 < sampleLength n ∧
      a.2.2 < sampleLength n - a.2.1 ∧
      ¬ ArithmeticExcluded sourceMu 1 Q0 n a.2.2 a.2.1 ∧
      startCutoff n ≤ a.2.2 := by
  rw [lateTupleDomain, Finset.mem_filter, mem_residualTupleDomain_iff]
  tauto

theorem early_late_exact_partition (Q0 n : ℕ) :
    earlyTupleDomain Q0 n ∪ lateTupleDomain Q0 n =
        residualTupleDomain sourceMu 1 Q0 n ∧
      Disjoint (earlyTupleDomain Q0 n) (lateTupleDomain Q0 n) := by
  constructor
  · ext a
    by_cases ha : a ∈ residualTupleDomain sourceMu 1 Q0 n
    · simp [earlyTupleDomain, lateTupleDomain, ha, lt_or_ge]
    · simp [earlyTupleDomain, lateTupleDomain, ha]
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [earlyTupleDomain, lateTupleDomain, Finset.mem_filter] at ha hb
    omega

theorem earlyTupleDomain_eq_product (Q0 n : ℕ) :
    earlyTupleDomain Q0 n =
      T58TriangularFejerAudit.positiveFejerFrequencies n ×ˢ
        earlyResidualRectangle Q0 n := by
  ext a
  simp only [earlyTupleDomain, earlyResidualRectangle, residualTupleDomain,
    Finset.mem_filter, Finset.mem_product]
  tauto

theorem lateTupleDomain_eq_product (Q0 n : ℕ) :
    lateTupleDomain Q0 n =
      T58TriangularFejerAudit.positiveFejerFrequencies n ×ˢ
        lateResidualRectangle Q0 n := by
  ext a
  simp only [lateTupleDomain, lateResidualRectangle, residualTupleDomain,
    Finset.mem_filter, Finset.mem_product]
  tauto

theorem startCutoff_cast_le (n : ℕ) :
    (startCutoff n : ℝ) ≤ (125 / 763 : ℝ) * n := by
  have hnat : startCutoff n * 763 ≤ 125 * n := by
    simpa [startCutoff, mul_comm] using Nat.div_mul_le_self (125 * n) 763
  have hreal : (startCutoff n : ℝ) * 763 ≤ 125 * n := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  linarith

theorem earlyResidualRectangle_card_cast_le (Q0 n : ℕ) :
    ((earlyResidualRectangle Q0 n).card : ℝ) ≤
      (125 / 763 : ℝ) * (n : ℝ) ^ 2 := by
  let target : Finset (ℕ × ℕ) :=
    Finset.Ico 1 n ×ˢ Finset.range (startCutoff n)
  have hsubset : earlyResidualRectangle Q0 n ⊆ target := by
    intro p hp
    rw [earlyResidualRectangle, Finset.mem_filter] at hp
    have hrange := mem_residualShortRectangle_iff.mp hp.1
    simp only [target, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    exact ⟨⟨hrange.1, hrange.2.1⟩, hp.2⟩
  have hcardNat : (earlyResidualRectangle Q0 n).card ≤
      (n - 1) * startCutoff n := by
    calc
      (earlyResidualRectangle Q0 n).card ≤ target.card :=
        Finset.card_le_card hsubset
      _ = (n - 1) * startCutoff n := by
        simp only [target, Finset.card_product, Nat.card_Ico,
          Finset.card_range]
  have hcard : ((earlyResidualRectangle Q0 n).card : ℝ) ≤
      (n : ℝ) * startCutoff n := by
    exact_mod_cast hcardNat.trans
      (Nat.mul_le_mul (Nat.sub_le n 1) (le_refl (startCutoff n)))
  calc
    ((earlyResidualRectangle Q0 n).card : ℝ) ≤
        (n : ℝ) * startCutoff n := hcard
    _ ≤ (n : ℝ) * ((125 / 763 : ℝ) * n) := by
      gcongr
      exact startCutoff_cast_le n
    _ = (125 / 763 : ℝ) * (n : ℝ) ^ 2 := by ring

theorem sum_abs_vaalerCoefficient_lt_four_thirds
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ h ∈ Finset.Ico 1 (shortBandwidth n),
      |vaalerCoefficient (shortBandwidth n) h|) < 4 / 3 := by
  let H := shortBandwidth n
  have hHnat : 2 ≤ H := two_le_shortBandwidth n hn
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hpoint (h : ℕ) (hh : h ∈ Finset.Ico 1 H) :
      |vaalerCoefficient H h| ≤
        (H : ℝ)⁻¹ * (1 / 3 + 2 * (1 - (h : ℝ) / (H : ℝ))) := by
    have hh' := Finset.mem_Ico.mp hh
    have hratio0 : 0 ≤ (h : ℝ) / (H : ℝ) := by positivity
    have hratio1 : (h : ℝ) / (H : ℝ) < 1 := by
      rw [div_lt_one hHpos]
      exact_mod_cast hh'.2
    have hsine :
        |Real.sin (Real.pi * (h : ℝ) / (H : ℝ)) / Real.pi| ≤ 1 / 3 := by
      calc
        |Real.sin (Real.pi * (h : ℝ) / (H : ℝ)) / Real.pi| =
            |Real.sin (Real.pi * (h : ℝ) / (H : ℝ))| / Real.pi := by
          rw [abs_div, abs_of_pos Real.pi_pos]
        _ ≤ 1 / Real.pi := by
          gcongr
          exact Real.abs_sin_le_one _
        _ ≤ 1 / 3 := by
          exact (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1)
            Real.pi_pos (by norm_num : (0 : ℝ) < 3)).2
              (by linarith [Real.pi_gt_three])
    have hcosine :
        |2 * (1 - (h : ℝ) / (H : ℝ)) *
            Real.cos (Real.pi * (h : ℝ) / (H : ℝ))| ≤
          2 * (1 - (h : ℝ) / (H : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sub_nonneg.mpr hratio1.le)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    rw [vaalerCoefficient_explicit, abs_mul,
      abs_of_pos (inv_pos.mpr hHpos)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hHpos.le)
    exact (abs_add_le _ _).trans (add_le_add hsine hcosine)
  have hcard : ((Finset.Ico 1 H).card : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : 1 ≤ H)]
    norm_num
  calc
    (∑ h ∈ Finset.Ico 1 (shortBandwidth n),
        |vaalerCoefficient (shortBandwidth n) h|) =
        ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := by rfl
    _ ≤ ∑ h ∈ Finset.Ico 1 H,
        (H : ℝ)⁻¹ * (1 / 3 + 2 * (1 - (h : ℝ) / (H : ℝ))) :=
      Finset.sum_le_sum hpoint
    _ = (H : ℝ)⁻¹ *
        (((H : ℝ) - 1) / 3 + 2 * (((H : ℝ) - 1) / 2)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      rw [← Finset.mul_sum, sum_linear_weights H hHnat]
      ring
    _ < 4 / 3 := by
      have hHone : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
      field_simp [hHpos.ne']
      nlinarith

/-- The exact early-start estimate.  The constant is
`1000/2289 = (8/3)*(125/763)`; all residual masks remain in the sum. -/
theorem normalized_earlyTupleCosineSum_lt
    (Q0 n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    |restrictedTupleCosineSum n (earlyTupleDomain Q0 n) x /
        (sampleLength n : ℝ)| <
      (1000 / 2289 : ℝ) * (n : ℝ) ^ 2 /
        (sampleLength n : ℝ) := by
  classical
  let P := earlyResidualRectangle Q0 n
  let H := shortBandwidth n
  let L := sampleLength n
  have hLnat : 0 < L := by
    dsimp [L, sampleLength, t56SampleLength]
    positivity
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hinner (h : ℕ) :
      |∑ p ∈ P, tupleWeight n (h, p) *
          Real.cos (2 * Real.pi * (tupleFrequency (h, p) : ℝ) * x)| ≤
        (P.card : ℝ) * |vaalerCoefficient H h| := by
    calc
      |∑ p ∈ P, tupleWeight n (h, p) *
          Real.cos (2 * Real.pi * (tupleFrequency (h, p) : ℝ) * x)| ≤
          ∑ p ∈ P, |tupleWeight n (h, p) *
            Real.cos (2 * Real.pi * (tupleFrequency (h, p) : ℝ) * x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ P, |vaalerCoefficient H h| := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (Real.abs_cos_le_one _)
      _ = (P.card : ℝ) * |vaalerCoefficient H h| := by simp
  have htotal :
      |restrictedTupleCosineSum n (earlyTupleDomain Q0 n) x| ≤
        2 * (P.card : ℝ) *
          ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := by
    rw [restrictedTupleCosineSum, earlyTupleDomain_eq_product,
      Finset.sum_product]
    change |2 * ∑ h ∈ Finset.Ico 1 H,
      ∑ p ∈ P, tupleWeight n (h, p) *
        Real.cos (2 * Real.pi * (tupleFrequency (h, p) : ℝ) * x)| ≤ _
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |∑ h ∈ Finset.Ico 1 H,
          ∑ p ∈ P, tupleWeight n (h, p) *
            Real.cos (2 * Real.pi * (tupleFrequency (h, p) : ℝ) * x)| ≤
          2 * ∑ h ∈ Finset.Ico 1 H,
            |∑ p ∈ P, tupleWeight n (h, p) *
              Real.cos (2 * Real.pi * (tupleFrequency (h, p) : ℝ) * x)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ 2 * ∑ h ∈ Finset.Ico 1 H,
          (P.card : ℝ) * |vaalerCoefficient H h| := by
        gcongr with h hh
        exact hinner h
      _ = 2 * (P.card : ℝ) *
          ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := by
        rw [← Finset.mul_sum]
        ring
  have hmass :
      (∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h|) < 4 / 3 := by
    simpa [H] using sum_abs_vaalerCoefficient_lt_four_thirds n hn
  have hcard : (P.card : ℝ) ≤ (125 / 763 : ℝ) * (n : ℝ) ^ 2 := by
    simpa [P] using earlyResidualRectangle_card_cast_le Q0 n
  have hbound :
      |restrictedTupleCosineSum n (earlyTupleDomain Q0 n) x| <
        (1000 / 2289 : ℝ) * (n : ℝ) ^ 2 := by
    calc
      |restrictedTupleCosineSum n (earlyTupleDomain Q0 n) x| ≤
          2 * (P.card : ℝ) *
            ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := htotal
      _ ≤ 2 * ((125 / 763 : ℝ) * (n : ℝ) ^ 2) *
          ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := by
        gcongr
      _ < 2 * ((125 / 763 : ℝ) * (n : ℝ) ^ 2) * (4 / 3) := by
        gcongr
      _ = (1000 / 2289 : ℝ) * (n : ℝ) ^ 2 := by ring
  rw [abs_div, abs_of_pos hL]
  exact (div_lt_div_iff_of_pos_right hL).2 hbound

theorem square_le_four_mul_sampleLength (n : ℕ) :
    n ^ 2 ≤ 4 * sampleLength n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [sampleLength, t56SampleLength]
  | one => norm_num [sampleLength, t56SampleLength]
  | more n hn _ =>
      have hlength : sampleLength (n + 2) = 10 * sampleLength n := by
        simp only [sampleLength, t56SampleLength]
        rw [show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ]
        ring
      rw [hlength]
      by_cases hn0 : n = 0
      · subst n
        norm_num [sampleLength, t56SampleLength]
      · have hquad : (n + 2) ^ 2 ≤ 10 * n ^ 2 := by
          have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
          nlinarith
        calc
          (n + 2) ^ 2 ≤ 10 * n ^ 2 := hquad
          _ ≤ 10 * (4 * sampleLength n) := Nat.mul_le_mul_left 10 hn
          _ = 4 * (10 * sampleLength n) := by ring

theorem sampleLength_le_shortBandwidth (n : ℕ) (hn : 1 ≤ n) :
    sampleLength n ≤ shortBandwidth n := by
  have hexp : n / 2 + 1 ≤ n := by omega
  have hpow : 10 ^ (n / 2 + 1) ≤ 10 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have htwo : 2 * shortBandwidth n = 10 ^ n :=
    DecimalFactorComplexity.FejerSpectralCriterion.two_mul_half_ten_pow n hn
  have hten : 10 * sampleLength n = 10 ^ (n / 2 + 1) := by
    simp [sampleLength, t56SampleLength, pow_succ, mul_comm]
  omega

theorem residualStructuredCard_le (Q0 n : ℕ) :
    residualStructuredCard sourceMu 1 Q0 n ≤
      (n - 1) * sampleLength n := by
  let target : Finset (ℕ × ℕ) :=
    Finset.Ico 1 n ×ˢ Finset.range (sampleLength n)
  have hsubset : residualShortRectangle sourceMu 1 Q0 n ⊆ target := by
    intro p hp
    have hrange := mem_residualShortRectangle_iff.mp hp
    have hjL : p.2 < sampleLength n :=
      hrange.2.2.1.trans_le (Nat.sub_le (sampleLength n) p.1)
    simp only [target, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    exact ⟨⟨hrange.1, hrange.2.1⟩, hjL⟩
  have hcard : (residualShortRectangle sourceMu 1 Q0 n).card ≤
      (n - 1) * sampleLength n := by
    calc
      (residualShortRectangle sourceMu 1 Q0 n).card ≤ target.card :=
        Finset.card_le_card hsubset
      _ = (n - 1) * sampleLength n := by
        simp only [target, Finset.card_product, Nat.card_Ico,
          Finset.card_range]
  have heqReal : (residualStructuredCard sourceMu 1 Q0 n : ℝ) =
      ((residualShortRectangle sourceMu 1 Q0 n).card : ℝ) := by
    calc
      (residualStructuredCard sourceMu 1 Q0 n : ℝ) =
          ∑ r ∈ Theory.PiDigits.PositiveLowerBlockDensity.T26.shortResidualLags
              n (sampleLength n),
            ∑ _j ∈ residualStartDomain sourceMu 1 Q0 n r, (1 : ℝ) := by
        simp [residualStructuredCard]
      _ = ∑ p ∈ residualShortRectangle sourceMu 1 Q0 n, (1 : ℝ) := by
        symm
        exact sum_residualShortRectangle_eq_nested sourceMu 1 Q0 n
          (fun _r _j => (1 : ℝ))
      _ = ((residualShortRectangle sourceMu 1 Q0 n).card : ℝ) := by simp
  have heq : residualStructuredCard sourceMu 1 Q0 n =
      (residualShortRectangle sourceMu 1 Q0 n).card := by
    exact_mod_cast heqReal
  rw [heq]
  exact hcard

theorem normalized_zeroMode_le_eight (Q0 n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (2 / (shortBandwidth n : ℝ) *
          residualStructuredCard sourceMu 1 Q0 n) /
        (sampleLength n : ℝ) ∧
      (2 / (shortBandwidth n : ℝ) *
          residualStructuredCard sourceMu 1 Q0 n) /
        (sampleLength n : ℝ) ≤ 8 := by
  have hHnat : 0 < shortBandwidth n := by
    exact (two_le_shortBandwidth n hn).trans_lt' (by omega)
  have hLnat : 0 < sampleLength n := by positivity
  have hH : (0 : ℝ) < shortBandwidth n := by exact_mod_cast hHnat
  have hL : (0 : ℝ) < sampleLength n := by exact_mod_cast hLnat
  have hcard : (residualStructuredCard sourceMu 1 Q0 n : ℝ) ≤
      (n : ℝ) * sampleLength n := by
    exact_mod_cast (residualStructuredCard_le Q0 n).trans
      (Nat.mul_le_mul (Nat.sub_le n 1) (le_refl (sampleLength n)))
  have hnSquare : n ≤ n ^ 2 := by nlinarith
  have hnFourL : n ≤ 4 * sampleLength n :=
    hnSquare.trans (square_le_four_mul_sampleLength n)
  have hLH := sampleLength_le_shortBandwidth n hn
  have hnFourH : n ≤ 4 * shortBandwidth n :=
    hnFourL.trans (Nat.mul_le_mul_left 4 hLH)
  constructor
  · positivity
  · have hnReal : (n : ℝ) ≤ 4 * shortBandwidth n := by exact_mod_cast hnFourH
    calc
      (2 / (shortBandwidth n : ℝ) *
            residualStructuredCard sourceMu 1 Q0 n) /
          (sampleLength n : ℝ) ≤
          (2 / (shortBandwidth n : ℝ) *
            ((n : ℝ) * sampleLength n)) /
          (sampleLength n : ℝ) := by gcongr
      _ = 2 * (n : ℝ) / shortBandwidth n := by
        field_simp [hH.ne', hL.ne']
      _ ≤ 8 := by
        apply (div_le_iff₀ hH).2
        nlinarith

theorem restricted_normalized_frequency_grouping
    (n : ℕ) (s : Finset ResidualTuple) (x : ℝ) :
    restrictedTupleCosineSum n s x / (sampleLength n : ℝ) =
      ∑ q ∈ restrictedFrequencySupport s,
        restrictedGroupedCoefficient n s q *
          Real.cos (2 * Real.pi * (q : ℝ) * x) := by
  classical
  let phase : ℕ → ℝ := fun q =>
    Real.cos (2 * Real.pi * (q : ℝ) * x)
  have hmaps : ∀ a ∈ s, tupleFrequency a ∈ restrictedFrequencySupport s := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hgroup :
      (∑ q ∈ restrictedFrequencySupport s,
          ∑ a ∈ s with tupleFrequency a = q,
            tupleWeight n a * phase (tupleFrequency a)) =
        ∑ a ∈ s, tupleWeight n a * phase (tupleFrequency a) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  symm
  calc
    (∑ q ∈ restrictedFrequencySupport s,
        restrictedGroupedCoefficient n s q *
          Real.cos (2 * Real.pi * (q : ℝ) * x)) =
        (2 / (sampleLength n : ℝ)) *
          ∑ q ∈ restrictedFrequencySupport s,
            (∑ a ∈ s with tupleFrequency a = q, tupleWeight n a) * phase q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [phase, restrictedGroupedCoefficient, restrictedFrequencyFiber]
      ring
    _ = (2 / (sampleLength n : ℝ)) *
          ∑ q ∈ restrictedFrequencySupport s,
            ∑ a ∈ s with tupleFrequency a = q,
              tupleWeight n a * phase (tupleFrequency a) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = (2 / (sampleLength n : ℝ)) *
          ∑ a ∈ s, tupleWeight n a * phase (tupleFrequency a) := by
      rw [hgroup]
    _ = restrictedTupleCosineSum n s x / (sampleLength n : ℝ) := by
      simp only [restrictedTupleCosineSum, phase]
      ring

theorem signed_sum_eq_early_add_late (Q0 n : ℕ) :
    signedStructuredDenominatorSum sourceMu 1 Q0 n =
      restrictedTupleCosineSum n (earlyTupleDomain Q0 n) Real.pi +
        restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi := by
  classical
  rw [← residualTupleCosineSum_pi_eq_T61]
  unfold residualTupleCosineSum restrictedTupleCosineSum
  have hpart := (early_late_exact_partition Q0 n).1
  have hdisj := (early_late_exact_partition Q0 n).2
  rw [← hpart, Finset.sum_union hdisj]
  ring

theorem lateGroupedCoefficient_eq_explicit (Q0 n q : ℕ) :
    lateGroupedCoefficient Q0 n q =
      (2 : ℝ) / (sampleLength n : ℝ) *
        ∑ a ∈ restrictedFrequencyFiber (lateTupleDomain Q0 n) q,
          ((shortBandwidth n : ℝ)⁻¹ *
            (Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ)) /
                Real.pi +
              2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
                Real.cos (Real.pi * (a.1 : ℝ) /
                  (shortBandwidth n : ℝ)))) := by
  unfold lateGroupedCoefficient restrictedGroupedCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact tupleWeight_explicit n a

/-- The late grouped family contains only positive integer frequencies.  T61's
zero Fourier mode remains the separate term bounded above. -/
theorem lateGroupedCoefficient_zero_frequency (Q0 n : ℕ) :
    lateGroupedCoefficient Q0 n 0 = 0 := by
  have hfiber : restrictedFrequencyFiber (lateTupleDomain Q0 n) 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    rw [restrictedFrequencyFiber, Finset.mem_filter] at ha
    have hbase : a ∈ residualTupleDomain sourceMu 1 Q0 n :=
      (Finset.mem_filter.mp ha.1).1
    have hsupport : tupleFrequency a ∈ frequencySupport sourceMu 1 Q0 n :=
      mem_frequencySupport_iff.mpr ⟨a, hbase, rfl⟩
    have hpositive := frequencySupport_positive hsupport
    omega
  simp [lateGroupedCoefficient, restrictedGroupedCoefficient, hfiber]

theorem piLateDistinctCovarianceBound_iff_quantifiers (Q0 : ℕ) :
    PiLateDistinctCovarianceBound Q0 ↔
      ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
        ∀ n : ℕ, N0 ≤ n →
          |∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
            ∑ q' ∈ (restrictedFrequencySupport (lateTupleDomain Q0 n)).erase q,
              ((2 : ℝ) / (sampleLength n : ℝ) *
                  ∑ a ∈ restrictedFrequencyFiber (lateTupleDomain Q0 n) q,
                    tupleWeight n a) *
                ((2 : ℝ) / (sampleLength n : ℝ) *
                  ∑ a ∈ restrictedFrequencyFiber (lateTupleDomain Q0 n) q',
                    tupleWeight n a) *
                Real.cos (2 * Real.pi * (q : ℝ) * Real.pi) *
                Real.cos (2 * Real.pi * (q' : ℝ) * Real.pi)| ≤ C := by
  rfl

/-! ## Subset-stable equal-frequency control -/

theorem restrictedFrequencyFiber_card_le
    {μ c : ℝ} {Q0 n q : ℕ} {s : Finset ResidualTuple}
    (hs : s ⊆ residualTupleDomain μ c Q0 n) (hn : 1 ≤ n) :
    (restrictedFrequencyFiber s q).card ≤ n * (n - 1) := by
  apply le_trans (Finset.card_le_card (s := restrictedFrequencyFiber s q)
    (t := frequencyFiber μ c Q0 n q) ?_)
  · exact frequencyFiber_card_le μ c Q0 n q hn
  · intro a ha
    rw [restrictedFrequencyFiber, Finset.mem_filter] at ha
    rw [frequencyFiber, Finset.mem_filter]
    exact ⟨hs ha.1, ha.2⟩

theorem restrictedOneScaleEnergy_le_fiber_weight
    {μ c : ℝ} {Q0 n : ℕ} {s : Finset ResidualTuple}
    (hs : s ⊆ residualTupleDomain μ c Q0 n) (hn : 1 ≤ n) :
    restrictedOneScaleEnergy n s ≤
      (4 / (sampleLength n : ℝ) ^ 2) * (n * (n - 1) : ℕ) *
        ∑ a ∈ s, tupleWeight n a ^ 2 := by
  classical
  let Q := restrictedFrequencySupport s
  let C : ℝ := (n * (n - 1) : ℕ)
  let F : ℝ := 4 / (sampleLength n : ℝ) ^ 2
  have hmaps : ∀ a ∈ s, tupleFrequency a ∈ Q := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hregroup :
      (∑ q ∈ Q, ∑ a ∈ s with tupleFrequency a = q,
          tupleWeight n a ^ 2) = ∑ a ∈ s, tupleWeight n a ^ 2 :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hfiber (q : ℕ) :
      (∑ a ∈ restrictedFrequencyFiber s q, tupleWeight n a) ^ 2 ≤
        C * ∑ a ∈ restrictedFrequencyFiber s q, tupleWeight n a ^ 2 := by
    calc
      (∑ a ∈ restrictedFrequencyFiber s q, tupleWeight n a) ^ 2 ≤
          ((restrictedFrequencyFiber s q).card : ℝ) *
            ∑ a ∈ restrictedFrequencyFiber s q, tupleWeight n a ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ C * ∑ a ∈ restrictedFrequencyFiber s q,
          tupleWeight n a ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C]
          exact_mod_cast restrictedFrequencyFiber_card_le hs hn
        · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF : 0 ≤ F := by dsimp [F]; positivity
  calc
    restrictedOneScaleEnergy n s =
        F * ∑ q ∈ Q,
          (∑ a ∈ restrictedFrequencyFiber s q, tupleWeight n a) ^ 2 := by
      unfold restrictedOneScaleEnergy restrictedGroupedCoefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [F, sq_abs]
      ring
    _ ≤ F * ∑ q ∈ Q,
          C * ∑ a ∈ restrictedFrequencyFiber s q,
            tupleWeight n a ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hF
      exact Finset.sum_le_sum fun q _ => hfiber q
    _ = F * C * ∑ a ∈ s, tupleWeight n a ^ 2 := by
      rw [← Finset.mul_sum]
      simp only [restrictedFrequencyFiber] at hregroup ⊢
      rw [hregroup]
      ring
    _ = (4 / (sampleLength n : ℝ) ^ 2) * (n * (n - 1) : ℕ) *
          ∑ a ∈ s, tupleWeight n a ^ 2 := by rfl

theorem restrictedOneScaleEnergy_lt
    {μ c : ℝ} {Q0 n : ℕ} {s : Finset ResidualTuple}
    (hs : s ⊆ residualTupleDomain μ c Q0 n) (hn : 2 ≤ n) :
    restrictedOneScaleEnergy n s <
      36 * (n : ℝ) ^ 3 /
        ((shortBandwidth n : ℝ) * (sampleLength n : ℝ)) := by
  classical
  let H := shortBandwidth n
  let L := sampleLength n
  have hn1 : 1 ≤ n := by omega
  have hHnat : 1 ≤ H := by
    exact (two_le_shortBandwidth n hn1).trans' (by omega)
  have hLnat : 0 < L := by
    dsimp [L, sampleLength, t56SampleLength]
    positivity
  have hH : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hsquare (a : ResidualTuple) (ha : a ∈ s) :
      tupleWeight n a ^ 2 ≤ 9 / (H : ℝ) ^ 2 := by
    have habs := (abs_tupleWeight_lt_three_div (hs ha)).le
    have hnonneg : (0 : ℝ) ≤ 3 / H := by positivity
    calc
      tupleWeight n a ^ 2 = |tupleWeight n a| ^ 2 := by rw [sq_abs]
      _ ≤ (3 / (H : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 9 / (H : ℝ) ^ 2 := by ring
  have hsum :
      (∑ a ∈ s, tupleWeight n a ^ 2) ≤
        (s.card : ℝ) * (9 / (H : ℝ) ^ 2) := by
    calc
      (∑ a ∈ s, tupleWeight n a ^ 2) ≤
          ∑ _a ∈ s, 9 / (H : ℝ) ^ 2 := Finset.sum_le_sum hsquare
      _ = (s.card : ℝ) * (9 / (H : ℝ) ^ 2) := by simp
  have hcardNat : s.card ≤ (H - 1) * (n - 1) * L :=
    (Finset.card_le_card hs).trans (residualTupleDomain_card_le μ c Q0 n)
  have hcard : (s.card : ℝ) ≤ (((H - 1) * (n - 1) * L : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hsum' :
      (∑ a ∈ s, tupleWeight n a ^ 2) ≤
        (((H - 1) * (n - 1) * L : ℕ) : ℝ) *
          (9 / (H : ℝ) ^ 2) :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hbase := restrictedOneScaleEnergy_le_fiber_weight hs hn1
  change restrictedOneScaleEnergy n s <
    36 * (n : ℝ) ^ 3 / ((H : ℝ) * (L : ℝ))
  calc
    restrictedOneScaleEnergy n s ≤
        (4 / (L : ℝ) ^ 2) * ((n * (n - 1) : ℕ) : ℝ) *
          ∑ a ∈ s, tupleWeight n a ^ 2 := by simpa [L] using hbase
    _ ≤ (4 / (L : ℝ) ^ 2) * ((n * (n - 1) : ℕ) : ℝ) *
          ((((H - 1) * (n - 1) * L : ℕ) : ℝ) *
            (9 / (H : ℝ) ^ 2)) := by gcongr
    _ < (4 / (L : ℝ) ^ 2) * ((n * n : ℕ) : ℝ) *
          ((((H : ℕ) * n * L : ℕ) : ℝ) *
            (9 / (H : ℝ) ^ 2)) := by
      have hnsub : n - 1 ≤ n := Nat.sub_le n 1
      have hHsub : H - 1 < H := Nat.sub_lt (by omega) (by omega)
      norm_cast
      gcongr <;> omega
    _ = 36 * (n : ℝ) ^ 3 / ((H : ℝ) * (L : ℝ)) := by
      field_simp [hH.ne', hL.ne']
      push_cast
      ring

theorem restrictedOneScaleEnergy_lt_square_envelope
    {μ c : ℝ} {Q0 n : ℕ} {s : Finset ResidualTuple}
    (hs : s ⊆ residualTupleDomain μ c Q0 n) (hn : 2 ≤ n) :
    restrictedOneScaleEnergy n s <
      (24 * (n : ℝ) ^ 2 / 5 ^ n) ^ 2 := by
  let H := shortBandwidth n
  let L := sampleLength n
  have hn1 : 1 ≤ n := by omega
  have hHnat : 0 < H := (two_le_shortBandwidth n hn1).trans_lt' (by omega)
  have hLnat : 0 < L := by
    dsimp [L, sampleLength, t56SampleLength]
    positivity
  have htwo : 2 * H = 10 ^ n := by
    simpa [H, shortBandwidth] using
      DecimalFactorComplexity.FejerSpectralCriterion.two_mul_half_ten_pow n hn1
  have hLdef : L = 10 ^ (n / 2) := rfl
  have hprod : 2 * (H * L) = 10 ^ (n + n / 2) := by
    calc
      2 * (H * L) = (2 * H) * L := by ring
      _ = 10 ^ n * 10 ^ (n / 2) := by rw [htwo, hLdef]
      _ = 10 ^ (n + n / 2) := by rw [pow_add]
  have hpNat : 25 ^ n < 16 * n * H * L := by
    calc
      25 ^ n ≤ 2 * 10 ^ (n + n / 2) := twentyfive_pow_le_decimalProduct n hn
      _ = 4 * (H * L) := by rw [← hprod]; ring
      _ < 16 * n * H * L := by
        have hHL : 0 < H * L := Nat.mul_pos hHnat hLnat
        nlinarith
  have hp : (25 : ℝ) ^ n < 16 * (n : ℝ) * (H : ℝ) * (L : ℝ) := by
    exact_mod_cast hpNat
  have hH : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hfive : ((5 : ℝ) ^ n) ^ 2 = (25 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  calc
    restrictedOneScaleEnergy n s <
        36 * (n : ℝ) ^ 3 / ((H : ℝ) * (L : ℝ)) := by
      simpa [H, L] using restrictedOneScaleEnergy_lt hs hn
    _ < (24 * (n : ℝ) ^ 2 / 5 ^ n) ^ 2 := by
      rw [div_pow]
      apply (div_lt_div_iff₀ (mul_pos hH hL) (sq_pos_of_pos (by positivity))).2
      rw [hfive]
      have hmul := mul_lt_mul_of_pos_left hp
        (show (0 : ℝ) < 36 * (n : ℝ) ^ 3 by positivity)
      nlinarith [hmul]

/-- T86's fiber and coefficient estimates are stable under tuple deletion;
in particular the late equal-frequency square remains below `42`. -/
theorem late_equalFrequency_groupedSquare_lt_fortyTwo
    (Q0 n : ℕ) (hn : 2 ≤ n) :
    restrictedOneScaleEnergy n (lateTupleDomain Q0 n) < 42 := by
  have hs : lateTupleDomain Q0 n ⊆ residualTupleDomain sourceMu 1 Q0 n := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have henergy := restrictedOneScaleEnergy_lt_square_envelope hs hn
  have hterm : 24 * (n : ℝ) ^ 2 / 5 ^ n < 129 / 20 := by
    have hmem : n ∈ Finset.Icc 2 n := by simp [hn]
    have hle : 24 * (n : ℝ) ^ 2 / 5 ^ n ≤
        ∑ k ∈ Finset.Icc 2 n, 24 * (k : ℝ) ^ 2 / 5 ^ k :=
      Finset.single_le_sum (s := Finset.Icc 2 n)
        (f := fun k : ℕ => 24 * (k : ℝ) ^ 2 / 5 ^ k)
        (fun k _ => by positivity) hmem
    exact hle.trans_lt (finite_envelope_sum_lt n)
  have hpos : 0 ≤ 24 * (n : ℝ) ^ 2 / 5 ^ n := by positivity
  have hsquare : (24 * (n : ℝ) ^ 2 / 5 ^ n) ^ 2 < (129 / 20 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hpos (by positivity)).mpr hterm
  nlinarith

/-! ## Equal/distinct frequency split and the conditional bridge -/

theorem sq_sum_eq_diagonal_add_ordered_distinct
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 =
      (∑ i ∈ s, f i ^ 2) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_erase_add _ _ hi]
  ring

theorem normalized_late_square_eq_equal_add_distinct (Q0 n : ℕ) :
    (restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi /
        (sampleLength n : ℝ)) ^ 2 =
      (∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
        (lateGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) +
        normalizedLateDistinctCovariance Q0 n := by
  rw [restricted_normalized_frequency_grouping]
  calc
    (∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
        lateGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2 =
        (∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
          (lateGroupedCoefficient Q0 n q *
            Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) +
          ∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
            ∑ q' ∈ (restrictedFrequencySupport (lateTupleDomain Q0 n)).erase q,
              (lateGroupedCoefficient Q0 n q *
                Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) *
              (lateGroupedCoefficient Q0 n q' *
                Real.cos (2 * Real.pi * (q' : ℝ) * Real.pi)) :=
      sq_sum_eq_diagonal_add_ordered_distinct _ _
    _ = _ := by
      congr 1
      unfold normalizedLateDistinctCovariance
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro q' hq'
      ring

theorem normalized_late_equalFrequencyTerm_lt_fortyTwo
    (Q0 n : ℕ) (hn : 2 ≤ n) :
    (∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
      (lateGroupedCoefficient Q0 n q *
        Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) < 42 := by
  calc
    (∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
        (lateGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) ≤
        restrictedOneScaleEnergy n (lateTupleDomain Q0 n) := by
      unfold restrictedOneScaleEnergy
      apply Finset.sum_le_sum
      intro q hq
      rw [mul_pow]
      have hcos : Real.cos (2 * Real.pi * (q : ℝ) * Real.pi) ^ 2 ≤ 1 := by
        calc
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi) ^ 2 =
              |Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)| ^ 2 := by
            rw [sq_abs]
          _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
            (Real.abs_cos_le_one _) 2
          _ = 1 := by norm_num
      have hcoeff : 0 ≤ |lateGroupedCoefficient Q0 n q| ^ 2 := sq_nonneg _
      rw [sq_abs]
      nlinarith
    _ < 42 := late_equalFrequency_groupedSquare_lt_fortyTwo Q0 n hn

theorem normalized_late_square_le_fortyTwo_add_covariance
    (Q0 n : ℕ) (hn : 2 ≤ n) :
    (restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi /
        (sampleLength n : ℝ)) ^ 2 <
      42 + |normalizedLateDistinctCovariance Q0 n| := by
  rw [normalized_late_square_eq_equal_add_distinct]
  have hequal := normalized_late_equalFrequencyTerm_lt_fortyTwo Q0 n hn
  have hcov := le_abs_self (normalizedLateDistinctCovariance Q0 n)
  linarith

theorem piLateDistinctCovarianceBound_implies_signedPremise
    {Q0 : ℕ} (hCov : PiLateDistinctCovarianceBound Q0) :
    SignedStructuredDenominatorPremise sourceMu 1 Q0 := by
  obtain ⟨C, hC, N0, hN0, hcov⟩ := hCov
  refine ⟨C + 53, by positivity, N0, by omega, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := hN0.trans hn
  have hn1 : 1 ≤ n := by omega
  let L : ℝ := sampleLength n
  let early : ℝ :=
    restrictedTupleCosineSum n (earlyTupleDomain Q0 n) Real.pi / L
  let late : ℝ :=
    restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi / L
  let zero : ℝ :=
    (2 / (shortBandwidth n : ℝ) *
      residualStructuredCard sourceMu 1 Q0 n) / L
  have hL : 0 < L := by
    dsimp [L, sampleLength, t56SampleLength]
    positivity
  have hzero : zero ≤ 8 := by
    simpa [zero, L] using (normalized_zeroMode_le_eight Q0 n hn1).2
  have hearlyRaw := normalized_earlyTupleCosineSum_lt Q0 n hn1 Real.pi
  have hsquareNat := square_le_four_mul_sampleLength n
  have hsquare : (n : ℝ) ^ 2 ≤ 4 * L := by
    dsimp [L]
    exact_mod_cast hsquareNat
  have hearly : |early| < 2 := by
    have hratio :
        (1000 / 2289 : ℝ) * (n : ℝ) ^ 2 / L ≤
          (1000 / 2289 : ℝ) * 4 := by
      apply (div_le_iff₀ hL).2
      nlinarith
    have hconst : (1000 / 2289 : ℝ) * 4 < 2 := by norm_num
    exact hearlyRaw.trans_le hratio |>.trans hconst
  have hlateSquare : late ^ 2 < 42 + C := by
    have hbase := normalized_late_square_le_fortyTwo_add_covariance Q0 n hn2
    have hcovn := hcov n hn
    exact hbase.trans_le (by simpa [add_comm] using add_le_add_left hcovn 42)
  have habsLate_le : |late| ≤ late ^ 2 + 1 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|late| - 1)]
  have hlate : |late| < C + 43 := by linarith
  have hdecomposition :
      completeStructuredVaalerExpression sourceMu 1 Q0 n / L =
        zero + early + late := by
    unfold completeStructuredVaalerExpression
    rw [signed_sum_eq_early_add_late]
    dsimp [zero, early, late]
    ring
  have hnormalized :
      completeStructuredVaalerExpression sourceMu 1 Q0 n / L < C + 53 := by
    rw [hdecomposition]
    have hearUpper : early ≤ |early| := le_abs_self early
    have hlateUpper : late ≤ |late| := le_abs_self late
    linarith
  have hmul := (div_le_iff₀ hL).mp hnormalized.le
  simpa [L] using hmul

/-- Complete conditional chain.  The source-shaped irrationality premise,
the sole late distinct-frequency covariance premise, and T56's separate
long-sector premise are all explicit arguments. -/
theorem source_covariance_longSector_conditional_chain
    {Q0 : ℕ}
    (hSource : SourceEffectiveIrrationality Q0)
    (hCov : PiLateDistinctCovarianceBound Q0)
    (hLong : SparseLongResidualLinearBound sourceMu 1 Q0) :
    SignedStructuredDenominatorPremise sourceMu 1 Q0 ∧
      SparseShortRepunitIncidenceBound sourceMu 1 Q0 ∧
      PiSparseLongBandC7 ∧ PiExponentialCollisionC2 ∧
        PiPositiveFactorEntropyC1 := by
  have hSigned := piLateDistinctCovarianceBound_implies_signedPremise hCov
  obtain ⟨hShort, hC7, hC2, hC1⟩ :=
    signedStructuredDenominator_conditional_chain hSource.2 hLong hSigned
  exact ⟨hSigned, hShort, hC7, hC2, hC1⟩

end DecimalFactorComplexity.T88StartTruncation

#print axioms DecimalFactorComplexity.T88StartTruncation.startCutoff_and_source_constants
#print axioms DecimalFactorComplexity.T88StartTruncation.sourceEffectiveIrrationality_iff_quantifiers
#print axioms DecimalFactorComplexity.T88StartTruncation.mem_earlyTupleDomain_iff
#print axioms DecimalFactorComplexity.T88StartTruncation.mem_lateTupleDomain_iff
#print axioms DecimalFactorComplexity.T88StartTruncation.early_late_exact_partition
#print axioms DecimalFactorComplexity.T88StartTruncation.normalized_earlyTupleCosineSum_lt
#print axioms DecimalFactorComplexity.T88StartTruncation.normalized_zeroMode_le_eight
#print axioms DecimalFactorComplexity.T88StartTruncation.restricted_normalized_frequency_grouping
#print axioms DecimalFactorComplexity.T88StartTruncation.lateGroupedCoefficient_eq_explicit
#print axioms DecimalFactorComplexity.T88StartTruncation.lateGroupedCoefficient_zero_frequency
#print axioms DecimalFactorComplexity.T88StartTruncation.piLateDistinctCovarianceBound_iff_quantifiers
#print axioms DecimalFactorComplexity.T88StartTruncation.restrictedOneScaleEnergy_le_fiber_weight
#print axioms DecimalFactorComplexity.T88StartTruncation.late_equalFrequency_groupedSquare_lt_fortyTwo
#print axioms DecimalFactorComplexity.T88StartTruncation.normalized_late_square_eq_equal_add_distinct
#print axioms DecimalFactorComplexity.T88StartTruncation.normalized_late_equalFrequencyTerm_lt_fortyTwo
#print axioms DecimalFactorComplexity.T88StartTruncation.piLateDistinctCovarianceBound_implies_signedPremise
#print axioms DecimalFactorComplexity.T88StartTruncation.source_covariance_longSector_conditional_chain
