import TheoryLib.PiPositiveDecimalFactorEntropy.T61T61VaalerAnalytic
import TheoryLib.PiPositiveDecimalFactorEntropy.T86T86GroupedSquareBound
import TheoryLib.PiPositiveDecimalFactorEntropy.T88T88StartTruncation

/-!
# T89: diagonal truncation of the T61 signed short residual

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

Every genuinely arithmetic fixed-pi estimate below remains an explicit
premise.  Deterministic identities and phase-uniform coefficient bounds are
specialized at `Real.pi`, but no covariance or long-sector estimate is proved
there, nor is any instance of C7, C2, C1, or positive decimal factor entropy.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T89DiagonalTruncation

open DecimalFactorComplexity
open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T61VaalerAnalytic
open DecimalFactorComplexity.T86GroupedSquareBound
open DecimalFactorComplexity.T88StartTruncation
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- The inclusive irrationality-aligned diagonal mask.  The endpoint is
included because T25's arithmetic exclusion comparison is non-strict. -/
def diagonalTupleDomain (Q0 n : ℕ) : Finset ResidualTuple :=
  (residualTupleDomain sourceMu 1 Q0 n).filter fun a =>
    a.2.2 + a.2.1 ≤ startCutoff n

/-- The exact complementary tuple domain. -/
def diagonalComplementTupleDomain (Q0 n : ℕ) : Finset ResidualTuple :=
  (residualTupleDomain sourceMu 1 Q0 n).filter fun a =>
    startCutoff n < a.2.2 + a.2.1

/-- The corresponding masked `(r,j)` diagonal labels. -/
def diagonalResidualRectangle (Q0 n : ℕ) : Finset (ℕ × ℕ) :=
  (residualShortRectangle sourceMu 1 Q0 n).filter fun p =>
    p.2 + p.1 ≤ startCutoff n

theorem mem_diagonalTupleDomain_iff
    {Q0 n : ℕ} {a : ResidualTuple} :
    a ∈ diagonalTupleDomain Q0 n ↔
      1 ≤ a.1 ∧ a.1 < shortBandwidth n ∧
      0 < a.2.1 ∧ a.2.1 < n ∧
      a.2.1 < sampleLength n ∧
      a.2.2 < sampleLength n - a.2.1 ∧
      ¬ ArithmeticExcluded sourceMu 1 Q0 n a.2.2 a.2.1 ∧
      a.2.2 + a.2.1 ≤ startCutoff n := by
  rw [diagonalTupleDomain, Finset.mem_filter, mem_residualTupleDomain_iff]
  tauto

theorem mem_diagonalComplementTupleDomain_iff
    {Q0 n : ℕ} {a : ResidualTuple} :
    a ∈ diagonalComplementTupleDomain Q0 n ↔
      1 ≤ a.1 ∧ a.1 < shortBandwidth n ∧
      0 < a.2.1 ∧ a.2.1 < n ∧
      a.2.1 < sampleLength n ∧
      a.2.2 < sampleLength n - a.2.1 ∧
      ¬ ArithmeticExcluded sourceMu 1 Q0 n a.2.2 a.2.1 ∧
      startCutoff n < a.2.2 + a.2.1 := by
  rw [diagonalComplementTupleDomain, Finset.mem_filter,
    mem_residualTupleDomain_iff]
  tauto

theorem diagonal_exact_partition (Q0 n : ℕ) :
    diagonalTupleDomain Q0 n ∪ diagonalComplementTupleDomain Q0 n =
        residualTupleDomain sourceMu 1 Q0 n ∧
      Disjoint (diagonalTupleDomain Q0 n)
        (diagonalComplementTupleDomain Q0 n) := by
  constructor
  · ext a
    by_cases ha : a ∈ residualTupleDomain sourceMu 1 Q0 n
    · simp [diagonalTupleDomain, diagonalComplementTupleDomain, ha,
        le_or_gt]
    · simp [diagonalTupleDomain, diagonalComplementTupleDomain, ha]
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [diagonalTupleDomain, diagonalComplementTupleDomain,
      Finset.mem_filter] at ha hb
    omega

/-- Decimal growth at the inclusive diagonal endpoint places the structured
denominator inside T25's arithmetic exclusion region once it reaches `Q0`. -/
theorem arithmeticExcluded_of_sum_le_startCutoff
    {Q0 n j r : ℕ} (hr : 0 < r)
    (hQ0 : Q0 ≤ structuredDenominator j r)
    (hdiag : j + r ≤ startCutoff n) :
    ArithmeticExcluded sourceMu 1 Q0 n j r := by
  refine ⟨hQ0, ?_⟩
  have hdenNat : 0 < structuredDenominator j r := by
    unfold structuredDenominator
    exact Nat.mul_pos (by positivity)
      (by have := one_lt_pow₀ (by norm_num : (1 : ℕ) < 10) hr.ne'; omega)
  have hRew :
      (structuredDenominator j r : ℝ) *
          (1 / (structuredDenominator j r : ℝ) ^ sourceMu) =
        (structuredDenominator j r : ℝ) ^ (-sourceLoss) := by
    rw [show sourceMu = t24StrongestMu from rfl,
      show sourceLoss = t24StrongestLoss from rfl]
    exact t24Strongest_scaled_rationalBound_eq_loss hdenNat
  rw [hRew]
  have hden_le_10jr : (structuredDenominator j r : ℝ) ≤
      (10 : ℝ) ^ (j + r : ℕ) := by
    exact_mod_cast (show structuredDenominator j r ≤ 10 ^ (j + r) by
      unfold structuredDenominator
      rw [pow_add]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hloss_nonneg : (0 : ℝ) ≤ sourceLoss := by
    show (0 : ℝ) ≤ 763 / 125
    positivity
  have hstep_a : (structuredDenominator j r : ℝ) ^ sourceLoss ≤
      (10 : ℝ) ^ ((j + r : ℕ) * sourceLoss) := by
    have hdenReal : (0 : ℝ) < structuredDenominator j r := by
      exact_mod_cast hdenNat
    calc
      (structuredDenominator j r : ℝ) ^ sourceLoss ≤
          ((10 : ℝ) ^ (j + r : ℕ)) ^ sourceLoss :=
        Real.rpow_le_rpow hdenReal.le hden_le_10jr hloss_nonneg
      _ = (10 : ℝ) ^ ((j + r : ℕ) * sourceLoss) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hstep_b : ((j + r : ℕ) : ℝ) * sourceLoss ≤ (n : ℝ) := by
    show ((j + r : ℕ) : ℝ) * (763 / 125) ≤ (n : ℝ)
    have hjr_cast : ((j + r : ℕ) : ℝ) ≤ (startCutoff n : ℝ) := by
      exact_mod_cast hdiag
    have hsc : (startCutoff n : ℝ) ≤ (125 / 763 : ℝ) * n :=
      startCutoff_cast_le n
    nlinarith
  have hstep_c : (10 : ℝ) ^ ((j + r : ℕ) * sourceLoss) ≤
      (10 : ℝ) ^ (n : ℕ) := by
    have h10 : (1 : ℝ) ≤ 10 := by norm_num
    have h10n : (10 : ℝ) ^ (n : ℕ) = (10 : ℝ) ^ (n : ℝ) :=
      (Real.rpow_natCast 10 n).symm
    rw [h10n]
    exact Real.rpow_le_rpow_of_exponent_le h10 hstep_b
  have hden_loss_le_10n :
      (structuredDenominator j r : ℝ) ^ sourceLoss ≤
        (10 : ℝ) ^ (n : ℕ) := by
    linarith [hstep_a, hstep_c]
  have h10n_pos : (0 : ℝ) < (10 : ℝ) ^ (n : ℕ) := by positivity
  have hden_loss_pos :
      (0 : ℝ) < (structuredDenominator j r : ℝ) ^ sourceLoss := by
    positivity
  rw [Real.rpow_neg
    (by positivity : (0 : ℝ) ≤ structuredDenominator j r)]
  exact (inv_le_inv₀ h10n_pos hden_loss_pos).2 hden_loss_le_10n

/-- Thus every residual diagonal label is below the source onset. -/
theorem diagonal_residual_denominator_lt
    {Q0 n r j : ℕ} (hp : (r, j) ∈ diagonalResidualRectangle Q0 n) :
    structuredDenominator j r < Q0 := by
  rw [diagonalResidualRectangle, Finset.mem_filter] at hp
  have hrange := mem_residualShortRectangle_iff.mp hp.1
  by_contra hnot
  exact hrange.2.2.2
    (arithmeticExcluded_of_sum_le_startCutoff hrange.1
      (le_of_not_gt hnot) hp.2)

/-- Positive-lag structured denominators inject the diagonal labels into
`range Q0`; hence the diagonal residual has at most `Q0-1` labels. -/
theorem diagonalResidualRectangle_card_le (Q0 n : ℕ) :
    (diagonalResidualRectangle Q0 n).card ≤ Q0 - 1 := by
  classical
  let f : ℕ × ℕ → ℕ := fun p => structuredDenominator p.2 p.1
  let target := Finset.Ico 1 Q0
  have hmaps : ∀ p ∈ diagonalResidualRectangle Q0 n, f p ∈ target := by
    intro p hp
    have hpbase := (Finset.mem_filter.mp hp).1
    have hrange := mem_residualShortRectangle_iff.mp hpbase
    have hpos : 0 < structuredDenominator p.2 p.1 := by
      unfold structuredDenominator
      have hpow : 1 < 10 ^ p.1 :=
        Nat.one_lt_pow (Nat.ne_of_gt hrange.1) (by norm_num)
      exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
    exact Finset.mem_Ico.mpr ⟨hpos, diagonal_residual_denominator_lt hp⟩
  have hinj : Set.InjOn f (diagonalResidualRectangle Q0 n) := by
    intro p hp p' hp' heq
    have hpbase := (Finset.mem_filter.mp hp).1
    have hpbase' := (Finset.mem_filter.mp hp').1
    have hr := (mem_residualShortRectangle_iff.mp hpbase).1
    have hr' := (mem_residualShortRectangle_iff.mp hpbase').1
    have hphi : T58TriangularFejerAudit.phi 1 p.2 p.1 =
        T58TriangularFejerAudit.phi 1 p'.2 p'.1 := by
      simpa [f, T58TriangularFejerAudit.phi_eq_frequency_mul_structuredDenominator]
        using heq
    obtain ⟨hj, hrEq⟩ := T58TriangularFejerAudit.phi_fixed_h_injective
      (h := 1) (j₁ := p.2) (r₁ := p.1) (j₂ := p'.2) (r₂ := p'.1)
      (by norm_num) hr hr' hphi
    exact Prod.ext hrEq hj
  calc
    (diagonalResidualRectangle Q0 n).card ≤ target.card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = Q0 - 1 := by simp [target]

theorem diagonalTupleDomain_eq_product (Q0 n : ℕ) :
    diagonalTupleDomain Q0 n =
      T58TriangularFejerAudit.positiveFejerFrequencies n ×ˢ
        diagonalResidualRectangle Q0 n := by
  ext a
  simp only [diagonalTupleDomain, diagonalResidualRectangle,
    residualTupleDomain, Finset.mem_filter, Finset.mem_product]
  tauto

/-- Strongest direct diagonal-sector estimate from this decomposition.  The
first bound retains the exact residual cardinality and literal signed-weight
mass; the second uses the sharp available mass constant `4/3`; the third uses
only the source onset.  All retain T61's outer factor two and normalization. -/
theorem normalized_diagonalTupleCosineSum_lt
    (Q0 n : ℕ) (hSource : SourceEffectiveIrrationality Q0)
    (hn : 1 ≤ n) (x : ℝ) :
    (|restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x /
          (sampleLength n : ℝ)| ≤
        (2 * (diagonalResidualRectangle Q0 n).card *
          ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
            |vaalerCoefficient (shortBandwidth n) h|) /
          (sampleLength n : ℝ)) ∧
      (|restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x /
          (sampleLength n : ℝ)| ≤
        (8 / 3 : ℝ) * (diagonalResidualRectangle Q0 n).card /
          (sampleLength n : ℝ)) ∧
      |restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x /
          (sampleLength n : ℝ)| <
        (8 / 3 : ℝ) * (Q0 - 1 : ℕ) / (sampleLength n : ℝ) := by
  classical
  let P := diagonalResidualRectangle Q0 n
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
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      _ = (P.card : ℝ) * |vaalerCoefficient H h| := by simp
  have htotal :
      |restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x| ≤
        2 * (P.card : ℝ) *
          ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := by
    rw [restrictedTupleCosineSum, diagonalTupleDomain_eq_product,
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
  have hcard : (P.card : ℝ) ≤ (Q0 - 1 : ℕ) := by
    exact_mod_cast diagonalResidualRectangle_card_le Q0 n
  have hQ0 : 2 ≤ Q0 := hSource.1
  have hQpos : (0 : ℝ) < (Q0 - 1 : ℕ) := by
    exact_mod_cast (show 0 < Q0 - 1 by omega)
  have hexactRaw :
      |restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x| ≤
        2 * (P.card : ℝ) *
          ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := htotal
  have hcardRaw :
      |restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x| ≤
        (8 / 3 : ℝ) * (P.card : ℝ) := by
    calc
      |restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x| ≤
          2 * (P.card : ℝ) *
            ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := htotal
      _ ≤ 2 * (P.card : ℝ) * (4 / 3 : ℝ) := by
        gcongr
      _ = (8 / 3 : ℝ) * (P.card : ℝ) := by ring
  have hbound :
      |restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x| <
        (8 / 3 : ℝ) * (Q0 - 1 : ℕ) := by
    calc
      |restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) x| ≤
          2 * (P.card : ℝ) *
            ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := htotal
      _ ≤ 2 * (Q0 - 1 : ℕ) *
          ∑ h ∈ Finset.Ico 1 H, |vaalerCoefficient H h| := by
        gcongr
      _ < 2 * (Q0 - 1 : ℕ) * (4 / 3 : ℝ) := by
        gcongr
      _ = (8 / 3 : ℝ) * (Q0 - 1 : ℕ) := by ring
  rw [abs_div, abs_of_pos hL]
  refine ⟨?_, ?_, ?_⟩
  · simpa [P, H, L] using
      (div_le_div_iff_of_pos_right hL).2 hexactRaw
  · simpa [P, L] using
      (div_le_div_iff_of_pos_right hL).2 hcardRaw
  · exact (div_lt_div_iff_of_pos_right hL).2 hbound

/-- The complementary coefficient, grouped by the exact positive integer
frequency `q = h * 10^j * (10^r-1)` and normalized by `2/L_n`. -/
abbrev diagonalComplementGroupedCoefficient (Q0 n q : ℕ) : ℝ :=
  restrictedGroupedCoefficient n (diagonalComplementTupleDomain Q0 n) q

/-- Every complementary tuple has T61/T86's exact structured frequency. -/
theorem diagonalComplement_tupleFrequency_eq (h r j : ℕ) :
    tupleFrequency (h, (r, j)) = h * 10 ^ j * (10 ^ r - 1) := by
  exact tupleFrequency_eq h r j

/-- Ordered covariance over distinct complementary frequencies. -/
def normalizedDiagonalComplementDistinctCovariance (Q0 n : ℕ) : ℝ :=
  ∑ q ∈ restrictedFrequencySupport (diagonalComplementTupleDomain Q0 n),
    ∑ q' ∈
        (restrictedFrequencySupport (diagonalComplementTupleDomain Q0 n)).erase q,
      diagonalComplementGroupedCoefficient Q0 n q *
        diagonalComplementGroupedCoefficient Q0 n q' *
        Real.cos (2 * Real.pi * (q : ℝ) * Real.pi) *
        Real.cos (2 * Real.pi * (q' : ℝ) * Real.pi)

theorem diagonalComplement_frequency_and_weight (Q0 n q : ℕ) :
    diagonalComplementGroupedCoefficient Q0 n q =
      (2 : ℝ) / (sampleLength n : ℝ) *
        ∑ a ∈ restrictedFrequencyFiber
            (diagonalComplementTupleDomain Q0 n) q,
          ((shortBandwidth n : ℝ)⁻¹ *
            (Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ)) /
                Real.pi +
              2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
                Real.cos (Real.pi * (a.1 : ℝ) /
                  (shortBandwidth n : ℝ)))) := by
  unfold diagonalComplementGroupedCoefficient restrictedGroupedCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact tupleWeight_explicit n a

theorem normalized_diagonalComplement_square_eq_equal_add_distinct
    (Q0 n : ℕ) :
    (restrictedTupleCosineSum n (diagonalComplementTupleDomain Q0 n) Real.pi /
        (sampleLength n : ℝ)) ^ 2 =
      (∑ q ∈ restrictedFrequencySupport
          (diagonalComplementTupleDomain Q0 n),
        (diagonalComplementGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) +
        normalizedDiagonalComplementDistinctCovariance Q0 n := by
  rw [restricted_normalized_frequency_grouping]
  calc
    (∑ q ∈ restrictedFrequencySupport (diagonalComplementTupleDomain Q0 n),
        diagonalComplementGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2 =
        (∑ q ∈ restrictedFrequencySupport (diagonalComplementTupleDomain Q0 n),
          (diagonalComplementGroupedCoefficient Q0 n q *
            Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) +
          ∑ q ∈ restrictedFrequencySupport (diagonalComplementTupleDomain Q0 n),
            ∑ q' ∈ (restrictedFrequencySupport
                (diagonalComplementTupleDomain Q0 n)).erase q,
              (diagonalComplementGroupedCoefficient Q0 n q *
                Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) *
              (diagonalComplementGroupedCoefficient Q0 n q' *
                Real.cos (2 * Real.pi * (q' : ℝ) * Real.pi)) :=
      sq_sum_eq_diagonal_add_ordered_distinct _ _
    _ = _ := by
      congr 1
      unfold normalizedDiagonalComplementDistinctCovariance
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro q' hq'
      ring

/-- T86's equal-frequency estimate is stable under the diagonal deletion. -/
theorem diagonalComplement_equalFrequencyTerm_lt_fortyTwo
    (Q0 n : ℕ) (hn : 2 ≤ n) :
    (∑ q ∈ restrictedFrequencySupport (diagonalComplementTupleDomain Q0 n),
      (diagonalComplementGroupedCoefficient Q0 n q *
        Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) < 42 := by
  have hs : diagonalComplementTupleDomain Q0 n ⊆
      residualTupleDomain sourceMu 1 Q0 n := by
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
  have hpositive : 0 ≤ 24 * (n : ℝ) ^ 2 / 5 ^ n := by positivity
  have hsquare : (24 * (n : ℝ) ^ 2 / 5 ^ n) ^ 2 < (129 / 20 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hpositive (by positivity)).mpr hterm
  have hfortyTwo :
      restrictedOneScaleEnergy n (diagonalComplementTupleDomain Q0 n) < 42 := by
    nlinarith
  calc
    (∑ q ∈ restrictedFrequencySupport (diagonalComplementTupleDomain Q0 n),
        (diagonalComplementGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2) ≤
        restrictedOneScaleEnergy n (diagonalComplementTupleDomain Q0 n) := by
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
      have hcoeff : 0 ≤ |diagonalComplementGroupedCoefficient Q0 n q| ^ 2 :=
        sq_nonneg _
      rw [sq_abs]
      nlinarith
    _ < 42 := hfortyTwo

/-- Only an upper, not a two-sided, covariance estimate enters the square
bound used by the downstream signed inequality. -/
theorem diagonalComplement_square_lt_of_covariance_le
    (Q0 n : ℕ) (hn : 2 ≤ n) {C : ℝ}
    (hCov : normalizedDiagonalComplementDistinctCovariance Q0 n ≤ C) :
    (restrictedTupleCosineSum n (diagonalComplementTupleDomain Q0 n) Real.pi /
        (sampleLength n : ℝ)) ^ 2 < 42 + C := by
  rw [normalized_diagonalComplement_square_eq_equal_add_distinct]
  linarith [diagonalComplement_equalFrequencyTerm_lt_fortyTwo Q0 n hn]

theorem signed_sum_eq_diagonal_add_complement (Q0 n : ℕ) :
    signedStructuredDenominatorSum sourceMu 1 Q0 n =
      restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) Real.pi +
        restrictedTupleCosineSum n
          (diagonalComplementTupleDomain Q0 n) Real.pi := by
  classical
  rw [← residualTupleCosineSum_pi_eq_T61]
  unfold residualTupleCosineSum restrictedTupleCosineSum
  have hpart := (diagonal_exact_partition Q0 n).1
  have hdisj := (diagonal_exact_partition Q0 n).2
  rw [← hpart, Finset.sum_union hdisj]
  ring

/-- An eventual one-sided covariance premise on the diagonal complement. -/
def PiDiagonalComplementCovarianceUpperBound (Q0 : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
    ∀ n : ℕ, N0 ≤ n →
      normalizedDiagonalComplementDistinctCovariance Q0 n ≤ C

/-- The matching absolute covariance premise. -/
def PiDiagonalComplementCovarianceAbsoluteBound (Q0 : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
    ∀ n : ℕ, N0 ≤ n →
      |normalizedDiagonalComplementDistinctCovariance Q0 n| ≤ C

/-- The complete signed bridge uses only the one-sided covariance premise.
The displayed `C+52` retains the zero-mode bound `8`, complementary square
The constant `42`, and eventual diagonal bound `1`. -/
theorem diagonalComplement_upperBound_implies_signedPremise
    {Q0 : ℕ} (hSource : SourceEffectiveIrrationality Q0)
    (hCov : PiDiagonalComplementCovarianceUpperBound Q0) :
    SignedStructuredDenominatorPremise sourceMu 1 Q0 := by
  obtain ⟨C, hC, N0, hN0, hcov⟩ := hCov
  let N := max N0 (4 * Q0)
  refine ⟨C + 52, by positivity, N, by dsimp [N]; omega, ?_⟩
  intro n hn
  have hnCov : N0 ≤ n := (Nat.le_max_left N0 (4 * Q0)).trans hn
  have hnDiag : 4 * Q0 ≤ n := (Nat.le_max_right N0 (4 * Q0)).trans hn
  have hn2 : 2 ≤ n := hN0.trans hnCov
  have hn1 : 1 ≤ n := by omega
  let L : ℝ := sampleLength n
  let diagonal : ℝ :=
    restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) Real.pi / L
  let complement : ℝ :=
    restrictedTupleCosineSum n
      (diagonalComplementTupleDomain Q0 n) Real.pi / L
  let zero : ℝ :=
    (2 / (shortBandwidth n : ℝ) *
      residualStructuredCard sourceMu 1 Q0 n) / L
  have hL : 0 < L := by
    dsimp [L, sampleLength, t56SampleLength]
    positivity
  have hzero : zero ≤ 8 := by
    simpa [zero, L] using (normalized_zeroMode_le_eight Q0 n hn1).2
  have hdiagRaw := normalized_diagonalTupleCosineSum_lt
    Q0 n hSource hn1 Real.pi
  have hsquareNat := square_le_four_mul_sampleLength n
  have hsquare : (n : ℝ) ^ 2 ≤ 4 * L := by
    dsimp [L]
    exact_mod_cast hsquareNat
  have hQ0 : 2 ≤ Q0 := hSource.1
  have hnDiagReal : (4 : ℝ) * Q0 ≤ n := by exact_mod_cast hnDiag
  have hfourQnonneg : (0 : ℝ) ≤ 4 * Q0 := by positivity
  have hsquareLower : ((4 : ℝ) * Q0) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hfourQnonneg hnDiagReal 2
  have hnumerator : (8 / 3 : ℝ) * (Q0 - 1 : ℕ) < L := by
    have hQReal : (2 : ℝ) ≤ Q0 := by exact_mod_cast hQ0
    have hsubCast : ((Q0 - 1 : ℕ) : ℝ) = (Q0 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Q0)]
      norm_num
    rw [hsubCast]
    nlinarith [sq_nonneg ((Q0 : ℝ) - 1)]
  have hdiagonal : |diagonal| < 1 := by
    have hratio :
        (8 / 3 : ℝ) * (Q0 - 1 : ℕ) / L < 1 :=
      (div_lt_one hL).2 hnumerator
    exact hdiagRaw.2.2.trans hratio
  have hcomplementSquare : complement ^ 2 < 42 + C := by
    have hbase := diagonalComplement_square_lt_of_covariance_le
      Q0 n hn2 (hcov n hnCov)
    simpa [complement, L] using hbase
  have habsComplement_le : |complement| ≤ complement ^ 2 + 1 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|complement| - 1)]
  have hcomplement : |complement| < C + 43 := by linarith
  have hdecomposition :
      completeStructuredVaalerExpression sourceMu 1 Q0 n / L =
        zero + diagonal + complement := by
    unfold completeStructuredVaalerExpression
    rw [signed_sum_eq_diagonal_add_complement]
    dsimp [zero, diagonal, complement]
    ring
  have hnormalized :
      completeStructuredVaalerExpression sourceMu 1 Q0 n / L < C + 52 := by
    rw [hdecomposition]
    have hdiagUpper : diagonal ≤ |diagonal| := le_abs_self diagonal
    have hcompUpper : complement ≤ |complement| := le_abs_self complement
    linarith
  have hmul := (div_le_iff₀ hL).mp hnormalized.le
  simpa [L] using hmul

/-- Within the diagonal-complement domain, the equal-frequency `<42` bound
supplies the missing lower covariance bound.  Thus one-sided and absolute
eventual boundedness are equivalent after the explicit replacement constant
`max C 42`.  The comparison with T88's different domain is proved below. -/
theorem diagonalComplement_upperBound_iff_absoluteBound (Q0 : ℕ) :
    PiDiagonalComplementCovarianceUpperBound Q0 ↔
      PiDiagonalComplementCovarianceAbsoluteBound Q0 := by
  constructor
  · rintro ⟨C, hC, N0, hN0, hupper⟩
    refine ⟨max C 42, hC.trans_le (le_max_left C 42), N0, hN0, ?_⟩
    intro n hn
    let covariance := normalizedDiagonalComplementDistinctCovariance Q0 n
    have hsquare :
        0 ≤ (restrictedTupleCosineSum n
          (diagonalComplementTupleDomain Q0 n) Real.pi /
            (sampleLength n : ℝ)) ^ 2 := sq_nonneg _
    rw [normalized_diagonalComplement_square_eq_equal_add_distinct] at hsquare
    have hequal := diagonalComplement_equalFrequencyTerm_lt_fortyTwo Q0 n
      (hN0.trans hn)
    have hlower : -42 < covariance := by
      dsimp [covariance]
      linarith
    rw [abs_le]
    exact ⟨(neg_le_neg (le_max_right C 42)).trans hlower.le,
      (hupper n hn).trans (le_max_left C 42)⟩
  · rintro ⟨C, hC, N0, hN0, habs⟩
    refine ⟨C, hC, N0, hN0, ?_⟩
    intro n hn
    exact (le_abs_self _).trans (habs n hn)

/-! ## Exact comparison with T88's rectangular late sector -/

/-- The two exact partitions of the same T61 residual give this normalized
identity.  It uses T88's actual late domain and T89's actual diagonal
complement, with their literal signed weights and `Real.pi` phases. -/
theorem normalized_late_sub_diagonalComplement_eq_diagonal_sub_early
    (Q0 n : ℕ) :
    restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi /
          (sampleLength n : ℝ) -
        restrictedTupleCosineSum n
            (diagonalComplementTupleDomain Q0 n) Real.pi /
          (sampleLength n : ℝ) =
      restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) Real.pi /
          (sampleLength n : ℝ) -
        restrictedTupleCosineSum n (earlyTupleDomain Q0 n) Real.pi /
          (sampleLength n : ℝ) := by
  have hL : (sampleLength n : ℝ) ≠ 0 := by
    positivity
  have hrect := signed_sum_eq_early_add_late Q0 n
  have hdiag := signed_sum_eq_diagonal_add_complement Q0 n
  field_simp [hL]
  linarith

/-- Eventually the normalized sums on T88's late rectangle and T89's
diagonal complement differ by less than three.  The constants are exactly
T88's early bound `2` and the diagonal bound `1`. -/
theorem normalized_late_sub_diagonalComplement_abs_lt_three
    (Q0 n : ℕ) (hSource : SourceEffectiveIrrationality Q0)
    (hn2 : 2 ≤ n) (hnDiag : 4 * Q0 ≤ n) :
    |restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi /
          (sampleLength n : ℝ) -
        restrictedTupleCosineSum n
            (diagonalComplementTupleDomain Q0 n) Real.pi /
          (sampleLength n : ℝ)| < 3 := by
  let L : ℝ := sampleLength n
  let early : ℝ :=
    restrictedTupleCosineSum n (earlyTupleDomain Q0 n) Real.pi / L
  let diagonal : ℝ :=
    restrictedTupleCosineSum n (diagonalTupleDomain Q0 n) Real.pi / L
  have hL : 0 < L := by
    dsimp [L, sampleLength, t56SampleLength]
    positivity
  have hn1 : 1 ≤ n := by omega
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
    have hearly' :
        |early| < (1000 / 2289 : ℝ) * (n : ℝ) ^ 2 / L := by
      simpa [early, L] using hearlyRaw
    exact (hearly'.trans_le hratio).trans hconst
  have hdiagRaw := normalized_diagonalTupleCosineSum_lt
    Q0 n hSource hn1 Real.pi
  have hQ0 : 2 ≤ Q0 := hSource.1
  have hnDiagReal : (4 : ℝ) * Q0 ≤ n := by exact_mod_cast hnDiag
  have hfourQnonneg : (0 : ℝ) ≤ 4 * Q0 := by positivity
  have hsquareLower : ((4 : ℝ) * Q0) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hfourQnonneg hnDiagReal 2
  have hnumerator : (8 / 3 : ℝ) * (Q0 - 1 : ℕ) < L := by
    have hQReal : (2 : ℝ) ≤ Q0 := by exact_mod_cast hQ0
    have hsubCast : ((Q0 - 1 : ℕ) : ℝ) = (Q0 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Q0)]
      norm_num
    rw [hsubCast]
    nlinarith [sq_nonneg ((Q0 : ℝ) - 1)]
  have hdiagonal : |diagonal| < 1 := by
    have hratio :
        (8 / 3 : ℝ) * (Q0 - 1 : ℕ) / L < 1 :=
      (div_lt_one hL).2 hnumerator
    have hdiagonal' :
        |diagonal| < (8 / 3 : ℝ) * (Q0 - 1 : ℕ) / L := by
      simpa [diagonal, L] using hdiagRaw.2.2
    exact hdiagonal'.trans hratio
  rw [normalized_late_sub_diagonalComplement_eq_diagonal_sub_early]
  change |diagonal - early| < 3
  calc
    |diagonal - early| ≤ |diagonal| + |early| := abs_sub _ _
    _ < 1 + 2 := add_lt_add hdiagonal hearly
    _ = 3 := by norm_num

/-- T88's actual absolute late covariance premise implies the actual
one-sided diagonal-complement premise.  The explicit constant transform is
`C ↦ (C+46)^2`; no covariance estimate is asserted. -/
theorem piLateDistinctCovarianceBound_implies_diagonalComplementUpperBound
    {Q0 : ℕ} (hSource : SourceEffectiveIrrationality Q0)
    (hLate : PiLateDistinctCovarianceBound Q0) :
    PiDiagonalComplementCovarianceUpperBound Q0 := by
  obtain ⟨C, hC, N0, hN0, hcov⟩ := hLate
  let N := max N0 (4 * Q0)
  refine ⟨(C + 46) ^ 2, by positivity, N, by dsimp [N]; omega, ?_⟩
  intro n hn
  have hnLate : N0 ≤ n := (Nat.le_max_left N0 (4 * Q0)).trans hn
  have hnDiag : 4 * Q0 ≤ n := (Nat.le_max_right N0 (4 * Q0)).trans hn
  have hn2 : 2 ≤ n := hN0.trans hnLate
  let late : ℝ :=
    restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi /
      (sampleLength n : ℝ)
  let diagonalComplement : ℝ :=
    restrictedTupleCosineSum n
        (diagonalComplementTupleDomain Q0 n) Real.pi /
      (sampleLength n : ℝ)
  have hdiff : |late - diagonalComplement| < 3 := by
    simpa [late, diagonalComplement] using
      normalized_late_sub_diagonalComplement_abs_lt_three
        Q0 n hSource hn2 hnDiag
  have hlateSquare : late ^ 2 < 42 + C := by
    rw [normalized_late_square_eq_equal_add_distinct]
    have hequal := normalized_late_equalFrequencyTerm_lt_fortyTwo Q0 n hn2
    have hcovUpper := (le_abs_self
      (normalizedLateDistinctCovariance Q0 n)).trans (hcov n hnLate)
    linarith
  have hlateAbs_le : |late| ≤ late ^ 2 + 1 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|late| - 1)]
  have hlateAbs : |late| < C + 43 := by linarith
  have hcompAbs : |diagonalComplement| < C + 46 := by
    calc
      |diagonalComplement| = |late - (late - diagonalComplement)| := by ring_nf
      _ ≤ |late| + |late - diagonalComplement| := abs_sub _ _
      _ < (C + 43) + 3 := add_lt_add hlateAbs hdiff
      _ = C + 46 := by ring
  have hcompSquare : diagonalComplement ^ 2 < (C + 46) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg diagonalComplement) (by positivity)).2 hcompAbs
  have hequalNonneg :
      0 ≤ ∑ q ∈ restrictedFrequencySupport
          (diagonalComplementTupleDomain Q0 n),
        (diagonalComplementGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsplit := normalized_diagonalComplement_square_eq_equal_add_distinct Q0 n
  have hcovLe : normalizedDiagonalComplementDistinctCovariance Q0 n ≤
      diagonalComplement ^ 2 := by
    dsimp [diagonalComplement]
    linarith
  exact (hcovLe.trans_lt hcompSquare).le

/-- Conversely, the actual one-sided diagonal-complement premise implies
T88's actual absolute late covariance premise.  The explicit transform is
`C ↦ (C+46)^2+42`; the added `42` is precisely the subset-stable
equal-frequency bound. -/
theorem diagonalComplementUpperBound_implies_piLateDistinctCovarianceBound
    {Q0 : ℕ} (hSource : SourceEffectiveIrrationality Q0)
    (hDiagonal : PiDiagonalComplementCovarianceUpperBound Q0) :
    PiLateDistinctCovarianceBound Q0 := by
  obtain ⟨C, hC, N0, hN0, hcov⟩ := hDiagonal
  let N := max N0 (4 * Q0)
  refine ⟨(C + 46) ^ 2 + 42, by positivity, N, by dsimp [N]; omega, ?_⟩
  intro n hn
  have hnDiagonal : N0 ≤ n := (Nat.le_max_left N0 (4 * Q0)).trans hn
  have hnDiag : 4 * Q0 ≤ n := (Nat.le_max_right N0 (4 * Q0)).trans hn
  have hn2 : 2 ≤ n := hN0.trans hnDiagonal
  let late : ℝ :=
    restrictedTupleCosineSum n (lateTupleDomain Q0 n) Real.pi /
      (sampleLength n : ℝ)
  let diagonalComplement : ℝ :=
    restrictedTupleCosineSum n
        (diagonalComplementTupleDomain Q0 n) Real.pi /
      (sampleLength n : ℝ)
  have hdiff : |late - diagonalComplement| < 3 := by
    simpa [late, diagonalComplement] using
      normalized_late_sub_diagonalComplement_abs_lt_three
        Q0 n hSource hn2 hnDiag
  have hcompSquare : diagonalComplement ^ 2 < 42 + C := by
    simpa [diagonalComplement] using
      diagonalComplement_square_lt_of_covariance_le
        Q0 n hn2 (hcov n hnDiagonal)
  have hcompAbs_le : |diagonalComplement| ≤ diagonalComplement ^ 2 + 1 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|diagonalComplement| - 1)]
  have hcompAbs : |diagonalComplement| < C + 43 := by linarith
  have hlateAbs : |late| < C + 46 := by
    calc
      |late| = |diagonalComplement + (late - diagonalComplement)| := by ring_nf
      _ ≤ |diagonalComplement| + |late - diagonalComplement| := abs_add_le _ _
      _ < (C + 43) + 3 := add_lt_add hcompAbs hdiff
      _ = C + 46 := by ring
  have hlateSquare : late ^ 2 < (C + 46) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg late) (by positivity)).2 hlateAbs
  have hequalNonneg :
      0 ≤ ∑ q ∈ restrictedFrequencySupport (lateTupleDomain Q0 n),
        (lateGroupedCoefficient Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * Real.pi)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hequalLt := normalized_late_equalFrequencyTerm_lt_fortyTwo Q0 n hn2
  have hsplit := normalized_late_square_eq_equal_add_distinct Q0 n
  have hupper : normalizedLateDistinctCovariance Q0 n < (C + 46) ^ 2 := by
    dsimp [late] at hlateSquare
    linarith
  have hlower : -42 < normalizedLateDistinctCovariance Q0 n := by
    have hsquareNonneg : 0 ≤ late ^ 2 := sq_nonneg _
    dsimp [late] at hsquareNonneg
    linarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (C + 46)]

/-- Exact no-gain result for the proposed geometry.  Under the same explicit
source-shaped irrationality premise, T88's rectangular absolute covariance
condition and the diagonal complement's one-sided condition are equivalent
as eventual fixed-`Real.pi` premises.  The proof gives both constant maps and
does not establish either premise. -/
theorem sourceEffectiveIrrationality_covariancePremises_iff
    {Q0 : ℕ} (hSource : SourceEffectiveIrrationality Q0) :
    PiLateDistinctCovarianceBound Q0 ↔
      PiDiagonalComplementCovarianceUpperBound Q0 := by
  exact ⟨piLateDistinctCovarianceBound_implies_diagonalComplementUpperBound hSource,
    diagonalComplementUpperBound_implies_piLateDistinctCovarianceBound hSource⟩

end DecimalFactorComplexity.T89DiagonalTruncation

#print axioms DecimalFactorComplexity.T89DiagonalTruncation.mem_diagonalTupleDomain_iff
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.mem_diagonalComplementTupleDomain_iff
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonal_exact_partition
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.arithmeticExcluded_of_sum_le_startCutoff
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonal_residual_denominator_lt
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonalResidualRectangle_card_le
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.normalized_diagonalTupleCosineSum_lt
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonalComplement_tupleFrequency_eq
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonalComplement_frequency_and_weight
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.normalized_diagonalComplement_square_eq_equal_add_distinct
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonalComplement_equalFrequencyTerm_lt_fortyTwo
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonalComplement_square_lt_of_covariance_le
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.signed_sum_eq_diagonal_add_complement
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonalComplement_upperBound_implies_signedPremise
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.normalized_late_sub_diagonalComplement_eq_diagonal_sub_early
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.normalized_late_sub_diagonalComplement_abs_lt_three
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.piLateDistinctCovarianceBound_implies_diagonalComplementUpperBound
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.diagonalComplementUpperBound_implies_piLateDistinctCovarianceBound
#print axioms DecimalFactorComplexity.T89DiagonalTruncation.sourceEffectiveIrrationality_covariancePremises_iff
