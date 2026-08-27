import TheoryLib.PiLongLagBlockCollisionDecay.T2T2UniformLongLagResidual
import TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction

/-!
# T12: deterministic scale-matched spectral frontier

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

Every spectral and excursion assertion below is an explicit hypothesis. In
particular, this file proves neither an almost-everywhere statement nor a
spectral estimate for `Real.pi`.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T12

open DecimalFactorComplexity
open Theory.PiDigits.LongLagBlockCollisionDecay
open Theory.PiDigits.LongLagBlockCollisionDecay.T2
open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The exact scale on the right side of C1. -/
def scaleMatchedTarget (s : ℝ) (m N : ℕ) : ℝ :=
  (N : ℝ) + (N : ℝ) ^ 2 * (10 : ℝ) ^ (-s * (m : ℝ))

/-- Direct scale-matched L1 control of the exact T8 positive frequencies.
One nonnegative `B_s` is selected before all positive `m,N`. -/
def ScaleMatchedL1Bound (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖spectralSum μ c Q0 m N h‖) ≤
          B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N

/-- Scale-dependent squared-energy control. Its right side is precisely
`A_s * 10^m * T_s(m,N)^2`, with `A_s` independent of `m,N`. -/
def ScaleMatchedSquaredEnergyBound (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        positiveSpectralEnergy μ c Q0 m N ≤
          A * (decimalFrequency m : ℝ) *
            (scaleMatchedTarget s m N) ^ 2

/-- Quantifier audit for the direct L1 premise. -/
theorem scaleMatchedL1Bound_iff_quantifiers (μ c : ℝ) (Q0 : ℕ) :
    ScaleMatchedL1Bound μ c Q0 ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
                ‖spectralSum μ c Q0 m N h‖) ≤
              B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
  rfl

/-- Quantifier audit for the scale-dependent energy premise. -/
theorem scaleMatchedSquaredEnergyBound_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    ScaleMatchedSquaredEnergyBound μ c Q0 ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ A : ℝ, 0 ≤ A ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            positiveSpectralEnergy μ c Q0 m N ≤
              A * (decimalFrequency m : ℝ) *
                (scaleMatchedTarget s m N) ^ 2 := by
  rfl

/-- Cauchy-Schwarz at one scale, retaining the sharp displayed multiplier
`sqrt A` in front of `10^m * T_s(m,N)`. -/
theorem positiveFrequencyNormSum_le_scaleMatched_of_energy
    (μ c : ℝ) (Q0 m N : ℕ) (s A : ℝ)
    (hN : 1 ≤ N) (hA : 0 ≤ A)
    (henergy : positiveSpectralEnergy μ c Q0 m N ≤
      A * (decimalFrequency m : ℝ) *
        (scaleMatchedTarget s m N) ^ 2) :
    (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
        ‖spectralSum μ c Q0 m N h‖) ≤
      Real.sqrt A * (decimalFrequency m : ℝ) *
        scaleMatchedTarget s m N := by
  let L := ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ‖spectralSum μ c Q0 m N h‖
  have hfreqPosNat : 0 < decimalFrequency m := by
    unfold decimalFrequency
    positivity
  have hfreqPos : (0 : ℝ) < decimalFrequency m := by
    exact_mod_cast hfreqPosNat
  have htargetPos : 0 < scaleMatchedTarget s m N := by
    unfold scaleMatchedTarget
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hcard : ((Finset.Icc 1 (decimalFrequency m)).card : ℝ) =
      (decimalFrequency m : ℝ) := by
    norm_cast
    simp
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.Icc 1 (decimalFrequency m))
    (f := fun h => ‖spectralSum μ c Q0 m N h‖)
  have hsq : L ^ 2 ≤
      (decimalFrequency m : ℝ) * positiveSpectralEnergy μ c Q0 m N := by
    simpa only [L, hcard, positiveSpectralEnergy] using hCS
  have hsqEnergy : L ^ 2 ≤
      A * (decimalFrequency m : ℝ) ^ 2 *
        (scaleMatchedTarget s m N) ^ 2 := by
    calc
      L ^ 2 ≤ (decimalFrequency m : ℝ) *
          positiveSpectralEnergy μ c Q0 m N := hsq
      _ ≤ (decimalFrequency m : ℝ) *
          (A * (decimalFrequency m : ℝ) *
            (scaleMatchedTarget s m N) ^ 2) := by gcongr
      _ = A * (decimalFrequency m : ℝ) ^ 2 *
          (scaleMatchedTarget s m N) ^ 2 := by ring
  have htargetSq : L ^ 2 ≤
      (Real.sqrt A * (decimalFrequency m : ℝ) *
        scaleMatchedTarget s m N) ^ 2 := by
    calc
      L ^ 2 ≤ A * (decimalFrequency m : ℝ) ^ 2 *
          (scaleMatchedTarget s m N) ^ 2 := hsqEnergy
      _ = (Real.sqrt A) ^ 2 * (decimalFrequency m : ℝ) ^ 2 *
          (scaleMatchedTarget s m N) ^ 2 := by
        rw [Real.sq_sqrt hA]
      _ = (Real.sqrt A * (decimalFrequency m : ℝ) *
          scaleMatchedTarget s m N) ^ 2 := by ring
  have hL : 0 ≤ L := by
    unfold L
    positivity
  have hright : 0 ≤ Real.sqrt A * (decimalFrequency m : ℝ) *
      scaleMatchedTarget s m N := by positivity
  exact (sq_le_sq₀ hL hright).mp htargetSq

/-- The squared-energy premise implies the direct L1 premise, with the
displayed choice `B_s = sqrt A_s`. -/
theorem scaleMatchedSquaredEnergyBound_implies_L1
    {μ c : ℝ} {Q0 : ℕ}
    (henergy : ScaleMatchedSquaredEnergyBound μ c Q0) :
    ScaleMatchedL1Bound μ c Q0 := by
  intro s hs0 hs1
  obtain ⟨A, hA, hbound⟩ := henergy s hs0 hs1
  refine ⟨Real.sqrt A, Real.sqrt_nonneg A, ?_⟩
  intro m N hm hN
  exact positiveFrequencyNormSum_le_scaleMatched_of_energy
    μ c Q0 m N s A hN hA (hbound m N hm hN)

/-- A pointwise direct L1 estimate gives T2's residual bound with the exact
constant `pi^2 * (1 + B)`. -/
theorem longResidualPairCount_le_of_scaleMatchedL1
    (μ c : ℝ) (Q0 m N : ℕ) (s B : ℝ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hs0 : 0 < s) (hs1 : s < 1)
    (hB : 0 ≤ B)
    (hL1 : (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
        ‖spectralSum μ c Q0 m N h‖) ≤
      B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N) :
    (longResidualPairCount μ c Q0 m N : ℝ) ≤
      (Real.pi ^ 2 * (1 + B)) * scaleMatchedTarget s m N := by
  have hmajor := longResidualPairCount_le_majorant μ c Q0 m N hm
  have hcardNat := orderedLongPairDomain_card_le_two_sq μ c Q0 m N
  have hcard : ((orderedLongPairDomain μ c Q0 m N).card : ℝ) ≤
      2 * (N : ℝ) ^ 2 := by exact_mod_cast hcardNat
  have hfreqPos : (0 : ℝ) < decimalFrequency m := by
    unfold decimalFrequency
    positivity
  have hdecay : (10 : ℝ) ^ (-(m : ℝ)) =
      ((decimalFrequency m : ℝ))⁻¹ := by
    unfold decimalFrequency
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast]
    exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10) (m : ℝ)
  have hmReal : (0 : ℝ) ≤ m := by positivity
  have hexponent : -(m : ℝ) ≤ -s * (m : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1.le) hmReal]
  have hpow : (10 : ℝ) ^ (-(m : ℝ)) ≤
      (10 : ℝ) ^ (-s * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hscale : (N : ℝ) ^ 2 * ((decimalFrequency m : ℝ))⁻¹ ≤
      scaleMatchedTarget s m N := by
    unfold scaleMatchedTarget
    rw [← hdecay]
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    calc
      (N : ℝ) ^ 2 * (10 : ℝ) ^ (-(m : ℝ)) ≤
          (N : ℝ) ^ 2 * (10 : ℝ) ^ (-s * (m : ℝ)) := by gcongr
      _ ≤ (N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-s * (m : ℝ)) := by linarith
  calc
    (longResidualPairCount μ c Q0 m N : ℝ) ≤
        Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
          (orderedLongPairDomain μ c Q0 m N).card +
        Real.pi ^ 2 / (decimalFrequency m : ℝ) *
          ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖spectralSum μ c Q0 m N h‖ := hmajor
    _ ≤ Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
          (2 * (N : ℝ) ^ 2) +
        Real.pi ^ 2 / (decimalFrequency m : ℝ) *
          (B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N) := by
      gcongr
    _ = Real.pi ^ 2 * ((N : ℝ) ^ 2 *
          ((decimalFrequency m : ℝ))⁻¹) +
        Real.pi ^ 2 * B * scaleMatchedTarget s m N := by
      field_simp [ne_of_gt hfreqPos]
    _ ≤ Real.pi ^ 2 * scaleMatchedTarget s m N +
        Real.pi ^ 2 * B * scaleMatchedTarget s m N := by
      gcongr
    _ = (Real.pi ^ 2 * (1 + B)) * scaleMatchedTarget s m N := by
      ring

/-- The pointwise energy version, with the displayed constant
`pi^2 * (1 + sqrt A)`. -/
theorem longResidualPairCount_le_of_scaleMatchedEnergy
    (μ c : ℝ) (Q0 m N : ℕ) (s A : ℝ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hs0 : 0 < s) (hs1 : s < 1)
    (hA : 0 ≤ A)
    (henergy : positiveSpectralEnergy μ c Q0 m N ≤
      A * (decimalFrequency m : ℝ) *
        (scaleMatchedTarget s m N) ^ 2) :
    (longResidualPairCount μ c Q0 m N : ℝ) ≤
      (Real.pi ^ 2 * (1 + Real.sqrt A)) *
        scaleMatchedTarget s m N := by
  apply longResidualPairCount_le_of_scaleMatchedL1
    μ c Q0 m N s (Real.sqrt A) hm hN hs0 hs1 (Real.sqrt_nonneg A)
  exact positiveFrequencyNormSum_le_scaleMatched_of_energy
    μ c Q0 m N s A hN hA henergy

/-- Fully quantified residual conclusion of the L1 premise. The theorem type
shows one `B_s` before all positive `m,N` and its resulting constant. -/
theorem scaleMatchedL1Bound_implies_residual_with_constants
    {μ c : ℝ} {Q0 : ℕ} (hL1 : ScaleMatchedL1Bound μ c Q0) :
    ∀ s : ℝ, 0 < s → s < 1 →
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          (longResidualPairCount μ c Q0 m N : ℝ) ≤
            (Real.pi ^ 2 * (1 + B)) * scaleMatchedTarget s m N := by
  intro s hs0 hs1
  obtain ⟨B, hB, hbound⟩ := hL1 s hs0 hs1
  refine ⟨B, hB, ?_⟩
  intro m N hm hN
  exact longResidualPairCount_le_of_scaleMatchedL1
    μ c Q0 m N s B hm hN hs0 hs1 hB (hbound m N hm hN)

/-- Fully quantified canonical collision conclusion with the same displayed
constant. Effective irrationality is a separate premise, as required by T2. -/
theorem scaleMatchedL1Bound_implies_C1_with_constants
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hL1 : ScaleMatchedL1Bound μ c Q0) :
    ∀ s : ℝ, 0 < s → s < 1 →
      ∃ B : ℝ, 0 ≤ B ∧ 1 ≤ Real.pi ^ 2 * (1 + B) ∧
        ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          (R_pi m N : ℝ) ≤
            (Real.pi ^ 2 * (1 + B)) * scaleMatchedTarget s m N := by
  intro s hs0 hs1
  obtain ⟨B, hB, hbound⟩ := hL1 s hs0 hs1
  have hpi : 1 ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hC : 1 ≤ Real.pi ^ 2 * (1 + B) := by
    nlinarith [mul_le_mul hpi (show 1 ≤ 1 + B by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg Real.pi)]
  refine ⟨B, hB, hC, ?_⟩
  intro m N hm hN
  have hcompare : (R_pi m N : ℝ) ≤
      (longResidualPairCount μ c Q0 m N : ℝ) := by
    exact_mod_cast R_pi_le_longResidualPairCount hm hIrr
  exact hcompare.trans (longResidualPairCount_le_of_scaleMatchedL1
    μ c Q0 m N s B hm hN hs0 hs1 hB (hbound m N hm hN))

/-- The direct L1 premise and the separate arithmetic premise imply exactly
T2's residual predicate. The witness is `pi^2 * (1 + B_s)`. -/
theorem scaleMatchedL1Bound_implies_T2
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hL1 : ScaleMatchedL1Bound μ c Q0) :
    PiUniformLongLagResidualPairDecay μ c Q0 := by
  refine ⟨hIrr, ?_⟩
  intro s hs0 hs1
  obtain ⟨B, hB, hbound⟩ := hL1 s hs0 hs1
  refine ⟨Real.pi ^ 2 * (1 + B), ?_, ?_⟩
  · have hpi : 1 ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul hpi (show 1 ≤ 1 + B by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg Real.pi)]
  · intro m N hm hN
    simpa only [scaleMatchedTarget] using
      longResidualPairCount_le_of_scaleMatchedL1
        μ c Q0 m N s B hm hN hs0 hs1 hB (hbound m N hm hN)

/-- Conditional C1 transfer from the new L1 premise. No L1 estimate for pi is
asserted by this theorem. -/
theorem scaleMatchedL1Bound_implies_C1
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hL1 : ScaleMatchedL1Bound μ c Q0) :
    PiLongLagBlockCollisionDecay := by
  exact piUniformLongLagResidualPairDecay_implies_C1
    (scaleMatchedL1Bound_implies_T2 hIrr hL1)

/-- At scale `m=1`, the arithmetic exclusion is impossible for `(mu,c)=(8,1)`.
This fact is independent of the denominator onset `Q0`. -/
theorem not_arithmeticExcluded_eight_one_at_one
    (Q0 n r : ℕ) (hr : 1 ≤ r) :
    ¬ ArithmeticExcluded 8 1 Q0 1 n r := by
  intro hExcluded
  rcases hExcluded with ⟨_, hIneq⟩
  have h10r : 10 ≤ 10 ^ r := by
    simpa using pow_le_pow_right' (a := (10 : ℕ)) (by norm_num) hr
  have h10n : 1 ≤ 10 ^ n := one_le_pow₀ (by norm_num)
  have hsub : 9 ≤ 10 ^ r - 1 := by omega
  have hdNat : 9 ≤ structuredDenominator n r := by
    unfold structuredDenominator
    calc
      9 = 1 * 9 := by norm_num
      _ ≤ 10 ^ n * (10 ^ r - 1) := Nat.mul_le_mul h10n hsub
  have hd : (9 : ℝ) ≤ structuredDenominator n r := by
    exact_mod_cast hdNat
  have hdPos : (0 : ℝ) < structuredDenominator n r := lt_of_lt_of_le (by norm_num) hd
  have hrewrite : (structuredDenominator n r : ℝ) *
      (1 / (structuredDenominator n r : ℝ) ^ (8 : ℝ)) =
        1 / (structuredDenominator n r : ℝ) ^ 7 := by
    have h8 : (8 : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
    rw [h8, Real.rpow_natCast]
    field_simp [ne_of_gt hdPos]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, pow_one] at hIneq
  rw [hrewrite] at hIneq
  have hsmall := (le_div_iff₀ (pow_pos hdPos 7)).mp hIneq
  have hlarge : (4782969 : ℝ) ≤
      (structuredDenominator n r : ℝ) ^ 7 := by
    calc
      (4782969 : ℝ) = 9 ^ 7 := by norm_num
      _ ≤ (structuredDenominator n r : ℝ) ^ 7 :=
        pow_le_pow_left₀ (by norm_num) hd 7
  norm_num at hsmall
  linarith

/-- All ordered unequal pairs of indices below `N`. -/
def fullOrderedPairDomain (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun p => p.1 ≠ p.2

/-- Exact `m=1` specialization of T8's domain at `(mu,c)=(8,1)`.
The two T8 coordinates range over every ordered unequal pair below `N`. -/
theorem mem_orderedLongPairDomain_eight_one_one_iff
    (Q0 N : ℕ) (q : OrderedLongPair) :
    q ∈ orderedLongPairDomain 8 1 Q0 1 N ↔
      orderedFirst q < N ∧ orderedSecond q < N ∧
        orderedFirst q ≠ orderedSecond q := by
  constructor
  · intro hq
    have hcoords := ordered_coordinates_lt hq
    have hcore := (mem_orderedLongPairDomain_iff.mp hq).1
    refine ⟨hcoords.1, hcoords.2, ?_⟩
    rcases q with ⟨b, ⟨r, n⟩⟩
    cases b <;> simp only [orderedFirst, orderedSecond, Bool.false_eq_true,
      ↓reduceIte] at hcore ⊢ <;> omega
  · rintro ⟨hfirst, hsecond, hne⟩
    rcases q with ⟨b, ⟨r, n⟩⟩
    cases b
    · simp only [orderedFirst, orderedSecond, Bool.false_eq_true, ↓reduceIte]
        at hfirst hsecond hne ⊢
      rw [mem_orderedLongPairDomain_iff]
      change 0 < r ∧ 1 ≤ r ∧ r < N ∧ n < N - r ∧
        ¬ ArithmeticExcluded 8 1 Q0 1 n r
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      exact not_arithmeticExcluded_eight_one_at_one Q0 n r (by omega)
    · simp only [orderedFirst, orderedSecond, ↓reduceIte]
        at hfirst hsecond hne ⊢
      rw [mem_orderedLongPairDomain_iff]
      change 0 < r ∧ 1 ≤ r ∧ r < N ∧ n < N - r ∧
        ¬ ArithmeticExcluded 8 1 Q0 1 n r
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      exact not_arithmeticExcluded_eight_one_at_one Q0 n r (by omega)

/-- The coordinate representation is injective on the exact `m=1` domain. -/
theorem orderedCoordinates_injective_at_one
    {Q0 N : ℕ} {q₁ q₂ : OrderedLongPair}
    (hq₁ : q₁ ∈ orderedLongPairDomain 8 1 Q0 1 N)
    (hq₂ : q₂ ∈ orderedLongPairDomain 8 1 Q0 1 N)
    (heq : (orderedFirst q₁, orderedSecond q₁) =
      (orderedFirst q₂, orderedSecond q₂)) :
    q₁ = q₂ := by
  have hr₁ := (mem_orderedLongPairDomain_iff.mp hq₁).1
  have hr₂ := (mem_orderedLongPairDomain_iff.mp hq₂).1
  rcases q₁ with ⟨b₁, ⟨r₁, n₁⟩⟩
  rcases q₂ with ⟨b₂, ⟨r₂, n₂⟩⟩
  cases b₁ <;> cases b₂
  · simp only [orderedFirst, orderedSecond, Bool.false_eq_true, ↓reduceIte]
      at heq
    change 0 < r₁ at hr₁
    change 0 < r₂ at hr₂
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    congr <;> omega
  · simp only [orderedFirst, orderedSecond, Bool.false_eq_true, ↓reduceIte]
      at heq
    change 0 < r₁ at hr₁
    change 0 < r₂ at hr₂
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    omega
  · simp only [orderedFirst, orderedSecond, Bool.false_eq_true, ↓reduceIte]
      at heq
    change 0 < r₁ at hr₁
    change 0 < r₂ at hr₂
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    omega
  · simp only [orderedFirst, orderedSecond, ↓reduceIte] at heq
    change 0 < r₁ at hr₁
    change 0 < r₂ at hr₂
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    congr <;> omega

/-- Every ordered unequal pair below `N` has a T8 record at `m=1`. -/
theorem exists_orderedLongPair_at_one
    (Q0 N : ℕ) {p : ℕ × ℕ} (hp : p ∈ fullOrderedPairDomain N) :
    ∃ q ∈ orderedLongPairDomain 8 1 Q0 1 N,
      (orderedFirst q, orderedSecond q) = p := by
  rcases p with ⟨a, b⟩
  have hp' := Finset.mem_filter.mp hp
  have hprod := Finset.mem_product.mp hp'.1
  have ha := Finset.mem_range.mp hprod.1
  have hb := Finset.mem_range.mp hprod.2
  have hab : a ≠ b := hp'.2
  by_cases hlt : a < b
  · let q : OrderedLongPair := ⟨false, ⟨b - a, a⟩⟩
    refine ⟨q, ?_, ?_⟩
    · apply (mem_orderedLongPairDomain_eight_one_one_iff Q0 N q).mpr
      dsimp [q, orderedFirst, orderedSecond]
      omega
    · apply Prod.ext <;> dsimp [q, orderedFirst, orderedSecond] <;> omega
  · have hgt : b < a := by omega
    let q : OrderedLongPair := ⟨true, ⟨a - b, b⟩⟩
    refine ⟨q, ?_, ?_⟩
    · apply (mem_orderedLongPairDomain_eight_one_one_iff Q0 N q).mpr
      dsimp [q, orderedFirst, orderedSecond]
      omega
    · apply Prod.ext <;> dsimp [q, orderedFirst, orderedSecond] <;> omega

/-- At `m=1`, T8's spectral sum is exactly the sum over all ordered unequal
index pairs. This theorem records both the full domain and the phase. -/
theorem spectralSum_eight_one_one_eq_fullDomain
    (Q0 N h : ℕ) :
    spectralSum 8 1 Q0 1 N h =
      ∑ p ∈ fullOrderedPairDomain N,
        Theory.PiDigits.T27.phase (h : ℤ)
          (((10 : ℝ) ^ p.1 - (10 : ℝ) ^ p.2) * Real.pi) := by
  classical
  unfold spectralSum signedSpectralSum
  apply Finset.sum_bij
      (fun q _hq => (orderedFirst q, orderedSecond q))
  · intro q hq
    rw [fullOrderedPairDomain, Finset.mem_filter]
    have h := (mem_orderedLongPairDomain_eight_one_one_iff Q0 N q).mp hq
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr h.1, Finset.mem_range.mpr h.2.1⟩, h.2.2⟩
  · intro q₁ hq₁ q₂ hq₂ heq
    exact orderedCoordinates_injective_at_one hq₁ hq₂ heq
  · intro p hp
    rcases exists_orderedLongPair_at_one Q0 N hp with ⟨q, hq, heq⟩
    exact ⟨q, hq, heq⟩
  · intro q _hq
    rfl

/-- The one-frequency decimal lacunary orbit sum used in the exact spectral
identity. The orbit exponents are exactly `a=0,...,N-1`. -/
def decimalOrbitSum (N h : ℕ) : ℂ :=
  ∑ a ∈ Finset.range N,
    Theory.PiDigits.T27.phase (h : ℤ) ((10 : ℝ) ^ a * Real.pi)

/-- Multiplying one phase by the conjugate of another subtracts their real
phase arguments. -/
theorem phase_mul_conj_phase_eq_sub_real (h : ℤ) (x y : ℝ) :
    Theory.PiDigits.T27.phase h x *
        conj (Theory.PiDigits.T27.phase h y) =
      Theory.PiDigits.T27.phase h (x - y) := by
  rw [← Theory.PiDigits.T27.phase_neg]
  have hneg : Theory.PiDigits.T27.phase (-h) y =
      Theory.PiDigits.T27.phase h (-y) := by
    unfold Theory.PiDigits.T27.phase
    congr 1
    push_cast
    ring
  rw [hneg, ← Theory.PiDigits.T27.phase_add_real]
  congr 1

/-- Exact `m=1` spectral identity. The `N` diagonal terms are removed from
the squared modulus, and both off-diagonal orientations remain. -/
theorem spectralSum_eight_one_one_eq_normSq_sub
    (Q0 N h : ℕ) :
    spectralSum 8 1 Q0 1 N h =
      (Complex.normSq (decimalOrbitSum N h) : ℂ) - (N : ℂ) := by
  rw [spectralSum_eight_one_one_eq_fullDomain]
  let P := (Finset.range N).product (Finset.range N)
  let f : ℕ × ℕ → ℂ := fun p =>
    Theory.PiDigits.T27.phase (h : ℤ)
      (((10 : ℝ) ^ p.1 - (10 : ℝ) ^ p.2) * Real.pi)
  have htotal : (Complex.normSq (decimalOrbitSum N h) : ℂ) =
      ∑ p ∈ P, f p := by
    dsimp [P]
    rw [Finset.sum_product, Finset.sum_comm]
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [decimalOrbitSum, map_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_comm]
    rw [phase_mul_conj_phase_eq_sub_real]
    dsimp [f]
    congr 1
    ring
  have hdiag : (∑ p ∈ P.filter fun p => ¬ p.1 ≠ p.2, f p) = (N : ℂ) := by
    dsimp [P]
    rw [Finset.sum_filter, Finset.sum_product]
    simp only [not_not]
    have hinner : ∀ x ∈ Finset.range N,
        (∑ y ∈ Finset.range N, if x = y then f (x, y) else 0) = (1 : ℂ) := by
      intro x hx
      rw [← Finset.sum_filter]
      have hfilter : (Finset.range N).filter (fun y => x = y) = {x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩
          rfl
        · intro hy
          subst y
          exact ⟨Finset.mem_range.mp hx, rfl⟩
      rw [hfilter]
      simp [f, Theory.PiDigits.T27.phase]
    calc
      (∑ x ∈ Finset.range N,
          ∑ y ∈ Finset.range N, if x = y then f (x, y) else 0) =
          ∑ _x ∈ Finset.range N, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hinner x hx
      _ = (N : ℂ) := by simp
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun p => p.1 ≠ p.2) f
  have hoff : (∑ p ∈ fullOrderedPairDomain N, f p) =
      (Complex.normSq (decimalOrbitSum N h) : ℂ) - (N : ℂ) := by
    rw [eq_sub_iff_add_eq]
    rw [← hdiag, htotal]
    simpa only [fullOrderedPairDomain, P] using hsplit
  simpa only [f] using hoff

/-- An explicit external fixed-frequency excursion hypothesis of the strength
supplied by a lacunary LIL after the diagonal-removal identity. It is stated
only as a hypothesis for the fixed pi orbit; this file does not prove it. -/
def FixedFrequencyLILExcursion (Q0 h : ℕ) : Prop :=
  1 ≤ h ∧ h ≤ 10 ∧
    ∀ L : ℝ, 0 ≤ L →
      ∃ N : ℕ, 1 ≤ N ∧
        L * (N : ℝ) < ‖spectralSum 8 1 Q0 1 N h‖

/-- Quantifier audit for the external fixed-frequency excursion premise. -/
theorem fixedFrequencyLILExcursion_iff_quantifiers (Q0 h : ℕ) :
    FixedFrequencyLILExcursion Q0 h ↔
      1 ≤ h ∧ h ≤ 10 ∧
        ∀ L : ℝ, 0 ≤ L →
          ∃ N : ℕ, 1 ≤ N ∧
            L * (N : ℝ) < ‖spectralSum 8 1 Q0 1 N h‖ := by
  rfl

/-- An explicit fixed-frequency excursion contradicts T8's old uniform
squared-energy predicate. The excursion remains a premise, not a conclusion
about pi and not an almost-everywhere assertion. -/
theorem fixedFrequencyLILExcursion_not_uniformSpectralEnergyBound
    {Q0 h : ℕ} (hexcursion : FixedFrequencyLILExcursion Q0 h) :
    ¬ UniformSpectralEnergyBound 8 1 Q0 := by
  rintro ⟨K, hK, henergy⟩
  rcases hexcursion with ⟨hh1, hh10, hexcursion⟩
  let L : ℝ := 10 * K + 1
  have hL : 0 ≤ L := by
    dsimp [L]
    linarith
  obtain ⟨N, hN, hlarge⟩ := hexcursion L hL
  have hmem : h ∈ Finset.Icc 1 (decimalFrequency 1) := by
    simp only [Finset.mem_Icc, decimalFrequency]
    norm_num
    exact ⟨hh1, hh10⟩
  have hterm : ‖spectralSum 8 1 Q0 1 N h‖ ^ 2 ≤
      positiveSpectralEnergy 8 1 Q0 1 N := by
    unfold positiveSpectralEnergy
    exact Finset.single_le_sum
      (fun i _hi => sq_nonneg ‖spectralSum 8 1 Q0 1 N i‖) hmem
  have henergy' : positiveSpectralEnergy 8 1 Q0 1 N ≤
      K * 10 * (N : ℝ) ^ 2 := by
    simpa [decimalFrequency] using henergy 1 N (by norm_num) hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hLsq : 10 * K < L ^ 2 := by
    dsimp [L]
    nlinarith [sq_nonneg K]
  have hscaled : K * 10 * (N : ℝ) ^ 2 < (L * (N : ℝ)) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right hLsq (sq_pos_of_pos hNreal)
    nlinarith
  have hsquare : (L * (N : ℝ)) ^ 2 <
      ‖spectralSum 8 1 Q0 1 N h‖ ^ 2 := by
    exact (sq_lt_sq₀ (mul_nonneg hL hNreal.le) (norm_nonneg _)).mpr hlarge
  exact (not_lt_of_ge (hterm.trans henergy')) (hscaled.trans hsquare)

end Theory.PiDigits.LongLagBlockCollisionDecay.T12

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.scaleMatchedL1Bound_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.scaleMatchedSquaredEnergyBound_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.positiveFrequencyNormSum_le_scaleMatched_of_energy
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.scaleMatchedSquaredEnergyBound_implies_L1
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.longResidualPairCount_le_of_scaleMatchedL1
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.longResidualPairCount_le_of_scaleMatchedEnergy
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.scaleMatchedL1Bound_implies_residual_with_constants
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.scaleMatchedL1Bound_implies_C1_with_constants
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.scaleMatchedL1Bound_implies_T2
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.scaleMatchedL1Bound_implies_C1
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.not_arithmeticExcluded_eight_one_at_one
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.mem_orderedLongPairDomain_eight_one_one_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.spectralSum_eight_one_one_eq_fullDomain
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.spectralSum_eight_one_one_eq_normSq_sub
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.fixedFrequencyLILExcursion_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T12.fixedFrequencyLILExcursion_not_uniformSpectralEnergyBound
