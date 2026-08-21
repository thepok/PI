import TheoryLib.PiPositiveDecimalFactorEntropy.T3FiniteFourierObstruction
import TheoryLib.PiDecimalFactorComplexity.T4FinitePrefixCollisionEnergy

/-!
# T4: finite-prefix multiplicity transfer

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file transfers T3's Fourier coefficient of the uniform distribution on
distinct occupied factor cells to a finite prefix in which cells occur with
multiplicity.  Every coefficient here is a coefficient of decimal block-cell
labels.  It is not an ordinary lacunary-orbit sum.

The pi specialization assumes the literal failure of C1.  It makes no
unconditional assertion about pi or its factor entropy.
-/

noncomputable section

set_option maxHeartbeats 800000

open Finset
open scoped BigOperators ComplexConjugate

namespace DecimalFactorEntropy.FinitePrefixMultiplicityTransfer

open DecimalFactorComplexity
open DecimalFactorEntropy.FiniteFourierObstruction

/-- Number of prefix indices carrying the cell label `a`. -/
def prefixMultiplicity {q M : ℕ} (label : Fin M → ZMod q)
    (a : ZMod q) : ℕ :=
  ((Finset.univ : Finset (Fin M)).filter fun i => label i = a).card

/-- Multiplicity normalized by the explicitly supplied prefix length `M`. -/
def normalizedMultiplicity {q M : ℕ} (label : Fin M → ZMod q)
    (a : ZMod q) : ℝ :=
  (prefixMultiplicity label a : ℝ) / M

/-- Uniform mass on one cell of a nonempty finite support. -/
def uniformCellMass {q : ℕ} (S : Finset (ZMod q)) : ℝ :=
  ((S.card : ℝ))⁻¹

/-- The normalized coefficient obtained by averaging cell labels over time. -/
def normalizedPrefixCoefficient {q M : ℕ} (label : Fin M → ZMod q)
    (ψ : AddChar (ZMod q) ℂ) : ℂ :=
  ((M : ℂ))⁻¹ * ∑ i : Fin M, ψ (label i)

/-- The coefficient of the uniform probability on the distinct cells in `S`. -/
def uniformSupportCoefficient {q : ℕ} (S : Finset (ZMod q))
    (ψ : AddChar (ZMod q) ℂ) : ℂ :=
  ((S.card : ℂ))⁻¹ * ∑ a ∈ S, ψ a

/-- The `ℓ¹` distance from prefix multiplicity weights to uniform mass on `S`. -/
def multiplicityDefect {q M : ℕ} (S : Finset (ZMod q))
    (label : Fin M → ZMod q) : ℝ :=
  ∑ a ∈ S, |normalizedMultiplicity label a - uniformCellMass S|

/-- A prefix has no labels outside `S` and visits every cell in `S`. -/
def CoversExactly {q M : ℕ} (S : Finset (ZMod q))
    (label : Fin M → ZMod q) : Prop :=
  (∀ i, label i ∈ S) ∧ ∀ a ∈ S, ∃ i, label i = a

@[simp] theorem prefixMultiplicity_eq_card_filter {q M : ℕ}
    (label : Fin M → ZMod q) (a : ZMod q) :
    prefixMultiplicity label a =
      ((Finset.univ : Finset (Fin M)).filter fun i => label i = a).card := rfl

theorem sum_prefixMultiplicity_eq_prefixLength {q M : ℕ}
    (S : Finset (ZMod q)) (label : Fin M → ZMod q)
    (hmaps : ∀ i, label i ∈ S) :
    ∑ a ∈ S, prefixMultiplicity label a = M := by
  classical
  simpa [prefixMultiplicity] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin M))) (t := S) (f := label)
      (fun i _hi => hmaps i)).symm

theorem normalizedPrefixCoefficient_eq_multiplicitySum
    {q M : ℕ} (S : Finset (ZMod q)) (label : Fin M → ZMod q)
    (ψ : AddChar (ZMod q) ℂ) (hM : 0 < M)
    (hmaps : ∀ i, label i ∈ S) :
    normalizedPrefixCoefficient label ψ =
      ∑ a ∈ S, (normalizedMultiplicity label a : ℂ) * ψ a := by
  classical
  have hfiber :
      (∑ a ∈ S, ∑ i ∈ (Finset.univ : Finset (Fin M)) with label i = a,
        ψ (label i)) = ∑ i : Fin M, ψ (label i) :=
    Finset.sum_fiberwise_of_maps_to (fun i _hi => hmaps i)
      (fun i => ψ (label i))
  rw [normalizedPrefixCoefficient, ← hfiber, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hinter :
      (∑ i ∈ (Finset.univ : Finset (Fin M)) with label i = a,
          ψ (label i)) = (prefixMultiplicity label a : ℂ) * ψ a := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin M)) with label i = a,
          ψ (label i)) =
          ∑ _i ∈ (Finset.univ : Finset (Fin M)).filter
            (fun i => label i = a), ψ a := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mem_filter] at hi
              rw [hi.2]
      _ = ((Finset.univ : Finset (Fin M)).filter
            (fun i => label i = a)).card • ψ a := by
              rw [Finset.sum_const]
      _ = (prefixMultiplicity label a : ℂ) * ψ a := by
              rw [nsmul_eq_mul]
              rfl
  rw [hinter, normalizedMultiplicity]
  push_cast
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem uniformSupportCoefficient_eq_massSum
    {q : ℕ} (S : Finset (ZMod q)) (ψ : AddChar (ZMod q) ℂ)
    (hS : S.Nonempty) :
    uniformSupportCoefficient S ψ =
      ∑ a ∈ S, (uniformCellMass S : ℂ) * ψ a := by
  classical
  rw [uniformSupportCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  unfold uniformCellMass
  push_cast
  have hcard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  field_simp

/-- Exact difference between the uniform-support coefficient and its
multiplicity-weighted prefix counterpart. -/
theorem uniform_sub_prefixCoefficient_eq_weightDifferenceSum
    {q M : ℕ} (S : Finset (ZMod q)) (label : Fin M → ZMod q)
    (ψ : AddChar (ZMod q) ℂ) (hM : 0 < M) (hS : S.Nonempty)
    (hmaps : ∀ i, label i ∈ S) :
    uniformSupportCoefficient S ψ - normalizedPrefixCoefficient label ψ =
      ∑ a ∈ S,
        ((uniformCellMass S - normalizedMultiplicity label a : ℝ) : ℂ) * ψ a := by
  rw [uniformSupportCoefficient_eq_massSum S ψ hS,
    normalizedPrefixCoefficient_eq_multiplicitySum S label ψ hM hmaps,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast
  ring

/-- The uniform and multiplicity-weighted coefficients differ by at most the
`ℓ¹` multiplicity defect. -/
theorem norm_uniform_sub_prefixCoefficient_le_defect
    {q M : ℕ} [NeZero q] (S : Finset (ZMod q)) (label : Fin M → ZMod q)
    (ψ : AddChar (ZMod q) ℂ) (hM : 0 < M) (hS : S.Nonempty)
    (hmaps : ∀ i, label i ∈ S) :
    ‖uniformSupportCoefficient S ψ - normalizedPrefixCoefficient label ψ‖ ≤
      multiplicityDefect S label := by
  rw [uniform_sub_prefixCoefficient_eq_weightDifferenceSum
    S label ψ hM hS hmaps]
  calc
    ‖∑ a ∈ S,
        ((uniformCellMass S - normalizedMultiplicity label a : ℝ) : ℂ) * ψ a‖ ≤
        ∑ a ∈ S,
          ‖((uniformCellMass S - normalizedMultiplicity label a : ℝ) : ℂ) * ψ a‖ :=
      norm_sum_le _ _
    _ = multiplicityDefect S label := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [norm_mul, ψ.norm_apply, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]

/-- Quantitative multiplicity-transfer comparison. All normalization,
coverage, frequency, ambient modulus, and prefix-length hypotheses are
explicit. -/
theorem uniformSupportCoefficient_le_prefix_add_defect
    (q M : ℕ) [NeZero q] (S : Finset (ZMod q))
    (label : Fin M → ZMod q) (ψ : AddChar (ZMod q) ℂ)
    (hM : 0 < M) (hS : S.Nonempty)
    (hcover : CoversExactly S label) :
    ‖uniformSupportCoefficient S ψ‖ ≤
      ‖normalizedPrefixCoefficient label ψ‖ + multiplicityDefect S label := by
  have hdiff := norm_uniform_sub_prefixCoefficient_le_defect
    S label ψ hM hS hcover.1
  calc
    ‖uniformSupportCoefficient S ψ‖ =
        ‖(uniformSupportCoefficient S ψ - normalizedPrefixCoefficient label ψ) +
          normalizedPrefixCoefficient label ψ‖ := by ring_nf
    _ ≤ ‖uniformSupportCoefficient S ψ - normalizedPrefixCoefficient label ψ‖ +
          ‖normalizedPrefixCoefficient label ψ‖ := norm_add_le _ _
    _ ≤ multiplicityDefect S label +
          ‖normalizedPrefixCoefficient label ψ‖ :=
      add_le_add hdiff le_rfl
    _ = _ := add_comm _ _

/-- A uniform-support coefficient of size at least `δ` forces either an
unweighted normalized time coefficient of size at least `δ/2`, or an `ℓ¹`
multiplicity defect of size at least `δ/2`. -/
theorem finitePrefix_multiplicityTransfer_dichotomy
    (q M : ℕ) [NeZero q] (S : Finset (ZMod q))
    (label : Fin M → ZMod q) (ψ : AddChar (ZMod q) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hψ : ψ ≠ 0)
    (hM : 0 < M) (hS : S.Nonempty) (hcover : CoversExactly S label)
    (hlarge : δ ≤ ‖uniformSupportCoefficient S ψ‖) :
    δ / 2 ≤ ‖normalizedPrefixCoefficient label ψ‖ ∨
      δ / 2 ≤ multiplicityDefect S label := by
  have hcompare := uniformSupportCoefficient_le_prefix_add_defect
    q M S label ψ hM hS hcover
  by_cases hψzero : ψ = 0
  · exact (hψ hψzero).elim
  by_cases hδneg : δ < 0
  · exact (not_lt_of_ge hδ hδneg).elim
  by_contra h
  push Not at h
  linarith

/-- Cell label of the length-`n` factor beginning at a prefix index. -/
def prefixFactorCellLabel (x : Stream (Fin 10)) (n M : ℕ) :
    Fin M → ZMod (10 ^ n) :=
  fun i => factorCellCode x n (factorAt x n i)

theorem prefixFactorCellLabel_mem_factorCellSet
    (x : Stream (Fin 10)) (n M : ℕ) (i : Fin M) :
    prefixFactorCellLabel x n M i ∈ factorCellSet x n := by
  classical
  simp [prefixFactorCellLabel, factorCellSet]

/-- T3's distributional coefficient is exactly the uniform finite-support
coefficient used in the multiplicity transfer. -/
theorem factorCellFourier_eq_uniformSupportCoefficient
    (x : Stream (Fin 10)) (n : ℕ)
    (ψ : AddChar (ZMod (10 ^ n)) ℂ) :
    factorCellFourier x n ψ =
      uniformSupportCoefficient (factorCellSet x n) ψ := by
  classical
  let S := factorCellSet x n
  have hS : S.Nonempty := by
    rw [← Finset.card_pos, show S = factorCellSet x n from rfl,
      factorCellSet_card]
    exact DecimalFactorEntropy.canonicalFactorComplexity_pos x n
  have hcardR : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  have hcardC : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  rw [factorCellFourier, finiteFourier]
  calc
    (∑ a : ZMod (10 ^ n), (factorCellDistribution x n a : ℂ) * ψ a) =
        ∑ a ∈ S, (((S.card : ℝ)⁻¹ : ℝ) : ℂ) * ψ a := by
      calc
        _ = ∑ a ∈ S, (factorCellDistribution x n a : ℂ) * ψ a := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro a hauniv haS
          simp [factorCellDistribution, S, haS]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [factorCellDistribution, S, ha]
    _ = ((S.card : ℂ))⁻¹ * ∑ a ∈ S, ψ a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      push_cast
      field_simp
    _ = uniformSupportCoefficient S ψ := by
      rw [uniformSupportCoefficient]

/-- Decimal specialization with explicit block length `n`, prefix length `M`,
coverage, nonzero frequency, and normalization hypotheses. -/
theorem decimalFactorCell_multiplicityTransfer_dichotomy
    (x : Stream (Fin 10)) (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (ψ : AddChar (ZMod (10 ^ n)) ℂ) (hψ : ψ ≠ 0)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcoverage : ∀ a ∈ factorCellSet x n,
      ∃ i : Fin M, prefixFactorCellLabel x n M i = a)
    (hlarge : δ ≤ ‖factorCellFourier x n ψ‖) :
    δ / 2 ≤ ‖normalizedPrefixCoefficient
        (prefixFactorCellLabel x n M) ψ‖ ∨
      δ / 2 ≤ multiplicityDefect (factorCellSet x n)
        (prefixFactorCellLabel x n M) := by
  by_cases hnzero : n = 0
  · exact (hn.ne' hnzero).elim
  have hS : (factorCellSet x n).Nonempty := by
    rw [← Finset.card_pos, factorCellSet_card]
    exact DecimalFactorEntropy.canonicalFactorComplexity_pos x n
  have hcover : CoversExactly (factorCellSet x n)
      (prefixFactorCellLabel x n M) :=
    ⟨prefixFactorCellLabel_mem_factorCellSet x n M, hcoverage⟩
  apply finitePrefix_multiplicityTransfer_dichotomy
    (10 ^ n) M (factorCellSet x n) (prefixFactorCellLabel x n M)
      ψ δ hδ hψ hM hS hcover
  simpa [factorCellFourier_eq_uniformSupportCoefficient] using hlarge

/-- Conditional pi specialization. Literal failure of C1 supplies T3's
nonzero uniform-support coefficient. Every positive prefix that covers all
occupied length-`n` cells then satisfies the multiplicity-transfer dichotomy.
No premise or conclusion is an ordinary orbit-sum estimate. -/
theorem pi_failure_C1_implies_eventual_prefix_multiplicity_dichotomy
    (hfailure :
      ¬ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        (10 : ℝ) ^ (η * (n : ℝ)) ≤
          (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ) <
          (10 : ℝ) ^ (ε * (n : ℝ)) ∧
        ∃ ψ : AddChar (ZMod (10 ^ n)) ℂ, ψ ≠ 0 ∧
          (((10 ^ n : ℕ) : ℝ) /
              ((10 : ℝ) ^ (ε * (n : ℝ))) - 1) /
                (((10 ^ n : ℕ) : ℝ) - 1) ≤
              ‖factorCellFourier Theory.PiDigits.piDigit n ψ‖ ^ 2 ∧
          ∀ M : ℕ, 0 < M →
            (∀ a ∈ factorCellSet Theory.PiDigits.piDigit n,
              ∃ i : Fin M,
                prefixFactorCellLabel Theory.PiDigits.piDigit n M i = a) →
            ‖factorCellFourier Theory.PiDigits.piDigit n ψ‖ / 2 ≤
                ‖normalizedPrefixCoefficient
                  (prefixFactorCellLabel Theory.PiDigits.piDigit n M) ψ‖ ∨
              ‖factorCellFourier Theory.PiDigits.piDigit n ψ‖ / 2 ≤
                multiplicityDefect
                  (factorCellSet Theory.PiDigits.piDigit n)
                  (prefixFactorCellLabel Theory.PiDigits.piDigit n M) := by
  have ht3 := pi_failure_C1_implies_eventual_nonzero_factorCell_frequency
    hfailure
  intro ε hε
  obtain ⟨N, hN, hall⟩ := ht3 ε hε
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨hcomplexity, ψ, hψ, hfourier⟩ := hall n hn
  refine ⟨hcomplexity, ψ, hψ, hfourier, ?_⟩
  intro M hM hcoverage
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hN.trans hn)
  exact decimalFactorCell_multiplicityTransfer_dichotomy
    Theory.PiDigits.piDigit n M hnpos hM ψ hψ
      ‖factorCellFourier Theory.PiDigits.piDigit n ψ‖ (norm_nonneg _)
      hcoverage le_rfl

/-! ## Sharpness family -/

/-- The order-two character on ten cells: it is `1` on even labels and `-1`
on odd labels. -/
def decimalParityChar : AddChar (ZMod 10) ℂ :=
  (ZMod.stdAddChar (N := 10)).mulShift 5

@[simp] theorem decimalParityChar_zero : decimalParityChar 0 = 1 := by
  simp [decimalParityChar]

@[simp] theorem decimalParityChar_one : decimalParityChar 1 = -1 := by
  change ZMod.stdAddChar (5 : ZMod 10) = -1
  rw [show (5 : ZMod 10) = (5 : ℤ) by norm_num, ZMod.stdAddChar_coe]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (5 : ℤ) / (10 : ℕ) =
      (Real.pi : ℂ) * Complex.I by norm_num; ring]
  exact Complex.exp_pi_mul_I

@[simp] theorem decimalParityChar_two : decimalParityChar 2 = 1 := by
  rw [show (2 : ZMod 10) = 1 + 1 by norm_num,
    AddChar.map_add_eq_mul, decimalParityChar_one]
  norm_num

theorem decimalParityChar_ne_zero : decimalParityChar ≠ 0 := by
  intro h
  have hzero := congrFun (congrArg DFunLike.coe h) 1
  norm_num at hzero

/-- Four-segment sharpness prefix. For each `r > 0`, labels `0` and `2`
occur `r` times each and label `1` occurs `2r` times. -/
def sharpnessLabel (r : ℕ) (i : Fin (4 * r)) : ZMod 10 :=
  if i.val < r then 0 else if i.val < 2 * r then 2 else 1

def sharpnessSupport : Finset (ZMod 10) := {0, 1, 2}

theorem sharpnessLabel_mem_support (r : ℕ) (i : Fin (4 * r)) :
    sharpnessLabel r i ∈ sharpnessSupport := by
  simp only [sharpnessLabel, sharpnessSupport, Finset.mem_insert,
    Finset.mem_singleton]
  split_ifs <;> simp

theorem sharpnessLabel_covers (r : ℕ) (hr : 0 < r) :
    CoversExactly sharpnessSupport (sharpnessLabel r) := by
  refine ⟨sharpnessLabel_mem_support r, ?_⟩
  intro a ha
  simp only [sharpnessSupport, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simp [sharpnessLabel, hr]
  · refine ⟨⟨2 * r, by omega⟩, ?_⟩
    simp [sharpnessLabel, hr]
  · refine ⟨⟨r, by omega⟩, ?_⟩
    simp [sharpnessLabel, hr]

theorem sharpness_prefixMultiplicity_zero (r : ℕ) :
    prefixMultiplicity (sharpnessLabel r) 0 = r := by
  classical
  unfold prefixMultiplicity
  have hfilter :
      ((Finset.univ : Finset (Fin (4 * r))).filter
          fun i => sharpnessLabel r i = 0) =
        (Finset.univ.filter fun i : Fin (4 * r) => i.val < r) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold sharpnessLabel
    by_cases h₁ : i.val < r
    · simp [h₁]
    · by_cases h₂ : i.val < 2 * r
      · simp [h₁, h₂]
        decide
      · simp [h₁, h₂]
        decide
  rw [hfilter]
  simpa [min_eq_right (by omega : r ≤ 4 * r)] using
    (Fin.card_filter_val_lt (n := 4 * r) (m := r))

theorem sharpness_prefixMultiplicity_two (r : ℕ) :
    prefixMultiplicity (sharpnessLabel r) 2 = r := by
  classical
  unfold prefixMultiplicity
  let A := (Finset.univ : Finset (Fin (4 * r))).filter
    fun i => i.val < 2 * r
  let B := (Finset.univ : Finset (Fin (4 * r))).filter
    fun i => i.val < r
  have hfilter :
      ((Finset.univ : Finset (Fin (4 * r))).filter
          fun i => sharpnessLabel r i = 2) = A \ B := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, A, B]
    unfold sharpnessLabel
    by_cases h₁ : i.val < r
    · simp [h₁]
      decide
    · by_cases h₂ : i.val < 2 * r
      · simp [h₁, h₂]
      · simp [h₁, h₂]
        decide
  have hBA : B ⊆ A := by
    intro i hi
    simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  rw [hfilter, Finset.card_sdiff_of_subset hBA]
  have hA : A.card = 2 * r := by
    simpa [A, min_eq_right (by omega : 2 * r ≤ 4 * r)] using
      (Fin.card_filter_val_lt (n := 4 * r) (m := 2 * r))
  have hB : B.card = r := by
    simpa [B, min_eq_right (by omega : r ≤ 4 * r)] using
      (Fin.card_filter_val_lt (n := 4 * r) (m := r))
  rw [hA, hB]
  omega

theorem sharpness_prefixMultiplicity_one (r : ℕ) :
    prefixMultiplicity (sharpnessLabel r) 1 = 2 * r := by
  classical
  unfold prefixMultiplicity
  let A := (Finset.univ : Finset (Fin (4 * r))).filter
    fun i => i.val < 2 * r
  have hfilter :
      ((Finset.univ : Finset (Fin (4 * r))).filter
          fun i => sharpnessLabel r i = 1) = Finset.univ \ A := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, A]
    unfold sharpnessLabel
    by_cases h₁ : i.val < r
    · have h₂ : i.val < 2 * r := by omega
      simp [h₁, h₂]
      decide
    · by_cases h₂ : i.val < 2 * r
      · simp [h₁, h₂]
        decide
      · simp [h₁, h₂]
  have hA : A.card = 2 * r := by
    simpa [A, min_eq_right (by omega : 2 * r ≤ 4 * r)] using
      (Fin.card_filter_val_lt (n := 4 * r) (m := 2 * r))
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ A),
    Finset.card_univ, Fintype.card_fin, hA]
  omega

theorem sum_sharpnessSupport {A : Type*} [AddCommMonoid A]
    (f : ZMod 10 → A) :
    ∑ a ∈ sharpnessSupport, f a = f 0 + f 1 + f 2 := by
  classical
  have h0 : (0 : ZMod 10) ∉ ({1, 2} : Finset (ZMod 10)) := by decide
  have h1 : (1 : ZMod 10) ∉ ({2} : Finset (ZMod 10)) := by decide
  rw [sharpnessSupport, Finset.sum_insert h0, Finset.sum_insert h1,
    Finset.sum_singleton]
  simp [add_assoc]

@[simp] theorem sharpnessSupport_card : sharpnessSupport.card = 3 := by
  have h0 : (0 : ZMod 10) ∉ ({1, 2} : Finset (ZMod 10)) := by decide
  have h1 : (1 : ZMod 10) ∉ ({2} : Finset (ZMod 10)) := by decide
  rw [sharpnessSupport, Finset.card_insert_of_notMem h0,
    Finset.card_insert_of_notMem h1, Finset.card_singleton]

theorem sharpness_uniformSupportCoefficient :
    uniformSupportCoefficient sharpnessSupport decimalParityChar = (1 / 3 : ℂ) := by
  rw [uniformSupportCoefficient, sharpnessSupport_card, sum_sharpnessSupport]
  norm_num

theorem sharpness_normalizedPrefixCoefficient_zero
    (r : ℕ) (hr : 0 < r) :
    normalizedPrefixCoefficient (sharpnessLabel r) decimalParityChar = 0 := by
  rw [normalizedPrefixCoefficient_eq_multiplicitySum
    sharpnessSupport (sharpnessLabel r) decimalParityChar (by omega)
      (sharpnessLabel_mem_support r)]
  rw [sum_sharpnessSupport]
  simp only [normalizedMultiplicity, sharpness_prefixMultiplicity_zero,
    sharpness_prefixMultiplicity_one, sharpness_prefixMultiplicity_two,
    decimalParityChar_zero, decimalParityChar_one, decimalParityChar_two]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  ring

theorem sharpness_multiplicityDefect
    (r : ℕ) (hr : 0 < r) :
    multiplicityDefect sharpnessSupport (sharpnessLabel r) = 1 / 3 := by
  rw [multiplicityDefect, sum_sharpnessSupport]
  simp only [normalizedMultiplicity, uniformCellMass, sharpnessSupport_card,
    Nat.cast_ofNat, sharpness_prefixMultiplicity_zero,
    sharpness_prefixMultiplicity_one, sharpness_prefixMultiplicity_two]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hquarter : (r : ℝ) / (4 * r) = 1 / 4 := by
    field_simp
  have hhalf : (2 * (r : ℝ)) / (4 * r) = 1 / 2 := by
    field_simp
    norm_num
  push_cast
  rw [hquarter, hhalf]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Explicit scalable sharpness family at `q = 10^n` with `n = 1` and
prefix length `M = 4r`. The uniform coefficient has norm `1/3`, while the
normalized time cell-label coefficient is exactly zero. The positive defect
is therefore essential in the dichotomy. -/
theorem multiplicityDefect_alternative_sharpness_family
    (r : ℕ) (hr : 0 < r) :
    (10 : ℕ) = 10 ^ (1 : ℕ) ∧
    0 < 4 * r ∧
    decimalParityChar ≠ 0 ∧
    CoversExactly sharpnessSupport (sharpnessLabel r) ∧
    ‖uniformSupportCoefficient sharpnessSupport decimalParityChar‖ = 1 / 3 ∧
    normalizedPrefixCoefficient (sharpnessLabel r) decimalParityChar = 0 ∧
    multiplicityDefect sharpnessSupport (sharpnessLabel r) = 1 / 3 ∧
    ¬ (1 / 6 : ℝ) ≤
        ‖normalizedPrefixCoefficient (sharpnessLabel r) decimalParityChar‖ ∧
    (1 / 6 : ℝ) ≤ multiplicityDefect sharpnessSupport (sharpnessLabel r) := by
  refine ⟨by norm_num, by omega, decimalParityChar_ne_zero,
    sharpnessLabel_covers r hr, ?_, sharpness_normalizedPrefixCoefficient_zero r hr,
    sharpness_multiplicityDefect r hr, ?_, ?_⟩
  · rw [sharpness_uniformSupportCoefficient]
    norm_num
  · rw [sharpness_normalizedPrefixCoefficient_zero r hr]
    norm_num
  · rw [sharpness_multiplicityDefect r hr]
    norm_num

#print axioms finitePrefix_multiplicityTransfer_dichotomy
#print axioms decimalFactorCell_multiplicityTransfer_dichotomy
#print axioms pi_failure_C1_implies_eventual_prefix_multiplicity_dichotomy
#print axioms multiplicityDefect_alternative_sharpness_family


end DecimalFactorEntropy.FinitePrefixMultiplicityTransfer
