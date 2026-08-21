import TheoryLib.PiQuantitativeBlockHitting.T23T23MorseHedlundFrequencyDefect

/-!
# T26: many-frequency first-occurrence Fourier defect

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

T23 finds one frequency detecting the pair energy of a support occupying
distinct decimal cells.  This file retains T23's aggregate energy estimate and
uses the exact pointwise bound `E_h ≤ P^2` to show that at least `q/16` of the
frequencies `1,...,q` detect a quarter-scale energy when `P ≥ 4`.

For pi, the selected support consists of one first occurrence of every
distinct length-`m` factor and the ambient prefix is T23's explicit sum
cutoff.  The cutoff and the multiplicities of intervening orbit visits remain
uncontrolled.  Thus the result does not imply T19's uniform normalized
cancellation hypothesis, decimal disjunctivity, or V1.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.ManyFrequencyFirstOccurrenceDefect

open Theory.PiDigits.DigitChangeFourierDefect
open Theory.PiDigits.MorseHedlundFrequencyDefect
open Theory.PiDigits.FactorComplexity

/-- The aggregate version of T23's selected-support averaging estimate. -/
theorem sum_selectedPairEnergy_ge {P q : ℕ} (hq : 4 ≤ q)
    (code : Fin P → Fin q) (hcode : Function.Injective code)
    (x : Fin P → ℝ)
    (hcell : ∀ i, x i ∈ Set.Ico
      (((code i).val : ℝ) / q) ((((code i).val + 1 : ℕ) : ℝ) / q)) :
    (q : ℝ) * ((P : ℝ) * (P - 3 : ℕ) / 2) ≤
      ∑ r : Fin q,
        selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
  classical
  let E : Fin P → Fin P → Fin q → ℝ := fun i j r ↦
    1 - Real.cos
      (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))
  have hsumI :
      (∑ i : Fin P, (q : ℝ) / 2 * (P - 3 : ℕ)) ≤
        ∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r := by
    apply Finset.sum_le_sum
    intro i _hi
    simpa only [E] using
      sum_neighbor_frequencyEnergy_ge hq code hcode x hcell i
  have hreorder :
      (∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r) =
        ∑ r : Fin q,
          selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
    calc
      (∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r) =
          ∑ i : Fin P, ∑ r : Fin q, ∑ j : Fin P, E i j r := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact Finset.sum_comm
      _ = ∑ r : Fin q, ∑ i : Fin P, ∑ j : Fin P, E i j r :=
        Finset.sum_comm
      _ = ∑ r : Fin q,
          selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
            apply Finset.sum_congr rfl
            intro r _hr
            rw [selectedPairEnergy, ← Finset.univ_product_univ,
              Finset.sum_product]
            rfl
  rw [← hreorder]
  calc
    (q : ℝ) * ((P : ℝ) * (P - 3 : ℕ) / 2) =
        ∑ i : Fin P, (q : ℝ) / 2 * (P - 3 : ℕ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
    _ ≤ ∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r := hsumI

/-- An ordered-pair cosine energy is nonnegative term by term. -/
lemma selectedPairEnergy_nonneg {P : ℕ} (x : Fin P → ℝ) (h : ℤ) :
    0 ≤ selectedPairEnergy x h := by
  unfold selectedPairEnergy
  exact Finset.sum_nonneg fun ij _hij ↦ one_sub_cos_nonneg _

/-- The exact all-pairs identity improves the naive termwise bound `2P²` to
the sharp bound `P²`. -/
lemma selectedPairEnergy_le_sq {P : ℕ} (x : Fin P → ℝ) (h : ℤ) :
    selectedPairEnergy x h ≤ (P : ℝ) ^ 2 := by
  have hid := finiteCircle_defect_eq_pairCosineEnergy x h
  change (P : ℝ) ^ 2 - ‖∑ i : Fin P, phase h (x i)‖ ^ 2 =
    selectedPairEnergy x h at hid
  rw [← hid]
  exact sub_le_self _ (sq_nonneg _)

/-- Frequencies whose selected ordered-pair energy reaches half of T23's
average lower bound. -/
def largeEnergyFrequencies {P : ℕ} (q : ℕ) (x : Fin P → ℝ) :
    Finset (Fin q) :=
  Finset.univ.filter fun r ↦
    (P : ℝ) * (P - 3 : ℕ) / 4 ≤
      selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ)

/-- At least one sixteenth of the canonical frequencies have selected pair
energy at least `P(P-3)/4`.  The integer form avoids rounding conventions. -/
theorem q_le_sixteen_mul_card_largeEnergyFrequencies {P q : ℕ}
    (hP : 4 ≤ P) (hq : 4 ≤ q)
    (code : Fin P → Fin q) (hcode : Function.Injective code)
    (x : Fin P → ℝ)
    (hcell : ∀ i, x i ∈ Set.Ico
      (((code i).val : ℝ) / q) ((((code i).val + 1 : ℕ) : ℝ) / q)) :
    q ≤ 16 * (largeEnergyFrequencies q x).card := by
  classical
  let threshold : ℝ := (P : ℝ) * (P - 3 : ℕ) / 4
  let energy : Fin q → ℝ := fun r ↦
    selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ)
  let good := (Finset.univ : Finset (Fin q)).filter fun r ↦
    threshold ≤ energy r
  let bad := (Finset.univ : Finset (Fin q)).filter fun r ↦
    ¬ threshold ≤ energy r
  have hgoodDef : good = largeEnergyFrequencies q x := by
    rfl
  have haggregate :
      (q : ℝ) * ((P : ℝ) * (P - 3 : ℕ) / 2) ≤
        ∑ r : Fin q, energy r := by
    simpa only [energy] using
      sum_selectedPairEnergy_ge hq code hcode x hcell
  have hgoodSum :
      (∑ r ∈ good, energy r) ≤ (good.card : ℝ) * (P : ℝ) ^ 2 := by
    calc
      (∑ r ∈ good, energy r) ≤ ∑ _r ∈ good, (P : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        exact selectedPairEnergy_le_sq x ((r.val + 1 : ℕ) : ℤ)
      _ = (good.card : ℝ) * (P : ℝ) ^ 2 := by simp
  have hbadSum :
      (∑ r ∈ bad, energy r) ≤ (bad.card : ℝ) * threshold := by
    calc
      (∑ r ∈ bad, energy r) ≤ ∑ _r ∈ bad, threshold := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' : ¬ threshold ≤ energy r := by
          simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hr
        exact le_of_lt (lt_of_not_ge hr')
      _ = (bad.card : ℝ) * threshold := by simp
  have hsplit :
      (∑ r ∈ good, energy r) + (∑ r ∈ bad, energy r) =
        ∑ r : Fin q, energy r := by
    simpa only [good, bad] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin q))
        (fun r ↦ threshold ≤ energy r) energy)
  have hbadCard : bad.card ≤ q := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset _ _ : bad ⊆ Finset.univ)
  have hthresholdNonneg : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hupper :
      (∑ r : Fin q, energy r) ≤
        (good.card : ℝ) * (P : ℝ) ^ 2 + (q : ℝ) * threshold := by
    rw [← hsplit]
    calc
      (∑ r ∈ good, energy r) + ∑ r ∈ bad, energy r ≤
          (good.card : ℝ) * (P : ℝ) ^ 2 +
            (bad.card : ℝ) * threshold := add_le_add hgoodSum hbadSum
      _ ≤ (good.card : ℝ) * (P : ℝ) ^ 2 +
          (q : ℝ) * threshold := by
            gcongr
  have hmain : (q : ℝ) * threshold ≤
      (good.card : ℝ) * (P : ℝ) ^ 2 := by
    dsimp [threshold] at haggregate hupper ⊢
    linarith
  have hsubcast : ((P - 3 : ℕ) : ℝ) = (P : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hPpos : (0 : ℝ) < P := by positivity
  have hcancelP :
      (q : ℝ) * ((P - 3 : ℕ) : ℝ) / 4 ≤
        (good.card : ℝ) * (P : ℝ) := by
    dsimp [threshold] at hmain
    apply (mul_le_mul_iff_of_pos_left hPpos).mp
    calc
      (P : ℝ) * ((q : ℝ) * ((P - 3 : ℕ) : ℝ) / 4) =
          (q : ℝ) * ((P : ℝ) * (P - 3 : ℕ) / 4) := by ring
      _ ≤ (good.card : ℝ) * (P : ℝ) ^ 2 := hmain
      _ = (P : ℝ) * ((good.card : ℝ) * (P : ℝ)) := by ring
  have hratio : (P : ℝ) ≤ 4 * ((P - 3 : ℕ) : ℝ) := by
    rw [hsubcast]
    have hp4 : (4 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hscaledRatio :
      (good.card : ℝ) * (P : ℝ) ≤
        (good.card : ℝ) * (4 * ((P - 3 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hratio (by positivity)
  have hqScaled :
      (q : ℝ) * ((P - 3 : ℕ) : ℝ) ≤
        (16 * good.card : ℕ) * ((P - 3 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hsubPos : (0 : ℝ) < ((P - 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < P - 3 by omega)
  have hreal : (q : ℝ) ≤ (16 * good.card : ℕ) :=
    (mul_le_mul_iff_of_pos_right hsubPos).mp hqScaled
  rw [← hgoodDef]
  exact_mod_cast hreal

/-- Frequencies whose full ambient-prefix defect reaches the selected-support
threshold determined by `P`. -/
def largeFullDefectFrequencies (P q : ℕ) {N : ℕ} (y : Fin N → ℝ) :
    Finset (Fin q) :=
  Finset.univ.filter fun r ↦
    (P : ℝ) * (P - 3 : ℕ) / 4 ≤
      (N : ℝ) ^ 2 -
        ‖∑ i : Fin N, phase ((r.val + 1 : ℕ) : ℤ) (y i)‖ ^ 2

/-- The many-frequency selected-support bound transfers monotonically to any
ambient prefix containing that support. -/
theorem q_le_sixteen_mul_card_largeFullDefectFrequencies
    {P N q : ℕ} (hP : 4 ≤ P) (hq : 4 ≤ q)
    (idx : Fin P ↪ Fin N) (y : Fin N → ℝ)
    (code : Fin P → Fin q) (hcode : Function.Injective code)
    (hcell : ∀ i, y (idx i) ∈ Set.Ico
      (((code i).val : ℝ) / q) ((((code i).val + 1 : ℕ) : ℝ) / q)) :
    q ≤ 16 * (largeFullDefectFrequencies P q y).card := by
  let x : Fin P → ℝ := fun i ↦ y (idx i)
  have hselected := q_le_sixteen_mul_card_largeEnergyFrequencies
    hP hq code hcode x hcell
  have hsubset : largeEnergyFrequencies q x ⊆
      largeFullDefectFrequencies P q y := by
    intro r hr
    have hrEnergy :
        (P : ℝ) * (P - 3 : ℕ) / 4 ≤
          selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
      simpa only [largeEnergyFrequencies, Finset.mem_filter,
        Finset.mem_univ, true_and] using hr
    have htransfer := selectedPairEnergy_le_fullDefect idx x y
      ((r.val + 1 : ℕ) : ℤ) (fun _ ↦ rfl)
    simp only [largeFullDefectFrequencies, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hrEnergy.trans htransfer
  have hcard := Finset.card_le_card hsubset
  exact hselected.trans (Nat.mul_le_mul_left 16 hcard)

/-- The inspectable set of canonical frequencies with large full-prefix
defect for the pi first-occurrence construction. -/
def piManyFirstOccurrenceDefectFrequencies (m : ℕ) : Finset (Fin (10 ^ m)) :=
  largeFullDefectFrequencies (piFactorComplexity m) (10 ^ m)
    (fun i : Fin (piFirstOccurrencePrefixLength m) ↦ piOrbit i.val)

/-- At least one sixteenth of the frequencies `1,...,10^m` meet the exact
factor-complexity defect threshold on T23's canonical first-occurrence
prefix. -/
theorem pi_q_le_sixteen_mul_card_manyFirstOccurrenceDefectFrequencies
    (m : ℕ) (hm : 3 ≤ m) :
    10 ^ m ≤ 16 * (piManyFirstOccurrenceDefectFrequencies m).card := by
  have hP : 4 ≤ piFactorComplexity m :=
    by
      have hp := pi_factorComplexity_lower_bound m (by omega)
      omega
  have hq : 4 ≤ 10 ^ m := by
    calc
      4 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa only [piManyFirstOccurrenceDefectFrequencies] using
    (q_le_sixteen_mul_card_largeFullDefectFrequencies hP hq
      (piFirstOccurrenceEmbedding m)
      (fun i : Fin (piFirstOccurrencePrefixLength m) ↦ piOrbit i.val)
      (piFirstOccurrenceCylinderCode m)
      (piFirstOccurrenceCylinderCode_injective m)
      (piFirstOccurrenceEmbedding_mem_cell m))

/-- Every retained pi frequency has the Morse--Hedlund quadratic defect
`(m+1)(m-2)/4`.  The frequency is `r.val+1`, hence lies in
`1,...,10^m`. -/
theorem pi_manyFirstOccurrenceDefectFrequencies_spec
    (m : ℕ) (hm : 3 ≤ m) :
    10 ^ m ≤ 16 * (piManyFirstOccurrenceDefectFrequencies m).card ∧
      ∀ r ∈ piManyFirstOccurrenceDefectFrequencies m,
        1 ≤ r.val + 1 ∧ r.val + 1 ≤ 10 ^ m ∧
          ((m + 1 : ℕ) : ℝ) * (m - 2 : ℕ) / 4 ≤
            (piFirstOccurrencePrefixLength m : ℝ) ^ 2 -
              ‖exponentialSum piOrbit (piFirstOccurrencePrefixLength m)
                ((r.val + 1 : ℕ) : ℤ)‖ ^ 2 := by
  refine ⟨pi_q_le_sixteen_mul_card_manyFirstOccurrenceDefectFrequencies m hm,
    ?_⟩
  intro r hr
  have hrFull :
      (piFactorComplexity m : ℝ) *
          (piFactorComplexity m - 3 : ℕ) / 4 ≤
        (piFirstOccurrencePrefixLength m : ℝ) ^ 2 -
          ‖∑ i : Fin (piFirstOccurrencePrefixLength m),
            phase ((r.val + 1 : ℕ) : ℤ) (piOrbit i.val)‖ ^ 2 := by
    have hr' : r ∈ largeFullDefectFrequencies
        (piFactorComplexity m) (10 ^ m)
        (fun i : Fin (piFirstOccurrencePrefixLength m) ↦ piOrbit i.val) := by
      simpa only [piManyFirstOccurrenceDefectFrequencies] using hr
    simpa only [largeFullDefectFrequencies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hr'
  have hp : m + 1 ≤ piFactorComplexity m :=
    pi_factorComplexity_lower_bound m (by omega)
  have hsub : m - 2 ≤ piFactorComplexity m - 3 := by omega
  have hpR : ((m + 1 : ℕ) : ℝ) ≤ piFactorComplexity m := by
    exact_mod_cast hp
  have hsubR : ((m - 2 : ℕ) : ℝ) ≤
      (piFactorComplexity m - 3 : ℕ) := by
    exact_mod_cast hsub
  have hmul : ((m + 1 : ℕ) : ℝ) * (m - 2 : ℕ) ≤
      (piFactorComplexity m : ℝ) *
        (piFactorComplexity m - 3 : ℕ) := by
    exact mul_le_mul hpR hsubR (by positivity) (by positivity)
  have hdefect : ((m + 1 : ℕ) : ℝ) * (m - 2 : ℕ) / 4 ≤
      (piFirstOccurrencePrefixLength m : ℝ) ^ 2 -
        ‖∑ i : Fin (piFirstOccurrencePrefixLength m),
          phase ((r.val + 1 : ℕ) : ℤ) (piOrbit i.val)‖ ^ 2 :=
    (div_le_div_of_nonneg_right hmul (by norm_num)).trans hrFull
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ phase ((r.val + 1 : ℕ) : ℤ) (piOrbit i))
    (piFirstOccurrencePrefixLength m)] at hdefect
  refine ⟨by omega, by omega, ?_⟩
  simpa only [exponentialSum] using hdefect

end Theory.PiDigits.ManyFrequencyFirstOccurrenceDefect
