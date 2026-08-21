import TheoryLib.PiQuantitativeBlockHitting.T26T26ManyFrequencyFirstOccurrenceDefect

/-!
# T27: many-frequency linear additive gap

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

T26 retains at least one sixteenth of the frequencies `1,...,q` whose
selected-support pair energy is at least `P(P-3)/4`.  For `P ≥ 4`, the exact
all-pairs identity bounds the norm of each such selected sum by `31P/32`.
Splitting an ambient sum into those `P` selected terms and its complement then
gives the additive gap `P/32` at every retained frequency.

For pi, both the retained frequency and the canonical first-occurrence cutoff
move with `m`.  The result is an additive saving, not normalized cancellation;
it does not provide T19's simultaneous smallness for all natural-scale
frequencies and does not imply decimal disjunctivity or V1.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.ManyFrequencyLinearGap

open Theory.PiDigits.DigitChangeFourierDefect
open Theory.PiDigits.MorseHedlundFrequencyDefect
open Theory.PiDigits.ManyFrequencyFirstOccurrenceDefect
open Theory.PiDigits.FactorComplexity

/-- Every T26-good frequency has selected-support norm at most `31P/32` once
`P ≥ 4`.  The constant is uniform in the frequency window `q`. -/
theorem norm_selectedSupport_le_thirtyOne_mul_div_thirtyTwo
    {P q : ℕ} (hP : 4 ≤ P) (x : Fin P → ℝ) {r : Fin q}
    (hr : r ∈ largeEnergyFrequencies q x) :
    ‖∑ i : Fin P, phase ((r.val + 1 : ℕ) : ℤ) (x i)‖ ≤
      31 * (P : ℝ) / 32 := by
  have henergy :
      (P : ℝ) * (P - 3 : ℕ) / 4 ≤
        selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
    simpa only [largeEnergyFrequencies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hr
  have hid := finiteCircle_defect_eq_pairCosineEnergy x
    ((r.val + 1 : ℕ) : ℤ)
  change (P : ℝ) ^ 2 -
      ‖∑ i : Fin P, phase ((r.val + 1 : ℕ) : ℤ) (x i)‖ ^ 2 =
        selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) at hid
  have hsubcast : ((P - 3 : ℕ) : ℝ) = (P : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hsubcast] at henergy
  have hPcast : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hsq :
      ‖∑ i : Fin P, phase ((r.val + 1 : ℕ) : ℤ) (x i)‖ ^ 2 ≤
        (31 * (P : ℝ) / 32) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- An ambient unit-modulus sum is bounded by the selected embedded sum plus
the exact number `N-P` of omitted terms. -/
theorem norm_ambientSum_le_selected_add_complement
    {P N : ℕ} (idx : Fin P ↪ Fin N) (y : Fin N → ℝ) (h : ℤ) :
    ‖∑ i : Fin N, phase h (y i)‖ ≤
      ‖∑ i : Fin P, phase h (y (idx i))‖ + (N - P : ℕ) := by
  classical
  let selected : Finset (Fin N) := Finset.univ.map idx
  have hselectedSubset : selected ⊆ (Finset.univ : Finset (Fin N)) :=
    Finset.subset_univ selected
  have hsplit :
      (∑ i : Fin N, phase h (y i)) =
        (∑ i ∈ selected, phase h (y i)) +
          ∑ i ∈ (Finset.univ : Finset (Fin N)) \ selected,
            phase h (y i) := by
    have hsum := Finset.sum_sdiff (f := fun i ↦ phase h (y i))
      hselectedSubset
    simpa only [add_comm] using hsum.symm
  have hselectedSum :
      (∑ i ∈ selected, phase h (y i)) =
        ∑ i : Fin P, phase h (y (idx i)) := by
    dsimp only [selected]
    rw [Finset.sum_map]
  have hcard :
      ((Finset.univ : Finset (Fin N)) \ selected).card = N - P := by
    rw [Finset.card_sdiff_of_subset hselectedSubset]
    simp only [Finset.card_univ, Fintype.card_fin, selected,
      Finset.card_map]
  have hcomplement :
      ‖∑ i ∈ (Finset.univ : Finset (Fin N)) \ selected,
          phase h (y i)‖ ≤ (N - P : ℕ) := by
    calc
      ‖∑ i ∈ (Finset.univ : Finset (Fin N)) \ selected,
          phase h (y i)‖ ≤
          ∑ i ∈ (Finset.univ : Finset (Fin N)) \ selected,
            ‖phase h (y i)‖ := norm_sum_le _ _
      _ = (((Finset.univ : Finset (Fin N)) \ selected).card : ℝ) := by
        simp only [Theory.PiDigits.T27.norm_phase, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      _ = (N - P : ℕ) := by rw [hcard]
  rw [hsplit, hselectedSum]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hcomplement)

/-- A `31P/32` selected-support norm bound leaves additive ambient gap at
least `P/32`.  No upper bound on the ambient length `N` is needed. -/
theorem selected_norm_bound_implies_ambient_additiveGap
    {P N : ℕ} (idx : Fin P ↪ Fin N) (y : Fin N → ℝ) (h : ℤ)
    (hselected :
      ‖∑ i : Fin P, phase h (y (idx i))‖ ≤ 31 * (P : ℝ) / 32) :
    (P : ℝ) / 32 ≤
      (N : ℝ) - ‖∑ i : Fin N, phase h (y i)‖ := by
  have hPN : P ≤ N := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective idx idx.injective
  have hambient := norm_ambientSum_le_selected_add_complement idx y h
  have hsubcast : ((N - P : ℕ) : ℝ) = (N : ℝ) - P := by
    rw [Nat.cast_sub hPN]
  rw [hsubcast] at hambient
  linarith

/-- Every frequency in T26's selected-energy good set has ambient additive
gap at least `P/32`. -/
theorem largeEnergyFrequency_ambient_additiveGap
    {P N q : ℕ} (hP : 4 ≤ P) (idx : Fin P ↪ Fin N)
    (y : Fin N → ℝ) {r : Fin q}
    (hr : r ∈ largeEnergyFrequencies q (fun i ↦ y (idx i))) :
    (P : ℝ) / 32 ≤
      (N : ℝ) -
        ‖∑ i : Fin N, phase ((r.val + 1 : ℕ) : ℤ) (y i)‖ := by
  apply selected_norm_bound_implies_ambient_additiveGap idx y
    ((r.val + 1 : ℕ) : ℤ)
  exact norm_selectedSupport_le_thirtyOne_mul_div_thirtyTwo hP
    (fun i ↦ y (idx i)) hr

/-- The pi first-occurrence selected-energy good set.  Unlike T26's larger
full-defect set, membership here retains the selected norm information needed
for the `P/32` complement argument. -/
def piManyFirstOccurrenceLinearGapFrequencies (m : ℕ) :
    Finset (Fin (10 ^ m)) :=
  largeEnergyFrequencies (10 ^ m)
    (fun i : Fin (piFactorComplexity m) ↦
      piOrbit (piFirstOccurrenceEmbedding m i).val)

/-- At least one sixteenth of `1,...,10^m` belong to the pi linear-gap set. -/
theorem pi_q_le_sixteen_mul_card_manyFirstOccurrenceLinearGapFrequencies
    (m : ℕ) (hm : 3 ≤ m) :
    10 ^ m ≤
      16 * (piManyFirstOccurrenceLinearGapFrequencies m).card := by
  have hP : 4 ≤ piFactorComplexity m := by
    have hp := pi_factorComplexity_lower_bound m (by omega)
    omega
  have hq : 4 ≤ 10 ^ m := by
    calc
      4 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa only [piManyFirstOccurrenceLinearGapFrequencies] using
    (q_le_sixteen_mul_card_largeEnergyFrequencies hP hq
      (piFirstOccurrenceCylinderCode m)
      (piFirstOccurrenceCylinderCode_injective m)
      (fun i : Fin (piFactorComplexity m) ↦
        piOrbit (piFirstOccurrenceEmbedding m i).val)
      (piFirstOccurrenceEmbedding_mem_cell m))

/-- **Pi specialization.** At the canonical first-occurrence prefix, every
retained frequency has additive gap at least `p_pi(m)/32`, hence at least
`(m+1)/32`.  Both the retained frequencies and the cutoff depend on `m`. -/
theorem pi_manyFirstOccurrenceLinearGapFrequencies_spec
    (m : ℕ) (hm : 3 ≤ m) :
    10 ^ m ≤
        16 * (piManyFirstOccurrenceLinearGapFrequencies m).card ∧
      ∀ r ∈ piManyFirstOccurrenceLinearGapFrequencies m,
        1 ≤ r.val + 1 ∧ r.val + 1 ≤ 10 ^ m ∧
          ((m + 1 : ℕ) : ℝ) / 32 ≤
            (piFactorComplexity m : ℝ) / 32 ∧
          (piFactorComplexity m : ℝ) / 32 ≤
            (piFirstOccurrencePrefixLength m : ℝ) -
              ‖exponentialSum piOrbit (piFirstOccurrencePrefixLength m)
                ((r.val + 1 : ℕ) : ℤ)‖ := by
  refine ⟨
    pi_q_le_sixteen_mul_card_manyFirstOccurrenceLinearGapFrequencies m hm,
    ?_⟩
  intro r hr
  have hP : 4 ≤ piFactorComplexity m := by
    have hp := pi_factorComplexity_lower_bound m (by omega)
    omega
  have hgap := largeEnergyFrequency_ambient_additiveGap hP
    (piFirstOccurrenceEmbedding m)
    (fun i : Fin (piFirstOccurrencePrefixLength m) ↦ piOrbit i.val) hr
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ phase ((r.val + 1 : ℕ) : ℤ) (piOrbit i))
    (piFirstOccurrencePrefixLength m)] at hgap
  have hp : m + 1 ≤ piFactorComplexity m :=
    pi_factorComplexity_lower_bound m (by omega)
  have hpR : ((m + 1 : ℕ) : ℝ) ≤ piFactorComplexity m := by
    exact_mod_cast hp
  refine ⟨by omega, by omega, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right hpR (by norm_num)
  · simpa only [exponentialSum] using hgap

end Theory.PiDigits.ManyFrequencyLinearGap
