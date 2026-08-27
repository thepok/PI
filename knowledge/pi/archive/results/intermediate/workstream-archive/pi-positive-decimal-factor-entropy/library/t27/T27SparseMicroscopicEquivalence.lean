import TheoryLib.PiPositiveDecimalFactorEntropy.T8T8DyadicShellFejer
import TheoryLib.PiPositiveDecimalFactorEntropy.T10T10ScaleAdaptiveOrbitFourier
import TheoryLib.PiPositiveDecimalFactorEntropy.T16T16MicroscopicFullEntropy
import TheoryLib.PiPositiveDecimalFactorEntropy.T26T26SparseLongBandFejer

/-!
# T27: sparse long-band energy is equivalent to microscopic collisions

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The generic results keep sample length `L`, bandwidth `H`, and cyclic cell
count `q` independent.  All pair counts are ordered, include the diagonal,
and use strict circular cutoffs.  The final equivalence is between two
explicit unproved hypotheses about pi; neither hypothesis is asserted.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace DecimalFactorComplexity.SparseMicroscopicEquivalence

open DecimalFactorComplexity
open DecimalFactorComplexity.DyadicShellFejer
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.MicroscopicFullEntropy
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.ScaleAdaptiveOrbitFourier
open DecimalFactorComplexity.SparseLongBandFejer

/-- Short notation for the strict ordered, diagonal-inclusive pair count. -/
abbrev pairCount {L : ℕ} (x : Fin L → ℝ) (r : ℝ) : ℕ :=
  orderedCirclePairCount x r

/-- Literal expansion showing that `pairCount` counts all ordered pairs,
including diagonals, under a strict circular cutoff. -/
theorem pairCount_eq_strict_ordered_pairs
    {L : ℕ} (x : Fin L → ℝ) (r : ℝ) :
    pairCount x r =
      ((Finset.univ.filter fun ij : Fin L × Fin L =>
        circleDistance (x ij.2 - x ij.1) < r).card) := by
  rfl

/-- T16's cyclic occupancy comparison with independent sample length `L` and
cell count `q`.  The factor `2*R+3` and strict radii are explicit. -/
theorem pairCount_radius_le_independent_cells
    {L q : ℕ} (x : Fin L → ℝ) (R : ℕ) (hq : 0 < q) :
    (pairCount x ((R : ℝ) / (q : ℝ)) : ℝ) ≤
      (2 * R + 3) * (pairCount x ((q : ℝ)⁻¹) : ℝ) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let label : Fin L → ZMod q := fun i => cyclicCell q (x i)
  let related := (Finset.univ : Finset (Fin L × Fin L)).filter fun ij =>
    label ij.2 ∈ cyclicNeighbors q R (label ij.1)
  let equal := (Finset.univ : Finset (Fin L × Fin L)).filter fun ij =>
    label ij.1 = label ij.2
  have hlarge : pairCount x ((R : ℝ) / (q : ℝ)) ≤ related.card := by
    unfold pairCount orderedCirclePairCount
    apply Finset.card_le_card
    intro ij hij
    simp only [related, Finset.mem_filter, Finset.mem_univ, true_and]
    exact circleDistance_lt_implies_mem_cyclicNeighbors hq
      ((mem_orderedCirclePairs_iff x _ ij).mp hij)
  have hdegree : (related.card : ℝ) ≤
      (2 * R + 3) * (equal.card : ℝ) := by
    simpa [related, equal] using
      labelledPairs_le_degree_mul_equalPairs label
        (cyclicNeighbors q R) (2 * R + 3)
        (cyclicNeighbors_card_le q R)
        (fun _ _ => mem_cyclicNeighbors_symm)
  have hequal : equal.card ≤ pairCount x ((q : ℝ)⁻¹) := by
    unfold pairCount orderedCirclePairCount
    apply Finset.card_le_card
    intro ij hij
    have hij' := (Finset.mem_filter.mp hij).2
    rw [mem_orderedCirclePairs_iff]
    exact same_cyclicCell_implies_circleDistance_lt hq hij'
  calc
    (pairCount x ((R : ℝ) / (q : ℝ)) : ℝ) ≤
        (related.card : ℝ) := by exact_mod_cast hlarge
    _ ≤ (2 * R + 3) * (equal.card : ℝ) := hdegree
    _ ≤ (2 * R + 3) * (pairCount x ((q : ℝ)⁻¹) : ℝ) := by
      gcongr

/-- Cauchy-Schwarz for the `q` cyclic occupancies.  The sample length and
cell count are independent, and equal-cell pairs are ordered diagonals
included. -/
theorem sampleLength_sq_le_cells_mul_equalCellPairs
    {L q : ℕ} (x : Fin L → ℝ) (hq : 0 < q) :
    L ^ 2 ≤ q *
      ((Finset.univ.filter fun ij : Fin L × Fin L =>
        cyclicCell q (x ij.1) = cyclicCell q (x ij.2)).card) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let fiber (a : ZMod q) :=
    (Finset.univ : Finset (Fin L)).filter fun i => cyclicCell q (x i) = a
  have hsum : ∑ a : ZMod q, (fiber a).card = L := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin L)))
      (t := (Finset.univ : Finset (ZMod q)))
      (f := fun i => cyclicCell q (x i)) (by simp)
    simpa [fiber] using h.symm
  have hcs :
      (∑ a : ZMod q, (fiber a).card) ^ 2 ≤
        (Fintype.card (ZMod q)) * ∑ a : ZMod q, (fiber a).card ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (ZMod q)))
      (f := fun a => (fiber a).card)
  have hequal :
      ((Finset.univ.filter fun ij : Fin L × Fin L =>
        cyclicCell q (x ij.1) = cyclicCell q (x ij.2)).card) =
          ∑ a : ZMod q, (fiber a).card ^ 2 := by
    have hfirst := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ.filter fun ij : Fin L × Fin L =>
        cyclicCell q (x ij.1) = cyclicCell q (x ij.2)))
      (t := (Finset.univ : Finset (ZMod q)))
      (f := fun ij => cyclicCell q (x ij.1)) (by simp)
    rw [hfirst]
    apply Finset.sum_congr rfl
    intro a ha
    rw [pow_two, ← Finset.card_product]
    apply congrArg Finset.card
    ext ij
    simp only [Finset.mem_filter, Finset.mem_product, fiber,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨heq, hfirst⟩
      exact ⟨hfirst, heq ▸ hfirst⟩
    · rintro ⟨hfirst, hsecond⟩
      exact ⟨hfirst.trans hsecond.symm, hfirst⟩
  rw [hsum] at hcs
  simpa [hequal] using hcs

/-- Independent-cell occupancy lower bound in the strict pair-count notation:
`L^2 ≤ q P_x(1/q)`. -/
theorem sampleLength_sq_le_cells_mul_pairCount
    {L q : ℕ} (x : Fin L → ℝ) (hq : 0 < q) :
    L ^ 2 ≤ q * pairCount x ((q : ℝ)⁻¹) := by
  classical
  let equal := (Finset.univ.filter fun ij : Fin L × Fin L =>
    cyclicCell q (x ij.1) = cyclicCell q (x ij.2))
  have hlower := sampleLength_sq_le_cells_mul_equalCellPairs x hq
  have hequal : equal.card ≤ pairCount x ((q : ℝ)⁻¹) := by
    unfold pairCount orderedCirclePairCount
    apply Finset.card_le_card
    intro ij hij
    have hij' := (Finset.mem_filter.mp hij).2
    rw [mem_orderedCirclePairs_iff]
    exact same_cyclicCell_implies_circleDistance_lt hq hij'
  exact hlower.trans (Nat.mul_le_mul_left q hequal)

/-- The complete generic triangular band, including frequency zero. -/
theorem ordinaryFejerEnergy_eq_complete_triangular_band
    {L : ℕ} (x : Fin L → ℝ) (H : ℕ) :
    ordinaryFejerEnergy x H =
      ∑ h ∈ fejerFrequencies H,
        (1 - (h.natAbs : ℝ) / (H : ℝ)) *
          ‖∑ j : Fin L, Theory.PiDigits.T27.phase h (x j)‖ ^ 2 := by
  rfl

/-- The frequency-zero square in the complete band is exactly `L^2`. -/
theorem complete_triangular_band_zero_mode
    {L : ℕ} (x : Fin L → ℝ) :
    ‖∑ j : Fin L, Theory.PiDigits.T27.phase 0 (x j)‖ ^ 2 =
      (L : ℝ) ^ 2 := by
  exact ordinaryOrbitSum_zero x

/-- The order-`H-1` Fejer kernel has exact height `H` at zero. -/
theorem fejerKernel_pred_zero (H : ℕ) (hH : 1 ≤ H) :
    Theory.PiDigits.T27.fejerKernel (H - 1) 0 = (H : ℝ) := by
  unfold Theory.PiDigits.T27.fejerKernel Theory.PiDigits.T27.dirichletKernel
  rw [show H - 1 + 1 = H by omega]
  simp [Theory.PiDigits.T27.phase]
  rw [Nat.cast_sub hH]
  field_simp
  ring_nf
  exact mul_inv_cancel₀ (by positivity)

/-- Every ordered diagonal contributes the kernel height, so the exact
diagonal contribution is `H*L`. -/
theorem ordered_diagonal_fejer_contribution
    {L : ℕ} (x : Fin L → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (∑ i : Fin L,
      Theory.PiDigits.T27.fejerKernel (H - 1) (x i - x i)) =
        (H : ℝ) * L := by
  simp [fejerKernel_pred_zero H hH]
  ring

/-- A dyadic shell is bounded by the cumulative occupancy estimate at its
strict upper endpoint. -/
theorem dyadicShellPairs_card_le_seven_mul
    {L : ℕ} (x : Fin L → ℝ) (H k : ℕ) (hH : 1 ≤ H) :
    ((dyadicShellPairs x H k).card : ℝ) ≤
      7 * (2 : ℝ) ^ k *
        (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
  have hsubset : dyadicShellPairs x H k ⊆ dyadicNearPairs x H (k + 1) := by
    intro ij hij
    simpa [dyadicNearPairs] using (Finset.mem_filter.mp hij).2.2
  have hcard : ((dyadicShellPairs x H k).card : ℝ) ≤
      ((dyadicNearPairs x H (k + 1)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hq : 0 < 2 * H := by omega
  have hoccupancy := pairCount_radius_le_independent_cells
    x (2 ^ (k + 1)) hq
  have hnear : ((dyadicNearPairs x H (k + 1)).card : ℝ) ≤
      (2 * 2 ^ (k + 1) + 3) *
        (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
    simpa [pairCount, orderedCirclePairCount, orderedCirclePairs,
      dyadicNearPairs, pairCircleDistance, dyadicCutoff,
      Nat.cast_mul, Nat.cast_pow] using hoccupancy
  have hcoef :
      2 * (2 : ℝ) ^ (k + 1) + 3 ≤ 7 * (2 : ℝ) ^ k := by
    have hk : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  calc
    ((dyadicShellPairs x H k).card : ℝ) ≤
        ((dyadicNearPairs x H (k + 1)).card : ℝ) := hcard
    _ ≤ (2 * (2 : ℝ) ^ (k + 1) + 3) *
        (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := hnear
    _ ≤ 7 * (2 : ℝ) ^ k *
        (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- The strict central region contributes at most `H P_x(1/(2H))`. -/
theorem core_fejerSum_le_pairCount
    {L : ℕ} (x : Fin L → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (∑ ij ∈ dyadicNearPairs x H 0,
      Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        (H : ℝ) * (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
  have hcard : ((dyadicNearPairs x H 0).card : ℝ) =
      (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
    congr 1
    unfold pairCount orderedCirclePairCount orderedCirclePairs
    apply congrArg Finset.card
    ext ij
    simp [dyadicNearPairs, pairCircleDistance, dyadicCutoff]
  calc
    (∑ ij ∈ dyadicNearPairs x H 0,
        Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        ∑ _ij ∈ dyadicNearPairs x H 0, (H : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      exact fejerKernel_pred_le_height H hH _
    _ = ((dyadicNearPairs x H 0).card : ℝ) * H := by simp
    _ = (H : ℝ) * (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
      rw [hcard]
      ring

/-- All shells before `K` contribute at most `14 H P_x(1/(2H))`.
This is a deliberately simple universal geometric-series constant. -/
theorem shells_fejerSum_le_pairCount
    {L : ℕ} (x : Fin L → ℝ) (H K : ℕ) (hH : 1 ≤ H) :
    (∑ k ∈ Finset.range K, ∑ ij ∈ dyadicShellPairs x H k,
      Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        14 * (H : ℝ) *
          (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
  let P : ℝ := pairCount x ((2 * (H : ℝ))⁻¹)
  have hP : 0 ≤ P := by positivity
  have hone (k : ℕ) :
      (∑ ij ∈ dyadicShellPairs x H k,
        Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
          7 * (H : ℝ) * P * (1 / 2 : ℝ) ^ k := by
    have hcard := dyadicShellPairs_card_le_seven_mul x H k hH
    have hscale : 0 ≤ (H : ℝ) / (4 : ℝ) ^ k := by positivity
    have hp : (1 / 2 : ℝ) ^ k * (4 : ℝ) ^ k = (2 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num
    calc
      (∑ ij ∈ dyadicShellPairs x H k,
          Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
          ∑ _ij ∈ dyadicShellPairs x H k,
            ((H : ℝ) / (4 : ℝ) ^ k) := by
        apply Finset.sum_le_sum
        intro ij hij
        apply fejerKernel_pred_le_of_dyadicCutoff_le H k hH
        exact (Finset.mem_filter.mp hij).2.1
      _ = ((dyadicShellPairs x H k).card : ℝ) *
          ((H : ℝ) / (4 : ℝ) ^ k) := by simp
      _ ≤ (7 * (2 : ℝ) ^ k * P) *
          ((H : ℝ) / (4 : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_right
        · simpa [P] using hcard
        · exact hscale
      _ = 7 * (H : ℝ) * P * (1 / 2 : ℝ) ^ k := by
        field_simp
        calc
          (2 : ℝ) ^ k * P = P * (2 : ℝ) ^ k := by ring
          _ = P * ((1 / 2 : ℝ) ^ k * (4 : ℝ) ^ k) := by rw [hp]
          _ = P * (4 : ℝ) ^ k * (1 / 2 : ℝ) ^ k := by ring
  have hgeom : (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one
      (x := (1 / 2 : ℝ)) (m := 0) (n := K) (by norm_num) (by norm_num)
    norm_num at h
    simpa using h
  have hcoef : 0 ≤ 7 * (H : ℝ) * P := by positivity
  calc
    (∑ k ∈ Finset.range K, ∑ ij ∈ dyadicShellPairs x H k,
        Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        ∑ k ∈ Finset.range K,
          7 * (H : ℝ) * P * (1 / 2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hone k
    _ = (7 * (H : ℝ) * P) *
        ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ (7 * (H : ℝ) * P) * 2 :=
      mul_le_mul_of_nonneg_left hgeom hcoef
    _ = 14 * (H : ℝ) *
        (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
      dsimp [P]
      ring

/-- If the final dyadic scale satisfies `H^2 ≤ 4^K`, the entire remaining
far tail has the raw bound `L^2/H`. -/
theorem far_fejerSum_le_sampleLength_sq_div
    {L : ℕ} (x : Fin L → ℝ) (H K : ℕ) (hH : 1 ≤ H)
    (hterminal : H ^ 2 ≤ 4 ^ K) :
    (∑ ij ∈ dyadicFarPairs x H K,
      Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        (L : ℝ) ^ 2 / H := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have hcardNat : (dyadicFarPairs x H K).card ≤ L ^ 2 := by
    calc
      (dyadicFarPairs x H K).card ≤
          (Finset.univ : Finset (Fin L × Fin L)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = L ^ 2 := by simp [pow_two]
  have hcard : ((dyadicFarPairs x H K).card : ℝ) ≤ (L : ℝ) ^ 2 := by
    exact_mod_cast hcardNat
  have hterminalR : (H : ℝ) ^ 2 ≤ (4 : ℝ) ^ K := by
    exact_mod_cast hterminal
  have hratio : (H : ℝ) / (4 : ℝ) ^ K ≤ 1 / H := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ K) hHR]
    nlinarith
  have hscale : 0 ≤ (H : ℝ) / (4 : ℝ) ^ K := by positivity
  calc
    (∑ ij ∈ dyadicFarPairs x H K,
        Theory.PiDigits.T27.fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        ∑ _ij ∈ dyadicFarPairs x H K,
          ((H : ℝ) / (4 : ℝ) ^ K) := by
      apply Finset.sum_le_sum
      intro ij hij
      apply fejerKernel_pred_le_of_dyadicCutoff_le H K hH
      exact (Finset.mem_filter.mp hij).2
    _ = ((dyadicFarPairs x H K).card : ℝ) *
        ((H : ℝ) / (4 : ℝ) ^ K) := by simp
    _ ≤ (L : ℝ) ^ 2 * ((H : ℝ) / (4 : ℝ) ^ K) :=
      mul_le_mul_of_nonneg_right hcard hscale
    _ ≤ (L : ℝ) ^ 2 * (1 / H) := by
      gcongr
    _ = (L : ℝ) ^ 2 / H := by ring

/-- Raw arbitrary-sequence estimate with independent `L` and `H`.  It keeps
the strict central cutoff and the unabsorbed far term `L^2/H`. -/
theorem ordinaryFejerEnergy_le_fifteen_mul_add_far
    {L : ℕ} (x : Fin L → ℝ) (H K : ℕ) (hH : 1 ≤ H)
    (hterminal : H ^ 2 ≤ 4 ^ K) :
    ordinaryFejerEnergy x H ≤
      15 * (H : ℝ) * (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) +
        (L : ℝ) ^ 2 / H := by
  rw [← orderedPair_fejerKernel_eq_ordinaryFejerEnergy x H hH]
  change finiteFejerEnergy x H ≤
    15 * (H : ℝ) * (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) +
      (L : ℝ) ^ 2 / H
  rw [finiteFejerEnergy_eq_core_add_shells_add_far x H K hH]
  have hcore := core_fejerSum_le_pairCount x H hH
  have hshell := shells_fejerSum_le_pairCount x H K hH
  have hfar := far_fejerSum_le_sampleLength_sq_div x H K hH hterminal
  linarith

/-- The choice `K=H` always reaches the raw `L^2/H` tail. -/
theorem bandwidth_sq_le_four_pow_bandwidth (H : ℕ) : H ^ 2 ≤ 4 ^ H := by
  calc
    H ^ 2 ≤ 2 * H ^ 2 + 1 := by omega
    _ ≤ 2 ^ (2 * H) := Nat.two_mul_sq_add_one_le_two_pow_two_mul H
    _ = 4 ^ H := by rw [pow_mul]; norm_num

/-- Universal arbitrary-sequence estimate after absorbing `L^2/H` with the
independent-cell occupancy lower bound at `q=2H`. -/
theorem ordinaryFejerEnergy_le_seventeen_mul_pairCount
    {L : ℕ} (x : Fin L → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    ordinaryFejerEnergy x H ≤
      17 * (H : ℝ) * (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
  have hraw := ordinaryFejerEnergy_le_fifteen_mul_add_far
    x H H hH (bandwidth_sq_le_four_pow_bandwidth H)
  have hq : 0 < 2 * H := by omega
  have hoccNat := sampleLength_sq_le_cells_mul_pairCount x hq
  have hocc : (L : ℝ) ^ 2 ≤
      (2 * (H : ℝ)) *
        (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
    exact_mod_cast hoccNat
  have hHR : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have hfar : (L : ℝ) ^ 2 / H ≤
      2 * (H : ℝ) *
        (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
    calc
      (L : ℝ) ^ 2 / H ≤
          ((2 * (H : ℝ)) *
            (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ)) / H := by
        gcongr
      _ = 2 * (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
        field_simp
      _ ≤ 2 * (H : ℝ) *
          (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by
        have hP : 0 ≤ (pairCount x ((2 * (H : ℝ))⁻¹) : ℝ) := by positivity
        have htwo : (2 : ℝ) ≤ 2 * H := by exact_mod_cast Nat.mul_le_mul_left 2 hH
        exact mul_le_mul_of_nonneg_right htwo hP
  linarith

/-- At the sparse decimal parameters, the generic complete energy is exactly
T26's sample-first complete pi energy. -/
theorem ordinaryFejerEnergy_pi_eq_completePiFejerEnergy (n : ℕ) :
    ordinaryFejerEnergy
        (fun j : Fin (sparseSampleLength n) => piDecimalShiftOrbit j)
        (longBandwidth n) =
      completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) := by
  rfl

/-- The decimal cutoff identifies the strict generic ordered pair count with
`Q_pi(n,L)` for every independently chosen sample length `L`. -/
theorem pairCount_pi_eq_Q_pi (n L : ℕ) :
    pairCount (fun j : Fin L => piDecimalShiftOrbit j)
        (((10 : ℝ) ^ n)⁻¹) = Q_pi n L := by
  classical
  unfold pairCount orderedCirclePairCount orderedCirclePairs Q_pi
  apply congrArg Finset.card
  ext ij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [circleDistance_piShift_sub_eq_powerDifference]
  rw [mem_piNearReturnPairs_iff]

/-- At every positive scale, `2*H_n=10^n` converts the strict `1/(2H_n)`
pair count exactly to `Q_pi(n,L_n)`. -/
theorem sparse_pairCount_eq_Q_pi (n : ℕ) (hn : 1 ≤ n) :
    pairCount
        (fun j : Fin (sparseSampleLength n) => piDecimalShiftOrbit j)
        ((2 * (longBandwidth n : ℝ))⁻¹) =
      Q_pi n (sparseSampleLength n) := by
  have htwoNat : 2 * longBandwidth n = 10 ^ n :=
    two_mul_longBandwidth n hn
  have htwoReal : 2 * (longBandwidth n : ℝ) = (10 : ℝ) ^ n := by
    exact_mod_cast htwoNat
  rw [htwoReal]
  exact pairCount_pi_eq_Q_pi n (sparseSampleLength n)

/-- Named T27 boundary exposing the exact natural-number parameter identity
`2*H_n=10^n` for `n≥1`. -/
theorem two_mul_sparse_longBandwidth (n : ℕ) (hn : 1 ≤ n) :
    2 * longBandwidth n = 10 ^ n :=
  two_mul_longBandwidth n hn

/-- The exact eventual statement `Q_pi(n,L_n)=O(L_n)`.  Its one positive
constant is fixed before the cutoff and before all later `n`. -/
def PiSparseMicroscopicQBound : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      (Q_pi n (sparseSampleLength n) : ℝ) ≤
        A * (sparseSampleLength n : ℝ)

/-- Literal quantifier expansion of the sparse microscopic frontier. -/
theorem piSparseMicroscopicQBound_iff_quantifiers :
    PiSparseMicroscopicQBound ↔
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (Q_pi n (sparseSampleLength n) : ℝ) ≤
            A * (sparseSampleLength n : ℝ) :=
  Iff.rfl

/-- T26's energy-to-collision direction, repackaged with the actual positive
big-O constant `pi^2 C/4`. -/
theorem piSparseLongBandC7_implies_sparseMicroscopicQBound
    (hC7 : PiSparseLongBandC7) : PiSparseMicroscopicQBound := by
  obtain ⟨C, hC, N, hN, hall⟩ :=
    piSparseLongBandC7_implies_explicit_Q_linear hC7
  refine ⟨Real.pi ^ 2 / 4 * C, by positivity, N, hN, ?_⟩
  intro n hn
  exact hall n hn

/-- The new collision-to-energy direction with the numerical universal
constant `17`; it retains the exact eventual quantifier order. -/
theorem piSparseMicroscopicQBound_implies_C7_explicit
    (A : ℝ) (_hA : 0 < A) (N : ℕ) (hN : 1 ≤ N)
    (hQ : ∀ n : ℕ, N ≤ n →
      (Q_pi n (sparseSampleLength n) : ℝ) ≤
        A * (sparseSampleLength n : ℝ)) :
    ∀ n : ℕ, N ≤ n →
      completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) ≤
        (17 * A) * (longBandwidth n : ℝ) *
          (sparseSampleLength n : ℝ) := by
  intro n hn
  have hnpos : 1 ≤ n := hN.trans hn
  have hH : 1 ≤ longBandwidth n := by
    have htwo := two_mul_longBandwidth n hnpos
    have hpow : 0 < 10 ^ n := by positivity
    omega
  let x : Fin (sparseSampleLength n) → ℝ := fun j => piDecimalShiftOrbit j
  have hgeneric := ordinaryFejerEnergy_le_seventeen_mul_pairCount x
    (longBandwidth n) hH
  have hpair := sparse_pairCount_eq_Q_pi n hnpos
  calc
    completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) =
        ordinaryFejerEnergy x (longBandwidth n) := by
      symm
      exact ordinaryFejerEnergy_pi_eq_completePiFejerEnergy n
    _ ≤ 17 * (longBandwidth n : ℝ) *
        (pairCount x ((2 * (longBandwidth n : ℝ))⁻¹) : ℝ) := hgeneric
    _ = 17 * (longBandwidth n : ℝ) *
        (Q_pi n (sparseSampleLength n) : ℝ) := by rw [hpair]
    _ ≤ 17 * (longBandwidth n : ℝ) *
        (A * (sparseSampleLength n : ℝ)) := by
      gcongr
      exact hQ n hn
    _ = (17 * A) * (longBandwidth n : ℝ) *
        (sparseSampleLength n : ℝ) := by ring

/-- The sparse microscopic eventual bound implies C7; no instance of the
hypothesis is asserted. -/
theorem piSparseMicroscopicQBound_implies_C7
    (hQ : PiSparseMicroscopicQBound) : PiSparseLongBandC7 := by
  obtain ⟨A, hA, N, hN, hall⟩ := hQ
  refine ⟨17 * A, by positivity, N, hN, ?_⟩
  exact piSparseMicroscopicQBound_implies_C7_explicit A hA N hN hall

/-- Exact equivalence, in both eventual-quantifier directions, between the
unproved C7 energy hypothesis and `Q_pi(n,L_n)=O(L_n)`. -/
theorem piSparseLongBandC7_iff_sparseMicroscopicQBound :
    PiSparseLongBandC7 ↔ PiSparseMicroscopicQBound :=
  ⟨piSparseLongBandC7_implies_sparseMicroscopicQBound,
    piSparseMicroscopicQBound_implies_C7⟩

/-- Fully exposed version of the exact equivalence checked by T27. -/
theorem piSparseLongBandC7_iff_Q_linear_quantifiers :
    PiSparseLongBandC7 ↔
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (Q_pi n (10 ^ (n / 2)) : ℝ) ≤
            A * ((10 ^ (n / 2) : ℕ) : ℝ) := by
  rw [piSparseLongBandC7_iff_sparseMicroscopicQBound,
    piSparseMicroscopicQBound_iff_quantifiers]
  rfl

/-- Both sides written with literal eventual quantifiers and raw sparse
parameters.  This is an equivalence of hypotheses, not an assertion of either
side. -/
theorem C7_quantifiers_iff_Q_linear_quantifiers :
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        completePiFejerEnergy (10 ^ (n / 2)) (10 ^ n / 2) ≤
          C * ((10 ^ n / 2 : ℕ) : ℝ) *
            ((10 ^ (n / 2) : ℕ) : ℝ)) ↔
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (Q_pi n (10 ^ (n / 2)) : ℝ) ≤
            A * ((10 ^ (n / 2) : ℕ) : ℝ) := by
  change
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) ≤
          C * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ)) ↔ _
  rw [← piSparseLongBandC7_iff_quantifiers]
  exact piSparseLongBandC7_iff_Q_linear_quantifiers

end DecimalFactorComplexity.SparseMicroscopicEquivalence

#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.pairCount_eq_strict_ordered_pairs
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.pairCount_radius_le_independent_cells
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.sampleLength_sq_le_cells_mul_pairCount
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.ordinaryFejerEnergy_eq_complete_triangular_band
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.complete_triangular_band_zero_mode
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.ordered_diagonal_fejer_contribution
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.ordinaryFejerEnergy_le_fifteen_mul_add_far
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.ordinaryFejerEnergy_le_seventeen_mul_pairCount
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.pairCount_pi_eq_Q_pi
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.sparse_pairCount_eq_Q_pi
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.two_mul_sparse_longBandwidth
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.piSparseMicroscopicQBound_iff_quantifiers
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.piSparseLongBandC7_implies_sparseMicroscopicQBound
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.piSparseMicroscopicQBound_implies_C7_explicit
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.piSparseMicroscopicQBound_implies_C7
#print axioms DecimalFactorComplexity.SparseMicroscopicEquivalence.C7_quantifiers_iff_Q_linear_quantifiers
