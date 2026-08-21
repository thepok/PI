import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion
import Mathlib.Algebra.Order.Round

/-!
# T8: dyadic pair counts imply a finite Fejer-energy bound

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The generic part treats an arbitrary finite sequence on `R/Z`.  The order is
`H - 1`, so the normalized Fejer kernel has mass one and height `H`.  Ordered
pairs, including the diagonal, are split at the strict central cutoff
`distance < 1/(2H)`, the half-open shells
`2^k/(2H) <= distance < 2^(k+1)/(2H)` for `k < K`, and the closed far tail
`2^K/(2H) <= distance`.

The final part fixes `M = 10^n` and `H = M/2`.  Its multiscale estimate is an
explicit unproved hypothesis about the decimal orbit of pi.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace DecimalFactorComplexity.DyadicShellFejer

open DecimalFactorComplexity
open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.PairCorrelationConditional
open Theory.PiDigits.BoundaryRobustFejerDichotomy

abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-- Circular distance between the entries indexed by an ordered pair. -/
def pairCircleDistance {M : ℕ} (x : Fin M → ℝ) (ij : Fin M × Fin M) : ℝ :=
  circleDistance (x ij.2 - x ij.1)

/-- The `k`th dyadic radius `2^k/(2H)`. -/
def dyadicCutoff (H k : ℕ) : ℝ :=
  (2 : ℝ) ^ k / (2 * (H : ℝ))

/-- Ordered pairs below the strict `k`th dyadic cutoff. -/
def dyadicNearPairs {M : ℕ} (x : Fin M → ℝ) (H k : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter fun ij => pairCircleDistance x ij < dyadicCutoff H k

/-- The half-open `k`th shell.  Its lower endpoint is included and its upper
endpoint is excluded. -/
def dyadicShellPairs {M : ℕ} (x : Fin M → ℝ) (H k : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter fun ij =>
    dyadicCutoff H k ≤ pairCircleDistance x ij ∧
      pairCircleDistance x ij < dyadicCutoff H (k + 1)

/-- Ordered pairs at or beyond the last dyadic cutoff. -/
def dyadicFarPairs {M : ℕ} (x : Fin M → ℝ) (H K : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter fun ij => dyadicCutoff H K ≤ pairCircleDistance x ij

/-- Pair-side form of the order-`H-1` Fejer energy.  T7 proves that this is
the weighted Fourier energy for the decimal orbit of pi. -/
def finiteFejerEnergy {M : ℕ} (x : Fin M → ℝ) (H : ℕ) : ℝ :=
  ∑ ij : Fin M × Fin M, fejerKernel (H - 1) (x ij.2 - x ij.1)

/-- Energy normalized by the total number `M^2` of ordered pairs. -/
def normalizedFiniteFejerEnergy {M : ℕ} (x : Fin M → ℝ) (H : ℕ) : ℝ :=
  finiteFejerEnergy x H / ((M : ℝ) ^ 2)

/-- Raw multiscale pair-count assumptions.  The central count is normalized
by `M^2/H`; shell `k` by `M^2 2^(k+1)/H`; and `H <= 4^K` makes the uncounted
far-pair tail contribute at most `M^2`. -/
def DyadicPairCountBounds {M : ℕ} (x : Fin M → ℝ)
    (H K : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧ H ≤ 4 ^ K ∧
    ((dyadicNearPairs x H 0).card : ℝ) ≤ A * (M : ℝ) ^ 2 / H ∧
    ∀ k : ℕ, k < K →
      ((dyadicShellPairs x H k).card : ℝ) ≤
        A * (M : ℝ) ^ 2 * (2 : ℝ) ^ (k + 1) / H

/-- The central cutoff is literally the strict radius `1/(2H)`. -/
theorem dyadicCutoff_zero (H : ℕ) :
    dyadicCutoff H 0 = (2 * (H : ℝ))⁻¹ := by
  unfold dyadicCutoff
  simp [div_eq_mul_inv]

/-- A theorem-level expansion exposing every generic multiscale quantifier,
shell range, endpoint convention, normalization, and constant. -/
theorem dyadicPairCountBounds_iff_quantifiers (M : ℕ) (x : Fin M → ℝ)
    (H K : ℕ) (A : ℝ) :
    DyadicPairCountBounds x H K A ↔
      0 ≤ A ∧ H ≤ 4 ^ K ∧
      (((Finset.univ.filter (fun ij : Fin M × Fin M =>
          circleDistance (x ij.2 - x ij.1) < (2 * (H : ℝ))⁻¹)).card : ℝ) ≤
        A * (M : ℝ) ^ 2 / H) ∧
      ∀ k : ℕ, k < K →
        (((Finset.univ.filter (fun ij : Fin M × Fin M =>
          (2 : ℝ) ^ k / (2 * (H : ℝ)) ≤
              circleDistance (x ij.2 - x ij.1) ∧
            circleDistance (x ij.2 - x ij.1) <
              (2 : ℝ) ^ (k + 1) / (2 * (H : ℝ)))).card : ℝ) ≤
          A * (M : ℝ) ^ 2 * (2 : ℝ) ^ (k + 1) / H) := by
  unfold DyadicPairCountBounds dyadicNearPairs dyadicShellPairs
    pairCircleDistance dyadicCutoff
  simp only [pow_zero, one_div]

/-- The custom circle distance is attained by the nearest integer and is at
most one half. -/
theorem exists_int_circleDistance_eq_abs_le_half (y : ℝ) :
    ∃ z : ℤ, circleDistance y = |y - (z : ℝ)| ∧ |y - (z : ℝ)| ≤ 1 / 2 := by
  refine ⟨round y, ?_, ?_⟩
  · apply le_antisymm
    · exact circleDistance_le_abs_sub_int y (round y)
    · unfold circleDistance
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨z, rfl⟩
      exact round_le y z
  · simpa using abs_sub_round y

/-- In particular, the custom circle distance always lies in `[0,1/2]`. -/
theorem circleDistance_le_half (y : ℝ) : circleDistance y ≤ 1 / 2 := by
  obtain ⟨z, hz, hzhalf⟩ := exists_int_circleDistance_eq_abs_le_half y
  rw [hz]
  exact hzhalf

/-- Dyadic cutoffs strictly increase when `H` is positive. -/
theorem dyadicCutoff_lt_succ (H k : ℕ) (hH : 1 ≤ H) :
    dyadicCutoff H k < dyadicCutoff H (k + 1) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  unfold dyadicCutoff
  rw [pow_succ]
  apply div_lt_div_of_pos_right _ (by positivity : (0 : ℝ) < 2 * H)
  have hpow : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
  nlinarith

/-- Passing from cutoff `k` to `k+1` adds exactly shell `k`. -/
theorem dyadicNearPairs_succ_eq_union {M : ℕ} (x : Fin M → ℝ)
    (H k : ℕ) (hH : 1 ≤ H) :
    dyadicNearPairs x H (k + 1) =
      dyadicNearPairs x H k ∪ dyadicShellPairs x H k := by
  ext ij
  simp only [dyadicNearPairs, dyadicShellPairs, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  have hcut := dyadicCutoff_lt_succ H k hH
  constructor
  · intro hupper
    by_cases hlower : pairCircleDistance x ij < dyadicCutoff H k
    · exact Or.inl hlower
    · exact Or.inr ⟨le_of_not_gt hlower, hupper⟩
  · rintro (hnear | hshell)
    · exact hnear.trans hcut
    · exact hshell.2

/-- The old near region and the newly added shell are disjoint. -/
theorem disjoint_dyadicNearPairs_dyadicShellPairs {M : ℕ}
    (x : Fin M → ℝ) (H k : ℕ) :
    Disjoint (dyadicNearPairs x H k) (dyadicShellPairs x H k) := by
  rw [Finset.disjoint_left]
  intro ij hnear hshell
  simp only [dyadicNearPairs, Finset.mem_filter, Finset.mem_univ,
    true_and] at hnear
  simp only [dyadicShellPairs, Finset.mem_filter, Finset.mem_univ,
    true_and] at hshell
  exact (not_lt_of_ge hshell.1) hnear

/-- The strict near region and closed far region partition all ordered pairs. -/
theorem dyadicNearPairs_union_farPairs {M : ℕ} (x : Fin M → ℝ)
    (H K : ℕ) :
    dyadicNearPairs x H K ∪ dyadicFarPairs x H K = Finset.univ := by
  ext ij
  simp only [dyadicNearPairs, dyadicFarPairs, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact lt_or_ge (pairCircleDistance x ij) (dyadicCutoff H K)

/-- The near/far partition is disjoint because the cutoff is strict on the
near side and weak on the far side. -/
theorem disjoint_dyadicNearPairs_dyadicFarPairs {M : ℕ}
    (x : Fin M → ℝ) (H K : ℕ) :
    Disjoint (dyadicNearPairs x H K) (dyadicFarPairs x H K) := by
  rw [Finset.disjoint_left]
  intro ij hnear hfar
  simp only [dyadicNearPairs, Finset.mem_filter, Finset.mem_univ,
    true_and] at hnear
  simp only [dyadicFarPairs, Finset.mem_filter, Finset.mem_univ,
    true_and] at hfar
  exact (not_lt_of_ge hfar) hnear

/-- Exact finite shell decomposition of a sum over the strict near region. -/
theorem sum_dyadicNearPairs_eq_core_add_shells {M : ℕ}
    (x : Fin M → ℝ) (H K : ℕ) (hH : 1 ≤ H)
    (f : Fin M × Fin M → ℝ) :
    (∑ ij ∈ dyadicNearPairs x H K, f ij) =
      (∑ ij ∈ dyadicNearPairs x H 0, f ij) +
        ∑ k ∈ Finset.range K, ∑ ij ∈ dyadicShellPairs x H k, f ij := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show K + 1 = Nat.succ K by omega,
        dyadicNearPairs_succ_eq_union x H K hH,
        Finset.sum_union (disjoint_dyadicNearPairs_dyadicShellPairs x H K),
        ih, Finset.sum_range_succ]
      ring

/-- Exact decomposition of the full pair-side energy into the central region,
all shells `k < K`, and the far tail. -/
theorem finiteFejerEnergy_eq_core_add_shells_add_far {M : ℕ}
    (x : Fin M → ℝ) (H K : ℕ) (hH : 1 ≤ H) :
    finiteFejerEnergy x H =
      (∑ ij ∈ dyadicNearPairs x H 0,
        fejerKernel (H - 1) (x ij.2 - x ij.1)) +
      (∑ k ∈ Finset.range K, ∑ ij ∈ dyadicShellPairs x H k,
        fejerKernel (H - 1) (x ij.2 - x ij.1)) +
      ∑ ij ∈ dyadicFarPairs x H K,
        fejerKernel (H - 1) (x ij.2 - x ij.1) := by
  classical
  unfold finiteFejerEnergy
  rw [← dyadicNearPairs_union_farPairs x H K,
    Finset.sum_union (disjoint_dyadicNearPairs_dyadicFarPairs x H K),
    sum_dyadicNearPairs_eq_core_add_shells x H K hH]

/-- The order-`H-1` normalized Fejer kernel has height at most `H`. -/
theorem fejerKernel_pred_le_height (H : ℕ) (hH : 1 ≤ H) (y : ℝ) :
    fejerKernel (H - 1) y ≤ (H : ℝ) := by
  have hk := Theory.PiDigits.T27.fejerKernel_le (H - 1) y
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hH
  simpa only [Nat.cast_add, Nat.cast_one, hcast] using hk

/-- Beyond the `k`th dyadic cutoff, inverse-square decay improves the height
`H` to the explicit bound `H/4^k`. -/
theorem fejerKernel_pred_le_of_dyadicCutoff_le
    (H k : ℕ) (hH : 1 ≤ H) (y : ℝ)
    (hy : dyadicCutoff H k ≤ circleDistance y) :
    fejerKernel (H - 1) y ≤ (H : ℝ) / (4 : ℝ) ^ k := by
  obtain ⟨z, hz, hzhalf⟩ := exists_int_circleDistance_eq_abs_le_half y
  let t : ℝ := y - (z : ℝ)
  have hHR : (0 : ℝ) < H := by
    exact_mod_cast Nat.zero_lt_of_lt hH
  have htcut : dyadicCutoff H k ≤ |t| := by
    simpa only [t, hz] using hy
  have hcutpos : 0 < dyadicCutoff H k := by
    unfold dyadicCutoff
    positivity
  have htpos : 0 < |t| := hcutpos.trans_le htcut
  have ht0 : t ≠ 0 := abs_pos.mp htpos
  have hkernel := fejerKernel_le_inverse_square (H - 1) ht0 (by
    simpa only [t] using hzhalf)
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hH
  have hshift : fejerKernel (H - 1) t = fejerKernel (H - 1) y := by
    have hp :=
      DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_int_shift
        (H - 1) z t
    simpa only [t, sub_add_cancel] using hp.symm
  have htwo' : (2 : ℝ) ^ k ≤ |t| * (2 * (H : ℝ)) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * H)).mp
    simpa only [dyadicCutoff] using htcut
  have htwo : (2 : ℝ) ^ k ≤ 2 * (H : ℝ) * |t| := by
    nlinarith [htwo']
  have hsquare : ((2 : ℝ) ^ k) ^ 2 ≤ (2 * (H : ℝ) * |t|) ^ 2 := by
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k, abs_nonneg t]
  have hpow : (4 : ℝ) ^ k ≤ 4 * (H : ℝ) ^ 2 * t ^ 2 := by
    have hpow_eq : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      calc
        (4 : ℝ) ^ k = ((2 : ℝ) ^ 2) ^ k := by norm_num
        _ = (2 : ℝ) ^ (2 * k) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (k * 2) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ k) ^ 2 := by rw [pow_mul]
    rw [hpow_eq]
    nlinarith [hsquare, sq_abs t]
  have hden : 0 < 4 * (H : ℝ) * t ^ 2 := by positivity
  have hfourpow : 0 < (4 : ℝ) ^ k := by positivity
  calc
    fejerKernel (H - 1) y = fejerKernel (H - 1) t := hshift.symm
    _ ≤ 1 / (4 * (H : ℝ) * t ^ 2) := by
      simpa only [hcast] using hkernel
    _ ≤ (H : ℝ) / (4 : ℝ) ^ k := by
      apply (le_div_iff₀ hfourpow).2
      calc
        1 / (4 * (H : ℝ) * t ^ 2) * (4 : ℝ) ^ k =
            (4 : ℝ) ^ k / (4 * (H : ℝ) * t ^ 2) := by ring
        _ ≤ (H : ℝ) := by
          apply (div_le_iff₀ hden).2
          nlinarith [hpow]

/-- The strict central region contributes at most `A M^2` under its raw
pair-count bound. -/
theorem core_fejerSum_le {M : ℕ} (x : Fin M → ℝ) (H : ℕ)
    (A : ℝ) (hH : 1 ≤ H)
    (hcount : ((dyadicNearPairs x H 0).card : ℝ) ≤
      A * (M : ℝ) ^ 2 / H) :
    (∑ ij ∈ dyadicNearPairs x H 0,
      fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤ A * (M : ℝ) ^ 2 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  calc
    (∑ ij ∈ dyadicNearPairs x H 0,
        fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        ∑ _ij ∈ dyadicNearPairs x H 0, (H : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      exact fejerKernel_pred_le_height H hH _
    _ = ((dyadicNearPairs x H 0).card : ℝ) * H := by simp
    _ ≤ (A * (M : ℝ) ^ 2 / H) * H :=
      mul_le_mul_of_nonneg_right hcount hHR.le
    _ = A * (M : ℝ) ^ 2 := by field_simp

/-- A single shell has the explicit geometric contribution
`2 A M^2 (1/2)^k`. -/
theorem shell_fejerSum_le {M : ℕ} (x : Fin M → ℝ) (H k : ℕ)
    (A : ℝ) (hH : 1 ≤ H)
    (hcount : ((dyadicShellPairs x H k).card : ℝ) ≤
      A * (M : ℝ) ^ 2 * (2 : ℝ) ^ (k + 1) / H) :
    (∑ ij ∈ dyadicShellPairs x H k,
      fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        2 * A * (M : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  have hscale : 0 ≤ (H : ℝ) / (4 : ℝ) ^ k := by positivity
  calc
    (∑ ij ∈ dyadicShellPairs x H k,
        fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        ∑ _ij ∈ dyadicShellPairs x H k,
          ((H : ℝ) / (4 : ℝ) ^ k) := by
      apply Finset.sum_le_sum
      intro ij hij
      apply fejerKernel_pred_le_of_dyadicCutoff_le H k hH
      exact (Finset.mem_filter.mp hij).2.1
    _ = ((dyadicShellPairs x H k).card : ℝ) *
        ((H : ℝ) / (4 : ℝ) ^ k) := by simp
    _ ≤ (A * (M : ℝ) ^ 2 * (2 : ℝ) ^ (k + 1) / H) *
        ((H : ℝ) / (4 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hcount hscale
    _ = 2 * A * (M : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k := by
      have hp : (1 / 2 : ℝ) ^ k * (4 : ℝ) ^ k = (2 : ℝ) ^ k := by
        rw [← mul_pow]
        norm_num
      field_simp
      calc
        A * (M : ℝ) ^ 2 * (2 : ℝ) ^ (k + 1) =
            A * (M : ℝ) ^ 2 *
              ((1 / 2 : ℝ) ^ k * (4 : ℝ) ^ k) * 2 := by
                rw [pow_succ, hp]
                ring
        _ = A * (M : ℝ) ^ 2 * (4 : ℝ) ^ k * 2 *
            (1 / 2 : ℝ) ^ k := by ring

/-- Summing all shells costs at most `4 A M^2`; this is the only geometric
series estimate in the argument. -/
theorem shells_fejerSum_le {M : ℕ} (x : Fin M → ℝ) (H K : ℕ)
    (A : ℝ) (hH : 1 ≤ H) (hA : 0 ≤ A)
    (hcount : ∀ k : ℕ, k < K →
      ((dyadicShellPairs x H k).card : ℝ) ≤
        A * (M : ℝ) ^ 2 * (2 : ℝ) ^ (k + 1) / H) :
    (∑ k ∈ Finset.range K, ∑ ij ∈ dyadicShellPairs x H k,
      fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        4 * A * (M : ℝ) ^ 2 := by
  have hgeom : (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one
      (x := (1 / 2 : ℝ)) (m := 0) (n := K) (by norm_num) (by norm_num)
    norm_num at h
    simpa using h
  have hcoefficient : 0 ≤ 2 * A * (M : ℝ) ^ 2 := by positivity
  calc
    (∑ k ∈ Finset.range K, ∑ ij ∈ dyadicShellPairs x H k,
        fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        ∑ k ∈ Finset.range K,
          2 * A * (M : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact shell_fejerSum_le x H k A hH
        (hcount k (Finset.mem_range.mp hk))
    _ = (2 * A * (M : ℝ) ^ 2) *
        ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ (2 * A * (M : ℝ) ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hgeom hcoefficient
    _ = 4 * A * (M : ℝ) ^ 2 := by ring

/-- The closed far tail contributes at most `M^2` when `H <= 4^K`; no
distributional information about far pairs is assumed. -/
theorem far_fejerSum_le {M : ℕ} (x : Fin M → ℝ) (H K : ℕ)
    (hH : 1 ≤ H) (hterminal : H ≤ 4 ^ K) :
    (∑ ij ∈ dyadicFarPairs x H K,
      fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤ (M : ℝ) ^ 2 := by
  have hscale : 0 ≤ (H : ℝ) / (4 : ℝ) ^ K := by positivity
  have hcardNat : (dyadicFarPairs x H K).card ≤ M ^ 2 := by
    calc
      (dyadicFarPairs x H K).card ≤
          (Finset.univ : Finset (Fin M × Fin M)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = M ^ 2 := by simp [pow_two]
  have hcard : ((dyadicFarPairs x H K).card : ℝ) ≤ (M : ℝ) ^ 2 := by
    exact_mod_cast hcardNat
  have hterminalR : (H : ℝ) ≤ (4 : ℝ) ^ K := by exact_mod_cast hterminal
  have hratio : (H : ℝ) / (4 : ℝ) ^ K ≤ 1 := by
    exact (div_le_one (by positivity : (0 : ℝ) < (4 : ℝ) ^ K)).2 hterminalR
  calc
    (∑ ij ∈ dyadicFarPairs x H K,
        fejerKernel (H - 1) (x ij.2 - x ij.1)) ≤
        ∑ _ij ∈ dyadicFarPairs x H K,
          ((H : ℝ) / (4 : ℝ) ^ K) := by
      apply Finset.sum_le_sum
      intro ij hij
      apply fejerKernel_pred_le_of_dyadicCutoff_le H K hH
      exact (Finset.mem_filter.mp hij).2
    _ = ((dyadicFarPairs x H K).card : ℝ) *
        ((H : ℝ) / (4 : ℝ) ^ K) := by simp
    _ ≤ (M : ℝ) ^ 2 * ((H : ℝ) / (4 : ℝ) ^ K) :=
      mul_le_mul_of_nonneg_right hcard hscale
    _ ≤ (M : ℝ) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hratio (sq_nonneg (M : ℝ))
    _ = (M : ℝ) ^ 2 := by ring

/-- Generic dyadic-shell theorem with all constants visible.  It includes
ordered diagonal pairs, uses strict upper shell endpoints, and pays `1*M^2`
for the entire far tail. -/
theorem finiteFejerEnergy_le_of_dyadicPairCountBounds
    (M : ℕ) (x : Fin M → ℝ) (H K : ℕ) (A : ℝ)
    (hH : 1 ≤ H) (hbounds : DyadicPairCountBounds x H K A) :
    finiteFejerEnergy x H ≤ (5 * A + 1) * (M : ℝ) ^ 2 := by
  rcases hbounds with ⟨hA, hterminal, hcoreCount, hshellCount⟩
  have hdecomp := finiteFejerEnergy_eq_core_add_shells_add_far x H K hH
  have hcore := core_fejerSum_le x H A hH hcoreCount
  have hshells := shells_fejerSum_le x H K A hH hA hshellCount
  have hfar := far_fejerSum_le x H K hH hterminal
  rw [hdecomp]
  calc
    (∑ ij ∈ dyadicNearPairs x H 0,
          fejerKernel (H - 1) (x ij.2 - x ij.1)) +
        (∑ k ∈ Finset.range K, ∑ ij ∈ dyadicShellPairs x H k,
          fejerKernel (H - 1) (x ij.2 - x ij.1)) +
      ∑ ij ∈ dyadicFarPairs x H K,
          fejerKernel (H - 1) (x ij.2 - x ij.1) ≤
        A * (M : ℝ) ^ 2 + 4 * A * (M : ℝ) ^ 2 + (M : ℝ) ^ 2 :=
      add_le_add (add_le_add hcore hshells) hfar
    _ = (5 * A + 1) * (M : ℝ) ^ 2 := by ring

/-- Dividing by the `M^2` ordered-pair normalization gives the same explicit
The constant. -/
theorem normalizedFiniteFejerEnergy_le_of_dyadicPairCountBounds
    (M : ℕ) (x : Fin M → ℝ) (H K : ℕ) (A : ℝ)
    (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hbounds : DyadicPairCountBounds x H K A) :
    normalizedFiniteFejerEnergy x H ≤ 5 * A + 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  unfold normalizedFiniteFejerEnergy
  apply (div_le_iff₀ (sq_pos_of_pos hMpos)).2
  simpa only [mul_comm] using
    finiteFejerEnergy_le_of_dyadicPairCountBounds M x H K A hH hbounds

/-- Fixed-pi multiscale estimate left explicitly unproved.  At every large
`n`, it fixes `M=10^n`, `H=M/2`, permits a terminal shell count `K`, and
requires exactly the raw bounds used by the generic theorem. -/
def PiDyadicMultiscaleHypothesis : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∃ K : ℕ,
      DyadicPairCountBounds
        (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
        (10 ^ n / 2) K A

/-- Full quantifier expansion of the unproved fixed-pi hypothesis. -/
theorem piDyadicMultiscaleHypothesis_iff_quantifiers :
    PiDyadicMultiscaleHypothesis ↔
      ∃ A : ℝ, 0 ≤ A ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
        ∀ n : ℕ, n0 ≤ n → ∃ K : ℕ,
          (10 ^ n / 2) ≤ 4 ^ K ∧
          (((Finset.univ.filter (fun ij : Fin (10 ^ n) × Fin (10 ^ n) =>
            circleDistance
                (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
              (2 * ((10 ^ n / 2 : ℕ) : ℝ))⁻¹)).card : ℝ) ≤
            A * ((10 ^ n : ℕ) : ℝ) ^ 2 / (10 ^ n / 2 : ℕ)) ∧
          ∀ k : ℕ, k < K →
            (((Finset.univ.filter (fun ij : Fin (10 ^ n) × Fin (10 ^ n) =>
              (2 : ℝ) ^ k / (2 * ((10 ^ n / 2 : ℕ) : ℝ)) ≤
                  circleDistance
                    (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) ∧
                circleDistance
                    (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
                  (2 : ℝ) ^ (k + 1) /
                    (2 * ((10 ^ n / 2 : ℕ) : ℝ)))).card : ℝ) ≤
              A * ((10 ^ n : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (k + 1) /
                (10 ^ n / 2 : ℕ)) := by
  constructor
  · rintro ⟨A, hA, n0, hn0, hall⟩
    refine ⟨A, hA, n0, hn0, ?_⟩
    intro n hn
    obtain ⟨K, hbounds⟩ := hall n hn
    refine ⟨K, ?_⟩
    exact ((dyadicPairCountBounds_iff_quantifiers
      (10 ^ n)
      (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
      (10 ^ n / 2) K A).mp hbounds).2
  · rintro ⟨A, hA, n0, hn0, hall⟩
    refine ⟨A, hA, n0, hn0, ?_⟩
    intro n hn
    obtain ⟨K, hrest⟩ := hall n hn
    refine ⟨K, ?_⟩
    exact (dyadicPairCountBounds_iff_quantifiers
      (10 ^ n)
      (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
      (10 ^ n / 2) K A).mpr ⟨hA, hrest⟩

/-- The fixed-pi multiscale hypothesis implies exactly C4, represented by
T7's still-conditional `PiFejerSpectralHypothesis`, with constant `5A+1`. -/
theorem piDyadicMultiscaleHypothesis_implies_C4
    (hmulti : PiDyadicMultiscaleHypothesis) : PiFejerSpectralHypothesis := by
  obtain ⟨A, hA, n0, hn0, hmulti⟩ := hmulti
  refine ⟨5 * A + 1, by linarith, n0, hn0, ?_⟩
  intro n hn
  obtain ⟨K, hbounds⟩ := hmulti n hn
  have hnpos : 1 ≤ n := hn0.trans hn
  have hdouble := two_mul_half_ten_pow n hnpos
  have hpowpos : 0 < 10 ^ n := pow_pos (by norm_num) n
  have hH : 1 ≤ 10 ^ n / 2 := by omega
  have hgeneric := finiteFejerEnergy_le_of_dyadicPairCountBounds
    (10 ^ n)
    (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
    (10 ^ n / 2) K A hH hbounds
  rw [← orderedPair_fejerKernel_eq_piFejerEnergy
    (10 ^ n / 2) (10 ^ n) hH]
  exact hgeneric

/-- C2 is reached from the multiscale hypothesis only by first supplying
T7's Fejer spectral hypothesis. -/
theorem piDyadicMultiscaleHypothesis_implies_C2
    (hmulti : PiDyadicMultiscaleHypothesis) : PiExponentialCollisionC2 := by
  exact piFejerSpectralHypothesis_implies_C2
    (piDyadicMultiscaleHypothesis_implies_C4 hmulti)

/-- Canonical C1 is reached only through the preceding T7-to-C2 step and
T2's accepted collision-to-entropy implication. -/
theorem piDyadicMultiscaleHypothesis_implies_C1
    (hmulti : PiDyadicMultiscaleHypothesis) : PiPositiveFactorEntropyC1 := by
  exact piExponentialCollisionC2_implies_C1
    (piDyadicMultiscaleHypothesis_implies_C2 hmulti)

end DecimalFactorComplexity.DyadicShellFejer

#print axioms DecimalFactorComplexity.DyadicShellFejer.dyadicPairCountBounds_iff_quantifiers
#print axioms DecimalFactorComplexity.DyadicShellFejer.finiteFejerEnergy_le_of_dyadicPairCountBounds
#print axioms DecimalFactorComplexity.DyadicShellFejer.normalizedFiniteFejerEnergy_le_of_dyadicPairCountBounds
#print axioms DecimalFactorComplexity.DyadicShellFejer.piDyadicMultiscaleHypothesis_iff_quantifiers
#print axioms DecimalFactorComplexity.DyadicShellFejer.piDyadicMultiscaleHypothesis_implies_C4
#print axioms DecimalFactorComplexity.DyadicShellFejer.piDyadicMultiscaleHypothesis_implies_C2
#print axioms DecimalFactorComplexity.DyadicShellFejer.piDyadicMultiscaleHypothesis_implies_C1
