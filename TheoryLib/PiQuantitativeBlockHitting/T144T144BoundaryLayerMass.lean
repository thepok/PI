import TheoryLib.PiQuantitativeBlockHitting.T143T143BoundaryEndpointLayers
import TheoryLib.PiQuantitativeBlockHitting.T129T129BoundaryKernelNormalizedComparison

/-!
# T144: exact masses of the decimal boundary layers

This module computes the total positive coefficient mass on frequencies
divisible by a decimal layer spacing.  It contains no orbit estimate or
interval consumer.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.BoundaryLayerMass

open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.BoundaryCoefficientAbel
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison

/-- Total positive-frequency T128 coefficient mass on the `d`-spaced layer. -/
def boundaryLayerMass (q d : ℕ) : ℝ :=
  ∑ i ∈ range ((2 * q - 1) / d),
    positiveBoundaryCoefficient q (d * (i + 1))

private lemma sum_range_cast (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ)) = n * (n - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

private lemma sum_range_cast_sq (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ) ^ 2) =
      n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

private lemma sum_range_cast_cube (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ) ^ 3) =
      (n * (n - 1) / 2) ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

private lemma layer_quotient (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    (2 * (d * n) - 1) / d = 2 * n - 1 := by
  have hprod : (2 * n - 1) * d + d = 2 * (d * n) := by
    calc
      (2 * n - 1) * d + d = (2 * n - 1) * d + 1 * d := by simp
      _ = (2 * n - 1 + 1) * d := (Nat.add_mul _ _ _).symm
      _ = 2 * n * d := by rw [show 2 * n - 1 + 1 = 2 * n by omega]
      _ = 2 * (d * n) := by ring
  have hfull : (2 * n) * d = 2 * (d * n) := by ring
  apply Nat.div_eq_of_lt_le
  · omega
  · have hrhs : (2 * n - 1 + 1) * d = 2 * (d * n) := by
      calc
        (2 * n - 1 + 1) * d = (2 * n - 1) * d + 1 * d := Nat.add_mul _ _ _
        _ = (2 * n - 1) * d + d := by simp
        _ = 2 * (d * n) := hprod
    rw [hrhs]
    omega

set_option maxHeartbeats 800000 in
-- The exact cubic layer sum requires repeated normalization of three symbolic
-- power sums; the scoped budget does not affect any later declaration.
/-- Exact layer mass whenever `q = d*n`.  Decimal layers are the special case
`q=10^k`, `d=10^s`, `n=10^(k-s)`. -/
theorem boundaryLayerMass_eq
    (q d n : ℕ) (hq : 1 < q) (hd : 0 < d) (hn : 0 < n)
    (hqd : q = d * n) :
    boundaryLayerMass q d =
      ((1 - Real.cos (Real.pi / q)) * (q : ℝ) ^ 2 / d -
        boundaryZeroCoefficient q) / 2 := by
  subst q
  have hdn : 1 < d * n := hq
  rw [boundaryLayerMass, layer_quotient d n hd hn]
  rw [← sum_range_add_sum_Ico
    (fun i => positiveBoundaryCoefficient (d * n) (d * (i + 1)))
    (show n ≤ 2 * n - 1 by omega)]
  have hfirst :
      (∑ i ∈ range n,
        positiveBoundaryCoefficient (d * n) (d * (i + 1))) =
      ∑ i ∈ range n,
        ((1 - Real.cos (Real.pi / (d * n))) *
            (4 * ((d * n : ℕ) : ℝ) ^ 3 + 2 * (d * n : ℕ) -
              6 * (d * n : ℕ) * ((d * (i + 1) : ℕ) : ℝ) ^ 2 +
              3 * ((d * (i + 1) : ℕ) : ℝ) ^ 3 - 3 * (d * (i + 1) : ℕ)) /
                (6 * ((d * n : ℕ) : ℝ) ^ 2) +
          (3 * ((d * (i + 1) : ℕ) : ℝ) - 2 * (d * n : ℕ)) /
            (2 * ((d * n : ℕ) : ℝ) ^ 2)) := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have hle : d * (i + 1) ≤ d * n :=
      Nat.mul_le_mul_left d (show i + 1 ≤ n by omega)
    have hsupp : d * (i + 1) ≤ 2 * (d * n) - 1 := by
      have hqtop : d * n ≤ 2 * (d * n) - 1 := by omega
      exact hle.trans hqtop
    rw [positiveBoundaryCoefficient_eq_piecewise (d * n) (d * (i + 1))
      hdn (by positivity) hsupp, if_pos hle]
    push_cast
    ring
  rw [hfirst]
  have htail :
      (∑ i ∈ Ico n (2 * n - 1),
        positiveBoundaryCoefficient (d * n) (d * (i + 1))) =
      ∑ i ∈ Ico n (2 * n - 1),
        ((1 - Real.cos (Real.pi / (d * n))) *
            (2 * ((d * n : ℕ) : ℝ) - ((d * (i + 1) : ℕ) : ℝ) - 1) *
            (2 * ((d * n : ℕ) : ℝ) - ((d * (i + 1) : ℕ) : ℝ)) *
            (2 * ((d * n : ℕ) : ℝ) - ((d * (i + 1) : ℕ) : ℝ) + 1) /
              (6 * ((d * n : ℕ) : ℝ) ^ 2) +
          (2 * ((d * n : ℕ) : ℝ) - ((d * (i + 1) : ℕ) : ℝ)) /
            (2 * ((d * n : ℕ) : ℝ) ^ 2)) := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_Ico.mp hi
    have hnot : ¬ d * (i + 1) ≤ d * n :=
      not_le.mpr ((Nat.mul_lt_mul_left hd).mpr (by omega))
    have hsupp : d * (i + 1) ≤ 2 * (d * n) - 1 := by
      have hmul := Nat.mul_le_mul_left d (show i + 1 ≤ 2 * n - 1 by omega)
      have htop : d * (2 * n - 1) ≤ 2 * (d * n) - 1 := by
        have hprod : (2 * n - 1) * d + d = 2 * (d * n) := by
          calc
            (2 * n - 1) * d + d = (2 * n - 1) * d + 1 * d := by simp
            _ = (2 * n - 1 + 1) * d := (Nat.add_mul _ _ _).symm
            _ = 2 * n * d := by rw [show 2 * n - 1 + 1 = 2 * n by omega]
            _ = 2 * (d * n) := by ring
        rw [Nat.mul_comm d]
        omega
      exact hmul.trans htop
    rw [positiveBoundaryCoefficient_eq_piecewise (d * n) (d * (i + 1))
      hdn (by positivity) hsupp, if_neg hnot]
    push_cast
    ring
  rw [htail]
  rw [boundaryZeroCoefficient_eq (d * n) (by positivity)]
  -- Both finite pieces are cubic polynomials.  Reduce the tail interval to
  -- range sums and use the three elementary power-sum identities above.
  rw [sum_Ico_eq_sub _ (show n ≤ 2 * n - 1 by omega)]
  push_cast
  ring_nf
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring_nf
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring_nf
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring_nf
  simp only [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [sum_range_cast, sum_range_cast_sq, sum_range_cast_cube]
  simp [Finset.sum_const, nsmul_eq_mul]
  rw [Nat.cast_sub (show 1 ≤ n * 2 by omega)]
  push_cast
  field_simp
  ring

/-- Exact mass of the `s`th decimal valuation layer at scale `q=10^k`. -/
theorem boundaryLayerMass_pow_ten_eq
    (k s : ℕ) (hs0 : 1 ≤ s) (hsk : s ≤ k) :
    boundaryLayerMass (10 ^ k) (10 ^ s) =
      ((1 - Real.cos (Real.pi / (10 ^ k : ℕ))) * ((10 ^ k : ℕ) : ℝ) ^ 2 /
          (10 ^ s : ℕ) - boundaryZeroCoefficient (10 ^ k)) / 2 := by
  apply boundaryLayerMass_eq (10 ^ k) (10 ^ s) (10 ^ (k - s))
  · exact one_lt_pow₀ (by norm_num) (by omega)
  · positivity
  · positivity
  · rw [← pow_add, Nat.add_sub_of_le hsk]

end Theory.PiDigits.BoundaryLayerMass

#print axioms Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass_eq
#print axioms Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass_pow_ten_eq
