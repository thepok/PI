import TheoryLib.PiQuantitativeBlockHitting.T151T151BoundaryProjectedLayerFloor
import TheoryLib.PiQuantitativeBlockHitting.T176T176SignedBlockBellmanTransport
import TheoryLib.PiQuantitativeBlockHitting.T192T192PrimitiveValuationShells

/-!
# T193: positive-valuation shell aggregate and central one-time seed

This module closes the deterministic central one-time seed.  It estimates
all strictly positive decimal-valuation shells together, combines them with
T192's zero shell, and translates the atom bound into T176's native unit-block
capital.  It contains no recurrence or irrationality input.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace Theory.PiDigits.T193PositiveValuationShellAggregate

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryRootGridProjection
open Theory.PiDigits.BoundaryProjectedLayerFloor
open Theory.PiDigits.BoundaryEndpointLayers
open Theory.PiDigits.BoundaryLayerMass
open Theory.PiDigits.BoundaryLayerScalarBounds
open Theory.PiDigits.BoundaryEndpointContraction
open Theory.PiDigits.T192PrimitiveValuationShells
open Theory.PiDigits.SignedBlockBellmanTransport

abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- Total positive coefficient mass over every nonzero decimal valuation
available at scale `10^k`. -/
def positiveValuationLayerMassSum (k : ℕ) : ℝ :=
  ∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ s)

/-- Sum of the exact positive-valuation primitive shells at one orbit time. -/
def positiveValuationShellSum (k A n : ℕ) : ℂ :=
  ∑ s ∈ Icc 1 k, primitiveValuationShell (10 ^ k) A n s

private lemma inverse_pow_ten_sum_le_one_ninth (k : ℕ) :
    (∑ s ∈ Icc 1 k, (1 : ℝ) / (10 ^ s : ℕ)) ≤ 1 / 9 := by
  have hgeom := geom_sum_Ico_le_of_lt_one
    (m := 1) (n := k + 1) (x := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
  rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by
    ext s
    simp]
  convert hgeom using 1 <;> norm_num [div_pow]

/-- The full positive-valuation mass budget is strictly below `5/18`. -/
theorem positiveValuationLayerMassSum_lt_five_div_eighteen
    (k : ℕ) (hk : 3 ≤ k) :
    positiveValuationLayerMassSum k < 5 / 18 := by
  let q : ℕ := 10 ^ k
  let delta : ℝ := 1 - Real.cos (Real.pi / q)
  let alpha : ℝ := boundaryZeroCoefficient q
  have hq : 1000 ≤ q := by
    calc
      1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq0 : 0 < q := by omega
  have halpha : 0 ≤ alpha := by
    dsimp [alpha]
    exact (boundaryZeroCoefficient_lower q hq0).trans' (by positivity)
  have hsum := inverse_pow_ten_sum_le_one_ninth k
  have hlayer : positiveValuationLayerMassSum k ≤
      delta * (q : ℝ) ^ 2 / 2 *
        (∑ s ∈ Icc 1 k, (1 : ℝ) / (10 ^ s : ℕ)) := by
    unfold positiveValuationLayerMassSum
    calc
      (∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ s)) =
          ∑ s ∈ Icc 1 k,
            (delta * (q : ℝ) ^ 2 / (10 ^ s : ℕ) - alpha) / 2 := by
        apply sum_congr rfl
        intro s hs
        have hs' := mem_Icc.mp hs
        rw [boundaryLayerMass_pow_ten_eq k s hs'.1 hs'.2]
      _ ≤ ∑ s ∈ Icc 1 k,
            delta * (q : ℝ) ^ 2 / 2 * ((1 : ℝ) / (10 ^ s : ℕ)) := by
        apply sum_le_sum
        intro s hs
        have hpow : (0 : ℝ) < (10 ^ s : ℕ) := by positivity
        dsimp [alpha] at halpha
        field_simp
        nlinarith
      _ = _ := by rw [mul_sum]
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    exact sub_nonneg.mpr (Real.cos_le_one _)
  have hcoef : 0 ≤ delta * (q : ℝ) ^ 2 / 2 := by positivity
  have hbudget : positiveValuationLayerMassSum k ≤
      delta * (q : ℝ) ^ 2 / 18 := by
    have := mul_le_mul_of_nonneg_left hsum hcoef
    nlinarith [hlayer]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / q)
  have hpiSq : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hqR : (0 : ℝ) < q := by positivity
  have hdelta : delta * (q : ℝ) ^ 2 < 5 := by
    dsimp [delta]
    field_simp at hcos ⊢
    nlinarith [sq_pos_of_pos hqR]
  nlinarith

private lemma last_decimal_layer_mass_eq_zero (k : ℕ) :
    boundaryLayerMass (10 ^ k) (10 ^ (k + 1)) = 0 := by
  unfold boundaryLayerMass
  have hdiv : (2 * 10 ^ k - 1) / 10 ^ (k + 1) = 0 := by
    apply Nat.div_eq_of_lt
    rw [pow_succ]
    have hkpos : 0 < 10 ^ k := by positivity
    omega
  rw [hdiv]
  simp

private lemma shifted_layer_mass_sum_eq_tail (k : ℕ) (hk : 1 ≤ k) :
    (∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ (s + 1))) =
      positiveValuationLayerMassSum k - boundaryLayerMass (10 ^ k) 10 := by
  let M : ℕ → ℝ := fun s => boundaryLayerMass (10 ^ k) (10 ^ s)
  have hreindex : (∑ s ∈ Icc 1 k, M (s + 1)) =
      ∑ r ∈ Icc 2 (k + 1), M r := by
    apply Finset.sum_bij (fun s _ => s + 1)
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    · intro a ha b hb hab
      omega
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      refine ⟨r - 1, ?_, by omega⟩
      simp only [Finset.mem_Icc]
      omega
    · intro s hs
      rfl
  rw [hreindex]
  have hlast : M (k + 1) = 0 := last_decimal_layer_mass_eq_zero k
  have htop : k + 1 ∈ Finset.Icc 2 (k + 1) := by simp [hk]
  rw [sum_eq_add_sum_diff_singleton (s := Finset.Icc 2 (k + 1))
    (f := M) (i := k + 1) (fun h => (h htop).elim), hlast, zero_add]
  have hset : Finset.Icc 2 (k + 1) \ {k + 1} = Finset.Icc 2 k := by
    ext s
    simp only [mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
    omega
  rw [hset]
  unfold positiveValuationLayerMassSum
  have hone : 1 ∈ Finset.Icc 1 k := by simp [hk]
  rw [sum_eq_add_sum_diff_singleton (s := Finset.Icc 1 k)
    (f := M) (i := 1) (fun h => (h hone).elim)]
  have hset' : Finset.Icc 1 k \ {1} = Finset.Icc 2 k := by
    ext s
    simp only [mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
    omega
  rw [hset']
  dsimp [M]
  norm_num

private lemma first_layer_sum_gt
    (k : ℕ) (hk : 3 ≤ k) (t : ℕ → ℝ) :
    -positiveValuationLayerMassSum k + 50109 / 200000 <
      ∑ s ∈ Icc 1 k,
        (divisibleBoundaryPolynomial (10 ^ k) (10 ^ s) (t s)).re := by
  let q : ℕ := 10 ^ k
  let M : ℕ → ℝ := fun s => boundaryLayerMass q (10 ^ s)
  let L : ℕ → ℝ := fun s =>
    (divisibleBoundaryPolynomial q (10 ^ s) (t s)).re
  have hq : 1000 ≤ q := by
    calc
      1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqR : (1000 : ℝ) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := by positivity
  have hqSq : (1000000 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have halphaRaw := boundaryZeroCoefficient_lt_twelve_div_five_mul q hq
  have halpha : boundaryZeroCoefficient q < 3 / 1250 := by
    calc
      boundaryZeroCoefficient q < 12 / (5 * (q : ℝ)) := halphaRaw
      _ ≤ 3 / 1250 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * q)).2
        nlinarith
  have herr : 40 / (q : ℝ) ^ 2 + 4400 / (q : ℝ) ^ 2 ≤ 111 / 25000 := by
    field_simp
    nlinarith [sq_pos_of_pos hqPos]
  have hL1 := divisibleBoundaryPolynomial_re_gt q 10 hq (by norm_num) (t 1)
  have hL2 := divisibleBoundaryPolynomial_re_gt q 100 hq (by norm_num) (t 2)
  have hL1' : -(193 / 20000 : ℝ) - 40 / (q : ℝ) ^ 2 -
      boundaryZeroCoefficient q / 2 < L 1 := by
    dsimp [L]
    convert hL1 using 1 <;> ring
  have hL2' : -(193 / 200000 : ℝ) - 4400 / (q : ℝ) ^ 2 -
      boundaryZeroCoefficient q / 2 < L 2 := by
    dsimp [L]
    convert hL2 using 1 <;> ring
  have hM1 := boundaryLayerMass_ten_gt k hk
  have hM2 := boundaryLayerMass_hundred_gt k hk
  change 49 / 200 < M 1 at hM1
  change 23 / 1000 < M 2 at hM2
  have hpair : -(M 1 + M 2) + 50109 / 200000 < L 1 + L 2 := by
    nlinarith [hL1', hL2']
  let S : Finset ℕ := (Icc 1 k \ {1}) \ {2}
  have hrest : -(∑ s ∈ S, M s) ≤ ∑ s ∈ S, L s := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc 1 k := (mem_sdiff.mp (mem_sdiff.mp hs).1).1
    have hnorm := boundaryLayerPolynomial_norm_le_mass q s hq (t s)
    have hre : -‖boundaryLayerPolynomial q s (t s)‖ ≤
        (boundaryLayerPolynomial q s (t s)).re := by
      have habs := Complex.abs_re_le_norm (boundaryLayerPolynomial q s (t s))
      exact (neg_le_neg habs).trans (neg_abs_le _)
    rw [boundaryLayerPolynomial_eq_divisible] at hnorm hre
    exact (neg_le_neg hnorm).trans hre
  have h1 : 1 ∈ Finset.Icc 1 k := by simp [show 1 ≤ k by omega]
  have h2 : 2 ∈ Finset.Icc 1 k := by simp [show 2 ≤ k by omega]
  have h2rest : 2 ∈ Finset.Icc 1 k \ {1} := by simp [h2]
  have hsumL : (∑ s ∈ Finset.Icc 1 k, L s) =
      L 1 + L 2 + ∑ s ∈ S, L s := by
    rw [sum_eq_add_sum_diff_singleton (s := Finset.Icc 1 k) (f := L) (i := 1)
      (fun h => (h h1).elim)]
    rw [sum_eq_add_sum_diff_singleton (s := Finset.Icc 1 k \ {1}) (f := L) (i := 2)
      (fun h => (h h2rest).elim)]
    dsimp [S]
    ring
  have hsumM : positiveValuationLayerMassSum k =
      M 1 + M 2 + ∑ s ∈ S, M s := by
    unfold positiveValuationLayerMassSum
    change (∑ s ∈ Finset.Icc 1 k, M s) = _
    rw [sum_eq_add_sum_diff_singleton (s := Finset.Icc 1 k) (f := M) (i := 1)
      (fun h => (h h1).elim)]
    rw [sum_eq_add_sum_diff_singleton (s := Finset.Icc 1 k \ {1}) (f := M) (i := 2)
      (fun h => (h h2rest).elim)]
    dsimp [S]
    ring
  rw [hsumL, hsumM]
  linarith

/-- All strictly positive valuation shells have a uniform aggregate floor. -/
theorem positiveValuationShellSum_re_gt
    (k A n : ℕ) (hk : 3 ≤ k) :
    -(108019 / 1800000 : ℝ) < (positiveValuationShellSum k A n).re := by
  let q : ℕ := 10 ^ k
  let c : ℝ := decimalCylinderCenter q A
  let t₁ : ℕ → ℝ := fun s => piOrbit n - (10 ^ s : ℕ) * c
  let t₂ : ℕ → ℝ := fun s =>
    10 * piOrbit n - (10 ^ (s + 1) : ℕ) * c
  have hq : 1000 ≤ q := by
    calc
      1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hfirst := first_layer_sum_gt k hk t₁
  have hsecond :
      (∑ s ∈ Icc 1 k,
        (divisibleBoundaryPolynomial q (10 ^ (s + 1)) (t₂ s)).re) ≤
      ∑ s ∈ Icc 1 k, boundaryLayerMass q (10 ^ (s + 1)) := by
    apply Finset.sum_le_sum
    intro s hs
    have hnorm := boundaryLayerPolynomial_norm_le_mass q (s + 1) hq (t₂ s)
    rw [boundaryLayerPolynomial_eq_divisible] at hnorm
    exact (Complex.re_le_norm _).trans hnorm
  have hshift := shifted_layer_mass_sum_eq_tail k (by omega)
  have hmass := positiveValuationLayerMassSum_lt_five_div_eighteen k hk
  have hm1 := boundaryLayerMass_ten_gt k hk
  have hshell : (positiveValuationShellSum k A n).re =
      (∑ s ∈ Icc 1 k,
        (divisibleBoundaryPolynomial q (10 ^ s) (t₁ s)).re) -
      ∑ s ∈ Icc 1 k,
        (divisibleBoundaryPolynomial q (10 ^ (s + 1)) (t₂ s)).re := by
    unfold positiveValuationShellSum
    simp_rw [primitiveValuationShell_eq_layerDifference]
    unfold boundaryValuationLayerDifference
    rw [Complex.re_sum]
    simp_rw [Complex.sub_re]
    rw [sum_sub_distrib]
  rw [hshell]
  dsimp [q] at hfirst hsecond hshift hmass hm1 ⊢
  rw [hshift] at hsecond
  nlinarith

/-- A central normalized coordinate gives a strictly positive full one-time
primitive atom. -/
theorem primitiveBoundaryAtom_re_gt_7139_div_45000
    (k A n : ℕ) (hk : 3 ≤ k) (y : ℝ)
    (hy : |y| ≤ 9 / 22)
    (hyCoord : piOrbit n - decimalCylinderCenter (10 ^ k) A =
      y / (10 ^ k : ℕ)) :
    (7139 / 45000 : ℝ) < (primitiveBoundaryAtom (10 ^ k) A n).re := by
  have hzero := primitiveValuationShell_zero_re_gt k A n hk y hy hyCoord
  have hpositive := positiveValuationShellSum_re_gt k A n hk
  have hdecomp := primitiveBoundaryAtom_eq_sum_valuationShells k A n
  have h0mem : 0 ∈ range (k + 1) := by simp
  have hset : range (k + 1) \ {0} = Finset.Icc 1 k := by
    ext s
    simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hsplit : primitiveBoundaryAtom (10 ^ k) A n =
      primitiveValuationShell (10 ^ k) A n 0 +
        positiveValuationShellSum k A n := by
    rw [hdecomp]
    rw [sum_eq_add_sum_diff_singleton (s := range (k + 1))
      (f := fun s => primitiveValuationShell (10 ^ k) A n s) (i := 0)
      (fun h => (h h0mem).elim)]
    rw [hset]
    rfl
  rw [hsplit]
  simp only [Complex.add_re]
  norm_num at hzero hpositive ⊢
  linarith

/-- Native T176 unit-block capital produced by the deterministic central
one-time seed. -/
theorem central_unitBlock_surplus_gt_three_div_twenty
    (k A n : ℕ) (hk : 3 ≤ k) (y : ℝ)
    (hy : |y| ≤ 9 / 22)
    (hyCoord : piOrbit n - decimalCylinderCenter (10 ^ k) A =
      y / (10 ^ k : ℕ)) :
    (3 / 20 : ℝ) * (10 ^ k : ℕ) <
      (10 ^ k : ℕ) *
          (primitiveBoundaryFourierBlockSum (10 ^ k) A n 1).re -
        signedBlockPotential (10 ^ k) := by
  have hatom := primitiveBoundaryAtom_re_gt_7139_div_45000
    k A n hk y hy hyCoord
  have hblock : primitiveBoundaryFourierBlockSum (10 ^ k) A n 1 =
      primitiveBoundaryAtom (10 ^ k) A n := by
    unfold primitiveBoundaryFourierBlockSum
    norm_num
    exact primitiveBoundaryFourierSum_succ_sub_eq_atom (10 ^ k) A n
  rw [hblock]
  have hq : 1000 ≤ 10 ^ k := by
    calc
      1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqR : (1000 : ℝ) ≤ (10 ^ k : ℕ) := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < (10 ^ k : ℕ) := by positivity
  unfold signedBlockPotential
  push_cast
  have hmul := mul_lt_mul_of_pos_left hatom hqPos
  have hgap : 7 / (3 * ((10 ^ k : ℕ) : ℝ)) <
      (389 / 45000 : ℝ) * (10 ^ k : ℕ) := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * (10 ^ k : ℕ))).2
    have hqSq : (1000000 : ℝ) ≤ ((10 ^ k : ℕ) : ℝ) ^ 2 := by nlinarith
    field_simp
    nlinarith
  push_cast at hmul hgap
  calc
    (3 / 20 : ℝ) * (10 : ℝ) ^ k =
        (10 : ℝ) ^ k * (7139 / 45000) -
          (389 / 45000) * (10 : ℝ) ^ k := by ring
    _ < (10 : ℝ) ^ k *
          (primitiveBoundaryAtom (10 ^ k) A n).re -
          (389 / 45000) * (10 : ℝ) ^ k := sub_lt_sub_right hmul _
    _ < (10 : ℝ) ^ k *
          (primitiveBoundaryAtom (10 ^ k) A n).re -
          7 / (3 * (10 : ℝ) ^ k) := sub_lt_sub_left hgap _

end Theory.PiDigits.T193PositiveValuationShellAggregate

#print axioms
  Theory.PiDigits.T193PositiveValuationShellAggregate.positiveValuationLayerMassSum_lt_five_div_eighteen
#print axioms
  Theory.PiDigits.T193PositiveValuationShellAggregate.positiveValuationShellSum_re_gt
#print axioms
  Theory.PiDigits.T193PositiveValuationShellAggregate.primitiveBoundaryAtom_re_gt_7139_div_45000
#print axioms
  Theory.PiDigits.T193PositiveValuationShellAggregate.central_unitBlock_surplus_gt_three_div_twenty
