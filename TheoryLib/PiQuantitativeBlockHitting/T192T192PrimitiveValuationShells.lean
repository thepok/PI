import TheoryLib.PiQuantitativeBlockHitting.T172T172PositiveLeftExtensionTransport
import TheoryLib.PiQuantitativeBlockHitting.T191T191CentralBoundaryKernelFloor

/-!
# T192: one-time primitive atoms and decimal valuation shells

This module extracts one literal time atom from the primitive prefix sum and
partitions it by the exact power-of-ten valuation of the original boundary
frequency.  The zero shell is then bounded by the ten-point root-grid
projection.  No positive-valuation aggregate is estimated here.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace Theory.PiDigits.T192PrimitiveValuationShells

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.PositiveLeftExtensionTransport
open Theory.PiDigits.BoundaryRootGridProjection
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.T191CentralBoundaryKernelFloor

abbrev phase := Theory.PiDigits.T27.phase
abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- The single time atom whose prefix sum is the primitive boundary Fourier
sum.  It is deliberately written over the uncompressed positive support. -/
def primitiveBoundaryAtom (q A n : ℕ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q,
    centeredBoundaryTerm q A h * phase (tenPrimitivePart h : ℤ) (piOrbit n)

/-- Exact shell of frequencies having decimal valuation `s`. -/
def primitiveValuationShell (q A n s : ℕ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q with tenValuation h = s,
    centeredBoundaryTerm q A h * phase (tenPrimitivePart h : ℤ) (piOrbit n)

/-- A one-time primitive atom is exactly the difference of consecutive
primitive prefix sums. -/
theorem primitiveBoundaryFourierSum_succ_sub_eq_atom (q A n : ℕ) :
    primitiveBoundaryFourierSum q A (n + 1) -
        primitiveBoundaryFourierSum q A n = primitiveBoundaryAtom q A n := by
  rw [primitiveBoundaryFourierSum_eq_support_sum,
    primitiveBoundaryFourierSum_eq_support_sum]
  unfold primitiveBoundaryAtom
  simp only [Theory.PiDigits.T27.exponentialSum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_range_succ]
  ring

private lemma tenValuation_le_decimal_scale
    (k h : ℕ) (hh0 : 1 ≤ h) (hhsupp : h ≤ 2 * 10 ^ k - 1) :
    tenValuation h ≤ k := by
  have hdvd : 10 ^ tenValuation h ∣ h := pow_padicValNat_dvd
  have hpow : 10 ^ tenValuation h ≤ h := Nat.le_of_dvd (by omega) hdvd
  by_contra hnot
  have hkp : k + 1 ≤ tenValuation h := by omega
  have hpow' : 10 ^ (k + 1) ≤ 10 ^ tenValuation h :=
    Nat.pow_le_pow_right (by omega) hkp
  rw [pow_succ] at hpow'
  have hkpow : 0 < 10 ^ k := pow_pos (by omega) _
  omega

/-- At decimal scale `10^k`, the atom is the disjoint sum of shells
`s = 0, ..., k`. -/
theorem primitiveBoundaryAtom_eq_sum_valuationShells (k A n : ℕ) :
    primitiveBoundaryAtom (10 ^ k) A n =
      ∑ s ∈ range (k + 1), primitiveValuationShell (10 ^ k) A n s := by
  classical
  unfold primitiveBoundaryAtom primitiveValuationShell
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' := Finset.mem_Icc.mp hh
  have hv := tenValuation_le_decimal_scale k h hh'.1 hh'.2
  simp [hv]

/-- The layer-difference expression which deletes all frequencies divisible
by one additional power of ten. -/
def boundaryValuationLayerDifference (q A n s : ℕ) : ℂ :=
  divisibleBoundaryPolynomial q (10 ^ s)
      (piOrbit n - (10 ^ s : ℕ) * decimalCylinderCenter q A) -
    divisibleBoundaryPolynomial q (10 ^ (s + 1))
      (10 * piOrbit n - (10 ^ (s + 1) : ℕ) * decimalCylinderCenter q A)

private lemma pow_ten_dvd_iff_le_tenValuation {h s : ℕ} (hh : h ≠ 0) :
    10 ^ s ∣ h ↔ s ≤ tenValuation h := by
  exact Nat.pow_dvd_iff_le_padicValNat (by norm_num) hh

private lemma layerTerm_eq_primitiveTerm
    (q A n s h : ℕ) (hval : tenValuation h = s) :
    (positiveBoundaryCoefficient q h : ℂ) *
        phase ((h / 10 ^ s : ℕ) : ℤ)
          (piOrbit n - (10 ^ s : ℕ) * decimalCylinderCenter q A) =
      centeredBoundaryTerm q A h *
        phase (tenPrimitivePart h : ℤ) (piOrbit n) := by
  have hred := ten_reduction h
  rw [hval] at hred
  have hquot : h / 10 ^ s = tenPrimitivePart h := by
    have heq : 10 ^ s * (h / 10 ^ s) =
        10 ^ s * tenPrimitivePart h := by
      rw [Nat.mul_div_cancel' (show 10 ^ s ∣ h from ⟨_, hred.symm⟩)]
      exact hred.symm
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) s) heq
  rw [hquot]
  unfold centeredBoundaryTerm
  rw [mul_assoc]
  congr 1
  rw [show piOrbit n - (10 ^ s : ℕ) * decimalCylinderCenter q A =
      (-(10 ^ s : ℕ) * decimalCylinderCenter q A) + piOrbit n by ring]
  change Theory.PiDigits.T27.phase (tenPrimitivePart h : ℤ)
      (-((10 ^ s : ℕ) : ℝ) * decimalCylinderCenter q A + piOrbit n) = _
  rw [Theory.PiDigits.T27.phase_add_real]
  congr 1
  unfold Theory.PiDigits.T27.phase
  congr 1
  have hredC : (10 : ℂ) ^ s * (tenPrimitivePart h : ℂ) = (h : ℂ) := by
    exact_mod_cast hred
  push_cast
  calc
    2 * (Real.pi : ℂ) * Complex.I * (tenPrimitivePart h : ℂ) *
          (-(10 : ℂ) ^ s * (decimalCylinderCenter q A : ℂ)) =
        -(2 * (Real.pi : ℂ) * Complex.I *
          ((10 : ℂ) ^ s * (tenPrimitivePart h : ℂ)) *
          (decimalCylinderCenter q A : ℂ)) := by ring
    _ = 2 * (Real.pi : ℂ) * Complex.I * (-(h : ℂ)) *
          (decimalCylinderCenter q A : ℂ) := by rw [hredC]; ring

private lemma nextLayerTerm_eq_currentLayerTerm
    (q A n s h : ℕ) (hdiv : 10 ^ (s + 1) ∣ h) :
    (positiveBoundaryCoefficient q h : ℂ) *
        phase ((h / 10 ^ (s + 1) : ℕ) : ℤ)
          (10 * piOrbit n - (10 ^ (s + 1) : ℕ) * decimalCylinderCenter q A) =
      (positiveBoundaryCoefficient q h : ℂ) *
        phase ((h / 10 ^ s : ℕ) : ℤ)
          (piOrbit n - (10 ^ s : ℕ) * decimalCylinderCenter q A) := by
  obtain ⟨m, rfl⟩ := hdiv
  rw [Nat.mul_div_cancel_left m (pow_pos (by norm_num) (s + 1))]
  rw [show 10 ^ (s + 1) * m / 10 ^ s = 10 * m by
    rw [pow_succ]
    simpa [Nat.mul_assoc] using
      Nat.mul_div_cancel_left (10 * m) (pow_pos (by norm_num) s)]
  unfold phase Theory.PiDigits.T27.phase
  congr 2
  push_cast
  ring

/-- Exact valuation shells are differences of consecutive divisibility
layers; in particular they are not the divisibility layers themselves. -/
theorem primitiveValuationShell_eq_layerDifference
    (q A n s : ℕ) :
    primitiveValuationShell q A n s =
      boundaryValuationLayerDifference q A n s := by
  classical
  let F : ℕ → ℂ := fun h =>
    (positiveBoundaryCoefficient q h : ℂ) *
      phase ((h / 10 ^ s : ℕ) : ℤ)
        (piOrbit n - (10 ^ s : ℕ) * decimalCylinderCenter q A)
  have hshell : primitiveValuationShell q A n s =
      ∑ h ∈ positiveBoundarySupport q with tenValuation h = s, F h := by
    unfold primitiveValuationShell
    apply Finset.sum_congr rfl
    intro h hh
    exact (layerTerm_eq_primitiveTerm q A n s h
      (Finset.mem_filter.mp hh).2).symm
  have hcurrent : divisibleBoundaryPolynomial q (10 ^ s)
        (piOrbit n - (10 ^ s : ℕ) * decimalCylinderCenter q A) =
      ∑ h ∈ positiveBoundarySupport q with s ≤ tenValuation h, F h := by
    unfold divisibleBoundaryPolynomial positiveBoundarySupport
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : h ≠ 0 := by
      simp only [Finset.mem_Icc] at hh
      omega
    have hiff := pow_ten_dvd_iff_le_tenValuation (s := s) hh0
    by_cases hdvd : 10 ^ s ∣ h
    · have hle := hiff.mp hdvd
      simp [hdvd, hle, F]
    · have hnle : ¬s ≤ tenValuation h := by simpa [hiff] using hdvd
      simp [hdvd, hnle]
  have hnext : divisibleBoundaryPolynomial q (10 ^ (s + 1))
        (10 * piOrbit n - (10 ^ (s + 1) : ℕ) * decimalCylinderCenter q A) =
      ∑ h ∈ positiveBoundarySupport q with s + 1 ≤ tenValuation h, F h := by
    unfold divisibleBoundaryPolynomial positiveBoundarySupport
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : h ≠ 0 := by
      simp only [Finset.mem_Icc] at hh
      omega
    have hiff := pow_ten_dvd_iff_le_tenValuation (s := s + 1) hh0
    by_cases hdvd : 10 ^ (s + 1) ∣ h
    · have hle := hiff.mp hdvd
      simp only [if_pos hdvd, if_pos hle]
      exact nextLayerTerm_eq_currentLayerTerm q A n s h hdvd
    · have hnle : ¬s + 1 ≤ tenValuation h := by simpa [hiff] using hdvd
      simp [hdvd, hnle]
  rw [hshell]
  unfold boundaryValuationLayerDifference
  rw [hcurrent, hnext]
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases heq : tenValuation h = s
  · have hle : s ≤ tenValuation h := by omega
    have hnle : ¬s + 1 ≤ tenValuation h := by omega
    simp [heq, hle, hnle]
  · by_cases hle : s ≤ tenValuation h
    · have hnextle : s + 1 ≤ tenValuation h := by omega
      simp [heq, hle, hnextle]
    · have hnnext : ¬s + 1 ≤ tenValuation h := by omega
      simp [heq, hle, hnnext]

/-- The valuation-zero shell retains nine tenths of the positive-frequency
half, equivalently `9/20` of the full boundary minorant. -/
theorem valuationZeroLayerDifference_re_ge
    (q : ℕ) (hq : 1000 ≤ q) (z : ℝ) (hz : |z| ≤ 9 / (22 * q)) :
    (9 / 20 : ℝ) * (boundaryMinorant q z).re ≤
      (divisibleBoundaryPolynomial q 1 z -
        divisibleBoundaryPolynomial q 10 (10 * z)).re := by
  classical
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hzBounds : -(9 / (22 * (q : ℝ))) ≤ z ∧
      z ≤ 9 / (22 * (q : ℝ)) := (abs_le.mp hz)
  have hzqLow : -(9 / 22 : ℝ) ≤ (q : ℝ) * z := by
    calc
      -(9 / 22 : ℝ) = (q : ℝ) * (-(9 / (22 * (q : ℝ)))) := by
        field_simp
      _ ≤ (q : ℝ) * z := mul_le_mul_of_nonneg_left hzBounds.1 hqR.le
  have hzqHigh : (q : ℝ) * z ≤ 9 / 22 := by
    calc
      (q : ℝ) * z ≤ (q : ℝ) * (9 / (22 * (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hzBounds.2 hqR.le
      _ = 9 / 22 := by field_simp
  have hprojOne := rootGridProjection_eq q 1 hq0 (by norm_num) z
  norm_num at hprojOne
  have hfar (r : ℕ) (hr : r ∈ range 10 \ {0}) :
      (boundaryMinorant q ((10 * z + r) / 10)).re ≤ 0 := by
    have hrRange : r < 10 := Finset.mem_range.mp (Finset.mem_sdiff.mp hr).1
    have hr0 : r ≠ 0 := by simpa using (Finset.mem_sdiff.mp hr).2
    have hrOne : 1 ≤ r := by omega
    let x : ℝ := z + (r : ℝ) / 10 + 1 / (2 * q)
    have hx0 : 0 ≤ x := by
      have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hrOne
      have hqx0 : 0 ≤ (q : ℝ) * x := by
        dsimp [x]
        field_simp
        nlinarith
      exact (mul_nonneg_iff_of_pos_left hqR).mp hqx0
    have hx1 : x < 1 := by
      have hrR : (r : ℝ) ≤ 9 := by exact_mod_cast (show r ≤ 9 by omega)
      have hqLower : (1000 : ℝ) ≤ q := by exact_mod_cast hq
      have hqx : (q : ℝ) * x < (q : ℝ) := by
        dsimp [x]
        field_simp
        nlinarith
      apply lt_of_mul_lt_mul_left
      · simpa using hqx
      · exact hqR.le
    have hxOutside : x ∉ Set.Ico (0 : ℝ) (0 + (q : ℝ)⁻¹) := by
      have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hrOne
      have hqx : (1 : ℝ) ≤ (q : ℝ) * x := by
        have hqr : (q : ℝ) ≤ (q : ℝ) * r := by
          simpa using mul_le_mul_of_nonneg_left hrR hqR.le
        have hqLower : (1000 : ℝ) ≤ q := by exact_mod_cast hq
        dsimp [x]
        field_simp
        ring_nf
        nlinarith
      have hxLower : (q : ℝ)⁻¹ ≤ x := by
        rw [inv_eq_one_div]
        exact (div_le_iff₀ hqR).2 (by simpa [mul_comm] using hqx)
      exact fun hxMem => (not_lt_of_ge hxLower) (by simpa using hxMem.2)
    have hout := boundaryMinorant_re_nonpos_outside q hq0 x 0
      ⟨hx0, hx1⟩ (by norm_num)
      (by
        rw [zero_add, inv_le_one₀ hqR]
        exact_mod_cast (show 1 ≤ q by omega))
      hxOutside
    convert hout using 1
    dsimp [x]
    congr 2
    field_simp
    ring
  let f : ℕ → ℝ := fun r => (boundaryMinorant q ((10 * z + r) / 10)).re
  have hfarSum : ∑ r ∈ range 10 \ {0}, f r ≤ 0 := by
    exact Finset.sum_nonpos fun r hr => hfar r hr
  have hsum : (∑ r ∈ range 10,
      (boundaryMinorant q ((10 * z + r) / 10)).re) ≤
      (boundaryMinorant q z).re := by
    change (∑ r ∈ range 10, f r) ≤ _
    rw [sum_eq_add_sum_diff_singleton 0 f (fun h => (h (by simp)).elim)]
    have hf0 : f 0 = (boundaryMinorant q z).re := by
      dsimp [f]
      congr 2
      ring
    rw [hf0]
    linarith
  have hprojTen := rootGridProjection_eq q 10 hq0 (by norm_num) (10 * z)
  have hprojTen' : boundaryZeroCoefficient q +
        2 * (divisibleBoundaryPolynomial q 10 (10 * z)).re ≤
      (1 / 10 : ℝ) * (boundaryMinorant q z).re := by
    rw [hprojTen]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  norm_num [Complex.sub_re]
  nlinarith

/-- Coordinate form of the valuation-zero estimate for the actual primitive
atom.  The hypothesis names the normalized displacement `y` explicitly. -/
theorem primitiveValuationShell_zero_re_ge
    (k A n : ℕ) (hk : 3 ≤ k) (y : ℝ)
    (hy : |y| ≤ 9 / 22)
    (hyCoord : piOrbit n - decimalCylinderCenter (10 ^ k) A =
      y / (10 ^ k : ℕ)) :
    (9 / 20 : ℝ) *
        (boundaryMinorant (10 ^ k) (y / (10 ^ k : ℕ))).re ≤
      (primitiveValuationShell (10 ^ k) A n 0).re := by
  let q : ℕ := 10 ^ k
  have hq : 1000 ≤ q := by
    calc
      1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqR : (0 : ℝ) < q := by positivity
  have hz : |y / (q : ℕ)| ≤ 9 / (22 * (q : ℕ)) := by
    rw [abs_div, abs_of_pos hqR]
    calc
      |y| / (q : ℝ) ≤ (9 / 22 : ℝ) / q :=
        div_le_div_of_nonneg_right hy hqR.le
      _ = 9 / (22 * (q : ℝ)) := by ring
  have hzero := valuationZeroLayerDifference_re_ge q hq (y / q) hz
  rw [primitiveValuationShell_eq_layerDifference]
  dsimp [boundaryValuationLayerDifference]
  norm_num
  change _ ≤ (divisibleBoundaryPolynomial q 1
      (piOrbit n - decimalCylinderCenter q A) -
    divisibleBoundaryPolynomial q 10
      (10 * piOrbit n - 10 * decimalCylinderCenter q A)).re
  rw [show piOrbit n - decimalCylinderCenter q A = y / q by
    simpa [q] using hyCoord]
  rw [show 10 * piOrbit n - 10 * decimalCylinderCenter q A =
      10 * (y / q) by
    rw [← show piOrbit n - decimalCylinderCenter q A = y / q by
      simpa [q] using hyCoord]
    ring]
  simpa [q] using hzero

/-- T191 turns the structural `9/20` retention into an explicit strict
valuation-zero floor throughout the central chamber. -/
theorem primitiveValuationShell_zero_re_gt
    (k A n : ℕ) (hk : 3 ≤ k) (y : ℝ)
    (hy : |y| ≤ 9 / 22)
    (hyCoord : piOrbit n - decimalCylinderCenter (10 ^ k) A =
      y / (10 ^ k : ℕ)) :
    (9 / 20 : ℝ) * (4859 / 10000 : ℝ) <
      (primitiveValuationShell (10 ^ k) A n 0).re := by
  have hfloor := boundaryMinorant_re_gt_4859_div_10000 k hk y hy
  have hretained := primitiveValuationShell_zero_re_ge k A n hk y hy hyCoord
  exact (mul_lt_mul_of_pos_left hfloor (by norm_num)).trans_le hretained

end Theory.PiDigits.T192PrimitiveValuationShells

#print axioms
  Theory.PiDigits.T192PrimitiveValuationShells.primitiveBoundaryFourierSum_succ_sub_eq_atom
#print axioms
  Theory.PiDigits.T192PrimitiveValuationShells.primitiveBoundaryAtom_eq_sum_valuationShells
#print axioms
  Theory.PiDigits.T192PrimitiveValuationShells.primitiveValuationShell_eq_layerDifference
#print axioms
  Theory.PiDigits.T192PrimitiveValuationShells.valuationZeroLayerDifference_re_ge
#print axioms
  Theory.PiDigits.T192PrimitiveValuationShells.primitiveValuationShell_zero_re_ge
#print axioms
  Theory.PiDigits.T192PrimitiveValuationShells.primitiveValuationShell_zero_re_gt
