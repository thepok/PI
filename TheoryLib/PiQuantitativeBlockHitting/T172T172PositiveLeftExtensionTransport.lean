import TheoryLib.PiQuantitativeBlockHitting.T156T156BoundaryNaturalThresholdClosure

/-!
# T172: positive left-extension transport

This isolated module records the literal primitive-frequency form of the
decimal left-extension calculation.  The transport statements are valid at
an arbitrary fixed horizon `N`; only the final T156 consumer specializes to
the natural horizon.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.PositiveLeftExtensionTransport

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.LongLagBlockCollisionDecay.T16

abbrev phase := Theory.PiDigits.T27.phase

/-- Coefficient gained when the ten left children are projected to their
zero digit-character sector. -/
def leftExtensionCoefficientDefect (q h : ℕ) : ℝ :=
  10 * positiveBoundaryCoefficient (10 * q) (10 * h) -
    positiveBoundaryCoefficient q h

/-- Literal primitive-frequency remainder in the zero-sector transport law. -/
def leftExtensionRemainder (q A N : ℕ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q,
    (leftExtensionCoefficientDefect q h : ℂ) *
      phase (-(h : ℤ)) (decimalCylinderCenter q A) *
      exponentialSum piOrbit N (tenPrimitivePart h : ℤ)

/-- Primitive compression can equivalently be written as one sum over the
uncompressed positive support, with the primitive frequency in the orbit
sum. -/
theorem primitiveBoundaryFourierSum_eq_support_sum (q A N : ℕ) :
    primitiveBoundaryFourierSum q A N =
      ∑ h ∈ positiveBoundarySupport q,
        centeredBoundaryTerm q A h *
          exponentialSum piOrbit N (tenPrimitivePart h : ℤ) := by
  classical
  have hmaps : ∀ h ∈ positiveBoundarySupport q,
      tenPrimitivePart h ∈ primitiveBoundarySupport q := by
    intro h hh
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := positiveBoundarySupport q) (t := primitiveBoundarySupport q)
    (g := tenPrimitivePart) hmaps
    (fun h => centeredBoundaryTerm q A h *
      exponentialSum piOrbit N (tenPrimitivePart h : ℤ))
  unfold primitiveBoundaryFourierSum primitiveRayCoefficient primitiveBoundaryFiber
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  rw [(Finset.mem_filter.mp hh).2]

private lemma phase_neg_nat_grid_sum
    (h d : ℕ) (hd : 0 < d) (t : ℝ) :
    (∑ r ∈ range d, phase (-(h : ℤ)) ((t + r) / d)) =
      if d ∣ h then (d : ℂ) * phase (-((h / d : ℕ) : ℤ)) t else 0 := by
  classical
  have hpositive :
      (∑ r ∈ range d, phase (h : ℤ) ((t + r) / d)) =
        if d ∣ h then (d : ℂ) * phase ((h / d : ℕ) : ℤ) t else 0 := by
    by_cases hdiv : d ∣ h
    · obtain ⟨m, rfl⟩ := hdiv
      simp only [if_pos (dvd_mul_right d m)]
      have hquot : d * m / d = m := Nat.mul_div_cancel_left m hd
      have hterm (r : ℕ) :
          phase ((d * m : ℕ) : ℤ) ((t + r) / d) = phase (m : ℤ) t := by
        have hreduce :
            phase ((d * m : ℕ) : ℤ) ((t + r) / d) =
              phase (m : ℤ) (t + r) := by
          unfold phase Theory.PiDigits.T27.phase
          congr 1
          have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
          push_cast
          field_simp
        rw [hreduce]
        change Theory.PiDigits.T27.phase (m : ℤ) (t + (r : ℝ)) =
          Theory.PiDigits.T27.phase (m : ℤ) t
        rw [Theory.PiDigits.T27.phase_add_real]
        have hinter : phase (m : ℤ) (r : ℝ) = 1 := by
          unfold phase Theory.PiDigits.T27.phase
          convert Complex.exp_int_mul_two_pi_mul_I (m * r : ℤ) using 1
          push_cast
          ring_nf
        change Theory.PiDigits.T27.phase (m : ℤ) (r : ℝ) = 1 at hinter
        rw [hinter, mul_one]
      simp_rw [hterm]
      rw [sum_const, card_range, nsmul_eq_mul, hquot]
    · simp only [if_neg hdiv]
      have hsplit (r : ℕ) :
          phase (h : ℤ) ((t + r) / d) =
            phase (h : ℤ) (t / d) * phase (h : ℤ) (1 / (d : ℝ)) ^ r := by
        rw [show (t + (r : ℝ)) / d = t / d + (r : ℝ) / d by ring]
        change Theory.PiDigits.T27.phase (h : ℤ) (t / d + (r : ℝ) / d) =
          Theory.PiDigits.T27.phase (h : ℤ) (t / d) *
            Theory.PiDigits.T27.phase (h : ℤ) (1 / (d : ℝ)) ^ r
        rw [Theory.PiDigits.T27.phase_add_real]
        congr 1
        unfold Theory.PiDigits.T27.phase
        rw [show 2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
              ((((r : ℝ) / d : ℝ) : ℂ)) =
            (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
              ((((1 : ℝ) / d : ℝ) : ℂ))) by push_cast; ring,
          Complex.exp_nat_mul]
      simp_rw [hsplit]
      rw [← Finset.mul_sum]
      let z := phase (h : ℤ) (1 / (d : ℝ))
      have hzpow : z ^ d = 1 :=
        Theory.PiDigits.SharperNaturalScaleResonance.phase_uniformGrid_root_pow
          (h : ℤ) d hd
      have hzne : z ≠ 1 := by
        intro hz
        have hexp :
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) / (d : ℂ)) = 1 := by
          change Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
              ((((1 : ℝ) / d : ℝ) : ℂ))) = 1 at hz
          convert hz using 1
          push_cast
          field_simp
        exact hdiv
          ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hd.ne').mp hexp)
      have hgeom := geom_sum_mul_neg z d
      rw [hzpow, sub_self] at hgeom
      have hsum : ∑ r ∈ range d, z ^ r = 0 :=
        (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hzne.symm)
      rw [hsum, mul_zero]
  calc
    (∑ r ∈ range d, phase (-(h : ℤ)) ((t + r) / d)) =
        conj (∑ r ∈ range d, phase (h : ℤ) ((t + r) / d)) := by
      rw [map_sum]
      apply sum_congr rfl
      intro r hr
      exact Theory.PiDigits.T27.phase_neg (h : ℤ) _
    _ = if d ∣ h then (d : ℂ) * phase (-((h / d : ℕ) : ℤ)) t else 0 := by
      rw [hpositive]
      by_cases hdiv : d ∣ h
      · simp only [if_pos hdiv, map_mul]
        rw [map_natCast]
        rw [← Theory.PiDigits.T27.phase_neg]
      · simp [hdiv]

private lemma tenPrimitivePart_ten_mul (h : ℕ) :
    tenPrimitivePart (10 * h) = tenPrimitivePart h := by
  unfold tenPrimitivePart
  rw [Nat.divMaxPow_base_mul (by norm_num)]

private lemma phase_neg_nat_grid_sum_ten (h : ℕ) (t : ℝ) :
    (∑ r ∈ range 10, phase (-(h : ℤ)) ((t + r) / 10)) =
      if 10 ∣ h then (10 : ℂ) * phase (-((h / 10 : ℕ) : ℤ)) t else 0 :=
  phase_neg_nat_grid_sum h 10 (by norm_num) t

/-- Averaging the ten fine left children is exactly the coarse primitive
sum plus the explicit coefficient defect.  This is a finite root-grid
identity and uses no orbit cancellation hypothesis. -/
theorem primitiveBoundaryFourierSum_leftExtension (q A N : ℕ) :
    (∑ d ∈ Finset.range 10,
      primitiveBoundaryFourierSum (10 * q) (A + d * q) N) =
        primitiveBoundaryFourierSum q A N + leftExtensionRemainder q A N := by
  classical
  by_cases hq : q = 0
  · subst q
    simp [primitiveBoundaryFourierSum, primitiveBoundarySupport,
      positiveBoundarySupport, leftExtensionRemainder]
  rw [primitiveBoundaryFourierSum_eq_support_sum q A N]
  simp_rw [primitiveBoundaryFourierSum_eq_support_sum]
  rw [Finset.sum_comm]
  unfold centeredBoundaryTerm
  have hcenter (d : ℕ) :
      decimalCylinderCenter (10 * q) (A + d * q) =
        (decimalCylinderCenter q A + d) / 10 := by
    unfold decimalCylinderCenter
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    field_simp
    ring
  simp_rw [hcenter]
  rw [show (∑ h ∈ positiveBoundarySupport (10 * q),
      ∑ d ∈ range 10,
        ((positiveBoundaryCoefficient (10 * q) h : ℂ) *
            phase (-(h : ℤ)) ((decimalCylinderCenter q A + d) / 10)) *
          exponentialSum piOrbit N (tenPrimitivePart h : ℤ)) =
      ∑ h ∈ positiveBoundarySupport (10 * q),
        ((positiveBoundaryCoefficient (10 * q) h : ℂ) *
          (∑ d ∈ range 10,
            phase (-(h : ℤ)) ((decimalCylinderCenter q A + d) / 10))) *
          exponentialSum piOrbit N (tenPrimitivePart h : ℤ) by
    apply sum_congr rfl
    intro h hh
    rw [Finset.mul_sum, Finset.sum_mul]]
  simp_rw [phase_neg_nat_grid_sum_ten]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  rw [← Finset.sum_filter]
  -- Reindex the surviving fine frequencies `10*h` by the coarse support.
  rw [show (∑ h ∈ positiveBoundarySupport (10 * q) with 10 ∣ h,
      ((positiveBoundaryCoefficient (10 * q) h : ℂ) *
        ((10 : ℂ) * phase (-((h / 10 : ℕ) : ℤ))
          (decimalCylinderCenter q A))) *
        exponentialSum piOrbit N (tenPrimitivePart h : ℤ)) =
      ∑ h ∈ positiveBoundarySupport q,
        ((10 * positiveBoundaryCoefficient (10 * q) (10 * h) : ℝ) : ℂ) *
          phase (-(h : ℤ)) (decimalCylinderCenter q A) *
          exponentialSum piOrbit N (tenPrimitivePart h : ℤ) by
    apply Finset.sum_bij (fun h _ => h / 10)
    · intro h hh
      simp only [positiveBoundarySupport, Finset.mem_filter, Finset.mem_Icc] at hh ⊢
      rcases hh with ⟨⟨hh1, hh2⟩, hdiv⟩
      constructor <;> omega
    · intro a ha b hb hab
      rcases (Finset.mem_filter.mp ha).2 with ⟨m, rfl⟩
      rcases (Finset.mem_filter.mp hb).2 with ⟨n, rfl⟩
      omega
    · intro h hh
      refine ⟨10 * h, ?_, by simp⟩
      simp only [Finset.mem_filter, positiveBoundarySupport, Finset.mem_Icc]
      simp only [positiveBoundarySupport, Finset.mem_Icc] at hh
      exact ⟨⟨by omega, by omega⟩, dvd_mul_right 10 h⟩
    · intro h hh
      rcases (Finset.mem_filter.mp hh).2 with ⟨m, rfl⟩
      rw [Nat.mul_div_cancel_left m (by norm_num), tenPrimitivePart_ten_mul]
      push_cast
      ring]
  unfold leftExtensionRemainder leftExtensionCoefficientDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  push_cast
  ring

/-- The exact remainder mass.  This is a finite coefficient object and does
not contain any orbit information. -/
def leftExtensionDefectMass (q : ℕ) : ℝ :=
  ∑ h ∈ positiveBoundarySupport q, leftExtensionCoefficientDefect q h

private lemma sum_positiveBoundarySupport_eq_range
    {R : Type*} [AddCommMonoid R] (q : ℕ) (f : ℕ → R) :
    (∑ h ∈ positiveBoundarySupport q, f h) =
      ∑ i ∈ range (2 * q - 1), f (i + 1) := by
  unfold positiveBoundarySupport
  rw [show Icc 1 (2 * q - 1) = Ico 1 (2 * q) by
    ext h
    simp only [mem_Icc, mem_Ico]
    omega, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_comm]

/-- The defect mass is the difference between the ten-spaced fine layer and
the full coarse positive mass. -/
theorem leftExtensionDefectMass_eq_layerMass (q : ℕ) (hq : 0 < q) :
    leftExtensionDefectMass q =
      10 * Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass (10 * q) 10 -
        Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass q 1 := by
  unfold leftExtensionDefectMass leftExtensionCoefficientDefect
  rw [Finset.sum_sub_distrib]
  simp_rw [sum_positiveBoundarySupport_eq_range]
  unfold Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass
  have hquot : (2 * (10 * q) - 1) / 10 = 2 * q - 1 := by omega
  rw [hquot]
  simp only [Nat.one_mul, Nat.div_one]
  rw [Finset.mul_sum]

/-- The quartic cosine mismatch which remains after quadratic scaling. -/
def leftExtensionCosineDefect (q : ℕ) : ℝ :=
  100 * (1 - Real.cos (Real.pi / (10 * q))) -
    (1 - Real.cos (Real.pi / q))

private lemma leftExtensionCosineDefect_bounds
    (q : ℕ) (hq : 1000 ≤ q) :
    3 / (q : ℝ) ^ 4 < leftExtensionCosineDefect q ∧
      leftExtensionCosineDefect q < 41 / (10 * (q : ℝ) ^ 4) := by
  let z : ℝ := Real.pi / (2 * q)
  let w : ℝ := z / 10
  have hqR : (1000 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hw0 : 0 < w := by dsimp [w]; positivity
  have hz1 : |z| ≤ 1 := by
    rw [abs_of_pos hz0]
    dsimp [z]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
    nlinarith [Real.pi_lt_four]
  have hw1 : |w| ≤ 1 := by
    rw [abs_of_pos hw0]
    have hzle : z ≤ 1 := (le_abs_self z).trans hz1
    dsimp [w]
    nlinarith
  have hzSin := Real.sin_bound hz1
  have hwSin := Real.sin_bound hw1
  rw [abs_of_pos hz0] at hzSin
  rw [abs_of_pos hw0] at hwSin
  have hzLower : z - z ^ 3 / 6 - z ^ 4 * (5 / 96) ≤ Real.sin z := by
    linarith [neg_le_of_abs_le hzSin]
  have hzUpper : Real.sin z ≤ z - z ^ 3 / 6 + z ^ 4 * (5 / 96) := by
    linarith [le_of_abs_le hzSin]
  have hwLower : w - w ^ 3 / 6 - w ^ 4 * (5 / 96) ≤ Real.sin w := by
    linarith [neg_le_of_abs_le hwSin]
  have hwUpper : Real.sin w ≤ w - w ^ 3 / 6 + w ^ 4 * (5 / 96) := by
    linarith [le_of_abs_le hwSin]
  have hzSmall : z < 1 / 500 := by
    dsimp [z]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
    nlinarith [Real.pi_lt_four]
  have hwSmall : w < 1 / 5000 := by dsimp [w]; linarith
  have hzLower0 : 0 ≤ z - z ^ 3 / 6 - z ^ 4 * (5 / 96) := by
    nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]
  have hwLower0 : 0 ≤ w - w ^ 3 / 6 - w ^ 4 * (5 / 96) := by
    nlinarith [sq_nonneg w, sq_nonneg (w ^ 2)]
  have hzSin0 : 0 ≤ Real.sin z :=
    Real.sin_nonneg_of_nonneg_of_le_pi hz0.le (by linarith [Real.pi_gt_d2])
  have hwSin0 : 0 ≤ Real.sin w :=
    Real.sin_nonneg_of_nonneg_of_le_pi hw0.le (by linarith [Real.pi_gt_d2])
  have hzSqLower :
      (z - z ^ 3 / 6 - z ^ 4 * (5 / 96)) ^ 2 ≤ Real.sin z ^ 2 :=
    (sq_le_sq₀ hzLower0 hzSin0).2 hzLower
  have hzUpper0 : 0 ≤ z - z ^ 3 / 6 + z ^ 4 * (5 / 96) := by
    nlinarith [sq_nonneg z]
  have hwUpper0 : 0 ≤ w - w ^ 3 / 6 + w ^ 4 * (5 / 96) := by
    nlinarith [sq_nonneg w]
  have hzSqUpper : Real.sin z ^ 2 ≤
      (z - z ^ 3 / 6 + z ^ 4 * (5 / 96)) ^ 2 :=
    (sq_le_sq₀ hzSin0 hzUpper0).2 hzUpper
  have hwSqLower :
      (w - w ^ 3 / 6 - w ^ 4 * (5 / 96)) ^ 2 ≤ Real.sin w ^ 2 :=
    (sq_le_sq₀ hwLower0 hwSin0).2 hwLower
  have hwSqUpper : Real.sin w ^ 2 ≤
      (w - w ^ 3 / 6 + w ^ 4 * (5 / 96)) ^ 2 :=
    (sq_le_sq₀ hwSin0 hwUpper0).2 hwUpper
  have sinSqLower (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 500)
      (hsq : (x - x ^ 3 / 6 - x ^ 4 * (5 / 96)) ^ 2 ≤ Real.sin x ^ 2) :
      x ^ 2 - (401 / 1200) * x ^ 4 ≤ Real.sin x ^ 2 := by
    have hx5 : x ^ 5 ≤ x ^ 4 / 500 := by
      calc
        x ^ 5 = x ^ 4 * x := by ring
        _ ≤ x ^ 4 * (1 / 500) :=
          mul_le_mul_of_nonneg_left hx (pow_nonneg hx0 4)
        _ = x ^ 4 / 500 := by ring
    calc
      x ^ 2 - (401 / 1200) * x ^ 4 ≤
          (x - x ^ 3 / 6 - x ^ 4 * (5 / 96)) ^ 2 := by
        ring_nf at hx5 ⊢
        linarith [pow_nonneg hx0 4, pow_nonneg hx0 6,
          pow_nonneg hx0 7, pow_nonneg hx0 8]
      _ ≤ Real.sin x ^ 2 := hsq
  have sinSqUpper (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 500)
      (hsq : Real.sin x ^ 2 ≤
        (x - x ^ 3 / 6 + x ^ 4 * (5 / 96)) ^ 2) :
      Real.sin x ^ 2 ≤ x ^ 2 - (399 / 1200) * x ^ 4 := by
    have hx5 : x ^ 5 ≤ x ^ 4 / 500 := by
      calc
        x ^ 5 = x ^ 4 * x := by ring
        _ ≤ x ^ 4 * (1 / 500) :=
          mul_le_mul_of_nonneg_left hx (pow_nonneg hx0 4)
        _ = x ^ 4 / 500 := by ring
    have hx6 : x ^ 6 ≤ x ^ 4 / 250000 := by
      have hx2 : x ^ 2 ≤ (1 / 500) ^ 2 :=
        (sq_le_sq₀ hx0 (by norm_num)).2 hx
      calc
        x ^ 6 = x ^ 4 * x ^ 2 := by ring
        _ ≤ x ^ 4 * (1 / 500) ^ 2 :=
          mul_le_mul_of_nonneg_left hx2 (pow_nonneg hx0 4)
        _ = x ^ 4 / 250000 := by ring
    have hx8 : x ^ 8 ≤ x ^ 4 / 62500000000 := by
      have hx4 : x ^ 4 ≤ (1 / 500) ^ 4 := by
        exact pow_le_pow_left₀ hx0 hx 4
      calc
        x ^ 8 = x ^ 4 * x ^ 4 := by ring
        _ ≤ x ^ 4 * (1 / 500) ^ 4 :=
          mul_le_mul_of_nonneg_left hx4 (pow_nonneg hx0 4)
        _ = x ^ 4 / 62500000000 := by ring
    calc
      Real.sin x ^ 2 ≤
          (x - x ^ 3 / 6 + x ^ 4 * (5 / 96)) ^ 2 := hsq
      _ ≤ x ^ 2 - (399 / 1200) * x ^ 4 := by
        ring_nf at hx5 hx6 hx8 ⊢
        linarith [pow_nonneg hx0 4, pow_nonneg hx0 7]
  have hzSqLower' : z ^ 2 - (401 / 1200) * z ^ 4 ≤ Real.sin z ^ 2 :=
    sinSqLower z hz0.le hzSmall.le hzSqLower
  have hzSqUpper' : Real.sin z ^ 2 ≤ z ^ 2 - (399 / 1200) * z ^ 4 :=
    sinSqUpper z hz0.le hzSmall.le hzSqUpper
  have hwSqLower' : w ^ 2 - (401 / 1200) * w ^ 4 ≤ Real.sin w ^ 2 :=
    sinSqLower w hw0.le (by linarith) hwSqLower
  have hwSqUpper' : Real.sin w ^ 2 ≤ w ^ 2 - (399 / 1200) * w ^ 4 :=
    sinSqUpper w hw0.le (by linarith) hwSqUpper
  have hdefect : leftExtensionCosineDefect q =
      2 * (100 * Real.sin w ^ 2 - Real.sin z ^ 2) := by
    unfold leftExtensionCosineDefect
    rw [show Real.pi / (10 * (q : ℝ)) = 2 * w by
          dsimp [w, z]; field_simp,
      show Real.pi / (q : ℝ) = 2 * z by dsimp [z]; field_simp,
      Real.cos_two_mul_eq_one_sub, Real.cos_two_mul_eq_one_sub]
    ring
  rw [hdefect]
  have hdefectLower : (39499 / 60000) * z ^ 4 ≤
      2 * (100 * Real.sin w ^ 2 - Real.sin z ^ 2) := by
    dsimp [w] at hwSqLower' ⊢
    nlinarith only [hwSqLower', hzSqUpper']
  have hdefectUpper : 2 * (100 * Real.sin w ^ 2 - Real.sin z ^ 2) ≤
      (39701 / 60000) * z ^ 4 := by
    dsimp [w] at hwSqUpper' ⊢
    nlinarith only [hwSqUpper', hzSqLower']
  constructor
  · have hpi4 : 81 < Real.pi ^ 4 := by
      have hpi2 : (3 : ℝ) ^ 2 < Real.pi ^ 2 :=
        (sq_lt_sq₀ (by norm_num) Real.pi_pos.le).2 Real.pi_gt_three
      have hpi4' : ((3 : ℝ) ^ 2) ^ 2 < (Real.pi ^ 2) ^ 2 :=
        (sq_lt_sq₀ (sq_nonneg 3) (sq_nonneg Real.pi)).2 hpi2
      norm_num at hpi4' ⊢
      convert hpi4' using 1 <;> ring
    dsimp [z] at hdefectLower ⊢
    field_simp at hdefectLower ⊢
    nlinarith only [hdefectLower, hpi4]
  · have hpi4 : Real.pi ^ 4 < (63 / 20 : ℝ) ^ 4 := by
      have hpilt : Real.pi < (63 / 20 : ℝ) := by
        convert Real.pi_lt_d2 using 1 <;> norm_num
      have hpi2 : Real.pi ^ 2 < (63 / 20 : ℝ) ^ 2 :=
        (sq_lt_sq₀ Real.pi_pos.le (by norm_num)).2 hpilt
      have hpi4' : (Real.pi ^ 2) ^ 2 < (((63 / 20 : ℝ) ^ 2)) ^ 2 :=
        (sq_lt_sq₀ (sq_nonneg Real.pi) (sq_nonneg (63 / 20 : ℝ))).2 hpi2
      convert hpi4' using 1 <;> ring
    dsimp [z] at hdefectUpper ⊢
    field_simp at hdefectUpper ⊢
    nlinarith only [hdefectUpper, hpi4]

private lemma one_sub_cos_fine_lt
    (q : ℕ) (hq : 1000 ≤ q) :
    1 - Real.cos (Real.pi / (10 * q)) < 1 / (20 * (q : ℝ) ^ 2) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hcos := Real.one_sub_sq_div_two_le_cos
    (x := Real.pi / (10 * (q : ℝ)))
  have hpilt : Real.pi < (63 / 20 : ℝ) := by
    convert Real.pi_lt_d2 using 1 <;> norm_num
  have hpi2 : Real.pi ^ 2 < 10 := by
    have := (sq_lt_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 63 / 20)).2 hpilt
    norm_num at this ⊢
    nlinarith
  field_simp at hcos ⊢
  nlinarith

private lemma coarse_cosine_gap_lt
    (q : ℕ) (hq : 1000 ≤ q) :
    1 - Real.cos (Real.pi / q) < 5 / (q : ℝ) ^ 2 := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hcos := Real.one_sub_sq_div_two_le_cos
    (x := Real.pi / (q : ℝ))
  have hpilt : Real.pi < (63 / 20 : ℝ) := by
    convert Real.pi_lt_d2 using 1 <;> norm_num
  have hpi2 : Real.pi ^ 2 < 10 := by
    have := (sq_lt_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 63 / 20)).2 hpilt
    norm_num at this ⊢
    nlinarith
  field_simp at hcos ⊢
  nlinarith

private lemma fine_cosine_gap_lt_coarse
    (q : ℕ) (hq : 1000 ≤ q) :
    1 - Real.cos (Real.pi / (10 * q)) <
      1 - Real.cos (Real.pi / q) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hx0 : 0 ≤ Real.pi / (10 * (q : ℝ)) := by positivity
  have hyPi : Real.pi / (q : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hq0).2
    exact le_mul_of_one_le_right Real.pi_pos.le
      (by exact_mod_cast (show 1 ≤ q by omega))
  have hxy : Real.pi / (10 * (q : ℝ)) < Real.pi / (q : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 10 * q) hq0).2
    nlinarith [Real.pi_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi hx0 hyPi hxy
  linarith

/-- Every coefficient in the literal left-extension remainder is strictly
positive at the natural decimal scales. -/
theorem leftExtensionCoefficientDefect_pos
    (q h : ℕ) (hq : 1000 ≤ q) (hh : h ∈ positiveBoundarySupport q) :
    0 < leftExtensionCoefficientDefect q h := by
  have hq1 : 1 < q := by omega
  have hh' : 0 < h ∧ h ≤ 2 * q - 1 := by
    simpa [positiveBoundarySupport] using hh
  have hfine0 : 0 < 10 * h := by omega
  have hfinesupp : 10 * h ≤ 2 * (10 * q) - 1 := by omega
  have hD := (leftExtensionCosineDefect_bounds q hq).1
  have hD0 : 0 < leftExtensionCosineDefect q :=
    lt_trans (by positivity : 0 < 3 / (q : ℝ) ^ 4) hD
  have ha10 : 0 ≤ 1 - Real.cos (Real.pi / (10 * q)) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hadiff : 0 < (1 - Real.cos (Real.pi / q)) -
      (1 - Real.cos (Real.pi / (10 * q))) :=
    sub_pos.mpr (fine_cosine_gap_lt_coarse q hq)
  have hadiffUpper : (1 - Real.cos (Real.pi / q)) -
      (1 - Real.cos (Real.pi / (10 * q))) < 5 / (q : ℝ) ^ 2 := by
    have := coarse_cosine_gap_lt q hq
    nlinarith
  have hadiff' : 0 < Real.cos (Real.pi / (10 * q)) -
      Real.cos (Real.pi / q) := by linarith
  have hadiffUpper' : Real.cos (Real.pi / (10 * q)) -
      Real.cos (Real.pi / q) < 5 / (q : ℝ) ^ 2 := by linarith
  have hden : 0 < 6 * (q : ℝ) ^ 2 := by positivity
  rw [leftExtensionCoefficientDefect,
    Theory.PiDigits.BoundaryCoefficientAbel.positiveBoundaryCoefficient_eq_piecewise
      (10 * q) (10 * h) (by omega) hfine0 hfinesupp,
    Theory.PiDigits.BoundaryCoefficientAbel.positiveBoundaryCoefficient_eq_piecewise
      q h hq1 hh'.1 hh'.2]
  by_cases hhq : h ≤ q
  · simp only [if_pos hhq, show 10 * h ≤ 10 * q by omega, if_true]
    let P : ℝ := 4 * (q : ℝ) ^ 3 - 6 * q * (h : ℝ) ^ 2 + 3 * (h : ℝ) ^ 3
    let L : ℝ := 2 * q - h * 3
    have hform :
        10 * ((1 - Real.cos (Real.pi / (10 * (q : ℕ)))) *
              (4 * ((10 * q : ℕ) : ℝ) ^ 3 + 2 * (10 * q : ℕ) -
                6 * (10 * q : ℕ) * ((10 * h : ℕ) : ℝ) ^ 2 +
                3 * ((10 * h : ℕ) : ℝ) ^ 3 - 3 * (10 * h : ℕ)) /
                (6 * ((10 * q : ℕ) : ℝ) ^ 2) +
              (3 * ((10 * h : ℕ) : ℝ) - 2 * (10 * q : ℕ)) /
                (2 * ((10 * q : ℕ) : ℝ) ^ 2)) -
            ((1 - Real.cos (Real.pi / (q : ℝ))) *
              (4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
                3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2) +
              (3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2)) =
          (leftExtensionCosineDefect q * P -
            ((1 - Real.cos (Real.pi / q)) -
              (1 - Real.cos (Real.pi / (10 * q)))) * L) /
            (6 * (q : ℝ) ^ 2) := by
      dsimp [P, L, leftExtensionCosineDefect]
      push_cast
      field_simp
      ring
    norm_num [Nat.cast_mul] at hform ⊢
    have hP : P = 2 * (q : ℝ) ^ 2 * L +
        3 * h * (2 * (q : ℝ) ^ 2 - 2 * q * h + (h : ℝ) ^ 2) := by
      dsimp [P, L]
      ring
    have hquad : 0 < 2 * (q : ℝ) ^ 2 - 2 * q * h + (h : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((q : ℝ) - h), sq_pos_of_pos (show (0 : ℝ) < q by positivity)]
    by_cases hL : 0 < L
    · have hscaled :
          6 / (q : ℝ) ^ 2 < 2 * (q : ℝ) ^ 2 * leftExtensionCosineDefect q := by
        have hqR : (0 : ℝ) < q := by positivity
        field_simp at hD ⊢
        nlinarith
      have hnum : 0 < leftExtensionCosineDefect q * P -
          (Real.cos (Real.pi / (10 * q)) - Real.cos (Real.pi / q)) * L := by
        have hfivesix : 5 / (q : ℝ) ^ 2 < 6 / (q : ℝ) ^ 2 := by
          exact (div_lt_div_iff_of_pos_right
            (show 0 < (q : ℝ) ^ 2 by positivity)).2 (by norm_num)
        have hscaledL := mul_lt_mul_of_pos_right
          (lt_trans hadiffUpper' (lt_trans hfivesix hscaled)) hL
        rw [hP]
        nlinarith [mul_pos (show (0 : ℝ) < h by exact_mod_cast hh'.1) hquad]
      have hdifference := div_pos hnum hden
      rw [← hform] at hdifference
      exact sub_pos.mp hdifference
    · have hP0 : 0 < P := by
        have hhR : (h : ℝ) ≤ q := by exact_mod_cast hhq
        have hfactor : 0 < (q : ℝ) ^ 2 + q * h - (h : ℝ) ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_left hhR
            (show (0 : ℝ) ≤ h by positivity)
          nlinarith [sq_pos_of_pos (show (0 : ℝ) < q by positivity)]
        have hidentity : P = (q : ℝ) ^ 3 +
            3 * ((q : ℝ) - h) *
              ((q : ℝ) ^ 2 + q * h - (h : ℝ) ^ 2) := by
          dsimp [P]
          ring
        rw [hidentity]
        positivity
      have hnum : 0 < leftExtensionCosineDefect q * P -
          (Real.cos (Real.pi / (10 * q)) - Real.cos (Real.pi / q)) * L := by
        nlinarith [mul_pos hD0 hP0]
      have hdifference := div_pos hnum hden
      rw [← hform] at hdifference
      exact sub_pos.mp hdifference
  · have hhq' : q < h := by omega
    simp only [if_neg hhq, if_neg (show ¬ 10 * h ≤ 10 * q by omega)]
    let t : ℝ := 2 * q - h
    have ht : 0 < t := by
      dsimp [t]
      have hlt : (h : ℝ) < 2 * q := by
        exact_mod_cast (show h < 2 * q by omega)
      linarith
    have hform :
        10 * ((1 - Real.cos (Real.pi / (10 * (q : ℕ)))) *
              ((2 * ((10 * q : ℕ) : ℝ) - (10 * h : ℕ) - 1) *
                (2 * ((10 * q : ℕ) : ℝ) - (10 * h : ℕ)) *
                (2 * ((10 * q : ℕ) : ℝ) - (10 * h : ℕ) + 1)) /
                (6 * ((10 * q : ℕ) : ℝ) ^ 2) +
              (2 * ((10 * q : ℕ) : ℝ) - (10 * h : ℕ)) /
                (2 * ((10 * q : ℕ) : ℝ) ^ 2)) -
            ((1 - Real.cos (Real.pi / (q : ℝ))) *
              ((2 * (q : ℝ) - h - 1) * (2 * (q : ℝ) - h) *
                (2 * (q : ℝ) - h + 1)) / (6 * (q : ℝ) ^ 2) +
              (2 * (q : ℝ) - h) / (2 * (q : ℝ) ^ 2)) =
          (leftExtensionCosineDefect q * t ^ 3 +
            ((1 - Real.cos (Real.pi / q)) -
              (1 - Real.cos (Real.pi / (10 * q)))) * t) /
            (6 * (q : ℝ) ^ 2) := by
      dsimp [t, leftExtensionCosineDefect]
      push_cast
      field_simp
      ring
    norm_num [Nat.cast_mul] at hform ⊢
    have hdifference := div_pos
      (add_pos (mul_pos hD0 (pow_pos ht 3)) (mul_pos hadiff' ht))
      hden
    rw [← hform] at hdifference
    exact sub_pos.mp hdifference

/-- Closed form for the exact coefficient defect mass. -/
theorem leftExtensionDefectMass_eq_closed
    (q : ℕ) (hq : 1000 ≤ q) :
    leftExtensionDefectMass q =
      leftExtensionCosineDefect q *
          ((q - 1 : ℕ) * (3 * (q : ℝ) ^ 2 + q + 1)) /
            (6 * (q : ℝ)) +
        33 * (1 - Real.cos (Real.pi / (10 * q))) / (2 * (q : ℝ)) := by
  rw [leftExtensionDefectMass_eq_layerMass q (by omega)]
  rw [Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass_eq
      (10 * q) 10 q (by omega) (by norm_num) (by omega) rfl,
    Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass_eq
      q 1 q (by omega) (by norm_num) (by omega) (by simp)]
  rw [Theory.PiDigits.BoundaryKernelNormalizedComparison.boundaryZeroCoefficient_eq
      (10 * q) (by positivity),
    Theory.PiDigits.BoundaryKernelNormalizedComparison.boundaryZeroCoefficient_eq
      q (by positivity)]
  unfold leftExtensionCosineDefect
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ q)]
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The exact positive defect mass is quartically small coefficientwise and
quadratically small after summing the full positive support. -/
theorem leftExtensionDefectMass_lt
    (q : ℕ) (hq : 1000 ≤ q) :
    leftExtensionDefectMass q < 21 / (10 * (q : ℝ) ^ 2) := by
  rw [leftExtensionDefectMass_eq_closed q hq]
  let D := leftExtensionCosineDefect q
  let a := 1 - Real.cos (Real.pi / (10 * q))
  let F := ((q - 1 : ℕ) * (3 * (q : ℝ) ^ 2 + q + 1)) /
    (6 * (q : ℝ))
  have hqR : (1000 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hD0 : 0 < D := by
    dsimp [D]
    exact lt_trans (by positivity : 0 < 3 / (q : ℝ) ^ 4)
      (leftExtensionCosineDefect_bounds q hq).1
  have hDupper : D < 41 / (10 * (q : ℝ) ^ 4) :=
    (leftExtensionCosineDefect_bounds q hq).2
  have haupper : a < 1 / (20 * (q : ℝ) ^ 2) :=
    one_sub_cos_fine_lt q hq
  have hF : F < (51 / 100) * (q : ℝ) ^ 2 := by
    dsimp [F]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    field_simp
    nlinarith [sq_nonneg ((q : ℝ) - 1),
      mul_pos hq0 (sq_pos_of_pos hq0)]
  have hDF : D * F < D * ((51 / 100) * (q : ℝ) ^ 2) :=
    mul_lt_mul_of_pos_left hF hD0
  have hDFupper : D * ((51 / 100) * (q : ℝ) ^ 2) <
      2091 / (1000 * (q : ℝ) ^ 2) := by
    field_simp at hDupper ⊢
    nlinarith
  have haTerm : 33 * a / (2 * (q : ℝ)) <
      33 / (40 * (q : ℝ) ^ 3) := by
    field_simp at haupper ⊢
    nlinarith
  rw [show leftExtensionCosineDefect q *
          ((q - 1 : ℕ) * (3 * (q : ℝ) ^ 2 + q + 1)) /
          (6 * (q : ℝ)) = D * F by dsimp [D, F]; ring,
    show 33 * (1 - Real.cos (Real.pi / (10 * q))) / (2 * (q : ℝ)) =
        33 * a / (2 * (q : ℝ)) by rfl]
  have hfinal : 2091 / (1000 * (q : ℝ) ^ 2) +
      33 / (40 * (q : ℝ) ^ 3) < 21 / (10 * (q : ℝ) ^ 2) := by
    field_simp
    nlinarith
  linarith

/-- Once coefficient positivity is available, the literal remainder is
bounded by `N` times its exact mass. -/
theorem norm_leftExtensionRemainder_le
    (q A N : ℕ)
    (hpos : ∀ h ∈ positiveBoundarySupport q,
      0 ≤ leftExtensionCoefficientDefect q h) :
    ‖leftExtensionRemainder q A N‖ ≤ N * leftExtensionDefectMass q := by
  unfold leftExtensionRemainder leftExtensionDefectMass
  calc
    ‖∑ h ∈ positiveBoundarySupport q,
        (leftExtensionCoefficientDefect q h : ℂ) *
          phase (-(h : ℤ)) (decimalCylinderCenter q A) *
          exponentialSum piOrbit N (tenPrimitivePart h : ℤ)‖ ≤
        ∑ h ∈ positiveBoundarySupport q,
          ‖(leftExtensionCoefficientDefect q h : ℂ) *
            phase (-(h : ℤ)) (decimalCylinderCenter q A) *
            exponentialSum piOrbit N (tenPrimitivePart h : ℤ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ positiveBoundarySupport q,
          leftExtensionCoefficientDefect q h * N := by
      apply sum_le_sum
      intro h hh
      rw [norm_mul, norm_mul, Complex.norm_real,
        Theory.PiDigits.T27.norm_phase]
      simp only [mul_one]
      have hsum := Theory.PiDigits.PowerTenFrequencyShift.norm_sum_phase_range_le
        N 0 (tenPrimitivePart h : ℤ)
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos h hh)]
      apply mul_le_mul_of_nonneg_left _ (hpos h hh)
      simpa [exponentialSum, Theory.PiDigits.T27.exponentialSum] using hsum
    _ = N * ∑ h ∈ positiveBoundarySupport q,
          leftExtensionCoefficientDefect q h := by
      rw [← Finset.sum_mul]
      ring

/-- Literal one-step consequence of the proved zero-sector identity.  The
remaining premise is purely coefficient-side and is intended to be discharged
from the closed T142 formulas. -/
theorem exists_leftExtension_score_ge
    (q A N : ℕ)
    (hpos : ∀ h ∈ positiveBoundarySupport q,
      0 ≤ leftExtensionCoefficientDefect q h) :
    ∃ d < 10,
      ((primitiveBoundaryFourierSum q A N).re -
          N * leftExtensionDefectMass q) / 10 ≤
        (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re := by
  have hrem := norm_leftExtensionRemainder_le q A N hpos
  have hremre : -(N * leftExtensionDefectMass q) ≤
      (leftExtensionRemainder q A N).re := by
    have habs := Complex.abs_re_le_norm (leftExtensionRemainder q A N)
    have hre : -(leftExtensionRemainder q A N).re ≤
        ‖leftExtensionRemainder q A N‖ := by
      exact (neg_le_abs _).trans habs
    linarith
  have hsum :
      (primitiveBoundaryFourierSum q A N).re -
          N * leftExtensionDefectMass q ≤
        ∑ d ∈ Finset.range 10,
          (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re := by
    rw [← Complex.re_sum, primitiveBoundaryFourierSum_leftExtension]
    simp only [Complex.add_re]
    linarith
  by_contra hnone
  push Not at hnone
  have hall : ∀ d ∈ Finset.range 10,
      (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re <
        ((primitiveBoundaryFourierSum q A N).re -
          N * leftExtensionDefectMass q) / 10 := by
    intro d hd
    exact hnone d (Finset.mem_range.mp hd)
  have hstrict :
      ∑ d ∈ Finset.range 10,
          (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re <
        ∑ _d ∈ Finset.range 10,
          (((primitiveBoundaryFourierSum q A N).re -
            N * leftExtensionDefectMass q) / 10) := by
    exact Finset.sum_lt_sum_of_nonempty (by simp) (fun d hd => hall d hd)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hstrict
  norm_num at hstrict
  linarith

/-- Unconditional quantitative left-extension step at every decimal scale
`q ≥ 1000`.  One of the ten children retains one tenth of the parent score,
up to the explicit `21 N / (10 q²)` total coefficient defect. -/
theorem exists_leftExtension_score_ge_of_large
    (q A N : ℕ) (hq : 1000 ≤ q) :
    ∃ d < 10,
      ((primitiveBoundaryFourierSum q A N).re -
          N * (21 / (10 * (q : ℝ) ^ 2))) / 10 ≤
        (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re := by
  obtain ⟨d, hd, hscore⟩ := exists_leftExtension_score_ge q A N
    (fun h hh => (leftExtensionCoefficientDefect_pos q h hq hh).le)
  refine ⟨d, hd, ?_⟩
  have hmass := leftExtensionDefectMass_lt q hq
  have hN : (0 : ℝ) ≤ N := by positivity
  have hleft :
      ((primitiveBoundaryFourierSum q A N).re -
          N * (21 / (10 * (q : ℝ) ^ 2))) / 10 ≤
        ((primitiveBoundaryFourierSum q A N).re -
          N * leftExtensionDefectMass q) / 10 := by
    have hmul := mul_le_mul_of_nonneg_left hmass.le hN
    nlinarith
  exact hleft.trans hscore

end Theory.PiDigits.PositiveLeftExtensionTransport

#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.primitiveBoundaryFourierSum_eq_support_sum
#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.primitiveBoundaryFourierSum_leftExtension
#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.leftExtensionCoefficientDefect_pos
#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.leftExtensionDefectMass_eq_closed
#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.leftExtensionDefectMass_lt
#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.norm_leftExtensionRemainder_le
#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.exists_leftExtension_score_ge
#print axioms Theory.PiDigits.PositiveLeftExtensionTransport.exists_leftExtension_score_ge_of_large
