import TheoryLib.PiQuantitativeBlockHitting.T145T145BoundaryLayerScalarBounds
import TheoryLib.PiLongLagBlockCollisionDecay.T34T34CancellingRepunitIncidence
import TheoryLib.PiQuantitativeBlockHitting.T138T138PrimitiveRayCoefficientGap

/-!
# T146: torus-distance and sine bounds for decimal endpoint phases

This module keeps every distance on `R/Z` expressed through
`nearestIntegerDistance`.  It contains no endpoint estimate or consumer.
-/

noncomputable section

namespace Theory.PiDigits.BoundaryPhaseTorusBounds

open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T34
open Theory.PiDigits.PrimitiveRayCoefficientGap

/-- The fixed irrational displacement separating the two decimal layers has
an explicit distance from every integer. -/
theorem nearestIntegerDistance_nine_mul_pi_gt :
    13 / 50 < nearestIntegerDistance (9 * Real.pi) := by
  have hround : round (9 * Real.pi) = 28 := by
    rw [round_eq_iff]
    constructor <;> norm_num <;> nlinarith [Real.pi_gt_d2, Real.pi_lt_d2]
  unfold nearestIntegerDistance
  rw [hround]
  push_cast
  rw [abs_of_pos]
  · nlinarith [Real.pi_gt_d2]
  · nlinarith [Real.pi_gt_d2]

/-- If `θ₂ = 10 θ₁ - 9π`, the two phases cannot both lie in their indicated
small torus neighborhoods. -/
theorem decimal_phase_distance_dichotomy
    (θ₁ θ₂ : ℝ) (hrel : θ₂ = 10 * θ₁ - 9 * Real.pi) :
    7 / 1000 ≤ nearestIntegerDistance θ₁ ∨
      19 / 100 ≤ nearestIntegerDistance θ₂ := by
  by_contra h
  push Not at h
  let z : ℤ := 10 * round θ₁ - round θ₂
  have hnear := round_le (9 * Real.pi) z
  have hrewrite :
      9 * Real.pi - (z : ℝ) =
        10 * (θ₁ - (round θ₁ : ℝ)) - (θ₂ - (round θ₂ : ℝ)) := by
    dsimp [z]
    push_cast
    rw [hrel]
    ring
  rw [hrewrite] at hnear
  have habs :
      |10 * (θ₁ - (round θ₁ : ℝ)) - (θ₂ - (round θ₂ : ℝ))| ≤
        10 * nearestIntegerDistance θ₁ + nearestIntegerDistance θ₂ := by
    calc
      |_ - _| ≤ |10 * (θ₁ - (round θ₁ : ℝ))| +
          |θ₂ - (round θ₂ : ℝ)| := abs_sub _ _
      _ = 10 * nearestIntegerDistance θ₁ + nearestIntegerDistance θ₂ := by
        rw [abs_mul]
        norm_num [nearestIntegerDistance]
  have hsmall :
      10 * nearestIntegerDistance θ₁ + nearestIntegerDistance θ₂ < 13 / 50 := by
    nlinarith
  have hu : nearestIntegerDistance (9 * Real.pi) < 13 / 50 :=
    hnear.trans_lt (habs.trans_lt hsmall)
  exact (not_lt_of_ge nearestIntegerDistance_nine_mul_pi_gt.le) hu

/-- The actual first and second decimal endpoint phases obey the generic
two-layer dichotomy. -/
theorem decimal_center_phase_distance_dichotomy (q A : ℕ) :
    7 / 1000 ≤ nearestIntegerDistance
        (Real.pi - 10 * decimalCylinderCenter q A) ∨
      19 / 100 ≤ nearestIntegerDistance
        (Real.pi - 100 * decimalCylinderCenter q A) := by
  apply decimal_phase_distance_dichotomy
  ring

/-- Absolute sine is exactly sine of the canonical torus distance. -/
theorem abs_sin_pi_eq_sin_nearestIntegerDistance (x : ℝ) :
    |Real.sin (Real.pi * x)| =
      Real.sin (Real.pi * nearestIntegerDistance x) := by
  let u : ℝ := x - (round x : ℝ)
  have hu : |u| = nearestIntegerDistance x := rfl
  have hhalf := nearestIntegerDistance_le_half x
  have hx : Real.pi * x = Real.pi * u + (round x : ℝ) * Real.pi := by
    dsimp [u]
    ring
  rw [hx, Real.sin_add_int_mul_pi, abs_mul]
  simp
  have harg : |Real.pi * u| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos, hu]
    nlinarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi harg, abs_mul,
    abs_of_pos Real.pi_pos, hu]

/-- Monotonicity bridge from a certified torus-distance lower bound to an
absolute sine lower bound. -/
theorem sin_pi_mul_le_abs_sin_of_le_distance
    (a x : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ nearestIntegerDistance x) :
    Real.sin (Real.pi * a) ≤ |Real.sin (Real.pi * x)| := by
  rw [abs_sin_pi_eq_sin_nearestIntegerDistance]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · nlinarith [Real.pi_pos]
  · have hhalf := nearestIntegerDistance_le_half x
    nlinarith [Real.pi_pos]
  · exact mul_le_mul_of_nonneg_left ha Real.pi_pos.le

/-- Explicit lower sine bound at the first dichotomy radius. -/
theorem sine_seven_pi_div_thousand_gt :
    219 / 10000 < Real.sin (7 * Real.pi / 1000) := by
  let x : ℝ := 7 * Real.pi / 1000
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; nlinarith [Real.pi_lt_four]
  have hs := Real.sin_gt_sub_cube hx0 hx1
  have hlo : 2198 / 100000 < x := by
    dsimp [x]
    nlinarith [Real.pi_gt_d2]
  have hhi : x < 7 / 250 := by
    dsimp [x]
    nlinarith [Real.pi_lt_four]
  have hcube : x ^ 3 < (7 / 250 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hhi hx0.le (by norm_num)
  nlinarith

/-- Explicit lower sine bound at the second dichotomy radius. -/
theorem sine_nineteen_pi_div_hundred_gt :
    561 / 1000 < Real.sin (19 * Real.pi / 100) := by
  let δ : ℝ := 7 * Real.pi / 300
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; nlinarith [Real.pi_lt_d2]
  have hδlo : 1831 / 25000 < δ := by
    dsimp [δ]
    nlinarith [Real.pi_gt_d2]
  have hδhi : δ < 3 / 40 := by
    dsimp [δ]
    nlinarith [Real.pi_lt_d2]
  have hδcube : δ ^ 3 < (3 / 40 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hδhi hδ0.le (by norm_num)
  have hsinRaw := Real.sin_gt_sub_cube hδ0 hδ1
  have hsinδ :
      1831 / 25000 - (3 / 40 : ℝ) ^ 3 / 4 < Real.sin δ := by
    nlinarith
  have hsinδ0 : 0 < Real.sin δ := by
    have : (0 : ℝ) < 1831 / 25000 - (3 / 40 : ℝ) ^ 3 / 4 := by norm_num
    linarith
  have hcosRaw := Real.one_sub_sq_div_two_le_cos (x := δ)
  have hδsq : δ ^ 2 < (3 / 40 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hδhi hδ0.le (by norm_num)
  have hcosδ : 1 - (3 / 40 : ℝ) ^ 2 / 2 < Real.cos δ := by
    nlinarith
  have hsqrt : (433 / 250 : ℝ) < √3 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsqrtHalf : (433 / 500 : ℝ) < √3 / 2 := by linarith
  have hprod :
      (433 / 500 : ℝ) *
          (1831 / 25000 - (3 / 40 : ℝ) ^ 3 / 4) <
        (√3 / 2) * Real.sin δ := by
    calc
      (433 / 500 : ℝ) *
          (1831 / 25000 - (3 / 40 : ℝ) ^ 3 / 4) <
          (√3 / 2) *
            (1831 / 25000 - (3 / 40 : ℝ) ^ 3 / 4) := by
              apply mul_lt_mul_of_pos_right hsqrtHalf
              norm_num
      _ < (√3 / 2) * Real.sin δ := by
        apply mul_lt_mul_of_pos_left hsinδ
        positivity
  have harg : 19 * Real.pi / 100 = Real.pi / 6 + δ := by
    dsimp [δ]
    ring
  rw [harg, Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
  nlinarith

end Theory.PiDigits.BoundaryPhaseTorusBounds

#print axioms Theory.PiDigits.BoundaryPhaseTorusBounds.nearestIntegerDistance_nine_mul_pi_gt
#print axioms Theory.PiDigits.BoundaryPhaseTorusBounds.decimal_phase_distance_dichotomy
#print axioms Theory.PiDigits.BoundaryPhaseTorusBounds.decimal_center_phase_distance_dichotomy
#print axioms Theory.PiDigits.BoundaryPhaseTorusBounds.abs_sin_pi_eq_sin_nearestIntegerDistance
#print axioms Theory.PiDigits.BoundaryPhaseTorusBounds.sin_pi_mul_le_abs_sin_of_le_distance
#print axioms Theory.PiDigits.BoundaryPhaseTorusBounds.sine_seven_pi_div_thousand_gt
#print axioms Theory.PiDigits.BoundaryPhaseTorusBounds.sine_nineteen_pi_div_hundred_gt
