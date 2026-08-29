import TheoryLib.PiQuantitativeBlockHitting.T185T185BoundaryMinorantSineBridge

/-!
# T191: central boundary-kernel floor

The boundary-matched kernel has a uniform positive floor on the central
normalized chamber used by the unit-block carrier argument.  This is a
pointwise analytic statement; it contains no orbit or cancellation premise.
-/

noncomputable section

namespace Theory.PiDigits.T191CentralBoundaryKernelFloor

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelFloors
open Theory.PiDigits.T185BoundaryMinorantSineBridge

private lemma pi_lt_twenty_two_sevenths :
    Real.pi < (22 : ℝ) / 7 := by
  nlinarith [Real.pi_lt_d20]

private lemma sin_three_sevenths_bounds :
    (3 : ℝ) / 7 - ((3 : ℝ) / 7) ^ 3 / 6 -
          ((3 : ℝ) / 7) ^ 4 * (5 / 96) ≤ Real.sin ((3 : ℝ) / 7) ∧
      Real.sin ((3 : ℝ) / 7) ≤
        (3 : ℝ) / 7 - ((3 : ℝ) / 7) ^ 3 / 6 +
          ((3 : ℝ) / 7) ^ 4 * (5 / 96) := by
  have h := Real.sin_bound (x := (3 : ℝ) / 7) (by norm_num)
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 7)] at h
  constructor <;> linarith [neg_le_of_abs_le h, le_of_abs_le h]

private lemma sin_nine_sevenths_gt :
    (7393 : ℝ) / 10000 * (9 / 7) < Real.sin (9 / 7) := by
  obtain ⟨hlo, hhi⟩ := sin_three_sevenths_bounds
  have hs0 : 0 ≤ Real.sin ((3 : ℝ) / 7) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
      (by nlinarith [Real.pi_gt_d2])
  have hcube : Real.sin ((3 : ℝ) / 7) ^ 3 ≤
      ((3 : ℝ) / 7 - ((3 : ℝ) / 7) ^ 3 / 6 +
        ((3 : ℝ) / 7) ^ 4 * (5 / 96)) ^ 3 := by
    exact pow_le_pow_left₀ hs0 hhi 3
  rw [show (9 : ℝ) / 7 = 3 * (3 / 7) by ring,
    Real.sin_three_mul]
  nlinarith

private lemma scaled_le_sin_on_central {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ (9 : ℝ) / 7) :
    (7393 : ℝ) / 10000 * x ≤ Real.sin x := by
  let a : ℝ := 9 / 7
  let b : ℝ := x / a
  have ha0 : 0 < a := by norm_num [a]
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    exact (div_le_one ha0).2 (by simpa [a] using hx)
  have haPi : a ≤ Real.pi := by
    dsimp [a]
    nlinarith [Real.pi_gt_d2]
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
    (show a ∈ Set.Icc 0 Real.pi by exact ⟨ha0.le, haPi⟩)
    (sub_nonneg.mpr hb1) hb0 (by ring : (1 - b) + b = 1)
  simp only [Real.sin_zero, smul_eq_mul, mul_zero, zero_add] at hconc
  have hba : b * a = x := by
    dsimp [b]
    field_simp
  rw [hba] at hconc
  have ha : (7393 : ℝ) / 10000 * a < Real.sin a := by
    simpa [a] using sin_nine_sevenths_gt
  have hscaled : (7393 : ℝ) / 10000 * x ≤ b * Real.sin a := by
    have := mul_le_mul_of_nonneg_left ha.le hb0
    calc
      (7393 : ℝ) / 10000 * x = b * ((7393 : ℝ) / 10000 * a) := by
        rw [← hba]
        ring
      _ ≤ b * Real.sin a := this
  exact hscaled.trans hconc

private lemma sin_small_ge (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 350) :
    (9999 : ℝ) / 10000 * x ≤ Real.sin x := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; linarith
  have h := Real.sin_bound hx1
  rw [abs_of_nonneg hx0] at h
  have hlower := neg_le_of_abs_le h
  have hx2 : x ^ 2 ≤ (1 / 350 : ℝ) ^ 2 :=
    (sq_le_sq₀ hx0 (by norm_num)).2 hx
  have hx3 : x ^ 3 ≤ x * (1 / 350 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg x]
  have hx4 : x ^ 4 ≤ x * (1 / 350 : ℝ) ^ 3 := by
    have hx3' : x ^ 3 ≤ (1 / 350 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hx0 hx 3
    nlinarith
  nlinarith

/-- The boundary-matched kernel is uniformly positive throughout the
central normalized chamber `|y| ≤ 9/22` at every decimal scale `10^k`,
`k ≥ 3`. -/
theorem boundaryMinorant_re_gt_4859_div_10000
    (k : ℕ) (hk : 3 ≤ k) (y : ℝ) (hy : |y| ≤ 9 / 22) :
    (4859 : ℝ) / 10000 <
      (boundaryMinorant (10 ^ k) (y / (10 ^ k : ℕ))).re := by
  let q : ℕ := 10 ^ k
  have hq : 1000 ≤ q := by
    calc
      1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq0 : 0 < q := by positivity
  have hqR : (0 : ℝ) < q := by positivity
  by_cases hy0 : y = 0
  · subst y
    rw [zero_div, boundaryMinorant_eq q hq0]
    norm_num
    have hfejer : fejerFactor q 0 = q := by
      unfold fejerFactor geometricSum
      simp [Theory.PiDigits.T27.phase]
    rw [hfejer]
    norm_num
    push_cast
    have hcast : (Real.pi : ℂ) / (q : ℂ) =
        ((Real.pi / (q : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    have hpow : ((q : ℂ) ^ 2) = (((q : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, hpow, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    have hcos := Theory.PiDigits.BoundaryMatchedKernel.two_div_sq_le_one_sub_cos_pi_div
      q hq0
    have htwo : (2 : ℝ) ≤ (q : ℝ) ^ 2 *
        (1 - Real.cos (Real.pi / q)) := by
      calc
        (2 : ℝ) = (q : ℝ) ^ 2 * (2 / (q : ℝ) ^ 2) := by
          field_simp [ne_of_gt hqR]
        _ ≤ _ := mul_le_mul_of_nonneg_left hcos (sq_nonneg (q : ℝ))
    rw [div_eq_mul_inv] at htwo
    nlinarith
  · let u : ℝ := |y|
    let a : ℝ := Real.pi * (1 + 2 * u) / (2 * q)
    let b : ℝ := Real.pi * (1 - 2 * u) / (2 * q)
    have hu0 : 0 ≤ u := abs_nonneg y
    have hu : u ≤ 9 / 22 := by simpa [u] using hy
    have huHalf : u < 1 / 2 := by dsimp [u] at hu ⊢; linarith
    have huPi : Real.pi * u ≤ 9 / 7 := by
      have hpi := pi_lt_twenty_two_sevenths
      have := mul_le_mul_of_nonneg_right hpi.le hu0
      nlinarith
    have hsinc : (7393 : ℝ) / 10000 * (Real.pi * u) ≤
        Real.sin (Real.pi * u) :=
      scaled_le_sin_on_central (mul_nonneg Real.pi_pos.le hu0) huPi
    have ha0 : 0 < a := by dsimp [a]; positivity
    have hb0 : 0 < b := by
      dsimp [b]
      exact div_pos (mul_pos Real.pi_pos (by linarith)) (by positivity)
    have haSmall : a ≤ 1 / 350 := by
      dsimp [a]
      have hpi := pi_lt_twenty_two_sevenths
      have hqR' : (1000 : ℝ) ≤ q := by exact_mod_cast hq
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
      nlinarith
    have hbSmall : b ≤ 1 / 350 := by
      dsimp [b]
      have hpi := pi_lt_twenty_two_sevenths
      have hqR' : (1000 : ℝ) ≤ q := by exact_mod_cast hq
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
      nlinarith
    have hsinA := sin_small_ge a ha0.le haSmall
    have hsinB := sin_small_ge b hb0.le hbSmall
    have hsinA0 : 0 ≤ Real.sin a := hsinA.trans' (by positivity)
    have hsinB0 : 0 ≤ Real.sin b := hsinB.trans' (by positivity)
    have hcosGap :
        ((9999 : ℝ) / 10000) ^ 2 *
            Real.pi ^ 2 * (1 - 4 * u ^ 2) / (2 * (q : ℝ) ^ 2) ≤
          Real.cos (2 * Real.pi * (u / q)) - Real.cos (Real.pi / q) := by
      have hmul := mul_le_mul hsinA hsinB (by positivity) hsinA0
      rw [Real.cos_sub_cos]
      have hrewrite :
          -2 * Real.sin ((2 * Real.pi * (u / q) + Real.pi / q) / 2) *
              Real.sin ((2 * Real.pi * (u / q) - Real.pi / q) / 2) =
            2 * Real.sin a * Real.sin b := by
        dsimp [a, b]
        rw [show (2 * Real.pi * (u / q) + Real.pi / q) / 2 =
              Real.pi * (1 + 2 * u) / (2 * q) by field_simp <;> ring,
          show (2 * Real.pi * (u / q) - Real.pi / q) / 2 =
              -(Real.pi * (1 - 2 * u) / (2 * q)) by field_simp <;> ring,
          Real.sin_neg]
        ring
      rw [hrewrite]
      dsimp [a, b] at hmul
      field_simp at hmul ⊢
      nlinarith [sq_pos_of_pos hqR]
    have hdenSin : Real.sin (Real.pi * (u / q)) ≤ Real.pi * (u / q) := by
      apply Real.sin_le
      positivity
    have hden0 : 0 < Real.sin (Real.pi * (u / q)) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · dsimp [u]
        positivity
      · have huq : u / q < 1 := by
          apply (div_lt_one hqR).2
          have hqR' : (1000 : ℝ) ≤ q := by exact_mod_cast hq
          linarith
        nlinarith [Real.pi_pos]
    have hnum0 : 0 ≤ Real.sin (Real.pi * u) := by
      exact hsinc.trans' (by positivity)
    have hfejerLower :
        (q : ℝ) * ((7393 : ℝ) / 10000) ^ 2 ≤
          Real.sin (Real.pi * u) ^ 2 /
            ((q : ℝ) * Real.sin (Real.pi * (u / q)) ^ 2) := by
      have hnumSq := (sq_le_sq₀ (by positivity) hnum0).2 hsinc
      have hdenSq := (sq_le_sq₀ hden0.le (by positivity)).2 hdenSin
      have hdenSqPos : 0 < Real.sin (Real.pi * (u / q)) ^ 2 :=
        sq_pos_of_pos hden0
      apply (le_div_iff₀ (mul_pos hqR hdenSqPos)).2
      calc
        (q : ℝ) * ((7393 : ℝ) / 10000) ^ 2 *
              ((q : ℝ) * Real.sin (Real.pi * (u / q)) ^ 2) =
            (q : ℝ) ^ 2 * ((7393 : ℝ) / 10000) ^ 2 *
              Real.sin (Real.pi * (u / q)) ^ 2 := by ring
        _ ≤ (q : ℝ) ^ 2 * ((7393 : ℝ) / 10000) ^ 2 *
              (Real.pi * (u / q)) ^ 2 :=
          mul_le_mul_of_nonneg_left hdenSq (by positivity)
        _ = ((7393 : ℝ) / 10000 * (Real.pi * u)) ^ 2 := by
          field_simp
        _ ≤ Real.sin (Real.pi * u) ^ 2 := hnumSq
    have hfejer0 : 0 ≤
        Real.sin (Real.pi * u) ^ 2 /
          ((q : ℝ) * Real.sin (Real.pi * (u / q)) ^ 2) := by positivity
    have hkernel :
        ((9999 : ℝ) / 10000) ^ 2 * Real.pi ^ 2 *
              (1 - 4 * u ^ 2) / (2 * (q : ℝ) ^ 2) *
            ((q : ℝ) * ((7393 : ℝ) / 10000) ^ 2) ^ 2 ≤
          (Real.cos (2 * Real.pi * (u / q)) - Real.cos (Real.pi / q)) *
            (Real.sin (Real.pi * u) ^ 2 /
              ((q : ℝ) * Real.sin (Real.pi * (u / q)) ^ 2)) ^ 2 := by
      have hgap0 : 0 ≤
          ((9999 : ℝ) / 10000) ^ 2 * Real.pi ^ 2 *
            (1 - 4 * u ^ 2) / (2 * (q : ℝ) ^ 2) := by
        have : 0 ≤ 1 - 4 * u ^ 2 := by nlinarith [sq_nonneg u]
        positivity
      have hfejerSq := (sq_le_sq₀ (by positivity) hfejer0).2 hfejerLower
      calc
        _ ≤ (Real.cos (2 * Real.pi * (u / q)) - Real.cos (Real.pi / q)) *
              ((q : ℝ) * ((7393 : ℝ) / 10000) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hcosGap (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hfejerSq (hgap0.trans hcosGap)
    have hnumeric : (4859 : ℝ) / 10000 <
        ((9999 : ℝ) / 10000) ^ 2 * (157 / 50 : ℝ) ^ 2 *
          (40 / 121) / 2 * ((7393 : ℝ) / 10000) ^ 4 := by norm_num
    have hpi : (157 / 50 : ℝ) ^ 2 < Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_d2]
    have hshape : (40 / 121 : ℝ) ≤ 1 - 4 * u ^ 2 := by
      nlinarith [sq_nonneg (9 / 22 - u), sq_nonneg (9 / 22 + u)]
    have hlower : (4859 : ℝ) / 10000 <
        ((9999 : ℝ) / 10000) ^ 2 * Real.pi ^ 2 *
          (1 - 4 * u ^ 2) / 2 * ((7393 : ℝ) / 10000) ^ 4 := by
      have hpishape : (157 / 50 : ℝ) ^ 2 * (40 / 121) ≤
          Real.pi ^ 2 * (1 - 4 * u ^ 2) :=
        mul_le_mul hpi.le hshape (by norm_num) (sq_nonneg Real.pi)
      have hfactor : 0 ≤ ((9999 : ℝ) / 10000) ^ 2 / 2 *
          ((7393 : ℝ) / 10000) ^ 4 := by positivity
      apply hnumeric.trans_le
      have := mul_le_mul_of_nonneg_left hpishape hfactor
      convert this using 1 <;> ring
    have hsiny : Real.sin (Real.pi * y) ^ 2 = Real.sin (Real.pi * u) ^ 2 := by
      dsimp [u]
      by_cases hypos : 0 ≤ y
      · rw [abs_of_nonneg hypos]
      · rw [abs_of_neg (lt_of_not_ge hypos), show Real.pi * y =
            -(Real.pi * -y) by ring, Real.sin_neg]
        ring
    have hcosy : Real.cos (2 * Real.pi * (y / q)) =
        Real.cos (2 * Real.pi * (u / q)) := by
      dsimp [u]
      have habsarg : 2 * Real.pi * (|y| / q) = |2 * Real.pi * (y / q)| := by
        rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
          abs_of_pos hqR]
      rw [habsarg, Real.cos_abs]
    have hsinDen : Real.sin (Real.pi * (y / q)) ^ 2 =
        Real.sin (Real.pi * (u / q)) ^ 2 := by
      dsimp [u]
      by_cases hypos : 0 ≤ y
      · rw [abs_of_nonneg hypos]
      · rw [abs_of_neg (lt_of_not_ge hypos), show Real.pi * (y / q) =
            -(Real.pi * (-y / q)) by ring, Real.sin_neg]
        ring
    have hsinNonzero : Real.sin (Real.pi * (y / q)) ≠ 0 := by
      intro hzero
      have hsquare : Real.sin (Real.pi * (y / q)) ^ 2 = 0 := by simp [hzero]
      have hsquarePos : 0 < Real.sin (Real.pi * (y / q)) ^ 2 := by
        rw [hsinDen]
        exact sq_pos_of_pos hden0
      exact (ne_of_gt hsquarePos) hsquare
    rw [boundaryMinorant_re_eq_closed_sine q hq0 (y / q) hsinNonzero]
    rw [show Real.pi * q * (y / q) = Real.pi * y by field_simp]
    rw [hsiny, hcosy, hsinDen]
    have hscaled :
        ((9999 : ℝ) / 10000) ^ 2 * Real.pi ^ 2 *
              (1 - 4 * u ^ 2) / 2 * ((7393 : ℝ) / 10000) ^ 4 =
          ((9999 : ℝ) / 10000) ^ 2 * Real.pi ^ 2 *
              (1 - 4 * u ^ 2) / (2 * (q : ℝ) ^ 2) *
            ((q : ℝ) * ((7393 : ℝ) / 10000) ^ 2) ^ 2 := by
      field_simp [ne_of_gt hqR]
    rw [hscaled] at hlower
    exact hlower.trans_le hkernel

end Theory.PiDigits.T191CentralBoundaryKernelFloor

#print axioms Theory.PiDigits.T191CentralBoundaryKernelFloor.boundaryMinorant_re_gt_4859_div_10000
