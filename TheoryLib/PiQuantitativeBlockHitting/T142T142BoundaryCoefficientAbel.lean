import TheoryLib.PiQuantitativeBlockHitting.T138T138PrimitiveRayCoefficientGap

/-!
# T142: boundary-coefficient Abel bounds

This module supplies the coefficient-side input for the two-scale endpoint
analysis following T139.  It proves a uniform upper bound and the one-peak
shape of the actual positive T128 coefficients, including every positively
dilated sampled sequence.  Abel summation and the later endpoint theorem are
deliberately not included here.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.BoundaryCoefficientAbel

open Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra
open Theory.PiDigits.EdgeFrequencyFibers
open Theory.PiDigits.PrimitiveRayCoefficientGap

private lemma one_sub_cos_pi_div_lt_five_div_sq
    (q : ℕ) (hq : 0 < q) :
    1 - Real.cos (Real.pi / q) < 5 / (q : ℝ) ^ 2 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / q)
  have hpi := Real.pi_lt_d2
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpiSq : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
  have hsq : (Real.pi / q) ^ 2 / 2 < 5 / (q : ℝ) ^ 2 := by
    field_simp
    nlinarith [sq_pos_of_pos hqR]
  linarith

/-- At natural decimal scales the cosine deficit is already large enough to
force the last first-branch coefficient difference to be negative. -/
theorem three_lt_one_sub_cos_pi_div_mul
    (q : ℕ) (hq : 1000 ≤ q) :
    3 < (1 - Real.cos (Real.pi / q)) * q * (q + 1) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  let y : ℝ := Real.pi / (2 * q)
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hyUpper : y < 2 / (q : ℝ) := by
    dsimp [y]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
    field_simp
    nlinarith [Real.pi_lt_four]
  have hyOne : y ≤ 1 := by
    have htwoDiv : 2 / (q : ℝ) ≤ 1 := by
      exact (div_le_one hqR).2 (by exact_mod_cast (show 2 ≤ q by omega))
    linarith
  have hsinRaw := Real.sin_gt_sub_cube hy0 hyOne
  have hyLower : 157 / (100 * (q : ℝ)) < y := by
    dsimp [y]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 100 * q)).2
    field_simp
    nlinarith [Real.pi_gt_d2]
  have hyCube : y ^ 3 < 8 / (q : ℝ) ^ 3 := by
    have hright : (0 : ℝ) < 2 / q := by positivity
    have hp := pow_lt_pow_left₀ hyUpper hy0.le (by norm_num : 3 ≠ 0)
    convert hp using 1 <;> ring
  have hsinLower : 3 / (2 * (q : ℝ)) < Real.sin y := by
    have hqSq : (1000000 : ℝ) ≤ (q : ℝ) ^ 2 := by
      have hs := Nat.mul_self_le_mul_self hq
      norm_num [pow_two] at hs ⊢
      exact_mod_cast hs
    have hpre : 3 / (2 * (q : ℝ)) < y - y ^ 3 / 4 := by
      field_simp at hyLower hyCube hqSq ⊢
      nlinarith
    exact hpre.trans hsinRaw
  have hsin0 : 0 < Real.sin y := lt_trans (by positivity) hsinLower
  have hsinSq : (3 / (2 * (q : ℝ))) ^ 2 < Real.sin y ^ 2 :=
    (sq_lt_sq₀ (by positivity) hsin0.le).2 hsinLower
  have hcos : Real.cos (Real.pi / q) = 1 - 2 * Real.sin y ^ 2 := by
    rw [show Real.pi / (q : ℝ) = 2 * y by
      dsimp [y]
      field_simp]
    exact Real.cos_two_mul_eq_one_sub y
  rw [hcos]
  have hqPlus : (0 : ℝ) < q + 1 := by positivity
  field_simp at hsinSq ⊢
  nlinarith [mul_pos hqR hqPlus]

private lemma boundary_shape_polynomial_lt
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (5 / 2 : ℝ) * x ^ 3 - 5 * x ^ 2 + 3 / 2 * x + 7 / 3 < 59 / 24 := by
  have hsquare : 0 ≤ (x - 1 / 6) ^ 2 := sq_nonneg _
  by_cases hxSixth : x ≤ 1 / 6
  · have hcube : x ^ 3 ≤ (1 / 6) * x ^ 2 := by
      nlinarith [mul_nonneg hx0 (sq_nonneg x)]
    nlinarith
  · by_cases hxFifth : x ≤ 1 / 5
    · have hy0 : 0 ≤ x - 1 / 6 := by linarith
      have hy : x - 1 / 6 ≤ 1 / 30 := by linarith
      have hy2 : (x - 1 / 6) ^ 2 ≤ (1 / 30) ^ 2 :=
        (sq_le_sq₀ hy0 (by norm_num)).2 hy
      have hy3 : (x - 1 / 6) ^ 3 ≤ (1 / 30) ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_left hy2 hy0
        have hmul' := mul_le_mul_of_nonneg_right hy (sq_nonneg (1 / 30 : ℝ))
        nlinarith
      nlinarith
    · have hleft : 0 ≤ 1 - x := by linarith
      have hright : 0 ≤ 5 * x - 1 := by linarith
      have hprod : 0 ≤ (1 - x) * (5 * x - 1) := mul_nonneg hleft hright
      nlinarith

private lemma fejerSquareCoefficient_nonneg
    (q h : ℕ) (hq : 0 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    0 ≤ fejerSquareCoefficient q h := by
  rw [← Theory.PiDigits.MainFrequencyFibers.aggregatedFejerSquareCoefficient_eq
    q h hq hh0 hhsupp,
    Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.aggregatedFejerSquareCoefficient_eq_card]
  positivity

/-- Closed piecewise formula for the actual positive T128 coefficient. -/
theorem positiveBoundaryCoefficient_eq_piecewise
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    positiveBoundaryCoefficient q h =
      if h ≤ q then
        (1 - Real.cos (Real.pi / q)) *
            (4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
              3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2) +
          (3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2)
      else
        (1 - Real.cos (Real.pi / q)) *
            ((2 * q - h - 1 : ℝ) * (2 * q - h : ℝ) *
              (2 * q - h + 1 : ℝ)) / (6 * (q : ℝ) ^ 2) +
          (2 * q - h : ℝ) / (2 * (q : ℝ) ^ 2) := by
  rw [positiveBoundaryCoefficient,
    aggregatedBoundaryCoefficient_eq_affine q h hq hh0 hhsupp]
  unfold affineCoefficient
  rw [show neighboringCoefficient q h - Real.cos (Real.pi / q) *
      fejerSquareCoefficient q h =
      (1 - Real.cos (Real.pi / q)) * fejerSquareCoefficient q h +
        (neighboringCoefficient q h - fejerSquareCoefficient q h) by ring,
    ← signedEdgeCoefficient_eq_neighboring_sub q h hq hh0 hhsupp,
    signedEdgeCoefficient_eq_piecewise q h (by omega) hh0 hhsupp]
  by_cases hhq : h ≤ q
  · simp only [if_pos hhq]
    unfold fejerSquareCoefficient cubicMultiplicity
    rw [if_pos hhq]
    ring
  · simp only [if_neg hhq]
    unfold fejerSquareCoefficient cubicMultiplicity
    rw [if_neg hhq]
    ring

/-- Exact first difference on the rising-side formula.  This is the algebraic
input for the remaining one-peak argument; no monotonicity is assumed here. -/
theorem positiveBoundaryCoefficient_succ_sub_eq
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsucc : h + 1 ≤ q) :
    2 * (q : ℝ) ^ 2 *
        (positiveBoundaryCoefficient q (h + 1) - positiveBoundaryCoefficient q h) =
      3 + (1 - Real.cos (Real.pi / q)) *
        (3 * (h : ℝ) ^ 2 + (3 - 4 * q) * h - 2 * q) := by
  have hq0 : 0 < q := by omega
  have hh1 : 0 < h + 1 := by omega
  have hhsupp : h ≤ 2 * q - 1 := by omega
  have hhsuccsupp : h + 1 ≤ 2 * q - 1 := by omega
  rw [positiveBoundaryCoefficient_eq_piecewise q (h + 1) hq hh1 hhsuccsupp,
    positiveBoundaryCoefficient_eq_piecewise q h hq hh0 hhsupp]
  simp only [if_pos hhsucc, if_pos (show h ≤ q by omega)]
  push_cast
  field_simp [show (q : ℝ) ≠ 0 by positivity]
  ring

private def firstDifferenceShape (q h : ℕ) : ℝ :=
  3 + (1 - Real.cos (Real.pi / q)) *
    (3 * (h : ℝ) ^ 2 + (3 - 4 * q) * h - 2 * q)

private lemma firstDifferenceShape_last_neg
    (q : ℕ) (hq : 1000 ≤ q) :
    firstDifferenceShape q (q - 1) < 0 := by
  have hq0 : 1 ≤ q := by omega
  have hcos := three_lt_one_sub_cos_pi_div_mul q hq
  rw [firstDifferenceShape, Nat.cast_sub hq0]
  push_cast
  nlinarith

/-- Once the first-branch difference shape becomes negative, it remains
negative through the end of that branch. -/
private theorem firstDifferenceShape_neg_persistent
    (q h j : ℕ) (hq : 1000 ≤ q) (hhj : h ≤ j) (hjq : j ≤ q - 1)
    (hhneg : firstDifferenceShape q h < 0) :
    firstDifferenceShape q j < 0 := by
  have hq0 : 1 ≤ q := by omega
  have hdelta : 0 ≤ 1 - Real.cos (Real.pi / q) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  by_cases hjThird : q ≤ 3 * j
  · have hjqR : (j : ℝ) ≤ q - 1 := by exact_mod_cast hjq
    have hjThirdR : (q : ℝ) ≤ 3 * j := by exact_mod_cast hjThird
    have hleft : (j : ℝ) - (q - 1) ≤ 0 := by linarith
    have hright : 0 ≤ 3 * (j : ℝ) - q := by linarith
    have hprod :
        (1 - Real.cos (Real.pi / q)) * ((j : ℝ) - (q - 1)) *
          (3 * (j : ℝ) - q) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hdelta hleft) hright
    have hidentity :
        firstDifferenceShape q j - firstDifferenceShape q (q - 1) =
          (1 - Real.cos (Real.pi / q)) * ((j : ℝ) - (q - 1)) *
            (3 * (j : ℝ) - q) := by
      rw [firstDifferenceShape, firstDifferenceShape, Nat.cast_sub hq0]
      push_cast
      ring
    have hend := firstDifferenceShape_last_neg q hq
    rw [← hidentity] at hprod
    linarith
  · have hjThird : 3 * j < q := by omega
    have hhjR : (h : ℝ) ≤ j := by exact_mod_cast hhj
    have hbracket :
        3 * ((j : ℝ) + h) + 3 - 4 * q ≤ 0 := by
      have hjThirdR : 3 * (j : ℝ) < q := by exact_mod_cast hjThird
      have hqR : (1000 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    have hgap : 0 ≤ (j : ℝ) - h := by linarith
    have hprod :
        (1 - Real.cos (Real.pi / q)) * ((j : ℝ) - h) *
          (3 * ((j : ℝ) + h) + 3 - 4 * q) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hdelta hgap) hbracket
    have hidentity :
        firstDifferenceShape q j - firstDifferenceShape q h =
          (1 - Real.cos (Real.pi / q)) * ((j : ℝ) - h) *
            (3 * ((j : ℝ) + h) + 3 - 4 * q) := by
      rw [firstDifferenceShape, firstDifferenceShape]
      ring
    rw [← hidentity] at hprod
    linarith

/-- Exact first difference on the decreasing tail of the coefficient profile. -/
theorem positiveBoundaryCoefficient_succ_sub_eq_tail
    (q h : ℕ) (hq : 1 < q) (hhq : q ≤ h) (hhsucc : h + 1 ≤ 2 * q - 1) :
    2 * (q : ℝ) ^ 2 *
        (positiveBoundaryCoefficient q (h + 1) - positiveBoundaryCoefficient q h) =
      -(1 + (1 - Real.cos (Real.pi / q)) *
        ((2 * q - h : ℕ) : ℝ) * ((2 * q - h - 1 : ℕ) : ℝ)) := by
  have hh0 : 0 < h := by omega
  have hh1 : 0 < h + 1 := by omega
  have hhsupp : h ≤ 2 * q - 1 := by omega
  rw [positiveBoundaryCoefficient_eq_piecewise q (h + 1) hq hh1 hhsucc,
    positiveBoundaryCoefficient_eq_piecewise q h hq hh0 hhsupp]
  simp only [if_neg (show ¬h + 1 ≤ q by omega)]
  by_cases hhEq : h = q
  · subst h
    simp only [if_pos (le_refl q)]
    rw [show 2 * q - q = q by omega, show q - 1 = q - 1 by rfl,
      Nat.cast_sub (show 1 ≤ q by omega)]
    push_cast
    field_simp [show (q : ℝ) ≠ 0 by positivity]
    ring

  · simp only [if_neg (show ¬h ≤ q by omega)]
    have hh2q : h ≤ 2 * q := by omega
    have htcast : (((2 * q - h : ℕ) : ℝ)) = 2 * (q : ℝ) - h := by
      rw [Nat.cast_sub hh2q]
      push_cast
      ring
    have htmcast : (((2 * q - h - 1 : ℕ) : ℝ)) = 2 * (q : ℝ) - h - 1 := by
      rw [Nat.cast_sub (show 1 ≤ 2 * q - h by omega), htcast]
      norm_num
    rw [htcast, htmcast]
    push_cast
    field_simp [show (q : ℝ) ≠ 0 by positivity]
    ring

/-- The entire second branch of the boundary profile is strictly decreasing. -/
theorem positiveBoundaryCoefficient_succ_lt_tail
    (q h : ℕ) (hq : 1 < q) (hhq : q ≤ h) (hhsucc : h + 1 ≤ 2 * q - 1) :
    positiveBoundaryCoefficient q (h + 1) < positiveBoundaryCoefficient q h := by
  have hdiff := positiveBoundaryCoefficient_succ_sub_eq_tail q h hq hhq hhsucc
  have hdelta : 0 ≤ 1 - Real.cos (Real.pi / q) := sub_nonneg.mpr (Real.cos_le_one _)
  have hqR : (0 : ℝ) < q := by positivity
  have hprod : 0 ≤ (1 - Real.cos (Real.pi / q)) *
      ((2 * q - h : ℕ) : ℝ) * ((2 * q - h - 1 : ℕ) : ℝ) := by positivity
  nlinarith [sq_pos_of_pos hqR]

/-- The positive boundary coefficients have one peak: they are nondecreasing
before a peak index in the first branch and strictly decreasing afterwards. -/
theorem positiveBoundaryCoefficient_exists_peak
    (q : ℕ) (hq : 1000 ≤ q) :
    ∃ p, 1 ≤ p ∧ p ≤ q - 1 ∧
      (∀ h, 1 ≤ h → h < p →
        positiveBoundaryCoefficient q h ≤ positiveBoundaryCoefficient q (h + 1)) ∧
      (∀ h, p ≤ h → h ≤ 2 * q - 2 →
        positiveBoundaryCoefficient q (h + 1) < positiveBoundaryCoefficient q h) := by
  classical
  let P : ℕ → Prop := fun h =>
    1 ≤ h ∧ h ≤ q - 1 ∧ firstDifferenceShape q h < 0
  have hP : ∃ h, P h := by
    refine ⟨q - 1, ?_⟩
    exact ⟨by omega, le_rfl, firstDifferenceShape_last_neg q hq⟩
  let p := Nat.find hP
  have hp := Nat.find_spec hP
  refine ⟨p, hp.1, hp.2.1, ?_, ?_⟩
  · intro h hh1 hhp
    have hhq : h ≤ q - 1 := le_trans (Nat.le_of_lt hhp) hp.2.1
    have hnP := Nat.find_min hP hhp
    have hg : 0 ≤ firstDifferenceShape q h := by
      by_contra hneg
      exact hnP ⟨hh1, hhq, lt_of_not_ge hneg⟩
    have hdiff := positiveBoundaryCoefficient_succ_sub_eq q h
      (by omega) (by omega) (by omega)
    change 2 * (q : ℝ) ^ 2 *
        (positiveBoundaryCoefficient q (h + 1) - positiveBoundaryCoefficient q h) =
      firstDifferenceShape q h at hdiff
    have hqR : (0 : ℝ) < q := by positivity
    nlinarith [sq_pos_of_pos hqR]
  · intro h hph hhLast
    by_cases hhq : h < q
    · have hhBranch : h ≤ q - 1 := by omega
      have hg := firstDifferenceShape_neg_persistent q p h hq hph hhBranch hp.2.2
      have hdiff := positiveBoundaryCoefficient_succ_sub_eq q h
        (by omega) (by omega) (by omega)
      change 2 * (q : ℝ) ^ 2 *
          (positiveBoundaryCoefficient q (h + 1) - positiveBoundaryCoefficient q h) =
        firstDifferenceShape q h at hdiff
      have hqR : (0 : ℝ) < q := by positivity
      nlinarith [sq_pos_of_pos hqR]
    · exact positiveBoundaryCoefficient_succ_lt_tail q h (by omega) (by omega) (by omega)

private lemma interval_mono_of_succ
    (a : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j)
    (hstep : ∀ n, i ≤ n → n < j → a n ≤ a (n + 1)) :
    a i ≤ a j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
      exact (ih fun m him hmn => hstep m him (lt_trans hmn (Nat.lt_succ_self n))).trans
        (hstep n hin (Nat.lt_succ_self n))

private lemma interval_antitone_of_succ
    (a : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j)
    (hstep : ∀ n, i ≤ n → n < j → a (n + 1) ≤ a n) :
    a j ≤ a i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
      exact (hstep n hin (Nat.lt_succ_self n)).trans
        (ih fun m him hmn => hstep m him (lt_trans hmn (Nat.lt_succ_self n)))

/-- A peak-free formulation of unimodality: no middle coefficient lies below
both endpoints of an ordered triple in the positive support. -/
theorem positiveBoundaryCoefficient_quasiconcave
    (q i j k : ℕ) (hq : 1000 ≤ q) (hi : 1 ≤ i)
    (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ 2 * q - 1) :
    min (positiveBoundaryCoefficient q i) (positiveBoundaryCoefficient q k) ≤
      positiveBoundaryCoefficient q j := by
  obtain ⟨p, hp1, hpq, hincr, hdecr⟩ :=
    positiveBoundaryCoefficient_exists_peak q hq
  by_cases hjp : j < p
  · have hmono : positiveBoundaryCoefficient q i ≤ positiveBoundaryCoefficient q j := by
      apply interval_mono_of_succ (positiveBoundaryCoefficient q) hij
      intro n hin hnj
      exact hincr n (le_trans hi hin) (lt_trans hnj hjp)
    exact (min_le_left _ _).trans hmono
  · have hpj : p ≤ j := by omega
    have hanti : positiveBoundaryCoefficient q k ≤ positiveBoundaryCoefficient q j := by
      apply interval_antitone_of_succ (positiveBoundaryCoefficient q) hjk
      intro n hjn hnk
      apply (hdecr n (le_trans hpj hjn) (by omega)).le
    exact (min_le_right _ _).trans hanti

/-- Sampling the coefficient profile along any positive dilation preserves its
one-peak shape.  The statement includes the full supported sample range. -/
theorem sampled_positiveBoundaryCoefficient_quasiconcave
    (q d i j k : ℕ) (hq : 1000 ≤ q) (hd : 0 < d) (hi : 1 ≤ i)
    (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ (2 * q - 1) / d) :
    min (positiveBoundaryCoefficient q (d * i))
        (positiveBoundaryCoefficient q (d * k)) ≤
      positiveBoundaryCoefficient q (d * j) := by
  apply positiveBoundaryCoefficient_quasiconcave q (d * i) (d * j) (d * k) hq
  · exact Nat.mul_pos hd (by omega)
  · exact Nat.mul_le_mul_left d hij
  · exact Nat.mul_le_mul_left d hjk
  · have hmul := (Nat.le_div_iff_mul_le hd).1 hk
    simpa [Nat.mul_comm] using hmul

/-- Every actual positive-frequency coefficient of the T128 boundary kernel
is uniformly smaller than `5/(2q)`. -/
theorem positiveBoundaryCoefficient_lt_five_div_two_mul
    (q h : ℕ) (hq : 1000 ≤ q) (hh0 : 1 ≤ h) (hhsupp : h ≤ 2 * q - 1) :
    positiveBoundaryCoefficient q h < 5 / (2 * (q : ℝ)) := by
  have hq0 : 0 < q := by omega
  have hq1 : 1 < q := by omega
  have hhpos : 0 < h := by omega
  rw [positiveBoundaryCoefficient,
    aggregatedBoundaryCoefficient_eq_affine q h hq1 hhpos hhsupp]
  unfold affineCoefficient
  rw [show neighboringCoefficient q h - Real.cos (Real.pi / q) *
      fejerSquareCoefficient q h =
      (1 - Real.cos (Real.pi / q)) * fejerSquareCoefficient q h +
        (neighboringCoefficient q h - fejerSquareCoefficient q h) by ring,
    ← signedEdgeCoefficient_eq_neighboring_sub q h hq1 hhpos hhsupp,
    signedEdgeCoefficient_eq_piecewise q h hq0 hhpos hhsupp]
  have hdelta := one_sub_cos_pi_div_lt_five_div_sq q hq0
  have hB0 := fejerSquareCoefficient_nonneg q h hq0 hhpos hhsupp
  have hgain :
      (1 - Real.cos (Real.pi / q)) * fejerSquareCoefficient q h ≤
        (5 / (q : ℝ) ^ 2) * fejerSquareCoefficient q h :=
    mul_le_mul_of_nonneg_right hdelta.le hB0
  by_cases hhq : h ≤ q
  · rw [if_pos hhq]
    have hqR : (0 : ℝ) < q := by positivity
    have hx0 : 0 ≤ (h : ℝ) / q := by positivity
    have hx1 : (h : ℝ) / q ≤ 1 := by
      exact (div_le_one hqR).2 (by exact_mod_cast hhq)
    have hshape := boundary_shape_polynomial_lt hx0 hx1
    have hBform : fejerSquareCoefficient q h =
        (4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
          3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2) := by
      unfold fejerSquareCoefficient cubicMultiplicity
      rw [if_pos hhq]
      ring
    have hsmall : (10 - 15 * ((h : ℝ) / q)) / (6 * (q : ℝ) ^ 2) ≤
        1 / 600000 := by
      have hqSq : (1000000 : ℝ) ≤ (q : ℝ) ^ 2 := by
        have := Nat.mul_self_le_mul_self hq
        norm_num [pow_two] at this ⊢
        exact_mod_cast this
      have hnum : 10 - 15 * ((h : ℝ) / q) ≤ 10 := by nlinarith
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * q ^ 2)).2
      nlinarith
    have hupper := add_le_add_right hgain
      ((3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2))
    have htarget :
        (1 - Real.cos (Real.pi / q)) * fejerSquareCoefficient q h +
            (3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2) ≤
          (5 / (q : ℝ) ^ 2) * fejerSquareCoefficient q h +
            (3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2) := by
      simpa [add_comm] using hupper
    rw [hBform] at htarget
    rw [show (5 / (q : ℝ) ^ 2) *
          ((4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
            3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2)) +
          (3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2) =
        ((5 / 2 : ℝ) * ((h : ℝ) / q) ^ 3 -
          5 * ((h : ℝ) / q) ^ 2 + 3 / 2 * ((h : ℝ) / q) + 7 / 3 +
          (10 - 15 * ((h : ℝ) / q)) / (6 * (q : ℝ) ^ 2)) / q by
      field_simp
      ring] at htarget
    have hqInv : (0 : ℝ) < (q : ℝ) := by positivity
    rw [hBform]
    apply lt_of_le_of_lt htarget
    rw [show 5 / (2 * (q : ℝ)) = (5 / 2 : ℝ) / q by ring]
    apply (div_lt_div_iff_of_pos_right hqInv).2
    nlinarith
  · rw [if_neg hhq]
    have hhq' : q < h := by omega
    have hgap : 0 < 2 * q - h := by omega
    have hy0 : (0 : ℝ) ≤ ((2 * q - h : ℕ) : ℝ) / q := by positivity
    have hy1 : ((2 * q - h : ℕ) : ℝ) / q ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < q)).2
      exact_mod_cast (show 2 * q - h ≤ q by omega)
    have hBform : fejerSquareCoefficient q h =
        (((2 * q - h - 1 : ℕ) : ℝ) * (2 * q - h : ℕ) *
          (2 * q - h + 1 : ℕ)) / (6 * (q : ℝ) ^ 2) := by
      have htcast : (((2 * q - h : ℕ) : ℝ)) = 2 * (q : ℝ) - h := by
        rw [Nat.cast_sub (by omega : h ≤ 2 * q)]
        push_cast
        ring
      have htmcast : (((2 * q - h - 1 : ℕ) : ℝ)) = 2 * (q : ℝ) - h - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * q - h), htcast]
        norm_num
      have htpcast : (((2 * q - h + 1 : ℕ) : ℝ)) = 2 * (q : ℝ) - h + 1 := by
        push_cast
        rw [htcast]
      unfold fejerSquareCoefficient cubicMultiplicity
      rw [if_neg hhq]
      rw [htcast, htmcast, htpcast]
      ring
    have hcasts :
        (((2 * q - h - 1 : ℕ) : ℝ) * (2 * q - h : ℕ) *
            (2 * q - h + 1 : ℕ)) ≤
          (((2 * q - h : ℕ) : ℝ) ^ 3) := by
      let t := 2 * q - h
      have ht : 1 ≤ t := by dsimp [t]; omega
      have hm : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub ht]
        norm_num
      have hp : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by norm_num
      change ((t - 1 : ℕ) : ℝ) * t * (t + 1 : ℕ) ≤ (t : ℝ) ^ 3
      rw [hm, hp]
      have htR : (0 : ℝ) ≤ t := by positivity
      nlinarith
    have hqR : (0 : ℝ) < q := by positivity
    have hupper := add_le_add_right hgain
      ((2 * q - h : ℝ) / (2 * (q : ℝ) ^ 2))
    have htarget :
        (1 - Real.cos (Real.pi / q)) * fejerSquareCoefficient q h +
            (2 * q - h : ℝ) / (2 * (q : ℝ) ^ 2) ≤
          (5 / (q : ℝ) ^ 2) * fejerSquareCoefficient q h +
            (2 * q - h : ℝ) / (2 * (q : ℝ) ^ 2) := by
      simpa [add_comm] using hupper
    rw [hBform] at htarget
    have hyCube : (((2 * q - h : ℕ) : ℝ) / q) ^ 3 ≤ 1 := by
      nlinarith [sq_nonneg ((((2 * q - h : ℕ) : ℝ) / q) - 1)]
    rw [show (5 / (q : ℝ) ^ 2) *
          ((((2 * q - h - 1 : ℕ) : ℝ) * (2 * q - h : ℕ) *
            (2 * q - h + 1 : ℕ)) / (6 * (q : ℝ) ^ 2)) +
          (2 * q - h : ℝ) / (2 * (q : ℝ) ^ 2) =
        (5 / 6 *
          ((((2 * q - h - 1 : ℕ) : ℝ) * (2 * q - h : ℕ) *
            (2 * q - h + 1 : ℕ)) / (q : ℝ) ^ 3) +
          (1 / 2) * (((2 * q - h : ℕ) : ℝ) / q)) / q by
      field_simp
      rw [Nat.cast_sub (by omega : h ≤ 2 * q)]
      push_cast
      ring] at htarget
    rw [hBform]
    apply lt_of_le_of_lt htarget
    rw [show 5 / (2 * (q : ℝ)) = (5 / 2 : ℝ) / q by ring]
    apply (div_lt_div_iff_of_pos_right hqR).2
    have hprodScaled :
        ((((2 * q - h - 1 : ℕ) : ℝ) * (2 * q - h : ℕ) *
          (2 * q - h + 1 : ℕ)) / (q : ℝ) ^ 3) ≤ 2 := by
      have hqCube : (0 : ℝ) < (q : ℝ) ^ 3 := by positivity
      apply (div_le_iff₀ hqCube).2
      have hgapCube : (((2 * q - h : ℕ) : ℝ) ^ 3) ≤ (q : ℝ) ^ 3 := by
        gcongr
        exact_mod_cast (show 2 * q - h ≤ q by omega)
      nlinarith
    nlinarith

end Theory.PiDigits.BoundaryCoefficientAbel

#print axioms Theory.PiDigits.BoundaryCoefficientAbel.positiveBoundaryCoefficient_lt_five_div_two_mul
