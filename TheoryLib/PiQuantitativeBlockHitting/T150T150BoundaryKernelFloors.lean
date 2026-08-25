import TheoryLib.PiQuantitativeBlockHitting.T149T149BoundaryRootGridProjection
import Mathlib.Analysis.Calculus.Taylor

/-!
# T150: explicit lower floors for the boundary kernel

This module proves the global and away-from-the-central-lobe lower bounds
used by the root-grid endpoint projection.  It contains no orbit-cancellation
claim.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace Theory.PiDigits.BoundaryKernelFloors

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.BoundaryMatchedKernel

abbrev phase := Theory.PiDigits.T27.phase

private lemma phase_nat_re_eq_cos (n : ℕ) (t : ℝ) :
    (phase (n : ℤ) t).re = Real.cos (2 * Real.pi * n * t) := by
  unfold phase Theory.PiDigits.T27.phase
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (t : ℂ) =
      (((2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  exact Complex.exp_ofReal_mul_I_re _

private lemma normSq_one_sub_phase_nat (n : ℕ) (t : ℝ) :
    Complex.normSq (1 - Theory.PiDigits.T27.phase (n : ℤ) t) =
      4 * Real.sin (Real.pi * n * t) ^ 2 := by
  have hnorm : Complex.normSq (phase (n : ℤ) t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Theory.PiDigits.T27.norm_phase]
    norm_num
  rw [Complex.normSq_sub, Complex.normSq_one, hnorm]
  simp only [one_mul, Complex.conj_re]
  rw [phase_nat_re_eq_cos]
  rw [show Real.cos (2 * Real.pi * n * t) =
      1 - 2 * Real.sin (Real.pi * n * t) ^ 2 by
    convert Real.cos_two_mul_eq_one_sub (Real.pi * n * t) using 1 <;> ring]
  ring

/-- Exact sine-quotient form of the normalized Fejer factor away from its
removable singularities. -/
theorem fejerFactor_eq_sine_quotient
    (q : ℕ) (hq : 0 < q) (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) :
    fejerFactor q t =
      Real.sin (Real.pi * q * t) ^ 2 /
        ((q : ℝ) * Real.sin (Real.pi * t) ^ 2) := by
  have hgeom := geometricSum_mul_one_sub_phase q t
  have hnorm := congrArg Complex.normSq hgeom
  rw [Complex.normSq_mul] at hnorm
  change Complex.normSq (geometricSum q t) *
      Complex.normSq (1 - Theory.PiDigits.T27.phase 1 t) =
    Complex.normSq (1 - Theory.PiDigits.T27.phase (q : ℤ) t) at hnorm
  have hone := normSq_one_sub_phase_nat 1 t
  norm_num at hone
  rw [hone, normSq_one_sub_phase_nat q] at hnorm
  norm_num at hnorm
  unfold fejerFactor
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsinSq : Real.sin (Real.pi * t) ^ 2 ≠ 0 := pow_ne_zero _ hsin
  have hnorm' : Complex.normSq (geometricSum q t) *
      Real.sin (Real.pi * t) ^ 2 = Real.sin (Real.pi * q * t) ^ 2 := by
    nlinarith
  field_simp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm'

private lemma boundaryMinorant_re_eq_sine_form
    (q : ℕ) (hq : 0 < q) (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) :
    (boundaryMinorant q t).re =
      (Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q)) *
        (Real.sin (Real.pi * q * t) ^ 2 /
          ((q : ℝ) * Real.sin (Real.pi * t) ^ 2)) ^ 2 := by
  rw [boundaryMinorant_eq q hq, fejerFactor_eq_sine_quotient q hq t hsin]
  rfl

private lemma sin_two_lt_ninety_one_hundred :
    Real.sin 2 < (91 : ℝ) / 100 := by
  obtain ⟨z, hz, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.sin) (x₀ := 0) (x := 2) (n := 9) (by norm_num : (0 : ℝ) ≠ 2)
    (Real.contDiff_sin.contDiffOn.of_le le_rfl)
  have hzIoo : z ∈ Set.Ioo (0 : ℝ) 2 := by
    simpa [uIoo] using hz
  have hzpi : z ≤ Real.pi := by
    exact hzIoo.2.le.trans (by nlinarith [Real.pi_gt_d2])
  have hsinz : 0 ≤ Real.sin z :=
    Real.sin_nonneg_of_nonneg_of_le_pi hzIoo.1.le hzpi
  have hpoly :
      taylorWithinEval Real.sin 9 (uIcc (0 : ℝ) 2) 0 2 =
        2 - 2 ^ 3 / 6 + 2 ^ 5 / 120 - 2 ^ 7 / 5040 + 2 ^ 9 / 362880 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2), taylor_within_apply]
    norm_num only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial]
    simp_rw [Real.iteratedDerivWithin_sin_Icc _ (by norm_num : (0 : ℝ) < 2)
      (show (0 : ℝ) ∈ Set.Icc 0 2 by norm_num)]
    norm_num [Real.iteratedDeriv_even_sin, Real.iteratedDeriv_odd_sin]
  rw [hpoly] at hTaylor
  have hderiv : iteratedDeriv 10 Real.sin z = -Real.sin z := by
    rw [show 10 = 2 * 5 by norm_num, Real.iteratedDeriv_even_sin]
    norm_num
  rw [hderiv] at hTaylor
  norm_num at hTaylor ⊢
  nlinarith

private lemma sine_fourth_le_one (x : ℝ) : Real.sin x ^ 4 ≤ 1 := by
  have hs0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have hs2 : Real.sin x ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
  nlinarith [sq_nonneg (1 - Real.sin x ^ 2)]

private lemma sine_le_sine_two_on_two_pi {y : ℝ}
    (hy2 : 2 ≤ y) (hypi : y ≤ Real.pi) :
    Real.sin y ≤ Real.sin 2 := by
  have hpi2 : Real.pi - y ≤ Real.pi / 2 := by
    nlinarith [Real.pi_lt_four]
  have hnonneg : 0 ≤ Real.pi - y := by linarith
  have hle : Real.pi - y ≤ Real.pi - 2 := by linarith
  have htop : Real.pi - 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_lt_four]
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by nlinarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi - y)
    htop hle
  rw [Real.sin_pi_sub, Real.sin_pi_sub] at hs
  exact hs

private lemma small_y_kernel_numerator_lt
    {y : ℝ} (hy0 : Real.pi / 2 < y) (hy5 : y ≤ 5) :
    (4 * y ^ 2 - Real.pi ^ 2) * Real.sin y ^ 4 <
      (48 / 125 : ℝ) * y ^ 4 := by
  have hypos : 0 < y := lt_trans (by positivity) hy0
  have hpiSqLow : (157 / 50 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_d2]
  by_cases hy2 : y ≤ 2
  · have hySq : y ^ 2 ≤ 4 := by nlinarith
    have hpoly : (48 / 125 : ℝ) * y ^ 4 > 4 * y ^ 2 - Real.pi ^ 2 := by
      have hfac : 48 * (y ^ 2 + 4) - 500 < 0 := by nlinarith
      have hprod : 0 ≤ (y ^ 2 - 4) * (48 * (y ^ 2 + 4) - 500) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      nlinarith
    have hsin := sine_fourth_le_one y
    have hcoef : 0 < 4 * y ^ 2 - Real.pi ^ 2 := by
      have hyPi : Real.pi < 2 * y := by nlinarith
      have hsquare := (sq_lt_sq₀ Real.pi_pos.le (by positivity : 0 ≤ 2 * y)).2 hyPi
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsin hcoef.le]
  · have hy2' : 2 < y := lt_of_not_ge hy2
    by_cases hypi : y ≤ Real.pi
    · have hsin0 : 0 ≤ Real.sin y :=
        Real.sin_nonneg_of_nonneg_of_le_pi hypos.le hypi
      have hsin : Real.sin y < (91 : ℝ) / 100 :=
        (sine_le_sine_two_on_two_pi hy2'.le hypi).trans_lt
          sin_two_lt_ninety_one_hundred
      have hsin4 : Real.sin y ^ 4 < ((91 : ℝ) / 100) ^ 4 := by
        exact pow_lt_pow_left₀ hsin hsin0 (by norm_num)
      have hratio : Real.pi ^ 2 * (4 * y ^ 2 - Real.pi ^ 2) ≤ 4 * y ^ 4 := by
        nlinarith [sq_nonneg (2 * y ^ 2 - Real.pi ^ 2)]
      have hcoef : 0 < 4 * y ^ 2 - Real.pi ^ 2 := by
        have : Real.pi < 2 * y := by nlinarith [Real.pi_lt_four]
        nlinarith [sq_pos_of_pos Real.pi_pos, sq_pos_of_pos hypos]
      have hmul := mul_lt_mul_of_pos_left hsin4 hcoef
      have hpi9 : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
      nlinarith [mul_pos (sq_pos_of_pos Real.pi_pos) (pow_pos hypos 4)]
    · have hypi' : Real.pi < y := lt_of_not_ge hypi
      have hratio :
          Real.pi ^ 2 * (4 * y ^ 2 - Real.pi ^ 2) ≤ 3 * y ^ 4 := by
        have hySq : Real.pi ^ 2 < y ^ 2 :=
          (sq_lt_sq₀ Real.pi_pos.le hypos.le).2 hypi'
        have h1 : 0 ≤ y ^ 2 - Real.pi ^ 2 := by linarith
        have h2 : 0 ≤ 3 * y ^ 2 - Real.pi ^ 2 := by nlinarith
        nlinarith [mul_nonneg h1 h2]
      have hsin := sine_fourth_le_one y
      have hcoef : 0 < 4 * y ^ 2 - Real.pi ^ 2 := by
        have hySq : Real.pi ^ 2 < y ^ 2 :=
          (sq_lt_sq₀ Real.pi_pos.le hypos.le).2 hypi'
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsin hcoef.le
      have hpi9 : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
      nlinarith [mul_pos (sq_pos_of_pos Real.pi_pos) (pow_pos hypos 4)]

private lemma cosine_gap_le_scaled
    (q : ℕ) (hq : 1000 ≤ q) (x : ℝ)
    (hx : Real.pi / (2 * (q : ℝ)) < x) (hxHalf : x ≤ Real.pi / 2) :
    Real.cos (Real.pi / q) - Real.cos (2 * x) ≤
      (4 * ((q : ℝ) * x) ^ 2 - Real.pi ^ 2) / (2 * (q : ℝ) ^ 2) := by
  have hqR : (0 : ℝ) < q := by positivity
  let a : ℝ := Real.pi / (2 * (q : ℝ))
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hxa : 0 < x - a := by exact sub_pos.mpr hx
  have hx0 : 0 < x := lt_trans ha0 hx
  have hsum0 : 0 ≤ x + a := by positivity
  have hsumPi : x + a ≤ Real.pi := by
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have haHalf : a ≤ Real.pi / 2 := by
      dsimp [a]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
      nlinarith [Real.pi_pos]
    linarith
  have hdiffPi : x - a ≤ Real.pi := by linarith
  have hs1non : 0 ≤ Real.sin (x + a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hsum0 hsumPi
  have hs2non : 0 ≤ Real.sin (x - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hxa.le hdiffPi
  have hs1 := Real.sin_le hsum0
  have hs2 := Real.sin_le hxa.le
  have hmul : Real.sin (x + a) * Real.sin (x - a) ≤ (x + a) * (x - a) :=
    calc
      Real.sin (x + a) * Real.sin (x - a) ≤
          (x + a) * Real.sin (x - a) :=
        mul_le_mul_of_nonneg_right hs1 hs2non
      _ ≤ (x + a) * (x - a) :=
        mul_le_mul_of_nonneg_left hs2 hsum0
  rw [Real.cos_sub_cos]
  have hrewrite :
      -2 * Real.sin ((Real.pi / q + 2 * x) / 2) *
          Real.sin ((Real.pi / q - 2 * x) / 2) =
        2 * Real.sin (x + a) * Real.sin (x - a) := by
    have hqa : Real.pi / q = 2 * a := by dsimp [a]; field_simp
    rw [hqa]
    rw [show (2 * a + 2 * x) / 2 = x + a by ring,
      show (2 * a - 2 * x) / 2 = -(x - a) by ring, Real.sin_neg]
    ring
  rw [hrewrite]
  have := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [a] at this ⊢
  field_simp at this ⊢
  nlinarith [sq_pos_of_pos hqR]

private lemma fejerFactor_zero (q : ℕ) (hq : 0 < q) :
    fejerFactor q 0 = q := by
  unfold fejerFactor geometricSum
  simp [Theory.PiDigits.T27.phase]

set_option maxHeartbeats 800000 in
-- The exact rational normalization in the two analytic branches makes the
-- final nonlinear arithmetic pass larger than Lean's default heartbeat cap.
private lemma boundaryMinorant_re_gt_neg_on_half
    (q : ℕ) (hq : 1000 ≤ q) (t : ℝ) (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    -(193 / 1000 : ℝ) < (boundaryMinorant q t).re := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  rcases ht0.eq_or_lt with rfl | htpos
  · rw [boundaryMinorant_eq q hq0, fejerFactor_zero q hq0]
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
    have hc := Real.cos_le_one (Real.pi / q)
    rw [div_eq_mul_inv] at hc
    nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hc)]
  have harg0 : 0 < Real.pi * t := mul_pos Real.pi_pos htpos
  have hargHalf : Real.pi * t ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsx0 : 0 < Real.sin (Real.pi * t) := Real.sin_pos_of_pos_of_lt_pi
    harg0 (hargHalf.trans_lt (by nlinarith [Real.pi_pos]))
  rw [boundaryMinorant_re_eq_sine_form q hq0 t (ne_of_gt hsx0)]
  let x : ℝ := Real.pi * t
  let y : ℝ := (q : ℝ) * x
  have hx0 : 0 < x := by exact harg0
  have hxHalf : x ≤ Real.pi / 2 := by exact hargHalf
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hsinRewrite : Real.sin (Real.pi * q * t) = Real.sin y := by
    dsimp [x, y]
    congr 1
    push_cast
    ring
  rw [hsinRewrite]
  rw [show 2 * Real.pi * t = 2 * x by dsimp [x]; ring,
    show Real.pi * t = x by rfl]
  change -(193 / 1000 : ℝ) <
    (Real.cos (2 * x) - Real.cos (Real.pi / q)) *
      (Real.sin y ^ 2 / ((q : ℝ) * Real.sin x ^ 2)) ^ 2
  by_cases hcentral : x ≤ Real.pi / (2 * (q : ℝ))
  · have hangle : 2 * x ≤ Real.pi / q := by
      field_simp at hcentral ⊢
      nlinarith [sq_pos_of_pos hqR]
    have hqangle : Real.pi / (q : ℝ) ≤ Real.pi := by
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      apply (div_le_iff₀ hqR).2
      nlinarith [Real.pi_pos]
    have hcos : Real.cos (Real.pi / q) ≤ Real.cos (2 * x) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hqangle hangle
    have hfac : 0 ≤ (Real.sin y ^ 2 /
        ((q : ℝ) * Real.sin x ^ 2)) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hcos) hfac]
  · have houtside : Real.pi / (2 * (q : ℝ)) < x := lt_of_not_ge hcentral
    let gap : ℝ := Real.cos (Real.pi / q) - Real.cos (2 * x)
    have hgap0 : 0 ≤ gap := by
      have hangle : Real.pi / (q : ℝ) ≤ 2 * x := by
        field_simp at houtside ⊢
        nlinarith [sq_pos_of_pos hqR]
      have hxpi : 2 * x ≤ Real.pi := by nlinarith
      exact sub_nonneg.mpr
        (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hxpi hangle)
    have htarget : gap *
        (Real.sin y ^ 2 / ((q : ℝ) * Real.sin x ^ 2)) ^ 2 <
          (193 / 1000 : ℝ) := by
      by_cases hy5 : y ≤ 5
      · have hyPi : Real.pi / 2 < y := by
          dsimp [y]
          have := mul_lt_mul_of_pos_left houtside hqR
          field_simp at this ⊢
          nlinarith [sq_pos_of_pos hqR]
        have hnumer := small_y_kernel_numerator_lt hyPi hy5
        have hgap := cosine_gap_le_scaled q hq x houtside hxHalf
        have hxSmall : x ≤ 1 / 200 := by
          dsimp [y] at hy5
          have hq1000 : (1000 : ℝ) ≤ q := by exact_mod_cast hq
          nlinarith
        have hsraw := Real.sin_gt_sub_cube hx0 (hxSmall.trans (by norm_num))
        have hslinear : (159999 / 160000 : ℝ) * x < Real.sin x := by
          have hxSq : x ^ 2 ≤ (1 / 200 : ℝ) ^ 2 := by nlinarith
          nlinarith [mul_pos hx0 (sub_pos.mpr (by norm_num : (0 : ℝ) < 1))]
        have hs0 : 0 < Real.sin x := by exact hsx0
        have hratio : x / Real.sin x < (160000 / 159999 : ℝ) := by
          apply (div_lt_iff₀ hs0).2
          nlinarith
        have hratio4 : (x / Real.sin x) ^ 4 <
            (160000 / 159999 : ℝ) ^ 4 :=
          pow_lt_pow_left₀ hratio (by positivity) (by norm_num)
        have hnum0 : 0 < 4 * y ^ 2 - Real.pi ^ 2 := by
          have hyPi' : Real.pi < 2 * y := by nlinarith
          have hsquare := (sq_lt_sq₀ Real.pi_pos.le (by positivity : 0 ≤ 2 * y)).2 hyPi'
          nlinarith
        have hA : gap *
            (Real.sin y ^ 2 / ((q : ℝ) * Real.sin x ^ 2)) ^ 2 ≤
              ((4 * y ^ 2 - Real.pi ^ 2) * Real.sin y ^ 4) /
                (2 * (q : ℝ) ^ 4 * Real.sin x ^ 4) := by
          have hm := mul_le_mul_of_nonneg_right hgap
            (sq_nonneg (Real.sin y ^ 2 / ((q : ℝ) * Real.sin x ^ 2)))
          dsimp [y] at hm ⊢
          field_simp at hm ⊢
          nlinarith [sq_pos_of_pos hqR, sq_pos_of_pos hs0]
        have hB : ((4 * y ^ 2 - Real.pi ^ 2) * Real.sin y ^ 4) /
              (2 * (q : ℝ) ^ 4 * Real.sin x ^ 4) <
            (24 / 125 : ℝ) * (x / Real.sin x) ^ 4 := by
          dsimp [y] at hnumer ⊢
          field_simp at hnumer ⊢
          nlinarith [sq_pos_of_pos hqR, pow_pos hs0 4]
        calc
          gap * (Real.sin y ^ 2 / ((q : ℝ) * Real.sin x ^ 2)) ^ 2 ≤ _ := hA
          _ < (24 / 125 : ℝ) * (x / Real.sin x) ^ 4 := hB
          _ < (24 / 125 : ℝ) * (160000 / 159999 : ℝ) ^ 4 :=
            mul_lt_mul_of_pos_left hratio4 (by norm_num)
          _ < 193 / 1000 := by norm_num
      · have hy5' : 5 < y := lt_of_not_ge hy5
        have hgapCoarse : gap ≤ 2 * Real.sin x ^ 2 := by
          have hc := Real.cos_le_one (Real.pi / q)
          have hcos : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
            convert Real.cos_two_mul_eq_one_sub x using 1 <;> ring
          dsimp [gap]
          rw [hcos]
          linarith
        have hsy4 := sine_fourth_le_one y
        have hcoarse : gap *
            (Real.sin y ^ 2 / ((q : ℝ) * Real.sin x ^ 2)) ^ 2 ≤
              2 / ((q : ℝ) ^ 2 * Real.sin x ^ 2) := by
          have hm := mul_le_mul hgapCoarse hsy4
            (by positivity : 0 ≤ Real.sin y ^ 4)
            (by positivity : 0 ≤ 2 * Real.sin x ^ 2)
          rw [div_pow]
          calc
            gap * ((Real.sin y ^ 2) ^ 2 /
                ((q : ℝ) * Real.sin x ^ 2) ^ 2) =
                gap * Real.sin y ^ 4 /
                  ((q : ℝ) ^ 2 * Real.sin x ^ 4) := by ring
            _ ≤ (2 * Real.sin x ^ 2) /
                  ((q : ℝ) ^ 2 * Real.sin x ^ 4) := by
              simp only [mul_one] at hm
              exact div_le_div_of_nonneg_right hm (by positivity)
            _ = 2 / ((q : ℝ) ^ 2 * Real.sin x ^ 2) := by
              field_simp
        by_cases hx1 : x ≤ 1
        · have hsraw := Real.sin_gt_sub_cube hx0 hx1
          have hslinear : (3 / 4 : ℝ) * x < Real.sin x := by
            nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1)]
          have hsSq : (9 / 16 : ℝ) * x ^ 2 < Real.sin x ^ 2 := by
            have := (sq_lt_sq₀ (by positivity : (0 : ℝ) ≤ 3 / 4 * x)
              hsx0.le).2 hslinear
            nlinarith
          have hbound : 2 / ((q : ℝ) ^ 2 * Real.sin x ^ 2) < 193 / 1000 := by
            dsimp [y] at hy5'
            have hqxSq : 25 < (q : ℝ) ^ 2 * x ^ 2 := by
              have hsquare := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 5)
                (by positivity : 0 ≤ (q : ℝ) * x)).2 hy5'
              nlinarith
            have hden : 225 / 16 < (q : ℝ) ^ 2 * Real.sin x ^ 2 := by
              have hm := mul_lt_mul_of_pos_left hsSq (sq_pos_of_pos hqR)
              nlinarith
            apply (div_lt_iff₀ (mul_pos (sq_pos_of_pos hqR) (sq_pos_of_pos hsx0))).2
            nlinarith
          exact hcoarse.trans_lt hbound
        · have hx1' : 1 < x := lt_of_not_ge hx1
          have hsOne : (3 / 4 : ℝ) < Real.sin 1 := by
            nlinarith [Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1)
              (by norm_num : (1 : ℝ) ≤ 1)]
          have hsMon : Real.sin 1 ≤ Real.sin x :=
            Real.sin_le_sin_of_le_of_le_pi_div_two
              (by nlinarith [Real.pi_pos]) hxHalf hx1'.le
          have hsLower : (3 / 4 : ℝ) < Real.sin x := hsOne.trans_le hsMon
          have hbound : 2 / ((q : ℝ) ^ 2 * Real.sin x ^ 2) < 193 / 1000 := by
            have hq1000 : (1000 : ℝ) ≤ q := by exact_mod_cast hq
            have hsSq : (9 / 16 : ℝ) < Real.sin x ^ 2 := by
              have := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 4)
                hsx0.le).2 hsLower
              norm_num at this ⊢
              exact this
            field_simp
            nlinarith [sq_pos_of_pos hqR, sq_pos_of_pos hsx0]
          exact hcoarse.trans_lt hbound
    dsimp [gap] at htarget
    nlinarith

private lemma boundaryMinorant_re_one_sub
    (q : ℕ) (hq : 0 < q) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (boundaryMinorant q (1 - t)).re = (boundaryMinorant q t).re := by
  have hsinT : Real.sin (Real.pi * t) ≠ 0 := by
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0)
      (by nlinarith [Real.pi_pos]))
  have hsinOne : Real.sin (Real.pi * (1 - t)) ≠ 0 := by
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub]
    exact hsinT
  rw [boundaryMinorant_re_eq_sine_form q hq (1 - t) hsinOne,
    boundaryMinorant_re_eq_sine_form q hq t hsinT]
  have hcos : Real.cos (2 * Real.pi * (1 - t)) = Real.cos (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (1 - t) = 2 * Real.pi - 2 * Real.pi * t by ring,
      Real.cos_two_pi_sub]
  have hden : Real.sin (Real.pi * (1 - t)) = Real.sin (Real.pi * t) := by
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub]
  have hnum : Real.sin (Real.pi * q * (1 - t)) ^ 2 =
      Real.sin (Real.pi * q * t) ^ 2 := by
    have harg : Real.pi * q * (1 - t) =
        (q : ℝ) * Real.pi - Real.pi * q * t := by push_cast; ring
    rw [harg, Real.sin_nat_mul_pi_sub]
    simp only [neg_sq]
    rw [mul_pow]
    simp [← pow_mul]
  rw [hcos, hden, hnum]

/-- Uniform global floor on the unit-period representative of the boundary
kernel.  This is the one exceptional-point estimate used by T151. -/
theorem boundaryMinorant_re_gt_neg_193
    (q : ℕ) (hq : 1000 ≤ q) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -(193 / 1000 : ℝ) < (boundaryMinorant q t).re := by
  by_cases hhalf : t ≤ 1 / 2
  · exact boundaryMinorant_re_gt_neg_on_half q hq t ht0 hhalf
  · have htpos : 0 < t := by linarith
    have hu0 : 0 ≤ 1 - t := by linarith
    have huHalf : 1 - t ≤ 1 / 2 := by linarith
    rw [← boundaryMinorant_re_one_sub q (by omega) t htpos ht1]
    exact boundaryMinorant_re_gt_neg_on_half q hq (1 - t) hu0 huHalf

/-- A rational lower chord for the sine at the root-grid separation radius. -/
lemma three_div_two_mul_lt_sin_pi_div_two_mul
    (d : ℕ) (hd : 10 ≤ d) :
    3 / (2 * (d : ℝ)) < Real.sin (Real.pi / (2 * d)) := by
  let x : ℝ := Real.pi / (2 * d)
  have hd0 : (0 : ℝ) < d := by positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    have hdR : (10 : ℝ) ≤ d := by exact_mod_cast hd
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).2
    nlinarith [Real.pi_lt_four]
  have hs := Real.sin_gt_sub_cube hx0 hx1
  have hlo : 157 / (100 * (d : ℝ)) < x := by
    dsimp [x]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 100 * d)).2
    field_simp
    nlinarith [Real.pi_gt_d2]
  have hhi : x < 2 / (d : ℝ) := by
    dsimp [x]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * d)).2
    field_simp
    nlinarith [Real.pi_lt_four]
  have hcube : x ^ 3 < (2 / (d : ℝ)) ^ 3 :=
    pow_lt_pow_left₀ hhi hx0.le (by norm_num)
  have hdSq : (100 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have hdR : (10 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hcsmall : x ^ 3 / 4 < 1 / (50 * (d : ℝ)) := by
    field_simp at hcube hdSq ⊢
    nlinarith [mul_pos hd0 (sq_pos_of_pos hd0)]
  have hrat : 3 / (2 * (d : ℝ)) <
      157 / (100 * (d : ℝ)) - 1 / (50 * (d : ℝ)) := by
    field_simp
    nlinarith
  nlinarith

private lemma sin_pi_mul_lower_on_rootGrid_middle
    (d : ℕ) (hd : 10 ≤ d) (t : ℝ)
    (ht0 : 1 / (2 * (d : ℝ)) ≤ t)
    (ht1 : t ≤ 1 - 1 / (2 * (d : ℝ))) :
    3 / (2 * (d : ℝ)) < Real.sin (Real.pi * t) := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hbase := three_div_two_mul_lt_sin_pi_div_two_mul d hd
  by_cases hhalf : t ≤ 1 / 2
  · have harg0 : 0 ≤ Real.pi / (2 * (d : ℝ)) := by positivity
    have hargle : Real.pi / (2 * (d : ℝ)) ≤ Real.pi * t := by
      have := mul_le_mul_of_nonneg_left ht0 Real.pi_pos.le
      convert this using 1 <;> field_simp <;> ring
    have hargHalf : Real.pi * t ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    exact hbase.trans_le
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        hargHalf hargle)
  · have hhalf' : 1 / 2 < t := lt_of_not_ge hhalf
    have hsep0 : 0 < 1 / (2 * (d : ℝ)) := by positivity
    have hone0 : 0 ≤ 1 - t := by
      have : t ≤ 1 := by linarith
      linarith
    have honeHalf : 1 - t ≤ 1 / 2 := by linarith
    have honeLow : 1 / (2 * (d : ℝ)) ≤ 1 - t := by linarith
    have harg0 : 0 ≤ Real.pi / (2 * (d : ℝ)) := by positivity
    have hargle : Real.pi / (2 * (d : ℝ)) ≤ Real.pi * (1 - t) := by
      have := mul_le_mul_of_nonneg_left honeLow Real.pi_pos.le
      convert this using 1 <;> field_simp <;> ring
    have hargHalf : Real.pi * (1 - t) ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hsine : Real.sin (Real.pi / (2 * (d : ℝ))) ≤
        Real.sin (Real.pi * (1 - t)) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        hargHalf hargle
    have hsym : Real.sin (Real.pi * (1 - t)) = Real.sin (Real.pi * t) := by
      rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring,
        Real.sin_pi_sub]
    rw [hsym] at hsine
    exact hbase.trans_le hsine

/-- Away from the one possible central-lobe point of a root grid, the
boundary kernel has a much smaller negative floor. -/
theorem boundaryMinorant_re_gt_neg_eight_mul_sq_div
    (q d : ℕ) (hq : 0 < q) (hd : 10 ≤ d) (t : ℝ)
    (ht0 : 1 / (2 * (d : ℝ)) ≤ t)
    (ht1 : t ≤ 1 - 1 / (2 * (d : ℝ))) :
    -(8 * (d : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2)) <
      (boundaryMinorant q t).re := by
  have hqR : (0 : ℝ) < q := by positivity
  have hs := sin_pi_mul_lower_on_rootGrid_middle d hd t ht0 ht1
  have hs0 : 0 < Real.sin (Real.pi * t) := lt_trans (by positivity) hs
  have hsin : Real.sin (Real.pi * t) ≠ 0 := ne_of_gt hs0
  rw [boundaryMinorant_re_eq_sine_form q hq t hsin]
  let a : ℝ := Real.sin (Real.pi * t)
  let b : ℝ := Real.sin (Real.pi * q * t)
  have hb : b ^ 2 ≤ 1 := by
    dsimp [b]
    nlinarith [sq_nonneg (Real.sin (Real.pi * q * t)),
      Real.neg_one_le_sin (Real.pi * q * t), Real.sin_le_one (Real.pi * q * t)]
  have hcos : Real.cos (2 * Real.pi * t) = 1 - 2 * a ^ 2 := by
    dsimp [a]
    convert Real.cos_two_mul_eq_one_sub (Real.pi * t) using 1 <;> ring
  have hdiff : -(2 * a ^ 2) ≤
      Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q) := by
    rw [hcos]
    linarith [Real.cos_le_one (Real.pi / q)]
  have ha0 : 0 < a := by exact hs0
  have hF0 : 0 ≤ (b ^ 2 / ((q : ℝ) * a ^ 2)) ^ 2 := sq_nonneg _
  have hfirst :
      -(2 * a ^ 2) * (b ^ 2 / ((q : ℝ) * a ^ 2)) ^ 2 ≤
        (Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q)) *
          (b ^ 2 / ((q : ℝ) * a ^ 2)) ^ 2 :=
    mul_le_mul_of_nonneg_right hdiff hF0
  have hsecond :
      -(2 / ((q : ℝ) ^ 2 * a ^ 2)) ≤
        -(2 * a ^ 2) * (b ^ 2 / ((q : ℝ) * a ^ 2)) ^ 2 := by
    have hb0 : 0 ≤ b ^ 2 := sq_nonneg _
    have hb4 : (b ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - b ^ 2)]
    field_simp
    nlinarith [sq_pos_of_pos hqR, sq_pos_of_pos ha0]
  have hsSq : 9 < 4 * (d : ℝ) ^ 2 * a ^ 2 := by
    have hX : 3 < 2 * (d : ℝ) * a := by
      have hraw := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * d)).1 hs
      nlinarith
    have hsq := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 3)
      (by positivity : 0 ≤ 2 * (d : ℝ) * a)).2 hX
    nlinarith
  have hstrict :
      -(8 * (d : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2)) <
        -(2 / ((q : ℝ) ^ 2 * a ^ 2)) := by
    have hqSq : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hqR
    have haSq : 0 < a ^ 2 := sq_pos_of_pos ha0
    field_simp
    nlinarith
  exact hstrict.trans_le (hsecond.trans hfirst)

end Theory.PiDigits.BoundaryKernelFloors

#print axioms Theory.PiDigits.BoundaryKernelFloors.fejerFactor_eq_sine_quotient
