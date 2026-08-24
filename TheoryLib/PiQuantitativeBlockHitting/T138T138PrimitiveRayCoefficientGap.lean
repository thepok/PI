import TheoryLib.PiQuantitativeBlockHitting.T132T132EdgeFrequencyFibers
import TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD

/-!
# T138: primitive-ray coefficient gap for the boundary kernel

This file proves the coefficient-specific strict contraction behind the
primitive power-of-ten compression of the T128 boundary kernel.  It does not
assert cancellation for the decimal orbit of pi.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.PrimitiveRayCoefficientGap

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra
open Theory.PiDigits.EdgeFrequencyFibers
open Theory.PiDigits.LongLagBlockCollisionDecay.T16

/-- The actual positive-frequency coefficient of the T128 boundary kernel. -/
def positiveBoundaryCoefficient (q h : ℕ) : ℝ :=
  aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) (h : ℤ)

/-- Every coefficient in the lower fifth of the positive support has the
uniform lower bound needed for primitive-ray contraction. -/
theorem one_div_three_mul_lt_positiveBoundaryCoefficient
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsmall : 5 * h ≤ q) :
    1 / (3 * (q : ℝ)) < positiveBoundaryCoefficient q h := by
  have hhsupp : h ≤ 2 * q - 1 := by omega
  rw [positiveBoundaryCoefficient,
    aggregatedBoundaryCoefficient_eq_affine q h hq hh0 hhsupp]
  unfold affineCoefficient
  rw [show neighboringCoefficient q h -
      Real.cos (Real.pi / q) * fejerSquareCoefficient q h =
      (neighboringCoefficient q h - fejerSquareCoefficient q h) +
        (1 - Real.cos (Real.pi / q)) * fejerSquareCoefficient q h by ring]
  rw [← signedEdgeCoefficient_eq_neighboring_sub q h (by omega) hh0 hhsupp]
  rw [signedEdgeCoefficient_eq_piecewise q h (by omega) hh0 hhsupp,
    if_pos (by omega : h ≤ q)]
  have hbeta := boundaryBeta_lt_jacksonBeta q hq
  unfold jacksonBeta at hbeta
  have hB : 2 / (q : ℝ) ^ 2 < 1 - Real.cos (Real.pi / q) := by linarith
  have hBform : fejerSquareCoefficient q h =
      (4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
        3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2) := by
    unfold fejerSquareCoefficient cubicMultiplicity
    rw [if_pos (by omega : h ≤ q)]
    ring
  rw [hBform]
  have hqR : (0 : ℝ) < q := by positivity
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
  have hhsmallR : (5 : ℝ) * h ≤ q := by exact_mod_cast hhsmall
  have hqh : (5 : ℝ) * q * h ^ 2 ≤ q ^ 2 * h := by
    nlinarith [mul_nonneg hqR.le hhR.le]
  have hpoly : 0 <
      6 * (h : ℝ) ^ 3 + (33 / 5 : ℝ) * q ^ 2 * h - 6 * h + 4 * q := by
    have : (0 : ℝ) ≤ 6 * (h : ℝ) ^ 3 := by positivity
    nlinarith
  have hden : 0 < 6 * (q : ℝ) ^ 2 := by positivity
  have hBpos : 0 <
      (4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
        3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2) := by
    apply div_pos
    · nlinarith [hqh, sq_nonneg ((q : ℝ) - h)]
    · positivity
  have hgain :
      2 / (q : ℝ) ^ 2 *
          ((4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
            3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2)) <
        (1 - Real.cos (Real.pi / q)) *
          ((4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
            3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2)) := by
    exact mul_lt_mul_of_pos_right hB hBpos
  calc
    1 / (3 * (q : ℝ)) <
        2 / (q : ℝ) ^ 2 *
            ((4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
              3 * (h : ℝ) ^ 3 - 3 * h) / (6 * (q : ℝ) ^ 2)) +
          (3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2) := by
      field_simp
      nlinarith [hpoly, sq_nonneg ((h : ℝ) - q)]
    _ < _ := by linarith

/-- The top frequency at the exceptional first decimal scale has the stronger
coefficient bound used to close the `q = 10` case. -/
theorem one_div_twenty_lt_positiveBoundaryCoefficient_ten :
    (1 : ℝ) / 20 < positiveBoundaryCoefficient 10 10 := by
  rw [positiveBoundaryCoefficient,
    aggregatedBoundaryCoefficient_eq_affine 10 10 (by norm_num) (by norm_num) (by norm_num)]
  unfold affineCoefficient neighboringCoefficient fejerSquareCoefficient cubicMultiplicity
  norm_num
  have hbeta := boundaryBeta_lt_jacksonBeta 10 (by norm_num)
  unfold jacksonBeta at hbeta
  nlinarith

/-- Sum of the first `M` odd squares, in the real normalization used by the
phase-spread estimate. -/
private lemma sum_odd_sq (M : ℕ) :
    (∑ j ∈ Finset.range M, (((2 * j + 1 : ℕ) : ℝ) ^ 2)) =
      (M : ℝ) * (4 * (M : ℝ) ^ 2 - 1) / 3 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Finite odd-frequency cosine sum in a denominator-free form. -/
private lemma two_sin_mul_sum_odd_cos (M : ℕ) (θ : ℝ) :
    2 * Real.sin θ *
        (∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * θ)) =
      Real.sin (2 * M * θ) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have htrig := Real.sin_sub_sin (2 * (M + 1) * θ) (2 * M * θ)
      have hterm :
          2 * Real.sin θ * Real.cos ((2 * (M : ℝ) + 1) * θ) =
            Real.sin (2 * ((M : ℝ) + 1) * θ) -
              Real.sin (2 * (M : ℝ) * θ) := by
        rw [htrig]
        congr 2 <;> ring
      push_cast
      rw [hterm]
      ring

/-- Quadratic lower bound for `1-cos` on `[0,π]`. -/
private lemma two_mul_sq_div_pi_sq_le_one_sub_cos
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    2 * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hhalf0 : 0 ≤ x / 2 := by positivity
  have hhalfpi : x / 2 ≤ Real.pi / 2 := by linarith
  have hs := Real.mul_le_sin hhalf0 hhalfpi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs' : x / Real.pi ≤ Real.sin (x / 2) := by
    calc
      x / Real.pi = 2 / Real.pi * (x / 2) := by ring
      _ ≤ Real.sin (x / 2) := hs
  have hxdiv : 0 ≤ x / Real.pi := by positivity
  have hsin : 0 ≤ Real.sin (x / 2) := hxdiv.trans hs'
  have hsq : (x / Real.pi) ^ 2 ≤ Real.sin (x / 2) ^ 2 :=
    (sq_le_sq₀ hxdiv hsin).2 hs'
  rw [show Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 by
    convert Real.cos_two_mul_eq_one_sub (x / 2) using 1 <;> ring]
  have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
  calc
    2 * x ^ 2 / Real.pi ^ 2 = 2 * (x / Real.pi) ^ 2 := by field_simp
    _ ≤ 2 * Real.sin (x / 2) ^ 2 := by gcongr
    _ = 1 - (1 - 2 * Real.sin (x / 2) ^ 2) := by ring

private lemma abs_sum_odd_cos_lt_half
    (M : ℕ) (θ : ℝ) (hM : 0 < M) (hθ0 : 0 < θ)
    (hθhalf : θ ≤ Real.pi / 2) (hθlarge : Real.pi / (2 * M) < θ) :
    |∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * θ)| < (M : ℝ) / 2 := by
  let C : ℝ := ∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * θ)
  have hsinLower : 1 / (M : ℝ) < Real.sin θ := by
    have hlin := Real.mul_le_sin hθ0.le hθhalf
    have hmul : 2 / Real.pi * (Real.pi / (2 * M)) <
        2 / Real.pi * θ := by
      exact mul_lt_mul_of_pos_left hθlarge (by positivity)
    calc
      1 / (M : ℝ) = 2 / Real.pi * (Real.pi / (2 * M)) := by
        field_simp
      _ < 2 / Real.pi * θ := hmul
      _ ≤ Real.sin θ := hlin
  have hsinPos : 0 < Real.sin θ := by
    have : 0 < 1 / (M : ℝ) := by positivity
    linarith
  have hid := two_sin_mul_sum_odd_cos M θ
  change 2 * Real.sin θ * C = Real.sin (2 * M * θ) at hid
  have habs : 2 * Real.sin θ * |C| ≤ 1 := by
    have habseq := congrArg abs hid
    have hright := Real.abs_sin_le_one (2 * M * θ)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos hsinPos] at habseq
    nlinarith
  by_contra hnot
  have hC : (M : ℝ) / 2 ≤ |C| := le_of_not_gt hnot
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hprod : (1 / (M : ℝ)) * ((M : ℝ) / 2) <
      Real.sin θ * |C| := by
    exact mul_lt_mul hsinLower hC (by positivity) (by positivity)
  have hcancel : (1 / (M : ℝ)) * ((M : ℝ) / 2) = 1 / 2 := by
    field_simp
  rw [hcancel] at hprod
  nlinarith

private lemma sum_odd_cos_nonneg_of_small
    (M : ℕ) (θ : ℝ) (hM : 0 < M) (hθ0 : 0 < θ)
    (hθsmall : θ ≤ Real.pi / (2 * M)) :
    0 ≤ ∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * θ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hθpi : 2 * (M : ℝ) * θ ≤ Real.pi := by
    calc
      2 * (M : ℝ) * θ ≤ 2 * (M : ℝ) * (Real.pi / (2 * M)) :=
        mul_le_mul_of_nonneg_left hθsmall (by positivity)
      _ = Real.pi := by field_simp
  have hsin : 0 ≤ Real.sin (2 * M * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hθpi
  have hsinθ : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi hθ0
    have := Real.pi_pos
    have hbase : θ ≤ Real.pi / 2 := hθsmall.trans (by
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
        (by exact_mod_cast (show 2 ≤ 2 * M by omega)))
    linarith
  have hid := two_sin_mul_sum_odd_cos M θ
  nlinarith

/-- The phase-spread estimate used by the uniform primitive-ray gap.  The
constants are intentionally loose, leaving a large formal safety margin. -/
theorem odd_phase_spread
    (M r : ℕ) (hM : 0 < M) (hr0 : 0 < r) (hrq : r < 100 * M) :
    (100 * M : ℝ) / 500000 ≤
      ∑ j ∈ Finset.range M,
        (1 - Real.cos ((2 * j + 1) * (Real.pi * r / (100 * M)))) := by
  let θ : ℝ := Real.pi * r / (100 * M)
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθpi : θ < Real.pi := by
    dsimp [θ]
    have hrqR : (r : ℝ) < 100 * M := by exact_mod_cast hrq
    rw [div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left hrqR Real.pi_pos
  change (100 * M : ℝ) / 500000 ≤
    ∑ j ∈ Finset.range M, (1 - Real.cos ((2 * j + 1) * θ))
  by_cases hsmall : θ ≤ Real.pi / (2 * M)
  · have hterm (j : ℕ) (hj : j ∈ Finset.range M) :
        2 * (((2 * j + 1 : ℕ) : ℝ) * θ) ^ 2 / Real.pi ^ 2 ≤
          1 - Real.cos ((2 * j + 1) * θ) := by
      have hraw := two_mul_sq_div_pi_sq_le_one_sub_cos
        (x := (((2 * j + 1 : ℕ) : ℝ) * θ)) (by positivity) (by
          have hjlt := Finset.mem_range.mp hj
          have hfac : ((2 * j + 1 : ℕ) : ℝ) < 2 * M := by
            exact_mod_cast (by omega)
          have hlt := mul_lt_mul_of_pos_right hfac hθ0
          have hle : (2 * (M : ℝ)) * θ ≤ Real.pi := by
            calc
              (2 * (M : ℝ)) * θ ≤
                  (2 * (M : ℝ)) * (Real.pi / (2 * M)) :=
                    mul_le_mul_of_nonneg_left hsmall (by positivity)
              _ = Real.pi := by field_simp
          exact hlt.le.trans hle)
      norm_num at hraw ⊢
      exact hraw
    calc
      (100 * M : ℝ) / 500000 ≤
          ∑ j ∈ Finset.range M,
            2 * (((2 * j + 1 : ℕ) : ℝ) * θ) ^ 2 / Real.pi ^ 2 := by
        rw [show (∑ j ∈ Finset.range M,
            2 * (((2 * j + 1 : ℕ) : ℝ) * θ) ^ 2 / Real.pi ^ 2) =
            (2 * θ ^ 2 / Real.pi ^ 2) *
              ∑ j ∈ Finset.range M, (((2 * j + 1 : ℕ) : ℝ) ^ 2) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring]
        rw [sum_odd_sq]
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr0
        have hθlower : Real.pi / (100 * M) ≤ θ := by
          dsimp [θ]
          have hden : (0 : ℝ) < 100 * M := by positivity
          apply div_le_div_of_nonneg_right
          · nlinarith [Real.pi_pos]
          · positivity
        have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
        have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        have hθsq : (Real.pi / (100 * M)) ^ 2 ≤ θ ^ 2 := by
          exact (sq_le_sq₀ (by positivity) hθ0.le).2 hθlower
        calc
          (100 * M : ℝ) / 500000 ≤
              (2 * (Real.pi / (100 * M)) ^ 2 / Real.pi ^ 2) *
                ((M : ℝ) * (4 * (M : ℝ) ^ 2 - 1) / 3) := by
            field_simp
            nlinarith [sq_nonneg ((M : ℝ) - 1)]
          _ ≤ (2 * θ ^ 2 / Real.pi ^ 2) *
                ((M : ℝ) * (4 * (M : ℝ) ^ 2 - 1) / 3) := by
            apply mul_le_mul_of_nonneg_right
            · gcongr
            · nlinarith [sq_nonneg ((M : ℝ) - 1)]
      _ ≤ _ := Finset.sum_le_sum hterm
  · have hlarge : Real.pi / (2 * M) < θ := lt_of_not_ge hsmall
    have hsumform :
        (∑ j ∈ Finset.range M, (1 - Real.cos ((2 * j + 1) * θ))) =
          (M : ℝ) -
            ∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * θ) := by
      rw [Finset.sum_sub_distrib]
      simp
    have hconstant : (100 * M : ℝ) / 500000 = (M : ℝ) / 5000 := by
      push_cast
      ring
    rw [hsumform, hconstant]
    by_cases hhalf : θ ≤ Real.pi / 2
    · have habs := abs_sum_odd_cos_lt_half M θ hM hθ0 hhalf hlarge
      have hle := le_abs_self
        (∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * θ))
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      nlinarith
    · let φ : ℝ := Real.pi - θ
      have hφ0 : 0 < φ := by dsimp [φ]; linarith
      have hφhalf : φ ≤ Real.pi / 2 := by dsimp [φ]; linarith
      have hcos (j : ℕ) :
          Real.cos ((2 * j + 1) * θ) =
            -Real.cos ((2 * j + 1) * φ) := by
        have hodd : Odd (2 * j + 1) := ⟨j, by omega⟩
        have hc := Real.cos_nat_mul_pi_sub
          (((2 * j + 1 : ℕ) : ℝ) * φ) (2 * j + 1)
        rw [hodd.neg_one_pow] at hc
        norm_num at hc
        have harg : (2 * (j : ℝ) + 1) * θ =
            ((2 * j + 1 : ℕ) : ℝ) * Real.pi -
              ((2 * j + 1 : ℕ) : ℝ) * φ := by
          push_cast
          dsimp [φ]
          ring
        rw [harg]
        norm_num at hc ⊢
        exact hc
      have hsumcos :
          (∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * θ)) =
            -∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * φ) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact hcos j
      rw [hsumcos]
      by_cases hφsmall : φ ≤ Real.pi / (2 * M)
      · have hnonneg := sum_odd_cos_nonneg_of_small M φ hM hφ0 hφsmall
        have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
        nlinarith
      · have habs := abs_sum_odd_cos_lt_half M φ hM hφ0 hφhalf
          (lt_of_not_ge hφsmall)
        have hneg := neg_abs_le
          (∑ j ∈ Finset.range M, Real.cos ((2 * j + 1) * φ))
        have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
        nlinarith

/-- Reduction of an odd integral center multiplier to the half-period used by
`odd_phase_spread`. -/
private lemma exists_reduced_center_multiplier
    (M m : ℕ) (hM : 0 < M) (hm : Odd m) :
    ∃ r : ℕ, 0 < r ∧ r < 100 * M ∧
      ∀ u : ℕ, Real.cos (Real.pi * m * u / (100 * M)) =
        Real.cos (Real.pi * r * u / (100 * M)) := by
  let q := 100 * M
  let s := m % (2 * q)
  have hq : 0 < q := by dsimp [q]; positivity
  have hslt : s < 2 * q := by
    dsimp [s]
    exact Nat.mod_lt _ (by positivity)
  have hdecomp : s + 2 * q * (m / (2 * q)) = m := by
    dsimp [s]
    exact Nat.mod_add_div m (2 * q)
  have hsodd : Odd s := by
    have heven : Even (2 * q * (m / (2 * q))) :=
      ⟨q * (m / (2 * q)), by ring⟩
    have hle : 2 * q * (m / (2 * q)) ≤ m := by
      exact Nat.le.intro (by simpa only [Nat.add_comm] using hdecomp)
    have hoddSub := Nat.Odd.sub_even hle hm heven
    have hsub : m - 2 * q * (m / (2 * q)) = s := by omega
    simpa only [hsub] using hoddSub
  have hs0 : 0 < s := by
    have hsne : s ≠ 0 := by
      intro hs
      rw [hs] at hsodd
      norm_num at hsodd
    exact Nat.pos_of_ne_zero hsne
  by_cases hslow : s < q
  · refine ⟨s, hs0, hslow, ?_⟩
    intro u
    have harg : Real.pi * (m : ℝ) * u / q =
        Real.pi * (s : ℝ) * u / q +
          ((m / (2 * q)) * u : ℕ) * (2 * Real.pi) := by
      have hqR : (q : ℝ) ≠ 0 := by positivity
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hdecomp
      push_cast at hcast ⊢
      field_simp
      nlinarith [Real.pi_pos]
    dsimp [q] at harg
    norm_num at harg ⊢
    rw [harg]
    convert Real.cos_add_nat_mul_two_pi
      (Real.pi * (s : ℝ) * u / (100 * M)) ((m / (2 * (100 * M))) * u) using 1 <;>
        push_cast <;> ring
  · have hsq : q < s := by
      have hqeven : Even q := ⟨50 * M, by dsimp [q]; omega⟩
      have hsne : s ≠ q := by
        intro heq
        exact (Nat.not_even_iff_odd.mpr hsodd) (heq ▸ hqeven)
      omega
    let r := 2 * q - s
    have hr0 : 0 < r := by dsimp [r]; omega
    have hrq : r < q := by dsimp [r]; omega
    refine ⟨r, hr0, hrq, ?_⟩
    intro u
    have hms : Real.cos (Real.pi * m * u / q) =
        Real.cos (Real.pi * s * u / q) := by
      have harg : Real.pi * (m : ℝ) * u / q =
          Real.pi * (s : ℝ) * u / q +
            ((m / (2 * q)) * u : ℕ) * (2 * Real.pi) := by
        have hqR : (q : ℝ) ≠ 0 := by positivity
        have hcast := congrArg (fun n : ℕ => (n : ℝ)) hdecomp
        push_cast at hcast ⊢
        field_simp
        nlinarith [Real.pi_pos]
      rw [harg, Real.cos_add_nat_mul_two_pi]
    dsimp [q] at hms ⊢
    norm_num at hms ⊢
    rw [hms]
    have harg : Real.pi * (s : ℝ) * u / q =
        (u : ℕ) * (2 * Real.pi) - Real.pi * (r : ℝ) * u / q := by
      have hrs : r + s = 2 * q := by dsimp [r]; omega
      have hqR : (q : ℝ) ≠ 0 := by positivity
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hrs
      push_cast at hcast ⊢
      field_simp
      nlinarith [Real.pi_pos]
    dsimp [q] at harg
    norm_num at harg ⊢
    rw [harg]
    exact Real.cos_nat_mul_two_pi_sub _ u

/-- Target-uniform phase spread at the exact decimal-cylinder center. -/
theorem decimal_center_phase_spread
    (M A : ℕ) (hM : 0 < M) :
    (100 * M : ℝ) / 500000 ≤
      ∑ j ∈ Finset.range M,
        (1 - Real.cos (Real.pi * (9 * (2 * A + 1)) * (2 * j + 1) /
          (100 * M))) := by
  have hm : Odd (9 * (2 * A + 1)) := by
    exact (show Odd 9 by norm_num).mul ⟨A, by omega⟩
  obtain ⟨r, hr0, hrq, hcos⟩ :=
    exists_reduced_center_multiplier M (9 * (2 * A + 1)) hM hm
  have hspread := odd_phase_spread M r hM hr0 hrq
  calc
    (100 * M : ℝ) / 500000 ≤
        ∑ j ∈ Finset.range M,
          (1 - Real.cos ((2 * j + 1) * (Real.pi * r / (100 * M)))) := hspread
    _ = ∑ j ∈ Finset.range M,
          (1 - Real.cos (Real.pi * (9 * (2 * A + 1)) * (2 * j + 1) /
            (100 * M))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hc := (hcos (2 * j + 1)).symm
      norm_num at hc ⊢
      convert hc using 1 <;> ring

/-- Center of the decimal cylinder with label `A` at mesh `q`. -/
def decimalCylinderCenter (q A : ℕ) : ℝ := (2 * A + 1 : ℝ) / (2 * q)

/-- The exact centered positive-frequency T128 summand. -/
def centeredBoundaryTerm (q A h : ℕ) : ℂ :=
  positiveBoundaryCoefficient q h *
    Theory.PiDigits.T27.phase (-(h : ℤ)) (decimalCylinderCenter q A)

/-- Exact positive support of the T128 boundary kernel. -/
def positiveBoundarySupport (q : ℕ) : Finset ℕ := Finset.Icc 1 (2 * q - 1)

/-- Primitive bases actually represented in the positive T128 support. -/
def primitiveBoundarySupport (q : ℕ) : Finset ℕ :=
  (positiveBoundarySupport q).image tenPrimitivePart

/-- Frequencies in one exact primitive power-of-ten ray. -/
def primitiveBoundaryFiber (q u : ℕ) : Finset ℕ :=
  (positiveBoundarySupport q).filter fun h => tenPrimitivePart h = u

/-- Coefficient load before primitive-ray compression. -/
def positiveBoundaryLoad (q : ℕ) : ℝ :=
  ∑ h ∈ positiveBoundarySupport q, ‖centeredBoundaryTerm q 0 h‖

/-- Exact coefficient load after collecting every positive frequency on its
primitive power-of-ten ray. -/
def primitiveBoundaryLoad (q A : ℕ) : ℝ :=
  ∑ u ∈ primitiveBoundarySupport q,
    ‖∑ h ∈ primitiveBoundaryFiber q u, centeredBoundaryTerm q A h‖

private lemma phase_re_eq_cos (h : ℤ) (x : ℝ) :
    (Theory.PiDigits.T27.phase h x).re =
      Real.cos (2 * Real.pi * h * x) := by
  unfold Theory.PiDigits.T27.phase
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (x : ℂ) =
      (((2 * Real.pi * (h : ℝ) * x : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  exact Complex.exp_ofReal_mul_I_re _

private lemma centered_pair_normSq
    (q A u : ℕ) :
    Complex.normSq
        (centeredBoundaryTerm q A u + centeredBoundaryTerm q A (10 * u)) =
      positiveBoundaryCoefficient q u ^ 2 +
        positiveBoundaryCoefficient q (10 * u) ^ 2 +
        2 * positiveBoundaryCoefficient q u *
          positiveBoundaryCoefficient q (10 * u) *
          Real.cos (Real.pi * (9 * (2 * A + 1)) * u / q) := by
  let a := positiveBoundaryCoefficient q u
  let b := positiveBoundaryCoefficient q (10 * u)
  let c := decimalCylinderCenter q A
  have hcross :
      ((centeredBoundaryTerm q A u) *
        star (centeredBoundaryTerm q A (10 * u))).re =
        a * b * Real.cos (Real.pi * (9 * (2 * A + 1)) * u / q) := by
    change (((a : ℂ) * Theory.PiDigits.T27.phase (-(u : ℤ)) c) *
      star ((b : ℂ) * Theory.PiDigits.T27.phase (-(10 * u : ℕ) : ℤ) c)).re = _
    rw [show star ((b : ℂ) *
        Theory.PiDigits.T27.phase (-(10 * u : ℕ) : ℤ) c) =
        (b : ℂ) * Theory.PiDigits.T27.phase (10 * u : ℕ) c by
      change (starRingEnd ℂ) ((b : ℂ) *
        Theory.PiDigits.T27.phase (-(10 * u : ℕ) : ℤ) c) = _
      rw [map_mul, Complex.conj_ofReal]
      rw [Theory.PiDigits.T27.phase_neg]
      simp]
    rw [show ((a : ℂ) * Theory.PiDigits.T27.phase (-(u : ℤ)) c) *
        ((b : ℂ) * Theory.PiDigits.T27.phase (10 * u : ℕ) c) =
        ((a * b : ℝ) : ℂ) *
          (Theory.PiDigits.T27.phase (-(u : ℤ)) c *
            Theory.PiDigits.T27.phase (10 * u : ℕ) c) by
              push_cast
              ring]
    rw [← Theory.PiDigits.T27.phase_add]
    have hfreq : -(u : ℤ) + (10 * u : ℕ) = 9 * (u : ℤ) := by
      push_cast
      ring
    rw [hfreq]
    change ((a * b : ℝ) * Theory.PiDigits.T27.phase (9 * (u : ℤ)) c).re = _
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [phase_re_eq_cos]
    dsimp [c, decimalCylinderCenter]
    congr 2
    push_cast
    ring
  rw [Complex.normSq_add]
  change Complex.normSq (centeredBoundaryTerm q A u) +
      Complex.normSq (centeredBoundaryTerm q A (10 * u)) +
        2 * ((centeredBoundaryTerm q A u) *
          star (centeredBoundaryTerm q A (10 * u))).re = _
  rw [hcross]
  have hnormSq_u : Complex.normSq (centeredBoundaryTerm q A u) = a ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    unfold centeredBoundaryTerm
    rw [norm_mul, Theory.PiDigits.T27.norm_phase, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnormSq_ten :
      Complex.normSq (centeredBoundaryTerm q A (10 * u)) = b ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    unfold centeredBoundaryTerm
    rw [norm_mul, Theory.PiDigits.T27.norm_phase, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnormSq_u, hnormSq_ten]
  dsimp [a, b]
  ring

/-- Harmonic coefficient governing the loss from the first two entries on a
primitive ray. -/
def boundaryPairHarmonic (q u : ℕ) : ℝ :=
  positiveBoundaryCoefficient q u * positiveBoundaryCoefficient q (10 * u) /
    (positiveBoundaryCoefficient q u + positiveBoundaryCoefficient q (10 * u))

private lemma boundaryPairHarmonic_baseline
    (q u : ℕ) (hq : 0 < q)
    (ha : 1 / (3 * (q : ℝ)) < positiveBoundaryCoefficient q u)
    (hb : 1 / (3 * (q : ℝ)) < positiveBoundaryCoefficient q (10 * u)) :
    1 / (6 * (q : ℝ)) < boundaryPairHarmonic q u := by
  let a := positiveBoundaryCoefficient q u
  let b := positiveBoundaryCoefficient q (10 * u)
  have ha0 : 0 < a := (by positivity : 0 < 1 / (3 * (q : ℝ))).trans ha
  have hb0 : 0 < b := (by positivity : 0 < 1 / (3 * (q : ℝ))).trans hb
  unfold boundaryPairHarmonic
  change 1 / (6 * (q : ℝ)) < a * b / (a + b)
  let d : ℝ := 1 / (3 * (q : ℝ))
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hdb : d * b < a * b := mul_lt_mul_of_pos_right ha hb0
  have hda : d * a < b * a := mul_lt_mul_of_pos_right hb ha0
  have hhalf : d / 2 * (a + b) < a * b := by nlinarith
  have heq : 1 / (6 * (q : ℝ)) = d / 2 := by
    dsimp [d]
    ring
  rw [heq]
  exact (lt_div_iff₀ (show 0 < a + b by positivity)).2 hhalf

/-- Loss from combining the first two coefficients on one selected ray. -/
private lemma centered_pair_loss_lower
    (q A u : ℕ)
    (ha0 : 0 < positiveBoundaryCoefficient q u)
    (hb0 : 0 < positiveBoundaryCoefficient q (10 * u)) :
    boundaryPairHarmonic q u *
        (1 - Real.cos (Real.pi * (9 * (2 * A + 1)) * u / q)) ≤
      ‖centeredBoundaryTerm q A u‖ + ‖centeredBoundaryTerm q A (10 * u)‖ -
        ‖centeredBoundaryTerm q A u + centeredBoundaryTerm q A (10 * u)‖ := by
  let a := positiveBoundaryCoefficient q u
  let b := positiveBoundaryCoefficient q (10 * u)
  let C := 1 - Real.cos (Real.pi * (9 * (2 * A + 1)) * u / q)
  let n := ‖centeredBoundaryTerm q A u + centeredBoundaryTerm q A (10 * u)‖
  have hcosle := Real.cos_le_one
    (Real.pi * (9 * (2 * A + 1)) * u / q)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hnormu : ‖centeredBoundaryTerm q A u‖ = a := by
    unfold centeredBoundaryTerm
    rw [norm_mul, Theory.PiDigits.T27.norm_phase, mul_one, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos ha0]
  have hnormten : ‖centeredBoundaryTerm q A (10 * u)‖ = b := by
    unfold centeredBoundaryTerm
    rw [norm_mul, Theory.PiDigits.T27.norm_phase, mul_one, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos hb0]
  have hn0 : 0 ≤ n := norm_nonneg _
  have hnle : n ≤ a + b := by
    dsimp [n]
    exact (norm_add_le _ _).trans_eq (by rw [hnormu, hnormten])
  have hsq : n ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * (1 - C) := by
    dsimp [n, a, b, C]
    rw [← Complex.normSq_eq_norm_sq, centered_pair_normSq]
    ring
  have hfactor : (a + b - n) * (a + b + n) = 2 * a * b * C := by
    nlinarith
  have hden : 0 < a + b + n := by positivity
  have hloss : a + b - n = 2 * a * b * C / (a + b + n) := by
    rw [eq_div_iff hden.ne']
    exact hfactor
  have hdenle : a + b + n ≤ 2 * (a + b) := by linarith
  have hfrac : a * b * C / (a + b) ≤
      2 * a * b * C / (a + b + n) := by
    rw [div_le_div_iff₀ (by positivity) hden]
    have habC : 0 ≤ a * b * C := by positivity
    nlinarith
  rw [hnormu, hnormten]
  change a * b / (a + b) * C ≤ a + b - n
  rw [hloss]
  have hrewrite : a * b / (a + b) * C = a * b * C / (a + b) := by ring
  rw [hrewrite]
  exact hfrac

/-- Loss of coefficient `ℓ¹` mass on one exact primitive ray. -/
def primitiveRayLoss (q A u : ℕ) : ℝ :=
  (∑ h ∈ primitiveBoundaryFiber q u, ‖centeredBoundaryTerm q A h‖) -
    ‖∑ h ∈ primitiveBoundaryFiber q u, centeredBoundaryTerm q A h‖

private lemma primitiveRayLoss_nonneg (q A u : ℕ) :
    0 ≤ primitiveRayLoss q A u := by
  unfold primitiveRayLoss
  exact sub_nonneg.mpr (norm_sum_le _ _)

private lemma centeredBoundaryTerm_norm_independent
    (q A B h : ℕ) :
    ‖centeredBoundaryTerm q A h‖ = ‖centeredBoundaryTerm q B h‖ := by
  unfold centeredBoundaryTerm
  simp only [norm_mul, Theory.PiDigits.T27.norm_phase, mul_one]

private lemma positiveBoundaryLoad_sub_primitiveBoundaryLoad
    (q A : ℕ) :
    positiveBoundaryLoad q - primitiveBoundaryLoad q A =
      ∑ u ∈ primitiveBoundarySupport q, primitiveRayLoss q A u := by
  classical
  have hmaps : ∀ h ∈ positiveBoundarySupport q,
      tenPrimitivePart h ∈ primitiveBoundarySupport q := by
    intro h hh
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  have hnormFib := Finset.sum_fiberwise_of_maps_to
    (s := positiveBoundarySupport q) (t := primitiveBoundarySupport q)
    (g := tenPrimitivePart) hmaps (fun h => ‖centeredBoundaryTerm q A h‖)
  have hnormA :
      (∑ h ∈ positiveBoundarySupport q, ‖centeredBoundaryTerm q A h‖) =
        positiveBoundaryLoad q := by
    unfold positiveBoundaryLoad
    apply Finset.sum_congr rfl
    intro h hh
    exact centeredBoundaryTerm_norm_independent q A 0 h
  unfold primitiveBoundaryLoad primitiveRayLoss primitiveBoundaryFiber
  rw [Finset.sum_sub_distrib]
  rw [hnormFib, hnormA]

private lemma tenPrimitivePart_eq_self_of_not_dvd
    {u : ℕ} (hu : ¬10 ∣ u) : tenPrimitivePart u = u := by
  unfold tenPrimitivePart
  have h := Nat.maxPowDvdDiv_of_not_dvd hu
  exact congrArg Prod.snd h

private lemma tenPrimitivePart_ten_mul_of_not_dvd
    {u : ℕ} (hu : ¬10 ∣ u) : tenPrimitivePart (10 * u) = u := by
  unfold tenPrimitivePart
  rw [Nat.divMaxPow_base_mul (by norm_num)]
  exact tenPrimitivePart_eq_self_of_not_dvd hu

private lemma primitiveRayLoss_pair_lower
    (q A u : ℕ) (hu0 : 0 < u) (huq : 10 * u ≤ 2 * q - 1)
    (huprim : ¬10 ∣ u) :
    ‖centeredBoundaryTerm q A u‖ + ‖centeredBoundaryTerm q A (10 * u)‖ -
        ‖centeredBoundaryTerm q A u + centeredBoundaryTerm q A (10 * u)‖ ≤
      primitiveRayLoss q A u := by
  classical
  let s := primitiveBoundaryFiber q u
  let t : Finset ℕ := {u, 10 * u}
  let f : ℕ → ℂ := fun h => centeredBoundaryTerm q A h
  have hune : u ≠ 10 * u := by omega
  have hus : u ∈ s := by
    simp only [s, primitiveBoundaryFiber, Finset.mem_filter,
      positiveBoundarySupport, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, tenPrimitivePart_eq_self_of_not_dvd huprim⟩
  have htens : 10 * u ∈ s := by
    simp only [s, primitiveBoundaryFiber, Finset.mem_filter,
      positiveBoundarySupport, Finset.mem_Icc]
    exact ⟨⟨by omega, huq⟩, tenPrimitivePart_ten_mul_of_not_dvd huprim⟩
  have htsub : t ⊆ s := by
    intro h hh
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact hus
    · exact htens
  have hsum := Finset.sum_sdiff htsub (f := f)
  have hnormsum := Finset.sum_sdiff htsub (f := fun h => ‖f h‖)
  have htcomplex : (∑ h ∈ t, f h) = f u + f (10 * u) := by
    simp [t, hune]
  have htreal : (∑ h ∈ t, ‖f h‖) = ‖f u‖ + ‖f (10 * u)‖ := by
    simp [t, hune]
  have hupper : ‖∑ h ∈ s, f h‖ ≤
      (∑ h ∈ s \ t, ‖f h‖) + ‖f u + f (10 * u)‖ := by
    calc
      ‖∑ h ∈ s, f h‖ =
          ‖(∑ h ∈ s \ t, f h) + ∑ h ∈ t, f h‖ := by rw [hsum]
      _ = ‖(∑ h ∈ s \ t, f h) + (f u + f (10 * u))‖ := by rw [htcomplex]
      _ ≤ ‖∑ h ∈ s \ t, f h‖ + ‖f u + f (10 * u)‖ := norm_add_le _ _
      _ ≤ (∑ h ∈ s \ t, ‖f h‖) + ‖f u + f (10 * u)‖ := by
        gcongr
        exact norm_sum_le _ _
  unfold primitiveRayLoss
  change _ ≤ (∑ h ∈ s, ‖f h‖) - ‖∑ h ∈ s, f h‖
  rw [← hnormsum, htreal]
  linarith

/-- For every decimal mesh divisible by `100`, collecting the actual positive
T128 coefficients on primitive power-of-ten rays loses a target-independent
amount of coefficient load.  The constant is deliberately coarse, but it is
uniform in both the mesh scale and the cylinder label. -/
theorem primitiveBoundaryLoad_lt_positiveBoundaryLoad_sub_gap
    (M A : ℕ) (hM : 0 < M) :
    primitiveBoundaryLoad (100 * M) A <
      positiveBoundaryLoad (100 * M) - 1 / 3000000 := by
  classical
  let q := 100 * M
  let C : ℕ → ℝ := fun j =>
    1 - Real.cos (Real.pi * (9 * (2 * A + 1)) * (2 * j + 1) / q)
  let H : ℕ → ℝ := fun j => boundaryPairHarmonic q (2 * j + 1)
  let L : ℕ → ℝ := fun j => primitiveRayLoss q A (2 * j + 1)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 < q := by dsimp [q]; omega
  have hC0 : ∀ j, 0 ≤ C j := by
    intro j
    dsimp [C]
    linarith [Real.cos_le_one
      (Real.pi * (9 * (2 * A + 1)) * (2 * j + 1) / q)]
  have hspread : (q : ℝ) / 500000 ≤ ∑ j ∈ Finset.range M, C j := by
    dsimp [q, C]
    convert decimal_center_phase_spread M A hM using 1 <;> push_cast <;> ring
  have hsumCpos : 0 < ∑ j ∈ Finset.range M, C j := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
    exact (div_pos hqR (by norm_num)).trans_le hspread
  obtain ⟨j0, hj0, hCj0⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ => hC0 j)).mp hsumCpos
  have hcoeff : ∀ j ∈ Finset.range M,
      1 / (3 * (q : ℝ)) < positiveBoundaryCoefficient q (2 * j + 1) ∧
      1 / (3 * (q : ℝ)) < positiveBoundaryCoefficient q (10 * (2 * j + 1)) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    constructor
    · apply one_div_three_mul_lt_positiveBoundaryCoefficient q (2 * j + 1) hq1
      · omega
      · dsimp [q]
        omega
    · apply one_div_three_mul_lt_positiveBoundaryCoefficient q (10 * (2 * j + 1)) hq1
      · omega
      · dsimp [q]
        omega
  have hH : ∀ j ∈ Finset.range M, 1 / (6 * (q : ℝ)) < H j := by
    intro j hj
    rcases hcoeff j hj with ⟨ha, hb⟩
    exact boundaryPairHarmonic_baseline q (2 * j + 1) hq0 ha hb
  have hbase_lt :
      (∑ j ∈ Finset.range M, (1 / (6 * (q : ℝ))) * C j) <
        ∑ j ∈ Finset.range M, H j * C j := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact mul_le_mul_of_nonneg_right (hH j hj).le (hC0 j)
    · refine ⟨j0, hj0, ?_⟩
      exact mul_lt_mul_of_pos_right (hH j0 hj0) hCj0
  have hdelta_lt : (1 : ℝ) / 3000000 <
      ∑ j ∈ Finset.range M, H j * C j := by
    calc
      (1 : ℝ) / 3000000 =
          (1 / (6 * (q : ℝ))) * ((q : ℝ) / 500000) := by
            field_simp
            norm_num
      _ ≤ (1 / (6 * (q : ℝ))) *
          (∑ j ∈ Finset.range M, C j) := by
            gcongr
      _ = ∑ j ∈ Finset.range M, (1 / (6 * (q : ℝ))) * C j := by
            rw [Finset.mul_sum]
      _ < _ := hbase_lt
  have hHL : ∀ j ∈ Finset.range M, H j * C j ≤ L j := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    rcases hcoeff j hj with ⟨ha, hb⟩
    have ha0 : 0 < positiveBoundaryCoefficient q (2 * j + 1) := by
      exact (by positivity : 0 < 1 / (3 * (q : ℝ))).trans ha
    have hb0 : 0 < positiveBoundaryCoefficient q (10 * (2 * j + 1)) := by
      exact (by positivity : 0 < 1 / (3 * (q : ℝ))).trans hb
    have hpair := centered_pair_loss_lower q A (2 * j + 1) ha0 hb0
    have hpair' : H j * C j ≤
        ‖centeredBoundaryTerm q A (2 * j + 1)‖ +
          ‖centeredBoundaryTerm q A (10 * (2 * j + 1))‖ -
          ‖centeredBoundaryTerm q A (2 * j + 1) +
            centeredBoundaryTerm q A (10 * (2 * j + 1))‖ := by
      dsimp [H, C]
      convert hpair using 1 <;> push_cast <;> ring
    apply hpair'.trans
    dsimp [L]
    apply primitiveRayLoss_pair_lower
    · omega
    · dsimp [q]
      omega
    · intro hdvd
      obtain ⟨d, hd⟩ := hdvd
      omega
  have hsumHL : (∑ j ∈ Finset.range M, H j * C j) ≤
      ∑ j ∈ Finset.range M, L j := Finset.sum_le_sum hHL
  let selected : Finset ℕ := (Finset.range M).image fun j => 2 * j + 1
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro i k hik
    change 2 * i + 1 = 2 * k + 1 at hik
    omega
  have hsumSelected : (∑ j ∈ Finset.range M, L j) =
      ∑ u ∈ selected, primitiveRayLoss q A u := by
    dsimp [L, selected]
    rw [Finset.sum_image]
    intro i hi k hk hik
    exact hinj hik
  have hselectedSub : selected ⊆ primitiveBoundarySupport q := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    apply Finset.mem_image.mpr
    refine ⟨2 * j + 1, ?_, ?_⟩
    · simp only [positiveBoundarySupport, Finset.mem_Icc]
      have hjM : j < M := Finset.mem_range.mp hj
      dsimp [q]
      omega
    · apply tenPrimitivePart_eq_self_of_not_dvd
      intro hdvd
      obtain ⟨d, hd⟩ := hdvd
      omega
  have hselectedAll : (∑ u ∈ selected, primitiveRayLoss q A u) ≤
      ∑ u ∈ primitiveBoundarySupport q, primitiveRayLoss q A u := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hselectedSub
      (fun u _ _ => primitiveRayLoss_nonneg q A u)
  have hgap : (1 : ℝ) / 3000000 <
      positiveBoundaryLoad q - primitiveBoundaryLoad q A := by
    rw [positiveBoundaryLoad_sub_primitiveBoundaryLoad]
    exact hdelta_lt.trans_le (hsumHL.trans_eq hsumSelected |>.trans hselectedAll)
  dsimp [q] at hgap ⊢
  linarith

private lemma exists_reduced_odd_multiplier_ten
    (m : ℕ) (hm : Odd m) :
    ∃ r : ℕ, 0 < r ∧ r < 10 ∧
      Real.cos (Real.pi * m / 10) = Real.cos (Real.pi * r / 10) := by
  let s := m % 20
  have hslt : s < 20 := Nat.mod_lt _ (by norm_num)
  have hdecomp : s + 20 * (m / 20) = m := by
    dsimp [s]
    exact Nat.mod_add_div m 20
  have hsodd : Odd s := by
    have heven : Even (20 * (m / 20)) := ⟨10 * (m / 20), by ring⟩
    have hle : 20 * (m / 20) ≤ m := by omega
    have hoddSub := Nat.Odd.sub_even hle hm heven
    have hsub : m - 20 * (m / 20) = s := by omega
    simpa only [hsub] using hoddSub
  have hs0 : 0 < s := by
    have hsne : s ≠ 0 := by
      intro hs
      rw [hs] at hsodd
      norm_num at hsodd
    omega
  by_cases hslow : s < 10
  · refine ⟨s, hs0, hslow, ?_⟩
    have harg : Real.pi * (m : ℝ) / 10 =
        Real.pi * (s : ℝ) / 10 + ((m / 20 : ℕ) : ℝ) * (2 * Real.pi) := by
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hdecomp
      push_cast at hcast
      rw [← hcast]
      ring
    rw [harg]
    convert Real.cos_add_nat_mul_two_pi (Real.pi * (s : ℝ) / 10) (m / 20) using 1 <;>
      push_cast <;> ring
  · have hs10 : 10 < s := by
      have htenEven : Even 10 := by norm_num
      have hsne : s ≠ 10 := by
        intro heq
        exact (Nat.not_even_iff_odd.mpr hsodd) (heq ▸ htenEven)
      omega
    let r := 20 - s
    have hr0 : 0 < r := by dsimp [r]; omega
    have hr10 : r < 10 := by dsimp [r]; omega
    refine ⟨r, hr0, hr10, ?_⟩
    have hms : Real.cos (Real.pi * m / 10) =
        Real.cos (Real.pi * s / 10) := by
      have harg : Real.pi * (m : ℝ) / 10 =
          Real.pi * (s : ℝ) / 10 + ((m / 20 : ℕ) : ℝ) * (2 * Real.pi) := by
        have hcast := congrArg (fun n : ℕ => (n : ℝ)) hdecomp
        push_cast at hcast
        rw [← hcast]
        ring
      rw [harg]
      convert Real.cos_add_nat_mul_two_pi (Real.pi * (s : ℝ) / 10) (m / 20) using 1 <;>
        push_cast <;> ring
    rw [hms]
    have harg : Real.pi * (s : ℝ) / 10 =
        2 * Real.pi - Real.pi * (r : ℝ) / 10 := by
      have hrs : r + s = 20 := by dsimp [r]; omega
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hrs
      push_cast at hcast
      linear_combination (Real.pi / 10) * hcast
    rw [harg]
    simpa using Real.cos_nat_mul_two_pi_sub (Real.pi * (r : ℝ) / 10) 1

private lemma one_div_fifty_le_ten_center_phase_loss (A : ℕ) :
    (1 : ℝ) / 50 ≤
      1 - Real.cos (Real.pi * (9 * (2 * A + 1)) / 10) := by
  have hm : Odd (9 * (2 * A + 1)) :=
    (show Odd 9 by norm_num).mul ⟨A, by omega⟩
  obtain ⟨r, hr0, hr10, hcos⟩ :=
    exists_reduced_odd_multiplier_ten (9 * (2 * A + 1)) hm
  have hcos' :
      Real.cos (Real.pi * (9 * (2 * (A : ℝ) + 1)) / 10) =
        Real.cos (Real.pi * (r : ℝ) / 10) := by
    convert hcos using 1 <;> push_cast <;> ring
  rw [hcos']
  have hx0 : 0 ≤ Real.pi * (r : ℝ) / 10 := by positivity
  have hxpi : Real.pi * (r : ℝ) / 10 ≤ Real.pi := by
    have hrR : (r : ℝ) ≤ 10 := by exact_mod_cast hr10.le
    nlinarith [Real.pi_pos]
  have hquad := two_mul_sq_div_pi_sq_le_one_sub_cos hx0 hxpi
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    (1 : ℝ) / 50 ≤ 2 * (Real.pi * (r : ℝ) / 10) ^ 2 / Real.pi ^ 2 := by
      field_simp
      nlinarith [sq_nonneg ((r : ℝ) - 1), Real.pi_pos]
    _ ≤ _ := hquad

/-- The exceptional first decimal mesh also has the same uniform primitive-ray
load gap. -/
theorem primitiveBoundaryLoad_ten_lt_positiveBoundaryLoad_sub_gap (A : ℕ) :
    primitiveBoundaryLoad 10 A < positiveBoundaryLoad 10 - 1 / 3000000 := by
  have ha := one_div_three_mul_lt_positiveBoundaryCoefficient 10 1
    (by norm_num) (by norm_num) (by norm_num)
  have hb := one_div_twenty_lt_positiveBoundaryCoefficient_ten
  have ha0 : 0 < positiveBoundaryCoefficient 10 1 :=
    (show (0 : ℝ) < 1 / (3 * (10 : ℝ)) by norm_num).trans ha
  have hb0 : 0 < positiveBoundaryCoefficient 10 10 :=
    (show (0 : ℝ) < 1 / 20 by norm_num).trans hb
  have hH : (1 : ℝ) / 50 < boundaryPairHarmonic 10 1 := by
    unfold boundaryPairHarmonic
    have hsum : 0 < positiveBoundaryCoefficient 10 1 +
        positiveBoundaryCoefficient 10 10 := add_pos ha0 hb0
    rw [lt_div_iff₀ hsum]
    nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]
  have hC := one_div_fifty_le_ten_center_phase_loss A
  have hpair := centered_pair_loss_lower 10 A 1 ha0 hb0
  have hloss : (1 : ℝ) / 2500 < primitiveRayLoss 10 A 1 := by
    have hprod : (1 : ℝ) / 2500 <
        boundaryPairHarmonic 10 1 *
          (1 - Real.cos (Real.pi * (9 * (2 * A + 1)) / 10)) := by
      nlinarith [mul_lt_mul_of_pos_right hH (show (0 : ℝ) < 1 / 50 by norm_num)]
    apply hprod.trans_le
    have hpair' : boundaryPairHarmonic 10 1 *
        (1 - Real.cos (Real.pi * (9 * (2 * A + 1)) / 10)) ≤
        ‖centeredBoundaryTerm 10 A 1‖ + ‖centeredBoundaryTerm 10 A 10‖ -
          ‖centeredBoundaryTerm 10 A 1 + centeredBoundaryTerm 10 A 10‖ := by
      convert hpair using 1 <;> norm_num
    apply hpair'.trans
    exact primitiveRayLoss_pair_lower 10 A 1 (by norm_num) (by norm_num) (by norm_num)
  have hone : 1 ∈ primitiveBoundarySupport 10 := by
    apply Finset.mem_image.mpr
    refine ⟨1, ?_, ?_⟩
    · simp [positiveBoundarySupport]
    · exact tenPrimitivePart_eq_self_of_not_dvd (by norm_num)
  have hall : primitiveRayLoss 10 A 1 ≤
      ∑ u ∈ primitiveBoundarySupport 10, primitiveRayLoss 10 A u := by
    exact Finset.single_le_sum (fun u _ => primitiveRayLoss_nonneg 10 A u) hone
  have hgap : (1 : ℝ) / 3000000 <
      positiveBoundaryLoad 10 - primitiveBoundaryLoad 10 A := by
    rw [positiveBoundaryLoad_sub_primitiveBoundaryLoad]
    exact (by norm_num : (1 : ℝ) / 3000000 < 1 / 2500).trans
      (hloss.trans_le hall)
  linarith

/-- Target- and scale-uniform strict primitive-ray load gap at every decimal
mesh `q = 10^k`, including the exceptional first scale. -/
theorem primitiveBoundaryLoad_pow_ten_lt_positiveBoundaryLoad_sub_gap
    (k A : ℕ) (hk : 1 ≤ k) :
    primitiveBoundaryLoad (10 ^ k) A <
      positiveBoundaryLoad (10 ^ k) - 1 / 3000000 := by
  cases k with
  | zero => omega
  | succ k =>
      cases k with
      | zero => simpa using primitiveBoundaryLoad_ten_lt_positiveBoundaryLoad_sub_gap A
      | succ k =>
          have h := primitiveBoundaryLoad_lt_positiveBoundaryLoad_sub_gap
            (10 ^ k) A (pow_pos (by norm_num) _)
          convert h using 1 <;> norm_num [pow_succ] <;> ring

end Theory.PiDigits.PrimitiveRayCoefficientGap

#print axioms Theory.PiDigits.PrimitiveRayCoefficientGap.one_div_three_mul_lt_positiveBoundaryCoefficient
#print axioms Theory.PiDigits.PrimitiveRayCoefficientGap.one_div_twenty_lt_positiveBoundaryCoefficient_ten
#print axioms Theory.PiDigits.PrimitiveRayCoefficientGap.odd_phase_spread
#print axioms Theory.PiDigits.PrimitiveRayCoefficientGap.decimal_center_phase_spread
#print axioms Theory.PiDigits.PrimitiveRayCoefficientGap.primitiveBoundaryLoad_lt_positiveBoundaryLoad_sub_gap
#print axioms Theory.PiDigits.PrimitiveRayCoefficientGap.primitiveBoundaryLoad_ten_lt_positiveBoundaryLoad_sub_gap
#print axioms Theory.PiDigits.PrimitiveRayCoefficientGap.primitiveBoundaryLoad_pow_ten_lt_positiveBoundaryLoad_sub_gap
