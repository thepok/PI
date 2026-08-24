import TheoryLib.PiQuantitativeBlockHitting.T139T139PrimitiveRayBoundaryConsumer

/-!
# T140: mixed-order boundary kernel

This file formalizes the finite directional part of the mixed-order Fejer
boundary mechanism.  The second Fejer order may be chosen independently of
the decimal interval scale.  No cancellation estimate for the decimal orbit
of pi is asserted.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.MixedOrderBoundaryKernel

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.DirectionalJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel

/-- Four indices underlying the product of order-`q` and order-`r` Fejer
factors. -/
abbrev MixedFejerIndex (q r : ℕ) :=
  (Fin q × Fin q) × (Fin r × Fin r)

/-- A base copy and the two shifts supplied by the cosine factor. -/
abbrev MixedBoundaryIndex (q r : ℕ) :=
  Sum (MixedFejerIndex q r) (Bool × MixedFejerIndex q r)

def mixedFejerFrequency {q r : ℕ} (i : MixedFejerIndex q r) : ℤ :=
  ((i.1.2 : ℤ) - (i.1.1 : ℤ)) + ((i.2.2 : ℤ) - (i.2.1 : ℤ))

/-- Frequencies in the exact finite presentation.  `false` is the `-1`
cosine shift and `true` is the `+1` shift. -/
def mixedBoundaryFrequency {q r : ℕ} : MixedBoundaryIndex q r → ℤ
  | Sum.inl i => mixedFejerFrequency i
  | Sum.inr (b, i) => mixedFejerFrequency i + if b then 1 else -1

/-- Coefficients in the exact finite presentation. -/
def mixedBoundaryCoefficient (q r : ℕ) : MixedBoundaryIndex q r → ℝ
  | Sum.inl _ => -Real.cos (Real.pi / q) / ((q : ℝ) * r)
  | Sum.inr _ => 1 / (2 * (q : ℝ) * r)

/-- Explicit finite Fourier presentation of
`(cos (2*pi*t) - cos (pi/q)) * F_q(t) * F_r(t)`. -/
def mixedBoundaryMinorant (q r : ℕ) (t : ℝ) : ℂ :=
  ∑ i : MixedBoundaryIndex q r,
    mixedBoundaryCoefficient q r i *
      Theory.PiDigits.T27.phase (mixedBoundaryFrequency i) t

/-- Its signed zero-frequency coefficient after equal frequencies are
collected. -/
def mixedBoundaryZeroCoefficient (q r : ℕ) : ℝ :=
  aggregatedCoefficient (mixedBoundaryCoefficient q r)
    (@mixedBoundaryFrequency q r) 0

private lemma mixedFejerPhaseSum_eq (q r : ℕ) (t : ℝ) :
    (∑ i : MixedFejerIndex q r,
      Theory.PiDigits.T27.phase (mixedFejerFrequency i) t) =
      (fejerFactor q t : ℂ) * q * ((fejerFactor r t : ℂ) * r) := by
  have hqsum :
      (∑ i : Fin q × Fin q,
        Theory.PiDigits.T27.phase ((i.2 : ℤ) - (i.1 : ℤ)) t) =
        (fejerFactor q t : ℂ) * q := by
    rw [Fintype.sum_prod_type]
    exact pairPhaseSum_eq q t
  have hrsum :
      (∑ i : Fin r × Fin r,
        Theory.PiDigits.T27.phase ((i.2 : ℤ) - (i.1 : ℤ)) t) =
        (fejerFactor r t : ℂ) * r := by
    rw [Fintype.sum_prod_type]
    exact pairPhaseSum_eq r t
  rw [Fintype.sum_prod_type]
  simp only [mixedFejerFrequency]
  simp_rw [Theory.PiDigits.T27.phase_add]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [hqsum, hrsum]

private lemma mixedBoundaryBaseSum_eq (q r : ℕ)
    (hq : 0 < q) (hr : 0 < r) (t : ℝ) :
    (∑ i : MixedFejerIndex q r,
      mixedBoundaryCoefficient q r (Sum.inl i) *
        Theory.PiDigits.T27.phase (mixedBoundaryFrequency (Sum.inl i)) t) =
      (-Real.cos (Real.pi / q) * fejerFactor q t * fejerFactor r t : ℝ) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [mixedBoundaryCoefficient, mixedBoundaryFrequency]
  rw [← Finset.mul_sum]
  rw [mixedFejerPhaseSum_eq q r t]
  push_cast
  field_simp

private lemma mixedBoundaryShiftSum_eq (q r : ℕ)
    (hq : 0 < q) (hr : 0 < r) (t : ℝ) :
    (∑ i : Bool × MixedFejerIndex q r,
      mixedBoundaryCoefficient q r (Sum.inr i) *
        Theory.PiDigits.T27.phase (mixedBoundaryFrequency (Sum.inr i)) t) =
      (Real.cos (2 * Real.pi * t) * fejerFactor q t * fejerFactor r t : ℝ) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [mixedBoundaryCoefficient, mixedBoundaryFrequency, Bool.false_eq_true,
    if_false, if_true]
  simp_rw [Theory.PiDigits.T27.phase_add]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [mixedFejerPhaseSum_eq q r t]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [mixedFejerPhaseSum_eq q r t]
  have hcos :
      Theory.PiDigits.T27.phase (-1) t + Theory.PiDigits.T27.phase 1 t =
        (2 * Real.cos (2 * Real.pi * t) : ℝ) := by
    rw [Theory.PiDigits.T27.phase_neg]
    have hphase : Theory.PiDigits.T27.phase 1 t =
        Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
      unfold Theory.PiDigits.T27.phase
      congr 1
      push_cast
      ring
    have hre : (Theory.PiDigits.T27.phase 1 t).re =
        Real.cos (2 * Real.pi * t) := by
      rw [hphase]
      exact Complex.exp_ofReal_mul_I_re _
    apply Complex.ext
    · change (conj (Theory.PiDigits.T27.phase 1 t)).re +
          (Theory.PiDigits.T27.phase 1 t).re =
        2 * Real.cos (2 * Real.pi * t)
      rw [Complex.conj_re, hre]
      ring
    · change (conj (Theory.PiDigits.T27.phase 1 t)).im +
          (Theory.PiDigits.T27.phase 1 t).im = 0
      rw [Complex.conj_im]
      ring
  push_cast at hcos ⊢
  field_simp
  rw [add_comm, hcos]
  ring

/-- Exact closed form of the mixed-order finite Fourier presentation. -/
theorem mixedBoundaryMinorant_eq (q r : ℕ)
    (hq : 0 < q) (hr : 0 < r) (t : ℝ) :
    mixedBoundaryMinorant q r t =
      ((Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q)) *
        fejerFactor q t * fejerFactor r t : ℝ) := by
  rw [mixedBoundaryMinorant, Fintype.sum_sum_type,
    mixedBoundaryBaseSum_eq q r hq hr t,
    mixedBoundaryShiftSum_eq q r hq hr t]
  push_cast
  ring

private lemma fejerFactor_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ fejerFactor n t := by
  unfold fejerFactor
  exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

/-- The mixed-order polynomial has the same exact outside sign as the
order-`q` boundary kernel.  No positivity assertion about its individual
Fourier coefficients is needed by this directional consumer. -/
theorem mixedBoundaryMinorant_re_nonpos_outside
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (x a : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (ha : 0 ≤ a)
    (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hout : x ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    (mixedBoundaryMinorant q r
      (x - (a + (q : ℝ)⁻¹ / 2))).re ≤ 0 := by
  let u := x - (a + (q : ℝ)⁻¹ / 2)
  have hsym := boundaryMinorant_re_nonpos_outside q hq x a hx ha haq hout
  rw [boundaryMinorant_eq q hq] at hsym
  rw [mixedBoundaryMinorant_eq q r hq hr]
  change (Real.cos (2 * Real.pi * u) - Real.cos (Real.pi / q)) *
      fejerFactor q u * fejerFactor r u ≤ 0
  have hqnonneg := fejerFactor_nonneg q u
  have hrnonneg := fejerFactor_nonneg r u
  by_cases hqzero : fejerFactor q u = 0
  · simp [hqzero]
  · have hqpos : 0 < fejerFactor q u := lt_of_le_of_ne hqnonneg (Ne.symm hqzero)
    have hdiff :
        Real.cos (2 * Real.pi * u) - Real.cos (Real.pi / q) ≤ 0 := by
      change (Real.cos (2 * Real.pi * u) - Real.cos (Real.pi / q)) *
          fejerFactor q u ^ 2 ≤ 0 at hsym
      nlinarith [sq_pos_of_pos hqpos]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hdiff hqnonneg) hrnonneg

/-- Target-centred directional defect of the mixed-order presentation. -/
def directionalMixedBoundaryDefect
    (x : ℕ → ℝ) (N q r : ℕ) (a : ℝ) : ℝ :=
  normalizedDirectionalFourierDefect
    (mixedBoundaryCoefficient q r) (@mixedBoundaryFrequency q r) x N
      (a + (q : ℝ)⁻¹ / 2)

/-- Avoiding a length-`1/q` interval forces the mixed-order directional
defect above its exact signed zero coefficient. -/
theorem finite_empty_decimalInterval_mixedBoundary_directional_obstruction
    (x : ℕ → ℝ) (N q r : ℕ) (a : ℝ)
    (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    mixedBoundaryZeroCoefficient q r ≤
      directionalMixedBoundaryDefect x N q r a := by
  unfold directionalMixedBoundaryDefect mixedBoundaryZeroCoefficient
  refine finiteFourierPresentation_directional_obstruction
    (mixedBoundaryCoefficient q r) (@mixedBoundaryFrequency q r) x N
      (a + (q : ℝ)⁻¹ / 2) _ hN (le_refl _) ?_
  intro j hj
  simpa only [mixedBoundaryMinorant] using
    mixedBoundaryMinorant_re_nonpos_outside q r hq hr (x j) a
      (hx j hj) ha haq (hempty j hj)

/-- A strict mixed-order directional margin forces a finite hit in the
prescribed interval. -/
theorem finite_decimalInterval_hit_of_mixedBoundary_directional_smallness
    (x : ℕ → ℝ) (N q r : ℕ) (a : ℝ)
    (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : directionalMixedBoundaryDefect x N q r a <
      mixedBoundaryZeroCoefficient q r) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  exact (not_lt_of_ge
    (finite_empty_decimalInterval_mixedBoundary_directional_obstruction
      x N q r a hN hq hr hx ha haq (fun j hj => hno j hj))) hsmall

/-- Exact bookkeeping identity behind directional finite separators.  It
retains the signed zero mode and both conjugate frequency directions. -/
theorem normalizedDirectionalFourierDefect_eq_zero_sub_average
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (minorant : ℝ → ℂ)
    (hminorant : ∀ t, minorant t = ∑ i, coefficient i *
      Theory.PiDigits.T27.phase (frequency i) t)
    (x : ℕ → ℝ) (N : ℕ) (center : ℝ) (hN : 0 < N) :
    normalizedDirectionalFourierDefect coefficient frequency x N center =
      aggregatedCoefficient coefficient frequency 0 -
        (∑ j ∈ Finset.range N, (minorant (x j - center)).re) / (N : ℝ) := by
  classical
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let z := centeredAggregatedNonzeroSum coefficient frequency x N center
  have hfourier :
      (∑ j ∈ Finset.range N, ∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)) =
      ∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
        Theory.PiDigits.T27.exponentialSum x N (frequency i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Theory.PiDigits.T27.exponentialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show x j - center = -center + x j by ring,
      Theory.PiDigits.T27.phase_add_real]
    ring
  have hsplit :
      (∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
        Theory.PiDigits.T27.exponentialSum x N (frequency i)) =
      (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z := by
    calc
      _ = (∑ i with frequency i = 0,
            coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
              Theory.PiDigits.T27.exponentialSum x N (frequency i)) +
          ∑ i with frequency i ≠ 0,
            coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
              Theory.PiDigits.T27.exponentialSum x N (frequency i) :=
          (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => frequency i = 0) _).symm
      _ = (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z := by
        congr 1
        · unfold aggregatedCoefficient
          push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hi0 : frequency i = 0 := (Finset.mem_filter.mp hi).2
          simp [hi0, Theory.PiDigits.T27.phase_zero,
            Theory.PiDigits.T27.exponentialSum_zero]
          ring
        · unfold z centeredAggregatedNonzeroSum
          symm
          simpa only [mul_assoc] using
            (sum_aggregatedCoefficient_mul_ne_zero coefficient frequency
              (fun h => Theory.PiDigits.T27.phase h (-center) *
                Theory.PiDigits.T27.exponentialSum x N h))
  have htotal :
      (∑ j ∈ Finset.range N, minorant (x j - center)) =
        (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z := by
    simp_rw [hminorant]
    exact hfourier.trans hsplit
  have hreal :
      (∑ j ∈ Finset.range N, (minorant (x j - center)).re) =
        (N : ℝ) * aggregatedCoefficient coefficient frequency 0 + z.re := by
    rw [show (∑ j ∈ Finset.range N, (minorant (x j - center)).re) =
        (∑ j ∈ Finset.range N, minorant (x j - center)).re by
      simp_rw [← Complex.reCLM_apply]
      rw [map_sum]]
    rw [htotal]
    simp
  unfold normalizedDirectionalFourierDefect
  change -z.re / (N : ℝ) = _
  rw [hreal]
  field_simp
  ring

private lemma fejerFactor_zero (n : ℕ) : fejerFactor n 0 = n := by
  unfold fejerFactor geometricSum
  simp [Theory.PiDigits.T27.phase]

private lemma fejerFactor_four_quarter :
    fejerFactor 4 (1 / 4 : ℝ) = 0 := by
  unfold fejerFactor
  have hmul := geometricSum_mul_one_sub_phase 4 (1 / 4 : ℝ)
  have htop :
      Theory.PiDigits.T27.phase ((4 : ℕ) : ℤ) (1 / 4 : ℝ) = 1 := by
    rw [Theory.PiDigits.T27.phase_nat_eq_pow]
    exact Theory.PiDigits.SharperNaturalScaleResonance.phase_uniformGrid_root_pow
      1 4 (by norm_num)
  have hbot : Theory.PiDigits.T27.phase 1 (1 / 4 : ℝ) ≠ 1 := by
    exact Theory.PiDigits.SharperNaturalScaleResonance.phase_uniformGrid_root_ne_one
      1 4 (by norm_num) (by norm_num) (by norm_num)
  rw [htop, sub_self] at hmul
  have hgeom : geometricSum 4 (1 / 4 : ℝ) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hbot.symm)
  rw [hgeom]
  norm_num

private lemma phase_re_eq_cos (h : ℤ) (x : ℝ) :
    (Theory.PiDigits.T27.phase h x).re =
      Real.cos (2 * Real.pi * (h : ℝ) * x) := by
  rw [Theory.PiDigits.T27.phase]
  convert Complex.exp_ofReal_mul_I_re (2 * Real.pi * (h : ℝ) * x) using 1
  push_cast
  ring

private lemma fejerFactor_ten_quarter :
    fejerFactor 10 (1 / 4 : ℝ) = 1 / 5 := by
  let z := Theory.PiDigits.T27.phase 1 (1 / 4 : ℝ)
  have hmul := geometricSum_mul_one_sub_phase 10 (1 / 4 : ℝ)
  have hz4 : z ^ 4 = 1 :=
    Theory.PiDigits.SharperNaturalScaleResonance.phase_uniformGrid_root_pow
      1 4 (by norm_num)
  have hz10 :
      Theory.PiDigits.T27.phase ((10 : ℕ) : ℤ) (1 / 4 : ℝ) = z ^ 2 := by
    rw [Theory.PiDigits.T27.phase_nat_eq_pow]
    change z ^ 10 = z ^ 2
    rw [show 10 = 4 * 2 + 2 by norm_num, pow_add, pow_mul, hz4]
    simp
  rw [hz10] at hmul
  have hzNorm : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, Theory.PiDigits.T27.norm_phase]
    norm_num
  have hzRe : z.re = 0 := by
    dsimp [z]
    rw [phase_re_eq_cos]
    convert Real.cos_pi_div_two using 1 <;> ring
  have hz2Norm : Complex.normSq (z ^ 2) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow,
      Theory.PiDigits.T27.norm_phase]
    norm_num
  have hz2Re : (z ^ 2).re = -1 := by
    rw [← Theory.PiDigits.T27.phase_nat_eq_pow]
    rw [phase_re_eq_cos]
    convert Real.cos_pi using 1 <;> ring
  have hden : Complex.normSq (1 - z) = 2 := by
    rw [Complex.normSq_sub, Complex.normSq_one, hzNorm]
    simp [hzRe]
    norm_num
  have hnum : Complex.normSq (1 - z ^ 2) = 4 := by
    rw [Complex.normSq_sub, Complex.normSq_one, hz2Norm]
    have hconj : (conj (z ^ 2)).re = (z ^ 2).re :=
      Complex.conj_re (z ^ 2)
    simp only [one_mul]
    rw [hconj, hz2Re]
    norm_num
  have hnorm := congrArg Complex.normSq hmul
  rw [Complex.normSq_mul, hden, hnum] at hnorm
  unfold fejerFactor
  norm_num
  nlinarith

private lemma cos_pi_div_ten_sq :
    Real.cos (Real.pi / 10) ^ 2 = (5 + Real.sqrt 5) / 8 := by
  have hdouble : Real.cos (Real.pi / 5) =
      2 * Real.cos (Real.pi / 10) ^ 2 - 1 := by
    rw [show Real.pi / 5 = 2 * (Real.pi / 10) by ring,
      Real.cos_two_mul]
  rw [Real.cos_pi_div_five] at hdouble
  nlinarith

private lemma cos_pi_div_ten_lower :
    (951 : ℝ) / 1000 < Real.cos (Real.pi / 10) := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 5 ^ 2 = 5 := by norm_num
  have hsqrtLower : (559 : ℝ) / 250 < Real.sqrt 5 := by nlinarith
  have hcos0 : 0 ≤ Real.cos (Real.pi / 10) :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [← sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 951 / 1000) hcos0]
  rw [cos_pi_div_ten_sq]
  nlinarith

private lemma cos_pi_div_ten_upper :
    Real.cos (Real.pi / 10) < (119 : ℝ) / 125 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 5 ^ 2 = 5 := by norm_num
  have hsqrtUpper : Real.sqrt 5 < (9 : ℝ) / 4 := by nlinarith
  have hcos0 : 0 ≤ Real.cos (Real.pi / 10) :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [← sq_lt_sq₀ hcos0 (by norm_num : (0 : ℝ) ≤ 119 / 125)]
  rw [cos_pi_div_ten_sq]
  nlinarith

/-- The exact 130-point witness from the mixed-order audit. -/
def mixedBoundarySeparatorSample (j : ℕ) : ℝ :=
  if j = 0 then 1 / 20 else 3 / 10

private lemma complex_cos_of_real_re (x : ℝ) :
    (Complex.cos (x : ℂ)).re = Real.cos x := by
  exact Complex.cos_ofReal_re x

private lemma mixedBoundaryMinorant_ten_four_zero :
    (mixedBoundaryMinorant 10 4 0).re =
      40 * (1 - Real.cos (Real.pi / 10)) := by
  rw [mixedBoundaryMinorant_eq 10 4 (by norm_num) (by norm_num),
    fejerFactor_zero, fejerFactor_zero]
  norm_num
  rw [show (Real.pi : ℂ) / 10 =
      ((Real.pi / 10 : ℝ) : ℂ) by push_cast; ring,
    complex_cos_of_real_re]
  ring

private lemma mixedBoundaryMinorant_ten_four_quarter :
    (mixedBoundaryMinorant 10 4 (1 / 4 : ℝ)).re = 0 := by
  rw [mixedBoundaryMinorant_eq 10 4 (by norm_num) (by norm_num),
    fejerFactor_four_quarter]
  norm_num

private lemma boundaryMinorant_ten_zero :
    (boundaryMinorant 10 0).re =
      100 * (1 - Real.cos (Real.pi / 10)) := by
  rw [boundaryMinorant_eq 10 (by norm_num), fejerFactor_zero]
  norm_num
  rw [show (Real.pi : ℂ) / 10 =
      ((Real.pi / 10 : ℝ) : ℂ) by push_cast; ring,
    complex_cos_of_real_re]
  ring

private lemma boundaryMinorant_ten_quarter :
    (boundaryMinorant 10 (1 / 4 : ℝ)).re =
      -Real.cos (Real.pi / 10) / 25 := by
  rw [boundaryMinorant_eq 10 (by norm_num), fejerFactor_ten_quarter]
  have hcos : Real.cos (2 * Real.pi * (1 / 4 : ℝ)) = 0 := by
    convert Real.cos_pi_div_two using 1 <;> ring
  rw [hcos]
  norm_num
  rw [show (Real.pi : ℂ) / 10 =
      ((Real.pi / 10 : ℝ) : ℂ) by push_cast; ring,
    complex_cos_of_real_re]
  ring

private lemma mixedSeparatorSample_sub_center (j : ℕ) :
    mixedBoundarySeparatorSample j - 1 / 20 =
      if j = 0 then 0 else 1 / 4 := by
  unfold mixedBoundarySeparatorSample
  split <;> norm_num

private lemma mixedSeparator_sum_mixed :
    (∑ j ∈ Finset.range 130,
      (mixedBoundaryMinorant 10 4
        (mixedBoundarySeparatorSample j - 1 / 20)).re) =
      40 * (1 - Real.cos (Real.pi / 10)) := by
  simp_rw [mixedSeparatorSample_sub_center]
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.range 130)
    (f := fun j =>
      (mixedBoundaryMinorant 10 4 (if j = 0 then 0 else 1 / 4)).re)
    (i := 0) (by simp)]
  rw [if_pos rfl, mixedBoundaryMinorant_ten_four_zero]
  have htail :
      (∑ x ∈ Finset.range 130 \ {0},
        (mixedBoundaryMinorant 10 4 (if x = 0 then 0 else 1 / 4)).re) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : j ≠ 0 := by
      intro hjz
      subst j
      simpa using hj
    rw [if_neg hj0, mixedBoundaryMinorant_ten_four_quarter]
  rw [htail, add_zero]

private lemma mixedSeparator_sum_symmetric :
    (∑ j ∈ Finset.range 130,
      (boundaryMinorant 10
        (mixedBoundarySeparatorSample j - 1 / 20)).re) =
      (2500 - 2629 * Real.cos (Real.pi / 10)) / 25 := by
  simp_rw [mixedSeparatorSample_sub_center]
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.range 130)
    (f := fun j =>
      (boundaryMinorant 10 (if j = 0 then 0 else 1 / 4)).re)
    (i := 0) (by simp)]
  rw [if_pos rfl, boundaryMinorant_ten_zero]
  have htail :
      (∑ x ∈ Finset.range 130 \ {0},
        (boundaryMinorant 10 (if x = 0 then 0 else 1 / 4)).re) =
        129 * (-Real.cos (Real.pi / 10) / 25) := by
    rw [show Finset.range 130 \ {0} = Finset.Ico 1 130 by ext j; simp; omega]
    calc
      _ = ∑ _ ∈ Finset.Ico 1 130,
          (-Real.cos (Real.pi / 10) / 25) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : j ≠ 0 := by
          intro hjz
          subst j
          simpa using hj
        rw [if_neg hj0, boundaryMinorant_ten_quarter]
      _ = _ := by simp
  rw [htail]
  ring

/-- At `q = 10`, allowing mixed order `r = 4` is a strict finite-predicate
weakening of the symmetric order-`10` directional criterion.  This sample is
not the decimal orbit of pi. -/
theorem mixedBoundary_directional_ten_four_strict_vs_symmetric :
    directionalMixedBoundaryDefect mixedBoundarySeparatorSample 130 10 4 0 <
        mixedBoundaryZeroCoefficient 10 4 ∧
      ¬ directionalBoundaryDefect mixedBoundarySeparatorSample 130 10 0 <
        boundaryZeroCoefficient 10 := by
  constructor
  · unfold directionalMixedBoundaryDefect
    rw [show (0 : ℝ) + ((10 : ℕ) : ℝ)⁻¹ / 2 = 1 / 20 by norm_num]
    rw [normalizedDirectionalFourierDefect_eq_zero_sub_average
      (mixedBoundaryCoefficient 10 4) (@mixedBoundaryFrequency 10 4)
      (mixedBoundaryMinorant 10 4) (fun _ => rfl)
      mixedBoundarySeparatorSample 130 (1 / 20) (by norm_num)]
    rw [mixedSeparator_sum_mixed]
    have hpos : 0 < 1 - Real.cos (Real.pi / 10) := by
      linarith [cos_pi_div_ten_upper]
    unfold mixedBoundaryZeroCoefficient
    norm_num
    linarith
  · unfold directionalBoundaryDefect
    rw [show (0 : ℝ) + ((10 : ℕ) : ℝ)⁻¹ / 2 = 1 / 20 by norm_num]
    rw [normalizedDirectionalFourierDefect_eq_zero_sub_average
      (boundaryCoefficient 10) (@jacksonFrequency 10)
      (boundaryMinorant 10) (fun _ => rfl)
      mixedBoundarySeparatorSample 130 (1 / 20) (by norm_num)]
    rw [mixedSeparator_sum_symmetric]
    have hneg :
        (2500 - 2629 * Real.cos (Real.pi / 10)) / 25 < 0 := by
      nlinarith [cos_pi_div_ten_lower]
    unfold boundaryZeroCoefficient
    norm_num
    linarith

end Theory.PiDigits.MixedOrderBoundaryKernel

#print axioms Theory.PiDigits.MixedOrderBoundaryKernel.mixedBoundaryMinorant_eq
#print axioms Theory.PiDigits.MixedOrderBoundaryKernel.mixedBoundaryMinorant_re_nonpos_outside
#print axioms Theory.PiDigits.MixedOrderBoundaryKernel.finite_empty_decimalInterval_mixedBoundary_directional_obstruction
#print axioms Theory.PiDigits.MixedOrderBoundaryKernel.finite_decimalInterval_hit_of_mixedBoundary_directional_smallness
#print axioms Theory.PiDigits.MixedOrderBoundaryKernel.normalizedDirectionalFourierDefect_eq_zero_sub_average
#print axioms Theory.PiDigits.MixedOrderBoundaryKernel.mixedBoundary_directional_ten_four_strict_vs_symmetric
