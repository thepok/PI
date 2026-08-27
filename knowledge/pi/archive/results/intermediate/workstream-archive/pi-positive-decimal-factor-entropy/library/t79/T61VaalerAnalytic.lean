import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TheoryLib.PiDecimalFactorComplexity.T8PiLacunaryNearReturns
import TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit
import TheoryLib.PiPositiveDecimalFactorEntropy.T58T58TriangularFejerAudit
import TheoryLib.PiDecimalFactorComplexity.T10PiWeightedFourierReduction

/-!
# T61: analytic facts for the explicit periodic Vaaler polynomial

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file isolates the real analysis needed by the explicit polynomial in
`T61PeriodicVaaler`.  It does not import that research artifact.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace DecimalFactorComplexity.T61VaalerAnalytic

open DecimalFactorComplexity
open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.SparseLongBandFejer
open DecimalFactorComplexity.SparseMicroscopicEquivalence
open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T58TriangularFejerAudit
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The coefficient function before sampling it at `h / H`. -/
def coefficientShape (y : ℝ) : ℝ :=
  Real.sin (Real.pi * y) / Real.pi +
    2 * (1 - y) * Real.cos (Real.pi * y)

/-- The explicit positive-frequency coefficient. -/
def vaalerCoefficient (H h : ℕ) : ℝ :=
  (H : ℝ)⁻¹ * coefficientShape ((h : ℝ) / (H : ℝ))

/-- The degree-`H-1` real periodic polynomial. -/
def periodicVaalerMajorant (H : ℕ) (x : ℝ) : ℝ :=
  2 / (H : ℝ) +
    2 * ∑ h ∈ Finset.Ico 1 H,
      vaalerCoefficient H h * Real.cos (2 * Real.pi * (h : ℝ) * x)

/-- The strict central circular indicator. -/
def strictCentralIndicator (H : ℕ) (x : ℝ) : ℝ :=
  if circleDistance x < (2 * (H : ℝ))⁻¹ then 1 else 0

/-- The auxiliary function whose nonzero root controls all coefficient signs. -/
def tangentRootFunction (t : ℝ) : ℝ := Real.tan t - 2 * t

theorem continuousOn_tangentRootFunction :
    ContinuousOn tangentRootFunction (Set.Icc (Real.pi / 4) (Real.arctan 4)) := by
  apply ContinuousOn.sub
  · apply ContinuousOn.mono Real.continuousOn_tan
    intro x hx
    simp only [Set.mem_setOf_eq]
    have hlow : -(Real.pi / 2) < x := by
      have hpi : 0 < Real.pi := Real.pi_pos
      have := hx.1
      linarith
    have hupp : x < Real.pi / 2 :=
      hx.2.trans_lt (Real.arctan_lt_pi_div_two 4)
    exact (Real.cos_pos_of_mem_Ioo ⟨hlow, hupp⟩).ne'
  · fun_prop

theorem tangentRootFunction_pi_div_four_neg :
    tangentRootFunction (Real.pi / 4) < 0 := by
  rw [tangentRootFunction, Real.tan_pi_div_four]
  have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
  linarith

theorem tangentRootFunction_arctan_four_pos :
    0 < tangentRootFunction (Real.arctan 4) := by
  rw [tangentRootFunction, Real.tan_arctan]
  have harctan : Real.arctan 4 < Real.pi / 2 := Real.arctan_lt_pi_div_two 4
  have hpi : Real.pi < 4 := Real.pi_lt_four
  linarith

theorem exists_tangentRoot :
    ∃ t : ℝ, Real.pi / 4 < t ∧ t < Real.arctan 4 ∧
      tangentRootFunction t = 0 := by
  have hle : Real.pi / 4 ≤ Real.arctan 4 := by
    rw [← Real.arctan_one]
    exact (Real.arctan_strictMono (by norm_num)).le
  obtain ⟨t, htmem, htzero⟩ :=
    intermediate_value_Icc (a := Real.pi / 4) (b := Real.arctan 4) hle
      continuousOn_tangentRootFunction
      ⟨tangentRootFunction_pi_div_four_neg.le,
        tangentRootFunction_arctan_four_pos.le⟩
  refine ⟨t, ?_, ?_, htzero⟩
  · rcases htmem.1.eq_or_lt with heq | hlt
    · subst t
      exact (tangentRootFunction_pi_div_four_neg.ne htzero).elim
    · exact hlt
  · rcases htmem.2.eq_or_lt with heq | hlt
    · subst t
      exact (tangentRootFunction_arctan_four_pos.ne' htzero).elim
    · exact hlt

theorem tangentRootFunction_strictMonoOn :
    StrictMonoOn tangentRootFunction (Set.Ico (Real.pi / 4) (Real.pi / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
  · apply ContinuousOn.sub
    · apply ContinuousOn.mono Real.continuousOn_tan
      intro x hx
      simp only [Set.mem_setOf_eq]
      have hlow : -(Real.pi / 2) < x := by
        have hpi := Real.pi_pos
        linarith [hx.1]
      exact (Real.cos_pos_of_mem_Ioo ⟨hlow, hx.2⟩).ne'
    · fun_prop
  · intro x hx
    rw [interior_Ico] at hx
    have hlow : -(Real.pi / 2) < x := by
      have hpi := Real.pi_pos
      linarith [hx.1]
    have hcos : Real.cos x ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨hlow, hx.2⟩).ne'
    have hderiv : deriv tangentRootFunction x = 1 / Real.cos x ^ 2 - 2 := by
      change deriv (fun t : ℝ => Real.tan t - 2 * t) x = _
      convert ((Real.hasDerivAt_tan hcos).sub
        ((hasDerivAt_id x).const_mul 2)).deriv using 1 <;> ring
    rw [hderiv]
    have htan : 1 < Real.tan x := by
      rw [← Real.tan_pi_div_four]
      exact Real.strictMonoOn_tan
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ⟨hlow, hx.2⟩ hx.1
    rw [Real.tan_eq_sin_div_cos] at htan
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx.2⟩
    have hsincos : Real.cos x < Real.sin x :=
      by simpa using (lt_div_iff₀ hcospos).mp htan
    have hsinpos : 0 < Real.sin x := hcospos.trans hsincos
    have hsin_sq : Real.cos x ^ 2 < Real.sin x ^ 2 :=
      (sq_lt_sq₀ hcospos.le hsinpos.le).mpr hsincos
    have htrig := Real.sin_sq_add_cos_sq x
    have hcoshalf : Real.cos x ^ 2 < 1 / 2 := by nlinarith
    rw [sub_pos]
    apply (lt_div_iff₀ (sq_pos_of_pos hcospos)).2
    nlinarith

theorem tangentRootFunction_signs {t₀ : ℝ}
    (ht₀ : Real.pi / 4 < t₀ ∧ t₀ < Real.arctan 4 ∧
      tangentRootFunction t₀ = 0) {t : ℝ}
    (ht : Real.pi / 4 ≤ t) (htop : t < Real.pi / 2) :
    (tangentRootFunction t < 0 ↔ t < t₀) ∧
      (tangentRootFunction t = 0 ↔ t = t₀) ∧
      (0 < tangentRootFunction t ↔ t₀ < t) := by
  have ht₀top : t₀ ≤ Real.pi / 2 :=
    (ht₀.2.1.trans (Real.arctan_lt_pi_div_two 4)).le
  have hmono := tangentRootFunction_strictMonoOn
  have htm : t ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) := ⟨ht, htop⟩
  have ht₀m : t₀ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) :=
    ⟨ht₀.1.le, ht₀.2.1.trans (Real.arctan_lt_pi_div_two 4)⟩
  constructor
  · constructor
    · intro hneg
      by_contra hnot
      have hle : t₀ ≤ t := le_of_not_gt hnot
      rcases hle.eq_or_lt with heq | hlt
      · subst t
        linarith
      · have := hmono ht₀m htm hlt
        linarith
    · intro hlt
      have := hmono htm ht₀m hlt
      linarith
  constructor
  · constructor
    · intro hz
      exact hmono.injOn htm ht₀m (hz.trans ht₀.2.2.symm)
    · rintro rfl
      exact ht₀.2.2
  · constructor
    · intro hpos
      by_contra hnot
      have hle : t ≤ t₀ := le_of_not_gt hnot
      rcases hle.eq_or_lt with heq | hlt
      · subst t
        linarith
      · have := hmono htm ht₀m hlt
        linarith
    · intro hlt
      have := hmono ht₀m htm hlt
      linarith

theorem tangentRootFunction_neg_of_pos_of_lt_pi_div_four {t : ℝ}
    (ht : 0 < t) (htop : t < Real.pi / 4) :
    tangentRootFunction t < 0 := by
  have htpi : t < Real.pi := by linarith [Real.pi_pos]
  have hsint : Real.sin t < t := Real.sin_lt ht
  have htthird : t < Real.pi / 3 := by linarith [Real.pi_pos]
  have hcost : 1 / 2 < Real.cos t := by
    rw [← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos
      ⟨ht.le, htpi.le⟩ ⟨by positivity, by linarith [Real.pi_pos]⟩ htthird
  have hcospos : 0 < Real.cos t := by linarith
  rw [tangentRootFunction, Real.tan_eq_sin_div_cos]
  rw [sub_neg]
  apply (div_lt_iff₀ hcospos).2
  nlinarith

theorem coefficientShape_eq_tangentRootFunction {y : ℝ}
    (hy : 1 / 2 < y) (hy1 : y < 1) :
    coefficientShape y =
      Real.cos (Real.pi * (1 - y)) / Real.pi *
        tangentRootFunction (Real.pi * (1 - y)) := by
  have htpos : 0 < Real.pi * (1 - y) := mul_pos Real.pi_pos (sub_pos.mpr hy1)
  have httop : Real.pi * (1 - y) < Real.pi / 2 := by
    convert mul_lt_mul_of_pos_left (show 1 - y < 1 / 2 by linarith) Real.pi_pos using 1 <;>
      ring
  have hcos : Real.cos (Real.pi * (1 - y)) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], httop⟩).ne'
  have hangle : Real.pi * y = Real.pi - Real.pi * (1 - y) := by ring
  rw [coefficientShape, tangentRootFunction, Real.tan_eq_sin_div_cos, hangle,
    Real.sin_pi_sub, Real.cos_pi_sub]
  field_simp [Real.pi_ne_zero, hcos]
  <;> ring

theorem coefficientShape_pos_of_mem_Ioc {y : ℝ}
    (hy : y ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    0 < coefficientShape y := by
  have hy1 : y < 1 := hy.2.trans_lt (by norm_num)
  have hangpos : 0 < Real.pi * y := mul_pos Real.pi_pos hy.1
  have hanglt : Real.pi * y < Real.pi :=
    by simpa using mul_lt_mul_of_pos_left hy1 Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi * y) :=
    Real.sin_pos_of_pos_of_lt_pi hangpos hanglt
  have hcos : 0 ≤ Real.cos (Real.pi * y) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith
    · convert mul_le_mul_of_nonneg_left hy.2 Real.pi_pos.le using 1 <;> ring
  rw [coefficientShape]
  have hfirst : 0 < Real.sin (Real.pi * y) / Real.pi :=
    div_pos hsin Real.pi_pos
  have hsecond : 0 ≤ 2 * (1 - y) * Real.cos (Real.pi * y) := by positivity
  linarith

/-- There is a single transition ratio, independent of `H`, for the explicit
coefficient shape on the open unit interval. -/
theorem exists_coefficientShape_sign_transition :
    ∃ u : ℝ, 1 / 2 < u ∧ u < 1 ∧
      ∀ y : ℝ, 0 < y → y < 1 →
        (0 < coefficientShape y ↔ y < u) ∧
        (coefficientShape y = 0 ↔ y = u) ∧
        (coefficientShape y < 0 ↔ u < y) := by
  obtain ⟨t₀, ht₀low, ht₀high, ht₀zero⟩ := exists_tangentRoot
  let u : ℝ := 1 - t₀ / Real.pi
  have ht₀pi : t₀ < Real.pi / 2 :=
    ht₀high.trans (Real.arctan_lt_pi_div_two 4)
  have hu : 1 / 2 < u := by
    dsimp [u]
    have hdiv : t₀ / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [ht₀pi]
    linarith
  have hu1 : u < 1 := by
    dsimp [u]
    have ht₀pos : 0 < t₀ := by linarith [Real.pi_pos]
    exact sub_lt_self _ (div_pos ht₀pos Real.pi_pos)
  refine ⟨u, hu, hu1, ?_⟩
  intro y hy0 hy1
  by_cases hyhalf : y ≤ 1 / 2
  · have hshape : 0 < coefficientShape y :=
      coefficientShape_pos_of_mem_Ioc ⟨hy0, hyhalf⟩
    have hyu : y < u := hyhalf.trans_lt hu
    constructor
    · exact ⟨fun _ => hyu, fun _ => hshape⟩
    constructor
    · exact ⟨fun hz => (hshape.ne' hz).elim, fun hyu' => (hyu.ne hyu').elim⟩
    · exact ⟨fun hneg => (lt_asymm hshape hneg).elim,
        fun huy => (lt_asymm huy hyu).elim⟩
  · have hyhalf' : 1 / 2 < y := lt_of_not_ge hyhalf
    let t : ℝ := Real.pi * (1 - y)
    have htpos : 0 < t := mul_pos Real.pi_pos (sub_pos.mpr hy1)
    have httop : t < Real.pi / 2 := by
      dsimp [t]
      convert mul_lt_mul_of_pos_left (show 1 - y < 1 / 2 by linarith) Real.pi_pos using 1 <;>
        ring
    have hcospos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], httop⟩
    have hfactor : 0 < Real.cos t / Real.pi := div_pos hcospos Real.pi_pos
    have hshape : coefficientShape y =
        Real.cos t / Real.pi * tangentRootFunction t := by
      simpa [t] using coefficientShape_eq_tangentRootFunction hyhalf' hy1
    have hyu_iff : y < u ↔ t₀ < t := by
      dsimp [u, t]
      constructor
      · intro h
        have hd : t₀ / Real.pi < 1 - y := by linarith
        have hm := (div_lt_iff₀ Real.pi_pos).mp hd
        nlinarith
      · intro h
        have hm : t₀ < (1 - y) * Real.pi := by simpa [mul_comm] using h
        have hd : t₀ / Real.pi < 1 - y :=
          (div_lt_iff₀ Real.pi_pos).mpr hm
        linarith
    have hyueq_iff : y = u ↔ t = t₀ := by
      dsimp [u, t]
      constructor
      · intro h
        field_simp [Real.pi_ne_zero] at h ⊢
        nlinarith [Real.pi_pos]
      · intro h
        field_simp [Real.pi_ne_zero] at h ⊢
        nlinarith [Real.pi_pos]
    have huy_iff : u < y ↔ t < t₀ := by
      dsimp [u, t]
      constructor
      · intro h
        have hd : 1 - y < t₀ / Real.pi := by linarith
        have hm := (lt_div_iff₀ Real.pi_pos).mp hd
        nlinarith
      · intro h
        have hm : (1 - y) * Real.pi < t₀ := by simpa [mul_comm] using h
        have hd : 1 - y < t₀ / Real.pi :=
          (lt_div_iff₀ Real.pi_pos).mpr hm
        linarith
    by_cases htquarter : Real.pi / 4 ≤ t
    · have hsigns := tangentRootFunction_signs
        ⟨ht₀low, ht₀high, ht₀zero⟩ htquarter httop
      rw [hshape, mul_pos_iff_of_pos_left hfactor]
      have hzero :
          (Real.cos t / Real.pi * tangentRootFunction t = 0 ↔
            tangentRootFunction t = 0) := by
        simp [hfactor.ne']
      have hneg :
          (Real.cos t / Real.pi * tangentRootFunction t < 0 ↔
            tangentRootFunction t < 0) := by
        constructor
        · intro hp
          by_contra hn
          exact (not_lt_of_ge (mul_nonneg hfactor.le (le_of_not_gt hn))) hp
        · exact mul_neg_of_pos_of_neg hfactor
      rw [hzero, hneg]
      exact ⟨hsigns.2.2.trans hyu_iff.symm,
        hsigns.2.1.trans hyueq_iff.symm,
        hsigns.1.trans huy_iff.symm⟩
    · have htquarter' : t < Real.pi / 4 := lt_of_not_ge htquarter
      have htneg := tangentRootFunction_neg_of_pos_of_lt_pi_div_four htpos htquarter'
      have htt₀ : t < t₀ := htquarter'.trans ht₀low
      have huy : u < y := huy_iff.mpr htt₀
      rw [hshape]
      have hshapeneg : Real.cos t / Real.pi * tangentRootFunction t < 0 :=
        mul_neg_of_pos_of_neg hfactor htneg
      constructor
      · exact ⟨fun hpos => (lt_asymm hpos hshapeneg).elim,
          fun hyu => (lt_asymm hyu huy).elim⟩
      constructor
      · exact ⟨fun hz => (hshapeneg.ne hz).elim,
          fun hyu => (huy.ne' hyu).elim⟩
      · exact ⟨fun _ => huy, fun _ => hshapeneg⟩

/-- Exact positive/zero/negative classification of every sampled coefficient. -/
theorem exists_vaalerCoefficient_sign_transition (H : ℕ) (hH : 2 ≤ H) :
    ∃ u : ℝ, 1 / 2 < u ∧ u < 1 ∧
      ∀ h : ℕ, 1 ≤ h → h < H →
        (0 < vaalerCoefficient H h ↔ (h : ℝ) / H < u) ∧
        (vaalerCoefficient H h = 0 ↔ (h : ℝ) / H = u) ∧
        (vaalerCoefficient H h < 0 ↔ u < (h : ℝ) / H) := by
  obtain ⟨u, hu, hu1, hsign⟩ := exists_coefficientShape_sign_transition
  refine ⟨u, hu, hu1, ?_⟩
  intro h hh0 hhH
  have hHpos : 0 < (H : ℝ) := by positivity
  have hratio0 : 0 < (h : ℝ) / (H : ℝ) := by positivity
  have hratio1 : (h : ℝ) / (H : ℝ) < 1 := by
    rw [div_lt_one hHpos]
    exact_mod_cast hhH
  have hs := hsign ((h : ℝ) / (H : ℝ)) hratio0 hratio1
  have hinv : 0 < (H : ℝ)⁻¹ := inv_pos.mpr hHpos
  rw [vaalerCoefficient, mul_pos_iff_of_pos_left hinv]
  have hzero :
      ((H : ℝ)⁻¹ * coefficientShape ((h : ℝ) / (H : ℝ)) = 0 ↔
        coefficientShape ((h : ℝ) / (H : ℝ)) = 0) := by
    simp [hinv.ne']
  have hneg :
      ((H : ℝ)⁻¹ * coefficientShape ((h : ℝ) / (H : ℝ)) < 0 ↔
        coefficientShape ((h : ℝ) / (H : ℝ)) < 0) := by
    constructor
    · intro hp
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg hinv.le (le_of_not_gt hn))) hp
    · exact mul_neg_of_pos_of_neg hinv
  rw [hzero, hneg]
  exact hs

theorem complex_root_sum (H : ℕ) (hH : 2 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      Complex.exp (((2 * Real.pi * (h : ℝ) / (H : ℝ) : ℝ) : ℂ) * Complex.I)) = -1 := by
  let z : ℂ := Complex.exp (((2 * Real.pi / (H : ℝ) : ℝ) : ℂ) * Complex.I)
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  have hHc : (H : ℂ) ≠ 0 := by exact_mod_cast hH0
  have hzpow : z ^ H = 1 := by
    change Complex.exp (((2 * Real.pi / (H : ℝ) : ℝ) : ℂ) * Complex.I) ^ H = 1
    rw [← Complex.exp_nat_mul]
    have harg : (H : ℂ) * (((2 * Real.pi / (H : ℝ) : ℝ) : ℂ) * Complex.I) =
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp [hH0, hHc]
    rw [harg, Complex.exp_mul_I]
    norm_num
  have hz1 : z ≠ 1 := by
    change Complex.exp (((2 * Real.pi / (H : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 1
    intro hz
    have hre := congrArg Complex.re hz
    have hre' : Real.cos (2 * Real.pi / (H : ℝ)) = 1 := by
      simpa only [Complex.exp_ofReal_mul_I_re, Complex.one_re] using hre
    have hangle0 : 0 < 2 * Real.pi / (H : ℝ) := by positivity
    have hanglepi : 2 * Real.pi / (H : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < H)]
      have hcast : (2 : ℝ) ≤ H := by exact_mod_cast hH
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcast Real.pi_pos.le
    have hcoslt : Real.cos (2 * Real.pi / (H : ℝ)) < 1 := by
      rw [← Real.cos_zero]
      exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
        ⟨hangle0.le, hanglepi⟩ hangle0
    linarith
  have hgeom := geom_sum_mul z H
  have hsum0 : ∑ h ∈ Finset.range H, z ^ h = 0 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hz1)
    simpa [hzpow] using hgeom
  have hpowers (h : ℕ) : z ^ h =
      Complex.exp (((2 * Real.pi * (h : ℝ) / (H : ℝ) : ℝ) : ℂ) * Complex.I) := by
    change Complex.exp (((2 * Real.pi / (H : ℝ) : ℝ) : ℂ) * Complex.I) ^ h = _
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [hH0, hHc]
  simp_rw [← hpowers]
  rw [Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ H), hsum0]
  simp

theorem sum_cos_roots (H : ℕ) (hH : 2 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ))) = -1 := by
  calc
    (∑ h ∈ Finset.Ico 1 H,
        Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ))) =
        Complex.re (∑ h ∈ Finset.Ico 1 H,
          Complex.exp (((2 * Real.pi * (h : ℝ) / (H : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      change (∑ h ∈ Finset.Ico 1 H,
        Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ))) =
          Complex.reCLM.toAddMonoidHom (∑ h ∈ Finset.Ico 1 H,
            Complex.exp (((2 * Real.pi * (h : ℝ) / (H : ℝ) : ℝ) : ℂ) * Complex.I))
      rw [map_sum Complex.reCLM.toAddMonoidHom]
      apply Finset.sum_congr rfl
      intro h _hh
      exact (Complex.exp_ofReal_mul_I_re _).symm
    _ = Complex.re (-1) := congrArg Complex.re (complex_root_sum H hH)
    _ = -1 := by norm_num

theorem sum_sin_roots (H : ℕ) (hH : 2 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      Real.sin (2 * Real.pi * (h : ℝ) / (H : ℝ))) = 0 := by
  calc
    (∑ h ∈ Finset.Ico 1 H,
        Real.sin (2 * Real.pi * (h : ℝ) / (H : ℝ))) =
        Complex.im (∑ h ∈ Finset.Ico 1 H,
          Complex.exp (((2 * Real.pi * (h : ℝ) / (H : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      change (∑ h ∈ Finset.Ico 1 H,
        Real.sin (2 * Real.pi * (h : ℝ) / (H : ℝ))) =
          Complex.imCLM.toAddMonoidHom (∑ h ∈ Finset.Ico 1 H,
            Complex.exp (((2 * Real.pi * (h : ℝ) / (H : ℝ) : ℝ) : ℂ) * Complex.I))
      rw [map_sum Complex.imCLM.toAddMonoidHom]
      apply Finset.sum_congr rfl
      intro h _hh
      exact (Complex.exp_ofReal_mul_I_im _).symm
    _ = Complex.im (-1) := congrArg Complex.im (complex_root_sum H hH)
    _ = 0 := by norm_num

theorem sum_Ico_reflect (H : ℕ) (f : ℕ → ℝ) :
    (∑ h ∈ Finset.Ico 1 H, f h) =
      ∑ h ∈ Finset.Ico 1 H, f (H - h) := by
  apply Finset.sum_bij' (fun h _ => H - h) (fun h _ => H - h)
  · intro h hh
    simp only [Finset.mem_Ico] at hh ⊢
    omega
  · intro h hh
    simp only [Finset.mem_Ico] at hh ⊢
    omega
  · intro h hh
    simp only [Finset.mem_Ico] at hh
    omega
  · intro h hh
    simp only [Finset.mem_Ico] at hh
    omega
  · intro h hh
    congr 1
    simp only [Finset.mem_Ico] at hh
    omega

theorem sum_linear_weights (H : ℕ) (hH : 2 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H, (1 - (h : ℝ) / (H : ℝ))) =
      ((H : ℝ) - 1) / 2 := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  have hreflect := sum_Ico_reflect H (fun h => 1 - (h : ℝ) / (H : ℝ))
  have hpair (h : ℕ) (hh : h ∈ Finset.Ico 1 H) :
      (1 - (h : ℝ) / (H : ℝ)) +
        (1 - ((H - h : ℕ) : ℝ) / (H : ℝ)) = 1 := by
    have hhm : 1 ≤ h ∧ h < H := Finset.mem_Ico.mp hh
    have hhH : h ≤ H := hhm.2.le
    rw [Nat.cast_sub hhH]
    field_simp [hH0]
    ring
  have hcard : ((Finset.Ico 1 H).card : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.card_Ico]
    rw [Nat.cast_sub (by omega : 1 ≤ H)]
    norm_num
  calc
    (∑ h ∈ Finset.Ico 1 H, (1 - (h : ℝ) / (H : ℝ))) =
        ((∑ h ∈ Finset.Ico 1 H, (1 - (h : ℝ) / (H : ℝ))) +
          ∑ h ∈ Finset.Ico 1 H, (1 - ((H - h : ℕ) : ℝ) / (H : ℝ))) / 2 := by
      rw [← hreflect]
      ring
    _ = (∑ _h ∈ Finset.Ico 1 H, (1 : ℝ)) / 2 := by
      rw [← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      exact hpair
    _ = ((H : ℝ) - 1) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hcard]

theorem sum_weighted_cos_roots (H : ℕ) (hH : 2 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      (1 - (h : ℝ) / (H : ℝ)) *
        Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ))) = -1 / 2 := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  let f : ℕ → ℝ := fun h =>
    (1 - (h : ℝ) / (H : ℝ)) *
      Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ))
  have hreflect := sum_Ico_reflect H f
  have hpair (h : ℕ) (hh : h ∈ Finset.Ico 1 H) :
      f h + f (H - h) = Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ)) := by
    have hhm : 1 ≤ h ∧ h < H := Finset.mem_Ico.mp hh
    have hhH : h ≤ H := hhm.2.le
    have hangle : 2 * Real.pi * ((H - h : ℕ) : ℝ) / (H : ℝ) =
        2 * Real.pi - 2 * Real.pi * (h : ℝ) / (H : ℝ) := by
      rw [Nat.cast_sub hhH]
      field_simp [hH0]
    dsimp [f]
    rw [hangle, Real.cos_two_pi_sub]
    rw [Nat.cast_sub hhH]
    field_simp [hH0]
    ring
  calc
    (∑ h ∈ Finset.Ico 1 H,
        (1 - (h : ℝ) / (H : ℝ)) *
          Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ))) =
        ((∑ h ∈ Finset.Ico 1 H, f h) +
          ∑ h ∈ Finset.Ico 1 H, f (H - h)) / 2 := by
      dsimp [f]
      rw [← hreflect]
      ring
    _ = (∑ h ∈ Finset.Ico 1 H,
        Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ))) / 2 := by
      rw [← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      exact hpair
    _ = -1 / 2 := by rw [sum_cos_roots H hH]

theorem sum_sin_mul_cos_half_roots (H : ℕ) (hH : 2 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      Real.sin (Real.pi * (h : ℝ) / (H : ℝ)) *
        Real.cos (Real.pi * (h : ℝ) / (H : ℝ))) = 0 := by
  calc
    (∑ h ∈ Finset.Ico 1 H,
        Real.sin (Real.pi * (h : ℝ) / (H : ℝ)) *
          Real.cos (Real.pi * (h : ℝ) / (H : ℝ))) =
        (1 / 2 : ℝ) * ∑ h ∈ Finset.Ico 1 H,
          Real.sin (2 * Real.pi * (h : ℝ) / (H : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      rw [show 2 * Real.pi * (h : ℝ) / (H : ℝ) =
        2 * (Real.pi * (h : ℝ) / (H : ℝ)) by ring,
        Real.sin_two_mul]
      ring
    _ = 0 := by rw [sum_sin_roots H hH]; ring

theorem sum_weighted_cos_sq_half_roots (H : ℕ) (hH : 2 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      (1 - (h : ℝ) / (H : ℝ)) *
        Real.cos (Real.pi * (h : ℝ) / (H : ℝ)) ^ 2) =
      ((H : ℝ) - 2) / 4 := by
  calc
    (∑ h ∈ Finset.Ico 1 H,
        (1 - (h : ℝ) / (H : ℝ)) *
          Real.cos (Real.pi * (h : ℝ) / (H : ℝ)) ^ 2) =
        (1 / 2 : ℝ) *
            (∑ h ∈ Finset.Ico 1 H, (1 - (h : ℝ) / (H : ℝ))) +
          (1 / 2 : ℝ) * ∑ h ∈ Finset.Ico 1 H,
            (1 - (h : ℝ) / (H : ℝ)) *
              Real.cos (2 * Real.pi * (h : ℝ) / (H : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h _hh
      rw [Real.cos_sq, show 2 * (Real.pi * (h : ℝ) / (H : ℝ)) =
        2 * Real.pi * (h : ℝ) / (H : ℝ) by ring]
      ring
    _ = ((H : ℝ) - 2) / 4 := by
      rw [sum_linear_weights H hH, sum_weighted_cos_roots H hH]
      ring

/-- The majorant takes the boundary value one at the positive endpoint. -/
theorem periodicVaalerMajorant_endpoint_pos (H : ℕ) (hH : 2 ≤ H) :
    periodicVaalerMajorant H ((2 * (H : ℝ))⁻¹) = 1 := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcos (h : ℕ) :
      Real.cos (2 * Real.pi * (h : ℝ) * (2 * (H : ℝ))⁻¹) =
        Real.cos (Real.pi * (h : ℝ) / (H : ℝ)) := by
    congr 1
    field_simp [hH0]
  have hsum :
      (∑ h ∈ Finset.Ico 1 H,
          vaalerCoefficient H h *
            Real.cos (Real.pi * (h : ℝ) / (H : ℝ))) =
        (H : ℝ)⁻¹ *
          ((1 / Real.pi) *
              (∑ h ∈ Finset.Ico 1 H,
                Real.sin (Real.pi * (h : ℝ) / (H : ℝ)) *
                  Real.cos (Real.pi * (h : ℝ) / (H : ℝ))) +
            2 * (∑ h ∈ Finset.Ico 1 H,
              (1 - (h : ℝ) / (H : ℝ)) *
                Real.cos (Real.pi * (h : ℝ) / (H : ℝ)) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _hh
    rw [vaalerCoefficient, coefficientShape]
    ring
  rw [periodicVaalerMajorant]
  simp_rw [hcos]
  rw [hsum, sum_sin_mul_cos_half_roots H hH,
    sum_weighted_cos_sq_half_roots H hH]
  field_simp [hH0, hpi0]
  ring

/-- The majorant is even. -/
theorem periodicVaalerMajorant_neg (H : ℕ) (x : ℝ) :
    periodicVaalerMajorant H (-x) = periodicVaalerMajorant H x := by
  rw [periodicVaalerMajorant, periodicVaalerMajorant]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro h _hh
  rw [mul_neg, Real.cos_neg]

/-- The majorant takes the boundary value one at the negative endpoint. -/
theorem periodicVaalerMajorant_endpoint_neg (H : ℕ) (hH : 2 ≤ H) :
    periodicVaalerMajorant H (-((2 * (H : ℝ))⁻¹)) = 1 := by
  rw [periodicVaalerMajorant_neg]
  exact periodicVaalerMajorant_endpoint_pos H hH

/-! ## The scalar sine inequality -/

theorem sin_sub_cubic_nonneg {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  let f : ℝ → ℝ := fun y => Real.sin y - (y - y ^ 3 / 6)
  have hf (y : ℝ) : HasDerivAt f (Real.cos y - 1 + y ^ 2 / 2) y := by
    dsimp [f]
    convert (Real.hasDerivAt_sin y).sub
      ((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).mul_const (6 : ℝ)⁻¹)) using 1
    norm_num
    ring
  have hmono : Monotone f := by
    apply monotone_of_hasDerivAt_nonneg hf
    show ∀ y : ℝ, 0 ≤ Real.cos y - 1 + y ^ 2 / 2
    intro y
    have hcos := Real.one_sub_sq_div_two_le_cos (x := y)
    linarith
  have := hmono hx
  simpa [f] using this

theorem scalar_sine_bound_low {t : ℝ}
    (ht : 0 < t) (htop : t ≤ 13 / 10) :
    1 ≤ Real.sin t ^ 2 *
      (1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
        2 / (Real.pi * t * (Real.pi - t))) := by
  let P : ℝ := 63 / 20
  let x : ℝ := 10 * t / 13
  have hpiP : Real.pi < P := by
    convert Real.pi_lt_d2 using 1 <;> norm_num [P]
  have htP : t < P := htop.trans_lt (by norm_num [P])
  have htpi : t < Real.pi := htop.trans_lt (by linarith [Real.pi_gt_three])
  have hpit : 0 < Real.pi - t := sub_pos.mpr htpi
  have hPt : 0 < P - t := sub_pos.mpr htP
  have hPpos : 0 < P := by norm_num [P]
  have hA :
      1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t)) ≤
        1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
          2 / (Real.pi * t * (Real.pi - t)) := by
    have hsquare : (Real.pi - t) ^ 2 ≤ (P - t) ^ 2 := by
      exact pow_le_pow_left₀ hpit.le (sub_le_sub_right hpiP.le t) 2
    have hprod : Real.pi * t * (Real.pi - t) ≤ P * t * (P - t) := by
      have hpi0 := Real.pi_pos.le
      have ht0 := ht.le
      have hpt0 := hpit.le
      have hPt0 := hPt.le
      calc
        Real.pi * t * (Real.pi - t) ≤ P * t * (Real.pi - t) := by gcongr
        _ ≤ P * t * (P - t) := by gcongr
    have hsqpos : 0 < (Real.pi - t) ^ 2 := sq_pos_of_pos hpit
    have hprodpos : 0 < Real.pi * t * (Real.pi - t) := by positivity
    gcongr
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    nlinarith
  have hbern :
      0 ≤ (1134 / 5 : ℝ) * (1 - x) ^ 5 +
        5 * (14004567 / 100000 : ℝ) * x * (1 - x) ^ 4 +
        10 * (403803 / 5000 : ℝ) * x ^ 2 * (1 - x) ^ 3 +
        10 * (3558014859 / 80000000 : ℝ) * x ^ 3 * (1 - x) ^ 2 +
        5 * (379652961 / 20000000 : ℝ) * x ^ 4 * (1 - x) +
        (487411 / 1600000 : ℝ) * x ^ 5 := by positivity
  have hpoly :
      0 ≤ (34400 * t ^ 5 - 108360 * t ^ 4 - 162753 * t ^ 3 +
        1300320 * t ^ 2 - 2669364 * t + 1814400) / 8000 := by
    have hid :
        (34400 * t ^ 5 - 108360 * t ^ 4 - 162753 * t ^ 3 +
          1300320 * t ^ 2 - 2669364 * t + 1814400) / 8000 =
          (1134 / 5 : ℝ) * (1 - x) ^ 5 +
          5 * (14004567 / 100000 : ℝ) * x * (1 - x) ^ 4 +
          10 * (403803 / 5000 : ℝ) * x ^ 2 * (1 - x) ^ 3 +
          10 * (3558014859 / 80000000 : ℝ) * x ^ 3 * (1 - x) ^ 2 +
          5 * (379652961 / 20000000 : ℝ) * x ^ 4 * (1 - x) +
          (487411 / 1600000 : ℝ) * x ^ 5 := by
      dsimp [x]
      ring
    rw [hid]
    exact hbern
  have hcubic : t - t ^ 3 / 6 ≤ Real.sin t :=
    sin_sub_cubic_nonneg ht.le
  have hcubic0 : 0 ≤ t - t ^ 3 / 6 := by
    have ht2 : t ^ 2 ≤ (13 / 10 : ℝ) ^ 2 :=
      pow_le_pow_left₀ ht.le htop 2
    nlinarith [sq_nonneg t]
  have hsquare : (t - t ^ 3 / 6) ^ 2 ≤ Real.sin t ^ 2 :=
    pow_le_pow_left₀ hcubic0 hcubic 2
  have hfixed :
      1 ≤ (t - t ^ 3 / 6) ^ 2 *
        (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) := by
    rw [← sub_nonneg]
    have hid :
        (t - t ^ 3 / 6) ^ 2 *
            (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) - 1 =
          t * ((34400 * t ^ 5 - 108360 * t ^ 4 - 162753 * t ^ 3 +
            1300320 * t ^ 2 - 2669364 * t + 1814400) / 8000) /
            (36 * P * (P - t) ^ 2) := by
      field_simp [ht.ne', hPt.ne', hPpos.ne']
      ring
    rw [hid]
    positivity
  calc
    1 ≤ (t - t ^ 3 / 6) ^ 2 *
        (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) := hfixed
    _ ≤ Real.sin t ^ 2 *
        (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) := by
      gcongr
    _ ≤ Real.sin t ^ 2 *
        (1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
          2 / (Real.pi * t * (Real.pi - t))) := by gcongr

theorem scalar_sine_bound_high {t : ℝ}
    (ht : 13 / 10 ≤ t) (htop : t ≤ Real.pi / 2) :
    1 ≤ Real.sin t ^ 2 *
      (1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
        2 / (Real.pi * t * (Real.pi - t))) := by
  let P : ℝ := 63 / 20
  let x : ℝ := (40 / 11) * (t - 13 / 10)
  have hpiP : Real.pi < P := by
    convert Real.pi_lt_d2 using 1 <;> norm_num [P]
  have ht0 : 0 < t := by linarith
  have htP : t < P := by linarith [hpiP, Real.pi_pos]
  have hpit : 0 < Real.pi - t := sub_pos.mpr (htop.trans_lt (by linarith [Real.pi_pos]))
  have hPt : 0 < P - t := sub_pos.mpr htP
  have hPpos : 0 < P := by norm_num [P]
  have hA :
      1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t)) ≤
        1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
          2 / (Real.pi * t * (Real.pi - t)) := by
    have hsquare : (Real.pi - t) ^ 2 ≤ (P - t) ^ 2 := by
      exact pow_le_pow_left₀ hpit.le (sub_le_sub_right hpiP.le t) 2
    have hprod : Real.pi * t * (Real.pi - t) ≤ P * t * (P - t) := by
      calc
        Real.pi * t * (Real.pi - t) ≤ P * t * (Real.pi - t) := by gcongr
        _ ≤ P * t * (P - t) := by gcongr
    have hsqpos : 0 < (Real.pi - t) ^ 2 := sq_pos_of_pos hpit
    have hprodpos : 0 < Real.pi * t * (Real.pi - t) := by positivity
    gcongr
  have htPtwo : t ≤ P / 2 :=
    htop.trans ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hpiP.le)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x, P] at htPtwo ⊢
    nlinarith
  have hdelta0 : 0 ≤ Real.pi / 2 - t := sub_nonneg.mpr htop
  have hdeltaP : Real.pi / 2 - t ≤ P / 2 - t :=
    sub_le_sub_right
      ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hpiP.le) t
  have hcoslower :
      1 - (P / 2 - t) ^ 2 / 2 ≤ Real.sin t := by
    rw [← Real.cos_pi_div_two_sub]
    have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 - t)
    have hsquares : (Real.pi / 2 - t) ^ 2 ≤ (P / 2 - t) ^ 2 :=
      pow_le_pow_left₀ hdelta0 hdeltaP 2
    linarith
  have hlower0 : 0 ≤ 1 - (P / 2 - t) ^ 2 / 2 := by
    dsimp [P]
    have hbound : P / 2 - t ≤ 11 / 40 := by dsimp [P]; linarith
    nlinarith [sq_nonneg (P / 2 - t)]
  have hsquare : (1 - (P / 2 - t) ^ 2 / 2) ^ 2 ≤ Real.sin t ^ 2 :=
    pow_le_pow_left₀ hlower0 hcoslower 2
  have hbern :
      0 ≤ (18726087943 / 16384000000 : ℝ) * (1 - x) ^ 6 +
        6 * (574062635107 / 491520000000 : ℝ) * x * (1 - x) ^ 5 +
        15 * (2911716535907 / 2457600000000 : ℝ) * x ^ 2 * (1 - x) ^ 4 +
        20 * (12243557 / 10240000 : ℝ) * x ^ 3 * (1 - x) ^ 3 +
        15 * (184677499 / 153600000 : ℝ) * x ^ 4 * (1 - x) ^ 2 +
        6 * (61729857 / 51200000 : ℝ) * x ^ 5 * (1 - x) +
        (61729857 / 51200000 : ℝ) * x ^ 6 := by positivity
  have hpoly :
      0 ≤ (76177123 * x ^ 6 - 457062738 * x ^ 5 - 1015031248 * x ^ 4 +
        7107209912 * x ^ 3 - 19996623713 * x ^ 2 +
        24559993634 * x + 187260879430) / 163840000000 := by
    have hid :
        (76177123 * x ^ 6 - 457062738 * x ^ 5 - 1015031248 * x ^ 4 +
          7107209912 * x ^ 3 - 19996623713 * x ^ 2 +
          24559993634 * x + 187260879430) / 163840000000 =
          (18726087943 / 16384000000 : ℝ) * (1 - x) ^ 6 +
          6 * (574062635107 / 491520000000 : ℝ) * x * (1 - x) ^ 5 +
          15 * (2911716535907 / 2457600000000 : ℝ) * x ^ 2 * (1 - x) ^ 4 +
          20 * (12243557 / 10240000 : ℝ) * x ^ 3 * (1 - x) ^ 3 +
          15 * (184677499 / 153600000 : ℝ) * x ^ 4 * (1 - x) ^ 2 +
          6 * (61729857 / 51200000 : ℝ) * x ^ 5 * (1 - x) +
          (61729857 / 51200000 : ℝ) * x ^ 6 := by ring
    rw [hid]
    exact hbern
  have hfixed :
      1 ≤ (1 - (P / 2 - t) ^ 2 / 2) ^ 2 *
        (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) := by
    rw [← sub_nonneg]
    have hid :
        (1 - (P / 2 - t) ^ 2 / 2) ^ 2 *
            (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) - 1 =
          ((76177123 * x ^ 6 - 457062738 * x ^ 5 - 1015031248 * x ^ 4 +
            7107209912 * x ^ 3 - 19996623713 * x ^ 2 +
            24559993634 * x + 187260879430) / 163840000000) /
            (P * t ^ 2 * (P - t) ^ 2) := by
      field_simp [ht0.ne', hPt.ne', hPpos.ne']
      dsimp [P, x]
      ring
    rw [hid]
    positivity
  calc
    1 ≤ (1 - (P / 2 - t) ^ 2 / 2) ^ 2 *
        (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) := hfixed
    _ ≤ Real.sin t ^ 2 *
        (1 / t ^ 2 + 1 / (P - t) ^ 2 + 2 / (P * t * (P - t))) := by
      gcongr
    _ ≤ Real.sin t ^ 2 *
        (1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
          2 / (Real.pi * t * (Real.pi - t))) := by gcongr

theorem scalar_sine_bound_half {t : ℝ}
    (ht : 0 < t) (htop : t ≤ Real.pi / 2) :
    1 ≤ Real.sin t ^ 2 *
      (1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
        2 / (Real.pi * t * (Real.pi - t))) := by
  by_cases hsplit : t ≤ 13 / 10
  · exact scalar_sine_bound_low ht hsplit
  · exact scalar_sine_bound_high (le_of_not_ge hsplit) htop

/-- The sharp scalar inequality needed in the central Vaaler estimate. -/
theorem scalar_sine_bound (t : ℝ) (ht : 0 < t) (htop : t < Real.pi) :
    1 ≤ Real.sin t ^ 2 *
      (1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
        2 / (Real.pi * t * (Real.pi - t))) := by
  by_cases hhalf : t ≤ Real.pi / 2
  · exact scalar_sine_bound_half ht hhalf
  · let s := Real.pi - t
    have hs0 : 0 < s := sub_pos.mpr htop
    have hshalf : s ≤ Real.pi / 2 := by dsimp [s]; linarith
    have hs := scalar_sine_bound_half hs0 hshalf
    dsimp [s] at hs
    rw [Real.sin_pi_sub, sub_sub_cancel] at hs
    convert hs using 1 <;> ring

/-! ## Exact finite trigonometric reduction -/

theorem sum_secondDifference (f : ℕ → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      (2 * f h - f (h - 1) - f (h + 1))) =
        f 1 - f 0 + f (H - 1) - f H := by
  induction H, hH using Nat.le_induction with
  | base => simp
  | succ H hH ih =>
      rw [Finset.sum_Ico_succ_top hH]
      rw [ih]
      have hsub : H + 1 - 1 = H := by omega
      rw [hsub]
      ring

theorem sum_weighted_secondDifference (f : ℕ → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H,
      ((H - h : ℕ) : ℝ) * (2 * f h - f (h - 1) - f (h + 1))) =
        (H : ℝ) * f 1 - ((H : ℝ) - 1) * f 0 - f H := by
  induction H, hH using Nat.le_induction with
  | base => simp
  | succ H hH ih =>
      rw [Finset.sum_Ico_succ_top hH]
      have hweight (h : ℕ) (hh : h ∈ Finset.Ico 1 H) :
          (((H + 1 - h : ℕ) : ℝ) : ℝ) = (H - h : ℕ) + 1 := by
        have hhH : h ≤ H := (Finset.mem_Ico.mp hh).2.le
        exact_mod_cast (show H + 1 - h = (H - h) + 1 by omega)
      have hlast : (((H + 1 - H : ℕ) : ℝ) : ℝ) = 1 := by
        norm_num
      have hreplace :
          (∑ h ∈ Finset.Ico 1 H,
              (((H + 1 - h : ℕ) : ℝ) : ℝ) *
                (2 * f h - f (h - 1) - f (h + 1))) =
            ∑ h ∈ Finset.Ico 1 H,
              (((H - h : ℕ) : ℝ) + 1) *
                (2 * f h - f (h - 1) - f (h + 1)) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [hweight h hh]
      rw [hreplace]
      rw [hlast, one_mul]
      have hdist :
          (∑ h ∈ Finset.Ico 1 H,
              (((H - h : ℕ) : ℝ) + 1) *
                (2 * f h - f (h - 1) - f (h + 1))) =
            (∑ h ∈ Finset.Ico 1 H,
              ((H - h : ℕ) : ℝ) * (2 * f h - f (h - 1) - f (h + 1))) +
            ∑ h ∈ Finset.Ico 1 H, (2 * f h - f (h - 1) - f (h + 1)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro h _hh
        ring
      rw [hdist, ih, sum_secondDifference f H hH]
      push_cast
      ring

theorem cosine_secondDifference (z : ℝ) (h : ℕ) (hh : 1 ≤ h) :
    2 * Real.cos ((h : ℝ) * z) - Real.cos (((h - 1 : ℕ) : ℝ) * z) -
        Real.cos (((h + 1 : ℕ) : ℝ) * z) =
      2 * (1 - Real.cos z) * Real.cos ((h : ℝ) * z) := by
  rw [Nat.cast_sub hh]
  push_cast
  rw [show ((h : ℝ) - 1) * z = (h : ℝ) * z - z by ring,
    show ((h : ℝ) + 1) * z = (h : ℝ) * z + z by ring,
    Real.cos_sub, Real.cos_add]
  ring

/-- Exact Fejer cosine identity, in a denominator-free form. -/
theorem fejerCosineSum_mul_one_sub_cos (H : ℕ) (hH : 1 ≤ H) (z : ℝ) :
    (1 - Real.cos z) *
        ((H : ℝ) + 2 * ∑ h ∈ Finset.Ico 1 H,
          ((H - h : ℕ) : ℝ) * Real.cos ((h : ℝ) * z)) =
      1 - Real.cos ((H : ℝ) * z) := by
  let f : ℕ → ℝ := fun h => Real.cos ((h : ℝ) * z)
  have hsecond := sum_weighted_secondDifference f H hH
  have hpoint (h : ℕ) (hh : h ∈ Finset.Ico 1 H) :
      2 * f h - f (h - 1) - f (h + 1) =
        2 * (1 - Real.cos z) * f h := by
    exact cosine_secondDifference z h (Finset.mem_Ico.mp hh).1
  have hreplace :
      (∑ h ∈ Finset.Ico 1 H,
          ((H - h : ℕ) : ℝ) * (2 * f h - f (h - 1) - f (h + 1))) =
        ∑ h ∈ Finset.Ico 1 H,
          ((H - h : ℕ) : ℝ) * (2 * (1 - Real.cos z) * f h) := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [hpoint h hh]
  rw [hreplace] at hsecond
  have hfactor :
      (∑ h ∈ Finset.Ico 1 H,
          ((H - h : ℕ) : ℝ) * (2 * (1 - Real.cos z) * f h)) =
        2 * (1 - Real.cos z) *
          ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) * f h := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _hh
    ring
  rw [hfactor] at hsecond
  dsimp [f] at hsecond ⊢
  norm_num at hsecond ⊢
  nlinarith

theorem sum_firstDifference (f : ℕ → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (∑ h ∈ Finset.Ico 1 H, (f (h - 1) - f h)) = f 0 - f (H - 1) := by
  induction H, hH using Nat.le_induction with
  | base => simp
  | succ H hH ih =>
      rw [Finset.sum_Ico_succ_top hH, ih]
      have hsub : H + 1 - 1 = H := by omega
      rw [hsub]
      ring

theorem sine_sum_mul_two_sin_half (H : ℕ) (z : ℝ) :
    2 * Real.sin (z / 2) *
        (∑ h ∈ Finset.Ico 1 H, Real.sin ((h : ℝ) * z)) =
      Real.cos (z / 2) - Real.cos (((H : ℝ) - 1 / 2) * z) := by
  by_cases hH : H = 0
  · subst H
    have hempty : Finset.Ico 1 0 = ∅ := by simp
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero, Nat.cast_zero, zero_sub]
    rw [show -(1 / 2 : ℝ) * z = -(z / 2) by ring, Real.cos_neg]
    ring
  have hH1 : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr hH
  let f : ℕ → ℝ := fun h => Real.cos (((h : ℝ) + 1 / 2) * z)
  have htel := sum_firstDifference f H hH1
  have hpoint (h : ℕ) (hh : h ∈ Finset.Ico 1 H) :
      f (h - 1) - f h = 2 * Real.sin (z / 2) * Real.sin ((h : ℝ) * z) := by
    have hh1 := (Finset.mem_Ico.mp hh).1
    dsimp [f]
    rw [Nat.cast_sub hh1]
    rw [Real.cos_sub_cos]
    norm_num
    have hsum :
        ((((h : ℝ) - 1) + 1 / 2) * z + ((h : ℝ) + 1 / 2) * z) / 2 =
          (h : ℝ) * z := by ring
    have hdiff :
        ((((h : ℝ) - 1) + 1 / 2) * z - ((h : ℝ) + 1 / 2) * z) / 2 =
          -(z / 2) := by ring
    rw [hsum, hdiff, Real.sin_neg]
    ring
  have hreplace :
      (∑ h ∈ Finset.Ico 1 H, (f (h - 1) - f h)) =
        ∑ h ∈ Finset.Ico 1 H,
          2 * Real.sin (z / 2) * Real.sin ((h : ℝ) * z) := by
    apply Finset.sum_congr rfl
    exact hpoint
  rw [hreplace] at htel
  rw [← Finset.mul_sum] at htel
  dsimp [f] at htel ⊢
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 / 2 = (H : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub hH1]
    ring
  rw [hcast] at htel
  convert htel using 1 <;> ring

def unnormalizedFejerCosineSum (H : ℕ) (z : ℝ) : ℝ :=
  (H : ℝ) + 2 * ∑ h ∈ Finset.Ico 1 H,
    ((H - h : ℕ) : ℝ) * Real.cos ((h : ℝ) * z)

theorem periodicVaalerMajorant_decomposition
    (H : ℕ) (hH : 1 ≤ H) (x : ℝ) :
    periodicVaalerMajorant H x =
      (H : ℝ)⁻¹ ^ 2 *
        (unnormalizedFejerCosineSum H
            (Real.pi / (H : ℝ) - 2 * Real.pi * x) +
          unnormalizedFejerCosineSum H
            (Real.pi / (H : ℝ) + 2 * Real.pi * x)) +
      1 / (Real.pi * (H : ℝ)) *
        ((∑ h ∈ Finset.Ico 1 H,
            Real.sin ((h : ℝ) *
              (Real.pi / (H : ℝ) - 2 * Real.pi * x))) +
          ∑ h ∈ Finset.Ico 1 H,
            Real.sin ((h : ℝ) *
              (Real.pi / (H : ℝ) + 2 * Real.pi * x))) := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  rw [periodicVaalerMajorant]
  unfold unnormalizedFejerCosineSum
  have hsum :
      2 * ∑ h ∈ Finset.Ico 1 H,
          vaalerCoefficient H h * Real.cos (2 * Real.pi * (h : ℝ) * x) =
        (H : ℝ)⁻¹ ^ 2 *
          ((2 * ∑ h ∈ Finset.Ico 1 H,
              ((H - h : ℕ) : ℝ) *
                Real.cos ((h : ℝ) *
                  (Real.pi / (H : ℝ) - 2 * Real.pi * x))) +
            2 * ∑ h ∈ Finset.Ico 1 H,
              ((H - h : ℕ) : ℝ) *
                Real.cos ((h : ℝ) *
                  (Real.pi / (H : ℝ) + 2 * Real.pi * x))) +
          1 / (Real.pi * (H : ℝ)) *
            ((∑ h ∈ Finset.Ico 1 H,
                Real.sin ((h : ℝ) *
                  (Real.pi / (H : ℝ) - 2 * Real.pi * x))) +
              ∑ h ∈ Finset.Ico 1 H,
                Real.sin ((h : ℝ) *
                  (Real.pi / (H : ℝ) + 2 * Real.pi * x))) := by
    calc
      2 * ∑ h ∈ Finset.Ico 1 H,
          vaalerCoefficient H h * Real.cos (2 * Real.pi * (h : ℝ) * x) =
          ∑ h ∈ Finset.Ico 1 H,
            2 * (vaalerCoefficient H h * Real.cos (2 * Real.pi * (h : ℝ) * x)) := by
        rw [Finset.mul_sum]
      _ = ∑ h ∈ Finset.Ico 1 H,
          ((H : ℝ)⁻¹ ^ 2 *
              (2 * ((H - h : ℕ) : ℝ) *
                (Real.cos ((h : ℝ) *
                    (Real.pi / (H : ℝ) - 2 * Real.pi * x)) +
                  Real.cos ((h : ℝ) *
                    (Real.pi / (H : ℝ) + 2 * Real.pi * x)))) +
            1 / (Real.pi * (H : ℝ)) *
              (Real.sin ((h : ℝ) *
                  (Real.pi / (H : ℝ) - 2 * Real.pi * x)) +
                Real.sin ((h : ℝ) *
                  (Real.pi / (H : ℝ) + 2 * Real.pi * x)))) := by
        apply Finset.sum_congr rfl
        intro h hh
        have hhH : h ≤ H := (Finset.mem_Ico.mp hh).2.le
        rw [vaalerCoefficient, coefficientShape, Nat.cast_sub hhH]
        rw [show (h : ℝ) * (Real.pi / (H : ℝ) - 2 * Real.pi * x) =
            Real.pi * (h : ℝ) / (H : ℝ) - 2 * Real.pi * (h : ℝ) * x by ring,
          show (h : ℝ) * (Real.pi / (H : ℝ) + 2 * Real.pi * x) =
            Real.pi * (h : ℝ) / (H : ℝ) + 2 * Real.pi * (h : ℝ) * x by ring]
        rw [← Real.two_mul_cos_mul_cos, ← Real.two_mul_sin_mul_cos]
        field_simp [hH0, Real.pi_ne_zero]
        ring
      _ = _ := by
        have hFm :
            (∑ h ∈ Finset.Ico 1 H,
              (H : ℝ)⁻¹ ^ 2 *
                (2 * (((H - h : ℕ) : ℝ) *
                  Real.cos ((h : ℝ) *
                    (Real.pi / (H : ℝ) - 2 * Real.pi * x))))) =
              (H : ℝ)⁻¹ ^ 2 *
                (2 * ∑ h ∈ Finset.Ico 1 H,
                  ((H - h : ℕ) : ℝ) *
                    Real.cos ((h : ℝ) *
                      (Real.pi / (H : ℝ) - 2 * Real.pi * x))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
        have hFp :
            (∑ h ∈ Finset.Ico 1 H,
              (H : ℝ)⁻¹ ^ 2 *
                (2 * (((H - h : ℕ) : ℝ) *
                  Real.cos ((h : ℝ) *
                    (Real.pi / (H : ℝ) + 2 * Real.pi * x))))) =
              (H : ℝ)⁻¹ ^ 2 *
                (2 * ∑ h ∈ Finset.Ico 1 H,
                  ((H - h : ℕ) : ℝ) *
                    Real.cos ((h : ℝ) *
                      (Real.pi / (H : ℝ) + 2 * Real.pi * x))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
        have hSm :
            (∑ h ∈ Finset.Ico 1 H,
              1 / (Real.pi * (H : ℝ)) *
                Real.sin ((h : ℝ) *
                  (Real.pi / (H : ℝ) - 2 * Real.pi * x))) =
              1 / (Real.pi * (H : ℝ)) *
                ∑ h ∈ Finset.Ico 1 H,
                  Real.sin ((h : ℝ) *
                    (Real.pi / (H : ℝ) - 2 * Real.pi * x)) := by
          rw [Finset.mul_sum]
        have hSp :
            (∑ h ∈ Finset.Ico 1 H,
              1 / (Real.pi * (H : ℝ)) *
                Real.sin ((h : ℝ) *
                  (Real.pi / (H : ℝ) + 2 * Real.pi * x))) =
              1 / (Real.pi * (H : ℝ)) *
                ∑ h ∈ Finset.Ico 1 H,
                  Real.sin ((h : ℝ) *
                    (Real.pi / (H : ℝ) + 2 * Real.pi * x)) := by
          rw [Finset.mul_sum]
        rw [Finset.sum_add_distrib]
        have hfej :
            (∑ h ∈ Finset.Ico 1 H,
              (H : ℝ)⁻¹ ^ 2 *
                (2 * ((H - h : ℕ) : ℝ) *
                  (Real.cos ((h : ℝ) *
                      (Real.pi / (H : ℝ) - 2 * Real.pi * x)) +
                    Real.cos ((h : ℝ) *
                      (Real.pi / (H : ℝ) + 2 * Real.pi * x))))) =
              (∑ h ∈ Finset.Ico 1 H,
                (H : ℝ)⁻¹ ^ 2 *
                  (2 * (((H - h : ℕ) : ℝ) *
                    Real.cos ((h : ℝ) *
                      (Real.pi / (H : ℝ) - 2 * Real.pi * x))))) +
              ∑ h ∈ Finset.Ico 1 H,
                (H : ℝ)⁻¹ ^ 2 *
                  (2 * (((H - h : ℕ) : ℝ) *
                    Real.cos ((h : ℝ) *
                      (Real.pi / (H : ℝ) + 2 * Real.pi * x)))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro h _hh
          ring
        have hsin :
            (∑ h ∈ Finset.Ico 1 H,
              1 / (Real.pi * (H : ℝ)) *
                (Real.sin ((h : ℝ) *
                    (Real.pi / (H : ℝ) - 2 * Real.pi * x)) +
                  Real.sin ((h : ℝ) *
                    (Real.pi / (H : ℝ) + 2 * Real.pi * x)))) =
              (∑ h ∈ Finset.Ico 1 H,
                1 / (Real.pi * (H : ℝ)) *
                  Real.sin ((h : ℝ) *
                    (Real.pi / (H : ℝ) - 2 * Real.pi * x))) +
              ∑ h ∈ Finset.Ico 1 H,
                1 / (Real.pi * (H : ℝ)) *
                  Real.sin ((h : ℝ) *
                    (Real.pi / (H : ℝ) + 2 * Real.pi * x)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro h _hh
          ring
        rw [hfej, hsin, hFm, hFp, hSm, hSp]
        ring
  rw [hsum]
  have hconst : (H : ℝ) * (H : ℝ)⁻¹ ^ 2 = (H : ℝ)⁻¹ := by
    field_simp [hH0]
  have hzero : 2 / (H : ℝ) = (H : ℝ)⁻¹ ^ 2 * ((H : ℝ) + (H : ℝ)) := by
    field_simp [hH0]
    norm_num
  rw [hzero]
  ring

theorem unnormalizedFejerCosineSum_closed
    (H : ℕ) (hH : 1 ≤ H) {z : ℝ} (hz : 1 - Real.cos z ≠ 0) :
    unnormalizedFejerCosineSum H z =
      (1 - Real.cos ((H : ℝ) * z)) / (1 - Real.cos z) := by
  rw [eq_div_iff hz]
  rw [mul_comm]
  exact fejerCosineSum_mul_one_sub_cos H hH z

theorem one_sub_cos_two_ne_zero {u : ℝ} (hu : Real.sin u ≠ 0) :
    1 - Real.cos (2 * u) ≠ 0 := by
  intro h
  have htrig := Real.sin_sq_add_cos_sq u
  rw [Real.cos_two_mul] at h
  nlinarith [sq_pos_of_ne_zero hu]

theorem shiftedFejerCosineSum_closed
    (H : ℕ) (hH : 1 ≤ H) (theta : ℝ)
    (hs : Real.sin ((Real.pi / (H : ℝ) + theta) / 2) ≠ 0) :
    unnormalizedFejerCosineSum H (Real.pi / (H : ℝ) + theta) =
      Real.cos ((H : ℝ) * theta / 2) ^ 2 /
        Real.sin ((Real.pi / (H : ℝ) + theta) / 2) ^ 2 := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  let u := (Real.pi / (H : ℝ) + theta) / 2
  have hz : Real.pi / (H : ℝ) + theta = 2 * u := by dsimp [u]; ring
  have hden : 1 - Real.cos (Real.pi / (H : ℝ) + theta) ≠ 0 := by
    rw [hz]
    exact one_sub_cos_two_ne_zero hs
  rw [unnormalizedFejerCosineSum_closed H hH hden]
  have hangle : (H : ℝ) * (Real.pi / (H : ℝ) + theta) =
      Real.pi + (H : ℝ) * theta := by field_simp [hH0]
  rw [hangle, Real.cos_add, Real.cos_pi, Real.sin_pi]
  norm_num
  rw [show (H : ℝ) * theta = 2 * ((H : ℝ) * theta / 2) by ring,
    Real.cos_two_mul]
  rw [hz, Real.cos_two_mul]
  have htrig := Real.sin_sq_add_cos_sq u
  have halg :
      (1 + (2 * Real.cos ((H : ℝ) * theta / 2) ^ 2 - 1)) /
          (1 - (2 * Real.cos u ^ 2 - 1)) =
        Real.cos ((H : ℝ) * theta / 2) ^ 2 / Real.sin u ^ 2 := by
    have hdeneq : 1 - (2 * Real.cos u ^ 2 - 1) = 2 * Real.sin u ^ 2 := by
      nlinarith
    rw [hdeneq]
    field_simp [hs]
    ring
  simpa [u] using halg

theorem shiftedSineSum_closed
    (H : ℕ) (hH : 1 ≤ H) (theta : ℝ)
    (hs : Real.sin ((Real.pi / (H : ℝ) + theta) / 2) ≠ 0) :
    (∑ h ∈ Finset.Ico 1 H,
      Real.sin ((h : ℝ) * (Real.pi / (H : ℝ) + theta))) =
      Real.cos ((H : ℝ) * theta / 2) *
        Real.cos ((Real.pi / (H : ℝ) + theta) / 2 -
          (H : ℝ) * theta / 2) /
        Real.sin ((Real.pi / (H : ℝ) + theta) / 2) := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  let u := (Real.pi / (H : ℝ) + theta) / 2
  let T := (H : ℝ) * theta / 2
  have hz : Real.pi / (H : ℝ) + theta = 2 * u := by dsimp [u]; ring
  have hangle : ((H : ℝ) - 1 / 2) *
      (Real.pi / (H : ℝ) + theta) = Real.pi + 2 * T - u := by
    dsimp [u, T]
    field_simp [hH0]
  have hcos : Real.cos u - Real.cos (Real.pi + 2 * T - u) =
      2 * Real.cos T * Real.cos (u - T) := by
    rw [show Real.pi + 2 * T - u = Real.pi + (2 * T - u) by ring,
      Real.cos_add, Real.cos_pi, Real.sin_pi]
    norm_num
    have hc1 : Real.cos u =
        Real.cos T * Real.cos (u - T) - Real.sin T * Real.sin (u - T) := by
      rw [show u = T + (u - T) by ring, Real.cos_add]
      ring
    have hc2 : Real.cos (2 * T - u) =
        Real.cos T * Real.cos (u - T) + Real.sin T * Real.sin (u - T) := by
      rw [show 2 * T - u = T - (u - T) by ring, Real.cos_sub]
    rw [hc1, hc2]
    ring
  have hsum := sine_sum_mul_two_sin_half H
    (Real.pi / (H : ℝ) + theta)
  rw [hangle] at hsum
  rw [hz] at hsum
  norm_num at hsum
  rw [hcos] at hsum
  have hsums :
      (∑ h ∈ Finset.Ico 1 H, Real.sin ((h : ℝ) * (2 * u))) =
        ∑ h ∈ Finset.Ico 1 H,
          Real.sin ((h : ℝ) * (Real.pi / (H : ℝ) + theta)) := by
    rw [← hz]
  rw [hsums] at hsum
  dsimp [u, T] at hsum ⊢
  apply (eq_div_iff hs).2
  nlinarith

theorem pairedSineSum_closed
    (H : ℕ) (hH : 1 ≤ H) (theta : ℝ)
    (hsp : Real.sin ((Real.pi / (H : ℝ) + theta) / 2) ≠ 0)
    (hsm : Real.sin ((Real.pi / (H : ℝ) - theta) / 2) ≠ 0) :
    ((∑ h ∈ Finset.Ico 1 H,
        Real.sin ((h : ℝ) * (Real.pi / (H : ℝ) - theta))) +
      ∑ h ∈ Finset.Ico 1 H,
        Real.sin ((h : ℝ) * (Real.pi / (H : ℝ) + theta))) =
      Real.cos ((H : ℝ) * theta / 2) ^ 2 *
        Real.sin (Real.pi / (H : ℝ)) /
          (Real.sin ((Real.pi / (H : ℝ) + theta) / 2) *
            Real.sin ((Real.pi / (H : ℝ) - theta) / 2)) := by
  have hm := shiftedSineSum_closed H hH (-theta)
    (by simpa only [sub_eq_add_neg] using hsm)
  have hp := shiftedSineSum_closed H hH theta hsp
  have hout : (H : ℝ) * (-theta) / 2 = -((H : ℝ) * theta / 2) := by ring
  rw [hout, Real.cos_neg] at hm
  have hmclean :
      (∑ h ∈ Finset.Ico 1 H,
        Real.sin ((h : ℝ) * (Real.pi / (H : ℝ) - theta))) =
        Real.cos ((H : ℝ) * theta / 2) *
          Real.cos ((Real.pi / (H : ℝ) - theta) / 2 +
            (H : ℝ) * theta / 2) /
          Real.sin ((Real.pi / (H : ℝ) - theta) / 2) := by
    convert hm using 1 <;> ring
  rw [hmclean, hp]
  have hidentity :
      Real.cos (((Real.pi / (H : ℝ) + theta) / 2) -
          (H : ℝ) * theta / 2) *
          Real.sin ((Real.pi / (H : ℝ) - theta) / 2) +
        Real.cos (((Real.pi / (H : ℝ) - theta) / 2) +
          (H : ℝ) * theta / 2) *
          Real.sin ((Real.pi / (H : ℝ) + theta) / 2) =
        Real.cos ((H : ℝ) * theta / 2) *
          Real.sin (Real.pi / (H : ℝ)) := by
    rw [Real.cos_sub, Real.cos_add,
      show Real.pi / (H : ℝ) =
        (Real.pi / (H : ℝ) + theta) / 2 +
          (Real.pi / (H : ℝ) - theta) / 2 by ring,
      Real.sin_add]
    ring
  let C := Real.cos ((H : ℝ) * theta / 2)
  let A := Real.cos ((Real.pi / (H : ℝ) + theta) / 2 -
    (H : ℝ) * theta / 2)
  let B := Real.cos ((Real.pi / (H : ℝ) - theta) / 2 +
    (H : ℝ) * theta / 2)
  let sp := Real.sin ((Real.pi / (H : ℝ) + theta) / 2)
  let sm := Real.sin ((Real.pi / (H : ℝ) - theta) / 2)
  have hfrac : C * B / sm + C * A / sp =
      C * (A * sm + B * sp) / (sp * sm) := by
    field_simp [sp, sm, hsp, hsm]
    ring
  change C * B / sm + C * A / sp =
    C ^ 2 * Real.sin (Real.pi / (H : ℝ)) / (sp * sm)
  rw [hfrac]
  have hid : A * sm + B * sp = C * Real.sin (Real.pi / (H : ℝ)) := by
    exact hidentity
  rw [hid]
  ring

theorem periodicVaalerMajorant_closed
    (H : ℕ) (hH : 1 ≤ H) (x : ℝ)
    (hsp : Real.sin ((Real.pi / (H : ℝ) + 2 * Real.pi * x) / 2) ≠ 0)
    (hsm : Real.sin ((Real.pi / (H : ℝ) - 2 * Real.pi * x) / 2) ≠ 0) :
    periodicVaalerMajorant H x =
      Real.cos ((H : ℝ) * (2 * Real.pi * x) / 2) ^ 2 /
        (H : ℝ) ^ 2 *
        (1 / Real.sin ((Real.pi / (H : ℝ) + 2 * Real.pi * x) / 2) ^ 2 +
          1 / Real.sin ((Real.pi / (H : ℝ) - 2 * Real.pi * x) / 2) ^ 2 +
          (H : ℝ) * Real.sin (Real.pi / (H : ℝ)) /
            (Real.pi *
              Real.sin ((Real.pi / (H : ℝ) + 2 * Real.pi * x) / 2) *
              Real.sin ((Real.pi / (H : ℝ) - 2 * Real.pi * x) / 2))) := by
  have hplus := shiftedFejerCosineSum_closed H hH (2 * Real.pi * x) hsp
  have hminus := shiftedFejerCosineSum_closed H hH (-(2 * Real.pi * x))
    (by simpa only [sub_eq_add_neg] using hsm)
  have hminusClean :
      unnormalizedFejerCosineSum H
          (Real.pi / (H : ℝ) - 2 * Real.pi * x) =
        Real.cos ((H : ℝ) * (2 * Real.pi * x) / 2) ^ 2 /
          Real.sin ((Real.pi / (H : ℝ) - 2 * Real.pi * x) / 2) ^ 2 := by
    rw [show Real.pi / (H : ℝ) - 2 * Real.pi * x =
      Real.pi / (H : ℝ) + -(2 * Real.pi * x) by ring]
    convert hminus using 1
    · rw [show (H : ℝ) * -(2 * Real.pi * x) / 2 =
        -((H : ℝ) * (2 * Real.pi * x) / 2) by ring, Real.cos_neg]
  have hsine := pairedSineSum_closed H hH (2 * Real.pi * x) hsp hsm
  rw [periodicVaalerMajorant_decomposition H hH x,
    hminusClean, hplus, hsine]
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  field_simp [hH0, Real.pi_ne_zero, hsp, hsm]
  ring

theorem periodicVaalerMajorant_ge_one_of_abs_lt
    (H : ℕ) (hH : 2 ≤ H) {x : ℝ}
    (hx : |x| < (2 * (H : ℝ))⁻¹) :
    1 ≤ periodicVaalerMajorant H x := by
  have hHpos : 0 < (H : ℝ) := by positivity
  have hH0 : (H : ℝ) ≠ 0 := hHpos.ne'
  let a := Real.pi / (H : ℝ)
  let theta := 2 * Real.pi * x
  let u := (a + theta) / 2
  let v := (a - theta) / 2
  let t := (H : ℝ) * u
  have hx' := abs_lt.mp hx
  have hthetaUpper : theta < a := by
    dsimp [theta, a]
    calc
      2 * Real.pi * x < 2 * Real.pi * (2 * (H : ℝ))⁻¹ := by
        exact mul_lt_mul_of_pos_left hx'.2 (by positivity)
      _ = Real.pi / (H : ℝ) := by field_simp [hH0]
  have hthetaLower : -a < theta := by
    dsimp [theta, a]
    calc
      -(Real.pi / (H : ℝ)) = 2 * Real.pi * (-(2 * (H : ℝ))⁻¹) := by
          field_simp [hH0]
      _ < 2 * Real.pi * x :=
        mul_lt_mul_of_pos_left hx'.1 (by positivity)
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hv0 : 0 < v := by dsimp [v]; linarith
  have huv : u + v = a := by dsimp [u, v]; ring
  have ha0 : 0 < a := div_pos Real.pi_pos hHpos
  have hua : u < a := by linarith
  have hva : v < a := by linarith
  have haHalf : a ≤ Real.pi / 2 := by
    dsimp [a]
    rw [div_le_iff₀ hHpos]
    have hcast : (2 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith [Real.pi_pos]
  have hupi : u < Real.pi := by linarith [Real.pi_pos]
  have hvpi : v < Real.pi := by linarith [Real.pi_pos]
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hsv : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 hvpi
  have hsp : Real.sin ((Real.pi / (H : ℝ) + theta) / 2) ≠ 0 := by
    simpa [u, a] using hsu.ne'
  have hsm : Real.sin ((Real.pi / (H : ℝ) - theta) / 2) ≠ 0 := by
    simpa [v, a] using hsv.ne'
  have ht0 : 0 < t := mul_pos hHpos hu0
  have htpi : t < Real.pi := by
    dsimp [t]
    have := mul_lt_mul_of_pos_left hua hHpos
    dsimp [a] at this
    field_simp [hH0] at this
    exact this
  have hpit : Real.pi - t = (H : ℝ) * v := by
    dsimp [t, u, v, a, theta]
    field_simp [hH0]
    ring
  have hcost : Real.cos ((H : ℝ) * theta / 2) = Real.sin t := by
    have ht : t = Real.pi / 2 + (H : ℝ) * theta / 2 := by
      dsimp [t, u, a]
      field_simp [hH0]
    rw [ht, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  have hsu_le : Real.sin u ≤ u := Real.sin_le hu0.le
  have hsv_le : Real.sin v ≤ v := Real.sin_le hv0.le
  have htermU : 1 / t ^ 2 ≤ 1 / ((H : ℝ) ^ 2 * Real.sin u ^ 2) := by
    have hmul : (H : ℝ) * Real.sin u ≤ t := by
      dsimp [t]
      gcongr
    have hsquare : ((H : ℝ) * Real.sin u) ^ 2 ≤ t ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hHpos.le hsu.le) hmul 2
    change ((H : ℝ) * Real.sin u) ^ 2 ≤ ((H : ℝ) * u) ^ 2 at hsquare
    change 1 / ((H : ℝ) * u) ^ 2 ≤ 1 / ((H : ℝ) ^ 2 * Real.sin u ^ 2)
    rw [mul_pow]
    simp only [mul_pow] at hsquare
    exact one_div_le_one_div_of_le (by positivity) hsquare
  have htermV : 1 / (Real.pi - t) ^ 2 ≤
      1 / ((H : ℝ) ^ 2 * Real.sin v ^ 2) := by
    rw [hpit]
    have hmul : (H : ℝ) * Real.sin v ≤ (H : ℝ) * v := by gcongr
    have hsquare := pow_le_pow_left₀ (mul_nonneg hHpos.le hsv.le) hmul 2
    rw [mul_pow]
    simp only [mul_pow] at hsquare
    exact one_div_le_one_div_of_le (by positivity) hsquare
  have hsinA : 2 / (H : ℝ) ≤ Real.sin a := by
    have hj := Real.mul_le_sin ha0.le haHalf
    calc
      2 / (H : ℝ) = 2 / Real.pi * a := by
        dsimp [a]
        field_simp [hH0, Real.pi_ne_zero]
      _ ≤ Real.sin a := hj
  have huvSin : Real.sin u * Real.sin v ≤ u * v :=
    mul_le_mul hsu_le hsv_le hsv.le hu0.le
  have hcross : 2 / (Real.pi * t * (Real.pi - t)) ≤
      Real.sin a / (Real.pi * (H : ℝ) * Real.sin u * Real.sin v) := by
    rw [hpit]
    have hden : Real.pi * (H : ℝ) ^ 2 * Real.sin u * Real.sin v ≤
        Real.pi * (H : ℝ) ^ 2 * u * v := by gcongr
    have hleft : 2 / (Real.pi * ((H : ℝ) * u) * ((H : ℝ) * v)) ≤
        2 / (Real.pi * (H : ℝ) ^ 2 * Real.sin u * Real.sin v) := by
      have := one_div_le_one_div_of_le (by positivity) hden
      have heq : Real.pi * ((H : ℝ) * u) * ((H : ℝ) * v) =
          Real.pi * (H : ℝ) ^ 2 * u * v := by ring
      rw [heq]
      gcongr
    calc
      2 / (Real.pi * ((H : ℝ) * u) * ((H : ℝ) * v)) ≤
          2 / (Real.pi * (H : ℝ) ^ 2 * Real.sin u * Real.sin v) := hleft
      _ ≤ Real.sin a / (Real.pi * (H : ℝ) * Real.sin u * Real.sin v) := by
        have hnum : 2 ≤ (H : ℝ) * Real.sin a := by
          have := mul_le_mul_of_nonneg_left hsinA hHpos.le
          field_simp [hH0] at this
          exact this
        have heq : Real.sin a / (Real.pi * (H : ℝ) * Real.sin u * Real.sin v) =
            ((H : ℝ) * Real.sin a) /
              (Real.pi * (H : ℝ) ^ 2 * Real.sin u * Real.sin v) := by
          field_simp [hH0, hsu.ne', hsv.ne', Real.pi_ne_zero]
        rw [heq]
        gcongr
  have hscalar := scalar_sine_bound t ht0 htpi
  have hH1 : 1 ≤ H := by omega
  rw [periodicVaalerMajorant_closed H hH1 x hsp hsm, hcost]
  change 1 ≤ Real.sin t ^ 2 / (H : ℝ) ^ 2 *
    (1 / Real.sin u ^ 2 + 1 / Real.sin v ^ 2 +
      (H : ℝ) * Real.sin a / (Real.pi * Real.sin u * Real.sin v))
  have hnormalize :
      Real.sin t ^ 2 / (H : ℝ) ^ 2 *
          (1 / Real.sin u ^ 2 + 1 / Real.sin v ^ 2 +
            (H : ℝ) * Real.sin a / (Real.pi * Real.sin u * Real.sin v)) =
        Real.sin t ^ 2 *
          (1 / ((H : ℝ) ^ 2 * Real.sin u ^ 2) +
            1 / ((H : ℝ) ^ 2 * Real.sin v ^ 2) +
            Real.sin a / (Real.pi * (H : ℝ) * Real.sin u * Real.sin v)) := by
    field_simp [hH0, hsu.ne', hsv.ne', Real.pi_ne_zero]
  rw [hnormalize]
  calc
    1 ≤ Real.sin t ^ 2 *
        (1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 +
          2 / (Real.pi * t * (Real.pi - t))) := hscalar
    _ ≤ _ := by gcongr

theorem periodicVaalerMajorant_nonneg_of_sines_ne_zero
    (H : ℕ) (hH : 2 ≤ H) (x : ℝ)
    (hsp : Real.sin ((Real.pi / (H : ℝ) + 2 * Real.pi * x) / 2) ≠ 0)
    (hsm : Real.sin ((Real.pi / (H : ℝ) - 2 * Real.pi * x) / 2) ≠ 0) :
    0 ≤ periodicVaalerMajorant H x := by
  have hHpos : 0 < (H : ℝ) := by positivity
  have hH0 : (H : ℝ) ≠ 0 := hHpos.ne'
  let a := Real.pi / (H : ℝ)
  let theta := 2 * Real.pi * x
  let up := (a + theta) / 2
  let um := (a - theta) / 2
  let k := (H : ℝ) * Real.sin a / (2 * Real.pi)
  have hprod : Real.sin up * Real.sin um =
      (Real.cos theta - Real.cos a) / 2 := by
    have h := Real.two_mul_sin_mul_sin up um
    have hsub : up - um = theta := by dsimp [up, um]; ring
    have hadd : up + um = a := by dsimp [up, um]; ring
    rw [hsub, hadd] at h
    linarith
  have hsumsq : Real.sin up ^ 2 + Real.sin um ^ 2 =
      1 - Real.cos a * Real.cos theta := by
    rw [show Real.sin up ^ 2 = (1 - Real.cos (2 * up)) / 2 by
      nlinarith [Real.sin_sq_add_cos_sq up, Real.cos_two_mul up],
      show Real.sin um ^ 2 = (1 - Real.cos (2 * um)) / 2 by
      nlinarith [Real.sin_sq_add_cos_sq um, Real.cos_two_mul um]]
    rw [show 2 * up = a + theta by dsimp [up]; ring,
      show 2 * um = a - theta by dsimp [um]; ring,
      Real.cos_add, Real.cos_sub]
    ring
  have ha0 : 0 < a := div_pos Real.pi_pos hHpos
  have haHalf : a ≤ Real.pi / 2 := by
    dsimp [a]
    rw [div_le_iff₀ hHpos]
    have hcast : (2 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith [Real.pi_pos]
  have hsina : 0 ≤ Real.sin a :=
    (Real.sin_pos_of_pos_of_lt_pi ha0
      (haHalf.trans_lt (by linarith [Real.pi_pos]))).le
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hB : 0 ≤ 1 - Real.cos a * Real.cos theta +
      (H : ℝ) * Real.sin a / Real.pi * (Real.sin up * Real.sin um) := by
    rw [hprod]
    have hform :
        1 - Real.cos a * Real.cos theta +
            (H : ℝ) * Real.sin a / Real.pi *
              ((Real.cos theta - Real.cos a) / 2) =
          1 - k * Real.cos a + (k - Real.cos a) * Real.cos theta := by
      dsimp [k]
      ring
    rw [hform]
    by_cases htwo : H = 2
    · subst H
      have ha : a = Real.pi / 2 := by dsimp [a]
      rw [ha, Real.cos_pi_div_two]
      have hk : k = 1 / Real.pi := by
        dsimp [k]
        rw [ha, Real.sin_pi_div_two]
        ring
      rw [hk]
      have hcos := Real.neg_one_le_cos theta
      have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hk1 : 1 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 hpi
      nlinarith
    · have hH3 : 3 ≤ H := by omega
      have haThird : a ≤ Real.pi / 3 := by
        dsimp [a]
        rw [div_le_iff₀ hHpos]
        have hcast : (3 : ℝ) ≤ H := by exact_mod_cast hH3
        nlinarith [Real.pi_pos]
      have hcosa : 1 / 2 ≤ Real.cos a := by
        rw [← Real.cos_pi_div_three]
        exact Real.strictAntiOn_cos.antitoneOn
          ⟨ha0.le, by linarith [Real.pi_pos]⟩
          ⟨by positivity, by linarith [Real.pi_pos]⟩ haThird
      have hsinale : Real.sin a ≤ a := Real.sin_le ha0.le
      have hka : k ≤ Real.cos a := by
        have hkhalf : k ≤ 1 / 2 := by
          dsimp [k, a] at *
          field_simp [hH0, Real.pi_ne_zero] at hsinale ⊢
          nlinarith [Real.pi_pos]
        exact hkhalf.trans hcosa
      have hcos := Real.cos_le_one theta
      have hcosa1 := Real.cos_le_one a
      have hcoef : k - Real.cos a ≤ 0 := sub_nonpos.mpr hka
      have hmul : k - Real.cos a ≤
          (k - Real.cos a) * Real.cos theta := by
        nlinarith [mul_nonneg (neg_nonneg.mpr hcoef) (sub_nonneg.mpr hcos)]
      have hone : 0 ≤ (1 - Real.cos a) * (1 + k) := by positivity
      nlinarith
  have hbracket : 0 ≤
      1 / Real.sin up ^ 2 + 1 / Real.sin um ^ 2 +
        (H : ℝ) * Real.sin a /
          (Real.pi * Real.sin up * Real.sin um) := by
    have hsup : Real.sin up ≠ 0 := by
      simpa [up, a, theta] using hsp
    have hsum : Real.sin um ≠ 0 := by
      simpa [um, a, theta] using hsm
    have heq :
        1 / Real.sin up ^ 2 + 1 / Real.sin um ^ 2 +
            (H : ℝ) * Real.sin a /
              (Real.pi * Real.sin up * Real.sin um) =
          (1 - Real.cos a * Real.cos theta +
            (H : ℝ) * Real.sin a / Real.pi *
              (Real.sin up * Real.sin um)) /
            (Real.sin up ^ 2 * Real.sin um ^ 2) := by
      field_simp [hsup, hsum]
      nlinarith [hsumsq]
    rw [heq]
    positivity
  have hH1 : 1 ≤ H := by omega
  rw [periodicVaalerMajorant_closed H hH1 x hsp hsm]
  change 0 ≤ Real.cos ((H : ℝ) * theta / 2) ^ 2 / (H : ℝ) ^ 2 *
    (1 / Real.sin up ^ 2 + 1 / Real.sin um ^ 2 +
      (H : ℝ) * Real.sin a / (Real.pi * Real.sin up * Real.sin um))
  positivity

theorem periodicVaalerMajorant_add_int (H : ℕ) (x : ℝ) (z : ℤ) :
    periodicVaalerMajorant H (x + (z : ℝ)) = periodicVaalerMajorant H x := by
  rw [periodicVaalerMajorant, periodicVaalerMajorant]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro h _hh
  congr 1
  have harg : 2 * Real.pi * (h : ℝ) * (x + (z : ℝ)) =
      2 * Real.pi * (h : ℝ) * x + ((h : ℤ) * z : ℤ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.cos_add_int_mul_two_pi]

theorem periodicVaalerMajorant_nonneg (H : ℕ) (hH : 2 ≤ H) (x : ℝ) :
    0 ≤ periodicVaalerMajorant H x := by
  have hHpos : 0 < (H : ℝ) := by positivity
  have hH0 : (H : ℝ) ≠ 0 := hHpos.ne'
  by_cases hsp : Real.sin ((Real.pi / (H : ℝ) + 2 * Real.pi * x) / 2) = 0
  · obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hsp
    have hx : x = (z : ℝ) - (2 * (H : ℝ))⁻¹ := by
      have hpi0 := Real.pi_ne_zero
      field_simp [hH0, hpi0] at hz ⊢
      nlinarith
    rw [hx, show (z : ℝ) - (2 * (H : ℝ))⁻¹ =
      -((2 * (H : ℝ))⁻¹) + (z : ℝ) by ring,
      periodicVaalerMajorant_add_int,
      periodicVaalerMajorant_endpoint_neg H hH]
    norm_num
  · by_cases hsm : Real.sin ((Real.pi / (H : ℝ) - 2 * Real.pi * x) / 2) = 0
    · obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hsm
      have hx : x = (2 * (H : ℝ))⁻¹ - (z : ℝ) := by
        have hpi0 := Real.pi_ne_zero
        field_simp [hH0, hpi0] at hz ⊢
        nlinarith
      rw [hx, show (2 * (H : ℝ))⁻¹ - (z : ℝ) =
        (2 * (H : ℝ))⁻¹ + ((-z : ℤ) : ℝ) by push_cast; ring,
        periodicVaalerMajorant_add_int,
        periodicVaalerMajorant_endpoint_pos H hH]
      norm_num
    · exact periodicVaalerMajorant_nonneg_of_sines_ne_zero H hH x hsp hsm

/-- The explicit polynomial pointwise majorizes the strict circular indicator. -/
theorem strictCentralIndicator_le_periodicVaalerMajorant
    (H : ℕ) (hH : 2 ≤ H) (x : ℝ) :
    strictCentralIndicator H x ≤ periodicVaalerMajorant H x := by
  rw [strictCentralIndicator]
  split_ifs with hx
  · obtain ⟨z, hz⟩ :=
      DecimalFactorComplexity.WeightedFourierReduction.exists_int_abs_sub_lt_of_circleDistance_lt hx
    have hmajor := periodicVaalerMajorant_ge_one_of_abs_lt H hH hz
    have hperiod := periodicVaalerMajorant_add_int H (x - (z : ℝ)) z
    rw [sub_add_cancel] at hperiod
    exact hmajor.trans_eq hperiod.symm
  · exact periodicVaalerMajorant_nonneg H hH x

/-- All analytic claims needed by the T61 periodic Vaaler interface. -/
theorem vaalerAnalyticClaims (H : ℕ) (hH : 2 ≤ H) :
    (∀ x : ℝ, strictCentralIndicator H x ≤ periodicVaalerMajorant H x) ∧
    periodicVaalerMajorant H ((2 * (H : ℝ))⁻¹) = 1 ∧
    periodicVaalerMajorant H (-((2 * (H : ℝ))⁻¹)) = 1 ∧
    ∃ u : ℝ, 1 / 2 < u ∧ u < 1 ∧
      ∀ h : ℕ, 1 ≤ h → h < H →
        (0 < vaalerCoefficient H h ↔ (h : ℝ) / H < u) ∧
        (vaalerCoefficient H h = 0 ↔ (h : ℝ) / H = u) ∧
        (vaalerCoefficient H h < 0 ↔ u < (h : ℝ) / H) := by
  refine ⟨strictCentralIndicator_le_periodicVaalerMajorant H hH,
    periodicVaalerMajorant_endpoint_pos H hH,
    periodicVaalerMajorant_endpoint_neg H hH, ?_⟩
  exact exists_vaalerCoefficient_sign_transition H hH

/-! ## Fourier, endpoint, and T56 range audits -/

/-- The exact T56 sample length `L_n = 10^(n/2)`, with natural division. -/
abbrev sampleLength (n : ℕ) : ℕ := t56SampleLength n

/-- The exact T58 bandwidth `H_n = 10^n/2`, with natural division. -/
abbrev shortBandwidth (n : ℕ) : ℕ := bandwidth n

/-- T56's residual start range at one short lag, before imposing nearness. -/
def residualStartDomain (μ c : ℝ) (Q0 n r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (sampleLength n - r)).filter fun j =>
    ¬ ArithmeticExcluded μ c Q0 n j r

/-- Complete upper-triangular residual domain, represented by `(r,j)`. -/
def residualShortRectangle (μ c : ℝ) (Q0 n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (shortRectangle n).filter fun p =>
    ¬ ArithmeticExcluded μ c Q0 n p.2 p.1

/-- Every lag, start, endpoint, and arithmetic mask in the domain. -/
theorem mem_residualShortRectangle_iff
    {μ c : ℝ} {Q0 n r j : ℕ} :
    (r, j) ∈ residualShortRectangle μ c Q0 n ↔
      0 < r ∧ r < n ∧ j < sampleLength n - r ∧
        ¬ ArithmeticExcluded μ c Q0 n j r := by
  classical
  simp only [residualShortRectangle, Finset.mem_filter,
    mem_shortRectangle_iff]
  tauto

/-- The coefficient definition unfolds to the T59/T60 roadmap formula. -/
theorem vaalerCoefficient_explicit (H h : ℕ) :
    vaalerCoefficient H h =
      (H : ℝ)⁻¹ *
        (Real.sin (Real.pi * (h : ℝ) / (H : ℝ)) / Real.pi +
          2 * (1 - (h : ℝ) / (H : ℝ)) *
            Real.cos (Real.pi * (h : ℝ) / (H : ℝ))) := by
  rw [vaalerCoefficient, coefficientShape]
  congr 3 <;> ring

/-- Every signed Fourier coefficient, including zero and the strict cutoff. -/
def vaalerFourierCoefficient (H : ℕ) (h : ℤ) : ℝ :=
  if h = 0 then 2 / (H : ℝ)
  else if h.natAbs < H then vaalerCoefficient H h.natAbs else 0

theorem vaalerFourierCoefficient_zero (H : ℕ) :
    vaalerFourierCoefficient H 0 = 2 / (H : ℝ) := by
  simp [vaalerFourierCoefficient]

theorem vaalerFourierCoefficient_of_mem
    {H : ℕ} {h : ℤ} (hh0 : h ≠ 0) (hhH : h.natAbs < H) :
    vaalerFourierCoefficient H h = vaalerCoefficient H h.natAbs := by
  simp [vaalerFourierCoefficient, hh0, hhH]

theorem vaalerFourierCoefficient_of_cutoff
    {H : ℕ} {h : ℤ} (hhH : H ≤ h.natAbs) :
    vaalerFourierCoefficient H h = 0 := by
  by_cases hh0 : h = 0
  · subst h
    have hH0 : H = 0 := by omega
    subst H
    norm_num [vaalerFourierCoefficient]
  · simp [vaalerFourierCoefficient, hh0, not_lt.mpr hhH]

theorem vaalerFourierCoefficient_neg (H : ℕ) (h : ℤ) :
    vaalerFourierCoefficient H (-h) = vaalerFourierCoefficient H h := by
  by_cases hh0 : h = 0
  · subst h
    simp
  · have hneg0 : -h ≠ 0 := neg_ne_zero.mpr hh0
    simp only [vaalerFourierCoefficient, hh0, hneg0, if_false,
      Int.natAbs_neg]

/-- The finite formula displays exactly the positive frequencies `1 ≤ h < H`. -/
theorem periodicVaalerMajorant_finite_formula (H : ℕ) (x : ℝ) :
    periodicVaalerMajorant H x =
      2 / (H : ℝ) +
        2 * ∑ h ∈ Finset.Ico 1 H,
          vaalerCoefficient H h * Real.cos (2 * Real.pi * (h : ℝ) * x) := by
  rfl

theorem mem_vaalerPositiveFrequencies_iff {H h : ℕ} :
    h ∈ Finset.Ico 1 H ↔ 1 ≤ h ∧ h < H := by
  simp

/-- On the centered half-open fundamental interval, circle distance is absolute value. -/
theorem circleDistance_eq_abs_of_mem_half {x : ℝ}
    (hx : x ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2)) :
    circleDistance x = |x| := by
  have hround : round x = 0 := (round_eq_zero_iff.mpr hx)
  apply le_antisymm
  · simpa using circleDistance_le_abs_sub_int x (0 : ℤ)
  · unfold circleDistance
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    simpa [hround] using round_le x z

/-- The strict positive endpoint is excluded by the indicator. -/
theorem strictCentralIndicator_endpoint_pos (H : ℕ) (hH : 2 ≤ H) :
    strictCentralIndicator H ((2 * (H : ℝ))⁻¹) = 0 := by
  have hHpos : 0 < (H : ℝ) := by positivity
  have hdelta0 : 0 ≤ (2 * (H : ℝ))⁻¹ := by positivity
  have hdeltahalf : (2 * (H : ℝ))⁻¹ < (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      inv_lt_inv₀ (by positivity) (by norm_num)]
    have hcast : (2 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  have hcircle : circleDistance ((2 * (H : ℝ))⁻¹) =
      (2 * (H : ℝ))⁻¹ := by
    rw [circleDistance_eq_abs_of_mem_half ⟨by linarith, hdeltahalf⟩,
      abs_of_nonneg hdelta0]
  rw [strictCentralIndicator, hcircle]
  simp

/-- The strict negative endpoint is also excluded by the indicator. -/
theorem strictCentralIndicator_endpoint_neg (H : ℕ) (hH : 2 ≤ H) :
    strictCentralIndicator H (-((2 * (H : ℝ))⁻¹)) = 0 := by
  have hHpos : 0 < (H : ℝ) := by positivity
  have hdelta0 : 0 ≤ (2 * (H : ℝ))⁻¹ := by positivity
  have hdeltahalf : (2 * (H : ℝ))⁻¹ < (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      inv_lt_inv₀ (by positivity) (by norm_num)]
    have hcast : (2 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  have hcircle : circleDistance (-((2 * (H : ℝ))⁻¹)) =
      (2 * (H : ℝ))⁻¹ := by
    rw [circleDistance_eq_abs_of_mem_half]
    · simp [abs_of_nonneg hdelta0]
    · constructor <;> linarith
  rw [strictCentralIndicator, hcircle]
  simp

/-- Complete analytic certificate; unlike the fixed-pi estimate below, this is proved. -/
def VaalerAnalyticCertificate (H : ℕ) : Prop :=
  2 ≤ H ∧
  (∀ x : ℝ, strictCentralIndicator H x ≤ periodicVaalerMajorant H x) ∧
  strictCentralIndicator H ((2 * (H : ℝ))⁻¹) = 0 ∧
  strictCentralIndicator H (-((2 * (H : ℝ))⁻¹)) = 0 ∧
  periodicVaalerMajorant H ((2 * (H : ℝ))⁻¹) = 1 ∧
  periodicVaalerMajorant H (-((2 * (H : ℝ))⁻¹)) = 1 ∧
  ∃ u : ℝ, 1 / 2 < u ∧ u < 1 ∧
    (∀ h : ℕ, 1 ≤ h → h < H →
      (0 < vaalerCoefficient H h ↔ (h : ℝ) / H < u) ∧
      (vaalerCoefficient H h = 0 ↔ (h : ℝ) / H = u) ∧
      (vaalerCoefficient H h < 0 ↔ u < (h : ℝ) / H))

theorem vaalerAnalyticCertificate_proved (H : ℕ) (hH : 2 ≤ H) :
    VaalerAnalyticCertificate H := by
  obtain ⟨hmajor, hpos, hneg, u, hu, hu1, hsign⟩ :=
    vaalerAnalyticClaims H hH
  exact ⟨hH, hmajor, strictCentralIndicator_endpoint_pos H hH,
    strictCentralIndicator_endpoint_neg H hH, hpos, hneg,
    u, hu, hu1, hsign⟩

/-! ## The sole unproved fixed-pi signed premise -/

/-- The complete signed positive-frequency sum over T56's residual rectangle. -/
def signedStructuredDenominatorSum (μ c : ℝ) (Q0 n : ℕ) : ℝ :=
  2 * ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
    vaalerCoefficient (shortBandwidth n) h *
      ∑ r ∈ shortResidualLags n (sampleLength n),
        ∑ j ∈ residualStartDomain μ c Q0 n r,
          Real.cos (2 * Real.pi * (h : ℝ) *
            ((structuredDenominator j r : ℝ) * Real.pi))

/-- Number of masked labels in the complete nested T56 short rectangle. -/
def residualStructuredCard (μ c : ℝ) (Q0 n : ℕ) : ℕ :=
  ∑ r ∈ shortResidualLags n (sampleLength n),
    (residualStartDomain μ c Q0 n r).card

/-- The zero mode plus the genuinely signed complete Fourier sum. -/
def completeStructuredVaalerExpression (μ c : ℝ) (Q0 n : ℕ) : ℝ :=
  2 / (shortBandwidth n : ℝ) * residualStructuredCard μ c Q0 n +
    signedStructuredDenominatorSum μ c Q0 n

/-- Sum of the proved Vaaler majorant over every masked T56 short label. -/
def structuredVaalerMajorantTotal (μ c : ℝ) (Q0 n : ℕ) : ℝ :=
  ∑ r ∈ shortResidualLags n (sampleLength n),
    ∑ j ∈ residualStartDomain μ c Q0 n r,
      periodicVaalerMajorant (shortBandwidth n)
        ((structuredDenominator j r : ℝ) * Real.pi)

/-- Exact finite expansion of the complete nested majorant sum. -/
theorem structuredVaalerMajorantTotal_eq_completeExpression
    (μ c : ℝ) (Q0 n : ℕ) :
    structuredVaalerMajorantTotal μ c Q0 n =
      completeStructuredVaalerExpression μ c Q0 n := by
  classical
  unfold structuredVaalerMajorantTotal completeStructuredVaalerExpression
    residualStructuredCard signedStructuredDenominatorSum
  simp_rw [periodicVaalerMajorant]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_sum]
  have hcomm :
      (∑ r ∈ shortResidualLags n (sampleLength n),
        ∑ j ∈ residualStartDomain μ c Q0 n r,
          ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
            vaalerCoefficient (shortBandwidth n) h *
              Real.cos (2 * Real.pi * (h : ℝ) *
                ((structuredDenominator j r : ℝ) * Real.pi))) =
        ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
          vaalerCoefficient (shortBandwidth n) h *
            ∑ r ∈ shortResidualLags n (sampleLength n),
              ∑ j ∈ residualStartDomain μ c Q0 n r,
                Real.cos (2 * Real.pi * (h : ℝ) *
                  ((structuredDenominator j r : ℝ) * Real.pi)) := by
    calc
      (∑ r ∈ shortResidualLags n (sampleLength n),
          ∑ j ∈ residualStartDomain μ c Q0 n r,
            ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
              vaalerCoefficient (shortBandwidth n) h *
                Real.cos (2 * Real.pi * (h : ℝ) *
                  ((structuredDenominator j r : ℝ) * Real.pi))) =
          ∑ r ∈ shortResidualLags n (sampleLength n),
            ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
              ∑ j ∈ residualStartDomain μ c Q0 n r,
                vaalerCoefficient (shortBandwidth n) h *
                  Real.cos (2 * Real.pi * (h : ℝ) *
                    ((structuredDenominator j r : ℝ) * Real.pi)) := by
        apply Finset.sum_congr rfl
        intro r _hr
        rw [Finset.sum_comm]
      _ = ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
            ∑ r ∈ shortResidualLags n (sampleLength n),
              ∑ j ∈ residualStartDomain μ c Q0 n r,
                vaalerCoefficient (shortBandwidth n) h *
                  Real.cos (2 * Real.pi * (h : ℝ) *
                    ((structuredDenominator j r : ℝ) * Real.pi)) := by
        rw [Finset.sum_comm]
      _ = ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
            vaalerCoefficient (shortBandwidth n) h *
              ∑ r ∈ shortResidualLags n (sampleLength n),
                ∑ j ∈ residualStartDomain μ c Q0 n r,
                  Real.cos (2 * Real.pi * (h : ℝ) *
                    ((structuredDenominator j r : ℝ) * Real.pi)) := by
        apply Finset.sum_congr rfl
        intro h _hh
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        rw [Finset.mul_sum]
  have hfactor :
      (∑ r ∈ shortResidualLags n (sampleLength n),
        ∑ j ∈ residualStartDomain μ c Q0 n r,
          2 * ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
            vaalerCoefficient (shortBandwidth n) h *
              Real.cos (2 * Real.pi * (h : ℝ) *
                ((structuredDenominator j r : ℝ) * Real.pi))) =
        2 * ∑ r ∈ shortResidualLags n (sampleLength n),
          ∑ j ∈ residualStartDomain μ c Q0 n r,
            ∑ h ∈ Finset.Ico 1 (shortBandwidth n),
              vaalerCoefficient (shortBandwidth n) h *
                Real.cos (2 * Real.pi * (h : ℝ) *
                  ((structuredDenominator j r : ℝ) * Real.pi)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [Finset.mul_sum]
  have hconst :
      (∑ r ∈ shortResidualLags n (sampleLength n),
        ((residualStartDomain μ c Q0 n r).card : ℝ) *
          (2 / (shortBandwidth n : ℝ))) =
        2 / (shortBandwidth n : ℝ) *
          ∑ r ∈ shortResidualLags n (sampleLength n),
            ((residualStartDomain μ c Q0 n r).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  rw [hfactor, hcomm, hconst]

/-- Upper-triangular strict residual incidences, before restoring orientation. -/
def strictResidualIncidenceCount (μ c : ℝ) (Q0 n : ℕ) : ℕ :=
  ∑ r ∈ shortResidualLags n (sampleLength n),
    (residualNearReturnStarts μ c Q0 n (sampleLength n) r).card

theorem shortResidualPairCount_eq_two_mul_strictResidualIncidenceCount
    (μ c : ℝ) (Q0 n : ℕ) :
    shortResidualPairCount μ c Q0 n (sampleLength n) =
      2 * strictResidualIncidenceCount μ c Q0 n := by
  rfl

/-- The decimal cutoff is exactly the Vaaler central radius. -/
theorem decimalCutoff_eq_centralRadius (n : ℕ) (hn : 1 ≤ n) :
    ((10 : ℝ) ^ n)⁻¹ = (2 * (shortBandwidth n : ℝ))⁻¹ := by
  have hnat : 2 * shortBandwidth n = 10 ^ n := by
    exact DecimalFactorComplexity.FejerSpectralCriterion.two_mul_half_ten_pow n hn
  have hreal : 2 * (shortBandwidth n : ℝ) = (10 : ℝ) ^ n := by
    exact_mod_cast hnat
  rw [hreal]

/-- Every eventual T56 bandwidth satisfies the analytic theorem's `H ≥ 2`. -/
theorem two_le_shortBandwidth (n : ℕ) (hn : 1 ≤ n) :
    2 ≤ shortBandwidth n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  change 2 ≤ 10 ^ (1 + k) / 2
  rw [Nat.add_comm 1 k, pow_succ]
  have hpow : 1 ≤ 10 ^ k := one_le_pow₀ (by norm_num)
  omega

/-- The strict incidence count is the sum of strict indicators over all labels. -/
theorem strictResidualIncidenceCount_cast_eq_indicatorSum
    (μ c : ℝ) (Q0 n : ℕ) :
    (strictResidualIncidenceCount μ c Q0 n : ℝ) =
      ∑ r ∈ shortResidualLags n (sampleLength n),
        ∑ j ∈ residualStartDomain μ c Q0 n r,
          strictCentralIndicator (shortBandwidth n)
            ((structuredDenominator j r : ℝ) * Real.pi) := by
  classical
  have hsets (r : ℕ) (hr : r ∈ shortResidualLags n (sampleLength n)) :
      residualNearReturnStarts μ c Q0 n (sampleLength n) r =
        (residualStartDomain μ c Q0 n r).filter fun j =>
          circleDistance ((structuredDenominator j r : ℝ) * Real.pi) <
            (2 * (shortBandwidth n : ℝ))⁻¹ := by
    have hrs := mem_shortResidualLags_iff.mp hr
    have hn : 1 ≤ n := by omega
    ext j
    simp only [residualNearReturnStarts, nearReturnStarts, residualStartDomain,
      Finset.mem_filter, Finset.mem_range]
    rw [structuredDenominator_cast, decimalCutoff_eq_centralRadius n hn]
    tauto
  unfold strictResidualIncidenceCount
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  rw [hsets r hr]
  simp [strictCentralIndicator]

/-- The now-proved Vaaler theorem bounds every strict residual incidence. -/
theorem strictResidualIncidenceCount_le_majorantTotal
    (μ c : ℝ) (Q0 n : ℕ) (hn : 1 ≤ n) :
    (strictResidualIncidenceCount μ c Q0 n : ℝ) ≤
      structuredVaalerMajorantTotal μ c Q0 n := by
  rw [strictResidualIncidenceCount_cast_eq_indicatorSum]
  unfold structuredVaalerMajorantTotal
  gcongr with r hr j hj
  exact strictCentralIndicator_le_periodicVaalerMajorant
    (shortBandwidth n) (two_le_shortBandwidth n hn) _

/-- The sole unproved premise: one eventual bound on the complete, explicitly
signed fixed-pi expression.  It contains no analytic-majorant hypothesis. -/
def SignedStructuredDenominatorPremise (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      completeStructuredVaalerExpression μ c Q0 n ≤
        B * (sampleLength n : ℝ)

theorem signedStructuredDenominatorPremise_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    SignedStructuredDenominatorPremise μ c Q0 ↔
      ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          completeStructuredVaalerExpression μ c Q0 n ≤
            B * (sampleLength n : ℝ) := by
  rfl

/-! ## Conditional chain through T56 -/

theorem signedStructuredDenominatorPremise_implies_sparseShortRepunitIncidenceBound
    {μ c : ℝ} {Q0 : ℕ}
    (hSigned : SignedStructuredDenominatorPremise μ c Q0) :
    SparseShortRepunitIncidenceBound μ c Q0 := by
  obtain ⟨B, hB, N, hN, hall⟩ := hSigned
  refine ⟨2 * B, mul_pos (by norm_num) hB, N, hN, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := hN.trans hn
  have hmajor := strictResidualIncidenceCount_le_majorantTotal
    μ c Q0 n hn1
  rw [structuredVaalerMajorantTotal_eq_completeExpression] at hmajor
  have hincidence :
      (strictResidualIncidenceCount μ c Q0 n : ℝ) ≤
        B * (sampleLength n : ℝ) := hmajor.trans (hall n hn)
  have hcountCast :
      (shortResidualPairCount μ c Q0 n (sampleLength n) : ℝ) =
        2 * (strictResidualIncidenceCount μ c Q0 n : ℝ) := by
    exact_mod_cast
      shortResidualPairCount_eq_two_mul_strictResidualIncidenceCount μ c Q0 n
  rw [hcountCast]
  calc
    2 * (strictResidualIncidenceCount μ c Q0 n : ℝ) ≤
        2 * (B * (sampleLength n : ℝ)) :=
      mul_le_mul_of_nonneg_left hincidence (by norm_num)
    _ = (2 * B) * (sampleLength n : ℝ) := by ring

/-- C7 remains conditional on T56's separate arithmetic and long-sector inputs. -/
theorem signedStructuredDenominatorPremise_implies_C7
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hLong : SparseLongResidualLinearBound μ c Q0)
    (hSigned : SignedStructuredDenominatorPremise μ c Q0) :
    PiSparseLongBandC7 :=
  sparse_sector_linear_bounds_imply_C7 hIrr
    (signedStructuredDenominatorPremise_implies_sparseShortRepunitIncidenceBound
      hSigned)
    hLong

/-- C2 follows conditionally only through the displayed C7 theorem. -/
theorem signedStructuredDenominatorPremise_implies_C2
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hLong : SparseLongResidualLinearBound μ c Q0)
    (hSigned : SignedStructuredDenominatorPremise μ c Q0) :
    PiExponentialCollisionC2 :=
  piSparseLongBandC7_implies_C2
    (signedStructuredDenominatorPremise_implies_C7 hIrr hLong hSigned)

/-- Canonical C1 follows conditionally through the displayed C2 theorem. -/
theorem signedStructuredDenominatorPremise_implies_C1
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hLong : SparseLongResidualLinearBound μ c Q0)
    (hSigned : SignedStructuredDenominatorPremise μ c Q0) :
    PiPositiveFactorEntropyC1 :=
  piExponentialCollisionC2_implies_C1
    (signedStructuredDenominatorPremise_implies_C2 hIrr hLong hSigned)

/-- One theorem exposing the complete conditional chain and all three inputs. -/
theorem signedStructuredDenominator_conditional_chain
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hLong : SparseLongResidualLinearBound μ c Q0)
    (hSigned : SignedStructuredDenominatorPremise μ c Q0) :
    SparseShortRepunitIncidenceBound μ c Q0 ∧
      PiSparseLongBandC7 ∧ PiExponentialCollisionC2 ∧
        PiPositiveFactorEntropyC1 := by
  have hShort :=
    signedStructuredDenominatorPremise_implies_sparseShortRepunitIncidenceBound
      hSigned
  have hC7 := sparse_sector_linear_bounds_imply_C7 hIrr hShort hLong
  have hC2 := piSparseLongBandC7_implies_C2 hC7
  exact ⟨hShort, hC7, hC2, piExponentialCollisionC2_implies_C1 hC2⟩

/-! ## Finite abstract phase separation -/

/-- A signed coefficient family with both signs present. -/
def abstractCoefficient (k : ℕ) : ℝ := if Even k then 1 else -1

/-- Every nonzero phase is chosen to match its coefficient. -/
def abstractPhase (k : ℕ) : ℝ := abstractCoefficient k

/-- Injective abstract unsigned frequency assignment. -/
def abstractFrequency (k : ℕ) : ℕ := k

/-- Signed total on the finite range of `n*L` labels. -/
def abstractSignedTotal (n L : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n * L), abstractCoefficient k * abstractPhase k

theorem abstractPhase_ne_zero (k : ℕ) : abstractPhase k ≠ 0 := by
  by_cases hk : Even k <;> simp [abstractPhase, abstractCoefficient, hk]

theorem abstractFrequency_injective : Function.Injective abstractFrequency := by
  intro a b h
  exact h

/-- Every unsigned frequency fiber has multiplicity at most one. -/
theorem abstractFrequency_fiber_card_le_one (N q : ℕ) :
    ((Finset.range N).filter fun k => abstractFrequency k = q).card ≤ 1 := by
  apply Finset.card_le_card (t := {q})
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  simp only [Finset.mem_singleton]
  exact hk.2

theorem abstractSignedTotal_eq (n L : ℕ) :
    abstractSignedTotal n L = n * L := by
  classical
  unfold abstractSignedTotal
  calc
    (∑ k ∈ Finset.range (n * L),
        abstractCoefficient k * abstractPhase k) =
        ∑ _k ∈ Finset.range (n * L), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases heven : Even k <;>
        simp [abstractPhase, abstractCoefficient, heven]
    _ = n * L := by simp

/-- Finite separation: pointwise nonvanishing and unsigned multiplicity one
do not imply any uniform signed bound. -/
theorem exists_finite_phase_separation (C : ℕ) :
    ∃ n L : ℕ,
      0 < L ∧
      (∀ k ∈ Finset.range (n * L), abstractPhase k ≠ 0) ∧
      (∀ q : ℕ,
        ((Finset.range (n * L)).filter fun k =>
          abstractFrequency k = q).card ≤ 1) ∧
      (∃ k ∈ Finset.range (n * L), 0 < abstractCoefficient k) ∧
      (∃ k ∈ Finset.range (n * L), abstractCoefficient k < 0) ∧
      (C : ℝ) * L < abstractSignedTotal n L := by
  refine ⟨C + 2, 1, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _hk
    exact abstractPhase_ne_zero k
  · intro q
    exact abstractFrequency_fiber_card_le_one _ q
  · refine ⟨0, by simp, ?_⟩
    norm_num [abstractCoefficient]
  · refine ⟨1, by simp, ?_⟩
    norm_num [abstractCoefficient, Even]
  · rw [abstractSignedTotal_eq]
    push_cast
    norm_num

end DecimalFactorComplexity.T61VaalerAnalytic

#print axioms DecimalFactorComplexity.T61VaalerAnalytic.scalar_sine_bound
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.strictCentralIndicator_le_periodicVaalerMajorant
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.periodicVaalerMajorant_endpoint_pos
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.exists_vaalerCoefficient_sign_transition
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.vaalerCoefficient_explicit
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.vaalerFourierCoefficient_zero
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.vaalerFourierCoefficient_of_mem
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.vaalerFourierCoefficient_of_cutoff
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.mem_residualShortRectangle_iff
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.vaalerAnalyticCertificate_proved
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.structuredVaalerMajorantTotal_eq_completeExpression
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.decimalCutoff_eq_centralRadius
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.strictResidualIncidenceCount_cast_eq_indicatorSum
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.signedStructuredDenominatorPremise_iff_quantifiers
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.signedStructuredDenominator_conditional_chain
#print axioms DecimalFactorComplexity.T61VaalerAnalytic.exists_finite_phase_separation
