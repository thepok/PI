import TheoryLib.PiDigits.T20BaseTenOrbitDensity
import TheoryLib.PiDigits.T26WeylCancellationV1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A finite exponential-sum certificate for decimal cylinders

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The final specialization in this file is conditional.  The required finite
exponential-sum bounds for the base-ten orbit of `Real.pi` are not proved
here or in T26.  Consequently this file proves neither T7's canonical V1 nor
its sibling V3 unconditionally.
-/

noncomputable section

open scoped ComplexConjugate Real
open Finset Set

namespace Theory.PiDigits.T27

/-- The T26-normalized Fourier phase at integer frequency `h`. -/
def phase (h : ℤ) (x : ℝ) : ℂ :=
  Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (x : ℂ))

/-- The unnormalized finite exponential sum at frequency `h`. -/
def exponentialSum (x : ℕ → ℝ) (N : ℕ) (h : ℤ) : ℂ :=
  ∑ j ∈ range N, phase h (x j)

/-- The length-`H+1` geometric kernel whose square is the Fejer kernel. -/
def dirichletKernel (H : ℕ) (x : ℝ) : ℂ :=
  ∑ r ∈ range (H + 1), phase (r : ℤ) x

/-- A nonnegative Fejer kernel, normalized to have circle mean one. -/
def fejerKernel (H : ℕ) (x : ℝ) : ℝ :=
  ‖dirichletKernel H x‖ ^ 2 / (H + 1 : ℝ)

/-- Uniform bounds for the first `H` positive and negative nonzero
frequencies. -/
def FirstFrequencyBound (x : ℕ → ℝ) (N H : ℕ) (B : ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ H → ‖exponentialSum x N h‖ ≤ B

lemma phase_zero (x : ℝ) : phase 0 x = 1 := by
  simp [phase]

lemma phase_add (h q : ℤ) (x : ℝ) :
    phase (h + q) x = phase h x * phase q x := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_add_real (h : ℤ) (x y : ℝ) :
    phase h (x + y) = phase h x * phase h y := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_neg (h : ℤ) (x : ℝ) : phase (-h) x = conj (phase h x) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, map_intCast,
    Complex.conj_I, Int.cast_neg]
  ring

lemma phase_sub (h q : ℤ) (x : ℝ) :
    conj (phase h x) * phase q x = phase (q - h) x := by
  rw [← phase_neg, ← phase_add]
  congr 1
  omega

lemma norm_phase (h : ℤ) (x : ℝ) : ‖phase h x‖ = 1 := by
  rw [phase]
  convert Complex.norm_exp_ofReal_mul_I
    (2 * Real.pi * h * x) using 2
  push_cast
  ring

lemma fejerKernel_nonneg (H : ℕ) (x : ℝ) : 0 ≤ fejerKernel H x := by
  exact div_nonneg (sq_nonneg _) (by positivity)

lemma fejerKernel_le (H : ℕ) (x : ℝ) :
    fejerKernel H x ≤ H + 1 := by
  have hnorm : ‖dirichletKernel H x‖ ≤ H + 1 := by
    calc
      ‖dirichletKernel H x‖ ≤ ∑ r ∈ range (H + 1), ‖phase (r : ℤ) x‖ :=
        norm_sum_le _ _
      _ = H + 1 := by simp [norm_phase]
  rw [fejerKernel]
  have hpos : 0 < (H + 1 : ℝ) := by positivity
  apply (div_le_iff₀ hpos).2
  have hsquare : ‖dirichletKernel H x‖ ^ 2 ≤ (H + 1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  nlinarith

lemma normSq_dirichletKernel (H : ℕ) (x : ℝ) :
    Complex.normSq (dirichletKernel H x) =
      (∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
        phase ((s : ℤ) - (r : ℤ)) x).re := by
  classical
  have hc : (Complex.normSq (dirichletKernel H x) : ℂ) =
      ∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
        phase ((s : ℤ) - (r : ℤ)) x := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [dirichletKernel, map_sum]
    rw [sum_mul]
    apply sum_congr rfl
    intro r hr
    rw [mul_sum]
    apply sum_congr rfl
    intro s hs
    exact phase_sub (r : ℤ) (s : ℤ) x
  have := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, map_sum] using this

lemma fejerKernel_eq_doubleSum (H : ℕ) (x : ℝ) :
    fejerKernel H x =
      (∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
        phase ((s : ℤ) - (r : ℤ)) x).re / (H + 1 : ℝ) := by
  rw [fejerKernel, ← Complex.normSq_eq_norm_sq,
    normSq_dirichletKernel]

lemma sum_fejerKernel_eq_frequencySums (x : ℕ → ℝ) (N H : ℕ) :
    (∑ j ∈ range N, fejerKernel H (x j)) * (H + 1 : ℝ) =
      ∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
        (exponentialSum x N ((s : ℤ) - (r : ℤ))).re := by
  classical
  simp_rw [fejerKernel_eq_doubleSum]
  rw [sum_mul]
  simp_rw [div_mul_cancel₀ _ (by positivity : (H + 1 : ℝ) ≠ 0)]
  simp only [exponentialSum]
  simp_rw [← Complex.reCLM_apply, map_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [sum_comm]

lemma exponentialSum_zero (x : ℕ → ℝ) (N : ℕ) :
    exponentialSum x N 0 = N := by
  simp [exponentialSum, phase_zero]

lemma frequencySum_re_lower {x : ℕ → ℝ} {N H : ℕ} {B : ℝ}
    (hbound : FirstFrequencyBound x N H B) {h : ℤ}
    (h0 : h ≠ 0) (hH : h.natAbs ≤ H) :
    -B ≤ (exponentialSum x N h).re := by
  exact neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans (hbound h h0 hH))

lemma inner_frequency_sum_lower {x : ℕ → ℝ} {N H : ℕ} {B : ℝ}
    (hbound : FirstFrequencyBound x N H B) {r : ℕ}
    (hr : r ∈ range (H + 1)) :
    (N : ℝ) - H * B ≤
      ∑ s ∈ range (H + 1),
        (exponentialSum x N ((s : ℤ) - (r : ℤ))).re := by
  classical
  let t := range (H + 1)
  have herase : ∑ s ∈ t.erase r, (-B) ≤
      ∑ s ∈ t.erase r,
        (exponentialSum x N ((s : ℤ) - (r : ℤ))).re := by
    apply sum_le_sum
    intro s hs
    have hsr : s ≠ r := by
      exact fun h => (mem_erase.mp hs).1 h
    apply frequencySum_re_lower hbound
    · exact sub_ne_zero.mpr (by exact_mod_cast hsr)
    · have hslt : s < H + 1 := mem_range.mp (mem_of_mem_erase hs)
      have hrlt : r < H + 1 := mem_range.mp hr
      omega
  have hdiag :
      (exponentialSum x N ((r : ℤ) - (r : ℤ))).re = N := by
    rw [sub_self, exponentialSum_zero]
    norm_num
  rw [← sum_erase_add _ _ hr]
  calc
    (N : ℝ) - H * B = ∑ _s ∈ t.erase r, (-B) + N := by
      simp [t, card_erase_of_mem hr]
      ring
    _ ≤ (∑ s ∈ t.erase r,
          (exponentialSum x N ((s : ℤ) - (r : ℤ))).re) + N :=
      add_le_add herase le_rfl
    _ = (∑ s ∈ t.erase r,
          (exponentialSum x N ((s : ℤ) - (r : ℤ))).re) +
            (exponentialSum x N ((r : ℤ) - (r : ℤ))).re := by rw [hdiag]
    _ = _ := by rfl

/-- The finite Fourier part of the certificate.  The aggregate error is
`H * B` with universal numerical coefficient one: no discrepancy hypothesis
occurs in the statement. -/
lemma sum_fejerKernel_lower_of_firstFrequencyBound
    {x : ℕ → ℝ} {N H : ℕ} {B : ℝ}
    (hbound : FirstFrequencyBound x N H B) :
    (N : ℝ) - H * B ≤ ∑ j ∈ range N, fejerKernel H (x j) := by
  classical
  have htotal : (H + 1 : ℝ) * ((N : ℝ) - H * B) ≤
      ∑ r ∈ range (H + 1), ∑ s ∈ range (H + 1),
        (exponentialSum x N ((s : ℤ) - (r : ℤ))).re := by
    calc
      (H + 1 : ℝ) * ((N : ℝ) - H * B) =
          ∑ _r ∈ range (H + 1), ((N : ℝ) - H * B) := by
        simp
        ring
      _ ≤ _ := by
        apply sum_le_sum
        intro r hr
        exact inner_frequency_sum_lower hbound hr
  rw [← sum_fejerKernel_eq_frequencySums] at htotal
  have hpos : 0 < (H + 1 : ℝ) := by positivity
  nlinarith

lemma phase_nat_eq_pow (r : ℕ) (x : ℝ) :
    phase (r : ℤ) x = phase 1 x ^ r := by
  induction r with
  | zero => simp [phase_zero]
  | succ r ih =>
      rw [Nat.cast_succ, phase_add, ih, pow_succ]

lemma dirichletKernel_mul_one_sub (H : ℕ) (x : ℝ) :
    dirichletKernel H x * (1 - phase 1 x) =
      1 - phase 1 x ^ (H + 1) := by
  simp_rw [dirichletKernel, phase_nat_eq_pow]
  exact geom_sum_mul_neg (phase 1 x) (H + 1)

lemma norm_dirichletKernel_le_inv {H : ℕ} {x L : ℝ} (hL : 0 < L)
    (hsep : 2 * L ≤ ‖1 - phase 1 x‖) :
    ‖dirichletKernel H x‖ ≤ L⁻¹ := by
  have hproduct :
      ‖dirichletKernel H x‖ * ‖1 - phase 1 x‖ ≤ 2 := by
    rw [← norm_mul, dirichletKernel_mul_one_sub]
    calc
      ‖1 - phase 1 x ^ (H + 1)‖ ≤
          ‖(1 : ℂ)‖ + ‖phase 1 x ^ (H + 1)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_phase]
  have hscaled : ‖dirichletKernel H x‖ * (2 * L) ≤ 2 :=
    calc
      _ ≤ ‖dirichletKernel H x‖ * ‖1 - phase 1 x‖ :=
        mul_le_mul_of_nonneg_left hsep (norm_nonneg _)
      _ ≤ 2 := hproduct
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hL).2
  nlinarith

lemma fejerKernel_le_inv_sq {H : ℕ} {x L : ℝ} (hL : 0 < L)
    (hsep : 2 * L ≤ ‖1 - phase 1 x‖) :
    fejerKernel H x ≤ 1 / ((H + 1 : ℝ) * L ^ 2) := by
  have hnorm := norm_dirichletKernel_le_inv (H := H) hL hsep
  rw [fejerKernel]
  have hsq : ‖dirichletKernel H x‖ ^ 2 ≤ L⁻¹ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (inv_nonneg.mpr hL.le)).2 hnorm
  calc
    ‖dirichletKernel H x‖ ^ 2 / (H + 1 : ℝ) ≤
        L⁻¹ ^ 2 / (H + 1 : ℝ) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ = 1 / ((H + 1 : ℝ) * L ^ 2) := by
      field_simp [hL.ne']

lemma norm_one_sub_phase_one (u : ℝ) :
    ‖1 - phase 1 u‖ = 2 * |Real.sin (Real.pi * u)| := by
  rw [norm_sub_rev, phase]
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * u)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  convert h using 1 <;> push_cast <;> ring

lemma abs_sin_pi_mul_lower {u L : ℝ} (hL : 0 < L)
    (hu0 : L / 2 ≤ |u|) (hu1 : |u| ≤ 1 - L / 2) :
    L ≤ |Real.sin (Real.pi * u)| := by
  have hu_le_one : |u| ≤ 1 := by linarith
  have habs_pi_u : |Real.pi * u| = Real.pi * |u| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hsin_abs : |Real.sin (Real.pi * u)| =
      Real.sin (Real.pi * |u|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi]
    · rw [habs_pi_u]
    · rw [habs_pi_u]
      nlinarith [Real.pi_pos]
  rw [hsin_abs]
  by_cases hu : |u| ≤ 1 / 2
  · have harg0 : 0 ≤ Real.pi * |u| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
    have harg1 : Real.pi * |u| ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin harg0 harg1
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    calc
      L ≤ 2 * |u| := by linarith
      _ = 2 / Real.pi * (Real.pi * |u|) := by field_simp
      _ ≤ Real.sin (Real.pi * |u|) := hs
  · have hu' : 1 / 2 ≤ |u| := le_of_not_ge hu
    have hv0 : 0 ≤ Real.pi * (1 - |u|) := by
      apply mul_nonneg Real.pi_pos.le
      linarith
    have hv1 : Real.pi * (1 - |u|) ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hv0 hv1
    have hrewrite : Real.sin (Real.pi * |u|) =
        Real.sin (Real.pi * (1 - |u|)) := by
      rw [← Real.sin_pi_sub]
      congr 1
      ring
    rw [hrewrite]
    calc
      L ≤ 2 * (1 - |u|) := by linarith
      _ = 2 / Real.pi * (Real.pi * (1 - |u|)) := by
        field_simp
      _ ≤ Real.sin (Real.pi * (1 - |u|)) := hs

lemma phase_separation_of_outside_interval {t a L : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (ha : 0 ≤ a) (hL : 0 < L)
    (haL : a + L ≤ 1) (hout : t ∉ Ico a (a + L)) :
    2 * L ≤ ‖1 - phase 1 (t - (a + L / 2))‖ := by
  have hfar : L / 2 ≤ |t - (a + L / 2)| := by
    simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hout
    rcases hout with hleft | hright
    · exact (show L / 2 ≤ -(t - (a + L / 2)) by linarith).trans
        (neg_le_abs _)
    · exact (show L / 2 ≤ t - (a + L / 2) by linarith).trans
        (le_abs_self _)
  have hnear : |t - (a + L / 2)| ≤ 1 - L / 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2.le]
  rw [norm_one_sub_phase_one]
  nlinarith [abs_sin_pi_mul_lower hL hfar hnear]

lemma exponentialSum_sub_const (x : ℕ → ℝ) (N : ℕ) (h : ℤ) (c : ℝ) :
    exponentialSum (fun j => x j - c) N h =
      phase h (-c) * exponentialSum x N h := by
  classical
  rw [exponentialSum, exponentialSum, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [show x j - c = -c + x j by ring, phase_add_real]

lemma firstFrequencyBound_sub_const {x : ℕ → ℝ} {N H : ℕ} {B : ℝ}
    (hbound : FirstFrequencyBound x N H B) (c : ℝ) :
    FirstFrequencyBound (fun j => x j - c) N H B := by
  intro h h0 hH
  rw [exponentialSum_sub_const, norm_mul, norm_phase, one_mul]
  exact hbound h h0 hH

/-- Number of the first `N` orbit points in the half-open interval
`[a,a+L)`. -/
def cylinderCount (x : ℕ → ℝ) (N : ℕ) (a L : ℝ) : ℕ :=
  ((range N).filter fun j => x j ∈ Set.Ico a (a + L)).card

/-- Signed lower discrepancy of a half-open cylinder.  A value strictly below
the cylinder length is equivalent to positive empirical mass. -/
def cylinderDeficit (x : ℕ → ℝ) (N : ℕ) (a L : ℝ) : ℝ :=
  L - (cylinderCount x N a L : ℝ) / N

lemma sum_shifted_fejerKernel_upper {x : ℕ → ℝ} {N H : ℕ} {a L : ℝ}
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (hL : 0 < L) (haL : a + L ≤ 1) :
    ∑ j ∈ range N, fejerKernel H (x j - (a + L / 2)) ≤
      (cylinderCount x N a L : ℝ) * (H + 1) +
        N * (1 / ((H + 1 : ℝ) * L ^ 2)) := by
  classical
  let A : ℝ := 1 / ((H + 1 : ℝ) * L ^ 2)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  calc
    ∑ j ∈ range N, fejerKernel H (x j - (a + L / 2)) ≤
        ∑ j ∈ range N,
          ((if x j ∈ Set.Ico a (a + L) then (H + 1 : ℝ) else 0) + A) := by
      apply sum_le_sum
      intro j hj
      have hjN : j < N := mem_range.mp hj
      by_cases hmem : x j ∈ Set.Ico a (a + L)
      · simp only [hmem, if_true]
        exact (fejerKernel_le H _).trans (le_add_of_nonneg_right hA)
      · simp only [hmem, if_false, zero_add]
        exact fejerKernel_le_inv_sq hL
          (phase_separation_of_outside_interval (hx j hjN) ha hL haL hmem)
    _ = (cylinderCount x N a L : ℝ) * (H + 1) + N * A := by
      simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
      congr 1
      calc
        ∑ j ∈ range N,
            (if x j ∈ Set.Ico a (a + L) then (H + 1 : ℝ) else 0) =
            ∑ j ∈ range N,
              (if x j ∈ Set.Ico a (a + L) then (1 : ℝ) else 0) *
                (H + 1 : ℝ) := by
          apply sum_congr rfl
          intro j hj
          split <;> simp_all
        _ = (∑ j ∈ range N,
              if x j ∈ Set.Ico a (a + L) then (1 : ℝ) else 0) *
                (H + 1 : ℝ) := by rw [sum_mul]
        _ = (cylinderCount x N a L : ℝ) * (H + 1) := by
          simp [cylinderCount]
    _ = _ := by rfl

/-- A finite Erdos-Turan-style one-sided discrepancy inequality.  Every
quantity is explicit: `N` points, the first `H` positive and negative
frequencies, their common bound `B`, and a cylinder `[a,a+L)`.  The proof
derives the estimate from those finite sums via the Fejer kernel. -/
theorem decimalCylinderDeficit_le_of_firstFrequencyBound
    (x : ℕ → ℝ) (N H : ℕ) (hN : 0 < N) (a L B : ℝ)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (hL : 0 < L) (haL : a + L ≤ 1)
    (hbound : FirstFrequencyBound x N H B) :
    cylinderDeficit x N a L ≤
      L - ((N : ℝ) - H * B -
        N * (1 / ((H + 1 : ℝ) * L ^ 2))) /
          ((N : ℝ) * (H + 1 : ℝ)) := by
  let c : ℝ := a + L / 2
  let A : ℝ := 1 / ((H + 1 : ℝ) * L ^ 2)
  have hlower : (N : ℝ) - H * B ≤
      ∑ j ∈ range N, fejerKernel H (x j - c) :=
    sum_fejerKernel_lower_of_firstFrequencyBound
      (firstFrequencyBound_sub_const hbound c)
  have hupper : ∑ j ∈ range N, fejerKernel H (x j - c) ≤
      (cylinderCount x N a L : ℝ) * (H + 1) + N * A := by
    simpa only [c, A] using
      sum_shifted_fejerKernel_upper (H := H) hx ha hL haL
  have hraw : (N : ℝ) - H * B - N * A ≤
      (cylinderCount x N a L : ℝ) * (H + 1) := by
    linarith
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hM : 0 < (H + 1 : ℝ) := by positivity
  unfold cylinderDeficit
  apply sub_le_sub_left
  apply (div_le_iff₀ (mul_pos hNR hM)).2
  calc
    (N : ℝ) - H * B - N * A ≤
        (cylinderCount x N a L : ℝ) * (H + 1) := hraw
    _ = ((cylinderCount x N a L : ℝ) / N) *
          ((N : ℝ) * (H + 1 : ℝ)) := by
      field_simp

/-- The quantitative coverage certificate extracted from the discrepancy
inequality.  The strict inequality is checkable using only `N`, `H`, `L`, and
the finite exponential-sum bound `B`. -/
theorem decimalCylinder_covered_of_firstFrequencyBound
    (x : ℕ → ℝ) (N H : ℕ) (hN : 0 < N) (a L B : ℝ)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (hL : 0 < L) (haL : a + L ≤ 1)
    (hbound : FirstFrequencyBound x N H B)
    (hcertificate :
      H * B + N * (1 / ((H + 1 : ℝ) * L ^ 2)) < N) :
    ∃ j < N, x j ∈ Set.Ico a (a + L) := by
  have hdisc := decimalCylinderDeficit_le_of_firstFrequencyBound
    x N H hN a L B hx ha hL haL hbound
  have hstrict :
      L - ((N : ℝ) - H * B -
        N * (1 / ((H + 1 : ℝ) * L ^ 2))) /
          ((N : ℝ) * (H + 1 : ℝ)) < L := by
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    have hM : 0 < (H + 1 : ℝ) := by positivity
    apply sub_lt_self
    exact div_pos (by linarith) (mul_pos hNR hM)
  have hdeficit : cylinderDeficit x N a L < L := hdisc.trans_lt hstrict
  have hcount : cylinderCount x N a L ≠ 0 := by
    intro hz
    simp [cylinderDeficit, hz] at hdeficit
  rw [cylinderCount, card_ne_zero] at hcount
  obtain ⟨j, hj⟩ := hcount
  simp only [mem_filter, Finset.mem_range] at hj
  exact ⟨j, hj.1, hj.2⟩

/-- The common length `10^-k` of every `k`-digit decimal cylinder. -/
def decimalCylinderLength (k : ℕ) : ℝ :=
  ((10 : ℝ) ^ k)⁻¹

/-- The left endpoint of the decimal cylinder represented by `s`. -/
def decimalCylinderLeft (s : List (Fin 10)) : ℝ :=
  (Theory.PiDigits.T20.wordValue s : ℝ) / (10 : ℝ) ^ s.length

lemma decimalCylinderLength_pos (k : ℕ) : 0 < decimalCylinderLength k := by
  simp [decimalCylinderLength]

lemma decimalCylinderLeft_nonneg (s : List (Fin 10)) :
    0 ≤ decimalCylinderLeft s := by
  simp [decimalCylinderLeft]
  positivity

lemma decimalCylinderRight_le_one (s : List (Fin 10)) :
    decimalCylinderLeft s + decimalCylinderLength s.length ≤ 1 := by
  have hpow : 0 < (10 : ℝ) ^ s.length := by positivity
  have hv : ((Theory.PiDigits.T20.wordValue s + 1 : ℕ) : ℝ) ≤
      (10 : ℝ) ^ s.length := by
    exact_mod_cast Theory.PiDigits.T20.wordValue_lt_pow_length s
  rw [decimalCylinderLeft, decimalCylinderLength, inv_eq_one_div]
  rw [← add_div]
  push_cast at hv
  exact (div_le_one hpow).2 hv

lemma decimalCylinder_interval (s : List (Fin 10)) :
    Set.Ico (decimalCylinderLeft s)
        (decimalCylinderLeft s + decimalCylinderLength s.length) =
      Set.Ico
        ((Theory.PiDigits.T20.wordValue s : ℝ) / (10 : ℝ) ^ s.length)
        (((Theory.PiDigits.T20.wordValue s + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ s.length) := by
  ext z
  simp only [Set.mem_Ico, decimalCylinderLeft, decimalCylinderLength,
    inv_eq_one_div]
  push_cast
  simp only [add_div]

/-- Named decimal-cylinder coverage theorem.  If the explicit discrepancy
upper bound derived above is strictly below the common cylinder length
`10^-k`, every word of exactly length `k` has a hit among the first `N`
points.  Lists beginning with zero are included without exception. -/
theorem everyLengthKDecimalCylinder_covered_of_finiteExponentialBounds
    (x : ℕ → ℝ) (k H N : ℕ) (hN : 0 < N) (B : ℝ)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (hbound : FirstFrequencyBound x N H B)
    (hstrict :
      decimalCylinderLength k -
          ((N : ℝ) - H * B -
            N * (1 / ((H + 1 : ℝ) * decimalCylinderLength k ^ 2))) /
              ((N : ℝ) * (H + 1 : ℝ)) <
        decimalCylinderLength k) :
    ∀ s : List (Fin 10), s.length = k →
      ∃ j < N,
        x j ∈ Set.Ico
          ((Theory.PiDigits.T20.wordValue s : ℝ) / (10 : ℝ) ^ s.length)
          (((Theory.PiDigits.T20.wordValue s + 1 : ℕ) : ℝ) /
            (10 : ℝ) ^ s.length) := by
  intro s hs
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hM : 0 < (H + 1 : ℝ) := by positivity
  have hcertificate :
      H * B + N *
          (1 / ((H + 1 : ℝ) * decimalCylinderLength k ^ 2)) < N := by
    have hquot : 0 <
        ((N : ℝ) - H * B -
          N * (1 / ((H + 1 : ℝ) * decimalCylinderLength k ^ 2))) /
            ((N : ℝ) * (H + 1 : ℝ)) := by
      linarith
    have hnum := (div_pos_iff.mp hquot)
    rcases hnum with hnum | hnum
    · linarith
    · exfalso
      exact (not_lt_of_ge (mul_pos hNR hM).le) hnum.2
  have hhit := decimalCylinder_covered_of_firstFrequencyBound
    x N H hN (decimalCylinderLeft s) (decimalCylinderLength s.length) B
    hx (decimalCylinderLeft_nonneg s) (decimalCylinderLength_pos s.length)
    (decimalCylinderRight_le_one s) hbound (by simpa [hs] using hcertificate)
  obtain ⟨j, hjN, hj⟩ := hhit
  exact ⟨j, hjN, by simpa only [decimalCylinder_interval] using hj⟩

/-- T20's exact fractional-part orbit for `Real.pi`. -/
def piFractionalOrbit (j : ℕ) : ℝ :=
  Int.fract ((10 : ℝ) ^ j * Real.pi)

lemma piFractionalOrbit_mem_Ico (j : ℕ) :
    piFractionalOrbit j ∈ Set.Ico (0 : ℝ) 1 :=
  Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi j

/-- Conditional specialization to T7's exact floor-based decimal digit
stream.  The displayed bounds on the first `H` nonzero frequencies are
currently unproved for pi.  The conclusion covers every length-`k` list,
including lists with leading zeros, but it does not prove V1 or V3
unconditionally. -/
theorem pi_everyLengthKWord_occurs_of_finiteExponentialBounds
    (k H N : ℕ) (hN : 0 < N) (B : ℝ)
    (hbound :
      ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ H →
        ‖∑ j ∈ range N,
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
              ((piFractionalOrbit j : ℝ) : ℂ))‖ ≤ B)
    (hstrict :
      decimalCylinderLength k -
          ((N : ℝ) - H * B -
            N * (1 / ((H + 1 : ℝ) * decimalCylinderLength k ^ 2))) /
              ((N : ℝ) * (H + 1 : ℝ)) <
        decimalCylinderLength k) :
    ∀ s : List (Fin 10), s.length = k →
      ∃ n < N, ∀ i : ℕ, ∀ hi : i < s.length,
        Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩ := by
  have hfinite : FirstFrequencyBound piFractionalOrbit N H B := by
    intro h h0 hH
    simpa only [exponentialSum, phase] using hbound h h0 hH
  have hcoverage :=
    everyLengthKDecimalCylinder_covered_of_finiteExponentialBounds
      piFractionalOrbit k H N hN B
      (fun j _hj => piFractionalOrbit_mem_Ico j) hfinite hstrict
  intro s hs
  obtain ⟨n, hnN, hn⟩ := hcoverage s hs
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder s
    (piFractionalOrbit n) hn
  refine ⟨n, hnN, ?_⟩
  intro i hi
  have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
    Real.pi Real.pi_pos.le n i
  exact (Theory.PiDigits.T20.decimalDigit_pi (n + i)).symm.trans
    (hshift.symm.trans (hdigits i hi))

end Theory.PiDigits.T27

#print axioms Theory.PiDigits.T27.decimalCylinderDeficit_le_of_firstFrequencyBound
#print axioms Theory.PiDigits.T27.decimalCylinder_covered_of_firstFrequencyBound
#print axioms Theory.PiDigits.T27.everyLengthKDecimalCylinder_covered_of_finiteExponentialBounds
#print axioms Theory.PiDigits.T27.pi_everyLengthKWord_occurs_of_finiteExponentialBounds
