import TheoryLib.PiDigits.T20BaseTenOrbitDensity
import Mathlib.Analysis.Fourier.AddCircle

/-!
# A conditional Weyl target for decimal blocks of pi

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The hypothesis about exponential sums for `Real.pi` below is unproved.  It
imposes equidistribution, which is stronger than the orbit density equivalent
to canonical V1.  Thus this file proves only a conditional implication to V1.
It proves neither canonical V1 nor sibling V3 unconditionally, and it makes no
claim that V1 implies the cancellation hypothesis.
-/

noncomputable section

open scoped ComplexConjugate Real Topology
open Filter Finset Set TopologicalSpace
open MeasureTheory

namespace Theory.PiDigits.T26

/-- The normalized empirical mean of a continuous test function along a
sequence in the unit additive circle. -/
def circleEmpiricalMean (u : ℕ → UnitAddCircle)
    (f : C(UnitAddCircle, ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ range N, f (u k)

/-- Weyl cancellation for every nonzero Fourier character of a circle-valued
sequence. -/
def CircleWeylCancellation (u : ℕ → UnitAddCircle) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto (fun N => circleEmpiricalMean u (fourier h) N)
      atTop (𝓝 0)

/-- The Haar mean of a continuous complex-valued function on the unit circle. -/
def circleHaarMean (f : C(UnitAddCircle, ℂ)) : ℂ :=
  ∫ z, f z ∂AddCircle.haarAddCircle

lemma integral_fourier_unit (h : ℤ) :
    circleHaarMean (fourier h : C(UnitAddCircle, ℂ)) =
      if h = 0 then 1 else 0 := by
  classical
  by_cases hh : h = 0
  · subst h
    simp [circleHaarMean]
  · simp only [circleHaarMean, if_neg hh]
    exact integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hh (by norm_num) :
        ∀ x : UnitAddCircle,
          fourier h (x + ↑((1 : ℝ) / 2 / h)) =
            -fourier h x)

lemma circleEmpiricalMean_fourier_zero_tendsto (u : ℕ → UnitAddCircle) :
    Tendsto
      (fun N => circleEmpiricalMean u (fourier 0) N)
      atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [circleEmpiricalMean, fourier_zero, sum_const, card_range,
    nsmul_eq_mul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  simpa using (inv_mul_cancel₀ hN0).symm

lemma norm_circleEmpiricalMean_sub_le (u : ℕ → UnitAddCircle)
    (f g : C(UnitAddCircle, ℂ)) (N : ℕ) :
    ‖circleEmpiricalMean u f N - circleEmpiricalMean u g N‖ ≤ ‖f - g‖ := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [circleEmpiricalMean]
  · rw [circleEmpiricalMean, circleEmpiricalMean, ← mul_sub, ← sum_sub_distrib]
    have hsum :
        ‖∑ k ∈ range N, (f (u k) - g (u k))‖ ≤ (N : ℝ) * ‖f - g‖ := by
      calc
        ‖∑ k ∈ range N, (f (u k) - g (u k))‖ ≤
            ∑ k ∈ range N, ‖f (u k) - g (u k)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range N, ‖f - g‖ := by
          exact sum_le_sum fun k _ => by
            simpa only [ContinuousMap.sub_apply] using
              (f - g).norm_coe_le_norm (u k)
        _ = (N : ℝ) * ‖f - g‖ := by simp
    rw [norm_mul, norm_inv, norm_natCast]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    calc
      (N : ℝ)⁻¹ * ‖∑ k ∈ range N, (f (u k) - g (u k))‖ ≤
          (N : ℝ)⁻¹ * ((N : ℝ) * ‖f - g‖) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = ((N : ℝ)⁻¹ * (N : ℝ)) * ‖f - g‖ := by rw [mul_assoc]
      _ = ‖f - g‖ := by rw [inv_mul_cancel₀ hNR, one_mul]

lemma continuousMap_integrable_haar (f : C(UnitAddCircle, ℂ)) :
    Integrable f AddCircle.haarAddCircle := by
  apply Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
  exact ae_of_all _ fun z => f.norm_coe_le_norm z

lemma norm_circleHaarMean_sub_le (f g : C(UnitAddCircle, ℂ)) :
    ‖circleHaarMean f - circleHaarMean g‖ ≤ ‖f - g‖ := by
  rw [circleHaarMean, circleHaarMean,
    ← integral_sub (continuousMap_integrable_haar f) (continuousMap_integrable_haar g)]
  simpa using norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle)
    (ae_of_all _ fun z => (f - g).norm_coe_le_norm z)

lemma circleEmpiricalMean_add (u : ℕ → UnitAddCircle)
    (f g : C(UnitAddCircle, ℂ)) (N : ℕ) :
    circleEmpiricalMean u (f + g) N =
      circleEmpiricalMean u f N + circleEmpiricalMean u g N := by
  simp only [circleEmpiricalMean, ContinuousMap.add_apply, sum_add_distrib]
  ring

lemma circleEmpiricalMean_smul (u : ℕ → UnitAddCircle) (c : ℂ)
    (f : C(UnitAddCircle, ℂ)) (N : ℕ) :
    circleEmpiricalMean u (c • f) N = c * circleEmpiricalMean u f N := by
  simp only [circleEmpiricalMean, ContinuousMap.smul_apply, smul_eq_mul, ← mul_sum]
  ring

lemma circleHaarMean_add (f g : C(UnitAddCircle, ℂ)) :
    circleHaarMean (f + g) = circleHaarMean f + circleHaarMean g := by
  simpa only [circleHaarMean, ContinuousMap.add_apply] using
    integral_add (continuousMap_integrable_haar f) (continuousMap_integrable_haar g)

lemma circleHaarMean_smul (c : ℂ) (f : C(UnitAddCircle, ℂ)) :
    circleHaarMean (c • f) = c * circleHaarMean f := by
  unfold circleHaarMean
  change (∫ z, c * f z ∂AddCircle.haarAddCircle) =
    c * ∫ z, f z ∂AddCircle.haarAddCircle
  exact integral_const_mul c f

/-- The Fourier/Stone-Weierstrass form of Weyl's criterion needed here:
cancellation of all nonzero characters gives convergence of every continuous
test-function mean to normalized Haar mean. -/
theorem circleWeylCancellation_implies_continuous_equidistribution
    (u : ℕ → UnitAddCircle) (hu : CircleWeylCancellation u)
    (f : C(UnitAddCircle, ℂ)) :
    Tendsto (fun N => circleEmpiricalMean u f N) atTop
      (𝓝 (circleHaarMean f)) := by
  classical
  have hfourier (h : ℤ) :
      Tendsto (fun N => circleEmpiricalMean u (fourier h) N) atTop
        (𝓝 (circleHaarMean (fourier h))) := by
    by_cases hh : h = 0
    · subst h
      simpa [integral_fourier_unit] using circleEmpiricalMean_fourier_zero_tendsto u
    · simpa [integral_fourier_unit, hh] using hu h hh
  have hspan : ∀ g ∈ Submodule.span ℂ (range (fourier : ℤ → C(UnitAddCircle, ℂ))),
      Tendsto (fun N => circleEmpiricalMean u g N) atTop
        (𝓝 (circleHaarMean g)) := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ =>
      Tendsto (fun N => circleEmpiricalMean u g N) atTop
        (𝓝 (circleHaarMean g))) ?_ ?_ ?_ ?_ hg
    · intro g hg
      obtain ⟨h, rfl⟩ := hg
      exact hfourier h
    · simp [circleEmpiricalMean, circleHaarMean]
    · intro g q _ _ hg hq
      simpa only [circleEmpiricalMean_add, circleHaarMean_add] using hg.add hq
    · intro c g _ hg
      simpa only [circleEmpiricalMean_smul, circleHaarMean_smul] using hg.const_mul c
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hfmem : f ∈ (Submodule.span ℂ
      (range (fourier : ℤ → C(UnitAddCircle, ℂ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hfmem
  obtain ⟨g, hgspan, hgf⟩ := hfmem (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hspan g hgspan) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm] at hgf ⊢
  have hN' := hN n hn
  rw [dist_eq_norm] at hN'
  have hfg : ‖f - g‖ < ε / 3 := by simpa [norm_sub_rev] using hgf
  have havg :
      ‖circleEmpiricalMean u f n - circleEmpiricalMean u g n‖ < ε / 3 :=
    (norm_circleEmpiricalMean_sub_le u f g n).trans_lt hfg
  have hmean : ‖circleHaarMean g - circleHaarMean f‖ < ε / 3 :=
    (norm_circleHaarMean_sub_le g f).trans_lt (by
      simpa [norm_sub_rev] using hfg)
  calc
    ‖circleEmpiricalMean u f n - circleHaarMean f‖ ≤
        ‖circleEmpiricalMean u f n - circleEmpiricalMean u g n‖ +
          ‖circleEmpiricalMean u g n - circleHaarMean g‖ +
            ‖circleHaarMean g - circleHaarMean f‖ := by
      calc
        _ = ‖(circleEmpiricalMean u f n - circleEmpiricalMean u g n) +
              ((circleEmpiricalMean u g n - circleHaarMean g) +
                (circleHaarMean g - circleHaarMean f))‖ := by ring_nf
        _ ≤ ‖circleEmpiricalMean u f n - circleEmpiricalMean u g n‖ +
              ‖(circleEmpiricalMean u g n - circleHaarMean g) +
                (circleHaarMean g - circleHaarMean f)‖ := norm_add_le _ _
        _ ≤ ‖circleEmpiricalMean u f n - circleEmpiricalMean u g n‖ +
              (‖circleEmpiricalMean u g n - circleHaarMean g‖ +
                ‖circleHaarMean g - circleHaarMean f‖) :=
          add_le_add le_rfl (norm_add_le _ _)
        _ = ‖circleEmpiricalMean u f n - circleEmpiricalMean u g n‖ +
              ‖circleEmpiricalMean u g n - circleHaarMean g‖ +
                ‖circleHaarMean g - circleHaarMean f‖ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- Circle Weyl cancellation forces the sequence to have dense range. -/
theorem circleWeylCancellation_implies_denseRange
    (u : ℕ → UnitAddCircle) (hu : CircleWeylCancellation u) :
    DenseRange u := by
  rw [Metric.denseRange_iff]
  intro y ε hε
  by_contra hnear
  push Not at hnear
  let b : UnitAddCircle → ℝ := fun z => max 0 (ε - dist y z)
  have hbcont : Continuous b := by
    exact continuous_const.max (continuous_const.sub (continuous_const.dist continuous_id))
  have hbnonneg : 0 ≤ b := fun z => le_max_left _ _
  have hby : b y ≠ 0 := by
    dsimp [b]
    rw [dist_self, sub_zero, max_eq_right hε.le]
    exact hε.ne'
  have hbcomp : HasCompactSupport b :=
    isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have hbpos : 0 < ∫ z, b z ∂AddCircle.haarAddCircle :=
    hbcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hbcomp hbnonneg hby
  let f : C(UnitAddCircle, ℂ) :=
    ⟨fun z => (b z : ℂ), Complex.continuous_ofReal.comp hbcont⟩
  have hfu (k : ℕ) : f (u k) = 0 := by
    have hk : ε - dist y (u k) ≤ 0 := sub_nonpos.mpr (hnear k)
    simp [f, b, max_eq_left hk]
  have havgzero (N : ℕ) : circleEmpiricalMean u f N = 0 := by
    simp [circleEmpiricalMean, hfu]
  have hlim := circleWeylCancellation_implies_continuous_equidistribution u hu f
  have hlimzero : Tendsto (fun _N : ℕ => (0 : ℂ)) atTop
      (𝓝 (circleHaarMean f)) :=
    hlim.congr' (Filter.Eventually.of_forall fun N => havgzero N)
  have hmean_zero : circleHaarMean f = 0 :=
    tendsto_nhds_unique hlimzero tendsto_const_nhds
  have hmean_ne : circleHaarMean f ≠ 0 := by
    unfold circleHaarMean f
    change (∫ z, (b z : ℂ) ∂AddCircle.haarAddCircle) ≠ 0
    rw [integral_complex_ofReal]
    exact_mod_cast hbpos.ne'
  exact hmean_ne hmean_zero

/-- Explicit real Weyl cancellation.  The phase is `2 * pi * i * h * x_k`. -/
def RealWeylCancellation (x : ℕ → ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto
      (fun N : ℕ =>
        (N : ℂ)⁻¹ * ∑ k ∈ range N,
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (x k : ℂ)))
      atTop (𝓝 0)

lemma realWeylCancellation_iff_circle (x : ℕ → ℝ) :
    RealWeylCancellation x ↔
      CircleWeylCancellation (fun k => (x k : UnitAddCircle)) := by
  constructor
  · intro hx h hh
    simpa only [circleEmpiricalMean, fourier_coe_apply, div_one,
      Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_one] using hx h hh
  · intro hx h hh
    simpa only [circleEmpiricalMean, fourier_coe_apply, div_one,
      Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_one] using hx h hh

/-- Away from the endpoints of `[0,1]`, a sufficiently short circle distance
to `y` is the ordinary distance from the fractional representative to `y`. -/
lemma abs_fract_sub_lt_of_circle_dist_lt {x y r : ℝ}
    (hyr0 : r < y) (hyr1 : r < 1 - y)
    (hxy : dist (x : UnitAddCircle) (y : UnitAddCircle) < r) :
    |Int.fract x - y| < r := by
  have hmem : Int.fract x ∈
      ((fun t : ℝ => (t : UnitAddCircle)) ⁻¹'
        Metric.closedBall (y : UnitAddCircle) r) := by
    change dist ((Int.fract x : ℝ) : UnitAddCircle) (y : UnitAddCircle) ≤ r
    rw [AddCircle.coe_fract]
    exact hxy.le
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hmem
  simp only [mem_iUnion] at hmem
  obtain ⟨z : ℤ, hz⟩ := hmem
  have hz' : |Int.fract x - (y + (z : ℝ))| ≤ r := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, zsmul_eq_mul, mul_one] using hz
  have hz0 : z = 0 := by
    by_contra hz_ne
    rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz_ne with hzneg | hzpos
    · have hlarge : r < Int.fract x - (y + (z : ℝ)) := by
        have hfract0 := Int.fract_nonneg x
        nlinarith
      have habs : r < |Int.fract x - (y + (z : ℝ))| :=
        hlarge.trans_le (le_abs_self _)
      exact (not_lt_of_ge hz') habs
    · have hlarge : r < (y + (z : ℝ)) - Int.fract x := by
        have hfract1 := Int.fract_lt_one x
        nlinarith
      have habs : r < |Int.fract x - (y + (z : ℝ))| := by
        rw [abs_sub_comm]
        exact hlarge.trans_le (le_abs_self _)
      exact (not_lt_of_ge hz') habs
  subst z
  simp only [Int.cast_zero, add_zero] at hz'
  have hrhalf : |Int.fract x - y| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one]
    exact hz'.trans (by linarith)
  have hnorm : ‖((Int.fract x - y : ℝ) : UnitAddCircle)‖ =
      |Int.fract x - y| :=
    (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2 hrhalf
  rw [← AddCircle.coe_fract x, dist_eq_norm,
    ← QuotientAddGroup.mk_sub, hnorm] at hxy
  exact hxy

/-- Generic cancellation-to-density bridge in the real fractional-part
normalization used by T20. -/
theorem realWeylCancellation_implies_fractOrbitDense
    (x : ℕ → ℝ) (hx : RealWeylCancellation x) :
    ∀ y : ℝ, y ∈ Icc (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, |Int.fract (x k) - y| < ε := by
  intro y hy ε hε
  let r : ℝ := min (ε / 4) (1 / 8)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hre : r < ε := (min_le_left _ _).trans_lt (by linarith)
  have hre4 : r ≤ ε / 4 := min_le_left _ _
  let center : ℝ := max r (min (1 - r) y)
  have hcenter0 : r ≤ center := le_max_left _ _
  have hcenter1 : center ≤ 1 - r := by
    dsimp [center]
    apply max_le
    · linarith [show r ≤ 1 / 8 from min_le_right _ _]
    · exact min_le_left _ _
  have hcenter_mem : center ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
  have hycenter : |center - y| ≤ r := by
    rw [abs_le]
    constructor
    · have hlower : y - r ≤ center := by
        dsimp [center]
        exact (le_min (by linarith [hy.2]) (by linarith)).trans (le_max_right _ _)
      linarith
    · have hupper : center ≤ y + r := by
        dsimp [center]
        exact max_le (by linarith [hy.1])
          ((min_le_right (1 - r) y).trans (by linarith))
      linarith
  have hcircle := circleWeylCancellation_implies_denseRange
    (fun k => (x k : UnitAddCircle))
    ((realWeylCancellation_iff_circle x).mp hx)
  rw [Metric.denseRange_iff] at hcircle
  obtain ⟨k, hk⟩ := hcircle (center : UnitAddCircle) (r / 2) (by positivity)
  have hkreal : |Int.fract (x k) - center| < r / 2 :=
    abs_fract_sub_lt_of_circle_dist_lt
      (by linarith) (by linarith) (by simpa [dist_comm] using hk)
  refine ⟨k, ?_⟩
  calc
    |Int.fract (x k) - y| ≤
        |Int.fract (x k) - center| + |center - y| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (Int.fract (x k) - center) (center - y)
    _ < r / 2 + r := add_lt_add_of_lt_of_le hkreal hycenter
    _ < ε := by linarith

/-- The explicit, currently unproved finite-sum hypothesis for the base-ten
orbit of `Real.pi`. -/
def PiBaseTenWeylCancellation : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto
      (fun N : ℕ =>
        (N : ℂ)⁻¹ * ∑ k ∈ range N,
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
              (((10 : ℝ) ^ k * Real.pi : ℝ) : ℂ)))
      atTop (𝓝 0)

/-- Exact conditional specialization through T20 to T7's canonical V1.
The hypothesis is open; this theorem is not an unconditional proof of V1. -/
theorem pi_baseTen_weylCancellation_implies_canonicalV1
    (hcancel :
      ∀ h : ℤ, h ≠ 0 →
        Tendsto
          (fun N : ℕ =>
            (N : ℂ)⁻¹ * ∑ k ∈ range N,
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
                  (((10 : ℝ) ^ k * Real.pi : ℝ) : ℂ)))
          atTop (𝓝 0)) :
    Theory.PiDigits.V1 := by
  have hx : RealWeylCancellation (fun k => (10 : ℝ) ^ k * Real.pi) := hcancel
  apply Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense.mpr
  simpa only using realWeylCancellation_implies_fractOrbitDense
    (fun k => (10 : ℝ) ^ k * Real.pi) hx

end Theory.PiDigits.T26

#print axioms Theory.PiDigits.T26.circleWeylCancellation_implies_continuous_equidistribution
#print axioms Theory.PiDigits.T26.circleWeylCancellation_implies_denseRange
#print axioms Theory.PiDigits.T26.realWeylCancellation_implies_fractOrbitDense
#print axioms Theory.PiDigits.T26.pi_baseTen_weylCancellation_implies_canonicalV1
