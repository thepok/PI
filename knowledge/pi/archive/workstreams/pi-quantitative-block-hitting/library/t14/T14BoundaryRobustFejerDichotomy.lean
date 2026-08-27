import TheoryLib.PiQuantitativeBlockHitting.T8PiNoV1NaturalScaleResonance
import TheoryLib.PiDecimalFactorComplexity.T10PiWeightedFourierReduction
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# T14: boundary-robust Fejer dichotomy

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This is a necessary-only obstruction. It supplies neither an upper bound for
the circular boundary count nor an upper bound for the aggregated complex
exponential sums of the fixed pi orbit. It therefore neither proves nor
refutes canonical C1.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset Set

namespace Theory.PiDigits.BoundaryRobustFejerDichotomy

abbrev phase := Theory.PiDigits.T27.phase
abbrev exponentialSum := Theory.PiDigits.T27.exponentialSum
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-- Intrinsic distance on `R/Z`, written using all integer translates. -/
def circularDistance (x y : ℝ) : ℝ :=
  sInf (Set.range fun z : ℤ => |x - y - z|)

lemma circularDistance_le_abs_sub_int (x y : ℝ) (z : ℤ) :
    circularDistance x y ≤ |x - y - z| := by
  unfold circularDistance
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨w, rfl⟩; exact abs_nonneg _⟩
  · exact ⟨z, rfl⟩

/-- The left endpoint of the `a`th `q`-adic cylinder. -/
def cylinderLeft (q a : ℕ) : ℝ := (a : ℝ) / q

/-- The right endpoint, interpreted modulo one by `circularDistance`. -/
def cylinderRight (q a : ℕ) : ℝ := ((a + 1 : ℕ) : ℝ) / q

/-- Membership of a canonical `[0,1)` representative in the half-open
`q`-adic cylinder. -/
def inCylinder (q a : ℕ) (x : ℝ) : Prop :=
  x ∈ Set.Ico (cylinderLeft q a) (cylinderRight q a)

/-- Number of indexed sample points in a half-open cylinder. -/
noncomputable def cylinderCount (x : ℕ → ℝ) (N q a : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n => inCylinder q a (x n)).card

/-- Number of indexed samples in the circular `delta`-neighborhood of either
topological boundary point. Repeated values retain their multiplicity. -/
noncomputable def twoBoundaryCount
    (x : ℕ → ℝ) (N q a : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact ((range N).filter fun n =>
    circularDistance (x n) (cylinderLeft q a) < δ ∨
      circularDistance (x n) (cylinderRight q a) < δ).card

/-- All nonzero signed frequencies with absolute value at most `M`. -/
def signedFrequencies (M : ℕ) : Finset ℤ :=
  (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter fun h => h ≠ 0

/-- All signed frequencies with absolute value at most `M`, including zero. -/
def signedFrequenciesZero (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- The aggregated triangular Fejer coefficient `1-|h|/(M+1)`. -/
def triangularCoefficient (M : ℕ) (h : ℤ) : ℝ :=
  1 - (h.natAbs : ℝ) / (M + 1 : ℝ)

/-- Absolute value of the Fourier coefficient of a length `1/q` cylinder,
including the triangular Fejer multiplier. -/
def fejerCylinderWeight (q M : ℕ) (h : ℤ) : ℝ :=
  triangularCoefficient M h *
    |Real.sin (Real.pi * (h : ℝ) / q)| /
      (Real.pi * (h.natAbs : ℝ))

/-- The signed complex Fourier coefficient of the Fejer-smoothed cylinder. -/
def fejerCylinderCoefficient (q a M : ℕ) (h : ℤ) : ℂ :=
  ((triangularCoefficient M h *
      (Real.sin (Real.pi * (h : ℝ) / q) /
        (Real.pi * (h : ℝ)))) : ℂ) *
    phase (-h) (((a : ℝ) + 1 / 2) / q)

/-- T13's sum of complex moduli of ordinary signed-frequency exponential
sums, with one aggregated coefficient for each `h`. -/
def aggregatedFourierSum (x : ℕ → ℝ) (N q M : ℕ) : ℝ :=
  ∑ h ∈ signedFrequencies M,
    fejerCylinderWeight q M h * ‖exponentialSum x N h‖

/-- The periodic half-open cylinder indicator. -/
noncomputable def cylinderIndicator (q a : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if inCylinder q a (Int.fract x) then 1 else 0

/-- Fejer convolution of the periodic cylinder indicator over one period. -/
def fejerApproximation (q a M : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    fejerKernel M t * cylinderIndicator q a (x - t)

/-- Sum of the Fejer approximants over an indexed sample. -/
def fejerEstimator (x : ℕ → ℝ) (N q a M : ℕ) : ℂ :=
  ((∑ n ∈ range N, fejerApproximation q a M (x n) : ℝ) : ℂ)

theorem cylinderIndicator_measurable (q a : ℕ) :
    Measurable (cylinderIndicator q a) := by
  classical
  unfold cylinderIndicator inCylinder
  apply Measurable.ite
  · exact measurableSet_Ico.preimage measurable_fract
  · exact measurable_const
  · exact measurable_const

lemma cylinderIndicator_nonneg (q a : ℕ) (x : ℝ) :
    0 ≤ cylinderIndicator q a x := by
  classical
  unfold cylinderIndicator
  split <;> norm_num

lemma cylinderIndicator_le_one (q a : ℕ) (x : ℝ) :
    cylinderIndicator q a x ≤ 1 := by
  classical
  unfold cylinderIndicator
  split <;> norm_num

lemma fejerIntegrand_intervalIntegrable
    (q a M : ℕ) (x b c : ℝ) :
    IntervalIntegrable
      (fun t => fejerKernel M t * cylinderIndicator q a (x - t))
      MeasureTheory.volume b c := by
  rw [intervalIntegrable_iff]
  apply MeasureTheory.IntegrableOn.of_bound
  · exact (MeasureTheory.measure_mono Set.uIoc_subset_uIcc).trans_lt
      isCompact_uIcc.measure_lt_top
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact
        (DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M).measurable
    · exact (cylinderIndicator_measurable q a).comp
        (measurable_const.sub measurable_id)
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Theory.PiDigits.T27.fejerKernel_nonneg M t)
      (cylinderIndicator_nonneg q a (x - t)))]
    calc
      fejerKernel M t * cylinderIndicator q a (x - t) ≤
          fejerKernel M t * 1 :=
        mul_le_mul_of_nonneg_left (cylinderIndicator_le_one q a (x - t))
          (Theory.PiDigits.T27.fejerKernel_nonneg M t)
      _ ≤ M + 1 := by simpa using Theory.PiDigits.T27.fejerKernel_le M t

lemma phaseIndicator_intervalIntegrable
    (q a : ℕ) (h : ℤ) (b c : ℝ) :
    IntervalIntegrable
      (fun y => phase h y * (cylinderIndicator q a y : ℂ))
      MeasureTheory.volume b c := by
  rw [intervalIntegrable_iff]
  apply MeasureTheory.IntegrableOn.of_bound
  · exact (MeasureTheory.measure_mono Set.uIoc_subset_uIcc).trans_lt
      isCompact_uIcc.measure_lt_top
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · unfold phase Theory.PiDigits.T27.phase
      fun_prop
    · exact Complex.measurable_ofReal.comp (cylinderIndicator_measurable q a)
  · filter_upwards with y
    rw [norm_mul, Theory.PiDigits.T27.norm_phase, one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cylinderIndicator_nonneg q a y)]
    exact cylinderIndicator_le_one q a y

lemma shiftedPhaseIndicator_intervalIntegrable
    (q a : ℕ) (h : ℤ) (x b c : ℝ) :
    IntervalIntegrable
      (fun t => phase h t * (cylinderIndicator q a (x - t) : ℂ))
      MeasureTheory.volume b c := by
  rw [intervalIntegrable_iff]
  apply MeasureTheory.IntegrableOn.of_bound
  · exact (MeasureTheory.measure_mono Set.uIoc_subset_uIcc).trans_lt
      isCompact_uIcc.measure_lt_top
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · unfold phase Theory.PiDigits.T27.phase
      fun_prop
    · exact Complex.measurable_ofReal.comp
        ((cylinderIndicator_measurable q a).comp
          (measurable_const.sub measurable_id))
  · filter_upwards with t
    rw [norm_mul, Theory.PiDigits.T27.norm_phase, one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cylinderIndicator_nonneg q a (x - t))]
    exact cylinderIndicator_le_one q a (x - t)

lemma mem_signedFrequencies {M : ℕ} {h : ℤ} :
    h ∈ signedFrequencies M ↔ h ≠ 0 ∧ h.natAbs ≤ M := by
  classical
  simp only [signedFrequencies, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hzero⟩
    refine ⟨hzero, ?_⟩
    by_cases hh : 0 ≤ h
    · have hcast : (h.natAbs : ℤ) = h := Int.natAbs_of_nonneg hh
      exact_mod_cast (show (h.natAbs : ℤ) ≤ M by simpa [hcast] using hu)
    · have hh' : h ≤ 0 := le_of_not_ge hh
      have hcast : (h.natAbs : ℤ) = -h := Int.ofNat_natAbs_of_nonpos hh'
      exact_mod_cast (show (h.natAbs : ℤ) ≤ M by rw [hcast]; omega)
  · rintro ⟨hzero, habs⟩
    refine ⟨?_, hzero⟩
    have habsZ : (h.natAbs : ℤ) ≤ M := by exact_mod_cast habs
    by_cases hh : 0 ≤ h
    · rw [Int.natAbs_of_nonneg hh] at habsZ
      constructor <;> omega
    · have hh' : h ≤ 0 := le_of_not_ge hh
      rw [Int.ofNat_natAbs_of_nonpos hh'] at habsZ
      constructor <;> omega

lemma mem_signedFrequenciesZero {M : ℕ} {h : ℤ} :
    h ∈ signedFrequenciesZero M ↔ h.natAbs ≤ M := by
  simp only [signedFrequenciesZero, Finset.mem_Icc]
  constructor
  · rintro ⟨hl, hu⟩
    by_cases hh : 0 ≤ h
    · have hcast : (h.natAbs : ℤ) = h := Int.natAbs_of_nonneg hh
      exact_mod_cast (show (h.natAbs : ℤ) ≤ M by rw [hcast]; exact hu)
    · have hh' : h ≤ 0 := le_of_not_ge hh
      have hcast : (h.natAbs : ℤ) = -h := Int.ofNat_natAbs_of_nonpos hh'
      exact_mod_cast (show (h.natAbs : ℤ) ≤ M by rw [hcast]; omega)
  · intro habs
    have habsZ : (h.natAbs : ℤ) ≤ M := by exact_mod_cast habs
    by_cases hh : 0 ≤ h
    · rw [Int.natAbs_of_nonneg hh] at habsZ
      constructor <;> omega
    · have hh' : h ≤ 0 := le_of_not_ge hh
      rw [Int.ofNat_natAbs_of_nonpos hh'] at habsZ
      constructor <;> omega

lemma triangularCoefficient_nonneg {M : ℕ} {h : ℤ}
    (hh : h.natAbs ≤ M) : 0 ≤ triangularCoefficient M h := by
  have hhR : (h.natAbs : ℝ) ≤ M := by exact_mod_cast hh
  unfold triangularCoefficient
  rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < M + 1)]
  linarith

lemma fejerKernel_eq_complexDoubleSum (M : ℕ) (x : ℝ) :
    (fejerKernel M x : ℂ) =
      (M + 1 : ℂ)⁻¹ *
        ∑ r ∈ range (M + 1), ∑ s ∈ range (M + 1),
          phase ((s : ℤ) - (r : ℤ)) x := by
  classical
  have hsquare :
      ((‖Theory.PiDigits.T27.dirichletKernel M x‖ ^ 2 : ℝ) : ℂ) =
        ∑ r ∈ range (M + 1), ∑ s ∈ range (M + 1),
          phase ((s : ℤ) - (r : ℤ)) x := by
    rw [← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self]
    simp only [Theory.PiDigits.T27.dirichletKernel, map_sum]
    rw [sum_mul]
    apply sum_congr rfl
    intro r hr
    rw [mul_sum]
    apply sum_congr rfl
    intro s hs
    exact Theory.PiDigits.T27.phase_sub (r : ℤ) (s : ℤ) x
  unfold fejerKernel Theory.PiDigits.T27.fejerKernel
  rw [Complex.ofReal_div, hsquare]
  push_cast
  ring

/-- Complex aggregated expansion of the Fejer kernel. Ordered pairs occur only
inside the proof; the theorem statement has one term per signed frequency. -/
theorem fejerKernel_eq_aggregated (M : ℕ) (x : ℝ) :
    (fejerKernel M x : ℂ) =
      ∑ h ∈ signedFrequenciesZero M,
        (triangularCoefficient M h : ℂ) * phase h x := by
  classical
  rw [fejerKernel_eq_complexDoubleSum]
  let S : Finset (ℕ × ℕ) := range (M + 1) ×ˢ range (M + 1)
  let g : ℕ × ℕ → ℤ := fun rs => (rs.2 : ℤ) - (rs.1 : ℤ)
  have hmaps : ∀ rs ∈ S, g rs ∈ signedFrequenciesZero M := by
    intro rs hrs
    rw [mem_signedFrequenciesZero]
    simp only [S, Finset.mem_product, Finset.mem_range] at hrs
    simp only [g]
    omega
  have hgroup :
      ∑ r ∈ range (M + 1), ∑ s ∈ range (M + 1),
          phase ((s : ℤ) - (r : ℤ)) x =
        ∑ h ∈ signedFrequenciesZero M,
          ((DecimalFactorComplexity.WeightedFourierReduction.doubleFrequencyFiber
              M h).card : ℂ) * phase h x := by
    calc
      _ = ∑ rs ∈ S, phase (g rs) x := by
        simp only [S, g, sum_product]
      _ = ∑ h ∈ signedFrequenciesZero M,
          ∑ rs ∈ S with g rs = h, phase (g rs) x := by
        exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ h ∈ signedFrequenciesZero M,
          ((DecimalFactorComplexity.WeightedFourierReduction.doubleFrequencyFiber
              M h).card : ℂ) * phase h x := by
        apply sum_congr rfl
        intro h hh
        have hfiber : S.filter (fun rs => g rs = h) =
            DecimalFactorComplexity.WeightedFourierReduction.doubleFrequencyFiber M h := by
          rfl
        calc
          (∑ rs ∈ S with g rs = h, phase (g rs) x) =
              ∑ _rs ∈ S.filter (fun rs => g rs = h), phase h x := by
            apply sum_congr rfl
            intro rs hrs
            rw [(Finset.mem_filter.mp hrs).2]
          _ = ((S.filter (fun rs => g rs = h)).card : ℂ) * phase h x := by
            simp only [Finset.sum_const, nsmul_eq_mul]
          _ = _ := by rw [hfiber]
  rw [hgroup]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro h hh
  rw [← mul_assoc]
  congr 1
  rw [DecimalFactorComplexity.WeightedFourierReduction.card_doubleFrequencyFiber
    (mem_signedFrequenciesZero.mp hh)]
  have hle : h.natAbs ≤ M + 1 :=
    (mem_signedFrequenciesZero.mp hh).trans (Nat.le_succ M)
  rw [Nat.cast_sub hle]
  unfold triangularCoefficient
  push_cast
  have hpos : (M + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
  field_simp

lemma integral_phase_period (h : ℤ) :
    (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), phase h t) =
      if h = 0 then 1 else 0 := by
  have hpre := UnitAddCircle.intervalIntegral_preimage
    (-1 / 2 : ℝ) (fourier h)
  have hhaar := Theory.PiDigits.T26.integral_fourier_unit h
  unfold Theory.PiDigits.T26.circleHaarMean at hhaar
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hpre
  simp only [ENNReal.ofReal_one, one_smul, add_comm, neg_div] at hpre
  norm_num at hpre
  calc
    (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), phase h t) =
        ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (t : ℂ)) := by
      rfl
    _ = ∫ z : UnitAddCircle, fourier h z ∂AddCircle.haarAddCircle := by
      convert hpre using 1 <;> norm_num
    _ = if h = 0 then 1 else 0 := hhaar

/-- The normalized Fejer kernel has mass one on a full period. -/
theorem integral_fejerKernel_period (M : ℕ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), fejerKernel M t = 1 := by
  have hcomplex :
      (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (fejerKernel M t : ℂ)) = 1 := by
    rw [intervalIntegral.integral_congr
      (fun t _ => fejerKernel_eq_aggregated M t)]
    rw [intervalIntegral.integral_finsetSum]
    · calc
        (∑ h ∈ signedFrequenciesZero M,
            ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
              (triangularCoefficient M h : ℂ) * phase h t) =
            ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
              (triangularCoefficient M 0 : ℂ) * phase 0 t := by
          apply Finset.sum_eq_single 0
          · intro h hh hzero
            rw [intervalIntegral.integral_const_mul, integral_phase_period,
              if_neg hzero, mul_zero]
          · simp [signedFrequenciesZero]
        _ = 1 := by
          rw [intervalIntegral.integral_const_mul, integral_phase_period]
          simp [triangularCoefficient]
    · intro h hh
      apply IntervalIntegrable.const_mul
      apply Continuous.intervalIntegrable
      unfold phase Theory.PiDigits.T27.phase
      fun_prop
  have hre := congrArg Complex.re hcomplex
  have hint : IntervalIntegrable
      (fun t : ℝ => (fejerKernel M t : ℂ)) MeasureTheory.volume
        (-1 / 2) (1 / 2) := by
    apply Continuous.intervalIntegrable
    have hk :=
      DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M
    fun_prop
  change (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    Complex.re ((fejerKernel M t : ℝ) : ℂ)) = 1
  have hmap := Complex.reCLM.intervalIntegral_comp_comm hint
  simp only [Complex.reCLM_apply] at hmap
  rw [hmap]
  simpa using hre

/-- Exact nonzero Fourier coefficient of a half-open `q`-adic cylinder. -/
theorem integral_cylinder_phase (q a : ℕ) (h : ℤ)
    (hq : 0 < q) (hzero : h ≠ 0) :
    (∫ y in cylinderLeft q a..cylinderRight q a, phase (-h) y) =
      phase (-h) (((a : ℝ) + 1 / 2) / q) *
        ((Real.sin (Real.pi * (h : ℝ) / q) /
          (Real.pi * (h : ℝ)) : ℝ) : ℂ) := by
  set c : ℝ := ((a : ℝ) + 1 / 2) / q
  have hL : cylinderLeft q a = c - 1 / (2 * (q : ℝ)) := by
    unfold cylinderLeft c; push_cast; ring
  have hR : cylinderRight q a = c + 1 / (2 * (q : ℝ)) := by
    unfold cylinderRight c; push_cast; ring
  rw [hL, hR]
  have hfact : ∀ y : ℝ, phase (-h) y =
      phase (-h) c * phase (-h) (y - c) := by
    intro y
    have hy : y = c + (y - c) := by ring
    unfold phase
    rw [hy, Theory.PiDigits.T27.phase_add_real]
    congr 1
    congr 1
    ring
  rw [intervalIntegral.integral_congr (fun y _ => hfact y),
    intervalIntegral.integral_const_mul]
  have hshift : (fun x : ℝ => phase (-h) (x - c)) =
      (fun x : ℝ => phase (-h) (x + (-c))) := by funext x; ring
  rw [hshift, intervalIntegral.integral_comp_add_right]
  have hshift_int :
      (∫ x in (c - 1 / (2 * (q : ℝ)) + -c)..
          (c + 1 / (2 * (q : ℝ)) + -c), phase (-h) x) =
        ∫ x in (-(1 / (2 * (q : ℝ))))..(1 / (2 * (q : ℝ))),
          phase (-h) x := by
    congr 1 <;> ring
  rw [hshift_int]
  rw [DecimalFactorComplexity.WeightedFourierReduction.integral_phase_neg_formula
    hzero (1 / (2 * (q : ℝ)))]
  apply congrArg (fun z : ℂ => phase (-h) c * z)
  have harg1 :
      (2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) *
          ((1 / (2 * (q : ℝ)) : ℝ) : ℂ) =
        Real.pi * (-h : ℝ) / (q : ℝ) * Complex.I := by
    push_cast
    ring_nf
  have harg2 :
      (2 * (Real.pi : ℂ) * Complex.I * (-h : ℂ)) *
          ((-(1 / (2 * (q : ℝ))) : ℝ) : ℂ) =
        Real.pi * (h : ℝ) / (q : ℝ) * Complex.I := by
    push_cast
    ring_nf
  rw [harg1, harg2]
  have harg1' :
      Complex.exp (↑Real.pi * ↑(-↑h) / ↑↑q * Complex.I) =
        ↑(Real.cos (Real.pi * -↑h / ↑q)) +
          ↑(Real.sin (Real.pi * -↑h / ↑q)) * Complex.I := by
    have hkey : (Real.pi * -↑h / ↑q : ℝ) * Complex.I =
        ↑Real.pi * ↑(-↑h) / ↑↑q * Complex.I := by
      push_cast; ring
    rw [← hkey, Complex.exp_ofReal_mul_I]
  have harg2' :
      Complex.exp (↑Real.pi * ↑↑h / ↑↑q * Complex.I) =
        ↑(Real.cos (Real.pi * ↑h / ↑q)) +
          ↑(Real.sin (Real.pi * ↑h / ↑q)) * Complex.I := by
    have hkey : (Real.pi * ↑h / ↑q : ℝ) * Complex.I =
        ↑Real.pi * ↑↑h / ↑↑q * Complex.I := by
      push_cast; ring
    rw [← hkey, Complex.exp_ofReal_mul_I]
  push_cast
  rw [harg1', harg2']
  have hargnegR : Real.pi * -(h : ℝ) / (q : ℝ) =
      -(Real.pi * (h : ℝ) / (q : ℝ)) := by ring
  rw [hargnegR, Real.cos_neg, Real.sin_neg]
  have hsin : Complex.sin ((Real.pi : ℂ) * (h : ℂ) / (q : ℂ)) =
      (Real.sin (Real.pi * (h : ℝ) / (q : ℝ)) : ℂ) := by
    rw [show (Real.pi : ℂ) * (h : ℂ) / (q : ℂ) =
      ((Real.pi * (h : ℝ) / (q : ℝ) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin]
  rw [hsin]
  push_cast
  have hpih : (Real.pi : ℂ) * (h : ℂ) ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Int.cast_ne_zero.mpr hzero)
  field_simp [hpih, Complex.I_ne_zero]
  ring

lemma fejerKernel_le_inverse_square (M : ℕ) {t : ℝ}
    (ht0 : t ≠ 0) (ht : |t| ≤ 1 / 2) :
    fejerKernel M t ≤ 1 / (4 * (M + 1 : ℝ) * t ^ 2) := by
  have habs : 0 < |t| := abs_pos.mpr ht0
  have hsin := Real.mul_abs_le_abs_sin
    (x := Real.pi * t) (by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos])
  have hpi : (2 / Real.pi) * |Real.pi * t| = 2 * |t| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hpi] at hsin
  have hsep : 2 * (2 * |t|) ≤ ‖1 - phase 1 t‖ := by
    rw [Theory.PiDigits.T27.norm_one_sub_phase_one]
    nlinarith
  have hbound := Theory.PiDigits.T27.fejerKernel_le_inv_sq
    (H := M) (x := t) (L := 2 * |t|) (by positivity) hsep
  calc
    fejerKernel M t ≤ 1 / ((M + 1 : ℝ) * (2 * |t|) ^ 2) := hbound
    _ = 1 / (4 * (M + 1 : ℝ) * t ^ 2) := by
      rw [mul_pow, sq_abs]
      ring

lemma integral_fejerKernel_pos_tail_le (M : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (∫ t in δ..(1 / 2 : ℝ), fejerKernel M t) ≤
      1 / (4 * (M + 1 : ℝ) * δ) := by
  let c : ℝ := 1 / (4 * (M + 1 : ℝ))
  have hkint : IntervalIntegrable (fejerKernel M) MeasureTheory.volume δ (1 / 2) := by
    simpa only [fejerKernel] using
      (DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M).intervalIntegrable
        δ (1 / 2)
  have hzero : (0 : ℝ) ∉ Set.uIcc δ (1 / 2 : ℝ) := by
    simp only [Set.mem_uIcc, Set.mem_Icc, not_or]
    constructor <;> intro h <;> linarith
  have hzint : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ))
      MeasureTheory.volume δ (1 / 2) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hgint : IntervalIntegrable (fun t : ℝ => c * t ^ (-2 : ℤ))
      MeasureTheory.volume δ (1 / 2) := hzint.const_mul c
  have hmono : (∫ t in δ..(1 / 2 : ℝ), fejerKernel M t) ≤
      ∫ t in δ..(1 / 2 : ℝ), c * t ^ (-2 : ℤ) := by
    apply intervalIntegral.integral_mono_on hδhalf hkint hgint
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    calc
      fejerKernel M t ≤ 1 / (4 * (M + 1 : ℝ) * t ^ 2) :=
        fejerKernel_le_inverse_square M ht0 (by
          rw [abs_of_nonneg (hδ.le.trans ht.1)]
          exact ht.2)
      _ = c * t ^ (-2 : ℤ) := by
        dsimp [c]
        rw [zpow_neg, zpow_ofNat]
        field_simp
  calc
    (∫ t in δ..(1 / 2 : ℝ), fejerKernel M t) ≤
        ∫ t in δ..(1 / 2 : ℝ), c * t ^ (-2 : ℤ) := hmono
    _ = c * (((1 / 2 : ℝ) ^ ((-2 : ℤ) + 1) -
          δ ^ ((-2 : ℤ) + 1)) / ((-2 : ℤ) + 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_zpow]
      exact Or.inr ⟨by norm_num, hzero⟩
    _ ≤ 1 / (4 * (M + 1 : ℝ) * δ) := by
      dsimp [c]
      norm_num
      have hM : (0 : ℝ) < M + 1 := by positivity
      field_simp
      nlinarith

lemma fejerKernel_neg (M : ℕ) (t : ℝ) :
    fejerKernel M (-t) = fejerKernel M t := by
  have hdir : Theory.PiDigits.T27.dirichletKernel M (-t) =
      conj (Theory.PiDigits.T27.dirichletKernel M t) := by
    unfold Theory.PiDigits.T27.dirichletKernel
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    exact DecimalFactorComplexity.WeightedFourierReduction.phase_neg_real (r : ℤ) t
  unfold fejerKernel Theory.PiDigits.T27.fejerKernel
  rw [hdir]
  simp

lemma integral_fejerKernel_tail_le (M : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (∫ t in (-1 / 2 : ℝ)..(-δ), fejerKernel M t) +
        (∫ t in δ..(1 / 2 : ℝ), fejerKernel M t) ≤
      1 / (2 * (M + 1 : ℝ) * δ) := by
  have hpos := integral_fejerKernel_pos_tail_le M hδ hδhalf
  have hneg : (∫ t in (-1 / 2 : ℝ)..(-δ), fejerKernel M t) =
      ∫ t in δ..(1 / 2 : ℝ), fejerKernel M t := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fejerKernel M) (a := δ) (b := (1 / 2 : ℝ))
    simp_rw [fejerKernel_neg] at hcomp
    convert hcomp.symm using 1 <;> norm_num
  rw [hneg]
  calc
    (∫ t in δ..(1 / 2 : ℝ), fejerKernel M t) +
        ∫ t in δ..(1 / 2 : ℝ), fejerKernel M t ≤
      1 / (4 * (M + 1 : ℝ) * δ) +
        1 / (4 * (M + 1 : ℝ) * δ) := add_le_add hpos hpos
    _ = 1 / (2 * (M + 1 : ℝ) * δ) := by
      field_simp
      ring

theorem cylinderIndicator_stable
    (q a : ℕ) (x t δ : ℝ)
    (hq : 0 < q) (ha : a < q) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hleft : δ ≤ circularDistance x (cylinderLeft q a))
    (hright : δ ≤ circularDistance x (cylinderRight q a))
    (ht : |t| < δ) :
    cylinderIndicator q a (x - t) = cylinderIndicator q a x := by
  classical
  let l := cylinderLeft q a
  let r := cylinderRight q a
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl0 : 0 ≤ l := by dsimp [l, cylinderLeft]; positivity
  have hlr : l < r := by
    dsimp [l, r, cylinderLeft, cylinderRight]
    apply (div_lt_div_iff_of_pos_right hqR).2
    push_cast
    norm_num
  have hr1 : r ≤ 1 := by
    dsimp [r, cylinderRight]
    apply (div_le_one hqR).2
    exact_mod_cast Nat.succ_le_of_lt ha
  have htlo : -δ < t := (abs_lt.mp ht).1
  have hthi : t < δ := (abs_lt.mp ht).2
  have hfractx : Int.fract x = x := Int.fract_eq_self.2 hx
  have hleft0 : δ ≤ |x - l| := by
    simpa only [l, Int.cast_zero, sub_zero] using
      hleft.trans (circularDistance_le_abs_sub_int x (cylinderLeft q a) 0)
  have hright0 : δ ≤ |x - r| := by
    simpa only [r, Int.cast_zero, sub_zero] using
      hright.trans (circularDistance_le_abs_sub_int x (cylinderRight q a) 0)
  let u := x - t
  by_cases hu0 : u < 0
  · have huLower : -(1 : ℝ) < u := by
      dsimp [u]
      linarith [hx.1, hδhalf]
    have huplus0 : 0 ≤ u + 1 := by linarith
    have huplus1 : u + 1 < 1 := by linarith
    have hfractu : Int.fract u = u + 1 := by
      calc
        Int.fract u = Int.fract (u + (1 : ℤ)) :=
          (Int.fract_add_intCast u 1).symm
        _ = u + 1 := by
          convert Int.fract_eq_self.2 ⟨huplus0, huplus1⟩ using 1 <;> norm_num
    have hxnot : ¬ inCylinder q a x := by
      intro hmem
      have hxl : 0 ≤ x - l := sub_nonneg.mpr hmem.1
      rw [abs_of_nonneg hxl] at hleft0
      dsimp [u] at hu0
      linarith
    have hygt : r < u + 1 := by
      have hwrap : δ ≤ |x - r - (-1 : ℤ)| :=
        hright.trans (circularDistance_le_abs_sub_int x r (-1))
      have hnonneg : 0 ≤ x - r + 1 := by linarith [hx.1, hr1]
      norm_num at hwrap
      rw [abs_of_nonneg hnonneg] at hwrap
      dsimp [u]
      linarith
    have hynot : ¬ inCylinder q a (u + 1) := fun hmem =>
      (not_lt_of_ge hmem.2.le) hygt
    unfold cylinderIndicator
    rw [show x - t = u by rfl, hfractu, hfractx]
    simp [hxnot, hynot]
  · have hu0' : 0 ≤ u := le_of_not_gt hu0
    by_cases hu1 : u < 1
    · have hfractu : Int.fract u = u := Int.fract_eq_self.2 ⟨hu0', hu1⟩
      have hlower : l ≤ u ↔ l ≤ x := by
        constructor
        · intro hlu
          by_contra hxl
          have hxl' : x < l := lt_of_not_ge hxl
          have habs : |x - l| = l - x := by
            rw [abs_of_neg (sub_neg.mpr hxl')]; ring
          rw [habs] at hleft0
          dsimp [u] at hlu
          linarith [le_abs_self t]
        · intro hlx
          by_contra hlu
          have hul : u < l := lt_of_not_ge hlu
          have habs : |x - l| = x - l := by
            rw [abs_of_nonneg (sub_nonneg.mpr hlx)]
          rw [habs] at hleft0
          dsimp [u] at hul
          linarith [le_abs_self t]
      have hupper : u < r ↔ x < r := by
        constructor
        · intro hur
          by_contra hxr
          have hrx : r ≤ x := le_of_not_gt hxr
          have habs : |x - r| = x - r := by
            rw [abs_of_nonneg (sub_nonneg.mpr hrx)]
          rw [habs] at hright0
          dsimp [u] at hur
          linarith [neg_le_abs t]
        · intro hxr
          by_contra hur
          have hru : r ≤ u := le_of_not_gt hur
          have habs : |x - r| = r - x := by
            rw [abs_of_neg (sub_neg.mpr hxr)]; ring
          rw [habs] at hright0
          dsimp [u] at hru
          linarith [le_abs_self t]
      unfold cylinderIndicator inCylinder
      rw [show x - t = u by rfl, hfractu, hfractx]
      simp only [Set.mem_Ico]
      change (if l ≤ u ∧ u < r then (1 : ℝ) else 0) =
        if l ≤ x ∧ x < r then (1 : ℝ) else 0
      apply if_congr (and_congr hlower hupper) <;> rfl
    · have hu1' : 1 ≤ u := le_of_not_gt hu1
      have huUpper : u - 1 < 1 := by
        dsimp [u]
        linarith [hx.2, hδhalf]
      have hfractu : Int.fract u = u - 1 := by
        calc
          Int.fract u = Int.fract ((u - 1) + (1 : ℤ)) := by congr 1 <;> norm_num
          _ = Int.fract (u - 1) := Int.fract_add_intCast (u - 1) 1
          _ = u - 1 := Int.fract_eq_self.2 ⟨by linarith, huUpper⟩
      have hxnot : ¬ inCylinder q a x := by
        intro hmem
        have habs : |x - r| = r - x := by
          rw [abs_of_neg (sub_neg.mpr hmem.2)]; ring
        rw [habs] at hright0
        dsimp [u] at hu1'
        linarith
      have hylt : u - 1 < l := by
        have hwrap : δ ≤ |x - l - (1 : ℤ)| := by
          simpa only [l] using
            hleft.trans (circularDistance_le_abs_sub_int x (cylinderLeft q a) 1)
        have hneg : x - l - 1 < 0 := by linarith [hx.2, hl0]
        norm_num at hwrap
        rw [abs_of_neg hneg] at hwrap
        dsimp [u]
        linarith
      have hynot : ¬ inCylinder q a (u - 1) := fun hmem =>
        (not_lt_of_ge hmem.1) hylt
      unfold cylinderIndicator
      rw [show x - t = u by rfl, hfractu, hfractx]
      simp [hxnot, hynot]

lemma cylinderIndicator_int_shift (q a : ℕ) (x : ℝ) (z : ℤ) :
    cylinderIndicator q a (x + z) = cylinderIndicator q a x := by
  classical
  unfold cylinderIndicator
  rw [Int.fract_add_intCast]

theorem integral_phase_mul_cylinderIndicator_period
    (q a : ℕ) (h : ℤ) (hq : 0 < q) (ha : a < q) :
    (∫ y in (0 : ℝ)..1,
        phase h y * (cylinderIndicator q a y : ℂ)) =
      ∫ y in cylinderLeft q a..cylinderRight q a, phase h y := by
  let l := cylinderLeft q a
  let r := cylinderRight q a
  let F : ℝ → ℂ := fun y => phase h y * (cylinderIndicator q a y : ℂ)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl0 : 0 ≤ l := by dsimp [l, cylinderLeft]; positivity
  have hlr : l < r := by
    dsimp [l, r, cylinderLeft, cylinderRight]
    apply (div_lt_div_iff_of_pos_right hqR).2
    push_cast
    norm_num
  have hr1 : r ≤ 1 := by
    dsimp [r, cylinderRight]
    apply (div_le_one hqR).2
    exact_mod_cast Nat.succ_le_of_lt ha
  have hzero_left : (∫ y in (0 : ℝ)..l, F y) = 0 := by
    have hz : (∫ y in (0 : ℝ)..l, F y) =
        ∫ _y in (0 : ℝ)..l, (0 : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.volume.ae_ne l] with y hyl hy
      rw [Set.uIoc_of_le hl0] at hy
      have hylt : y < l := lt_of_le_of_ne hy.2 hyl
      have hy0 : 0 ≤ y := hy.1.le
      have hy1 : y < 1 := hylt.trans (hlr.trans_le hr1)
      have hfract : Int.fract y = y := Int.fract_eq_self.2 ⟨hy0, hy1⟩
      have hnot : ¬ inCylinder q a y := by
        intro hm
        exact (not_lt_of_ge hm.1) hylt
      simp [F, cylinderIndicator, hfract, hnot]
    simpa using hz
  have hmiddle : (∫ y in l..r, F y) = ∫ y in l..r, phase h y := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.volume.ae_ne r] with y hyr hy
    rw [Set.uIoc_of_le hlr.le] at hy
    have hyr' : y < r := lt_of_le_of_ne hy.2 hyr
    have hy0 : 0 ≤ y := hl0.trans (hy.1.le)
    have hy1 : y < 1 := hyr'.trans_le hr1
    have hfract : Int.fract y = y := Int.fract_eq_self.2 ⟨hy0, hy1⟩
    have hmem : inCylinder q a y := ⟨by simpa [l] using hy.1.le,
      by simpa [r] using hyr'⟩
    simp [F, cylinderIndicator, hfract, hmem]
  have hzero_right : (∫ y in r..(1 : ℝ), F y) = 0 := by
    have hz : (∫ y in r..(1 : ℝ), F y) =
        ∫ _y in r..(1 : ℝ), (0 : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.volume.ae_ne (1 : ℝ)] with y hy1 hy
      rw [Set.uIoc_of_le hr1] at hy
      have hylt1 : y < 1 := lt_of_le_of_ne hy.2 hy1
      have hy0 : 0 ≤ y := hl0.trans (hlr.le.trans hy.1.le)
      have hfract : Int.fract y = y := Int.fract_eq_self.2 ⟨hy0, hylt1⟩
      have hnot : ¬ inCylinder q a y := by
        intro hm
        exact (not_lt_of_ge hy.1.le) hm.2
      simp [F, cylinderIndicator, hfract, hnot]
    simpa using hz
  have hsplit_left := intervalIntegral.integral_add_adjacent_intervals
    (phaseIndicator_intervalIntegrable q a h 0 l)
    (phaseIndicator_intervalIntegrable q a h l r)
  have hsplit_right := intervalIntegral.integral_add_adjacent_intervals
    (phaseIndicator_intervalIntegrable q a h 0 r)
    (phaseIndicator_intervalIntegrable q a h r 1)
  change (∫ y in (0 : ℝ)..1, F y) = ∫ y in l..r, phase h y
  rw [← hsplit_right, ← hsplit_left, hzero_left, hmiddle, hzero_right,
    zero_add, add_zero]

theorem integral_phase_mul_shiftedIndicator
    (q a : ℕ) (h : ℤ) (x : ℝ) (hq : 0 < q) (ha : a < q) :
    (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        phase h t * (cylinderIndicator q a (x - t) : ℂ)) =
      phase h x *
        ∫ y in cylinderLeft q a..cylinderRight q a, phase (-h) y := by
  let G : ℝ → ℂ := fun y => phase (-h) y * (cylinderIndicator q a y : ℂ)
  have hchange : (fun t : ℝ =>
      phase h t * (cylinderIndicator q a (x - t) : ℂ)) =
      fun t : ℝ =>
        (phase h x * phase (-h) (x - t)) *
          (cylinderIndicator q a (x - t) : ℂ) := by
    funext t
    congr 1
    calc
      phase h t = phase h (x - (x - t)) := by congr 1 <;> ring
      _ = phase h x * conj (phase h (x - t)) :=
        DecimalFactorComplexity.WeightedFourierReduction.phase_real_sub h x (x - t)
      _ = phase h x * phase (-h) (x - t) := by
        exact congrArg (fun z : ℂ => phase h x * z)
          (Theory.PiDigits.T27.phase_neg h (x - t)).symm
  rw [hchange]
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun y : ℝ => (phase h x * phase (-h) y) *
      (cylinderIndicator q a y : ℂ))
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) x
  rw [hsub]
  rw [intervalIntegral.integral_congr (fun y _ => by
    change (phase h x * phase (-h) y) * (cylinderIndicator q a y : ℂ) =
      phase h x * G y
    simp only [G]
    ring), intervalIntegral.integral_const_mul]
  have hperiodic : Function.Periodic G 1 := by
    intro y
    simp only [G]
    have hp : phase (-h) (y + 1) = phase (-h) y := by
      convert DecimalFactorComplexity.WeightedFourierReduction.phase_int_shift
        (-h) 1 y using 1 <;> norm_num
    have hi : cylinderIndicator q a (y + 1) = cylinderIndicator q a y := by
      convert cylinderIndicator_int_shift q a y 1 using 1 <;> norm_num
    rw [hp, hi]
  have hperiod := hperiodic.intervalIntegral_add_eq (x - 1 / 2) 0
  have hnormalized : (∫ y in x - (1 / 2 : ℝ)..x - (-1 / 2 : ℝ), G y) =
      ∫ y in (0 : ℝ)..1, G y := by
    convert hperiod using 1 <;> ring
  rw [hnormalized]
  rw [integral_phase_mul_cylinderIndicator_period q a (-h) hq ha]

/-- Exact finite Fourier expansion of the cylinder/Fejer convolution. -/
theorem fejerApproximation_eq_aggregated (q a M : ℕ) (x : ℝ)
    (hq : 0 < q) (ha : a < q) :
    (fejerApproximation q a M x : ℂ) =
      (1 / (q : ℝ) : ℝ) +
        ∑ h ∈ signedFrequencies M,
          fejerCylinderCoefficient q a M h * phase h x := by
  classical
  have hint := fejerIntegrand_intervalIntegrable q a M x (-1 / 2) (1 / 2)
  have hmap := Complex.ofRealCLM.intervalIntegral_comp_comm hint
  simp only [Complex.ofRealCLM_apply] at hmap
  unfold fejerApproximation
  rw [← hmap]
  rw [intervalIntegral.integral_congr (fun t _ => by
    calc
      ((fejerKernel M t * cylinderIndicator q a (x - t) : ℝ) : ℂ) =
          (fejerKernel M t : ℂ) * (cylinderIndicator q a (x - t) : ℂ) := by
        exact Complex.ofReal_mul _ _
      _ = (∑ h ∈ signedFrequenciesZero M,
          (triangularCoefficient M h : ℂ) * phase h t) *
            (cylinderIndicator q a (x - t) : ℂ) := by
        rw [fejerKernel_eq_aggregated M t])]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · have hmode (h : ℤ) :
        (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          ((triangularCoefficient M h : ℂ) * phase h t) *
            (cylinderIndicator q a (x - t) : ℂ)) =
          (triangularCoefficient M h : ℂ) * phase h x *
            ∫ y in cylinderLeft q a..cylinderRight q a, phase (-h) y := by
      rw [show (fun t : ℝ => ((triangularCoefficient M h : ℂ) * phase h t) *
          (cylinderIndicator q a (x - t) : ℂ)) =
        fun t : ℝ => (triangularCoefficient M h : ℂ) *
          (phase h t * (cylinderIndicator q a (x - t) : ℂ)) by
            funext t; ring,
        intervalIntegral.integral_const_mul,
        integral_phase_mul_shiftedIndicator q a h x hq ha]
      ring
    have hset : signedFrequenciesZero M = insert 0 (signedFrequencies M) := by
      ext h
      rw [mem_signedFrequenciesZero]
      simp only [Finset.mem_insert, mem_signedFrequencies]
      by_cases hz : h = 0
      · subst h
        simp
      · simp [hz]
    rw [hset, Finset.sum_insert]
    · simp_rw [hmode]
      simp only [triangularCoefficient, Int.natAbs_zero, Nat.cast_zero,
        zero_div, sub_zero, neg_zero, Theory.PiDigits.T27.phase_zero, mul_one,
        Complex.ofReal_one, one_mul]
      have hzeroIntegral :
          (∫ _y in cylinderLeft q a..cylinderRight q a, (1 : ℂ)) =
            (1 / (q : ℝ) : ℂ) := by
        rw [intervalIntegral.integral_const]
        unfold cylinderLeft cylinderRight
        push_cast
        field_simp
        rw [Complex.real_smul]
        simp
      rw [hzeroIntegral]
      have hqcast : (1 / (q : ℂ)) = ((1 / (q : ℝ) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [← hqcast]
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      obtain ⟨hzero, hM⟩ := mem_signedFrequencies.mp hh
      rw [integral_cylinder_phase q a h hq hzero]
      unfold fejerCylinderCoefficient triangularCoefficient
      push_cast
      ring
    · simp [mem_signedFrequencies]
  · intro h hh
    rw [show (fun t : ℝ => ((triangularCoefficient M h : ℂ) * phase h t) *
        (cylinderIndicator q a (x - t) : ℂ)) =
      fun t : ℝ => (triangularCoefficient M h : ℂ) *
        (phase h t * (cylinderIndicator q a (x - t) : ℂ)) by
      funext t; ring]
    apply IntervalIntegrable.const_mul
    exact shiftedPhaseIndicator_intervalIntegrable q a h x (-1 / 2) (1 / 2)

lemma abs_cylinderIndicator_sub_le_one (q a : ℕ) (x y : ℝ) :
    |cylinderIndicator q a x - cylinderIndicator q a y| ≤ 1 := by
  have hx0 := cylinderIndicator_nonneg q a x
  have hx1 := cylinderIndicator_le_one q a x
  have hy0 := cylinderIndicator_nonneg q a y
  have hy1 := cylinderIndicator_le_one q a y
  rw [abs_le]
  constructor <;> linarith

lemma fejerErrorIntegrand_intervalIntegrable
    (q a M : ℕ) (x b c : ℝ) :
    IntervalIntegrable
      (fun t => fejerKernel M t *
        (cylinderIndicator q a (x - t) - cylinderIndicator q a x))
      MeasureTheory.volume b c := by
  have hfirst := fejerIntegrand_intervalIntegrable q a M x b c
  have hkernel : IntervalIntegrable (fejerKernel M) MeasureTheory.volume b c := by
    simpa only [fejerKernel] using
      (DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M).intervalIntegrable b c
  have hsecond := hkernel.mul_const (cylinderIndicator q a x)
  convert hfirst.sub hsecond using 1
  funext t
  ring

lemma norm_fejerErrorIntegrand_le (q a M : ℕ) (x t : ℝ) :
    ‖fejerKernel M t *
        (cylinderIndicator q a (x - t) - cylinderIndicator q a x)‖ ≤
      fejerKernel M t := by
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Theory.PiDigits.T27.fejerKernel_nonneg M t)]
  calc
    fejerKernel M t *
        |cylinderIndicator q a (x - t) - cylinderIndicator q a x| ≤
      fejerKernel M t * 1 :=
        mul_le_mul_of_nonneg_left
          (abs_cylinderIndicator_sub_le_one q a (x - t) x)
          (Theory.PiDigits.T27.fejerKernel_nonneg M t)
    _ = fejerKernel M t := mul_one _

/-- Pointwise circular Fejer tail estimate away from both cylinder boundaries. -/
theorem norm_fejerApproximation_sub_indicator_le
    (q a M : ℕ) (x δ : ℝ)
    (hq : 0 < q) (ha : a < q) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hleft : δ ≤ circularDistance x (cylinderLeft q a))
    (hright : δ ≤ circularDistance x (cylinderRight q a)) :
    ‖((fejerApproximation q a M x : ℝ) : ℂ) -
        (cylinderIndicator q a x : ℂ)‖ ≤
      1 / (2 * (M + 1 : ℝ) * δ) := by
  let F : ℝ → ℝ := fun t => fejerKernel M t *
    (cylinderIndicator q a (x - t) - cylinderIndicator q a x)
  have hmass := integral_fejerKernel_period M
  have hfirst := fejerIntegrand_intervalIntegrable q a M x (-1 / 2) (1 / 2)
  have hkernel : IntervalIntegrable (fejerKernel M) MeasureTheory.volume
      (-1 / 2) (1 / 2) := by
    simpa only [fejerKernel] using
      (DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M).intervalIntegrable
        (-1 / 2) (1 / 2)
  have hsecond := hkernel.mul_const (cylinderIndicator q a x)
  have hdiff : fejerApproximation q a M x - cylinderIndicator q a x =
      ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), F t := by
    unfold fejerApproximation
    calc
      (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          fejerKernel M t * cylinderIndicator q a (x - t)) -
          cylinderIndicator q a x =
        (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          fejerKernel M t * cylinderIndicator q a (x - t)) -
          ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
            fejerKernel M t * cylinderIndicator q a x := by
        rw [intervalIntegral.integral_mul_const, hmass, one_mul]
      _ = ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          (fejerKernel M t * cylinderIndicator q a (x - t) -
            fejerKernel M t * cylinderIndicator q a x) := by
        rw [intervalIntegral.integral_sub hfirst hsecond]
      _ = ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), F t := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [F]
        ring
  have hcentral : (∫ t in (-δ)..δ, F t) = 0 := by
    have hz : (∫ t in (-δ)..δ, F t) = ∫ _t in (-δ)..δ, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.volume.ae_ne δ] with t htne ht
      rw [Set.uIoc_of_le (by linarith : -δ ≤ δ)] at ht
      have habs : |t| < δ := by
        rw [abs_lt]
        exact ⟨ht.1, lt_of_le_of_ne ht.2 htne⟩
      simp only [F]
      rw [cylinderIndicator_stable q a x t δ hq ha hx hδ hδhalf
        hleft hright habs]
      simp
    simpa using hz
  have hFint (b c : ℝ) : IntervalIntegrable F MeasureTheory.volume b c := by
    simpa only [F] using fejerErrorIntegrand_intervalIntegrable q a M x b c
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals
    (hFint (-1 / 2) (-δ)) (hFint (-δ) δ)
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals
    (hFint (-1 / 2) δ) (hFint δ (1 / 2))
  have hsplit : (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), F t) =
      (∫ t in (-1 / 2 : ℝ)..(-δ), F t) +
        ∫ t in δ..(1 / 2 : ℝ), F t := by
    rw [← hsplitRight, ← hsplitLeft, hcentral, add_zero]
  have hkneg : IntervalIntegrable (fejerKernel M) MeasureTheory.volume
      (-1 / 2) (-δ) := by
    simpa only [fejerKernel] using
      (DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M).intervalIntegrable
        (-1 / 2) (-δ)
  have hkpos : IntervalIntegrable (fejerKernel M) MeasureTheory.volume
      δ (1 / 2) := by
    simpa only [fejerKernel] using
      (DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M).intervalIntegrable
        δ (1 / 2)
  have hneg : ‖∫ t in (-1 / 2 : ℝ)..(-δ), F t‖ ≤
      ∫ t in (-1 / 2 : ℝ)..(-δ), fejerKernel M t := by
    calc
      ‖∫ t in (-1 / 2 : ℝ)..(-δ), F t‖ ≤
          ∫ t in (-1 / 2 : ℝ)..(-δ), ‖F t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ t in (-1 / 2 : ℝ)..(-δ), fejerKernel M t := by
        apply intervalIntegral.integral_mono_on (by linarith) (hFint _ _).norm hkneg
        intro t ht
        exact norm_fejerErrorIntegrand_le q a M x t
  have hpos : ‖∫ t in δ..(1 / 2 : ℝ), F t‖ ≤
      ∫ t in δ..(1 / 2 : ℝ), fejerKernel M t := by
    calc
      ‖∫ t in δ..(1 / 2 : ℝ), F t‖ ≤
          ∫ t in δ..(1 / 2 : ℝ), ‖F t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hδhalf
      _ ≤ ∫ t in δ..(1 / 2 : ℝ), fejerKernel M t := by
        apply intervalIntegral.integral_mono_on hδhalf (hFint _ _).norm hkpos
        intro t ht
        exact norm_fejerErrorIntegrand_le q a M x t
  rw [show ((fejerApproximation q a M x : ℝ) : ℂ) -
      (cylinderIndicator q a x : ℂ) =
        ((fejerApproximation q a M x - cylinderIndicator q a x : ℝ) : ℂ) by
      push_cast
      rfl]
  rw [Complex.norm_real, Real.norm_eq_abs, hdiff, ← Real.norm_eq_abs, hsplit]
  calc
    ‖(∫ t in (-1 / 2 : ℝ)..(-δ), F t) +
        ∫ t in δ..(1 / 2 : ℝ), F t‖ ≤
      ‖∫ t in (-1 / 2 : ℝ)..(-δ), F t‖ +
        ‖∫ t in δ..(1 / 2 : ℝ), F t‖ := norm_add_le _ _
    _ ≤ (∫ t in (-1 / 2 : ℝ)..(-δ), fejerKernel M t) +
        ∫ t in δ..(1 / 2 : ℝ), fejerKernel M t := add_le_add hneg hpos
    _ ≤ 1 / (2 * (M + 1 : ℝ) * δ) :=
      integral_fejerKernel_tail_le M hδ hδhalf

/-- The Fejer approximation always lies in `[0,1]`. -/
theorem fejerApproximation_mem_unitInterval
    (q a M : ℕ) (x : ℝ) (hq : 0 < q) (ha : a < q) :
    fejerApproximation q a M x ∈ Set.Icc (0 : ℝ) 1 := by
  have hbounds : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hfirst := fejerIntegrand_intervalIntegrable q a M x (-1 / 2) (1 / 2)
  have hkernel : IntervalIntegrable (fejerKernel M) MeasureTheory.volume
      (-1 / 2) (1 / 2) := by
    simpa only [fejerKernel] using
      (DecimalFactorComplexity.WeightedFourierReduction.fejerKernel_continuous M).intervalIntegrable
        (-1 / 2) (1 / 2)
  constructor
  · unfold fejerApproximation
    apply intervalIntegral.integral_nonneg_of_forall hbounds
    intro t
    exact mul_nonneg (Theory.PiDigits.T27.fejerKernel_nonneg M t)
      (cylinderIndicator_nonneg q a (x - t))
  · unfold fejerApproximation
    calc
      (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          fejerKernel M t * cylinderIndicator q a (x - t)) ≤
        ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), fejerKernel M t := by
          apply intervalIntegral.integral_mono_on hbounds hfirst hkernel
          intro t ht
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (cylinderIndicator_le_one q a (x - t))
              (Theory.PiDigits.T27.fejerKernel_nonneg M t)
      _ = 1 := integral_fejerKernel_period M

lemma cylinderCount_eq_sum_indicator
    (x : ℕ → ℝ) (N q a : ℕ)
    (hx : ∀ n < N, x n ∈ Set.Ico (0 : ℝ) 1) :
    (cylinderCount x N q a : ℝ) =
      ∑ n ∈ range N, cylinderIndicator q a (x n) := by
  classical
  unfold cylinderCount cylinderIndicator
  norm_cast
  simp only [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Int.fract_eq_self.2 (hx n (Finset.mem_range.mp hn))]

lemma norm_fejerApproximation_sub_indicator_le_one
    (q a M : ℕ) (x : ℝ) (hq : 0 < q) (ha : a < q) :
    ‖((fejerApproximation q a M x : ℝ) : ℂ) -
        (cylinderIndicator q a x : ℂ)‖ ≤ 1 := by
  rw [show ((fejerApproximation q a M x : ℝ) : ℂ) -
      (cylinderIndicator q a x : ℂ) =
        ((fejerApproximation q a M x - cylinderIndicator q a x : ℝ) : ℂ) by
      push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hA := fejerApproximation_mem_unitInterval q a M x hq ha
  have hJ0 := cylinderIndicator_nonneg q a x
  have hJ1 := cylinderIndicator_le_one q a x
  rcases hA with ⟨hA0, hA1⟩
  constructor <;> linarith

/-- The analytic certificate omitted by the previous T14 attempt. It is now a
theorem from T13's parameters and the canonical-representative invariant. -/
theorem fejerEstimator_error_and_expansion
    (x : ℕ → ℝ) (N q a M : ℕ) (δ : ℝ)
    (hq : 0 < q) (ha : a < q)
    (hx : ∀ n < N, x n ∈ Set.Ico (0 : ℝ) 1)
    (hδ : 0 < δ) (hδq : δ ≤ 1 / (2 * (q : ℝ))) :
    ‖fejerEstimator x N q a M - (cylinderCount x N q a : ℂ)‖ ≤
        (twoBoundaryCount x N q a δ : ℝ) +
          (N : ℝ) / (2 * (M + 1 : ℝ) * δ) ∧
      fejerEstimator x N q a M = (N : ℝ) / q +
        ∑ h ∈ signedFrequencies M,
          fejerCylinderCoefficient q a M h * exponentialSum x N h := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hδhalf : δ ≤ 1 / 2 := by
    calc
      δ ≤ 1 / (2 * (q : ℝ)) := hδq
      _ ≤ 1 / 2 := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)
          (by norm_num : (0 : ℝ) < 2)).2
        nlinarith
  constructor
  · have hcount := cylinderCount_eq_sum_indicator x N q a hx
    have hcountC : (cylinderCount x N q a : ℂ) =
        ∑ n ∈ range N, (cylinderIndicator q a (x n) : ℂ) := by
      have hc := congrArg (fun r : ℝ => (r : ℂ)) hcount
      push_cast at hc
      exact hc
    have hsumForm : fejerEstimator x N q a M - (cylinderCount x N q a : ℂ) =
        ∑ n ∈ range N,
          (((fejerApproximation q a M (x n) : ℝ) : ℂ) -
            (cylinderIndicator q a (x n) : ℂ)) := by
      unfold fejerEstimator
      push_cast
      rw [hcountC]
      rw [← Finset.sum_sub_distrib]
    rw [hsumForm]
    calc
      ‖∑ n ∈ range N,
          (((fejerApproximation q a M (x n) : ℝ) : ℂ) -
            (cylinderIndicator q a (x n) : ℂ))‖ ≤
        ∑ n ∈ range N,
          ‖((fejerApproximation q a M (x n) : ℝ) : ℂ) -
            (cylinderIndicator q a (x n) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N,
          ((if circularDistance (x n) (cylinderLeft q a) < δ ∨
              circularDistance (x n) (cylinderRight q a) < δ then 1 else 0) +
            1 / (2 * (M + 1 : ℝ) * δ)) := by
        apply Finset.sum_le_sum
        intro n hn
        split_ifs with hb
        · have heps : 0 ≤ 1 / (2 * (M + 1 : ℝ) * δ) := by positivity
          exact (norm_fejerApproximation_sub_indicator_le_one q a M (x n) hq ha).trans
            (le_add_of_nonneg_right heps)
        · push Not at hb
          simpa using norm_fejerApproximation_sub_indicator_le q a M (x n) δ
            hq ha (hx n (Finset.mem_range.mp hn)) hδ hδhalf
            hb.1 hb.2
      _ = (twoBoundaryCount x N q a δ : ℝ) +
          (N : ℝ) / (2 * (M + 1 : ℝ) * δ) := by
        rw [Finset.sum_add_distrib]
        unfold twoBoundaryCount
        have hcard :
            (∑ n ∈ range N,
              if circularDistance (x n) (cylinderLeft q a) < δ ∨
                circularDistance (x n) (cylinderRight q a) < δ
              then (1 : ℝ) else 0) =
              (((range N).filter fun n =>
                circularDistance (x n) (cylinderLeft q a) < δ ∨
                  circularDistance (x n) (cylinderRight q a) < δ).card : ℝ) := by
          norm_cast
          rw [Finset.card_filter]
        rw [hcard]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        rw [div_eq_mul_inv]
        ring
  · unfold fejerEstimator
    push_cast
    simp_rw [fejerApproximation_eq_aggregated q a M _ hq ha]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_comm]
    congr 1
    · push_cast
      ring
    · apply Finset.sum_congr rfl
      intro h hh
      rw [← Finset.mul_sum]
      unfold exponentialSum Theory.PiDigits.T27.exponentialSum
      rfl

/-- Complex modulus of the aggregated cylinder coefficient. -/
theorem norm_fejerCylinderCoefficient {q a M : ℕ} {h : ℤ}
    (hq : 0 < q) (hzero : h ≠ 0) (hh : h.natAbs ≤ M) :
    ‖fejerCylinderCoefficient q a M h‖ =
      fejerCylinderWeight q M h := by
  rw [fejerCylinderCoefficient, norm_mul,
    Theory.PiDigits.T27.norm_phase, mul_one]
  rw [norm_mul, norm_div, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (triangularCoefficient_nonneg hh),
    abs_of_pos Real.pi_pos]
  have hcastAbs : (((|h| : ℤ) : ℝ)) = |(h : ℝ)| := Int.cast_abs
  have hcastNat : (h.natAbs : ℝ) = ((|h| : ℤ) : ℝ) := Nat.cast_natAbs h
  have hcast : |(h : ℝ)| = (h.natAbs : ℝ) :=
    hcastAbs.symm.trans hcastNat.symm
  rw [hcast]
  unfold fejerCylinderWeight
  ring

/-- Complex triangle inequality after aggregation by signed frequency. -/
theorem norm_aggregated_remainder_le
    (x : ℕ → ℝ) (N q a M : ℕ) (hq : 0 < q) :
    ‖∑ h ∈ signedFrequencies M,
        fejerCylinderCoefficient q a M h * exponentialSum x N h‖ ≤
      aggregatedFourierSum x N q M := by
  classical
  calc
    ‖∑ h ∈ signedFrequencies M,
        fejerCylinderCoefficient q a M h * exponentialSum x N h‖ ≤
        ∑ h ∈ signedFrequencies M,
          ‖fejerCylinderCoefficient q a M h * exponentialSum x N h‖ :=
      norm_sum_le _ _
    _ = aggregatedFourierSum x N q M := by
      unfold aggregatedFourierSum
      apply Finset.sum_congr rfl
      intro h hhmem
      obtain ⟨hzero, hh⟩ := mem_signedFrequencies.mp hhmem
      rw [norm_mul, norm_fejerCylinderCoefficient hq hzero hh]

/-- T13's unconditional finite empty-cylinder dichotomy. The sample is given
by canonical representatives in `[0,1)`; both boundary tests are circular. -/
theorem finite_emptyCylinder_dichotomy
    (x : ℕ → ℝ) (N q a M : ℕ) (δ : ℝ)
    (hN : 0 < N) (hq : 0 < q) (ha : a < q)
    (hx : ∀ n < N, x n ∈ Set.Ico (0 : ℝ) 1)
    (hδ : 0 < δ) (hδq : δ ≤ 1 / (2 * (q : ℝ)))
    (hMδ : 2 * (q : ℝ) ≤ (M + 1 : ℝ) * δ)
    (hempty : cylinderCount x N q a = 0) :
    (N : ℝ) / (4 * q) ≤ twoBoundaryCount x N q a δ ∨
      (N : ℝ) / (2 * q) ≤ aggregatedFourierSum x N q M := by
  classical
  obtain ⟨herr, hexp⟩ := fejerEstimator_error_and_expansion
    x N q a M δ hq ha hx hδ hδq
  by_cases hboundary : (N : ℝ) / (4 * q) ≤
      twoBoundaryCount x N q a δ
  · exact Or.inl hboundary
  · right
    have hboundary' : (twoBoundaryCount x N q a δ : ℝ) <
        (N : ℝ) / (4 * q) := lt_of_not_ge hboundary
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have htailDen : 0 < 2 * (M + 1 : ℝ) * δ := by positivity
    have hfourDen : 0 < 4 * (q : ℝ) := by positivity
    have htail : (N : ℝ) / (2 * (M + 1 : ℝ) * δ) ≤
        (N : ℝ) / (4 * q) := by
      rw [div_le_div_iff₀ htailDen hfourDen]
      nlinarith
    rw [hempty, Nat.cast_zero, sub_zero] at herr
    have hestimator : ‖fejerEstimator x N q a M‖ < (N : ℝ) / (2 * q) := by
      calc
        ‖fejerEstimator x N q a M‖ ≤
            (twoBoundaryCount x N q a δ : ℝ) +
              (N : ℝ) / (2 * (M + 1 : ℝ) * δ) := herr
        _ < (N : ℝ) / (4 * q) + (N : ℝ) / (4 * q) :=
          add_lt_add_of_lt_of_le hboundary' htail
        _ = (N : ℝ) / (2 * q) := by field_simp; ring
    let R : ℂ := ∑ h ∈ signedFrequencies M,
      fejerCylinderCoefficient q a M h * exponentialSum x N h
    have hR : R = fejerEstimator x N q a M - (((N : ℝ) / q : ℝ) : ℂ) := by
      rw [hexp]
      dsimp only [R]
      push_cast
      ring
    have htriangle := norm_add_le (fejerEstimator x N q a M)
      (-fejerEstimator x N q a M + (((N : ℝ) / q : ℝ) : ℂ))
    have hsum : fejerEstimator x N q a M +
        (-fejerEstimator x N q a M + (((N : ℝ) / q : ℝ) : ℂ)) =
          (((N : ℝ) / q : ℝ) : ℂ) := by ring
    rw [hsum] at htriangle
    have hsecond :
        ‖-fejerEstimator x N q a M + (((N : ℝ) / q : ℝ) : ℂ)‖ = ‖R‖ := by
      rw [hR]
      rw [show -fejerEstimator x N q a M + (((N : ℝ) / q : ℝ) : ℂ) =
        -(fejerEstimator x N q a M - (((N : ℝ) / q : ℝ) : ℂ)) by ring,
        norm_neg]
    rw [hsecond, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hNR hqR)] at htriangle
    have hsplit : (N : ℝ) / q =
        (N : ℝ) / (2 * q) + (N : ℝ) / (2 * q) := by
      field_simp
      ring
    rw [hsplit] at htriangle
    have hRlarge : (N : ℝ) / (2 * q) < ‖R‖ := by linarith
    have hRupper : ‖R‖ ≤ aggregatedFourierSum x N q M := by
      dsimp only [R]
      exact norm_aggregated_remainder_le x N q a M hq
    exact hRlarge.le.trans hRupper

/-- Contrapositive cover criterion: simultaneous strict failure of both
obstruction branches forces a cylinder hit. -/
theorem cylinder_hit_of_small_boundary_and_aggregated_sum
    (x : ℕ → ℝ) (N q a M : ℕ) (δ : ℝ)
    (hN : 0 < N) (hq : 0 < q) (ha : a < q)
    (hx : ∀ n < N, x n ∈ Set.Ico (0 : ℝ) 1)
    (hδ : 0 < δ) (hδq : δ ≤ 1 / (2 * (q : ℝ)))
    (hMδ : 2 * (q : ℝ) ≤ (M + 1 : ℝ) * δ)
    (hboundary : (twoBoundaryCount x N q a δ : ℝ) < (N : ℝ) / (4 * q))
    (hfourier : aggregatedFourierSum x N q M < (N : ℝ) / (2 * q)) :
    ∃ n < N, inCylinder q a (x n) := by
  classical
  by_contra hhit
  push Not at hhit
  have hempty : cylinderCount x N q a = 0 := by
    unfold cylinderCount
    rw [Finset.card_eq_zero]
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    simpa using hhit n
  rcases finite_emptyCylinder_dichotomy x N q a M δ hN hq ha hx hδ hδq
      hMδ hempty with hlarge | hlarge
  · exact (not_lt_of_ge hlarge) hboundary
  · exact (not_lt_of_ge hlarge) hfourier

/-- Simultaneous contrapositive criterion for all `q` cylinders. -/
theorem all_cylinders_hit_of_small_boundary_and_aggregated_sum
    (x : ℕ → ℝ) (N q M : ℕ) (δ : ℝ)
    (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ n < N, x n ∈ Set.Ico (0 : ℝ) 1)
    (hδ : 0 < δ) (hδq : δ ≤ 1 / (2 * (q : ℝ)))
    (hMδ : 2 * (q : ℝ) ≤ (M + 1 : ℝ) * δ)
    (hboundary : ∀ a < q,
      (twoBoundaryCount x N q a δ : ℝ) < (N : ℝ) / (4 * q))
    (hfourier : aggregatedFourierSum x N q M < (N : ℝ) / (2 * q)) :
    ∀ a < q, ∃ n < N, inCylinder q a (x n) := by
  intro a ha
  exact cylinder_hit_of_small_boundary_and_aggregated_sum x N q a M δ
    hN hq ha hx hδ hδq hMδ (hboundary a ha) hfourier

/-- The fully numerical T13 choice `delta=1/(4q)`, `M=8q^2`. -/
theorem finite_emptyCylinder_explicit
    (x : ℕ → ℝ) (N q a : ℕ)
    (hN : 0 < N) (hq : 0 < q) (ha : a < q)
    (hx : ∀ n < N, x n ∈ Set.Ico (0 : ℝ) 1)
    (hempty : cylinderCount x N q a = 0) :
    (N : ℝ) / (4 * q) ≤
        twoBoundaryCount x N q a (1 / (4 * (q : ℝ))) ∨
      (N : ℝ) / (2 * q) ≤
        aggregatedFourierSum x N q (8 * q ^ 2) := by
  apply finite_emptyCylinder_dichotomy x N q a (8 * q ^ 2)
    (1 / (4 * (q : ℝ))) hN hq ha hx
  · positivity
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * q)
      (by positivity : (0 : ℝ) < 2 * q)).2
    nlinarith
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    push_cast
    field_simp
    nlinarith [sq_nonneg ((q : ℝ) - 1)]
  · exact hempty

/-- A point of the pi orbit in the cylinder encoded by `w` yields the exact
next `k` digits. -/
theorem pi_digits_of_mem_wordCylinder
    {k n : ℕ}
    (w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k)
    (hmem : inCylinder (10 ^ k) (Theory.PiDigits.T20.wordValue (List.ofFn w))
      (Theory.PiDigits.T27.piFractionalOrbit n)) :
    ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j := by
  let s : List (Fin 10) := List.ofFn w
  have hinterval : Theory.PiDigits.T27.piFractionalOrbit n ∈
      Set.Ico
        ((Theory.PiDigits.T20.wordValue s : ℝ) / (10 : ℝ) ^ s.length)
        (((Theory.PiDigits.T20.wordValue s + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ s.length) := by
    simpa only [inCylinder, cylinderLeft, cylinderRight, s,
      List.length_ofFn, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one] using hmem
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
    s (Theory.PiDigits.T27.piFractionalOrbit n) hinterval
  intro j
  have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
    Real.pi Real.pi_pos.le n j.val
  have hj : j.val < s.length := by simpa only [s, List.length_ofFn] using j.isLt
  exact (Theory.PiDigits.T20.decimalDigit_pi (n + j.val)).symm.trans
    (hshift.symm.trans (by simpa only [s, List.get_ofFn] using hdigits j.val hj))

/-- The contrapositive criterion at the canonical exact full-containment
deadline `D=C*k*10^k`, with exactly `D-k+1` admissible starts. -/
theorem pi_fullContainment_at_exact_deadline_of_smallness
    (C k M : ℕ) (δ : ℝ) (hC : 1 ≤ C) (hk : 1 ≤ k)
    (hδ : 0 < δ) (hδq : δ ≤ 1 / (2 * ((10 ^ k : ℕ) : ℝ)))
    (hMδ : 2 * ((10 ^ k : ℕ) : ℝ) ≤ (M + 1 : ℝ) * δ)
    (hboundary : ∀ w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k,
      (twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit
        (C * k * 10 ^ k - k + 1) (10 ^ k)
        (Theory.PiDigits.T20.wordValue (List.ofFn w)) δ : ℝ) <
          (C * k * 10 ^ k - k + 1 : ℕ) / (4 * (10 ^ k : ℕ)))
    (hfourier : aggregatedFourierSum Theory.PiDigits.T27.piFractionalOrbit
      (C * k * 10 ^ k - k + 1) (10 ^ k) M <
        (C * k * 10 ^ k - k + 1 : ℕ) / (2 * (10 ^ k : ℕ))) :
    Theory.PiDigits.QuantitativeBlockHitting.CoversAllLengthKWordsBy
      Theory.PiDigits.piDigit k (C * k * 10 ^ k) := by
  classical
  have hkD : k ≤ C * k * 10 ^ k := by
    calc
      k = 1 * k * 1 := by omega
      _ ≤ C * k * 10 ^ k :=
        Nat.mul_le_mul (Nat.mul_le_mul hC le_rfl)
          (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
  have hN : 0 < C * k * 10 ^ k - k + 1 := by omega
  intro w
  have ha : Theory.PiDigits.T20.wordValue (List.ofFn w) < 10 ^ k := by
    simpa only [List.length_ofFn] using
      Theory.PiDigits.T20.wordValue_lt_pow_length (List.ofFn w)
  obtain ⟨n, hn, hdigits⟩ := cylinder_hit_of_small_boundary_and_aggregated_sum
    Theory.PiDigits.T27.piFractionalOrbit
    (C * k * 10 ^ k - k + 1) (10 ^ k)
    (Theory.PiDigits.T20.wordValue (List.ofFn w)) M δ
    hN (by positivity) ha
    (fun n _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico n)
    hδ hδq hMδ (hboundary w) hfourier
  refine ⟨n, by omega, ?_⟩
  intro j
  exact (pi_digits_of_mem_wordCylinder w hdigits j).symm

/-- Literal `not C1` forces T13's unconditional dichotomy at bad lengths
beyond every positive threshold and at the exact full-containment deadline. -/
theorem not_C1_implies_unbounded_boundary_or_aggregated_resonance
    (hnotC1 : ¬ Theory.PiDigits.QuantitativeBlockHitting.C1) :
    ∀ C K : ℕ, 1 ≤ C → 1 ≤ K →
      ∃ k : ℕ, K ≤ k ∧ 1 ≤ k ∧
        ∃ w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k,
          let q := 10 ^ k
          let D := C * k * q
          let N := D - k + 1
          let a := Theory.PiDigits.T20.wordValue (List.ofFn w)
          a < q ∧
          (¬ ∃ n : ℕ, n + k ≤ D ∧
            ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
          cylinderCount Theory.PiDigits.T27.piFractionalOrbit N q a = 0 ∧
          ∀ δ : ℝ, ∀ M : ℕ, 0 < δ →
            δ ≤ 1 / (2 * (q : ℝ)) →
            2 * (q : ℝ) ≤ (M + 1 : ℝ) * δ →
            (N : ℝ) / (4 * q) ≤
                twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit N q a δ ∨
              (N : ℝ) / (2 * q) ≤
                aggregatedFourierSum
                  Theory.PiDigits.T27.piFractionalOrbit N q M := by
  classical
  intro C K hC hK
  rcases
      Theory.PiDigits.PiNoV1NaturalScaleResonance.not_C1_implies_unbounded_naturalScale_resonance
        hnotC1 C K hC hK with
    ⟨k, hKk, w, hmissing, _hresonance⟩
  have hk : 1 ≤ k := hK.trans hKk
  have ha : Theory.PiDigits.T20.wordValue (List.ofFn w) < 10 ^ k := by
    simpa only [List.length_ofFn] using
      Theory.PiDigits.T20.wordValue_lt_pow_length (List.ofFn w)
  have hkD : k ≤ C * k * 10 ^ k := by
    calc
      k = 1 * k * 1 := by omega
      _ ≤ C * k * 10 ^ k :=
        Nat.mul_le_mul (Nat.mul_le_mul hC le_rfl)
          (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
  have hN : 0 < C * k * 10 ^ k - k + 1 := by omega
  have hnone : ∀ n < C * k * 10 ^ k - k + 1,
      ¬ inCylinder (10 ^ k)
        (Theory.PiDigits.T20.wordValue (List.ofFn w))
        (Theory.PiDigits.T27.piFractionalOrbit n) := by
    intro n hn hmem
    apply hmissing
    refine ⟨n, ?_, pi_digits_of_mem_wordCylinder w hmem⟩
    omega
  have hempty : cylinderCount Theory.PiDigits.T27.piFractionalOrbit
      (C * k * 10 ^ k - k + 1) (10 ^ k)
      (Theory.PiDigits.T20.wordValue (List.ofFn w)) = 0 := by
    unfold cylinderCount
    rw [Finset.card_eq_zero]
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    simpa using hnone n
  refine ⟨k, hKk, hk, w, ?_⟩
  dsimp only
  refine ⟨ha, hmissing, hempty, ?_⟩
  intro δ M hδ hδq hMδ
  exact finite_emptyCylinder_dichotomy
    Theory.PiDigits.T27.piFractionalOrbit
    (C * k * 10 ^ k - k + 1) (10 ^ k)
    (Theory.PiDigits.T20.wordValue (List.ofFn w)) M δ
    hN (by positivity) ha
    (fun n _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico n)
    hδ hδq hMδ hempty

/-- Fully numerical literal `not C1` specialization with
`delta=1/(4*10^k)` and `M=8*(10^k)^2`. -/
theorem not_C1_implies_unbounded_explicit_boundary_or_aggregated_resonance
    (hnotC1 : ¬ Theory.PiDigits.QuantitativeBlockHitting.C1) :
    ∀ C K : ℕ, 1 ≤ C → 1 ≤ K →
      ∃ k : ℕ, K ≤ k ∧ 1 ≤ k ∧
        ∃ w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k,
          let q := 10 ^ k
          let D := C * k * q
          let N := D - k + 1
          let a := Theory.PiDigits.T20.wordValue (List.ofFn w)
          a < q ∧
          (¬ ∃ n : ℕ, n + k ≤ D ∧
            ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
          cylinderCount Theory.PiDigits.T27.piFractionalOrbit N q a = 0 ∧
          ((N : ℝ) / (4 * q) ≤
              twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit N q a
                (1 / (4 * (q : ℝ))) ∨
            (N : ℝ) / (2 * q) ≤
              aggregatedFourierSum Theory.PiDigits.T27.piFractionalOrbit
                N q (8 * q ^ 2)) := by
  intro C K hC hK
  obtain ⟨k, hKk, hk, w, hrest⟩ :=
    not_C1_implies_unbounded_boundary_or_aggregated_resonance
      hnotC1 C K hC hK
  refine ⟨k, hKk, hk, w, ?_⟩
  dsimp only at hrest ⊢
  rcases hrest with ⟨ha, hmissing, hempty, hall⟩
  refine ⟨ha, hmissing, hempty, hall (1 / (4 * ((10 ^ k : ℕ) : ℝ)))
    (8 * (10 ^ k) ^ 2) (by positivity) ?_ ?_⟩
  · have hqR : (0 : ℝ) < (10 ^ k : ℕ) := by positivity
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (10 ^ k : ℕ))
      (by positivity : (0 : ℝ) < 2 * (10 ^ k : ℕ))).2
    nlinarith
  · have hqR : (0 : ℝ) < (10 ^ k : ℕ) := by positivity
    push_cast
    field_simp
    nlinarith [sq_nonneg (((10 ^ k : ℕ) : ℝ) - 1)]

#print axioms fejerKernel_eq_aggregated
#print axioms integral_fejerKernel_tail_le
#print axioms cylinderIndicator_stable
#print axioms fejerApproximation_eq_aggregated
#print axioms norm_fejerApproximation_sub_indicator_le
#print axioms fejerEstimator_error_and_expansion
#print axioms finite_emptyCylinder_dichotomy
#print axioms cylinder_hit_of_small_boundary_and_aggregated_sum
#print axioms all_cylinders_hit_of_small_boundary_and_aggregated_sum
#print axioms finite_emptyCylinder_explicit
#print axioms pi_fullContainment_at_exact_deadline_of_smallness
#print axioms not_C1_implies_unbounded_boundary_or_aggregated_resonance
#print axioms not_C1_implies_unbounded_explicit_boundary_or_aggregated_resonance

end Theory.PiDigits.BoundaryRobustFejerDichotomy
