import TheoryLib.PiQuantitativeBlockHitting.T148T148ImprovedPrimitiveBoundaryConsumer

/-!
# T149: root-grid projection of the terminal boundary layers

This module projects the exact T128 boundary polynomial onto frequencies
divisible by a prescribed integer.  It then applies the projection to the
first two terminal decimal-valuation layers.  The argument is pointwise in
the cylinder label and the horizon; it is not target averaging.
-/

noncomputable section

open Finset Set
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.BoundaryRootGridProjection

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.DirectionalJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.BoundaryEndpointLayers
open Theory.PiDigits.BoundaryLayerMass
open Theory.PiDigits.BoundaryLayerScalarBounds
open Theory.PiDigits.BoundaryEndpointContraction

abbrev phase := Theory.PiDigits.T27.phase

/-- Positive-frequency polynomial on the frequencies divisible by `d`, with
the quotient frequency used in the phase. -/
def divisibleBoundaryPolynomial (q d : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q with d ∣ h,
    (positiveBoundaryCoefficient q h : ℂ) * phase ((h / d : ℕ) : ℤ) t

private lemma phase_nat_grid_sum
    (h d : ℕ) (hd : 0 < d) (t : ℝ) :
    (∑ r ∈ range d, phase (h : ℤ) ((t + r) / d)) =
      if d ∣ h then (d : ℂ) * phase ((h / d : ℕ) : ℤ) t else 0 := by
  classical
  by_cases hdiv : d ∣ h
  · obtain ⟨m, rfl⟩ := hdiv
    simp only [if_pos (dvd_mul_right d m)]
    have hquot : d * m / d = m := Nat.mul_div_cancel_left m hd
    have hterm (r : ℕ) :
        phase ((d * m : ℕ) : ℤ) ((t + r) / d) = phase (m : ℤ) t := by
      have hreduce :
          phase ((d * m : ℕ) : ℤ) ((t + r) / d) =
            phase (m : ℤ) (t + r) := by
        unfold phase Theory.PiDigits.T27.phase
        congr 1
        have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
        push_cast
        field_simp
      rw [hreduce]
      change Theory.PiDigits.T27.phase (m : ℤ) (t + (r : ℝ)) =
        Theory.PiDigits.T27.phase (m : ℤ) t
      rw [Theory.PiDigits.T27.phase_add_real]
      have hinter : phase (m : ℤ) (r : ℝ) = 1 := by
        unfold phase Theory.PiDigits.T27.phase
        convert Complex.exp_int_mul_two_pi_mul_I (m * r : ℤ) using 1
        push_cast
        ring
      change Theory.PiDigits.T27.phase (m : ℤ) (r : ℝ) = 1 at hinter
      rw [hinter, mul_one]
    simp_rw [hterm]
    rw [sum_const, card_range, nsmul_eq_mul]
    rw [hquot]
  · simp only [if_neg hdiv]
    have hsplit (r : ℕ) :
        phase (h : ℤ) ((t + r) / d) =
          phase (h : ℤ) (t / d) * phase (h : ℤ) (1 / (d : ℝ)) ^ r := by
      rw [show (t + (r : ℝ)) / d = t / d + (r : ℝ) / d by ring,
        show phase (h : ℤ) (t / d + (r : ℝ) / d) =
          phase (h : ℤ) (t / d) * phase (h : ℤ) ((r : ℝ) / d) from
            Theory.PiDigits.T27.phase_add_real _ _ _]
      congr 1
      unfold phase Theory.PiDigits.T27.phase
      have harg :
          2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
              ((((r : ℝ) / d : ℝ) : ℂ)) =
            (r : ℂ) *
              (2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) : ℂ) *
                ((((1 : ℝ) / d : ℝ) : ℂ))) := by
        push_cast
        ring
      rw [harg, Complex.exp_nat_mul]
    simp_rw [hsplit]
    rw [← Finset.mul_sum]
    let z := phase (h : ℤ) (1 / (d : ℝ))
    have hzpow : z ^ d = 1 :=
      Theory.PiDigits.SharperNaturalScaleResonance.phase_uniformGrid_root_pow
        (h : ℤ) d hd
    have hzne : z ≠ 1 := by
      intro hz
      have hexp :
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) / (d : ℂ)) = 1 := by
        change Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) /
            (d : ℂ)) = 1
        change Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
            ((((1 : ℝ) / d : ℝ) : ℂ))) = 1 at hz
        convert hz using 1
        push_cast
        field_simp
      have hdvd : d ∣ h :=
        (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hd.ne').mp hexp
      exact hdiv hdvd
    have hgeom := geom_sum_mul_neg z d
    rw [hzpow, sub_self] at hgeom
    have hsum : ∑ r ∈ range d, z ^ r = 0 :=
      (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hzne.symm)
    rw [hsum, mul_zero]

private lemma positive_frequency_represented
    (q h : ℕ) (hq : 0 < q) (hh0 : 0 < h) (hh : h ≤ 2 * q - 1) :
    (h : ℤ) ∈ Finset.image (@jacksonFrequency q) Finset.univ := by
  by_cases hlo : h ≤ q
  · let i : Bool × Fin q := (false, ⟨0, hq⟩)
    let j : Bool × Fin q := (true, ⟨q - h, by omega⟩)
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr (i, j), Finset.mem_univ _, ?_⟩
    simp only [i, j, jacksonFrequency, edgeFrequency, if_false, if_true]
    push_cast
    rw [Nat.cast_sub hlo]
    ring
  · have hhq' : q ≤ h := by omega
    let i : Bool × Fin q := (false, ⟨h - q, by omega⟩)
    let j : Bool × Fin q := (true, ⟨0, hq⟩)
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr (i, j), Finset.mem_univ _, ?_⟩
    simp only [i, j, jacksonFrequency, edgeFrequency, if_false, if_true]
    push_cast
    rw [Nat.cast_sub hhq']
    ring

private lemma jacksonFrequency_lt_two_mul
    {q : ℕ} (hq : 0 < q) (i : JacksonIndex q) :
    jacksonFrequency i < (2 * q : ℕ) := by
  rcases i with ⟨⟨r, s, u, v⟩⟩ | ⟨⟨bi, i⟩, ⟨bj, j⟩⟩
  · simp only [jacksonFrequency]
    have hr := r.isLt
    have hs := s.isLt
    have hu := u.isLt
    have hv := v.isLt
    push_cast
    omega
  · cases bi <;> cases bj <;> simp only [jacksonFrequency, edgeFrequency, if_true,
      if_false] <;> have hi := i.isLt <;> have hj := j.isLt <;> push_cast <;> omega

private lemma positiveFrequencyImage_eq (q : ℕ) (hq : 0 < q) :
    (Finset.image (@jacksonFrequency q) Finset.univ).filter (fun h => 0 < h) =
      (positiveBoundarySupport q).image (fun h : ℕ => (h : ℤ)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzimage, hzpos⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, hi, hifreq⟩ := Finset.mem_image.mp hzimage
    have hlt := jacksonFrequency_lt_two_mul hq i
    rw [hifreq] at hlt
    have hzNat : z = (z.toNat : ℤ) := (Int.toNat_of_nonneg hzpos.le).symm
    apply Finset.mem_image.mpr
    refine ⟨z.toNat, ?_, hzNat.symm⟩
    change z.toNat ∈ Finset.Icc 1 (2 * q - 1)
    simp only [Finset.mem_Icc]
    constructor
    · have : (0 : ℤ) < (z.toNat : ℤ) := by simpa only [← hzNat] using hzpos
      exact_mod_cast this
    · have hlt' : (z.toNat : ℤ) < (2 * q : ℕ) := by simpa only [← hzNat] using hlt
      have : z.toNat < 2 * q := by exact_mod_cast hlt'
      omega
  · intro hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hz
    change h ∈ Finset.Icc 1 (2 * q - 1) at hh
    simp only [Finset.mem_Icc] at hh
    apply Finset.mem_filter.mpr
    exact ⟨positive_frequency_represented q h hq (by omega) hh.2, by exact_mod_cast hh.1⟩

private lemma boundaryMinorant_eq_aggregated (q : ℕ) (t : ℝ) :
    boundaryMinorant q t =
      ∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ,
        (aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h : ℂ) *
          phase h t := by
  unfold boundaryMinorant
  simpa using (sum_aggregatedCoefficient_mul
    (boundaryCoefficient q) (@jacksonFrequency q) (fun h => phase h t)).symm

private def reverseJacksonIndex {q : ℕ} : JacksonIndex q → JacksonIndex q
  | Sum.inl (r, s, u, v) => Sum.inl (s, r, v, u)
  | Sum.inr (i, j) => Sum.inr (j, i)

private lemma reverseJacksonIndex_involutive {q : ℕ} :
    Function.Involutive (@reverseJacksonIndex q) := by
  intro i
  rcases i with ⟨r, s, u, v⟩ | ⟨i, j⟩ <;> rfl

private def reverseJacksonEquiv (q : ℕ) : JacksonIndex q ≃ JacksonIndex q :=
  { toFun := reverseJacksonIndex
    invFun := reverseJacksonIndex
    left_inv := reverseJacksonIndex_involutive
    right_inv := reverseJacksonIndex_involutive }

private lemma jacksonFrequency_reverse {q : ℕ} (i : JacksonIndex q) :
    jacksonFrequency (reverseJacksonIndex i) = -jacksonFrequency i := by
  rcases i with ⟨r, s, u, v⟩ | ⟨i, j⟩ <;>
    simp only [reverseJacksonIndex, jacksonFrequency] <;> ring

private lemma boundaryCoefficient_reverse {q : ℕ} (i : JacksonIndex q) :
    boundaryCoefficient q (reverseJacksonIndex i) = boundaryCoefficient q i := by
  rcases i with ⟨r, s, u, v⟩ | ⟨i, j⟩
  · rfl
  · simp only [reverseJacksonIndex, boundaryCoefficient]
    ring

private def rawBoundaryTerm (q : ℕ) (t : ℝ) (i : JacksonIndex q) : ℂ :=
  boundaryCoefficient q i * phase (jacksonFrequency i) t

private def rawPositiveBoundaryPolynomial (q : ℕ) (t : ℝ) : ℂ :=
  ∑ i : JacksonIndex q with 0 < jacksonFrequency i, rawBoundaryTerm q t i

private lemma rawBoundaryTerm_reverse (q : ℕ) (t : ℝ) (i : JacksonIndex q) :
    rawBoundaryTerm q t (reverseJacksonIndex i) = star (rawBoundaryTerm q t i) := by
  unfold rawBoundaryTerm
  rw [boundaryCoefficient_reverse, jacksonFrequency_reverse]
  change (boundaryCoefficient q i : ℂ) * phase (-jacksonFrequency i) t =
    (starRingEnd ℂ) ((boundaryCoefficient q i : ℂ) * phase (jacksonFrequency i) t)
  rw [map_mul, Complex.conj_ofReal, ← Theory.PiDigits.T27.phase_neg]

private lemma rawNegativeBoundaryPolynomial_eq_conj (q : ℕ) (t : ℝ) :
    (∑ i : JacksonIndex q with jacksonFrequency i < 0, rawBoundaryTerm q t i) =
      star (rawPositiveBoundaryPolynomial q t) := by
  classical
  unfold rawPositiveBoundaryPolynomial
  change _ = (starRingEnd ℂ)
    (∑ i : JacksonIndex q with 0 < jacksonFrequency i, rawBoundaryTerm q t i)
  simp only [Finset.sum_filter]
  rw [map_sum]
  conv_lhs => rw [← (reverseJacksonEquiv q).sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change (if jacksonFrequency (reverseJacksonIndex i) < 0 then
      rawBoundaryTerm q t (reverseJacksonIndex i) else 0) = _
  rw [jacksonFrequency_reverse, rawBoundaryTerm_reverse]
  by_cases hip : 0 < jacksonFrequency i
  · simp [hip]
  · have : ¬-jacksonFrequency i < 0 := by omega
    simp [hip, this]

private lemma rawPositiveBoundaryPolynomial_eq_positive
    (q : ℕ) (hq : 0 < q) (t : ℝ) :
    rawPositiveBoundaryPolynomial q t =
      ∑ h ∈ positiveBoundarySupport q,
        (positiveBoundaryCoefficient q h : ℂ) * phase (h : ℤ) t := by
  classical
  have hagg := sum_aggregatedCoefficient_mul
    (boundaryCoefficient q) (@jacksonFrequency q)
    (fun h => if 0 < h then phase h t else 0)
  have hraw : rawPositiveBoundaryPolynomial q t =
      ∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ with 0 < h,
        (aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h : ℂ) *
          phase h t := by
    calc
      rawPositiveBoundaryPolynomial q t =
          ∑ i : JacksonIndex q,
            boundaryCoefficient q i *
              (if 0 < jacksonFrequency i then phase (jacksonFrequency i) t else 0) := by
            unfold rawPositiveBoundaryPolynomial rawBoundaryTerm
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hp : 0 < jacksonFrequency i <;> simp [hp]
      _ = ∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ,
            aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h *
              (if 0 < h then phase h t else 0) := hagg.symm
      _ = ∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ with 0 < h,
            aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h *
              phase h t := by
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro h hh
            by_cases hp : 0 < h <;> simp [hp]
  rw [hraw]
  change (∑ h ∈ (Finset.image (@jacksonFrequency q) Finset.univ).filter
      (fun h => 0 < h), _) = _
  rw [positiveFrequencyImage_eq q hq]
  unfold positiveBoundaryCoefficient
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact Int.ofNat_inj.mp hij

private lemma boundaryMinorant_re_eq_zero_add_positive
    (q : ℕ) (hq : 0 < q) (t : ℝ) :
    (boundaryMinorant q t).re = boundaryZeroCoefficient q +
      2 * (∑ h ∈ positiveBoundarySupport q,
        (positiveBoundaryCoefficient q h : ℂ) * phase (h : ℤ) t).re := by
  classical
  have hsplit : boundaryMinorant q t =
      (∑ i : JacksonIndex q with jacksonFrequency i = 0, rawBoundaryTerm q t i) +
      rawPositiveBoundaryPolynomial q t +
      ∑ i : JacksonIndex q with jacksonFrequency i < 0, rawBoundaryTerm q t i := by
    unfold boundaryMinorant rawPositiveBoundaryPolynomial rawBoundaryTerm
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz : jacksonFrequency i = 0
    · simp [hz]
    · by_cases hp : 0 < jacksonFrequency i
      · have hn : ¬jacksonFrequency i < 0 := by omega
        simp [hz, hp, hn]
      · have hn : jacksonFrequency i < 0 := by omega
        simp [hz, hp, hn]
  have hzero :
      (∑ i : JacksonIndex q with jacksonFrequency i = 0, rawBoundaryTerm q t i) =
        (boundaryZeroCoefficient q : ℂ) := by
    unfold rawBoundaryTerm boundaryZeroCoefficient aggregatedCoefficient
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 := (Finset.mem_filter.mp hi).2
    rw [hi0]
    change (boundaryCoefficient q i : ℂ) *
      Theory.PiDigits.T27.phase 0 t = boundaryCoefficient q i
    rw [Theory.PiDigits.T27.phase_zero, mul_one]
  rw [hsplit, hzero, rawNegativeBoundaryPolynomial_eq_conj,
    rawPositiveBoundaryPolynomial_eq_positive q hq]
  simp
  ring

/-- Exact root-grid projection.  The spatial average is only a Fourier
projector onto one divisibility layer and remains pointwise in `t`. -/
theorem rootGridProjection_eq
    (q d : ℕ) (hq : 0 < q) (hd : 0 < d) (t : ℝ) :
    boundaryZeroCoefficient q + 2 * (divisibleBoundaryPolynomial q d t).re =
      (1 / (d : ℝ)) * ∑ r ∈ range d,
        (boundaryMinorant q ((t + r) / d)).re := by
  classical
  let P : ℕ → ℂ := fun r =>
    ∑ h ∈ positiveBoundarySupport q,
      (positiveBoundaryCoefficient q h : ℂ) * phase (h : ℤ) ((t + r) / d)
  have hproj : (∑ r ∈ range d, P r) =
      (d : ℂ) * divisibleBoundaryPolynomial q d t := by
    dsimp [P]
    rw [Finset.sum_comm]
    calc
      (∑ x ∈ positiveBoundarySupport q,
          ∑ r ∈ range d,
            (positiveBoundaryCoefficient q x : ℂ) *
              phase (x : ℤ) ((t + r) / d)) =
          ∑ x ∈ positiveBoundarySupport q,
            (positiveBoundaryCoefficient q x : ℂ) *
              (∑ r ∈ range d, phase (x : ℤ) ((t + r) / d)) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ = ∑ x ∈ positiveBoundarySupport q,
            (positiveBoundaryCoefficient q x : ℂ) *
              (if d ∣ x then (d : ℂ) * phase ((x / d : ℕ) : ℤ) t else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [phase_nat_grid_sum x d hd t]
      _ = (d : ℂ) * divisibleBoundaryPolynomial q d t := by
            unfold divisibleBoundaryPolynomial
            rw [Finset.mul_sum]
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hdx : d ∣ x <;> simp [hdx] <;> ring
  have hreproj : (∑ r ∈ range d, (P r).re) =
      (d : ℝ) * (divisibleBoundaryPolynomial q d t).re := by
    have := congrArg Complex.re hproj
    simpa using this
  have hexpand (r : ℕ) :
      (boundaryMinorant q ((t + r) / d)).re =
        boundaryZeroCoefficient q + 2 * (P r).re := by
    exact boundaryMinorant_re_eq_zero_add_positive q hq _
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
    ← Finset.mul_sum, hreproj]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- The decimal layer polynomial is the corresponding root-grid projection. -/
theorem boundaryLayerPolynomial_eq_divisible
    (q s : ℕ) (t : ℝ) :
    boundaryLayerPolynomial q s t = divisibleBoundaryPolynomial q (10 ^ s) t := by
  classical
  let d := 10 ^ s
  have hd : 0 < d := by dsimp [d]; positivity
  unfold boundaryLayerPolynomial divisibleBoundaryPolynomial
  change (∑ m ∈ Icc 1 ((2 * q - 1) / d),
      (positiveBoundaryCoefficient q (d * m) : ℂ) * phase (m : ℤ) t) =
    ∑ h ∈ (positiveBoundarySupport q).filter (fun h => d ∣ h),
      (positiveBoundaryCoefficient q h : ℂ) * phase ((h / d : ℕ) : ℤ) t
  apply Finset.sum_bij (fun m _ => d * m)
  · intro m hm
    have hm' := mem_Icc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hd (by omega), ?_⟩, dvd_mul_right d m⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hm'.2
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.mul_left_cancel hd heq
  · intro h hh
    obtain ⟨hhSupp, hhDiv⟩ := Finset.mem_filter.mp hh
    obtain ⟨m, rfl⟩ := hhDiv
    refine ⟨m, ?_, by rfl⟩
    have hh' := mem_Icc.mp hhSupp
    apply Finset.mem_Icc.mpr
    constructor
    · by_contra hm0
      have : m = 0 := by omega
      subst m
      simp at hh'
    · apply (Nat.le_div_iff_mul_le hd).2
      simpa [Nat.mul_comm] using hh'.2
  · intro m hm
    rw [Nat.mul_div_cancel_left m hd]

end Theory.PiDigits.BoundaryRootGridProjection

#print axioms Theory.PiDigits.BoundaryRootGridProjection.rootGridProjection_eq
#print axioms Theory.PiDigits.BoundaryRootGridProjection.boundaryLayerPolynomial_eq_divisible
