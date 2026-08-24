import TheoryLib.PiQuantitativeBlockHitting.T25T25PowerTenFrequencyShift
import TheoryLib.PiQuantitativeBlockHitting.T138T138PrimitiveRayCoefficientGap

/-!
# T139: exact primitive-ray boundary consumer

This file compresses the actual positive-frequency T128 obstruction along
power-of-ten rays on the finite pi orbit.  It retains the conjugate negative
frequencies and both finite endpoint blocks.  The final result is conditional:
it converts a primitive-frequency estimate into the verified T128 interval
hit, but proves no cancellation estimate for pi.
-/

noncomputable section

open Finset Set
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.PrimitiveRayBoundaryConsumer

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.DirectionalJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PowerTenFrequencyShift

abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit
abbrev phase := Theory.PiDigits.T27.phase
abbrev exponentialSum := Theory.PiDigits.T27.exponentialSum

/-- Swap the two sides of each difference in the finite Jackson index. -/
def reverseJacksonIndex {q : ℕ} : JacksonIndex q → JacksonIndex q
  | Sum.inl (r, s, u, v) => Sum.inl (s, r, v, u)
  | Sum.inr (i, j) => Sum.inr (j, i)

private lemma reverseJacksonIndex_involutive {q : ℕ} :
    Function.Involutive (@reverseJacksonIndex q) := by
  intro i
  rcases i with ⟨r, s, u, v⟩ | ⟨i, j⟩ <;> rfl

def reverseJacksonEquiv (q : ℕ) : JacksonIndex q ≃ JacksonIndex q :=
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

/-- The actual aggregated T128 coefficient is even in the frequency. -/
theorem aggregatedBoundaryCoefficient_neg (q : ℕ) (h : ℤ) :
    aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) (-h) =
      aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h := by
  classical
  unfold aggregatedCoefficient
  simp only [Finset.sum_filter]
  conv_lhs => rw [← (reverseJacksonEquiv q).sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change (if jacksonFrequency (reverseJacksonIndex i) = -h then
      boundaryCoefficient q (reverseJacksonIndex i) else 0) = _
  rw [boundaryCoefficient_reverse, jacksonFrequency_reverse]
  by_cases hh : jacksonFrequency i = h
  · simp [hh]
  · simp only [if_neg hh]
    rw [if_neg]
    omega

/-- Positive-frequency half of the exact centered T128 obstruction. -/
def positiveBoundaryFourierSum (q A N : ℕ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q,
    centeredBoundaryTerm q A h * exponentialSum piOrbit N (h : ℤ)

private lemma centeredBoundaryConjugateTerm (q A N h : ℕ) :
    star ((positiveBoundaryCoefficient q h : ℂ) *
        phase (-(h : ℤ)) (decimalCylinderCenter q A) *
        exponentialSum piOrbit N (h : ℤ)) =
      (positiveBoundaryCoefficient q h : ℂ) * phase (h : ℤ) (decimalCylinderCenter q A) *
        exponentialSum piOrbit N (-(h : ℤ)) := by
  change (starRingEnd ℂ) ((positiveBoundaryCoefficient q h : ℂ) *
      phase (-(h : ℤ)) (decimalCylinderCenter q A) *
      exponentialSum piOrbit N (h : ℤ)) = _
  rw [map_mul, map_mul, Complex.conj_ofReal, ← Theory.PiDigits.T27.phase_neg]
  rw [← Theory.PiDigits.SharperNaturalScaleResonance.exponentialSum_neg]
  simp

private def rawBoundaryTerm (q A N : ℕ) (i : JacksonIndex q) : ℂ :=
  boundaryCoefficient q i *
    phase (jacksonFrequency i) (-decimalCylinderCenter q A) *
    exponentialSum piOrbit N (jacksonFrequency i)

private def rawPositiveBoundarySum (q A N : ℕ) : ℂ :=
  ∑ i : JacksonIndex q with 0 < jacksonFrequency i, rawBoundaryTerm q A N i

private lemma rawBoundaryTerm_reverse (q A N : ℕ) (i : JacksonIndex q) :
    rawBoundaryTerm q A N (reverseJacksonIndex i) =
      star (rawBoundaryTerm q A N i) := by
  unfold rawBoundaryTerm
  rw [boundaryCoefficient_reverse, jacksonFrequency_reverse]
  change (boundaryCoefficient q i : ℂ) * phase (-jacksonFrequency i)
      (-decimalCylinderCenter q A) * exponentialSum piOrbit N (-jacksonFrequency i) = _
  change _ = (starRingEnd ℂ) ((boundaryCoefficient q i : ℂ) *
      phase (jacksonFrequency i) (-decimalCylinderCenter q A) *
      exponentialSum piOrbit N (jacksonFrequency i))
  rw [map_mul, map_mul, Complex.conj_ofReal, ← Theory.PiDigits.T27.phase_neg,
    ← Theory.PiDigits.SharperNaturalScaleResonance.exponentialSum_neg]

private lemma rawNegativeBoundarySum_eq_conj (q A N : ℕ) :
    (∑ i : JacksonIndex q with jacksonFrequency i < 0,
        rawBoundaryTerm q A N i) = star (rawPositiveBoundarySum q A N) := by
  classical
  unfold rawPositiveBoundarySum
  change _ = (starRingEnd ℂ)
    (∑ i : JacksonIndex q with 0 < jacksonFrequency i, rawBoundaryTerm q A N i)
  simp only [Finset.sum_filter]
  rw [map_sum]
  conv_lhs => rw [← (reverseJacksonEquiv q).sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change (if jacksonFrequency (reverseJacksonIndex i) < 0 then
      rawBoundaryTerm q A N (reverseJacksonIndex i) else 0) = _
  rw [jacksonFrequency_reverse, rawBoundaryTerm_reverse]
  by_cases hip : 0 < jacksonFrequency i
  · simp [hip]
  · have : ¬-jacksonFrequency i < 0 := by omega
    simp [hip, this]

private lemma centeredAggregatedNonzeroSum_re_eq_two_mul_rawPositive
    (q A N : ℕ) :
    (centeredAggregatedNonzeroSum (boundaryCoefficient q) (@jacksonFrequency q)
      piOrbit N (decimalCylinderCenter q A)).re =
      2 * (rawPositiveBoundarySum q A N).re := by
  classical
  have hraw := sum_aggregatedCoefficient_mul_ne_zero
    (boundaryCoefficient q) (@jacksonFrequency q)
    (fun h => phase h (-decimalCylinderCenter q A) * exponentialSum piOrbit N h)
  have hcenter : centeredAggregatedNonzeroSum (boundaryCoefficient q)
      (@jacksonFrequency q) piOrbit N (decimalCylinderCenter q A) =
      ∑ i : JacksonIndex q with jacksonFrequency i ≠ 0, rawBoundaryTerm q A N i := by
    unfold centeredAggregatedNonzeroSum rawBoundaryTerm
    simpa only [mul_assoc] using hraw
  have hsplit : (∑ i : JacksonIndex q with jacksonFrequency i ≠ 0,
      rawBoundaryTerm q A N i) =
      rawPositiveBoundarySum q A N +
        ∑ i : JacksonIndex q with jacksonFrequency i < 0,
          rawBoundaryTerm q A N i := by
    unfold rawPositiveBoundarySum
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : 0 < jacksonFrequency i
    · have hn : jacksonFrequency i ≠ 0 := ne_of_gt hp
      have hneg : ¬jacksonFrequency i < 0 := by omega
      simp [hp, hn, hneg]
    · by_cases hz : jacksonFrequency i = 0
      · simp [hz]
      · have hneg : jacksonFrequency i < 0 := by omega
        simp [hp, hz, hneg]
  rw [hcenter, hsplit, rawNegativeBoundarySum_eq_conj]
  simp
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
  · let i : Bool × Fin q := (false, ⟨h - q, by omega⟩)
    let j : Bool × Fin q := (true, ⟨0, hq⟩)
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr (i, j), Finset.mem_univ _, ?_⟩
    simp only [i, j, jacksonFrequency, edgeFrequency, if_false, if_true]
    push_cast
    rw [Nat.cast_sub (by omega : q ≤ h)]
    ring

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

private lemma rawPositiveBoundarySum_eq_positiveBoundaryFourierSum
    (q A N : ℕ) (hq : 0 < q) :
    rawPositiveBoundarySum q A N = positiveBoundaryFourierSum q A N := by
  classical
  have hagg := sum_aggregatedCoefficient_mul
    (boundaryCoefficient q) (@jacksonFrequency q)
    (fun h => if 0 < h then
      phase h (-decimalCylinderCenter q A) * exponentialSum piOrbit N h else 0)
  have hraw : rawPositiveBoundarySum q A N =
      ∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ with 0 < h,
        aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h *
          phase h (-decimalCylinderCenter q A) * exponentialSum piOrbit N h := by
    calc
      rawPositiveBoundarySum q A N =
          ∑ i : JacksonIndex q,
            boundaryCoefficient q i *
              (if 0 < jacksonFrequency i then
                phase (jacksonFrequency i) (-decimalCylinderCenter q A) *
                  exponentialSum piOrbit N (jacksonFrequency i) else 0) := by
            unfold rawPositiveBoundarySum rawBoundaryTerm
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hp : 0 < jacksonFrequency i <;> simp [hp] <;> ring
      _ = ∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ,
            aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h *
              (if 0 < h then phase h (-decimalCylinderCenter q A) *
                exponentialSum piOrbit N h else 0) := hagg.symm
      _ = ∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ with 0 < h,
            aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h *
              phase h (-decimalCylinderCenter q A) * exponentialSum piOrbit N h := by
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro h hh
            by_cases hp : 0 < h <;> simp [hp, mul_assoc]
  rw [hraw]
  change (∑ h ∈ (Finset.image (@jacksonFrequency q) Finset.univ).filter
      (fun h => 0 < h), _) = _
  rw [positiveFrequencyImage_eq q hq]
  unfold positiveBoundaryFourierSum centeredBoundaryTerm positiveBoundaryCoefficient
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro h hh
    push_cast
    rw [show phase (h : ℤ) (-decimalCylinderCenter q A) =
        phase (-(h : ℤ)) (decimalCylinderCenter q A) by
      unfold phase Theory.PiDigits.T27.phase
      congr 1
      push_cast
      ring]
  · intro i hi j hj hij
    exact Int.ofNat_inj.mp hij

/-- The exact signed T128 directional defect uses both conjugate halves; its
real part is twice the compressed positive-frequency half. -/
theorem directionalBoundaryDefect_eq_positiveBoundaryFourierSum
    (q A N : ℕ) (hq : 0 < q) :
    directionalBoundaryDefect piOrbit N q ((A : ℝ) / q) =
      -2 * (positiveBoundaryFourierSum q A N).re / N := by
  unfold directionalBoundaryDefect normalizedDirectionalFourierDefect
  have hcenter := centeredAggregatedNonzeroSum_re_eq_two_mul_rawPositive q A N
  rw [rawPositiveBoundarySum_eq_positiveBoundaryFourierSum q A N hq] at hcenter
  have hcenterEq : (A : ℝ) / q + (q : ℝ)⁻¹ / 2 = decimalCylinderCenter q A := by
    unfold decimalCylinderCenter
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hcenterEq, hcenter]
  ring

/-- Exact centered coefficient remaining on one primitive power-of-ten ray. -/
def primitiveRayCoefficient (q A u : ℕ) : ℂ :=
  ∑ h ∈ primitiveBoundaryFiber q u, centeredBoundaryTerm q A h

/-- The arithmetic part of the compressed obstruction.  Every displayed
frequency is primitive (not divisible by ten). -/
def primitiveBoundaryFourierSum (q A N : ℕ) : ℂ :=
  ∑ u ∈ primitiveBoundarySupport q,
    primitiveRayCoefficient q A u * exponentialSum piOrbit N (u : ℤ)

/-- Both endpoint blocks created by shifting frequency `h` down to its
primitive part. -/
def primitiveShiftEndpointBlock (N h : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (tenValuation h),
      phase (tenPrimitivePart h : ℤ) (piOrbit (N + j))) -
    exponentialSum piOrbit (tenValuation h) (tenPrimitivePart h : ℤ)

/-- Exact finite endpoint term in the simultaneous primitive-ray identity. -/
def primitiveBoundaryEndpoint (q A N : ℕ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q,
    centeredBoundaryTerm q A h * primitiveShiftEndpointBlock N h

/-- Absolute endpoint budget.  It is finite, explicit, and independent of
the prefix length `N`. -/
def primitiveBoundaryEndpointBudget (q A : ℕ) : ℝ :=
  ∑ h ∈ positiveBoundarySupport q,
    tenValuation h * ‖centeredBoundaryTerm q A h‖

private lemma exponentialSum_eq_primitive_add_endpoint (N h : ℕ) :
    exponentialSum piOrbit N (h : ℤ) =
      exponentialSum piOrbit N (tenPrimitivePart h : ℤ) +
        primitiveShiftEndpointBlock N h := by
  have hshift := pi_exponentialSum_powTen_frequency_add_boundary N
    (tenValuation h) (tenPrimitivePart h : ℤ)
  have hfreq : (10 : ℤ) ^ tenValuation h * (tenPrimitivePart h : ℤ) = h := by
    have hred := ten_reduction h
    exact_mod_cast hred
  rw [hfreq] at hshift
  unfold primitiveShiftEndpointBlock
  linear_combination hshift

/-- Exact finite-orbit primitive-ray/coboundary identity for the positive
half of the actual T128 obstruction.  No phase or endpoint is discarded. -/
theorem positiveBoundaryFourierSum_eq_primitive_add_endpoint
    (q A N : ℕ) :
    positiveBoundaryFourierSum q A N =
      primitiveBoundaryFourierSum q A N + primitiveBoundaryEndpoint q A N := by
  classical
  have hmaps : ∀ h ∈ positiveBoundarySupport q,
      tenPrimitivePart h ∈ primitiveBoundarySupport q := by
    intro h hh
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := positiveBoundarySupport q) (t := primitiveBoundarySupport q)
    (g := tenPrimitivePart) hmaps
    (fun h => centeredBoundaryTerm q A h *
      exponentialSum piOrbit N (tenPrimitivePart h : ℤ))
  unfold positiveBoundaryFourierSum primitiveBoundaryFourierSum
    primitiveRayCoefficient primitiveBoundaryEndpoint primitiveBoundaryFiber
  have hexpand :
      (∑ h ∈ positiveBoundarySupport q,
        centeredBoundaryTerm q A h * exponentialSum piOrbit N (h : ℤ)) =
      ∑ h ∈ positiveBoundarySupport q,
        (centeredBoundaryTerm q A h *
          exponentialSum piOrbit N (tenPrimitivePart h : ℤ) +
        centeredBoundaryTerm q A h * primitiveShiftEndpointBlock N h) := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [exponentialSum_eq_primitive_add_endpoint]
    ring
  rw [hexpand]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  have hpart : tenPrimitivePart h = u := (Finset.mem_filter.mp hh).2
  rw [hpart]

private lemma primitiveShiftEndpointBlock_norm_le (N h : ℕ) :
    ‖primitiveShiftEndpointBlock N h‖ ≤ 2 * tenValuation h := by
  unfold primitiveShiftEndpointBlock
  calc
    ‖(∑ j ∈ Finset.range (tenValuation h),
        phase (tenPrimitivePart h : ℤ) (piOrbit (N + j))) -
        exponentialSum piOrbit (tenValuation h) (tenPrimitivePart h : ℤ)‖ ≤
      ‖∑ j ∈ Finset.range (tenValuation h),
        phase (tenPrimitivePart h : ℤ) (piOrbit (N + j))‖ +
      ‖exponentialSum piOrbit (tenValuation h) (tenPrimitivePart h : ℤ)‖ :=
        norm_sub_le _ _
    _ ≤ tenValuation h + tenValuation h := by
      apply add_le_add
      · exact norm_sum_phase_range_le (tenValuation h) N (tenPrimitivePart h : ℤ)
      · simpa only [zero_add] using
          norm_sum_phase_range_le (tenValuation h) 0 (tenPrimitivePart h : ℤ)
    _ = 2 * tenValuation h := by ring

/-- The two endpoint blocks cost at most twice the exact endpoint budget. -/
theorem primitiveBoundaryEndpoint_norm_le (q A N : ℕ) :
    ‖primitiveBoundaryEndpoint q A N‖ ≤
      2 * primitiveBoundaryEndpointBudget q A := by
  unfold primitiveBoundaryEndpoint primitiveBoundaryEndpointBudget
  calc
    ‖∑ h ∈ positiveBoundarySupport q,
        centeredBoundaryTerm q A h * primitiveShiftEndpointBlock N h‖ ≤
      ∑ h ∈ positiveBoundarySupport q,
        ‖centeredBoundaryTerm q A h * primitiveShiftEndpointBlock N h‖ :=
          norm_sum_le _ _
    _ ≤ ∑ h ∈ positiveBoundarySupport q,
        2 * (tenValuation h * ‖centeredBoundaryTerm q A h‖) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      have hb := primitiveShiftEndpointBlock_norm_le N h
      have hn := norm_nonneg (centeredBoundaryTerm q A h)
      nlinarith
    _ = 2 * ∑ h ∈ positiveBoundarySupport q,
        tenValuation h * ‖centeredBoundaryTerm q A h‖ := by
      rw [Finset.mul_sum]

/-- Every frequency retained by the compressed arithmetic premise is
genuinely primitive for multiplication by ten. -/
theorem not_ten_dvd_of_mem_primitiveBoundarySupport
    {q u : ℕ} (hu : u ∈ primitiveBoundarySupport q) : ¬10 ∣ u := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hu
  apply ten_not_dvd_primitivePart
  simp only [positiveBoundarySupport, Finset.mem_Icc] at hh
  omega

/-- Exact full signed T128 defect after simultaneous primitive-ray
compression.  Both endpoint blocks remain visible. -/
theorem directionalBoundaryDefect_eq_primitive_add_endpoint
    (q A N : ℕ) (hq : 0 < q) :
    directionalBoundaryDefect piOrbit N q ((A : ℝ) / q) =
      -2 * (primitiveBoundaryFourierSum q A N +
        primitiveBoundaryEndpoint q A N).re / N := by
  rw [directionalBoundaryDefect_eq_positiveBoundaryFourierSum q A N hq,
    positiveBoundaryFourierSum_eq_primitive_add_endpoint]

/-- Exact endpoint accounting gives the advertised `4 E / N` upper bound
for the actual signed directional obstruction. -/
theorem directionalBoundaryDefect_le_primitive_add_four_endpointBudget
    (q A N : ℕ) (hq : 0 < q) (hN : 0 < N) :
    directionalBoundaryDefect piOrbit N q ((A : ℝ) / q) ≤
      -2 * (primitiveBoundaryFourierSum q A N).re / N +
        4 * primitiveBoundaryEndpointBudget q A / N := by
  rw [directionalBoundaryDefect_eq_primitive_add_endpoint q A N hq]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hbre :
      -(primitiveBoundaryEndpoint q A N).re ≤
        ‖primitiveBoundaryEndpoint q A N‖ := by
    exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hbnorm := primitiveBoundaryEndpoint_norm_le q A N
  rw [Complex.add_re]
  calc
    -2 * ((primitiveBoundaryFourierSum q A N).re +
        (primitiveBoundaryEndpoint q A N).re) / N ≤
      (-2 * (primitiveBoundaryFourierSum q A N).re +
        4 * primitiveBoundaryEndpointBudget q A) / N := by
          apply (div_le_div_iff_of_pos_right hNR).2
          nlinarith
    _ = -2 * (primitiveBoundaryFourierSum q A N).re / N +
        4 * primitiveBoundaryEndpointBudget q A / N := by ring

/-- Primitive-frequency-only conditional T128 consumer for the actual pi
orbit.  The strict premise retains the exact T128 zero coefficient. -/
theorem piOrbit_hit_of_primitiveBoundary_smallness
    (q A N : ℕ) (hq : 0 < q) (hA : A < q) (hN : 0 < N)
    (hsmall :
      -2 * (primitiveBoundaryFourierSum q A N).re / N +
          4 * primitiveBoundaryEndpointBudget q A / N <
        boundaryZeroCoefficient q) :
    ∃ j : ℕ, j < N ∧ piOrbit j ∈
      Set.Ico ((A : ℝ) / q) (((A : ℝ) + 1) / q) := by
  have hdefect : directionalBoundaryDefect piOrbit N q ((A : ℝ) / q) <
      boundaryZeroCoefficient q :=
    (directionalBoundaryDefect_le_primitive_add_four_endpointBudget
      q A N hq hN).trans_lt hsmall
  have haq : (A : ℝ) / q + (q : ℝ)⁻¹ ≤ 1 := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hAle : A + 1 ≤ q := by omega
    have hAleR : ((A + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hAle
    calc
      (A : ℝ) / q + (q : ℝ)⁻¹ = ((A + 1 : ℕ) : ℝ) / q := by
        rw [inv_eq_one_div]
        push_cast
        ring
      _ ≤ (q : ℝ) / q := div_le_div_of_nonneg_right hAleR hqR.le
      _ = 1 := div_self hqR.ne'
  have hhit := finite_decimalInterval_hit_of_boundary_directional_smallness
    piOrbit N q ((A : ℝ) / q) hN hq
    (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
    (by positivity) haq hdefect
  obtain ⟨j, hjN, hj⟩ := hhit
  refine ⟨j, hjN, ?_⟩
  convert hj using 1 <;> field_simp <;> ring

/-- Decimal-scale wrapper of the primitive-only T128 consumer. -/
theorem piOrbit_hit_of_primitiveBoundary_smallness_pow_ten
    (k A N : ℕ) (hk : 1 ≤ k) (hA : A < 10 ^ k) (hN : 0 < N)
    (hsmall :
      -2 * (primitiveBoundaryFourierSum (10 ^ k) A N).re / N +
          4 * primitiveBoundaryEndpointBudget (10 ^ k) A / N <
        boundaryZeroCoefficient (10 ^ k)) :
    ∃ j : ℕ, j < N ∧ piOrbit j ∈
      Set.Ico ((A : ℝ) / (10 ^ k : ℕ))
        (((A : ℝ) + 1) / (10 ^ k : ℕ)) := by
  exact piOrbit_hit_of_primitiveBoundary_smallness
    (10 ^ k) A N (pow_pos (by norm_num) _) hA hN hsmall

private lemma primitiveBoundaryFourierSum_norm_le
    (q A N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hcancel : ∀ u ∈ primitiveBoundarySupport q,
      ‖exponentialSum piOrbit N (u : ℤ)‖ ≤ ε * N) :
    ‖primitiveBoundaryFourierSum q A N‖ ≤
      ε * N * primitiveBoundaryLoad q A := by
  unfold primitiveBoundaryFourierSum primitiveBoundaryLoad primitiveRayCoefficient
  calc
    ‖∑ u ∈ primitiveBoundarySupport q,
        (∑ h ∈ primitiveBoundaryFiber q u, centeredBoundaryTerm q A h) *
          exponentialSum piOrbit N (u : ℤ)‖ ≤
      ∑ u ∈ primitiveBoundarySupport q,
        ‖(∑ h ∈ primitiveBoundaryFiber q u, centeredBoundaryTerm q A h) *
          exponentialSum piOrbit N (u : ℤ)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ primitiveBoundarySupport q,
        ‖∑ h ∈ primitiveBoundaryFiber q u, centeredBoundaryTerm q A h‖ *
          (ε * N) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hcancel u hu) (norm_nonneg _)
    _ = ε * N * ∑ u ∈ primitiveBoundarySupport q,
        ‖∑ h ∈ primitiveBoundaryFiber q u, centeredBoundaryTerm q A h‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Coefficient-gap version of the decimal-scale consumer.  It requires
cancellation only at primitive frequencies and uses T138's strict uniform
`1 / 3000000` load improvement. -/
theorem piOrbit_hit_of_uniform_primitiveCancellation_pow_ten
    (k A N : ℕ) (ε : ℝ) (hk : 1 ≤ k) (hA : A < 10 ^ k)
    (hN : 0 < N) (hε : 0 ≤ ε)
    (hcancel : ∀ u ∈ primitiveBoundarySupport (10 ^ k),
      ‖exponentialSum piOrbit N (u : ℤ)‖ ≤ ε * N)
    (hthreshold :
      2 * ε * (positiveBoundaryLoad (10 ^ k) - 1 / 3000000) +
          4 * primitiveBoundaryEndpointBudget (10 ^ k) A / N <
        boundaryZeroCoefficient (10 ^ k)) :
    ∃ j : ℕ, j < N ∧ piOrbit j ∈
      Set.Ico ((A : ℝ) / (10 ^ k : ℕ))
        (((A : ℝ) + 1) / (10 ^ k : ℕ)) := by
  let q := 10 ^ k
  have hq0 : 0 < q := pow_pos (by norm_num) _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnorm := primitiveBoundaryFourierSum_norm_le q A N ε hε hcancel
  have hre : -(primitiveBoundaryFourierSum q A N).re ≤
      ‖primitiveBoundaryFourierSum q A N‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hload := primitiveBoundaryLoad_pow_ten_lt_positiveBoundaryLoad_sub_gap
    k A hk
  have hsmall :
      -2 * (primitiveBoundaryFourierSum q A N).re / N +
          4 * primitiveBoundaryEndpointBudget q A / N <
        boundaryZeroCoefficient q := by
    apply lt_of_le_of_lt ?_ hthreshold
    dsimp [q] at hload ⊢
    have hloadLe : primitiveBoundaryLoad (10 ^ k) A ≤
        positiveBoundaryLoad (10 ^ k) - 1 / 3000000 := hload.le
    have hmain : -2 * (primitiveBoundaryFourierSum (10 ^ k) A N).re / N ≤
        2 * ε * (positiveBoundaryLoad (10 ^ k) - 1 / 3000000) := by
      rw [div_le_iff₀ hNR]
      have hεN : 0 ≤ ε * (N : ℝ) := mul_nonneg hε (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hloadLe hεN
      nlinarith
    linarith
  exact piOrbit_hit_of_primitiveBoundary_smallness_pow_ten
    k A N hk hA hN hsmall

end Theory.PiDigits.PrimitiveRayBoundaryConsumer

#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.aggregatedBoundaryCoefficient_neg
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.directionalBoundaryDefect_eq_positiveBoundaryFourierSum
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.positiveBoundaryFourierSum_eq_primitive_add_endpoint
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.primitiveBoundaryEndpoint_norm_le
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.not_ten_dvd_of_mem_primitiveBoundarySupport
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.directionalBoundaryDefect_eq_primitive_add_endpoint
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.directionalBoundaryDefect_le_primitive_add_four_endpointBudget
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.piOrbit_hit_of_primitiveBoundary_smallness
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.piOrbit_hit_of_primitiveBoundary_smallness_pow_ten
#print axioms Theory.PiDigits.PrimitiveRayBoundaryConsumer.piOrbit_hit_of_uniform_primitiveCancellation_pow_ten
