import TheoryLib.PiQuantitativeBlockHitting.T140T140MixedOrderBoundaryKernel
import TheoryLib.PiQuantitativeBlockHitting.T149T149BoundaryRootGridProjection

/-!
# T174: exact finite primitive score identity

This module exposes the real Fourier decomposition of the T128 boundary
minorant and identifies the real primitive score with its exact finite
spatial score.  Both the signed zero mode and the primitive-shift endpoint
are retained.  No positivity or numerical information about the pi orbit is
asserted.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.FinitePrimitiveScoreIdentity

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.DirectionalJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.BoundaryRootGridProjection
open Theory.PiDigits.MixedOrderBoundaryKernel

abbrev phase := Theory.PiDigits.T27.phase

/-- The T128 boundary minorant is its signed zero coefficient plus twice the
real part of its positive-frequency polynomial. -/
theorem boundaryMinorant_re_eq_zero_add_positive
    (q : ℕ) (hq : 0 < q) (t : ℝ) :
    (boundaryMinorant q t).re = boundaryZeroCoefficient q +
      2 * (∑ h ∈ positiveBoundarySupport q,
        (positiveBoundaryCoefficient q h : ℂ) * phase (h : ℤ) t).re := by
  have hprojection := rootGridProjection_eq q 1 hq (by norm_num) t
  simpa [divisibleBoundaryPolynomial] using hprojection.symm

/-- Exact finite spatial-score identity for the primitive T139 sum.  The
normalization has no hidden average: the spatial sum is unnormalized, so the
zero mode occurs with multiplicity `N`.  The primitive-shift endpoint enters
with a minus sign when the primitive score is isolated. -/
theorem two_mul_primitiveBoundaryFourierSum_re_eq_finite_score
    (q A N : ℕ) (hq : 0 < q) (hN : 0 < N) :
    2 * (primitiveBoundaryFourierSum q A N).re =
      (∑ n ∈ range N,
          (boundaryMinorant q
            (piOrbit n - decimalCylinderCenter q A)).re) -
        (N : ℝ) * boundaryZeroCoefficient q -
        2 * (primitiveBoundaryEndpoint q A N).re := by
  have havg := normalizedDirectionalFourierDefect_eq_zero_sub_average
    (boundaryCoefficient q) (@jacksonFrequency q) (boundaryMinorant q)
    (fun t => rfl) piOrbit N (decimalCylinderCenter q A) hN
  have hcenter : (A : ℝ) / q + (q : ℝ)⁻¹ / 2 =
      decimalCylinderCenter q A := by
    unfold decimalCylinderCenter
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp
  have hdir := directionalBoundaryDefect_eq_positiveBoundaryFourierSum q A N hq
  unfold directionalBoundaryDefect at hdir
  rw [hcenter] at hdir
  have hprimitive := congrArg Complex.re
    (positiveBoundaryFourierSum_eq_primitive_add_endpoint q A N)
  simp only [Complex.add_re] at hprimitive
  rw [hdir, hprimitive] at havg
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNR] at havg
  unfold boundaryZeroCoefficient
  linarith

end Theory.PiDigits.FinitePrimitiveScoreIdentity

#print axioms Theory.PiDigits.FinitePrimitiveScoreIdentity.boundaryMinorant_re_eq_zero_add_positive
#print axioms Theory.PiDigits.FinitePrimitiveScoreIdentity.two_mul_primitiveBoundaryFourierSum_re_eq_finite_score
