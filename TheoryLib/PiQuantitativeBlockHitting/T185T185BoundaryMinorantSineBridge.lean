import TheoryLib.PiQuantitativeBlockHitting.T150T150BoundaryKernelFloors
import TheoryLib.PiQuantitativeBlockHitting.T174T174FinitePrimitiveScoreIdentity

/-!
# T185: closed sine bridge for the finite primitive score

This module exposes the exact sine quotient hidden behind the boundary
minorant and connects it directly to the finite spatial identity of T174.
The only exceptional case is the removable singularity at an integral phase,
which is kept as the explicit hypothesis `sin (pi * t) != 0` expected by a
reflected interval certificate.

No numerical payload and no cancellation estimate occurs here.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.T185BoundaryMinorantSineBridge

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.BoundaryKernelFloors
open Theory.PiDigits.FinitePrimitiveScoreIdentity

/-- Public restatement of the exact normalized Fejer sine quotient used by
T150.  This is the semantic target for reflected sine intervals. -/
theorem fejerFactor_eq_closed_sine
    (q : ℕ) (hq : 0 < q) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    fejerFactor q t =
      Real.sin (Real.pi * q * t) ^ 2 /
        ((q : ℝ) * Real.sin (Real.pi * t) ^ 2) := by
  exact fejerFactor_eq_sine_quotient q hq t hsin

/-- Exact real closed sine form of the boundary minorant away from the
removable singularity. -/
theorem boundaryMinorant_re_eq_closed_sine
    (q : ℕ) (hq : 0 < q) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    (boundaryMinorant q t).re =
      (Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q)) *
        (Real.sin (Real.pi * q * t) ^ 2 /
          ((q : ℝ) * Real.sin (Real.pi * t) ^ 2)) ^ 2 := by
  rw [boundaryMinorant_eq q hq, fejerFactor_eq_closed_sine q hq t hsin]
  rfl

/-- T174's literal zero-mode/positive-frequency decomposition with the
T129 closed zero coefficient substituted. -/
theorem boundaryMinorant_re_eq_closed_zero_add_positive
    (q : ℕ) (hq : 0 < q) (t : ℝ) :
    (boundaryMinorant q t).re =
      (2 * ((q : ℝ) ^ 2 - 1) -
          (2 * (q : ℝ) ^ 2 + 1) * Real.cos (Real.pi / q)) /
          (3 * (q : ℝ)) +
        2 * (∑ h ∈ positiveBoundarySupport q,
          (positiveBoundaryCoefficient q h : ℂ) *
            Theory.PiDigits.T27.phase (h : ℤ) t).re := by
  rw [boundaryMinorant_re_eq_zero_add_positive q hq t,
    boundaryZeroCoefficient_eq q hq]

/-- Direct equality between a reflected closed-sine evaluation and the
literal positive-frequency polynomial, including the exact signed zero mode.
-/
theorem closed_sine_eq_closed_zero_add_positive
    (q : ℕ) (hq : 0 < q) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    (Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q)) *
        (Real.sin (Real.pi * q * t) ^ 2 /
          ((q : ℝ) * Real.sin (Real.pi * t) ^ 2)) ^ 2 =
      (2 * ((q : ℝ) ^ 2 - 1) -
          (2 * (q : ℝ) ^ 2 + 1) * Real.cos (Real.pi / q)) /
          (3 * (q : ℝ)) +
        2 * (∑ h ∈ positiveBoundarySupport q,
          (positiveBoundaryCoefficient q h : ℂ) *
            Theory.PiDigits.T27.phase (h : ℤ) t).re := by
  rw [← boundaryMinorant_re_eq_closed_sine q hq t hsin]
  exact boundaryMinorant_re_eq_closed_zero_add_positive q hq t

/-- The positive-frequency real part isolated from the reflected closed sine
form.  This version is convenient when a certificate bounds the kernel value
before it is summed over orbit points. -/
theorem two_mul_positiveBoundaryPolynomial_re_eq_closed_sine_sub_zero
    (q : ℕ) (hq : 0 < q) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    2 * (∑ h ∈ positiveBoundarySupport q,
          (positiveBoundaryCoefficient q h : ℂ) *
            Theory.PiDigits.T27.phase (h : ℤ) t).re =
      (Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q)) *
          (Real.sin (Real.pi * q * t) ^ 2 /
            ((q : ℝ) * Real.sin (Real.pi * t) ^ 2)) ^ 2 -
        (2 * ((q : ℝ) ^ 2 - 1) -
          (2 * (q : ℝ) ^ 2 + 1) * Real.cos (Real.pi / q)) /
          (3 * (q : ℝ)) := by
  have hclosed := closed_sine_eq_closed_zero_add_positive q hq t hsin
  linarith

/-- T174 with every spatial boundary-minorant leaf replaced by its exact
closed sine expression.  This is the final algebraic interface needed by a
reflected arithmetic payload; the primitive endpoint and signed zero mode
remain visible with their literal signs. -/
theorem two_mul_primitiveBoundaryFourierSum_re_eq_closed_sine_score
    (q A N : ℕ) (hq : 0 < q) (hN : 0 < N)
    (hsin : ∀ n ∈ range N,
      Real.sin (Real.pi *
        (piOrbit n - decimalCylinderCenter q A)) ≠ 0) :
    2 * (primitiveBoundaryFourierSum q A N).re =
      (∑ n ∈ range N,
        (Real.cos (2 * Real.pi *
              (piOrbit n - decimalCylinderCenter q A)) -
            Real.cos (Real.pi / q)) *
          (Real.sin (Real.pi * q *
                (piOrbit n - decimalCylinderCenter q A)) ^ 2 /
            ((q : ℝ) * Real.sin (Real.pi *
                (piOrbit n - decimalCylinderCenter q A)) ^ 2)) ^ 2) -
        (N : ℝ) * boundaryZeroCoefficient q -
        2 * (primitiveBoundaryEndpoint q A N).re := by
  have hbase := two_mul_primitiveBoundaryFourierSum_re_eq_finite_score
    q A N hq hN
  have hsum :
      (∑ n ∈ range N,
          (boundaryMinorant q
            (piOrbit n - decimalCylinderCenter q A)).re) =
        ∑ n ∈ range N,
          (Real.cos (2 * Real.pi *
                (piOrbit n - decimalCylinderCenter q A)) -
              Real.cos (Real.pi / q)) *
            (Real.sin (Real.pi * q *
                  (piOrbit n - decimalCylinderCenter q A)) ^ 2 /
              ((q : ℝ) * Real.sin (Real.pi *
                  (piOrbit n - decimalCylinderCenter q A)) ^ 2)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    exact boundaryMinorant_re_eq_closed_sine q hq _ (hsin n hn)
  rw [hbase, hsum]

end Theory.PiDigits.T185BoundaryMinorantSineBridge

#print axioms Theory.PiDigits.T185BoundaryMinorantSineBridge.fejerFactor_eq_closed_sine
#print axioms Theory.PiDigits.T185BoundaryMinorantSineBridge.boundaryMinorant_re_eq_closed_sine
#print axioms Theory.PiDigits.T185BoundaryMinorantSineBridge.boundaryMinorant_re_eq_closed_zero_add_positive
#print axioms Theory.PiDigits.T185BoundaryMinorantSineBridge.closed_sine_eq_closed_zero_add_positive
#print axioms Theory.PiDigits.T185BoundaryMinorantSineBridge.two_mul_positiveBoundaryPolynomial_re_eq_closed_sine_sub_zero
#print axioms Theory.PiDigits.T185BoundaryMinorantSineBridge.two_mul_primitiveBoundaryFourierSum_re_eq_closed_sine_score
