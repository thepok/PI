import TheoryLib.PiPositiveDecimalFactorEntropy.T1CanonicalEntropy
import TheoryLib.PiPositiveDecimalFactorEntropy.T3FiniteFourierObstruction
import TheoryLib.PiPositiveDecimalFactorEntropy.T8T8DyadicShellFejer
import TheoryLib.PiPositiveDecimalFactorEntropy.T18T18FiniteCircleQuantization

/-!
# T90: public housekeeping interface

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This additive module is the single import surface for the public T1 factor
split, T3 finite Parseval, T8 attained circle-distance representative, and T18
two-point exponential estimate.  Those declarations already exist in accepted
modules, so they are imported rather than redeclared.

In particular, this module asserts no equality between T3's Fourier
coefficient of the uniform distribution on distinct factor cells and T10's
time-indexed ordinary orbit sum.  T18 supplies a separate, per-sample floor
quantization of an orbit multiplicity measure; it does not identify that
measure with T3's distinct-factor distribution or provide the common
scale-uniform finite set required by the inverse results audited in T15.
-/

namespace DecimalFactorEntropy.T90Housekeeping

#check DecimalFactorEntropy.splitFactor_injective
#check DecimalFactorEntropy.canonicalFactorComplexity_submultiplicative
#check DecimalFactorEntropy.FiniteFourierObstruction.finiteFourier_parseval
#check DecimalFactorComplexity.DyadicShellFejer.exists_int_circleDistance_eq_abs_le_half
#check DecimalFactorComplexity.FiniteCircleQuantization.norm_exp_I_mul_sub_exp_I_mul_le
#check DecimalFactorComplexity.FiniteCircleQuantization.finiteFourier_orbitCellMeasure_eq
#check DecimalFactorComplexity.FiniteCircleQuantization.simultaneous_quantizedOrbitSum_error

end DecimalFactorEntropy.T90Housekeeping

#print axioms DecimalFactorEntropy.splitFactor_injective
#print axioms DecimalFactorEntropy.canonicalFactorComplexity_submultiplicative
#print axioms DecimalFactorEntropy.FiniteFourierObstruction.finiteFourier_parseval
#print axioms DecimalFactorComplexity.DyadicShellFejer.exists_int_circleDistance_eq_abs_le_half
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.norm_exp_I_mul_sub_exp_I_mul_le
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.finiteFourier_orbitCellMeasure_eq
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.simultaneous_quantizedOrbitSum_error
