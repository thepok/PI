import TheoryLib.PiQuantitativeBlockHitting.T63T63HuttonFiveAdicTransient

/-!
Independent concrete replay for T63.  These checks deliberately exercise:

* the `K = 0`, `e = 0` two-minimum case;
* the one-minimum layer immediately after `5^1` enters;
* the last one-minimum prefix before `3 * 5^1` enters;
* the two-minimum boundary `3 * 5^1 = 4K+3`;
* the analogous one- and two-minimum cases at exponent two.
-/

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonFiveAdicTransient

example : fiveMinimumLayerNumerator 0 = 87112 := by
  norm_num [fiveMinimumLayerNumerator,
    Theory.PiDigits.HuttonUpperHalfPrimeSurvival.huttonCancellationFactor]

example : fiveMinimumLayerDenominator 0 = 27783 := by
  norm_num [fiveMinimumLayerDenominator]

example : huttonLowerRat 0 = (87112 : ℚ) / 27783 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

example : padicValRat 5 (huttonLowerRat 0) = 0 := by
  exact padicValRat_five_huttonLowerRat 0 0 (by norm_num) (by norm_num)

example : padicValNat 5 (huttonLowerRat 0).den = 0 := by
  exact padicValNat_five_huttonLowerRat_den 0 0 (by norm_num) (by norm_num)

-- `R = 7`: only the exponent `5` is in the minimum layer.
example : padicValRat 5 (huttonLowerRat 1) = -1 := by
  exact padicValRat_five_huttonLowerRat 1 1 (by norm_num) (by norm_num)

example : padicValNat 5 (huttonLowerRat 1).den = 1 := by
  exact padicValNat_five_huttonLowerRat_den 1 1 (by norm_num) (by norm_num)

-- Direct rational normalization, independent of the valuation theorem.
example : (huttonLowerRat 1).den % 5 = 0 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

example : (huttonLowerRat 1).den % 25 ≠ 0 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

-- `R = 11`: the final one-minimum prefix before exponent `15` enters.
example : padicValRat 5 (huttonLowerRat 2) = -1 := by
  exact padicValRat_five_huttonLowerRat 2 1 (by norm_num) (by norm_num)

-- `R = 15`: the second minimum exponent enters at the closed endpoint.
example : padicValRat 5 (huttonLowerRat 3) = -1 := by
  exact padicValRat_five_huttonLowerRat 3 1 (by norm_num) (by norm_num)

example : padicValNat 5 (huttonLowerRat 3).den = 1 := by
  exact padicValNat_five_huttonLowerRat_den 3 1 (by norm_num) (by norm_num)

-- The two-minimum layer also survives direct rational normalization.
example : (huttonLowerRat 3).den % 5 = 0 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

example : (huttonLowerRat 3).den % 25 ≠ 0 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

-- `R = 27`: one-minimum case for `e = 2`.
example : padicValRat 5 (huttonLowerRat 6) = -2 := by
  exact padicValRat_five_huttonLowerRat 6 2 (by norm_num) (by norm_num)

-- `R = 75`: two-minimum boundary for `e = 2`.
example : padicValRat 5 (huttonLowerRat 18) = -2 := by
  exact padicValRat_five_huttonLowerRat 18 2 (by norm_num) (by norm_num)

example : padicValNat 5 (huttonLowerRat 18).den = 2 := by
  exact padicValNat_five_huttonLowerRat_den 18 2 (by norm_num) (by norm_num)

#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_huttonLowerRat
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValNat_five_huttonLowerRat_den
