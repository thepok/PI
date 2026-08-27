import TheoryLib.PiQuantitativeBlockHitting.T66T66HuttonDecimalTransient

open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonFiveAdicTransient
open Theory.PiDigits.HuttonDecimalTransient
open Theory.PiDigits.MachinGridStability

example : huttonLowerRat 0 = 87112 / 27783 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

-- The first nontrivial five-primary range is also an exact direct reduction:
-- its denominator is odd and contains one factor of five.
example : huttonLowerRat 1 = 198037417616 / 63038098935 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

example : (huttonLowerRat 1).den = 63038098935 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

example : padicValNat 2 (huttonLowerRat 1).den = 0 := by
  rw [show (huttonLowerRat 1).den = 63038098935 by
    norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]]
  exact padicValNat.eq_zero_of_not_dvd (by norm_num)

example : padicValNat 5 (huttonLowerRat 1).den = 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [show (huttonLowerRat 1).den = 63038098935 by
    norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]]
  rw [show 63038098935 = 5 * 12607619787 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

example : padicValRat 2 (huttonPairRat 0) = 2 := by
  exact padicValRat_two_huttonPairRat 0

example : (2 : ℤ) ≤ padicValRat 2 (huttonLowerRat 7) := by
  exact two_le_padicValRat_two_huttonLowerRat 7

example : Odd (huttonLowerRat 0).den := by
  exact huttonLowerRat_den_odd 0

example : Odd (huttonLowerRat 18).den := by
  exact huttonLowerRat_den_odd 18

example : padicValNat 2 (huttonLowerRat 18).den = 0 := by
  exact padicValNat_two_huttonLowerRat_den 18

example :
    max (padicValNat 2 (huttonLowerRat 0).den)
        (padicValNat 5 (huttonLowerRat 0).den) = 0 := by
  exact huttonLowerRat_baseTen_denominator_exponent
    0 0 (by norm_num) (by norm_num)

example :
    max (padicValNat 2 (huttonLowerRat 18).den)
        (padicValNat 5 (huttonLowerRat 18).den) = 2 := by
  exact huttonLowerRat_baseTen_denominator_exponent
    18 2 (by norm_num) (by norm_num)

-- Check the first admissible `R = 4*K+3` above `5^2`: `R=27`, `K=6`.
example :
    max (padicValNat 2 (huttonLowerRat 6).den)
        (padicValNat 5 (huttonLowerRat 6).den) = 2 := by
  exact huttonLowerRat_baseTen_denominator_exponent
    6 2 (by norm_num) (by norm_num)

-- `R=123` is the last admissible value below `5^3=125`, while `R=127`
-- is the first admissible value above it.
example :
    max (padicValNat 2 (huttonLowerRat 30).den)
        (padicValNat 5 (huttonLowerRat 30).den) = 2 := by
  exact huttonLowerRat_baseTen_denominator_exponent
    30 2 (by norm_num) (by norm_num)

example :
    max (padicValNat 2 (huttonLowerRat 31).den)
        (padicValNat 5 (huttonLowerRat 31).den) = 3 := by
  exact huttonLowerRat_baseTen_denominator_exponent
    31 3 (by norm_num) (by norm_num)

#print axioms Theory.PiDigits.HuttonDecimalTransient.huttonLowerRat_den_odd
#print axioms
  Theory.PiDigits.HuttonDecimalTransient.huttonLowerRat_baseTen_denominator_exponent
