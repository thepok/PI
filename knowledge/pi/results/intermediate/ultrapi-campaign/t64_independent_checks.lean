import TheoryLib.PiQuantitativeBlockHitting.T64T64HuttonOneThirdPrimeProduct

open Finset

namespace T64IndependentChecks

open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonOneThirdPrimeProduct

-- At K = 2, R = 11: the prime at the closed upper endpoint is included.
example : huttonOneThirdPrimeSet 2 = {11} := by decide

example : huttonOneThirdPrimeProduct 2 = 11 := by decide

example : 11 ∣ (huttonLowerRat 2).den := by
  exact huttonOneThirdPrime_dvd_huttonLowerRat_den 2 11 (by decide)

-- At K = 3, R = 15: precisely the primes 11 and 13 survive the filters.
example : huttonOneThirdPrimeSet 3 = {11, 13} := by decide

example : huttonOneThirdPrimeProduct 3 = 143 := by decide

-- At K = 4, R = 19: 17 is deliberately excluded, while R itself is included.
example : huttonOneThirdPrimeSet 4 = {11, 13, 19} := by decide

-- At K = 9, R = 39 = 3 * 13: the lower endpoint is strict.
example : 13 ∉ huttonOneThirdPrimeSet 9 := by decide

example : 19 ∈ huttonOneThirdPrimeSet 9 := by decide

-- A concrete instance of the exact denominator multiplicity theorem.
example : padicValNat 11 (huttonLowerRat 2).den = 1 := by
  exact padicValNat_huttonLowerRat_den_oneThirdPrime
    2 5 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

end T64IndependentChecks

#print axioms
  Theory.PiDigits.HuttonOneThirdPrimeProduct.padicValRat_huttonLowerRat_oneThirdPrime
#print axioms
  Theory.PiDigits.HuttonOneThirdPrimeProduct.huttonOneThirdPrimeProduct_dvd_huttonLowerRat_den
