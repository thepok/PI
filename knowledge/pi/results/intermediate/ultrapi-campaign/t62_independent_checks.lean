import TheoryLib.PiQuantitativeBlockHitting.T62T62HuttonEligiblePrimeProduct

open Theory.PiDigits.HuttonEligiblePrimeProduct
open Theory.PiDigits.HuttonRationalShadow

-- Kernel-reduced boundary checks; deliberately no `native_decide`.
example : huttonEligiblePrimeSet 0 = ∅ := by decide
example : huttonEligiblePrimeSet 1 = ∅ := by decide
example : huttonEligiblePrimeSet 2 = {11} := by decide
example : huttonEligiblePrimeSet 3 = {11, 13} := by decide
example : huttonEligiblePrimeSet 4 = {11, 13, 19} := by decide
example : huttonEligiblePrimeProduct 0 = 1 := by decide
example : huttonEligiblePrimeProduct 1 = 1 := by decide
example : huttonEligiblePrimeProduct 2 = 11 := by decide
example : huttonEligiblePrimeProduct 3 = 143 := by decide
example : huttonEligiblePrimeProduct 4 = 2717 := by decide

example : (huttonLowerRat 0).den = 27783 := by
  norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
    Theory.PiDigits.MachinGridStability.arctanTermRat]

example : (huttonLowerRat 2).den = 19265262529822155 := by
  norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
    Theory.PiDigits.MachinGridStability.arctanTermRat]

example : (huttonLowerRat 4).den = 179980826858896989916014909885 := by
  norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
    Theory.PiDigits.MachinGridStability.arctanTermRat]

example : 11 ∣ (huttonLowerRat 2).den := by
  rw [show (huttonLowerRat 2).den = 19265262529822155 by
    norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
      Theory.PiDigits.MachinGridStability.arctanTermRat]]
  norm_num

example : ¬ 11 ^ 2 ∣ (huttonLowerRat 2).den := by
  rw [show (huttonLowerRat 2).den = 19265262529822155 by
    norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
      Theory.PiDigits.MachinGridStability.arctanTermRat]]
  norm_num

example : 2717 ∣ (huttonLowerRat 4).den := by
  rw [show (huttonLowerRat 4).den = 179980826858896989916014909885 by
    norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
      Theory.PiDigits.MachinGridStability.arctanTermRat]]
  norm_num

example : ¬ 11 ^ 2 ∣ (huttonLowerRat 4).den := by
  rw [show (huttonLowerRat 4).den = 179980826858896989916014909885 by
    norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
      Theory.PiDigits.MachinGridStability.arctanTermRat]]
  norm_num

example : ¬ 13 ^ 2 ∣ (huttonLowerRat 4).den := by
  rw [show (huttonLowerRat 4).den = 179980826858896989916014909885 by
    norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
      Theory.PiDigits.MachinGridStability.arctanTermRat]]
  norm_num

example : ¬ 19 ^ 2 ∣ (huttonLowerRat 4).den := by
  rw [show (huttonLowerRat 4).den = 179980826858896989916014909885 by
    norm_num [huttonLowerRat, Theory.PiDigits.MachinGridStability.arctanPartialRat,
      Theory.PiDigits.MachinGridStability.arctanTermRat]]
  norm_num
