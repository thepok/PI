import TheoryLib.PiQuantitativeBlockHitting.T68T68HuttonSimultaneousPrimary

/-!
Independent audit checks for T68.

These examples pin the first admissible parameter `a = 2`, including the
quotient-based index and the exact reduced-denominator valuations.  They
also specialize the two generic score-gap theorems at that boundary.  No
new theorem is exported to `TheoryLib`.
-/

open Theory.PiDigits.HuttonUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonRationalShadow

namespace Theory.PiDigits.HuttonSimultaneousPrimary.T68IndependentChecks

example : primaryRadius 2 = 3087 := by
  norm_num [primaryRadius]

example : primaryIndex 2 = 771 := by
  norm_num [primaryIndex, primaryRadius]

example : primaryLastIndex 2 = 1543 := by
  norm_num [primaryLastIndex, primaryIndex, primaryRadius]

example : 4 * primaryIndex 2 + 3 = 3087 := by
  norm_num [primaryIndex, primaryRadius]

example : 2 * primaryLastIndex 2 + 1 = 3087 := by
  norm_num [primaryLastIndex, primaryIndex, primaryRadius]

example : huttonTermCount (primaryIndex 2) = 1544 := by
  norm_num [huttonTermCount, primaryIndex, primaryRadius]

example :
    padicValNat 3 (huttonLowerRat (primaryIndex 2)).den = 3089 := by
  simpa [primaryRadius] using
    padicValNat_three_huttonLowerRat_den_primary 2 (by norm_num)

example :
    padicValNat 7 (huttonLowerRat (primaryIndex 2)).den = 3090 := by
  simpa [primaryRadius] using
    padicValNat_seven_huttonLowerRat_den_primary 2 (by norm_num)

example :
    padicValRat 3 (huttonLowerRat (primaryIndex 2)) = -3089 := by
  simpa [primaryRadius] using
    padicValRat_three_huttonLowerRat_primary 2 (by norm_num)

example :
    padicValRat 7 (huttonLowerRat (primaryIndex 2)) = -3090 := by
  simpa [primaryRadius] using
    padicValRat_seven_huttonLowerRat_primary 2 (by norm_num)

example (r : ℕ) (hrOdd : Odd r) (hrPos : 0 < r) (hr : r < 3087) :
    r + padicValNat 3 r ≤ 3085 := by
  simpa [primaryRadius] using
    primary_three_score_gap 2 r (by norm_num) hrOdd hrPos
      (by simpa [primaryRadius] using hr)

example (r : ℕ) (hrOdd : Odd r) (hrPos : 0 < r) (hr : r < 3087) :
    r + padicValNat 7 r ≤ 3085 := by
  simpa [primaryRadius] using
    primary_seven_score_gap 2 r (by norm_num) hrOdd hrPos
      (by simpa [primaryRadius] using hr)

end Theory.PiDigits.HuttonSimultaneousPrimary.T68IndependentChecks
