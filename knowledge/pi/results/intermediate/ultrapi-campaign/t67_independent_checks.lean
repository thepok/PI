import TheoryLib.PiQuantitativeBlockHitting.T67T67TwoThreeArctanShadow

/-!
Independent replay checks for T67.  These examples use both direct rational
normalization at small indices and the general exported theorems.  They are
checks, not additional research claims.
-/

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.TwoThreeArctanShadow

example : twoThreeTermCount 0 = 2 := by
  norm_num [twoThreeTermCount]

example : twoThreePairRat 0 = 10 / 3 := by
  norm_num [twoThreePairRat, arctanTermRat]

example : twoThreePairRat 1 = -35 / 162 := by
  norm_num [twoThreePairRat, arctanTermRat]

example : twoThreeLowerRat 0 = 505 / 162 := by
  norm_num [twoThreeLowerRat, twoThreeTermCount, arctanPartialRat,
    arctanTermRat]

example : twoThreeLowerRat 1 = 1538665 / 489888 := by
  norm_num [twoThreeLowerRat, twoThreeTermCount, arctanPartialRat,
    arctanTermRat]

example : (twoThreeLowerRat 0).den = 162 := by
  norm_num [twoThreeLowerRat, twoThreeTermCount, arctanPartialRat,
    arctanTermRat]

example : (twoThreeLowerRat 1).den = 489888 := by
  norm_num [twoThreeLowerRat, twoThreeTermCount, arctanPartialRat,
    arctanTermRat]

example : twoThreeUpperRat 0 = 6115 / 1944 := by
  norm_num [twoThreeUpperRat, twoThreeTermCount, arctanPartialRat,
    arctanTermRat]

example : (twoThreeUpperRat 0).den = 1944 := by
  norm_num [twoThreeUpperRat, twoThreeTermCount, arctanPartialRat,
    arctanTermRat]

example (j : ℕ) :
    padicValRat 2 (twoThreePairRat j) = 1 - 2 * (j : ℤ) :=
  padicValRat_two_twoThreePairRat j

example (n : ℕ) :
    padicValRat 2 (∑ j ∈ Finset.range (n + 1), twoThreePairRat j) =
      1 - 2 * (n : ℤ) :=
  padicValRat_two_twoThreePair_prefix n

example (K : ℕ) :
    padicValRat 2 (twoThreeLowerRat K) = -(4 * (K : ℤ) + 1) :=
  padicValRat_two_twoThreeLowerRat K

example (K : ℕ) :
    padicValNat 2 (twoThreeLowerRat K).den = 4 * K + 1 :=
  padicValNat_two_twoThreeLowerRat_den K

example (K : ℕ) :
    padicValNat 5 (twoThreeLowerRat K).den ≤ 4 * K + 1 :=
  padicValNat_five_twoThreeLowerRat_den_le K

example (K : ℕ) :
    max (padicValNat 2 (twoThreeLowerRat K).den)
        (padicValNat 5 (twoThreeLowerRat K).den) = 4 * K + 1 :=
  twoThreeLowerRat_baseTen_denominator_exponent K

example (K : ℕ) :
    twoThreeWidth K =
      4 / (((4 * K + 5 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * K + 5)) +
        4 / (((4 * K + 5 : ℕ) : ℝ) * (3 : ℝ) ^ (4 * K + 5)) :=
  twoThreeWidth_eq_explicit K

example (K : ℕ) :
    twoThreeLower K ≤ Real.pi ∧
      Real.pi ≤ twoThreeUpper K ∧
      twoThreeUpper K - twoThreeLower K = twoThreeWidth K :=
  pi_mem_twoThree_bracket K

example (K : ℕ) :
    (1 : ℝ) / 10 < (10 : ℝ) ^ (4 * K + 1) * twoThreeWidth K :=
  postTransient_scaled_width_gt_one_tenth K

-- Boundary replay: at K = 0 the exact scaled base-two contribution is 1/4,
-- already strictly wider than a one-digit decimal cylinder.
example :
    (1 : ℝ) / 10 <
      (10 : ℝ) ^ (4 * 0 + 1) *
        (4 / (((4 * 0 + 5 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * 0 + 5))) := by
  norm_num

#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValRat_two_twoThreeLowerRat
#print axioms Theory.PiDigits.TwoThreeArctanShadow.padicValNat_two_twoThreeLowerRat_den
#print axioms
  Theory.PiDigits.TwoThreeArctanShadow.twoThreeLowerRat_baseTen_denominator_exponent
#print axioms Theory.PiDigits.TwoThreeArctanShadow.pi_mem_twoThree_bracket
#print axioms
  Theory.PiDigits.TwoThreeArctanShadow.postTransient_scaled_width_gt_one_tenth
