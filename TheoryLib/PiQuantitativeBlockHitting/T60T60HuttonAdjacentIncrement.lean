import TheoryLib.PiQuantitativeBlockHitting.T58T58HuttonRationalShadow

/-!
# T60: exact adjacent increments of the rational Hutton shadows

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module makes the elementary adjacent-increment calculation for the
Hutton lower approximants exact.  It is the rational identity used by the
subsequent denominator/period analysis.  It proves no valuation bound,
decimal-cylinder hit, distribution statement, or every-word theorem for pi.
-/

noncomputable section

namespace Theory.PiDigits.HuttonAdjacentIncrement

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.HuttonRationalShadow

/-- Passing from `K` to `K+1` adds exactly two Taylor terms in each of the
two arctangent series. -/
theorem huttonLowerRat_succ_sub_terms (K : ℕ) :
    huttonLowerRat (K + 1) - huttonLowerRat K =
      8 * (arctanTermRat 3 (2 * (K + 1)) +
        arctanTermRat 3 (2 * (K + 1) + 1)) +
      4 * (arctanTermRat 7 (2 * (K + 1)) +
        arctanTermRat 7 (2 * (K + 1) + 1)) := by
  unfold huttonLowerRat
  rw [show 2 * (K + 1 + 1) = 2 * (K + 1) + 2 by omega]
  rw [arctanPartialRat_add_two, arctanPartialRat_add_two]
  ring

/-- Closed form of the adjacent increment.  With `R = 4*K+7`, this is

`16*(4*R+1)/(R*(R-2)*3^R) + 8*(24*R+1)/(R*(R-2)*7^R)`.

In particular, both summands are visibly positive. -/
theorem huttonLowerRat_succ_sub_eq (K : ℕ) :
    huttonLowerRat (K + 1) - huttonLowerRat K =
      16 * ((16 * K + 29 : ℕ) : ℚ) /
          (((4 * K + 7 : ℕ) : ℚ) * ((4 * K + 5 : ℕ) : ℚ) *
            (3 : ℚ) ^ (4 * K + 7)) +
      8 * ((96 * K + 169 : ℕ) : ℚ) /
          (((4 * K + 7 : ℕ) : ℚ) * ((4 * K + 5 : ℕ) : ℚ) *
            (7 : ℚ) ^ (4 * K + 7)) := by
  rw [huttonLowerRat_succ_sub_terms]
  unfold arctanTermRat
  have h3pow :
      (3 : ℚ) ^ (4 * K + 7) = (3 : ℚ) ^ (4 * K + 5) * 3 ^ 2 := by
    rw [show 4 * K + 7 = 4 * K + 5 + 2 by omega, pow_add]
  have h7pow :
      (7 : ℚ) ^ (4 * K + 7) = (7 : ℚ) ^ (4 * K + 5) * 7 ^ 2 := by
    rw [show 4 * K + 7 = 4 * K + 5 + 2 by omega, pow_add]
  simp only [Even.neg_one_pow (even_two_mul (K + 1)), one_mul]
  rw [show 2 * (2 * (K + 1)) + 1 = 4 * K + 5 by omega]
  rw [show 2 * (2 * (K + 1) + 1) + 1 = 4 * K + 7 by omega]
  simp only [Odd.neg_one_pow (odd_two_mul_add_one (K + 1)), neg_mul]
  rw [inv_pow, inv_pow, inv_pow, inv_pow]
  rw [h3pow, h7pow]
  push_cast
  field_simp
  ring

/-- The rational Hutton lower approximants strictly increase at every
adjacent step. -/
theorem huttonLowerRat_strictMono_step (K : ℕ) :
    huttonLowerRat K < huttonLowerRat (K + 1) := by
  apply sub_pos.mp
  rw [huttonLowerRat_succ_sub_eq]
  positivity

end Theory.PiDigits.HuttonAdjacentIncrement

#print axioms Theory.PiDigits.HuttonAdjacentIncrement.huttonLowerRat_succ_sub_terms
#print axioms Theory.PiDigits.HuttonAdjacentIncrement.huttonLowerRat_succ_sub_eq
#print axioms Theory.PiDigits.HuttonAdjacentIncrement.huttonLowerRat_strictMono_step
