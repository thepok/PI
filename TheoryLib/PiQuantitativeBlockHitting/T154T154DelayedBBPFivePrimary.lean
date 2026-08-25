import TheoryLib.PiQuantitativeBlockHitting.T141T141ScaledBBPFiveAdicNumerator

/-!
# T154: delayed removal of the five-primary BBP numerator factor

T141 shows that the actual reduced numerator of
`10^m * bbpPartial (7*m)` retains all but logarithmically many of the
five-adic factors supplied by the decimal scaling.  Here `m = n+k`: once the
explicit logarithmic loss is at most `n`, the numerator contains `5^k`.
Dividing out that factor gives an exact rational presentation of the delayed
truncation `10^n * bbpPartial (7*(n+k))` with denominator `2^k * D`.

These are arithmetic identities only.  They assert no cancellation,
distribution, digit occurrence, or V1 conclusion.
-/

namespace Theory.PiDigits.T154DelayedBBPFivePrimary

open T74ThreePrimaryDecimation
open T77SelectedPadicDefectShell
open T115SampledBBPCellDefectPhase
open T141ScaledBBPFiveAdicNumerator

/-- The actual reduced numerator after removing the guaranteed `5^k` factor. -/
def delayedBBPNumerator (k n : ℕ) : ℤ :=
  (scaledBBPRat (n + k)).num / (5 : ℤ) ^ k

/-- T141's linear-minus-logarithmic valuation bound, reindexed at depth
`m=n+k`.  The displayed log condition is the exact theorem-friendly burn-in
criterion. -/
theorem delayed_scaledBBPRat_five_arithmetic
    (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n) :
    ¬ 5 ∣ (scaledBBPRat (n + k)).den ∧
      5 ^ k ∣ (scaledBBPRat (n + k)).num.natAbs := by
  have hbase := scaledBBPRat_five_arithmetic_log (n + k) hm
  refine ⟨hbase.1, ?_⟩
  have hk : k ≤ n + k - Nat.log 5 (56 * (n + k) + 5) := by omega
  exact (Nat.pow_dvd_pow 5 hk).trans hbase.2

/-- The logarithmic burn-in makes division by `5^k` exact in the reduced
integer numerator. -/
theorem scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator
    (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n) :
    (scaledBBPRat (n + k)).num =
      (5 : ℤ) ^ k * delayedBBPNumerator k n := by
  have hnat := (delayed_scaledBBPRat_five_arithmetic k n hm hlog).2
  have hint : (5 : ℤ) ^ k ∣ (scaledBBPRat (n + k)).num := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast hnat
  unfold delayedBBPNumerator
  rw [mul_comm]
  exact (Int.ediv_mul_cancel hint).symm

/-- Exact delayed rational identity.  After the logarithmic burn-in, the
natural `10^n` scaling of the depth-`n+k` BBP truncation has the five-free
presentation `U/(2^k D)`, where `U` is the actual reduced numerator divided
by `5^k` and `D` is its actual reduced denominator. -/
theorem delayed_bbpPartial_eq_num_div_two_pow_den
    (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n) :
    (10 : ℚ) ^ n * bbpPartial (7 * (n + k)) =
      (delayedBBPNumerator k n : ℚ) /
        ((2 ^ k * (scaledBBPRat (n + k)).den : ℕ) : ℚ) := by
  let R : ℚ := scaledBBPRat (n + k)
  let U : ℤ := delayedBBPNumerator k n
  have hD : (R.den : ℚ) ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5 : (5 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnum : R.num = (5 : ℤ) ^ k * U := by
    exact scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator k n hm hlog
  have hR : R = (R.num : ℚ) / (R.den : ℚ) := (Rat.num_div_den R).symm
  have hscale : R = (10 : ℚ) ^ k * ((10 : ℚ) ^ n * bbpPartial (7 * (n + k))) := by
    simp only [R, scaledBBPRat]
    rw [show n + k = k + n by omega, pow_add]
    ring
  change (10 : ℚ) ^ n * bbpPartial (7 * (n + k)) =
    (U : ℚ) / ((2 ^ k * R.den : ℕ) : ℚ)
  calc
    (10 : ℚ) ^ n * bbpPartial (7 * (n + k)) = R / (10 : ℚ) ^ k := by
      rw [hscale]
      field_simp
    _ = (U : ℚ) / ((2 ^ k * R.den : ℕ) : ℚ) := by
      nth_rewrite 1 [hR]
      rw [hnum]
      push_cast
      rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      field_simp

end Theory.PiDigits.T154DelayedBBPFivePrimary

#print axioms Theory.PiDigits.T154DelayedBBPFivePrimary.delayed_scaledBBPRat_five_arithmetic
#print axioms Theory.PiDigits.T154DelayedBBPFivePrimary.scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator
#print axioms Theory.PiDigits.T154DelayedBBPFivePrimary.delayed_bbpPartial_eq_num_div_two_pow_den
