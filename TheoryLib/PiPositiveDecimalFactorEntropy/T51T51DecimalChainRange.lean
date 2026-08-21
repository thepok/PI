import TheoryLib.PiPositiveDecimalFactorEntropy.T40T40DecimalFrequencyDecimation

/-!
# T51: exact full-band decimal-chain range

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file proves only the arithmetic frequency range used by the non-pi T51
Fibonacci sibling. It imports T40's checked frequency convention but makes no
claim about pi, C1, the sibling's orbit sums, or its Fejer-energy limit.
-/

namespace DecimalFactorComplexity.T51FibonacciTwoBlock

open DecimalFactorComplexity.T40DecimalFrequencyDecimation

/-- At sample size `10^n` and full bandwidth `10^n/2`, T40's frequency
`decimalFrequency 1 r = 10^r` is strictly admissible exactly for `r < n`. -/
theorem fullBand_decimalFrequencyAdmissible_iff
    (n r : ℕ) (hn : 1 ≤ n) :
    DecimalFrequencyAdmissible (10 ^ n / 2) 1 r ↔ r < n := by
  rw [decimalFrequencyAdmissible_iff]
  simp only [Int.natAbs_one, mul_one]
  constructor
  · intro hadm
    by_contra hnr
    have hpow : 10 ^ n ≤ 10 ^ r :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hnr)
    have hhalf : 10 ^ n / 2 < 10 ^ n :=
      Nat.div_lt_self (by positivity) (by norm_num)
    omega
  · intro hr
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hrk : r ≤ k := by omega
    have hpow : 10 ^ r ≤ 10 ^ k :=
      Nat.pow_le_pow_right (by norm_num) hrk
    calc
      10 ^ r ≤ 10 ^ k := hpow
      _ < 5 * 10 ^ k := by
        have hpos : 0 < 10 ^ k := by positivity
        omega
      _ = 10 ^ (1 + k) / 2 := by
        rw [pow_add]
        norm_num
        omega

/-- Consequently `0,...,n-1` is the complete maximal admissible range. -/
theorem fullBand_complete_chain_range
    (n r : ℕ) (hn : 1 ≤ n) :
    DecimalFrequencyAdmissible (10 ^ n / 2) 1 r ↔ r ≤ n - 1 := by
  rw [fullBand_decimalFrequencyAdmissible_iff n r hn]
  omega

end DecimalFactorComplexity.T51FibonacciTwoBlock

#print axioms DecimalFactorComplexity.T51FibonacciTwoBlock.fullBand_decimalFrequencyAdmissible_iff
#print axioms DecimalFactorComplexity.T51FibonacciTwoBlock.fullBand_complete_chain_range
