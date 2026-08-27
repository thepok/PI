import TheoryLib.PiDigits.T7Statements
import TheoryLib.PiDecimalFactorComplexity.T1DecimalFactorComplexity
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# A linear factor-complexity bound for the decimal digits of pi

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The canonical question V1 asks for every decimal block to occur. At length
`n`, that would require all `10 ^ n` blocks, whereas this file proves only the
much weaker lower bound `n + 1`. Thus this result does not resolve V1.

V3 asks whether every digit occurs infinitely often (equivalently, whether
every infinite decimal stream embeds as a subsequence). A lower bound on the
total number of factors does not establish that recurrence, so this result
also does not resolve V3.
-/

open scoped BigOperators

namespace Theory.PiDigits.FactorComplexity

open DecimalFactorComplexity

/-- The exact number of distinct contiguous length-`n` factors in T7's
floor-based decimal digit stream for pi. -/
noncomputable def piFactorComplexity (n : ℕ) : ℕ :=
  canonicalFactorComplexity Theory.PiDigits.piDigit n

/-- T7's floor-and-remainder definition is exactly mathlib's decimal digit
stream for the fractional part `pi - 3`. -/
lemma piDigit_eq_digits (n : ℕ) :
    Theory.PiDigits.piDigit n = Real.digits (Real.pi - 3) 10 n := by
  apply Fin.ext
  simp only [Theory.PiDigits.piDigit, Real.digits, Fin.val_ofNat]
  change ⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ % 10 =
    ⌊(Real.pi - 3) * (10 : ℝ) ^ (n + 1)⌋₊ % 10
  let q : ℕ := 3 * 10 ^ (n + 1)
  have hqfloor : q ≤ ⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ := by
    apply Nat.le_floor
    dsimp [q]
    push_cast
    exact mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity)
  have hfloor :
      ⌊(Real.pi - 3) * (10 : ℝ) ^ (n + 1)⌋₊ =
        ⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ - q := by
    rw [show (Real.pi - 3) * (10 : ℝ) ^ (n + 1) =
        Real.pi * (10 : ℝ) ^ (n + 1) - (q : ℕ) by
      dsimp [q]
      push_cast
      ring]
    exact Nat.floor_sub_natCast _ _
  rw [hfloor]
  have hqmod : q ≡ 0 [MOD 10] := by
    apply Dvd.dvd.modEq_zero_nat
    refine ⟨3 * 10 ^ n, ?_⟩
    dsimp [q]
    simp [pow_succ]
    ring
  have hmod :
      ⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ - q ≡
        ⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ [MOD 10] := by
    simpa using Nat.ModEq.sub hqfloor (Nat.zero_le _) Nat.ModEq.rfl hqmod
  exact hmod.symm

/-- A purely periodic decimal expansion represents a rational real number. -/
lemma not_irrational_ofDigits_of_periodic (d : ℕ → Fin 10) (p : ℕ) (hp : 0 < p)
    (hperiodic : ∀ i, d (i + p) = d i) :
    ¬ Irrational (Real.ofDigits d) := by
  let A : ℚ :=
    ∑ i ∈ Finset.range p, (d i : ℕ) * ((10 : ℚ) ^ (i + 1))⁻¹
  let c : ℚ := ((10 : ℚ) ^ p)⁻¹
  have hshift : (fun i ↦ d (i + p)) = d := funext hperiodic
  have hx := Real.ofDigits_eq_sum_add_ofDigits d p
  rw [hshift] at hx
  have hA :
      (A : ℝ) = ∑ i ∈ Finset.range p, Real.ofDigitsTerm d i := by
    simp [A, Real.ofDigitsTerm]
  have hc : ((((10 : ℕ) : ℝ) ^ p)⁻¹) = (c : ℝ) := by
    simp [c]
  rw [← hA, hc] at hx
  have hpow : (1 : ℚ) < 10 ^ p := one_lt_pow₀ (by norm_num) hp.ne'
  have hpowpos : (0 : ℚ) < 10 ^ p := pow_pos (by norm_num) p
  have hden : (1 - c : ℚ) ≠ 0 :=
    (sub_pos.mpr ((inv_lt_one₀ hpowpos).2 hpow)).ne'
  intro hirr
  have hprod := hirr.mul_ratCast hden
  have heq : Real.ofDigits d * ((1 - c : ℚ) : ℝ) = (A : ℝ) := by
    push_cast
    linarith [hx]
  rw [heq] at hprod
  exact (Rat.not_irrational A) hprod

/-- An eventually periodic decimal expansion, including an arbitrary finite
prefix, represents a rational real number. -/
lemma not_irrational_ofDigits_of_eventuallyPeriodic (d : ℕ → Fin 10)
    (hperiodic : EventuallyPeriodic d) : ¬ Irrational (Real.ofDigits d) := by
  obtain ⟨start, period, hperiod, htail⟩ := hperiodic
  let tail : ℕ → Fin 10 := fun i ↦ d (i + start)
  have htailPeriodic : ∀ i, tail (i + period) = tail i := by
    intro i
    dsimp [tail]
    rw [show i + period + start = start + i + period by omega,
      show i + start = start + i by omega]
    exact htail i
  have htailRational :=
    not_irrational_ofDigits_of_periodic tail period hperiod htailPeriodic
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational htailRational
  let A : ℚ :=
    ∑ i ∈ Finset.range start, (d i : ℕ) * ((10 : ℚ) ^ (i + 1))⁻¹
  let c : ℚ := ((10 : ℚ) ^ start)⁻¹
  have hA :
      (A : ℝ) = ∑ i ∈ Finset.range start, Real.ofDigitsTerm d i := by
    simp [A, Real.ofDigitsTerm]
  have hc : (((10 : ℝ) ^ start)⁻¹) = (c : ℝ) := by
    simp [c]
  have hx := Real.ofDigits_eq_sum_add_ofDigits d start
  have hrat : Real.ofDigits d = ((A + c * q : ℚ) : ℝ) := by
    calc
      Real.ofDigits d =
          (∑ i ∈ Finset.range start, Real.ofDigitsTerm d i) +
            ((10 : ℝ) ^ start)⁻¹ * Real.ofDigits tail := by
        simpa [tail] using hx
      _ = (A : ℝ) + (c : ℝ) * (q : ℝ) := by rw [← hA, hc, hq]
      _ = ((A + c * q : ℚ) : ℝ) := by push_cast; rfl
  intro hirr
  exact hirr ⟨A + c * q, hrat.symm⟩

/-- T7's exact decimal digit stream for pi is not eventually periodic. The
bridge uses the reconstruction of `pi - 3` from its decimal digits and the
irrationality of pi. -/
theorem piDigit_not_eventuallyPeriodic :
    ¬ EventuallyPeriodic Theory.PiDigits.piDigit := by
  intro hperiodic
  have hdigitEq : Theory.PiDigits.piDigit = Real.digits (Real.pi - 3) 10 :=
    funext piDigit_eq_digits
  rw [hdigitEq] at hperiodic
  have hrational :=
    not_irrational_ofDigits_of_eventuallyPeriodic
      (Real.digits (Real.pi - 3) 10) hperiodic
  have hinterval : Real.pi - 3 ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · linarith [Real.pi_gt_three]
    · linarith [Real.pi_lt_four]
  have hreconstruct :
      Real.ofDigits (Real.digits (Real.pi - 3) 10) = Real.pi - 3 :=
    Real.ofDigits_digits (by norm_num) hinterval
  apply hrational
  rw [hreconstruct]
  exact irrational_pi.sub_natCast 3

/-- Every positive length `n` has at least `n + 1` distinct contiguous
length-`n` factors in T7's exact decimal digit stream for pi. This is the
Morse--Hedlund bound, not the `10 ^ n` bound required by canonical V1, and it
does not resolve either V1 or V3. -/
theorem pi_factorComplexity_lower_bound :
    ∀ n : ℕ, 0 < n → n + 1 ≤ piFactorComplexity n := by
  simpa only [piFactorComplexity] using
    morse_hedlund_canonical Theory.PiDigits.piDigit piDigit_not_eventuallyPeriodic

end Theory.PiDigits.FactorComplexity

#print axioms Theory.PiDigits.FactorComplexity.piDigit_not_eventuallyPeriodic
#print axioms Theory.PiDigits.FactorComplexity.pi_factorComplexity_lower_bound
