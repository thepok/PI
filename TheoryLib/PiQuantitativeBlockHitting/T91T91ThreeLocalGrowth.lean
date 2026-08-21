import TheoryLib.PiQuantitativeBlockHitting.T90T90ScaledCarryInterface

/-!
# T91: three-local denominator and selected-depth growth

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module records three narrow interfaces for the selected BBP path: generic
three-local reduced-denominator information, a local residue representation
at powers of three, and growth of the positive even selected depths.  It does
not assert compatibility of that representation with rational addition or
multiplication, a shadow cover, a hidden carry, a decimal digit, an SP1
resolution, or canonical V1.
-/

namespace Theory.PiDigits.T91ThreeLocalGrowth

open T77SelectedPadicDefectShell T88SelectedDepthDenominatorValuations

/-- Even powers of three are powers of nine. -/
theorem three_pow_two_mul (m : ℕ) : 3 ^ (2 * m) = 9 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have h2 : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [h2, pow_add, pow_two, ih]
      ring

/-- A basic exponential lower bound used only for selected-depth growth. -/
theorem nine_pow_add_two_ge (n : ℕ) : 8 * n + 13 ≤ 9 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hstep : 9 ^ (n + 1 + 2) = 9 * 9 ^ (n + 2) := by
        rw [pow_add]
        ring
      have hscaled : 9 * (8 * n + 13) ≤ 9 * 9 ^ (n + 2) :=
        Nat.mul_le_mul_left _ ih
      have hlin : 8 * (n + 1) + 13 ≤ 9 * (8 * n + 13) := by omega
      omega

/-- Positive even selected depths eventually exceed every natural bound.
This is exponent growth only; no circle coverage or approximation-error
premise is asserted. -/
theorem selectedDepth_even_tends_to_infinity (N : ℕ) :
    ∃ E : ℕ, ∀ t : ℕ, E ≤ t → N ≤ selectedDepth (2 * t) := by
  refine ⟨N + 2, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := by omega
  have hmono : 3 ^ (2 * (N + 2)) ≤ 3 ^ (2 * t) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hscale := selectedDepth_scale_exact t ht1
  have hkey0 := nine_pow_add_two_ge N
  rw [← three_pow_two_mul] at hkey0
  omega

/-- A rational with nonnegative three-adic valuation has a reduced
denominator not divisible by three.  This is a local denominator fact only. -/
theorem not_dvd_three_den_of_nonneg_val {q : ℚ} (h : 0 ≤ padicValRat 3 q) :
    ¬ (3 ∣ q.den) := by
  intro hdvd
  have hden0 : q.den ≠ 0 := q.den_ne_zero
  have hdenval : 1 ≤ padicValNat 3 q.den :=
    Nat.pow_dvd_iff_le_padicValNat (p := 3) (k := 1) (by norm_num) hden0 |>.1 hdvd
  have hcop : q.num.natAbs.Coprime q.den := q.reduced
  have hnum : ¬ (3 : ℕ) ∣ q.num.natAbs := by
    intro hx
    have hgcd : (3 : ℕ) ∣ q.num.natAbs.gcd q.den := Nat.dvd_gcd hx hdvd
    rw [Nat.Coprime.gcd_eq_one hcop] at hgcd
    exact absurd hgcd (by norm_num)
  have hnumval : padicValInt 3 q.num = 0 := by
    simp only [padicValInt, padicValNat.eq_zero_of_not_dvd hnum]
  have hdef : padicValRat 3 q =
      ((padicValInt 3 q.num : ℕ) : ℤ) - ((padicValNat 3 q.den : ℕ) : ℤ) := rfl
  rw [hdef, hnumval] at h
  omega

/-- The genuine unit used to invert a denominator prime to three in
`ZMod (3^n)`.  This also covers `n = 0`, where the modulus is one. -/
private def threeDenUnit (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime d
    (((Nat.prime_three.coprime_iff_not_dvd).mpr hden).pow_left n).symm

private theorem coe_threeDenUnit (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    ((threeDenUnit n hden : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) =
      (d : ZMod (3 ^ n)) := by
  rw [threeDenUnit, ZMod.coe_unitOfCoprime]

/-- The local residue of a rational whose reduced denominator is prime to
three, represented by its reduced numerator times the inverse denominator
unit in `ZMod (3^n)`.  This is a per-rational representation only. -/
def threeLocalResidue (n : ℕ) (q : ℚ) (hden : ¬ (3 ∣ q.den)) : ZMod (3 ^ n) :=
  (q.num : ZMod (3 ^ n)) *
    (((threeDenUnit n hden)⁻¹ : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n))

/-- Multiplying the local residue by the reduced denominator recovers the
reduced numerator in `ZMod (3^n)`. -/
theorem threeLocalResidue_mul_den (n : ℕ) (q : ℚ) (hden : ¬ (3 ∣ q.den)) :
    threeLocalResidue n q hden * (q.den : ZMod (3 ^ n)) =
      (q.num : ZMod (3 ^ n)) := by
  have hunit : (((threeDenUnit n hden)⁻¹ : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) *
      ((threeDenUnit n hden : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) = 1 :=
    Units.inv_mul _
  rw [threeLocalResidue, mul_assoc, ← coe_threeDenUnit n hden, hunit, mul_one]

end Theory.PiDigits.T91ThreeLocalGrowth

#print axioms Theory.PiDigits.T91ThreeLocalGrowth.three_pow_two_mul
#print axioms Theory.PiDigits.T91ThreeLocalGrowth.nine_pow_add_two_ge
#print axioms Theory.PiDigits.T91ThreeLocalGrowth.selectedDepth_even_tends_to_infinity
#print axioms Theory.PiDigits.T91ThreeLocalGrowth.not_dvd_three_den_of_nonneg_val
#print axioms Theory.PiDigits.T91ThreeLocalGrowth.threeLocalResidue
#print axioms Theory.PiDigits.T91ThreeLocalGrowth.threeLocalResidue_mul_den
