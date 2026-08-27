import TheoryLib.PiQuantitativeBlockHitting.T181T181ReflectedIntervalArithmetic

/-!
# T183: reflected fixed-point Horner evaluation of `exp (x I)`

This file is the small semantic core for generated trigonometric leaves.  A
certificate stores only a rational centre and final common-scale integer
rows.  The executable checker recomputes the 128-style backward Horner
recursion with outward integer division.  No large numerical payload occurs
here.
-/

namespace Theory.PiDigits.T183ReflectedExpHorner

open Theory.PiDigits.T171CompactFixedPointCertificate
open Theory.PiDigits.T180ReflectedTrigIntervalCore
open Theory.PiDigits.T181ReflectedIntervalArithmetic

noncomputable section

/-- Exact backward Horner value.  `steps` counts the remaining multiplications
and `k+1` is the next factorial factor. -/
def backwardHorner (center : Real) : Nat → Nat → Complex
  | 0, _ => 1
  | steps + 1, k =>
      1 + ((center : Complex) * Complex.I) / (k + 1) *
        backwardHorner center steps (k + 1)

/-- The Horner form of the first `n` exponential terms. -/
def reflectedExpPartial (n : Nat) (center : Real) : Complex :=
  match n with
  | 0 => 0
  | n + 1 => backwardHorner center n 0

private def hornerPolynomial (center : Real) (steps k : Nat) : Complex :=
  ∑ m ∈ Finset.range (steps + 1),
    (((center : Complex) * Complex.I) ^ m * k.factorial) /
      (k + m).factorial

private theorem hornerPolynomial_succ (center : Real) (steps k : Nat) :
    hornerPolynomial center (steps + 1) k =
      1 + ((center : Complex) * Complex.I) / (k + 1) *
        hornerPolynomial center steps (k + 1) := by
  unfold hornerPolynomial
  rw [show steps + 1 + 1 = (steps + 1) + 1 by omega,
    Finset.sum_range_succ']
  have hzero :
      ((center : Complex) * Complex.I) ^ 0 * (k.factorial : Complex) /
          ((k + 0).factorial : Complex) = 1 := by
    simp only [pow_zero, one_mul, Nat.add_zero]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  rw [hzero, Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.factorial_succ, pow_succ]
  have hkm : k + (m + 1) = k + 1 + m := by omega
  rw [hkm]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1 + m))]

private theorem backwardHorner_eq_hornerPolynomial
    (center : Real) (steps k : Nat) :
    backwardHorner center steps k = hornerPolynomial center steps k := by
  induction steps generalizing k with
  | zero =>
      unfold backwardHorner hornerPolynomial
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton,
        pow_zero, one_mul]
      exact (div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))).symm
  | succ steps ih =>
      rw [backwardHorner, ih, ← hornerPolynomial_succ]

/-- Backward Horner evaluation is exactly T180's exponential partial sum. -/
theorem reflectedExpPartial_eq_expIPartial (n : Nat) (center : Real) :
    reflectedExpPartial n center = expIPartial n center := by
  cases n with
  | zero => simp [reflectedExpPartial, expIPartial]
  | succ n =>
      rw [reflectedExpPartial, backwardHorner_eq_hornerPolynomial]
      unfold hornerPolynomial expIPartial
      apply Finset.sum_congr rfl
      intro m hm
      simp

structure ComplexInterval where
  re : FixedInterval
  im : FixedInterval
deriving DecidableEq, BEq, Repr

def EnclosesComplex (scale : Nat) (row : ComplexInterval) (z : Complex) : Prop :=
  EnclosesReal scale row.re z.re ∧ EnclosesReal scale row.im z.im

/-- Outward common-scale multiplication by the exact rational `p/d`.
The endpoint order is reversed when `p` is negative. -/
def mulRationalInterval (p : Int) (d : Nat) (row : FixedInterval) : FixedInterval :=
  if 0 ≤ p then
    ⟨p * row.lower / d, p * row.upper / d + 1⟩
  else
    ⟨p * row.upper / d, p * row.lower / d + 1⟩

/-- One executable complex Horner step
`z ↦ 1 + (p/q) I z / k`. -/
def hornerStep (scale : Nat) (p : Int) (q k : Nat)
    (z : ComplexInterval) : ComplexInterval :=
  let xr := mulRationalInterval p (q * k) z.re
  let xi := mulRationalInterval p (q * k) z.im
  ⟨⟨(scale : Int) - xi.upper, (scale : Int) - xi.lower⟩, xr⟩

/-- Deterministically regenerated fixed-point Horner rows. -/
def hornerRows (scale : Nat) (p : Int) (q : Nat) : Nat → Nat → ComplexInterval
  | 0, _ => ⟨⟨scale, scale⟩, ⟨0, 0⟩⟩
  | steps + 1, k =>
      hornerStep scale p q (k + 1) (hornerRows scale p q steps (k + 1))

structure HornerCertificate where
  scale : Nat
  centerNumerator : Int
  centerDenominator : Nat
  terms : Nat
  claimed : ComplexInterval
deriving DecidableEq, Repr

/-- The reflected checker contains integer and natural operations only. -/
def checkHorner (c : HornerCertificate) : Bool :=
  c.scale > 0 && c.centerDenominator > 0 && c.terms > 0 &&
    decide (c.claimed = hornerRows c.scale c.centerNumerator c.centerDenominator
      (c.terms - 1) 0)

private theorem integer_division_encloses_real (a : Int) (d : Nat)
    (hd : 0 < d) :
    (a / d : Int) ≤ (a : Real) / d ∧
      (a : Real) / d ≤ (a / d + 1 : Int) := by
  have h := integerRow_encloses_fraction 1 d a hd
  unfold Encloses integerRow at h
  norm_num at h
  exact_mod_cast h

theorem mulRationalInterval_sound {scale d : Nat} {p : Int}
    {row : FixedInterval} {x : Real} (hd : 0 < d)
    (hrow : EnclosesReal scale row x) :
    EnclosesReal scale (mulRationalInterval p d row) ((p : Real) / d * x) := by
  unfold EnclosesReal at hrow ⊢
  have hdR : (0 : Real) < d := by exact_mod_cast hd
  by_cases hp : 0 ≤ p
  · simp only [mulRationalInterval, if_pos hp]
    have hl := (integer_division_encloses_real (p * row.lower) d hd).1
    have hu := (integer_division_encloses_real (p * row.upper) d hd).2
    have hpR : (0 : Real) ≤ p := by exact_mod_cast hp
    constructor
    · calc
        ((p * row.lower / d : Int) : Real) ≤
            ((p : Real) * row.lower) / d := by simpa using hl
        _ ≤ ((p : Real) * ((scale : Real) * x)) / d :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrow.1 hpR) hdR.le
        _ = (scale : Real) * ((p : Real) / d * x) := by ring
    · calc
        (scale : Real) * ((p : Real) / d * x) =
            ((p : Real) * ((scale : Real) * x)) / d := by ring
        _ ≤ ((p : Real) * row.upper) / d := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrow.2 hpR) hdR.le
        _ ≤ ((p * row.upper / d + 1 : Int) : Real) := by simpa using hu
  · have hpR : (p : Real) ≤ 0 := by exact_mod_cast (le_of_not_ge hp)
    simp only [mulRationalInterval, if_neg hp]
    have hl := (integer_division_encloses_real (p * row.upper) d hd).1
    have hu := (integer_division_encloses_real (p * row.lower) d hd).2
    constructor
    · calc
        ((p * row.upper / d : Int) : Real) ≤
            ((p : Real) * row.upper) / d := by simpa using hl
        _ ≤ ((p : Real) * ((scale : Real) * x)) / d := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonpos_left hrow.2 hpR) hdR.le
        _ = (scale : Real) * ((p : Real) / d * x) := by ring
    · calc
        (scale : Real) * ((p : Real) / d * x) =
            ((p : Real) * ((scale : Real) * x)) / d := by ring
        _ ≤ ((p : Real) * row.lower) / d := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonpos_left hrow.1 hpR) hdR.le
        _ ≤ ((p * row.lower / d + 1 : Int) : Real) := by simpa using hu

theorem hornerStep_sound {scale q k : Nat} {p : Int}
    {z : ComplexInterval} {w : Complex} (hq : 0 < q) (hk : 0 < k)
    (hz : EnclosesComplex scale z w) :
    EnclosesComplex scale (hornerStep scale p q k z)
      (1 + (((((p : Real) / (q * k) : Real)) : Complex) * Complex.I) * w) := by
  have hqk : 0 < q * k := Nat.mul_pos hq hk
  have hre := mulRationalInterval_sound (p := p) (d := q * k) hqk hz.1
  have him := mulRationalInterval_sound (p := p) (d := q * k) hqk hz.2
  let a : Real := (p : Real) / (q * k)
  have hreal :
      (1 + (((a : Real) : Complex) * Complex.I) * w).re = 1 - a * w.im := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      sub_eq_add_neg]
  have himag :
      (1 + (((a : Real) : Complex) * Complex.I) * w).im = a * w.re := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  unfold EnclosesComplex hornerStep
  dsimp only
  constructor
  · unfold EnclosesReal at hre him ⊢
    rw [show (1 + (((((p : Real) / (q * k) : Real)) : Complex) *
      Complex.I) * w).re = 1 - a * w.im by exact hreal]
    have him' : EnclosesReal scale (mulRationalInterval p (q * k) z.im)
        (a * w.im) := by simpa [a, Nat.cast_mul] using him
    unfold EnclosesReal at him'
    constructor
    · simpa [mul_sub] using sub_le_sub_left him'.2 (scale : Real)
    · simpa [mul_sub] using sub_le_sub_left him'.1 (scale : Real)
  · rw [show (1 + (((((p : Real) / (q * k) : Real)) : Complex) *
      Complex.I) * w).im = a * w.re by exact himag]
    simpa [a, Nat.cast_mul] using hre

theorem hornerRows_sound {scale q : Nat} {p : Int}
    (hq : 0 < q) (steps k : Nat) :
    EnclosesComplex scale (hornerRows scale p q steps k)
      (backwardHorner ((p : Real) / q) steps k) := by
  induction steps generalizing k with
  | zero =>
      unfold hornerRows backwardHorner EnclosesComplex EnclosesReal
      norm_num
  | succ steps ih =>
      rw [hornerRows, backwardHorner]
      convert hornerStep_sound hq (Nat.succ_pos k) (ih (k + 1)) using 1
      push_cast
      field_simp

/-- A successful certificate encloses the exact backward Horner value. -/
theorem checkedHorner_sound {c : HornerCertificate}
    (hc : checkHorner c = true) :
    EnclosesComplex c.scale c.claimed
      (reflectedExpPartial c.terms
        ((c.centerNumerator : Real) / c.centerDenominator)) := by
  simp only [checkHorner, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨hs, hq⟩, hn⟩, hclaim⟩
  cases ht : c.terms with
  | zero => omega
  | succ n =>
      rw [ht] at hclaim
      simp only [reflectedExpPartial]
      rw [hclaim]
      exact hornerRows_sound hq n 0

/-- Final T180-compatible sine/cosine interface.  The returned inequalities
have the same shape as `checked_trig_bounds`; only the rational Taylor payload
has been replaced by a reflected Horner certificate. -/
theorem checkedHorner_trig_bounds {n : Nat} (hn : 8 ≤ n)
    {x center width : Real} (hcenter : |center| ≤ 4)
    (hwidth : |x - center| ≤ width)
    {c : HornerCertificate} (hc : checkHorner c = true)
    (hnTerms : c.terms = n)
    (hcenterEq : center = (c.centerNumerator : Real) / c.centerDenominator) :
    ((c.claimed.re.lower : Real) / c.scale) -
          (width + trigRemainder n) ≤ Real.cos x ∧
      Real.cos x ≤ ((c.claimed.re.upper : Real) / c.scale) +
          (width + trigRemainder n) ∧
      ((c.claimed.im.lower : Real) / c.scale) -
          (width + trigRemainder n) ≤ Real.sin x ∧
      Real.sin x ≤ ((c.claimed.im.upper : Real) / c.scale) +
          (width + trigRemainder n) := by
  have hsNat : 0 < c.scale := by
    simp only [checkHorner, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.1
  have hs : (0 : Real) < c.scale := by exact_mod_cast hsNat
  have hcert := checkedHorner_sound hc
  rw [hnTerms, ← hcenterEq, reflectedExpPartial_eq_expIPartial] at hcert
  have htrig := trig_error_with_input_width hn hcenter hwidth
  unfold EnclosesComplex EnclosesReal at hcert
  rcases abs_le.mp htrig.1 with ⟨hcosL, hcosU⟩
  rcases abs_le.mp htrig.2 with ⟨hsinL, hsinU⟩
  rcases hcert with ⟨⟨hreL, hreU⟩, ⟨himL, himU⟩⟩
  have hreL' : (c.claimed.re.lower : Real) / c.scale ≤
      (expIPartial n center).re := (div_le_iff₀ hs).2 (by simpa [mul_comm] using hreL)
  have hreU' : (expIPartial n center).re ≤
      (c.claimed.re.upper : Real) / c.scale :=
        (le_div_iff₀ hs).2 (by simpa [mul_comm] using hreU)
  have himL' : (c.claimed.im.lower : Real) / c.scale ≤
      (expIPartial n center).im := (div_le_iff₀ hs).2 (by simpa [mul_comm] using himL)
  have himU' : (expIPartial n center).im ≤
      (c.claimed.im.upper : Real) / c.scale :=
        (le_div_iff₀ hs).2 (by simpa [mul_comm] using himU)
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private def demo : HornerCertificate where
  scale := 100
  centerNumerator := 0
  centerDenominator := 1
  terms := 8
  claimed := ⟨⟨99, 100⟩, ⟨0, 1⟩⟩

private theorem demo_checks : checkHorner demo = true := by rfl

#print axioms Theory.PiDigits.T183ReflectedExpHorner.mulRationalInterval_sound
#print axioms Theory.PiDigits.T183ReflectedExpHorner.reflectedExpPartial_eq_expIPartial
#print axioms Theory.PiDigits.T183ReflectedExpHorner.hornerRows_sound
#print axioms Theory.PiDigits.T183ReflectedExpHorner.checkedHorner_sound
#print axioms Theory.PiDigits.T183ReflectedExpHorner.checkedHorner_trig_bounds

end

end Theory.PiDigits.T183ReflectedExpHorner
