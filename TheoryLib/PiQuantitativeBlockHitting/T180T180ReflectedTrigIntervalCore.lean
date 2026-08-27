import TheoryLib.PiQuantitativeBlockHitting.T175T175DecimalSuffixCylinder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# T180: reflected rational intervals for certified trigonometry

This file is the small trusted core intended for a later finite certificate of
the actual `q = 1000`, `A = 334`, `N = 10000` signed score.  It contains no
large numerical payload.  A certificate is a list of exact rational summands;
the executable checker regenerates their common-scale integer enclosures and
checks only integer equalities and inequalities.

The analytic error is supplied by mathlib's `Complex.exp_bound'`.  For an
angle of absolute value at most four, the first `n` exponential terms have
error at most `2 * 4^n / n!`, provided `8 ≤ n`.  Real and imaginary projection
give simultaneous cosine and sine bounds.  The one-Lipschitz bounds for sine
and cosine then transport the enclosure from an exact rational centre to a
narrow input interval.
-/

namespace Theory.PiDigits.T180ReflectedTrigIntervalCore

open Finset
open Theory.PiDigits.T171CompactFixedPointCertificate

noncomputable section

/-- The first `n` terms of `exp (x I)`. -/
def expIPartial (n : Nat) (x : Real) : Complex :=
  ∑ m ∈ Finset.range n, (((x : Complex) * Complex.I) ^ m) / m.factorial

/-- A uniform rational remainder used after reducing an angle to `[-4,4]`. -/
def trigRemainder (n : Nat) : Real :=
  2 * 4 ^ n / n.factorial

/-- Mathlib's complex exponential tail bound, projected simultaneously to the
real and imaginary coordinates. -/
theorem expIPartial_trig_error {n : Nat} (hn : 8 ≤ n) {x : Real}
    (hx : |x| ≤ 4) :
    |Real.cos x - (expIPartial n x).re| ≤ trigRemainder n ∧
      |Real.sin x - (expIPartial n x).im| ≤ trigRemainder n := by
  let z : Complex := (x : Complex) * Complex.I
  have hznorm : ‖z‖ = |x| := by
    simp [z, Real.norm_eq_abs]
  have hhalf : ‖z‖ / (n.succ : Real) ≤ 1 / 2 := by
    rw [hznorm]
    have hnR : (9 : Real) ≤ n.succ := by exact_mod_cast Nat.succ_le_succ hn
    have hnpos : (0 : Real) < n.succ := by positivity
    calc
      |x| / (n.succ : Real) ≤ 4 / (n.succ : Real) :=
        div_le_div_of_nonneg_right hx hnpos.le
      _ ≤ 4 / 9 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
      _ ≤ 1 / 2 := by norm_num
  have htail := Complex.exp_bound' (x := z) (n := n) hhalf
  have hpow : ‖z‖ ^ n ≤ (4 : Real) ^ n := by
    rw [hznorm]
    exact pow_le_pow_left₀ (abs_nonneg x) hx n
  have hfac : (0 : Real) < n.factorial := by positivity
  have htail' :
      ‖Complex.exp z - ∑ m ∈ Finset.range n, z ^ m / m.factorial‖ ≤
        trigRemainder n := by
    calc
      _ ≤ ‖z‖ ^ n / n.factorial * 2 := htail
      _ ≤ (4 : Real) ^ n / n.factorial * 2 := by
        gcongr
      _ = trigRemainder n := by rw [trigRemainder]; ring
  have hre := Complex.abs_re_le_norm
    (Complex.exp z - ∑ m ∈ Finset.range n, z ^ m / m.factorial)
  have him := Complex.abs_im_le_norm
    (Complex.exp z - ∑ m ∈ Finset.range n, z ^ m / m.factorial)
  constructor
  · calc
      |Real.cos x - (expIPartial n x).re| =
          |(Complex.exp z -
            ∑ m ∈ Finset.range n, z ^ m / m.factorial).re| := by
              simp [expIPartial, z, Complex.exp_ofReal_mul_I_re]
      _ ≤ ‖Complex.exp z -
            ∑ m ∈ Finset.range n, z ^ m / m.factorial‖ := hre
      _ ≤ trigRemainder n := htail'
  · calc
      |Real.sin x - (expIPartial n x).im| =
          |(Complex.exp z -
            ∑ m ∈ Finset.range n, z ^ m / m.factorial).im| := by
              simp [expIPartial, z, Complex.exp_ofReal_mul_I_im]
      _ ≤ ‖Complex.exp z -
            ∑ m ∈ Finset.range n, z ^ m / m.factorial‖ := him
      _ ≤ trigRemainder n := htail'

/-- One exact rational summand in a reflected certificate. -/
structure RationalTerm where
  numerator : Int
  denominator : Nat
deriving DecidableEq, Repr

def RationalTerm.value (t : RationalTerm) : Rat :=
  (t.numerator : Rat) / t.denominator

/-- An untrusted payload for the sum of exact rational terms.  The checker
regenerates every outward-rounded integer row. -/
structure RationalSumCertificate where
  scale : Nat
  terms : List RationalTerm
  claimedLower : Int
  claimedUpper : Int
deriving DecidableEq, Repr

def RationalSumCertificate.rows (c : RationalSumCertificate) : List FixedInterval :=
  c.terms.map fun t => integerRow c.scale t.numerator t.denominator

def RationalSumCertificate.additive (c : RationalSumCertificate) : AdditiveCertificate where
  scale := c.scale
  rows := c.rows
  claimedLower := c.claimedLower
  claimedUpper := c.claimedUpper

/-- Executable reflected checker: denominator positivity and the T171 integer
sum checker are both recomputed. -/
def checkRationalSum (c : RationalSumCertificate) : Bool :=
  c.terms.all (fun t => 0 < t.denominator) && check c.additive

private theorem rows_enclose_aux (scale : Nat) (terms : List RationalTerm)
    (hden : ∀ t ∈ terms, 0 < t.denominator) :
    List.Forall₂ (Encloses scale)
      (terms.map fun t => integerRow scale t.numerator t.denominator)
      (terms.map RationalTerm.value) := by
  induction terms with
  | nil => exact .nil
  | cons t ts ih =>
      apply List.Forall₂.cons
      · exact integerRow_encloses_fraction _ _ _
          (hden t List.mem_cons_self)
      · exact ih fun u hu => hden u (List.mem_cons_of_mem t hu)

private theorem rows_enclose (c : RationalSumCertificate)
    (hden : ∀ t ∈ c.terms, 0 < t.denominator) :
    List.Forall₂ (Encloses c.scale) c.rows
      (c.terms.map RationalTerm.value) := by
  exact rows_enclose_aux c.scale c.terms hden

/-- Soundness of a successful rational-sum certificate. -/
theorem checkedRationalSum_bounds {c : RationalSumCertificate}
    (hc : checkRationalSum c = true) :
    (c.claimedLower : Rat) / c.scale ≤
        (c.terms.map RationalTerm.value).sum ∧
      (c.terms.map RationalTerm.value).sum ≤
        (c.claimedUpper : Rat) / c.scale := by
  simp only [checkRationalSum, Bool.and_eq_true, List.all_eq_true] at hc
  apply checked_sum_bounds hc.2
  apply rows_enclose c
  intro t ht
  exact of_decide_eq_true (hc.1 t ht)

/-- Real-valued form of `checkedRationalSum_bounds`, convenient for analytic
consumers. -/
theorem checkedRationalSum_bounds_real {c : RationalSumCertificate}
    (hc : checkRationalSum c = true) :
    (((c.claimedLower : Rat) / c.scale : Rat) : Real) ≤
        (((c.terms.map RationalTerm.value).sum : Rat) : Real) ∧
      (((c.terms.map RationalTerm.value).sum : Rat) : Real) ≤
        (((c.claimedUpper : Rat) / c.scale : Rat) : Real) := by
  exact_mod_cast checkedRationalSum_bounds hc

/-- Transport a centre-point Taylor enclosure to any nearby actual input.
This is the semantic interface needed by a suffix-cylinder consumer. -/
theorem trig_error_with_input_width {n : Nat} (hn : 8 ≤ n)
    {x center width : Real} (hcenter : |center| ≤ 4)
    (hwidth : |x - center| ≤ width) :
    |Real.cos x - (expIPartial n center).re| ≤
        width + trigRemainder n ∧
      |Real.sin x - (expIPartial n center).im| ≤
        width + trigRemainder n := by
  have ht := expIPartial_trig_error hn hcenter
  constructor
  · calc
      |Real.cos x - (expIPartial n center).re| ≤
          |Real.cos x - Real.cos center| +
            |Real.cos center - (expIPartial n center).re| :=
        abs_sub_le _ _ _
      _ ≤ width + trigRemainder n :=
        add_le_add ((Real.abs_cos_sub_cos_le x center).trans hwidth) ht.1
  · calc
      |Real.sin x - (expIPartial n center).im| ≤
          |Real.sin x - Real.sin center| +
            |Real.sin center - (expIPartial n center).im| :=
        abs_sub_le _ _ _
      _ ≤ width + trigRemainder n :=
        add_le_add ((Real.abs_sin_sub_sin_le x center).trans hwidth) ht.2

/-- End-to-end semantic interface for two successful reflected certificates.
The two equalities are purely algebraic: a generated T181 payload proves that
its rational real/imaginary term lists are the coordinates of `expIPartial`.
All transcendental and input-interval error is discharged here. -/
theorem checked_trig_bounds {n : Nat} (hn : 8 ≤ n)
    {x center width : Real} (hcenter : |center| ≤ 4)
    (hwidth : |x - center| ≤ width)
    {reCert imCert : RationalSumCertificate}
    (hreCheck : checkRationalSum reCert = true)
    (himCheck : checkRationalSum imCert = true)
    (hreTerms : (((reCert.terms.map RationalTerm.value).sum : Rat) : Real) =
      (expIPartial n center).re)
    (himTerms : (((imCert.terms.map RationalTerm.value).sum : Rat) : Real) =
      (expIPartial n center).im) :
    (((reCert.claimedLower : Rat) / reCert.scale : Rat) : Real) -
          (width + trigRemainder n) ≤ Real.cos x ∧
      Real.cos x ≤
        (((reCert.claimedUpper : Rat) / reCert.scale : Rat) : Real) +
          (width + trigRemainder n) ∧
      (((imCert.claimedLower : Rat) / imCert.scale : Rat) : Real) -
          (width + trigRemainder n) ≤ Real.sin x ∧
      Real.sin x ≤
        (((imCert.claimedUpper : Rat) / imCert.scale : Rat) : Real) +
          (width + trigRemainder n) := by
  have hreCert := checkedRationalSum_bounds_real hreCheck
  have himCert := checkedRationalSum_bounds_real himCheck
  have htrig := trig_error_with_input_width hn hcenter hwidth
  rw [← hreTerms] at htrig
  rw [← himTerms] at htrig
  have hreErr := (abs_le.mp htrig.1)
  have himErr := (abs_le.mp htrig.2)
  constructor
  · linarith [hreCert.1]
  constructor
  · linarith [hreCert.2]
  constructor
  · linarith [himCert.1]
  · linarith [himCert.2]

/-! A small reflected arithmetic demo.  It checks the exact rational sum
`1 - 1/2 = 1/2` at common scale twelve. -/

private def demoCertificate : RationalSumCertificate where
  scale := 12
  terms := [⟨1, 1⟩, ⟨-1, 2⟩]
  claimedLower := 6
  claimedUpper := 8

private theorem demo_checks : checkRationalSum demoCertificate = true := by
  rfl

theorem demo_half_enclosed :
    (demoCertificate.claimedLower : Rat) / demoCertificate.scale ≤ (1 : Rat) / 2 ∧
      (1 : Rat) / 2 ≤
        (demoCertificate.claimedUpper : Rat) / demoCertificate.scale := by
  have h := checkedRationalSum_bounds demo_checks
  norm_num [demoCertificate, RationalTerm.value] at h ⊢

end

end Theory.PiDigits.T180ReflectedTrigIntervalCore

#print axioms Theory.PiDigits.T180ReflectedTrigIntervalCore.expIPartial_trig_error
#print axioms Theory.PiDigits.T180ReflectedTrigIntervalCore.checkedRationalSum_bounds
#print axioms Theory.PiDigits.T180ReflectedTrigIntervalCore.trig_error_with_input_width
#print axioms Theory.PiDigits.T180ReflectedTrigIntervalCore.checked_trig_bounds
#print axioms Theory.PiDigits.T180ReflectedTrigIntervalCore.demo_half_enclosed
