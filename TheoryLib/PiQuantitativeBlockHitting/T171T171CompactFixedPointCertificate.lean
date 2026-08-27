import TheoryLib.PiQuantitativeBlockHitting.T170T170MachinFixedPointIntervals

/-!
# T171: compact additive fixed-point certificates

This isolated prototype separates a long numerical certificate into two layers.

* The untrusted payload is a list of integer lower/upper numerators at one
  common positive scale.  The checker only compares and adds integers.
* A small semantic theorem says that, if each integer interval encloses the
  corresponding exact quantity, a successful integer check proves bounds for
  the exact sum.

In particular, the checker never constructs or normalizes one rational per
term.  Later interval primitives (range reduction, Taylor steps, products,
and divisions) can emit these integer endpoint rows and prove their local
enclosure lemmas independently.  The additive consumer below is insensitive
to how those rows were produced.

The final theorem exercises the architecture on 725 integer rows and certifies
500 fractional decimal places of pi.  It is a fixed-constant arithmetic
milestone, not a digit-occurrence or distribution result.
-/

namespace Theory.PiDigits.T171CompactFixedPointCertificate

open Finset
open Theory.PiDigits.MachinGridStability

/-- Integer endpoints for a quantity after multiplication by a common scale. -/
structure FixedInterval where
  lower : Int
  upper : Int
deriving DecidableEq, Repr

/-- A compact certificate for an additive computation.

`claimedLower` and `claimedUpper` make the final comparison constant-size.
The checker recomputes both claims from the endpoint rows, so they are not
trusted. -/
structure AdditiveCertificate where
  scale : Nat
  rows : List FixedInterval
  claimedLower : Int
  claimedUpper : Int
deriving DecidableEq, Repr

def lowerTotal (rows : List FixedInterval) : Int :=
  (rows.map FixedInterval.lower).sum

def upperTotal (rows : List FixedInterval) : Int :=
  (rows.map FixedInterval.upper).sum

/-- The executable checker.  It performs only natural/integer operations. -/
def check (certificate : AdditiveCertificate) : Bool :=
  certificate.scale > 0 &&
    certificate.rows.all (fun row => row.lower ≤ row.upper) &&
    certificate.claimedLower == lowerTotal certificate.rows &&
    certificate.claimedUpper == upperTotal certificate.rows

/-- Semantic meaning of one fixed-point row.  Rationals occur only in this
specification/proof layer, never in `check`. -/
def Encloses (scale : Nat) (row : FixedInterval) (x : Rat) : Prop :=
  (row.lower : Rat) ≤ (scale : Rat) * x ∧
    (scale : Rat) * x ≤ (row.upper : Rat)

theorem lowerTotal_le_scaled_sum {scale : Nat} {rows : List FixedInterval}
    {xs : List Rat} (h : List.Forall₂ (Encloses scale) rows xs) :
    (lowerTotal rows : Rat) ≤ (scale : Rat) * xs.sum := by
  induction h with
  | nil => simp [lowerTotal]
  | cons hx _ ih =>
      simp only [lowerTotal, List.map_cons, List.sum_cons] at ih ⊢
      simpa [mul_add] using add_le_add hx.1 ih

theorem scaled_sum_le_upperTotal {scale : Nat} {rows : List FixedInterval}
    {xs : List Rat} (h : List.Forall₂ (Encloses scale) rows xs) :
    (scale : Rat) * xs.sum ≤ (upperTotal rows : Rat) := by
  induction h with
  | nil => simp [upperTotal]
  | cons hx _ ih =>
      simp only [upperTotal, List.map_cons, List.sum_cons] at ih ⊢
      simpa [mul_add] using add_le_add hx.2 ih

theorem check_scale_pos {certificate : AdditiveCertificate}
    (hcheck : check certificate = true) : 0 < certificate.scale := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.1.1.1

theorem check_claims {certificate : AdditiveCertificate}
    (hcheck : check certificate = true) :
    certificate.claimedLower = lowerTotal certificate.rows ∧
      certificate.claimedUpper = upperTotal certificate.rows := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
  exact ⟨hcheck.1.2, hcheck.2⟩

/-- Soundness of a successful integer certificate.  The strict comparisons
against requested thresholds are tiny integer facts, even for a long row
payload. -/
theorem checked_sum_bounds {certificate : AdditiveCertificate} {xs : List Rat}
    (hcheck : check certificate = true)
    (hencloses : List.Forall₂ (Encloses certificate.scale) certificate.rows xs) :
    (certificate.claimedLower : Rat) / certificate.scale ≤ xs.sum ∧
      xs.sum ≤ (certificate.claimedUpper : Rat) / certificate.scale := by
  have hscaleNat := check_scale_pos hcheck
  have hscale : (0 : Rat) < certificate.scale := by exact_mod_cast hscaleNat
  obtain ⟨hlower, hupper⟩ := check_claims hcheck
  constructor
  · rw [div_le_iff₀ hscale, hlower]
    simpa [mul_comm] using lowerTotal_le_scaled_sum hencloses
  · rw [le_div_iff₀ hscale, hupper]
    simpa [mul_comm] using scaled_sum_le_upperTotal hencloses

/-- Direct lower-threshold interface for a future signed-score theorem. -/
theorem checked_strict_lower {certificate : AdditiveCertificate} {xs : List Rat}
    {threshold : Int} (hcheck : check certificate = true)
    (hencloses : List.Forall₂ (Encloses certificate.scale) certificate.rows xs)
    (hthreshold : threshold < certificate.claimedLower) :
    (threshold : Rat) / certificate.scale < xs.sum := by
  have hscaleNat := check_scale_pos hcheck
  have hscale : (0 : Rat) < certificate.scale := by exact_mod_cast hscaleNat
  rw [div_lt_iff₀ hscale]
  have hthresholdRat : (threshold : Rat) < certificate.claimedLower := by
    exact_mod_cast hthreshold
  calc
    (threshold : Rat) < certificate.claimedLower := hthresholdRat
    _ = lowerTotal certificate.rows := congrArg Int.cast (check_claims hcheck).1
    _ ≤ (certificate.scale : Rat) * xs.sum := lowerTotal_le_scaled_sum hencloses
    _ = xs.sum * certificate.scale := mul_comm _ _

/-! ## A genuine 500-place Machin certificate -/

def machinTerms (K : Nat) : List Rat :=
  ((List.range (2 * (K + 1))).map (fun n =>
      (((16 : Int) * (-1) ^ n : Int) : Rat) /
        ((5 ^ (2 * n + 1) * (2 * n + 1) : Nat) : Rat))) ++
    ((List.range (2 * (K + 1) + 1)).map (fun n =>
      (((-4 : Int) * (-1) ^ n : Int) : Rat) /
        ((239 ^ (2 * n + 1) * (2 * n + 1) : Nat) : Rat)))

def integerRow (scale : Nat) (numerator : Int) (denominator : Nat) : FixedInterval :=
  ⟨numerator * scale / denominator, numerator * scale / denominator + 1⟩

theorem integerRow_encloses_fraction (scale denominator : Nat) (numerator : Int)
    (hden : 0 < denominator) :
    Encloses scale (integerRow scale numerator denominator)
      ((numerator : Rat) / denominator) := by
  have hdenI : (0 : Int) < denominator := by exact_mod_cast hden
  have hlowerI :
      (numerator * (scale : Int) / denominator) * denominator ≤
        numerator * scale := Int.ediv_mul_le _ hdenI.ne'
  have hdecomp := Int.emod_add_mul_ediv (numerator * (scale : Int)) denominator
  have hdecomp' :
      numerator * (scale : Int) % denominator +
          (numerator * (scale : Int) / denominator) * denominator =
        numerator * scale := by simpa [mul_comm] using hdecomp
  have hrem := Int.emod_lt_of_pos (numerator * (scale : Int)) hdenI
  have hupperI : numerator * (scale : Int) <
      (numerator * (scale : Int) / denominator + 1) * denominator := by
    calc
      numerator * (scale : Int) =
          numerator * (scale : Int) % denominator +
            (numerator * (scale : Int) / denominator) * denominator := hdecomp'.symm
      _ < denominator + (numerator * (scale : Int) / denominator) * denominator :=
        by simpa [add_comm] using
          add_lt_add_right hrem ((numerator * (scale : Int) / denominator) * denominator)
      _ = (numerator * (scale : Int) / denominator + 1) * denominator := by ring
  change
    ((numerator * (scale : Int) / denominator : Int) : Rat) ≤
          (scale : Rat) * ((numerator : Rat) / denominator) ∧
      (scale : Rat) * ((numerator : Rat) / denominator) ≤
          (((numerator * (scale : Int) / denominator + 1 : Int)) : Rat)
  have hdenQ : (0 : Rat) < denominator := by exact_mod_cast hden
  constructor
  · rw [show (scale : Rat) * ((numerator : Rat) / denominator) =
        ((numerator : Rat) * scale) / denominator by ring,
      le_div_iff₀ hdenQ]
    exact_mod_cast (by simpa [mul_comm, mul_left_comm] using hlowerI)
  ·
    rw [show (scale : Rat) * ((numerator : Rat) / denominator) =
        ((numerator : Rat) * scale) / denominator by ring]
    apply le_of_lt ((div_lt_iff₀ hdenQ).2 ?_)
    exact_mod_cast (by simpa [mul_comm, mul_left_comm] using hupperI)

def machinRows (scale K : Nat) : List FixedInterval :=
  ((List.range (2 * (K + 1))).map (fun n =>
      integerRow scale ((16 : Int) * (-1) ^ n)
        (5 ^ (2 * n + 1) * (2 * n + 1)))) ++
    ((List.range (2 * (K + 1) + 1)).map (fun n =>
      integerRow scale ((-4 : Int) * (-1) ^ n)
        (239 ^ (2 * n + 1) * (2 * n + 1))))

theorem machinRows_enclose (scale K : Nat) :
    List.Forall₂ (Encloses scale) (machinRows scale K) (machinTerms K) := by
  unfold machinRows machinTerms
  apply List.rel_append
  · induction List.range (2 * (K + 1)) with
    | nil => exact .nil
    | cons n ns ih => exact .cons (integerRow_encloses_fraction _ _ _ (by positivity)) ih
  · induction List.range (2 * (K + 1) + 1) with
    | nil => exact .nil
    | cons n ns ih => exact .cons (integerRow_encloses_fraction _ _ _ (by positivity)) ih

private theorem list_range_sum_eq_finset_sum (f : Nat → Rat) (n : Nat) :
    (List.map f (List.range n)).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem integerTerm_eq (coefficient : Int) (q n : Nat) :
    ((((coefficient * (-1) ^ n : Int) : Rat) /
        ((q ^ (2 * n + 1) * (2 * n + 1) : Nat) : Rat))) =
      (coefficient : Rat) * arctanTermRat q n := by
  simp [arctanTermRat, div_eq_mul_inv, mul_inv_rev]
  ring

theorem machinTerms_sum_eq (K : Nat) :
    (machinTerms K).sum = machinLowerRat K := by
  unfold machinTerms
  simp_rw [integerTerm_eq 16 5 _, integerTerm_eq (-4) 239 _]
  simp only [List.sum_append, list_range_sum_eq_finset_sum]
  simp [machinLowerRat, arctanPartialRat, arctanTermRat, Finset.mul_sum]
  ring

private def decimalScale500 : Nat := 10 ^ 500
private def workScale505 : Nat := 10 ^ 505
private def machinK500 : Nat := 180

private def piPrefix500 : Nat :=
  314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912

private def machinCertificate500 : AdditiveCertificate where
  scale := workScale505
  rows := machinRows workScale505 machinK500
  claimedLower :=
    31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491297976
  claimedUpper :=
    31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298701

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 1000 in
private theorem machinCertificate500_checks : check machinCertificate500 = true := by
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 1000 in
private theorem prefix500_lt_certified_lower :
    (piPrefix500 : Rat) / decimalScale500 <
      (machinCertificate500.claimedLower : Rat) / workScale505 := by
  norm_num [piPrefix500, decimalScale500, workScale505, machinCertificate500]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 1000 in
private theorem certified_upper_add_tail_lt_prefix500_succ :
    (machinCertificate500.claimedUpper : Rat) / workScale505 +
        1 / (625 : Rat) ^ machinK500 <
      (piPrefix500 + 1 : Rat) / decimalScale500 := by
  norm_num [piPrefix500, decimalScale500, workScale505, machinK500,
    machinCertificate500]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A real, substantially larger successor to T170's 100-place experiment.
The certificate checker evaluates 725 fixed-point rows but elaborates only two
large rational comparisons. -/
theorem pi_mem_decimalCylinder_500 :
    (piPrefix500 : Real) / decimalScale500 < Real.pi ∧
      Real.pi < (piPrefix500 + 1 : Real) / decimalScale500 := by
  have hbounds := checked_sum_bounds machinCertificate500_checks
    (machinRows_enclose workScale505 machinK500)
  rw [machinTerms_sum_eq] at hbounds
  have hlowerRat :
      (piPrefix500 : Rat) / decimalScale500 < machinLowerRat machinK500 :=
    prefix500_lt_certified_lower.trans_le hbounds.1
  have hupperRat :
      machinLowerRat machinK500 + 1 / (625 : Rat) ^ machinK500 <
        (piPrefix500 + 1 : Rat) / decimalScale500 := by
    calc
      machinLowerRat machinK500 + 1 / (625 : Rat) ^ machinK500 ≤
          (machinCertificate500.claimedUpper : Rat) / workScale505 +
            1 / (625 : Rat) ^ machinK500 := by
        have hu := add_le_add_right hbounds.2 (1 / (625 : Rat) ^ machinK500)
        simpa only [machinCertificate500, add_comm] using hu
      _ < _ := certified_upper_add_tail_lt_prefix500_succ
  constructor
  · have hcast :
        ((((piPrefix500 : Rat) / decimalScale500 : Rat)) : Real) <
          (machinLowerRat machinK500 : Real) := Rat.cast_lt.mpr hlowerRat
    exact (show (piPrefix500 : Real) / decimalScale500 < machinLower machinK500 by
      simpa [machinLower] using hcast).trans_le (machinLower_le_pi machinK500)
  · have htail := pi_sub_machinLower_lt_pow625 machinK500
    have hcast :
        ((machinLowerRat machinK500 + 1 / (625 : Rat) ^ machinK500 : Rat) : Real) <
          ((((piPrefix500 + 1 : Rat) / decimalScale500 : Rat)) : Real) :=
      Rat.cast_lt.mpr hupperRat
    have hreal :
        machinLower machinK500 + 1 / (625 : Real) ^ machinK500 <
          (piPrefix500 + 1 : Real) / decimalScale500 := by
      simpa [machinLower] using hcast
    linarith

end Theory.PiDigits.T171CompactFixedPointCertificate

#print axioms Theory.PiDigits.T171CompactFixedPointCertificate.pi_mem_decimalCylinder_500
