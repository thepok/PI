import TheoryLib.PiQuantitativeBlockHitting.T58T58HuttonRationalShadow
import TheoryLib.PiQuantitativeBlockHitting.T37T37FloorSymbolicBridge

/-!
# T59: exact decimal-cylinder certificates from a Hutton bracket

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

If a certified real bracket is contained in one translated half-open base-ten
cylinder at a prescribed position, every point of that bracket has the same
arithmetic block code.  Applying T58's rational Hutton bracket therefore
gives an exact finite certificate for one prescribed contiguous block of pi.

The module proves only this implication.  It does not prove that a suitable
Hutton bracket exists for every word or at any unbounded family of positions,
and hence proves no density, normality, or every-word statement for pi.
-/

noncomputable section

namespace Theory.PiDigits.HuttonCylinderCertificate

open Theory.PiDigits.OversampledBBPGridStability
open Theory.PiDigits.FloorSymbolicBridge
open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open DecimalFactorComplexity.FiniteCylinderEnergy

/-- A real point trapped in a translated decimal cylinder has the stated
arithmetic block code.  The integer `z` is the whole-number part at the
prescribed scale; `a` is the length-`m` cylinder label. -/
theorem decimalBlockCode_eq_of_mem_scaled_cylinder
    {x : ℝ} {N m a : ℕ} {z : ℤ}
    (ha : a < 10 ^ m)
    (hlower : (z : ℝ) + (a : ℝ) / (10 : ℝ) ^ m ≤
      (10 : ℝ) ^ N * x)
    (hupper : (10 : ℝ) ^ N * x <
      (z : ℝ) + ((a + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m) :
    decimalBlockCode x N m = (a : ℤ) := by
  let X : ℝ := (10 : ℝ) ^ N * x
  let q : ℕ := 10 ^ m
  have hqpos : (0 : ℝ) < q := by positivity
  have hqcast : (q : ℝ) = (10 : ℝ) ^ m := by simp [q]
  have ha_nonneg : (0 : ℝ) ≤ a := by positivity
  have hfrac_nonneg : (0 : ℝ) ≤ (a : ℝ) / (10 : ℝ) ^ m := by positivity
  have ha_succ_le : a + 1 ≤ q := by omega
  have hfrac_succ_le : ((a + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (10 : ℝ) ^ m)]
    dsimp [q] at ha_succ_le
    exact_mod_cast ha_succ_le
  have hXlower : (z : ℝ) ≤ X := by
    dsimp [X]
    exact le_trans (le_add_of_nonneg_right hfrac_nonneg) hlower
  have hXupper : X < (z : ℝ) + 1 := by
    dsimp [X]
    have hzadd :
        (z : ℝ) + ((a + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m ≤
          (z : ℝ) + 1 := by
      linarith
    exact hupper.trans_le hzadd
  have hfloorN : ⌊X⌋ = z := by
    rw [Int.floor_eq_iff]
    exact ⟨hXlower, hXupper⟩
  have hfloorNm : ⌊(q : ℝ) * X⌋ = (q : ℤ) * z + (a : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hlower hqpos.le
      calc
        (((q : ℤ) * z + (a : ℤ) : ℤ) : ℝ) =
            (q : ℝ) * (z : ℝ) + (a : ℝ) := by
          push_cast
          rfl
        _ = (q : ℝ) * ((z : ℝ) + (a : ℝ) / (10 : ℝ) ^ m) := by
          rw [hqcast]
          field_simp
        _ ≤ (q : ℝ) * X := by simpa [X] using hmul
    · have hmul := mul_lt_mul_of_pos_left hupper hqpos
      calc
        (q : ℝ) * X <
            (q : ℝ) * ((z : ℝ) + ((a + 1 : ℕ) : ℝ) /
              (10 : ℝ) ^ m) := by simpa [X] using hmul
        _ = (q : ℝ) * (z : ℝ) + ((a + 1 : ℕ) : ℝ) := by
          rw [hqcast]
          field_simp
        _ = (((q : ℤ) * z + (a : ℤ) : ℤ) : ℝ) + 1 := by
          push_cast
          ring
  unfold decimalBlockCode decimalPrefixFloor
  have hpow : (10 : ℝ) ^ (N + m) * x = (q : ℝ) * X := by
    dsimp [q, X]
    simp only [Nat.cast_pow, Nat.cast_ofNat, pow_add]
    ring
  rw [hpow, hfloorNm]
  have hfloorN' : ⌊(10 : ℝ) ^ N * x⌋ = z := by simpa [X] using hfloorN
  rw [hfloorN']
  simp [q]

/-- Any closed bracket contained in one translated decimal cylinder gives
the same code for every point in the bracket. -/
theorem decimalBlockCode_eq_of_bracket_in_scaled_cylinder
    {lower upper x : ℝ} {N m a : ℕ} {z : ℤ}
    (hlx : lower ≤ x) (hxu : x ≤ upper)
    (ha : a < 10 ^ m)
    (hlower : (z : ℝ) + (a : ℝ) / (10 : ℝ) ^ m ≤
      (10 : ℝ) ^ N * lower)
    (hupper : (10 : ℝ) ^ N * upper <
      (z : ℝ) + ((a + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m) :
    decimalBlockCode x N m = (a : ℤ) := by
  apply decimalBlockCode_eq_of_mem_scaled_cylinder ha
  · exact hlower.trans (mul_le_mul_of_nonneg_left hlx (by positivity))
  · exact (mul_le_mul_of_nonneg_left hxu (by positivity)).trans_lt hupper

/-- T58's exact rational Hutton bracket certifies the arithmetic pi block
whenever its scaled endpoints fit in the requested half-open cylinder. -/
theorem decimalBlockCode_pi_eq_of_hutton_bracket
    (K N m a : ℕ) (z : ℤ)
    (ha : a < 10 ^ m)
    (hlower : (z : ℝ) + (a : ℝ) / (10 : ℝ) ^ m ≤
      (10 : ℝ) ^ N * huttonLower K)
    (hupper : (10 : ℝ) ^ N * huttonUpper K <
      (z : ℝ) + ((a + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m) :
    decimalBlockCode Real.pi N m = (a : ℤ) := by
  exact decimalBlockCode_eq_of_bracket_in_scaled_cylinder
    (huttonLower_le_pi K) (pi_le_huttonUpper K) ha hlower hupper

/-- Symbolic form of the same finite certificate: the canonical length-`m`
pi cylinder at zero-based position `N` has numerical value `a`. -/
theorem piCylinderCode_val_eq_of_hutton_bracket
    (K N m a : ℕ) (z : ℤ)
    (ha : a < 10 ^ m)
    (hlower : (z : ℝ) + (a : ℝ) / (10 : ℝ) ^ m ≤
      (10 : ℝ) ^ N * huttonLower K)
    (hupper : (10 : ℝ) ^ N * huttonUpper K <
      (z : ℝ) + ((a + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m) :
    (piCylinderCode m N).val = a := by
  have hcode := decimalBlockCode_pi_eq_of_hutton_bracket
    K N m a z ha hlower hupper
  rw [decimalBlockCode_pi_eq_piCylinderCode_val] at hcode
  exact_mod_cast hcode

end Theory.PiDigits.HuttonCylinderCertificate

#print axioms
  Theory.PiDigits.HuttonCylinderCertificate.decimalBlockCode_eq_of_mem_scaled_cylinder
#print axioms
  Theory.PiDigits.HuttonCylinderCertificate.decimalBlockCode_eq_of_bracket_in_scaled_cylinder
#print axioms
  Theory.PiDigits.HuttonCylinderCertificate.decimalBlockCode_pi_eq_of_hutton_bracket
#print axioms
  Theory.PiDigits.HuttonCylinderCertificate.piCylinderCode_val_eq_of_hutton_bracket
