import TheoryLib.PiQuantitativeBlockHitting.T36T36MachinGridStability

/-!
# T37: exact bridge from arithmetic floor blocks to symbolic pi cylinders

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T35 and T36 compare an explicit rational Machin approximation with `pi`
through the difference of two integer prefix floors.  This module identifies
that arithmetic code exactly with the repository's symbolic length-`m` pi
cylinder at the same zero-based start `N`.

The underlying identity is valid for every real `x`, including negative
values: subtracting the scaled integer part leaves the floor of the scaled
fractional part.  Thus the resulting finite code always uses the half-open
floor-cell convention.  This convention is unambiguous at terminating
rational endpoints.  At `m = 0`, both sides are the unique code in `Fin 1`.

The final Machin statements retain T36's explicit published hypothesis
`IrrationalityMeasureBelow pi 8`.  They prove eventual agreement with the
symbolic pi cylinder, not density, normality, or the every-word conjecture.
-/

noncomputable section

open Filter

namespace Theory.PiDigits.FloorSymbolicBridge

open DecimalFactorComplexity
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.FiniteCylinderEnergy
open Theory.PiDigits.OversampledBBPGridStability
open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- Scaling a real by a natural number splits its floor into the scaled
integer part and the floor of the scaled fractional part.  No sign condition
on `x` is needed. -/
theorem floor_natScale_sub_eq_floor_natScale_fract (q : ℕ) (x : ℝ) :
    ⌊(q : ℝ) * x⌋ - (q : ℤ) * ⌊x⌋ =
      ⌊(q : ℝ) * Int.fract x⌋ := by
  let z : ℤ := (q : ℤ) * ⌊x⌋
  have hfloor :
      ⌊(q : ℝ) * x⌋ = z + ⌊(q : ℝ) * Int.fract x⌋ := by
    calc
      ⌊(q : ℝ) * x⌋ =
          ⌊(z : ℝ) + (q : ℝ) * Int.fract x⌋ := by
        congr 1
        dsimp [z]
        push_cast
        nlinarith [Int.floor_add_fract x]
      _ = z + ⌊(q : ℝ) * Int.fract x⌋ :=
        Int.floor_intCast_add z ((q : ℝ) * Int.fract x)
  dsimp [z] at hfloor
  omega

/-- Power-of-ten form of the generic floor/fractional-part identity. -/
theorem floor_powTen_add_sub_eq_floor_powTen_fract
    (x : ℝ) (N m : ℕ) :
    ⌊(10 : ℝ) ^ (N + m) * x⌋ -
        ((10 ^ m : ℕ) : ℤ) * ⌊(10 : ℝ) ^ N * x⌋ =
      ⌊(10 : ℝ) ^ m * Int.fract ((10 : ℝ) ^ N * x)⌋ := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_add, mul_assoc, mul_comm,
    mul_left_comm] using
    (floor_natScale_sub_eq_floor_natScale_fract (10 ^ m)
      ((10 : ℝ) ^ N * x))

/-- T35's arithmetic block code is exactly the floor label of the scaled
fractional orbit, for every real input. -/
theorem decimalBlockCode_eq_floor_powTen_fract
    (x : ℝ) (N m : ℕ) :
    decimalBlockCode x N m =
      ⌊(10 : ℝ) ^ m * Int.fract ((10 : ℝ) ^ N * x)⌋ := by
  simpa only [decimalBlockCode, decimalPrefixFloor, Nat.cast_pow,
    Nat.cast_ofNat] using
    (floor_powTen_add_sub_eq_floor_powTen_fract x N m)

/-- The same half-open arithmetic block label packaged canonically in
`Fin (10^m)`.  Defining it through the nonnegative fractional part makes the
range proof uniform even when `x` is negative. -/
def decimalBlockFinCode (x : ℝ) (N m : ℕ) : Fin (10 ^ m) := by
  refine ⟨⌊(10 : ℝ) ^ m * Int.fract ((10 : ℝ) ^ N * x)⌋₊, ?_⟩
  apply (Nat.floor_lt
    (mul_nonneg (by positivity) (Int.fract_nonneg _))).2
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_one] using
    (mul_lt_mul_of_pos_left
      (Int.fract_lt_one ((10 : ℝ) ^ N * x)) (by positivity : 0 < (10 : ℝ) ^ m))

/-- The integer-valued and finite-valued arithmetic block codes agree
exactly. -/
theorem decimalBlockCode_eq_intCast_decimalBlockFinCode
    (x : ℝ) (N m : ℕ) :
    decimalBlockCode x N m = (decimalBlockFinCode x N m).val := by
  rw [decimalBlockCode_eq_floor_powTen_fract]
  let y : ℝ := (10 : ℝ) ^ m * Int.fract ((10 : ℝ) ^ N * x)
  have hy : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg (by positivity) (Int.fract_nonneg _)
  have hfloor : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy
  change ⌊y⌋ = (⌊y⌋₊ : ℤ)
  calc
    ⌊y⌋ = ((⌊y⌋.toNat : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg hfloor).symm
    _ = (⌊y⌋₊ : ℤ) := by rw [Int.floor_toNat]

@[simp] theorem decimalBlockCode_zero_length (x : ℝ) (N : ℕ) :
    decimalBlockCode x N 0 = 0 := by
  simp [decimalBlockCode, decimalPrefixFloor]

@[simp] theorem decimalBlockFinCode_zero_length (x : ℝ) (N : ℕ) :
    decimalBlockFinCode x N 0 = 0 := by
  apply Fin.ext
  omega

/-- The finite arithmetic code of `pi` is the exact symbolic cylinder label.
The zero-based start `N` is preserved, and the result includes `m = 0`. -/
theorem decimalBlockFinCode_pi_eq_piCylinderCode (N m : ℕ) :
    decimalBlockFinCode Real.pi N m = piCylinderCode m N := by
  rw [piCylinderCode_eq_decimalCode]
  apply Fin.ext
  change ⌊(10 : ℝ) ^ m * Int.fract ((10 : ℝ) ^ N * Real.pi)⌋₊ =
    ⌊unitCoordinate (DecimalFactorComplexity.ClusterNearReturns.piDecimalCircleOrbit N) *
      ((10 ^ m : ℕ) : ℝ)⌋₊
  rw [unitCoordinate_piDecimalCircleOrbit]
  simp only [Theory.PiDigits.T20.baseTenOrbit, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_comm]

/-- Integer-valued version of the exact pi cylinder bridge. -/
theorem decimalBlockCode_pi_eq_piCylinderCode_val (N m : ℕ) :
    decimalBlockCode Real.pi N m = (piCylinderCode m N).val := by
  rw [decimalBlockCode_eq_intCast_decimalBlockFinCode,
    decimalBlockFinCode_pi_eq_piCylinderCode]

/-- The symbolic cylinder value is literally the value of the contiguous
`blockAt piDigit m N` word.  This records the repository's indexing
convention explicitly: digit zero is the first fractional digit. -/
theorem piCylinderCode_val_eq_blockAt_wordValue (N m : ℕ) :
    (piCylinderCode m N).val =
      Theory.PiDigits.T20.wordValue
        (List.ofFn (blockAt Theory.PiDigits.piDigit m N)) := by
  rfl

/-- T35's arithmetic pi block code is exactly the numerical value of the
repository's symbolic contiguous pi block. -/
theorem decimalBlockCode_pi_eq_blockAt_wordValue (N m : ℕ) :
    decimalBlockCode Real.pi N m =
      (Theory.PiDigits.T20.wordValue
        (List.ofFn (blockAt Theory.PiDigits.piDigit m N)) : ℤ) := by
  rw [decimalBlockCode_pi_eq_piCylinderCode_val,
    piCylinderCode_val_eq_blockAt_wordValue]

/-- Conditional T36 output with the former floor-code/symbolic-code gap
closed: the triple-oversampled rational Machin code eventually equals the
integer value of the exact symbolic pi cylinder. -/
theorem pi_eventually_decimalBlockCode_threeOversampled_machinLower_eq_piCylinderCode
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      decimalBlockCode (machinLower (3 * N)) N m =
        (piCylinderCode m N).val := by
  intro m
  obtain ⟨C, hC⟩ :=
    pi_eventually_decimalBlockCode_threeOversampled_machinLower_eq hSource m
  exact ⟨C, fun N hN ↦
    (hC N hN).trans (decimalBlockCode_pi_eq_piCylinderCode_val N m)⟩

/-- The explicit rational Machin floor code as a fixed-alphabet stream for a
chosen block length `m`. -/
def machinBlockCode (m : ℕ) : ℕ → Fin (10 ^ m) := fun N ↦
  decimalBlockFinCode (machinLower (3 * N)) N m

/-- Conditional eventual equality of the Fin-valued rational Machin-code
stream and the symbolic pi-cylinder stream. -/
theorem eventually_machinBlockCode_eq_piCylinderCode
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) (m : ℕ) :
    machinBlockCode m =ᶠ[atTop] piCylinderCode m := by
  obtain ⟨C, hC⟩ :=
    pi_eventually_decimalBlockCode_threeOversampled_machinLower_eq hSource m
  filter_upwards [eventually_ge_atTop C] with N hN
  apply Fin.ext
  have hcode := hC N hN
  rw [decimalBlockCode_eq_intCast_decimalBlockFinCode,
    decimalBlockCode_pi_eq_piCylinderCode_val] at hcode
  exact_mod_cast hcode

end Theory.PiDigits.FloorSymbolicBridge

namespace Theory.PiDigits.FloorSymbolicBridge

#print axioms floor_natScale_sub_eq_floor_natScale_fract
#print axioms floor_powTen_add_sub_eq_floor_powTen_fract
#print axioms decimalBlockCode_eq_floor_powTen_fract
#print axioms decimalBlockCode_eq_intCast_decimalBlockFinCode
#print axioms decimalBlockCode_zero_length
#print axioms decimalBlockFinCode_zero_length
#print axioms decimalBlockFinCode_pi_eq_piCylinderCode
#print axioms decimalBlockCode_pi_eq_piCylinderCode_val
#print axioms piCylinderCode_val_eq_blockAt_wordValue
#print axioms decimalBlockCode_pi_eq_blockAt_wordValue
#print axioms pi_eventually_decimalBlockCode_threeOversampled_machinLower_eq_piCylinderCode
#print axioms eventually_machinBlockCode_eq_piCylinderCode

end Theory.PiDigits.FloorSymbolicBridge
