import TheoryLib.PiQuantitativeBlockHitting.T173T173MachinIntegerCertificate10015

/-!
# T175: decimal cylinders transport to orbit suffix cylinders

A strict length-`L` decimal cylinder for `x` determines, after multiplication
by `10^n`, the strict cylinder encoded by the remaining suffix of the prefix.
The proof explicitly identifies the floor, so the all-nines suffix case is
covered without a non-wrapping assumption: its upper endpoint is exactly one.
-/

namespace Theory.PiDigits.T175DecimalSuffixCylinder

/-- A strict rational cylinder transports through an integral scale factor.
The new numerator is the remainder modulo the remaining denominator. -/
theorem fract_mul_mem_suffixCylinder
    (x : ℝ) (P scale multiplier suffixScale : ℕ)
    (hmultiplier : 0 < multiplier) (hsuffixScale : 0 < suffixScale)
    (hscale : scale = multiplier * suffixScale)
    (hx : (P : ℝ) / scale < x ∧ x < (P + 1 : ℝ) / scale) :
    ((P % suffixScale : ℕ) : ℝ) / suffixScale <
        Int.fract ((multiplier : ℝ) * x) ∧
      Int.fract ((multiplier : ℝ) * x) <
        ((P % suffixScale : ℕ) + 1 : ℝ) / suffixScale := by
  have hmR : (0 : ℝ) < multiplier := by exact_mod_cast hmultiplier
  have hsR : (0 : ℝ) < suffixScale := by exact_mod_cast hsuffixScale
  have hscaleR : (scale : ℝ) = multiplier * suffixScale := by
    exact_mod_cast hscale
  have hcancel (a : ℝ) :
      (multiplier : ℝ) * (a / ((multiplier : ℝ) * suffixScale)) =
        a / suffixScale := by
    field_simp
  have hlower : (P : ℝ) / suffixScale < (multiplier : ℝ) * x := by
    have h := mul_lt_mul_of_pos_left hx.1 hmR
    rw [hscaleR] at h
    rw [hcancel] at h
    exact h
  have hupper : (multiplier : ℝ) * x < (P + 1 : ℝ) / suffixScale := by
    have h := mul_lt_mul_of_pos_left hx.2 hmR
    rw [hscaleR] at h
    rw [hcancel] at h
    exact h
  have hPdecomp : P % suffixScale + suffixScale * (P / suffixScale) = P :=
    Nat.mod_add_div P suffixScale
  have hrem_lt : P % suffixScale < suffixScale := Nat.mod_lt P hsuffixScale
  have hquot_lower : ((P / suffixScale : ℕ) : ℝ) < (multiplier : ℝ) * x := by
    have hrem_nonneg : (0 : ℝ) ≤ ((P % suffixScale : ℕ) : ℝ) := by positivity
    have hdecompR : (P : ℝ) =
        ((P % suffixScale : ℕ) : ℝ) +
          suffixScale * ((P / suffixScale : ℕ) : ℝ) := by
      exact_mod_cast hPdecomp.symm
    have hPdiv : (P : ℝ) / suffixScale =
        ((P / suffixScale : ℕ) : ℝ) +
          ((P % suffixScale : ℕ) : ℝ) / suffixScale := by
      rw [hdecompR]
      field_simp
      ring
    rw [hPdiv] at hlower
    have hremfrac_nonneg :
        (0 : ℝ) ≤ ((P % suffixScale : ℕ) : ℝ) / suffixScale :=
      div_nonneg hrem_nonneg hsR.le
    linarith
  have hquot_upper : (multiplier : ℝ) * x <
      ((P / suffixScale : ℕ) : ℝ) + 1 := by
    have hdecompR : (P + 1 : ℝ) =
        ((P % suffixScale : ℕ) : ℝ) +
          suffixScale * ((P / suffixScale : ℕ) : ℝ) + 1 := by
      exact_mod_cast congrArg (fun z : ℕ => z + 1) hPdecomp.symm
    have hrem_succ : ((P % suffixScale : ℕ) : ℝ) + 1 ≤ suffixScale := by
      exact_mod_cast hrem_lt
    have hPdiv : (P + 1 : ℝ) / suffixScale =
        ((P / suffixScale : ℕ) : ℝ) +
          (((P % suffixScale : ℕ) : ℝ) + 1) / suffixScale := by
      rw [hdecompR]
      field_simp
      ring
    rw [hPdiv] at hupper
    have hfrac_le :
        (((P % suffixScale : ℕ) : ℝ) + 1) / suffixScale ≤ 1 := by
      exact (div_le_one hsR).2 hrem_succ
    nlinarith
  have hfloor : ⌊(multiplier : ℝ) * x⌋ = (P / suffixScale : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast hquot_lower.le
    · exact_mod_cast hquot_upper
  rw [Int.fract, hfloor]
  have hdecompR : (P : ℝ) =
      ((P % suffixScale : ℕ) : ℝ) +
        suffixScale * ((P / suffixScale : ℕ) : ℝ) := by
    exact_mod_cast hPdecomp.symm
  change
    ((P % suffixScale : ℕ) : ℝ) / suffixScale <
        (multiplier : ℝ) * x - ((P / suffixScale : ℕ) : ℝ) ∧
      (multiplier : ℝ) * x - ((P / suffixScale : ℕ) : ℝ) <
        (((P % suffixScale : ℕ) : ℝ) + 1) / suffixScale
  have hPdiv : (P : ℝ) / suffixScale =
      ((P / suffixScale : ℕ) : ℝ) +
        ((P % suffixScale : ℕ) : ℝ) / suffixScale := by
    rw [hdecompR]
    field_simp
    ring
  constructor
  · rw [hPdiv] at hlower
    linarith
  · have hPsuccDiv : (P + 1 : ℝ) / suffixScale =
        ((P / suffixScale : ℕ) : ℝ) +
          (((P % suffixScale : ℕ) : ℝ) + 1) / suffixScale := by
      rw [hdecompR]
      field_simp
      ring
    rw [hPsuccDiv] at hupper
    linarith

/-- Decimal specialization: after `n ≤ L` shifts, the surviving cylinder
is encoded by the suffix `P % 10^(L-n)`. -/
theorem fract_powTen_mem_decimalSuffixCylinder
    (x : ℝ) (P L n : ℕ) (hnL : n ≤ L)
    (hx : (P : ℝ) / ((10 ^ L : ℕ) : ℝ) < x ∧
      x < (P + 1 : ℝ) / ((10 ^ L : ℕ) : ℝ)) :
    ((P % 10 ^ (L - n) : ℕ) : ℝ) /
        ((10 ^ (L - n) : ℕ) : ℝ) <
        Int.fract ((10 : ℝ) ^ n * x) ∧
      Int.fract ((10 : ℝ) ^ n * x) <
        ((P % 10 ^ (L - n) : ℕ) + 1 : ℝ) /
          ((10 ^ (L - n) : ℕ) : ℝ) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (fract_mul_mem_suffixCylinder x P (10 ^ L) (10 ^ n) (10 ^ (L - n))
      (by positivity) (by positivity) (by rw [← pow_add, Nat.add_sub_of_le hnL]) hx)

/-- Direct consumer of the public 10,015-place T173 certificate. -/
theorem piOrbit_mem_certified_suffixCylinder (n : ℕ)
    (hn : n ≤
      Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPlaces) :
    ((Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPrefix %
          10 ^ (Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPlaces - n) : ℕ) : ℝ) /
        ((10 ^ (Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPlaces - n) : ℕ) : ℝ) <
          Int.fract ((10 : ℝ) ^ n * Real.pi) ∧
      Int.fract ((10 : ℝ) ^ n * Real.pi) <
        ((Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPrefix %
            10 ^ (Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPlaces - n) : ℕ) + 1 : ℝ) /
          ((10 ^ (Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPlaces - n) : ℕ) : ℝ) := by
  apply fract_powTen_mem_decimalSuffixCylinder
    Real.pi
    Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPrefix
    Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPlaces n hn
  have hscale :
      Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiScale =
        10 ^ Theory.PiDigits.T173MachinIntegerCertificate10015.certifiedPiPlaces := rfl
  have hx :=
    Theory.PiDigits.T173MachinIntegerCertificate10015.pi_mem_certified_decimalCylinder
  rw [hscale] at hx
  exact hx

end Theory.PiDigits.T175DecimalSuffixCylinder

#print axioms Theory.PiDigits.T175DecimalSuffixCylinder.fract_mul_mem_suffixCylinder
#print axioms Theory.PiDigits.T175DecimalSuffixCylinder.fract_powTen_mem_decimalSuffixCylinder
#print axioms Theory.PiDigits.T175DecimalSuffixCylinder.piOrbit_mem_certified_suffixCylinder
