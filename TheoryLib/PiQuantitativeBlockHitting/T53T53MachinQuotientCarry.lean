import TheoryLib.PiQuantitativeBlockHitting.T52T52MachinSeedThreePrimaryPersistence

/-!
# T53: exact quotient and carry recurrence for a factored rational grid

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Write a numerator modulo `F * D` as `F * c + r`, with `r < F` and
`c < D`.  The local denominator calculations determine the fine remainder
`r`, while `c` is the complementary quotient.  This module proves the exact
base-ten carry recurrence for that split.  In particular, the next decimal
digit is the coarse carry

`(10 * c + (10 * r) / F) / D`.

These are elementary exact identities.  They expose why knowing the fine CRT
components does not by itself select a decimal cell.  They do not prove a
Machin numerator-distribution estimate, a cylinder hit, normality, or the
every-word conjecture for pi.
-/

noncomputable section

namespace Theory.PiDigits.MachinQuotientCarry

/-- The fine remainder of a numerator modulo the controlled factor. -/
def fineRemainder (b F : ℕ) : ℕ := b % F

/-- The complementary quotient after the fine factor has been removed. -/
def coarseQuotient (b F : ℕ) : ℕ := b / F

/-- The carry created inside the controlled factor by one multiplication by
ten. -/
def fineCarry (r F : ℕ) : ℕ := (10 * r) / F

/-- The next fine remainder after multiplication by ten. -/
def nextFineRemainder (r F : ℕ) : ℕ := (10 * r) % F

/-- The carry through the complementary factor.  For a canonical numerator
state, this is the next base-ten digit. -/
def decimalCarry (c r F D : ℕ) : ℕ :=
  (10 * c + fineCarry r F) / D

/-- The next complementary quotient state. -/
def nextCoarseQuotient (c r F D : ℕ) : ℕ :=
  (10 * c + fineCarry r F) % D

/-- The reconstructed numerator after one multiplication by ten and reduction
modulo the full factored denominator. -/
def nextNumerator (c r F D : ℕ) : ℕ :=
  F * nextCoarseQuotient c r F D + nextFineRemainder r F

/-- Euclidean quotient and remainder reconstruct the original numerator. -/
theorem coarse_mul_add_fine_eq (b F : ℕ) :
    F * coarseQuotient b F + fineRemainder b F = b := by
  exact Nat.div_add_mod b F

/-- The canonical fine remainder lies in its expected range. -/
theorem fineRemainder_lt (b F : ℕ) (hF : 0 < F) :
    fineRemainder b F < F := by
  exact Nat.mod_lt b hF

/-- A numerator below `F * D` has complementary quotient below `D`. -/
theorem coarseQuotient_lt
    (b F D : ℕ) (hF : 0 < F) (hb : b < F * D) :
    coarseQuotient b F < D := by
  rw [coarseQuotient, Nat.div_lt_iff_lt_mul hF]
  simpa [Nat.mul_comm] using hb

/-- Exact rational split into the coarse grid point and its fine offset. -/
theorem quotient_split_rat
    (c r F D : ℕ) (hF : 0 < F) (hD : 0 < D) :
    (((F * c + r : ℕ) : ℚ) / ((F * D : ℕ) : ℚ)) =
      (c : ℚ) / D + (r : ℚ) / ((F * D : ℕ) : ℚ) := by
  have hFq : (F : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hF)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  push_cast
  field_simp

/-- Multiplication by the complementary factor recovers the coarse cell plus
the normalized fine remainder. -/
theorem scaled_quotient_split_rat
    (c r F D : ℕ) (hF : 0 < F) (hD : 0 < D) :
    (D : ℚ) *
        (((F * c + r : ℕ) : ℚ) / ((F * D : ℕ) : ℚ)) =
      (c : ℚ) + (r : ℚ) / F := by
  rw [quotient_split_rat c r F D hF hD]
  have hFq : (F : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hF)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  push_cast
  field_simp

/-- The fine carry is a decimal digit. -/
theorem fineCarry_lt_ten
    (r F : ℕ) (hF : 0 < F) (hr : r < F) :
    fineCarry r F < 10 := by
  rw [fineCarry, Nat.div_lt_iff_lt_mul hF]
  exact (Nat.mul_lt_mul_left (by norm_num : 0 < 10)).2 hr

/-- The next fine remainder remains in its factor. -/
theorem nextFineRemainder_lt
    (r F : ℕ) (hF : 0 < F) :
    nextFineRemainder r F < F := by
  exact Nat.mod_lt _ hF

/-- The next coarse quotient remains in its complementary factor. -/
theorem nextCoarseQuotient_lt
    (c r F D : ℕ) (hD : 0 < D) :
    nextCoarseQuotient c r F D < D := by
  exact Nat.mod_lt _ hD

/-- Exact two-level Euclidean reconstruction after multiplying the numerator
by ten. -/
theorem ten_mul_eq_fullCarry_add_nextNumerator
    (c r F D : ℕ) :
    10 * (F * c + r) =
      (F * D) * decimalCarry c r F D + nextNumerator c r F D := by
  simp only [fineCarry, decimalCarry, nextCoarseQuotient,
    nextFineRemainder, nextNumerator]
  calc
    10 * (F * c + r) = F * (10 * c) + 10 * r := by ring
    _ = F * (10 * c) +
        (F * ((10 * r) / F) + (10 * r) % F) := by
      rw [Nat.div_add_mod]
    _ = F * (10 * c + (10 * r) / F) + (10 * r) % F := by ring
    _ = F *
          (D * ((10 * c + (10 * r) / F) / D) +
            (10 * c + (10 * r) / F) % D) +
          (10 * r) % F := by
      rw [Nat.div_add_mod]
    _ = (F * D) * ((10 * c + (10 * r) / F) / D) +
          (F * ((10 * c + (10 * r) / F) % D) +
            (10 * r) % F) := by ring

/-- The reconstructed next numerator is the canonical remainder modulo the
full denominator. -/
theorem nextNumerator_lt
    (c r F D : ℕ) (hF : 0 < F) (hD : 0 < D) :
    nextNumerator c r F D < F * D := by
  have hc : nextCoarseQuotient c r F D < D :=
    nextCoarseQuotient_lt c r F D hD
  have hr : nextFineRemainder r F < F :=
    nextFineRemainder_lt r F hF
  have hcSucc : nextCoarseQuotient c r F D + 1 ≤ D :=
    Nat.succ_le_iff.mpr hc
  have hmul :
      F * (nextCoarseQuotient c r F D + 1) ≤ F * D :=
    Nat.mul_le_mul_left F hcSucc
  calc
    nextNumerator c r F D =
        F * nextCoarseQuotient c r F D + nextFineRemainder r F := rfl
    _ < F * nextCoarseQuotient c r F D + F :=
      Nat.add_lt_add_left hr _
    _ = F * (nextCoarseQuotient c r F D + 1) := by ring
    _ ≤ F * D := hmul

/-- The coarse carry is exactly the quotient by the full denominator.  For a
canonical rational numerator state, it is the next base-ten digit. -/
theorem decimalCarry_eq_fullQuotient
    (c r F D : ℕ) (hF : 0 < F) (hD : 0 < D) :
    decimalCarry c r F D =
      (10 * (F * c + r)) / (F * D) := by
  have hrec := ten_mul_eq_fullCarry_add_nextNumerator c r F D
  have hnext := nextNumerator_lt c r F D hF hD
  have hFD : 0 < F * D := Nat.mul_pos hF hD
  rw [hrec, Nat.add_comm]
  rw [Nat.add_mul_div_left _ _ hFD,
    Nat.div_eq_of_lt hnext, zero_add]

/-- The reconstructed state is exactly the residue modulo the full
denominator. -/
theorem nextNumerator_eq_fullRemainder
    (c r F D : ℕ) (hF : 0 < F) (hD : 0 < D) :
    nextNumerator c r F D =
      (10 * (F * c + r)) % (F * D) := by
  have hrec := ten_mul_eq_fullCarry_add_nextNumerator c r F D
  have hnext := nextNumerator_lt c r F D hF hD
  rw [hrec, Nat.add_comm]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hnext]

/-- Reducing the next full numerator modulo `F` recovers the fine recurrence. -/
theorem nextNumerator_mod_eq_nextFineRemainder
    (c r F D : ℕ) (hF : 0 < F) :
    nextNumerator c r F D % F = nextFineRemainder r F := by
  have hnextFine := nextFineRemainder_lt r F hF
  rw [nextNumerator, Nat.add_comm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hnextFine]

/-- Dividing the next full numerator by `F` recovers the coarse recurrence. -/
theorem nextNumerator_div_eq_nextCoarseQuotient
    (c r F D : ℕ) (hF : 0 < F) :
    nextNumerator c r F D / F = nextCoarseQuotient c r F D := by
  have hnextFine := nextFineRemainder_lt r F hF
  rw [nextNumerator, Nat.add_comm, Nat.add_mul_div_left _ _ hF,
    Nat.div_eq_of_lt hnextFine, zero_add]

/-- For a canonical state, the full carry is one of the ten decimal digits. -/
theorem decimalCarry_lt_ten
    (c r F D : ℕ) (hF : 0 < F) (hD : 0 < D)
    (hc : c < D) (hr : r < F) :
    decimalCarry c r F D < 10 := by
  have hk : fineCarry r F < 10 := fineCarry_lt_ten r F hF hr
  rw [decimalCarry, Nat.div_lt_iff_lt_mul hD]
  have hcSucc : c + 1 ≤ D := Nat.succ_le_iff.mpr hc
  have hleft : 10 * c + fineCarry r F < 10 * (c + 1) := by
    omega
  have hright : 10 * (c + 1) ≤ 10 * D :=
    Nat.mul_le_mul_left 10 hcSucc
  exact hleft.trans_le hright

end Theory.PiDigits.MachinQuotientCarry

#print axioms Theory.PiDigits.MachinQuotientCarry.coarse_mul_add_fine_eq
#print axioms Theory.PiDigits.MachinQuotientCarry.fineRemainder_lt
#print axioms Theory.PiDigits.MachinQuotientCarry.coarseQuotient_lt
#print axioms Theory.PiDigits.MachinQuotientCarry.quotient_split_rat
#print axioms Theory.PiDigits.MachinQuotientCarry.scaled_quotient_split_rat
#print axioms Theory.PiDigits.MachinQuotientCarry.fineCarry_lt_ten
#print axioms Theory.PiDigits.MachinQuotientCarry.nextFineRemainder_lt
#print axioms Theory.PiDigits.MachinQuotientCarry.nextCoarseQuotient_lt
#print axioms Theory.PiDigits.MachinQuotientCarry.ten_mul_eq_fullCarry_add_nextNumerator
#print axioms Theory.PiDigits.MachinQuotientCarry.nextNumerator_lt
#print axioms Theory.PiDigits.MachinQuotientCarry.decimalCarry_eq_fullQuotient
#print axioms Theory.PiDigits.MachinQuotientCarry.nextNumerator_eq_fullRemainder
#print axioms Theory.PiDigits.MachinQuotientCarry.nextNumerator_mod_eq_nextFineRemainder
#print axioms Theory.PiDigits.MachinQuotientCarry.nextNumerator_div_eq_nextCoarseQuotient
#print axioms Theory.PiDigits.MachinQuotientCarry.decimalCarry_lt_ten
