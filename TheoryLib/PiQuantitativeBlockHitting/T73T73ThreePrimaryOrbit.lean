import Mathlib.RingTheory.ZMod.UnitsCyclic
import TheoryLib.PiQuantitativeBlockHitting.T72T72ColoredRepunitReturn

/-!
# T73: the exact decimal orbit on powers of three

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The BBP three-primary calculation isolates powers of ten modulo `3^(e+2)`.
This module records the generic arithmetic fact needed there: ten has exact
multiplicative order `3^e`, and its first `3^e` powers are pairwise distinct.

These are local finite-orbit theorems. They do not control the other CRT
coordinates of a BBP denominator and prove no density, normality, or
every-finite-word statement for pi.
-/

namespace Theory.PiDigits.T73ThreePrimaryOrbit

/-- Ten, regarded as a unit modulo `3^(e+2)`. -/
def tenUnit (e : ℕ) : (ZMod (3 ^ (e + 2)))ˣ :=
  ZMod.unitOfCoprime 10 ((by norm_num : Nat.Coprime 10 3).pow_right _)

@[simp] theorem tenUnit_coe (e : ℕ) :
    ((tenUnit e : (ZMod (3 ^ (e + 2)))ˣ) : ZMod (3 ^ (e + 2))) = 10 := by
  simp [tenUnit]

/-- The exact period underlying the isolated three-primary BBP orbit. -/
theorem orderOf_tenUnit (e : ℕ) : orderOf (tenUnit e) = 3 ^ e := by
  have h := ZMod.orderOf_one_add_mul_prime_pow
    (p := 3) (by norm_num) 2 (by norm_num) (by norm_num)
    (1 : ℤ) (by norm_num) e
  have hcoe :
      orderOf (((tenUnit e : (ZMod (3 ^ (e + 2)))ˣ) :
        ZMod (3 ^ (e + 2)))) = 3 ^ e := by
    convert h using 1
    all_goals norm_num [tenUnit, add_comm]
  simpa only [orderOf_units] using hcoe

/-- Equality of two decimal powers modulo `3^(e+2)` is exactly equality of
their exponent classes modulo the period `3^e`. -/
theorem tenUnit_pow_eq_iff (e n m : ℕ) :
    tenUnit e ^ n = tenUnit e ^ m ↔ n % (3 ^ e) = m % (3 ^ e) := by
  rw [pow_inj_mod, orderOf_tenUnit]

/-- One complete period of decimal powers modulo `3^(e+2)` has no repeats. -/
theorem tenUnit_pow_injective_on_period (e : ℕ) :
    Function.Injective (fun i : Fin (3 ^ e) ↦ tenUnit e ^ i.val) := by
  intro i j hij
  have hmod := (tenUnit_pow_eq_iff e i.val j.val).mp hij
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
  exact Fin.ext hmod

/-- The integer quotient occurring after the fixed factor three is removed
from `10^n - 16`. -/
def residualTen (n : ℕ) : ℤ := ((10 : ℤ) ^ n - 16) / 3

/-- The quotient in `residualTen` is exact at every exponent. -/
theorem three_mul_residualTen (n : ℕ) :
    3 * residualTen n = (10 : ℤ) ^ n - 16 := by
  have hpow : (3 : ℤ) ∣ (10 : ℤ) ^ n - 1 := by
    have hnine : (9 : ℤ) ∣ (10 : ℤ) ^ n - 1 := by
      simpa using sub_dvd_pow_sub_pow (10 : ℤ) 1 n
    exact (by norm_num : (3 : ℤ) ∣ 9).trans hnine
  have hdiv : (3 : ℤ) ∣ (10 : ℤ) ^ n - 16 := by
    convert hpow.sub (by norm_num : (3 : ℤ) ∣ 15) using 1
    all_goals ring
  rw [residualTen, mul_comm]
  exact Int.ediv_mul_cancel hdiv

/-- Every residual quotient lies in the residue-one coset modulo three. -/
theorem residualTen_mod_three (n : ℕ) :
    (residualTen n : ZMod 3) = 1 := by
  have hnine : (9 : ℤ) ∣ (10 : ℤ) ^ n - 1 := by
    simpa using sub_dvd_pow_sub_pow (10 : ℤ) 1 n
  obtain ⟨c, hc⟩ := hnine
  have hquot : residualTen n - 1 = 3 * (c - 2) := by
    have hthree := three_mul_residualTen n
    omega
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub
    (residualTen n) 1 3).mpr
  refine ⟨-(c - 2), ?_⟩
  calc
    1 - residualTen n = -(residualTen n - 1) := by ring
    _ = -(3 * (c - 2)) := by rw [hquot]
    _ = ((3 : ℕ) : ℤ) * -(c - 2) := by ring

/-- The residual quotient modulo its reduced denominator. -/
def residualClass (e n : ℕ) : ZMod (3 ^ (e + 1)) := residualTen n

/-- The first `3^e` residual quotients modulo `3^(e+1)` have no repeats.
This is the exact complete-period assertion for the isolated coordinate; it
does not assert anything about its synchronized CRT complement. -/
theorem residualClass_injective_on_period (e : ℕ) :
    Function.Injective (fun i : Fin (3 ^ e) ↦ residualClass e i.val) := by
  intro i j hij
  have hdiv : ((3 ^ (e + 1) : ℕ) : ℤ) ∣ residualTen j.val - residualTen i.val := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      (residualTen i.val) (residualTen j.val) (3 ^ (e + 1))).mp hij
  obtain ⟨c, hc⟩ := hdiv
  have hpowDiv : ((3 ^ (e + 2) : ℕ) : ℤ) ∣
      (10 : ℤ) ^ j.val - (10 : ℤ) ^ i.val := by
    refine ⟨c, ?_⟩
    calc
      (10 : ℤ) ^ j.val - (10 : ℤ) ^ i.val =
          ((10 : ℤ) ^ j.val - 16) - ((10 : ℤ) ^ i.val - 16) := by ring
      _ = 3 * residualTen j.val - 3 * residualTen i.val := by
        rw [three_mul_residualTen, three_mul_residualTen]
      _ = 3 * ((3 ^ (e + 1) : ℕ) : ℤ) * c := by
        calc
          3 * residualTen j.val - 3 * residualTen i.val =
              3 * (residualTen j.val - residualTen i.val) := by ring
          _ = 3 * (((3 ^ (e + 1) : ℕ) : ℤ) * c) := by rw [hc]
          _ = 3 * ((3 ^ (e + 1) : ℕ) : ℤ) * c := by ring
      _ = ((3 ^ (e + 2) : ℕ) : ℤ) * c := by push_cast; ring
  have hpowCast :
      ((10 : ℤ) ^ i.val : ZMod (3 ^ (e + 2))) =
        ((10 : ℤ) ^ j.val : ZMod (3 ^ (e + 2))) := by
    simpa only [Int.cast_pow, Int.cast_ofNat] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub
        ((10 : ℤ) ^ i.val) ((10 : ℤ) ^ j.val) (3 ^ (e + 2))).mpr hpowDiv
  have hunit : tenUnit e ^ i.val = tenUnit e ^ j.val := by
    apply Units.ext
    simpa [tenUnit] using hpowCast
  exact tenUnit_pow_injective_on_period e hunit

/-- The complete period contains exactly `3^e` distinct residual classes. -/
theorem residualClass_range_ncard (e : ℕ) :
    (Set.range (fun i : Fin (3 ^ e) ↦ residualClass e i.val)).ncard = 3 ^ e := by
  rw [Set.ncard_range_of_injective (residualClass_injective_on_period e)]
  simp

/-- Reduction of every point in the complete period to modulus three is one.
Together with the distinct-point count, this records the two ingredients of
the isolated coset orbit without claiming anything about other CRT factors.
-/
theorem residualClass_cast_three (e : ℕ) (i : Fin (3 ^ e)) :
    ZMod.castHom (show 3 ∣ 3 ^ (e + 1) by exact dvd_pow_self 3 (by omega))
      (ZMod 3) (residualClass e i.val) = 1 := by
  simpa [residualClass, ZMod.castHom_apply] using residualTen_mod_three i.val

end Theory.PiDigits.T73ThreePrimaryOrbit

#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.tenUnit_coe
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.orderOf_tenUnit
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.tenUnit_pow_eq_iff
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.tenUnit_pow_injective_on_period
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.three_mul_residualTen
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.residualClass_injective_on_period
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.residualTen_mod_three
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.residualClass_range_ncard
#print axioms Theory.PiDigits.T73ThreePrimaryOrbit.residualClass_cast_three
