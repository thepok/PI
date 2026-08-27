import TheoryLib.PiQuantitativeBlockHitting.T73T73ThreePrimaryOrbit

/-!
Independent type-surface, boundary, and converse checks for T73.

This file deliberately re-derives the unrestricted collision criterion for
the residual quotient rather than merely calling the period-injectivity
theorem.  It does not mention the BBP depth epochs, the other CRT coordinates,
or decimal digits of pi.
-/

namespace UltraPiT73IndependentChecks

open Theory.PiDigits.T73ThreePrimaryOrbit

/-- Pin the exact unit order, including the exponent shift in the modulus. -/
example (e : ℕ) : orderOf (tenUnit e) = 3 ^ e := by
  exact orderOf_tenUnit e

/-- Pin the unrestricted exponent collision criterion for the unit orbit. -/
example (e n m : ℕ) :
    tenUnit e ^ n = tenUnit e ^ m ↔ n % (3 ^ e) = m % (3 ^ e) := by
  exact tenUnit_pow_eq_iff e n m

/-- Equality of high-modulus powers implies equality of the residual
quotients one factor of three lower.  This is the converse direction not
used by T73's injectivity proof. -/
theorem residualClass_eq_of_tenUnit_pow_eq (e n m : ℕ)
    (hunit : tenUnit e ^ n = tenUnit e ^ m) :
    residualClass e n = residualClass e m := by
  have hpowCast :
      ((10 : ℤ) ^ n : ZMod (3 ^ (e + 2))) =
        ((10 : ℤ) ^ m : ZMod (3 ^ (e + 2))) := by
    have hval := congrArg Units.val hunit
    simpa [tenUnit] using hval
  have hpowDiv : ((3 ^ (e + 2) : ℕ) : ℤ) ∣
      (10 : ℤ) ^ m - (10 : ℤ) ^ n := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((10 : ℤ) ^ n) ((10 : ℤ) ^ m) (3 ^ (e + 2))).mp
        (by simpa only [Int.cast_pow, Int.cast_ofNat] using hpowCast)
  obtain ⟨c, hc⟩ := hpowDiv
  have hresDiv : ((3 ^ (e + 1) : ℕ) : ℤ) ∣ residualTen m - residualTen n := by
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
    calc
      3 * (residualTen m - residualTen n) =
          ((10 : ℤ) ^ m - 16) - ((10 : ℤ) ^ n - 16) := by
            rw [mul_sub, three_mul_residualTen, three_mul_residualTen]
      _ = (10 : ℤ) ^ m - (10 : ℤ) ^ n := by ring
      _ = ((3 ^ (e + 2) : ℕ) : ℤ) * c := hc
      _ = 3 * (((3 ^ (e + 1) : ℕ) : ℤ) * c) := by
        push_cast
        ring
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub
    (residualTen n) (residualTen m) (3 ^ (e + 1))).mpr hresDiv

/-- Independent unrestricted collision criterion for the residual orbit.
It pins both the exact period and the absence of any hidden shorter period. -/
theorem residualClass_eq_iff_exponent_mod (e n m : ℕ) :
    residualClass e n = residualClass e m ↔
      n % (3 ^ e) = m % (3 ^ e) := by
  constructor
  · intro hij
    have hdiv : ((3 ^ (e + 1) : ℕ) : ℤ) ∣
        residualTen m - residualTen n := by
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub
        (residualTen n) (residualTen m) (3 ^ (e + 1))).mp hij
    obtain ⟨c, hc⟩ := hdiv
    have hpowDiv : ((3 ^ (e + 2) : ℕ) : ℤ) ∣
        (10 : ℤ) ^ m - (10 : ℤ) ^ n := by
      refine ⟨c, ?_⟩
      calc
        (10 : ℤ) ^ m - (10 : ℤ) ^ n =
            ((10 : ℤ) ^ m - 16) - ((10 : ℤ) ^ n - 16) := by ring
        _ = 3 * residualTen m - 3 * residualTen n := by
          rw [three_mul_residualTen, three_mul_residualTen]
        _ = 3 * (((3 ^ (e + 1) : ℕ) : ℤ) * c) := by
          rw [← mul_sub, hc]
        _ = ((3 ^ (e + 2) : ℕ) : ℤ) * c := by
          push_cast
          ring
    have hpowCast :
        ((10 : ℤ) ^ n : ZMod (3 ^ (e + 2))) =
          ((10 : ℤ) ^ m : ZMod (3 ^ (e + 2))) := by
      simpa only [Int.cast_pow, Int.cast_ofNat] using
        (ZMod.intCast_eq_intCast_iff_dvd_sub
          ((10 : ℤ) ^ n) ((10 : ℤ) ^ m) (3 ^ (e + 2))).mpr hpowDiv
    have hunit : tenUnit e ^ n = tenUnit e ^ m := by
      apply Units.ext
      simpa [tenUnit] using hpowCast
    exact (tenUnit_pow_eq_iff e n m).mp hunit
  · intro hmod
    exact residualClass_eq_of_tenUnit_pow_eq e n m
      ((tenUnit_pow_eq_iff e n m).mpr hmod)

/-- A period shift really returns the residual class. -/
example (e n : ℕ) : residualClass e (n + 3 ^ e) = residualClass e n := by
  rw [residualClass_eq_iff_exponent_mod]
  simp

/-- The two T73 range statements jointly pin the size and the residue-one
coset containment; they do not mention any synchronized CRT complement. -/
example (e : ℕ) :
    (Set.range (fun i : Fin (3 ^ e) ↦ residualClass e i.val)).ncard = 3 ^ e ∧
      ∀ x ∈ Set.range (fun i : Fin (3 ^ e) ↦ residualClass e i.val),
        ZMod.castHom (show 3 ∣ 3 ^ (e + 1) by exact dvd_pow_self 3 (by omega))
          (ZMod 3) x = 1 := by
  refine ⟨residualClass_range_ncard e, ?_⟩
  rintro x ⟨i, rfl⟩
  exact residualClass_cast_three e i

/-- The ambient residue-one coset used by the informal report, expressed by
the canonical representative modulo three. -/
def residueOneCoset (e : ℕ) : Set (ZMod (3 ^ (e + 1))) :=
  {x | x.val % 3 = 1}

/-- Independent cardinal-free parametrization of the residue-one coset.
This checks the elementary finite-fiber fact needed to turn T73's count and
containment into actual coset exhaustion. -/
theorem residueOneCoset_eq_affine_range (e : ℕ) :
    residueOneCoset e =
      Set.range (fun j : Fin (3 ^ e) ↦
        ((1 + 3 * j.val : ℕ) : ZMod (3 ^ (e + 1)))) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxmod : x.val % 3 = 1 := hx
    have hxdecomp : x.val = 3 * (x.val / 3) + 1 := by omega
    have hxlt : x.val < 3 * 3 ^ e := by
      calc
        x.val < 3 ^ (e + 1) := x.val_lt
        _ = 3 * 3 ^ e := by ring
    have hjlt : x.val / 3 < 3 ^ e := by
      omega
    let j : Fin (3 ^ e) := ⟨x.val / 3, hjlt⟩
    refine ⟨j, ?_⟩
    apply ZMod.val_injective (3 ^ (e + 1))
    rw [ZMod.val_natCast_of_lt]
    · dsimp [j]
      omega
    · calc
        1 + 3 * (x.val / 3) = x.val := by omega
        _ < 3 ^ (e + 1) := x.val_lt
  · rintro x ⟨j, rfl⟩
    rw [residueOneCoset]
    change (((1 + 3 * j.val : ℕ) : ZMod (3 ^ (e + 1))).val % 3 = 1)
    rw [ZMod.val_natCast_of_lt]
    · omega
    · rw [show 3 ^ (e + 1) = 3 * 3 ^ e by ring]
      omega

/-- T73's complete-period residual range is exactly the residue-one coset.
This theorem is an independent downstream consequence, not a declaration in
the audited T73 source. -/
theorem residualClass_range_eq_residueOneCoset (e : ℕ) :
    Set.range (fun i : Fin (3 ^ e) ↦ residualClass e i.val) =
      residueOneCoset e := by
  have hcoset_cast (x : ZMod (3 ^ (e + 1))) :
      x ∈ residueOneCoset e ↔
        ZMod.castHom
          (show 3 ∣ 3 ^ (e + 1) by exact dvd_pow_self 3 (by omega))
          (ZMod 3) x = 1 := by
    rw [residueOneCoset]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    change x.val % 3 = 1 ↔ (x.val : ZMod 3) = (1 : ZMod 3)
    constructor
    · intro hx
      apply ZMod.val_injective 3
      change x.val % 3 = 1
      exact hx
    · intro hx
      have hv := congrArg ZMod.val hx
      change x.val % 3 = 1 at hv
      exact hv
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · rintro x ⟨i, rfl⟩
    rw [hcoset_cast]
    exact residualClass_cast_three e i
  · have hfinj : Function.Injective (fun j : Fin (3 ^ e) ↦
        ((1 + 3 * j.val : ℕ) : ZMod (3 ^ (e + 1)))) := by
      intro i j hij
      have hv := congrArg ZMod.val hij
      rw [ZMod.val_natCast_of_lt, ZMod.val_natCast_of_lt] at hv
      · exact Fin.ext (by omega)
      · rw [show 3 ^ (e + 1) = 3 * 3 ^ e by ring]
        omega
      · rw [show 3 ^ (e + 1) = 3 * 3 ^ e by ring]
        omega
    rw [residueOneCoset_eq_affine_range,
      Set.ncard_range_of_injective hfinj,
      residualClass_range_ncard]
    simp

/-- Boundary audit: at `e = 0`, the unit orbit has the singleton period. -/
example : orderOf (tenUnit 0) = 1 := by
  simpa using orderOf_tenUnit 0

/-- Boundary audit: the quotient is exact even at exponent zero. -/
example : residualTen 0 = -5 := by
  norm_num [residualTen]

/-- Boundary audit: the singleton residual orbit is the residue-one class. -/
example : residualClass 0 0 = (1 : ZMod 3) := by
  simpa [residualClass] using residualTen_mod_three 0

/-- Small nontrivial audit: in orbit order, the first three residual classes
modulo nine are exactly `4`, `7`, and `1`. -/
example :
    residualClass 1 0 = (4 : ZMod 9) ∧
      residualClass 1 1 = (7 : ZMod 9) ∧
        residualClass 1 2 = (1 : ZMod 9) := by
  decide

end UltraPiT73IndependentChecks

#print axioms UltraPiT73IndependentChecks.residualClass_eq_of_tenUnit_pow_eq
#print axioms UltraPiT73IndependentChecks.residualClass_eq_iff_exponent_mod
#print axioms UltraPiT73IndependentChecks.residueOneCoset_eq_affine_range
#print axioms UltraPiT73IndependentChecks.residualClass_range_eq_residueOneCoset
