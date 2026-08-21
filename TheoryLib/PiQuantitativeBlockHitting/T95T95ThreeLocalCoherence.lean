import TheoryLib.PiQuantitativeBlockHitting.T94T94SelectedResidueTransition

/-!
# T95: cast-down compatibility of three-local residues

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module proves that canonical reduction between powers of three commutes
with T91's local residue representation.  It is a finite residue projection
statement only; it does not assert a carry, decimal digit, SP1 resolution, or
canonical V1.
-/

namespace Theory.PiDigits.T95ThreeLocalCoherence

/-- Reducing a three-local residue from precision `m` to precision `n ≤ m`
gives the residue of the same rational at precision `n`. -/
theorem threeLocalResidue_cast_down (n m : ℕ) (hnm : n ≤ m) (q : ℚ)
    (hden : ¬ (3 ∣ q.den)) :
    ZMod.castHom (pow_dvd_pow 3 hnm) (ZMod (3 ^ n))
        (T91ThreeLocalGrowth.threeLocalResidue m q hden) =
      T91ThreeLocalGrowth.threeLocalResidue n q hden := by
  have hunit : IsUnit ((q.den : ℕ) : ZMod (3 ^ n)) :=
    (ZMod.isUnit_iff_coprime q.den (3 ^ n)).2
      (Nat.prime_three.coprime_pow_of_not_dvd hden)
  have fint : ∀ k : ℤ,
      ZMod.castHom (pow_dvd_pow 3 hnm) (ZMod (3 ^ n)) ((k : ZMod (3 ^ m))) =
        (k : ZMod (3 ^ n)) := fun k => by
    rw [ZMod.castHom_apply, ZMod.cast_intCast (pow_dvd_pow 3 hnm) k]
  have fnat : ∀ k : ℕ,
      ZMod.castHom (pow_dvd_pow 3 hnm) (ZMod (3 ^ n)) ((k : ZMod (3 ^ m))) =
        (k : ZMod (3 ^ n)) := fun k => by
    rw [ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow 3 hnm) k]
  have hstep : ZMod.castHom (pow_dvd_pow 3 hnm) (ZMod (3 ^ n))
        (T91ThreeLocalGrowth.threeLocalResidue m q hden *
          ((q.den : ℕ) : ZMod (3 ^ m))) =
      ZMod.castHom (pow_dvd_pow 3 hnm) (ZMod (3 ^ n))
        (T91ThreeLocalGrowth.threeLocalResidue m q hden) *
        ((q.den : ℕ) : ZMod (3 ^ n)) := by
    rw [map_mul, fnat]
  have hmul : ZMod.castHom (pow_dvd_pow 3 hnm) (ZMod (3 ^ n))
        (T91ThreeLocalGrowth.threeLocalResidue m q hden) *
        ((q.den : ℕ) : ZMod (3 ^ n)) =
      ((q.num : ℤ) : ZMod (3 ^ n)) := by
    rw [← hstep, T91ThreeLocalGrowth.threeLocalResidue_mul_den m q hden]
    exact fint _
  exact hunit.mul_left_injective
    (hmul.trans (T91ThreeLocalGrowth.threeLocalResidue_mul_den n q hden).symm)

/-- Projecting the next positive-even scaled residue by two precision digits
recovers the current residue.  This is an inverse-system identity only. -/
theorem evenScaledResidue_coherent (t : ℕ) (ht : 1 ≤ t) :
    ZMod.castHom (pow_dvd_pow 3 (by omega : 2 * t ≤ 2 * t + 2))
        (ZMod (3 ^ (2 * t)))
        (T92ThreeLocalCongruence.evenScaledResidue
          (2 * t + 2) (t + 1) (by omega)) =
      T92ThreeLocalCongruence.evenScaledResidue (2 * t) t ht := by
  open T90ScaledCarryInterface T92ThreeLocalCongruence
    T94SelectedResidueTransition in
    let castDown := ZMod.castHom
      (pow_dvd_pow 3 (by omega : 2 * t ≤ 2 * t + 2))
      (ZMod (3 ^ (2 * t)))
    have hcoh : castDown (evenScaledResidue (2 * t + 2) t ht) =
        evenScaledResidue (2 * t) t ht := by
      simpa only [evenScaledResidue] using
        threeLocalResidue_cast_down (2 * t) (2 * t + 2) (by omega)
          (evenScaledPartial t) (evenScaledPartial_den_not_dvd_three t ht)
    have hzero : castDown
        ((3 : ZMod (3 ^ (2 * t + 2))) ^ (2 * t)) = 0 := by
      have hthree : castDown (3 : ZMod (3 ^ (2 * t + 2))) =
          (3 : ZMod (3 ^ (2 * t))) := by
        dsimp [castDown]
        simpa using (ZMod.cast_natCast
          (pow_dvd_pow 3 (by omega : 2 * t ≤ 2 * t + 2)) 3)
      rw [map_pow, hthree]
      have hpow : (3 : ZMod (3 ^ (2 * t))) ^ (2 * t) =
          ((3 ^ (2 * t) : ℕ) : ZMod (3 ^ (2 * t))) := by norm_cast
      rw [hpow, ZMod.natCast_eq_zero_iff]
    have hstep := evenScaledResidue_step t ht
    change castDown (evenScaledResidue (2 * t + 2) (t + 1) (by omega)) = _
    rw [hstep, map_add, hcoh, hzero, add_zero]

end Theory.PiDigits.T95ThreeLocalCoherence

#print axioms Theory.PiDigits.T95ThreeLocalCoherence.threeLocalResidue_cast_down
#print axioms Theory.PiDigits.T95ThreeLocalCoherence.evenScaledResidue_coherent
