import TheoryLib.PiQuantitativeBlockHitting.T95T95ThreeLocalCoherence
import TheoryLib.PiQuantitativeBlockHitting.T96T96SelectedRationalCauchy

/-!
# T97: Cauchy cast-down compatibility of even scaled residues

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Reducing the positive-even scaled BBP partial residue at precision `3^(2*t)`
to precision `3^(2*s)` for `s ≤ t` recovers the residue of the `s`th partial
sum.  This is finite inverse-system compatibility only; it asserts no padic
completion, carry, decimal digit, SP1 resolution, or canonical V1.
-/

namespace Theory.PiDigits.T97SelectedResidueCauchy

open T89SelectedDepthScaledIntegrality T90ScaledCarryInterface
  T91ThreeLocalGrowth T92ThreeLocalCongruence T94SelectedResidueTransition
  T95ThreeLocalCoherence T96SelectedRationalCauchy

/-- Cast-down from the larger selected precision agrees with the residue of
the smaller selected partial sum. -/
theorem evenScaledResidue_cast_down_cauchy (s t : ℕ) (hs : 1 ≤ s)
    (hst : s ≤ t) :
    ZMod.castHom (pow_dvd_pow 3 (by omega : 2 * s ≤ 2 * t))
        (ZMod (3 ^ (2 * s))) (evenScaledResidue (2 * t) t (by omega)) =
      evenScaledResidue (2 * s) s hs := by
  simp only [evenScaledResidue]
  calc
    ZMod.castHom (pow_dvd_pow 3 (by omega : 2 * s ≤ 2 * t))
          (ZMod (3 ^ (2 * s)))
          (threeLocalResidue (2 * t) (evenScaledPartial t)
            (evenScaledPartial_den_not_dvd_three t (by omega))) =
        threeLocalResidue (2 * s) (evenScaledPartial t)
          (evenScaledPartial_den_not_dvd_three t (by omega)) :=
      threeLocalResidue_cast_down (2 * s) (2 * t) (by omega)
        (evenScaledPartial t) (evenScaledPartial_den_not_dvd_three t (by omega))
    _ = threeLocalResidue (2 * s) (evenScaledPartial s)
          (evenScaledPartial_den_not_dvd_three s hs) :=
      threeLocalResidue_eq_of_ratCongruentThree (2 * s) (evenScaledPartial t)
        (evenScaledPartial s) (scaled_bbpPartial_three_integral t (by omega))
        (scaled_bbpPartial_three_integral s hs)
        (evenScaledPartial_cauchy s t hs hst)

end Theory.PiDigits.T97SelectedResidueCauchy

#print axioms Theory.PiDigits.T97SelectedResidueCauchy.evenScaledResidue_cast_down_cauchy
