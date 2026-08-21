import TheoryLib.PiQuantitativeBlockHitting.T91T91ThreeLocalGrowth
import TheoryLib.PiQuantitativeBlockHitting.T86T86NonselectedEndpointCongruence

/-!
# T92: three-local cross-product congruence

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module introduces the integer cross-product congruence interface needed
for local rational residues, and two scoped interfaces for positive-even
scaled BBP partial sums.  It does not assert transitivity, operation
compatibility, a residue transition, a hidden carry, a decimal digit, an SP1
resolution, or canonical V1.
-/

namespace Theory.PiDigits.T92ThreeLocalCongruence

open T91ThreeLocalGrowth
open T77SelectedPadicDefectShell T78SelectedPadicDefectCongruence
  T86NonselectedEndpointCongruence T89SelectedDepthScaledIntegrality
  T90ScaledCarryInterface

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Two reduced rationals are three-locally congruent at level `n` when
`3^n` divides their numerator-denominator cross-difference.  At level zero
the modulus is one, so the relation is deliberately universal. -/
def ThreeLocalCongruent (n : ℕ) (p q : ℚ) : Prop :=
  ((3 : ℕ) ^ n : ℤ) ∣ p.num * q.den - q.num * p.den

/-- Reflexivity of the cross-product congruence. -/
theorem threeLocalCongruent_refl (n : ℕ) (q : ℚ) :
    ThreeLocalCongruent n q q := by
  unfold ThreeLocalCongruent
  simp

/-- Symmetry of the cross-product congruence. -/
theorem threeLocalCongruent_symm {n : ℕ} {p q : ℚ}
    (h : ThreeLocalCongruent n p q) : ThreeLocalCongruent n q p := by
  unfold ThreeLocalCongruent at h ⊢
  have hneg : q.num * p.den - p.num * q.den =
      -(p.num * q.den - q.num * p.den) := by ring
  rw [hneg]
  exact dvd_neg.mpr h

/-- A genuine denominator unit in `ZMod (3^n)`, also at the trivial modulus
`3^0 = 1`. -/
private def denUnit (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime d
    (((Nat.prime_three.coprime_iff_not_dvd).mpr hden).pow_left n).symm

private theorem coe_denUnit (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    ((denUnit n hden : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) =
      (d : ZMod (3 ^ n)) := by
  rw [denUnit, ZMod.coe_unitOfCoprime]

private theorem isUnit_coe_den (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    IsUnit (d : ZMod (3 ^ n)) := by
  rw [← coe_denUnit n hden]
  exact Units.isUnit _

/-- Equality of local residues is exactly cross-product congruence of their
reduced numerator-denominator presentations. -/
theorem threeLocalResidue_eq_iff (n : ℕ) (p q : ℚ)
    (hp : ¬ (3 ∣ p.den)) (hq : ¬ (3 ∣ q.den)) :
    threeLocalResidue n p hp = threeLocalResidue n q hq ↔
      ThreeLocalCongruent n p q := by
  constructor
  · intro heq
    show (3 ^ n : ℤ) ∣ p.num * q.den - q.num * p.den
    have step : (threeLocalResidue n p hp * (p.den : ZMod (3 ^ n))) *
          (q.den : ZMod (3 ^ n)) =
        (threeLocalResidue n q hq * (q.den : ZMod (3 ^ n))) *
          (p.den : ZMod (3 ^ n)) := by
      rw [heq]
      ring
    have key : (p.num : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)) =
        (q.num : ZMod (3 ^ n)) * (p.den : ZMod (3 ^ n)) := by
      rw [← threeLocalResidue_mul_den n p hp,
        ← threeLocalResidue_mul_den n q hq]
      exact step
    have h0 : ((p.num * q.den - q.num * p.den : ℤ) : ZMod (3 ^ n)) = 0 := by
      push_cast
      exact sub_eq_zero.mpr key
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
  · intro hdvd
    refine (isUnit_coe_den n hq).mul_right_injective ?_
    refine (isUnit_coe_den n hp).mul_right_injective ?_
    have key : (p.num : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)) =
        (q.num : ZMod (3 ^ n)) * (p.den : ZMod (3 ^ n)) := by
      have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (q.num * p.den)
        (p.num * q.den) (3 ^ n)).2 hdvd
      push_cast at h
      exact h.symm
    calc (p.den : ZMod (3 ^ n)) * ((q.den : ZMod (3 ^ n)) *
            threeLocalResidue n p hp) =
          (threeLocalResidue n p hp * (p.den : ZMod (3 ^ n))) *
            (q.den : ZMod (3 ^ n)) := by ring
      _ = (p.num : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)) := by
          rw [threeLocalResidue_mul_den n p hp]
      _ = (q.num : ZMod (3 ^ n)) * (p.den : ZMod (3 ^ n)) := key
      _ = (threeLocalResidue n q hq * (q.den : ZMod (3 ^ n))) *
            (p.den : ZMod (3 ^ n)) := by
          rw [threeLocalResidue_mul_den n q hq]
      _ = (p.den : ZMod (3 ^ n)) * ((q.den : ZMod (3 ^ n)) *
            threeLocalResidue n q hq) := by ring

/-- The even scaled BBP partial sum is three-adically integral, so its reduced
denominator is prime to three and admits a local residue representation. -/
theorem evenScaledPartial_den_not_dvd_three (t : ℕ) (ht : 1 ≤ t) :
    ¬ (3 ∣ (evenScaledPartial t).den) :=
  not_dvd_three_den_of_nonneg_val (scaled_bbpPartial_three_integral t ht)

/-- The local residue of a positive-even scaled BBP partial sum at precision
`3^n`.  This is a per-rational representation, not a carry digit. -/
def evenScaledResidue (n t : ℕ) (ht : 1 ≤ t) : ZMod (3 ^ n) :=
  threeLocalResidue n (evenScaledPartial t)
    (evenScaledPartial_den_not_dvd_three t ht)

/-- The local residue of an integer cast is its ordinary class in `ZMod`. -/
theorem threeLocalResidue_intCast (n : ℕ) (z : ℤ) :
    threeLocalResidue n (z : ℚ) (by simp) = (z : ZMod (3 ^ n)) := by
  have hden : ((z : ℚ)).den = 1 := by simp
  have hnum : ((z : ℚ)).num = z := by simp
  have hnotdvd : ¬ (3 ∣ 1) := by simp
  have key := threeLocalResidue_mul_den n (z : ℚ) hnotdvd
  rw [hden, Nat.cast_one, mul_one] at key
  exact key.trans (by rw [hnum])

/-- Multiplication by the reduced denominator recovers the reduced numerator
of the represented scaled partial sum. -/
theorem evenScaledResidue_mul_den (n t : ℕ) (ht : 1 ≤ t) :
    evenScaledResidue n t ht * ((evenScaledPartial t).den : ZMod (3 ^ n)) =
      ((evenScaledPartial t).num : ZMod (3 ^ n)) :=
  threeLocalResidue_mul_den n _ _

/-- Scaling a rational three-adic congruence by an explicit power of three
raises its precision by that exponent. -/
theorem ratCongruentThree_scale_pow_three {n k : ℕ} {x y : ℚ}
    (h : RatCongruentThree n x y) :
    RatCongruentThree (n + k) ((3 : ℚ) ^ k * x) ((3 : ℚ) ^ k * y) := by
  rcases h with rfl | hval
  · exact Or.inl rfl
  · by_cases hz : x - y = 0
    · have hxy : x = y := sub_eq_zero.mp hz
      subst hxy
      exact Or.inl rfl
    · right
      rw [show ((3 : ℚ) ^ k * x - (3 : ℚ) ^ k * y) =
          (3 : ℚ) ^ k * (x - y) by ring,
        padicValRat.mul (pow_ne_zero _ (by norm_num)) hz]
      have hpowcoe : ((3 : ℚ) ^ k) = (((3 ^ k : ℕ) : ℚ)) := by
        norm_cast
      rw [hpowcoe, padicValRat.of_nat, padicValNat.prime_pow (p := 3)]
      omega

/-- At precision `3^(2t+2)`, the next even scaled partial sum is rationally
congruent to the current one plus `3^(2t)`.  This is not a hidden-lift or
decimal-digit assertion. -/
theorem evenScaledPartial_step_congruent (t : ℕ) (ht : 1 ≤ t) :
    RatCongruentThree (2 * t + 2) (evenScaledPartial (t + 1))
      (evenScaledPartial t + (3 : ℚ) ^ (2 * t)) := by
  have htr := evenScaledPartial_transport t ht
  have hed := endpointDefect_congr_one_at_selectedDepth t ht
  have hscaled : RatCongruentThree (2 * t + 2)
      ((3 : ℚ) ^ (2 * t) * endpointDefect (selectedDepth (2 * t)))
      ((3 : ℚ) ^ (2 * t)) := by
    have h := ratCongruentThree_scale_pow_three (n := 2) (k := 2 * t) hed
    rw [show (2 + 2 * t) = 2 * t + 2 by omega] at h
    simpa using h
  rw [show evenScaledPartial (t + 1) = evenScaledPartial t +
      (3 : ℚ) ^ (2 * t) * endpointDefect (selectedDepth (2 * t)) by linarith]
  exact ratCongruentThree_add (ratCongruentThree_refl _ _) hscaled

/-- The index of the `j`th term in a moving tail beginning at the selected
even depth.  This is an index interface only, not a shadow approximation. -/
def selectedTailIndex (e : ℕ) (j : Fin (e + 1)) : ℕ :=
  selectedDepth (2 * e) + j

/-- Every index in the moving tail eventually exceeds every prescribed bound.
This records index escape only; it supplies neither circle coverage nor an
Archimedean approximation-error bound. -/
theorem selectedTailIndex_tends_to_infinity (N : ℕ) :
    ∃ E : ℕ, ∀ e : ℕ, E ≤ e → ∀ j : Fin (e + 1),
      N ≤ selectedTailIndex e j := by
  obtain ⟨E, hE⟩ := selectedDepth_even_tends_to_infinity N
  refine ⟨E, fun e he j => ?_⟩
  exact le_trans (hE e he) (Nat.le_add_right _ _)

end Theory.PiDigits.T92ThreeLocalCongruence

#print axioms Theory.PiDigits.T92ThreeLocalCongruence.ThreeLocalCongruent
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.threeLocalCongruent_refl
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.threeLocalCongruent_symm
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.threeLocalResidue_eq_iff
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.evenScaledPartial_den_not_dvd_three
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.evenScaledResidue
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.threeLocalResidue_intCast
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.evenScaledResidue_mul_den
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.ratCongruentThree_scale_pow_three
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.evenScaledPartial_step_congruent
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.selectedTailIndex
#print axioms Theory.PiDigits.T92ThreeLocalCongruence.selectedTailIndex_tends_to_infinity
