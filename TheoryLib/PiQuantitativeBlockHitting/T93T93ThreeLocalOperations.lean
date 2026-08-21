import TheoryLib.PiQuantitativeBlockHitting.T92T92ThreeLocalCongruence
import TheoryLib.PiQuantitativeBlockHitting.T78T78SelectedPadicDefectCongruence

/-!
# T93: rational congruence to three-local cross products

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module bridges the rational three-adic congruence used by the selected
BBP track to T92's integer cross-product congruence, and records the exact
addition and multiplication rules for T91's per-rational residue
representation.  It does not assert a residue transition, a hidden carry, a
decimal digit, an SP1 resolution, or canonical V1.
-/

namespace Theory.PiDigits.T93ThreeLocalOperations

open T78SelectedPadicDefectCongruence T91ThreeLocalGrowth
  T92ThreeLocalCongruence

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Rational three-adic congruence between three-integral rationals implies
the canonical T92 cross-product divisibility at the same precision. -/
theorem threeLocalCongruent_of_ratCongruentThree (n : ℕ) (p q : ℚ)
    (hp : 0 ≤ padicValRat 3 p) (hq : 0 ≤ padicValRat 3 q)
    (h : RatCongruentThree n p q) : ThreeLocalCongruent n p q := by
  have hpden := not_dvd_three_den_of_nonneg_val hp
  have hqden := not_dvd_three_den_of_nonneg_val hq
  unfold RatCongruentThree at h
  rcases h with rfl | hval
  · simp only [ThreeLocalCongruent, sub_self]
    exact dvd_zero _
  · unfold ThreeLocalCongruent
    set c : ℤ := p.num * q.den - q.num * p.den with hc
    have key : (p - q) * ((p.den : ℚ) * (q.den : ℚ)) =
        ((p.num * q.den - q.num * p.den : ℤ) : ℚ) := by
      have step : (p * (p.den : ℚ)) * (q.den : ℚ) -
          (q * (q.den : ℚ)) * (p.den : ℚ) =
          (p.num : ℚ) * (q.den : ℚ) - (q.num : ℚ) * (p.den : ℚ) := by
        rw [Rat.mul_den_eq_num p, Rat.mul_den_eq_num q]
      calc (p - q) * ((p.den : ℚ) * (q.den : ℚ)) =
          (p * (p.den : ℚ)) * (q.den : ℚ) -
            (q * (q.den : ℚ)) * (p.den : ℚ) := by ring
        _ = (p.num : ℚ) * (q.den : ℚ) - (q.num : ℚ) * (p.den : ℚ) := step
        _ = ((p.num * q.den - q.num * p.den : ℤ) : ℚ) := by
          push_cast
          ring
    have hrep : p - q = (c : ℚ) / ((p.den * q.den : ℕ) : ℚ) := by
      rw [eq_div_iff (by positivity)]
      push_cast
      exact key
    by_cases hcz : c = 0
    · rw [hcz]
      exact dvd_zero _
    · have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hcz
      have hv : (n : ℤ) ≤
          padicValRat 3 ((c : ℚ) / ((p.den * q.den : ℕ) : ℚ)) := by
        rwa [← hrep]
      rw [padicValRat.div hcq (by positivity), padicValRat.of_int] at hv
      have hDval : padicValNat 3 (p.den * q.den) = 0 := by
        refine padicValNat.eq_zero_of_not_dvd ?_
        intro hdvd
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with hd | hd
        · exact hpden hd
        · exact hqden hd
      have hDrat : padicValRat 3 (((p.den * q.den : ℕ) : ℚ)) = 0 := by
        rw [padicValRat.of_nat]
        exact_mod_cast hDval
      rw [hDrat, sub_zero] at hv
      exact (padicValInt_dvd_iff n c).2 (Or.inr (by omega))

/-- A genuine denominator unit in `ZMod (3^n)`, including the trivial
modulus `3^0 = 1`. -/
private def residueDenUnit (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime d
    (((Nat.prime_three.coprime_iff_not_dvd).mpr hden).pow_left n).symm

private theorem coe_residueDenUnit (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    ((residueDenUnit n hden : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) =
      (d : ZMod (3 ^ n)) := by
  rw [residueDenUnit, ZMod.coe_unitOfCoprime]

private theorem isUnit_coe_den (n : ℕ) {d : ℕ} (hden : ¬ (3 ∣ d)) :
    IsUnit (d : ZMod (3 ^ n)) := by
  rw [← coe_residueDenUnit n hden]
  exact Units.isUnit _

/-- The T91 three-local residue of a product equals the product of the
factor residues when all involved reduced denominators are three-units.
This is a representation identity, not a hidden-carry assertion. -/
theorem threeLocalResidue_mul (n : ℕ) (p q : ℚ)
    (hp : ¬ (3 ∣ p.den)) (hq : ¬ (3 ∣ q.den))
    (hpq : ¬ (3 ∣ (p * q).den)) :
    threeLocalResidue n (p * q) hpq =
      threeLocalResidue n p hp * threeLocalResidue n q hq := by
  have hA := threeLocalResidue_mul_den n (p * q) hpq
  have hp1 := threeLocalResidue_mul_den n p hp
  have hq1 := threeLocalResidue_mul_den n q hq
  have hC : ((p * q).num : ZMod (3 ^ n)) * (p.den : ZMod (3 ^ n)) *
        (q.den : ZMod (3 ^ n)) =
      ((p.num : ℤ) : ZMod (3 ^ n)) * ((q.num : ℤ) : ZMod (3 ^ n)) *
        ((p * q).den : ZMod (3 ^ n)) := by
    have h := congrArg (fun z : ℤ => (z : ZMod (3 ^ n))) (Rat.mul_num_den' p q)
    push_cast at h ⊢
    exact h
  have hunit : IsUnit (((p * q).den : ZMod (3 ^ n)) *
      ((p.den : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)))) :=
    (isUnit_coe_den n hpq).mul ((isUnit_coe_den n hp).mul (isUnit_coe_den n hq))
  refine hunit.mul_left_injective ?_
  calc threeLocalResidue n (p * q) hpq *
        (((p * q).den : ZMod (3 ^ n)) *
          ((p.den : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)))) =
      (threeLocalResidue n (p * q) hpq * ((p * q).den : ZMod (3 ^ n))) *
        ((p.den : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n))) := by ring
    _ = ((p * q).num : ZMod (3 ^ n)) * ((p.den : ZMod (3 ^ n)) *
          (q.den : ZMod (3 ^ n))) := by rw [hA]
    _ = ((p.num : ℤ) : ZMod (3 ^ n)) * ((q.num : ℤ) : ZMod (3 ^ n)) *
          ((p * q).den : ZMod (3 ^ n)) := by
          linear_combination hC
    _ = (threeLocalResidue n p hp * (p.den : ZMod (3 ^ n))) *
          (threeLocalResidue n q hq * (q.den : ZMod (3 ^ n))) *
          ((p * q).den : ZMod (3 ^ n)) := by rw [← hp1, ← hq1]
    _ = threeLocalResidue n p hp * threeLocalResidue n q hq *
          (((p * q).den : ZMod (3 ^ n)) *
            ((p.den : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)))) := by ring

private theorem isUnit_coe_of_not_dvd_three (n : ℕ) {d : ℕ} (hd : ¬ (3 ∣ d)) :
    IsUnit (d : ZMod (3 ^ n)) :=
  (ZMod.isUnit_iff_coprime d (3 ^ n)).2
    (Nat.prime_three.coprime_pow_of_not_dvd hd)

private theorem add_mul_den_prod (p q : ℚ) :
    (p + q) * ((p.den : ℚ) * (q.den : ℚ)) =
      ((p.num * q.den + q.num * p.den : ℤ) : ℚ) := by
  have hp := Rat.mul_den_eq_num p
  have hq := Rat.mul_den_eq_num q
  calc (p + q) * ((p.den : ℚ) * (q.den : ℚ)) =
      (p * (p.den : ℚ)) * (q.den : ℚ) +
        (q * (q.den : ℚ)) * (p.den : ℚ) := by ring
    _ = (p.num : ℚ) * (q.den : ℚ) + (q.num : ℚ) * (p.den : ℚ) := by rw [hp, hq]
    _ = ((p.num * q.den + q.num * p.den : ℤ) : ℚ) := by push_cast; ring

private theorem add_num_cross_mul_den (p q : ℚ) :
    (p + q).num * ((p.den * q.den : ℕ) : ℤ) =
      (p.num * q.den + q.num * p.den) * ((p + q).den : ℕ) := by
  have hsum := Rat.mul_den_eq_num (p + q)
  have key : ((p + q).num : ℚ) * ((p.den : ℚ) * (q.den : ℚ)) =
      ((p.num * q.den + q.num * p.den : ℤ) : ℚ) * ((p + q).den : ℚ) := by
    rw [← hsum, ← add_mul_den_prod p q]
    ring
  exact_mod_cast key

/-- The T91 three-local residue of a sum equals the sum of factor residues
when all involved reduced denominators are three-units.  This is a
representation identity, not a hidden-carry assertion. -/
theorem threeLocalResidue_add (n : ℕ) (p q : ℚ)
    (hp : ¬ (3 ∣ p.den)) (hq : ¬ (3 ∣ q.den))
    (hpq : ¬ (3 ∣ (p + q).den)) :
    threeLocalResidue n (p + q) hpq =
      threeLocalResidue n p hp + threeLocalResidue n q hq := by
  classical
  have hdenprod : ((p.den * q.den : ℕ) : ZMod (3 ^ n)) =
      (p.den : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)) := by push_cast; ring
  have hcross : ((p + q).num : ZMod (3 ^ n)) *
      ((p.den * q.den : ℕ) : ZMod (3 ^ n)) =
      ((p.num : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)) +
        (q.num : ZMod (3 ^ n)) * (p.den : ZMod (3 ^ n))) *
        ((p + q).den : ZMod (3 ^ n)) := by
    have h := congrArg (fun z : ℤ => (z : ZMod (3 ^ n))) (add_num_cross_mul_den p q)
    push_cast at h ⊢
    linear_combination h
  have hsum :
      (threeLocalResidue n (p + q) hpq * ((p + q).den : ZMod (3 ^ n))) *
        ((p.den * q.den : ℕ) : ZMod (3 ^ n)) =
      (threeLocalResidue n p hp + threeLocalResidue n q hq) *
        ((p + q).den : ZMod (3 ^ n)) *
        ((p.den * q.den : ℕ) : ZMod (3 ^ n)) := by
    calc (threeLocalResidue n (p + q) hpq * ((p + q).den : ZMod (3 ^ n))) *
          ((p.den * q.den : ℕ) : ZMod (3 ^ n)) =
        ((p + q).num : ZMod (3 ^ n)) *
          ((p.den * q.den : ℕ) : ZMod (3 ^ n)) := by
            rw [threeLocalResidue_mul_den n (p + q) hpq]
      _ = ((p.num : ZMod (3 ^ n)) * (q.den : ZMod (3 ^ n)) +
            (q.num : ZMod (3 ^ n)) * (p.den : ZMod (3 ^ n))) *
            ((p + q).den : ZMod (3 ^ n)) := hcross
      _ = (threeLocalResidue n p hp + threeLocalResidue n q hq) *
            ((p + q).den : ZMod (3 ^ n)) *
            ((p.den * q.den : ℕ) : ZMod (3 ^ n)) := by
            rw [← threeLocalResidue_mul_den n p hp,
              ← threeLocalResidue_mul_den n q hq, hdenprod]
            ring
  exact (isUnit_coe_of_not_dvd_three n hpq).mul_left_injective
    ((isUnit_coe_of_not_dvd_three n (Nat.prime_three.not_dvd_mul hp hq)).mul_left_injective hsum)

end Theory.PiDigits.T93ThreeLocalOperations

#print axioms Theory.PiDigits.T93ThreeLocalOperations.threeLocalCongruent_of_ratCongruentThree
#print axioms Theory.PiDigits.T93ThreeLocalOperations.threeLocalResidue_mul
#print axioms Theory.PiDigits.T93ThreeLocalOperations.threeLocalResidue_add
