import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TheoryLib.PiQuantitativeBlockHitting.T77T77SelectedPadicDefectShell

/-!
# T78: rational three-adic transport for the selected BBP defect

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module develops the exact `padicValRat` bridge left open by T77.  Its
first target is the uniform congruence

`((16^t - 1) / (15*t)) = 1 (mod 3)`

in the localization at three.  Later declarations transport that lemma
through the four rational BBP pole shells.
-/

open scoped BigOperators

namespace Theory.PiDigits.T78SelectedPadicDefectCongruence

open T74ThreePrimaryDecimation
open T77SelectedPadicDefectShell

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Rational congruence modulo a power of three, expressed using
`padicValRat`.  Equality is a separate branch because mathlib assigns
valuation zero, rather than infinity, to the zero rational. -/
def RatCongruentThree (n : ℕ) (x y : ℚ) : Prop :=
  x = y ∨ (n : ℤ) ≤ padicValRat 3 (x - y)

/-- Reflexivity of rational three-adic congruence. -/
theorem ratCongruentThree_refl (n : ℕ) (x : ℚ) :
    RatCongruentThree n x x := by
  exact Or.inl rfl

/-- Symmetry of rational three-adic congruence. -/
theorem ratCongruentThree_symm {n : ℕ} {x y : ℚ}
    (h : RatCongruentThree n x y) : RatCongruentThree n y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [show y - x = -(x - y) by ring, padicValRat.neg]
    exact h

/-- Rational three-adic congruence is transitive. -/
theorem ratCongruentThree_trans {n : ℕ} {x y z : ℚ}
    (hxy : RatCongruentThree n x y) (hyz : RatCongruentThree n y z) :
    RatCongruentThree n x z := by
  rcases hxy with hxy | hxy
  · rw [hxy]
    exact hyz
  · rcases hyz with hyz | hyz
    · rw [hyz] at hxy
      exact Or.inr hxy
    · by_cases hz : x - z = 0
      · exact Or.inl (sub_eq_zero.mp hz)
      · right
        have hadd : x - z = (x - y) + (y - z) := by ring
        rw [hadd]
        exact le_trans (le_min hxy hyz)
          (padicValRat.min_le_padicValRat_add (by rwa [← hadd]))

/-- Congruences add without any nonzero side condition. -/
theorem ratCongruentThree_add {n : ℕ} {x y u v : ℚ}
    (hxy : RatCongruentThree n x y) (huv : RatCongruentThree n u v) :
    RatCongruentThree n (x + u) (y + v) := by
  rcases hxy with rfl | hxy
  · rcases huv with rfl | huv
    · exact Or.inl rfl
    · right
      rwa [show (x + u) - (x + v) = u - v by ring]
  · rcases huv with rfl | huv
    · right
      rwa [show (x + u) - (y + u) = x - y by ring]
    · by_cases hz : (x + u) - (y + v) = 0
      · exact Or.inl (sub_eq_zero.mp hz)
      · right
        have hadd : (x + u) - (y + v) = (x - y) + (u - v) := by ring
        rw [hadd]
        exact le_trans (le_min hxy huv)
          (padicValRat.min_le_padicValRat_add (by rwa [← hadd]))

/-- A finite sum of termwise congruences is congruent to the sum of the
comparison terms. -/
theorem ratCongruentThree_sum {n : ℕ} {S : Finset ℕ} {f g : ℕ → ℚ}
    (h : ∀ i ∈ S, RatCongruentThree n (f i) (g i)) :
    RatCongruentThree n (∑ i ∈ S, f i) (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [RatCongruentThree]
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ratCongruentThree_add (h a (by simp))
        (ih (fun i hi ↦ h i (by simp [hi])))

/-- Rational three-adic congruence is preserved by negation. -/
theorem ratCongruentThree_neg {n : ℕ} {u v : ℚ}
    (h : RatCongruentThree n u v) : RatCongruentThree n (-u) (-v) := by
  have q' := ratCongruentThree_add h (ratCongruentThree_refl n (-v))
  rw [show (u : ℚ) + -v = u - v by ring, show (v : ℚ) + -v = 0 by ring] at q'
  have r : RatCongruentThree n 0 (u - v) := ratCongruentThree_symm q'
  have s : RatCongruentThree n (0 + -u) ((u - v) + -u) :=
    ratCongruentThree_add r (ratCongruentThree_refl n (-u))
  rw [zero_add, show (u - v) + -u = -v by ring] at s
  exact s

/-- Rational three-adic congruence is preserved by subtraction. -/
theorem ratCongruentThree_sub {n : ℕ} {x y u v : ℚ}
    (hxy : RatCongruentThree n x y) (huv : RatCongruentThree n u v) :
    RatCongruentThree n (x - u) (y - v) := by
  have h := ratCongruentThree_add hxy (ratCongruentThree_neg huv)
  rw [show (x : ℚ) - u = x + -u by ring,
      show (y : ℚ) - v = y + -v by ring]
  exact h

/-- Multiplication by a rational three-adic unit preserves congruence. -/
theorem ratCongruentThree_mul_unit {n : ℕ} {u x y : ℚ}
    (hu : u ≠ 0) (hvu : padicValRat 3 u = 0)
    (hxy : RatCongruentThree n x y) :
    RatCongruentThree n (u * x) (u * y) := by
  rcases hxy with rfl | h
  · exact Or.inl rfl
  · by_cases hz : x - y = 0
    · have heq : x = y := by linarith
      subst heq
      exact Or.inl rfl
    · right
      have hsub : u * x - u * y = u * (x - y) := by ring
      have hmul : padicValRat 3 (u * (x - y)) =
          padicValRat 3 u + padicValRat 3 (x - y) :=
        padicValRat.mul hu hz
      rw [hsub, hmul, hvu, zero_add]
      exact h

/-- The elementary valuation bound needed in the binomial remainder. -/
theorem padicValNat_three_le_sub_two {s : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 s ≤ s - 2 := by
  by_contra h
  have hpos : 0 < s := by omega
  have hge : s - 1 ≤ padicValNat 3 s := by omega
  have hdvd : 3 ^ (s - 1) ∣ s :=
    (Nat.pow_dvd_pow 3 hge).trans (pow_padicValNat_dvd (p := 3) (n := s))
  have hle : 3 ^ (s - 1) ≤ s := Nat.le_of_dvd hpos hdvd
  have hlt : s < 3 ^ (s - 1) := by
    have lt_three_pow_aux : ∀ n : ℕ, n + 2 < 3 ^ (n + 1) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        calc n + 3 ≤ 3 * (n + 2) := by omega
          _ < 3 * 3 ^ (n + 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ = 3 ^ (n + 1) * 3 := mul_comm 3 _
          _ = 3 ^ (n + 2) := (pow_succ 3 (n + 1)).symm
    have h2 := lt_three_pow_aux (s - 2)
    rwa [show s - 2 + 2 = s by omega, show s - 2 + 1 = s - 1 by omega] at h2
  omega

/-- The normalized nonconstant binomial summand in
`((1+15)^t-1)/(15*t)`. -/
def normalizedBinomialTerm (t s : ℕ) : ℚ :=
  (Nat.choose t s : ℚ) / t * 15 ^ (s - 1)

/-- The binomial quotient used by every paired BBP error. -/
def binomialQuotient (t : ℕ) : ℚ :=
  ((16 : ℚ) ^ t - 1) / (15 * t)

/-- Moving one factor from a binomial coefficient to its index. -/
theorem normalizedBinomialTerm_eq (t s : ℕ)
    (ht : 0 < t) (hs : 1 ≤ s) (hst : s ≤ t) :
    normalizedBinomialTerm t s =
      (Nat.choose (t - 1) (s - 1) : ℚ) / s * 15 ^ (s - 1) := by
  have hchoose :
      (Nat.choose t s : ℚ) * s = t * (Nat.choose (t - 1) (s - 1) : ℚ) := by
    have h := Nat.add_one_mul_choose_eq (t - 1) (s - 1)
    rw [show t - 1 + 1 = t by omega, show s - 1 + 1 = s by omega] at h
    exact_mod_cast h.symm
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hsq : (s : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  unfold normalizedBinomialTerm
  field_simp
  linear_combination hchoose

/-- Fifteen has exact three-adic valuation one. -/
theorem padicValRat_three_fifteen : padicValRat 3 (15 : ℚ) = 1 := by
  have hcast : (15 : ℚ) = ((15 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat]
  have hsplit : (15 : ℕ) = 3 * 5 := by norm_num
  rw [hsplit, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self (p := 3),
    padicValNat.eq_zero_of_not_dvd (by decide)]
  norm_num

/-- Every nonconstant normalized binomial summand is divisible by three in
the localization at three. -/
theorem one_le_padicValRat_normalizedBinomialTerm (t s : ℕ)
    (ht : 0 < t) (hs : 2 ≤ s) (hst : s ≤ t) :
    (1 : ℤ) ≤ padicValRat 3 (normalizedBinomialTerm t s) := by
  rw [normalizedBinomialTerm_eq t s ht (by omega) hst]
  have hspos : 0 < s := by omega
  have hs0q : (s : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hspos
  have hchoose0n : Nat.choose (t - 1) (s - 1) ≠ 0 :=
    Nat.choose_ne_zero (by omega)
  have hchoose0q : ((Nat.choose (t - 1) (s - 1) : ℕ) : ℚ) ≠ 0 :=
    by exact_mod_cast hchoose0n
  have hpow0 : (15 : ℚ) ^ (s - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpowval : padicValRat 3 ((15 : ℚ) ^ (s - 1)) = ((s - 1 : ℕ) : ℤ) := by
    rw [padicValRat.pow (k := s - 1) (show (15 : ℚ) ≠ 0 by norm_num),
      padicValRat_three_fifteen, mul_one]
  rw [padicValRat.mul (div_ne_zero hchoose0q hs0q) hpow0,
    padicValRat.div hchoose0q hs0q,
    padicValRat.of_nat, padicValRat.of_nat, hpowval]
  have hval := padicValNat_three_le_sub_two hs
  have hchooseNonneg :
      0 ≤ ((padicValNat 3 (Nat.choose (t - 1) (s - 1)) : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le _
  omega

end Theory.PiDigits.T78SelectedPadicDefectCongruence

#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.ratCongruentThree_add
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.ratCongruentThree_sum
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.ratCongruentThree_trans
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.ratCongruentThree_neg
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.ratCongruentThree_sub
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.ratCongruentThree_mul_unit
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.padicValNat_three_le_sub_two
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.normalizedBinomialTerm_eq
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.padicValRat_three_fifteen
#print axioms Theory.PiDigits.T78SelectedPadicDefectCongruence.one_le_padicValRat_normalizedBinomialTerm
