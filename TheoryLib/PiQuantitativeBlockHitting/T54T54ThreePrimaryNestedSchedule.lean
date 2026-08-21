import TheoryLib.PiQuantitativeBlockHitting.T53T53MachinQuotientCarry

/-!
# T54: exact nested schedule for the persistent three-primary factor

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T52 identifies a persistent denominator factor `3^(a-1)` whenever

`3^a <= 12*j+3 < 3^(a+1)`.

This module proves the elementary but useful compatibility of those factors
at adjacent indices.  If `a` and `a'` describe the windows at `j` and `j+1`,
then `a'` is either `a` or `a+1`.  Consequently the persistent factor is
unchanged or triples, and the old factor always divides the new one.

These exact nesting statements do not control the complementary numerator
phase and do not imply a decimal cylinder hit, normality, or the every-word
conjecture for pi.
-/

namespace Theory.PiDigits.ThreePrimaryNestedSchedule

/-- The persistent three-primary factor supplied by an exponent window. -/
def threePrimaryFactor (a : ℕ) : ℕ := 3 ^ (a - 1)

/-- Every exponent window containing `12*j+3` has positive exponent. -/
lemma one_le_threePrimaryExponent
    (j a : ℕ) (hupper : 12 * j + 3 < 3 ^ (a + 1)) :
    1 ≤ a := by
  by_contra hnot
  have ha : a = 0 := by omega
  simp [ha] at hupper

/-- Adjacent values `12*j+3` and `12*(j+1)+3` can cross at most one
power-of-three threshold. -/
theorem adjacent_threePrimaryExponent
    (j a a' : ℕ)
    (hlower : 3 ^ a ≤ 12 * j + 3)
    (hupper : 12 * j + 3 < 3 ^ (a + 1))
    (hlower' : 3 ^ a' ≤ 12 * (j + 1) + 3)
    (hupper' : 12 * (j + 1) + 3 < 3 ^ (a' + 1)) :
    a' = a ∨ a' = a + 1 := by
  have ha : 1 ≤ a := one_le_threePrimaryExponent j a hupper
  have hindex : 12 * j + 3 ≤ 12 * (j + 1) + 3 := by omega
  have hpowForward : 3 ^ a < 3 ^ (a' + 1) :=
    hlower.trans_lt (hindex.trans_lt hupper')
  have haa' : a ≤ a' := by
    have : a < a' + 1 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hpowForward
    omega
  have hnine : 3 ^ 2 ≤ 3 ^ (a + 1) :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).2 (by omega)
  have hnextUpper : 12 * (j + 1) + 3 < 3 ^ (a + 2) := by
    rw [show a + 2 = (a + 1) + 1 by omega, pow_succ]
    norm_num at hnine
    omega
  have hpowBackward : 3 ^ a' < 3 ^ (a + 2) :=
    hlower'.trans_lt hnextUpper
  have ha'upper : a' ≤ a + 1 := by
    have : a' < a + 2 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hpowBackward
    omega
  omega

/-- Along adjacent exponent windows, the persistent factor is unchanged or
is multiplied by three. -/
theorem threePrimaryFactor_eq_or_eq_three_mul
    (j a a' : ℕ)
    (hlower : 3 ^ a ≤ 12 * j + 3)
    (hupper : 12 * j + 3 < 3 ^ (a + 1))
    (hlower' : 3 ^ a' ≤ 12 * (j + 1) + 3)
    (hupper' : 12 * (j + 1) + 3 < 3 ^ (a' + 1)) :
    threePrimaryFactor a' = threePrimaryFactor a ∨
      threePrimaryFactor a' = 3 * threePrimaryFactor a := by
  have ha : 1 ≤ a := one_le_threePrimaryExponent j a hupper
  rcases adjacent_threePrimaryExponent j a a'
      hlower hupper hlower' hupper' with hsame | hstep
  · exact Or.inl (congrArg threePrimaryFactor hsame)
  · right
    subst a'
    simp only [threePrimaryFactor, Nat.add_sub_cancel]
    calc
      3 ^ a = 3 ^ ((a - 1) + 1) := by
        congr 1
        omega
      _ = 3 ^ (a - 1) * 3 := by rw [pow_succ]
      _ = 3 * 3 ^ (a - 1) := Nat.mul_comm _ _

/-- The three-primary factors form a divisibility chain along adjacent
exponent windows. -/
theorem threePrimaryFactor_dvd_next
    (j a a' : ℕ)
    (hlower : 3 ^ a ≤ 12 * j + 3)
    (hupper : 12 * j + 3 < 3 ^ (a + 1))
    (hlower' : 3 ^ a' ≤ 12 * (j + 1) + 3)
    (hupper' : 12 * (j + 1) + 3 < 3 ^ (a' + 1)) :
    threePrimaryFactor a ∣ threePrimaryFactor a' := by
  rcases threePrimaryFactor_eq_or_eq_three_mul j a a'
      hlower hupper hlower' hupper' with hsame | htriple
  · rw [hsame]
  · rw [htriple]
    exact ⟨3, by ac_rfl⟩

/-- The exact adjacent quotient of persistent factors is one or three. -/
theorem threePrimaryFactor_div_eq_one_or_three
    (j a a' : ℕ)
    (hlower : 3 ^ a ≤ 12 * j + 3)
    (hupper : 12 * j + 3 < 3 ^ (a + 1))
    (hlower' : 3 ^ a' ≤ 12 * (j + 1) + 3)
    (hupper' : 12 * (j + 1) + 3 < 3 ^ (a' + 1)) :
    threePrimaryFactor a' / threePrimaryFactor a = 1 ∨
      threePrimaryFactor a' / threePrimaryFactor a = 3 := by
  rcases threePrimaryFactor_eq_or_eq_three_mul j a a'
      hlower hupper hlower' hupper' with hsame | htriple
  · left
    rw [hsame]
    exact Nat.div_self (by simp [threePrimaryFactor])
  · right
    rw [htriple]
    rw [Nat.mul_comm 3 (threePrimaryFactor a)]
    exact Nat.mul_div_right 3
      (show 0 < threePrimaryFactor a by
        unfold threePrimaryFactor
        positivity)

end Theory.PiDigits.ThreePrimaryNestedSchedule

#print axioms Theory.PiDigits.ThreePrimaryNestedSchedule.one_le_threePrimaryExponent
#print axioms Theory.PiDigits.ThreePrimaryNestedSchedule.adjacent_threePrimaryExponent
#print axioms Theory.PiDigits.ThreePrimaryNestedSchedule.threePrimaryFactor_eq_or_eq_three_mul
#print axioms Theory.PiDigits.ThreePrimaryNestedSchedule.threePrimaryFactor_dvd_next
#print axioms Theory.PiDigits.ThreePrimaryNestedSchedule.threePrimaryFactor_div_eq_one_or_three
