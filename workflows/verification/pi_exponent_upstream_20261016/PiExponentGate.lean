import OAI.NumberTheory.PiExponent.Main

/- Literal statements are repeated here so a renamed or weakened upstream
   definition cannot silently change the checked mathematical target. -/

#check (OAI.PiExponent.pi_eventual_lower_bound :
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|)

#check (OAI.PiExponent.pi_integer_eventual_lower_bound :
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|)

#check (OAI.PiExponent.main :
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2)

#check (OAI.PiExponent.flint_hills_summable :
  Summable (fun n : ℕ =>
    1 / (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sin (n + 1 : ℕ) ^ 2)))

#print axioms OAI.PiExponent.main
#print axioms OAI.PiExponent.pi_eventual_lower_bound
#print axioms OAI.PiExponent.pi_irrationalityExponent_eq_two
#print axioms OAI.PiExponent.flint_hills_summable
