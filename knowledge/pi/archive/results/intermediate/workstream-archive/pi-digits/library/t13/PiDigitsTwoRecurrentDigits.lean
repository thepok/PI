import TheoryLib.PiDigits.T11PiDigitFactorComplexity

/-!
# Two recurrent decimal digits of pi

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file proves only a partial result related to sibling V3: two distinct
digits occur arbitrarily late in T7's exact decimal digit stream for pi. V3
requires this for every decimal digit, so the result does not resolve V3.
It also does not prove that every finite block occurs and therefore does not
resolve canonical V1.
-/

namespace Theory.PiDigits.TwoRecurrentDigits

open DecimalFactorComplexity
open Theory.PiDigits.FactorComplexity

variable {α : Type*} [Fintype α]

/-- A symbol is recurrent when it occurs at or beyond every threshold. -/
def OccursArbitrarilyLate (s : ℕ → α) (a : α) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ s n = a

/-- Every stream over a finite alphabet has an arbitrarily-late symbol. -/
lemma exists_occursArbitrarilyLate (s : ℕ → α) :
    ∃ a : α, OccursArbitrarilyLate s a := by
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber s
  have ha' : Set.Infinite {n : ℕ | s n = a} := by
    simpa using Set.infinite_coe_iff.mp ha
  refine ⟨a, fun N ↦ ?_⟩
  obtain ⟨n, hn, hN⟩ := ha'.exists_gt N
  exact ⟨n, hN.le, hn⟩

/-- If at most one symbol is arbitrarily late, finiteness of the alphabet
gives a common cutoff after which the stream is constant. -/
lemma eventuallyConstant_of_subsingleton_recurrent (s : ℕ → α)
    (hunique : ∀ a b : α,
      OccursArbitrarilyLate s a → OccursArbitrarilyLate s b → a = b) :
    ∃ start : ℕ, ∃ a : α, ∀ n : ℕ, start ≤ n → s n = a := by
  classical
  obtain ⟨a, ha⟩ := exists_occursArbitrarilyLate s
  have hthreshold : ∀ b : α, ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → s n = b → b = a := by
    intro b
    by_cases hba : b = a
    · exact ⟨0, fun _ _ _ ↦ hba⟩
    · have hnot : ¬ OccursArbitrarilyLate s b := fun hb ↦ hba (hunique b a hb ha)
      simp only [OccursArbitrarilyLate, not_forall] at hnot
      obtain ⟨N, hN⟩ := hnot
      push Not at hN
      exact ⟨N, fun n hn hsn ↦ (hN n hn hsn).elim⟩
  let cutoff : α → ℕ := fun b ↦ (hthreshold b).choose
  let start : ℕ := Finset.univ.sup cutoff
  refine ⟨start, a, fun n hn ↦ ?_⟩
  have hcutoff : cutoff (s n) ≤ start := by
    exact Finset.le_sup (Finset.mem_univ (s n))
  exact (hthreshold (s n)).choose_spec n (hcutoff.trans hn) rfl

omit [Fintype α] in
/-- If `s` is constant from `start` onward, every factor is represented by
one of the `start + 1` starting positions from zero through `start`. -/
lemma canonicalFactorComplexity_le_of_eventuallyConstant (s : ℕ → α)
    {start : ℕ} {a : α} (hconstant : ∀ n : ℕ, start ≤ n → s n = a)
    (length : ℕ) :
    canonicalFactorComplexity s length ≤ start + 1 := by
  let representatives : Fin (start + 1) → Factor s length :=
    fun i ↦ factorAt s length i
  have hsurjective : Function.Surjective representatives := by
    intro w
    obtain ⟨i, hi⟩ := w.2
    by_cases histart : i < start
    · refine ⟨⟨i, by omega⟩, ?_⟩
      apply Subtype.ext
      funext j
      exact (hi j).symm
    · refine ⟨⟨start, by omega⟩, ?_⟩
      apply Subtype.ext
      funext j
      calc
        s (start + j) = a := hconstant _ (by omega)
        _ = s (i + j) := (hconstant _ (by omega)).symm
        _ = w.1 j := (hi j).symm
  simpa [canonicalFactorComplexity] using
    Nat.card_le_card_of_surjective representatives hsurjective

/-- A finite-alphabet stream satisfying the Morse--Hedlund lower bound has at
least two distinct symbols occurring arbitrarily late. -/
lemma exists_two_occursArbitrarilyLate_of_complexity_lower_bound (s : ℕ → α)
    (hlower : ∀ n : ℕ, 0 < n → n + 1 ≤ canonicalFactorComplexity s n) :
    ∃ a b : α, a ≠ b ∧
      OccursArbitrarilyLate s a ∧ OccursArbitrarilyLate s b := by
  by_contra htwo
  have hunique : ∀ a b : α,
      OccursArbitrarilyLate s a → OccursArbitrarilyLate s b → a = b := by
    intro a b ha hb
    by_contra hab
    exact htwo ⟨a, b, hab, ha, hb⟩
  obtain ⟨start, a, hconstant⟩ :=
    eventuallyConstant_of_subsingleton_recurrent s hunique
  have hlower' := hlower (start + 1) (by omega)
  have hupper := canonicalFactorComplexity_le_of_eventuallyConstant
    s hconstant (start + 1)
  omega

/-- Two distinct decimal digits each occur beyond every threshold in T7's
exact floor-based decimal digit stream for pi. This is a partial sibling-V3
result only: it does not establish recurrence of all ten digits and hence does
not resolve V3. It gives no occurrence theorem for arbitrary finite blocks and
therefore does not resolve canonical V1. -/
theorem pi_has_two_distinct_arbitrarily_late_digits :
    ∃ a b : Fin 10, a ≠ b ∧
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Theory.PiDigits.piDigit n = a) ∧
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Theory.PiDigits.piDigit n = b) := by
  apply exists_two_occursArbitrarilyLate_of_complexity_lower_bound
  simpa only [piFactorComplexity] using pi_factorComplexity_lower_bound

end Theory.PiDigits.TwoRecurrentDigits

#print axioms Theory.PiDigits.TwoRecurrentDigits.exists_occursArbitrarilyLate
#print axioms Theory.PiDigits.TwoRecurrentDigits.eventuallyConstant_of_subsingleton_recurrent
#print axioms Theory.PiDigits.TwoRecurrentDigits.canonicalFactorComplexity_le_of_eventuallyConstant
#print axioms Theory.PiDigits.TwoRecurrentDigits.exists_two_occursArbitrarilyLate_of_complexity_lower_bound
#print axioms Theory.PiDigits.TwoRecurrentDigits.pi_has_two_distinct_arbitrarily_late_digits
