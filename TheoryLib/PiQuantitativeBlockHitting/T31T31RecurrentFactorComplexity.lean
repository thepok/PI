import TheoryLib.PiQuantitativeBlockHitting.T30T30MaximalEntropyEquivalence
import TheoryLib.PiDigits.T11PiDigitFactorComplexity

/-!
# T31: every positive length has recurrent Morse--Hedlund complexity

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

A factor is recurrent here when it occurs at starts beyond every prescribed
threshold.  For an arbitrary finite-alphabet stream which is not eventually
periodic, the recurrent length-`n` factors already satisfy the sharp
Morse--Hedlund lower bound `n + 1`.  The proof removes the finitely many
nonrecurrent factors, shifts beyond all their last occurrences, and applies
one-sided Morse--Hedlund to that tail.

The specialization says that at least `n + 1` distinct length-`n` decimal
blocks recur arbitrarily late in the exact digit stream of pi.  Canonical V1
would require all `10 ^ n` blocks, including every prescribed block.  Thus
this is an unconditional strengthening of the recurrent-digit baseline, not
a proof of V1 or normality.
-/

noncomputable section

namespace Theory.PiDigits.RecurrentFactorComplexity

open DecimalFactorComplexity
open Theory.PiDigits.FactorComplexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A length-`n` block is recurrent when it occurs at starts beyond every
threshold. -/
def RecurrentBlock (s : Stream α) (n : ℕ) (w : Block α n) : Prop :=
  ∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧ blockAt s n i = w

/-- The finite type of recurrent length-`n` blocks. -/
abbrev RecurrentFactor (s : Stream α) (n : ℕ) :=
  {w : Block α n // RecurrentBlock s n w}

/-- The number of distinct recurrent length-`n` blocks. -/
def recurrentFactorComplexity (s : Stream α) (n : ℕ) : ℕ :=
  Nat.card (RecurrentFactor s n)

omit [DecidableEq α] in
/-- Finiteness of the block alphabet gives one start after which every
length-`n` block is recurrent. -/
lemma exists_recurrentBlock_cutoff (s : Stream α) (n : ℕ) :
    ∃ C : ℕ, ∀ i : ℕ, C ≤ i → RecurrentBlock s n (blockAt s n i) := by
  classical
  have hthreshold : ∀ w : Block α n, ∃ N : ℕ,
      ∀ i : ℕ, N ≤ i → blockAt s n i = w → RecurrentBlock s n w := by
    intro w
    by_cases hw : RecurrentBlock s n w
    · exact ⟨0, fun _ _ _ ↦ hw⟩
    · simp only [RecurrentBlock, not_forall] at hw
      obtain ⟨N, hN⟩ := hw
      push Not at hN
      exact ⟨N, fun i hi hisw ↦ (hN i hi hisw).elim⟩
  let cutoff : Block α n → ℕ := fun w ↦ (hthreshold w).choose
  let C : ℕ := Finset.univ.sup cutoff
  refine ⟨C, fun i hi ↦ ?_⟩
  have hcutoff : cutoff (blockAt s n i) ≤ C :=
    Finset.le_sup (Finset.mem_univ (blockAt s n i))
  exact (hthreshold (blockAt s n i)).choose_spec i (hcutoff.trans hi) rfl

/-- Delete the first `C` symbols from a stream. -/
def dropStream (s : Stream α) (C : ℕ) : Stream α :=
  fun i ↦ s (C + i)

omit [Fintype α] [DecidableEq α] in
lemma blockAt_dropStream (s : Stream α) (C n i : ℕ) :
    blockAt (dropStream s C) n i = blockAt s n (C + i) := by
  funext j
  simp [blockAt, dropStream, Nat.add_assoc]

omit [Fintype α] [DecidableEq α] in
/-- Eventual periodicity of a tail implies eventual periodicity of the
original stream. -/
lemma eventuallyPeriodic_of_dropStream
    (s : Stream α) (C : ℕ)
    (hperiodic : EventuallyPeriodic (dropStream s C)) :
    EventuallyPeriodic s := by
  obtain ⟨start, period, hperiod, htail⟩ := hperiodic
  refine ⟨C + start, period, hperiod, fun i ↦ ?_⟩
  simpa [dropStream, Nat.add_assoc] using htail i

/-- Once `C` is beyond all last occurrences of nonrecurrent blocks, every
factor of the shifted stream canonically gives a recurrent factor of the
original stream. -/
def tailFactorToRecurrent
    (s : Stream α) (n C : ℕ)
    (hC : ∀ i : ℕ, C ≤ i → RecurrentBlock s n (blockAt s n i)) :
    Factor (dropStream s C) n → RecurrentFactor s n := by
  intro v
  refine ⟨v.1, ?_⟩
  let i := firstOccurrence v
  have hrec : RecurrentBlock s n (blockAt s n (C + i)) :=
    hC (C + i) (by omega)
  have hblock : blockAt (dropStream s C) n i = v.1 := by
    funext j
    exact (firstOccurrence_spec v j).symm
  have horiginal : blockAt s n (C + i) = v.1 := by
    rw [← blockAt_dropStream]
    exact hblock
  rwa [horiginal] at hrec

lemma tailFactorToRecurrent_injective
    (s : Stream α) (n C : ℕ)
    (hC : ∀ i : ℕ, C ≤ i → RecurrentBlock s n (blockAt s n i)) :
    Function.Injective (tailFactorToRecurrent s n C hC) := by
  intro v w hvw
  apply Subtype.ext
  exact congrArg (fun x : RecurrentFactor s n ↦ x.1) hvw

/-- Every non-eventually-periodic finite-alphabet stream has at least `n + 1`
distinct recurrent factors of every positive length `n`. -/
theorem recurrentFactorComplexity_lower_bound
    (s : Stream α) (haperiodic : ¬EventuallyPeriodic s) :
    ∀ n : ℕ, 0 < n → n + 1 ≤ recurrentFactorComplexity s n := by
  intro n hn
  obtain ⟨C, hC⟩ := exists_recurrentBlock_cutoff s n
  have htailAperiodic : ¬EventuallyPeriodic (dropStream s C) := by
    intro htail
    exact haperiodic (eventuallyPeriodic_of_dropStream s C htail)
  have hlower : n + 1 ≤ canonicalFactorComplexity (dropStream s C) n :=
    morse_hedlund_canonical (dropStream s C) htailAperiodic n hn
  have hupper : canonicalFactorComplexity (dropStream s C) n ≤
      recurrentFactorComplexity s n := by
    exact Nat.card_le_card_of_injective
      (tailFactorToRecurrent s n C hC)
      (tailFactorToRecurrent_injective s n C hC)
  exact hlower.trans hupper

/-- For every positive `n`, at least `n + 1` distinct length-`n` decimal
blocks occur at starts beyond every threshold in the exact decimal expansion
of pi. -/
theorem pi_recurrentFactorComplexity_lower_bound :
    ∀ n : ℕ, 0 < n →
      n + 1 ≤ recurrentFactorComplexity Theory.PiDigits.piDigit n := by
  exact recurrentFactorComplexity_lower_bound
    Theory.PiDigits.piDigit piDigit_not_eventuallyPeriodic

/-- Fully expanded occurrence form of the pi theorem: there is a finite set
of at least `n + 1` distinct blocks, and each member occurs arbitrarily late.
-/
theorem pi_has_many_distinct_arbitrarily_late_blocks
    (n : ℕ) (hn : 0 < n) :
    ∃ W : Finset (Block (Fin 10) n),
      n + 1 ≤ W.card ∧
      ∀ w ∈ W, ∀ N : ℕ, ∃ i : ℕ,
        N ≤ i ∧ blockAt Theory.PiDigits.piDigit n i = w := by
  classical
  let W : Finset (Block (Fin 10) n) :=
    Finset.univ.filter (RecurrentBlock Theory.PiDigits.piDigit n)
  refine ⟨W, ?_, ?_⟩
  · have hcard : W.card =
        recurrentFactorComplexity Theory.PiDigits.piDigit n := by
      rw [recurrentFactorComplexity, Nat.card_eq_fintype_card,
        Fintype.card_subtype]
    rw [hcard]
    exact pi_recurrentFactorComplexity_lower_bound n hn
  · intro w hw
    simpa [W, RecurrentBlock] using hw

end Theory.PiDigits.RecurrentFactorComplexity

#print axioms Theory.PiDigits.RecurrentFactorComplexity.recurrentFactorComplexity_lower_bound
#print axioms Theory.PiDigits.RecurrentFactorComplexity.pi_recurrentFactorComplexity_lower_bound
#print axioms Theory.PiDigits.RecurrentFactorComplexity.pi_has_many_distinct_arbitrarily_late_blocks
