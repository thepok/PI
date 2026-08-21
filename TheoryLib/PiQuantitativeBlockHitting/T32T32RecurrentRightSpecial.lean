import TheoryLib.PiQuantitativeBlockHitting.T31T31RecurrentFactorComplexity

/-!
# T32: recurrent right-special factors at every length

Source: problems/local/pi-digits.txt
SHA-256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825

Deleting the last symbol maps recurrent length-n+1 factors onto recurrent
length-n factors. For a non-eventually-periodic finite-alphabet stream this
map cannot be injective: beyond a common recurrent-factor cutoff, injectivity
would make the ordinary tail complexity flat, and the existing one-sided
Morse--Hedlund machinery would make the tail, hence the original stream,
eventually periodic.

Consequently recurrent factor complexity increases by at least one at every
length, and every length has a recurrent factor with two distinct recurrent
one-symbol right extensions. The specialization applies to the exact decimal
digit stream of pi. It is a structural strengthening of T31, not a proof of
canonical V1: neither branch nor either appended digit is prescribed.
-/

noncomputable section

namespace Theory.PiDigits.RecurrentFactorComplexity

open DecimalFactorComplexity
open Theory.PiDigits.FactorComplexity

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- Recurrence of a block descends when its final symbol is deleted. -/
lemma recurrentBlock_initial (s : Stream α) (n : ℕ)
    {v : Block α (n + 1)} (hv : RecurrentBlock s (n + 1) v) :
    RecurrentBlock s n (initial v) := by
  intro N
  obtain ⟨i, hi, hiv⟩ := hv N
  refine ⟨i, hi, ?_⟩
  funext j
  change s (i + j) = v j.castSucc
  exact congrFun hiv j.castSucc

/-- Delete the final symbol of a recurrent factor. -/
noncomputable def recurrentInitial (s : Stream α) (n : ℕ) :
    RecurrentFactor s (n + 1) → RecurrentFactor s n :=
  fun v => ⟨initial v.1, recurrentBlock_initial s n v.2⟩

omit [DecidableEq α] in
/-- Every recurrent factor has at least one recurrent right extension. -/
lemma recurrentInitial_surjective (s : Stream α) (n : ℕ) :
    Function.Surjective (recurrentInitial s n) := by
  obtain ⟨C, hC⟩ := exists_recurrentBlock_cutoff s (n + 1)
  intro w
  obtain ⟨i, hi, hiw⟩ := w.2 C
  let v : RecurrentFactor s (n + 1) :=
    ⟨blockAt s (n + 1) i, hC i hi⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  exact hiw

/-- If recurrent right extension were unique at one length, a common tail
cutoff would have flat ordinary complexity and hence be eventually periodic. -/
lemma recurrentInitial_injective_implies_eventuallyPeriodic
    (s : Stream α) (n : ℕ)
    (hinj : Function.Injective (recurrentInitial s n)) :
    EventuallyPeriodic s := by
  obtain ⟨C, hC⟩ := exists_recurrentBlock_cutoff s (n + 1)
  let tail := dropStream s C
  have hinitInj : Function.Injective (initialFactor tail n) := by
    intro v w hvw
    let rv := tailFactorToRecurrent s (n + 1) C hC v
    let rw := tailFactorToRecurrent s (n + 1) C hC w
    have hrinit : recurrentInitial s n rv = recurrentInitial s n rw := by
      apply Subtype.ext
      change initial v.1 = initial w.1
      exact congrArg Subtype.val hvw
    have hr := hinj hrinit
    have hrval := congrArg Subtype.val hr
    change v.1 = w.1 at hrval
    exact Subtype.ext hrval
  have hinitSurj : Function.Surjective (initialFactor tail n) := by
    intro w
    exact ⟨extendFactor tail n w, initial_extendFactor tail n w⟩
  have hflat :
      canonicalFactorComplexity tail (n + 1) =
        canonicalFactorComplexity tail n := by
    exact Nat.card_congr
      (Equiv.ofBijective (initialFactor tail n) ⟨hinitInj, hinitSurj⟩)
  have htail : EventuallyPeriodic tail := by
    exact eventuallyPeriodic_of_flat tail (canonicalComplexityData tail) n hflat
  exact eventuallyPeriodic_of_dropStream s C htail

/-- Every non-eventually-periodic stream has two distinct recurrent
length-n+1 factors with the same recurrent length-n prefix. -/
theorem exists_distinct_recurrent_extensions
    (s : Stream α) (haperiodic : ¬ EventuallyPeriodic s) (n : ℕ) :
    ∃ v₁ v₂ : RecurrentFactor s (n + 1),
      v₁ ≠ v₂ ∧ recurrentInitial s n v₁ = recurrentInitial s n v₂ := by
  by_contra hNo
  have hinj : Function.Injective (recurrentInitial s n) := by
    intro v₁ v₂ heq
    by_contra hne
    exact hNo ⟨v₁, v₂, hne, heq⟩
  exact haperiodic
    (recurrentInitial_injective_implies_eventuallyPeriodic s n hinj)

omit [Fintype α] [DecidableEq α] in
/-- Distinct blocks with the same prefix have distinct final symbols. -/
lemma last_ne_of_initial_eq_of_ne {n : ℕ} {v₁ v₂ : Block α (n + 1)}
    (hne : v₁ ≠ v₂) (hinit : initial v₁ = initial v₂) :
    v₁ (Fin.last n) ≠ v₂ (Fin.last n) := by
  intro hlast
  apply hne
  funext j
  refine Fin.lastCases hlast (fun i => ?_) j
  exact congrFun hinit i

omit [Fintype α] [DecidableEq α] in
lemma snoc_initial_last {n : ℕ} (v : Block α (n + 1)) :
    Fin.snoc (initial v) (v (Fin.last n)) = v := by
  funext j
  cases j using Fin.lastCases <;> simp [initial]

/-- Abstract right-special form, retaining the recurrent-factor subtypes. -/
theorem exists_recurrent_block_two_recurrent_right_extensions
    (s : Stream α) (haperiodic : ¬ EventuallyPeriodic s) (n : ℕ) :
    ∃ w : RecurrentFactor s n,
      ∃ v₁ v₂ : RecurrentFactor s (n + 1),
        recurrentInitial s n v₁ = w ∧
        recurrentInitial s n v₂ = w ∧
        v₁.1 (Fin.last n) ≠ v₂.1 (Fin.last n) := by
  obtain ⟨v₁, v₂, hne, heq⟩ :=
    exists_distinct_recurrent_extensions s haperiodic n
  refine ⟨recurrentInitial s n v₁, v₁, v₂, rfl, heq.symm, ?_⟩
  apply last_ne_of_initial_eq_of_ne
  · intro hval
    exact hne (Subtype.ext hval)
  · exact congrArg Subtype.val heq

/-- Fully expanded right-special form: one recurrent length-n block has
two distinct symbols whose appended blocks both recur arbitrarily late. -/
theorem exists_recurrent_rightSpecial_blocks
    (s : Stream α) (haperiodic : ¬ EventuallyPeriodic s) (n : ℕ) :
    ∃ w : Block α n, ∃ a b : α,
      a ≠ b ∧
      RecurrentBlock s n w ∧
      RecurrentBlock s (n + 1) (Fin.snoc w a) ∧
      RecurrentBlock s (n + 1) (Fin.snoc w b) := by
  obtain ⟨w, v₁, v₂, hv₁, hv₂, hab⟩ :=
    exists_recurrent_block_two_recurrent_right_extensions s haperiodic n
  let a := v₁.1 (Fin.last n)
  let b := v₂.1 (Fin.last n)
  have hinit₁ : initial v₁.1 = w.1 := congrArg Subtype.val hv₁
  have hinit₂ : initial v₂.1 = w.1 := congrArg Subtype.val hv₂
  have hblock₁ : Fin.snoc w.1 a = v₁.1 := by
    rw [← hinit₁]
    exact snoc_initial_last v₁.1
  have hblock₂ : Fin.snoc w.1 b = v₂.1 := by
    rw [← hinit₂]
    exact snoc_initial_last v₂.1
  refine ⟨w.1, a, b, hab, w.2, ?_, ?_⟩
  · rw [hblock₁]
    exact v₁.2
  · rw [hblock₂]
    exact v₂.2

/-- Recurrent factor complexity increases strictly at every length. -/
theorem recurrentFactorComplexity_succ_lower_bound
    (s : Stream α) (haperiodic : ¬ EventuallyPeriodic s) (n : ℕ) :
    recurrentFactorComplexity s n + 1 ≤
      recurrentFactorComplexity s (n + 1) := by
  classical
  letI := Fintype.ofFinite (RecurrentFactor s n)
  letI := Fintype.ofFinite (RecurrentFactor s (n + 1))
  have hsurj := recurrentInitial_surjective s n
  obtain ⟨v₁, v₂, hne, heq⟩ :=
    exists_distinct_recurrent_extensions s haperiodic n
  have hninj : ¬Function.Injective (recurrentInitial s n) := by
    intro hinj
    exact hne (hinj heq)
  have hlt := Fintype.card_lt_of_surjective_not_injective
    (recurrentInitial s n) hsurj hninj
  simpa [recurrentFactorComplexity, Nat.card_eq_fintype_card] using hlt

/-- At every length, the exact decimal stream of pi has a recurrent block
with two distinct recurrent one-digit right extensions. -/
theorem pi_exists_recurrent_rightSpecial_blocks (n : ℕ) :
    ∃ w : Block (Fin 10) n, ∃ a b : Fin 10,
      a ≠ b ∧
      RecurrentBlock Theory.PiDigits.piDigit n w ∧
      RecurrentBlock Theory.PiDigits.piDigit (n + 1) (Fin.snoc w a) ∧
      RecurrentBlock Theory.PiDigits.piDigit (n + 1) (Fin.snoc w b) := by
  exact exists_recurrent_rightSpecial_blocks Theory.PiDigits.piDigit
    piDigit_not_eventuallyPeriodic n

/-- Pi's recurrent decimal factor complexity increases by at least one at
every successive length, including the step from length zero to one. -/
theorem pi_recurrentFactorComplexity_succ_lower_bound (n : ℕ) :
    recurrentFactorComplexity Theory.PiDigits.piDigit n + 1 ≤
      recurrentFactorComplexity Theory.PiDigits.piDigit (n + 1) := by
  exact recurrentFactorComplexity_succ_lower_bound Theory.PiDigits.piDigit
    piDigit_not_eventuallyPeriodic n

end Theory.PiDigits.RecurrentFactorComplexity

#print axioms Theory.PiDigits.RecurrentFactorComplexity.exists_recurrent_rightSpecial_blocks
#print axioms Theory.PiDigits.RecurrentFactorComplexity.recurrentFactorComplexity_succ_lower_bound
#print axioms Theory.PiDigits.RecurrentFactorComplexity.pi_exists_recurrent_rightSpecial_blocks
#print axioms
  Theory.PiDigits.RecurrentFactorComplexity.pi_recurrentFactorComplexity_succ_lower_bound
