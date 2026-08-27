import TheoryLib.PiDigits.T7Statements
import TheoryLib.PiDigits.T9PiDigitsV3Reduction

/-!
# T21: the logical relationship between decimal V1 and sibling V3

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

All finite lists are allowed below, including the empty word. An occurrence
"beyond `N`" means that its starting index is at least `N`.

The periodic stream constructed below is an artificial decimal stream, not
the decimal expansion of pi. Consequently, the unconditional separator below
proves neither canonical V1 nor sibling V3 for pi. The only theorem about pi
is the conditional implication `V1 → V3`.
-/

namespace Theory.PiDigits.T21

/-- The finite word `w` starts at position `n` in the decimal stream `x`. -/
def WordOccursAt (x : ℕ → Fin 10) (w : List (Fin 10)) (n : ℕ) : Prop :=
  ∀ i : ℕ, ∀ hi : i < w.length, x (n + i) = w[i]

/-- Generic decimal disjunctivity: every finite word occurs contiguously. -/
def EveryFiniteWordOccurs (x : ℕ → Fin 10) : Prop :=
  ∀ w : List (Fin 10), ∃ n : ℕ, WordOccursAt x w n

/-- Every finite word has an occurrence starting beyond every threshold. -/
def EveryFiniteWordOccursArbitrarilyLate (x : ℕ → Fin 10) : Prop :=
  ∀ w : List (Fin 10), ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ WordOccursAt x w n

/-- For decimal streams, finite-word universality is automatically recurrent. -/
theorem everyFiniteWordOccurs_iff_arbitrarilyLate (x : ℕ → Fin 10) :
    EveryFiniteWordOccurs x ↔ EveryFiniteWordOccursArbitrarilyLate x := by
  constructor
  · intro h w N
    obtain ⟨n, hn⟩ := h (List.replicate N (0 : Fin 10) ++ w)
    refine ⟨n + N, by omega, ?_⟩
    intro i hi
    have hindex : N + i < (List.replicate N (0 : Fin 10) ++ w).length := by
      simp only [List.length_append, List.length_replicate]
      omega
    have hoccurs := hn (N + i) hindex
    rw [List.getElem_append_right (by simp :
      (List.replicate N (0 : Fin 10)).length ≤ N + i)] at hoccurs
    simpa [WordOccursAt, Nat.add_assoc] using hoccurs
  · intro h w
    obtain ⟨n, _, hn⟩ := h w 0
    exact ⟨n, hn⟩

/-- T7's canonical V1 is definitionally generic finite-word universality for `piDigit`. -/
theorem canonicalV1_iff_everyFiniteWordOccurs_piDigit :
    Theory.PiDigits.V1 ↔ EveryFiniteWordOccurs Theory.PiDigits.piDigit := by
  rfl

/--
T7's exact canonical V1 implies T7's exact sibling V3. This is conditional:
it does not prove either proposition for pi.
-/
theorem canonicalV1_implies_siblingV3 :
    Theory.PiDigits.V1 → Theory.PiDigits.V3 := by
  intro hV1
  apply Theory.PiDigits.V3Reduction.everyDigitOccursArbitrarilyLate_implies_siblingV3
  have hrecurrent : EveryFiniteWordOccursArbitrarilyLate Theory.PiDigits.piDigit :=
    (everyFiniteWordOccurs_iff_arbitrarilyLate Theory.PiDigits.piDigit).mp
      (canonicalV1_iff_everyFiniteWordOccurs_piDigit.mp hV1)
  intro d N
  obtain ⟨n, hn, hword⟩ := hrecurrent [d] N
  refine ⟨n, hn, ?_⟩
  simpa [WordOccursAt] using hword 0 (by simp)

/-- The artificial periodic decimal stream `0, 1, ..., 9, 0, 1, ...`. -/
def periodicDecimalStream (n : ℕ) : Fin 10 :=
  ⟨n % 10, Nat.mod_lt n (by norm_num)⟩

/-- Every digit occurs arbitrarily late in the artificial periodic stream. -/
theorem periodicDecimalStream_everyDigitOccursArbitrarilyLate :
    Theory.PiDigits.V3Reduction.EveryDigitOccursArbitrarilyLate
      periodicDecimalStream := by
  intro d N
  refine ⟨10 * (N + 1) + d.val, by omega, ?_⟩
  apply Fin.ext
  simp [periodicDecimalStream, Nat.mod_eq_of_lt d.isLt]

/-- The artificial periodic stream satisfies the generic analogue of sibling V3. -/
theorem periodicDecimalStream_satisfies_genericV3 :
    Theory.PiDigits.V3Reduction.EveryStreamIsSubsequence
      periodicDecimalStream := by
  exact
    Theory.PiDigits.V3Reduction.everyStreamIsSubsequence_of_everyDigitOccursArbitrarilyLate
      periodicDecimalStream periodicDecimalStream_everyDigitOccursArbitrarilyLate

/-- The word `[0, 0]` never starts in the artificial periodic stream. -/
theorem periodicDecimalStream_omits_zero_zero (n : ℕ) :
    ¬ WordOccursAt periodicDecimalStream [0, 0] n := by
  intro h
  have hzero := h 0 (by simp)
  have hone := h 1 (by simp)
  have hzeroVal := congrArg Fin.val hzero
  have honeVal := congrArg Fin.val hone
  simp [periodicDecimalStream] at hzeroVal honeVal
  omega

/-- The artificial periodic stream fails generic finite-word universality. -/
theorem periodicDecimalStream_fails_genericV1 :
    ¬ EveryFiniteWordOccurs periodicDecimalStream := by
  intro h
  obtain ⟨n, hn⟩ := h [0, 0]
  exact periodicDecimalStream_omits_zero_zero n hn

/--
An explicit generic decimal stream satisfies the analogue of sibling V3 and
fails the analogue of canonical V1. This witness is `periodicDecimalStream`,
not `piDigit`; the theorem makes no unconditional assertion about pi.
-/
theorem periodicDecimalStream_satisfies_genericV3_and_not_genericV1 :
    Theory.PiDigits.V3Reduction.EveryStreamIsSubsequence periodicDecimalStream ∧
      ¬ EveryFiniteWordOccurs periodicDecimalStream :=
  ⟨periodicDecimalStream_satisfies_genericV3,
    periodicDecimalStream_fails_genericV1⟩

end Theory.PiDigits.T21

#print axioms Theory.PiDigits.T21.everyFiniteWordOccurs_iff_arbitrarilyLate
#print axioms Theory.PiDigits.T21.canonicalV1_iff_everyFiniteWordOccurs_piDigit
#print axioms Theory.PiDigits.T21.canonicalV1_implies_siblingV3
#print axioms Theory.PiDigits.T21.periodicDecimalStream_everyDigitOccursArbitrarilyLate
#print axioms Theory.PiDigits.T21.periodicDecimalStream_satisfies_genericV3
#print axioms Theory.PiDigits.T21.periodicDecimalStream_omits_zero_zero
#print axioms Theory.PiDigits.T21.periodicDecimalStream_fails_genericV1
#print axioms Theory.PiDigits.T21.periodicDecimalStream_satisfies_genericV3_and_not_genericV1
