import TheoryLib.PiDigits.T11PiDigitFactorComplexity
import TheoryLib.PiDigits.T21PiDigitsV1V3Relationship

/-!
# Quantitative block hitting for the decimal digits of pi

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

The imported pi stream is zero-based: stream index `n` is the source's digit
`d_(n+1)`. Hence the source condition `i + k - 1 <= N` is represented exactly
by `n + k <= N`. Words are functions `Fin k -> Fin 10`, so leading zeroes are
retained and occurrences are contiguous at arbitrary natural-number starts.

The statement's ambiguous readings are kept separate below. `C1` is canonical:
one `C` works for all positive `k` and all words. `A2` allows a different
The constant for each `k`; `A3` requires the canonical rate only eventually; `A4`
bounds only the one-based start `n + 1`; and `A5` removes the factor `k` from
the deadline. None of these open propositions is asserted unconditionally.
-/

namespace Theory.PiDigits.QuantitativeBlockHitting

open DecimalFactorComplexity

/-- A length-`k` decimal word. This includes words whose first digit is zero. -/
abbrev DecimalWord (k : ℕ) := Block (Fin 10) k

/-- The word occurs contiguously at zero-based start `n` and is fully contained
in the prefix of length `N`. The inequality translates the source's one-based
condition `i + k - 1 <= N` using `i = n + 1`. -/
def FullyContainedOccurrence (x : ℕ → Fin 10) {k : ℕ}
    (w : DecimalWord k) (N : ℕ) : Prop :=
  ∃ n : ℕ, n + k ≤ N ∧ OccursAt x w n

/-- Every length-`k` decimal word is fully contained in the prefix of length
`N`, with an independently chosen arbitrary contiguous start. -/
def CoversAllLengthKWordsBy (x : ℕ → Fin 10) (k N : ℕ) : Prop :=
  ∀ w : DecimalWord k, FullyContainedOccurrence x w N

/-- Full-containment cover time. It is the infimum of successful finite prefix
lengths in `ℕ∞`; if no finite prefix covers all words, every term is `⊤` and
the cover time is `⊤`. -/
noncomputable def fullContainmentCoverTime (x : ℕ → Fin 10) (k : ℕ) : ℕ∞ :=
  by
    classical
    exact ⨅ N : ℕ, if CoversAllLengthKWordsBy x k N then (N : ℕ∞) else ⊤

/-- Any successful prefix gives an upper bound for full-containment cover time. -/
theorem fullContainmentCoverTime_le_of_covers {x : ℕ → Fin 10} {k N : ℕ}
    (h : CoversAllLengthKWordsBy x k N) :
    fullContainmentCoverTime x k ≤ (N : ℕ∞) := by
  classical
  unfold fullContainmentCoverTime
  exact (iInf_le (fun M : ℕ =>
    if CoversAllLengthKWordsBy x k M then (M : ℕ∞) else ⊤) N).trans (by simp [h])

/-- If no finite prefix covers all length-`k` words, cover time is infinity. -/
theorem fullContainmentCoverTime_eq_top_of_never_covers {x : ℕ → Fin 10} {k : ℕ}
    (h : ∀ N : ℕ, ¬ CoversAllLengthKWordsBy x k N) :
    fullContainmentCoverTime x k = ⊤ := by
  classical
  simp [fullContainmentCoverTime, h]

/-- C1, the canonical conjecture: one natural `C >= 1` works uniformly for
every positive length and every decimal word, with full containment. -/
def C1 : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
    CoversAllLengthKWordsBy Theory.PiDigits.piDigit k (C * k * 10 ^ k)

/-- A2: the constant may depend on `k`. This is not the quantitative target. -/
def A2 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ Ck : ℕ, 1 ≤ Ck ∧
    CoversAllLengthKWordsBy Theory.PiDigits.piDigit k (Ck * k * 10 ^ k)

/-- A3: one constant gives the canonical rate only at all sufficiently large
positive lengths. -/
def A3 : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ K : ℕ, ∀ k : ℕ, max 1 K ≤ k →
    CoversAllLengthKWordsBy Theory.PiDigits.piDigit k (C * k * 10 ^ k)

/-- A4: only the one-based start `n + 1` is bounded; the factor need not be
fully contained by the same numerical deadline. -/
def A4 : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ w : DecimalWord k,
    ∃ n : ℕ, n + 1 ≤ C * k * 10 ^ k ∧
      OccursAt Theory.PiDigits.piDigit w n

/-- A5: the stronger full-containment deadline `C * 10^k`, without the factor
`k`, holds uniformly at every positive length. -/
def A5 : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
    CoversAllLengthKWordsBy Theory.PiDigits.piDigit k (C * 10 ^ k)

/-- C1 with every quantifier and the arbitrary-start full-containment witness
expanded. This theorem type is an audit surface for the canonical statement. -/
theorem C1_iff_explicit_uniform_full_containment :
    C1 ↔ ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ w : DecimalWord k, ∃ n : ℕ,
        n + k ≤ C * k * 10 ^ k ∧
          OccursAt Theory.PiDigits.piDigit w n := by
  rfl

/-- Canonical C1 gives the corresponding uniform upper bound on the
infinity-valued full-containment cover time. -/
theorem C1_implies_fullContainmentCoverTime_bound (h : C1) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      fullContainmentCoverTime Theory.PiDigits.piDigit k ≤
        ((C * k * 10 ^ k : ℕ) : ℕ∞) := by
  obtain ⟨C, hC, hcover⟩ := h
  refine ⟨C, hC, ?_⟩
  intro k hk
  exact fullContainmentCoverTime_le_of_covers (hcover k hk)

/-- Leading-zero coverage is explicit: the same uniform `C` covers every
positive-length word whose first digit is zero, at an arbitrary contiguous
start, with full containment. -/
theorem C1_implies_leadingZero_full_containment (h : C1) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, ∀ hk : 1 ≤ k, ∀ w : DecimalWord k,
      w ⟨0, hk⟩ = (0 : Fin 10) → ∃ n : ℕ,
        n + k ≤ C * k * 10 ^ k ∧
          OccursAt Theory.PiDigits.piDigit w n := by
  obtain ⟨C, hC, hcover⟩ := h
  refine ⟨C, hC, ?_⟩
  intro k hk w _
  exact hcover k hk w

/-- Canonical C1 implies T7's exact canonical V1 statement for lists. -/
theorem C1_implies_canonicalV1 (h : C1) : Theory.PiDigits.V1 := by
  obtain ⟨C, _, hcover⟩ := h
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons a t =>
    have hk : 1 ≤ (a :: t).length := by simp
    let w : DecimalWord (a :: t).length := fun j => (a :: t).get j
    obtain ⟨n, _, hn⟩ := hcover (a :: t).length hk w
    refine ⟨n, ?_⟩
    intro i hi
    exact (hn ⟨i, hi⟩).symm

/-- C1 supplies every finite function-valued decimal block, including the
zero-length block, and therefore gives decimal disjunctivity. -/
theorem C1_implies_decimalDisjunctive (h : C1) :
    Disjunctive Theory.PiDigits.piDigit := by
  obtain ⟨C, _, hcover⟩ := h
  intro k w
  by_cases hk : k = 0
  · subst k
    refine ⟨0, ?_⟩
    intro j
    exact Fin.elim0 j
  · obtain ⟨n, _, hn⟩ := hcover k (Nat.one_le_iff_ne_zero.mpr hk) w
    exact ⟨n, hn⟩

/-- C1 forces the exact maximum `10^k` distinct factors at every length `k`. -/
theorem C1_implies_full_factorComplexity (h : C1) :
    ∀ k : ℕ,
      Theory.PiDigits.FactorComplexity.piFactorComplexity k = 10 ^ k := by
  simpa only [Theory.PiDigits.FactorComplexity.piFactorComplexity] using
    (decimal_disjunctive_iff_canonical_factorComplexity
      Theory.PiDigits.piDigit).mp (C1_implies_decimalDisjunctive h)

/-- The requested combined implication from C1 to exact canonical V1 and full
length-`k` factor complexity. -/
theorem C1_implies_canonicalV1_and_full_factorComplexity (h : C1) :
    Theory.PiDigits.V1 ∧
      ∀ k : ℕ,
        Theory.PiDigits.FactorComplexity.piFactorComplexity k = 10 ^ k :=
  ⟨C1_implies_canonicalV1 h, C1_implies_full_factorComplexity h⟩

/-- Fully expanded acceptance theorem. Its hypothesis visibly quantifies one
uniform `C`, every positive `k`, every function-valued word (hence leading-zero
words), and an arbitrary contiguous start whose factor is fully contained. -/
theorem explicit_uniform_full_containment_implies_canonicalV1_and_full_factorComplexity
    (h : ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ w : DecimalWord k, ∃ n : ℕ,
        n + k ≤ C * k * 10 ^ k ∧
          OccursAt Theory.PiDigits.piDigit w n) :
    Theory.PiDigits.V1 ∧
      ∀ k : ℕ,
        Theory.PiDigits.FactorComplexity.piFactorComplexity k = 10 ^ k := by
  exact C1_implies_canonicalV1_and_full_factorComplexity
    (C1_iff_explicit_uniform_full_containment.mpr h)

/-- A single hostile-review surface containing every acceptance clause without
requiring `OccursAt` to be unfolded. The same displayed `C` covers all words
and, explicitly, all leading-zero words; `n + j` displays arbitrary contiguous
starts and `n + k` displays full containment. -/
theorem acceptance_audit_surface
    (h : ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ w : DecimalWord k,
      ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
        ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) :
    (Theory.PiDigits.V1 ∧
      ∀ k : ℕ,
        Theory.PiDigits.FactorComplexity.piFactorComplexity k = 10 ^ k) ∧
    ∃ C : ℕ, 1 ≤ C ∧
      (∀ k : ℕ, 1 ≤ k → ∀ w : DecimalWord k,
        ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
          ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
      (∀ k : ℕ, ∀ hk : 1 ≤ k, ∀ w : DecimalWord k,
        w ⟨0, hk⟩ = (0 : Fin 10) →
          ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
            ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) := by
  obtain ⟨C, hC, hwords⟩ := h
  have hC1 : C1 := by
    refine ⟨C, hC, ?_⟩
    intro k hk w
    obtain ⟨n, hcontained, hdigits⟩ := hwords k hk w
    exact ⟨n, hcontained, fun j => (hdigits j).symm⟩
  refine ⟨C1_implies_canonicalV1_and_full_factorComplexity hC1,
    ⟨C, hC, hwords, ?_⟩⟩
  intro k hk w _
  exact hwords k hk w

end Theory.PiDigits.QuantitativeBlockHitting

#print axioms Theory.PiDigits.QuantitativeBlockHitting.fullContainmentCoverTime_le_of_covers
#print axioms Theory.PiDigits.QuantitativeBlockHitting.fullContainmentCoverTime_eq_top_of_never_covers
#print axioms Theory.PiDigits.QuantitativeBlockHitting.C1_iff_explicit_uniform_full_containment
#print axioms Theory.PiDigits.QuantitativeBlockHitting.C1_implies_fullContainmentCoverTime_bound
#print axioms Theory.PiDigits.QuantitativeBlockHitting.C1_implies_leadingZero_full_containment
#print axioms Theory.PiDigits.QuantitativeBlockHitting.C1_implies_canonicalV1
#print axioms Theory.PiDigits.QuantitativeBlockHitting.C1_implies_full_factorComplexity
#print axioms Theory.PiDigits.QuantitativeBlockHitting.C1_implies_canonicalV1_and_full_factorComplexity
#print axioms Theory.PiDigits.QuantitativeBlockHitting.explicit_uniform_full_containment_implies_canonicalV1_and_full_factorComplexity
#print axioms Theory.PiDigits.QuantitativeBlockHitting.acceptance_audit_surface
