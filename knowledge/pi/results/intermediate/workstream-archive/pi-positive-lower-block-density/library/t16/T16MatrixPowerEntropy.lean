import TheoryLib.PiPositiveLowerBlockDensity.T13T13ForbiddenLanguageEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T14T14PrefixAutomatonCertificates
import TheoryLib.PiPositiveLowerBlockDensity.T15T15FinitePrefixIntrinsicEntropy

/-!
# T16: exact matrix-power approximation of forbidden-word entropy

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

Every conclusion involving pi is a necessary consequence of the literal
negation of canonical C1. Nothing here asserts that C1 fails for pi.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators Matrix

namespace Theory.PiDigits.PositiveLowerBlockDensity.T16

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T9
open Theory.PiDigits.PositiveLowerBlockDensity.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T13
open Theory.PiDigits.PositiveLowerBlockDensity.T14
open Theory.PiDigits.PositiveLowerBlockDensity.T15

/-- The row sum of the `r`th power of T14's forbidden-word transition
matrix, starting from `s`. -/
def forbiddenMatrixRowSum {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (r : ℕ) (s : PrefixState ell hell) : ℕ :=
  ∑ t : PrefixState ell hell,
    (forbiddenTransitionMatrix hell v ^ r) s t

/-- `R_v(r)`: the maximum row sum of the `r`th matrix power. The agenda uses
this at positive `r`; defining the harmless value at zero makes it a sequence
on `ℕ` suitable for `Tendsto ... atTop`. -/
def forbiddenMaxRowSum {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (r : ℕ) : ℕ :=
  Finset.univ.sup (forbiddenMatrixRowSum hell v r)

/-- The normalized logarithm of `R_v(r)`. -/
def forbiddenMaxRowLogRatio {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (r : ℕ) : ℝ :=
  Real.log (forbiddenMaxRowSum hell v r : ℝ) / (r : ℝ)

theorem initialState_val_subset {ell : ℕ} (hell : 0 < ell)
    (s : PrefixState ell hell) :
    (initialState hell).1 ⊆ s.1 := by
  intro q hq
  have hq0 : q = (⟨0, hell⟩ : Fin ell) := by
    simpa [initialState] using hq
  subst q
  exact s.2

theorem nextPrefixSet_mono {ell : ℕ} (v : DecimalWord ell)
    {s t : Finset (Fin ell)} (hst : s ⊆ t) (d : DecimalDigit) :
    nextPrefixSet v s d ⊆ nextPrefixSet v t d := by
  intro q hq
  simp only [nextPrefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  rcases hq with hzero | ⟨p, hp, hq, hd⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨p, hst hp, hq, hd⟩

theorem completesWord_mono {ell : ℕ} (v : DecimalWord ell)
    {s t : Finset (Fin ell)} (hst : s ⊆ t) (d : DecimalDigit) :
    completesWord v s d → completesWord v t d := by
  rintro ⟨q, hq, hlast, hd⟩
  exact ⟨q, hst hq, hlast, hd⟩

/-- A transition from a larger active-prefix set can be shadowed from a
smaller set. The larger state can only forbid additional labels. -/
theorem prefixStep_of_subset {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) {s t u : PrefixState ell hell}
    (hst : s.1 ⊆ t.1) (d : DecimalDigit)
    (hstep : PrefixStep hell v t d u) :
    PrefixStep hell v s d (nextState hell v s d) ∧
      (nextState hell v s d).1 ⊆ u.1 := by
  rcases hstep with ⟨hcomplete, rfl⟩
  constructor
  · exact ⟨fun hs => hcomplete (completesWord_mono v hst d hs), rfl⟩
  · exact nextPrefixSet_mono v hst d

/-- Every path from an arbitrary (even unreachable) T14 prefix state has a
path from the empty-prefix state with exactly the same labels. The shadow
endpoint's active-prefix set is contained in the original endpoint. -/
theorem arbitraryState_path_shadow {ell n : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) {s t : PrefixState ell hell}
    (p : LabelledPath (PrefixStep hell v) n s t) :
    ∃ u : PrefixState ell hell,
      ∃ q : LabelledPath (PrefixStep hell v) n (initialState hell) u,
        pathWord q = pathWord p ∧ u.1 ⊆ t.1 := by
  induction n generalizing s t with
  | zero =>
      obtain ⟨hst⟩ := p
      subst t
      exact ⟨initialState hell, PLift.up rfl, rfl, initialState_val_subset hell s⟩
  | succ n ih =>
      obtain ⟨j, p, a⟩ := p
      obtain ⟨u, q, hword, hsubset⟩ := ih p
      obtain ⟨hstep, hnext⟩ :=
        prefixStep_of_subset hell v hsubset a.1 a.2
      refine ⟨nextState hell v u a.1, ⟨u, q, ⟨a.1, hstep⟩⟩, ?_, hnext⟩
      simp only [pathWord, hword]

/-- A path from any automaton state canonically gives a T13 forbidden word.
This public map is the reusable arbitrary-state comparison bridge. -/
def arbitraryPathToForbiddenWord {ell n : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (s : PrefixState ell hell)
    (p : Σ t : PrefixState ell hell,
      LabelledPath (PrefixStep hell v) n s t) :
    ForbiddenLanguage v n := by
  let w : DecimalWord n :=
    listToWord (pathWord p.2) (pathWord_length p.2)
  refine ⟨w, ?_⟩
  rw [← properPrefixAutomaton_language_equivalence hell v w]
  obtain ⟨u, q, hword, _hsubset⟩ := arbitraryState_path_shadow hell v p.2
  change ProperPrefixAutomatonAccepts hell v
    (wordList (listToWord (pathWord p.2) (pathWord_length p.2)))
  rw [wordList_listToWord]
  refine ⟨u, castLabelledPath (pathWord_length p.2).symm q, ?_⟩
  rw [pathWord_castLabelledPath]
  exact hword

theorem arbitraryPathToForbiddenWord_injective {ell n : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) (s : PrefixState ell hell) :
    Function.Injective (arbitraryPathToForbiddenWord hell v s :
      (Σ t : PrefixState ell hell,
        LabelledPath (PrefixStep hell v) n s t) → ForbiddenLanguage v n) := by
  intro p q hpq
  apply fullPath_word_injective (PrefixStep hell v)
    (fun z d t u => prefixStep_right_unique hell v z d) n s
  have hword := congrArg (fun z : ForbiddenLanguage v n => wordList z.1) hpq
  simpa only [arbitraryPathToForbiddenWord, wordList_listToWord] using hword

/-- Arbitrary-state paths inject into T13 forbidden words from the empty
state. Thus every matrix-power row sum is bounded by T13's exact count. -/
theorem arbitraryState_rowSum_le_forbiddenWordCount {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) (r : ℕ)
    (s : PrefixState ell hell) :
    forbiddenMatrixRowSum hell v r s ≤ forbiddenWordCount v r := by
  have hcard :
      Nat.card (Σ t : PrefixState ell hell,
        LabelledPath (PrefixStep hell v) r s t) ≤
        Nat.card (ForbiddenLanguage v r) :=
    Nat.card_le_card_of_injective
      (arbitraryPathToForbiddenWord (n := r) hell v s)
      (arbitraryPathToForbiddenWord_injective (n := r) hell v s)
  rw [labelledPath_rowSum_eq_matrix_pow] at hcard
  simpa [forbiddenMatrixRowSum, forbiddenTransitionMatrix] using hcard

theorem forbiddenMatrixRowSum_le_max {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (r : ℕ) (s : PrefixState ell hell) :
    forbiddenMatrixRowSum hell v r s ≤ forbiddenMaxRowSum hell v r := by
  exact Finset.le_sup (f := forbiddenMatrixRowSum hell v r) (Finset.mem_univ s)

/-- The maximum over all rows is exactly the empty-state row, hence exactly
T13's forbidden-word count. -/
theorem forbiddenMaxRowSum_eq_forbiddenWordCount {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) (r : ℕ) :
    forbiddenMaxRowSum hell v r = forbiddenWordCount v r := by
  apply le_antisymm
  · unfold forbiddenMaxRowSum
    exact Finset.sup_le fun s _ =>
      arbitraryState_rowSum_le_forbiddenWordCount hell v r s
  · rw [forbiddenWordCount_eq_matrix_rowSum hell v r]
    exact forbiddenMatrixRowSum_le_max hell v r (initialState hell)

/-- Positivity of `R_v(r)` for every `r`, in particular for agenda lengths
`r ≥ 1`. -/
theorem forbiddenMaxRowSum_pos {ell : ℕ} (hell : 0 < ell)
    (v : DecimalWord ell) (r : ℕ) :
    0 < forbiddenMaxRowSum hell v r := by
  rw [forbiddenMaxRowSum_eq_forbiddenWordCount]
  exact forbiddenWordCount_pos v hell r

/-- Submultiplicativity of maximum matrix-power row sums. -/
theorem forbiddenMaxRowSum_submultiplicative {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) (r s : ℕ) :
    forbiddenMaxRowSum hell v (r + s) ≤
      forbiddenMaxRowSum hell v r * forbiddenMaxRowSum hell v s := by
  simp only [forbiddenMaxRowSum_eq_forbiddenWordCount]
  exact forbiddenWordCount_submultiplicative v r s

/-- The exact finite matrix-power certificate
`M_v^r * 1 ≤ R_v(r) * 1`, stated coordinatewise as a vector inequality. -/
theorem matrixPower_mulVec_one_le_maxRowSum {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) (r : ℕ) :
    (forbiddenTransitionMatrix hell v ^ r) *ᵥ
        (1 : PrefixState ell hell → ℕ) ≤
      fun _ => forbiddenMaxRowSum hell v r * 1 := by
  intro s
  simpa [Matrix.mulVec, dotProduct, forbiddenMatrixRowSum] using
    forbiddenMatrixRowSum_le_max hell v r s

/-- The normalized maximum-row logarithms are literally T13's normalized
forbidden-language logarithms. -/
theorem forbiddenMaxRowLogRatio_eq_forbiddenLogRatio {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) (r : ℕ) :
    forbiddenMaxRowLogRatio hell v r = forbiddenLogRatio v r := by
  simp [forbiddenMaxRowLogRatio, forbiddenLogRatio,
    forbiddenMaxRowSum_eq_forbiddenWordCount]

/-- Exact matrix-power approximation: `log R_v(r) / r` converges to `h(v)`. -/
theorem forbiddenMaxRowLogRatio_tendsto_entropy {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) :
    Tendsto (forbiddenMaxRowLogRatio hell v) atTop
      (𝓝 (forbiddenEntropy v)) := by
  have hfun : forbiddenMaxRowLogRatio hell v = forbiddenLogRatio v := by
    funext r
    exact forbiddenMaxRowLogRatio_eq_forbiddenLogRatio hell v r
  rw [hfun]
  exact forbiddenLogRatio_tendsto_entropy v hell

/-- Infimum characterization of `h(v)` by positive matrix powers. -/
theorem forbiddenEntropy_eq_iInf_maxRowLogRatio {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) :
    forbiddenEntropy v =
      ⨅ r : PositiveLength, forbiddenMaxRowLogRatio hell v r := by
  rw [forbiddenEntropy_eq_iInf]
  congr 1
  funext r
  exact (forbiddenMaxRowLogRatio_eq_forbiddenLogRatio hell v r).symm

theorem forbiddenEntropy_le_maxRowLogRatio {ell : ℕ}
    (hell : 0 < ell) (v : DecimalWord ell) {r : ℕ} (hr : 0 < r) :
    forbiddenEntropy v ≤ forbiddenMaxRowLogRatio hell v r := by
  rw [forbiddenMaxRowLogRatio_eq_forbiddenLogRatio]
  exact forbiddenEntropy_le_ratio v hell hr

/-- Necessary-only T16 transfer. Literal failure of canonical C1 gives the
T15 finite-prefix scales together with the asymptotically complete hierarchy
of exact finite matrix-power bounds. No failure or truth of C1 is asserted. -/
theorem not_piPositiveLowerBlockDensity_implies_matrixPowerFinitePrefixBounds
    (hnot : ¬PiPositiveLowerBlockDensity) :
    ∃ ell : ℕ, ∃ hell : 0 < ell, ∃ v : DecimalWord ell,
      ∃ cutoffs scales : ℕ → ℕ,
        StrictMono cutoffs ∧ StrictMono scales ∧ Tendsto scales atTop atTop ∧
        (∀ j, 2 * scales j ≤ cutoffs j) ∧
        Tendsto (containmentRatio cutoffs scales) atTop (𝓝 0) ∧
        Tendsto (occurrenceContamination v cutoffs scales) atTop (𝓝 0) ∧
        limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
          forbiddenEntropy v ∧
        forbiddenEntropy v < Real.log 10 ∧
        Tendsto (forbiddenMaxRowLogRatio hell v) atTop
          (𝓝 (forbiddenEntropy v)) ∧
        forbiddenEntropy v =
          ⨅ r : PositiveLength, forbiddenMaxRowLogRatio hell v r ∧
        (∀ r : ℕ, 0 < r →
          limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
            forbiddenMaxRowLogRatio hell v r) ∧
        ∀ r : ℕ,
          (forbiddenTransitionMatrix hell v ^ r) *ᵥ
              (1 : PrefixState ell hell → ℕ) ≤
            fun _ => forbiddenMaxRowSum hell v r * 1 := by
  obtain ⟨ell, hell, v, cutoffs, scales, hcutoffs, hscales, hscalesTop,
      hroom, hcontainment, hcontamination, hlimsup, hstrict, _hcertificate⟩ :=
    T15.not_piPositiveLowerBlockDensity_implies_intrinsicFinitePrefixEntropy hnot
  refine ⟨ell, hell, v, cutoffs, scales, hcutoffs, hscales, hscalesTop,
    hroom, hcontainment, hcontamination, hlimsup, hstrict,
    forbiddenMaxRowLogRatio_tendsto_entropy hell v,
    forbiddenEntropy_eq_iInf_maxRowLogRatio hell v, ?_, ?_⟩
  · intro r hr
    exact hlimsup.trans (forbiddenEntropy_le_maxRowLogRatio hell v hr)
  · exact matrixPower_mulVec_one_le_maxRowSum hell v

end Theory.PiDigits.PositiveLowerBlockDensity.T16

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T16.forbiddenMaxRowSum_pos
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T16.forbiddenMaxRowSum_submultiplicative
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T16.arbitraryState_rowSum_le_forbiddenWordCount
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T16.forbiddenMaxRowLogRatio_tendsto_entropy
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T16.forbiddenEntropy_eq_iInf_maxRowLogRatio
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T16.matrixPower_mulVec_one_le_maxRowSum
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T16.not_piPositiveLowerBlockDensity_implies_matrixPowerFinitePrefixBounds
