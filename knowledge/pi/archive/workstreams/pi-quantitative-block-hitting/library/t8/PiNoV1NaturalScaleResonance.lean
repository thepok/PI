import TheoryLib.PiQuantitativeBlockHitting.T1PiQuantitativeBlockHitting
import TheoryLib.PiQuantitativeBlockHitting.T6PiNaturalScaleResonanceObstruction

/-!
# Natural-scale resonance from failure of C1, without a V1 alternative

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

The results below are necessary conditions only. No converse is proved, and
they neither prove nor refute C1. The final theorem assumes the literal
negation of C1 and has no V1 hypothesis, conclusion, or failure disjunct.
-/

noncomputable section

namespace Theory.PiDigits.PiNoV1NaturalScaleResonance

open DecimalFactorComplexity

/-- A globally absent word over a nonempty finite alphabet has a globally
absent extension at every greater length. The extension is by an arbitrary
fixed alphabet symbol; any occurrence of it would contain the original word
as its prefix. -/
theorem exists_absent_extension
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (x : ℕ → α) {m k : ℕ} (u : Block α m) (hmk : m ≤ k)
    (hu : ¬ ∃ n : ℕ, OccursAt x u n) :
    ∃ w : Block α k, ¬ ∃ n : ℕ, OccursAt x w n := by
  classical
  let a : α := Classical.choice inferInstance
  let w : Block α k := fun j =>
    if hj : j.val < m then u ⟨j.val, hj⟩ else a
  refine ⟨w, ?_⟩
  rintro ⟨n, hn⟩
  apply hu
  refine ⟨n, ?_⟩
  intro j
  have hj := hn (Fin.castLE hmk j)
  simpa only [w, Fin.val_castLE, dif_pos j.isLt] using hj

/-- List-oriented form of `exists_absent_extension`, matching the canonical
V1 occurrence convention and returning the digit-equality orientation used by
the quantitative full-containment theorem. -/
theorem exists_absent_extension_of_missing_list
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (x : ℕ → α) (s : List α)
    (hs : ¬ ∃ n : ℕ, ∀ i : ℕ, ∀ hi : i < s.length,
      x (n + i) = s.get ⟨i, hi⟩)
    {k : ℕ} (hsk : s.length ≤ k) :
    ∃ w : Block α k, ¬ ∃ n : ℕ, ∀ j : Fin k, x (n + j) = w j := by
  let u : Block α s.length := fun j => s.get j
  have hu : ¬ ∃ n : ℕ, OccursAt x u n := by
    rintro ⟨n, hn⟩
    apply hs
    refine ⟨n, ?_⟩
    intro i hi
    exact (hn ⟨i, hi⟩).symm
  obtain ⟨w, hw⟩ := exists_absent_extension x u hsk hu
  refine ⟨w, ?_⟩
  rintro ⟨n, hn⟩
  apply hw
  exact ⟨n, fun j => (hn j).symm⟩

/-- **Necessary-only obstruction; no converse is asserted.**

Literal failure of T1's C1 forces bad lengths beyond every positive threshold
and natural-scale resonance at the exact number of starts admitted by the
full-containment deadline. The theorem type contains no V1 case split. It
neither proves nor refutes C1. -/
theorem not_C1_implies_unbounded_naturalScale_resonance
    (hnotC1 : ¬ Theory.PiDigits.QuantitativeBlockHitting.C1) :
    ∀ C K : ℕ, 1 ≤ C → 1 ≤ K →
      ∃ k : ℕ, K ≤ k ∧
        ∃ w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k,
        (¬ ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
          ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
        ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 128 * 10 ^ k ∧
          1 / (16388 * (k + 1 : ℝ) * (10 : ℝ) ^ k) ≤
            ‖Theory.PiDigits.T27.exponentialSum
              Theory.PiDigits.T27.piFractionalOrbit
              (C * k * 10 ^ k - k + 1) h‖ /
                ((C * k * 10 ^ k - k + 1 : ℕ) : ℝ) := by
  classical
  by_cases hV1 : Theory.PiDigits.V1
  · rcases
      Theory.PiDigits.PiNaturalScaleResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_naturalScale_resonance
        hnotC1 with hfailure | hresonance
    · exact False.elim (hfailure hV1)
    · exact hresonance.2
  · have hmissingList : ∃ s : List (Fin 10),
        ¬ ∃ n : ℕ, ∀ i : ℕ, ∀ hi : i < s.length,
          Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩ := by
      by_contra hnone
      apply hV1
      intro s
      by_contra hs
      exact hnone ⟨s, hs⟩
    obtain ⟨s, hs⟩ := hmissingList
    intro C K hC hK
    let k := max K s.length
    have hKk : K ≤ k := by exact Nat.le_max_left _ _
    have hsk : s.length ≤ k := by exact Nat.le_max_right _ _
    obtain ⟨w, hw⟩ :=
      exists_absent_extension_of_missing_list
        Theory.PiDigits.piDigit s hs hsk
    have hmissing : ¬ ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
        ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j := by
      rintro ⟨n, _, hn⟩
      exact hw ⟨n, hn⟩
    obtain ⟨h, hzero, hbound, hlarge⟩ :=
      Theory.PiDigits.PiNaturalScaleResonanceObstruction.normalized_piOrbit_naturalScale_resonance_of_missing_fullContainment
        C k hC w hmissing
    refine ⟨k, hKk, w, hmissing, h, hzero, hbound, ?_⟩
    have hkR : (1 : ℝ) ≤ k + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    calc
      1 / (16388 * (k + 1 : ℝ) * (10 : ℝ) ^ k) ≤
          1 / (16388 * (10 : ℝ) ^ k) := by
            apply one_div_le_one_div_of_le
            · positivity
            · nlinarith [mul_le_mul_of_nonneg_right hkR
                (show (0 : ℝ) ≤ 16388 * (10 : ℝ) ^ k by positivity)]
      _ ≤ _ := hlarge

#print axioms exists_absent_extension
#print axioms exists_absent_extension_of_missing_list
#print axioms not_C1_implies_unbounded_naturalScale_resonance

end Theory.PiDigits.PiNoV1NaturalScaleResonance
