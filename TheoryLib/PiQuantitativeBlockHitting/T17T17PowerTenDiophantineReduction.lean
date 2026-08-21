import TheoryLib.PiQuantitativeBlockHitting.T14T14BoundaryRobustFejerDichotomy
import TheoryLib.PiQuantitativeBlockHitting.T16T16DecimalBoundaryWordObstruction

/-!
# T17: power-of-ten Diophantine reduction

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file is conditional.  In particular, it does not assert that `Real.pi`
satisfies `PowerTenDiophantine`, and it proves neither `C1` nor `¬ C1`.
The literature result recorded in T9 is motivation only and is not imported
as a kernel-checked premise.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.PowerTenDiophantineReduction

open Theory.PiDigits.BoundaryRobustFejerDichotomy
open Theory.PiDigits.DecimalBoundaryWordObstruction
open Theory.PiDigits.QuantitativeBlockHitting

/-- A lower bound restricted to rational approximations whose denominator is
exactly a power of ten.  `A` is a threshold on the exponent, not on the
denominator itself. -/
def PowerTenDiophantine (x : ℝ) (mu A : ℕ) : Prop :=
  ∀ t : ℕ, A ≤ t → ∀ p : ℤ,
    1 / (10 : ℝ) ^ (mu * t) ≤ |x - (p : ℝ) / (10 : ℝ) ^ t|

/-- T20's digit-shift identity in the exact T27 pi-orbit notation. -/
theorem piFractionalOrbit_digit (t i : ℕ) :
    Real.digits (Theory.PiDigits.T27.piFractionalOrbit t) 10 i =
      Theory.PiDigits.piDigit (t + i) := by
  simpa only [Theory.PiDigits.T20.decimalDigit,
    Theory.PiDigits.T20.baseTenOrbit,
    Theory.PiDigits.T27.piFractionalOrbit] using
    (Theory.PiDigits.T20.decimalDigit_baseTenOrbit
      Real.pi Real.pi_pos.le t i).trans
        (Theory.PiDigits.T20.decimalDigit_pi (t + i))

/-- A run of `r` zero digits beginning at position `t` gives the corresponding
power-of-ten rational approximation to pi. -/
theorem zero_run_gives_powerTen_approximation {t r : ℕ}
    (hzero : ∀ i < r, Theory.PiDigits.piDigit (t + i) = (0 : Fin 10)) :
    ∃ p : ℤ,
      |Real.pi - (p : ℝ) / (10 : ℝ) ^ t| ≤
        1 / (10 : ℝ) ^ (t + r) := by
  let y : ℝ := Theory.PiDigits.T27.piFractionalOrbit t
  let p : ℤ := ⌊(10 : ℝ) ^ t * Real.pi⌋
  have hy : y ∈ Set.Ico (0 : ℝ) 1 :=
    Theory.PiDigits.T27.piFractionalOrbit_mem_Ico t
  have hprefix : ∀ i < r,
      Real.digits y 10 i = (fun _ : ℕ => (0 : Fin 10)) i := by
    intro i hi
    simpa only [y, piFractionalOrbit_digit] using hzero i hi
  have hclose := Real.abs_ofDigits_sub_ofDigits_le hprefix
  rw [Real.ofDigits_digits (by norm_num : 1 < 10) hy] at hclose
  have hzeroValue : Real.ofDigits (fun _ : ℕ => (0 : Fin 10)) = 0 := by
    simp [Real.ofDigits, Real.ofDigitsTerm]
  rw [hzeroValue, sub_zero] at hclose
  have hfract : y = (10 : ℝ) ^ t * Real.pi - (p : ℝ) := by
    simp only [y, Theory.PiDigits.T27.piFractionalOrbit, Int.fract, p]
  refine ⟨p, ?_⟩
  have htpos : (0 : ℝ) < (10 : ℝ) ^ t := by positivity
  have heq : Real.pi - (p : ℝ) / (10 : ℝ) ^ t = y / (10 : ℝ) ^ t := by
    rw [hfract]
    field_simp
  rw [heq, abs_div, abs_of_pos htpos]
  calc
    |y| / (10 : ℝ) ^ t ≤ ((10 : ℝ) ^ r)⁻¹ / (10 : ℝ) ^ t :=
      div_le_div_of_nonneg_right hclose htpos.le
    _ = 1 / (10 : ℝ) ^ (t + r) := by
      rw [pow_add]
      field_simp

/-- A run of `r` nine digits beginning at position `t` gives the rational
approximation from the other side of the decimal boundary. -/
theorem nine_run_gives_powerTen_approximation {t r : ℕ}
    (hnine : ∀ i < r, Theory.PiDigits.piDigit (t + i) = (9 : Fin 10)) :
    ∃ p : ℤ,
      |Real.pi - (p : ℝ) / (10 : ℝ) ^ t| ≤
        1 / (10 : ℝ) ^ (t + r) := by
  let y : ℝ := Theory.PiDigits.T27.piFractionalOrbit t
  let p : ℤ := ⌊(10 : ℝ) ^ t * Real.pi⌋ + 1
  have hy : y ∈ Set.Ico (0 : ℝ) 1 :=
    Theory.PiDigits.T27.piFractionalOrbit_mem_Ico t
  have hprefix : ∀ i < r,
      Real.digits y 10 i = (fun _ : ℕ => (9 : Fin 10)) i := by
    intro i hi
    simpa only [y, piFractionalOrbit_digit] using hnine i hi
  have hclose := Real.abs_ofDigits_sub_ofDigits_le hprefix
  rw [Real.ofDigits_digits (by norm_num : 1 < 10) hy] at hclose
  have hnineValue : Real.ofDigits (fun _ : ℕ => (9 : Fin 10)) = 1 := by
    simpa only [Fin.last] using Real.ofDigits_const_last_eq_one 9
  rw [hnineValue] at hclose
  have hfract : y =
      (10 : ℝ) ^ t * Real.pi - ((⌊(10 : ℝ) ^ t * Real.pi⌋ : ℤ) : ℝ) := by
    simp only [y, Theory.PiDigits.T27.piFractionalOrbit, Int.fract]
  refine ⟨p, ?_⟩
  have htpos : (0 : ℝ) < (10 : ℝ) ^ t := by positivity
  have heq : Real.pi - (p : ℝ) / (10 : ℝ) ^ t = (y - 1) / (10 : ℝ) ^ t := by
    dsimp only [p]
    push_cast
    rw [hfract]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos htpos]
  calc
    |y - 1| / (10 : ℝ) ^ t ≤ ((10 : ℝ) ^ r)⁻¹ / (10 : ℝ) ^ t :=
      div_le_div_of_nonneg_right hclose htpos.le
    _ = 1 / (10 : ℝ) ^ (t + r) := by
      rw [pow_add]
      field_simp

/-- Occurrence at one indexed start, using exactly T16's digit convention. -/
def PiWordOccursAt (v : List (Fin 10)) (n : ℕ) : Prop :=
  ∀ i : ℕ, ∀ hi : i < v.length,
    Theory.PiDigits.piDigit (n + i) = v.get ⟨i, hi⟩

/-- An appended constant suffix is a digit run beginning immediately after
the prefix. -/
theorem occurrence_append_replicate_gives_run
    {u : List (Fin 10)} {d : Fin 10} {n r : ℕ}
    (hocc : PiWordOccursAt (u ++ List.replicate r d) n) :
    ∀ i < r, Theory.PiDigits.piDigit (n + u.length + i) = d := by
  intro i hi
  have hindex : u.length + i < (u ++ List.replicate r d).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  have h := hocc (u.length + i) hindex
  rw [List.get_eq_getElem,
    List.getElem_append_right (by omega : u.length ≤ u.length + i)] at h
  simpa only [Nat.add_assoc, Nat.add_sub_cancel_left,
    List.getElem_replicate] using h

/-- The explicit suffix length used below is longer than the Diophantine
exponent loss at every exponent `t ≤ D`. -/
theorem diophantine_suffix_exponent_lt
    {mu t D : ℕ} (hmu : 1 ≤ mu) (htD : t ≤ D) :
    mu * t < t + ((mu - 1) * D + 1) := by
  have hmul : (mu - 1) * t ≤ (mu - 1) * D :=
    Nat.mul_le_mul_left (mu - 1) htD
  have hmuEq : mu = (mu - 1) + 1 := by omega
  calc
    mu * t = ((mu - 1) + 1) * t := congrArg (fun z : ℕ => z * t) hmuEq
    _ = (mu - 1) * t + t := by rw [Nat.add_mul, one_mul]
    _ ≤ (mu - 1) * D + t := Nat.add_le_add_right hmul t
    _ < t + ((mu - 1) * D + 1) := by omega

/-- Under the stated predicate, the explicit suffix cannot be all zeroes at
any exponent between `A` and `D`. -/
theorem powerTenDiophantine_excludes_zero_run
    {mu A t D : ℕ} (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A)
    (hAt : A ≤ t) (htD : t ≤ D) :
    ¬ ∀ i < (mu - 1) * D + 1,
      Theory.PiDigits.piDigit (t + i) = (0 : Fin 10) := by
  intro hzero
  obtain ⟨p, hupper⟩ := zero_run_gives_powerTen_approximation hzero
  have hlower := hpi t hAt p
  have hexp := diophantine_suffix_exponent_lt hmu htD
  have hstrict :
      1 / (10 : ℝ) ^ (t + ((mu - 1) * D + 1)) <
        1 / (10 : ℝ) ^ (mu * t) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 10) hexp
  linarith

/-- Under the stated predicate, the explicit suffix cannot be all nines at
any exponent between `A` and `D`. -/
theorem powerTenDiophantine_excludes_nine_run
    {mu A t D : ℕ} (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A)
    (hAt : A ≤ t) (htD : t ≤ D) :
    ¬ ∀ i < (mu - 1) * D + 1,
      Theory.PiDigits.piDigit (t + i) = (9 : Fin 10) := by
  intro hnine
  obtain ⟨p, hupper⟩ := nine_run_gives_powerTen_approximation hnine
  have hlower := hpi t hAt p
  have hexp := diophantine_suffix_exponent_lt hmu htD
  have hstrict :
      1 / (10 : ℝ) ^ (t + ((mu - 1) * D + 1)) <
        1 / (10 : ℝ) ^ (mu * t) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 10) hexp
  linarith

/-- No word with the explicit zero suffix occurs at a start whose length-`k`
prefix is fully contained by `D`. -/
theorem powerTenDiophantine_excludes_zero_suffix
    {mu A D k n : ℕ} {u : List (Fin 10)}
    (hmu : 1 ≤ mu) (hpi : PowerTenDiophantine Real.pi mu A)
    (hu : u.length = k) (hAk : A ≤ k) (hnD : n + k ≤ D) :
    ¬ PiWordOccursAt
      (u ++ List.replicate ((mu - 1) * D + 1) (0 : Fin 10)) n := by
  intro hocc
  apply powerTenDiophantine_excludes_zero_run hmu hpi
    (hAk.trans (Nat.le_add_left k n)) hnD
  simpa only [hu, Nat.add_comm] using
    occurrence_append_replicate_gives_run hocc

/-- No word with the explicit nine suffix occurs at a start whose length-`k`
prefix is fully contained by `D`. -/
theorem powerTenDiophantine_excludes_nine_suffix
    {mu A D k n : ℕ} {u : List (Fin 10)}
    (hmu : 1 ≤ mu) (hpi : PowerTenDiophantine Real.pi mu A)
    (hu : u.length = k) (hAk : A ≤ k) (hnD : n + k ≤ D) :
    ¬ PiWordOccursAt
      (u ++ List.replicate ((mu - 1) * D + 1) (9 : Fin 10)) n := by
  intro hocc
  apply powerTenDiophantine_excludes_nine_run hmu hpi
    (hAk.trans (Nat.le_add_left k n)) hnD
  simpa only [hu, Nat.add_comm] using
    occurrence_append_replicate_gives_run hocc

/-- Both exterior words from T16 are excluded uniformly at every admissible
start.  T16's carry audit makes the zero/nine suffixes explicit, including the
all-nine predecessor and all-zero successor wrap cases. -/
theorem powerTenDiophantine_excludes_adjacent_words
    {mu A D k a : ℕ} (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A)
    (hk : 0 < k) (ha : a < 10 ^ k) (hAk : A ≤ k) :
    let r : ℕ := (mu - 1) * D + 1
    ∀ n : ℕ, n + k ≤ D →
      ¬ PiWordOccursAt
          (fixedWord (k + r)
            (predecessorLabel (10 ^ k) (10 ^ r) a)) n ∧
        ¬ PiWordOccursAt
          (fixedWord (k + r)
            (successorLabel (10 ^ k) (10 ^ r) a)) n := by
  dsimp only
  let r : ℕ := (mu - 1) * D + 1
  have hr : 0 < r := by dsimp only [r]; omega
  obtain ⟨_hL, _hR, hPpos, hPzero, hSordinary, hSwrap, _hQ⟩ :=
    boundaryWords_complete_carry_audit (k := k) (r := r) (a := a) hk hr ha
  intro n hnD
  constructor
  · by_cases ha0 : a = 0
    · rw [hPzero ha0, List.replicate_add]
      exact powerTenDiophantine_excludes_nine_suffix hmu hpi
        (by simp) hAk hnD
    · rw [hPpos (Nat.pos_of_ne_zero ha0)]
      exact powerTenDiophantine_excludes_nine_suffix hmu hpi
        (fixedWord_length ((Nat.sub_le a 1).trans_lt ha)) hAk hnD
  · by_cases hasucc : a + 1 < 10 ^ k
    · rw [hSordinary hasucc]
      exact powerTenDiophantine_excludes_zero_suffix hmu hpi
        (fixedWord_length hasucc) hAk hnD
    · have heq : a + 1 = 10 ^ k := by omega
      rw [hSwrap heq, List.replicate_add]
      exact powerTenDiophantine_excludes_zero_suffix hmu hpi
        (by simp) hAk hnD

/-- T16's indexed occurrence count is zero when every indexed start is
excluded. -/
theorem piWordOccurrenceCount_eq_zero_of_forall_not_occursAt
    {v : List (Fin 10)} {N : ℕ}
    (hnone : ∀ n < N, ¬ PiWordOccursAt v n) :
    piWordOccurrenceCount v N = 0 := by
  classical
  unfold piWordOccurrenceCount
  rw [Finset.card_filter_eq_zero_iff]
  intro n hn hocc
  apply hnone n (Finset.mem_range.mp hn)
  exact hocc

/-- At the exact full-containment start count `N=D-k+1`, both T16 adjacent
word counts vanish for the explicit suffix length. -/
theorem adjacentWordCounts_eq_zero_at_exact_deadline
    {mu A D k a : ℕ} (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A)
    (hk : 0 < k) (ha : a < 10 ^ k) (hAk : A ≤ k) (hkD : k ≤ D) :
    let r : ℕ := (mu - 1) * D + 1
    let N : ℕ := D - k + 1
    piWordOccurrenceCount
          (fixedWord (k + r)
            (predecessorLabel (10 ^ k) (10 ^ r) a)) N = 0 ∧
      piWordOccurrenceCount
          (fixedWord (k + r)
            (successorLabel (10 ^ k) (10 ^ r) a)) N = 0 := by
  dsimp only
  have hnone := powerTenDiophantine_excludes_adjacent_words
    (D := D) hmu hpi hk ha hAk
  constructor
  · apply piWordOccurrenceCount_eq_zero_of_forall_not_occursAt
    intro n hn
    exact (hnone n (by omega)).1
  · apply piWordOccurrenceCount_eq_zero_of_forall_not_occursAt
    intro n hn
    exact (hnone n (by omega)).2

/-- The Diophantine hypothesis removes T14's boundary branch at the exact
deadline, by combining the zero adjacent counts above with T16's quantitative
boundary-to-word theorem. -/
theorem powerTenDiophantine_excludes_boundary_branch_at_exact_deadline
    {mu A D k a : ℕ} (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A)
    (hk : 0 < k) (ha : a < 10 ^ k) (hAk : A ≤ k)
    (hkD : k ≤ D)
    (hempty : cylinderCount Theory.PiDigits.T27.piFractionalOrbit
      (D - k + 1) (10 ^ k) a = 0) :
    let r : ℕ := (mu - 1) * D + 1
    ¬ ((D - k + 1 : ℕ) : ℝ) / (4 * (10 ^ k : ℕ)) ≤
      twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit
        (D - k + 1) (10 ^ k) a
        (1 / ((10 ^ (k + r) : ℕ) : ℝ)) := by
  dsimp only
  intro hboundary
  have hcounts := adjacentWordCounts_eq_zero_at_exact_deadline
    (D := D) hmu hpi hk ha hAk hkD
  have hadjacent := boundary_branch_forces_adjacent_word
    (N := D - k + 1) (k := k) (r := (mu - 1) * D + 1) (a := a)
    hk (by omega) ha hempty hboundary
  rw [hcounts.1, hcounts.2] at hadjacent
  have hN : 0 < D - k + 1 := by omega
  have hceil : 0 < Nat.ceil
      (((D - k + 1 : ℕ) : ℝ) / (8 * (10 ^ k : ℕ))) := by
    rw [Nat.ceil_pos]
    positivity
  have hzero : Nat.ceil
      (((D - k + 1 : ℕ) : ℝ) / (8 * (10 ^ k : ℕ))) ≤ 0 := by
    simpa only [max_eq_left (Nat.zero_le 0)] using hadjacent
  omega

/-- Conditional G11 conclusion.  If pi satisfies the displayed power-of-ten
Diophantine predicate, literal failure of C1 forces T14's aggregated
signed-frequency resonance at unbounded exact full-containment deadlines.
All arithmetic parameters and the eliminated T16 adjacent words remain
visible in the theorem type. -/
theorem not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine
    (mu A : ℕ) (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A) (hnotC1 : ¬ C1) :
    ∀ C K : ℕ, 1 ≤ C → 1 ≤ K →
      ∃ k : ℕ, K ≤ k ∧ A ≤ k ∧ 1 ≤ k ∧
        ∃ w : DecimalWord k,
          let q : ℕ := 10 ^ k
          let D : ℕ := C * k * q
          let N : ℕ := D - k + 1
          let a : ℕ := Theory.PiDigits.T20.wordValue (List.ofFn w)
          let r : ℕ := (mu - 1) * D + 1
          let M : ℕ := 2 * 10 ^ (2 * k + r)
          a < q ∧
          (¬ ∃ n : ℕ, n + k ≤ D ∧
            ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
          cylinderCount Theory.PiDigits.T27.piFractionalOrbit N q a = 0 ∧
          (∀ n : ℕ, n + k ≤ D →
            ¬ PiWordOccursAt
                (fixedWord (k + r)
                  (predecessorLabel q (10 ^ r) a)) n ∧
              ¬ PiWordOccursAt
                (fixedWord (k + r)
                  (successorLabel q (10 ^ r) a)) n) ∧
          piWordOccurrenceCount
              (fixedWord (k + r)
                (predecessorLabel q (10 ^ r) a)) N = 0 ∧
          piWordOccurrenceCount
              (fixedWord (k + r)
                (successorLabel q (10 ^ r) a)) N = 0 ∧
          2 * 10 ^ (2 * k + r) ≤ M + 1 ∧
          (N : ℝ) / (2 * q) ≤
            aggregatedFourierSum Theory.PiDigits.T27.piFractionalOrbit
              N q M := by
  intro C K hC hK
  have hmax : 1 ≤ max K A := hK.trans (le_max_left K A)
  obtain ⟨k, hmaxk, hk, w, hrest⟩ :=
    not_C1_implies_unbounded_boundary_or_aggregated_resonance
      hnotC1 C (max K A) hC hmax
  have hKk : K ≤ k := (le_max_left K A).trans hmaxk
  have hAk : A ≤ k := (le_max_right K A).trans hmaxk
  refine ⟨k, hKk, hAk, hk, w, ?_⟩
  dsimp only at hrest ⊢
  rcases hrest with ⟨ha, hmissing, hempty, hall⟩
  let D : ℕ := C * k * 10 ^ k
  let N : ℕ := D - k + 1
  let a : ℕ := Theory.PiDigits.T20.wordValue (List.ofFn w)
  let r : ℕ := (mu - 1) * D + 1
  let M : ℕ := 2 * 10 ^ (2 * k + r)
  have hkD : k ≤ D := by
    dsimp only [D]
    calc
      k = 1 * k * 1 := by omega
      _ ≤ C * k * 10 ^ k :=
        Nat.mul_le_mul (Nat.mul_le_mul hC le_rfl)
          (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
  have hpoint := powerTenDiophantine_excludes_adjacent_words
    (D := D) hmu hpi hk ha hAk
  have hcounts := adjacentWordCounts_eq_zero_at_exact_deadline
    (D := D) hmu hpi hk ha hAk hkD
  have hr : 0 < r := by dsimp only [r]; omega
  have hcut : 2 * 10 ^ (2 * k + r) ≤ M + 1 := by
    dsimp only [M]
    omega
  obtain ⟨hdelta, hdeltaq, hMdelta⟩ :=
    decimal_width_t14_hypotheses (k := k) (r := r) (M := M)
      hk hr hcut
  have hfourier : (N : ℝ) / (2 * (10 ^ k : ℕ)) ≤
      aggregatedFourierSum Theory.PiDigits.T27.piFractionalOrbit
        N (10 ^ k) M := by
    have hall' := hall
      (1 / ((10 ^ (k + r) : ℕ) : ℝ)) M hdelta hdeltaq hMdelta
    rcases hall' with hboundary | hresonance
    · exfalso
      apply powerTenDiophantine_excludes_boundary_branch_at_exact_deadline
        (D := D) hmu hpi hk ha hAk hkD
      · simpa only [N, D, a] using hempty
      · exact hboundary
    · simpa only [N, D, M] using hresonance
  refine ⟨ha, hmissing, hempty, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [D, r, a] using hpoint
  · simpa only [N, D, r, a] using hcounts.1
  · simpa only [N, D, r, a] using hcounts.2
  · simpa only [r, M] using hcut
  · simpa only [N, D, M] using hfourier

#print axioms zero_run_gives_powerTen_approximation
#print axioms nine_run_gives_powerTen_approximation
#print axioms powerTenDiophantine_excludes_adjacent_words
#print axioms adjacentWordCounts_eq_zero_at_exact_deadline
#print axioms powerTenDiophantine_excludes_boundary_branch_at_exact_deadline
#print axioms not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine

end Theory.PiDigits.PowerTenDiophantineReduction
