import TheoryLib.PiQuantitativeBlockHitting.T20T20DigitChangeFourierDefect
import TheoryLib.PiDigits.T11PiDigitFactorComplexity

/-!
# T21: aperiodicity forces an unbounded additive first-frequency gap

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file combines T20's digit-change Fourier-defect estimate with the
machine-checked non-eventual-periodicity of the decimal digit stream of pi.
The conclusion is only an unbounded *additive* gap from the trivial bound for
the first Fourier sum.  It gives no relative cancellation estimate and proves
neither decimal normality nor disjunctivity.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.UnboundedFourierGap

open Theory.PiDigits.DigitChangeFourierDefect

/-- A sequence with a uniform finite bound on all prefix change counts has an
eventually constant tail. -/
theorem exists_eventuallyConstant_of_changeCount_bounded
    {α : Type*} [DecidableEq α] (s : ℕ → α) (B : ℕ)
    (hbound : ∀ N : ℕ, Theory.PiDigits.T18.changeCount s N ≤ B) :
    ∃ A : ℕ, ∀ k : ℕ, s (A + k) = s A := by
  classical
  let C : Set ℕ := {j | s j ≠ s (j + 1)}
  have hCfinite : C.Finite := by
    by_contra hnot
    have hCinfinite : C.Infinite := hnot
    obtain ⟨t, htC, htcard⟩ :=
      hCinfinite.exists_subset_card_eq (B + 1)
    have htne : t.Nonempty := Finset.card_pos.mp (by omega)
    let N : ℕ := t.max' htne + 2
    have hsubset : t ⊆ Theory.PiDigits.T18.changePositions s N := by
      intro j hj
      have hjmax : j ≤ t.max' htne := Finset.le_max' t j hj
      have hjchange : s j ≠ s (j + 1) := htC hj
      simp only [Theory.PiDigits.T18.changePositions, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨by simp only [N]; omega, hjchange⟩
    have hcardle := Finset.card_le_card hsubset
    have hprefix : Theory.PiDigits.T18.changeCount s N ≤ B := hbound N
    have hprefix' :
        (Theory.PiDigits.T18.changePositions s N).card ≤ B := by
      simpa only [Theory.PiDigits.T18.changeCount] using hprefix
    rw [htcard] at hcardle
    omega
  obtain ⟨A, hA⟩ := hCfinite.bddAbove
  let start : ℕ := A + 1
  have hsame : ∀ j : ℕ, start ≤ j → s (j + 1) = s j := by
    intro j hj
    by_contra hne
    have hjC : j ∈ C := by
      simp only [C, Set.mem_setOf_eq]
      exact Ne.symm hne
    have hjA : j ≤ A := hA hjC
    simp only [start] at hj
    omega
  refine ⟨start, ?_⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        s (start + (k + 1)) = s ((start + k) + 1) := by simp [Nat.add_assoc]
        _ = s (start + k) := hsame (start + k) (by omega)
        _ = s start := ih

/-- Bounded prefix change counts imply eventual periodicity, with period one
on the constant tail. -/
theorem eventuallyPeriodic_of_changeCount_bounded
    {α : Type*} [DecidableEq α] (s : ℕ → α) (B : ℕ)
    (hbound : ∀ N : ℕ, Theory.PiDigits.T18.changeCount s N ≤ B) :
    DecimalFactorComplexity.EventuallyPeriodic s := by
  obtain ⟨A, htail⟩ :=
    exists_eventuallyConstant_of_changeCount_bounded s B hbound
  refine ⟨A, 1, by omega, ?_⟩
  intro i
  rw [show A + i + 1 = A + (i + 1) by omega, htail (i + 1), htail i]

/-- Prefix change count is monotone in the prefix length. -/
theorem changeCount_mono {α : Type*} [DecidableEq α] (s : ℕ → α) :
    Monotone (Theory.PiDigits.T18.changeCount s) := by
  intro M N hMN
  unfold Theory.PiDigits.T18.changeCount Theory.PiDigits.T18.changePositions
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

/-- The exact decimal digit stream of pi has unbounded prefix change count.
The strict form is convenient for subsequent cofinality arguments. -/
theorem pi_changeCount_unbounded (B : ℕ) :
    ∃ N : ℕ, B < Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N := by
  by_contra hnot
  push Not at hnot
  exact Theory.PiDigits.FactorComplexity.piDigit_not_eventuallyPeriodic
    (eventuallyPeriodic_of_changeCount_bounded Theory.PiDigits.piDigit B hnot)

/-- Trivial triangle-inequality bound for a finite unit-modulus phase sum. -/
lemma norm_exponentialSum_le (x : ℕ → ℝ) (N : ℕ) (h : ℤ) :
    ‖Theory.PiDigits.T27.exponentialSum x N h‖ ≤ (N : ℝ) := by
  unfold Theory.PiDigits.T27.exponentialSum
  calc
    ‖∑ j ∈ Finset.range N, Theory.PiDigits.T27.phase h (x j)‖ ≤
        ∑ j ∈ Finset.range N, ‖Theory.PiDigits.T27.phase h (x j)‖ :=
      norm_sum_le _ _
    _ = (N : ℝ) := by simp [Theory.PiDigits.T27.norm_phase]

/-- Pointwise additive spectral gap forced by the changed digits in the same
prefix.  The constant is the rational T20 constant after factoring the
difference of squares and applying the trivial norm bound. -/
theorem pi_firstFrequency_additiveGap_ge_digitChanges (N : ℕ) :
    (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) / 5000 ≤
      (N : ℝ) -
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N 1‖ := by
  cases N with
  | zero =>
      simp [Theory.PiDigits.T18.changeCount,
        Theory.PiDigits.T18.changePositions,
        Theory.PiDigits.T27.exponentialSum]
  | succ n =>
      let N : ℕ := n + 1
      let R : ℝ := ‖Theory.PiDigits.T27.exponentialSum
        Theory.PiDigits.T27.piFractionalOrbit N 1‖
      let C : ℝ :=
        (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ)
      have hN : (0 : ℝ) < N := by positivity
      have hRnonneg : 0 ≤ R := norm_nonneg _
      have hR : R ≤ (N : ℝ) := by
        exact norm_exponentialSum_le
          Theory.PiDigits.T27.piFractionalOrbit N 1
      have hdefect :=
        pi_firstFrequency_defect_ge_digitChanges N
      change C / 5000 ≤ (N : ℝ) - R
      change (N : ℝ) * C / 2500 ≤ (N : ℝ) ^ 2 - R ^ 2 at hdefect
      have hfactor : (N : ℝ) ^ 2 - R ^ 2 =
          ((N : ℝ) - R) * ((N : ℝ) + R) := by ring
      have hgap : 0 ≤ (N : ℝ) - R := sub_nonneg.mpr hR
      have hsum : (N : ℝ) + R ≤ 2 * N := by linarith
      have hupper : (N : ℝ) ^ 2 - R ^ 2 ≤
          2 * N * ((N : ℝ) - R) := by
        rw [hfactor]
        nlinarith
      nlinarith

/-- The additive gap between the trivial bound `N` and the first-frequency
pi-orbit sum exceeds every natural threshold along some prefix. -/
theorem pi_firstFrequency_additiveGap_unbounded (B : ℕ) :
    ∃ N : ℕ, (B : ℝ) ≤
      (N : ℝ) -
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N 1‖ := by
  obtain ⟨N, hchange⟩ := pi_changeCount_unbounded (5000 * B)
  refine ⟨N, ?_⟩
  have hgap := pi_firstFrequency_additiveGap_ge_digitChanges N
  have hcast : (5000 * B : ℕ) ≤
      Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N :=
    (Nat.le_of_lt hchange)
  have hcastReal : (5000 * B : ℝ) ≤
      (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) := by
    exact_mod_cast hcast
  calc
    (B : ℝ) = (5000 * B : ℝ) / 5000 := by ring
    _ ≤ (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) /
          5000 := by gcongr
    _ ≤ (N : ℝ) -
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N 1‖ := hgap

/-- Strong rate-free consequence: the additive first-frequency gap tends to
infinity in the order-theoretic sense that it eventually exceeds every
natural threshold. -/
theorem pi_firstFrequency_additiveGap_eventually_ge (B : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (B : ℝ) ≤
      (N : ℝ) -
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N 1‖ := by
  obtain ⟨N₀, hchange⟩ := pi_changeCount_unbounded (5000 * B)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hcountMono :
      Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N₀ ≤
        Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N :=
    changeCount_mono Theory.PiDigits.piDigit hN
  have hcount : (5000 * B : ℕ) ≤
      Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N :=
    (Nat.le_of_lt hchange).trans hcountMono
  have hcountReal : (5000 * B : ℝ) ≤
      (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) := by
    exact_mod_cast hcount
  have hgap := pi_firstFrequency_additiveGap_ge_digitChanges N
  calc
    (B : ℝ) = (5000 * B : ℝ) / 5000 := by ring
    _ ≤ (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) /
          5000 := by gcongr
    _ ≤ (N : ℝ) -
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N 1‖ := hgap

end Theory.PiDigits.UnboundedFourierGap
