import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity

/-!
# T3: finite Fourier lower-density certificate

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves a conditional sufficient criterion for the canonical A1
question.  Its quantifiers are fixed word length `k >= 1`, fixed frequency
cutoff `H`, fixed normalized error `epsilon`, an explicit `eta > 0`, and one
threshold `N0` that works for every `N >= N0` and every length-`k` word.

The final theorem for pi assumes the displayed finite-frequency exponential-
sum bounds.  Those bounds are not proved here, so this module does not prove
positive lower block density for pi, normality, or even the canonical claim
for one value of `k` unconditionally.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.PositiveLowerBlockDensity.T3

open Theory.PiDigits.PositiveLowerBlockDensity

/-- The explicit lower frequency supplied by T27 when every nonzero frequency
up to `H` has unnormalized exponential sum at most `epsilon * N`.

For a length-`k` decimal cylinder, `L = 10^-k`; T27 gives
`(1 - H*epsilon - 1 / ((H+1)*L^2)) / (H+1)` as the lower bound. -/
def finiteFourierLowerBound (k H : ℕ) (epsilon : ℝ) : ℝ :=
  (1 - (H : ℝ) * epsilon -
      1 / (((H + 1 : ℕ) : ℝ) *
        Theory.PiDigits.T27.decimalCylinderLength k ^ 2)) /
    ((H + 1 : ℕ) : ℝ)

/-- A single-prefix quantitative form of the T3 certificate. -/
theorem decimalCylinderFrequency_ge_of_normalizedFiniteFourierBound
    (x : ℕ → ℝ) (k H N : ℕ) (hN : 0 < N) (epsilon eta : ℝ)
    (hparameters :
      0 ≤ epsilon ∧ 0 < eta ∧ eta ≤ finiteFourierLowerBound k H epsilon)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (hbound : Theory.PiDigits.T27.FirstFrequencyBound
      x N H (epsilon * N))
    (w : List (Fin 10)) (hw : w.length = k) :
    eta ≤
      (Theory.PiDigits.T27.cylinderCount x N
          (Theory.PiDigits.T27.decimalCylinderLeft w)
          (Theory.PiDigits.T27.decimalCylinderLength w.length) : ℝ) / N := by
  have hdisc :=
    Theory.PiDigits.T27.decimalCylinderDeficit_le_of_firstFrequencyBound
      x N H hN (Theory.PiDigits.T27.decimalCylinderLeft w)
      (Theory.PiDigits.T27.decimalCylinderLength w.length) (epsilon * N)
      hx (Theory.PiDigits.T27.decimalCylinderLeft_nonneg w)
      (Theory.PiDigits.T27.decimalCylinderLength_pos w.length)
      (Theory.PiDigits.T27.decimalCylinderRight_le_one w) hbound
  have hraw :
      ((N : ℝ) - (H : ℝ) * (epsilon * N) -
          N * (1 / (((H + 1 : ℕ) : ℝ) *
            Theory.PiDigits.T27.decimalCylinderLength w.length ^ 2))) /
            ((N : ℝ) * ((H + 1 : ℕ) : ℝ)) ≤
        (Theory.PiDigits.T27.cylinderCount x N
            (Theory.PiDigits.T27.decimalCylinderLeft w)
            (Theory.PiDigits.T27.decimalCylinderLength w.length) : ℝ) / N := by
    unfold Theory.PiDigits.T27.cylinderDeficit at hdisc
    norm_num only [Nat.cast_add, Nat.cast_one] at hdisc ⊢
    linarith
  calc
    eta ≤ finiteFourierLowerBound k H epsilon := hparameters.2.2
    _ = ((N : ℝ) - (H : ℝ) * (epsilon * N) -
          N * (1 / (((H + 1 : ℕ) : ℝ) *
            Theory.PiDigits.T27.decimalCylinderLength w.length ^ 2))) /
            ((N : ℝ) * ((H + 1 : ℕ) : ℝ)) := by
      rw [finiteFourierLowerBound, ← hw]
      field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']
    _ ≤ _ := hraw

/-- Eventual uniform finite-frequency bounds force the same positive lower
frequency for every length-`k` decimal cylinder and every `N >= N0`.
The positivity of `eta` and the normalized error constraint are explicit in
`hparameters`. -/
theorem eventual_everyLengthKDecimalCylinder_frequency_ge
    (x : ℕ → ℝ) (k H N0 : ℕ) (hk : 1 ≤ k) (hN0 : 1 ≤ N0)
    (epsilon eta : ℝ)
    (hparameters :
      0 ≤ epsilon ∧ 0 < eta ∧ eta ≤ finiteFourierLowerBound k H epsilon)
    (hx : ∀ j, x j ∈ Set.Ico (0 : ℝ) 1)
    (hbound : ∀ N, N0 ≤ N →
      Theory.PiDigits.T27.FirstFrequencyBound x N H (epsilon * N)) :
    1 ≤ k ∧ 0 < eta ∧
      ∀ N, N0 ≤ N → ∀ w : List (Fin 10), w.length = k →
        eta ≤
          (Theory.PiDigits.T27.cylinderCount x N
              (Theory.PiDigits.T27.decimalCylinderLeft w)
              (Theory.PiDigits.T27.decimalCylinderLength w.length) : ℝ) / N := by
  refine ⟨hk, hparameters.2.1, ?_⟩
  intro N hN w hw
  exact decimalCylinderFrequency_ge_of_normalizedFiniteFourierBound
    x k H N (lt_of_lt_of_le Nat.zero_lt_one (hN0.trans hN)) epsilon eta
    hparameters (fun j _hj => hx j) (hbound N hN) w hw

/-- Every pi orbit point in a word cylinder contributes a start counted by
T1's exact overlapping `blockCount`.  This one-way inequality avoids any
decimal-endpoint converse. -/
theorem piCylinderCount_le_blockCount (w : List (Fin 10)) (N : ℕ) :
    Theory.PiDigits.T27.cylinderCount
        Theory.PiDigits.T27.piFractionalOrbit N
        (Theory.PiDigits.T27.decimalCylinderLeft w)
        (Theory.PiDigits.T27.decimalCylinderLength w.length) ≤
      blockCount Theory.PiDigits.piDigit w N := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [Theory.PiDigits.T27.cylinderCount, blockCount]
  unfold Theory.PiDigits.T27.cylinderCount blockCount
  apply Finset.card_le_card_of_injOn
      (fun j : ℕ =>
        (⟨j % N, Nat.mod_lt j (Nat.pos_of_ne_zero hN)⟩ : Fin N))
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    have hcyl := hj.2
    rw [Theory.PiDigits.T27.decimalCylinder_interval] at hcyl
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [Nat.mod_eq_of_lt hj.1]
    have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
      w (Theory.PiDigits.T27.piFractionalOrbit j) hcyl
    have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
      Real.pi Real.pi_pos.le j i.val
    exact (Theory.PiDigits.T20.decimalDigit_pi (j + i.val)).symm.trans
      (hshift.symm.trans (hdigits i.val i.isLt))
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
    simpa [Nat.mod_eq_of_lt hi.1, Nat.mod_eq_of_lt hj.1] using
      congrArg Fin.val hij

/-- Conditional pi specialization with all eventual finite-frequency
hypotheses displayed.  In source notation the conclusion is
`A_pi(w,N) / N >= eta` for every `N >= N0` and every length-`k` word.

The exponential-sum hypothesis below is unproved for pi. -/
theorem pi_eventual_everyLengthKWord_blockFrequency_ge_of_finiteFourierBounds
    (k H N0 : ℕ) (hk : 1 ≤ k) (hN0 : 1 ≤ N0) (epsilon eta : ℝ)
    (hparameters :
      0 ≤ epsilon ∧ 0 < eta ∧ eta ≤ finiteFourierLowerBound k H epsilon)
    (hpi_exponentialSum_unproved :
      ∀ N, N0 ≤ N → ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ H →
        ‖∑ j ∈ range N,
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
              ((Theory.PiDigits.T27.piFractionalOrbit j : ℝ) : ℂ))‖ ≤
          epsilon * N) :
    1 ≤ k ∧ 0 < eta ∧
      ∀ N, N0 ≤ N → ∀ w : List (Fin 10), w.length = k →
        eta ≤ blockFrequency Theory.PiDigits.piDigit w N := by
  have hfinite : ∀ N, N0 ≤ N →
      Theory.PiDigits.T27.FirstFrequencyBound
        Theory.PiDigits.T27.piFractionalOrbit N H (epsilon * N) := by
    intro N hN h h0 hH
    simpa only [Theory.PiDigits.T27.exponentialSum,
      Theory.PiDigits.T27.phase] using
        hpi_exponentialSum_unproved N hN h h0 hH
  have hcylinders := eventual_everyLengthKDecimalCylinder_frequency_ge
    Theory.PiDigits.T27.piFractionalOrbit k H N0 hk hN0 epsilon eta
    hparameters (fun j => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
    hfinite
  refine ⟨hcylinders.1, hcylinders.2.1, ?_⟩
  intro N hN w hw
  calc
    eta ≤
        (Theory.PiDigits.T27.cylinderCount
            Theory.PiDigits.T27.piFractionalOrbit N
            (Theory.PiDigits.T27.decimalCylinderLeft w)
            (Theory.PiDigits.T27.decimalCylinderLength w.length) : ℝ) / N :=
      hcylinders.2.2 N hN w hw
    _ ≤ blockFrequency Theory.PiDigits.piDigit w N := by
      unfold blockFrequency
      apply div_le_div_of_nonneg_right
      · exact_mod_cast piCylinderCount_le_blockCount w N
      · positivity

end Theory.PiDigits.PositiveLowerBlockDensity.T3

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T3.decimalCylinderFrequency_ge_of_normalizedFiniteFourierBound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T3.eventual_everyLengthKDecimalCylinder_frequency_ge
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T3.piCylinderCount_le_blockCount
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T3.pi_eventual_everyLengthKWord_blockFrequency_ge_of_finiteFourierBounds
