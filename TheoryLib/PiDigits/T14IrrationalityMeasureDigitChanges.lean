import TheoryLib.PiDigits.T11PiDigitFactorComplexity
import TheoryLib.PiDigits.T18FiniteAlphabetSubsequentialCounting
import TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset
import TheoryLib.PiPositiveDecimalFactorEntropy.T36T36DecimalPeriodicWindowGap

/-!
# T14: irrationality measure and decimal digit changes

This module turns T4's explicit source hypothesis into the logarithmic lower
bound for the number of changes in the floor-based decimal digits of pi.  It
does not prove the external irrationality-measure estimate and does not imply
either V1 or V3.
-/

noncomputable section

namespace Theory.PiDigits.T14

open DecimalFactorComplexity.PeriodicWindowGap
open Theory.PiDigits.LongLagBlockCollisionDecay.T4

private abbrev Digit := Fin 10
private abbrev Stream := ℕ → Digit

/-- The exponential checkpoints used to count disjoint constant-run gaps. -/
private def anchor (M j : ℕ) : ℕ := 8 ^ j * (M + 2) - 2

private lemma anchor_zero (M : ℕ) : anchor M 0 = M := by
  simp [anchor]

private lemma anchor_add_two (M j : ℕ) :
    anchor M j + 2 = 8 ^ j * (M + 2) := by
  unfold anchor
  have hpow : 1 ≤ 8 ^ j := one_le_pow₀ (by norm_num)
  have h : 2 ≤ 8 ^ j * (M + 2) := by nlinarith
  omega

private lemma anchor_succ (M j : ℕ) :
    anchor M (j + 1) + 2 = 8 * (anchor M j + 2) := by
  rw [anchor_add_two, anchor_add_two]
  simp only [pow_succ]
  ring

private lemma anchor_mono (M : ℕ) : Monotone (anchor M) := by
  intro j k hjk
  have hp : 8 ^ j ≤ 8 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
  unfold anchor
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_right (M + 2) hp) 2

/-- Absence of adjacent changes makes a half-open digit window period one. -/
private lemma exactPeriodicWindow_one_of_no_change
    (s : Stream) (a b : ℕ) (hab : a ≤ b)
    (hconstant : ∀ i : ℕ, a ≤ i → i < b → s i = s (i + 1)) :
    ExactPeriodicWindow s a 1 (b - a + 1) := by
  refine ⟨by norm_num, ?_⟩
  intro i hi
  simp only [Nat.mod_one, Nat.add_zero]
  have hia : a + i ≤ b := by omega
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i < b - a + 1 := by omega
      have hai : a + i < b := by omega
      exact (hconstant (a + i) (by omega) hai).symm.trans (ih hi' (by omega))

/-- A period-one window gap forces a change between consecutive exponential
checkpoints. -/
private lemma exists_change_between_anchors
    (s : Stream) (M j : ℕ)
    (hgap : ∀ a L : ℕ, M ≤ a → ExactPeriodicWindow s a 1 L →
      (L : ℝ) ≤ 7 * (a : ℝ) + 9) :
    ∃ i : ℕ, anchor M j ≤ i ∧ i < anchor M (j + 1) ∧ s i ≠ s (i + 1) := by
  let a := anchor M j
  let b := anchor M (j + 1)
  have haM : M ≤ a := by
    rw [← anchor_zero M]
    exact anchor_mono M (Nat.zero_le j)
  have hab : a ≤ b := anchor_mono M (Nat.le_succ j)
  by_contra hnot
  push Not at hnot
  have hw : ExactPeriodicWindow s a 1 (b - a + 1) :=
    exactPeriodicWindow_one_of_no_change s a b hab fun i hai hib ↦ hnot i hai hib
  have hbound := hgap a (b - a + 1) haM hw
  have hstep : b + 2 = 8 * (a + 2) := by
    simpa only [a, b] using anchor_succ M j
  have hlength : b - a + 1 = 7 * a + 15 := by omega
  rw [hlength] at hbound
  norm_num at hbound

/-- Generic counting core: if every sufficiently late constant window obeys
the exponent-eight period-one gap, then prefix changes grow logarithmically. -/
theorem changeCount_checkpoint_bound
    (s : Stream) (M N : ℕ)
    (hgap : ∀ a L : ℕ, M ≤ a → ExactPeriodicWindow s a 1 L →
      (L : ℝ) ≤ 7 * (a : ℝ) + 9) :
    N + 2 ≤ 8 ^ (Theory.PiDigits.T18.changeCount s N + 1) * (M + 2) := by
  classical
  let K := Theory.PiDigits.T18.changeCount s N
  have hKdef : K = Theory.PiDigits.T18.changeCount s N := rfl
  by_contra hnot
  have htop : anchor M (K + 1) < N := by
    have hprod : 8 ^ (K + 1) * (M + 2) < N + 2 := Nat.lt_of_not_ge hnot
    have hadd := anchor_add_two M (K + 1)
    omega
  let pick : (j : Fin (K + 1)) → ℕ := fun j ↦
    Classical.choose (exists_change_between_anchors s M j hgap)
  have pick_spec (j : Fin (K + 1)) :
      anchor M j ≤ pick j ∧ pick j < anchor M (j + 1) ∧
        s (pick j) ≠ s (pick j + 1) :=
    Classical.choose_spec (exists_change_between_anchors s M j hgap)
  have pick_mem (j : Fin (K + 1)) :
      pick j ∈ Theory.PiDigits.T18.changePositions s N := by
    simp only [Theory.PiDigits.T18.changePositions, Finset.mem_filter,
      Finset.mem_range]
    refine ⟨?_, (pick_spec j).2.2⟩
    have hj : j.val + 1 ≤ K + 1 := by omega
    have hanchor : anchor M (j.val + 1) ≤ anchor M (K + 1) :=
      anchor_mono M hj
    have hpick : pick j + 1 < N :=
      (Nat.succ_le_of_lt (pick_spec j).2.1).trans_lt (hanchor.trans_lt htop)
    exact Nat.lt_sub_of_add_lt hpick
  let f : Fin (K + 1) →
      {i // i ∈ Theory.PiDigits.T18.changePositions s N} :=
    fun j ↦ ⟨pick j, pick_mem j⟩
  have hf : Function.Injective f := by
    apply StrictMono.injective
    intro j k hjk
    apply Subtype.mk_lt_mk.mpr
    have hjk' : j.val + 1 ≤ k.val := by omega
    have hmiddle : anchor M (j.val + 1) ≤ anchor M k.val :=
      anchor_mono M hjk'
    exact (pick_spec j).2.1.trans_le (hmiddle.trans (pick_spec k).1)
  have hcard := Fintype.card_le_of_injective f hf
  have hcard' : K + 1 ≤ (Theory.PiDigits.T18.changePositions s N).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  have hK : K = (Theory.PiDigits.T18.changePositions s N).card := by
    exact hKdef
  omega

/-- T4's effective bound for pi transfers to the fractional part `pi - 3`.
The integer shift only changes the numerator by `3q`. -/
theorem effectiveIrrationality_pi_sub_three
    {Q0 : ℕ}
    (hIrr : Theory.PiDigits.PositiveLowerBlockDensity.T25.EffectiveIrrationality
      Real.pi 8 1 Q0) :
    EffectiveIrrationality (Real.pi - 3) 8 Q0 := by
  refine ⟨by norm_num, ?_⟩
  intro q hq0 hq z
  have hs := hIrr.2.2 q hq0 hq (z + 3 * q)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have heq :
      (Real.pi - 3) - (z : ℝ) / q =
        Real.pi - ((z + 3 * q : ℤ) : ℝ) / q := by
    push_cast
    field_simp [hqR]
    ring
  rw [heq]
  simpa only [one_div] using hs

/-- The public T14 bound. The published irrationality-measure result remains
an explicit premise; the conclusion is only a digit-change estimate. -/
theorem pi_changeCount_log_lower_bound
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) :
    ∃ C14 : ℝ, ∀ N : ℕ, 1 ≤ N →
      (1 / Real.log 8) * Real.log N - C14 ≤
        (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) := by
  obtain ⟨Q0, hIrr⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality hSource
  have hfracIrr := effectiveIrrationality_pi_sub_three hIrr
  have hrep : Represents (Real.pi - 3) Theory.PiDigits.piDigit := by
    rw [Represents, show Theory.PiDigits.piDigit =
        Real.digits (Real.pi - 3) 10 from
      funext Theory.PiDigits.FactorComplexity.piDigit_eq_digits]
    symm
    exact Real.ofDigits_digits (by norm_num) ⟨by linarith [Real.pi_gt_three],
      by linarith [Real.pi_lt_four]⟩
  have hgap : ∀ a L : ℕ, Q0 ≤ a →
      ExactPeriodicWindow Theory.PiDigits.piDigit a 1 L →
      (L : ℝ) ≤ 7 * (a : ℝ) + 9 := by
    intro a L ha hw
    have honset : Q0 ≤ periodicDenominator a 1 := by
      calc
        Q0 ≤ a := ha
        _ ≤ 10 ^ a := (Nat.lt_pow_self (by norm_num)).le
        _ ≤ periodicDenominator a 1 := by
          simp [periodicDenominator]
    have hg := effectiveIrrationality_periodic_window_gap
      (Real.pi - 3) 8 Q0 a 1 L Theory.PiDigits.piDigit hrep hfracIrr hw honset
    norm_num [roundingConstant] at hg ⊢
    linarith
  refine ⟨1 + Real.log (Q0 + 2) / Real.log 8, ?_⟩
  intro N hN
  have hnat := changeCount_checkpoint_bound Theory.PiDigits.piDigit Q0 N hgap
  let K := Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N
  have hNprod0 : N ≤
      8 ^ (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N + 1) *
        (Q0 + 2) := by omega
  have hNprod : N ≤ 8 ^ (K + 1) * (Q0 + 2) := by
    simpa only [K] using hNprod0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast : (N : ℝ) ≤ (8 : ℝ) ^ (K + 1) * (Q0 + 2) := by
    exact_mod_cast hNprod
  have hlog := Real.log_le_log hNpos hcast
  rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (by positivity), Real.log_pow] at hlog
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  change Real.log N ≤ (K + 1 : ℕ) * Real.log 8 + Real.log (Q0 + 2) at hlog
  calc
    (1 / Real.log 8) * Real.log N -
          (1 + Real.log (Q0 + 2) / Real.log 8) =
        (Real.log N - Real.log (Q0 + 2)) / Real.log 8 - 1 := by
          field_simp [hlog8.ne']
          ring
    _ ≤ (K : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hlog8]
      push_cast at hlog ⊢
      linarith

#print axioms Theory.PiDigits.T14.changeCount_checkpoint_bound
#print axioms Theory.PiDigits.T14.effectiveIrrationality_pi_sub_three
#print axioms Theory.PiDigits.T14.pi_changeCount_log_lower_bound

end Theory.PiDigits.T14
