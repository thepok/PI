import TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset
import TheoryLib.PiQuantitativeBlockHitting.T20T20DigitChangeFourierDefect
import TheoryLib.PiQuantitativeBlockHitting.T38T38MachinForcedOrbit
import TheoryLib.PiQuantitativeBlockHitting.T193T193PositiveValuationShellAggregate

/-!
# T194: conditional central pi return seed

An explicit irrationality-measure hypothesis rules out an arbitrarily long
terminal run in the two decimal chambers adjacent to zero and one.  Applied
to the actual decimal orbit of `pi`, this gives one unprescribed central
return.  Its containing decimal cell then feeds T193's native unit-block
surplus directly.

The published irrationality-measure estimate is not asserted here: it
remains the explicit hypothesis of the final theorem.  This module constructs
neither a ray nor a natural-horizon recurrence.
-/

noncomputable section

namespace Theory.PiDigits.T194CentralPiReturnSeed

open Theory.PiDigits.LongLagBlockCollisionDecay.T4
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.T193PositiveValuationShellAggregate
open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.SignedBlockBellmanTransport

abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

private lemma self_le_pow_ten (s : ℕ) : s ≤ 10 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ]
    have hp0 : 0 < 10 ^ s := pow_pos (by omega) _
    omega

private lemma sourceBelow36Fifths_implies_sourceBelowEight
    (hSource : IrrationalityMeasureBelow Real.pi ((36 : ℝ) / 5)) :
    IrrationalityMeasureBelow Real.pi 8 := by
  rcases hSource with ⟨mu, hmu, hSource⟩
  exact ⟨mu, by linarith, hSource⟩

private lemma orbit_low_step
    (j : ℕ) (hlow : piOrbit j < 1 / 11)
    (havoid : ¬ (1 / 11 ≤ piOrbit (j + 1) ∧ piOrbit (j + 1) ≤ 10 / 11)) :
    piOrbit (j + 1) < 1 / 11 := by
  have hx0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j).1
  have hten0 : (0 : ℝ) ≤ 10 * piOrbit j := by positivity
  have hten1 : 10 * piOrbit j < 1 := by nlinarith
  have hstep := Theory.PiDigits.DigitChangeFourierDefect.piOrbit_succ j
  rw [Int.fract_eq_self.2 ⟨hten0, hten1⟩] at hstep
  have hnext0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico (j + 1)).1
  have hnextUpper : piOrbit (j + 1) < 10 / 11 := by nlinarith
  by_contra hnot
  exact havoid ⟨le_of_not_gt hnot, hnextUpper.le⟩

private lemma orbit_high_step
    (j : ℕ) (hhigh : 10 / 11 < piOrbit j)
    (havoid : ¬ (1 / 11 ≤ piOrbit (j + 1) ∧ piOrbit (j + 1) ≤ 10 / 11)) :
    10 / 11 < piOrbit (j + 1) := by
  have hx1 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j).2
  have hfloor : ⌊10 * piOrbit j⌋ = (9 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> nlinarith
  have hstep := Theory.PiDigits.DigitChangeFourierDefect.piOrbit_succ j
  rw [Int.fract, hfloor] at hstep
  have hnextLower : 1 / 11 < piOrbit (j + 1) := by
    norm_num at hstep
    nlinarith
  by_contra hnot
  exact havoid ⟨hnextLower.le, le_of_not_gt hnot⟩

private lemma orbit_low_iterate
    (s L : ℕ)
    (havoid : ∀ j : ℕ, s ≤ j →
      ¬ (1 / 11 ≤ piOrbit j ∧ piOrbit j ≤ 10 / 11))
    (hlow : piOrbit s < 1 / 11) :
    piOrbit (s + L) = (10 : ℝ) ^ L * piOrbit s ∧
      piOrbit (s + L) < 1 / 11 := by
  induction L with
  | zero =>
      constructor
      · norm_num
      · exact hlow
  | succ L ih =>
      have hlowNext := orbit_low_step (s + L) ih.2
        (havoid (s + L + 1) (by omega))
      have hx0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico (s + L)).1
      have hten0 : (0 : ℝ) ≤ 10 * piOrbit (s + L) := by positivity
      have hten1 : 10 * piOrbit (s + L) < 1 := by nlinarith [ih.2]
      have hstep := Theory.PiDigits.DigitChangeFourierDefect.piOrbit_succ (s + L)
      change piOrbit (s + L + 1) = Int.fract (10 * piOrbit (s + L)) at hstep
      rw [Int.fract_eq_self.2 ⟨hten0, hten1⟩] at hstep
      constructor
      · rw [show s + Nat.succ L = s + L + 1 by omega, hstep, ih.1, pow_succ]
        ring
      · simpa only [show s + Nat.succ L = s + L + 1 by omega] using hlowNext

private lemma orbit_high_iterate
    (s L : ℕ)
    (havoid : ∀ j : ℕ, s ≤ j →
      ¬ (1 / 11 ≤ piOrbit j ∧ piOrbit j ≤ 10 / 11))
    (hhigh : 10 / 11 < piOrbit s) :
    1 - piOrbit (s + L) = (10 : ℝ) ^ L * (1 - piOrbit s) ∧
      10 / 11 < piOrbit (s + L) := by
  induction L with
  | zero =>
      constructor
      · norm_num
      · exact hhigh
  | succ L ih =>
      have hhighNext := orbit_high_step (s + L) ih.2
        (havoid (s + L + 1) (by omega))
      have hx1 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico (s + L)).2
      have hfloor : ⌊10 * piOrbit (s + L)⌋ = (9 : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor <;> norm_num <;> nlinarith [ih.2]
      have hstep := Theory.PiDigits.DigitChangeFourierDefect.piOrbit_succ (s + L)
      change piOrbit (s + L + 1) = Int.fract (10 * piOrbit (s + L)) at hstep
      rw [Int.fract, hfloor] at hstep
      constructor
      · rw [show s + Nat.succ L = s + L + 1 by omega]
        norm_num at hstep
        rw [hstep]
        calc
          1 - (10 * piOrbit (s + L) - 9) =
              10 * (1 - piOrbit (s + L)) := by ring
          _ = 10 * ((10 : ℝ) ^ L * (1 - piOrbit s)) := by rw [ih.1]
          _ = (10 : ℝ) ^ (L + 1) * (1 - piOrbit s) := by
            rw [pow_succ]
            ring
      · simpa only [show s + Nat.succ L = s + L + 1 by omega] using hhighNext

private lemma exists_piOrbit_mem_central_chamber
    (hSource : IrrationalityMeasureBelow Real.pi ((36 : ℝ) / 5))
    (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧
      1 / 11 ≤ piOrbit m ∧ piOrbit m ≤ 10 / 11 := by
  obtain ⟨Q0, hIrr⟩ := irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality
    (sourceBelow36Fifths_implies_sourceBelowEight hSource)
  by_contra hnone
  push Not at hnone
  let s : ℕ := max lower (max 1 Q0)
  let d : ℕ := 10 ^ s
  have hlowerS : lower ≤ s := le_max_left _ _
  have hs1 : 1 ≤ s := (le_max_left 1 Q0).trans (le_max_right lower (max 1 Q0))
  have hQ0s : Q0 ≤ s := (le_max_right 1 Q0).trans (le_max_right lower (max 1 Q0))
  have hsd : s ≤ d := by
    dsimp [d]
    exact self_le_pow_ten s
  have hQ0d : Q0 ≤ d := hQ0s.trans hsd
  have hd0 : 0 < d := by positivity
  have hdR : (0 : ℝ) < d := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have havoid (j : ℕ) :
      s ≤ j → ¬ (1 / 11 ≤ piOrbit j ∧ piOrbit j ≤ 10 / 11) := by
    intro hsj
    intro hj
    exact (not_lt_of_ge hj.2) (hnone j (hlowerS.trans hsj) hj.1)
  have hstart : piOrbit s < 1 / 11 ∨ 10 / 11 < piOrbit s := by
    have hx := Theory.PiDigits.T27.piFractionalOrbit_mem_Ico s
    by_cases hlow : piOrbit s < 1 / 11
    · exact Or.inl hlow
    · exact Or.inr (hnone s hlowerS (le_of_not_gt hlow))
  rcases hstart with hlow | hhigh
  · obtain ⟨hiterate, hend⟩ := orbit_low_iterate s (7 * s) havoid hlow
    let p : ℤ := ⌊(10 : ℝ) ^ s * Real.pi⌋
    have horbit : piOrbit s = (10 : ℝ) ^ s * Real.pi - p := by
      unfold piOrbit Theory.PiDigits.T27.piFractionalOrbit
      rw [Int.fract]
    have hdCast : (d : ℝ) = (10 : ℝ) ^ s := by simp [d]
    have hsmall : piOrbit s * (d : ℝ) ^ 7 < 1 := by
      calc
        piOrbit s * (d : ℝ) ^ 7 =
            (10 : ℝ) ^ (7 * s) * piOrbit s := by
          rw [hdCast, ← pow_mul]
          ring
        _ = piOrbit (s + 7 * s) := hiterate.symm
        _ < 1 / 11 := hend
        _ < 1 := by norm_num
    have hUpper : |Real.pi - (p : ℝ) / (d : ℝ)| < 1 / (d : ℝ) ^ (8 : ℝ) := by
      have hx0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico s).1
      have heq : Real.pi - (p : ℝ) / (d : ℝ) = piOrbit s / d := by
        rw [hdCast]
        field_simp
        nlinarith [horbit]
      rw [heq, abs_of_nonneg (by positivity)]
      rw [show (d : ℝ) ^ (8 : ℝ) = (d : ℝ) ^ (8 : ℕ) by
        exact Real.rpow_natCast d 8]
      apply (div_lt_div_iff₀ hdR (by positivity : (0 : ℝ) < (d : ℝ) ^ 8)).2
      field_simp
      nlinarith
    exact (not_lt_of_ge hUpper.le) (hIrr.2.2 d hQ0d hd0 p)
  · obtain ⟨hiterate, hend⟩ := orbit_high_iterate s (7 * s) havoid hhigh
    let p : ℤ := ⌊(10 : ℝ) ^ s * Real.pi⌋ + 1
    have horbit : piOrbit s = (10 : ℝ) ^ s * Real.pi - (⌊(10 : ℝ) ^ s * Real.pi⌋ : ℝ) := by
      unfold piOrbit Theory.PiDigits.T27.piFractionalOrbit
      rw [Int.fract]
    have hdCast : (d : ℝ) = (10 : ℝ) ^ s := by simp [d]
    have hsmall : (1 - piOrbit s) * (d : ℝ) ^ 7 < 1 := by
      calc
        (1 - piOrbit s) * (d : ℝ) ^ 7 =
            (10 : ℝ) ^ (7 * s) * (1 - piOrbit s) := by
          rw [hdCast, ← pow_mul]
          ring
        _ = 1 - piOrbit (s + 7 * s) := hiterate.symm
        _ < 1 / 11 := by nlinarith
        _ < 1 := by norm_num
    have hUpper : |Real.pi - (p : ℝ) / (d : ℝ)| < 1 / (d : ℝ) ^ (8 : ℝ) := by
      have hx1 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico s).2
      have heq : Real.pi - (p : ℝ) / (d : ℝ) = -(1 - piOrbit s) / d := by
        dsimp [p]
        push_cast
        rw [hdCast]
        field_simp
        ring_nf at horbit ⊢
        linarith
      rw [heq, abs_div, abs_neg, abs_of_nonneg (by linarith), abs_of_pos hdR]
      rw [show (d : ℝ) ^ (8 : ℝ) = (d : ℝ) ^ (8 : ℕ) by
        exact Real.rpow_natCast d 8]
      apply (div_lt_div_iff₀ hdR (by positivity : (0 : ℝ) < (d : ℝ) ^ 8)).2
      field_simp
      nlinarith
    exact (not_lt_of_ge hUpper.le) (hIrr.2.2 d hQ0d hd0 p)

/-- Conditional actual-pi seed: at every decimal scale at least `10^3`, one
unprescribed literal decimal cell has positive native T176 unit-block
capital.  The irrationality-measure premise is explicit. -/
theorem exists_central_pi_unitBlock_surplus
    (hSource : IrrationalityMeasureBelow Real.pi ((36 : ℝ) / 5))
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ n A : ℕ, A < 10 ^ k ∧
      (3 / 20 : ℝ) * (10 ^ k : ℕ) <
        (10 ^ k : ℕ) *
            (primitiveBoundaryFourierBlockSum (10 ^ k) A n 1).re -
          signedBlockPotential (10 ^ k) := by
  obtain ⟨m, hkm, hmLow, hmHigh⟩ :=
    exists_piOrbit_mem_central_chamber hSource k
  let n := m - k
  let A := ⌊(10 ^ k : ℕ) * piOrbit n⌋₊
  let y := (10 ^ k : ℕ) * piOrbit n - A - 1 / 2
  have hx := Theory.PiDigits.T27.piFractionalOrbit_mem_Ico n
  have hqPos : (0 : ℝ) < ((10 ^ k : ℕ) : ℝ) := by positivity
  have hA : A < 10 ^ k := by
    dsimp [A]
    rw [Nat.floor_lt (by
      exact mul_nonneg (by positivity) hx.1 :
        (0 : ℝ) ≤ ((10 ^ k : ℕ) : ℝ) * piOrbit n)]
    simpa using (mul_lt_mul_of_pos_left hx.2 hqPos)
  have hfrac : y = Int.fract ((10 ^ k : ℕ) * piOrbit n) - 1 / 2 := by
    dsimp [y, A]
    rw [Int.fract, ← natCast_floor_eq_intCast_floor
      (by exact mul_nonneg (by positivity) hx.1 :
        (0 : ℝ) ≤ ((10 ^ k : ℕ) : ℝ) * piOrbit n)]
  have horbitShift : Int.fract ((10 ^ k : ℕ) * piOrbit n) = piOrbit (n + k) := by
    unfold piOrbit Theory.PiDigits.T27.piFractionalOrbit
    have hfract := Theory.PiDigits.MachinForcedOrbit.fract_natCast_mul_fract_add
      ((10 : ℝ) ^ n * Real.pi) 0 (10 ^ k)
    simp only [add_zero] at hfract
    exact hfract.trans (by
      congr 1
      push_cast
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega)
  have hy : |y| ≤ 9 / 22 := by
    rw [hfrac, horbitShift]
    have hnk : n + k = m := by dsimp [n]; omega
    rw [hnk]
    rw [abs_le]
    constructor <;> nlinarith
  have hyCoord : piOrbit n - decimalCylinderCenter (10 ^ k) A =
      y / (10 ^ k : ℕ) := by
    dsimp [y, A]
    unfold decimalCylinderCenter
    field_simp
    ring
  exact ⟨n, A, hA,
    central_unitBlock_surplus_gt_three_div_twenty k A n hk y hy hyCoord⟩

end Theory.PiDigits.T194CentralPiReturnSeed

#print axioms Theory.PiDigits.T194CentralPiReturnSeed.exists_central_pi_unitBlock_surplus
