import TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset
import TheoryLib.PiQuantitativeBlockHitting.T20T20DigitChangeFourierDefect
import TheoryLib.PiQuantitativeBlockHitting.T38T38MachinForcedOrbit
import TheoryLib.PiQuantitativeBlockHitting.T193T193PositiveValuationShellAggregate

/-!
# T194: conditional central pi return seed

The irrationality of `pi` rules out an eventual decimal-orbit tail trapped in
either chamber adjacent to zero or one, giving an unconditional unprescribed
central return at every scale. Its containing decimal cell feeds T193's native
unit-block surplus directly. An explicit irrationality-measure hypothesis
additionally bounds a sufficiently long trapped finite window; after a
premise-dependent onset, the unit can then be chosen in the fresh
natural-horizon block `[q, 10*q)`.

The published irrationality-measure estimate is not asserted here: it remains
the explicit hypothesis only of the time-localized theorems. This module
constructs neither a ray nor a natural-horizon recurrence.
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

private lemma self_le_pow_ten_pred (k : ℕ) (hk : 2 ≤ k) :
    k ≤ 10 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hp : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow (k - 1) 10 (by omega)
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      omega

private lemma seven_mul_lt_two_mul_pow_ten (k : ℕ) (hk : 3 ≤ k) :
    7 * k < 2 * 10 ^ k := by
  have hkp := self_le_pow_ten_pred k (by omega)
  have hp : 0 < 10 ^ (k - 1) := pow_pos (by omega) _
  rw [show k = (k - 1) + 1 by omega, pow_succ]
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
    (s L : ℕ) (hlow : piOrbit s < 1 / 11)
    (havoid : ∀ j : ℕ, s ≤ j → j ≤ s + L →
      ¬ (1 / 11 ≤ piOrbit j ∧ piOrbit j ≤ 10 / 11)) :
    piOrbit (s + L) = (10 : ℝ) ^ L * piOrbit s ∧
      piOrbit (s + L) < 1 / 11 := by
  induction L with
  | zero =>
      constructor
      · norm_num
      · exact hlow
  | succ L ih =>
      have ih' := ih (fun j hsj hj => havoid j hsj (by omega))
      have hlowNext := orbit_low_step (s + L) ih'.2
        (havoid (s + L + 1) (by omega) (by omega))
      have hx0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico (s + L)).1
      have hten0 : (0 : ℝ) ≤ 10 * piOrbit (s + L) := by positivity
      have hten1 : 10 * piOrbit (s + L) < 1 := by nlinarith [ih'.2]
      have hstep := Theory.PiDigits.DigitChangeFourierDefect.piOrbit_succ (s + L)
      change piOrbit (s + L + 1) = Int.fract (10 * piOrbit (s + L)) at hstep
      rw [Int.fract_eq_self.2 ⟨hten0, hten1⟩] at hstep
      constructor
      · rw [show s + Nat.succ L = s + L + 1 by omega, hstep, ih'.1, pow_succ]
        ring
      · simpa only [show s + Nat.succ L = s + L + 1 by omega] using hlowNext

private lemma orbit_high_iterate
    (s L : ℕ) (hhigh : 10 / 11 < piOrbit s)
    (havoid : ∀ j : ℕ, s ≤ j → j ≤ s + L →
      ¬ (1 / 11 ≤ piOrbit j ∧ piOrbit j ≤ 10 / 11)) :
    1 - piOrbit (s + L) = (10 : ℝ) ^ L * (1 - piOrbit s) ∧
      10 / 11 < piOrbit (s + L) := by
  induction L with
  | zero =>
      constructor
      · norm_num
      · exact hhigh
  | succ L ih =>
      have ih' := ih (fun j hsj hj => havoid j hsj (by omega))
      have hhighNext := orbit_high_step (s + L) ih'.2
        (havoid (s + L + 1) (by omega) (by omega))
      have hx1 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico (s + L)).2
      have hfloor : ⌊10 * piOrbit (s + L)⌋ = (9 : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor <;> norm_num <;> nlinarith [ih'.2]
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
          _ = 10 * ((10 : ℝ) ^ L * (1 - piOrbit s)) := by rw [ih'.1]
          _ = (10 : ℝ) ^ (L + 1) * (1 - piOrbit s) := by
            rw [pow_succ]
            ring
      · simpa only [show s + Nat.succ L = s + L + 1 by omega] using hhighNext

private lemma exists_piOrbit_mem_central_chamber_Icc
    (Q0 s : ℕ) (hIrr : EffectiveIrrationality Real.pi 8 1 Q0)
    (hs : 1 ≤ s) (hQ0 : Q0 ≤ 10 ^ s) :
    ∃ m : ℕ, s ≤ m ∧ m ≤ 8 * s ∧
      1 / 11 ≤ piOrbit m ∧ piOrbit m ≤ 10 / 11 := by
  by_contra hnone
  push Not at hnone
  let d : ℕ := 10 ^ s
  have hQ0d : Q0 ≤ d := by simpa [d] using hQ0
  have hd0 : 0 < d := by positivity
  have hdR : (0 : ℝ) < d := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have havoid (j : ℕ) :
      s ≤ j → j ≤ s + 7 * s →
        ¬ (1 / 11 ≤ piOrbit j ∧ piOrbit j ≤ 10 / 11) := by
    intro hsj hjs
    intro hj
    exact (not_lt_of_ge hj.2) (hnone j hsj (by omega) hj.1)
  have hstart : piOrbit s < 1 / 11 ∨ 10 / 11 < piOrbit s := by
    have hx := Theory.PiDigits.T27.piFractionalOrbit_mem_Ico s
    by_cases hlow : piOrbit s < 1 / 11
    · exact Or.inl hlow
    · exact Or.inr (hnone s le_rfl (by omega) (le_of_not_gt hlow))
  rcases hstart with hlow | hhigh
  · obtain ⟨hiterate, hend⟩ := orbit_low_iterate s (7 * s) hlow havoid
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
  · obtain ⟨hiterate, hend⟩ := orbit_high_iterate s (7 * s) hhigh havoid
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

private lemma exists_piOrbit_mem_central_chamber
    (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧
      1 / 11 ≤ piOrbit m ∧ piOrbit m ≤ 10 / 11 := by
  by_contra hnone
  push Not at hnone
  have havoid (L j : ℕ) (hlj : lower ≤ j) (hju : j ≤ lower + L) :
      ¬ (1 / 11 ≤ piOrbit j ∧ piOrbit j ≤ 10 / 11) := by
    intro hj
    exact (not_lt_of_ge hj.2) (hnone j hlj hj.1)
  have hstart : piOrbit lower < 1 / 11 ∨ 10 / 11 < piOrbit lower := by
    by_cases hlow : piOrbit lower < 1 / 11
    · exact Or.inl hlow
    · exact Or.inr (hnone lower le_rfl (le_of_not_gt hlow))
  rcases hstart with hlow | hhigh
  · have hzero : piOrbit lower = 0 := by
      have hx0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico lower).1
      apply le_antisymm
      · by_contra hnot
        have hxpos : 0 < piOrbit lower := lt_of_not_ge hnot
        obtain ⟨L, hL⟩ := exists_nat_gt ((1 / 11 : ℝ) / piOrbit lower)
        have hLPow : (L : ℝ) ≤ (10 : ℝ) ^ L := by
          exact_mod_cast self_le_pow_ten L
        have hratio : (1 / 11 : ℝ) / piOrbit lower < (10 : ℝ) ^ L :=
          hL.trans_le hLPow
        have hlarge : (1 / 11 : ℝ) < (10 : ℝ) ^ L * piOrbit lower :=
          (div_lt_iff₀ hxpos).mp hratio
        obtain ⟨hiterate, hend⟩ := orbit_low_iterate lower L hlow (havoid L)
        rw [hiterate] at hend
        exact (not_lt_of_ge hlarge.le) hend
      · exact hx0
    have hfract : Int.fract ((10 : ℝ) ^ lower * Real.pi) = 0 := by
      simpa [piOrbit, Theory.PiDigits.T27.piFractionalOrbit] using hzero
    rcases Int.fract_eq_zero_iff.mp hfract with ⟨z, hz⟩
    have hirr : Irrational ((10 : ℝ) ^ lower * Real.pi) := by
      simpa using irrational_pi.natCast_mul
        (m := 10 ^ lower) (by positivity)
    exact hirr.ne_rat (z : ℚ) (by simpa using hz.symm)
  · have hx1 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico lower).2
    have hdelta : 0 < 1 - piOrbit lower := by linarith
    obtain ⟨L, hL⟩ := exists_nat_gt ((1 / 11 : ℝ) / (1 - piOrbit lower))
    have hLPow : (L : ℝ) ≤ (10 : ℝ) ^ L := by
      exact_mod_cast self_le_pow_ten L
    have hratio : (1 / 11 : ℝ) / (1 - piOrbit lower) < (10 : ℝ) ^ L :=
      hL.trans_le hLPow
    have hlarge : (1 / 11 : ℝ) < (10 : ℝ) ^ L * (1 - piOrbit lower) :=
      (div_lt_iff₀ hdelta).mp hratio
    obtain ⟨hiterate, hend⟩ := orbit_high_iterate lower L hhigh (havoid L)
    have hsmall : 1 - piOrbit (lower + L) < 1 / 11 := by linarith
    rw [hiterate] at hsmall
    exact (not_lt_of_ge hlarge.le) hsmall

/-- Unconditional actual-pi seed: at every decimal scale at least `10^3`, one
unprescribed literal decimal cell has positive native T176 unit-block
capital. This uses only the irrationality of `pi` and gives no timing bound. -/
theorem exists_central_pi_unitBlock_surplus
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ n A : ℕ, A < 10 ^ k ∧
      (3 / 20 : ℝ) * (10 ^ k : ℕ) <
        (10 ^ k : ℕ) *
            (primitiveBoundaryFourierBlockSum (10 ^ k) A n 1).re -
          signedBlockPotential (10 ^ k) := by
  obtain ⟨m, hkm, hmLow, hmHigh⟩ := exists_piOrbit_mem_central_chamber k
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

/-- Finite-window strengthening of the conditional actual-pi seed.  After an
onset depending only on the effective irrationality witness, every decimal
scale `q = 10^k` has an unprescribed central literal unit beginning before
time `8*q`.  In particular, this unit lies inside the next natural horizon
`10*q`; no coherent choice between scales is asserted. -/
theorem eventually_exists_central_pi_unitBlock_surplus_before_eight_scale
    (hSource : IrrationalityMeasureBelow Real.pi ((36 : ℝ) / 5)) :
    ∃ k0 : ℕ, ∀ k : ℕ, max 3 k0 ≤ k →
      ∃ n A : ℕ, n < 8 * 10 ^ k ∧ A < 10 ^ k ∧
        (3 / 20 : ℝ) * (10 ^ k : ℕ) <
          (10 ^ k : ℕ) *
              (primitiveBoundaryFourierBlockSum (10 ^ k) A n 1).re -
            signedBlockPotential (10 ^ k) := by
  obtain ⟨Q0, hIrr⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality
      (sourceBelow36Fifths_implies_sourceBelowEight hSource)
  refine ⟨Q0, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := (le_max_left 3 Q0).trans hk
  have hQ0k : Q0 ≤ k := (le_max_right 3 Q0).trans hk
  have hkq : k ≤ 10 ^ k := self_le_pow_ten k
  have hQ0q : Q0 ≤ 10 ^ k := hQ0k.trans hkq
  have hQ0pow : Q0 ≤ 10 ^ (10 ^ k) :=
    hQ0q.trans (self_le_pow_ten (10 ^ k))
  obtain ⟨m, hqm, hm8, hmLow, hmHigh⟩ :=
    exists_piOrbit_mem_central_chamber_Icc Q0 (10 ^ k) hIrr
      (Nat.one_le_pow k 10 (by omega)) hQ0pow
  let n := m - k
  have hkm : k ≤ m := hkq.trans hqm
  have hn8 : n < 8 * 10 ^ k := by
    dsimp [n]
    omega
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
  exact ⟨n, A, hn8, hA,
    central_unitBlock_surplus_gt_three_div_twenty k A n hk3 y hy hyCoord⟩

/-- Fresh-horizon form of the conditional actual-pi seed. After a
premise-dependent onset, the positive literal unit starts in the exact T189
fresh block `[q, 10*q)`. This asserts neither positivity of the whole fresh
block nor a same-child horizon transport. -/
theorem eventually_exists_central_pi_unitBlock_surplus_in_fresh_horizon
    (hSource : IrrationalityMeasureBelow Real.pi ((36 : ℝ) / 5)) :
    ∃ k0 : ℕ, ∀ k : ℕ, max 3 k0 ≤ k →
      ∃ n A : ℕ, 10 ^ k ≤ n ∧ n < 10 * 10 ^ k ∧ A < 10 ^ k ∧
        (3 / 20 : ℝ) * (10 ^ k : ℕ) <
          (10 ^ k : ℕ) *
              (primitiveBoundaryFourierBlockSum (10 ^ k) A n 1).re -
            signedBlockPotential (10 ^ k) := by
  obtain ⟨Q0, hIrr⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality
      (sourceBelow36Fifths_implies_sourceBelowEight hSource)
  refine ⟨Q0, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := (le_max_left 3 Q0).trans hk
  have hQ0k : Q0 ≤ k := (le_max_right 3 Q0).trans hk
  have hQ0s : Q0 ≤ 10 ^ k + k := hQ0k.trans (Nat.le_add_left k (10 ^ k))
  have hQ0pow : Q0 ≤ 10 ^ (10 ^ k + k) :=
    hQ0s.trans (self_le_pow_ten (10 ^ k + k))
  obtain ⟨m, hsm, hm8, hmLow, hmHigh⟩ :=
    exists_piOrbit_mem_central_chamber_Icc Q0 (10 ^ k + k) hIrr
      ((Nat.one_le_pow k 10 (by omega)).trans (Nat.le_add_right _ _)) hQ0pow
  let n := m - k
  have hkm : k ≤ m := (Nat.le_add_left k (10 ^ k)).trans hsm
  have hqn : 10 ^ k ≤ n := by
    dsimp [n]
    omega
  have hseven : 7 * k < 2 * 10 ^ k :=
    seven_mul_lt_two_mul_pow_ten k hk3
  have hn10 : n < 10 * 10 ^ k := by
    dsimp [n]
    omega
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
  exact ⟨n, A, hqn, hn10, hA,
    central_unitBlock_surplus_gt_three_div_twenty k A n hk3 y hy hyCoord⟩

end Theory.PiDigits.T194CentralPiReturnSeed

#print axioms Theory.PiDigits.T194CentralPiReturnSeed.exists_central_pi_unitBlock_surplus
#print axioms
  Theory.PiDigits.T194CentralPiReturnSeed.eventually_exists_central_pi_unitBlock_surplus_before_eight_scale
#print axioms
  Theory.PiDigits.T194CentralPiReturnSeed.eventually_exists_central_pi_unitBlock_surplus_in_fresh_horizon
