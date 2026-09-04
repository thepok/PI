import TheoryLib.PiQuantitativeBlockHitting.T191T191CentralBoundaryKernelFloor
import TheoryLib.PiQuantitativeBlockHitting.T194T194CentralPiReturnSeed
import Mathlib

/-!
# T228: central-return appendix

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t228; each task compiled and
axiom-checked; assembled by Claude Opus 5

All eight tasks share one byte-identical starter and each later task embedded
the earlier lemmas verbatim, so every declaration appears once here.
-/

noncomputable section
set_option autoImplicit false

namespace Theory.PiDigits.T228CentralReturnAppendix

open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.LongLagBlockCollisionDecay.T4
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.T191CentralBoundaryKernelFloor

def decimalOrbit (x : ℝ) (n : ℕ) : ℝ :=
  Int.fract ((10 : ℝ) ^ n * x)

def centralCellIndex (x : ℝ) (k n : ℕ) : ℕ :=
  ⌊((10 ^ k : ℕ) : ℝ) * decimalOrbit x n⌋₊

def centralOffset (x : ℝ) (k n : ℕ) : ℝ :=
  ((10 ^ k : ℕ) : ℝ) * decimalOrbit x n -
    centralCellIndex x k n - 1 / 2

def nextDecimalDigit (x : ℝ) (n : ℕ) : ℕ :=
  ⌊10 * decimalOrbit x n⌋₊

def CentralChamber (t : ℝ) : Prop := 1 / 11 ≤ t ∧ t ≤ 10 / 11

def BAκ (κ x : ℝ) : Prop :=
  0 < κ ∧ ∀ p : ℤ, ∀ q : ℕ, 0 < q →
    κ / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / (q : ℝ)|

-- Verbatim T138 helper definition.
def decimalCylinderCenter (q A : ℕ) : ℝ := (2 * A + 1 : ℝ) / (2 * q)

structure CentralWitness
    (x : ℝ) (k n A : ℕ) (y : ℝ) : Prop where
  hk : 3 ≤ k
  hnLower : 10 ^ k + 1 ≤ n
  hnUpper : n < 10 * 10 ^ k
  hA : A < 10 ^ k
  hAfloor : A = ⌊((10 ^ k : ℕ) : ℝ) * decimalOrbit x n⌋₊
  hyDef : y = ((10 ^ k : ℕ) : ℝ) * decimalOrbit x n - (A : ℝ) - 1 / 2
  hy : |y| ≤ 9 / 22
  hCoord :
    decimalOrbit x n - decimalCylinderCenter (10 ^ k) A =
      y / (10 ^ k : ℕ)

/-! ### Orbit basics and the central-offset dictionary

Tasks `pi-t228-central-return-01-central-offset-eq-shifted-orbit`,
`-02-abs-central-offset-le-iff` and
`-03-next-decimal-digit-interior-gives-central`. -/

lemma decimalOrbit_nonneg (x : ℝ) (n : ℕ) : 0 ≤ decimalOrbit x n :=
  Int.fract_nonneg _

lemma decimalOrbit_lt_one (x : ℝ) (n : ℕ) : decimalOrbit x n < 1 :=
  Int.fract_lt_one _

lemma decimalOrbit_add (x : ℝ) (n k : ℕ) :
    decimalOrbit x (n + k) = Int.fract (((10 ^ k : ℕ) : ℝ) * decimalOrbit x n) := by
  unfold decimalOrbit
  refine (Int.fract_eq_fract.2 ⟨-((10 ^ k : ℤ) * ⌊(10 : ℝ) ^ n * x⌋), ?_⟩).symm
  push_cast
  rw [Int.fract]
  ring

lemma decimalOrbit_succ (x : ℝ) (n : ℕ) :
    decimalOrbit x (n + 1) = Int.fract (10 * decimalOrbit x n) := by
  simpa using decimalOrbit_add x n 1

lemma centralOffset_eq_shiftedOrbit
    (x : ℝ) (k n : ℕ) :
    centralOffset x k n = decimalOrbit x (n + k) - 1 / 2 := by
  have hnn : (0 : ℝ) ≤ ((10 ^ k : ℕ) : ℝ) * decimalOrbit x n :=
    mul_nonneg (by positivity) (decimalOrbit_nonneg x n)
  rw [decimalOrbit_add x n k, Int.fract, centralOffset, centralCellIndex,
    natCast_floor_eq_intCast_floor hnn]

lemma abs_centralOffset_le_iff
    (x : ℝ) (k n : ℕ) :
    |centralOffset x k n| ≤ 9 / 22 ↔
      CentralChamber (decimalOrbit x (n + k)) := by
  rw [centralOffset_eq_shiftedOrbit, abs_le, CentralChamber]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma nextDecimalDigit_interior_gives_central
    {x : ℝ} {n : ℕ}
    (h1 : 1 ≤ nextDecimalDigit x n)
    (h8 : nextDecimalDigit x n ≤ 8) :
    decimalOrbit x n ∈ Set.Ico (1 / 10 : ℝ) (9 / 10) ∧
      CentralChamber (decimalOrbit x n) := by
  have hnn : (0 : ℝ) ≤ 10 * decimalOrbit x n := by
    have := decimalOrbit_nonneg x n; linarith
  have hlow : (1 : ℝ) ≤ 10 * decimalOrbit x n := by
    have := (Nat.le_floor_iff hnn).1 h1
    simpa using this
  have hhigh : 10 * decimalOrbit x n < 9 := by
    have := Nat.lt_of_floor_lt (a := 10 * decimalOrbit x n) (n := 9)
      (by unfold nextDecimalDigit at h8; omega)
    exact_mod_cast this
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ### Central returns

Tasks `pi-t228-central-return-04-irrational-arbitrarily-late-central-returns`,
`-05-measure-below-eight-timed-central-returns`,
`-06-badly-approximable-implies-measure-below-eight` and
`-07-measure-below-eight-eventually-central-witness`. -/

lemma orbit_low_step (x : ℝ) (j : ℕ) (hlow : decimalOrbit x j < 1 / 11)
    (havoid : ¬ CentralChamber (decimalOrbit x (j + 1))) :
    decimalOrbit x (j + 1) = 10 * decimalOrbit x j ∧
      decimalOrbit x (j + 1) < 1 / 11 := by
  have hx0 := decimalOrbit_nonneg x j
  have hten0 : (0 : ℝ) ≤ 10 * decimalOrbit x j := by linarith
  have hten1 : 10 * decimalOrbit x j < 1 := by linarith
  have hstep : decimalOrbit x (j + 1) = 10 * decimalOrbit x j := by
    rw [decimalOrbit_succ, Int.fract_eq_self.2 ⟨hten0, hten1⟩]
  refine ⟨hstep, ?_⟩
  by_contra hnot
  exact havoid ⟨le_of_not_gt hnot, by rw [hstep]; linarith⟩

lemma orbit_high_step (x : ℝ) (j : ℕ) (hhigh : 10 / 11 < decimalOrbit x j)
    (havoid : ¬ CentralChamber (decimalOrbit x (j + 1))) :
    1 - decimalOrbit x (j + 1) = 10 * (1 - decimalOrbit x j) ∧
      10 / 11 < decimalOrbit x (j + 1) := by
  have hx1 := decimalOrbit_lt_one x j
  have hfloor : ⌊10 * decimalOrbit x j⌋ = (9 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  have hstep : decimalOrbit x (j + 1) = 10 * decimalOrbit x j - 9 := by
    rw [decimalOrbit_succ, Int.fract, hfloor]
    push_cast
    ring
  refine ⟨by rw [hstep]; ring, ?_⟩
  by_contra hnot
  exact havoid ⟨by rw [hstep]; linarith, le_of_not_gt hnot⟩

lemma orbit_low_iterate (x : ℝ) (s L : ℕ) (hlow : decimalOrbit x s < 1 / 11)
    (havoid : ∀ j : ℕ, s ≤ j → j ≤ s + L → ¬ CentralChamber (decimalOrbit x j)) :
    decimalOrbit x (s + L) = (10 : ℝ) ^ L * decimalOrbit x s ∧
      decimalOrbit x (s + L) < 1 / 11 := by
  induction L with
  | zero => exact ⟨by norm_num, hlow⟩
  | succ L ih =>
      obtain ⟨hiter, hend⟩ := ih (fun j hsj hj => havoid j hsj (by omega))
      obtain ⟨hstep, hlt⟩ := orbit_low_step x (s + L) hend
        (havoid (s + L + 1) (by omega) (by omega))
      refine ⟨?_, by rw [show s + (L + 1) = s + L + 1 by omega]; exact hlt⟩
      rw [show s + (L + 1) = s + L + 1 by omega, hstep, hiter, pow_succ]
      ring

lemma orbit_high_iterate (x : ℝ) (s L : ℕ) (hhigh : 10 / 11 < decimalOrbit x s)
    (havoid : ∀ j : ℕ, s ≤ j → j ≤ s + L → ¬ CentralChamber (decimalOrbit x j)) :
    1 - decimalOrbit x (s + L) = (10 : ℝ) ^ L * (1 - decimalOrbit x s) ∧
      10 / 11 < decimalOrbit x (s + L) := by
  induction L with
  | zero => exact ⟨by norm_num, hhigh⟩
  | succ L ih =>
      obtain ⟨hiter, hend⟩ := ih (fun j hsj hj => havoid j hsj (by omega))
      obtain ⟨hstep, hlt⟩ := orbit_high_step x (s + L) hend
        (havoid (s + L + 1) (by omega) (by omega))
      refine ⟨?_, by rw [show s + (L + 1) = s + L + 1 by omega]; exact hlt⟩
      rw [show s + (L + 1) = s + L + 1 by omega, hstep, hiter, pow_succ]
      ring

lemma self_le_pow_ten (s : ℕ) : s ≤ 10 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ]
    have hp0 : 0 < 10 ^ s := pow_pos (by omega) _
    omega

theorem irrational_arbitrarily_late_central_returns
    {x : ℝ} (hx : Irrational x) :
    ∀ L : ℕ, ∃ m : ℕ, L ≤ m ∧ CentralChamber (decimalOrbit x m) := by
  intro lower
  by_contra hnone
  push Not at hnone
  have havoid (L j : ℕ) (hlj : lower ≤ j) (hju : j ≤ lower + L) :
      ¬ CentralChamber (decimalOrbit x j) := hnone j hlj
  have hstart : decimalOrbit x lower < 1 / 11 ∨ 10 / 11 < decimalOrbit x lower := by
    by_cases hlow : decimalOrbit x lower < 1 / 11
    · exact Or.inl hlow
    · rcases lt_or_ge (10 / 11 : ℝ) (decimalOrbit x lower) with h | h
      · exact Or.inr h
      · exact absurd ⟨le_of_not_gt hlow, h⟩ (hnone lower le_rfl)
  rcases hstart with hlow | hhigh
  · have hzero : decimalOrbit x lower = 0 := by
      have hx0 := decimalOrbit_nonneg x lower
      refine le_antisymm ?_ hx0
      by_contra hnot
      have hxpos : 0 < decimalOrbit x lower := lt_of_not_ge hnot
      obtain ⟨L, hL⟩ := exists_nat_gt ((1 / 11 : ℝ) / decimalOrbit x lower)
      have hLPow : (L : ℝ) ≤ (10 : ℝ) ^ L := by
        exact_mod_cast self_le_pow_ten L
      have hlarge : (1 / 11 : ℝ) < (10 : ℝ) ^ L * decimalOrbit x lower :=
        (div_lt_iff₀ hxpos).mp (hL.trans_le hLPow)
      obtain ⟨hiter, hend⟩ := orbit_low_iterate x lower L hlow (havoid L)
      rw [hiter] at hend
      exact (not_lt_of_ge hlarge.le) hend
    have hfract : Int.fract ((10 : ℝ) ^ lower * x) = 0 := hzero
    rcases Int.fract_eq_zero_iff.mp hfract with ⟨z, hz⟩
    have hirr : Irrational ((10 : ℝ) ^ lower * x) := by
      simpa using hx.natCast_mul (m := 10 ^ lower) (by positivity)
    exact hirr.ne_rat (z : ℚ) (by simpa using hz.symm)
  · have hx1 := decimalOrbit_lt_one x lower
    have hdelta : 0 < 1 - decimalOrbit x lower := by linarith
    obtain ⟨L, hL⟩ := exists_nat_gt ((1 / 11 : ℝ) / (1 - decimalOrbit x lower))
    have hLPow : (L : ℝ) ≤ (10 : ℝ) ^ L := by
      exact_mod_cast self_le_pow_ten L
    have hlarge : (1 / 11 : ℝ) < (10 : ℝ) ^ L * (1 - decimalOrbit x lower) :=
      (div_lt_iff₀ hdelta).mp (hL.trans_le hLPow)
    obtain ⟨hiter, hend⟩ := orbit_high_iterate x lower L hhigh (havoid L)
    have hsmall : 1 - decimalOrbit x (lower + L) < 1 / 11 := by linarith
    rw [hiter] at hsmall
    exact (not_lt_of_ge hlarge.le) hsmall

theorem measureBelow_eight_timed_central_returns
    {x : ℝ} (hSource : IrrationalityMeasureBelow x 8) :
    ∃ s0 : ℕ, ∀ s : ℕ, max 1 s0 ≤ s →
      ∃ m : ℕ, s ≤ m ∧ m ≤ 8 * s ∧
        CentralChamber (decimalOrbit x m) := by
  obtain ⟨μ, hμ, hS⟩ := hSource
  have hε : 0 < (8 : ℝ) - μ := sub_pos.mpr hμ
  obtain ⟨Q0, hQ0⟩ := hS (8 - μ) hε
  have hQ8 : ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ p : ℤ,
      1 / (q : ℝ) ^ (8 : ℝ) < |x - (p : ℝ) / q| := by
    intro q hq hq0 p
    have h := hQ0 q hq hq0 p
    have : μ + (8 - μ) = (8 : ℝ) := by ring
    simpa only [this] using h
  refine ⟨Q0, ?_⟩
  intro s hs
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have hsQ : Q0 ≤ s := le_trans (le_max_right _ _) hs
  by_contra hnone
  push Not at hnone
  set d : ℕ := 10 ^ s with hd
  have hQ0d : Q0 ≤ d := le_trans hsQ (self_le_pow_ten s)
  have hd0 : 0 < d := by positivity
  have hdR : (0 : ℝ) < d := by positivity
  have hdCast : (d : ℝ) = (10 : ℝ) ^ s := by simp [hd]
  have havoid : ∀ j : ℕ, s ≤ j → j ≤ s + 7 * s →
      ¬ CentralChamber (decimalOrbit x j) := by
    intro j hsj hjs
    exact hnone j hsj (by omega)
  have hstart : decimalOrbit x s < 1 / 11 ∨ 10 / 11 < decimalOrbit x s := by
    by_cases hlow : decimalOrbit x s < 1 / 11
    · exact Or.inl hlow
    · rcases lt_or_ge (10 / 11 : ℝ) (decimalOrbit x s) with h | h
      · exact Or.inr h
      · exact absurd ⟨le_of_not_gt hlow, h⟩ (havoid s le_rfl (by omega))
  rcases hstart with hlow | hhigh
  · obtain ⟨hiter, hend⟩ := orbit_low_iterate x s (7 * s) hlow havoid
    set p : ℤ := ⌊(10 : ℝ) ^ s * x⌋ with hp
    have horbit : decimalOrbit x s = (10 : ℝ) ^ s * x - p := by
      rw [decimalOrbit, Int.fract]
    have hx0 := decimalOrbit_nonneg x s
    have hsmall : decimalOrbit x s * (d : ℝ) ^ 7 < 1 := by
      calc
        decimalOrbit x s * (d : ℝ) ^ 7 =
            (10 : ℝ) ^ (7 * s) * decimalOrbit x s := by
          rw [hdCast, ← pow_mul]; ring
        _ = decimalOrbit x (s + 7 * s) := hiter.symm
        _ < 1 / 11 := hend
        _ < 1 := by norm_num
    have hUpper : |x - (p : ℝ) / (d : ℝ)| < 1 / (d : ℝ) ^ (8 : ℝ) := by
      have heq : x - (p : ℝ) / (d : ℝ) = decimalOrbit x s / d := by
        rw [hdCast]
        field_simp
        nlinarith [horbit]
      rw [heq, abs_of_nonneg (by positivity)]
      rw [show (d : ℝ) ^ (8 : ℝ) = (d : ℝ) ^ (8 : ℕ) from Real.rpow_natCast d 8]
      apply (div_lt_div_iff₀ hdR (by positivity : (0 : ℝ) < (d : ℝ) ^ 8)).2
      field_simp
      nlinarith
    exact (not_lt_of_ge hUpper.le) (hQ8 d hQ0d hd0 p)
  · obtain ⟨hiter, hend⟩ := orbit_high_iterate x s (7 * s) hhigh havoid
    set p : ℤ := ⌊(10 : ℝ) ^ s * x⌋ + 1 with hp
    have horbit : decimalOrbit x s = (10 : ℝ) ^ s * x - (⌊(10 : ℝ) ^ s * x⌋ : ℝ) := by
      rw [decimalOrbit, Int.fract]
    have hx1 := decimalOrbit_lt_one x s
    have hsmall : (1 - decimalOrbit x s) * (d : ℝ) ^ 7 < 1 := by
      calc
        (1 - decimalOrbit x s) * (d : ℝ) ^ 7 =
            (10 : ℝ) ^ (7 * s) * (1 - decimalOrbit x s) := by
          rw [hdCast, ← pow_mul]; ring
        _ = 1 - decimalOrbit x (s + 7 * s) := hiter.symm
        _ < 1 / 11 := by linarith
        _ < 1 := by norm_num
    have hUpper : |x - (p : ℝ) / (d : ℝ)| < 1 / (d : ℝ) ^ (8 : ℝ) := by
      have heq : x - (p : ℝ) / (d : ℝ) = -(1 - decimalOrbit x s) / d := by
        rw [hp, hdCast]
        push_cast
        field_simp
        ring_nf at horbit ⊢
        linarith
      rw [heq, abs_div, abs_neg, abs_of_nonneg (by linarith), abs_of_pos hdR]
      rw [show (d : ℝ) ^ (8 : ℝ) = (d : ℝ) ^ (8 : ℕ) from Real.rpow_natCast d 8]
      apply (div_lt_div_iff₀ hdR (by positivity : (0 : ℝ) < (d : ℝ) ^ 8)).2
      field_simp
      nlinarith
    exact (not_lt_of_ge hUpper.le) (hQ8 d hQ0d hd0 p)

theorem badlyApproximable_implies_measureBelow_eight
    {κ x : ℝ} (hBA : BAκ κ x) :
    IrrationalityMeasureBelow x 8 := by
  obtain ⟨hκ, hApprox⟩ := hBA
  refine ⟨2, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨Q0, hQ0⟩ := exists_nat_gt (max 1 ((1 / κ) ^ (1 / ε)))
  refine ⟨Q0, ?_⟩
  intro q hq hq0 p
  have hqR1 : (1 : ℝ) < (q : ℝ) := by
    have : ((Q0 : ℝ)) ≤ (q : ℝ) := by exact_mod_cast hq
    have h1 : (1 : ℝ) ≤ max 1 ((1 / κ) ^ (1 / ε)) := le_max_left _ _
    linarith [hQ0]
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hbase : (0 : ℝ) < 1 / κ := by positivity
  have hlt : ((1 / κ) ^ (1 / ε) : ℝ) < (q : ℝ) := by
    have : ((Q0 : ℝ)) ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 : ((1 / κ) ^ (1 / ε) : ℝ) ≤ max 1 ((1 / κ) ^ (1 / ε)) := le_max_right _ _
    linarith [hQ0]
  have hpow : ((1 / κ) : ℝ) < (q : ℝ) ^ ε := by
    have hmono := Real.rpow_lt_rpow (Real.rpow_nonneg hbase.le _) hlt hε
    rw [← Real.rpow_mul hbase.le, one_div_mul_cancel (ne_of_gt hε),
      Real.rpow_one] at hmono
    exact hmono
  have hεpos : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hqR0 ε
  have hkq : (1 : ℝ) < κ * (q : ℝ) ^ ε := by
    have h := (div_lt_iff₀ hκ).mp hpow
    nlinarith
  have hsplit : (q : ℝ) ^ (2 + ε) = (q : ℝ) ^ (2 : ℕ) * (q : ℝ) ^ ε := by
    rw [Real.rpow_add hqR0]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hq2 : (0 : ℝ) < (q : ℝ) ^ (2 : ℕ) := by positivity
  have hmain : 1 / (q : ℝ) ^ (2 + ε) < κ / (q : ℝ) ^ 2 := by
    rw [hsplit]
    rw [div_lt_div_iff₀ (by positivity) hq2]
    nlinarith
  exact lt_of_lt_of_le hmain (hApprox p q hq0)

lemma self_le_pow_ten_pred (k : ℕ) (hk : 2 ≤ k) : k ≤ 10 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hp : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow (k - 1) 10 (by omega)
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      omega

lemma eight_add_seven_mul_lt_two_mul_pow_ten (k : ℕ) (hk : 3 ≤ k) :
    8 + 7 * k < 2 * 10 ^ k := by
  have hkp := self_le_pow_ten_pred k (by omega)
  have hp : 0 < 10 ^ (k - 1) := pow_pos (by omega) _
  rw [show k = (k - 1) + 1 by omega, pow_succ]
  omega

theorem measureBelow_eight_eventually_centralWitness
    {x : ℝ} (hSource : IrrationalityMeasureBelow x 8) :
    ∃ k0 : ℕ, ∀ k : ℕ, max 3 k0 ≤ k →
      ∃ n A : ℕ, ∃ y : ℝ, CentralWitness x k n A y := by
  obtain ⟨s0, hs0⟩ := measureBelow_eight_timed_central_returns hSource
  refine ⟨s0, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hks0 : s0 ≤ k := le_trans (le_max_right _ _) hk
  set s : ℕ := 10 ^ k + 1 + k with hsdef
  have hks : k ≤ 10 ^ k := self_le_pow_ten k
  have hsbig : max 1 s0 ≤ s := by
    refine max_le ?_ ?_ <;> omega
  obtain ⟨m, hm1, hm2, hcentral⟩ := hs0 s hsbig
  have harith := eight_add_seven_mul_lt_two_mul_pow_ten k hk3
  refine ⟨m - k, centralCellIndex x k (m - k), centralOffset x k (m - k), ?_⟩
  have hmk : m - k + k = m := by omega
  have hnn : (0 : ℝ) ≤ ((10 ^ k : ℕ) : ℝ) * decimalOrbit x (m - k) :=
    mul_nonneg (by positivity) (decimalOrbit_nonneg x (m - k))
  refine
    { hk := hk3
      hnLower := by omega
      hnUpper := by omega
      hA := ?_
      hAfloor := rfl
      hyDef := rfl
      hy := ?_
      hCoord := ?_ }
  · rw [centralCellIndex, Nat.floor_lt hnn]
    have hlt := decimalOrbit_lt_one x (m - k)
    have : ((10 ^ k : ℕ) : ℝ) * decimalOrbit x (m - k) < ((10 ^ k : ℕ) : ℝ) * 1 := by
      apply mul_lt_mul_of_pos_left hlt (by positivity)
    simpa using this
  · rw [abs_centralOffset_le_iff, hmk]
    exact hcentral
  · have hpos : (0 : ℝ) < ((10 ^ k : ℕ) : ℝ) := by positivity
    rw [decimalCylinderCenter, centralOffset]
    field_simp
    ring

/-! ### Discharged badly-approximable forms

`badlyApproximable_implies_measureBelow_eight` (task
`pi-t228-central-return-06`) supplies the named exponent-eight premise of tasks
`-05` and `-07`, so both are recorded here with that premise discharged. -/

/-- Discharged form of `measureBelow_eight_timed_central_returns`. -/
theorem badlyApproximable_timed_central_returns
    {κ x : ℝ} (hBA : BAκ κ x) :
    ∃ s0 : ℕ, ∀ s : ℕ, max 1 s0 ≤ s →
      ∃ m : ℕ, s ≤ m ∧ m ≤ 8 * s ∧
        CentralChamber (decimalOrbit x m) :=
  measureBelow_eight_timed_central_returns
    (badlyApproximable_implies_measureBelow_eight hBA)

/-- Discharged form of `measureBelow_eight_eventually_centralWitness`. -/
theorem badlyApproximable_eventually_centralWitness
    {κ x : ℝ} (hBA : BAκ κ x) :
    ∃ k0 : ℕ, ∀ k : ℕ, max 3 k0 ≤ k →
      ∃ n A : ℕ, ∃ y : ℝ, CentralWitness x k n A y :=
  measureBelow_eight_eventually_centralWitness
    (badlyApproximable_implies_measureBelow_eight hBA)

/-! ### The T191 boundary floor at a central witness

Task `pi-t228-central-return-08-central-witness-boundary-floor`. -/

lemma centralWitness_boundaryFloor
    {x y : ℝ} {k n A : ℕ}
    (h : CentralWitness x k n A y) :
    (4859 : ℝ) / 10000 <
      (boundaryMinorant (10 ^ k) (y / (10 ^ k : ℕ))).re :=
  boundaryMinorant_re_gt_4859_div_10000 k h.hk y h.hy


end Theory.PiDigits.T228CentralReturnAppendix
