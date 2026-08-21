import TheoryLib.PiLongLagBlockCollisionDecay.T31T31CrossBlockAlmostEverywhere
import TheoryLib.PiLongLagBlockCollisionDecay.T87T87RecordDiagonalCriticalBand
import TheoryLib.PiLongLagBlockCollisionDecay.T90T90CenteredCriticalBandCore
import TheoryLib.PiLongLagBlockCollisionDecay.T97T97VariablePhaseBridge
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# T104: probability closure for the exact variable-phase critical band

Canonical local source: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file concerns only the Lebesgue-variable-phase residual sibling A12. It
proves no statement at `Real.pi` and no instance of C1, C2, or C3.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T104

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T87
open Theory.PiDigits.LongLagBlockCollisionDecay.T90
open Theory.PiDigits.LongLagBlockCollisionDecay.T97
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- The exact positive integers in the inclusive critical band
`10^m <= N^2 <= 2*10^m`. -/
def criticalBand (m : ℕ) : Finset ℕ :=
  Finset.Icc (Nat.sqrt (10 ^ m - 1) + 1) (Nat.sqrt (2 * 10 ^ m))

theorem mem_criticalBand_iff {m N : ℕ} :
    N ∈ criticalBand m ↔
      1 ≤ N ∧ 10 ^ m ≤ N ^ 2 ∧ N ^ 2 ≤ 2 * 10 ^ m := by
  rw [criticalBand, Finset.mem_Icc]
  constructor
  · rintro ⟨hlower, hupper⟩
    have hsqrtLower : Nat.sqrt (10 ^ m - 1) < N := by omega
    have hlower' : 10 ^ m - 1 < N ^ 2 := Nat.sqrt_lt'.mp hsqrtLower
    have hpow : 0 < 10 ^ m := pow_pos (by omega) _
    exact ⟨by nlinarith, by omega, Nat.le_sqrt'.mp hupper⟩
  · rintro ⟨hN, hlower, hupper⟩
    have hpow : 0 < 10 ^ m := pow_pos (by omega) _
    have hlower' : 10 ^ m - 1 < N ^ 2 := by omega
    exact ⟨by
      have := Nat.sqrt_lt'.mpr hlower'
      omega, Nat.le_sqrt'.mpr hupper⟩

/-- Exact count of the positive integer critical band. -/
theorem criticalBand_card_exact (m : ℕ) :
    (criticalBand m).card =
      Nat.sqrt (2 * 10 ^ m) - Nat.sqrt (10 ^ m - 1) := by
  simp [criticalBand, Nat.card_Icc]

theorem criticalBand_card_le_two_mul_four_pow (m : ℕ) :
    (criticalBand m).card ≤ 2 * 4 ^ m := by
  rw [criticalBand_card_exact]
  have hpow : 10 ^ m ≤ 16 ^ m := Nat.pow_le_pow_left (by norm_num) m
  have hpowFour : (4 ^ m) ^ 2 = 16 ^ m := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hsquare : 2 * 10 ^ m ≤ (2 * 4 ^ m) ^ 2 := by
    rw [mul_pow, hpowFour]
    nlinarith
  have hsqrt : Nat.sqrt (2 * 10 ^ m) ≤ 2 * 4 ^ m := by
    simpa using Nat.sqrt_le_sqrt hsquare
  omega

/-- T90's exact critical normalization, retained as a separately named target
for the probability argument. -/
def criticalTarget (m N : ℕ) : ℝ :=
  ((10 ^ m : ℕ) : ℝ) *
    ((N : ℝ) + (N : ℝ) ^ 2 /
      Real.sqrt (((10 ^ m : ℕ) : ℝ)))

/-- The one-sided bad event for one exact critical-band pair. -/
def criticalBadSet (m N : ℕ) : Set ℝ :=
  Set.Ico (0 : ℝ) 1 ∩
    {α | criticalTarget m N <
      variableCenteredCriticalRemainder 0 m N α}

/-- The finite union over every positive `N` in the exact critical band. -/
def criticalScaleBadSet (m : ℕ) : Set ℝ :=
  ⋃ N ∈ criticalBand m, criticalBadSet m N

/-- Phases lying in infinitely many exact critical-scale bad events. -/
def criticalExceptionalSet : Set ℝ :=
  {α | {m : ℕ | α ∈ criticalScaleBadSet m}.Infinite}

/-- A measurable full-measure subset of the literal phase interval. -/
def criticalGoodPhaseSet : Set ℝ :=
  Set.Ico (0 : ℝ) 1 \ toMeasurable phaseMeasure criticalExceptionalSet

theorem criticalTarget_eq_criticalNormalization (m N : ℕ) :
    criticalTarget m N = criticalNormalization m N := by
  rfl

theorem criticalTarget_ge_two_mul
    {m N : ℕ} (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    2 * ((10 ^ m : ℕ) : ℝ) * (N : ℝ) ≤ criticalTarget m N := by
  have hinner :=
    (critical_innerNormalization_bounds m N hN hlower hupper).1
  rw [criticalTarget]
  have hmul := mul_le_mul_of_nonneg_left hinner
    (show (0 : ℝ) ≤ (10 ^ m : ℕ) by positivity)
  nlinarith

/-- Constant-tracked one-sided Chebyshev estimate obtained directly from
T97's checked second moment. -/
theorem criticalBadSet_measureReal_le
    (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hlower : 10 ^ m ≤ N ^ 2) (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    phaseMeasure.real (criticalBadSet m N) ≤
      235113200 * Real.log (2 * N) / ((10 ^ m : ℕ) : ℝ) := by
  let H : ℝ := ((10 ^ m : ℕ) : ℝ)
  let Z : ℝ := criticalTarget m N
  let X : ℝ → ℝ := variableCenteredCriticalRemainder 0 m N
  let deviation : Set ℝ := {α | Z ^ 2 ≤ X α ^ 2}
  have hH : 0 < H := by dsimp [H]; positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hZ : 0 < Z := by dsimp [Z, criticalTarget]; positivity
  have hsubset : criticalBadSet m N ⊆ deviation := by
    intro α hα
    have hX : 0 ≤ X α := hZ.le.trans hα.2.le
    exact (sq_le_sq₀ hZ.le hX).2 hα.2.le
  have hcontinuous : Continuous X := by
    rw [show X = centeredWidthWeightedSquareFunction (8 : ℝ) 1 0 m N by
      funext α
      exact variableCenteredCriticalRemainder_eq_T31 0 m N α]
    exact continuous_centeredWidthWeightedSquareFunction (8 : ℝ) 1 0 m N
  have hint : Integrable (fun α => X α ^ 2) phaseMeasure := by
    rw [phaseMeasure]
    exact (hcontinuous.pow 2).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hmarkov : Z ^ 2 * phaseMeasure.real deviation ≤
      ∫ α, X α ^ 2 ∂phaseMeasure :=
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all phaseMeasure fun α => sq_nonneg (X α)) hint (Z ^ 2)
  have hmono : phaseMeasure.real (criticalBadSet m N) ≤
      phaseMeasure.real deviation := measureReal_mono hsubset
  have hvariance := variableCenteredCriticalRemainder_secondMoment_le
    0 m N hm hN
  have hscaled : Z ^ 2 * phaseMeasure.real (criticalBadSet m N) ≤
      940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N) := by
    calc
      Z ^ 2 * phaseMeasure.real (criticalBadSet m N) ≤
          Z ^ 2 * phaseMeasure.real deviation :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg Z)
      _ ≤ ∫ α, X α ^ 2 ∂phaseMeasure := hmarkov
      _ ≤ 940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N) := by
        simpa [X, H] using hvariance
  have htarget : 2 * H * (N : ℝ) ≤ Z := by
    simpa [H, Z] using criticalTarget_ge_two_mul hN hlower hupper
  have htargetSq : (2 * H * (N : ℝ)) ^ 2 ≤ Z ^ 2 :=
    (sq_le_sq₀ (by positivity) hZ.le).2 htarget
  have hscaled' : (2 * H * (N : ℝ)) ^ 2 *
      phaseMeasure.real (criticalBadSet m N) ≤
        940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N) :=
    (mul_le_mul_of_nonneg_right htargetSq measureReal_nonneg).trans hscaled
  have hden : 0 < (2 * H * (N : ℝ)) ^ 2 := by positivity
  have hraw : phaseMeasure.real (criticalBadSet m N) ≤
      (940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N)) /
        (2 * H * (N : ℝ)) ^ 2 :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled')
  calc
    phaseMeasure.real (criticalBadSet m N) ≤
        (940452800 * H * (N : ℝ) ^ 2 * Real.log (2 * N)) /
          (2 * H * (N : ℝ)) ^ 2 := hraw
    _ = 235113200 * Real.log (2 * N) / H := by
      field_simp
      ring
    _ = 235113200 * Real.log (2 * N) / ((10 ^ m : ℕ) : ℝ) := by rfl

theorem natCast_add_one_le_four_mul_five_four_pow (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) ≤ 4 * (5 / 4 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hpow : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ m :=
        one_le_pow₀ (by norm_num)
      rw [pow_succ]
      push_cast at ih ⊢
      nlinarith

theorem log_two_mul_critical_le
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hupper : N ^ 2 ≤ 2 * 10 ^ m) :
    Real.log (2 * N) ≤ 8 * (5 / 4 : ℝ) ^ m := by
  have hpow : 10 ^ m ≤ 16 ^ m := Nat.pow_le_pow_left (by norm_num) m
  have hpowFour : (4 ^ m) ^ 2 = 16 ^ m := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hsquare : 2 * 10 ^ m ≤ (2 * 4 ^ m) ^ 2 := by
    rw [mul_pow, hpowFour]
    nlinarith
  have hNbound : N ≤ 2 * 4 ^ m := by
    by_contra h
    have hlt : 2 * 4 ^ m < N := Nat.lt_of_not_ge h
    have hsquareLt : (2 * 4 ^ m) ^ 2 < N ^ 2 := by
      simpa [pow_two] using Nat.mul_self_lt_mul_self hlt
    omega
  have harg : (2 : ℝ) * N ≤ 4 * (4 : ℝ) ^ m := by
    have hmul := Nat.mul_le_mul_left 2 hNbound
    have hmulR : (2 : ℝ) * N ≤ (2 : ℝ) * (2 * 4 ^ m : ℕ) := by
      exact_mod_cast hmul
    push_cast at hmulR
    nlinarith
  have hlogMono : Real.log (2 * N) ≤ Real.log (4 * (4 : ℝ) ^ m) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by positivity : (0 : ℝ) < 2 * N)
      (by positivity : (0 : ℝ) < 4 * (4 : ℝ) ^ m)
      (by simpa using harg)
  have hlogFour : Real.log (4 : ℝ) < 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith [Real.log_two_lt_d9]
  have hlogExpand : Real.log (4 * (4 : ℝ) ^ m) =
      ((m + 1 : ℕ) : ℝ) * Real.log 4 := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hlogExpand] at hlogMono
  have hadd := natCast_add_one_le_four_mul_five_four_pow m
  have hmnonneg : (0 : ℝ) ≤ (m + 1 : ℕ) := by positivity
  calc
    Real.log (2 * N) ≤ ((m + 1 : ℕ) : ℝ) * Real.log 4 := hlogMono
    _ ≤ 2 * ((m + 1 : ℕ) : ℝ) := by nlinarith
    _ ≤ 8 * (5 / 4 : ℝ) ^ m := by nlinarith

/-- Explicit geometric majorant for the finite union at scale `m`. -/
def criticalScaleMajorant (m : ℕ) : ℝ :=
  3761811200 * (1 / 2 : ℝ) ^ m

theorem criticalScaleBadSet_measureReal_le
    (m : ℕ) (hm : 1 ≤ m) :
    phaseMeasure.real (criticalScaleBadSet m) ≤ criticalScaleMajorant m := by
  have hunion : phaseMeasure.real (criticalScaleBadSet m) ≤
      ∑ N ∈ criticalBand m, phaseMeasure.real (criticalBadSet m N) := by
    exact measureReal_biUnion_finset_le (criticalBand m) (criticalBadSet m)
  have hpoint : ∀ N ∈ criticalBand m,
      phaseMeasure.real (criticalBadSet m N) ≤
        235113200 * (8 * (5 / 4 : ℝ) ^ m) /
          ((10 ^ m : ℕ) : ℝ) := by
    intro N hNmem
    have hband := mem_criticalBand_iff.mp hNmem
    calc
      phaseMeasure.real (criticalBadSet m N) ≤
          235113200 * Real.log (2 * N) / ((10 ^ m : ℕ) : ℝ) :=
        criticalBadSet_measureReal_le m N hm hband.1 hband.2.1 hband.2.2
      _ ≤ 235113200 * (8 * (5 / 4 : ℝ) ^ m) /
          ((10 ^ m : ℕ) : ℝ) := by
        gcongr
        exact log_two_mul_critical_le hm hband.1 hband.2.2
  have hcard := criticalBand_card_le_two_mul_four_pow m
  have hcardR : ((criticalBand m).card : ℝ) ≤ (2 * 4 ^ m : ℕ) := by
    exact_mod_cast hcard
  calc
    phaseMeasure.real (criticalScaleBadSet m) ≤
        ∑ N ∈ criticalBand m, phaseMeasure.real (criticalBadSet m N) := hunion
    _ ≤ ∑ N ∈ criticalBand m,
        235113200 * (8 * (5 / 4 : ℝ) ^ m) /
          ((10 ^ m : ℕ) : ℝ) := Finset.sum_le_sum hpoint
    _ = ((criticalBand m).card : ℝ) *
        (235113200 * (8 * (5 / 4 : ℝ) ^ m) /
          ((10 ^ m : ℕ) : ℝ)) := by simp
    _ ≤ ((2 * 4 ^ m : ℕ) : ℝ) *
        (235113200 * (8 * (5 / 4 : ℝ) ^ m) /
          ((10 ^ m : ℕ) : ℝ)) := by
      gcongr
    _ = criticalScaleMajorant m := by
      unfold criticalScaleMajorant
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [div_pow, div_pow]
      field_simp
      have hp : (5 : ℝ) ^ m * (2 : ℝ) ^ m = (10 : ℝ) ^ m := by
        rw [← mul_pow]
        norm_num
      norm_num [one_pow]
      nlinarith

/-- The exact exceptional-event measures are dominated by an explicit
geometric series, including the harmless scale `m=0`. -/
theorem summable_criticalScaleBadSet_measureReal :
    Summable (fun m => phaseMeasure.real (criticalScaleBadSet m)) := by
  refine (summable_nat_add_iff 1).1 ?_
  have hgeom : Summable (fun m : ℕ =>
      3761811200 * (1 / 2 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  apply hgeom.of_nonneg_of_le (fun _ => measureReal_nonneg)
  intro m
  calc
    phaseMeasure.real (criticalScaleBadSet (m + 1)) ≤
        criticalScaleMajorant (m + 1) :=
      criticalScaleBadSet_measureReal_le (m + 1) (by omega)
    _ ≤ 3761811200 * (1 / 2 : ℝ) ^ m := by
      unfold criticalScaleMajorant
      rw [pow_succ]
      have hp : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
      nlinarith

/-- Explicit total summability bound. -/
theorem tsum_criticalScaleBadSet_measureReal_le :
    (∑' m, phaseMeasure.real (criticalScaleBadSet m)) ≤ 3761811201 := by
  let f : ℕ → ℝ := fun m => phaseMeasure.real (criticalScaleBadSet m)
  let g : ℕ → ℝ := fun m => 3761811200 * (1 / 2 : ℝ) ^ (m + 1)
  have hf : Summable f := summable_criticalScaleBadSet_measureReal
  have hg : Summable g := by
    exact (summable_nat_add_iff 1).2
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
  have htail : (∑' m, f (m + 1)) ≤ ∑' m, g m := by
    exact ((summable_nat_add_iff 1).2 hf).tsum_le_tsum
      (fun m => criticalScaleBadSet_measureReal_le (m + 1) (by omega)) hg
  have hgSum : (∑' m, g m) = 3761811200 := by
    have hhas :=
      (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 1880905600
    have hgHas : HasSum g 3761811200 := by
      convert hhas using 1
      · funext m
        dsimp [g]
        rw [pow_succ]
        ring
      · norm_num
    exact hgHas.tsum_eq
  have hzero : f 0 ≤ 1 := by
    dsimp [f]
    calc
      phaseMeasure.real (criticalScaleBadSet 0) ≤ phaseMeasure.real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp [phaseMeasure]
  have hsplit := hf.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  change (∑' m, f m) ≤ _
  rw [← hsplit]
  rw [hgSum] at htail
  linarith

/-- First Borel-Cantelli for the exact finite-union critical events. -/
theorem phaseMeasure_criticalExceptionalSet_eq_zero :
    phaseMeasure criticalExceptionalSet = 0 := by
  have hreal := summable_criticalScaleBadSet_measureReal
  have heq :
      (fun m => ENNReal.ofReal
        (phaseMeasure.real (criticalScaleBadSet m))) =
      (fun m => phaseMeasure (criticalScaleBadSet m)) := by
    funext m
    exact ofReal_measureReal
  have hsum : (∑' m, phaseMeasure (criticalScaleBadSet m)) ≠ ∞ := by
    rw [← heq]
    exact hreal.tsum_ofReal_ne_top
  have hfinite : ∀ᵐ α ∂phaseMeasure,
      {m : ℕ | α ∈ criticalScaleBadSet m}.Finite :=
    ae_finite_setOf_mem hsum
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hfinite] with α hα
  exact fun hinfinite => hinfinite hα

theorem criticalGoodPhaseSet_spec :
    MeasurableSet criticalGoodPhaseSet ∧
      phaseMeasure criticalGoodPhaseSet = 1 ∧
      criticalGoodPhaseSet ⊆ Set.Ico (0 : ℝ) 1 := by
  refine ⟨measurableSet_Ico.diff (measurableSet_toMeasurable _ _), ?_,
    Set.diff_subset⟩
  rw [criticalGoodPhaseSet, measure_diff_null]
  · simp [phaseMeasure]
  · rw [measure_toMeasurable]
    exact phaseMeasure_criticalExceptionalSet_eq_zero

/-- Public literal audit joining T87's record domain to T90's core domain.
The half-open endpoints, weak lag cutoff, arithmetic exclusion, both Boolean
orientations, both signs, and decimal frequency are all visible in the type. -/
theorem exact_domain_orientation_sign_audit
    (Q0 m : ℕ) (B : DyadicBlock) (p : LongPairCore) (hm : 1 ≤ m) :
    p ∈ blockCoreDomain m B ↔
      (0 < p.1 ∧ m ≤ p.1 ∧ B.start ≤ p.2 + p.1 ∧
          p.2 + p.1 < B.finish) ∧
        (false, p) ∈ blockRecordDomain (8 : ℝ) 1 Q0 m B ∧
        (true, p) ∈ blockRecordDomain (8 : ℝ) 1 Q0 m B ∧
        ¬ArithmeticExcluded (8 : ℝ) 1 Q0 m p.2 p.1 ∧
        signedDecimalFrequency (false, p) =
          -(10 ^ p.2 * (10 ^ p.1 - 1) : ℕ) ∧
        signedDecimalFrequency (true, p) =
          (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ) := by
  rw [mem_blockCoreDomain_literal]
  have haudit := blockCoreDomain_orientation_exclusion_audit Q0 m B p hm
  constructor
  · intro hp
    have hcore : p ∈ blockCoreDomain m B :=
      mem_blockCoreDomain_literal.mpr hp
    exact ⟨hp, haudit.mp hcore⟩
  · rintro ⟨hp, _⟩
    exact hp

/-- Almost-everywhere exact variable-phase closure. The witnesses `B_alpha`
and `m0(alpha)` are chosen before every later scale, critical-band integer,
and permitted `Q0`. The second conjunct unfolds the complete centered
observable, including every canonical block, inclusive frequency, literal
width, endpoint, coefficient, and record diagonal. -/
theorem almostEverywhere_eventual_variableCenteredCriticalRemainder :
    MeasurableSet criticalGoodPhaseSet ∧
    phaseMeasure criticalGoodPhaseSet = 1 ∧
    criticalGoodPhaseSet ⊆ Set.Ico (0 : ℝ) 1 ∧
    ∀ α ∈ criticalGoodPhaseSet,
      ∃ B_alpha : ℝ, 1 ≤ B_alpha ∧
      ∃ m0 : ℕ, 1 ≤ m0 ∧
      ∀ m : ℕ, m0 ≤ m →
      ∀ N : ℕ, 1 ≤ N →
        10 ^ m ≤ N ^ 2 → N ^ 2 ≤ 2 * 10 ^ m →
      ∀ Q0 : ℕ,
        variableCenteredCriticalRemainder Q0 m N α ≤
            B_alpha * (((10 ^ m : ℕ) : ℝ) *
              ((N : ℝ) + (N : ℝ) ^ 2 /
                Real.sqrt (((10 ^ m : ℕ) : ℝ)))) ∧
        variableCenteredCriticalRemainder Q0 m N α =
          ((translatedCanonicalBlocks N).map fun B =>
            (4 * ∑ h ∈ Finset.Icc (1 : ℕ) (10 ^ m),
              (∑ p ∈ blockCoreDomain m B,
                Real.cos (2 * Real.pi * α * (h : ℝ) *
                  (10 ^ p.2 * (10 ^ p.1 - 1) : ℕ))) ^ 2) /
                Real.sqrt ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2)).sum -
            (10 ^ m : ℝ) *
              ((translatedCanonicalBlocks N).map fun B =>
                (2 * (blockCoreDomain m B).card : ℕ) /
                  Real.sqrt ((B.finish : ℝ) ^ 2 -
                    (B.start : ℝ) ^ 2)).sum := by
  refine ⟨criticalGoodPhaseSet_spec.1, criticalGoodPhaseSet_spec.2.1,
    criticalGoodPhaseSet_spec.2.2, ?_⟩
  intro α hα
  have hnotExceptional : α ∉ criticalExceptionalSet := by
    intro hmem
    exact hα.2 (subset_toMeasurable phaseMeasure _ hmem)
  have hfinite : {m : ℕ | α ∈ criticalScaleBadSet m}.Finite :=
    Set.not_infinite.mp hnotExceptional
  let S : Finset ℕ := hfinite.toFinset
  let m0 : ℕ := S.sup id + 1
  refine ⟨1, by norm_num, m0, by dsimp [m0]; omega, ?_⟩
  intro m hm0 N hN hlower hupper Q0
  have hm : 1 ≤ m := by
    have hm0pos : 1 ≤ m0 := by dsimp [m0]; omega
    omega
  have hmnotS : m ∉ S := by
    intro hmS
    have hle : m ≤ S.sup id := Finset.le_sup (f := id) hmS
    dsimp [m0] at hm0
    omega
  have hnotScale : α ∉ criticalScaleBadSet m := by
    intro hmem
    apply hmnotS
    simpa [S] using hmem
  have hNmem : N ∈ criticalBand m :=
    mem_criticalBand_iff.mpr ⟨hN, hlower, hupper⟩
  have hnotBad : α ∉ criticalBadSet m N := by
    intro hbad
    apply hnotScale
    rw [criticalScaleBadSet]
    simp only [Set.mem_iUnion]
    exact ⟨N, ⟨hNmem, hbad⟩⟩
  have hboundZero : variableCenteredCriticalRemainder 0 m N α ≤
      criticalTarget m N := by
    exact le_of_not_gt fun hgt => hnotBad ⟨hα.1, hgt⟩
  have hQ0 := variableCenteredCriticalRemainder_Q0_independent
    Q0 0 m N α hm
  constructor
  · rw [hQ0]
    simpa [criticalTarget] using hboundZero
  · exact variableCenteredCriticalRemainder_literal Q0 m N α hm

/-- Literal almost-everywhere form. It displays the null exceptional set and
the quantifier order `almost every alpha, exists B_alpha, exists m0, forall
m, N, Q0`; the preceding theorem exposes the complete finite observable. -/
theorem almostEverywhere_eventual_variableCenteredCriticalRemainder_ae :
    phaseMeasure criticalExceptionalSet = 0 ∧
    ∀ᵐ α ∂phaseMeasure,
      α ∈ criticalGoodPhaseSet ∧
      ∃ B_alpha : ℝ, 1 ≤ B_alpha ∧
      ∃ m0 : ℕ, 1 ≤ m0 ∧
      ∀ m : ℕ, m0 ≤ m →
      ∀ N : ℕ, 1 ≤ N →
        10 ^ m ≤ N ^ 2 → N ^ 2 ≤ 2 * 10 ^ m →
      ∀ Q0 : ℕ,
        variableCenteredCriticalRemainder Q0 m N α ≤
          B_alpha * (((10 ^ m : ℕ) : ℝ) *
            ((N : ℝ) + (N : ℝ) ^ 2 /
              Real.sqrt (((10 ^ m : ℕ) : ℝ)))) := by
  have hmain := almostEverywhere_eventual_variableCenteredCriticalRemainder
  have hmem : ∀ᵐ α ∂phaseMeasure, α ∈ criticalGoodPhaseSet := by
    apply (ae_mem_iff_measure_eq hmain.1.nullMeasurableSet).2
    rw [hmain.2.1, phaseMeasure_univ]
  refine ⟨phaseMeasure_criticalExceptionalSet_eq_zero, ?_⟩
  filter_upwards [hmem] with α hα
  refine ⟨hα, ?_⟩
  obtain ⟨B_alpha, hB, m0, hm0, hbound⟩ := hmain.2.2.2 α hα
  exact ⟨B_alpha, hB, m0, hm0, fun m hm N hN hlower hupper Q0 =>
    (hbound m hm N hN hlower hupper Q0).1⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T104

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.mem_criticalBand_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.criticalBand_card_exact
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.criticalBadSet_measureReal_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.criticalScaleBadSet_measureReal_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.summable_criticalScaleBadSet_measureReal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.tsum_criticalScaleBadSet_measureReal_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.phaseMeasure_criticalExceptionalSet_eq_zero
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.exact_domain_orientation_sign_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.almostEverywhere_eventual_variableCenteredCriticalRemainder
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T104.almostEverywhere_eventual_variableCenteredCriticalRemainder_ae
