import TheoryLib.PiQuantitativeBlockHitting.T21T21UnboundedFourierGap
import TheoryLib.PiDigits.T29FixedFrequencyResonance

/-!
# T22: divergent additive gap at every fixed nonzero frequency

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file extends T21 from frequency one to every *fixed* nonzero integer
frequency.  For such an `h`, the phase path of the decimal pi orbit is the
frequency-one phase path of the decimal orbit seeded by `{h*pi}`.  That seed
is irrational, so its decimal expansion cannot have boundedly many digit
changes.  T20's path-energy inequality then forces the additive gap

`N - ||sum_{j<N} exp(2*pi*i*h*10^j*pi)||`

to tend to positive infinity in the order-theoretic sense: every real
threshold is exceeded by every sufficiently long prefix.

The conclusion is additive rather than relative: it is compatible with
linear-size resonance at the same fixed frequency and therefore does not
contradict T29.  For example, the asymptotic size `N - sqrt N` has a divergent
additive gap but normalized size tending to one.  In particular, this file
proves neither decimal normality nor decimal disjunctivity of pi.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.AllFixedFrequencyGap

open Theory.PiDigits.DigitChangeFourierDefect
open Theory.PiDigits.UnboundedFourierGap

abbrev phase := Theory.PiDigits.T27.phase
abbrev exponentialSum := Theory.PiDigits.T27.exponentialSum
abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- Multiplication by ten advances an arbitrary base-ten fractional orbit. -/
lemma baseTenOrbit_succ (x : ℝ) (j : ℕ) :
    Theory.PiDigits.T20.baseTenOrbit x (j + 1) =
      Int.fract (10 * Theory.PiDigits.T20.baseTenOrbit x j) := by
  unfold Theory.PiDigits.T20.baseTenOrbit
  rw [show (10 : ℝ) ^ (j + 1) * x =
      10 * ((10 : ℝ) ^ j * x) by
    rw [pow_succ]
    ring]
  exact fract_ten_eq_fract_ten_fract _

/-- The `i`-th digit at the `j`-th orbit point is the `(j+i)`-th digit of
the seed. -/
lemma baseTenOrbit_digit (x : ℝ) (hx : 0 ≤ x) (j i : ℕ) :
    Theory.PiDigits.T20.decimalDigit
        (Theory.PiDigits.T20.baseTenOrbit x j) i =
      Theory.PiDigits.T20.decimalDigit x (j + i) := by
  exact Theory.PiDigits.T20.decimalDigit_baseTenOrbit x hx j i

/-- An irrational point in the decimal unit interval has unbounded prefix
digit-change count. -/
theorem irrational_decimal_changeCount_unbounded {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hirr : Irrational x) (B : ℕ) :
    ∃ N : ℕ, B < Theory.PiDigits.T18.changeCount
      (Theory.PiDigits.T20.decimalDigit x) N := by
  have haperiodic :
      ¬ DecimalFactorComplexity.EventuallyPeriodic
        (Theory.PiDigits.T20.decimalDigit x) := by
    intro hperiodic
    have hnotirr :=
      Theory.PiDigits.FactorComplexity.not_irrational_ofDigits_of_eventuallyPeriodic
        (Theory.PiDigits.T20.decimalDigit x) hperiodic
    apply hnotirr
    rw [show Real.ofDigits (Theory.PiDigits.T20.decimalDigit x) = x by
      simpa only [Theory.PiDigits.T20.decimalDigit] using
        (Real.ofDigits_digits (b := 10) (by norm_num) hx)]
    exact hirr
  by_contra hnot
  push Not at hnot
  exact haperiodic
    (eventuallyPeriodic_of_changeCount_bounded
      (Theory.PiDigits.T20.decimalDigit x) B hnot)

/-- Every adjacent digit change of a nonnegative seed gives an orbit
increment whose absolute representative lies in `[1/100, 9/10]`. -/
theorem baseTenOrbit_succ_sub_abs_bounds (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hchange : Theory.PiDigits.T20.decimalDigit x j ≠
      Theory.PiDigits.T20.decimalDigit x (j + 1)) :
    (1 / 100 : ℝ) ≤
        |Theory.PiDigits.T20.baseTenOrbit x (j + 1) -
          Theory.PiDigits.T20.baseTenOrbit x j| ∧
      |Theory.PiDigits.T20.baseTenOrbit x (j + 1) -
          Theory.PiDigits.T20.baseTenOrbit x j| ≤ (9 / 10 : ℝ) := by
  let a : Fin 10 := Theory.PiDigits.T20.decimalDigit x j
  let b : Fin 10 := Theory.PiDigits.T20.decimalDigit x (j + 1)
  let y : ℝ := Theory.PiDigits.T20.baseTenOrbit x j
  have hy : y ∈ Set.Ico (0 : ℝ) 1 :=
    Theory.PiDigits.T20.baseTenOrbit_mem_Ico x j
  have hzero : Real.digits y 10 0 = a := by
    simpa only [y, a, Theory.PiDigits.T20.decimalDigit, Nat.add_zero] using
      (baseTenOrbit_digit x hx j 0)
  have hone : Real.digits y 10 1 = b := by
    simpa only [y, b, Theory.PiDigits.T20.decimalDigit] using
      (baseTenOrbit_digit x hx j 1)
  have hcell := mem_two_digit_cylinder hy a b hzero hone
  have hincrement :
      Theory.PiDigits.T20.baseTenOrbit x (j + 1) -
          Theory.PiDigits.T20.baseTenOrbit x j =
        9 * y - a.val := by
    rw [baseTenOrbit_succ, fract_ten_eq_sub_first_digit a b hcell]
    simp only [y]
    ring
  rw [hincrement]
  exact decimal_increment_abs_bounds a b hcell
    (by simpa only [a, b] using hchange)

/-- A changed decimal edge of an arbitrary nonnegative seed has the same
rational chord lower bound as T20's pi specialization. -/
theorem baseTen_changed_edge_norm_lower (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hchange : Theory.PiDigits.T20.decimalDigit x j ≠
      Theory.PiDigits.T20.decimalDigit x (j + 1)) :
    (1 / 25 : ℝ) ≤
      ‖phase 1 (Theory.PiDigits.T20.baseTenOrbit x (j + 1)) -
        phase 1 (Theory.PiDigits.T20.baseTenOrbit x j)‖ := by
  obtain ⟨hlow, hhigh⟩ := baseTenOrbit_succ_sub_abs_bounds x hx j hchange
  have hsin := Theory.PiDigits.T27.abs_sin_pi_mul_lower
    (u := Theory.PiDigits.T20.baseTenOrbit x (j + 1) -
      Theory.PiDigits.T20.baseTenOrbit x j)
    (L := (1 / 50 : ℝ)) (by norm_num)
    (by norm_num at hlow ⊢; exact hlow)
    (by norm_num at hhigh ⊢; linarith)
  rw [norm_phase_sub_phase_eq,
    Theory.PiDigits.T27.norm_one_sub_phase_one]
  norm_num at hsin ⊢
  linarith

/-- Squared form of `baseTen_changed_edge_norm_lower`. -/
theorem baseTen_changed_edge_sq_lower (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hchange : Theory.PiDigits.T20.decimalDigit x j ≠
      Theory.PiDigits.T20.decimalDigit x (j + 1)) :
    (1 / 625 : ℝ) ≤
      ‖phase 1 (Theory.PiDigits.T20.baseTenOrbit x (j + 1)) -
        phase 1 (Theory.PiDigits.T20.baseTenOrbit x j)‖ ^ 2 := by
  have h := baseTen_changed_edge_norm_lower x hx j hchange
  have hn := norm_nonneg
    (phase 1 (Theory.PiDigits.T20.baseTenOrbit x (j + 1)) -
      phase 1 (Theory.PiDigits.T20.baseTenOrbit x j))
  norm_num at h ⊢
  nlinarith

/-- The orbit path energy receives at least `1/625` from each adjacent
digit change of its seed. -/
theorem baseTen_pathEnergy_ge_changeCount (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (Theory.PiDigits.T18.changeCount
        (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 625 ≤
      pathEnergy
        (fun j ↦ phase 1 (Theory.PiDigits.T20.baseTenOrbit x j)) N := by
  classical
  let changes := Theory.PiDigits.T18.changePositions
    (Theory.PiDigits.T20.decimalDigit x) N
  let edge : ℕ → ℝ := fun j ↦
    ‖phase 1 (Theory.PiDigits.T20.baseTenOrbit x (j + 1)) -
      phase 1 (Theory.PiDigits.T20.baseTenOrbit x j)‖ ^ 2
  have hsubset : changes ⊆ Finset.range (N - 1) := by
    intro j hj
    have hj' : j ∈
        (Finset.range (N - 1)).filter
          (fun i ↦ Theory.PiDigits.T20.decimalDigit x i ≠
            Theory.PiDigits.T20.decimalDigit x (i + 1)) := by
      simpa only [changes, Theory.PiDigits.T18.changePositions] using hj
    exact (Finset.mem_filter.mp hj').1
  have hlower : (∑ j ∈ changes, (1 / 625 : ℝ)) ≤
      ∑ j ∈ changes, edge j := by
    apply Finset.sum_le_sum
    intro j hj
    apply baseTen_changed_edge_sq_lower x hx
    have hj' : j ∈
        (Finset.range (N - 1)).filter
          (fun i ↦ Theory.PiDigits.T20.decimalDigit x i ≠
            Theory.PiDigits.T20.decimalDigit x (i + 1)) := by
      simpa only [changes, Theory.PiDigits.T18.changePositions] using hj
    exact (Finset.mem_filter.mp hj').2
  have hmono : (∑ j ∈ changes, edge j) ≤
      ∑ j ∈ Finset.range (N - 1), edge j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j _hj _hnot
    exact sq_nonneg _
  calc
    (Theory.PiDigits.T18.changeCount
          (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 625 =
        ∑ j ∈ changes, (1 / 625 : ℝ) := by
          simp only [Theory.PiDigits.T18.changeCount, changes,
            Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ j ∈ changes, edge j := hlower
    _ ≤ ∑ j ∈ Finset.range (N - 1), edge j := hmono
    _ = pathEnergy
        (fun j ↦ phase 1 (Theory.PiDigits.T20.baseTenOrbit x j)) N := rfl

/-- Generic T20 bridge: changes in a nonnegative seed force a squared
first-frequency Fourier defect for its base-ten orbit. -/
theorem baseTen_firstFrequency_defect_ge_digitChanges
    (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (N : ℝ) *
        (Theory.PiDigits.T18.changeCount
          (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 2500 ≤
      (N : ℝ) ^ 2 -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ ^ 2 := by
  have hpath := baseTen_pathEnergy_ge_changeCount x hx N
  have hdefect := defect_ge_mul_pathEnergy
    (fun j ↦ phase 1 (Theory.PiDigits.T20.baseTenOrbit x j)) N
    (fun i hi ↦ Theory.PiDigits.T27.norm_phase 1
      (Theory.PiDigits.T20.baseTenOrbit x i))
  calc
    (N : ℝ) *
          (Theory.PiDigits.T18.changeCount
            (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 2500 =
        (N : ℝ) / 4 *
          ((Theory.PiDigits.T18.changeCount
            (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 625) := by
              ring
    _ ≤ (N : ℝ) / 4 *
        pathEnergy
          (fun j ↦ phase 1 (Theory.PiDigits.T20.baseTenOrbit x j)) N := by
      gcongr
    _ ≤ (N : ℝ) ^ 2 -
        ‖∑ i ∈ Finset.range N,
          phase 1 (Theory.PiDigits.T20.baseTenOrbit x i)‖ ^ 2 := hdefect
    _ = (N : ℝ) ^ 2 -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ ^ 2 := rfl

/-- Pointwise additive spectral gap forced by changes in the same decimal
prefix of an arbitrary nonnegative seed. -/
theorem baseTen_firstFrequency_additiveGap_ge_digitChanges
    (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (Theory.PiDigits.T18.changeCount
        (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 5000 ≤
      (N : ℝ) -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ := by
  cases N with
  | zero =>
      simp [Theory.PiDigits.T18.changeCount,
        Theory.PiDigits.T18.changePositions,
        Theory.PiDigits.T27.exponentialSum]
  | succ n =>
      let N : ℕ := n + 1
      let R : ℝ :=
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖
      let C : ℝ :=
        (Theory.PiDigits.T18.changeCount
          (Theory.PiDigits.T20.decimalDigit x) N : ℝ)
      have hN : (0 : ℝ) < N := by positivity
      have hRnonneg : 0 ≤ R := norm_nonneg _
      have hR : R ≤ (N : ℝ) := by
        exact norm_exponentialSum_le
          (Theory.PiDigits.T20.baseTenOrbit x) N 1
      have hdefect := baseTen_firstFrequency_defect_ge_digitChanges x hx N
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

/-- For an irrational seed in `[0,1)`, the additive first-frequency gap is
unbounded over natural thresholds. -/
theorem irrational_decimal_additiveGap_unbounded_nat {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hirr : Irrational x) (B : ℕ) :
    ∃ N : ℕ, (B : ℝ) ≤
      (N : ℝ) -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ := by
  obtain ⟨N, hchange⟩ :=
    irrational_decimal_changeCount_unbounded hx hirr (5000 * B)
  refine ⟨N, ?_⟩
  have hgap := baseTen_firstFrequency_additiveGap_ge_digitChanges x hx.1 N
  have hcast : (5000 * B : ℕ) ≤
      Theory.PiDigits.T18.changeCount
        (Theory.PiDigits.T20.decimalDigit x) N := Nat.le_of_lt hchange
  have hcastReal : (5000 * B : ℝ) ≤
      (Theory.PiDigits.T18.changeCount
        (Theory.PiDigits.T20.decimalDigit x) N : ℝ) := by
    exact_mod_cast hcast
  calc
    (B : ℝ) = (5000 * B : ℝ) / 5000 := by ring
    _ ≤ (Theory.PiDigits.T18.changeCount
          (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 5000 := by
        gcongr
    _ ≤ (N : ℝ) -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ := hgap

/-- Real-threshold formulation of unboundedness for an irrational decimal
seed. -/
theorem irrational_decimal_additiveGap_unbounded {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hirr : Irrational x) (A : ℝ) :
    ∃ N : ℕ, A ≤
      (N : ℝ) -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ := by
  obtain ⟨B, hB⟩ := exists_nat_ge A
  obtain ⟨N, hN⟩ := irrational_decimal_additiveGap_unbounded_nat hx hirr B
  exact ⟨N, hB.trans hN⟩

/-- Strong rate-free form: the additive first-frequency gap of an irrational
decimal seed eventually exceeds every natural threshold. -/
theorem irrational_decimal_additiveGap_eventually_ge_nat {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hirr : Irrational x) (B : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (B : ℝ) ≤
      (N : ℝ) -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ := by
  obtain ⟨N₀, hchange⟩ :=
    irrational_decimal_changeCount_unbounded hx hirr (5000 * B)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hcountMono :
      Theory.PiDigits.T18.changeCount
          (Theory.PiDigits.T20.decimalDigit x) N₀ ≤
        Theory.PiDigits.T18.changeCount
          (Theory.PiDigits.T20.decimalDigit x) N :=
    changeCount_mono (Theory.PiDigits.T20.decimalDigit x) hN
  have hcount : (5000 * B : ℕ) ≤
      Theory.PiDigits.T18.changeCount
        (Theory.PiDigits.T20.decimalDigit x) N :=
    (Nat.le_of_lt hchange).trans hcountMono
  have hcountReal : (5000 * B : ℝ) ≤
      (Theory.PiDigits.T18.changeCount
        (Theory.PiDigits.T20.decimalDigit x) N : ℝ) := by
    exact_mod_cast hcount
  have hgap := baseTen_firstFrequency_additiveGap_ge_digitChanges x hx.1 N
  calc
    (B : ℝ) = (5000 * B : ℝ) / 5000 := by ring
    _ ≤ (Theory.PiDigits.T18.changeCount
          (Theory.PiDigits.T20.decimalDigit x) N : ℝ) / 5000 := by
        gcongr
    _ ≤ (N : ℝ) -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ := hgap

/-- Real-threshold eventual divergence for an irrational decimal seed. -/
theorem irrational_decimal_additiveGap_eventually_ge {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hirr : Irrational x) (A : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → A ≤
      (N : ℝ) -
        ‖exponentialSum (Theory.PiDigits.T20.baseTenOrbit x) N 1‖ := by
  obtain ⟨B, hB⟩ := exists_nat_ge A
  obtain ⟨N₀, hN₀⟩ :=
    irrational_decimal_additiveGap_eventually_ge_nat hx hirr B
  exact ⟨N₀, fun N hN ↦ hB.trans (hN₀ N hN)⟩

/-- Fractional seed whose frequency-one decimal orbit represents frequency
`h` on the decimal pi orbit. -/
def fixedFrequencySeed (h : ℤ) : ℝ :=
  Int.fract ((h : ℝ) * Real.pi)

lemma fixedFrequencySeed_mem_Ico (h : ℤ) :
    fixedFrequencySeed h ∈ Set.Ico (0 : ℝ) 1 := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Every nonzero integer multiple of pi has irrational fractional part. -/
theorem fixedFrequencySeed_irrational (h : ℤ) (h0 : h ≠ 0) :
    Irrational (fixedFrequencySeed h) := by
  rw [fixedFrequencySeed, Int.fract]
  exact (irrational_pi.intCast_mul h0).sub_intCast _

/-- Multiplying a real by a natural integer before taking fractional part
is insensitive to first replacing the real by its fractional part. -/
lemma fract_natCast_mul_fract (x : ℝ) (n : ℕ) :
    Int.fract ((n : ℝ) * Int.fract x) =
      Int.fract ((n : ℝ) * x) := by
  let z : ℤ := (n : ℤ) * ⌊x⌋
  have harg : (n : ℝ) * Int.fract x = (n : ℝ) * x - (z : ℝ) := by
    dsimp [z]
    rw [Int.fract]
    push_cast
    ring
  rw [harg, Int.fract_sub_intCast]

/-- The decimal orbit of `{h*pi}` is the fractional part of the unwrapped
integer-frequency pi orbit. -/
lemma fixedFrequencySeed_orbit_eq (h : ℤ) (j : ℕ) :
    Theory.PiDigits.T20.baseTenOrbit (fixedFrequencySeed h) j =
      Int.fract ((10 : ℝ) ^ j * (h : ℝ) * Real.pi) := by
  unfold Theory.PiDigits.T20.baseTenOrbit fixedFrequencySeed
  have hfract := fract_natCast_mul_fract
    ((h : ℝ) * Real.pi) (10 ^ j)
  convert hfract using 1 <;> push_cast <;> ring

/-- Pointwise phase conjugacy between the frequency-one orbit of `{h*pi}`
and frequency `h` on the decimal pi orbit. -/
theorem fixedFrequencySeed_phase_eq_piOrbit (h : ℤ) (j : ℕ) :
    phase 1 (Theory.PiDigits.T20.baseTenOrbit (fixedFrequencySeed h) j) =
      phase h (piOrbit j) := by
  rw [fixedFrequencySeed_orbit_eq]
  unfold phase Theory.PiDigits.T27.phase piOrbit
    Theory.PiDigits.T27.piFractionalOrbit
  rw [Theory.PiDigits.T29.phase_fract_eq_phase 1
      ((10 : ℝ) ^ j * (h : ℝ) * Real.pi),
    Theory.PiDigits.T29.phase_fract_eq_phase h
      ((10 : ℝ) ^ j * Real.pi)]
  congr 1
  push_cast
  ring

/-- Exact equality of the seed-orbit sum at frequency one and the original
pi-orbit sum at frequency `h`. -/
theorem fixedFrequencySeed_exponentialSum_eq (h : ℤ) (N : ℕ) :
    exponentialSum
        (Theory.PiDigits.T20.baseTenOrbit (fixedFrequencySeed h)) N 1 =
      exponentialSum piOrbit N h := by
  classical
  apply Finset.sum_congr rfl
  intro j hj
  exact fixedFrequencySeed_phase_eq_piOrbit h j

/-- Pointwise all-frequency form of the T20/T21 bridge.  The controlling
digit changes are those of the conjugate seed `{h*pi}`. -/
theorem pi_fixedFrequency_additiveGap_ge_seedDigitChanges
    (h : ℤ) (N : ℕ) :
    (Theory.PiDigits.T18.changeCount
        (Theory.PiDigits.T20.decimalDigit (fixedFrequencySeed h)) N : ℝ) /
        5000 ≤
      (N : ℝ) - ‖exponentialSum piOrbit N h‖ := by
  rw [← fixedFrequencySeed_exponentialSum_eq h N]
  exact baseTen_firstFrequency_additiveGap_ge_digitChanges
    (fixedFrequencySeed h) (fixedFrequencySeed_mem_Ico h).1 N

/-- For every fixed nonzero integer frequency, the additive pi-orbit gap
eventually exceeds every natural threshold. -/
theorem pi_fixedFrequency_additiveGap_eventually_ge_nat
    (h : ℤ) (h0 : h ≠ 0) (B : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (B : ℝ) ≤
      (N : ℝ) - ‖exponentialSum piOrbit N h‖ := by
  obtain ⟨N₀, hN₀⟩ := irrational_decimal_additiveGap_eventually_ge_nat
    (fixedFrequencySeed_mem_Ico h) (fixedFrequencySeed_irrational h h0) B
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [← fixedFrequencySeed_exponentialSum_eq h N]
  exact hN₀ N hN

/-- Strongest threshold formulation: at every fixed nonzero integer
frequency, the additive gap tends to positive infinity in the order sense. -/
theorem pi_fixedFrequency_additiveGap_eventually_ge
    (h : ℤ) (h0 : h ≠ 0) (A : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → A ≤
      (N : ℝ) - ‖exponentialSum piOrbit N h‖ := by
  obtain ⟨N₀, hN₀⟩ := irrational_decimal_additiveGap_eventually_ge
    (fixedFrequencySeed_mem_Ico h) (fixedFrequencySeed_irrational h h0) A
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [← fixedFrequencySeed_exponentialSum_eq h N]
  exact hN₀ N hN

/-- Unboundedness corollary in the simpler existential form. -/
theorem pi_fixedFrequency_additiveGap_unbounded
    (h : ℤ) (h0 : h ≠ 0) (A : ℝ) :
    ∃ N : ℕ, A ≤ (N : ℝ) - ‖exponentialSum piOrbit N h‖ := by
  obtain ⟨N₀, hN₀⟩ := pi_fixedFrequency_additiveGap_eventually_ge h h0 A
  exact ⟨N₀, hN₀ N₀ le_rfl⟩

end Theory.PiDigits.AllFixedFrequencyGap
