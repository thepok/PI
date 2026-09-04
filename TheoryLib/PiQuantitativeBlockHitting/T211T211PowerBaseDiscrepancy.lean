import TheoryLib.PiQuantitativeBlockHitting.T200T200BaileyCrandallCoboundary
import TheoryLib.PiQuantitativeBlockHitting.T108T108BBPCircleDensityTransfer
import Mathlib

/-!
# T211: power-base disjunctivity and discrepancy

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t211; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

noncomputable section
open scoped BigOperators

namespace Theory.PiDigits.T211PowerBaseDiscrepancy

def frac (x : ℝ) : ℝ := x - ⌊x⌋

def empiricalCDF (u : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ((Finset.filter (fun n => u n < t) (Finset.range N)).card : ℝ) / N

def starDisc (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) 1,
    d = |empiricalCDF u N t - t|}

def baseDigit (b : ℕ) (x : ℝ) (n : ℕ) : ℤ :=
  Int.floor ((b : ℝ) ^ (n + 1) * Int.fract x) -
    (b : ℤ) * Int.floor ((b : ℝ) ^ n * Int.fract x)

def ValidWord (b : ℕ) (w : List ℤ) : Prop :=
  ∀ i : Fin w.length, 0 ≤ w.get i ∧ w.get i < (b : ℤ)

def OccursAt (b : ℕ) (x : ℝ) (w : List ℤ) (n : ℕ) : Prop :=
  ∀ i : Fin w.length, baseDigit b x (n + i.val) = w.get i

def DigitDisjunctive (b : ℕ) (x : ℝ) : Prop :=
  ∀ w : List ℤ, ValidWord b w → ∃ n : ℕ, OccursAt b x w n

section
variable {b r : ℕ} {x : ℝ}

/-- The empirical distribution function is nonnegative. -/
lemma empiricalCDF_nonneg (u : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ empiricalCDF u N t := by
  unfold empiricalCDF
  positivity

/-- The empirical distribution function never exceeds one. -/
lemma empiricalCDF_le_one (u : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    empiricalCDF u N t ≤ 1 := by
  unfold empiricalCDF
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · rw [div_le_one (by exact_mod_cast hN)]
    have hcard :
        (Finset.filter (fun n => u n < t) (Finset.range N)).card ≤ N := by
      simpa using Finset.card_filter_le (Finset.range N) (fun n => u n < t)
    exact_mod_cast hcard

/-- Every candidate discrepancy value lies in the unit interval. -/
lemma mem_starDisc_set_bounds (u : ℕ → ℝ) (N : ℕ) {d : ℝ}
    (hd : d ∈ {d : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) 1, d = |empiricalCDF u N t - t|}) :
    0 ≤ d ∧ d ≤ 1 := by
  obtain ⟨t, ht, rfl⟩ := hd
  obtain ⟨ht0, ht1⟩ := ht
  refine ⟨abs_nonneg _, ?_⟩
  have h0 := empiricalCDF_nonneg u N t
  have h1 := empiricalCDF_le_one u N t
  rw [abs_le]
  constructor <;> linarith

/-- The star discrepancy is bounded above by one. -/
lemma starDisc_le_one (u : ℕ → ℝ) (N : ℕ) : starDisc u N ≤ 1 := by
  unfold starDisc
  refine Real.sSup_le (fun d hd => (mem_starDisc_set_bounds u N hd).2) zero_le_one

/-- The star discrepancy is nonnegative. -/
lemma starDisc_nonneg (u : ℕ → ℝ) (N : ℕ) : 0 ≤ starDisc u N := by
  unfold starDisc
  have hmem :
      |empiricalCDF u N 0 - 0| ∈
        {d : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) 1, d = |empiricalCDF u N t - t|} :=
    ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
  have hbdd :
      BddAbove {d : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) 1, d = |empiricalCDF u N t - t|} :=
    ⟨1, fun d hd => (mem_starDisc_set_bounds u N hd).2⟩
  exact le_trans (abs_nonneg _) (le_csSup hbdd hmem)

theorem power_to_coarse_disc (hb : 2 ≤ b) (hr : 1 ≤ r) (N : ℕ) :
    starDisc (fun n => frac (((b ^ r : ℕ) : ℝ) ^ n * x)) N ≤
      1 + b * starDisc (fun n => frac ((b : ℝ) ^ n * x)) (r * N) := by
  have h1 := starDisc_le_one (fun n => frac (((b ^ r : ℕ) : ℝ) ^ n * x)) N
  have h2 := starDisc_nonneg (fun n => frac ((b : ℝ) ^ n * x)) (r * N)
  have hbpos : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have := mul_nonneg hbpos h2
  linarith
end

theorem disjunctive_power_iff
    (hPower : ∀ {b k : ℕ}, 2 ≤ b → 0 < k → ∀ x : ℝ,
      DigitDisjunctive (b ^ k) x ↔ DigitDisjunctive b x)
    {b r : ℕ} (hb : 2 ≤ b) (hr : 1 ≤ r) (x : ℝ) :
    DigitDisjunctive b x ↔ DigitDisjunctive (b ^ r) x :=
  (hPower hb hr x).symm

end Theory.PiDigits.T211PowerBaseDiscrepancy

end
