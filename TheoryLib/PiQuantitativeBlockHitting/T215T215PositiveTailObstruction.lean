import TheoryLib.PiQuantitativeBlockHitting.T202T202RamanujanTwoAdicRamp
import Mathlib

/-!
# T215: positive tail obstruction

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t215; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

noncomputable section

namespace Theory.PiDigits.T215PositiveTailObstruction

open scoped BigOperators
open Filter

lemma positive_tail (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n)
    (hsum : Summable a) (N : ℕ) : 0 < ∑' n, a (n + N) := by
  have hshift : Summable (fun n : ℕ => a (n + N)) :=
    (summable_nat_add_iff N).mpr hsum
  exact hshift.tsum_pos (fun n => (hpos (n + N)).le) 0 (hpos (0 + N))

lemma prefix_strictly_below_sum (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n)
    (hsum : Summable a) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n < ∑' n, a n := by
  have hsplit : (∑ n ∈ Finset.range N, a n) + (∑' n, a (n + N)) = ∑' n, a n :=
    hsum.sum_add_tsum_nat_add N
  have htail := positive_tail a hpos hsum N
  linarith

lemma cleared_positive_tail_not_zero (Q : ℕ) (hQ : 0 < Q)
    (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (hsum : Summable a) (N : ℕ) :
    0 < Q * ((∑' n, a n) - ∑ n ∈ Finset.range N, a n) := by
  have hQ' : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have h := prefix_strictly_below_sum a hpos hsum N
  have : (0 : ℝ) < (∑' n, a n) - ∑ n ∈ Finset.range N, a n := by linarith
  exact mul_pos hQ' this

def IsIntegral (x : ℝ) : Prop := ∃ z : ℤ, x = (z : ℝ)

def CarryKillingWitness (u : ℕ → ℝ) (B : ℕ) : Prop :=
  ∃ H J M : ℕ,
    H < J ∧ 0 < M ∧ B ∣ M ∧
    IsIntegral ((M : ℝ) * ∑ j ∈ Finset.range (H + 1), u j) ∧
    (∀ j, H < j → j ≤ J → IsIntegral ((M : ℝ) * u j)) ∧
    0 < (M : ℝ) * (∑' k : ℕ, u (J + 1 + k)) ∧
      (M : ℝ) * (∑' k : ℕ, u (J + 1 + k)) < 1

noncomputable def ramanujanTerm (n : ℕ) : ℝ :=
  ((((Theory.PiDigits.T202RamanujanDyadicRamp.centralCube n) *
    (42 * n + 5) : ℕ) : ℝ)) / (2 : ℝ) ^ (12 * n + 4)

noncomputable def canonicalMultiplier (N : ℕ) : ℝ :=
  (2 : ℝ) ^ Theory.PiDigits.T202RamanujanDyadicRamp.lambda N

noncomputable def canonicalScaledFirstOmitted (N : ℕ) : ℝ :=
  canonicalMultiplier N * ramanujanTerm (N + 1)

def CanonicalDirectSmallTail : Prop :=
  ∃ N0 : ℕ, ∀ N ≥ N0,
    canonicalMultiplier N * (∑' k : ℕ, ramanujanTerm (N + 1 + k)) < 1

def RamanujanDirectGrowthInput : Prop :=
  Summable ramanujanTerm ∧
    Tendsto canonicalScaledFirstOmitted atTop atTop

lemma ramanujanTerm_nonneg (n : ℕ) : 0 ≤ ramanujanTerm n := by
  unfold ramanujanTerm
  positivity

lemma canonicalMultiplier_pos (N : ℕ) : 0 < canonicalMultiplier N := by
  unfold canonicalMultiplier
  positivity

lemma shifted_summable (hsum : Summable ramanujanTerm) (N : ℕ) :
    Summable (fun k : ℕ => ramanujanTerm (N + 1 + k)) := by
  have h : Summable (fun k : ℕ => ramanujanTerm (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hsum
  refine h.congr ?_
  intro k
  rw [Nat.add_comm k (N + 1)]

lemma first_le_tail (hsum : Summable ramanujanTerm) (N : ℕ) :
    ramanujanTerm (N + 1) ≤ ∑' k : ℕ, ramanujanTerm (N + 1 + k) := by
  have hs := shifted_summable hsum N
  have := hs.le_tsum 0 (fun j _ => ramanujanTerm_nonneg _)
  simpa using this

theorem ramanujan_canonical_direct_small_tail_fails
    (hgrowth : RamanujanDirectGrowthInput) :
    ¬ CanonicalDirectSmallTail := by
  obtain ⟨hsum, htend⟩ := hgrowth
  rintro ⟨N0, hN0⟩
  have hev : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ canonicalScaledFirstOmitted N :=
    htend (eventually_ge_atTop 1)
  have hev2 : ∀ᶠ N : ℕ in atTop, N0 ≤ N := eventually_ge_atTop N0
  obtain ⟨N, hN1, hN2⟩ := (hev.and hev2).exists
  have hsmall := hN0 N hN2
  have hle : canonicalScaledFirstOmitted N ≤
      canonicalMultiplier N * (∑' k : ℕ, ramanujanTerm (N + 1 + k)) := by
    unfold canonicalScaledFirstOmitted
    exact mul_le_mul_of_nonneg_left (first_le_tail hsum N)
      (canonicalMultiplier_pos N).le
  linarith

end Theory.PiDigits.T215PositiveTailObstruction
