import TheoryLib.PiQuantitativeBlockHitting.T35T35OversampledBBPGridStability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# T36: a fully formal rational Machin approximation to pi

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module replaces the abstract geometric-tail premise in T35 by finite
rational Taylor sums and mathlib's formalized Machin identity.  The only
external premise retained by the decimal-grid conclusion is the published
irrationality-measure input, stated explicitly as
`IrrationalityMeasureBelow Real.pi 8`.

No result here proves decimal orbit density or the every-word conjecture.
-/

noncomputable section

namespace Theory.PiDigits.MachinGridStability

open Finset Filter
open Theory.PiDigits.OversampledBBPGridStability
open Theory.PiDigits.PowerTenDiophantineReduction
open Theory.PiDigits.LongLagBlockCollisionDecay.T4

/-- Magnitude of the `n`-th term in the arctangent series at `1/q`. -/
def arctanMagnitude (q n : ℕ) : ℝ :=
  ((q : ℝ)⁻¹) ^ (2 * n + 1) / (2 * n + 1)

/-- One arctangent Taylor term, defined over the rationals. -/
def arctanTermRat (q n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * ((q : ℚ)⁻¹) ^ (2 * n + 1) / (2 * n + 1)

/-- A finite arctangent Taylor sum, defined over the rationals. -/
def arctanPartialRat (q terms : ℕ) : ℚ :=
  ∑ n ∈ range terms, arctanTermRat q n

/-- The real embedding of the rational finite Taylor sum. -/
def arctanPartial (q terms : ℕ) : ℝ :=
  (arctanPartialRat q terms : ℝ)

/-- The rational and real presentations of the finite Taylor sum agree. -/
theorem arctanPartial_eq_sum (q terms : ℕ) :
    arctanPartial q terms =
      ∑ n ∈ range terms, (-1 : ℝ) ^ n * arctanMagnitude q n := by
  simp [arctanPartial, arctanPartialRat, arctanTermRat, arctanMagnitude,
    mul_div_assoc]

/-- Exact one-term recurrence for the finite rational Taylor sums. -/
theorem arctanPartialRat_succ (q terms : ℕ) :
    arctanPartialRat q (terms + 1) =
      arctanPartialRat q terms + arctanTermRat q terms := by
  simp [arctanPartialRat, sum_range_succ]

/-- Exact two-term recurrence, used by one step of the Machin sequence. -/
theorem arctanPartialRat_add_two (q terms : ℕ) :
    arctanPartialRat q (terms + 2) =
      arctanPartialRat q terms + arctanTermRat q terms +
        arctanTermRat q (terms + 1) := by
  calc
    arctanPartialRat q (terms + 2) =
        arctanPartialRat q ((terms + 1) + 1) := by
      congr 1
    _ = arctanPartialRat q (terms + 1) +
        arctanTermRat q (terms + 1) := arctanPartialRat_succ q (terms + 1)
    _ = arctanPartialRat q terms + arctanTermRat q terms +
        arctanTermRat q (terms + 1) := by
      rw [arctanPartialRat_succ]

lemma arctanMagnitude_nonneg (q n : ℕ) :
    0 ≤ arctanMagnitude q n := by
  unfold arctanMagnitude
  positivity

lemma arctanMagnitude_antitone (q : ℕ) (hq : 1 ≤ q) :
    Antitone (arctanMagnitude q) := by
  intro a b hab
  unfold arctanMagnitude
  have hbase : 0 ≤ ((q : ℝ)⁻¹) := by positivity
  have hbase_one : ((q : ℝ)⁻¹) ≤ 1 := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    exact (inv_le_one₀ hqpos).2 (by exact_mod_cast hq)
  apply div_le_div₀ (by positivity)
  · exact pow_le_pow_of_le_one hbase hbase_one (by omega)
  · positivity
  · exact_mod_cast (show 2 * a + 1 ≤ 2 * b + 1 by omega)

lemma summable_arctanMagnitude (q : ℕ) (hq : 2 ≤ q) :
    Summable (arctanMagnitude q) := by
  have hgeom : Summable (fun n : ℕ ↦ ((q : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_lt_one (by positivity)
      (by simpa using (inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)))
  refine Summable.of_nonneg_of_le (fun n ↦ arctanMagnitude_nonneg q n) ?_ hgeom
  intro n
  unfold arctanMagnitude
  have hbase : 0 ≤ ((q : ℝ)⁻¹) := by positivity
  have hbase_one : ((q : ℝ)⁻¹) ≤ 1 := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    exact (inv_le_one₀ hqpos).2 (by exact_mod_cast (show 1 ≤ q by omega))
  calc
    ((q : ℝ)⁻¹) ^ (2 * n + 1) / (2 * n + 1) ≤
        ((q : ℝ)⁻¹) ^ (2 * n + 1) := by
      exact div_le_self (by positivity) (by norm_num)
    _ ≤ ((q : ℝ)⁻¹) ^ n :=
      pow_le_pow_of_le_one hbase hbase_one (by omega)

/-- The finite sums converge to the corresponding arctangent. -/
theorem tendsto_arctanPartial (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (arctanPartial q) atTop (nhds (Real.arctan (q : ℝ)⁻¹)) := by
  have hs := Real.hasSum_arctan
    (x := (q : ℝ)⁻¹) (by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq))
  have hs' : HasSum
      (fun n : ℕ ↦ (-1 : ℝ) ^ n * arctanMagnitude q n)
      (Real.arctan (q : ℝ)⁻¹) := by
    simpa [arctanMagnitude, mul_div_assoc] using hs
  have heq : arctanPartial q =
      (fun terms ↦ ∑ n ∈ range terms,
        (-1 : ℝ) ^ n * arctanMagnitude q n) := by
    funext terms
    exact arctanPartial_eq_sum q terms
  rw [heq]
  exact hs'.tendsto_sum_nat

/-- Even-length Taylor sums lie below the arctangent. -/
theorem arctanPartial_even_le (q k : ℕ) (hq : 2 ≤ q) :
    arctanPartial q (2 * k) ≤ Real.arctan (q : ℝ)⁻¹ := by
  have ht : Tendsto
      (fun n ↦ ∑ i ∈ range n, (-1 : ℝ) ^ i * arctanMagnitude q i)
      atTop (nhds (Real.arctan (q : ℝ)⁻¹)) := by
    simpa only [← arctanPartial_eq_sum] using tendsto_arctanPartial q hq
  rw [arctanPartial_eq_sum]
  exact (arctanMagnitude_antitone q (by omega)).alternating_series_le_tendsto ht k

/-- Odd-length Taylor sums lie above the arctangent. -/
theorem arctan_le_arctanPartial_odd (q k : ℕ) (hq : 2 ≤ q) :
    Real.arctan (q : ℝ)⁻¹ ≤ arctanPartial q (2 * k + 1) := by
  have ht : Tendsto
      (fun n ↦ ∑ i ∈ range n, (-1 : ℝ) ^ i * arctanMagnitude q i)
      atTop (nhds (Real.arctan (q : ℝ)⁻¹)) := by
    simpa only [← arctanPartial_eq_sum] using tendsto_arctanPartial q hq
  rw [arctanPartial_eq_sum]
  exact (arctanMagnitude_antitone q (by omega)).tendsto_le_alternating_series ht k

/-- The alternating-series remainder bound for the rational Taylor sums. -/
theorem abs_arctan_sub_arctanPartial_le (q terms : ℕ) (hq : 2 ≤ q) :
    |Real.arctan (q : ℝ)⁻¹ - arctanPartial q terms| ≤
      arctanMagnitude q terms := by
  rw [arctanPartial_eq_sum]
  have hsum := (Real.hasSum_arctan
    (x := (q : ℝ)⁻¹) (by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq))).tsum_eq
  rw [← hsum]
  have herr := alternating_series_error_bound
    (arctanMagnitude q) (arctanMagnitude_antitone q (by omega))
      (summable_arctanMagnitude q hq) terms
  simpa [arctanMagnitude, mul_div_assoc] using herr

/-- A rational lower Machin approximant.  The shift by one makes the clean
geometric error estimate valid already at index zero. -/
def machinLowerRat (K : ℕ) : ℚ :=
  16 * arctanPartialRat 5 (2 * (K + 1)) -
    4 * arctanPartialRat 239 (2 * (K + 1) + 1)

/-- The real embedding of the rational lower Machin approximant. -/
def machinLower (K : ℕ) : ℝ :=
  (machinLowerRat K : ℝ)

theorem machinLower_eq (K : ℕ) :
    machinLower K =
      16 * arctanPartial 5 (2 * (K + 1)) -
        4 * arctanPartial 239 (2 * (K + 1) + 1) := by
  simp [machinLower, machinLowerRat, arctanPartial]

/-- Every Machin approximant is explicitly rational. -/
theorem machinLower_isRat (K : ℕ) :
    ∃ r : ℚ, machinLower K = (r : ℝ) :=
  ⟨machinLowerRat K, rfl⟩

/-- Exact rational step recurrence for the Machin approximation sequence. -/
theorem machinLowerRat_succ (K : ℕ) :
    machinLowerRat (K + 1) = machinLowerRat K +
      16 * (arctanTermRat 5 (2 * (K + 1)) +
        arctanTermRat 5 (2 * (K + 1) + 1)) -
      4 * (arctanTermRat 239 (2 * (K + 1) + 1) +
        arctanTermRat 239 (2 * (K + 1) + 2)) := by
  unfold machinLowerRat
  rw [show 2 * (K + 1 + 1) = 2 * (K + 1) + 2 by omega,
    arctanPartialRat_add_two,
    show 2 * (K + 1) + 2 + 1 = (2 * (K + 1) + 1) + 2 by omega,
    arctanPartialRat_add_two]
  ring

/-- Mathlib's Machin identity, normalized to solve for `pi`. -/
theorem pi_eq_machin :
    Real.pi = 16 * Real.arctan (5 : ℝ)⁻¹ -
      4 * Real.arctan (239 : ℝ)⁻¹ := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  linarith

/-- Every rational Machin approximant lies below `pi`. -/
theorem machinLower_le_pi (K : ℕ) : machinLower K ≤ Real.pi := by
  rw [machinLower_eq, pi_eq_machin]
  have h5 := arctanPartial_even_le 5 (K + 1) (by norm_num)
  have h239 := arctan_le_arctanPartial_odd 239 (K + 1) (by norm_num)
  linarith

/-- The first omitted `1/5` term after `2*k` terms is bounded by
`625^-k`. -/
lemma arctanMagnitude_five_even_le (k : ℕ) :
    arctanMagnitude 5 (2 * k) ≤ 1 / (625 : ℝ) ^ k := by
  unfold arctanMagnitude
  have hpow : ((5 : ℝ)⁻¹) ^ (2 * (2 * k) + 1) ≤
      ((5 : ℝ)⁻¹) ^ (4 * k) := by
    apply pow_le_pow_of_le_one (by positivity) (by norm_num)
    omega
  calc
    _ ≤ ((5 : ℝ)⁻¹) ^ (2 * (2 * k) + 1) := by
      exact div_le_self (by positivity) (by norm_num)
    _ ≤ ((5 : ℝ)⁻¹) ^ (4 * k) := hpow
    _ = 1 / (625 : ℝ) ^ k := by
      rw [pow_mul]
      norm_num [div_pow]

/-- The first omitted `1/239` term after `2*k+1` terms is no larger
than the corresponding `1/5` even remainder term. -/
lemma arctanMagnitude_239_odd_le_five_even (k : ℕ) :
    arctanMagnitude 239 (2 * k + 1) ≤ arctanMagnitude 5 (2 * k) := by
  unfold arctanMagnitude
  have hbase : (0 : ℝ) ≤ (239 : ℝ)⁻¹ := by positivity
  have hbase_le : (239 : ℝ)⁻¹ ≤ (5 : ℝ)⁻¹ := by norm_num
  have hsmall_nonneg : (0 : ℝ) ≤ (5 : ℝ)⁻¹ := by positivity
  have hsmall_one : (5 : ℝ)⁻¹ ≤ 1 := by norm_num
  have hnum : ((239 : ℝ)⁻¹) ^ (2 * (2 * k + 1) + 1) ≤
      ((5 : ℝ)⁻¹) ^ (2 * (2 * k) + 1) := by
    calc
      ((239 : ℝ)⁻¹) ^ (2 * (2 * k + 1) + 1) ≤
          ((5 : ℝ)⁻¹) ^ (2 * (2 * k + 1) + 1) :=
        pow_le_pow_left₀ hbase hbase_le _
      _ ≤ ((5 : ℝ)⁻¹) ^ (2 * (2 * k) + 1) :=
        pow_le_pow_of_le_one hsmall_nonneg hsmall_one (by omega)
  apply div_le_div₀ (by positivity) hnum (by positivity)
  exact_mod_cast (show 2 * (2 * k) + 1 ≤ 2 * (2 * k + 1) + 1 by omega)

/-- A common geometric bound for both signed Machin remainders. -/
lemma machin_remainders_le (K : ℕ) :
    Real.arctan (5 : ℝ)⁻¹ - arctanPartial 5 (2 * (K + 1)) ≤
        1 / (625 : ℝ) ^ (K + 1) ∧
      arctanPartial 239 (2 * (K + 1) + 1) -
          Real.arctan (239 : ℝ)⁻¹ ≤ 1 / (625 : ℝ) ^ (K + 1) := by
  have h5abs := abs_arctan_sub_arctanPartial_le
    5 (2 * (K + 1)) (by norm_num)
  have h239abs := abs_arctan_sub_arctanPartial_le
    239 (2 * (K + 1) + 1) (by norm_num)
  have h5mag := arctanMagnitude_five_even_le (K + 1)
  have h239mag : arctanMagnitude 239 (2 * (K + 1) + 1) ≤
      1 / (625 : ℝ) ^ (K + 1) :=
    (arctanMagnitude_239_odd_le_five_even (K + 1)).trans h5mag
  constructor
  · exact (le_abs_self _).trans (h5abs.trans h5mag)
  · exact (le_abs_self _).trans (by
      rw [abs_sub_comm] at h239abs
      exact h239abs.trans h239mag)

/-- The shifted Machin approximants have a base-625 geometric error. -/
theorem pi_sub_machinLower_lt_pow625 (K : ℕ) :
    Real.pi - machinLower K < 1 / (625 : ℝ) ^ K := by
  obtain ⟨h5, h239⟩ := machin_remainders_le K
  have hdecomp : Real.pi - machinLower K =
      16 * (Real.arctan (5 : ℝ)⁻¹ - arctanPartial 5 (2 * (K + 1))) +
        4 * (arctanPartial 239 (2 * (K + 1) + 1) -
          Real.arctan (239 : ℝ)⁻¹) := by
    rw [pi_eq_machin, machinLower_eq]
    ring
  have hcoarse : Real.pi - machinLower K ≤
      20 / (625 : ℝ) ^ (K + 1) := by
    rw [hdecomp]
    calc
      16 * (Real.arctan (5 : ℝ)⁻¹ - arctanPartial 5 (2 * (K + 1))) +
          4 * (arctanPartial 239 (2 * (K + 1) + 1) -
            Real.arctan (239 : ℝ)⁻¹) ≤
          16 * (1 / (625 : ℝ) ^ (K + 1)) +
            4 * (1 / (625 : ℝ) ^ (K + 1)) := by gcongr
      _ = 20 / (625 : ℝ) ^ (K + 1) := by ring
  refine hcoarse.trans_lt ?_
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (625 : ℝ) ^ (K + 1))
    (by positivity : (0 : ℝ) < (625 : ℝ) ^ K)]
  rw [pow_succ]
  have hp : (0 : ℝ) < (625 : ℝ) ^ K := by positivity
  nlinarith

/-- In particular, the same explicit approximants satisfy T35's weaker
base-16 geometric-tail contract. -/
theorem pi_sub_machinLower_lt_pow16 (K : ℕ) :
    Real.pi - machinLower K < 1 / (16 : ℝ) ^ K := by
  refine (pi_sub_machinLower_lt_pow625 K).trans_le ?_
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16)
    (by norm_num : (16 : ℝ) ≤ 625) K

/-- Triple sampling is enough for the sharper base-625 tail because
`10^8 < 625^3`. -/
theorem eventually_powTenEight_lt_pow625Three (m : ℕ) :
    ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      (10 : ℝ) ^ (8 * (N + m)) < (625 : ℝ) ^ (3 * N) := by
  let r : ℝ := (10 : ℝ) ^ 8 / (625 : ℝ) ^ 3
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_one : r < 1 := by
    dsimp [r]
    norm_num
  have ht : Tendsto (fun N : ℕ ↦ r ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_one
  have htarget : 0 < 1 / (10 : ℝ) ^ (8 * m) := by positivity
  have hevent : ∀ᶠ N : ℕ in atTop,
      r ^ N < 1 / (10 : ℝ) ^ (8 * m) :=
    ht.eventually (Iio_mem_nhds htarget)
  obtain ⟨C, hC⟩ := eventually_atTop.1 hevent
  refine ⟨C, fun N hN ↦ ?_⟩
  have hratio := hC N hN
  have hden625 : 0 < (625 : ℝ) ^ (3 * N) := by positivity
  have hden10 : 0 < (10 : ℝ) ^ (8 * m) := by positivity
  have hcross :
      (10 : ℝ) ^ (8 * N) * (10 : ℝ) ^ (8 * m) <
        (625 : ℝ) ^ (3 * N) := by
    dsimp [r] at hratio
    rw [div_pow] at hratio
    have hratio' :
        (10 : ℝ) ^ (8 * N) / (625 : ℝ) ^ (3 * N) <
          1 / (10 : ℝ) ^ (8 * m) := by
      simpa only [← pow_mul] using hratio
    have := (div_lt_div_iff₀ hden625 hden10).mp hratio'
    simpa only [one_mul] using this
  calc
    (10 : ℝ) ^ (8 * (N + m)) =
        (10 : ℝ) ^ (8 * N) * (10 : ℝ) ^ (8 * m) := by
      rw [← pow_add]
      congr 1
      omega
    _ < (625 : ℝ) ^ (3 * N) := hcross

/-- At a scale satisfying the displayed inequality, the explicit rational
Machin approximant sampled at `3*N` has exactly the same arithmetic
`decimalBlockCode` (floor code) at position `N` as `pi`.  The separate
floor-code-to-symbolic-digit bridge is not asserted in this module. -/
theorem decimalBlockCode_threeOversampled_machinLower_eq
    {A N m : ℕ}
    (hD : PowerTenDiophantine Real.pi 8 A)
    (hN : A ≤ N)
    (hscale : (10 : ℝ) ^ (8 * (N + m)) <
      (625 : ℝ) ^ (3 * N)) :
    decimalBlockCode (machinLower (3 * N)) N m =
      decimalBlockCode Real.pi N m := by
  have hscale_N : (10 : ℝ) ^ (8 * N) < (625 : ℝ) ^ (3 * N) := by
    refine lt_of_le_of_lt ?_ hscale
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10)
    omega
  have hclose_N : Real.pi - machinLower (3 * N) <
      1 / (10 : ℝ) ^ (8 * N) :=
    (pi_sub_machinLower_lt_pow625 (3 * N)).trans
      (one_div_lt_one_div_of_lt (by positivity) hscale_N)
  have hclose_Nm : Real.pi - machinLower (3 * N) <
      1 / (10 : ℝ) ^ (8 * (N + m)) :=
    (pi_sub_machinLower_lt_pow625 (3 * N)).trans
      (one_div_lt_one_div_of_lt (by positivity) hscale)
  apply decimalBlockCode_eq_of_prefixFloor_eq
  · exact decimalPrefixFloor_eq_of_powerTenDiophantine
      hD hN (machinLower_le_pi (3 * N)) hclose_N
  · exact decimalPrefixFloor_eq_of_powerTenDiophantine
      hD (hN.trans (Nat.le_add_right N m))
        (machinLower_le_pi (3 * N)) hclose_Nm

/-- Conditional only on the explicit published irrationality-measure premise,
triple-oversampled rational Machin approximants eventually reproduce the
fixed-length arithmetic floor code of `pi` at the matching position.  The
separate floor-code-to-symbolic-digit bridge is not asserted here. -/
theorem pi_eventually_decimalBlockCode_threeOversampled_machinLower_eq
    (hSource : IrrationalityMeasureBelow Real.pi 8) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      decimalBlockCode (machinLower (3 * N)) N m =
        decimalBlockCode Real.pi N m := by
  obtain ⟨A, hD⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_powerTenDiophantine hSource
  intro m
  obtain ⟨Cscale, hscale⟩ := eventually_powTenEight_lt_pow625Three m
  refine ⟨max A Cscale, fun N hN ↦ ?_⟩
  exact decimalBlockCode_threeOversampled_machinLower_eq hD
    ((le_max_left A Cscale).trans hN)
    (hscale N ((le_max_right A Cscale).trans hN))

/-- The direct T35 instantiation is retained as a compatibility corollary.
It uses sevenfold sampling and the weaker base-16 tail. -/
theorem pi_eventually_decimalBlockCode_sevenOversampled_machinLower_eq
    (hSource : IrrationalityMeasureBelow Real.pi 8) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      decimalBlockCode (machinLower (7 * N)) N m =
        decimalBlockCode Real.pi N m := by
  exact pi_eventually_decimalBlockCode_sevenOversampled_eq
    hSource machinLower_le_pi pi_sub_machinLower_lt_pow16

end Theory.PiDigits.MachinGridStability

namespace Theory.PiDigits.MachinGridStability

#print axioms arctanPartial_eq_sum
#print axioms arctanPartialRat_succ
#print axioms arctanPartialRat_add_two
#print axioms arctanMagnitude_nonneg
#print axioms arctanMagnitude_antitone
#print axioms summable_arctanMagnitude
#print axioms tendsto_arctanPartial
#print axioms arctanPartial_even_le
#print axioms arctan_le_arctanPartial_odd
#print axioms abs_arctan_sub_arctanPartial_le
#print axioms machinLower_eq
#print axioms machinLower_isRat
#print axioms machinLowerRat_succ
#print axioms pi_eq_machin
#print axioms machinLower_le_pi
#print axioms arctanMagnitude_five_even_le
#print axioms arctanMagnitude_239_odd_le_five_even
#print axioms machin_remainders_le
#print axioms pi_sub_machinLower_lt_pow625
#print axioms pi_sub_machinLower_lt_pow16
#print axioms eventually_powTenEight_lt_pow625Three
#print axioms decimalBlockCode_threeOversampled_machinLower_eq
#print axioms pi_eventually_decimalBlockCode_threeOversampled_machinLower_eq
#print axioms pi_eventually_decimalBlockCode_sevenOversampled_machinLower_eq

end Theory.PiDigits.MachinGridStability
