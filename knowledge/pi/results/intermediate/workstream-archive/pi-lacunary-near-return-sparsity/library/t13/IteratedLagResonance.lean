import TheoryLib.PiLacunaryNearReturnSparsity.T10LongLagResonance

/-!
# Arbitrary-depth lag resonance obstruction

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves deterministic finite autocorrelation lemmas and a conditional
consequence of the literal negation of canonical A1. It proves no cancellation
estimate and no unconditional assertion about `Real.pi`.
-/

noncomputable section

open Finset
open scoped ComplexConjugate Real

namespace DecimalFactorComplexity
namespace IteratedLagResonance

open LongLagResonance

/-- The finite autocorrelation at positive shift `s`. -/
def autocorrelation (z : ℕ → ℂ) (M s : ℕ) : ℂ :=
  ∑ j ∈ range (M - s), z (j + s) * conj (z j)

/-- One autocorrelation step replaces density denominator `D` by `8 * D^2`. -/
def nextDensityDenominator (D : ℕ) : ℕ := 8 * D ^ 2

/-- The explicit density denominator after `d` autocorrelation steps. -/
def densityDenominator (D : ℕ) : ℕ → ℕ
  | 0 => D
  | d + 1 => densityDenominator (nextDensityDenominator D) d

/-- A sufficient length for one extraction. `q` is the number of forbidden
shifts, `B` is the lower shift bound, and `R` is the required residual length. -/
def oneStepLengthThreshold (D B q R : ℕ) : ℕ :=
  max (8 * D ^ 2)
    (16 * (B + q + R) * D ^ 2)

/-- Fully explicit recursive threshold. The parameter `q` records shifts
already forbidden by earlier extraction steps. -/
def iterationLengthThresholdAux (D B K q : ℕ) : ℕ → ℕ
  | 0 => K
  | d + 1 => oneStepLengthThreshold D B q
      (iterationLengthThresholdAux (nextDensityDenominator D) B K (q + 1) d)

/-- Initial recursive threshold for depth `d`. -/
def iterationLengthThreshold (D B K d : ℕ) : ℕ :=
  iterationLengthThresholdAux D B K 0 d

/-- Apply successive multiplicative differences in the listed order. -/
def iteratedDifference (z : ℕ → ℂ) : List ℕ → ℕ → ℂ
  | [], j => z j
  | s :: shifts, j =>
      iteratedDifference (fun k => z (k + s) * conj (z k)) shifts j

/-- Unit-modulus base-ten geometric phase with real coefficient `c`. -/
def geometricPhase (c : ℝ) (j : ℕ) : ℂ :=
  Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (((10 : ℝ) ^ j * c : ℝ) : ℂ))

/-- The literal arbitrary-depth resonance sum, indexed by `Fin d`. -/
def iteratedResonanceSum (M h r d : ℕ) (shifts : Fin d → ℕ) : ℂ :=
  ∑ j ∈ range (M - ∑ t, shifts t),
    geometricPhase
      ((h : ℝ) * ((10 : ℝ) ^ r - 1) *
        (∏ t, ((10 : ℝ) ^ shifts t - 1)) * Real.pi) j

lemma geometricPhase_difference (c : ℝ) (j s : ℕ) :
    geometricPhase c (j + s) * conj (geometricPhase c j) =
      geometricPhase (c * ((10 : ℝ) ^ s - 1)) j := by
  unfold geometricPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  rw [pow_add]
  ring

lemma iteratedDifference_geometricPhase (c : ℝ) (shifts : List ℕ) (j : ℕ) :
    iteratedDifference (geometricPhase c) shifts j =
      geometricPhase
        (c * (shifts.map fun s => (10 : ℝ) ^ s - 1).prod) j := by
  induction shifts generalizing c with
  | nil => simp [iteratedDifference]
  | cons s shifts ih =>
      simp only [iteratedDifference]
      rw [show (fun k => geometricPhase c (k + s) * conj (geometricPhase c k)) =
          geometricPhase (c * ((10 : ℝ) ^ s - 1)) by
        funext k
        exact geometricPhase_difference c k s]
      rw [ih]
      simp only [List.map_cons, List.prod_cons]
      apply congrArg (fun x : ℝ => geometricPhase x j)
      ring

lemma norm_autocorrelation_le (z : ℕ → ℂ) (M s : ℕ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ‖autocorrelation z M s‖ ≤ (M - s : ℕ) := by
  rw [autocorrelation]
  calc
    ‖∑ j ∈ range (M - s), z (j + s) * conj (z j)‖ ≤
        ∑ j ∈ range (M - s), ‖z (j + s) * conj (z j)‖ :=
      norm_sum_le _ _
    _ = ∑ _j ∈ range (M - s), (1 : ℝ) := by
      apply sum_congr rfl
      intro j hj
      simp [hz]
    _ = (M - s : ℕ) := by simp

/-- Exact decomposition of the squared norm into positive-lag
autocorrelations. -/
lemma norm_sum_sq_eq_autocorrelation (z : ℕ → ℂ) (M : ℕ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ‖∑ j ∈ range M, z j‖ ^ 2 =
      M + 2 * ∑ s ∈ Icc 1 (M - 1), (autocorrelation z M s).re := by
  classical
  induction M with
  | zero => simp [autocorrelation]
  | succ n ih =>
    have hac (s : ℕ) (hs : s ∈ Icc 1 n) :
        autocorrelation z (n + 1) s =
          autocorrelation z n s + z n * conj (z (n - s)) := by
      rw [autocorrelation, autocorrelation]
      have hs_le : s ≤ n := (mem_Icc.mp hs).2
      have hsub : n + 1 - s = n - s + 1 := by omega
      rw [hsub, sum_range_succ, Nat.sub_add_cancel hs_le]
    have hold :
        (∑ s ∈ Icc 1 n, (autocorrelation z n s).re) =
          ∑ s ∈ Icc 1 (n - 1), (autocorrelation z n s).re := by
      symm
      apply Finset.sum_subset
      · intro s hs
        simp only [mem_Icc] at hs ⊢
        omega
      · intro s hs hns
        have hs_eq : s = n := by
          simp only [mem_Icc] at hs
          simp only [mem_Icc, not_and_or, not_le] at hns
          omega
        subst s
        simp [autocorrelation]
    have hcross :
        (∑ s ∈ Icc 1 n, (z n * conj (z (n - s))).re) =
          (z n * conj (∑ j ∈ range n, z j)).re := by
      calc
        (∑ s ∈ Icc 1 n, (z n * conj (z (n - s))).re) =
            ∑ j ∈ range n, (z n * conj (z j)).re := by
          apply Finset.sum_bij (fun s _ => n - s)
          · intro s hs
            simp only [mem_range]
            simp only [mem_Icc] at hs
            omega
          · intro a ha b hb hab
            simp only [mem_Icc] at ha hb
            omega
          · intro j hj
            simp only [mem_range] at hj
            refine ⟨n - j, ?_, ?_⟩
            · simp only [mem_Icc]
              omega
            · omega
          · intro s hs
            rfl
        _ = (z n * conj (∑ j ∈ range n, z j)).re := by
          simp [Finset.mul_sum]
    have hcorr :
        (∑ s ∈ Icc 1 n, (autocorrelation z (n + 1) s).re) =
          (∑ s ∈ Icc 1 (n - 1), (autocorrelation z n s).re) +
            (z n * conj (∑ j ∈ range n, z j)).re := by
      calc
        (∑ s ∈ Icc 1 n, (autocorrelation z (n + 1) s).re) =
            (∑ s ∈ Icc 1 n, (autocorrelation z n s).re) +
              ∑ s ∈ Icc 1 n, (z n * conj (z (n - s))).re := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro s hs
          rw [hac s hs, Complex.add_re]
        _ = (∑ s ∈ Icc 1 (n - 1), (autocorrelation z n s).re) +
              (z n * conj (∑ j ∈ range n, z j)).re := by
          rw [hold, hcross]
    rw [sum_range_succ, norm_add_sq (𝕜 := ℂ), ih, Nat.add_sub_cancel, hcorr]
    simp only [RCLike.inner_apply]
    rw [RCLike.re_to_complex, hz, Nat.cast_add, Nat.cast_one]
    ring

lemma small_shift_count_le (M B : ℕ) :
    ((Icc 1 (M - 1)).filter fun s => s < B).card ≤ B := by
  calc
    ((Icc 1 (M - 1)).filter fun s => s < B).card ≤ (range B).card := by
      apply card_le_card
      intro s hs
      exact mem_range.mpr (mem_filter.mp hs).2
    _ = B := card_range B

lemma forbidden_shift_count_le (M : ℕ) (F : Finset ℕ) :
    ((Icc 1 (M - 1)).filter fun s => s ∈ F).card ≤ F.card := by
  apply card_le_card
  intro s hs
  exact (mem_filter.mp hs).2

lemma positive_shift_count_le (M : ℕ) : (Icc 1 (M - 1)).card ≤ M := by
  simp only [Nat.card_Icc]
  omega

/-- A large unit-modulus sum has a large autocorrelation at a new shift. The
new shift is at least `B`, avoids `F`, and leaves at least `R` terms. -/
theorem oneStep_autocorrelation_extraction
    (z : ℕ → ℂ) (M D B R : ℕ) (F : Finset ℕ)
    (hz : ∀ j, ‖z j‖ = 1) (hD : 1 ≤ D)
    (hM : oneStepLengthThreshold D B F.card R ≤ M)
    (hlarge : (M : ℝ) / D < ‖∑ j ∈ range M, z j‖) :
    ∃ s ∈ Icc B (M - R), s ∉ F ∧
      ((M - s : ℕ) : ℝ) / nextDensityDenominator D <
        ‖autocorrelation z M s‖ := by
  classical
  by_contra hnone
  push Not at hnone
  let S : Finset ℕ := Icc 1 (M - 1)
  let E : ℝ := nextDensityDenominator D
  have hE : 0 < E := by
    dsimp [E, nextDensityDenominator]
    positivity
  have hterm : ∀ s ∈ S,
      (autocorrelation z M s).re ≤
        ((M - s : ℕ) : ℝ) / E +
          (if s < B then (M : ℝ) else 0) +
          (if s ∈ F then (M : ℝ) else 0) +
          (if M - R < s then (R : ℝ) else 0) := by
    intro s hs
    have hre : (autocorrelation z M s).re ≤ ‖autocorrelation z M s‖ :=
      Complex.re_le_norm _
    have hnorm := norm_autocorrelation_le z M s hz
    have hbaseNonneg : 0 ≤ ((M - s : ℕ) : ℝ) / E := by positivity
    by_cases hsB : s < B
    · simp only [if_pos hsB]
      calc
        (autocorrelation z M s).re ≤ ‖autocorrelation z M s‖ := hre
        _ ≤ ((M - s : ℕ) : ℝ) := hnorm
        _ ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M s
        _ ≤ ((M - s : ℕ) : ℝ) / E + (M : ℝ) +
              (if s ∈ F then (M : ℝ) else 0) +
              (if M - R < s then (R : ℝ) else 0) := by
          have hforbiddenNonneg :
              0 ≤ (if s ∈ F then (M : ℝ) else 0) := by
            split <;> positivity
          have hlateNonneg :
              0 ≤ (if M - R < s then (R : ℝ) else 0) := by
            split <;> positivity
          linarith
    · simp only [if_neg hsB]
      by_cases hsF : s ∈ F
      · simp only [if_pos hsF]
        calc
          (autocorrelation z M s).re ≤ ‖autocorrelation z M s‖ := hre
          _ ≤ ((M - s : ℕ) : ℝ) := hnorm
          _ ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M s
          _ ≤ ((M - s : ℕ) : ℝ) / E + 0 + (M : ℝ) +
                (if M - R < s then (R : ℝ) else 0) := by
            have hlateNonneg :
                0 ≤ (if M - R < s then (R : ℝ) else 0) := by
              split <;> positivity
            linarith
      · simp only [if_neg hsF]
        by_cases hsLate : M - R < s
        · simp only [if_pos hsLate]
          have hresidual : M - s ≤ R := by omega
          calc
            (autocorrelation z M s).re ≤ ‖autocorrelation z M s‖ := hre
            _ ≤ ((M - s : ℕ) : ℝ) := hnorm
            _ ≤ (R : ℝ) := by exact_mod_cast hresidual
            _ ≤ ((M - s : ℕ) : ℝ) / E + 0 + 0 + (R : ℝ) := by
              linarith
        · simp only [if_neg hsLate, add_zero]
          have hsAdmissible : s ∈ Icc B (M - R) :=
            mem_Icc.mpr ⟨Nat.le_of_not_gt hsB, Nat.le_of_not_gt hsLate⟩
          exact hre.trans (hnone s hsAdmissible hsF)
  have hbaseSum :
      (∑ s ∈ S, ((M - s : ℕ) : ℝ) / E) ≤ (M : ℝ) ^ 2 / E := by
    dsimp [S]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (LagDiscrepancy.lagLengthSum_le_sq M) hE.le
  have hsmallSum :
      (∑ s ∈ S, if s < B then (M : ℝ) else 0) ≤ (B : ℝ) * M := by
    calc
      (∑ s ∈ S, if s < B then (M : ℝ) else 0) =
          ((((S.filter fun s => s < B).card : ℕ) : ℝ) * M) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (B : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast small_shift_count_le M B
        · positivity
  have hforbiddenSum :
      (∑ s ∈ S, if s ∈ F then (M : ℝ) else 0) ≤ (F.card : ℝ) * M := by
    calc
      (∑ s ∈ S, if s ∈ F then (M : ℝ) else 0) =
          ((((S.filter fun s => s ∈ F).card : ℕ) : ℝ) * M) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (F.card : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast forbidden_shift_count_le M F
        · positivity
  have hlateSum :
      (∑ s ∈ S, if M - R < s then (R : ℝ) else 0) ≤ (M : ℝ) * R := by
    calc
      (∑ s ∈ S, if M - R < s then (R : ℝ) else 0) =
          ((((S.filter fun s => M - R < s).card : ℕ) : ℝ) * R) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (M : ℝ) * R := by
        apply mul_le_mul_of_nonneg_right
        · have hc : (S.filter fun s => M - R < s).card ≤ M := by
            exact (card_filter_le _ _).trans (by
              dsimp [S]
              exact positive_shift_count_le M)
          exact_mod_cast hc
        · positivity
  have hsumUpper :
      (∑ s ∈ S, (autocorrelation z M s).re) ≤
        (M : ℝ) ^ 2 / E + (B + F.card + R : ℕ) * (M : ℝ) := by
    have hsum := Finset.sum_le_sum fun s hs => hterm s hs
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at hsum
    norm_num only [Nat.cast_add]
    nlinarith
  have hMfirst : 8 * D ^ 2 ≤ M :=
    (le_max_left _ _).trans hM
  have hMsecond : 16 * (B + F.card + R) * D ^ 2 ≤ M :=
    (le_max_right _ _).trans hM
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hMpos : 0 < (M : ℝ) := by
    have : 0 < 8 * D ^ 2 := by positivity
    exact_mod_cast this.trans_le hMfirst
  have hdiag :
      (M : ℝ) ≤ (M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * (D : ℝ) ^ 2)).2
    have hMfirstReal : 8 * (D : ℝ) ^ 2 ≤ (M : ℝ) := by exact_mod_cast hMfirst
    nlinarith
  have hboundary :
      2 * ((B + F.card + R : ℕ) : ℝ) * (M : ℝ) ≤
        (M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * (D : ℝ) ^ 2)).2
    have hMsecondReal :
        16 * ((B + F.card + R : ℕ) : ℝ) * (D : ℝ) ^ 2 ≤ (M : ℝ) := by
      exact_mod_cast hMsecond
    nlinarith
  have hnormUpper :
      ‖∑ j ∈ range M, z j‖ ^ 2 ≤
        (M : ℝ) + 2 * ((M : ℝ) ^ 2 / E +
          ((B + F.card + R : ℕ) : ℝ) * M) := by
    rw [norm_sum_sq_eq_autocorrelation z M hz]
    dsimp [S] at hsumUpper
    have htwosum := mul_le_mul_of_nonneg_left hsumUpper
      (show (0 : ℝ) ≤ 2 by norm_num)
    exact add_le_add le_rfl htwosum
  have hstrictUpper :
      ‖∑ j ∈ range M, z j‖ ^ 2 < ((M : ℝ) / D) ^ 2 := by
    have hEeq : E = 8 * (D : ℝ) ^ 2 := by
      dsimp [E, nextDensityDenominator]
      push_cast
      ring
    rw [hEeq] at hnormUpper
    have hhalf :
        (M : ℝ) ^ 2 / (2 * (D : ℝ) ^ 2) < ((M : ℝ) / D) ^ 2 := by
      field_simp
      nlinarith
    have hcoarse :
        ‖∑ j ∈ range M, z j‖ ^ 2 ≤
          (M : ℝ) ^ 2 / (2 * (D : ℝ) ^ 2) := by
      calc
        ‖∑ j ∈ range M, z j‖ ^ 2 ≤
            (M : ℝ) + 2 * ((M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2) +
              ((B + F.card + R : ℕ) : ℝ) * M) := hnormUpper
        _ = (M : ℝ) + 2 * ((M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2)) +
              2 * ((B + F.card + R : ℕ) : ℝ) * M := by ring
        _ ≤ (M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2) +
              2 * ((M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2)) +
              (M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2) :=
          add_le_add (add_le_add hdiag le_rfl) hboundary
        _ = (M : ℝ) ^ 2 / (2 * (D : ℝ) ^ 2) := by
          field_simp
          ring
    exact hcoarse.trans_lt hhalf
  have hlower : ((M : ℝ) / D) ^ 2 < ‖∑ j ∈ range M, z j‖ ^ 2 :=
    (sq_lt_sq₀ (by positivity) (norm_nonneg _)).2 hlarge
  exact (not_lt_of_ge hstrictUpper.le) hlower

lemma nextDensityDenominator_pos (D : ℕ) (hD : 1 ≤ D) :
    1 ≤ nextDensityDenominator D := by
  unfold nextDensityDenominator
  have hpos : 0 < 8 * D ^ 2 :=
    Nat.mul_pos (by norm_num) (pow_pos (by omega) _)
  omega

lemma iteratedDifference_norm_one (z : ℕ → ℂ) (shifts : List ℕ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ∀ j, ‖iteratedDifference z shifts j‖ = 1 := by
  induction shifts generalizing z with
  | nil => simpa [iteratedDifference] using hz
  | cons s shifts ih =>
      apply ih
      intro j
      simp [hz]

/-- Arbitrary finite autocorrelation iteration. Every selected shift is at
least `B`, all selected shifts are distinct, `F` is avoided, the residual
length is at least `K`, and the recursive density loss is displayed. -/
theorem finite_autocorrelation_iteration
    (z : ℕ → ℂ) (M D B K d : ℕ) (F : Finset ℕ)
    (hz : ∀ j, ‖z j‖ = 1) (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hM : iterationLengthThresholdAux D B K F.card d ≤ M)
    (hlarge : (M : ℝ) / D < ‖∑ j ∈ range M, z j‖) :
    ∃ shifts : List ℕ,
      shifts.length = d ∧
      shifts.Nodup ∧
      (∀ s ∈ shifts, B ≤ s) ∧
      (∀ s ∈ shifts, s ∉ F) ∧
      K ≤ M - shifts.sum ∧
      ((M - shifts.sum : ℕ) : ℝ) / densityDenominator D d <
        ‖∑ j ∈ range (M - shifts.sum), iteratedDifference z shifts j‖ := by
  induction d generalizing z M D F with
  | zero =>
      refine ⟨[], rfl, List.nodup_nil, ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp at hs
      · intro s hs
        simp at hs
      · simpa [iterationLengthThresholdAux] using hM
      · simpa [densityDenominator, iteratedDifference] using hlarge
  | succ d ih =>
      let R := iterationLengthThresholdAux
        (nextDensityDenominator D) B K (F.card + 1) d
      have hstep : oneStepLengthThreshold D B F.card R ≤ M := by
        simpa [iterationLengthThresholdAux, R] using hM
      obtain ⟨s, hsRange, hsF, hsLarge⟩ :=
        oneStep_autocorrelation_extraction z M D B R F hz hD hstep hlarge
      have hsBounds := mem_Icc.mp hsRange
      have hR : R ≤ M - s := by omega
      let z' : ℕ → ℂ := fun j => z (j + s) * conj (z j)
      have hz' : ∀ j, ‖z' j‖ = 1 := by
        intro j
        simp [z', hz]
      have hcard : (insert s F).card = F.card + 1 := by
        rw [card_insert_of_notMem hsF]
      have hM' : iterationLengthThresholdAux (nextDensityDenominator D) B K
          (insert s F).card d ≤ M - s := by
        rw [hcard]
        exact hR
      have hlarge' :
          ((M - s : ℕ) : ℝ) / nextDensityDenominator D <
            ‖∑ j ∈ range (M - s), z' j‖ := by
        simpa [autocorrelation, z'] using hsLarge
      obtain ⟨rest, hrestLength, hrestNodup, hrestLower,
          hrestAvoid, hrestResidual, hrestLarge⟩ :=
        ih z' (M - s) (nextDensityDenominator D) (insert s F)
          hz' (nextDensityDenominator_pos D hD) hM' hlarge'
      refine ⟨s :: rest, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hrestLength]
      · rw [List.nodup_cons]
        constructor
        · intro hsRest
          exact hrestAvoid s hsRest (mem_insert_self s F)
        · exact hrestNodup
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hsBounds.1
        · exact hrestLower t ht
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hsF
        · exact fun htF => hrestAvoid t ht (mem_insert_of_mem htF)
      · simpa [List.sum_cons, Nat.sub_sub] using hrestResidual
      · simpa [List.sum_cons, Nat.sub_sub, densityDenominator,
          iteratedDifference, z'] using hrestLarge

/-- `Fin d` form of the arbitrary-depth theorem for base-ten geometric phases.
The displayed coefficient is exactly `c * ∏ t, (10^(shifts t) - 1)`. -/
theorem finite_geometric_autocorrelation_iteration
    (c : ℝ) (M D B K d : ℕ) (F : Finset ℕ)
    (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hM : iterationLengthThresholdAux D B K F.card d ≤ M)
    (hlarge : (M : ℝ) / D <
      ‖∑ j ∈ range M, geometricPhase c j‖) :
    ∃ shifts : Fin d → ℕ,
      Function.Injective shifts ∧
      (∀ t, B ≤ shifts t) ∧
      (∀ t, shifts t ∉ F) ∧
      K ≤ M - ∑ t, shifts t ∧
      ((M - ∑ t, shifts t : ℕ) : ℝ) / densityDenominator D d <
        ‖∑ j ∈ range (M - ∑ t, shifts t),
          geometricPhase
            (c * ∏ t, ((10 : ℝ) ^ shifts t - 1)) j‖ := by
  have hz : ∀ j, ‖geometricPhase c j‖ = 1 := by
    intro j
    simpa [geometricPhase, Theory.PiDigits.T27.phase] using
      Theory.PiDigits.T27.norm_phase (1 : ℤ) ((10 : ℝ) ^ j * c)
  obtain ⟨shifts, hlength, hnodup, hlower, havoid,
      hresidual, hresonance⟩ :=
    finite_autocorrelation_iteration (geometricPhase c) M D B K d F
      hz hD hB hM hlarge
  subst d
  let indexed : Fin shifts.length → ℕ := shifts.get
  have hindexedList : List.ofFn indexed = shifts := by
    exact List.ofFn_get shifts
  have hinjective : Function.Injective indexed := by
    apply List.nodup_ofFn.mp
    simpa [hindexedList] using hnodup
  refine ⟨indexed, hinjective, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hlower (indexed t) (List.get_mem shifts t)
  · intro t
    exact havoid (indexed t) (List.get_mem shifts t)
  · simpa [indexed, ← List.sum_ofFn, hindexedList] using hresidual
  · have hresonance' :
        ((M - shifts.sum : ℕ) : ℝ) / densityDenominator D shifts.length <
          ‖∑ j ∈ range (M - shifts.sum),
            geometricPhase
              (c * (shifts.map fun s => (10 : ℝ) ^ s - 1).prod) j‖ := by
        simpa only [iteratedDifference_geometricPhase] using hresonance
    have hsum : shifts.sum = ∑ t, indexed t := by
      rw [← List.sum_ofFn, hindexedList]
    have hproduct :
        (shifts.map fun s => (10 : ℝ) ^ s - 1).prod =
          ∏ t, ((10 : ℝ) ^ indexed t - 1) := by
      rw [← List.prod_ofFn]
      apply congrArg List.prod
      calc
        shifts.map (fun s => (10 : ℝ) ^ s - 1) =
            (List.ofFn indexed).map (fun s => (10 : ℝ) ^ s - 1) :=
          congrArg (List.map fun s => (10 : ℝ) ^ s - 1) hindexedList.symm
        _ = List.ofFn (fun t => (10 : ℝ) ^ indexed t - 1) := by
          rw [List.map_ofFn]
          rfl
    rw [← hsum, ← hproduct]
    exact hresonance'

lemma iterationLengthThresholdAux_pos (D B K q d : ℕ)
    (hD : 1 ≤ D) (hK : 1 ≤ K) :
    1 ≤ iterationLengthThresholdAux D B K q d := by
  cases d with
  | zero => simpa [iterationLengthThresholdAux] using hK
  | succ d =>
      simp only [iterationLengthThresholdAux, oneStepLengthThreshold]
      apply (show 1 ≤ 8 * D ^ 2 by
        have hpos : 0 < 8 * D ^ 2 :=
          Nat.mul_pos (by norm_num) (pow_pos (by omega) _)
        omega).trans
      exact le_max_left _ _

/-- Correctly labelled form of T10's initial-resonance bridge. This uses
T10's accepted finite long-lag and Fourier extraction lemmas and keeps the
premise as the literal negation of canonical A1. -/
theorem literal_not_A1_implies_arbitrarily_long_initial_resonance
    (hnotA1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ ∀ K : ℕ, 1 ≤ K →
        ∃ N r h : ℕ,
          N = 16 * A * n * K ∧
          r ∈ Icc 1 (N - 1) ∧
          K ≤ N - r ∧
          h ∈ Icc 1 (256 * A * n) ∧
          ((N - r : ℕ) : ℝ) /
              (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2) <
            ‖∑ j ∈ range (N - r),
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
                  (((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) *
                    Real.pi : ℝ) : ℂ))‖ := by
  push Not at hnotA1
  obtain ⟨A, hA, hbad⟩ := hnotA1
  have h32A : 1 ≤ 32 * A := by
    have hpos : 0 < 32 * A := Nat.mul_pos (by norm_num) (by omega)
    exact hpos
  obtain ⟨nRadius, hnRadius, hRadius⟩ :=
    LagDiscrepancy.eventually_eight_mul_scaled_decimalRadius_le_one
      (32 * A) h32A
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  have hmax : 1 ≤ max n0 nRadius := hn0.trans (le_max_left _ _)
  obtain ⟨n, hnmax, hbadN⟩ := hbad (max n0 nRadius) hmax
  have hn0n : n0 ≤ n := (le_max_left n0 nRadius).trans hnmax
  have hnRadiusN : nRadius ≤ n := (le_max_right n0 nRadius).trans hnmax
  have hn : 1 ≤ n := hn0.trans hn0n
  have hRadiusRaw := hRadius n hnRadiusN
  have hRadius256 :
      256 * (A : ℝ) * (n : ℝ) * LagDiscrepancy.decimalRadius n ≤ 1 := by
    convert hRadiusRaw using 1 <;> push_cast <;> ring
  refine ⟨n, hn0n, hn, ?_⟩
  intro K hK
  let N : ℕ := 16 * A * n * K
  have hANpos : 0 < A * n := Nat.mul_pos (by omega) (by omega)
  have hN : 1 ≤ N := by
    dsimp [N]
    have hpos : 0 < 16 * A * n * K := by positivity
    omega
  have hNlarge : 8 * A * n ≤ N := by
    dsimp [N]
    have hKpos : 0 < K := by omega
    nlinarith
  have hRadius8 :
      8 * (A : ℝ) * (n : ℝ) * LagDiscrepancy.decimalRadius n ≤ 1 := by
    have hrho := (LagDiscrepancy.decimalRadius_pos n).le
    nlinarith
  obtain ⟨r, hr, hlong, hdisc⟩ :=
    badFinite_nearReturn_implies_longLag A n N hA hn hNlarge hRadius8
      (hbadN N hN)
  obtain ⟨h, hh, hresonance⟩ :=
    longLagDiscrepancy_implies_resonance A n N r hA hn hr hRadius256 hdisc
  have hKlength : K ≤ N - r := by
    have hmul : (16 * A * n) * K ≤ (16 * A * n) * (N - r) := by
      simpa [N, mul_assoc] using hlong
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  refine ⟨N, r, h, rfl, hr, hKlength, hh, ?_⟩
  simpa only [lagExponentialSum, lagOrbitPoint] using hresonance

/-- Literal failure of canonical A1 conditionally forces arbitrary-depth
resonances. The premise exactly negates A1's ordered, diagonal-inclusive
`Q_pi` quantifiers. The shift family is positive, injective, and avoids the
original lag `r`; no assertion here says that the premise holds. -/
theorem literal_not_A1_implies_arbitrary_depth_resonance
    (hnotA1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ ∀ d K : ℕ, 1 ≤ K →
        ∃ N r h : ℕ, ∃ shifts : Fin d → ℕ,
          N = 16 * A * n *
            iterationLengthThresholdAux
              (131072 * A ^ 2 * n ^ 2) 1 K 1 d ∧
          r ∈ Icc 1 (N - 1) ∧
          h ∈ Icc 1 (256 * A * n) ∧
          Function.Injective shifts ∧
          (∀ t, 1 ≤ shifts t) ∧
          (∀ t, shifts t ≠ r) ∧
          K ≤ N - r - ∑ t, shifts t ∧
          (((N - r - ∑ t, shifts t : ℕ) : ℝ) /
              densityDenominator (131072 * A ^ 2 * n ^ 2) d <
            ‖iteratedResonanceSum (N - r) h r d shifts‖) := by
  obtain ⟨A, hA, hT10⟩ :=
    literal_not_A1_implies_arbitrarily_long_initial_resonance hnotA1
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hT10n⟩ := hT10 n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  intro d K hK
  let D : ℕ := 131072 * A ^ 2 * n ^ 2
  let L : ℕ := iterationLengthThresholdAux D 1 K 1 d
  have hD : 1 ≤ D := by
    dsimp [D]
    have hpos : 0 < 131072 * A ^ 2 * n ^ 2 := by positivity
    omega
  have hL : 1 ≤ L := iterationLengthThresholdAux_pos D 1 K 1 d hD hK
  obtain ⟨N, r, h, hN, hr, hLlength, hh, hinitial⟩ := hT10n L hL
  let c : ℝ := (h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi
  have hphase (j : ℕ) :
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
            (((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi : ℝ) : ℂ)) =
        geometricPhase c j := by
    unfold geometricPhase c
    congr 1
    push_cast
    ring
  have hinitial' :
      (((N - r : ℕ) : ℝ) / D <
        ‖∑ j ∈ range (N - r), geometricPhase c j‖) := by
    have hDcast : (D : ℝ) = 131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      dsimp [D]
      push_cast
      ring
    rw [hDcast]
    simpa only [hphase] using hinitial
  have hthreshold :
      iterationLengthThresholdAux D 1 K ({r} : Finset ℕ).card d ≤ N - r := by
    simpa [L] using hLlength
  obtain ⟨shifts, hinjective, hpositive, havoids, hresidual, hresonance⟩ :=
    finite_geometric_autocorrelation_iteration c (N - r) D 1 K d {r}
      hD (by norm_num) hthreshold hinitial'
  refine ⟨N, r, h, shifts, ?_, hr, hh, hinjective, hpositive, ?_,
    hresidual, ?_⟩
  · simpa [D, L] using hN
  · intro t
    simpa using havoids t
  · unfold iteratedResonanceSum
    dsimp [c, D] at hresonance ⊢
    have hcoefficient :
        (h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi *
            (∏ t, ((10 : ℝ) ^ shifts t - 1)) =
          (h : ℝ) * ((10 : ℝ) ^ r - 1) *
            (∏ t, ((10 : ℝ) ^ shifts t - 1)) * Real.pi := by
      ring
    rw [hcoefficient] at hresonance
    exact hresonance

/-- Checked depth-two specialization: in addition to the original lag `r`,
there are two positive, mutually distinct shifts, each different from `r`.
The residual length, harmonic cutoff, recursive denominator, and both phase
factors are literal in the conclusion. -/
theorem literal_not_A1_implies_depth_two_resonance
    (hnotA1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ ∀ K : ℕ, 1 ≤ K →
        ∃ N r h s0 s1 : ℕ,
          N = 16 * A * n *
            iterationLengthThresholdAux
              (131072 * A ^ 2 * n ^ 2) 1 K 1 2 ∧
          r ∈ Icc 1 (N - 1) ∧
          h ∈ Icc 1 (256 * A * n) ∧
          1 ≤ s0 ∧ 1 ≤ s1 ∧
          s0 ≠ r ∧ s1 ≠ r ∧ s0 ≠ s1 ∧
          K ≤ N - r - s0 - s1 ∧
          (((N - r - s0 - s1 : ℕ) : ℝ) /
              densityDenominator (131072 * A ^ 2 * n ^ 2) 2 <
            ‖∑ j ∈ range (N - r - s0 - s1),
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
                  (((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) *
                    ((10 : ℝ) ^ s0 - 1) * ((10 : ℝ) ^ s1 - 1) *
                    Real.pi : ℝ) : ℂ))‖) := by
  obtain ⟨A, hA, hmain⟩ :=
    literal_not_A1_implies_arbitrary_depth_resonance hnotA1
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hmainn⟩ := hmain n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  intro K hK
  obtain ⟨N, r, h, shifts, hN, hr, hh, hinjective, hpositive,
      havoids, hresidual, hresonance⟩ := hmainn 2 K hK
  let s0 : ℕ := shifts 0
  let s1 : ℕ := shifts 1
  have hs01 : s0 ≠ s1 := by
    intro heq
    have hfin : (0 : Fin 2) = 1 := hinjective heq
    norm_num at hfin
  refine ⟨N, r, h, s0, s1, hN, hr, hh, hpositive 0, hpositive 1,
    havoids 0, havoids 1, hs01, ?_, ?_⟩
  · simp only [Fin.sum_univ_two] at hresidual
    dsimp [s0, s1] at hresidual ⊢
    omega
  · unfold iteratedResonanceSum at hresonance
    simp only [Fin.sum_univ_two, Fin.prod_univ_two] at hresonance
    dsimp [s0, s1]
    have hresidualLength :
        N - r - shifts 0 - shifts 1 = N - r - (shifts 0 + shifts 1) := by
      omega
    rw [hresidualLength]
    have hphaseTwo (j : ℕ) :
        Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
              (((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) *
                ((10 : ℝ) ^ shifts 0 - 1) * ((10 : ℝ) ^ shifts 1 - 1) *
                Real.pi : ℝ) : ℂ)) =
          geometricPhase
            ((h : ℝ) * ((10 : ℝ) ^ r - 1) *
              (((10 : ℝ) ^ shifts 0 - 1) * ((10 : ℝ) ^ shifts 1 - 1)) *
              Real.pi) j := by
      unfold geometricPhase
      congr 1
      push_cast
      ring
    simpa only [hphaseTwo] using hresonance

end IteratedLagResonance
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.IteratedLagResonance.oneStep_autocorrelation_extraction
#print axioms DecimalFactorComplexity.IteratedLagResonance.finite_autocorrelation_iteration
#print axioms DecimalFactorComplexity.IteratedLagResonance.finite_geometric_autocorrelation_iteration
#print axioms DecimalFactorComplexity.IteratedLagResonance.literal_not_A1_implies_arbitrarily_long_initial_resonance
#print axioms DecimalFactorComplexity.IteratedLagResonance.literal_not_A1_implies_arbitrary_depth_resonance
#print axioms DecimalFactorComplexity.IteratedLagResonance.literal_not_A1_implies_depth_two_resonance
