import TheoryLib.PiLacunaryNearReturnSparsity.T10LongLagResonance
import TheoryLib.PiLacunaryNearReturnSparsity.T13IteratedLagResonance

/-!
# T73: many good middle shifts from one resonance

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

The immutable source calls the ordered, diagonal-inclusive near-return
statement canonical A1. The present agenda's conjecture identifier C1 refers
to that same near-return statement. Source sibling A10 instead counts equal
decimal factors and was called C1 only in the parent program. These two
context-dependent uses of `C1` are not equated here. This module proves only a
necessary obstruction from the literal negation of canonical A1/current-C1.
It proves no compatibility, cancellation, distinct-coefficient estimate,
canonical A1/current-C1, A10/parent-C1, or C2 claim.
-/

noncomputable section

open Finset
open scoped ComplexConjugate Real

namespace DecimalFactorComplexity.ManyChildResonanceT73

open IteratedLagResonance

/-- Legal middle shifts whose autocorrelation real part exceeds the displayed
next-density threshold. The interval is inclusive at both endpoints. -/
def goodMiddleShifts (z : ℕ → ℂ) (M D B R : ℕ) (F : Finset ℕ) : Finset ℕ :=
  (Icc B (M - R)).filter fun s =>
    s ∉ F ∧
      ((M - s : ℕ) : ℝ) / (8 * (D : ℝ) ^ 2) <
        (autocorrelation z M s).re

/-- Membership unfolds every range, forbidden-set, residual, and threshold
condition in the definition of a good middle shift. -/
theorem mem_goodMiddleShifts_iff (z : ℕ → ℂ) (M D B R : ℕ)
    (F : Finset ℕ) (s : ℕ) :
    s ∈ goodMiddleShifts z M D B R F ↔
      B ≤ s ∧ s ≤ M - R ∧ s ∉ F ∧
        ((M - s : ℕ) : ℝ) / (8 * (D : ℝ) ^ 2) <
          (autocorrelation z M s).re := by
  simp only [goodMiddleShifts, mem_filter, mem_Icc]
  tauto

/-- Every good middle shift is a legal child: it lies in the stated inclusive
range, avoids `F`, leaves at least `R` terms, and has the explicit next density
denominator `8 * D^2`. -/
theorem goodMiddleShift_child_resonance (z : ℕ → ℂ) (M D B R : ℕ)
    (F : Finset ℕ) (s : ℕ) (hB : 1 ≤ B)
    (hs : s ∈ goodMiddleShifts z M D B R F) :
    B ≤ s ∧ s ≤ M - R ∧ s ∉ F ∧ R ≤ M - s ∧
      ((M - s : ℕ) : ℝ) / (8 * (D : ℝ) ^ 2) <
        (autocorrelation z M s).re ∧
      ((M - s : ℕ) : ℝ) / (8 * (D : ℝ) ^ 2) <
        ‖autocorrelation z M s‖ := by
  rw [mem_goodMiddleShifts_iff] at hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, by omega, hs.2.2.2, ?_⟩
  exact hs.2.2.2.trans_le (Complex.re_le_norm _)

/-- Exact explicit linear lower bound for all good middle shifts. The losses
shown in the type are, respectively, the diagonal endpoint (`1/2`), the short
shifts (`B`), the forbidden shifts (`F.card`), and terminal shifts (`R`). -/
theorem goodMiddleShifts_card_lower
    (z : ℕ → ℂ) (M D B R : ℕ) (F : Finset ℕ)
    (hz : ∀ j, ‖z j‖ = 1) (hD : 1 ≤ D) (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hlarge : (M : ℝ) / D < ‖∑ j ∈ range M, z j‖) :
    3 * (M : ℝ) / (8 * (D : ℝ) ^ 2) - 1 / 2 -
        ((B + F.card + R : ℕ) : ℝ) <
      ((goodMiddleShifts z M D B R F).card : ℝ) := by
  classical
  let S : Finset ℕ := Icc 1 (M - 1)
  let G : Finset ℕ := goodMiddleShifts z M D B R F
  let E : ℝ := 8 * (D : ℝ) ^ 2
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hMnat : 0 < M := by
    by_contra hM
    have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM
    subst M
    simp at hlarge
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hMnat
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hterm : ∀ s ∈ S,
      (autocorrelation z M s).re ≤
        ((M - s : ℕ) : ℝ) / E +
          (if s ∈ G then (M : ℝ) else 0) +
          (if s < B then (M : ℝ) else 0) +
          (if s ∈ F then (M : ℝ) else 0) +
          (if M - R < s then (R : ℝ) else 0) := by
    intro s hsS
    have hnorm := norm_autocorrelation_le z M s hz
    have hre := Complex.re_le_norm (autocorrelation z M s)
    have hbase : 0 ≤ ((M - s : ℕ) : ℝ) / E := by positivity
    by_cases hsG : s ∈ G
    · simp only [if_pos hsG]
      have hresidual : ((M - s : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.sub_le M s
      have hsmall : 0 ≤ (if s < B then (M : ℝ) else 0) := by
        split <;> positivity
      have hforbidden : 0 ≤ (if s ∈ F then (M : ℝ) else 0) := by
        split <;> positivity
      have hterminal : 0 ≤ (if M - R < s then (R : ℝ) else 0) := by
        split <;> positivity
      exact hre.trans (hnorm.trans (by linarith))
    · simp only [if_neg hsG]
      by_cases hsB : s < B
      · simp only [if_pos hsB]
        have hresidual : ((M - s : ℕ) : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast Nat.sub_le M s
        have hforbidden : 0 ≤ (if s ∈ F then (M : ℝ) else 0) := by
          split <;> positivity
        have hterminal : 0 ≤ (if M - R < s then (R : ℝ) else 0) := by
          split <;> positivity
        exact hre.trans (hnorm.trans (by linarith))
      · simp only [if_neg hsB]
        by_cases hsF : s ∈ F
        · simp only [if_pos hsF]
          have hresidual : ((M - s : ℕ) : ℝ) ≤ (M : ℝ) := by
            exact_mod_cast Nat.sub_le M s
          have hterminal : 0 ≤ (if M - R < s then (R : ℝ) else 0) := by
            split <;> positivity
          exact hre.trans (hnorm.trans (by linarith))
        · simp only [if_neg hsF]
          by_cases hsLate : M - R < s
          · simp only [if_pos hsLate]
            have hresidual : M - s ≤ R := by omega
            have hresidualReal : ((M - s : ℕ) : ℝ) ≤ (R : ℝ) := by
              exact_mod_cast hresidual
            exact hre.trans (hnorm.trans (by linarith))
          · simp only [if_neg hsLate, add_zero]
            have hsRange : s ∈ Icc B (M - R) :=
              mem_Icc.mpr ⟨Nat.le_of_not_gt hsB, Nat.le_of_not_gt hsLate⟩
            have hnotThreshold : ¬ (((M - s : ℕ) : ℝ) / E <
                (autocorrelation z M s).re) := by
              intro hthreshold
              apply hsG
              apply (mem_goodMiddleShifts_iff z M D B R F s).2
              refine ⟨(mem_Icc.mp hsRange).1, (mem_Icc.mp hsRange).2, hsF, ?_⟩
              simpa [E] using hthreshold
            exact le_of_not_gt hnotThreshold
  have hbaseSum :
      (∑ s ∈ S, ((M - s : ℕ) : ℝ) / E) ≤ (M : ℝ) ^ 2 / E := by
    dsimp [S]
    rw [← sum_div]
    exact div_le_div_of_nonneg_right
      (LagDiscrepancy.lagLengthSum_le_sq M) hE.le
  have hGsubsetS : G ⊆ S := by
    intro s hsG
    have hs := (mem_goodMiddleShifts_iff z M D B R F s).mp hsG
    dsimp [S]
    simp only [mem_Icc]
    constructor
    · exact hB.trans hs.1
    · have hRM : R ≤ M := by
        by_contra hnot
        have : M - R = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hnot)
        omega
      omega
  have hfilterG : S.filter (fun s => s ∈ G) = G := by
    ext s
    simp only [mem_filter]
    constructor
    · exact fun hs => hs.2
    · exact fun hs => ⟨hGsubsetS hs, hs⟩
  have hgoodSum :
      (∑ s ∈ S, if s ∈ G then (M : ℝ) else 0) =
        (G.card : ℝ) * M := by
    rw [← sum_filter, hfilterG]
    simp
  have hsmallSum :
      (∑ s ∈ S, if s < B then (M : ℝ) else 0) ≤ (B : ℝ) * M := by
    calc
      (∑ s ∈ S, if s < B then (M : ℝ) else 0) =
          ((S.filter fun s => s < B).card : ℝ) * M := by
            rw [← sum_filter]
            simp
      _ ≤ (B : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast small_shift_count_le M B
        · positivity
  have hforbiddenSum :
      (∑ s ∈ S, if s ∈ F then (M : ℝ) else 0) ≤
        (F.card : ℝ) * M := by
    calc
      (∑ s ∈ S, if s ∈ F then (M : ℝ) else 0) =
          ((S.filter fun s => s ∈ F).card : ℝ) * M := by
            rw [← sum_filter]
            simp
      _ ≤ (F.card : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast forbidden_shift_count_le M F
        · positivity
  have hterminalSum :
      (∑ s ∈ S, if M - R < s then (R : ℝ) else 0) ≤
        (M : ℝ) * R := by
    calc
      (∑ s ∈ S, if M - R < s then (R : ℝ) else 0) =
          ((S.filter fun s => M - R < s).card : ℝ) * R := by
            rw [← sum_filter]
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
        (M : ℝ) ^ 2 / E + (G.card : ℝ) * M +
          (B : ℝ) * M + (F.card : ℝ) * M + (M : ℝ) * R := by
    have hsum := sum_le_sum fun s hs => hterm s hs
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib,
      sum_add_distrib] at hsum
    nlinarith
  have hlowerSq : ((M : ℝ) / D) ^ 2 < ‖∑ j ∈ range M, z j‖ ^ 2 :=
    (sq_lt_sq₀ (by positivity) (norm_nonneg _)).2 hlarge
  have hidentity := norm_sum_sq_eq_autocorrelation z M hz
  have htotal : ((M : ℝ) / D) ^ 2 <
      (M : ℝ) + 2 * ((M : ℝ) ^ 2 / E + (G.card : ℝ) * M +
        (B : ℝ) * M + (F.card : ℝ) * M + (M : ℝ) * R) := by
    rw [hidentity] at hlowerSq
    exact hlowerSq.trans_le (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hsumUpper (by norm_num)))
  dsimp [E, G] at htotal
  by_contra hnot
  have hcardUpper : ((goodMiddleShifts z M D B R F).card : ℝ) ≤
      3 * (M : ℝ) / (8 * (D : ℝ) ^ 2) - 1 / 2 -
        ((B + F.card + R : ℕ) : ℝ) := le_of_not_gt hnot
  have hscaled := mul_le_mul_of_nonneg_right hcardUpper hMreal.le
  norm_num only [Nat.cast_add] at hscaled
  rw [div_pow] at htotal
  have hleftEq : (M : ℝ) ^ 2 / (D : ℝ) ^ 2 =
      8 * ((M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2)) := by
    field_simp
  have hthreeEq : 3 * (M : ℝ) ^ 2 / (4 * (D : ℝ) ^ 2) =
      6 * ((M : ℝ) ^ 2 / (8 * (D : ℝ) ^ 2)) := by
    field_simp
    norm_num
  rw [hleftEq] at htotal
  have hfromLarge : 3 * (M : ℝ) ^ 2 / (4 * (D : ℝ) ^ 2) <
      (M : ℝ) + 2 * ((goodMiddleShifts z M D B R F).card : ℝ) * M +
        2 * (B : ℝ) * M + 2 * (F.card : ℝ) * M + 2 * (M : ℝ) * R := by
    rw [hthreeEq]
    nlinarith
  have hscaled2 := mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 2)
  have hfromCard :
      2 * ((goodMiddleShifts z M D B R F).card : ℝ) * M ≤
        3 * (M : ℝ) ^ 2 / (4 * (D : ℝ) ^ 2) - (M : ℝ) -
          2 * ((B : ℝ) + (F.card : ℝ) + (R : ℝ)) * M := by
    calc
      2 * ((goodMiddleShifts z M D B R F).card : ℝ) * M =
          2 * (((goodMiddleShifts z M D B R F).card : ℝ) * M) := by ring
      _ ≤ 2 * ((3 * (M : ℝ) / (8 * (D : ℝ) ^ 2) - 1 / 2 -
          ((B : ℝ) + (F.card : ℝ) + (R : ℝ))) * M) := hscaled2
      _ = 3 * (M : ℝ) ^ 2 / (4 * (D : ℝ) ^ 2) - (M : ℝ) -
          2 * ((B : ℝ) + (F.card : ℝ) + (R : ℝ)) * M := by
            field_simp
            ring
  nlinarith

/-- Autocorrelation of a base-ten geometric phase is exactly the child phase
with the new factor `10^s - 1`; the child has residual length `M - s`. -/
theorem autocorrelation_geometricPhase_eq (c : ℝ) (M s : ℕ) :
    autocorrelation (geometricPhase c) M s =
      ∑ j ∈ range (M - s),
        geometricPhase (c * ((10 : ℝ) ^ s - 1)) j := by
  unfold autocorrelation
  apply sum_congr rfl
  intro j _hj
  exact geometricPhase_difference c j s

/-- Every selected geometric shift gives the literal child resonance, with
its inclusive range, endpoint loss, residual length, and density constant. -/
theorem goodGeometricMiddleShift_child_resonance
    (c : ℝ) (M D B R : ℕ) (F : Finset ℕ) (s : ℕ) (hB : 1 ≤ B)
    (hs : s ∈ goodMiddleShifts (geometricPhase c) M D B R F) :
    B ≤ s ∧ s ≤ M - R ∧ s ∉ F ∧ R ≤ M - s ∧
      ((M - s : ℕ) : ℝ) / (8 * (D : ℝ) ^ 2) <
        (∑ j ∈ range (M - s),
          geometricPhase (c * ((10 : ℝ) ^ s - 1)) j).re ∧
      ((M - s : ℕ) : ℝ) / (8 * (D : ℝ) ^ 2) <
        ‖∑ j ∈ range (M - s),
          geometricPhase (c * ((10 : ℝ) ^ s - 1)) j‖ := by
  have hchild := goodMiddleShift_child_resonance
    (geometricPhase c) M D B R F s hB hs
  simpa only [autocorrelation_geometricPhase_eq] using hchild

/-- A sufficient parent length for `children` simultaneous good shifts, each
leaving at least `R` terms. There is no hidden floor or ceiling. -/
def manyChildLengthThreshold (D children R : ℕ) : ℕ :=
  8 * D ^ 2 * (children + R + 3)

/-- Literal failure of source-canonical A1, called C1 by the present agenda,
yields arbitrarily many simultaneous two-scale resonances. This is not the
A10 equal-factor statement called C1 in the parent program. The premise
unfolds the ordered, diagonal-inclusive `Q_pi` quantifiers. The conclusion
retains the parent resonance and every good child; it makes no compatibility
or cancellation assertion. -/
theorem literal_not_canonical_C1_implies_many_child_two_scale_resonances
    (hnotC1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧
        ∀ children R : ℕ, 1 ≤ children → 1 ≤ R →
          ∃ N r h : ℕ,
            N = 16 * A * n *
              manyChildLengthThreshold
                (131072 * A ^ 2 * n ^ 2) children R ∧
            r ∈ Icc 1 (N - 1) ∧
            h ∈ Icc 1 (256 * A * n) ∧
            (((N - r : ℕ) : ℝ) /
                (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2) <
              ‖∑ j ∈ range (N - r),
                geometricPhase
                  ((h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi) j‖) ∧
            children ≤
              (goodMiddleShifts
                (geometricPhase
                  ((h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi))
                (N - r) (131072 * A ^ 2 * n ^ 2) 1 R {r}).card ∧
            ∀ s ∈ goodMiddleShifts
                (geometricPhase
                  ((h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi))
                (N - r) (131072 * A ^ 2 * n ^ 2) 1 R {r},
              1 ≤ s ∧ s ≤ N - r - R ∧ s ≠ r ∧ R ≤ N - r - s ∧
              (((N - r - s : ℕ) : ℝ) /
                    (8 * ((131072 * A ^ 2 * n ^ 2 : ℕ) : ℝ) ^ 2) <
                (∑ j ∈ range (N - r - s),
                  geometricPhase
                    ((h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi *
                      ((10 : ℝ) ^ s - 1)) j).re) ∧
              (((N - r - s : ℕ) : ℝ) /
                    (8 * ((131072 * A ^ 2 * n ^ 2 : ℕ) : ℝ) ^ 2) <
                ‖∑ j ∈ range (N - r - s),
                  geometricPhase
                    ((h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi *
                      ((10 : ℝ) ^ s - 1)) j‖) := by
  obtain ⟨A, hA, hinitial⟩ :=
    literal_not_A1_implies_arbitrarily_long_initial_resonance hnotC1
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hinitialN⟩ := hinitial n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  intro children R hchildren hR
  let D : ℕ := 131072 * A ^ 2 * n ^ 2
  let L : ℕ := manyChildLengthThreshold D children R
  have hD : 1 ≤ D := by
    dsimp [D]
    have : 0 < 131072 * A ^ 2 * n ^ 2 := by positivity
    omega
  have hL : 1 ≤ L := by
    dsimp [L, manyChildLengthThreshold]
    have : 0 < 8 * D ^ 2 * (children + R + 3) := by positivity
    omega
  obtain ⟨N, r, h, hN, hr, hLlength, hh, hparentRaw⟩ :=
    hinitialN L hL
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
  have hDcast : (D : ℝ) =
      131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    dsimp [D]
    push_cast
    ring
  have hparent : (((N - r : ℕ) : ℝ) / D <
      ‖∑ j ∈ range (N - r), geometricPhase c j‖) := by
    rw [hDcast]
    simpa only [hphase] using hparentRaw
  have hz : ∀ j, ‖geometricPhase c j‖ = 1 := by
    intro j
    simpa [geometricPhase, Theory.PiDigits.T27.phase] using
      Theory.PiDigits.T27.norm_phase (1 : ℤ) ((10 : ℝ) ^ j * c)
  have hcardLower := goodMiddleShifts_card_lower
    (geometricPhase c) (N - r) D 1 R {r} hz hD (by norm_num) hR hparent
  have hscaleNat : 8 * D ^ 2 * (children + R + 3) ≤ N - r := by
    simpa [L, manyChildLengthThreshold] using hLlength
  have hscaleReal :
      8 * (D : ℝ) ^ 2 * ((children : ℝ) + R + 3) ≤ (N - r : ℕ) := by
    exact_mod_cast hscaleNat
  have hden : 0 < 8 * (D : ℝ) ^ 2 := by positivity
  have hchildrenLower : (children : ℝ) ≤
      3 * ((N - r : ℕ) : ℝ) / (8 * (D : ℝ) ^ 2) - 1 / 2 -
        (((1 + ({r} : Finset ℕ).card + R : ℕ) : ℝ)) := by
    simp only [card_singleton, Nat.cast_add, Nat.cast_one]
    rw [le_sub_iff_add_le, le_sub_iff_add_le]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hchildrenCardReal : (children : ℝ) <
      ((goodMiddleShifts (geometricPhase c) (N - r) D 1 R {r}).card : ℝ) :=
    hchildrenLower.trans_lt hcardLower
  have hchildrenCard : children ≤
      (goodMiddleShifts (geometricPhase c) (N - r) D 1 R {r}).card := by
    exact_mod_cast hchildrenCardReal.le
  refine ⟨N, r, h, ?_, hr, hh, ?_, hchildrenCard, ?_⟩
  · simpa [D, L] using hN
  · simpa [c, hDcast] using hparent
  · intro s hs
    have hchild := goodGeometricMiddleShift_child_resonance
      c (N - r) D 1 R {r} s (by norm_num) hs
    rcases hchild with ⟨hs1, hsUpper, hsAvoid, hsResidual, hsRe, hsNorm⟩
    have hsr : s ≠ r := by simpa using hsAvoid
    refine ⟨hs1, hsUpper, hsr, hsResidual, ?_, ?_⟩
    · simpa [c, D, mul_assoc] using hsRe
    · simpa [c, D, mul_assoc] using hsNorm

end DecimalFactorComplexity.ManyChildResonanceT73

#print axioms DecimalFactorComplexity.ManyChildResonanceT73.mem_goodMiddleShifts_iff
#print axioms DecimalFactorComplexity.ManyChildResonanceT73.goodMiddleShift_child_resonance
#print axioms DecimalFactorComplexity.ManyChildResonanceT73.goodMiddleShifts_card_lower
#print axioms DecimalFactorComplexity.ManyChildResonanceT73.autocorrelation_geometricPhase_eq
#print axioms DecimalFactorComplexity.ManyChildResonanceT73.goodGeometricMiddleShift_child_resonance
#print axioms DecimalFactorComplexity.ManyChildResonanceT73.literal_not_canonical_C1_implies_many_child_two_scale_resonances
