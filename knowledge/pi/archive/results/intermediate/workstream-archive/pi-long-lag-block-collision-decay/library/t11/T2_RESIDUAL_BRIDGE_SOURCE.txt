import TheoryLib.PiLongLagBlockCollisionDecay.T1T1LongLagBlockCollisionDecay

/-!
# T2: uniform long-lag residual pairs imply canonical collision decay

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

The estimate below bounds long-lag residual strict near-returns rather than
exact equal-block pairs. Its accompanying effective-irrationality premise
removes the complementary arithmetic class. Neither premise asserts the
desired bound on exact equal decimal blocks.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T2

open DecimalFactorComplexity
open DecimalFactorComplexity.FiniteCylinderEnergy
open Theory.PiDigits.LongLagBlockCollisionDecay
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- A uniform bound for the exact T26 long-lag residual class, together with
the arithmetic premise which makes the excluded class empty. The witness
`C_s` is chosen before `m,N`, so it is independent of both scale parameters. -/
def PiUniformLongLagResidualPairDecay (μ c : ℝ) (Q0 : ℕ) : Prop :=
  EffectiveIrrationality Real.pi μ c Q0 ∧
    ∀ s : ℝ, 0 < s → s < 1 →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          (longResidualPairCount μ c Q0 m N : ℝ) ≤
            C * ((N : ℝ) + (N : ℝ) ^ 2 *
              (10 : ℝ) ^ (-s * (m : ℝ)))

/-- Quantifier audit: one `C_s` controls every positive `m,N`, with no onset
and no dependence of the constant on either scale parameter. -/
theorem piUniformLongLagResidualPairDecay_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    PiUniformLongLagResidualPairDecay μ c Q0 ↔
      EffectiveIrrationality Real.pi μ c Q0 ∧
        ∀ s : ℝ, 0 < s → s < 1 →
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
              (longResidualPairCount μ c Q0 m N : ℝ) ≤
                C * ((N : ℝ) + (N : ℝ) ^ 2 *
                  (10 : ℝ) ^ (-s * (m : ℝ))) := by
  rfl

/-- The literal quantified failure of T25's effective-irrationality premise.
The third branch gives an explicit denominator and numerator resonance. -/
def EffectiveIrrationalityFailureCertificate
    (μ c : ℝ) (Q0 : ℕ) : Prop :=
  c ≤ 0 ∨ μ ≤ 1 ∨
    ∃ q : ℕ, Q0 ≤ q ∧ 0 < q ∧
      ∃ p : ℤ, |Real.pi - (p : ℝ) / q| ≤ c / (q : ℝ) ^ μ

/-- A literal failure certificate for the uniform residual hypothesis. Either
the arithmetic separation itself fails, or one exponent `s` has arbitrarily
large finite residual resonances relative to every proposed `C ≥ 1`. -/
def LongLagResidualResonanceCertificate (μ c : ℝ) (Q0 : ℕ) : Prop :=
  EffectiveIrrationalityFailureCertificate μ c Q0 ∨
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∀ C : ℝ, 1 ≤ C →
        ∃ m N : ℕ, 1 ≤ m ∧ 1 ≤ N ∧
          C * ((N : ℝ) + (N : ℝ) ^ 2 *
            (10 : ℝ) ^ (-s * (m : ℝ))) <
              (longResidualPairCount μ c Q0 m N : ℝ)

/-- The displayed arithmetic alternatives are exactly the negation of the
effective-irrationality premise, including all endpoint inequalities. -/
theorem not_effectiveIrrationality_iff_failureCertificate
    (μ c : ℝ) (Q0 : ℕ) :
    ¬ EffectiveIrrationality Real.pi μ c Q0 ↔
      EffectiveIrrationalityFailureCertificate μ c Q0 := by
  classical
  constructor
  · intro hnot
    rw [EffectiveIrrationality] at hnot
    push Not at hnot
    by_cases hc : 0 < c
    · by_cases hμ : 1 < μ
      · exact Or.inr (Or.inr (hnot hc hμ))
      · exact Or.inr (Or.inl (le_of_not_gt hμ))
    · exact Or.inl (le_of_not_gt hc)
  · intro hfailure hIrr
    rcases hIrr with ⟨hc, hμ, hall⟩
    rcases hfailure with hcFail | hμFail | ⟨q, hQ0, hq, p, hp⟩
    · exact (not_le_of_gt hc) hcFail
    · exact (not_le_of_gt hμ) hμFail
    · exact (not_le_of_gt (hall q hQ0 hq p)) hp

/-- Every exact equal-block collision at a positive long lag belongs to T26's
residual near-return fiber once the arithmetic excluded region is empty. -/
theorem longLagCollisionSum_le_residualPairCount
    {μ c : ℝ} {Q0 m N : ℕ} (hm : 1 ≤ m)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0) :
    2 * longLagCollisionSum m N ≤
      longResidualPairCount μ c Q0 m N := by
  classical
  have hlags : Finset.Icc m (N - 1) = longResidualLags m N := by
    ext r
    rw [mem_longResidualLags_iff]
    simp only [Finset.mem_Icc]
    omega
  have hfiber : ∀ r ∈ longResidualLags m N,
      ((Finset.range (N - r)).filter fun i =>
        B_pi i m = B_pi (i + r) m).card ≤
          (residualNearReturnStarts μ c Q0 m N r).card := by
    intro r hr
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hrpos : 0 < r := (mem_longResidualLags_iff.mp hr).1
    have hfactor : factorAt piDecimalStream m i =
        factorAt piDecimalStream m (i + r) :=
      (piCylinderCode_eq_iff_factorAt_eq m i (i + r)).mp hi.2
    have hnear : i ∈ nearReturnStarts m N r := by
      simp only [nearReturnStarts, Finset.mem_filter, Finset.mem_range]
      refine ⟨hi.1, ?_⟩
      rw [← structuredDenominator_cast]
      exact equal_decimalBlocks_implies_structured_nearInteger
        m i r hrpos hfactor
    have hnotExcluded : ¬ ArithmeticExcluded μ c Q0 m i r := by
      intro hExcluded
      exact effectiveIrrationality_excludes_equal_decimalBlocks
        hrpos hIrr hExcluded hfactor
    simp only [residualNearReturnStarts, Finset.mem_filter]
    exact ⟨hnear, hnotExcluded⟩
  have hsum : longLagCollisionSum m N ≤
      ∑ r ∈ longResidualLags m N,
        (residualNearReturnStarts μ c Q0 m N r).card := by
    unfold longLagCollisionSum
    rw [hlags]
    exact Finset.sum_le_sum hfiber
  unfold longResidualPairCount
  exact Nat.mul_le_mul_left 2 hsum

/-- Pointwise comparison between the canonical ordered collision count and
the stronger residual geometric count. Both conventions count orientations,
so there is no factor loss. -/
theorem R_pi_le_longResidualPairCount
    {μ c : ℝ} {Q0 m N : ℕ} (hm : 1 ≤ m)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0) :
    R_pi m N ≤ longResidualPairCount μ c Q0 m N := by
  rw [R_pi_eq_two_mul_longLagCollisionSum hm]
  exact longLagCollisionSum_le_residualPairCount hm hIrr

/-- The explicit residual hypothesis implies canonical C1 with the displayed
choice `C_s` unchanged; in particular it is independent of `m` and `N`. -/
theorem piUniformLongLagResidualPairDecay_implies_C1
    {μ c : ℝ} {Q0 : ℕ}
    (hResidual : PiUniformLongLagResidualPairDecay μ c Q0) :
    PiLongLagBlockCollisionDecay := by
  rcases hResidual with ⟨hIrr, hdecay⟩
  intro s hs0 hs1
  obtain ⟨C, hC, hbound⟩ := hdecay s hs0 hs1
  refine ⟨C, hC, ?_⟩
  intro m N hm hN
  have hcompare : (R_pi m N : ℝ) ≤
      (longResidualPairCount μ c Q0 m N : ℝ) := by
    exact_mod_cast R_pi_le_longResidualPairCount hm hIrr
  exact hcompare.trans (hbound m N hm hN)

/-- The resonance certificate is exactly, not merely a consequence of, the
negation of the uniform residual hypothesis. -/
theorem not_piUniformLongLagResidualPairDecay_iff_resonanceCertificate
    (μ c : ℝ) (Q0 : ℕ) :
    ¬ PiUniformLongLagResidualPairDecay μ c Q0 ↔
      LongLagResidualResonanceCertificate μ c Q0 := by
  classical
  constructor
  · intro hnot
    rw [PiUniformLongLagResidualPairDecay] at hnot
    rw [LongLagResidualResonanceCertificate]
    by_cases hIrr : EffectiveIrrationality Real.pi μ c Q0
    · right
      have hnotDecay : ¬ (∀ s : ℝ, 0 < s → s < 1 →
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
              (longResidualPairCount μ c Q0 m N : ℝ) ≤
                C * ((N : ℝ) + (N : ℝ) ^ 2 *
                  (10 : ℝ) ^ (-s * (m : ℝ)))) := by
        intro hdecay
        exact hnot ⟨hIrr, hdecay⟩
      push Not at hnotDecay
      obtain ⟨s, hs0, hs1, hfail⟩ := hnotDecay
      refine ⟨s, hs0, hs1, ?_⟩
      intro C hC
      exact hfail C hC
    · exact Or.inl
        ((not_effectiveIrrationality_iff_failureCertificate μ c Q0).mp hIrr)
  · intro hcertificate hResidual
    rcases hResidual with ⟨hIrr, hdecay⟩
    rcases hcertificate with hIrrFailure | ⟨s, hs0, hs1, hresonance⟩
    · exact
        ((not_effectiveIrrationality_iff_failureCertificate μ c Q0).mpr
          hIrrFailure) hIrr
    · obtain ⟨C, hC, hbound⟩ := hdecay s hs0 hs1
      obtain ⟨m, N, hm, hN, hlarge⟩ := hresonance C hC
      exact (not_lt_of_ge (hbound m N hm hN)) hlarge

/-- Literal contrapositive of the conditional C1 theorem, expressed through
the fully quantified resonance certificate. -/
theorem not_C1_implies_longLagResidualResonanceCertificate
    (μ c : ℝ) (Q0 : ℕ) (hnotC1 : ¬ PiLongLagBlockCollisionDecay) :
    LongLagResidualResonanceCertificate μ c Q0 := by
  apply
    (not_piUniformLongLagResidualPairDecay_iff_resonanceCertificate μ c Q0).mp
  intro hResidual
  exact hnotC1 (piUniformLongLagResidualPairDecay_implies_C1 hResidual)

end Theory.PiDigits.LongLagBlockCollisionDecay.T2

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T2.longLagCollisionSum_le_residualPairCount
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T2.R_pi_le_longResidualPairCount
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T2.piUniformLongLagResidualPairDecay_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T2.piUniformLongLagResidualPairDecay_implies_C1
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T2.not_effectiveIrrationality_iff_failureCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T2.not_piUniformLongLagResidualPairDecay_iff_resonanceCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T2.not_C1_implies_longLagResidualResonanceCertificate
