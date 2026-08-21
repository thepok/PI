import TheoryLib.PiLongLagBlockCollisionDecay.T2T2UniformLongLagResidual

/-!
# T4: published irrationality measure as a conditional T2 input

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

Publication locator for the external input:
* Doron Zeilberger and Wadim Zudilin, "The Irrationality Measure of Pi is at
  most 7.103205334137...", Moscow Journal of Combinatorics and Number Theory 9
  (2020), 407-419, DOI `10.2140/moscow.2020.9.407`.
* Retained source: `zeilberger-zudilin-moscow-2020-9-407.pdf`, SHA-256
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
* Definition locator: PDF page 3 (journal page 407), Introduction, first
  paragraph. Bound locator: PDF page 14 (journal page 418), paragraph headed
  "World record", especially the displayed bound
  `7.10320533413700172750577342281... < 8`.
* DOI URL: `https://doi.org/10.2140/moscow.2020.9.407`.

The external source is not proved by Lean. `IrrationalityMeasureBelow` records
the paper's definition of an irrationality-measure upper bound, and every
theorem using the published result takes that proposition as an explicit
hypothesis. In particular, no theorem below proves or refutes the canonical
collision-decay statement.
-/

noncomputable section

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T4

open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26
open Theory.PiDigits.LongLagBlockCollisionDecay
open Theory.PiDigits.LongLagBlockCollisionDecay.T2

/-- Source-level formulation of "the irrationality measure of `x` is below
`bound`". The witness `mu` works with every positive epsilon and an onset that
may depend on epsilon, exactly matching "all sufficiently large `q`" in the
published definition. -/
def IrrationalityMeasureBelow (x bound : ℝ) : Prop :=
  ∃ μ : ℝ, μ < bound ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ Q0 : ℕ, ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ p : ℤ,
        1 / (q : ℝ) ^ (μ + ε) < |x - (p : ℝ) / q|

/-- Quantifier audit for the external source-level statement. -/
theorem irrationalityMeasureBelow_iff_quantifiers (x bound : ℝ) :
    IrrationalityMeasureBelow x bound ↔
      ∃ μ : ℝ, μ < bound ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ Q0 : ℕ, ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ p : ℤ,
            1 / (q : ℝ) ^ (μ + ε) < |x - (p : ℝ) / q| := by
  rfl

/-- A source-level irrationality-measure bound strictly below `8` supplies an
onset for T2's effective irrationality premise at exponent `8` and constant
`1`. The source theorem remains the explicit hypothesis `hSource`. -/
theorem irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality
    (hSource : IrrationalityMeasureBelow Real.pi 8) :
    ∃ Q0 : ℕ, EffectiveIrrationality Real.pi 8 1 Q0 := by
  rcases hSource with ⟨μ, hμ, hSource⟩
  have hε : 0 < (8 : ℝ) - μ := sub_pos.mpr hμ
  obtain ⟨Q0, hQ0⟩ := hSource (8 - μ) hε
  refine ⟨Q0, ?_⟩
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q hQ hq p
  have hbound := hQ0 q hQ hq p
  have hexponent : μ + (8 - μ) = (8 : ℝ) := by ring
  simpa only [hexponent] using hbound

/-- The arithmetic-failure-free branch of T2's resonance certificate. -/
def PureLongLagResidualResonanceCertificate
    (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    ∀ C : ℝ, 1 ≤ C →
      ∃ m N : ℕ, 1 ≤ m ∧ 1 ≤ N ∧
        C * ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-s * (m : ℝ))) <
            (longResidualPairCount μ c Q0 m N : ℝ)

/-- Once effective irrationality is available, T2's disjunctive certificate
cannot take its arithmetic-failure branch. Failure of C1 therefore gives the
pure long-residual resonance branch. -/
theorem not_C1_implies_pureLongLagResidualResonanceCertificate
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hnotC1 : ¬ PiLongLagBlockCollisionDecay) :
    PureLongLagResidualResonanceCertificate μ c Q0 := by
  have hcertificate :=
    not_C1_implies_longLagResidualResonanceCertificate μ c Q0 hnotC1
  rcases hcertificate with hfailure | hpure
  · exact False.elim
      (((not_effectiveIrrationality_iff_failureCertificate μ c Q0).mpr
        hfailure) hIrr)
  · exact hpure

/-- Conditional fixed-pi reduction obtained by combining the source-level
hypothesis with T2. It asserts neither `C1` nor `¬ C1`: the latter remains an
explicit premise. -/
theorem published_mu_pi_lt_eight_and_not_C1_implies_pure_resonance
    (hSource : IrrationalityMeasureBelow Real.pi 8)
    (hnotC1 : ¬ PiLongLagBlockCollisionDecay) :
    ∃ Q0 : ℕ, EffectiveIrrationality Real.pi 8 1 Q0 ∧
      PureLongLagResidualResonanceCertificate 8 1 Q0 := by
  obtain ⟨Q0, hIrr⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality hSource
  exact ⟨Q0, hIrr,
    not_C1_implies_pureLongLagResidualResonanceCertificate hIrr hnotC1⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T4

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T4.irrationalityMeasureBelow_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T4.irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T4.not_C1_implies_pureLongLagResidualResonanceCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T4.published_mu_pi_lt_eight_and_not_C1_implies_pure_resonance
