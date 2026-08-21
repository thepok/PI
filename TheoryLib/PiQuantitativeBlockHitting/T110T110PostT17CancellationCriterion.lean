import TheoryLib.PiQuantitativeBlockHitting.T17T17PowerTenDiophantineReduction

/-!
# T110: post-T17 cancellation criterion

T17 proves that, under an explicit power-of-ten Diophantine hypothesis,
literal failure of C1 forces the exact aggregated Fourier lower bound at
arbitrarily large admissible decimal scales.  This file packages the direct
contrapositive: a strict upper bound on that same quantity throughout one
admissible tail forces C1.

The Diophantine premise remains explicit.  This theorem supplies no
cancellation estimate for the fixed pi orbit and therefore does not by itself
resolve C1.
-/

noncomputable section

namespace Theory.PiDigits.T110PostT17CancellationCriterion

open Theory.PiDigits.BoundaryRobustFejerDichotomy
open Theory.PiDigits.PowerTenDiophantineReduction
open Theory.PiDigits.QuantitativeBlockHitting

/-- Exact tail contrapositive of T17.

The guards `A ≤ k` and `1 ≤ k` make the hypothesis no stronger than needed:
T17 already supplies them for its resonant scales.  The threshold `K` itself
may be zero; T17 is invoked at `max K 1`. -/
theorem C1_of_tail_aggregatedFourierSum_lt_of_powerTenDiophantine
    (mu A C K : ℕ) (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A) (hC : 1 ≤ C)
    (hsmall :
      ∀ k : ℕ, K ≤ k → A ≤ k → 1 ≤ k →
        let q : ℕ := 10 ^ k
        let D : ℕ := C * k * q
        let N : ℕ := D - k + 1
        let r : ℕ := (mu - 1) * D + 1
        let M : ℕ := 2 * 10 ^ (2 * k + r)
        aggregatedFourierSum Theory.PiDigits.T27.piFractionalOrbit N q M <
          (N : ℝ) / (2 * q)) :
    C1 := by
  by_contra hnotC1
  obtain ⟨k, hmaxk, hAk, hk, _w, hrest⟩ :=
    not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine
      mu A hmu hpi hnotC1 C (max K 1) hC (by omega)
  have hKk : K ≤ k := (le_max_left K 1).trans hmaxk
  have hupper := hsmall k hKk hAk hk
  dsimp only at hrest hupper
  rcases hrest with
    ⟨_ha, _hmissing, _hempty, _hexcluded, _hpred, _hsucc, _hcut, hlower⟩
  exact (not_lt_of_ge hlower) hupper

#print axioms C1_of_tail_aggregatedFourierSum_lt_of_powerTenDiophantine

end Theory.PiDigits.T110PostT17CancellationCriterion
