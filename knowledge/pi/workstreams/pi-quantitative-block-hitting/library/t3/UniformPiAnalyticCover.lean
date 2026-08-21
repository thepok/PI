import TheoryLib.PiDigits.T27FiniteExponentialCylinderCoverage
import TheoryLib.PiQuantitativeBlockHitting.T1PiQuantitativeBlockHitting

/-!
# Uniform analytic conditions for quantitative decimal block hitting

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file proves conditional implications only. In particular, it does not
establish any of the finite exponential-sum bounds below for `Real.pi`.

For each positive word length `k`, the hypothesis supplies a positive prefix
length `N`, a frequency cutoff `H`, and a common bound `B`. The displayed
strict inequality is exactly the finite certificate used by T27 to force a
positive count in every half-open decimal cylinder of length `10⁻ᵏ`.
The bound `N ≤ C * k * 10^k` controls starts; changing `C` to `C + 1`
accounts for full containment of the final length-`k` occurrence.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.QuantitativeAnalyticCover

/-- A single finite Fourier certificate at decimal word length `k`.
All frequencies with `0 < |h| ≤ H`, of both signs, have the same bound `B`.
The strict numerical inequality is T27's sufficient condition for every
decimal interval of length `10⁻ᵏ` to contain one of the first `N` orbit points. -/
def PiFiniteFrequencyCertificate (k N H : ℕ) (B : ℝ) : Prop :=
  0 < N ∧
    T27.FirstFrequencyBound T27.piFractionalOrbit N H B ∧
    H * B + N *
      (1 / ((H + 1 : ℝ) * T27.decimalCylinderLength k ^ 2)) < N

/-- One constant controls the prefix lengths of a finite Fourier certificate
for every positive decimal word length. The witnesses `N`, `H`, and `B` may
depend on `k`; the prefix constant `C` may not. -/
def UniformPiFiniteFrequencyCertificates (C : ℕ) : Prop :=
  1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
    ∃ N H : ℕ, ∃ B : ℝ,
      N ≤ C * k * 10 ^ k ∧ PiFiniteFrequencyCertificate k N H B

/-- T20 and T27 turn one explicit finite-frequency certificate into an
occurrence of every function-valued length-`k` decimal word among starts
`n < N`. Function-valued words include leading-zero words. -/
theorem everyLengthKWord_occursBefore_of_piFiniteFrequencyCertificate
    (k N H : ℕ) (B : ℝ) (hcert : PiFiniteFrequencyCertificate k N H B) :
    ∀ w : QuantitativeBlockHitting.DecimalWord k, ∃ n < N,
      ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j := by
  obtain ⟨hN, hfrequency, hstrict⟩ := hcert
  have hraw :
      ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ H →
        ‖∑ j ∈ range N,
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
              ((T27.piFractionalOrbit j : ℝ) : ℂ))‖ ≤ B := by
    intro h hzero hH
    simpa only [T27.exponentialSum, T27.phase] using
      hfrequency h hzero hH
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hHreal : 0 < (H + 1 : ℝ) := by positivity
  have hdeficit :
      T27.decimalCylinderLength k -
          ((N : ℝ) - H * B -
            N * (1 / ((H + 1 : ℝ) *
              T27.decimalCylinderLength k ^ 2))) /
              ((N : ℝ) * (H + 1 : ℝ)) <
        T27.decimalCylinderLength k := by
    apply sub_lt_self
    exact div_pos (by linarith) (mul_pos hNreal hHreal)
  intro w
  let s : List (Fin 10) := List.ofFn w
  obtain ⟨n, hnN, hn⟩ :=
    T27.pi_everyLengthKWord_occurs_of_finiteExponentialBounds
      k H N hN B hraw hdeficit s (by simp [s])
  refine ⟨n, hnN, ?_⟩
  intro j
  have hj : j.val < s.length := by simp [s]
  simpa [s] using hn j.val hj

/-- A uniform family of finite-frequency certificates at
`N ≤ C * k * 10^k` gives every length-`k` word with full containment by
`(C + 1) * k * 10^k`. The added one is the explicit start-to-containment
loss. -/
theorem uniformPiFiniteFrequencyCertificates_give_fullContainment
    (C : ℕ) (hcert : UniformPiFiniteFrequencyCertificates C) :
    ∀ k : ℕ, 1 ≤ k → ∀ w : QuantitativeBlockHitting.DecimalWord k, ∃ n : ℕ,
      n + k ≤ (C + 1) * k * 10 ^ k ∧
        ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j := by
  intro k hk w
  obtain ⟨N, H, B, hNbound, hfinite⟩ := hcert.2 k hk
  obtain ⟨n, hnN, hn⟩ :=
    everyLengthKWord_occursBefore_of_piFiniteFrequencyCertificate
      k N H B hfinite w
  refine ⟨n, ?_, hn⟩
  have hpow : 1 ≤ 10 ^ k := one_le_pow₀ (by norm_num)
  have hkpow : k ≤ k * 10 ^ k := by
    simpa only [mul_one] using Nat.mul_le_mul_left k hpow
  calc
    n + k ≤ N + k := Nat.add_le_add_right hnN.le k
    _ ≤ C * k * 10 ^ k + k := Nat.add_le_add_right hNbound k
    _ ≤ C * k * 10 ^ k + k * 10 ^ k := Nat.add_le_add_left hkpow _
    _ = (C + 1) * k * 10 ^ k := by ring

/-- The uniform analytic hypothesis implies canonical C1, with the stated
constant change from `C` to `C + 1`. This remains a conditional theorem. -/
theorem uniformPiFiniteFrequencyCertificates_implies_C1
    (C : ℕ) (hcert : UniformPiFiniteFrequencyCertificates C) :
    QuantitativeBlockHitting.C1 := by
  refine ⟨C + 1, by omega, ?_⟩
  intro k hk w
  obtain ⟨n, hcontained, hdigits⟩ :=
    uniformPiFiniteFrequencyCertificates_give_fullContainment
      C hcert k hk w
  exact ⟨n, hcontained, fun j => (hdigits j).symm⟩

/-- Hostile-review surface: every analytic quantifier is expanded. One `C`
works for every positive `k`; each `k` has explicit `N`, `H`, and `B`; every
nonzero signed frequency through `H` is bounded; and the strict T27
certificate yields every word fully contained by the displayed prefix after
the constant change `C ↦ C + 1`. -/
theorem explicit_uniform_pi_finiteFrequencyBounds_imply_C1
    (C : ℕ) (hC : 1 ≤ C)
    (hanalytic : ∀ k : ℕ, 1 ≤ k →
      ∃ N H : ℕ, ∃ B : ℝ,
        0 < N ∧ N ≤ C * k * 10 ^ k ∧
        (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ H →
          ‖∑ j ∈ range N,
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
                ((Int.fract ((10 : ℝ) ^ j * Real.pi) : ℝ) : ℂ))‖ ≤ B) ∧
        H * B + N *
          (1 / ((H + 1 : ℝ) * (((10 : ℝ) ^ k)⁻¹) ^ 2)) < N) :
    QuantitativeBlockHitting.C1 ∧
      ∀ k : ℕ, 1 ≤ k →
        ∀ w : QuantitativeBlockHitting.DecimalWord k, ∃ n : ℕ,
        n + k ≤ (C + 1) * k * 10 ^ k ∧
          ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j := by
  have huniform : UniformPiFiniteFrequencyCertificates C := by
    refine ⟨hC, ?_⟩
    intro k hk
    obtain ⟨N, H, B, hN, hNbound, hraw, hstrict⟩ := hanalytic k hk
    refine ⟨N, H, B, hNbound, hN, ?_, ?_⟩
    · intro h hzero hH
      simpa only [T27.exponentialSum, T27.phase, T27.piFractionalOrbit] using
        hraw h hzero hH
    · simpa only [T27.decimalCylinderLength] using hstrict
  exact ⟨uniformPiFiniteFrequencyCertificates_implies_C1 C huniform,
    uniformPiFiniteFrequencyCertificates_give_fullContainment C huniform⟩

end Theory.PiDigits.QuantitativeAnalyticCover

#print axioms Theory.PiDigits.QuantitativeAnalyticCover.everyLengthKWord_occursBefore_of_piFiniteFrequencyCertificate
#print axioms Theory.PiDigits.QuantitativeAnalyticCover.uniformPiFiniteFrequencyCertificates_give_fullContainment
#print axioms Theory.PiDigits.QuantitativeAnalyticCover.uniformPiFiniteFrequencyCertificates_implies_C1
#print axioms Theory.PiDigits.QuantitativeAnalyticCover.explicit_uniform_pi_finiteFrequencyBounds_imply_C1
