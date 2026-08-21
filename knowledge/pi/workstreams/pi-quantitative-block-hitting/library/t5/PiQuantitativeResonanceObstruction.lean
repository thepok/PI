import TheoryLib.PiDigits.T27FiniteExponentialCylinderCoverage
import TheoryLib.PiDigits.T29FixedFrequencyResonance
import TheoryLib.PiQuantitativeBlockHitting.T1PiQuantitativeBlockHitting

/-!
# A quantitative resonance obstruction forced by failure of C1

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file proves a necessary consequence of the literal negation of T1's
canonical conjecture C1. It proves no converse. In particular, it neither
proves nor refutes C1. The right branch of the main theorem is conditional on
canonical V1 and records an obstruction at unbounded word lengths.

For a full-containment deadline `D = C * k * 10^k`, the possible zero-based
starts are exactly those below `N = D - k + 1`. The exponential sum in the
main theorem is normalized by this explicit `N`.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.QuantitativeResonanceObstruction

/-- Coverage with one canonical-rate constant at every length at least `K`
already implies C1. Shorter words are padded to length `K`; enlarging the
constant accounts for their common length-`K` deadline. -/
theorem C1_of_eventual_fullContainment (C K : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (heventual : ∀ k : ℕ, K ≤ k →
      Theory.PiDigits.QuantitativeBlockHitting.CoversAllLengthKWordsBy
        Theory.PiDigits.piDigit k
        (C * k * 10 ^ k)) :
    Theory.PiDigits.QuantitativeBlockHitting.C1 := by
  classical
  let C' := C * K * 10 ^ K
  have hC' : 1 ≤ C' := by
    dsimp [C']
    simpa only [one_mul] using
      Nat.mul_le_mul (Nat.mul_le_mul hC hK)
        (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
  have hCC' : C ≤ C' := by
    dsimp [C']
    calc
      C = C * 1 * 1 := by omega
      _ ≤ C * K * 10 ^ K :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hK)
          (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
  refine ⟨C', hC', ?_⟩
  intro k hk w
  by_cases hlarge : K ≤ k
  · obtain ⟨n, hn, hocc⟩ := heventual k hlarge w
    refine ⟨n, hn.trans ?_, hocc⟩
    exact Nat.mul_le_mul (Nat.mul_le_mul hCC' le_rfl) le_rfl
  · have hkK : k ≤ K := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    let wK : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord K := fun i =>
      if hi : i.val < k then w ⟨i.val, hi⟩ else 0
    obtain ⟨n, hn, hocc⟩ := heventual K le_rfl wK
    refine ⟨n, ?_, ?_⟩
    · have hfactor : 1 ≤ k * 10 ^ k := by
        simpa only [one_mul] using
          Nat.mul_le_mul hk (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
      calc
        n + k ≤ n + K := Nat.add_le_add_left hkK n
        _ ≤ C' := by simpa only [C'] using hn
        _ = C' * 1 := by simp
        _ ≤ C' * (k * 10 ^ k) := Nat.mul_le_mul_left C' hfactor
        _ = C' * k * 10 ^ k := by simp only [Nat.mul_assoc]
    · intro j
      have hj := hocc (Fin.castLE hkK j)
      simpa only [wK, Fin.val_castLE, dif_pos j.isLt] using hj

/-- A word omitted by the first `N` possible starts forces a nonzero bounded
frequency whose unnormalized pi-orbit sum is larger than the explicit linear
threshold. This is the finite-prefix version of T29's global-missing lemma. -/
theorem exists_piOrbit_resonance_of_missingBefore
    (s : List (Fin 10)) (N : ℕ) (hN : 0 < N)
    (hmissing : ∀ n : ℕ, n < N → ¬ ∀ i : ℕ, ∀ hi : i < s.length,
      Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ (2 * s.length) ∧
      (8 * (10 : ℝ) ^ (2 * s.length))⁻¹ * (N : ℝ) <
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ := by
  change ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ Theory.PiDigits.T29.H s.length ∧
    Theory.PiDigits.T29.epsilon s.length * (N : ℝ) <
      ‖Theory.PiDigits.T27.exponentialSum
        Theory.PiDigits.T27.piFractionalOrbit N h‖
  by_contra hno
  have hbound : Theory.PiDigits.T27.FirstFrequencyBound
      Theory.PiDigits.T27.piFractionalOrbit N
      (Theory.PiDigits.T29.H s.length)
      (Theory.PiDigits.T29.epsilon s.length * (N : ℝ)) := by
    intro h h0 hH
    exact le_of_not_gt fun hlarge => hno ⟨h, h0, hH, hlarge⟩
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcertificate :
      (Theory.PiDigits.T29.H s.length : ℝ) *
          (Theory.PiDigits.T29.epsilon s.length * (N : ℝ)) +
          (N : ℝ) *
            (1 / (((Theory.PiDigits.T29.H s.length : ℝ) + 1) *
              Theory.PiDigits.T27.decimalCylinderLength s.length ^ 2)) <
        (N : ℝ) := by
    calc
      (Theory.PiDigits.T29.H s.length : ℝ) *
            (Theory.PiDigits.T29.epsilon s.length * (N : ℝ)) +
            (N : ℝ) *
              (1 / (((Theory.PiDigits.T29.H s.length : ℝ) + 1) *
                Theory.PiDigits.T27.decimalCylinderLength s.length ^ 2)) =
          (N : ℝ) *
            ((Theory.PiDigits.T29.H s.length : ℝ) *
                Theory.PiDigits.T29.epsilon s.length +
              1 / (((Theory.PiDigits.T29.H s.length : ℝ) + 1) *
                Theory.PiDigits.T27.decimalCylinderLength s.length ^ 2)) := by ring
      _ < (N : ℝ) * 1 := mul_lt_mul_of_pos_left
        (Theory.PiDigits.T29.certificateCoefficient_lt_one s.length) hNR
      _ = (N : ℝ) := mul_one _
  obtain ⟨n, hnN, hnmem⟩ :=
    Theory.PiDigits.T27.decimalCylinder_covered_of_firstFrequencyBound
      Theory.PiDigits.T27.piFractionalOrbit N
      (Theory.PiDigits.T29.H s.length) hN
      (Theory.PiDigits.T27.decimalCylinderLeft s)
      (Theory.PiDigits.T27.decimalCylinderLength s.length)
      (Theory.PiDigits.T29.epsilon s.length * (N : ℝ))
      (fun j _hj => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (Theory.PiDigits.T27.decimalCylinderLength_pos s.length)
      (Theory.PiDigits.T27.decimalCylinderRight_le_one s) hbound hcertificate
  rw [Theory.PiDigits.T27.decimalCylinder_interval] at hnmem
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
    s (Theory.PiDigits.T27.piFractionalOrbit n) hnmem
  apply hmissing n hnN
  intro i hi
  have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
    Real.pi Real.pi_pos.le n i
  exact (Theory.PiDigits.T20.decimalDigit_pi (n + i)).symm.trans
    (hshift.symm.trans (hdigits i hi))

/-- A length-`k` function-valued word missing at the exact full-containment
deadline yields the requested normalized resonance at the exact number of
admissible starts. -/
theorem normalized_piOrbit_resonance_of_missing_fullContainment
    (C k : ℕ) (hC : 1 ≤ C)
    (w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k)
    (hmissing : ¬ ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
      ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ (2 * k) ∧
      (8 * (10 : ℝ) ^ (2 * k))⁻¹ ≤
        ‖Theory.PiDigits.T27.exponentialSum Theory.PiDigits.T27.piFractionalOrbit
          (C * k * 10 ^ k - k + 1) h‖ /
            ((C * k * 10 ^ k - k + 1 : ℕ) : ℝ) := by
  let D := C * k * 10 ^ k
  let N := D - k + 1
  let s : List (Fin 10) := List.ofFn w
  have hkD : k ≤ D := by
    dsimp [D]
    calc
      k = 1 * k * 1 := by omega
      _ ≤ C * k * 10 ^ k :=
        Nat.mul_le_mul (Nat.mul_le_mul hC le_rfl)
          (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
  have hN : 0 < N := by
    dsimp [N]
    omega
  have hmissingBefore : ∀ n : ℕ, n < N →
      ¬ ∀ i : ℕ, ∀ hi : i < s.length,
        Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩ := by
    intro n hn hocc
    apply hmissing
    refine ⟨n, ?_, ?_⟩
    · dsimp [N] at hn
      omega
    · intro j
      have hj : j.val < s.length := by simp only [s, List.length_ofFn, j.isLt]
      simpa only [s, List.get_ofFn] using hocc j.val hj
  obtain ⟨h, h0, hH, hlarge⟩ :=
    exists_piOrbit_resonance_of_missingBefore s N hN hmissingBefore
  refine ⟨h, h0, ?_, ?_⟩
  · simpa only [s, List.length_ofFn] using hH
  · have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    have hnormalized :
        (8 * (10 : ℝ) ^ (2 * s.length))⁻¹ ≤
          ‖Theory.PiDigits.T27.exponentialSum
            Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) := by
      apply (le_div_iff₀ hNR).2
      exact hlarge.le
    simpa only [s, List.length_ofFn, N, D] using hnormalized

/-- **Necessary obstruction under failure of C1; no converse is asserted.**

The hypothesis is the literal negation of T1's `C1`. The conclusion explicitly
splits on canonical V1. If V1 holds, then for every positive scale constant
`C` and every positive threshold `K`, a bad length `k ≥ K` has a displayed
word missing at the full-containment deadline `C*k*10^k`, and the pi orbit at
the exact start cutoff `C*k*10^k-k+1` has a displayed nonzero frequency and
normalized resonance. This theorem neither proves nor refutes C1. -/
theorem not_C1_implies_V1_failure_or_unbounded_resonance
    (hnotC1 : ¬ Theory.PiDigits.QuantitativeBlockHitting.C1) :
    (¬ Theory.PiDigits.V1) ∨
      (Theory.PiDigits.V1 ∧
        ∀ C K : ℕ, 1 ≤ C → 1 ≤ K →
          ∃ k : ℕ, K ≤ k ∧
            ∃ w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k,
            (¬ ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
              ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
            ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ (2 * k) ∧
              (8 * (10 : ℝ) ^ (2 * k))⁻¹ ≤
                ‖Theory.PiDigits.T27.exponentialSum
                  Theory.PiDigits.T27.piFractionalOrbit
                  (C * k * 10 ^ k - k + 1) h‖ /
                    ((C * k * 10 ^ k - k + 1 : ℕ) : ℝ)) := by
  classical
  by_cases hV1 : Theory.PiDigits.V1
  · right
    refine ⟨hV1, ?_⟩
    intro C K hC hK
    have hbad : ∃ k : ℕ, K ≤ k ∧
        ∃ w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k,
        ¬ Theory.PiDigits.QuantitativeBlockHitting.FullyContainedOccurrence
          Theory.PiDigits.piDigit w
          (C * k * 10 ^ k) := by
      by_contra hnone
      apply hnotC1
      apply C1_of_eventual_fullContainment C K hC hK
      intro k hk w
      by_contra hw
      exact hnone ⟨k, hk, w, hw⟩
    obtain ⟨k, hk, w, hw⟩ := hbad
    have hmissing : ¬ ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
        ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j := by
      rintro ⟨n, hn, hdigits⟩
      apply hw
      exact ⟨n, hn, fun j => (hdigits j).symm⟩
    obtain ⟨h, h0, hH, hresonance⟩ :=
      normalized_piOrbit_resonance_of_missing_fullContainment
        C k hC w hmissing
    exact ⟨k, hk, w, hmissing, h, h0, hH, hresonance⟩
  · exact Or.inl hV1

end Theory.PiDigits.QuantitativeResonanceObstruction

#print axioms Theory.PiDigits.QuantitativeResonanceObstruction.C1_of_eventual_fullContainment
#print axioms Theory.PiDigits.QuantitativeResonanceObstruction.exists_piOrbit_resonance_of_missingBefore
#print axioms Theory.PiDigits.QuantitativeResonanceObstruction.normalized_piOrbit_resonance_of_missing_fullContainment
#print axioms Theory.PiDigits.QuantitativeResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_resonance
