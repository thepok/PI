import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiPositiveLowerBlockDensity.T3T3FiniteFourierLowerDensity
import TheoryLib.PiDigits.T29FixedFrequencyResonance

/-!
# T6: fixed-frequency obstruction to positive lower block density

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only a necessary consequence of literal failure of the
canonical C1 statement. It does not prove that C1 fails for pi, that C1 holds,
or that pi is normal.

The final theorem keeps one word and one nonzero frequency fixed while the
cutoff `N` varies. Its length-`k` words are lists over `Fin 10`, so words with
leading zero digits are included.
-/

noncomputable section

open Filter Finset Set

namespace Theory.PiDigits.PositiveLowerBlockDensity.T6

open Theory.PiDigits.PositiveLowerBlockDensity

/-- T29's explicit constants make T3's normalized cylinder lower bound
strictly positive. -/
theorem finiteFourierLowerBound_pos (k : ℕ) :
    0 < T3.finiteFourierLowerBound k
      (Theory.PiDigits.T29.H k) (Theory.PiDigits.T29.epsilon k) := by
  have hcoef := Theory.PiDigits.T29.certificateCoefficient_lt_one k
  unfold T3.finiteFourierLowerBound
  norm_num only [Nat.cast_add, Nat.cast_one]
  apply div_pos
  · linarith
  · positivity

/-- Contrapositive of T3 at one cutoff: if a word's block frequency is below
the certified cylinder lower bound, one explicitly bounded nonzero Fourier
frequency must have a large sum at that same cutoff. -/
theorem exists_bounded_resonance_of_blockFrequency_lt
    (k H N : ℕ) (hN : 0 < N) (epsilon eta : ℝ)
    (hparameters :
      0 ≤ epsilon ∧ 0 < eta ∧ eta ≤ T3.finiteFourierLowerBound k H epsilon)
    (w : List (Fin 10)) (hw : w.length = k)
    (hsmall : blockFrequency Theory.PiDigits.piDigit w N < eta) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ H ∧
      epsilon * (N : ℝ) <
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ := by
  by_contra! hbound
  have hcylinder :=
    T3.decimalCylinderFrequency_ge_of_normalizedFiniteFourierBound
      Theory.PiDigits.T27.piFractionalOrbit k H N hN epsilon eta hparameters
      (fun j _hj => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      hbound w hw
  have hlower : eta ≤ blockFrequency Theory.PiDigits.piDigit w N := by
    calc
      eta ≤
          (Theory.PiDigits.T27.cylinderCount
              Theory.PiDigits.T27.piFractionalOrbit N
              (Theory.PiDigits.T27.decimalCylinderLeft w)
              (Theory.PiDigits.T27.decimalCylinderLength w.length) : ℝ) / N :=
        hcylinder
      _ ≤ blockFrequency Theory.PiDigits.piDigit w N := by
        unfold blockFrequency
        apply div_le_div_of_nonneg_right
        · exact_mod_cast T3.piCylinderCount_le_blockCount w N
        · positivity
  exact (not_le_of_gt hsmall) hlower

/-- Necessary-only T6 conclusion. Literal failure of canonical C1 forces a
length-`k` decimal word and one fixed nonzero frequency, bounded by
`2 * 10^(2*k)`, that resonate with the displayed positive constant along
arbitrarily late cutoffs where that same word's frequency tends to zero.

This is a conditional obstruction theorem and makes no unconditional claim
about pi. -/
theorem not_piPositiveLowerBlockDensity_implies_fixed_frequency_obstruction
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ w : List (Fin 10), w.length = k ∧
      ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ (2 * k) ∧
        0 < (8 * (10 : ℝ) ^ (2 * k))⁻¹ ∧
        ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ, m ≤ N ∧
          blockFrequency Theory.PiDigits.piDigit w N ≤ 1 / (m : ℝ) ∧
          (8 * (10 : ℝ) ^ (2 * k))⁻¹ ≤
            ‖∑ j ∈ range N,
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
                  ((Theory.PiDigits.T27.piFractionalOrbit j : ℝ) : ℂ))‖ /
              (N : ℝ) := by
  have hexists : ∃ w : List (Fin 10), w ≠ [] ∧
      ¬ 0 < liminf (blockFrequency Theory.PiDigits.piDigit w) atTop := by
    by_contra hnone
    apply hnot
    intro w hw
    by_contra hnonpos
    exact hnone ⟨w, hw, hnonpos⟩
  obtain ⟨w, hwne, hwliminf⟩ := hexists
  let k := w.length
  have hk : 1 ≤ k := by
    dsimp [k]
    apply Nat.one_le_iff_ne_zero.mpr
    intro hlength
    exact hwne (List.length_eq_zero_iff.mp hlength)
  let f : ℕ → ℝ := blockFrequency Theory.PiDigits.piDigit w
  have hfnonneg : ∀ N, 0 ≤ f N :=
    blockFrequency_nonneg Theory.PiDigits.piDigit w
  have hfle : ∀ N, f N ≤ 1 :=
    blockFrequency_le_one Theory.PiDigits.piDigit w
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·) f :=
    Filter.isCoboundedUnder_ge_of_le atTop hfle
  have hliminf_nonneg : 0 ≤ liminf f atTop :=
    le_liminf_of_le hcobounded (Filter.Eventually.of_forall hfnonneg)
  have hliminf_zero : liminf f atTop = 0 := by
    apply le_antisymm
    · exact le_of_not_gt hwliminf
    · exact hliminf_nonneg
  let eta := T3.finiteFourierLowerBound k
      (Theory.PiDigits.T29.H k) (Theory.PiDigits.T29.epsilon k) / 2
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (finiteFourierLowerBound_pos k) (by norm_num)
  have hparameters :
      0 ≤ Theory.PiDigits.T29.epsilon k ∧ 0 < eta ∧
        eta ≤ T3.finiteFourierLowerBound k
          (Theory.PiDigits.T29.H k) (Theory.PiDigits.T29.epsilon k) := by
    refine ⟨(Theory.PiDigits.T29.epsilon_pos k).le, heta, ?_⟩
    dsimp [eta]
    linarith [finiteFourierLowerBound_pos k]
  let S := Theory.PiDigits.T29.boundedFrequencies (Theory.PiDigits.T29.H k)
  let P : ℤ → ℕ → Prop := fun h t =>
    ∃ N : ℕ, t ≤ N ∧ f N ≤ 1 / (t : ℝ) ∧
      Theory.PiDigits.T29.epsilon k ≤
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ)
  have hunbounded : ∀ B : ℕ, ∃ t : ℕ, B ≤ t ∧ ∃ h ∈ S, P h t := by
    intro B
    let t := max 1 B
    have hBt : B ≤ t := by
      dsimp [t]
      omega
    have ht : 0 < t := by
      dsimp [t]
      omega
    have hinv : 0 < 1 / (t : ℝ) := by positivity
    let delta : ℝ := min eta (1 / (t : ℝ))
    have hdelta : 0 < delta := by
      dsimp [delta]
      exact lt_min heta hinv
    have hfrequent : ∃ᶠ N : ℕ in atTop, f N < delta :=
      frequently_lt_of_liminf_lt hcobounded (by
        rw [hliminf_zero]
        exact hdelta)
    obtain ⟨N, htN, hlow⟩ := hfrequent.forall_exists_of_atTop t
    have hN : 0 < N := ht.trans_le htN
    have hsmall : f N < eta :=
      hlow.trans_le (min_le_left eta (1 / (t : ℝ)))
    have hfrequency : f N ≤ 1 / (t : ℝ) :=
      hlow.le.trans (min_le_right eta (1 / (t : ℝ)))
    obtain ⟨h, hh0, hhH, hresonance⟩ :=
      exists_bounded_resonance_of_blockFrequency_lt
        k (Theory.PiDigits.T29.H k) N hN
        (Theory.PiDigits.T29.epsilon k) eta hparameters w rfl hsmall
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    have hnormalized : Theory.PiDigits.T29.epsilon k ≤
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) :=
      (le_div_iff₀ hNR).2 hresonance.le
    refine ⟨t, hBt, h, ?_, ?_⟩
    · rw [Theory.PiDigits.T29.mem_boundedFrequencies_iff]
      exact ⟨hh0, hhH⟩
    · exact ⟨N, htN, hfrequency, hnormalized⟩
  obtain ⟨h, hhS, hscales⟩ :=
    Theory.PiDigits.T29.Finset.exists_fixed_of_forall_exists_ge S P hunbounded
  have hh := hhS
  rw [Theory.PiDigits.T29.mem_boundedFrequencies_iff] at hh
  refine ⟨k, hk, w, rfl, h, hh.1, ?_, ?_, ?_⟩
  · simpa [Theory.PiDigits.T29.H] using hh.2
  · exact Theory.PiDigits.T29.epsilon_pos k
  · intro m hm
    obtain ⟨t, hmt, N, htN, hfrequency, hresonance⟩ := hscales m
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hreciprocal : 1 / (t : ℝ) ≤ 1 / (m : ℝ) := by
      apply one_div_le_one_div_of_le hmreal
      exact_mod_cast hmt
    refine ⟨N, hmt.trans htN, ?_, ?_⟩
    · exact hfrequency.trans hreciprocal
    · simpa only [Theory.PiDigits.T29.epsilon,
        Theory.PiDigits.T27.exponentialSum, Theory.PiDigits.T27.phase] using hresonance

end Theory.PiDigits.PositiveLowerBlockDensity.T6

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T6.finiteFourierLowerBound_pos
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T6.exists_bounded_resonance_of_blockFrequency_lt
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T6.not_piPositiveLowerBlockDensity_implies_fixed_frequency_obstruction
