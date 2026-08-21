import TheoryLib.PiPositiveLowerBlockDensity.T6T6FixedFrequencyLowerDensityObstruction
import TheoryLib.PiPositiveLowerBlockDensity.T7T7InvariantEmpiricalCluster
import TheoryLib.PiPositiveLowerBlockDensity.T19T19MinimalDeBruijnFlow

/-!
# T20: synchronized minimal flow and invariant Fourier obstruction

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

Every conclusion about pi below is necessary-only: it is conditional on the
literal negation of canonical C1. No assertion that C1 fails (or holds) is
made. The zero-mass conclusion uses T7's open set strictly inside a decimal
cylinder; no half-open cylinder mass is identified with a flow coordinate.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T20

open Theory.PiDigits.PositiveLowerBlockDensity

/-- The normalized pi-orbit exponential sum used for the common resonance
subsequence. -/
def normalizedPiResonance (N : ℕ) (h : ℤ) : ℝ :=
  ‖Theory.PiDigits.T27.exponentialSum
      Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ)

/-- Fixed-frequency pigeonholing on a sequence along which one word frequency
tends to zero. The returned indices are strictly increasing and positive, so
composition with the original cutoffs preserves positivity as well as every
pre-existing sequential limit. -/
theorem exists_fixed_frequency_refinement
    (k : ℕ) (w : List (Fin 10)) (hw : w.length = k)
    (cutoffs : ℕ → ℕ) (hcutoffs : StrictMono cutoffs)
    (hzero : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit w (cutoffs n))
      atTop (nhds 0)) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ (2 * k) ∧
      ∃ indices : ℕ → ℕ, StrictMono indices ∧
        (∀ n, 0 < indices n) ∧
        Tendsto
          (fun n => blockFrequency Theory.PiDigits.piDigit w
            (cutoffs (indices n))) atTop (nhds 0) ∧
        ∀ n, Theory.PiDigits.T29.epsilon k ≤
          normalizedPiResonance (cutoffs (indices n)) h := by
  let threshold := T3.finiteFourierLowerBound k
      (Theory.PiDigits.T29.H k) (Theory.PiDigits.T29.epsilon k) / 2
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact div_pos (T6.finiteFourierLowerBound_pos k) (by norm_num)
  have hparameters :
      0 ≤ Theory.PiDigits.T29.epsilon k ∧ 0 < threshold ∧
        threshold ≤ T3.finiteFourierLowerBound k
          (Theory.PiDigits.T29.H k) (Theory.PiDigits.T29.epsilon k) := by
    refine ⟨(Theory.PiDigits.T29.epsilon_pos k).le, hthreshold, ?_⟩
    dsimp [threshold]
    linarith [T6.finiteFourierLowerBound_pos k]
  let S := Theory.PiDigits.T29.boundedFrequencies (Theory.PiDigits.T29.H k)
  let R : ℤ → ℕ → Prop := fun h n =>
    Theory.PiDigits.T29.epsilon k ≤ normalizedPiResonance (cutoffs n) h
  have hunbounded : ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ ∃ h ∈ S, R h n := by
    intro B
    have hsmall : ∀ᶠ n : ℕ in atTop,
        blockFrequency Theory.PiDigits.piDigit w (cutoffs n) < threshold :=
      (tendsto_order.1 hzero).2 threshold hthreshold
    have hpositive : ∀ᶠ n : ℕ in atTop, 0 < cutoffs n :=
      hcutoffs.tendsto_atTop.eventually (eventually_ge_atTop 1)
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hsmall.and hpositive)
    let n := max B J
    have hn := hJ n (le_max_right B J)
    obtain ⟨h, hh0, hhH, hresonance⟩ :=
      T6.exists_bounded_resonance_of_blockFrequency_lt
        k (Theory.PiDigits.T29.H k) (cutoffs n) hn.2
        (Theory.PiDigits.T29.epsilon k) threshold hparameters w hw hn.1
    have hcutoffReal : 0 < (cutoffs n : ℝ) := by exact_mod_cast hn.2
    have hnormalized : Theory.PiDigits.T29.epsilon k ≤
        normalizedPiResonance (cutoffs n) h := by
      exact (le_div_iff₀ hcutoffReal).2 hresonance.le
    refine ⟨n, le_max_left B J, h, ?_, ?_⟩
    · rw [Theory.PiDigits.T29.mem_boundedFrequencies_iff]
      exact ⟨hh0, hhH⟩
    · exact hnormalized
  obtain ⟨h, hhS, hscales⟩ :=
    Theory.PiDigits.T29.Finset.exists_fixed_of_forall_exists_ge S R hunbounded
  let f : ℕ → ℝ := fun n =>
    blockFrequency Theory.PiDigits.piDigit w (cutoffs n)
  let r : ℕ → ℝ := fun n => normalizedPiResonance (cutoffs n) h
  have hwitness : ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ,
      m ≤ n ∧ f n ≤ 1 / (m : ℝ) ∧ Theory.PiDigits.T29.epsilon k ≤ r n := by
    intro m hm
    have hinv : 0 < 1 / (m : ℝ) := by positivity
    have hfrequency : ∀ᶠ n : ℕ in atTop, f n ≤ 1 / (m : ℝ) := by
      apply ((tendsto_order.1 hzero).2 (1 / (m : ℝ)) hinv).mono
      intro n hn
      exact hn.le
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hfrequency
    obtain ⟨n, hn, hresonance⟩ := hscales (max m J)
    refine ⟨n, (le_max_left m J).trans hn, ?_, ?_⟩
    · exact hJ n ((le_max_right m J).trans hn)
    · simpa [R, r] using hresonance
  let indices := T7.selectedCutoffs f r (Theory.PiDigits.T29.epsilon k) hwitness
  have hindices : StrictMono indices :=
    T7.selectedCutoffs_strictMono f r (Theory.PiDigits.T29.epsilon k) hwitness
  have hindicesPositive : ∀ n, 0 < indices n :=
    T7.selectedCutoffs_positive f r (Theory.PiDigits.T29.epsilon k) hwitness
  have hh := hhS
  rw [Theory.PiDigits.T29.mem_boundedFrequencies_iff] at hh
  refine ⟨h, hh.1, ?_, indices, hindices, hindicesPositive, ?_, ?_⟩
  · simpa [Theory.PiDigits.T29.H] using hh.2
  · exact hzero.comp hindices.tendsto_atTop
  · intro n
    simpa [indices, r] using
      T7.selectedCutoffs_resonance f r (Theory.PiDigits.T29.epsilon k) hwitness n

/-- All T19 and T7 necessary-only conclusions, synchronized on one cutoff
sequence. The edge length is `vertexLength + 1`; hence `vertexLength = 0` is
the explicit least-length `k = 1` case. -/
structure NecessaryPiSynchronizedObstruction where
  vertexLength : ℕ
  deficientWord : T19.DecimalWord (vertexLength + 1)
  least_k_ge_one : 1 ≤ vertexLength + 1
  least_k_deficient :
    liminf
      (blockFrequency Theory.PiDigits.piDigit (List.ofFn deficientWord))
      atTop = 0
  least_k_shorter_positive :
    ∀ ell : ℕ, 1 ≤ ell → ell < vertexLength + 1 →
      ∀ u : T19.DecimalWord ell,
        0 < liminf
          (blockFrequency Theory.PiDigits.piDigit (List.ofFn u)) atTop
  frequency : ℤ
  frequency_ne_zero : frequency ≠ 0
  frequency_bounded :
    frequency.natAbs ≤ 2 * 10 ^ (2 * (vertexLength + 1))
  resonanceConstant : ℝ
  resonanceConstant_eq :
    resonanceConstant = Theory.PiDigits.T29.epsilon (vertexLength + 1)
  resonanceConstant_pos : 0 < resonanceConstant
  cutoffs : ℕ → ℕ
  cutoffs_strictlyIncreasing : StrictMono cutoffs
  cutoffs_positive : ∀ n, 0 < cutoffs n
  deficientWord_frequency_tendsto_zero :
    Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit
        (List.ofFn deficientWord) (cutoffs n)) atTop (nhds 0)
  resonance_on_common_cutoffs :
    ∀ n, resonanceConstant ≤ normalizedPiResonance (cutoffs n) frequency
  shorterDelta : ℝ
  shorterDelta_pos : 0 < shorterDelta
  shorterWords_uniform_eventual :
    ∀ᶠ N : ℕ in atTop,
      ∀ ell : ℕ, 1 ≤ ell → ell < vertexLength + 1 →
        ∀ u : T19.DecimalWord ell,
          shorterDelta ≤
            blockFrequency Theory.PiDigits.piDigit (List.ofFn u) N
  shorterWords_on_common_cutoffs :
    ∀ᶠ n : ℕ in atTop,
      ∀ ell : ℕ, 1 ≤ ell → ell < vertexLength + 1 →
        ∀ u : T19.DecimalWord ell,
          shorterDelta ≤ blockFrequency Theory.PiDigits.piDigit
            (List.ofFn u) (cutoffs n)
  edgeLimit : T19.DecimalWord (vertexLength + 1) → ℝ
  vertexLimit : T19.DecimalWord vertexLength → ℝ
  completeVector_converges :
    ∀ u, Tendsto
      (fun n => T19.frequencyVector Theory.PiDigits.piDigit
        (vertexLength + 1) (cutoffs n) u)
      atTop (nhds (edgeLimit u))
  edgeLimit_nonnegative : ∀ u, 0 ≤ edgeLimit u
  edgeLimit_normalized : ∑ u, edgeLimit u = 1
  outgoing_marginal_identity :
    ∀ v, T19.outgoingMarginal edgeLimit v = vertexLimit v
  incoming_marginal_identity :
    ∀ v, T19.incomingMarginal edgeLimit v = vertexLimit v
  deficientWord_zero_edge : edgeLimit deficientWord = 0
  vertexMarginals_positive : ∀ v, 0 < vertexLimit v
  k_eq_one_vertexMarginal :
    vertexLength = 0 → ∀ v, vertexLimit v = 1
  cluster : ProbabilityMeasure UnitAddCircle
  empiricalMeasures_converge :
    Tendsto (fun n => piEmpiricalMeasure (cutoffs n)) atTop (𝓝 cluster)
  empiricalCluster : MapClusterPt cluster atTop piEmpiricalMeasure
  cluster_invariant : T7.timesTenMap cluster = cluster
  boundarySafeOpenSet_isOpen :
    IsOpen (T7.decimalInnerSet (List.ofFn deficientWord))
  boundarySafeOpenSet_nonempty :
    (T7.decimalInnerSet (List.ofFn deficientWord)).Nonempty
  boundarySafeOpenSet_subset_wordCylinder :
    ∀ x : ℝ,
      (x : UnitAddCircle) ∈ T7.decimalInnerSet (List.ofFn deficientWord) →
        Int.fract x ∈ Set.Ico
          ((Theory.PiDigits.T20.wordValue (List.ofFn deficientWord) : ℝ) /
            (10 : ℝ) ^ (List.ofFn deficientWord).length)
          (((Theory.PiDigits.T20.wordValue (List.ofFn deficientWord) + 1 : ℕ) : ℝ) /
            (10 : ℝ) ^ (List.ofFn deficientWord).length)
  boundarySafeOpenSet_zero_mass :
    (cluster : Measure UnitAddCircle)
      (T7.decimalInnerSet (List.ofFn deficientWord)) = 0
  positive_frequency_fourierCoeff :
    resonanceConstant ≤ ‖T7.measureFourierCoeff cluster frequency‖
  fourier_propagation :
    ∀ r : ℕ, T7.measureFourierCoeff cluster
      ((10 : ℤ) ^ r * frequency) = T7.measureFourierCoeff cluster frequency

/-- Necessary-only T20 conclusion. Literal failure of canonical C1 produces
one common strictly increasing sequence carrying the least deficient de
Bruijn flow, weak convergence to an invariant boundary-safe cluster, and one
fixed positive Fourier resonance propagated along powers of ten.

This theorem does not assert that C1 fails for pi. -/
theorem literal_not_C1_implies_synchronized_minimal_flow_cluster
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    Nonempty NecessaryPiSynchronizedObstruction := by
  obtain ⟨flow⟩ :=
    T19.not_piPositiveLowerBlockDensity_implies_minimal_deBruijnFlow hnot
  obtain ⟨h, hh0, hhbound, indices, hindices, hindicesPositive,
      hbaseZero, hbaseResonance⟩ :=
    exists_fixed_frequency_refinement (flow.vertexLength + 1)
      (List.ofFn flow.deficientWord) (by simp) flow.cutoffs
      flow.cutoffs_strictlyIncreasing flow.deficientWord_frequency_tendsto_zero
  let baseCutoffs : ℕ → ℕ := flow.cutoffs ∘ indices
  have hbaseStrict : StrictMono baseCutoffs :=
    flow.cutoffs_strictlyIncreasing.comp hindices
  have hbasePositive (n : ℕ) : 0 < baseCutoffs n := by
    exact (hindicesPositive n).trans_le
      (StrictMono.id_le flow.cutoffs_strictlyIncreasing (indices n))
  have hbaseZero' : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit
        (List.ofFn flow.deficientWord) (baseCutoffs n))
      atTop (nhds 0) := by
    simpa [baseCutoffs, Function.comp_def] using hbaseZero
  have hbaseResonance' (n : ℕ) :
      Theory.PiDigits.T29.epsilon (flow.vertexLength + 1) ≤
        normalizedPiResonance (baseCutoffs n) h := by
    simpa [baseCutoffs, Function.comp_def] using hbaseResonance n
  have hbaseVector (u : T19.DecimalWord (flow.vertexLength + 1)) :
      Tendsto
        (fun n => T19.frequencyVector Theory.PiDigits.piDigit
          (flow.vertexLength + 1) (baseCutoffs n) u)
        atTop (nhds (flow.edgeLimit u)) := by
    simpa [baseCutoffs, Function.comp_def] using
      (flow.completeVector_converges u).comp hindices.tendsto_atTop
  obtain ⟨ν, subseq, hsubseq, hν⟩ :=
    CompactSpace.tendsto_subseq
      (fun n => piEmpiricalMeasure (baseCutoffs n))
  let cutoffs : ℕ → ℕ := baseCutoffs ∘ subseq
  have hcutoffsStrict : StrictMono cutoffs := hbaseStrict.comp hsubseq
  have hcutoffsTop : Tendsto cutoffs atTop atTop :=
    hcutoffsStrict.tendsto_atTop
  have hcutoffsPositive (n : ℕ) : 0 < cutoffs n := hbasePositive (subseq n)
  have hzero : Tendsto
      (fun n => blockFrequency Theory.PiDigits.piDigit
        (List.ofFn flow.deficientWord) (cutoffs n))
      atTop (nhds 0) := by
    simpa [cutoffs, Function.comp_def] using
      hbaseZero'.comp hsubseq.tendsto_atTop
  have hresonance (n : ℕ) :
      Theory.PiDigits.T29.epsilon (flow.vertexLength + 1) ≤
        normalizedPiResonance (cutoffs n) h := by
    simpa [cutoffs, Function.comp_def] using hbaseResonance' (subseq n)
  have hvector (u : T19.DecimalWord (flow.vertexLength + 1)) :
      Tendsto
        (fun n => T19.frequencyVector Theory.PiDigits.piDigit
          (flow.vertexLength + 1) (cutoffs n) u)
        atTop (nhds (flow.edgeLimit u)) := by
    simpa [cutoffs, Function.comp_def] using
      (hbaseVector u).comp hsubseq.tendsto_atTop
  have hshorter : ∀ᶠ n : ℕ in atTop,
      ∀ ell : ℕ, 1 ≤ ell → ell < flow.vertexLength + 1 →
        ∀ u : T19.DecimalWord ell,
          flow.shorterDelta ≤ blockFrequency Theory.PiDigits.piDigit
            (List.ofFn u) (cutoffs n) :=
    hcutoffsTop.eventually flow.shorterWords_uniform_eventual
  have hν' : Tendsto (fun n => piEmpiricalMeasure (cutoffs n))
      atTop (𝓝 ν) := by
    simpa [cutoffs, Function.comp_def] using hν
  have hcluster : MapClusterPt ν atTop piEmpiricalMeasure := by
    apply MapClusterPt.of_comp hcutoffsTop
    exact hν'.mapClusterPt
  have hinvariant : T7.timesTenMap ν = ν :=
    T7.empiricalCluster_invariant cutoffs hcutoffsTop ν hν'
  have hzeroMass : (ν : Measure UnitAddCircle)
      (T7.decimalInnerSet (List.ofFn flow.deficientWord)) = 0 := by
    exact T7.zero_mass_decimalInnerSet_of_tendsto
      (List.ofFn flow.deficientWord) cutoffs hcutoffsPositive hzero ν hν'
  have hcoeffEach (n : ℕ) :
      Theory.PiDigits.T29.epsilon (flow.vertexLength + 1) ≤
        ‖T7.measureFourierCoeff (piEmpiricalMeasure (cutoffs n)) h‖ := by
    rw [T7.norm_measureFourierCoeff_piEmpiricalMeasure
      (cutoffs n) (hcutoffsPositive n) h]
    exact hresonance n
  have hcoeff : Theory.PiDigits.T29.epsilon (flow.vertexLength + 1) ≤
      ‖T7.measureFourierCoeff ν h‖ :=
    T7.measureFourierCoeff_lower_bound_of_tendsto hν' h
      (Theory.PiDigits.T29.epsilon (flow.vertexLength + 1)) hcoeffEach
  refine ⟨{
    vertexLength := flow.vertexLength
    deficientWord := flow.deficientWord
    least_k_ge_one := flow.least_k_ge_one
    least_k_deficient := flow.least_k_deficient
    least_k_shorter_positive := flow.least_k_shorter_positive
    frequency := h
    frequency_ne_zero := hh0
    frequency_bounded := hhbound
    resonanceConstant := Theory.PiDigits.T29.epsilon (flow.vertexLength + 1)
    resonanceConstant_eq := rfl
    resonanceConstant_pos := Theory.PiDigits.T29.epsilon_pos _
    cutoffs := cutoffs
    cutoffs_strictlyIncreasing := hcutoffsStrict
    cutoffs_positive := hcutoffsPositive
    deficientWord_frequency_tendsto_zero := hzero
    resonance_on_common_cutoffs := hresonance
    shorterDelta := flow.shorterDelta
    shorterDelta_pos := flow.shorterDelta_pos
    shorterWords_uniform_eventual := flow.shorterWords_uniform_eventual
    shorterWords_on_common_cutoffs := hshorter
    edgeLimit := flow.edgeLimit
    vertexLimit := flow.vertexLimit
    completeVector_converges := hvector
    edgeLimit_nonnegative := flow.edgeLimit_nonnegative
    edgeLimit_normalized := flow.edgeLimit_normalized
    outgoing_marginal_identity := flow.outgoing_marginal_identity
    incoming_marginal_identity := flow.incoming_marginal_identity
    deficientWord_zero_edge := flow.deficientWord_zero_edge
    vertexMarginals_positive := flow.vertexMarginals_positive
    k_eq_one_vertexMarginal := flow.k_eq_one_vertexMarginal
    cluster := ν
    empiricalMeasures_converge := hν'
    empiricalCluster := hcluster
    cluster_invariant := hinvariant
    boundarySafeOpenSet_isOpen :=
      T7.decimalInnerSet_isOpen (List.ofFn flow.deficientWord)
    boundarySafeOpenSet_nonempty :=
      T7.decimalInnerSet_nonempty (List.ofFn flow.deficientWord)
    boundarySafeOpenSet_subset_wordCylinder :=
      T7.decimalInnerSet_subset_wordCylinder (List.ofFn flow.deficientWord)
    boundarySafeOpenSet_zero_mass := hzeroMass
    positive_frequency_fourierCoeff := hcoeff
    fourier_propagation := T7.invariant_measureFourierCoeff_pow ν hinvariant h
  }⟩

end Theory.PiDigits.PositiveLowerBlockDensity.T20

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T20.exists_fixed_frequency_refinement
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T20.literal_not_C1_implies_synchronized_minimal_flow_cluster
