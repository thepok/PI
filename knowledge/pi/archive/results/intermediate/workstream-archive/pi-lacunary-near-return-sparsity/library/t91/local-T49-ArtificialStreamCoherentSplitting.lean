import TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting
import TheoryLib.PiLacunaryNearReturnSparsity.T37ArtificialStreamObstruction
import TheoryLib.PiDigits.T26WeylCancellationV1
import TheoryLib.PiPositiveDecimalFactorEntropy.T18T18FiniteCircleQuantization

/-!
# T49: coherent splitting without an original-coordinate branch

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module concerns only T37's explicit artificial stream, a recorded A13/A14
sibling. It makes no assertion about `Real.pi`, canonical C2, C1, or A1.
-/

noncomputable section

open Filter Finset Topology
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace DecimalFactorComplexity.ArtificialStreamCoherentSplittingT49

open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.ArtificialStreamObstruction
open DecimalFactorComplexity.FiniteCountTreeLeakage

/-- A stream parent has two distinct successor digits, each carrying at least
the fixed fraction `eta` of its overlapping first-start count. -/
def StreamQuantitativelySplitParent
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (N : ℕ) (eta : ℝ)
    (w : Word) : Prop :=
  ∃ d e : Digit, d ≠ e ∧
    eta * firstStartCount x N w ≤ firstStartCount x N (w ++ [d]) ∧
    eta * firstStartCount x N w ≤ firstStartCount x N (w ++ [e])

/-- Collision energy of all words of one fixed length in the T37 encoding. -/
def streamCollisionEnergy
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (n N : ℕ) : ℝ :=
  ∑ a : Fin (10 ^ n), (firstStartCount x N (decodedWord n a) : ℝ) ^ 2

/-- T14's energy-weighted splitting-level predicate for an arbitrary stream. -/
noncomputable def StreamQuantitativeSplittingLevel
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (n N : ℕ) (mu eta : ℝ) : Prop := by
  classical
  exact mu * streamCollisionEnergy x n N ≤
    ∑ a : Fin (10 ^ n),
      if StreamQuantitativelySplitParent x N eta (decodedWord n a) then
        (firstStartCount x N (decodedWord n a) : ℝ) ^ 2
      else 0

/-- The levels `l < m` satisfying the stream splitting predicate. -/
noncomputable def streamSplittingLevels
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (m N : ℕ) (mu eta : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun l =>
    StreamQuantitativeSplittingLevel x l N mu eta

/-- Number of stream splitting levels below `m`. -/
noncomputable def streamSplittingLevelCount
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (m N : ℕ) (mu eta : ℝ) : ℕ :=
  (streamSplittingLevels x m N mu eta).card

/-- Complete stream analogue of T14's fixed-parameter coherent predicate.
The empirical measures and their weak limit are part of the data, and every
parameter is fixed outside the triangular `m ≤ k` quantifiers. -/
def StreamCoherentPositiveDensitySplittingAt
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (empirical : ℕ → ProbabilityMeasure UnitAddCircle)
    (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle) : Prop :=
  0 < mu ∧ mu < 1 ∧ 0 < eta ∧ eta ≤ 1 / 10 ∧
    0 < d ∧ 0 ≤ B ∧ StrictMono N ∧ (∀ k, 0 < N k) ∧
    Tendsto (fun k => empirical (N k)) atTop (𝓝 nu) ∧
    ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
      d * (m : ℝ) - B ≤
        (streamSplittingLevelCount x m (N k) mu eta : ℝ)

/-- T37's symbolic decimal-tail orbit on the circle. -/
def artificialCircleOrbit (j : ℕ) : UnitAddCircle :=
  ((tailOrbit artificialStream j : ℝ) : UnitAddCircle)

/-- Empirical probability measure of T37's actual symbolic decimal-tail orbit. -/
def artificialEmpiricalMeasure (N : ℕ) : ProbabilityMeasure UnitAddCircle :=
  circleEmpiricalMeasure artificialCircleOrbit N

/-- Normalized Haar probability on `ℝ/ℤ`. -/
def circleHaarProbability : ProbabilityMeasure UnitAddCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

/-- T37's sample size is the uniform core mass plus the total error budget. -/
theorem sampledCheckpoint_eq_coreSize_add_budget (q : ℕ) :
    sampledCheckpoint q =
      10 ^ stageOrder q * zeroSeedCoreSize q +
        stageErrorBudget (stageStart q) q := by
  have htwo := twice_stageOrder_le_seedSegmentLength (stageStart q) q
  have hmul := Nat.mul_le_mul_left (10 ^ stageOrder q) htwo
  rw [sampledCheckpoint, stageStart_succ, stageLength, stageErrorBudget,
    zeroSeedCoreSize, Nat.mul_sub_left_distrib]
  rw [show 2 * stageOrder q * 10 ^ stageOrder q =
    10 ^ stageOrder q * (2 * stageOrder q) by ring]
  omega

/-- The normalized error budget tends to zero along the identity stage
sequence. This uses only T37's public error/core comparison. -/
theorem normalizedStageErrorBudget_tendsto_zero :
    Tendsto
      (fun q => (stageErrorBudget (stageStart q) q : ℝ) /
        sampledCheckpoint q)
      atTop (𝓝 0) := by
  have hm : Tendsto (fun q : ℕ => (stageOrder q : ℝ)) atTop atTop := by
    simpa [stageOrder, Nat.cast_add, Nat.cast_one] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun q : ℕ => (q : ℝ)) Filter.atTop Filter.atTop))
  have hupper : Tendsto (fun q : ℕ => 1 / (stageOrder q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hm
  apply squeeze_zero
  · intro q
    exact div_nonneg (by positivity) (by positivity)
  · intro q
    change (stageErrorBudget (stageStart q) q : ℝ) /
      (sampledCheckpoint q : ℝ) ≤ (1 : ℝ) / (stageOrder q : ℝ)
    have hcore := stageErrorBudget_mul_stageOrder_le_zeroSeedCoreSize q
    have hcoreSample : zeroSeedCoreSize q ≤ sampledCheckpoint q := by
      rw [sampledCheckpoint_eq_coreSize_add_budget]
      exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _))
    have hnat :
        stageErrorBudget (stageStart q) q * stageOrder q ≤ sampledCheckpoint q :=
      hcore.trans hcoreSample
    have hreal :
        (stageErrorBudget (stageStart q) q : ℝ) * stageOrder q ≤
          sampledCheckpoint q := by exact_mod_cast hnat
    have hNreal : 0 < (sampledCheckpoint q : ℝ) := by
      exact_mod_cast sampledCheckpoint_pos q
    have hmreal : 0 < (stageOrder q : ℝ) := by
      exact_mod_cast stageOrder_pos q
    rw [div_le_div_iff₀ hNreal hmreal]
    simpa using hreal
  · exact hupper

/-- At every depth already covered by a stage, each normalized word count is
within the normalized total error budget of the uniform value `10⁻ⁿ`. -/
theorem fixedDepth_frequency_discrepancy_le_error
    (q n : ℕ) (a : Fin (10 ^ n)) (hn : n ≤ stageOrder q) :
    abs
      ((firstStartCount artificialStream (sampledCheckpoint q)
          (decodedWord n a) : ℝ) / sampledCheckpoint q -
        ((10 ^ n : ℕ) : ℝ)⁻¹) ≤
      (stageErrorBudget (stageStart q) q : ℝ) / sampledCheckpoint q := by
  let C := firstStartCount artificialStream (sampledCheckpoint q) (decodedWord n a)
  let K := zeroSeedCoreSize q
  let E := stageErrorCount q (decodedWord n a)
  let B := stageErrorBudget (stageStart q) q
  let N := sampledCheckpoint q
  let P := 10 ^ n
  let T := 10 ^ (stageOrder q - n)
  have hcount : C = K * T + E := by
    dsimp only [C, K, E, T]
    rw [firstStartCount_sampledCheckpoint_eq_core_add_error,
      stageCoreCount_eq_coreSize_mul_pow q (decodedWord n a) (by simpa using hn)]
    simp [zeroSeedCoreSize]
  have hsample : N = P * T * K + B := by
    dsimp only [N, P, T, K, B]
    rw [sampledCheckpoint_eq_coreSize_add_budget]
    have hpow : 10 ^ stageOrder q = 10 ^ n * 10 ^ (stageOrder q - n) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
  have hE : E ≤ B := by
    exact stageErrorCount_le_budget q (decodedWord n a)
  have hNpos : 0 < (N : ℝ) := by
    dsimp only [N]
    exact_mod_cast sampledCheckpoint_pos q
  have hPpos : 0 < (P : ℝ) := by
    dsimp only [P]
    positivity
  have hPone : (1 : ℝ) ≤ P := by
    dsimp only [P]
    push_cast
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)
  have hcountReal : (C : ℝ) = K * T + E := by exact_mod_cast hcount
  have hsampleReal : (N : ℝ) = P * T * K + B := by exact_mod_cast hsample
  have hEReal : (E : ℝ) ≤ B := by exact_mod_cast hE
  have hdiff :
      (C : ℝ) / N - ((P : ℝ))⁻¹ =
        ((P : ℝ) * E - B) / ((P : ℝ) * N) := by
    rw [inv_eq_one_div]
    field_simp [hNpos.ne', hPpos.ne']
    nlinarith
  have habs : abs ((P : ℝ) * E - B) ≤ (P : ℝ) * B := by
    rw [abs_le]
    constructor <;> nlinarith [show (0 : ℝ) ≤ E by positivity,
      show (0 : ℝ) ≤ B by positivity]
  dsimp only [C, N, P, E, B] at hdiff ⊢
  rw [hdiff, abs_div, abs_of_pos (mul_pos hPpos hNpos)]
  rw [div_le_div_iff₀ (mul_pos hPpos hNpos) hNpos]
  dsimp only [P, E, B, N] at habs hNpos hPpos ⊢
  nlinarith

/-- Every fixed word has its uniform base-ten limiting frequency along T37's
unthinned sampled checkpoints. -/
theorem fixedDepth_frequency_tendsto_uniform (n : ℕ) (a : Fin (10 ^ n)) :
    Tendsto
      (fun q =>
        (firstStartCount artificialStream (sampledCheckpoint q)
          (decodedWord n a) : ℝ) / sampledCheckpoint q)
      atTop (𝓝 (((10 ^ n : ℕ) : ℝ)⁻¹)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  change Tendsto
    (fun q => abs
      ((firstStartCount artificialStream (sampledCheckpoint q)
          (decodedWord n a) : ℝ) / sampledCheckpoint q -
        ((10 ^ n : ℕ) : ℝ)⁻¹)) atTop (𝓝 0)
  apply squeeze_zero'
  · exact Eventually.of_forall fun q => abs_nonneg _
  · filter_upwards [eventually_ge_atTop n] with q hq
    exact fixedDepth_frequency_discrepancy_le_error q n a (by
      unfold stageOrder
      omega)
  · exact normalizedStageErrorBudget_tendsto_zero

/-- Integration against the generic positive-length empirical measure from T4
is the normalized finite sample sum. -/
theorem integral_circleEmpiricalMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : ℕ → UnitAddCircle) (N : ℕ) (hN : 0 < N)
    (f : C(UnitAddCircle, E)) :
    ∫ x, f x ∂(circleEmpiricalMeasure u N : Measure UnitAddCircle) =
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.range N, f (u j) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [circleEmpiricalMeasure, ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map
    (measurable_of_finite
      (fun n : Fin (M + 1) => u n.val)).aemeasurable
    f.continuous.aestronglyMeasurable]
  change (∫ x : Fin (M + 1), f (u x.val)
    ∂ProbabilityTheory.uniformOn Set.univ) = _
  have huniform :
      ProbabilityTheory.uniformOn (Set.univ : Set (Fin (M + 1))) =
        ((Fintype.card (Fin (M + 1)) : ENNReal)⁻¹ • Measure.count) := by
    ext A hA
    rw [ProbabilityTheory.uniformOn_univ]
    simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
  rw [huniform]
  simp only [Fintype.card_fin, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_count, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  simpa only [Nat.succ_eq_add_one] using
    (Fin.sum_univ_eq_sum_range (fun j => f (u j)) (M + 1))

/-- T37's recursive decoder has the expected ordinary base-ten value. -/
theorem wordValue_decodedWord (n : ℕ) (a : Fin (10 ^ n)) :
    Theory.PiDigits.T20.wordValue (decodedWord n a) = a.val := by
  induction n with
  | zero =>
      have ha : a = 0 := by ext; omega
      subst a
      rfl
  | succ n ih =>
      let ad := (decimalAppendEquiv n).symm a
      have ha : decimalAppendEquiv n ad = a :=
        (decimalAppendEquiv n).apply_symm_apply a
      have hword : decodedWord (n + 1) a = decodedWord n ad.1 ++ [ad.2] := by
        unfold decodedWord
        rw [show decodedTuple (n + 1) a =
          Fin.snoc (decodedTuple n ad.1) ad.2 by rfl]
        exact Theory.PiDigits.PositiveLowerBlockDensity.T19.ofFn_snoc n
          (decodedTuple n ad.1) ad.2
      rw [hword,
        Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_append, ih]
      simp only [List.length_cons, List.length_nil]
      rw [show Theory.PiDigits.T20.wordValue [ad.2] = ad.2.val by
        simp [Theory.PiDigits.T20.wordValue]]
      have hval : a.val = ad.2.val + 10 * ad.1.val := by
        rw [← ha]
        rfl
      omega

/-- Index of the length-`n` word beginning at one stream position in T37's
decoder. -/
noncomputable def wordIndex
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (n j : ℕ) : Fin (10 ^ n) :=
  (decodedTupleEquiv n).symm
    (Theory.PiDigits.PositiveLowerBlockDensity.T19.wordAt x j n)

theorem decodedWord_wordIndex
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (n j : ℕ) :
    decodedWord n (wordIndex x n j) = prefixWord x n j := by
  unfold decodedWord wordIndex prefixWord
  congr 1
  simpa only [decodedTupleEquiv_apply] using
    (decodedTupleEquiv n).apply_symm_apply
      (Theory.PiDigits.PositiveLowerBlockDensity.T19.wordAt x j n)

theorem wordIndex_val
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (n j : ℕ) :
    (wordIndex x n j).val = prefixLabel x n j := by
  rw [← wordValue_decodedWord n (wordIndex x n j),
    decodedWord_wordIndex]
  rfl

/-- Left endpoint on the circle of one decoded decimal word. -/
def decimalGridPoint (n : ℕ) (a : Fin (10 ^ n)) : UnitAddCircle :=
  ((((a.val : ℝ) / (10 : ℝ) ^ n) : ℝ) : UnitAddCircle)

/-- A finite prefix sum grouped exactly by T37's decoded word counts. -/
theorem sum_decimalGridPoint_eq_count
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (N n : ℕ) (f : UnitAddCircle → ℂ) :
    ∑ j ∈ Finset.range N, f (decimalGridPoint n (wordIndex x n j)) =
      ∑ a : Fin (10 ^ n),
        (firstStartCount x N (decodedWord n a) : ℂ) * f (decimalGridPoint n a) := by
  classical
  let label : Fin N → Fin (10 ^ n) := fun j => wordIndex x n j.val
  have hfiber :
      (∑ a : Fin (10 ^ n),
          ∑ j ∈ (Finset.univ : Finset (Fin N)) with label j = a,
            f (decimalGridPoint n (label j))) =
        ∑ j : Fin N, f (decimalGridPoint n (label j)) := by
    exact Finset.sum_fiberwise_of_maps_to (fun j _hj => by simp)
      (fun j => f (decimalGridPoint n (label j)))
  rw [← Fin.sum_univ_eq_sum_range] at ⊢
  change (∑ j : Fin N, f (decimalGridPoint n (label j))) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro a _ha
  have hcount :
      firstStartCount x N (decodedWord n a) =
        ((Finset.univ : Finset (Fin N)).filter fun j => label j = a).card := by
    rw [firstStartCount]
    change Theory.PiDigits.PositiveLowerBlockDensity.blockCount x
      (List.ofFn (decodedTuple n a)) N = _
    rw [Theory.PiDigits.PositiveLowerBlockDensity.T19.blockCount_ofFn_eq_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change Theory.PiDigits.PositiveLowerBlockDensity.T19.wordAt x j.val n =
        decodedTuple n a ↔
      (decodedTupleEquiv n).symm
        (Theory.PiDigits.PositiveLowerBlockDensity.T19.wordAt x j.val n) = a
    exact (decodedTupleEquiv n).symm_apply_eq.symm
  rw [hcount]
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin N)) with label j = a,
        f (decimalGridPoint n (label j))) =
        ∑ _j ∈ (Finset.univ : Finset (Fin N)) with label _j = a,
          f (decimalGridPoint n a) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [hj.2]
    _ = (((Finset.univ : Finset (Fin N)).filter fun j => label j = a).card : ℂ) *
        f (decimalGridPoint n a) := by simp

/-- At a fixed depth, the T37 frequency limits give convergence of every
Fourier-weighted decimal-grid average. -/
theorem fixedDepth_weightedFourier_tendsto (n : ℕ) (h : ℤ) :
    Tendsto
      (fun q => ∑ a : Fin (10 ^ n),
        (((firstStartCount artificialStream (sampledCheckpoint q)
          (decodedWord n a) : ℝ) / sampledCheckpoint q : ℝ) : ℂ) *
            fourier h (decimalGridPoint n a))
      atTop
      (𝓝 (∑ a : Fin (10 ^ n),
        ((((10 ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
          fourier h (decimalGridPoint n a))) := by
  apply tendsto_finsetSum
  intro a _ha
  exact ((Complex.continuous_ofReal.tendsto _).comp
    (fixedDepth_frequency_tendsto_uniform n a)).mul tendsto_const_nhds

/-- A nonzero Fourier character sums to zero on any sufficiently fine full
decimal grid. -/
theorem sum_fourier_decimalGridPoint_eq_zero
    (n : ℕ) (h : ℤ) (hh : h ≠ 0)
    (hn : 2 * (h.natAbs + 1) < 10 ^ n) :
    ∑ a : Fin (10 ^ n), fourier h (decimalGridPoint n a) = 0 := by
  classical
  let P := 10 ^ n
  letI : NeZero P := ⟨by simp [P]⟩
  have hchar :
      DecimalFactorComplexity.FiniteCircleQuantization.quantizedCharacter P h ≠ 0 :=
    DecimalFactorComplexity.FiniteCircleQuantization.lowFrequency_quantizedCharacter_ne_zero
      P (h.natAbs + 1) (by simpa [P] using hn) h hh (by omega)
  have hsum :
      ∑ z : ZMod P,
        DecimalFactorComplexity.FiniteCircleQuantization.quantizedCharacter P h z = 0 := by
    apply AddChar.sum_eq_zero_of_ne_one
    simpa only [AddChar.one_eq_zero] using hchar
  let e : Fin P ≃ ZMod P :=
    { toFun := fun a => (a.val : ZMod P)
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := by
        intro a
        apply Fin.ext
        simp [Nat.mod_eq_of_lt a.isLt]
      right_inv := by
        intro z
        exact ZMod.natCast_zmod_val z }
  calc
    ∑ a : Fin (10 ^ n), fourier h (decimalGridPoint n a) =
        ∑ z : ZMod P,
          DecimalFactorComplexity.FiniteCircleQuantization.quantizedCharacter P h z := by
      apply Fintype.sum_equiv e
      intro a
      unfold decimalGridPoint
      unfold DecimalFactorComplexity.FiniteCircleQuantization.quantizedCharacter
      rw [AddChar.mulShift_apply, fourier_coe_apply]
      change _ = ZMod.stdAddChar ((h : ZMod P) * (a.val : ZMod P))
      rw [show (h : ZMod P) * (a.val : ZMod P) =
        ((h * (a.val : ℤ) : ℤ) : ZMod P) by norm_cast]
      rw [ZMod.stdAddChar_coe]
      simp only [P, Nat.cast_pow, Nat.cast_ofNat]
      congr 1
      push_cast
      ring
    _ = 0 := hsum

/-- A tail and the left endpoint selected by its first `n` digits are at most
one decimal cell apart. -/
theorem abs_tailOrbit_sub_decimalGrid_le
    (x : DecimalFactorComplexity.ArtificialStreamObstruction.Stream)
    (n j : ℕ) :
    |tailOrbit x j - (wordIndex x n j).val / (10 : ℝ) ^ n| ≤
      ((10 : ℝ) ^ n)⁻¹ := by
  have hcell := tailOrbit_mem_closedCell x n j
  rw [← wordIndex_val x n j] at hcell
  have hpow : 0 < (10 : ℝ) ^ n := by positivity
  rw [abs_of_nonneg (sub_nonneg.mpr hcell.1)]
  have hwidth :
      (((((wordIndex x n j).val + 1 : ℕ) : ℝ) / (10 : ℝ) ^ n) -
        (wordIndex x n j).val / (10 : ℝ) ^ n) =
          ((10 : ℝ) ^ n)⁻¹ := by
    push_cast
    field_simp
    ring
  calc
    tailOrbit x j - (wordIndex x n j).val / (10 : ℝ) ^ n ≤
        ((((wordIndex x n j).val + 1 : ℕ) : ℝ) / (10 : ℝ) ^ n) -
          (wordIndex x n j).val / (10 : ℝ) ^ n :=
      sub_le_sub_right hcell.2 _
    _ = ((10 : ℝ) ^ n)⁻¹ := hwidth

/-- Fourier evaluation changes by at most the standard one-cell phase error
when a symbolic tail is replaced by its decimal-grid left endpoint. -/
theorem norm_fourier_artificialCircleOrbit_sub_grid_le (n j : ℕ) (h : ℤ) :
    ‖fourier h (artificialCircleOrbit j) -
        fourier h (decimalGridPoint n (wordIndex artificialStream n j))‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) / (10 : ℝ) ^ n := by
  let x := tailOrbit artificialStream j
  let y := (wordIndex artificialStream n j).val / (10 : ℝ) ^ n
  have hactual : fourier h (artificialCircleOrbit j) =
      Complex.exp (Complex.I * ((2 * Real.pi * (h : ℝ) * x : ℝ) : ℂ)) := by
    unfold artificialCircleOrbit
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hgrid : fourier h (decimalGridPoint n (wordIndex artificialStream n j)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (h : ℝ) * y : ℝ) : ℂ)) := by
    unfold decimalGridPoint
    rw [fourier_coe_apply]
    congr 1
    dsimp [y]
    push_cast
    field_simp
  rw [hactual, hgrid]
  have hexp :=
    DecimalFactorComplexity.FiniteCircleQuantization.norm_exp_I_mul_sub_exp_I_mul_le
      (2 * Real.pi * (h : ℝ) * x) (2 * Real.pi * (h : ℝ) * y)
  have hxy : |x - y| ≤ ((10 : ℝ) ^ n)⁻¹ := by
    simpa only [x, y] using abs_tailOrbit_sub_decimalGrid_le artificialStream n j
  calc
    _ ≤ |2 * Real.pi * (h : ℝ) * x - 2 * Real.pi * (h : ℝ) * y| := hexp
    _ = |2 * Real.pi * (h : ℝ)| * |x - y| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |2 * Real.pi * (h : ℝ)| * ((10 : ℝ) ^ n)⁻¹ :=
      mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    _ = 2 * Real.pi * (h.natAbs : ℝ) / (10 : ℝ) ^ n := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
        abs_of_nonneg Real.pi_pos.le]
      have habsh : |(h : ℝ)| = (h.natAbs : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        norm_num
      rw [habsh]
      ring

/-- The actual empirical Fourier mean differs from its count-weighted decimal
grid approximation by at most any common pointwise error bound. -/
theorem norm_circleEmpiricalMean_sub_weightedGrid_le
    (N n : ℕ) (hN : 0 < N) (h : ℤ) (C : ℝ)
    (hpoint : ∀ j < N,
      ‖fourier h (artificialCircleOrbit j) -
        fourier h (decimalGridPoint n (wordIndex artificialStream n j))‖ ≤ C) :
    ‖Theory.PiDigits.T26.circleEmpiricalMean artificialCircleOrbit (fourier h) N -
      ∑ a : Fin (10 ^ n),
        (((firstStartCount artificialStream N (decodedWord n a) : ℝ) / N : ℝ) : ℂ) *
          fourier h (decimalGridPoint n a)‖ ≤ C := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hweighted :
      (∑ a : Fin (10 ^ n),
        (((firstStartCount artificialStream N (decodedWord n a) : ℝ) / N : ℝ) : ℂ) *
          fourier h (decimalGridPoint n a)) =
        (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          fourier h (decimalGridPoint n (wordIndex artificialStream n j)) := by
    rw [sum_decimalGridPoint_eq_count]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [hweighted]
  unfold Theory.PiDigits.T26.circleEmpiricalMean
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, norm_natCast]
  have hsum :
      ‖∑ j ∈ Finset.range N,
          (fourier h (artificialCircleOrbit j) -
            fourier h (decimalGridPoint n (wordIndex artificialStream n j)))‖ ≤
        (N : ℝ) * C := by
    calc
      _ ≤ ∑ j ∈ Finset.range N,
          ‖fourier h (artificialCircleOrbit j) -
            fourier h (decimalGridPoint n (wordIndex artificialStream n j))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range N, C := by
        apply Finset.sum_le_sum
        intro j hj
        exact hpoint j (Finset.mem_range.mp hj)
      _ = (N : ℝ) * C := by simp
  calc
    (N : ℝ)⁻¹ * ‖∑ j ∈ Finset.range N,
        (fourier h (artificialCircleOrbit j) -
          fourier h (decimalGridPoint n (wordIndex artificialStream n j)))‖ ≤
        (N : ℝ)⁻¹ * ((N : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = C := by
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp

/-- Convergence of all circle Fourier integrals determines weak convergence
of probability measures. -/
theorem probabilityMeasure_tendsto_of_fourier_integrals
    {μ : ℕ → ProbabilityMeasure UnitAddCircle}
    {ν : ProbabilityMeasure UnitAddCircle}
    (hfourier : ∀ h : ℤ,
      Tendsto
        (fun k => ∫ z, fourier h z ∂(μ k : Measure UnitAddCircle))
        atTop
        (𝓝 (∫ z, fourier h z ∂(ν : Measure UnitAddCircle)))) :
    Tendsto μ atTop (𝓝 ν) := by
  classical
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  let fc : C(UnitAddCircle, ℂ) := f.toContinuousMap
  have hintegrable (ρ : ProbabilityMeasure UnitAddCircle)
      (g : C(UnitAddCircle, ℂ)) :
      Integrable g (ρ : Measure UnitAddCircle) := by
    apply Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
    exact ae_of_all _ fun z => g.norm_coe_le_norm z
  have hspan : ∀ g ∈ Submodule.span ℂ
      (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ))),
      Tendsto (fun k => ∫ z, g z ∂(μ k : Measure UnitAddCircle)) atTop
        (𝓝 (∫ z, g z ∂(ν : Measure UnitAddCircle))) := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ =>
      Tendsto (fun k => ∫ z, g z ∂(μ k : Measure UnitAddCircle)) atTop
        (𝓝 (∫ z, g z ∂(ν : Measure UnitAddCircle)))) ?_ ?_ ?_ ?_ hg
    · intro g hg
      obtain ⟨h, rfl⟩ := hg
      exact hfourier h
    · simp
    · intro g q _ _ hg hq
      have hμeq :
          (fun k => ∫ z, (g + q) z ∂(μ k : Measure UnitAddCircle)) =
            fun k => (∫ z, g z ∂(μ k : Measure UnitAddCircle)) +
              ∫ z, q z ∂(μ k : Measure UnitAddCircle) := by
        funext k
        exact integral_add (hintegrable (μ k) g) (hintegrable (μ k) q)
      have hνeq :
          (∫ z, (g + q) z ∂(ν : Measure UnitAddCircle)) =
            (∫ z, g z ∂(ν : Measure UnitAddCircle)) +
              ∫ z, q z ∂(ν : Measure UnitAddCircle) :=
        integral_add (hintegrable ν g) (hintegrable ν q)
      rw [hμeq, hνeq]
      exact hg.add hq
    · intro c g _ hg
      have hμeq :
          (fun k => ∫ z, (c • g) z ∂(μ k : Measure UnitAddCircle)) =
            fun k => c * ∫ z, g z ∂(μ k : Measure UnitAddCircle) := by
        funext k
        exact integral_const_mul c g
      have hνeq :
          (∫ z, (c • g) z ∂(ν : Measure UnitAddCircle)) =
            c * ∫ z, g z ∂(ν : Measure UnitAddCircle) :=
        integral_const_mul c g
      rw [hμeq, hνeq]
      exact hg.const_mul c
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hfmem : fc ∈ (Submodule.span ℂ
      (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hfmem
  obtain ⟨g, hgspan, hgf⟩ := hfmem (ε / 3) (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp (hspan g hgspan)
    (ε / 3) (by positivity)
  refine ⟨K, fun k hk => ?_⟩
  have hKg := hK k hk
  rw [dist_eq_norm] at hgf hKg ⊢
  have hμbound :
      ‖(∫ z, f z ∂(μ k : Measure UnitAddCircle)) -
          ∫ z, g z ∂(μ k : Measure UnitAddCircle)‖ < ε / 3 := by
    rw [← integral_sub
      (by simpa only [fc, BoundedContinuousFunction.coe_toContinuousMap] using
        hintegrable (μ k) fc)
      (hintegrable (μ k) g)]
    have hle : ‖∫ z, f z - g z ∂(μ k : Measure UnitAddCircle)‖ ≤
        ‖fc - g‖ := by
      simpa only [fc, BoundedContinuousFunction.coe_toContinuousMap,
        probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const
          (μ := (μ k : Measure UnitAddCircle))
          (C := ‖fc - g‖)
          (ae_of_all _ fun z => (fc - g).norm_coe_le_norm z))
    exact hle.trans_lt hgf
  have hνbound :
      ‖(∫ z, g z ∂(ν : Measure UnitAddCircle)) -
          ∫ z, f z ∂(ν : Measure UnitAddCircle)‖ < ε / 3 := by
    rw [← integral_sub (hintegrable ν g)
      (by simpa only [fc, BoundedContinuousFunction.coe_toContinuousMap] using
        hintegrable ν fc)]
    have hle : ‖∫ z, g z - f z ∂(ν : Measure UnitAddCircle)‖ ≤
        ‖g - fc‖ := by
      simpa only [fc, BoundedContinuousFunction.coe_toContinuousMap,
        probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const
          (μ := (ν : Measure UnitAddCircle))
          (C := ‖g - fc‖)
          (ae_of_all _ fun z => (g - fc).norm_coe_le_norm z))
    exact hle.trans_lt (by simpa only [norm_sub_rev] using hgf)
  calc
    ‖(∫ z, f z ∂(μ k : Measure UnitAddCircle)) -
        ∫ z, f z ∂(ν : Measure UnitAddCircle)‖ ≤
        ‖(∫ z, f z ∂(μ k : Measure UnitAddCircle)) -
          ∫ z, g z ∂(μ k : Measure UnitAddCircle)‖ +
        ‖(∫ z, g z ∂(μ k : Measure UnitAddCircle)) -
          ∫ z, g z ∂(ν : Measure UnitAddCircle)‖ +
        ‖(∫ z, g z ∂(ν : Measure UnitAddCircle)) -
          ∫ z, f z ∂(ν : Measure UnitAddCircle)‖ := by
      calc
        _ = ‖((∫ z, f z ∂(μ k : Measure UnitAddCircle)) -
              ∫ z, g z ∂(μ k : Measure UnitAddCircle)) +
            (((∫ z, g z ∂(μ k : Measure UnitAddCircle)) -
              ∫ z, g z ∂(ν : Measure UnitAddCircle)) +
            ((∫ z, g z ∂(ν : Measure UnitAddCircle)) -
              ∫ z, f z ∂(ν : Measure UnitAddCircle)))‖ := by congr 1; ring
        _ ≤ _ := by
          simpa only [add_assoc] using (norm_add_le _ _).trans
            (add_le_add le_rfl (norm_add_le _ _))
    _ < ε / 3 + ε / 3 + ε / 3 := by
      exact add_lt_add (add_lt_add hμbound hKg) hνbound
    _ = ε := by ring

/-- The actual symbolic decimal-tail empirical measures at T37's sampled
checkpoints converge weakly to normalized Haar probability on the circle. -/
theorem artificialEmpiricalMeasure_tendsto_circleHaarProbability :
    Tendsto (fun k => artificialEmpiricalMeasure (sampledCheckpoint k))
      atTop (𝓝 circleHaarProbability) := by
  apply probabilityMeasure_tendsto_of_fourier_integrals
  intro h
  have hhaar :
      (∫ z, fourier h z ∂(circleHaarProbability : Measure UnitAddCircle)) =
        if h = 0 then 1 else 0 := by
    exact Theory.PiDigits.T26.integral_fourier_unit h
  by_cases hh : h = 0
  · subst h
    simpa [hhaar, artificialEmpiricalMeasure, fourier_zero] using
      (tendsto_const_nhds : Tendsto (fun _k : ℕ => (1 : ℂ)) atTop (𝓝 1))
  · rw [hhaar, if_neg hh]
    have hmean :
        Tendsto
          (fun q => Theory.PiDigits.T26.circleEmpiricalMean artificialCircleOrbit
            (fourier h) (sampledCheckpoint q)) atTop (𝓝 0) := by
      refine Metric.tendsto_atTop.mpr fun ε hε => ?_
      let R : ℝ := max (2 * ((h.natAbs + 1 : ℕ) : ℝ))
        (4 * Real.pi * (h.natAbs : ℝ) / ε)
      have hpow : Tendsto (fun n : ℕ => (10 : ℝ) ^ n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      have hevent : ∀ᶠ n : ℕ in atTop, R < (10 : ℝ) ^ n :=
        hpow.eventually (eventually_gt_atTop R)
      obtain ⟨n, hnR⟩ := hevent.exists
      dsimp only [R] at hnR
      have hnAlias : 2 * (h.natAbs + 1) < 10 ^ n := by
        have hnatR : (2 * ((h.natAbs + 1 : ℕ) : ℝ)) < (10 : ℝ) ^ n :=
          (le_max_left _ _).trans_lt hnR
        exact_mod_cast hnatR
      let C : ℝ := 2 * Real.pi * (h.natAbs : ℝ) / (10 : ℝ) ^ n
      have hC : C < ε / 2 := by
        have hden : 0 < (10 : ℝ) ^ n := by positivity
        have hthreshold :
            4 * Real.pi * (h.natAbs : ℝ) / ε < (10 : ℝ) ^ n :=
          (le_max_right _ _).trans_lt hnR
        have hscaled :
            4 * Real.pi * (h.natAbs : ℝ) < (10 : ℝ) ^ n * ε := by
          exact (div_lt_iff₀ hε).mp hthreshold
        unfold C
        rw [div_lt_iff₀ hden]
        nlinarith
      have hweighted := fixedDepth_weightedFourier_tendsto n h
      have hgrid :
          (∑ a : Fin (10 ^ n),
            ((((10 ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
              fourier h (decimalGridPoint n a)) = 0 := by
        rw [← Finset.mul_sum, sum_fourier_decimalGridPoint_eq_zero n h hh hnAlias]
        simp
      rw [hgrid] at hweighted
      obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hweighted
        (ε / 2) (by positivity)
      refine ⟨K, fun q hq => ?_⟩
      have hweightedq := hK q hq
      rw [dist_zero_right] at hweightedq ⊢
      have happrox :
          ‖Theory.PiDigits.T26.circleEmpiricalMean artificialCircleOrbit
              (fourier h) (sampledCheckpoint q) -
            ∑ a : Fin (10 ^ n),
              (((firstStartCount artificialStream (sampledCheckpoint q)
                (decodedWord n a) : ℝ) / sampledCheckpoint q : ℝ) : ℂ) *
                fourier h (decimalGridPoint n a)‖ ≤ C := by
        apply norm_circleEmpiricalMean_sub_weightedGrid_le
          (sampledCheckpoint q) n (sampledCheckpoint_pos q) h C
        intro j _hj
        exact norm_fourier_artificialCircleOrbit_sub_grid_le n j h
      calc
        ‖Theory.PiDigits.T26.circleEmpiricalMean artificialCircleOrbit
            (fourier h) (sampledCheckpoint q)‖ ≤
            ‖Theory.PiDigits.T26.circleEmpiricalMean artificialCircleOrbit
                (fourier h) (sampledCheckpoint q) -
              ∑ a : Fin (10 ^ n),
                (((firstStartCount artificialStream (sampledCheckpoint q)
                  (decodedWord n a) : ℝ) / sampledCheckpoint q : ℝ) : ℂ) *
                  fourier h (decimalGridPoint n a)‖ +
            ‖∑ a : Fin (10 ^ n),
              (((firstStartCount artificialStream (sampledCheckpoint q)
                (decodedWord n a) : ℝ) / sampledCheckpoint q : ℝ) : ℂ) *
                fourier h (decimalGridPoint n a)‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            (Theory.PiDigits.T26.circleEmpiricalMean artificialCircleOrbit
              (fourier h) (sampledCheckpoint q) -
              ∑ a : Fin (10 ^ n),
                (((firstStartCount artificialStream (sampledCheckpoint q)
                  (decodedWord n a) : ℝ) / sampledCheckpoint q : ℝ) : ℂ) *
                  fourier h (decimalGridPoint n a))
            (∑ a : Fin (10 ^ n),
              (((firstStartCount artificialStream (sampledCheckpoint q)
                (decodedWord n a) : ℝ) / sampledCheckpoint q : ℝ) : ℂ) *
                fourier h (decimalGridPoint n a))
        _ < C + ε / 2 := add_lt_add_of_le_of_lt happrox hweightedq
        _ < ε := by linarith
    have hintegral (q : ℕ) :
        (∫ z, fourier h z
          ∂(artificialEmpiricalMeasure (sampledCheckpoint q) :
            Measure UnitAddCircle)) =
          Theory.PiDigits.T26.circleEmpiricalMean artificialCircleOrbit
            (fourier h) (sampledCheckpoint q) := by
      rw [artificialEmpiricalMeasure,
        integral_circleEmpiricalMeasure artificialCircleOrbit
          (sampledCheckpoint q) (sampledCheckpoint_pos q) (fourier h)]
      unfold Theory.PiDigits.T26.circleEmpiricalMean
      rw [Complex.real_smul]
      congr 1
      exact Complex.ofReal_inv _
    simpa only [hintegral] using hmean

/-- T37's exact core/error formulas force every shallow child to carry at
least one twentieth of its parent's actual count. -/
theorem one_twentieth_parent_le_child_of_shallow
    (q : ℕ) (w : Word) (z : Digit)
    (hw : w.length + 1 ≤ stageOrder q) :
    (1 / 20 : ℝ) *
        firstStartCount artificialStream (sampledCheckpoint q) w ≤
      firstStartCount artificialStream (sampledCheckpoint q) (w ++ [z]) := by
  have hparent := firstStartCount_sampledCheckpoint_eq_core_add_error q w
  have hchild := firstStartCount_sampledCheckpoint_eq_core_add_error q (w ++ [z])
  have hcore := ten_mul_stageCoreCount_child_eq_parent q w z hw
  have herror := stageErrorCount_le_budget q w
  have hbudget := stageErrorBudget_le_zeroSeedCoreSize q
  have hchildCore := zeroSeedCoreSize_le_shallowChildCoreCount q w z hw
  have hnat :
      firstStartCount artificialStream (sampledCheckpoint q) w ≤
        20 * firstStartCount artificialStream (sampledCheckpoint q) (w ++ [z]) := by
    omega
  have hreal :
      (firstStartCount artificialStream (sampledCheckpoint q) w : ℝ) ≤
        20 * firstStartCount artificialStream (sampledCheckpoint q) (w ++ [z]) := by
    exact_mod_cast hnat
  norm_num at ⊢
  linarith

/-- Every shallow parent in T37's sampled row is split by the two explicit
digits `0` and `1` at threshold `eta = 1/20`. -/
theorem artificialStream_splitParent_one_twentieth
    (q : ℕ) (w : Word) (hw : w.length + 1 ≤ stageOrder q) :
    StreamQuantitativelySplitParent artificialStream (sampledCheckpoint q)
      (1 / 20 : ℝ) w := by
  refine ⟨0, 1, by decide, ?_, ?_⟩
  · exact one_twentieth_parent_le_child_of_shallow q w 0 hw
  · exact one_twentieth_parent_le_child_of_shallow q w 1 hw

/-- Every shallow level carries all of its collision energy on split parents,
so it is a T14-style splitting level with `mu = 1/2`. -/
theorem artificialStream_splittingLevel_half_one_twentieth
    (q l : ℕ) (hl : l + 1 ≤ stageOrder q) :
    StreamQuantitativeSplittingLevel artificialStream l (sampledCheckpoint q)
      (1 / 2 : ℝ) (1 / 20 : ℝ) := by
  classical
  unfold StreamQuantitativeSplittingLevel streamCollisionEnergy
  have hsplit : ∀ a : Fin (10 ^ l),
      StreamQuantitativelySplitParent artificialStream (sampledCheckpoint q)
        (1 / 20 : ℝ) (decodedWord l a) := by
    intro a
    exact artificialStream_splitParent_one_twentieth q (decodedWord l a) (by
      simpa using hl)
  simp only [hsplit, if_true]
  have hnonneg : 0 ≤
      ∑ a : Fin (10 ^ l),
        (firstStartCount artificialStream (sampledCheckpoint q)
          (decodedWord l a) : ℝ) ^ 2 := by positivity
  linarith

/-- On every triangular entry `m ≤ k`, all levels `l < m` split. -/
theorem artificialStream_splittingLevelCount_eq
    (k m : ℕ) (hmk : m ≤ k) :
    streamSplittingLevelCount artificialStream m (sampledCheckpoint k)
      (1 / 2 : ℝ) (1 / 20 : ℝ) = m := by
  classical
  unfold streamSplittingLevelCount streamSplittingLevels
  rw [Finset.filter_eq_self.2]
  · exact Finset.card_range m
  · intro l hl
    rw [Finset.mem_range] at hl
    exact artificialStream_splittingLevel_half_one_twentieth k l (by
      unfold stageOrder
      omega)

/-- The fixed T49 witnesses satisfy every non-limit clause of the complete
coherent predicate, with the identity thinning of T37's sampled checkpoints. -/
theorem artificialStream_coherentSplitting_of_weakLimit
    (hweak : Tendsto
      (fun k => artificialEmpiricalMeasure (sampledCheckpoint k))
      atTop (𝓝 circleHaarProbability)) :
    StreamCoherentPositiveDensitySplittingAt
      artificialStream artificialEmpiricalMeasure
      (1 / 2 : ℝ) (1 / 20 : ℝ) 1 0 0 0 sampledCheckpoint
      circleHaarProbability := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, sampledCheckpoint_strictMono,
    sampledCheckpoint_pos, ?_, ?_⟩
  · simpa only using hweak
  · intro k _hk m _hm hmk
    rw [artificialStream_splittingLevelCount_eq k m hmk]
    norm_num

/-- Unconditional complete coherent splitting for T37's stream and identity
checkpoint thinning, with the accepted fixed parameters. -/
theorem artificialStream_complete_coherentSplitting :
    StreamCoherentPositiveDensitySplittingAt
      artificialStream artificialEmpiricalMeasure
      (1 / 2 : ℝ) (1 / 20 : ℝ) 1 0 0 0 sampledCheckpoint
      circleHaarProbability :=
  artificialStream_coherentSplitting_of_weakLimit
    artificialEmpiricalMeasure_tendsto_circleHaarProbability

/-- Expanded certificate: the stream, empirical weak limit, fixed constants,
identity checkpoints, triangular `m ≤ k` count, and every level `l < m` are
all visible in the theorem type. -/
theorem artificialStream_complete_coherentSplitting_explicit :
    Tendsto
        (fun k => artificialEmpiricalMeasure (sampledCheckpoint k))
        atTop (𝓝 circleHaarProbability) ∧
      StrictMono sampledCheckpoint ∧
      (∀ k, 0 < sampledCheckpoint k) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      (0 : ℝ) < 1 / 20 ∧ (1 / 20 : ℝ) ≤ 1 / 10 ∧
      (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 0 ∧
      (∀ k : ℕ, 0 ≤ k → ∀ m : ℕ, 0 ≤ m → m ≤ k →
        (1 : ℝ) * m - 0 ≤
          (streamSplittingLevelCount artificialStream m (sampledCheckpoint k)
            (1 / 2 : ℝ) (1 / 20 : ℝ) : ℝ)) ∧
      (∀ k m l : ℕ, m ≤ k → l < m →
        StreamQuantitativeSplittingLevel artificialStream l
          (sampledCheckpoint k) (1 / 2 : ℝ) (1 / 20 : ℝ)) := by
  refine ⟨artificialEmpiricalMeasure_tendsto_circleHaarProbability,
    sampledCheckpoint_strictMono, sampledCheckpoint_pos,
    by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_⟩
  · intro k _hk m _hm hmk
    rw [artificialStream_splittingLevelCount_eq k m hmk]
    norm_num
  · intro k m l hmk hlm
    exact artificialStream_splittingLevel_half_one_twentieth k l (by
      unfold stageOrder
      omega)

/-- T49's artificial sibling is a concrete countermodel to branch pullback:
complete coherent levelwise splitting coexists with failure of one fixed
original-coordinate eventually half-dominant branch. The negative conjunct is
T37's theorem verbatim and is not reproved here. -/
theorem coherentSplitting_does_not_imply_originalHalfDominantBranch :
    StreamCoherentPositiveDensitySplittingAt
        artificialStream artificialEmpiricalMeasure
        (1 / 2 : ℝ) (1 / 20 : ℝ) 1 0 0 0 sampledCheckpoint
        circleHaarProbability ∧
      ¬ ∃ root : Word, ∃ continuation : ℕ → Digit,
        ∀ i : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
          (1 / 2 : ℝ) *
                firstStartCount artificialStream (sampledCheckpoint q)
                  (root ++ DecimalFactorComplexity.MovingRootTangent.pathWord
                    continuation i) ≤
              firstStartCount artificialStream (sampledCheckpoint q)
                (root ++ DecimalFactorComplexity.MovingRootTangent.pathWord
                  continuation (i + 1)) ∧
            0 < (1 / 2 : ℝ) *
              firstStartCount artificialStream (sampledCheckpoint q)
                (root ++ DecimalFactorComplexity.MovingRootTangent.pathWord
                  continuation i) := by
  refine ⟨artificialStream_complete_coherentSplitting, ?_⟩
  exact no_original_halfDominant_branch_explicit

/-- Fully expanded sibling non-implication certificate. Its positive conjunct
exposes the weak limit and every triangular splitting level; its negative
conjunct is exactly T37's original-coordinate branch predicate. -/
theorem coherentSplitting_does_not_imply_originalHalfDominantBranch_explicit :
    (Tendsto
        (fun k => artificialEmpiricalMeasure (sampledCheckpoint k))
        atTop (𝓝 circleHaarProbability) ∧
      StrictMono sampledCheckpoint ∧
      (∀ k, 0 < sampledCheckpoint k) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      (0 : ℝ) < 1 / 20 ∧ (1 / 20 : ℝ) ≤ 1 / 10 ∧
      (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 0 ∧
      (∀ k : ℕ, 0 ≤ k → ∀ m : ℕ, 0 ≤ m → m ≤ k →
        (1 : ℝ) * m - 0 ≤
          (streamSplittingLevelCount artificialStream m (sampledCheckpoint k)
            (1 / 2 : ℝ) (1 / 20 : ℝ) : ℝ)) ∧
      (∀ k m l : ℕ, m ≤ k → l < m →
        StreamQuantitativeSplittingLevel artificialStream l
          (sampledCheckpoint k) (1 / 2 : ℝ) (1 / 20 : ℝ))) ∧
      ¬ ∃ root : Word, ∃ continuation : ℕ → Digit,
        ∀ i : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
          (1 / 2 : ℝ) *
                firstStartCount artificialStream (sampledCheckpoint q)
                  (root ++ DecimalFactorComplexity.MovingRootTangent.pathWord
                    continuation i) ≤
              firstStartCount artificialStream (sampledCheckpoint q)
                (root ++ DecimalFactorComplexity.MovingRootTangent.pathWord
                  continuation (i + 1)) ∧
            0 < (1 / 2 : ℝ) *
              firstStartCount artificialStream (sampledCheckpoint q)
                (root ++ DecimalFactorComplexity.MovingRootTangent.pathWord
                  continuation i) := by
  refine ⟨artificialStream_complete_coherentSplitting_explicit, ?_⟩
  exact no_original_halfDominant_branch_explicit

end DecimalFactorComplexity.ArtificialStreamCoherentSplittingT49

#print axioms DecimalFactorComplexity.ArtificialStreamCoherentSplittingT49.artificialEmpiricalMeasure_tendsto_circleHaarProbability
#print axioms DecimalFactorComplexity.ArtificialStreamCoherentSplittingT49.artificialStream_complete_coherentSplitting
#print axioms DecimalFactorComplexity.ArtificialStreamCoherentSplittingT49.artificialStream_complete_coherentSplitting_explicit
#print axioms DecimalFactorComplexity.ArtificialStreamCoherentSplittingT49.coherentSplitting_does_not_imply_originalHalfDominantBranch
#print axioms DecimalFactorComplexity.ArtificialStreamCoherentSplittingT49.coherentSplitting_does_not_imply_originalHalfDominantBranch_explicit
