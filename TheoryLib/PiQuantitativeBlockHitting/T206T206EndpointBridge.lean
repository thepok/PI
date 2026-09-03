import TheoryLib.PiDigits.T20BaseTenOrbitDensity
import TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore
import TheoryLib.PiPositiveDecimalFactorEntropy.T48T48EndpointCarryKMP
import TheoryLib.PiPositiveLowerBlockDensity.T22T22DecimalBoundaryAmbiguity

/-!
# T206: greedy/existential endpoint bridge

produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-03 (wave E2, one task per lemma), against the contracted signatures of
AllMath task pack t206; gate-checked per task; assembled by Codex
-/

noncomputable section
open scoped symmDiff
namespace Theory.PiDigits.T206EndpointBridge

abbrev DecimalStream :=
  DecimalFactorEntropy.T44EndpointSafeInvariantCore.DecimalStream

def greedyStream (x : ℝ) : DecimalStream :=
  fun n => Theory.PiDigits.T20.decimalDigit x n

def CWord (w : List (Fin 10)) : Set ℝ :=
  {x | x ∈ Set.Ico (0 : ℝ) 1 ∧
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord
      w (greedyStream x)}

def KWordReal (w : List (Fin 10)) : Set ℝ :=
  {x | x ∈ Set.Ico (0 : ℝ) 1 ∧
    (x : UnitAddCircle) ∈
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.KWord w}

def E10 : Set ℝ :=
  {x | ∃ m : ℤ, ∃ k : ℕ,
    x = (m : ℝ) / (10 : ℝ) ^ k}

theorem circleValue_greedyStream
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
      (greedyStream x) = (x : UnitAddCircle) := by
  have hreal : Real.ofDigits (greedyStream x) = x :=
    Real.ofDigits_digits (by norm_num) hx
  have hdef : DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
      (greedyStream x) = ((Real.ofDigits (greedyStream x) : ℝ) : UnitAddCircle) :=
    rfl
  rw [hdef, hreal]

theorem nonGreedy_avoiding_expansion_implies_E10
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    {a : DecimalStream} {w : List (Fin 10)}
    (ha : DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord w a)
    (hval :
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a =
        (x : UnitAddCircle))
    (hne : a ≠ greedyStream x) :
    x ∈ E10 := by
  -- The avoidance hypothesis is part of the contracted interface; retain it.
  have _ha_use := ha
  -- Real value of the fixed greedy expansion.
  have hgval : Real.ofDigits (greedyStream x) = x := by
    have h := Real.ofDigits_digits (b := 10) (by norm_num) hx
    simpa [greedyStream, Theory.PiDigits.T20.decimalDigit] using h
  -- Circle equality as real coercions.
  have hcirc : ((Real.ofDigits a : ℝ) : UnitAddCircle) = ((x : ℝ) : UnitAddCircle) :=
    hval
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_of_lt hx.2⟩
  have hAIcc : Real.ofDigits a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.ofDigits_nonneg a, Real.ofDigits_le_one a⟩
  have hend :=
    (Theory.Shared.DigitAutomata.T13.unitAddCircle_eq_iff_endpointEq hAIcc hxIcc).mp
      hcirc
  rw [Theory.Shared.DigitAutomata.T13.endpointEq] at hend
  rcases hend with hEq | ⟨hA0, hx1eq⟩ | ⟨hA1, hx0eq⟩
  · -- Main case: equal real values with distinct expansions.
    have hab : Real.ofDigits a = Real.ofDigits (greedyStream x) :=
      hEq.trans hgval.symm
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hne
    let m := n + 1
    have hABle :=
      DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode_le_add_one_of_realValue_eq
        a (greedyStream x) m hab
    have hBAle :=
      DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode_le_add_one_of_realValue_eq
        (greedyStream x) a m hab.symm
    have hfunNe :
        (fun i : Fin m => a i.val) ≠
          (fun i : Fin m => (greedyStream x) i.val) := by
      intro hcon
      apply hn
      have hmem : n < m := by simp [m]
      have h := congrFun hcon (⟨n, hmem⟩ : Fin m)
      simpa using h
    have hcodeNe :
        DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m ≠
          DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m := by
      intro hcon
      apply hfunNe
      have hcon' :
          Theory.Shared.DigitAutomata.T13.blockCode (fun i : Fin m => a i.val) =
            Theory.Shared.DigitAutomata.T13.blockCode
              (fun i : Fin m => (greedyStream x) i.val) := hcon
      exact Theory.Shared.DigitAutomata.T13.blockCode_injective 10 m hcon'
    have hvalNe :
        (DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val ≠
          (DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val := by
      intro hcon
      apply hcodeNe
      exact Fin.ext hcon
    have hAdj :
        (DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val + 1 =
            (DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val ∨
          (DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val + 1 =
            (DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val := by
      omega
    -- Closed cylinders for both expansions.
    have hcylA_raw :=
      Theory.Shared.DigitAutomata.T13.ofDigits_mem_cylinder 10 m (by omega) a
    have hcylG_raw :=
      Theory.Shared.DigitAutomata.T13.ofDigits_mem_cylinder 10 m (by omega)
        (greedyStream x)
    have hcylA_low :
        ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) /
            (10 : ℝ) ^ m ≤
          Real.ofDigits a := hcylA_raw.1
    have hcylA_up :
        Real.ofDigits a ≤
          (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) + 1) /
            (10 : ℝ) ^ m := by
      simpa [DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode] using hcylA_raw.2
    have hcylG_low :
        ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) /
            (10 : ℝ) ^ m ≤
          Real.ofDigits (greedyStream x) := hcylG_raw.1
    have hcylG_up :
        Real.ofDigits (greedyStream x) ≤
          (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) + 1) /
            (10 : ℝ) ^ m := by
      simpa [DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode] using hcylG_raw.2
    -- Transfer bounds to `x` (forward rewrites only touch the value, not the code).
    have hx_lowA :
        ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) /
            (10 : ℝ) ^ m ≤ x := by
      have h := hcylA_low
      rwa [hEq] at h
    have hx_upA :
        x ≤
          (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) + 1) /
            (10 : ℝ) ^ m := by
      have h := hcylA_up
      rwa [hEq] at h
    have hx_lowG :
        ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) /
            (10 : ℝ) ^ m ≤ x := by
      have h := hcylG_low
      rwa [hgval] at h
    have hx_upG :
        x ≤
          (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) + 1) /
            (10 : ℝ) ^ m := by
      have h := hcylG_up
      rwa [hgval] at h
    rcases hAdj with hAdj | hAdj
    · -- `a`-cylinder lies left, `x` is its right endpoint.
      have hxEq :
          x =
            ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) /
              (10 : ℝ) ^ m := by
        apply le_antisymm
        · have : x ≤
              (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) + 1) /
                (10 : ℝ) ^ m := hx_upA
          have hcast : (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) + 1) =
              ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) := by
            exact_mod_cast hAdj
          rw [hcast] at this
          exact this
        · exact hx_lowG
      show x ∈ E10
      refine ⟨((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℤ), m, ?_⟩
      push_cast
      exact hxEq
    · -- `greedy`-cylinder lies left, `x` is its right endpoint.
      have hxEq :
          x =
            ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) /
              (10 : ℝ) ^ m := by
        apply le_antisymm
        · have : x ≤
              (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) + 1) /
                (10 : ℝ) ^ m := hx_upG
          have hcast : (((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode (greedyStream x) m).val : ℝ) + 1) =
              ((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℝ) := by
            exact_mod_cast hAdj
          rw [hcast] at this
          exact this
        · exact hx_lowA
      show x ∈ E10
      refine ⟨((DecimalFactorEntropy.T48EndpointCarryKMP.prefixCode a m).val : ℤ), m, ?_⟩
      push_cast
      exact hxEq
  · -- `Real.ofDigits a = 0`, `x = 1`: impossible on `[0,1)`.
    have hlt := hx.2
    rw [hx1eq] at hlt
    exact absurd hlt (lt_irrefl (1 : ℝ))
  · -- `Real.ofDigits a = 1`, `x = 0`: zero is a power-of-ten rational.
    subst hx0eq
    show (0 : ℝ) ∈ E10
    exact ⟨0, 0, by simp⟩

namespace HypothesisForms

theorem CWord_subset_KWordReal
    (hCircle : ∀ {x : ℝ}, x ∈ Set.Ico (0 : ℝ) 1 →
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue
        (greedyStream x) = (x : UnitAddCircle))
    (w : List (Fin 10)) :
    CWord w ⊆ KWordReal w := by
  intro x hx
  obtain ⟨hxIco, hxAvoid⟩ := hx
  refine ⟨hxIco, ?_⟩
  exact (DecimalFactorEntropy.T44EndpointSafeInvariantCore.mem_KWord_iff_exists_avoiding_expansion
    w (x : UnitAddCircle)).mpr ⟨greedyStream x, hxAvoid, hCircle hxIco⟩

theorem KWordReal_diff_CWord_subset_E10
    (hNonGreedy : ∀ {x : ℝ}, x ∈ Set.Ico (0 : ℝ) 1 →
      ∀ {a : DecimalStream} {w : List (Fin 10)},
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord w a →
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.circleValue a =
          (x : UnitAddCircle) →
        a ≠ greedyStream x → x ∈ E10)
    (w : List (Fin 10)) :
    KWordReal w \ CWord w ⊆ E10 := by
  intro x hx
  obtain ⟨hK, hNotC⟩ := hx
  have hKmem : x ∈ Set.Ico (0 : ℝ) 1 ∧
      (x : UnitAddCircle) ∈
        DecimalFactorEntropy.T44EndpointSafeInvariantCore.KWord w := hK
  obtain ⟨hxIco, hxK⟩ := hKmem
  obtain ⟨a, haAvoid, haEq⟩ :=
    (DecimalFactorEntropy.T44EndpointSafeInvariantCore.mem_KWord_iff_exists_avoiding_expansion
      w (x : UnitAddCircle)).mp hxK
  have hne : a ≠ greedyStream x := by
    intro heq
    apply hNotC
    show x ∈ Set.Ico (0 : ℝ) 1 ∧
      DecimalFactorEntropy.T44EndpointSafeInvariantCore.AvoidsWord w (greedyStream x)
    exact ⟨hxIco, heq ▸ haAvoid⟩
  exact hNonGreedy hxIco haAvoid haEq hne

theorem CWord_symmDiff_KWordReal_subset_E10
    (hSubset : ∀ w : List (Fin 10), CWord w ⊆ KWordReal w)
    (hDiff : ∀ w : List (Fin 10), KWordReal w \ CWord w ⊆ E10)
    (w : List (Fin 10)) :
    CWord w ∆ KWordReal w ⊆ E10 := by
  intro x hx
  rw [Set.mem_symmDiff] at hx
  rcases hx with ⟨hC, hNK⟩ | ⟨hK, hNC⟩
  · exact absurd (hSubset w hC) hNK
  · exact hDiff w ⟨hK, hNC⟩

end HypothesisForms

theorem CWord_subset_KWordReal (w : List (Fin 10)) :
    CWord w ⊆ KWordReal w :=
  HypothesisForms.CWord_subset_KWordReal circleValue_greedyStream w

theorem KWordReal_diff_CWord_subset_E10 (w : List (Fin 10)) :
    KWordReal w \ CWord w ⊆ E10 :=
  HypothesisForms.KWordReal_diff_CWord_subset_E10
    nonGreedy_avoiding_expansion_implies_E10 w

theorem CWord_symmDiff_KWordReal_subset_E10 (w : List (Fin 10)) :
    CWord w ∆ KWordReal w ⊆ E10 :=
  HypothesisForms.CWord_symmDiff_KWordReal_subset_E10
    CWord_subset_KWordReal KWordReal_diff_CWord_subset_E10 w

end Theory.PiDigits.T206EndpointBridge
