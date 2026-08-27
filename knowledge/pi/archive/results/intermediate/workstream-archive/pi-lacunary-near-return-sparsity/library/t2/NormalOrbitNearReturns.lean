import TheoryLib.PiLacunaryNearReturnSparsity.T1LagDecomposition
import TheoryLib.PiPositiveLowerBlockDensity.T4T4BalancedNormalitySeparator
import TheoryLib.PiQuantitativeBlockHitting.T16T16DecimalBoundaryWordObstruction
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Normal decimal shift orbits have sparse near returns

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

T25 source statement: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file proves the every-`A`, eventually-every-`n`, exists-`N` estimate for
generic normal decimal streams and specializes it to T25's artificial
Champernowne stream.  Every count is over ordered pairs and includes the
diagonal.  This is a sibling result only: no theorem in this file concerns
`Real.pi` or proves the canonical fixed-pi question.
-/

noncomputable section

open Filter Finset Set Topology

namespace DecimalFactorComplexity.NormalOrbitNearReturns

open Theory.PiDigits.T20
open Theory.PiDigits.T22
open Theory.PiDigits.T23
open Theory.PiDigits.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T4

/-- The real represented by the decimal tail beginning at position `k`.
This is the symbolic base-ten shift orbit attached to a digit stream. -/
def tailOrbit (s : ℕ → Fin 10) (k : ℕ) : ℝ :=
  Real.ofDigits fun i => s (k + i)

/-- The length-`n` block beginning at `k`. -/
def prefixWord (s : ℕ → Fin 10) (n k : ℕ) : List (Fin 10) :=
  List.ofFn fun i : Fin n => s (k + i)

/-- The numerical label of the length-`n` block beginning at `k`. -/
def prefixLabel (s : ℕ → Fin 10) (n k : ℕ) : ℕ :=
  wordValue (prefixWord s n k)

theorem prefixLabel_lt (s : ℕ → Fin 10) (n k : ℕ) :
    prefixLabel s n k < 10 ^ n := by
  simpa [prefixLabel, prefixWord] using wordValue_lt_pow_length (prefixWord s n k)

/-- The finite prefix sum of a decimal tail is its integer block label divided
by `10^n`. -/
theorem prefixSum_eq_label_div (s : ℕ → Fin 10) (n k : ℕ) :
    (∑ i ∈ Finset.range n,
        Real.ofDigitsTerm (fun t => s (k + t)) i) =
      (prefixLabel s n k : ℝ) / (10 : ℝ) ^ n := by
  induction n with
  | zero => simp [Real.ofDigitsTerm, prefixLabel, prefixWord]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [prefixLabel, prefixWord]
    have happ : List.ofFn (fun i : Fin (n + 1) => s (k + i)) =
        (List.ofFn fun i : Fin n => s (k + i)) ++ [s (k + n)] := by
      rw [List.ofFn_succ_last]
      congr 1
    rw [happ]
    rw [Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_append,
      List.length_cons, List.length_nil, pow_one]
    simp only [wordValue, List.length_nil, pow_zero]
    push_cast
    ring_nf
    rw [Real.ofDigitsTerm, inv_pow, pow_add, pow_one]
    ring

/-- Every symbolic tail lies in the closed decimal cell selected by its first
`n` digits.  Closed cells safely cover the repeating-nine representation. -/
theorem tailOrbit_mem_closedCell (s : ℕ → Fin 10) (n k : ℕ) :
    tailOrbit s k ∈ Set.Icc
      ((prefixLabel s n k : ℝ) / (10 : ℝ) ^ n)
      (((prefixLabel s n k + 1 : ℕ) : ℝ) / (10 : ℝ) ^ n) := by
  rw [tailOrbit, Real.ofDigits_eq_sum_add_ofDigits (fun t => s (k + t)) n,
    prefixSum_eq_label_div]
  have htail0 : 0 ≤ Real.ofDigits (fun i => s (k + (i + n))) :=
    Real.ofDigits_nonneg _
  have htail1 : Real.ofDigits (fun i => s (k + (i + n))) ≤ 1 :=
    Real.ofDigits_le_one _
  have hpow : 0 < (10 : ℝ) ^ n := by positivity
  constructor
  · exact le_add_of_nonneg_right
      (mul_nonneg (inv_nonneg.mpr hpow.le) htail0)
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left htail1 (inv_nonneg.mpr hpow.le)]

/-- Ordered, diagonal-inclusive strict near-return pairs for a symbolic decimal
shift orbit. -/
def nearReturnPairs (s : ℕ → Fin 10) (n N : ℕ) : Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter fun ij =>
    circleDistance (tailOrbit s ij.2 - tailOrbit s ij.1) <
      ((10 : ℝ) ^ n)⁻¹

/-- Cardinality of the ordered, diagonal-inclusive near-return set. -/
def Q_stream (s : ℕ → Fin 10) (n N : ℕ) : ℕ :=
  (nearReturnPairs s n N).card

@[simp] theorem mem_nearReturnPairs_iff (s : ℕ → Fin 10) (n N : ℕ)
    (ij : Fin N × Fin N) :
    ij ∈ nearReturnPairs s n N ↔
      circleDistance (tailOrbit s ij.2 - tailOrbit s ij.1) <
        ((10 : ℝ) ^ n)⁻¹ := by
  classical
  simp [nearReturnPairs]

/-- Every diagonal pair is retained. -/
@[simp] theorem diagonal_mem_nearReturnPairs (s : ℕ → Fin 10) (n N : ℕ)
    (i : Fin N) : (i, i) ∈ nearReturnPairs s n N := by
  rw [mem_nearReturnPairs_iff]
  have hzero : circleDistance (0 : ℝ) ≤ 0 := by
    simpa using circleDistance_le_abs_sub_int (0 : ℝ) (0 : ℤ)
  have hpos : 0 < ((10 : ℝ) ^ n)⁻¹ := by positivity
  simpa using hzero.trans_lt hpos

/-- Circle distance is unchanged by subtracting an integer. -/
theorem circleDistance_sub_int (x : ℝ) (z : ℤ) :
    circleDistance (x - z) = circleDistance x := by
  unfold circleDistance
  apply congrArg sInf
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨z + w, ?_⟩
    push_cast
    congr 1
    ring
  · rintro ⟨w, rfl⟩
    refine ⟨w - z, ?_⟩
    push_cast
    congr 1
    ring

/-- For a nonnegative real, the symbolic tail of its floor-based decimal
digits is exactly its base-ten fractional-part orbit. -/
theorem tailOrbit_decimalDigit_eq_baseTenOrbit (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    tailOrbit (decimalDigit x) k = baseTenOrbit x k := by
  have hfun : (fun i => decimalDigit x (k + i)) =
      decimalDigit (baseTenOrbit x k) := by
    funext i
    exact (decimalDigit_baseTenOrbit x hx k i).symm
  rw [tailOrbit, hfun]
  exact Real.ofDigits_digits (by norm_num) (baseTenOrbit_mem_Ico x k)

/-- The stream count for the decimal digits of `x` is T1's existing generic
ordered, diagonal-inclusive power-difference count `Q_x`. -/
theorem Q_stream_decimalDigit_eq_Q_x (x : ℝ) (hx : 0 ≤ x) (n N : ℕ) :
    Q_stream (decimalDigit x) n N =
      DecimalFactorComplexity.LagDecomposition.Q_x x n N := by
  classical
  unfold Q_stream nearReturnPairs DecimalFactorComplexity.LagDecomposition.Q_x
  apply congrArg Finset.card
  ext ij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [tailOrbit_decimalDigit_eq_baseTenOrbit x hx,
    tailOrbit_decimalDigit_eq_baseTenOrbit x hx]
  let z : ℤ :=
    ⌊(10 : ℝ) ^ (ij.2 : ℕ) * x⌋ - ⌊(10 : ℝ) ^ (ij.1 : ℕ) * x⌋
  have hdifference :
      baseTenOrbit x ij.2 - baseTenOrbit x ij.1 =
        (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * x) - z := by
    dsimp [baseTenOrbit, z]
    rw [Int.cast_sub]
    simp only [Int.fract]
    ring
  rw [hdifference, circleDistance_sub_int]

/-- Two decimal cells are equal or cyclically adjacent. -/
def CyclicAdjacent (q a b : ℕ) : Prop :=
  b = a ∨ b + 1 = a ∨ a + 1 = b ∨
    (a = 0 ∧ b + 1 = q) ∨ (b = 0 ∧ a + 1 = q)

/-- Strict circle distance below one cell width forces equal or cyclically
adjacent cell labels.  Closed cells are allowed; strict distance excludes a
two-cell jump through a shared endpoint. -/
theorem circleDistance_lt_of_mem_closedCells
    {q a b : ℕ} {x y : ℝ} (hq : 0 < q) (ha : a < q) (hb : b < q)
    (hx : x ∈ Set.Icc ((a : ℝ) / q) (((a + 1 : ℕ) : ℝ) / q))
    (hy : y ∈ Set.Icc ((b : ℝ) / q) (((b + 1 : ℕ) : ℝ) / q))
    (hnear : circleDistance (x - y) < (q : ℝ)⁻¹) :
    CyclicAdjacent q a b := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwidth : (q : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hqR).2 (by exact_mod_cast hq)
  have hqinv : (q : ℝ) * (q : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hqR.ne'
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx0 : 0 ≤ x := by
    exact (div_nonneg (by positivity) hqR.le).trans hx.1
  have hy0 : 0 ≤ y := by
    exact (div_nonneg (by positivity) hqR.le).trans hy.1
  have hx1 : x ≤ 1 := by
    refine hx.2.trans ?_
    exact (div_le_one hqR).2 (by exact_mod_cast (Nat.succ_le_iff.mpr ha))
  have hy1 : y ≤ 1 := by
    refine hy.2.trans ?_
    exact (div_le_one hqR).2 (by exact_mod_cast (Nat.succ_le_iff.mpr hb))
  have hcirc :
      Theory.PiDigits.BoundaryRobustFejerDichotomy.circularDistance x y <
        (q : ℝ)⁻¹ := by
    simpa [circleDistance,
      Theory.PiDigits.BoundaryRobustFejerDichotomy.circularDistance] using hnear
  obtain ⟨z, hz⟩ :=
    (Theory.PiDigits.DecimalBoundaryWordObstruction.circularDistance_lt_iff_exists_int
      x y ((q : ℝ)⁻¹)).mp hcirc
  rw [abs_lt] at hz
  have hzloR : (-2 : ℝ) < (z : ℝ) := by linarith
  have hzhiR : (z : ℝ) < 2 := by linarith
  have hzlo : (-2 : ℤ) < z := by exact_mod_cast hzloR
  have hzhi : z < (2 : ℤ) := by exact_mod_cast hzhiR
  have hzcase : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  have hxa : (a : ℝ) ≤ q * x := by
    have := (div_le_iff₀ hqR).mp hx.1
    nlinarith
  have hxa1 : q * x ≤ (a + 1 : ℕ) := by
    have := (le_div_iff₀ hqR).mp hx.2
    push_cast at this ⊢
    nlinarith
  have hyb : (b : ℝ) ≤ q * y := by
    have := (div_le_iff₀ hqR).mp hy.1
    nlinarith
  have hyb1 : q * y ≤ (b + 1 : ℕ) := by
    have := (le_div_iff₀ hqR).mp hy.2
    push_cast at this ⊢
    nlinarith
  push_cast at hxa hxa1 hyb hyb1
  rcases hzcase with rfl | rfl | rfl
  · norm_num at hz
    have hmetric : (q : ℝ) * x - q * y + q < 1 := by
      calc
        (q : ℝ) * x - q * y + q = q * (x - y + 1) := by ring
        _ < q * (q : ℝ)⁻¹ := mul_lt_mul_of_pos_left hz.2 hqR
        _ = 1 := hqinv
    have hscaled : (q : ℝ) + a < b + 2 := by
      push_cast
      linarith
    have hscaledNat : q + a < b + 2 := by exact_mod_cast hscaled
    unfold CyclicAdjacent
    omega
  · norm_num at hz
    have hxy : (q : ℝ) * x - q * y < 1 := by
      calc
        (q : ℝ) * x - q * y = q * (x - y) := by ring
        _ < q * (q : ℝ)⁻¹ := mul_lt_mul_of_pos_left hz.2 hqR
        _ = 1 := hqinv
    have hyx : (q : ℝ) * y - q * x < 1 := by
      calc
        (q : ℝ) * y - q * x = -q * (x - y - (0 : ℝ)) := by ring
        _ < q * (q : ℝ)⁻¹ := by nlinarith [mul_lt_mul_of_pos_left hz.1 hqR]
        _ = 1 := hqinv
    have habR : (a : ℝ) < b + 2 := by
      push_cast
      linarith
    have hbaR : (b : ℝ) < a + 2 := by
      push_cast
      linarith
    have hab : a < b + 2 := by exact_mod_cast habR
    have hba : b < a + 2 := by exact_mod_cast hbaR
    unfold CyclicAdjacent
    omega
  · norm_num at hz
    have hmetric : (q : ℝ) * y - q * x + q < 1 := by
      calc
        (q : ℝ) * y - q * x + q = -q * (x - y - (1 : ℝ)) := by ring
        _ < q * (q : ℝ)⁻¹ := by nlinarith [mul_lt_mul_of_pos_left hz.1 hqR]
        _ = 1 := hqinv
    have hscaled : (q : ℝ) + b < a + 2 := by
      push_cast
      linarith
    have hscaledNat : q + b < a + 2 := by exact_mod_cast hscaled
    unfold CyclicAdjacent
    omega

/-- Metric near returns of symbolic tails are controlled by equal or adjacent
length-`n` decimal blocks. -/
theorem nearReturn_implies_prefixLabels_adjacent
    (s : ℕ → Fin 10) (n : ℕ) {i j : ℕ}
    (hnear : circleDistance (tailOrbit s j - tailOrbit s i) <
      ((10 : ℝ) ^ n)⁻¹) :
    CyclicAdjacent (10 ^ n) (prefixLabel s n i) (prefixLabel s n j) := by
  refine circleDistance_lt_of_mem_closedCells
    (q := 10 ^ n) (x := tailOrbit s i) (y := tailOrbit s j)
    (by positivity) (prefixLabel_lt s n i) (prefixLabel_lt s n j) ?_ ?_ ?_
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using tailOrbit_mem_closedCell s n i
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using tailOrbit_mem_closedCell s n j
  · rw [show tailOrbit s i - tailOrbit s j =
      -(tailOrbit s j - tailOrbit s i) by ring,
      DecimalFactorComplexity.LagDecomposition.circleDistance_neg]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnear

/-- Starts among the first `N` positions carrying decimal block label `a`. -/
def labelFiber (s : ℕ → Fin 10) (n N a : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun i => prefixLabel s n i = a

/-- At cutoff `N+n-1`, T25's contained-prefix count tests exactly the first
`N` starts.  This is the bridge from normality to the empirical fibers used in
the pair product count. -/
theorem labelFiber_card_eq_containedCount
    (s : ℕ → Fin 10) (n N a : ℕ) (hn : 1 ≤ n) (ha : a < 10 ^ n) :
    (labelFiber s n N a).card =
      finiteContiguousOccurrenceCount
        (Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a)
        (List.ofFn fun i : Fin (N + n - 1) => s i) := by
  classical
  have hstarts : N + n - 1 + 1 - n = N := by omega
  have hslice (i : ℕ) (hi : i < N) :
      ((List.ofFn fun t : Fin (N + n - 1) => s t).drop i).take n =
        prefixWord s n i := by
    have hlenLeft :
        (((List.ofFn fun t : Fin (N + n - 1) => s t).drop i).take n).length = n := by
      simp
      omega
    apply List.ext_getElem
    · simp [hlenLeft, prefixWord]
    · intro t htLeft htRight
      simp only [List.getElem_take, List.getElem_drop, prefixWord,
        List.getElem_ofFn]
  unfold labelFiber finiteContiguousOccurrenceCount
  rw [Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord_length ha,
    List.length_ofFn, hstarts]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨i.isLt, ?_⟩
    rw [hslice i i.isLt]
    symm
    apply Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord_eq_of_length_value ha
    · simp [prefixWord]
    · exact hi
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨⟨i, hi.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hword := hi.2
    rw [hslice i hi.1] at hword
    unfold prefixLabel
    rw [hword]
    exact Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord_value ha

/-- The finite empirical-product step.  If every decimal-block fiber has at
most `B` starts, each first coordinate can pair only with five displayed
fibers (three genuine cyclic neighbors, with separate wraparound bookkeeping).
Thus the ordered pair count, including its diagonal, is at most `5*B*N`. -/
theorem Q_stream_le_five_mul_of_labelFiber_le
    (s : ℕ → Fin 10) (n N B : ℕ)
    (hB : ∀ a : ℕ, (labelFiber s n N a).card ≤ B) :
    Q_stream s n N ≤ 5 * B * N := by
  classical
  let c : Fin N → ℕ := fun i => prefixLabel s n i
  let pairSet (f : ℕ → ℕ) : Finset (Fin N × Fin N) :=
    Finset.univ.filter fun ij => c ij.2 = f (c ij.1)
  have hsingle (f : ℕ → ℕ) : (pairSet f).card ≤ B * N := by
    have hpartition := Finset.card_eq_sum_card_fiberwise
      (s := pairSet f) (t := (Finset.univ : Finset (Fin N)))
      (f := Prod.fst) (by simp)
    rw [hpartition]
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin N)),
          ((pairSet f).filter fun ij => ij.1 = i).card ≤
          ∑ _i ∈ (Finset.univ : Finset (Fin N)), B := by
        apply Finset.sum_le_sum
        intro i hi
        have hcard :
            ((pairSet f).filter fun ij => ij.1 = i).card ≤
              (labelFiber s n N (f (c i))).card := by
          apply Finset.card_le_card_of_injOn Prod.snd
          · intro ij hij
            simp only [Finset.mem_coe, Finset.mem_filter, pairSet,
              Finset.mem_univ, true_and] at hij
            simp only [Finset.mem_coe, labelFiber, Finset.mem_filter,
              Finset.mem_univ, true_and]
            rcases hij with ⟨hpair, hfirst⟩
            simpa [c, hfirst] using hpair
          · intro x hx y hy hxy
            simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
            apply Prod.ext
            · exact hx.2.trans hy.2.symm
            · exact hxy
        exact hcard.trans (hB (f (c i)))
      _ = B * N := by simp [Nat.mul_comm]
  let S0 := pairSet id
  let S1 := pairSet fun a => a - 1
  let S2 := pairSet fun a => a + 1
  let S3 := pairSet fun _ => 10 ^ n - 1
  let S4 := pairSet fun _ => 0
  have hsubset : nearReturnPairs s n N ⊆ ((((S0 ∪ S1) ∪ S2) ∪ S3) ∪ S4) := by
    intro ij hij
    have hadj := nearReturn_implies_prefixLabels_adjacent s n
      (i := ij.1) (j := ij.2) ((mem_nearReturnPairs_iff s n N ij).mp hij)
    unfold CyclicAdjacent at hadj
    rcases hadj with h0 | h1 | h2 | h3 | h4
    · simp only [Finset.mem_union]
      left; left; left; left
      simp only [S0, pairSet, Finset.mem_filter, Finset.mem_univ, true_and, id_eq]
      simpa [c] using h0
    · simp only [Finset.mem_union]
      left; left; left; right
      simp only [S1, pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [c]
      omega
    · simp only [Finset.mem_union]
      left; left; right
      simp only [S2, pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [c] using h2.symm
    · simp only [Finset.mem_union]
      left; right
      simp only [S3, pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [c]
      omega
    · simp only [Finset.mem_union]
      right
      simp only [S4, pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [c] using h4.1
  have h0 : S0.card ≤ B * N := hsingle id
  have h1 : S1.card ≤ B * N := hsingle fun a => a - 1
  have h2 : S2.card ≤ B * N := hsingle fun a => a + 1
  have h3 : S3.card ≤ B * N := hsingle fun _ => 10 ^ n - 1
  have h4 : S4.card ≤ B * N := hsingle fun _ => 0
  have hu01 := Finset.card_union_le S0 S1
  have hu012 := Finset.card_union_le (S0 ∪ S1) S2
  have hu0123 := Finset.card_union_le ((S0 ∪ S1) ∪ S2) S3
  have hu01234 := Finset.card_union_le (((S0 ∪ S1) ∪ S2) ∪ S3) S4
  unfold Q_stream
  calc
    (nearReturnPairs s n N).card ≤ ((((S0 ∪ S1) ∪ S2) ∪ S3) ∪ S4).card :=
      Finset.card_le_card hsubset
    _ ≤ S0.card + S1.card + S2.card + S3.card + S4.card := by omega
    _ ≤ 5 * (B * N) := by omega
    _ = 5 * B * N := by ring

/-- Normality supplies a common cutoff, chosen as a multiple of `10^n`, at
which every one of the finitely many length-`n` block fibers has size at most
twice its uniform expectation. -/
theorem exists_uniform_labelFiber_bound_of_normality
    (s : ℕ → Fin 10) (hnormal : HasContainedPrefixBaseTenNormality s)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : ℕ, 2 * n ≤ 10 ^ n * M ∧
      ∀ a : ℕ,
        (labelFiber s n (10 ^ n * M + 1 - n) a).card ≤ 2 * M := by
  classical
  let q : ℕ := 10 ^ n
  have hq : 0 < q := by positivity
  have hqone : 1 ≤ q := hq
  have heach (a : Fin q) : ∃ K : ℕ, ∀ L : ℕ, K ≤ L →
      containedPrefixFrequency s
        (Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a) L <
          2 / (q : ℝ) := by
    have ha : (a : ℕ) < 10 ^ n := by simpa [q] using a.isLt
    have hwlen := Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord_length ha
    have hw : Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a ≠ [] := by
      intro hempty
      have := congrArg List.length hempty
      simp [hwlen] at this
      omega
    have ht := hnormal
      (Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a) hw
    have hlimit : (10 : ℝ) ^
        (-((Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a).length : ℤ)) =
          (q : ℝ)⁻¹ := by
      rw [hwlen]
      simp [q, zpow_neg]
    have hlt : (10 : ℝ) ^
        (-((Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a).length : ℤ)) <
          2 / (q : ℝ) := by
      rw [hlimit]
      rw [div_eq_mul_inv]
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      nlinarith [inv_pos.mpr hqR]
    have hev : ∀ᶠ L : ℕ in atTop,
        containedPrefixFrequency s
          (Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a) L <
            2 / (q : ℝ) :=
      ht.eventually (Iio_mem_nhds hlt)
    exact Filter.eventually_atTop.1 hev
  choose K hK using heach
  let M : ℕ := max (2 * n) (∑ a : Fin q, K a)
  have hMlarge : 2 * n ≤ q * M := by
    have hm : 2 * n ≤ M := le_max_left _ _
    exact hm.trans (Nat.le_mul_of_pos_left M hq)
  refine ⟨M, by simpa [q] using hMlarge, ?_⟩
  intro a
  by_cases ha : a < q
  · let af : Fin q := ⟨a, ha⟩
    have hKsum : K af ≤ ∑ b : Fin q, K b := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ af)
    have hKML : K af ≤ q * M := by
      have hKM : K af ≤ M := hKsum.trans (le_max_right _ _)
      exact hKM.trans (Nat.le_mul_of_pos_left M hq)
    have hfreq := hK af (q * M) hKML
    have hMpos : 0 < M := by
      have : 2 ≤ 2 * n := by omega
      exact lt_of_lt_of_le (by omega) (this.trans (le_max_left _ _))
    have hLpos : (0 : ℝ) < q * M := by positivity
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    unfold containedPrefixFrequency at hfreq
    norm_num only [Nat.cast_mul] at hfreq
    have hcountReal :
        (finiteContiguousOccurrenceCount
            (Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a)
            (List.ofFn fun i : Fin (q * M) => s i) : ℝ) ≤ 2 * M := by
      have hcross := (div_lt_div_iff₀ hLpos hqR).mp hfreq
      push_cast at hcross ⊢
      nlinarith
    have hcountNat :
        finiteContiguousOccurrenceCount
            (Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord n a)
            (List.ofFn fun i : Fin (q * M) => s i) ≤ 2 * M := by
      exact_mod_cast hcountReal
    have hcut : q * M + 1 - n + n - 1 = q * M := by omega
    rw [labelFiber_card_eq_containedCount s n (q * M + 1 - n) a hn
      (by simpa [q] using ha), hcut]
    exact hcountNat
  · have hempty : labelFiber s n (10 ^ n * M + 1 - n) a = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [labelFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hlt := prefixLabel_lt s n i
      rw [hi] at hlt
      exact ha (by simpa [q] using hlt)
    rw [hempty]
    simp

/-- Exponential decay eventually absorbs every fixed multiple of `n`. -/
theorem eventually_twenty_mul_le_ten_pow (A : ℕ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → 20 * A * n ≤ 10 ^ n := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1
    (by norm_num : (1 : ℝ) < 10)
  have hscaled : Tendsto
      (fun n : ℕ => (20 * A : ℝ) * ((n : ℝ) ^ 1 / (10 : ℝ) ^ n))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ht)
  have hev : ∀ᶠ n : ℕ in atTop,
      (20 * A : ℝ) * ((n : ℝ) ^ 1 / (10 : ℝ) ^ n) < 1 :=
    (tendsto_order.1 hscaled).2 1 (by norm_num)
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  have hnm : m ≤ n := (le_max_right 1 m).trans hn
  have hratio := hm n hnm
  have hpowR : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hreal : (20 * A * n : ℕ) < (10 : ℝ) ^ n := by
    have hratio' : ((20 * A * n : ℕ) : ℝ) / (10 : ℝ) ^ n < 1 := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      simpa [pow_one, div_eq_mul_inv, mul_assoc] using hratio
    exact (div_lt_one hpowR).mp hratio'
  exact Nat.le_of_lt (by exact_mod_cast hreal)

/-- Base-10 normality of a generic symbolic shift orbit implies the canonical
quantifier pattern for its ordered, diagonal-inclusive near-return count. -/
theorem normality_implies_nearReturn_estimate
    (s : ℕ → Fin 10) (hnormal : HasContainedPrefixBaseTenNormality s) :
    ∀ A : ℕ, 1 ≤ A → ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_stream s n N ≤ N ^ 2 := by
  intro A hA
  obtain ⟨n₀, hn₀, hscale⟩ := eventually_twenty_mul_le_ten_pow A
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := hn₀.trans hn
  obtain ⟨M, hMscale, hfiber⟩ :=
    exists_uniform_labelFiber_bound_of_normality s hnormal n hn1
  let q : ℕ := 10 ^ n
  let N : ℕ := q * M + 1 - n
  have hq : 0 < q := by positivity
  have hMpos : 0 < M := by
    by_contra hnot
    have hMzero : M = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hMzero, Nat.mul_zero] at hMscale
    omega
  have hN : 1 ≤ N := by
    dsimp [N, q]
    omega
  have hQ : Q_stream s n N ≤ 5 * (2 * M) * N := by
    apply Q_stream_le_five_mul_of_labelFiber_le
    intro a
    simpa [N, q] using hfiber a
  have hqscale : 20 * A * n ≤ q := by
    simpa [q] using hscale n hn
  have hmul : (20 * A * n) * M ≤ q * M :=
    Nat.mul_le_mul_right M hqscale
  have hnsmall : n ≤ (10 * A * n) * M := by
    calc
      n = 1 * 1 * n * 1 := by ring
      _ ≤ 10 * A * n * M := by
        gcongr
        all_goals omega
  have hdouble : 2 * ((10 * A * n) * M) ≤ q * M := by
    calc
      2 * ((10 * A * n) * M) = (20 * A * n) * M := by ring
      _ ≤ q * M := hmul
  have hsum : (10 * A * n) * M + n ≤ q * M := by
    calc
      (10 * A * n) * M + n ≤
          (10 * A * n) * M + (10 * A * n) * M :=
        Nat.add_le_add_left hnsmall _
      _ = 2 * ((10 * A * n) * M) := by ring
      _ ≤ q * M := hdouble
  have htarget : (10 * A * n) * M ≤ N := by
    dsimp [N]
    omega
  refine ⟨N, hN, ?_⟩
  calc
    A * n * Q_stream s n N ≤ A * n * (5 * (2 * M) * N) :=
      Nat.mul_le_mul_left (A * n) hQ
    _ = ((10 * A * n) * M) * N := by ring
    _ ≤ N * N := Nat.mul_le_mul_right N htarget
    _ = N ^ 2 := by ring

/-- Direct generic-real formulation using T1's canonical `Q_x`: normality of
the floor-based decimal orbit of a nonnegative real implies the estimate. -/
theorem normal_decimalOrbit_implies_Q_x_estimate
    (x : ℝ) (hx : 0 ≤ x)
    (hnormal : HasContainedPrefixBaseTenNormality (decimalDigit x)) :
    ∀ A : ℕ, 1 ≤ A → ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * DecimalFactorComplexity.LagDecomposition.Q_x x n N ≤ N ^ 2 := by
  simpa only [Q_stream_decimalDigit_eq_Q_x x hx] using
    normality_implies_nearReturn_estimate (decimalDigit x) hnormal

/-- T25 is exactly the contained-prefix normality predicate used above. -/
theorem champernowne_hasContainedPrefixBaseTenNormality :
    HasContainedPrefixBaseTenNormality champernowneDigit := by
  intro w hw
  simpa [containedPrefixFrequency, Theory.PiDigits.T25.blockFrequency,
    Theory.PiDigits.T25.streamPrefix] using
      champernowne_full_baseTen_normality w hw

/-- The solved Champernowne sibling with the exact every-`A`,
eventually-every-`n`, exists-`N` quantifiers.  `Q_stream` counts ordered pairs
and includes every diagonal pair.  This theorem makes no claim about pi. -/
theorem champernowne_nearReturn_estimate :
    ∀ A : ℕ, 1 ≤ A → ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_stream champernowneDigit n N ≤ N ^ 2 :=
  normality_implies_nearReturn_estimate champernowneDigit
    champernowne_hasContainedPrefixBaseTenNormality

#print axioms Q_stream_le_five_mul_of_labelFiber_le
#print axioms normality_implies_nearReturn_estimate
#print axioms normal_decimalOrbit_implies_Q_x_estimate
#print axioms champernowne_nearReturn_estimate

end DecimalFactorComplexity.NormalOrbitNearReturns
