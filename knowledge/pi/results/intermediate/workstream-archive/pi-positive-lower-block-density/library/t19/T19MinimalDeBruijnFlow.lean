import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiPositiveLowerBlockDensity.T6T6FixedFrequencyLowerDensityObstruction
import Mathlib.Topology.Sequences

/-!
# T19: minimal deficient length and a stationary de Bruijn flow

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

Every conclusion about pi in this module is necessary-only: it is conditional
on the literal negation of canonical C1.  No assertion that C1 fails is made.
-/

noncomputable section

open Filter Finset Set Topology

namespace Theory.PiDigits.PositiveLowerBlockDensity.T19

open Theory.PiDigits.PositiveLowerBlockDensity

/-- Decimal words represented as fixed-length tuples. -/
abbrev DecimalWord (k : ℕ) := Fin k → Fin 10

/-- The empirical vector containing every length-`k` block frequency. -/
def frequencyVector (s : ℕ → Fin 10) (k N : ℕ) : DecimalWord k → ℝ :=
  fun u => blockFrequency s (List.ofFn u) N

/-- Literal zero lower frequency at a positive block length. -/
def IsDeficientLength (s : ℕ → Fin 10) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ w : DecimalWord k,
    liminf (blockFrequency s (List.ofFn w)) atTop = 0

/-- Literal failure of canonical C1 gives a positive deficient length. -/
theorem literal_not_C1_exists_deficientLength
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ k : ℕ, IsDeficientLength Theory.PiDigits.piDigit k := by
  have hnotExplicit : ¬ ∀ k : ℕ, 1 ≤ k → ∀ w : DecimalWord k,
      0 < liminf
        (blockFrequency Theory.PiDigits.piDigit (List.ofFn w)) atTop := by
    intro h
    exact hnot (piPositiveLowerBlockDensity_iff_A1_quantifiers.mpr h)
  push Not at hnotExplicit
  obtain ⟨k, hk, w, hw⟩ := hnotExplicit
  let f := blockFrequency Theory.PiDigits.piDigit (List.ofFn w)
  have hfnonneg : ∀ N, 0 ≤ f N :=
    blockFrequency_nonneg Theory.PiDigits.piDigit (List.ofFn w)
  have hfle : ∀ N, f N ≤ 1 :=
    blockFrequency_le_one Theory.PiDigits.piDigit (List.ofFn w)
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·) f :=
    Filter.isCoboundedUnder_ge_of_le atTop hfle
  have hliminf_nonneg : 0 ≤ liminf f atTop :=
    le_liminf_of_le hcobounded (Filter.Eventually.of_forall hfnonneg)
  refine ⟨k, hk, w, le_antisymm hw hliminf_nonneg⟩

/-- The least positive deficient length, its deficient word, and positivity of
every lower frequency at every nonempty shorter length. -/
theorem exists_least_deficient_length
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ k : ℕ, 1 ≤ k ∧
      (∃ w : DecimalWord k,
        liminf (blockFrequency Theory.PiDigits.piDigit (List.ofFn w)) atTop = 0) ∧
      ∀ ell : ℕ, 1 ≤ ell → ell < k → ∀ u : DecimalWord ell,
        0 < liminf
          (blockFrequency Theory.PiDigits.piDigit (List.ofFn u)) atTop := by
  classical
  have hexists := literal_not_C1_exists_deficientLength hnot
  let k := Nat.find hexists
  have hk : IsDeficientLength Theory.PiDigits.piDigit k := Nat.find_spec hexists
  refine ⟨k, hk.1, hk.2, ?_⟩
  intro ell hell hellk u
  have hnotDef : ¬ IsDeficientLength Theory.PiDigits.piDigit ell := by
    intro hdef
    exact (not_le_of_gt hellk) (Nat.find_min' hexists hdef)
  let f := blockFrequency Theory.PiDigits.piDigit (List.ofFn u)
  have hfnonneg : ∀ N, 0 ≤ f N :=
    blockFrequency_nonneg Theory.PiDigits.piDigit (List.ofFn u)
  have hfle : ∀ N, f N ≤ 1 :=
    blockFrequency_le_one Theory.PiDigits.piDigit (List.ofFn u)
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·) f :=
    Filter.isCoboundedUnder_ge_of_le atTop hfle
  have hliminf_nonneg : 0 ≤ liminf f atTop :=
    le_liminf_of_le hcobounded (Filter.Eventually.of_forall hfnonneg)
  apply lt_of_le_of_ne hliminf_nonneg
  intro hzero
  apply hnotDef
  exact ⟨hell, u, hzero.symm⟩

/-- Finite positive liminfs have one positive eventual lower bound, uniform
in the finite index. -/
theorem finite_uniform_lower_bound
    {ι : Type*} [Fintype ι] (f : ι → ℕ → ℝ)
    (hnonneg : ∀ i N, 0 ≤ f i N)
    (hpos : ∀ i, 0 < liminf (f i) atTop) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ N : ℕ in atTop, ∀ i : ι, delta ≤ f i N := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image fun i : ι => liminf (f i) atTop)
  have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  let m : ℝ := S.min' hSne
  have hmpos : 0 < m := by
    have hmS : m ∈ S := S.min'_mem hSne
    rcases (Finset.mem_insert.mp hmS) with hm | hm
    · rw [hm]
      norm_num
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
      rw [← hi]
      exact hpos i
  let delta := m / 2
  have hdelta : 0 < delta := div_pos hmpos (by norm_num)
  refine ⟨delta, hdelta, eventually_all.mpr ?_⟩
  intro i
  have hmi : m ≤ liminf (f i) atTop := by
    apply S.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  have hdeltalt : delta < liminf (f i) atTop := by
    have : delta < m := by
      dsimp [delta]
      linarith
    exact this.trans_le hmi
  have hb : atTop.IsBoundedUnder (· ≥ ·) (f i) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (hnonneg i))
  exact (eventually_lt_of_lt_liminf hdeltalt hb).mono fun _ h => h.le

/-- The finite type of all nonempty words whose lengths are strictly below
`k`. It is empty exactly when `k = 1`. -/
abbrev NonemptyShortWord (k : ℕ) :=
  Σ ell : {ell : Fin k // 1 ≤ ell.val}, DecimalWord ell.val

/-- Minimality at `k` gives one positive delta and one common eventual range
which work for every nonempty word of every shorter length. -/
theorem least_length_uniform_shorter_delta
    (k : ℕ)
    (hshort : ∀ ell : ℕ, 1 ≤ ell → ell < k → ∀ u : DecimalWord ell,
      0 < liminf
        (blockFrequency Theory.PiDigits.piDigit (List.ofFn u)) atTop) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ N : ℕ in atTop, ∀ ell : ℕ, 1 ≤ ell → ell < k →
        ∀ u : DecimalWord ell,
          delta ≤ blockFrequency Theory.PiDigits.piDigit (List.ofFn u) N := by
  let f : NonemptyShortWord k → ℕ → ℝ := fun x N =>
    blockFrequency Theory.PiDigits.piDigit (List.ofFn x.2) N
  have hnonneg : ∀ x N, 0 ≤ f x N := by
    intro x N
    exact blockFrequency_nonneg Theory.PiDigits.piDigit (List.ofFn x.2) N
  have hpos : ∀ x, 0 < liminf (f x) atTop := by
    intro x
    exact hshort x.1.val x.1.2 x.1.val.isLt x.2
  obtain ⟨delta, hdelta, hevent⟩ :=
    finite_uniform_lower_bound f hnonneg hpos
  refine ⟨delta, hdelta, hevent.mono ?_⟩
  intro N hN ell hell hellk u
  exact hN ⟨⟨⟨ell, hellk⟩, hell⟩, u⟩

/-- A zero lower frequency has strictly increasing cutoffs along which the
frequency tends to zero. -/
theorem zero_liminf_strictlyIncreasing_cutoffs
    (s : ℕ → Fin 10) (w : List (Fin 10))
    (hzero : liminf (blockFrequency s w) atTop = 0) :
    ∃ cutoffs : ℕ → ℕ, StrictMono cutoffs ∧
      Tendsto (fun j => blockFrequency s w (cutoffs j)) atTop (nhds 0) := by
  let f := blockFrequency s w
  have hfle : ∀ N, f N ≤ 1 := blockFrequency_le_one s w
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·) f :=
    Filter.isCoboundedUnder_ge_of_le atTop hfle
  have hfrequent : ∀ j : ℕ, ∃ᶠ N : ℕ in atTop,
      f N < 1 / ((j + 1 : ℕ) : ℝ) := by
    intro j
    apply frequently_lt_of_liminf_lt hcobounded
    rw [hzero]
    positivity
  obtain ⟨cutoffs, hmono, hbound⟩ :=
    Filter.extraction_forall_of_frequently hfrequent
  refine ⟨cutoffs, hmono, ?_⟩
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun j => blockFrequency_nonneg s w _
  · exact Filter.Eventually.of_forall fun j => (hbound j).le
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (nhds 0))

/-- All coordinates of an empirical frequency vector lie in `[0,1]`. -/
def boundedFrequencyVector (s : ℕ → Fin 10) (k N : ℕ) :
    DecimalWord k → Set.Icc (0 : ℝ) 1 :=
  fun u => ⟨frequencyVector s k N u,
    blockFrequency_nonneg s (List.ofFn u) N,
    blockFrequency_le_one s (List.ofFn u) N⟩

/-- Finite-vector compactness: along a further strictly increasing
subsequence, every length-`k` frequency coordinate converges. -/
theorem exists_frequencyVector_convergent_subsequence
    (s : ℕ → Fin 10) (k : ℕ) (cutoffs : ℕ → ℕ) :
    ∃ limit : DecimalWord k → ℝ, ∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧
      (∀ u, 0 ≤ limit u ∧ limit u ≤ 1) ∧
      ∀ u, Tendsto
        (fun j => frequencyVector s k (cutoffs (subseq j)) u)
        atTop (nhds (limit u)) := by
  obtain ⟨q, subseq, hmono, hlim⟩ :=
    CompactSpace.tendsto_subseq (fun j => boundedFrequencyVector s k (cutoffs j))
  refine ⟨fun u => (q u).1, subseq, hmono, ?_, ?_⟩
  · intro u
    exact (q u).2
  · intro u
    have hcoord := (tendsto_pi_nhds.mp hlim) u
    have hval := (continuous_subtype_val.tendsto (q u)).comp hcoord
    simpa [boundedFrequencyVector, frequencyVector, Function.comp_def] using hval

/-- The length-`k` word seen at stream position `n`. -/
def wordAt (s : ℕ → Fin 10) (n k : ℕ) : DecimalWord k :=
  fun i => s (n + i.val)

/-- Tuple-facing description of T1's list-based block count. -/
theorem blockCount_ofFn_eq_filter
    (s : ℕ → Fin 10) {k : ℕ} (u : DecimalWord k) (N : ℕ) :
    blockCount s (List.ofFn u) N =
      ((Finset.univ : Finset (Fin N)).filter
        fun n => wordAt s n.val k = u).card := by
  unfold blockCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    funext i
    simpa [wordAt] using h (Fin.cast (by simp) i)
  · intro h i
    simpa [wordAt] using congrFun h (Fin.cast (by simp) i)

/-- Every start contributes to exactly one length-`k` block. -/
theorem sum_blockCount_all_words
    (s : ℕ → Fin 10) (k N : ℕ) :
    ∑ u : DecimalWord k, blockCount s (List.ofFn u) N = N := by
  classical
  let f : Fin N → DecimalWord k := fun n => wordAt s n.val k
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin N)))
    (t := (Finset.univ : Finset (DecimalWord k)))
    (f := f) (by simp)
  calc
    ∑ u : DecimalWord k, blockCount s (List.ofFn u) N =
        ∑ u : DecimalWord k,
          ((Finset.univ : Finset (Fin N)).filter fun n => f n = u).card := by
      apply Finset.sum_congr rfl
      intro u _
      exact blockCount_ofFn_eq_filter s u N
    _ = (Finset.univ : Finset (Fin N)).card := by
      simpa using hfiber.symm
    _ = N := by simp

/-- The complete empirical frequency vector is normalized at positive
cutoffs. -/
theorem sum_frequencyVector_eq_one
    (s : ℕ → Fin 10) (k N : ℕ) (hN : 0 < N) :
    ∑ u : DecimalWord k, frequencyVector s k N u = 1 := by
  unfold frequencyVector blockFrequency
  simp only [← Finset.sum_div]
  rw [← Nat.cast_sum, sum_blockCount_all_words]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hN))

@[simp] theorem wordAt_snoc
    (s : ℕ → Fin 10) (n ell : ℕ) :
    wordAt s n (ell + 1) =
      Fin.snoc (wordAt s n ell) (s (n + ell)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [wordAt]
  · simp [wordAt]

@[simp] theorem wordAt_cons
    (s : ℕ → Fin 10) (n ell : ℕ) :
    wordAt s n (ell + 1) =
      Fin.cons (s n) (wordAt s (n + 1) ell) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [wordAt]
  · change s (n + (j.val + 1)) = s (n + 1 + j.val)
    congr 1
    omega

@[simp] theorem ofFn_snoc (ell : ℕ) (v : DecimalWord ell) (d : Fin 10) :
    List.ofFn (Fin.snoc v d) = List.ofFn v ++ [d] := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

@[simp] theorem ofFn_cons (ell : ℕ) (d : Fin 10) (v : DecimalWord ell) :
    List.ofFn (Fin.cons d v) = d :: List.ofFn v := by
  exact List.ofFn_cons d v

/-- Appending one digit partitions occurrences of a vertex exactly. There is
no right-boundary error because T1 tests words in the infinite stream. -/
theorem sum_snoc_blockCount
    (s : ℕ → Fin 10) (ell N : ℕ) (v : DecimalWord ell) :
    ∑ d : Fin 10, blockCount s (List.ofFn (Fin.snoc v d)) N =
      blockCount s (List.ofFn v) N := by
  classical
  let starts : Finset (Fin N) :=
    Finset.univ.filter fun n => wordAt s n.val ell = v
  let next : Fin N → Fin 10 := fun n => s (n.val + ell)
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := starts) (t := (Finset.univ : Finset (Fin 10)))
    (f := next) (by simp)
  calc
    ∑ d : Fin 10, blockCount s (List.ofFn (Fin.snoc v d)) N =
        ∑ d : Fin 10, (starts.filter fun n => next n = d).card := by
      apply Finset.sum_congr rfl
      intro d _
      rw [blockCount_ofFn_eq_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [starts, next, wordAt_snoc]
    _ = starts.card := by simpa using hfiber.symm
    _ = blockCount s (List.ofFn v) N := by
      rw [blockCount_ofFn_eq_filter]

/-- Exact outgoing de Bruijn marginal identity for empirical frequencies. -/
theorem sum_snoc_blockFrequency
    (s : ℕ → Fin 10) (ell N : ℕ) (v : DecimalWord ell) :
    ∑ d : Fin 10, blockFrequency s (List.ofFn (Fin.snoc v d)) N =
      blockFrequency s (List.ofFn v) N := by
  unfold blockFrequency
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_snoc_blockCount]

/-- Indicator that the tuple `u` occurs at start `n`. -/
def blockHit (s : ℕ → Fin 10) {ell : ℕ} (u : DecimalWord ell) (n : ℕ) : ℕ :=
  if wordAt s n ell = u then 1 else 0

/-- Block counts as sums of occurrence indicators over the start range. -/
theorem blockCount_ofFn_eq_sum_range
    (s : ℕ → Fin 10) {ell : ℕ} (u : DecimalWord ell) (N : ℕ) :
    blockCount s (List.ofFn u) N =
      ∑ n ∈ Finset.range N, blockHit s u n := by
  rw [blockCount_ofFn_eq_filter]
  calc
    ((Finset.univ : Finset (Fin N)).filter
        fun n => wordAt s n.val ell = u).card =
        ∑ n : Fin N, blockHit s u n.val := by
      simpa [blockHit] using
        (Finset.sum_boole
          (fun n : Fin N => wordAt s n.val ell = u)
          (Finset.univ : Finset (Fin N))).symm
    _ = ∑ n ∈ Finset.range N, blockHit s u n := by
      exact Fin.sum_univ_eq_sum_range (fun n => blockHit s u n) N

/-- Prepending one digit partitions the shifted occurrences of a vertex. -/
theorem sum_cons_blockCount_eq_shifted
    (s : ℕ → Fin 10) (ell N : ℕ) (v : DecimalWord ell) :
    ∑ d : Fin 10, blockCount s (List.ofFn (Fin.cons d v)) N =
      ∑ n ∈ Finset.range N, blockHit s v (n + 1) := by
  classical
  let starts : Finset (Fin N) :=
    Finset.univ.filter fun n => wordAt s (n.val + 1) ell = v
  let first : Fin N → Fin 10 := fun n => s n.val
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := starts) (t := (Finset.univ : Finset (Fin 10)))
    (f := first) (by simp)
  calc
    ∑ d : Fin 10, blockCount s (List.ofFn (Fin.cons d v)) N =
        ∑ d : Fin 10, (starts.filter fun n => first n = d).card := by
      apply Finset.sum_congr rfl
      intro d _
      rw [blockCount_ofFn_eq_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [wordAt_cons]
      simp [starts, first, and_comm]
    _ = starts.card := by simpa using hfiber.symm
    _ = ∑ n : Fin N, blockHit s v (n.val + 1) := by
      simpa [starts, blockHit] using
        (Finset.sum_boole
          (fun n : Fin N => wordAt s (n.val + 1) ell = v)
          (Finset.univ : Finset (Fin N))).symm
    _ = ∑ n ∈ Finset.range N, blockHit s v (n + 1) := by
      exact Fin.sum_univ_eq_sum_range (fun n => blockHit s v (n + 1)) N

/-- Exact endpoint bookkeeping for the incoming de Bruijn marginal. -/
theorem sum_cons_blockCount_endpoint
    (s : ℕ → Fin 10) (ell N : ℕ) (v : DecimalWord ell) :
    (∑ d : Fin 10, blockCount s (List.ofFn (Fin.cons d v)) N) +
        blockHit s v 0 =
      blockCount s (List.ofFn v) N + blockHit s v N := by
  rw [sum_cons_blockCount_eq_shifted, blockCount_ofFn_eq_sum_range]
  exact (Finset.sum_range_succ' (blockHit s v) N).symm.trans
    (Finset.sum_range_succ (blockHit s v) N)

/-- The incoming count and the vertex count differ by at most one. -/
theorem abs_sum_cons_blockCount_sub_le_one
    (s : ℕ → Fin 10) (ell N : ℕ) (v : DecimalWord ell) :
    |((∑ d : Fin 10,
        blockCount s (List.ofFn (Fin.cons d v)) N : ℕ) : ℝ) -
        blockCount s (List.ofFn v) N| ≤ 1 := by
  let A : ℕ := ∑ d : Fin 10, blockCount s (List.ofFn (Fin.cons d v)) N
  let B : ℕ := blockCount s (List.ofFn v) N
  have hendpoint : A + blockHit s v 0 = B + blockHit s v N := by
    exact sum_cons_blockCount_endpoint s ell N v
  have h0 : blockHit s v 0 ≤ 1 := by
    unfold blockHit
    split <;> omega
  have hN : blockHit s v N ≤ 1 := by
    unfold blockHit
    split <;> omega
  have hAB : A ≤ B + 1 := by omega
  have hBA : B ≤ A + 1 := by omega
  change |(A : ℝ) - (B : ℝ)| ≤ 1
  have hABR : (A : ℝ) ≤ (B : ℝ) + 1 := by exact_mod_cast hAB
  have hBAR : (B : ℝ) ≤ (A : ℝ) + 1 := by exact_mod_cast hBA
  rw [abs_le]
  constructor <;> linarith

/-- Boundary-correct incoming marginal estimate. Its right side tends to zero
along every cutoff sequence tending to infinity. -/
theorem abs_sum_cons_blockFrequency_sub_le
    (s : ℕ → Fin 10) (ell N : ℕ) (hN : 0 < N)
    (v : DecimalWord ell) :
    |(∑ d : Fin 10, blockFrequency s (List.ofFn (Fin.cons d v)) N) -
        blockFrequency s (List.ofFn v) N| ≤ 1 / (N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  simp only [blockFrequency, ← Finset.sum_div, ← Nat.cast_sum]
  rw [← sub_div, abs_div, abs_of_pos hNR]
  exact (div_le_div_iff_of_pos_right hNR).2
    (abs_sum_cons_blockCount_sub_le_one s ell N v)

/-- Outgoing edge marginal of a length-`ell + 1` vector. -/
def outgoingMarginal {ell : ℕ} (p : DecimalWord (ell + 1) → ℝ)
    (v : DecimalWord ell) : ℝ :=
  ∑ d : Fin 10, p (Fin.snoc v d)

/-- Incoming edge marginal of a length-`ell + 1` vector. -/
def incomingMarginal {ell : ℕ} (p : DecimalWord (ell + 1) → ℝ)
    (v : DecimalWord ell) : ℝ :=
  ∑ d : Fin 10, p (Fin.cons d v)

/-- A coordinatewise empirical-vector limit is normalized. -/
theorem frequencyVector_limit_normalized
    (s : ℕ → Fin 10) (k : ℕ) (cutoffs : ℕ → ℕ)
    (hcutoffs : Tendsto cutoffs atTop atTop)
    (p : DecimalWord k → ℝ)
    (hconv : ∀ u, Tendsto
      (fun j => frequencyVector s k (cutoffs j) u) atTop (nhds (p u))) :
    ∑ u, p u = 1 := by
  have hsum : Tendsto
      (fun j => ∑ u : DecimalWord k, frequencyVector s k (cutoffs j) u)
      atTop (nhds (∑ u, p u)) :=
    tendsto_finsetSum Finset.univ fun u _ => hconv u
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < cutoffs j :=
    hcutoffs.eventually (eventually_ge_atTop 1)
  have hone : Tendsto
      (fun j => ∑ u : DecimalWord k, frequencyVector s k (cutoffs j) u)
      atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hpos] with j hj
    symm
    exact sum_frequencyVector_eq_one s k (cutoffs j) hj
  exact tendsto_nhds_unique hsum hone

/-- Exact outgoing counting identifies the limiting vertex frequency with
the outgoing edge marginal. -/
theorem vertexFrequency_tendsto_outgoingMarginal
    (s : ℕ → Fin 10) (ell : ℕ) (cutoffs : ℕ → ℕ)
    (p : DecimalWord (ell + 1) → ℝ)
    (hconv : ∀ u, Tendsto
      (fun j => frequencyVector s (ell + 1) (cutoffs j) u)
      atTop (nhds (p u))) (v : DecimalWord ell) :
    Tendsto (fun j => blockFrequency s (List.ofFn v) (cutoffs j))
      atTop (nhds (outgoingMarginal p v)) := by
  have hsum : Tendsto
      (fun j => ∑ d : Fin 10,
        blockFrequency s (List.ofFn (Fin.snoc v d)) (cutoffs j))
      atTop (nhds (outgoingMarginal p v)) := by
    exact tendsto_finsetSum Finset.univ fun d _ => hconv (Fin.snoc v d)
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun j =>
    sum_snoc_blockFrequency s ell (cutoffs j) v

/-- Boundary-correct passage to the limit: incoming and outgoing de Bruijn
marginals agree. -/
theorem frequencyVector_limit_marginals
    (s : ℕ → Fin 10) (ell : ℕ) (cutoffs : ℕ → ℕ)
    (hcutoffs : Tendsto cutoffs atTop atTop)
    (p : DecimalWord (ell + 1) → ℝ)
    (hconv : ∀ u, Tendsto
      (fun j => frequencyVector s (ell + 1) (cutoffs j) u)
      atTop (nhds (p u))) (v : DecimalWord ell) :
    incomingMarginal p v = outgoingMarginal p v := by
  let incoming : ℕ → ℝ := fun j => ∑ d : Fin 10,
    blockFrequency s (List.ofFn (Fin.cons d v)) (cutoffs j)
  let vertex : ℕ → ℝ := fun j =>
    blockFrequency s (List.ofFn v) (cutoffs j)
  have hincoming : Tendsto incoming atTop (nhds (incomingMarginal p v)) := by
    exact tendsto_finsetSum Finset.univ fun d _ => hconv (Fin.cons d v)
  have hvertex : Tendsto vertex atTop (nhds (outgoingMarginal p v)) :=
    vertexFrequency_tendsto_outgoingMarginal s ell cutoffs p hconv v
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < cutoffs j :=
    hcutoffs.eventually (eventually_ge_atTop 1)
  have hinv : Tendsto (fun j => 1 / (cutoffs j : ℝ)) atTop (nhds 0) :=
    (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (nhds 0)).comp hcutoffs
  have habs : Tendsto (fun j => |incoming j - vertex j|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun j => abs_nonneg _
    · filter_upwards [hpos] with j hj
      exact abs_sum_cons_blockFrequency_sub_le s ell (cutoffs j) hj v
    · exact hinv
  have hdiff : Tendsto (fun j => incoming j - vertex j) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habs
  have hdiffLimit := hincoming.sub hvertex
  have heq : incomingMarginal p v - outgoingMarginal p v = 0 :=
    tendsto_nhds_unique hdiffLimit hdiff
  linarith

/-- At `k = 1`, the unique order-zero vertex has marginal one. -/
theorem length_one_vertexMarginal_eq_one
    (s : ℕ → Fin 10) (cutoffs : ℕ → ℕ)
    (hcutoffs : Tendsto cutoffs atTop atTop)
    (p : DecimalWord 1 → ℝ)
    (hconv : ∀ u, Tendsto
      (fun j => frequencyVector s 1 (cutoffs j) u) atTop (nhds (p u)))
    (v : DecimalWord 0) : outgoingMarginal p v = 1 := by
  have hvertex :=
    vertexFrequency_tendsto_outgoingMarginal s 0 cutoffs p hconv v
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < cutoffs j :=
    hcutoffs.eventually (eventually_ge_atTop 1)
  have hempty : List.ofFn v = [] := by simp
  have hone : Tendsto
      (fun j => blockFrequency s (List.ofFn v) (cutoffs j))
      atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hpos] with j hj
    symm
    rw [hempty]
    simp [blockFrequency, blockCount, Nat.ne_of_gt hj]
  exact tendsto_nhds_unique hvertex hone

/-- All necessary-only conclusions at the least deficient pi block length.
The edge length is `vertexLength + 1`, so the `vertexLength = 0` field is the
explicit `k = 1` case. -/
structure NecessaryPiDeBruijnFlow where
  vertexLength : ℕ
  deficientWord : DecimalWord (vertexLength + 1)
  least_k_ge_one : 1 ≤ vertexLength + 1
  least_k_deficient :
    liminf
      (blockFrequency Theory.PiDigits.piDigit (List.ofFn deficientWord))
      atTop = 0
  least_k_shorter_positive :
    ∀ ell : ℕ, 1 ≤ ell → ell < vertexLength + 1 →
      ∀ u : DecimalWord ell,
        0 < liminf
          (blockFrequency Theory.PiDigits.piDigit (List.ofFn u)) atTop
  cutoffs : ℕ → ℕ
  cutoffs_strictlyIncreasing : StrictMono cutoffs
  deficientWord_frequency_tendsto_zero :
    Tendsto
      (fun j => blockFrequency Theory.PiDigits.piDigit
        (List.ofFn deficientWord) (cutoffs j))
      atTop (nhds 0)
  shorterDelta : ℝ
  shorterDelta_pos : 0 < shorterDelta
  shorterWords_uniform_eventual :
    ∀ᶠ N : ℕ in atTop,
      ∀ ell : ℕ, 1 ≤ ell → ell < vertexLength + 1 →
        ∀ u : DecimalWord ell,
          shorterDelta ≤
            blockFrequency Theory.PiDigits.piDigit (List.ofFn u) N
  edgeLimit : DecimalWord (vertexLength + 1) → ℝ
  vertexLimit : DecimalWord vertexLength → ℝ
  completeVector_converges :
    ∀ u, Tendsto
      (fun j => frequencyVector Theory.PiDigits.piDigit
        (vertexLength + 1) (cutoffs j) u)
      atTop (nhds (edgeLimit u))
  edgeLimit_nonnegative : ∀ u, 0 ≤ edgeLimit u
  edgeLimit_normalized : ∑ u, edgeLimit u = 1
  outgoing_marginal_identity :
    ∀ v, outgoingMarginal edgeLimit v = vertexLimit v
  incoming_marginal_identity :
    ∀ v, incomingMarginal edgeLimit v = vertexLimit v
  deficientWord_zero_edge : edgeLimit deficientWord = 0
  vertexMarginals_positive : ∀ v, 0 < vertexLimit v
  k_eq_one_vertexMarginal :
    vertexLength = 0 → ∀ v, vertexLimit v = 1

/-- Necessary-only T19 conclusion. Literal failure of canonical C1 forces a
least deficient length and a nonnegative normalized stationary de Bruijn-flow
limit with a missing edge and positive vertex marginals. This theorem does
not assert that C1 fails for pi. -/
theorem not_piPositiveLowerBlockDensity_implies_minimal_deBruijnFlow
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    Nonempty NecessaryPiDeBruijnFlow := by
  obtain ⟨k, hk, ⟨w, hzero⟩, hshort⟩ :=
    exists_least_deficient_length hnot
  cases k with
  | zero => omega
  | succ ell =>
      obtain ⟨delta, hdelta, hshortUniform⟩ :=
        least_length_uniform_shorter_delta (ell + 1) hshort
      obtain ⟨baseCutoffs, hbaseMono, hbaseZero⟩ :=
        zero_liminf_strictlyIncreasing_cutoffs
          Theory.PiDigits.piDigit (List.ofFn w) hzero
      obtain ⟨p, subseq, hsubseqMono, hpBounds, hpconv⟩ :=
        exists_frequencyVector_convergent_subsequence
          Theory.PiDigits.piDigit (ell + 1) baseCutoffs
      let cutoffs := baseCutoffs ∘ subseq
      have hcutoffsMono : StrictMono cutoffs :=
        hbaseMono.comp hsubseqMono
      have hcutoffsTop : Tendsto cutoffs atTop atTop :=
        hcutoffsMono.tendsto_atTop
      have hwZero : Tendsto
          (fun j => blockFrequency Theory.PiDigits.piDigit
            (List.ofFn w) (cutoffs j)) atTop (nhds 0) := by
        simpa [cutoffs, Function.comp_def] using
          hbaseZero.comp hsubseqMono.tendsto_atTop
      have hpconv' : ∀ u, Tendsto
          (fun j => frequencyVector Theory.PiDigits.piDigit
            (ell + 1) (cutoffs j) u) atTop (nhds (p u)) := by
        intro u
        simpa [cutoffs, Function.comp_def] using hpconv u
      let vertex : DecimalWord ell → ℝ := fun v => outgoingMarginal p v
      refine ⟨{
        vertexLength := ell
        deficientWord := w
        least_k_ge_one := by omega
        least_k_deficient := hzero
        least_k_shorter_positive := hshort
        cutoffs := cutoffs
        cutoffs_strictlyIncreasing := hcutoffsMono
        deficientWord_frequency_tendsto_zero := hwZero
        shorterDelta := delta
        shorterDelta_pos := hdelta
        shorterWords_uniform_eventual := hshortUniform
        edgeLimit := p
        vertexLimit := vertex
        completeVector_converges := hpconv'
        edgeLimit_nonnegative := fun u => (hpBounds u).1
        edgeLimit_normalized :=
          frequencyVector_limit_normalized Theory.PiDigits.piDigit
            (ell + 1) cutoffs hcutoffsTop p hpconv'
        outgoing_marginal_identity := by
          intro v
          rfl
        incoming_marginal_identity := by
          intro v
          exact frequencyVector_limit_marginals Theory.PiDigits.piDigit
            ell cutoffs hcutoffsTop p hpconv' v
        deficientWord_zero_edge := by
          exact tendsto_nhds_unique (hpconv' w) hwZero
        vertexMarginals_positive := by
          intro v
          by_cases hell : ell = 0
          · subst ell
            have hv := length_one_vertexMarginal_eq_one
              Theory.PiDigits.piDigit cutoffs hcutoffsTop p hpconv' v
            dsimp [vertex]
            rw [hv]
            norm_num
          · have hellpos : 1 ≤ ell := Nat.one_le_iff_ne_zero.mpr hell
            have heventVertex : ∀ᶠ N : ℕ in atTop,
                delta ≤ blockFrequency Theory.PiDigits.piDigit
                  (List.ofFn v) N := by
              filter_upwards [hshortUniform] with N hN
              exact hN ell hellpos (by omega) v
            have heventCutoffs : ∀ᶠ j : ℕ in atTop,
                delta ≤ blockFrequency Theory.PiDigits.piDigit
                  (List.ofFn v) (cutoffs j) :=
              hcutoffsTop.eventually heventVertex
            have hvertex := vertexFrequency_tendsto_outgoingMarginal
              Theory.PiDigits.piDigit ell cutoffs p hpconv' v
            have hdeltale : delta ≤ outgoingMarginal p v :=
              ge_of_tendsto hvertex heventCutoffs
            exact hdelta.trans_le hdeltale
        k_eq_one_vertexMarginal := by
          intro hell v
          subst ell
          exact length_one_vertexMarginal_eq_one
            Theory.PiDigits.piDigit cutoffs hcutoffsTop p hpconv' v
      }⟩

end Theory.PiDigits.PositiveLowerBlockDensity.T19

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.literal_not_C1_exists_deficientLength
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.exists_least_deficient_length
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.least_length_uniform_shorter_delta
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.zero_liminf_strictlyIncreasing_cutoffs
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.exists_frequencyVector_convergent_subsequence
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.sum_frequencyVector_eq_one
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.sum_snoc_blockFrequency
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.sum_cons_blockCount_endpoint
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.abs_sum_cons_blockFrequency_sub_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.frequencyVector_limit_normalized
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.vertexFrequency_tendsto_outgoingMarginal
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.frequencyVector_limit_marginals
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.length_one_vertexMarginal_eq_one
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T19.not_piPositiveLowerBlockDensity_implies_minimal_deBruijnFlow
