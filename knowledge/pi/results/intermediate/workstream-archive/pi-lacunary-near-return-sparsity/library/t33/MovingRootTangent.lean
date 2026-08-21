import TheoryLib.PiLacunaryNearReturnSparsity.T29FiniteCountTreeLeakage
import Mathlib.Topology.Order.Compact

/-!
# Moving-root tangent compactness and the separator obstruction

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module treats an abstract A14 sibling.  It makes no assertion of C2,
canonical A1, or any unconditional property of `Real.pi`.  Tangent words are
suffix coordinates relative to each row's root; they are never identified
with nodes in one original rooted tree.
-/

noncomputable section

open Finset Filter Topology

namespace DecimalFactorComplexity.MovingRootTangent

abbrev Digit := Fin 10
abbrev Word := List Digit

/-- The first `n` digits of an infinite digit sequence. -/
def pathWord (a : ℕ → Digit) : ℕ → Word
  | 0 => []
  | n + 1 => pathWord a n ++ [a n]

@[simp] theorem pathWord_zero (a : ℕ → Digit) : pathWord a 0 = [] := rfl

@[simp] theorem pathWord_succ (a : ℕ → Digit) (n : ℕ) :
    pathWord a (n + 1) = pathWord a n ++ [a n] := rfl

@[simp] theorem pathWord_length (a : ℕ → Digit) (n : ℕ) :
    (pathWord a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathWord, ih]

/-- One row of moving-root data.  `count` is an absolute word count, while
all compactness hypotheses are stated for its normalized suffix profile at
the explicit root. -/
structure MovingRootRow where
  count : Word → ℝ
  root : Word
  startDepth : ℕ
  windowLength : ℕ
  digit : ℕ → Digit
  threshold : ℝ
  root_length : root.length = startDepth
  root_pos : 0 < count root
  normalized_nonneg : ∀ v, v.length ≤ windowLength →
    0 ≤ count (root ++ v) / count root
  normalized_le_one : ∀ v, v.length ≤ windowLength →
    count (root ++ v) / count root ≤ 1
  normalized_conservation : ∀ v, v.length < windowLength →
    count (root ++ v) / count root =
      ∑ d : Digit, count (root ++ (v ++ [d])) / count root
  normalized_dominant : ∀ i, i < windowLength →
    threshold * (count (root ++ pathWord digit i) / count root) ≤
      count (root ++ pathWord digit (i + 1)) / count root

/-- The recentered, normalized suffix profile. -/
def normalizedProfile (row : MovingRootRow) (v : Word) : ℝ :=
  row.count (row.root ++ v) / row.count row.root

@[simp] theorem normalizedProfile_empty (row : MovingRootRow) :
    normalizedProfile row [] = 1 := by
  simp [normalizedProfile, row.root_pos.ne']

/-- Clamp a profile coordinate into the compact interval `[0,1]`; this agrees
with the normalized profile on every coordinate inside the row's window. -/
def boundedNormalizedProfile (row : MovingRootRow) (v : Word) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 (normalizedProfile row v)),
    le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem boundedNormalizedProfile_eq (row : MovingRootRow) (v : Word)
    (hv : v.length ≤ row.windowLength) :
    ((boundedNormalizedProfile row v : Set.Icc (0 : ℝ) 1) : ℝ) =
      normalizedProfile row v := by
  have hnonneg := row.normalized_nonneg v hv
  have hle := row.normalized_le_one v hv
  simp [boundedNormalizedProfile, normalizedProfile, hnonneg, hle]

/-- Moving-root compactness.  The extracted branch belongs to the limiting
suffix-coordinate tangent profile.  Absolute roots and start depths remain
row data and do not occur as nodes of the conclusion. -/
theorem exists_movingRoot_tangent_branch
    (rows : ℕ → MovingRootRow) (alpha : ℝ)
    (halpha : 0 < alpha)
    (hwindow : ∀ H : ℕ, ∀ᶠ q in atTop, H ≤ (rows q).windowLength)
    (hthreshold : Tendsto (fun q => (rows q).threshold) atTop (nhds alpha)) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ tangent : Word → ℝ, ∃ branch : ℕ → Digit,
        tangent [] = 1 ∧
        (∀ v, 0 ≤ tangent v ∧ tangent v ≤ 1) ∧
        (∀ v, tangent v = ∑ d : Digit, tangent (v ++ [d])) ∧
        (∀ v, Tendsto
          (fun j => normalizedProfile (rows (subseq j)) v)
          atTop (nhds (tangent v))) ∧
        (∀ i, ∀ᶠ j in atTop, (rows (subseq j)).digit i = branch i) ∧
        (∀ i, 0 < tangent (pathWord branch i)) ∧
        (∀ i, alpha * tangent (pathWord branch i) ≤
          tangent (pathWord branch (i + 1))) := by
  let joint : ℕ →
      (Word → Set.Icc (0 : ℝ) 1) × (ℕ → Digit) := fun q =>
    (boundedNormalizedProfile (rows q), (rows q).digit)
  obtain ⟨limit, subseq, hsubseq, hlimit⟩ :=
    CompactSpace.tendsto_subseq joint
  let tangent : Word → ℝ := fun v => ((limit.1 v : Set.Icc (0 : ℝ) 1) : ℝ)
  let branch : ℕ → Digit := limit.2
  have hprofile : ∀ v, Tendsto
      (fun j => normalizedProfile (rows (subseq j)) v)
      atTop (nhds (tangent v)) := by
    intro v
    have hcoord := (tendsto_pi_nhds.mp hlimit.fst_nhds) v
    have hval := (continuous_subtype_val.tendsto (limit.1 v)).comp hcoord
    have hinWindow : ∀ᶠ j in atTop,
        v.length ≤ (rows (subseq j)).windowLength :=
      hsubseq.tendsto_atTop.eventually (hwindow v.length)
    apply hval.congr'
    filter_upwards [hinWindow] with j hj
    simpa [joint, tangent, Function.comp_def] using
      (boundedNormalizedProfile_eq (rows (subseq j)) v hj)
  have hdigit : ∀ i, ∀ᶠ j in atTop,
      (rows (subseq j)).digit i = branch i := by
    intro i
    have hcoord := (tendsto_pi_nhds.mp hlimit.snd_nhds) i
    simpa [joint, branch, Function.comp_def, nhds_discrete] using hcoord
  have hpath : ∀ n, ∀ᶠ j in atTop,
      pathWord (rows (subseq j)).digit n = pathWord branch n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        filter_upwards [ih, hdigit n] with j hprefix hd
        simp [pathWord, hprefix, hd]
  have htangentRoot : tangent [] = 1 := by
    have hone : Tendsto
      (fun j => normalizedProfile (rows (subseq j)) [])
      atTop (nhds 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1))
    exact tendsto_nhds_unique (hprofile []) hone
  refine ⟨subseq, hsubseq, tangent, branch, htangentRoot, ?_, ?_, hprofile,
    hdigit, ?_⟩
  · intro v
    exact (limit.1 v).property
  · intro v
    have hinWindow : ∀ᶠ j in atTop,
        v.length < (rows (subseq j)).windowLength := by
      have hwide := hsubseq.tendsto_atTop.eventually (hwindow (v.length + 1))
      filter_upwards [hwide] with j hj
      omega
    have heq : ∀ᶠ j in atTop,
        normalizedProfile (rows (subseq j)) v =
          ∑ d : Digit,
            normalizedProfile (rows (subseq j)) (v ++ [d]) := by
      filter_upwards [hinWindow] with j hj
      simpa [normalizedProfile] using
        (rows (subseq j)).normalized_conservation v hj
    have hsum : Tendsto
        (fun j => ∑ d : Digit,
          normalizedProfile (rows (subseq j)) (v ++ [d]))
        atTop (nhds (∑ d : Digit, tangent (v ++ [d]))) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset Digit)
        (fun d _ => hprofile (v ++ [d]))
    have hsum' : Tendsto
        (fun j => ∑ d : Digit,
          normalizedProfile (rows (subseq j)) (v ++ [d]))
        atTop (nhds (tangent v)) :=
      (hprofile v).congr' heq
    exact tendsto_nhds_unique hsum' hsum
  · have hdominant : ∀ i, alpha * tangent (pathWord branch i) ≤
        tangent (pathWord branch (i + 1)) := by
      intro i
      have hinWindow : ∀ᶠ j in atTop,
          i < (rows (subseq j)).windowLength := by
        have hwide := hsubseq.tendsto_atTop.eventually (hwindow (i + 1))
        filter_upwards [hwide] with j hj
        omega
      have hineq : ∀ᶠ j in atTop,
          (rows (subseq j)).threshold *
              normalizedProfile (rows (subseq j)) (pathWord branch i) ≤
            normalizedProfile (rows (subseq j)) (pathWord branch (i + 1)) := by
        filter_upwards [hinWindow, hpath i, hpath (i + 1)] with j hj hp hps
        rw [← hp, ← hps]
        simpa [normalizedProfile] using
          (rows (subseq j)).normalized_dominant i hj
      have hthreshold' : Tendsto (fun j => (rows (subseq j)).threshold)
          atTop (nhds alpha) := hthreshold.comp hsubseq.tendsto_atTop
      exact le_of_tendsto_of_tendsto
        (hthreshold'.mul (hprofile (pathWord branch i)))
        (hprofile (pathWord branch (i + 1))) hineq
    refine ⟨?_, hdominant⟩
    intro i
    induction i with
    | zero => simpa [pathWord, htangentRoot]
    | succ i ih => exact (mul_pos halpha ih).trans_le (hdominant i)

/-! ## The exact triangular separator tree -/

/-- Start of block `k`; this is T31's `b_H` with `H = k + 1`. -/
def blockStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => blockStart k + (k + 2)

/-- The separator immediately after block `k`, whose good window has `k+1`
edge levels. -/
def separatorLevel (k : ℕ) : ℕ := blockStart k + (k + 1)

@[simp] theorem blockStart_succ (k : ℕ) :
    blockStart (k + 1) = blockStart k + (k + 2) := rfl

theorem blockStart_succ_eq_separator_add_one (k : ℕ) :
    blockStart (k + 1) = separatorLevel k + 1 := by
  rw [blockStart_succ]
  unfold separatorLevel
  omega

theorem separatorLevel_succ (k : ℕ) :
    separatorLevel (k + 1) = separatorLevel k + (k + 3) := by
  simp [separatorLevel]
  omega

theorem blockStart_strictMono : StrictMono blockStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp

theorem separatorLevel_strictMono : StrictMono separatorLevel := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [separatorLevel_succ]
  omega

theorem blockStart_closed_form (k : ℕ) :
    2 * blockStart k = k * (k + 3) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [blockStart_succ]
      nlinarith

/-- Separator edge levels are exactly `1,4,8,13,...`. -/
def IsSeparator (n : ℕ) : Prop := ∃ k, n = separatorLevel k

theorem block_level_not_separator (k i : ℕ) (hi : i < k + 1) :
    ¬ IsSeparator (blockStart k + i) := by
  rintro ⟨l, hl⟩
  have hbefore : blockStart k + i < separatorLevel k := by
    unfold separatorLevel
    omega
  rcases lt_trichotomy l k with hlk | rfl | hkl
  · have hstep : separatorLevel l < blockStart (l + 1) := by
      rw [blockStart_succ_eq_separator_add_one]
      omega
    have hmono : blockStart (l + 1) ≤ blockStart k :=
      blockStart_strictMono.monotone (by omega)
    omega
  · omega
  · have hmono := separatorLevel_strictMono hkl
    omega

theorem separator_unbounded (r : ℕ) : r ≤ separatorLevel r := by
  unfold separatorLevel
  omega

/-- At separators mass splits equally among all ten children; at every other
level the zero child receives all mass. -/
noncomputable def separatorWeight (n : ℕ) (d : Digit) : ℝ := by
  classical
  exact if IsSeparator n then 1 / 10 else if d = 0 then 1 else 0

theorem separatorWeight_nonneg (n : ℕ) (d : Digit) :
    0 ≤ separatorWeight n d := by
  classical
  unfold separatorWeight
  split_ifs <;> norm_num

theorem sum_separatorWeight (n : ℕ) :
    ∑ d : Digit, separatorWeight n d = 1 := by
  classical
  by_cases hs : IsSeparator n
  · simp [separatorWeight, hs]
  · simp [separatorWeight, hs]

/-- Product of edge weights down a suffix beginning at absolute level `n`. -/
def separatorCountFrom : ℕ → Word → ℝ
  | _, [] => 1
  | n, d :: w => separatorWeight n d * separatorCountFrom (n + 1) w

/-- The single original rooted count tree. -/
def separatorCount (w : Word) : ℝ := separatorCountFrom 0 w

theorem separatorCountFrom_nonneg (n : ℕ) (w : Word) :
    0 ≤ separatorCountFrom n w := by
  induction w generalizing n with
  | nil => simp [separatorCountFrom]
  | cons d w ih =>
      exact mul_nonneg (separatorWeight_nonneg n d) (ih (n + 1))

theorem separatorCount_nonneg (w : Word) : 0 ≤ separatorCount w :=
  separatorCountFrom_nonneg 0 w

theorem separatorCountFrom_append (n : ℕ) (u v : Word) :
    separatorCountFrom n (u ++ v) =
      separatorCountFrom n u * separatorCountFrom (n + u.length) v := by
  induction u generalizing n with
  | nil => simp [separatorCountFrom]
  | cons d u ih =>
      simp [separatorCountFrom, ih, Nat.add_assoc, Nat.add_comm, mul_assoc]

theorem separatorCount_append_digit (u : Word) (d : Digit) :
    separatorCount (u ++ [d]) =
      separatorCount u * separatorWeight u.length d := by
  change separatorCountFrom 0 (u ++ [d]) =
    separatorCountFrom 0 u * separatorWeight u.length d
  rw [separatorCountFrom_append]
  simp [separatorCountFrom, mul_comm]

theorem separatorCount_append (u v : Word) :
    separatorCount (u ++ v) =
      separatorCount u * separatorCountFrom u.length v := by
  change separatorCountFrom 0 (u ++ v) =
    separatorCountFrom 0 u * separatorCountFrom u.length v
  simpa using separatorCountFrom_append 0 u v

/-- Exact conservation at every node of the original tree. -/
theorem separatorCount_conservation (u : Word) :
    separatorCount u = ∑ d : Digit, separatorCount (u ++ [d]) := by
  simp_rw [separatorCount_append_digit]
  rw [← Finset.mul_sum, sum_separatorWeight, mul_one]

/-- Positive half-dominance in the original tree. -/
def HalfDominantEdge (u : Word) (d : Digit) : Prop :=
  0 < separatorCount u ∧
    (1 / 2 : ℝ) * separatorCount u ≤ separatorCount (u ++ [d])

theorem no_halfDominantEdge_at_separator (u : Word) (d : Digit)
    (hu : IsSeparator u.length) : ¬ HalfDominantEdge u d := by
  rintro ⟨hpos, hgood⟩
  rw [separatorCount_append_digit] at hgood
  simp [separatorWeight, hu] at hgood
  nlinarith

theorem separatorCountFrom_zero_replicate_pos (n m : ℕ) :
    0 < separatorCountFrom n (List.replicate m (0 : Digit)) := by
  induction m generalizing n with
  | zero => simp [separatorCountFrom]
  | succ m ih =>
      simp only [List.replicate_succ, separatorCountFrom]
      have hw : 0 < separatorWeight n (0 : Digit) := by
        classical
        by_cases hs : IsSeparator n <;> simp [separatorWeight, hs]
      exact mul_pos hw (ih (n + 1))

theorem separatorCount_zero_replicate_pos (m : ℕ) :
    0 < separatorCount (List.replicate m (0 : Digit)) :=
  separatorCountFrom_zero_replicate_pos 0 m

/-- The tangent tree concentrated on the all-zero suffix branch. -/
def zeroTangent : Word → ℝ
  | [] => 1
  | d :: w => if d = 0 then zeroTangent w else 0

theorem zeroTangent_nonneg (w : Word) : 0 ≤ zeroTangent w := by
  induction w with
  | nil => simp [zeroTangent]
  | cons d w ih =>
      simp only [zeroTangent]
      split_ifs <;> positivity

theorem zeroTangent_le_one (w : Word) : zeroTangent w ≤ 1 := by
  induction w with
  | nil => simp [zeroTangent]
  | cons d w ih =>
      simp only [zeroTangent]
      split_ifs <;> norm_num
      exact ih

theorem zeroTangent_append (u v : Word) :
    zeroTangent (u ++ v) = zeroTangent u * zeroTangent v := by
  induction u with
  | nil => simp [zeroTangent]
  | cons d u ih =>
      simp only [List.cons_append, zeroTangent]
      by_cases hd : d = 0 <;> simp [hd, ih]

theorem zeroTangent_conservation (u : Word) :
    zeroTangent u = ∑ d : Digit, zeroTangent (u ++ [d]) := by
  classical
  simp_rw [zeroTangent_append]
  rw [← Finset.mul_sum]
  simp [zeroTangent]

theorem zeroTangent_replicate_zero (m : ℕ) :
    zeroTangent (List.replicate m (0 : Digit)) = 1 := by
  induction m with
  | zero => simp [zeroTangent]
  | succ m ih => simp [List.replicate_succ, zeroTangent, ih]

theorem pathWord_zero_eq_replicate (m : ℕ) :
    pathWord (fun _ => (0 : Digit)) m = List.replicate m 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pathWord_succ, ih]
      simpa using (List.replicate_add m 1 (0 : Digit)).symm

/-- Within block `k`, every suffix window of length at most `k+1` sees no
separator, so its recentered profile is exactly the all-zero tangent tree. -/
theorem separatorCountFrom_block_eq_zeroTangent
    (k offset : ℕ) (v : Word)
    (hv : offset + v.length ≤ k + 1) :
    separatorCountFrom (blockStart k + offset) v = zeroTangent v := by
  induction v generalizing offset with
  | nil => simp [separatorCountFrom, zeroTangent]
  | cons d v ih =>
      have hoffset : offset < k + 1 := by
        simp only [List.length_cons] at hv
        omega
      have hnsep : ¬ IsSeparator (blockStart k + offset) :=
        block_level_not_separator k offset hoffset
      have htail :
          separatorCountFrom ((blockStart k + offset) + 1) v =
            zeroTangent v := by
        have hrec := ih (offset + 1) (by
          simp only [List.length_cons] at hv
          omega)
        simpa [Nat.add_assoc] using hrec
      classical
      simp [separatorCountFrom, zeroTangent, separatorWeight, hnsep, htail]

/-- Exact normalized recentering identity on every displayed triangular
window. -/
theorem separator_recentered_profile_eq_zeroTangent
    (k : ℕ) (v : Word) (hv : v.length ≤ k + 1) :
    separatorCount
          (List.replicate (blockStart k) (0 : Digit) ++ v) /
        separatorCount (List.replicate (blockStart k) (0 : Digit)) =
      zeroTangent v := by
  rw [separatorCount_append]
  simp only [List.length_replicate]
  have hzero : separatorCountFrom (blockStart k) v = zeroTangent v := by
    simpa using separatorCountFrom_block_eq_zeroTangent k 0 v
      (by simpa using hv)
  rw [hzero]
  have hne := (separatorCount_zero_replicate_pos (blockStart k)).ne'
  field_simp

/-- Every triangular block supplies exactly `k+1` consecutive positive,
zero-leakage, half-dominant edges beginning at `blockStart k`. -/
theorem separatorBlock_long_path (k : ℕ) :
    ∃ root : Word,
      root.length = blockStart k ∧ 0 < separatorCount root ∧
      ∀ i, i < k + 1 →
        separatorCount (root ++ List.replicate (i + 1) (0 : Digit)) =
            separatorCount (root ++ List.replicate i (0 : Digit)) ∧
          HalfDominantEdge
            (root ++ List.replicate i (0 : Digit)) (0 : Digit) := by
  let root : Word := List.replicate (blockStart k) (0 : Digit)
  refine ⟨root, by simp [root], separatorCount_zero_replicate_pos _, ?_⟩
  intro i hi
  let parent : Word := root ++ List.replicate i (0 : Digit)
  have hparentLength : parent.length = blockStart k + i := by
    simp [parent, root]
  have hnsep : ¬ IsSeparator parent.length := by
    rw [hparentLength]
    exact block_level_not_separator k i hi
  have hweight : separatorWeight parent.length (0 : Digit) = 1 := by
    classical
    simp [separatorWeight, hnsep]
  have hedge : separatorCount (parent ++ [(0 : Digit)]) =
      separatorCount parent := by
    rw [separatorCount_append_digit, hweight, mul_one]
  have hparentPos : 0 < separatorCount parent := by
    dsimp only [parent]
    rw [separatorCount_append]
    exact mul_pos (separatorCount_zero_replicate_pos _)
      (separatorCountFrom_zero_replicate_pos root.length i)
  have hdisplay :
      separatorCount (root ++ List.replicate (i + 1) (0 : Digit)) =
        separatorCount parent := by
    rw [List.replicate_add]
    simpa [parent, List.append_assoc] using hedge
  refine ⟨hdisplay, hparentPos, ?_⟩
  rw [← hedge]
  nlinarith

/-- The moving starts escape every fixed depth. -/
theorem blockStart_tendsto_atTop : Tendsto blockStart atTop atTop :=
  blockStart_strictMono.tendsto_atTop

/-- No branch in the original separator tree can remain half-dominant from
any absolute starting word, because it must cross a later separator. -/
theorem no_original_infinite_halfDominant_branch
    (root : Word) (a : ℕ → Digit) :
    ¬ ∀ i, HalfDominantEdge (root ++ pathWord a i) (a i) := by
  intro hbranch
  let s := separatorLevel root.length
  let i := s - root.length
  have hrs : root.length ≤ s := separator_unbounded root.length
  have hi : root.length + i = s := by
    dsimp only [i]
    omega
  have hlength : (root ++ pathWord a i).length = s := by
    simp [hi]
  have hsep : IsSeparator (root ++ pathWord a i).length := by
    rw [hlength]
    exact ⟨root.length, rfl⟩
  exact no_halfDominantEdge_at_separator
    (root ++ pathWord a i) (a i) hsep (hbranch i)

/-- The explicit `k`th moving-root row cut from the single separator tree. -/
def separatorRow (k : ℕ) : MovingRootRow where
  count := separatorCount
  root := List.replicate (blockStart k) (0 : Digit)
  startDepth := blockStart k
  windowLength := k + 1
  digit := fun _ => 0
  threshold := 1
  root_length := by simp
  root_pos := separatorCount_zero_replicate_pos _
  normalized_nonneg := by
    intro v hv
    rw [separator_recentered_profile_eq_zeroTangent k v hv]
    exact zeroTangent_nonneg v
  normalized_le_one := by
    intro v hv
    rw [separator_recentered_profile_eq_zeroTangent k v hv]
    exact zeroTangent_le_one v
  normalized_conservation := by
    intro v hv
    rw [separator_recentered_profile_eq_zeroTangent k v hv.le]
    have hchild : ∀ d : Digit, (v ++ [d]).length ≤ k + 1 := by
      intro d
      simp
      omega
    simp_rw [separator_recentered_profile_eq_zeroTangent k _ (hchild _)]
    exact zeroTangent_conservation v
  normalized_dominant := by
    intro i hi
    rw [pathWord_zero_eq_replicate, pathWord_zero_eq_replicate]
    rw [separator_recentered_profile_eq_zeroTangent k _ (by simp; omega)]
    rw [separator_recentered_profile_eq_zeroTangent k _ (by simp; omega)]
    simp [zeroTangent_replicate_zero]

theorem separatorRow_windows_tendsto :
    ∀ H : ℕ, ∀ᶠ k in atTop, H ≤ (separatorRow k).windowLength := by
  intro H
  filter_upwards [eventually_ge_atTop H] with k hk
  dsimp only [separatorRow]
  omega

/-- Compactness produces an infinite branch in a recentered tangent of the
explicit separator rows.  The conclusion remains entirely in suffix
coordinates. -/
theorem exists_separator_movingRoot_tangent_branch :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ tangent : Word → ℝ, ∃ branch : ℕ → Digit,
        tangent [] = 1 ∧
        (∀ v, 0 ≤ tangent v ∧ tangent v ≤ 1) ∧
        (∀ v, tangent v = ∑ d : Digit, tangent (v ++ [d])) ∧
        (∀ v, Tendsto
          (fun j => normalizedProfile (separatorRow (subseq j)) v)
          atTop (nhds (tangent v))) ∧
        (∀ i, ∀ᶠ j in atTop,
          (separatorRow (subseq j)).digit i = branch i) ∧
        (∀ i, 0 < tangent (pathWord branch i)) ∧
        (∀ i, tangent (pathWord branch i) ≤
          tangent (pathWord branch (i + 1))) := by
  simpa using exists_movingRoot_tangent_branch separatorRow 1
    (by norm_num) separatorRow_windows_tendsto tendsto_const_nhds

/-- Exact no-pullback counterexample: one conservative original tree has
arbitrarily long moving-root windows with escaping starts and a compact tangent
branch, but no positive half-dominant branch from any original root. -/
theorem separatorBlock_tangent_does_not_pull_back :
    (∀ u : Word,
      separatorCount u = ∑ d : Digit, separatorCount (u ++ [d])) ∧
    Tendsto (fun k => (separatorRow k).startDepth) atTop atTop ∧
    (∀ k, ∃ root : Word,
      root.length = (separatorRow k).startDepth ∧
      0 < separatorCount root ∧
      ∀ i, i < (separatorRow k).windowLength →
        separatorCount (root ++ List.replicate (i + 1) (0 : Digit)) =
            separatorCount (root ++ List.replicate i (0 : Digit)) ∧
          HalfDominantEdge
            (root ++ List.replicate i (0 : Digit)) (0 : Digit)) ∧
    (∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ tangent : Word → ℝ, ∃ branch : ℕ → Digit,
        tangent [] = 1 ∧
        (∀ v, 0 ≤ tangent v ∧ tangent v ≤ 1) ∧
        (∀ v, tangent v = ∑ d : Digit, tangent (v ++ [d])) ∧
        (∀ v, Tendsto
          (fun j => normalizedProfile (separatorRow (subseq j)) v)
          atTop (nhds (tangent v))) ∧
        (∀ i, ∀ᶠ j in atTop,
          (separatorRow (subseq j)).digit i = branch i) ∧
        (∀ i, 0 < tangent (pathWord branch i)) ∧
        (∀ i, tangent (pathWord branch i) ≤
          tangent (pathWord branch (i + 1)))) ∧
    (∀ root : Word, ∀ a : ℕ → Digit,
      ¬ ∀ i, HalfDominantEdge (root ++ pathWord a i) (a i)) := by
  refine ⟨separatorCount_conservation, ?_, ?_,
    exists_separator_movingRoot_tangent_branch, ?_⟩
  · simpa [separatorRow] using blockStart_tendsto_atTop
  · intro k
    simpa [separatorRow] using separatorBlock_long_path k
  · exact no_original_infinite_halfDominant_branch

/-! ## The bounded-start boundary, delegated to T29 -/

universe u

/-- Anchored compactness for one fixed predicate.  This is deliberately only
a wrapper around T29: the level types are finite, `edge` is fixed outside the
length quantifier, and every finite witness starts at or below one bound. -/
theorem bounded_start_fixed_predicate_wrapper
    {Node : ℕ → Type u} [∀ n, Finite (Node n)]
    (edge : (n : ℕ) → Node n → Node (n + 1) → Prop)
    (startBound : ℕ)
    (hanchored : ∀ length, ∃ start, start ≤ startBound ∧
      Nonempty
        (FiniteCountTreeLeakage.GoodPrefix Node edge start length)) :
    ∃ start, start ≤ startBound ∧
      ∃ node : (i : ℕ) → Node (start + i),
        FiniteCountTreeLeakage.InfiniteGoodBranch edge start node :=
  FiniteCountTreeLeakage.exists_infinite_good_branch_of_bounded_starts
    edge startBound hanchored

end DecimalFactorComplexity.MovingRootTangent

#print axioms DecimalFactorComplexity.MovingRootTangent.exists_movingRoot_tangent_branch
#print axioms DecimalFactorComplexity.MovingRootTangent.separatorCount_conservation
#print axioms DecimalFactorComplexity.MovingRootTangent.separatorBlock_long_path
#print axioms DecimalFactorComplexity.MovingRootTangent.exists_separator_movingRoot_tangent_branch
#print axioms DecimalFactorComplexity.MovingRootTangent.separatorBlock_tangent_does_not_pull_back
#print axioms DecimalFactorComplexity.MovingRootTangent.bounded_start_fixed_predicate_wrapper
