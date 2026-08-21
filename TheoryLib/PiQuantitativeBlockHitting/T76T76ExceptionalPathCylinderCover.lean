import TheoryLib.PiQuantitativeBlockHitting.T75T75UniformShadowCover

/-!
# T76: bounded exceptional prefixes have arbitrarily small cylinder covers

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module isolates an elementary abstract covering lemma for a possible
exceptional-path argument.  At depth `n`, the full `p`-ary prefix level has
`p^n` members and every Bernoulli cylinder has weight `p^{-n}`.  If the bad
prefix family has cardinality at most one fixed constant at every depth,
then its level weights are dominated by a geometric series.  Consequently
the paths whose prefixes are bad at infinitely many depths possess, for every
positive `epsilon`, a countable cylinder cover of total weight below
`epsilon`.

The countable cover is represented without measure theory: it is indexed by
`Nat`-many finite bad-prefix families.  `tailCylinderUnion` is its union and
`tailCoverWeight` is its total Bernoulli weight.

This result is entirely conditional on the uniform cardinality bound.  It
does not establish such a bound for BBP data, does not identify any actual
exceptional path, and proves nothing about `Real.pi`, canonical V1, or
normality.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Theory.PiDigits.T76ExceptionalPathCylinderCover

/-- Infinite one-sided paths over an alphabet with `p` symbols. -/
abbrev DigitPath (p : ℕ) := ℕ → Fin p

/-- A depth-`n` prefix over an alphabet with `p` symbols. -/
abbrev Prefix (p n : ℕ) := Fin n → Fin p

/-- Restriction of an infinite path to its first `n` coordinates. -/
def pathPrefix {p : ℕ} (x : DigitPath p) (n : ℕ) : Prefix p n :=
  fun i ↦ x i

/-- The cylinder consisting of paths with prescribed prefix `w`. -/
def cylinder {p n : ℕ} (w : Prefix p n) : Set (DigitPath p) :=
  {x | pathPrefix x n = w}

/-- The uniform Bernoulli weight of every depth-`n` `p`-ary cylinder. -/
def cylinderWeight (p n : ℕ) : ℝ :=
  ((p : ℝ)⁻¹) ^ n

/-- Total cylinder weight of a finite bad-prefix family at one depth. -/
def levelCoverWeight (p : ℕ) (B : ∀ n, Finset (Prefix p n)) (n : ℕ) : ℝ :=
  (B n).card * cylinderWeight p n

/-- Total weight of all bad-prefix cylinders at depths `N, N+1, ...`. -/
def tailCoverWeight (p : ℕ) (B : ∀ n, Finset (Prefix p n)) (N : ℕ) : ℝ :=
  ∑' k, levelCoverWeight p B (N + k)

/-- Paths having a bad prefix at infinitely many depths, expressed by the
equivalent cofinal quantifier rather than by a measure-theoretic limsup. -/
def badLimsup (p : ℕ) (B : ∀ n, Finset (Prefix p n)) : Set (DigitPath p) :=
  {x | ∀ N, ∃ n, N ≤ n ∧ pathPrefix x n ∈ B n}

/-- The union of all bad-prefix cylinders from depth `N` onward. -/
def tailCylinderUnion (p : ℕ) (B : ∀ n, Finset (Prefix p n)) (N : ℕ) :
    Set (DigitPath p) :=
  {x | ∃ k, pathPrefix x (N + k) ∈ B (N + k)}

/-- A concrete countable index type for the tail cover: one natural depth
offset followed by one member of that depth's finite bad family. -/
def TailCylinderIndex (p : ℕ) (B : ∀ n, Finset (Prefix p n)) (N : ℕ) :=
  Σ k : ℕ, {w : Prefix p (N + k) // w ∈ B (N + k)}

/-- The cylinder selected by a tail-cover index. -/
def tailCylinderAt {p : ℕ} {B : ∀ n, Finset (Prefix p n)} {N : ℕ}
    (i : TailCylinderIndex p B N) : Set (DigitPath p) :=
  cylinder i.2.1

/-- The individual Bernoulli weight selected by a tail-cover index. -/
def tailCylinderIndexWeight {p : ℕ} {B : ∀ n, Finset (Prefix p n)} {N : ℕ}
    (i : TailCylinderIndex p B N) : ℝ :=
  cylinderWeight p (N + i.1)

/-- The full depth-`n` prefix level has exactly the expected geometric size. -/
theorem prefixLevel_card (p n : ℕ) :
    Fintype.card (Prefix p n) = p ^ n := by
  simp [Prefix]

/-- Cylinder weights are nonnegative. -/
theorem cylinderWeight_nonneg (p n : ℕ) : 0 ≤ cylinderWeight p n := by
  exact pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) n

/-- The tail index really is countable: it is a natural-number-indexed
sigma type with finite fibers. -/
theorem tailCylinderIndex_countable (p : ℕ) (B : ∀ n, Finset (Prefix p n)) (N : ℕ) :
    Countable (TailCylinderIndex p B N) := by
  unfold TailCylinderIndex
  infer_instance

/-- Summing the equal weights over one finite bad-prefix fiber recovers the
aggregate one-level weight. -/
theorem badPrefixFiber_tsum_eq_levelCoverWeight (p : ℕ)
    (B : ∀ n, Finset (Prefix p n)) (n : ℕ) :
    (∑' _w : {w : Prefix p n // w ∈ B n}, cylinderWeight p n) =
      levelCoverWeight p B n := by
  rw [tsum_fintype]
  simp [levelCoverWeight]

/-- The concrete indexed cylinder family has exactly `tailCylinderUnion` as
its union. -/
theorem tailCylinderUnion_eq_iUnion (p : ℕ)
    (B : ∀ n, Finset (Prefix p n)) (N : ℕ) :
    tailCylinderUnion p B N =
      ⋃ i : TailCylinderIndex p B N, tailCylinderAt i := by
  ext x
  constructor
  · rintro ⟨k, hk⟩
    let i : TailCylinderIndex p B N := ⟨k, ⟨pathPrefix x (N + k), hk⟩⟩
    exact mem_iUnion.2 ⟨i, rfl⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    refine ⟨i.1, ?_⟩
    have hi' : pathPrefix x (N + i.1) = i.2.1 := by
      simpa [tailCylinderAt, cylinder] using hi
    rw [hi']
    exact i.2.2

/-- Every infinitely-often bad path belongs to every tail cylinder union. -/
theorem badLimsup_subset_tailCylinderUnion (p : ℕ)
    (B : ∀ n, Finset (Prefix p n)) (N : ℕ) :
    badLimsup p B ⊆ tailCylinderUnion p B N := by
  intro x hx
  obtain ⟨n, hn, hbad⟩ := hx N
  refine ⟨n - N, ?_⟩
  have hdepth : N + (n - N) = n := Nat.add_sub_of_le hn
  rw [hdepth]
  exact hbad

/-- A uniform cardinality bound gives the pointwise geometric level bound. -/
theorem levelCoverWeight_le_geometric {p C : ℕ}
    (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) (n : ℕ) :
    levelCoverWeight p B n ≤
      (C : ℝ) * ((p : ℝ)⁻¹) ^ n := by
  have hcardReal : ((B n).card : ℝ) ≤ C := by
    exact_mod_cast hcard n
  unfold levelCoverWeight cylinderWeight
  gcongr

/-- Under `2 ≤ p`, the one-level bad-family weights are summable. -/
theorem summable_levelCoverWeight {p C : ℕ}
    (hp : 2 ≤ p) (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) :
    Summable (levelCoverWeight p B) := by
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp
  have hq0 : 0 ≤ ((p : ℝ)⁻¹) := by positivity
  have hq1 : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hpReal
  have hgeom : Summable (fun n : ℕ ↦
      (C : ℝ) * ((p : ℝ)⁻¹) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (C : ℝ)
  exact hgeom.of_nonneg_of_le
    (fun n ↦ mul_nonneg (Nat.cast_nonneg _) (cylinderWeight_nonneg p n))
    (levelCoverWeight_le_geometric B hcard)

/-- The weights of the individually indexed tail cylinders are summable. -/
theorem summable_tailCylinderIndexWeight {p C : ℕ}
    (hp : 2 ≤ p) (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) (N : ℕ) :
    Summable (@tailCylinderIndexWeight p B N) := by
  refine (summable_sigma_of_nonneg
    (f := @tailCylinderIndexWeight p B N)
    (fun i ↦ cylinderWeight_nonneg p (N + i.1))).2 ?_
  constructor
  · intro k
    exact (hasSum_fintype _).summable
  · have htail :=
      (summable_nat_add_iff N).2 (summable_levelCoverWeight hp B hcard)
    simpa only [tailCylinderIndexWeight,
      badPrefixFiber_tsum_eq_levelCoverWeight, Nat.add_comm] using htail

/-- The sum of the individually indexed cylinder weights is exactly the
aggregate tail weight used below. -/
theorem tsum_tailCylinderIndexWeight_eq_tailCoverWeight {p C : ℕ}
    (hp : 2 ≤ p) (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) (N : ℕ) :
    (∑' i : TailCylinderIndex p B N, tailCylinderIndexWeight i) =
      tailCoverWeight p B N := by
  have hsigma := summable_tailCylinderIndexWeight hp B hcard N
  unfold TailCylinderIndex at hsigma ⊢
  unfold tailCylinderIndexWeight at hsigma ⊢
  rw [hsigma.tsum_sigma' (fun _ ↦ (hasSum_fintype _).summable)]
  simp only [badPrefixFiber_tsum_eq_levelCoverWeight, tailCoverWeight]

/-- Explicit geometric upper bound for the total weight of every tail. -/
theorem tailCoverWeight_le_geometric {p C : ℕ}
    (hp : 2 ≤ p) (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) (N : ℕ) :
    tailCoverWeight p B N ≤
      (C : ℝ) * ((p : ℝ)⁻¹) ^ N /
        (1 - (p : ℝ)⁻¹) := by
  let q : ℝ := (p : ℝ)⁻¹
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp
  have hq0 : 0 ≤ q := by simp [q]
  have hq1 : q < 1 := by simpa [q] using inv_lt_one_of_one_lt₀ hpReal
  have hlevels := summable_levelCoverWeight hp B hcard
  have htail : Summable (fun k ↦ levelCoverWeight p B (N + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hlevels
  have hgeom : Summable (fun k : ℕ ↦ (C : ℝ) * q ^ (N + k)) := by
    have h := (summable_geometric_of_lt_one hq0 hq1).mul_left (C : ℝ)
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 h
  have hle : tailCoverWeight p B N ≤
      ∑' k : ℕ, (C : ℝ) * q ^ (N + k) := by
    exact htail.tsum_le_tsum (fun k ↦ by
      simpa [q] using levelCoverWeight_le_geometric B hcard (N + k)) hgeom
  have hhas : HasSum (fun k : ℕ ↦ (C : ℝ) * q ^ (N + k))
      ((C : ℝ) * q ^ N / (1 - q)) := by
    have hbase := hasSum_geometric_of_lt_one hq0 hq1
    have hmul := hbase.mul_left ((C : ℝ) * q ^ N)
    simpa only [pow_add, div_eq_mul_inv, mul_assoc] using hmul
  exact hle.trans_eq (by simpa [q] using hhas.tsum_eq)

/-- Exact geometric total appearing in the current even-epoch Haar
calculation: summing `2 / (η² 3^(2+2r))` gives `1 / (4η²)`.  This is a
standalone real-series identity; it does not assert that any arithmetic bad
set satisfies the displayed majorant. -/
theorem hasSum_evenEpochHaarMajorant (η : ℝ) (hη : η ≠ 0) :
    HasSum (fun r : ℕ ↦
      2 / (η ^ 2 * (3 : ℝ) ^ (2 + 2 * r))) (1 / (4 * η ^ 2)) := by
  have hbase := hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 9)
    (by norm_num : (1 / 9 : ℝ) < 1)
  have hmul := hbase.mul_left (2 / (9 * η ^ 2))
  convert hmul using 1
  · funext r
    rw [show 2 + 2 * r = 2 * (r + 1) by omega, pow_mul, pow_succ]
    rw [div_pow]
    norm_num
    field_simp [hη]
    simp [pow_succ]
    ring
  · norm_num
    field_simp [hη]
    norm_num

/-- The tail weight tends to zero uniformly under the cardinality bound. -/
theorem tendsto_tailCoverWeight_zero {p C : ℕ}
    (hp : 2 ≤ p) (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) :
    Tendsto (tailCoverWeight p B) atTop (nhds 0) := by
  let q : ℝ := (p : ℝ)⁻¹
  let g : ℕ → ℝ := fun N ↦ (C : ℝ) * q ^ N / (1 - q)
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp
  have hq0 : 0 ≤ q := by simp [q]
  have hq1 : q < 1 := by simpa [q] using inv_lt_one_of_one_lt₀ hpReal
  have hg : Tendsto g atTop (nhds 0) := by
    simpa [g] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C : ℝ)).div_const
        (1 - q)
  have hnonneg : ∀ N, 0 ≤ tailCoverWeight p B N := by
    intro N
    exact tsum_nonneg fun k ↦ by
      exact mul_nonneg (Nat.cast_nonneg _) (cylinderWeight_nonneg p (N + k))
  have hupper : ∀ N, tailCoverWeight p B N ≤ g N := by
    intro N
    simpa [g, q] using tailCoverWeight_le_geometric hp B hcard N
  exact squeeze_zero hnonneg hupper hg

/-- Main outer-cover conclusion.  For every positive `epsilon`, one tail of
the countable cylinder family covers every infinitely-often bad path and has
total Bernoulli weight below `epsilon`. -/
theorem badLimsup_has_arbitrarily_small_cylinder_cover {p C : ℕ}
    (hp : 2 ≤ p) (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N,
      badLimsup p B ⊆ tailCylinderUnion p B N ∧
        tailCoverWeight p B N < ε := by
  intro ε hε
  have hevent : ∀ᶠ N in atTop, tailCoverWeight p B N < ε :=
    (tendsto_order.1 (tendsto_tailCoverWeight_zero hp B hcard)).2 ε hε
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  exact ⟨N, badLimsup_subset_tailCylinderUnion p B N, hN N le_rfl⟩

/-- Fully expanded countable-cover form of the main conclusion: the cover is
the union over the concrete countable index type, and the displayed `tsum`
is the sum of the individual cylinder weights. -/
theorem badLimsup_has_arbitrarily_small_indexed_cylinder_cover {p C : ℕ}
    (hp : 2 ≤ p) (B : ∀ n, Finset (Prefix p n))
    (hcard : ∀ n, (B n).card ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N,
      badLimsup p B ⊆
          ⋃ i : TailCylinderIndex p B N, tailCylinderAt i ∧
        (∑' i : TailCylinderIndex p B N, tailCylinderIndexWeight i) < ε := by
  intro ε hε
  obtain ⟨N, hcover, hweight⟩ :=
    badLimsup_has_arbitrarily_small_cylinder_cover hp B hcard ε hε
  refine ⟨N, ?_, ?_⟩
  · simpa [tailCylinderUnion_eq_iUnion] using hcover
  · rw [tsum_tailCylinderIndexWeight_eq_tailCoverWeight hp B hcard N]
    exact hweight

end Theory.PiDigits.T76ExceptionalPathCylinderCover

namespace Theory.PiDigits.T76ExceptionalPathCylinderCover

#print axioms prefixLevel_card
#print axioms tailCylinderIndex_countable
#print axioms badPrefixFiber_tsum_eq_levelCoverWeight
#print axioms tailCylinderUnion_eq_iUnion
#print axioms badLimsup_subset_tailCylinderUnion
#print axioms levelCoverWeight_le_geometric
#print axioms summable_levelCoverWeight
#print axioms summable_tailCylinderIndexWeight
#print axioms tsum_tailCylinderIndexWeight_eq_tailCoverWeight
#print axioms tailCoverWeight_le_geometric
#print axioms hasSum_evenEpochHaarMajorant
#print axioms tendsto_tailCoverWeight_zero
#print axioms badLimsup_has_arbitrarily_small_cylinder_cover
#print axioms badLimsup_has_arbitrarily_small_indexed_cylinder_cover

end Theory.PiDigits.T76ExceptionalPathCylinderCover
