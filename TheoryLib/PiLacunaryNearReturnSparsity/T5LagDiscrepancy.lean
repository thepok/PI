import TheoryLib.PiLacunaryNearReturnSparsity.T1LagDecomposition

/-!
# Lag discrepancy reduction for pi near returns

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module is a deterministic conditional reduction. It defines the
unnormalized discrepancy over all strict circular intervals of the canonical
radius for each lag orbit. No discrepancy estimate for `Real.pi` is asserted.
-/

noncomputable section

open Filter Finset

namespace DecimalFactorComplexity
namespace LagDiscrepancy

/-- The canonical radius `10⁻ⁿ`. -/
def decimalRadius (n : ℕ) : ℝ := ((10 : ℝ) ^ n)⁻¹

/-- The number of points in the length-`N-r` lag orbit
`10^j (10^r - 1) pi` that lie in the strict centered circular interval of
radius `10⁻ⁿ`. -/
def lagNearReturnCount (n N r : ℕ) : ℕ :=
  ((Finset.range (N - r)).filter fun j =>
    circleDistance
      ((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi) < decimalRadius n).card

/-- The unnormalized error for the interval centered at zero. -/
def lagCenteredIntervalError (n N r : ℕ) : ℝ :=
  |(lagNearReturnCount n N r : ℝ) -
    2 * decimalRadius n * ((N - r : ℕ) : ℝ)|

lemma decimalRadius_pos (n : ℕ) : 0 < decimalRadius n := by
  simp [decimalRadius]

lemma decimalRadius_le_half (n : ℕ) (hn : 1 ≤ n) :
    decimalRadius n ≤ (1 / 2 : ℝ) := by
  have hpow : (2 : ℝ) ≤ (10 : ℝ) ^ n := by
    calc
      (2 : ℝ) ≤ (10 : ℝ) ^ 1 := by norm_num
      _ ≤ (10 : ℝ) ^ n := pow_right_mono₀ (by norm_num) hn
  simpa [decimalRadius, one_div] using
    ((inv_le_inv₀ (by positivity) (by norm_num)).2 hpow)

lemma lagCenteredIntervalError_nonneg (n N r : ℕ) :
    0 ≤ lagCenteredIntervalError n N r := by
  exact abs_nonneg _

/-- The count in a strict circular interval of radius `radius` and arbitrary
real center. -/
def lagCircularIntervalCount (N r : ℕ) (radius center : ℝ) : ℕ :=
  ((Finset.range (N - r)).filter fun j =>
    circleDistance
      ((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi - center) < radius).card

/-- The unnormalized circular interval discrepancy of the lag orbit at a
fixed radius: the supremum of the absolute counting error over all centers.
The canonical applications use `radius = 10⁻ⁿ ≤ 1/2`, so `2 * radius` is the
circle length of each tested strict interval. -/
def lagCircularIntervalDiscrepancy (N r : ℕ) (radius : ℝ) : ℝ :=
  sSup (Set.range fun center : ℝ =>
    |(lagCircularIntervalCount N r radius center : ℝ) -
      2 * radius * ((N - r : ℕ) : ℝ)|)

lemma lagCircularIntervalCount_le_length (N r : ℕ) (radius center : ℝ) :
    lagCircularIntervalCount N r radius center ≤ N - r := by
  unfold lagCircularIntervalCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range (N - r))

lemma lagCircularIntervalError_range_bddAbove (N r : ℕ) (radius : ℝ) :
    BddAbove (Set.range fun center : ℝ =>
      |(lagCircularIntervalCount N r radius center : ℝ) -
        2 * radius * ((N - r : ℕ) : ℝ)|) := by
  refine ⟨((N - r : ℕ) : ℝ) +
    |2 * radius * ((N - r : ℕ) : ℝ)|, ?_⟩
  rintro d ⟨center, rfl⟩
  calc
    |(lagCircularIntervalCount N r radius center : ℝ) -
        2 * radius * ((N - r : ℕ) : ℝ)| ≤
        |(lagCircularIntervalCount N r radius center : ℝ)| +
          |2 * radius * ((N - r : ℕ) : ℝ)| := abs_sub _ _
    _ = (lagCircularIntervalCount N r radius center : ℝ) +
          |2 * radius * ((N - r : ℕ) : ℝ)| := by
      rw [abs_of_nonneg]
      positivity
    _ ≤ ((N - r : ℕ) : ℝ) +
          |2 * radius * ((N - r : ℕ) : ℝ)| := by
      gcongr
      exact_mod_cast lagCircularIntervalCount_le_length N r radius center

lemma lagCircularIntervalDiscrepancy_nonneg (N r : ℕ) (radius : ℝ) :
    0 ≤ lagCircularIntervalDiscrepancy N r radius := by
  have hmember := le_csSup (lagCircularIntervalError_range_bddAbove N r radius)
    (Set.mem_range_self (0 : ℝ))
  exact (abs_nonneg
    ((lagCircularIntervalCount N r radius 0 : ℝ) -
      2 * radius * ((N - r : ℕ) : ℝ))).trans hmember

/-- The error of the interval centered at zero is bounded by the full
circular interval discrepancy. -/
lemma lagCenteredIntervalError_le_discrepancy (n N r : ℕ) :
    lagCenteredIntervalError n N r ≤
      lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
  unfold lagCircularIntervalDiscrepancy
  have hle := le_csSup (lagCircularIntervalError_range_bddAbove N r (decimalRadius n))
    (Set.mem_range_self (0 : ℝ))
  simpa [lagCenteredIntervalError, lagNearReturnCount, lagCircularIntervalCount] using hle

/-- A count is at most its reference interval length plus its absolute
discrepancy. -/
lemma lagNearReturnCount_le_expected_add_discrepancy (n N r : ℕ) :
    (lagNearReturnCount n N r : ℝ) ≤
      2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
        lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
  have hcenter : (lagNearReturnCount n N r : ℝ) ≤
      2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
        lagCenteredIntervalError n N r := by
    unfold lagCenteredIntervalError
    linarith [le_abs_self
      ((lagNearReturnCount n N r : ℝ) -
        2 * decimalRadius n * ((N - r : ℕ) : ℝ))]
  exact hcenter.trans (add_le_add le_rfl
    (lagCenteredIntervalError_le_discrepancy n N r))

/-- The total lengths of all positive lag orbits are bounded by `N²`. -/
lemma lagLengthSum_le_sq (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 (N - 1), ((N - r : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
  have hcard : (Finset.Icc 1 (N - 1)).card ≤ N := by
    simp only [Nat.card_Icc]
    omega
  calc
    ∑ r ∈ Finset.Icc 1 (N - 1), ((N - r : ℕ) : ℝ) ≤
        ∑ _r ∈ Finset.Icc 1 (N - 1), (N : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact_mod_cast Nat.sub_le N r
    _ = ((Finset.Icc 1 (N - 1)).card : ℝ) * (N : ℝ) := by
      simp
    _ ≤ (N : ℝ) * (N : ℝ) := by
      gcongr
    _ = (N : ℝ) ^ 2 := by ring

/-- T1's exact ordered, diagonal-inclusive decomposition gives this aggregate
upper bound. The first term is the diagonal; the factor two retains both
orders of every positive lag. -/
theorem Q_pi_le_lagDiscrepancy_aggregate (n N : ℕ)
    (hn : 1 ≤ n) (hN : 1 ≤ N) :
    (Q_pi n N : ℝ) ≤ (N : ℝ) +
      2 * ∑ r ∈ Finset.Icc 1 (N - 1),
        (2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
          lagCircularIntervalDiscrepancy N r (decimalRadius n)) := by
  rw [LagDecomposition.Q_pi_orderedPair_lag_decomposition n N hn hN]
  push_cast
  gcongr with r hr
  exact lagNearReturnCount_le_expected_add_discrepancy n N r

/-- A coarser aggregate form with the interval-length sum bounded explicitly
by `N²`. -/
theorem Q_pi_le_lagDiscrepancy_sum (n N : ℕ)
    (hn : 1 ≤ n) (hN : 1 ≤ N) :
    (Q_pi n N : ℝ) ≤ (N : ℝ) +
      4 * decimalRadius n * (N : ℝ) ^ 2 +
        2 * ∑ r ∈ Finset.Icc 1 (N - 1),
          lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
  have hsplit :
      ∑ r ∈ Finset.Icc 1 (N - 1),
          (2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) =
        2 * decimalRadius n *
          (∑ r ∈ Finset.Icc 1 (N - 1), ((N - r : ℕ) : ℝ)) +
        ∑ r ∈ Finset.Icc 1 (N - 1),
          lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
  calc
    (Q_pi n N : ℝ) ≤ (N : ℝ) +
        2 * ∑ r ∈ Finset.Icc 1 (N - 1),
          (2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) :=
      Q_pi_le_lagDiscrepancy_aggregate n N hn hN
    _ = (N : ℝ) +
        4 * decimalRadius n *
          (∑ r ∈ Finset.Icc 1 (N - 1), ((N - r : ℕ) : ℝ)) +
        2 * ∑ r ∈ Finset.Icc 1 (N - 1),
          lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
      rw [hsplit]
      ring
    _ ≤ (N : ℝ) + 4 * decimalRadius n * (N : ℝ) ^ 2 +
        2 * ∑ r ∈ Finset.Icc 1 (N - 1),
          lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
      gcongr
      · exact mul_nonneg (by norm_num) (decimalRadius_pos n).le
      · exact lagLengthSum_le_sq N

/-- The exponential radius is eventually small relative to `1/(8 A n)`. -/
lemma eventually_eight_mul_scaled_decimalRadius_le_one (A : ℕ) (_hA : 1 ≤ A) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      8 * (A : ℝ) * (n : ℝ) * decimalRadius n ≤ 1 := by
  have ht : Tendsto
      (fun n : ℕ => (n : ℝ) * ((10 : ℝ)⁻¹) ^ n)
      atTop (nhds 0) := by
    exact tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hscaled : Tendsto
      (fun n : ℕ => (8 * (A : ℝ)) * ((n : ℝ) * ((10 : ℝ)⁻¹) ^ n))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul ht : Tendsto
      (fun n : ℕ => (8 * (A : ℝ)) * ((n : ℝ) * ((10 : ℝ)⁻¹) ^ n))
      atTop (nhds ((8 * (A : ℝ)) * 0)))
  have hevent : ∀ᶠ n : ℕ in atTop,
      (8 * (A : ℝ)) * ((n : ℝ) * ((10 : ℝ)⁻¹) ^ n) < 1 :=
    (tendsto_order.1 hscaled).2 1 (by norm_num)
  obtain ⟨m, hm⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  have hmn : m ≤ n := (le_max_right 1 m).trans hn
  have hstrict := hm n hmn
  simpa [decimalRadius, inv_pow, mul_assoc] using hstrict.le

/-- A bound on the aggregate unnormalized lag discrepancy implies C1 with its
literal canonical quantifier order. The constants reserve `1/8`, `1/2`, and
`1/4` of `N²` for the diagonal, reference interval lengths, and discrepancies.
This theorem does not assert the hypothesis for pi. -/
theorem aggregateLagDiscrepancyBound_implies_canonical_C1
    (haggregate :
      ∀ A : ℕ, 1 ≤ A → ∃ nDisc : ℕ, 1 ≤ nDisc ∧
        ∀ n : ℕ, nDisc ≤ n → ∃ N : ℕ, 1 ≤ N ∧
          8 * A * n ≤ N ∧
          (∑ r ∈ Finset.Icc 1 (N - 1),
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
              (N : ℝ) ^ 2 / (8 * (A : ℝ) * (n : ℝ))) :
    ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2 := by
  intro A hA
  obtain ⟨nDisc, hnDisc, hDisc⟩ := haggregate A hA
  obtain ⟨nRadius, hnRadius, hRadius⟩ :=
    eventually_eight_mul_scaled_decimalRadius_le_one A hA
  refine ⟨max nDisc nRadius, hnDisc.trans (le_max_left _ _), ?_⟩
  intro n hnmax
  have hnDiscN : nDisc ≤ n := (le_max_left nDisc nRadius).trans hnmax
  have hnRadiusN : nRadius ≤ n := (le_max_right nDisc nRadius).trans hnmax
  have hn : 1 ≤ n := hnDisc.trans hnDiscN
  obtain ⟨N, hN, hNlarge, hDiscSum⟩ := hDisc n hnDiscN
  refine ⟨N, hN, ?_⟩
  have hAreal : 0 < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hNlargeReal : 8 * (A : ℝ) * (n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hNlarge
  have hRadiusN := hRadius n hnRadiusN
  have hdiagTerm :
      (A : ℝ) * (n : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ 2 / 8 := by
    have hm := mul_le_mul_of_nonneg_right hNlargeReal
      (show 0 ≤ (N : ℝ) by positivity)
    nlinarith
  have hradiusTerm :
      4 * ((A : ℝ) * (n : ℝ)) * decimalRadius n * (N : ℝ) ^ 2 ≤
        (N : ℝ) ^ 2 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hRadiusN (sq_nonneg (N : ℝ))
    nlinarith
  have hdiscTerm :
      2 * ((A : ℝ) * (n : ℝ)) *
          (∑ r ∈ Finset.Icc 1 (N - 1),
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤ (N : ℝ) ^ 2 / 4 := by
    calc
      2 * ((A : ℝ) * (n : ℝ)) *
          (∑ r ∈ Finset.Icc 1 (N - 1),
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
          2 * ((A : ℝ) * (n : ℝ)) *
            ((N : ℝ) ^ 2 / (8 * (A : ℝ) * (n : ℝ))) := by
        gcongr
      _ = (N : ℝ) ^ 2 / 4 := by
        field_simp
        <;> ring
  have hQ := Q_pi_le_lagDiscrepancy_sum n N hn hN
  have hscaled :
      (A : ℝ) * (n : ℝ) * (Q_pi n N : ℝ) ≤ (N : ℝ) ^ 2 := by
    calc
      (A : ℝ) * (n : ℝ) * (Q_pi n N : ℝ) ≤
          ((A : ℝ) * (n : ℝ)) *
            ((N : ℝ) + 4 * decimalRadius n * (N : ℝ) ^ 2 +
              2 * ∑ r ∈ Finset.Icc 1 (N - 1),
                lagCircularIntervalDiscrepancy N r (decimalRadius n)) := by
        exact mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = (A : ℝ) * (n : ℝ) * (N : ℝ) +
          4 * ((A : ℝ) * (n : ℝ)) * decimalRadius n * (N : ℝ) ^ 2 +
          2 * ((A : ℝ) * (n : ℝ)) *
            (∑ r ∈ Finset.Icc 1 (N - 1),
              lagCircularIntervalDiscrepancy N r (decimalRadius n)) := by ring
      _ ≤ (N : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hscaled

/-- If every positive lag has discrepancy at most `c` times its orbit length,
then the ordered count has the displayed diagonal, interval-length, and
discrepancy contributions. -/
lemma Q_pi_le_of_normalized_lagDiscrepancy_le (n N : ℕ) (c : ℝ)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hdisc : ∀ r ∈ Finset.Icc 1 (N - 1),
      lagCircularIntervalDiscrepancy N r (decimalRadius n) ≤
        c * ((N - r : ℕ) : ℝ)) :
    (Q_pi n N : ℝ) ≤ (N : ℝ) +
      4 * decimalRadius n * (N : ℝ) ^ 2 + 2 * c * (N : ℝ) ^ 2 := by
  have hsum :
      ∑ r ∈ Finset.Icc 1 (N - 1),
          (2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
        (2 * decimalRadius n + c) * (N : ℝ) ^ 2 := by
    calc
      ∑ r ∈ Finset.Icc 1 (N - 1),
          (2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
          ∑ r ∈ Finset.Icc 1 (N - 1),
            (2 * decimalRadius n + c) * ((N - r : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        have := hdisc r hr
        nlinarith
      _ = (2 * decimalRadius n + c) *
          ∑ r ∈ Finset.Icc 1 (N - 1), ((N - r : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * decimalRadius n + c) * (N : ℝ) ^ 2 := by
        gcongr
        · nlinarith [decimalRadius_pos n]
        · exact lagLengthSum_le_sq N
  calc
    (Q_pi n N : ℝ) ≤ (N : ℝ) +
        2 * ∑ r ∈ Finset.Icc 1 (N - 1),
          (2 * decimalRadius n * ((N - r : ℕ) : ℝ) +
            lagCircularIntervalDiscrepancy N r (decimalRadius n)) :=
      Q_pi_le_lagDiscrepancy_aggregate n N hn hN
    _ ≤ (N : ℝ) + 2 * ((2 * decimalRadius n + c) * (N : ℝ) ^ 2) := by
      gcongr
    _ = (N : ℝ) + 4 * decimalRadius n * (N : ℝ) ^ 2 +
        2 * c * (N : ℝ) ^ 2 := by ring

/-- Literal failure of canonical C1 forces arbitrarily large scales at which
every `N ≥ 8 A n` has a positive lag whose discrepancy per orbit point is at
least `1/(8 A n)`. The premise repeats the canonical quantifiers literally. -/
theorem not_canonical_C1_implies_arbitrarily_large_badLag
    (hnot : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧
        ∀ N : ℕ, 8 * A * n ≤ N →
          ∃ r ∈ Finset.Icc 1 (N - 1),
            1 / (8 * (A : ℝ) * (n : ℝ)) ≤
              lagCircularIntervalDiscrepancy N r (decimalRadius n) /
                ((N - r : ℕ) : ℝ) := by
  push Not at hnot
  obtain ⟨A, hA, hbad⟩ := hnot
  obtain ⟨nRadius, hnRadius, hRadius⟩ :=
    eventually_eight_mul_scaled_decimalRadius_le_one A hA
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  have hmax : 1 ≤ max n0 nRadius := hn0.trans (le_max_left n0 nRadius)
  obtain ⟨n, hnmax, hbadN⟩ := hbad (max n0 nRadius) hmax
  have hn0n : n0 ≤ n := (le_max_left n0 nRadius).trans hnmax
  have hnRadiusN : nRadius ≤ n := (le_max_right n0 nRadius).trans hnmax
  have hn : 1 ≤ n := hn0.trans hn0n
  have hRadiusN := hRadius n hnRadiusN
  refine ⟨n, hn0n, hn, ?_⟩
  intro N hNlarge
  have hN : 1 ≤ N := by
    have hAn : 1 ≤ A * n := by
      have : 0 < A * n := Nat.mul_pos (by omega) (by omega)
      omega
    have h8 : 1 ≤ 8 * A * n := by
      calc
        1 ≤ 8 := by norm_num
        _ ≤ 8 * (A * n) := Nat.mul_le_mul_left 8 hAn
        _ = 8 * A * n := by ring
    exact h8.trans hNlarge
  by_contra hnone
  push Not at hnone
  have hdisc : ∀ r ∈ Finset.Icc 1 (N - 1),
      lagCircularIntervalDiscrepancy N r (decimalRadius n) ≤
        (1 / (8 * (A : ℝ) * (n : ℝ))) * ((N - r : ℕ) : ℝ) := by
    intro r hr
    have hrBounds := Finset.mem_Icc.mp hr
    have hlengthNat : 0 < N - r := by omega
    have hlength : 0 < (((N - r : ℕ) : ℝ)) := by exact_mod_cast hlengthNat
    have hsmall := hnone r hr
    exact ((div_lt_iff₀ hlength).mp hsmall).le
  have hAreal : 0 < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hc : 0 ≤ 1 / (8 * (A : ℝ) * (n : ℝ)) := by positivity
  have hQupper := Q_pi_le_of_normalized_lagDiscrepancy_le n N
    (1 / (8 * (A : ℝ) * (n : ℝ))) hn hN hc hdisc
  have hNlargeReal : 8 * (A : ℝ) * (n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hNlarge
  have hbadReal : (N : ℝ) ^ 2 <
      (A : ℝ) * (n : ℝ) * (Q_pi n N : ℝ) := by
    exact_mod_cast hbadN N hN
  have hdiagTerm :
      (A : ℝ) * (n : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ 2 / 8 := by
    have hm := mul_le_mul_of_nonneg_right hNlargeReal
      (show 0 ≤ (N : ℝ) by positivity)
    nlinarith
  have hradiusTerm :
      4 * ((A : ℝ) * (n : ℝ)) * decimalRadius n * (N : ℝ) ^ 2 ≤
        (N : ℝ) ^ 2 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hRadiusN
      (sq_nonneg (N : ℝ))
    nlinarith
  have hdiscrepancyTerm :
      2 * ((A : ℝ) * (n : ℝ)) *
          (1 / (8 * (A : ℝ) * (n : ℝ))) * (N : ℝ) ^ 2 =
        (N : ℝ) ^ 2 / 4 := by
    field_simp
    <;> ring
  have hscaledUpper :
      (A : ℝ) * (n : ℝ) * (Q_pi n N : ℝ) ≤
        (7 / 8 : ℝ) * (N : ℝ) ^ 2 := by
    calc
      (A : ℝ) * (n : ℝ) * (Q_pi n N : ℝ) ≤
          ((A : ℝ) * (n : ℝ)) *
            ((N : ℝ) + 4 * decimalRadius n * (N : ℝ) ^ 2 +
              2 * (1 / (8 * (A : ℝ) * (n : ℝ))) * (N : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hQupper (by positivity)
      _ = (A : ℝ) * (n : ℝ) * (N : ℝ) +
          4 * ((A : ℝ) * (n : ℝ)) * decimalRadius n * (N : ℝ) ^ 2 +
          2 * ((A : ℝ) * (n : ℝ)) *
            (1 / (8 * (A : ℝ) * (n : ℝ))) * (N : ℝ) ^ 2 := by ring
      _ ≤ (7 / 8 : ℝ) * (N : ℝ) ^ 2 := by
        rw [hdiscrepancyTerm]
        nlinarith
  have hNsqPos : 0 < (N : ℝ) ^ 2 := by positivity
  nlinarith

end LagDiscrepancy
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.LagDiscrepancy.Q_pi_le_lagDiscrepancy_aggregate
#print axioms DecimalFactorComplexity.LagDiscrepancy.Q_pi_le_lagDiscrepancy_sum
#print axioms DecimalFactorComplexity.LagDiscrepancy.aggregateLagDiscrepancyBound_implies_canonical_C1
#print axioms DecimalFactorComplexity.LagDiscrepancy.not_canonical_C1_implies_arbitrarily_large_badLag
