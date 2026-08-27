import TheoryLib.PiDecimalFactorComplexity.T8PiLacunaryNearReturns

/-!
# Exact ordered-pair lag decomposition

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

The indices in this file are zero-based. All pair counts are over ordered pairs,
include every diagonal pair, and use the strict circle-distance inequality from
T8. The generic definition `Q_x` is specialized below to T8's existing `Q_pi`;
the latter is imported rather than redefined. The named decomposition theorems
assume `1 ≤ n` and `1 ≤ N`, exactly as in the canonical question.
-/

namespace DecimalFactorComplexity
namespace LagDecomposition

/-- The ordered, diagonal-inclusive near-return count for an arbitrary real
point `x`, with exactly T8's orientation and strict threshold. -/
noncomputable def Q_x (x : ℝ) (n N : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    circleDistance
      (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * x) <
        ((10 : ℝ) ^ n)⁻¹).card

/-- The custom circle distance inherited from T8 is invariant under negation. -/
lemma circleDistance_neg (x : ℝ) : circleDistance (-x) = circleDistance x := by
  unfold circleDistance
  apply congrArg sInf
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    simp only [Int.cast_neg]
    rw [show -x - (z : ℝ) = -(x - (-(z : ℝ))) by ring, abs_neg]
  · rintro ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    simp only [Int.cast_neg]
    rw [show x - (z : ℝ) = -(-x - (-(z : ℝ))) by ring, abs_neg]

/-- Factoring the difference of two powers at positive lag `r`. -/
lemma pow_lag_factorization (x : ℝ) (j r : ℕ) :
    (((10 : ℝ) ^ (j + r) - (10 : ℝ) ^ j) * x) =
      ((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * x) := by
  rw [pow_add]
  ring

/-- A finite combinatorial decomposition for any symmetric, diagonal-valid
predicate on zero-based natural indices. -/
theorem symmetric_orderedPair_card_eq_lag_sum
    (P : ℕ → ℕ → Prop) [DecidableRel P]
    (hsymm : ∀ i j, P i j ↔ P j i) (hdiag : ∀ i, P i i) (N : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
        P (ij.1 : ℕ) (ij.2 : ℕ)).card =
      N + 2 * ∑ r ∈ Finset.Icc 1 (N - 1),
        ((Finset.range (N - r)).filter fun j => P j (j + r)).card := by
  classical
  let S := (Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    P (ij.1 : ℕ) (ij.2 : ℕ)
  let D := S.filter fun ij => ij.1 = ij.2
  let U := S.filter fun ij => ij.1 < ij.2
  let L := S.filter fun ij => ij.2 < ij.1
  have hpartition : S = (D ∪ U) ∪ L := by
    ext ij
    simp only [S, D, U, L, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hP
      rcases lt_trichotomy ij.1 ij.2 with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hP, hlt⟩)
      · exact Or.inl (Or.inl ⟨hP, heq⟩)
      · exact Or.inr ⟨hP, hgt⟩
    · rintro ((⟨hP, _⟩ | ⟨hP, _⟩) | ⟨hP, _⟩) <;> exact hP
  have hDU : Disjoint D U := by
    refine Finset.disjoint_left.mpr ?_
    intro ij hijD hijU
    simp only [D, Finset.mem_filter] at hijD
    simp only [U, Finset.mem_filter] at hijU
    omega
  have hDUL : Disjoint (D ∪ U) L := by
    refine Finset.disjoint_left.mpr ?_
    intro ij hijDU hijL
    simp only [Finset.mem_union] at hijDU
    simp only [D, U, L, Finset.mem_filter] at hijDU hijL
    rcases hijDU with hijD | hijU <;> omega
  have hDcard : D.card = N := by
    have hDeq : D = (Finset.univ : Finset (Fin N)).diag := by
      ext ij
      simp only [D, S, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_diag]
      constructor
      · rintro ⟨_, hij⟩
        exact hij
      · intro hij
        rw [hij]
        exact ⟨hdiag (ij.2 : ℕ), rfl⟩
    rw [hDeq, Finset.diag_card, Finset.card_univ, Fintype.card_fin]
  have hULcard : U.card = L.card := by
    apply Finset.card_bijective Prod.swap Prod.swap_bijective
    intro ij
    simp only [U, L, S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hP, hlt⟩
      exact ⟨(hsymm _ _).mp hP, hlt⟩
    · rintro ⟨hP, hlt⟩
      exact ⟨(hsymm _ _).mpr hP, hlt⟩
  have hUfiber :
      U.card = ∑ r ∈ Finset.Icc 1 (N - 1),
        (U.filter fun ij => (ij.2 : ℕ) - (ij.1 : ℕ) = r).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro ij hijU
    change ij ∈ U at hijU
    change (ij.2 : ℕ) - (ij.1 : ℕ) ∈ Finset.Icc 1 (N - 1)
    rw [Finset.mem_Icc]
    simp only [U, Finset.mem_filter] at hijU
    constructor <;> omega
  have hfiber (r : ℕ) (hr : r ∈ Finset.Icc 1 (N - 1)) :
      (U.filter fun ij => (ij.2 : ℕ) - (ij.1 : ℕ) = r).card =
        ((Finset.range (N - r)).filter fun j => P j (j + r)).card := by
    have hrpos : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    let A := U.filter fun ij => (ij.2 : ℕ) - (ij.1 : ℕ) = r
    let B := (Finset.range (N - r)).filter fun j => P j (j + r)
    change A.card = B.card
    refine Finset.card_bij (fun ij _ => (ij.1 : ℕ)) ?_ ?_ ?_
    · intro ij hijA
      simp only [A, U, S, Finset.mem_filter, Finset.mem_univ, true_and] at hijA
      simp only [B, Finset.mem_filter, Finset.mem_range]
      rcases hijA with ⟨⟨hP, hlt⟩, hdiff⟩
      have hadd : (ij.2 : ℕ) = (ij.1 : ℕ) + r := by omega
      constructor
      · omega
      · simpa [hadd] using hP
    · intro a ha b hb hab
      simp only [A, U, S, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rcases ha with ⟨⟨_, halts⟩, hadiff⟩
      rcases hb with ⟨⟨_, hblts⟩, hbdiff⟩
      have haadd : (a.2 : ℕ) = (a.1 : ℕ) + r := by omega
      have hbadd : (b.2 : ℕ) = (b.1 : ℕ) + r := by omega
      change (a.1 : ℕ) = (b.1 : ℕ) at hab
      apply Prod.ext
      · exact Fin.ext hab
      · apply Fin.ext
        rw [haadd, hbadd, hab]
    · intro j hjB
      simp only [B, Finset.mem_filter, Finset.mem_range] at hjB
      rcases hjB with ⟨hjbound, hP⟩
      have hjN : j < N := by omega
      have hjrN : j + r < N := by omega
      let a : Fin N := ⟨j, hjN⟩
      let b : Fin N := ⟨j + r, hjrN⟩
      refine ⟨(a, b), ?_, rfl⟩
      simp only [A, Finset.mem_filter]
      constructor
      · simp only [U, S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact hP
        · exact Fin.mk_lt_mk.mpr (by omega)
      · dsimp [a, b]
        omega
  calc
    ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
        P (ij.1 : ℕ) (ij.2 : ℕ)).card = S.card := rfl
    _ = D.card + U.card + L.card := by
      rw [hpartition, Finset.card_union_of_disjoint hDUL,
        Finset.card_union_of_disjoint hDU]
    _ = N + 2 * U.card := by omega
    _ = N + 2 * ∑ r ∈ Finset.Icc 1 (N - 1),
        (U.filter fun ij => (ij.2 : ℕ) - (ij.1 : ℕ) = r).card := by rw [hUfiber]
    _ = N + 2 * ∑ r ∈ Finset.Icc 1 (N - 1),
        ((Finset.range (N - r)).filter fun j => P j (j + r)).card := by
      congr 2
      exact Finset.sum_congr rfl hfiber

/-- Exact lag decomposition of the generic ordered-pair near-return count on
the canonical positive domain. The sum has lags `1 ≤ r ≤ N-1`; its inner
indices are exactly `j = 0, ..., N-r-1`. -/
theorem Q_x_orderedPair_lag_decomposition (x : ℝ) (n N : ℕ)
    (_hn : 1 ≤ n) (_hN : 1 ≤ N) :
    Q_x x n N =
      N + 2 * ∑ r ∈ Finset.Icc 1 (N - 1),
        ((Finset.range (N - r)).filter fun j =>
          circleDistance
            ((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * x) <
              ((10 : ℝ) ^ n)⁻¹).card := by
  classical
  let P : ℕ → ℕ → Prop := fun i j =>
    circleDistance (((10 : ℝ) ^ j - (10 : ℝ) ^ i) * x) <
      ((10 : ℝ) ^ n)⁻¹
  have hsymm : ∀ i j, P i j ↔ P j i := by
    intro i j
    dsimp [P]
    rw [show ((10 : ℝ) ^ i - (10 : ℝ) ^ j) * x =
      -(((10 : ℝ) ^ j - (10 : ℝ) ^ i) * x) by ring, circleDistance_neg]
  have hdiag : ∀ i, P i i := by
    intro i
    dsimp [P]
    have hzero : circleDistance (0 : ℝ) ≤ 0 := by
      simpa using circleDistance_le_abs_sub_int (0 : ℝ) (0 : ℤ)
    have hthreshold : 0 < ((10 : ℝ) ^ n)⁻¹ := by positivity
    simpa using hzero.trans_lt hthreshold
  rw [Q_x]
  rw [symmetric_orderedPair_card_eq_lag_sum P hsymm hdiag N]
  apply congrArg (fun t => N + 2 * t)
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  simp only [P]
  rw [pow_lag_factorization]

/-- T8's canonical count is the generic count specialized to `Real.pi`. -/
theorem Q_pi_eq_Q_x (n N : ℕ) : Q_pi n N = Q_x Real.pi n N := by
  rfl

/-- Exact lag decomposition in T8's `Q_pi` conventions on the canonical
positive domain: ordered pairs, diagonals included, zero-based indices, and
strict circle distance. -/
theorem Q_pi_orderedPair_lag_decomposition (n N : ℕ)
    (hn : 1 ≤ n) (hN : 1 ≤ N) :
    Q_pi n N =
      N + 2 * ∑ r ∈ Finset.Icc 1 (N - 1),
        ((Finset.range (N - r)).filter fun j =>
          circleDistance
            ((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi) <
              ((10 : ℝ) ^ n)⁻¹).card := by
  rw [Q_pi_eq_Q_x]
  exact Q_x_orderedPair_lag_decomposition Real.pi n N hn hN

end LagDecomposition
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.LagDecomposition.circleDistance_neg
#print axioms DecimalFactorComplexity.LagDecomposition.symmetric_orderedPair_card_eq_lag_sum
#print axioms DecimalFactorComplexity.LagDecomposition.Q_x_orderedPair_lag_decomposition
#print axioms DecimalFactorComplexity.LagDecomposition.Q_pi_eq_Q_x
#print axioms DecimalFactorComplexity.LagDecomposition.Q_pi_orderedPair_lag_decomposition
