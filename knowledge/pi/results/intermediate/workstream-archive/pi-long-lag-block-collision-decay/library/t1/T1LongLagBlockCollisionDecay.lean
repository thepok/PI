import TheoryLib.PiPositiveLowerBlockDensity.T26T26LongLagResidualReduction
import TheoryLib.PiLacunaryNearReturnSparsity.T1LagDecomposition
import TheoryLib.PiPositiveLowerBlockDensity.T12T12OverlappingForbiddenWordDimension

/-!
# T1: canonical long-lag decimal block collisions

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

The canonical count uses ordered pairs.  The auxiliary lag-sum form makes the
diagonal and the at-most `2 * N * m` ordered short-lag pairs explicit.
-/

noncomputable section

open Filter Finset

namespace Theory.PiDigits.LongLagBlockCollisionDecay

open DecimalFactorComplexity
open DecimalFactorComplexity.FiniteCylinderEnergy
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T9
open Theory.PiDigits.PositiveLowerBlockDensity.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T13
open Theory.PiDigits.PositiveLowerBlockDensity.T15
open Theory.PiDigits.PositiveLowerBlockDensity.T23
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The length-`m` decimal cylinder label of the block starting at `i`.
Via `piCylinderCode`, this is the tuple of the `m` decimal digits, encoded in
base ten with leading zeroes retained. -/
def B_pi (i m : ℕ) : Fin (10 ^ m) := piCylinderCode m i

/-- Ordered equal-block pairs at the canonical nonoverlapping lags.  The
condition `m ≤ Nat.dist i j` is the literal `|i-j| ≥ m` convention. -/
def R_pi (m N : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    m ≤ Nat.dist (ij.1 : ℕ) (ij.2 : ℕ) ∧
      B_pi ij.1 m = B_pi ij.2 m).card

/-- The positive-lag half of the canonical ordered count. -/
def longLagCollisionSum (m N : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc m (N - 1),
    ((Finset.range (N - r)).filter fun i => B_pi i m = B_pi (i + r) m).card

/-- Positive lags below the block length. -/
def shortLagCollisionSum (m N : ℕ) : ℕ :=
  ∑ r ∈ (Finset.Icc 1 (N - 1)).filter (fun r => r < m),
    ((Finset.range (N - r)).filter fun i => B_pi i m = B_pi (i + r) m).card

/-- The canonical predicate, including the additive finite-sample term and
the one constant for all positive `m` and `N`. -/
def PiLongLagBlockCollisionDecay : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        (R_pi m N : ℝ) ≤
          C * ((N : ℝ) + (N : ℝ) ^ 2 *
            (10 : ℝ) ^ (-s * (m : ℝ)))

/-- Quantifier audit for the canonical predicate. -/
theorem piLongLagBlockCollisionDecay_iff_quantifiers :
    PiLongLagBlockCollisionDecay ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            (R_pi m N : ℝ) ≤
              C * ((N : ℝ) + (N : ℝ) ^ 2 *
                (10 : ℝ) ^ (-s * (m : ℝ))) := by
  rfl

/-- The ordered-pair definition is exactly twice its positive-lag half. -/
theorem R_pi_eq_two_mul_longLagCollisionSum
    {m N : ℕ} (hm : 1 ≤ m) :
    R_pi m N = 2 * longLagCollisionSum m N := by
  classical
  let P : ℕ → ℕ → Prop := fun i j =>
    i = j ∨ (m ≤ Nat.dist i j ∧ B_pi i m = B_pi j m)
  have hsymm : ∀ i j, P i j ↔ P j i := by
    intro i j
    constructor
    · rintro (h | ⟨hd, hb⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨by simpa [Nat.dist_comm] using hd, hb.symm⟩
    · rintro (h | ⟨hd, hb⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨by simpa [Nat.dist_comm] using hd, hb.symm⟩
  have hdiag : ∀ i, P i i := fun i => Or.inl rfl
  have hlag := DecimalFactorComplexity.LagDecomposition.symmetric_orderedPair_card_eq_lag_sum
    P hsymm hdiag N
  let A := ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    P ij.1 ij.2)
  let D := (Finset.univ : Finset (Fin N)).diag
  let L := ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    m ≤ Nat.dist (ij.1 : ℕ) (ij.2 : ℕ) ∧
      B_pi ij.1 m = B_pi ij.2 m)
  have hpartition : A = D ∪ L := by
    ext ij
    simp only [A, D, L, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_diag, Finset.mem_union, P]
    constructor
    · rintro (h | h)
      · left
        exact Fin.ext h
      · exact Or.inr h
    · rintro (h | h)
      · left
        exact congrArg Fin.val h
      · exact Or.inr h
  have hdisjoint : Disjoint D L := by
    refine Finset.disjoint_left.mpr ?_
    intro ij hijD hijL
    simp only [D, Finset.mem_diag] at hijD
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hijL
    rcases ij with ⟨i, j⟩
    have heq : i = j := by simpa using hijD.2
    subst j
    have hzero : m ≤ 0 := by simpa using hijL.1
    omega
  have hAcard : A.card = N + R_pi m N := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
    simp [D, L, R_pi]
  have hsum :
      (∑ r ∈ Finset.Icc 1 (N - 1),
        ((Finset.range (N - r)).filter fun j => P j (j + r)).card) =
        longLagCollisionSum m N := by
    unfold longLagCollisionSum
    rw [show Finset.Icc m (N - 1) =
        (Finset.Icc 1 (N - 1)).filter (fun r => m ≤ r) by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_filter]
      omega]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    by_cases hmr : m ≤ r
    · rw [if_pos hmr]
      apply congrArg Finset.card
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, P]
      constructor
      · rintro ⟨hj, h | ⟨_, hb⟩⟩
        · omega
        · exact ⟨hj, hb⟩
      · rintro ⟨hj, hb⟩
        exact ⟨hj, Or.inr ⟨by
          have hdist : Nat.dist j (j + r) = r := by
            rw [Nat.dist_eq_sub_of_le (Nat.le_add_right j r)]
            omega
          simpa [hdist] using hmr, hb⟩⟩
    · rw [if_neg hmr, Finset.card_eq_zero]
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, P]
      constructor
      · rintro ⟨_, h | ⟨hd, _⟩⟩
        · omega
        · have hdist : Nat.dist j (j + r) = r := by
            rw [Nat.dist_eq_sub_of_le (Nat.le_add_right j r)]
            omega
          have hmr' : m ≤ r := by simpa [hdist] using hd
          exact (hmr hmr').elim
      · intro h
        simp at h
  have hAcard' : A.card = N + L.card := by
    simpa [R_pi, L] using hAcard
  have hlag' : A.card = N + 2 * longLagCollisionSum m N := by
    simpa [A, hsum] using hlag
  omega

/-- The total finite decimal-cylinder collision energy is the collision count
of all ordered equal-block pairs, including the diagonal. -/
theorem piCylinderCollisionEnergy_eq_blockPairCount (m N : ℕ) :
    piCylinderCollisionEnergy m N =
      ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
        B_pi ij.1 m = B_pi ij.2 m).card := by
  classical
  exact piCylinderCollisionEnergy_eq_equalPairs_card m N

/-- The positive short-lag half has at most `m * N` pairs: there are at most
`m` lags, and each lag has at most `N` first starts. -/
theorem shortLagCollisionSum_le_mul (m N : ℕ) :
    shortLagCollisionSum m N ≤ m * N := by
  classical
  let S := (Finset.Icc 1 (N - 1)).filter (fun r => r < m)
  have hcard : S.card ≤ m := by
    calc
      S.card ≤ (Finset.range m).card := by
        apply Finset.card_le_card
        intro r hr
        rw [Finset.mem_range]
        exact (Finset.mem_filter.mp hr).2
      _ = m := Finset.card_range _
  have hsum :
      (∑ r ∈ S,
        ((Finset.range (N - r)).filter fun i =>
          B_pi i m = B_pi (i + r) m).card) ≤
        ∑ _r ∈ S, N := by
    apply Finset.sum_le_sum
    intro r _hr
    exact (Finset.card_filter_le _ _).trans
      (by simp)
  unfold shortLagCollisionSum
  change (∑ r ∈ S,
      ((Finset.range (N - r)).filter fun i =>
        B_pi i m = B_pi (i + r) m).card) ≤ m * N
  calc
    _ ≤ ∑ _r ∈ S, N := hsum
    _ = S.card * N := by simp
    _ ≤ m * N := Nat.mul_le_mul_right N hcard

/-- The exact long/short lag comparison.  The `N` term is the ordered
diagonal, and `2 * N * m` bounds both orientations of all positive short
lags. -/
theorem piCylinderCollisionEnergy_le_R_pi_add_diagonal_add_short
    {m N : ℕ} (hm : 1 ≤ m) :
    piCylinderCollisionEnergy m N ≤ R_pi m N + N + 2 * N * m := by
  classical
  let P : ℕ → ℕ → Prop := fun i j => B_pi i m = B_pi j m
  have hsymm : ∀ i j, P i j ↔ P j i := by
    intro i j
    constructor <;> intro h <;> exact h.symm
  have hdiag : ∀ i, P i i := fun i => rfl
  have hlag := DecimalFactorComplexity.LagDecomposition.symmetric_orderedPair_card_eq_lag_sum
    P hsymm hdiag N
  let S := (Finset.Icc 1 (N - 1)).filter (fun r => r < m)
  let L := Finset.Icc m (N - 1)
  have hcover : Finset.Icc 1 (N - 1) = S ∪ L := by
    ext r
    simp only [S, L, Finset.mem_Icc, Finset.mem_filter, Finset.mem_union]
    omega
  have hdisjoint : Disjoint S L := by
    refine Finset.disjoint_left.mpr ?_
    intro r hrS hrL
    have hs := (Finset.mem_filter.mp hrS).2
    have hl := (Finset.mem_Icc.mp hrL).1
    omega
  have hsum :
      (∑ r ∈ Finset.Icc 1 (N - 1),
        ((Finset.range (N - r)).filter fun i => P i (i + r)).card) =
        shortLagCollisionSum m N + longLagCollisionSum m N := by
    rw [hcover, Finset.sum_union hdisjoint]
    unfold shortLagCollisionSum longLagCollisionSum S L P
    rfl
  have hshort := shortLagCollisionSum_le_mul m N
  have hR := R_pi_eq_two_mul_longLagCollisionSum (N := N) hm
  have hshort' : 2 * shortLagCollisionSum m N ≤ 2 * N * m := by
    calc
      2 * shortLagCollisionSum m N ≤ 2 * (m * N) :=
        Nat.mul_le_mul_left 2 hshort
      _ = 2 * N * m := by ac_rfl
  rw [piCylinderCollisionEnergy_eq_blockPairCount]
  change ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    P ij.1 ij.2).card ≤ R_pi m N + N + 2 * N * m
  rw [hlag, hsum, hR]
  omega

/-- Normalized form of the exact comparison. -/
theorem E_pi_le_R_pi_add_diagonal_add_short
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    T23.E_pi m N ≤
      ((R_pi m N + N + 2 * N * m : ℕ) : ℝ) / (N : ℝ) ^ 2 := by
  have hden : 0 < (N : ℝ) ^ 2 := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hN
    positivity
  rw [T23.E_pi_eq_normalizedPiCylinderCollisionEnergy]
  unfold normalizedPiCylinderCollisionEnergy
  apply (div_le_div_iff_of_pos_right hden).2
  exact_mod_cast piCylinderCollisionEnergy_le_R_pi_add_diagonal_add_short hm

/-- The canonical ordered long-lag collision decay implies the accepted
positive-lower-block-density predicate.  The proof selects a sufficiently
large low-frequency prefix, so the exact short-lag term is negligible rather
than being incorrectly absorbed into a uniform-in-`m` energy estimate. -/
theorem piLongLagBlockCollisionDecay_implies_piPositiveLowerBlockDensity
    (hDecay : PiLongLagBlockCollisionDecay) :
    PiPositiveLowerBlockDensity := by
  by_contra hnot
  obtain ⟨ell, hell, v, hzero⟩ := not_C1_exists_zero_liminf hnot
  let s := forbiddenDecayExponent v
  have hs : 0 < s ∧ s < 1 := by
    simpa [s] using forbiddenDecayExponent_pos_lt_one hell v
  obtain ⟨C, hC, hbound⟩ := hDecay s hs.1 hs.2
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨j, hj, hdecaySmall⟩ :=
    exists_twoBlockScale_forbidden_energy_small hell v C hCpos
  let m := (2 * ell) * j
  have hm : 0 < m := by
    dsimp [m]
    positivity
  obtain ⟨N, hroom, hMone, hrare, hshortSmall, hinverse⟩ :=
    zeroLiminf_exists_slowCutoff_shortLag_negligible
      v hzero C hCpos 1 m hm
  let M : ℕ := N + 1 - m
  change 1 ≤ M at hMone
  change (forbiddenWordCount v m : ℝ) *
      (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) <
        (1 : ℝ) / 16 at hshortSmall
  change C * (forbiddenWordCount v m : ℝ) * (1 / (M : ℝ)) <
      (1 : ℝ) / 16 at hinverse
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hMone
  have hlower := contaminatedForbiddenSupport_collision_lower_bound
    hell hm hroom v hrare
  change (1 : ℝ) / 4 ≤
    (forbiddenWordCount v m : ℝ) * T23.E_pi m M at hlower
  have hfinite := E_pi_le_R_pi_add_diagonal_add_short hm hMone
  have hR := hbound m M hm hMone
  have hRnormalized : (R_pi m M : ℝ) / (M : ℝ) ^ 2 ≤
      C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := by
    calc
      (R_pi m M : ℝ) / (M : ℝ) ^ 2 ≤
          (C * ((M : ℝ) + (M : ℝ) ^ 2 *
            (10 : ℝ) ^ (-s * (m : ℝ)))) / (M : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hR (by positivity)
      _ = C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := by
        field_simp [ne_of_gt hMpos]
        ring
  have hsplit :
      ((R_pi m M + M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2 =
        (R_pi m M : ℝ) / (M : ℝ) ^ 2 +
          ((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2 := by
    push_cast
    ring
  have henergyUpper : T23.E_pi m M ≤
      ((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2 +
        C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := by
    calc
      T23.E_pi m M ≤
          ((R_pi m M + M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2 := hfinite
      _ = (R_pi m M : ℝ) / (M : ℝ) ^ 2 +
          ((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2 := hsplit
      _ ≤ ((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2 +
          C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := by
        simpa [add_comm] using add_le_add_left hRnormalized
          (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2)
      _ = ((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2 +
          C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ)) := rfl
  have hcountNat := forbiddenWordCount_twoBlock_mul_le_pow v j
  have hcount : (forbiddenWordCount v m : ℝ) ≤
      (forbiddenQ v : ℝ) ^ j := by
    dsimp [m]
    exact_mod_cast hcountNat
  have hdecayNonneg : 0 ≤
      (10 : ℝ) ^ (-s * (m : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hfirst : C * (forbiddenWordCount v m : ℝ) *
      (10 : ℝ) ^ (-s * (m : ℝ)) < (1 : ℝ) / 16 := by
    apply lt_of_le_of_lt _ hdecaySmall
    have hmul := mul_le_mul_of_nonneg_left hcount hCpos.le
    exact mul_le_mul_of_nonneg_right hmul hdecayNonneg
  have hF : (0 : ℝ) ≤ forbiddenWordCount v m := by positivity
  have henergySmall :
      (forbiddenWordCount v m : ℝ) * T23.E_pi m M < (1 : ℝ) / 4 := by
    calc
      (forbiddenWordCount v m : ℝ) * T23.E_pi m M ≤
          (forbiddenWordCount v m : ℝ) *
            ((((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) +
              C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (M : ℝ))) :=
        mul_le_mul_of_nonneg_left henergyUpper hF
      _ = (forbiddenWordCount v m : ℝ) *
            (((M + 2 * M * m : ℕ) : ℝ) / (M : ℝ) ^ 2) +
          C * (forbiddenWordCount v m : ℝ) *
            (10 : ℝ) ^ (-s * (m : ℝ)) +
          C * (forbiddenWordCount v m : ℝ) * (1 / (M : ℝ)) := by
        ring
      _ < (1 : ℝ) / 16 + (1 : ℝ) / 16 + (1 : ℝ) / 16 :=
        add_lt_add (add_lt_add hshortSmall hfirst) hinverse
      _ < (1 : ℝ) / 4 := by norm_num
  exact (not_lt_of_ge hlower) henergySmall

end Theory.PiDigits.LongLagBlockCollisionDecay

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.piLongLagBlockCollisionDecay_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.R_pi_eq_two_mul_longLagCollisionSum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.piCylinderCollisionEnergy_eq_blockPairCount
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.piCylinderCollisionEnergy_le_R_pi_add_diagonal_add_short
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.E_pi_le_R_pi_add_diagonal_add_short
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.piLongLagBlockCollisionDecay_implies_piPositiveLowerBlockDensity
