import TheoryLib.PiDecimalFactorComplexity.T1DecimalFactorComplexity
import TheoryLib.PiDecimalFactorComplexity.T4FinitePrefixCollisionEnergy
import TheoryLib.PiDigits.T20BaseTenOrbitDensity

/-!
# Decimal collisions and lacunary near returns for pi

Source: `problems/local/pi-decimal-factor-complexity.txt`
SHA-256: `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`

The stream is zero-based: index `0` is the canonical digit `d_1`. Thus
`Fin N` in the imported T4 definitions means exactly the first `N` fractional
starting positions, `0, ..., N - 1`, corresponding to `d_1, ..., d_N`.
All pairs below are ordered pairs in `Fin N x Fin N`; diagonal pairs are
included.

`LacunaryNearReturnC2` is the exact strictly sufficient stronger sibling C2,
not C1 and not canonical A1. C2 is unproved for pi. It is used as a one-way
sufficient hypothesis rather than an equivalent reformulation: this file
proves only `C2 -> C1 -> A1`, states no converse, and makes no unconditional
growth claim for the decimal factor complexity of pi.
-/

namespace DecimalFactorComplexity

/-- The floor-based fractional decimal stream of pi. Index `0` is `d_1`. -/
noncomputable abbrev piDecimalStream : Stream (Fin 10) :=
  Theory.PiDigits.T20.decimalDigit Real.pi

/-- `E_pi(n,N)`, exactly T4's collision energy specialized to the fractional
decimal stream of pi and its first `N` zero-based starts. -/
noncomputable abbrev E_pi (n N : ℕ) : ℕ :=
  collisionEnergy piDecimalStream n N

/-- Distance from `x` to the nearest integer, defined as the infimum of all
integer-translate distances. -/
noncomputable def circleDistance (x : ℝ) : ℝ :=
  sInf (Set.range fun z : ℤ => |x - (z : ℝ)|)

/-- Circle distance is at most the distance to any specified integer. -/
lemma circleDistance_le_abs_sub_int (x : ℝ) (z : ℤ) :
    circleDistance x ≤ |x - (z : ℝ)| := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨w, rfl⟩; exact abs_nonneg _⟩
  · exact ⟨z, rfl⟩

/-- Equal first `n` floor-based decimal digits put two points of `[0,1)` in
the same half-open decimal cylinder, whose diameter is strictly `10^(-n)`. -/
lemma abs_sub_lt_inv_pow_of_decimal_prefix_eq {x y : ℝ} (hx : x ∈ Set.Ico 0 1)
    (hy : y ∈ Set.Ico 0 1) (n : ℕ)
    (hdigits : ∀ k : ℕ, k < n → Real.digits x 10 k = Real.digits y 10 k) :
    |x - y| < ((10 : ℝ) ^ n)⁻¹ := by
  have hsum :
      ∑ k ∈ Finset.range n, Real.ofDigitsTerm (Real.digits x 10) k =
        ∑ k ∈ Finset.range n, Real.ofDigitsTerm (Real.digits y 10) k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Real.ofDigitsTerm, hdigits k (Finset.mem_range.mp hk)]
  have hxsum := Real.ofDigits_digits_sum_eq (b := 10) hx n
  have hysum := Real.ofDigits_digits_sum_eq (b := 10) hy n
  have hfloorCast :
      (⌊(10 : ℝ) ^ n * x⌋₊ : ℝ) = (⌊(10 : ℝ) ^ n * y⌋₊ : ℝ) := by
    calc
      (⌊(10 : ℝ) ^ n * x⌋₊ : ℝ) =
          (10 : ℝ) ^ n *
            ∑ k ∈ Finset.range n, Real.ofDigitsTerm (Real.digits x 10) k := hxsum.symm
      _ = (10 : ℝ) ^ n *
            ∑ k ∈ Finset.range n, Real.ofDigitsTerm (Real.digits y 10) k := by rw [hsum]
      _ = (⌊(10 : ℝ) ^ n * y⌋₊ : ℝ) := hysum
  have hfloor : ⌊(10 : ℝ) ^ n * x⌋₊ = ⌊(10 : ℝ) ^ n * y⌋₊ := by
    exact_mod_cast hfloorCast
  have hpow : 0 < (10 : ℝ) ^ n := by positivity
  have hxnonneg : 0 ≤ (10 : ℝ) ^ n * x := mul_nonneg hpow.le hx.1
  have hynonneg : 0 ≤ (10 : ℝ) ^ n * y := mul_nonneg hpow.le hy.1
  have hxlo : (⌊(10 : ℝ) ^ n * x⌋₊ : ℝ) ≤ (10 : ℝ) ^ n * x :=
    Nat.floor_le hxnonneg
  have hylo : (⌊(10 : ℝ) ^ n * y⌋₊ : ℝ) ≤ (10 : ℝ) ^ n * y :=
    Nat.floor_le hynonneg
  have hxhi : (10 : ℝ) ^ n * x < (⌊(10 : ℝ) ^ n * x⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hyhi : (10 : ℝ) ^ n * y < (⌊(10 : ℝ) ^ n * y⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hscaled : |(10 : ℝ) ^ n * x - (10 : ℝ) ^ n * y| < 1 := by
    rw [hfloor] at hxlo hxhi
    rw [abs_lt]
    constructor <;> linarith
  have habspow : |(10 : ℝ) ^ n| = (10 : ℝ) ^ n := abs_of_pos hpow
  have hmul : (10 : ℝ) ^ n * |x - y| < 1 := by
    simpa [← mul_sub, abs_mul, habspow] using hscaled
  simpa using (lt_inv_mul_iff₀ hpow).2 hmul

/-- Ordered first-`N` pairs whose lacunary difference is within `10^(-n)`
of an integer. The diagonal and both orders of every off-diagonal pair are
retained. -/
noncomputable def piNearReturnPairs (n N : ℕ) : Finset (Fin N × Fin N) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun ij =>
    circleDistance
      (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
        ((10 : ℝ) ^ n)⁻¹

/-- `Q_pi(n,N)`: the ordered-pair lacunary near-return count. -/
noncomputable def Q_pi (n N : ℕ) : ℕ :=
  (piNearReturnPairs n N).card

@[simp] lemma mem_piNearReturnPairs_iff (n N : ℕ) (ij : Fin N × Fin N) :
    ij ∈ piNearReturnPairs n N ↔
      circleDistance
        (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
          ((10 : ℝ) ^ n)⁻¹ := by
  classical
  simp [piNearReturnPairs]

/-- The ordered-pair convention includes every diagonal pair. -/
@[simp] lemma diagonal_mem_piNearReturnPairs (n N : ℕ) (i : Fin N) :
    (i, i) ∈ piNearReturnPairs n N := by
  rw [mem_piNearReturnPairs_iff]
  have hzero : circleDistance (0 : ℝ) ≤ 0 := by
    simpa using circleDistance_le_abs_sub_int (0 : ℝ) (0 : ℤ)
  have hinv : 0 < ((10 : ℝ) ^ n)⁻¹ := inv_pos.mpr (by positivity)
  simpa using hzero.trans_lt hinv

/-- Equality of two T1 length-`n` pi factors implies the required lacunary
circle near-return estimate. -/
theorem pi_factor_eq_implies_circleDistance_lt (n : ℕ) {i j : ℕ}
    (hfactor : factorAt piDecimalStream n i = factorAt piDecimalStream n j) :
    circleDistance (((10 : ℝ) ^ j - (10 : ℝ) ^ i) * Real.pi) <
      ((10 : ℝ) ^ n)⁻¹ := by
  let xi := Theory.PiDigits.T20.baseTenOrbit Real.pi i
  let xj := Theory.PiDigits.T20.baseTenOrbit Real.pi j
  have hblocks : blockAt piDecimalStream n i = blockAt piDecimalStream n j :=
    congrArg Subtype.val hfactor
  have hdigits : ∀ k : ℕ, k < n → Real.digits xi 10 k = Real.digits xj 10 k := by
    intro k hk
    change Theory.PiDigits.T20.decimalDigit xi k =
      Theory.PiDigits.T20.decimalDigit xj k
    rw [show xi = Theory.PiDigits.T20.baseTenOrbit Real.pi i by rfl,
      show xj = Theory.PiDigits.T20.baseTenOrbit Real.pi j by rfl,
      Theory.PiDigits.T20.decimalDigit_baseTenOrbit Real.pi Real.pi_pos.le i k,
      Theory.PiDigits.T20.decimalDigit_baseTenOrbit Real.pi Real.pi_pos.le j k]
    exact congrFun hblocks ⟨k, hk⟩
  have hxi : xi ∈ Set.Ico (0 : ℝ) 1 := by
    exact Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi i
  have hxj : xj ∈ Set.Ico (0 : ℝ) 1 := by
    exact Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi j
  have hdecimal : |xi - xj| < ((10 : ℝ) ^ n)⁻¹ :=
    abs_sub_lt_inv_pow_of_decimal_prefix_eq hxi hxj n hdigits
  let z : ℤ :=
    ⌊(10 : ℝ) ^ j * Real.pi⌋ - ⌊(10 : ℝ) ^ i * Real.pi⌋
  have hrepresent :
      ((10 : ℝ) ^ j - (10 : ℝ) ^ i) * Real.pi - (z : ℝ) = xj - xi := by
    dsimp [z, xj, xi, Theory.PiDigits.T20.baseTenOrbit]
    rw [Int.cast_sub]
    simp only [Int.fract]
    ring
  calc
    circleDistance (((10 : ℝ) ^ j - (10 : ℝ) ^ i) * Real.pi) ≤
        |((10 : ℝ) ^ j - (10 : ℝ) ^ i) * Real.pi - (z : ℝ)| :=
      circleDistance_le_abs_sub_int _ z
    _ = |xj - xi| := by rw [hrepresent]
    _ = |xi - xj| := abs_sub_comm _ _
    _ < ((10 : ℝ) ^ n)⁻¹ := hdecimal

/-- Every imported T4 ordered collision pair is a C2 near-return pair. -/
theorem pi_collisionPairs_subset_nearReturnPairs (n N : ℕ) :
    collisionPairs piDecimalStream n N ⊆ piNearReturnPairs n N := by
  intro ij hij
  rw [mem_piNearReturnPairs_iff]
  exact pi_factor_eq_implies_circleDistance_lt n (mem_collisionPairs_iff _ _ _ _ |>.mp hij)

/-- The pi collision energy is bounded by the ordered-pair near-return count. -/
theorem pi_collisionEnergy_le_Q_pi (n N : ℕ) :
    E_pi n N ≤ Q_pi n N := by
  change collisionEnergy piDecimalStream n N ≤ Q_pi n N
  rw [collisionEnergy_eq_collisionPairCount, collisionPairCount, Q_pi]
  exact Finset.card_le_card (pi_collisionPairs_subset_nearReturnPairs n N)

/-- C2, the unproved strictly sufficient stronger sibling for pi. For every
positive `C`, eventually at every positive length `n`, some positive `N` has
`Q_pi(n,N) < N^2 / (C*n)` after coercion to the reals.

This is not C1, is not canonical A1, and is asserted only as a hypothesis. -/
def LacunaryNearReturnC2 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
      (Q_pi n N : ℝ) < (N : ℝ) ^ 2 / (C * (n : ℝ))

/-- The exact C2 sibling implies T4's exact C1 sibling. This is a one-way
sufficiency result and does not assert C2 for pi. -/
theorem lacunaryNearReturnC2_implies_collisionEnergyC1
    (hC2 : LacunaryNearReturnC2) : CollisionEnergyC1 piDecimalStream := by
  intro C hC
  obtain ⟨n0, hn0, hall⟩ := hC2 C hC
  refine ⟨n0, hn0, ?_⟩
  intro n hn
  obtain ⟨N, hN, hQ⟩ := hall n hn
  refine ⟨N, hN, ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le hn0 hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hdenom : 0 < C * (n : ℝ) := mul_pos hC hnreal
  have hQscaled : (Q_pi n N : ℝ) * (C * (n : ℝ)) < (N : ℝ) ^ 2 :=
    (lt_div_iff₀ hdenom).mp hQ
  have henergyNat := pi_collisionEnergy_le_Q_pi n N
  have henergyReal :
      (collisionEnergy piDecimalStream n N : ℝ) ≤ (Q_pi n N : ℝ) := by
    exact_mod_cast henergyNat
  calc
    C * (n : ℝ) * (collisionEnergy piDecimalStream n N : ℝ) ≤
        C * (n : ℝ) * (Q_pi n N : ℝ) :=
      mul_le_mul_of_nonneg_left henergyReal (mul_nonneg hC.le hnreal.le)
    _ = (Q_pi n N : ℝ) * (C * (n : ℝ)) := by ring
    _ < (N : ℝ) ^ 2 := hQscaled

/-- Consequently, C2 implies T1's canonical A1 through the imported T4
theorem. This conditional implication makes no unconditional pi claim. -/
theorem lacunaryNearReturnC2_implies_canonical_A1
    (hC2 : LacunaryNearReturnC2) :
    A1 piDecimalStream (canonicalComplexityData piDecimalStream) := by
  exact collisionEnergyC1_implies_canonical_A1 piDecimalStream
    (lacunaryNearReturnC2_implies_collisionEnergyC1 hC2)

end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.circleDistance_le_abs_sub_int
#print axioms DecimalFactorComplexity.abs_sub_lt_inv_pow_of_decimal_prefix_eq
#print axioms DecimalFactorComplexity.diagonal_mem_piNearReturnPairs
#print axioms DecimalFactorComplexity.pi_factor_eq_implies_circleDistance_lt
#print axioms DecimalFactorComplexity.pi_collisionPairs_subset_nearReturnPairs
#print axioms DecimalFactorComplexity.pi_collisionEnergy_le_Q_pi
#print axioms DecimalFactorComplexity.lacunaryNearReturnC2_implies_collisionEnergyC1
#print axioms DecimalFactorComplexity.lacunaryNearReturnC2_implies_canonical_A1
