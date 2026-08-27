import TheoryLib.PiLacunaryNearReturnSparsity.T26SharedResonanceChain

/-!
# T28: conditional adjacent-node compatibility bridge

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module isolates a sufficient compatibility hypothesis for two adjacent
nodes of one T26 chain.  The compatibility predicate records only T24-shaped
indices, coefficients, and scaled errors.  It contains neither canonical A1
nor a rational approximation to `Real.pi`.

The exponent-eight lower bound and coherent selection are explicit
hypotheses.  No compatibility property is asserted for `Real.pi`.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity
namespace AdjacentNodeCompatibility

open IteratedLagResonance
open FiniteInverseDichotomy
open SharedResonanceChain

/-- Canonical A1, with the ordered diagonal-inclusive count from T8. -/
def CanonicalA1 : Prop :=
  ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
      A * n * Q_pi n N ≤ N ^ 2

/-- The exact exponent-eight irrationality hypothesis used below. -/
def ExponentEightLowerBound (Q8 : ℕ) : Prop :=
  1 ≤ Q8 ∧ ∀ q : ℕ, Q8 ≤ q → 1 ≤ q → ∀ p : ℤ,
    ((q : ℝ) ^ 8)⁻¹ < |Real.pi - (p : ℝ) / (q : ℝ)|

/-- Natural-number version of T24's eventually-periodic denominator. -/
def decimalDenominatorNat (j s : ℕ) : ℕ :=
  10 ^ j * (10 ^ s - 1)

/-- The actual error in the scaled near-integer relation at one node. -/
def scaledIntegerError (beta : ℝ) (j s : ℕ) (a : ℤ) : ℝ :=
  |(decimalDenominatorNat j s : ℝ) * beta - (a : ℝ)|

/-- The natural multiplier of `pi` at prefix node `k`. -/
def nodeMultiplier (h r : ℕ) (shifts : List ℕ) (k : ℕ) : ℕ :=
  h * (10 ^ r - 1) *
    ((shifts.take k).map (fun t => 10 ^ t - 1)).prod

/-- The shift joining prefix nodes `k` and `k+1`. -/
def GeometricResonanceChain.shiftAt
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) : ℕ :=
  chain.shifts.get ⟨k, by simpa [chain.length_eq] using k.isLt⟩

/-- The new base-ten factor between adjacent prefix nodes. -/
def GeometricResonanceChain.adjacentFactor
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) : ℕ :=
  10 ^ GeometricResonanceChain.shiftAt chain k - 1

/-- The denominator of the rational approximation obtained after transport
to the second node. -/
def selectedDenominator
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (j s : ℕ) : ℕ :=
  nodeMultiplier h r chain.shifts k *
    GeometricResonanceChain.adjacentFactor chain k *
    decimalDenominatorNat j s

/-- A cap obtained from explicit preperiod and period bounds `J,S`. -/
def denominatorCap
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (J S : ℕ) : ℕ :=
  nodeMultiplier h r chain.shifts k *
    GeometricResonanceChain.adjacentFactor chain k *
    decimalDenominatorNat J S

/-- T24-shaped witnesses at two adjacent T26 nodes, together with the actual
error budget that forces exact cross multiplication.  This predicate has no
rational-approximation conclusion and does not mention A1. -/
def AdjacentPairCompatible
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (j0 s0 j1 s1 : ℕ) (a0 a1 : ℤ) : Prop :=
  let Q0 := decimalDenominatorNat j0 s0
  let Q1 := decimalDenominatorNat j1 s1
  let U := GeometricResonanceChain.adjacentFactor chain k
  let beta0 := chain.nodeCoefficient k
  let beta1 := chain.nodeCoefficient (k + 1)
  let e0 := scaledIntegerError beta0 j0 s0 a0
  let e1 := scaledIntegerError beta1 j1 s1 a1
  1 ≤ s0 ∧ j0 + s0 < chain.nodeResidual k ∧
  1 ≤ s1 ∧ j1 + s1 < chain.nodeResidual (k + 1) ∧
  e0 < inverseError (nodeTau D k) ∧
  e1 < inverseError (nodeTau D (k + 1)) ∧
  (Q0 : ℝ) * e1 + (U : ℝ) * (Q1 : ℝ) * e0 < 1

/-- Explicit preperiod/period bounds and the quantitative error condition
needed to close against exponent eight. -/
def ExponentEightClosingBounds
    {M D K d h r : ℕ} (Q8 J S : ℕ)
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (j0 s0 j1 s1 : ℕ) (a0 : ℤ) : Prop :=
  let C := nodeMultiplier h r chain.shifts k
  let Q0 := decimalDenominatorNat j0 s0
  let q := selectedDenominator chain k j1 s1
  let qCap := denominatorCap chain k J S
  1 ≤ S ∧ j1 ≤ J ∧ s1 ≤ S ∧ Q8 ≤ q ∧
    scaledIntegerError (chain.nodeCoefficient k) j0 s0 a0 *
        (qCap : ℝ) ^ 8 < (C * Q0 : ℕ)

lemma decimalDenominatorNat_cast (j s : ℕ) :
    (decimalDenominatorNat j s : ℝ) =
      (10 : ℝ) ^ j * ((10 : ℝ) ^ s - 1) := by
  unfold decimalDenominatorNat
  rw [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ))), Nat.cast_pow]
  norm_num

lemma decimalDenominatorNat_pos {j s : ℕ} (hs : 1 ≤ s) :
    1 ≤ decimalDenominatorNat j s := by
  have hpow : 1 < 10 ^ s := one_lt_pow₀ (by norm_num) (by omega)
  unfold decimalDenominatorNat
  have hleft : 1 ≤ 10 ^ j := one_le_pow₀ (by norm_num)
  have hright : 1 ≤ 10 ^ s - 1 := by omega
  nlinarith

lemma decimalDenominatorNat_mono
    {j s J S : ℕ} (hj : j ≤ J) (hs : s ≤ S) :
    decimalDenominatorNat j s ≤ decimalDenominatorNat J S := by
  unfold decimalDenominatorNat
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (by norm_num) hj
  · exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hs) 1

lemma factorProduct_cast (shifts : List ℕ) :
    (((shifts.map (fun t => 10 ^ t - 1)).prod : ℕ) : ℝ) =
      (shifts.map (fun t => (10 : ℝ) ^ t - 1)).prod := by
  induction shifts with
  | nil => simp
  | cons t shifts ih =>
      simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
      rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ))), Nat.cast_pow]
      norm_num

lemma GeometricResonanceChain.shiftAt_mem
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) :
    GeometricResonanceChain.shiftAt chain k ∈ chain.shifts := by
  unfold GeometricResonanceChain.shiftAt
  exact List.get_mem _ _

lemma GeometricResonanceChain.shiftAt_lower
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) : B ≤ GeometricResonanceChain.shiftAt chain k := by
  exact chain.shift_lower _
    (GeometricResonanceChain.shiftAt_mem chain k)

lemma GeometricResonanceChain.take_succ_eq
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) :
    chain.shifts.take (k + 1) =
      chain.shifts.take k ++ [GeometricResonanceChain.shiftAt chain k] := by
  have hk : k.val < chain.shifts.length := by
    simpa [chain.length_eq] using k.isLt
  simpa [GeometricResonanceChain.shiftAt, List.get_eq_getElem] using
    (List.take_append_getElem hk).symm

/-- Adjacent T26 prefix coefficients differ by the displayed base-ten
factor. -/
lemma GeometricResonanceChain.nodeCoefficient_succ
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) :
    chain.nodeCoefficient (k + 1) =
      (GeometricResonanceChain.adjacentFactor chain k : ℝ) *
        chain.nodeCoefficient k := by
  unfold GeometricResonanceChain.nodeCoefficient
  rw [GeometricResonanceChain.take_succ_eq chain k,
    List.map_append, List.prod_append]
  simp only [List.map_singleton, List.prod_singleton]
  rw [show
      (GeometricResonanceChain.adjacentFactor chain k : ℝ) =
        (10 : ℝ) ^ GeometricResonanceChain.shiftAt chain k - 1 by
    unfold GeometricResonanceChain.adjacentFactor
    rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ))), Nat.cast_pow]
    norm_num]
  ring

lemma GeometricResonanceChain.nodeCoefficient_eq_multiplier_pi
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}) (k : ℕ) :
    chain.nodeCoefficient k =
      (nodeMultiplier h r chain.shifts k : ℝ) * Real.pi := by
  unfold GeometricResonanceChain.nodeCoefficient nodeMultiplier
    initialCoefficient
  rw [Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ))), Nat.cast_pow,
    factorProduct_cast]
  norm_num
  ring

lemma nodeMultiplier_pos
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (hh : 1 ≤ h) (hr : 1 ≤ r) (k : ℕ) :
    1 ≤ nodeMultiplier h r chain.shifts k := by
  have hrpos : 0 < 10 ^ r - 1 := by
    have : 1 < 10 ^ r := one_lt_pow₀ (by norm_num) (by omega)
    omega
  have hprod :
      0 < ((chain.shifts.take k).map (fun t => 10 ^ t - 1)).prod := by
    apply List.prod_pos
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have htmem : t ∈ chain.shifts := List.mem_of_mem_take ht
    have htpos : 1 ≤ t := chain.shift_lower t htmem
    have : 1 < 10 ^ t := one_lt_pow₀ (by norm_num) (by omega)
    omega
  unfold nodeMultiplier
  have hhpos : 0 < h := by omega
  have : 0 < h * (10 ^ r - 1) *
      ((chain.shifts.take k).map (fun t => 10 ^ t - 1)).prod := by
    positivity
  omega

lemma adjacentFactor_pos
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) :
    1 ≤ GeometricResonanceChain.adjacentFactor chain k := by
  have ht : 1 ≤ GeometricResonanceChain.shiftAt chain k :=
    GeometricResonanceChain.shiftAt_lower chain k
  have hpow : 1 < 10 ^ GeometricResonanceChain.shiftAt chain k :=
    one_lt_pow₀ (by norm_num) (by omega)
  unfold GeometricResonanceChain.adjacentFactor
  omega

/-- The explicit component bounds imply the full selected-denominator cap. -/
theorem selectedDenominator_le_cap
    {M D K d h r Q8 J S j0 s0 j1 s1 : ℕ} {a0 : ℤ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}) (k : Fin d)
    (hb : ExponentEightClosingBounds Q8 J S chain k
      j0 s0 j1 s1 a0) :
    selectedDenominator chain k j1 s1 ≤ denominatorCap chain k J S := by
  dsimp [ExponentEightClosingBounds] at hb
  rcases hb with ⟨_hS, hj, hs, _hq, _herror⟩
  unfold selectedDenominator denominatorCap
  exact Nat.mul_le_mul_left
    (nodeMultiplier h r chain.shifts k *
      GeometricResonanceChain.adjacentFactor chain k)
    (decimalDenominatorNat_mono hj hs)

/-- Actual adjacent-node errors below one force exact integer cancellation. -/
theorem cross_node_cancellation
    {M D K d h r j0 s0 j1 s1 : ℕ} {a0 a1 : ℤ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}) (k : Fin d)
    (hc : AdjacentPairCompatible chain k j0 s0 j1 s1 a0 a1) :
    (decimalDenominatorNat j0 s0 : ℤ) * a1 =
      (GeometricResonanceChain.adjacentFactor chain k : ℤ) *
        (decimalDenominatorNat j1 s1 : ℤ) * a0 := by
  simp only [AdjacentPairCompatible] at hc
  rcases hc with ⟨_hs0, _hpos0, _hs1, _hpos1,
    _he0, _he1, hbudget⟩
  let Q0 : ℕ := decimalDenominatorNat j0 s0
  let Q1 : ℕ := decimalDenominatorNat j1 s1
  let U : ℕ := GeometricResonanceChain.adjacentFactor chain k
  let beta0 : ℝ := chain.nodeCoefficient k
  let beta1 : ℝ := chain.nodeCoefficient (k + 1)
  let z : ℤ := (Q0 : ℤ) * a1 - (U : ℤ) * (Q1 : ℤ) * a0
  have hcoeff : beta1 = (U : ℝ) * beta0 := by
    simpa [beta0, beta1, U] using
      GeometricResonanceChain.nodeCoefficient_succ chain k
  have hid :
      (z : ℝ) =
        -(Q0 : ℝ) * ((Q1 : ℝ) * beta1 - (a1 : ℝ)) +
          (U : ℝ) * (Q1 : ℝ) *
            ((Q0 : ℝ) * beta0 - (a0 : ℝ)) := by
    dsimp [z]
    push_cast
    rw [hcoeff]
    ring
  have hzle :
      |(z : ℝ)| ≤
        (Q0 : ℝ) * scaledIntegerError beta1 j1 s1 a1 +
          (U : ℝ) * (Q1 : ℝ) *
            scaledIntegerError beta0 j0 s0 a0 := by
    rw [hid]
    calc
      |-(Q0 : ℝ) * ((Q1 : ℝ) * beta1 - (a1 : ℝ)) +
          (U : ℝ) * (Q1 : ℝ) *
            ((Q0 : ℝ) * beta0 - (a0 : ℝ))| ≤
          |-(Q0 : ℝ) * ((Q1 : ℝ) * beta1 - (a1 : ℝ))| +
            |(U : ℝ) * (Q1 : ℝ) *
              ((Q0 : ℝ) * beta0 - (a0 : ℝ))| := abs_add_le _ _
      _ = (Q0 : ℝ) * scaledIntegerError beta1 j1 s1 a1 +
          (U : ℝ) * (Q1 : ℝ) *
            scaledIntegerError beta0 j0 s0 a0 := by
        simp [scaledIntegerError, Q0, Q1, U, abs_mul, mul_assoc]
  have hzlt : |(z : ℝ)| < 1 := hzle.trans_lt (by
    simpa [Q0, Q1, U, beta0, beta1] using hbudget)
  have hzabs : |z| < (1 : ℤ) := by
    exact_mod_cast (show |(z : ℝ)| < (1 : ℝ) from hzlt)
  have hzzero : z = 0 := Int.abs_lt_one_iff.mp hzabs
  exact sub_eq_zero.mp (by simpa [z, Q0, Q1, U] using hzzero)

/-- Cancellation transports the first node's error to the bounded second
denominator, yielding an explicit rational approximation to `pi`. -/
theorem compatible_pair_pi_error
    {M D K d h r j0 s0 j1 s1 : ℕ} {a0 a1 : ℤ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}) (k : Fin d)
    (hh : 1 ≤ h) (hr : 1 ≤ r)
    (hc : AdjacentPairCompatible chain k j0 s0 j1 s1 a0 a1) :
    |Real.pi - (a1 : ℝ) /
        (selectedDenominator chain k j1 s1 : ℝ)| =
      scaledIntegerError (chain.nodeCoefficient k) j0 s0 a0 /
        (nodeMultiplier h r chain.shifts k *
          decimalDenominatorNat j0 s0 : ℕ) := by
  let C : ℕ := nodeMultiplier h r chain.shifts k
  let Q0 : ℕ := decimalDenominatorNat j0 s0
  let Q1 : ℕ := decimalDenominatorNat j1 s1
  let U : ℕ := GeometricResonanceChain.adjacentFactor chain k
  have hs0 : 1 ≤ s0 := by
    simpa only [AdjacentPairCompatible] using hc.1
  have hs1 : 1 ≤ s1 := by
    simpa only [AdjacentPairCompatible] using hc.2.2.1
  have hCnat : 1 ≤ C := by
    exact nodeMultiplier_pos chain hh hr k
  have hQ0nat : 1 ≤ Q0 := decimalDenominatorNat_pos hs0
  have hQ1nat : 1 ≤ Q1 := decimalDenominatorNat_pos hs1
  have hUnat : 1 ≤ U := adjacentFactor_pos chain k
  have hC : (0 : ℝ) < C := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCnat)
  have hQ0 : (0 : ℝ) < Q0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ0nat)
  have hQ1 : (0 : ℝ) < Q1 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ1nat)
  have hU : (0 : ℝ) < U := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hUnat)
  have hcancelInt := cross_node_cancellation chain k hc
  have hcancel :
      (Q0 : ℝ) * (a1 : ℝ) =
        (U : ℝ) * (Q1 : ℝ) * (a0 : ℝ) := by
    exact_mod_cast (show
      (Q0 : ℤ) * a1 = (U : ℤ) * (Q1 : ℤ) * a0 by
        simpa [Q0, Q1, U] using hcancelInt)
  have hfractions :
      (a1 : ℝ) / ((C : ℝ) * U * Q1) =
        (a0 : ℝ) / ((C : ℝ) * Q0) := by
    field_simp
    nlinarith
  have hselected :
      (selectedDenominator chain k j1 s1 : ℝ) =
        (C : ℝ) * U * Q1 := by
    simp [selectedDenominator, C, U, Q1]
  have hnode : chain.nodeCoefficient k = (C : ℝ) * Real.pi := by
    simpa [C] using
      GeometricResonanceChain.nodeCoefficient_eq_multiplier_pi chain k
  have hdenom :
      ((C * Q0 : ℕ) : ℝ) = (C : ℝ) * Q0 := by norm_num
  rw [hselected, hfractions, hnode, hdenom]
  unfold scaledIntegerError
  have hrearrange :
      Real.pi - (a0 : ℝ) / ((C : ℝ) * Q0) =
        (((C : ℝ) * Q0) * Real.pi - (a0 : ℝ)) /
          ((C : ℝ) * Q0) := by
    field_simp
  rw [hrearrange, abs_div, abs_of_pos (mul_pos hC hQ0)]
  congr 2
  ring

/-- One compatible bounded adjacent pair contradicts the assumed
exponent-eight lower bound. -/
theorem compatible_pair_contradicts_exponentEight
    {M D K d h r Q8 J S j0 s0 j1 s1 : ℕ} {a0 a1 : ℤ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}) (k : Fin d)
    (hh : 1 ≤ h) (hr : 1 ≤ r)
    (hirr : ExponentEightLowerBound Q8)
    (hc : AdjacentPairCompatible chain k j0 s0 j1 s1 a0 a1)
    (hb : ExponentEightClosingBounds Q8 J S chain k
      j0 s0 j1 s1 a0) : False := by
  let C : ℕ := nodeMultiplier h r chain.shifts k
  let Q0 : ℕ := decimalDenominatorNat j0 s0
  let q : ℕ := selectedDenominator chain k j1 s1
  let qCap : ℕ := denominatorCap chain k J S
  have hb' := hb
  dsimp [ExponentEightClosingBounds] at hb'
  rcases hb' with ⟨hS, _hj, _hs, hQ8, herror⟩
  have hqnat : 1 ≤ q := hirr.1.trans hQ8
  have hCnat : 1 ≤ C := nodeMultiplier_pos chain hh hr k
  have hs0 : 1 ≤ s0 := by
    simpa only [AdjacentPairCompatible] using hc.1
  have hQ0nat : 1 ≤ Q0 := decimalDenominatorNat_pos hs0
  have hUnat :
      1 ≤ GeometricResonanceChain.adjacentFactor chain k :=
    adjacentFactor_pos chain k
  have hcapDenom : 1 ≤ decimalDenominatorNat J S :=
    decimalDenominatorNat_pos hS
  have hqCapNat : 1 ≤ qCap := by
    dsimp [qCap, denominatorCap]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hden : (0 : ℝ) < (C * Q0 : ℕ) := by
    exact_mod_cast (Nat.mul_pos
      (lt_of_lt_of_le Nat.zero_lt_one hCnat)
      (lt_of_lt_of_le Nat.zero_lt_one hQ0nat))
  have hcap : (0 : ℝ) < (qCap : ℝ) ^ 8 := by
    positivity
  have hsmall :
      scaledIntegerError (chain.nodeCoefficient k) j0 s0 a0 /
          (C * Q0 : ℕ) < ((qCap : ℝ) ^ 8)⁻¹ := by
    rw [div_lt_iff₀ hden]
    rw [show ((qCap : ℝ) ^ 8)⁻¹ * ((C * Q0 : ℕ) : ℝ) =
        ((C * Q0 : ℕ) : ℝ) / (qCap : ℝ) ^ 8 by
      rw [div_eq_mul_inv]
      ring]
    exact (lt_div_iff₀ hcap).2 (by simpa [C, Q0, qCap] using herror)
  have hqcap : q ≤ qCap := by
    simpa [q, qCap] using selectedDenominator_le_cap chain k hb
  have hpowle : (q : ℝ) ^ 8 ≤ (qCap : ℝ) ^ 8 := by
    gcongr
  have hqpow : (0 : ℝ) < (q : ℝ) ^ 8 := by positivity
  have hinvle : ((qCap : ℝ) ^ 8)⁻¹ ≤ ((q : ℝ) ^ 8)⁻¹ :=
    (inv_le_inv₀ hcap hqpow).2 hpowle
  have hpi := compatible_pair_pi_error chain k hh hr hc
  have hupp :
      |Real.pi - (a1 : ℝ) / (q : ℝ)| < ((q : ℝ) ^ 8)⁻¹ := by
    rw [show (q : ℝ) =
        (selectedDenominator chain k j1 s1 : ℕ) by rfl]
    rw [hpi]
    exact hsmall.trans_le hinvle
  have hlow := hirr.2 q hQ8 hqnat a1
  linarith

/-- A coherent selector must work on any positive T26 chain carrying all of
T24's nodewise alternatives.  This is a hypothesis, not a property proved for
`pi`. -/
def CoherentAdjacentSelection (Q8 J S : ℕ) : Prop :=
  ∀ {M D K d h r : ℕ}, 1 ≤ d → 1 ≤ h → 1 ≤ r →
    ∀ chain : GeometricResonanceChain
        (initialCoefficient h r) M D 1 K d {r},
      (∀ k : Fin (d + 1),
        CycleApproximation (chain.nodeCoefficient k) (nodeTau D k)
            (chain.nodeResidual k) ∨
          (¬ CycleApproximation (chain.nodeCoefficient k) (nodeTau D k)
              (chain.nodeResidual k) ∧
            PositivePreperiodApproximation
              (chain.nodeCoefficient k) (nodeTau D k)
                (chain.nodeResidual k))) →
      ∃ k : Fin d, ∃ j0 s0 j1 s1 : ℕ, ∃ a0 a1 : ℤ,
        AdjacentPairCompatible chain k j0 s0 j1 s1 a0 a1 ∧
          ExponentEightClosingBounds Q8 J S chain k
            j0 s0 j1 s1 a0

/-- Conditional canonical A1.  Both arithmetic inputs remain hypotheses. -/
theorem exponentEight_and_coherentSelection_imply_canonicalA1
    (Q8 J S : ℕ) (hirr : ExponentEightLowerBound Q8)
    (hselect : CoherentAdjacentSelection Q8 J S) : CanonicalA1 := by
  by_contra hnot
  have hnot' : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2) := by
    simpa only [CanonicalA1] using hnot
  obtain ⟨A, hA, hchains⟩ :=
    literal_not_A1_implies_shared_chain_nodewise_inverse_necessaryOnly hnot'
  obtain ⟨n, _hn0n, _hn, hdepth⟩ := hchains 1 (by norm_num)
  obtain ⟨N, r, h, chain, _hlength, _hN, hr, hh, hinverse⟩ :=
    hdepth 1
  have hrpos : 1 ≤ r := (mem_Icc.mp hr).1
  have hhpos : 1 ≤ h := (mem_Icc.mp hh).1
  obtain ⟨k, j0, s0, j1, s1, a0, a1, hc, hb⟩ :=
    hselect (by norm_num) hhpos hrpos chain hinverse
  exact compatible_pair_contradicts_exponentEight
    chain k hhpos hrpos hirr hc hb

/-- Inverse obstruction: under exponent eight, literal failure of A1 supplies
a T26 chain on which every proposed adjacent pair fails compatibility or one
of the displayed closing bounds. -/
theorem literal_not_A1_implies_adjacent_compatibility_obstruction
    (Q8 J S : ℕ) (hirr : ExponentEightLowerBound Q8)
    (hnotA1 : ¬ CanonicalA1) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧
        let D := initialDensity A n
        let d := 1
        let K := chainLengthRequest D d
        let L := iterationLengthThresholdAux D 1 K 1 d
        ∃ N r h : ℕ,
          ∃ chain : GeometricResonanceChain
              (initialCoefficient h r) (N - r) D 1 K d {r},
            chain.shifts.length = d ∧
            N = 16 * A * n * L ∧
            r ∈ Icc 1 (N - 1) ∧
            h ∈ Icc 1 (256 * A * n) ∧
            ∀ k : Fin d, ∀ j0 s0 j1 s1 : ℕ, ∀ a0 a1 : ℤ,
              ¬ AdjacentPairCompatible chain k j0 s0 j1 s1 a0 a1 ∨
                ¬ ExponentEightClosingBounds Q8 J S chain k
                  j0 s0 j1 s1 a0 := by
  have hnot' : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2) := by
    simpa only [CanonicalA1] using hnotA1
  obtain ⟨A, hA, hchains⟩ :=
    literal_not_A1_implies_shared_chain_nodewise_inverse_necessaryOnly hnot'
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hdepth⟩ := hchains n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  dsimp only
  obtain ⟨N, r, h, chain, hlength, hN, hr, hh, _hinverse⟩ :=
    hdepth 1
  refine ⟨N, r, h, chain, hlength, ?_, hr, hh, ?_⟩
  · simpa using hN
  · intro k j0 s0 j1 s1 a0 a1
    by_cases hc : AdjacentPairCompatible chain k j0 s0 j1 s1 a0 a1
    · right
      intro hb
      exact compatible_pair_contradicts_exponentEight chain k
        (mem_Icc.mp hh).1 (mem_Icc.mp hr).1 hirr hc hb
    · exact Or.inl hc

end AdjacentNodeCompatibility
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.AdjacentNodeCompatibility.GeometricResonanceChain.nodeCoefficient_succ
#print axioms DecimalFactorComplexity.AdjacentNodeCompatibility.selectedDenominator_le_cap
#print axioms DecimalFactorComplexity.AdjacentNodeCompatibility.cross_node_cancellation
#print axioms DecimalFactorComplexity.AdjacentNodeCompatibility.compatible_pair_pi_error
#print axioms DecimalFactorComplexity.AdjacentNodeCompatibility.compatible_pair_contradicts_exponentEight
#print axioms DecimalFactorComplexity.AdjacentNodeCompatibility.exponentEight_and_coherentSelection_imply_canonicalA1
#print axioms DecimalFactorComplexity.AdjacentNodeCompatibility.literal_not_A1_implies_adjacent_compatibility_obstruction
