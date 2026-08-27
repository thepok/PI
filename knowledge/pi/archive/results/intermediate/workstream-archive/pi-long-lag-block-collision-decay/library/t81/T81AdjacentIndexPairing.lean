import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc
import TheoryLib.PiLongLagBlockCollisionDecay.T76T76VariablePhasePooledHalfArc

/-!
# T81: adjacent-index equal-frequency pairing

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module concerns only T69's residual-A12, `m = 1`, dyadic pooled sum.
It proves that T76's sole nontrivial equal-frequency pairing has equal positive
coefficients, not opposite signs, and that the paired coefficient mass exceeds
every constant multiple of T69's `H_t * N_t` target along an infinite family.
It proves no estimate at `Real.pi`, no T69 aggregate premise, no full T29
predicate, and none of C1, C2, C3, or the canonical collision estimate.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T81

open Theory.PiDigits.LongLagBlockCollisionDecay.T66
open Theory.PiDigits.LongLagBlockCollisionDecay.T69
open Theory.PiDigits.LongLagBlockCollisionDecay.T76

/-- The two nontrivial equal-frequency channels at a fixed shift `r`. -/
def InteriorPairDomain (L h k : ℕ) : Prop :=
  (h = 10 ∧ k + 1 < L) ∨ (h = 1 ∧ 1 ≤ k ∧ k < L)

/-- Exchange `(10,k)` with `(1,k+1)`, and conversely.  The second branch is
only used on `h=1, k>=1` by `InteriorPairDomain`. -/
def adjacentSwap (h k : ℕ) : ℕ × ℕ :=
  if h = 10 then (1, k + 1) else (10, k - 1)

theorem adjacentSwap_mem
    {L h k : ℕ} (hk : InteriorPairDomain L h k) :
    InteriorPairDomain L (adjacentSwap h k).1 (adjacentSwap h k).2 := by
  rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk1, hkL⟩
  · simp [adjacentSwap, InteriorPairDomain]
    exact hk
  · simp [adjacentSwap, InteriorPairDomain]
    omega

theorem adjacentSwap_involutive
    {L h k : ℕ} (hk : InteriorPairDomain L h k) :
    adjacentSwap (adjacentSwap h k).1 (adjacentSwap h k).2 = (h, k) := by
  rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk1, hkL⟩
  · simp [adjacentSwap]
  · simp [adjacentSwap, Nat.sub_add_cancel hk1]

theorem adjacentSwap_ne
    {L h k : ℕ} (hk : InteriorPairDomain L h k) :
    adjacentSwap h k ≠ (h, k) := by
  rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk1, hkL⟩ <;>
    simp [adjacentSwap]

/-- T76's exhaustive finite frequency classification, exposed for the exact
finite orbit length used at one T69 shift. -/
theorem equalFrequencyClass_exact
    {L h h' r k l : ℕ}
    (hh1 : 1 ≤ h) (hh10 : h ≤ 10)
    (hh'1 : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hk : k < L) (hl : l < L) :
    pooledFrequency h r k = pooledFrequency h' r l ↔
      (h' = h ∧ l = k) ∨
      (h = 1 ∧ 1 ≤ k ∧ h' = 10 ∧ l + 1 = k) ∨
      (h = 10 ∧ k + 1 < L ∧ h' = 1 ∧ l = k + 1) := by
  exact finite_frequencyClass_iff hh1 hh10 hh'1 hh'10 hr hk hl

/-- The adjacent channels have literally equal positive integer frequency. -/
theorem adjacentFrequency_eq (r k : ℕ) :
    pooledFrequency 10 r k = pooledFrequency 1 r (k + 1) := by
  simp [pooledFrequency, pow_succ]
  ring

/-- A term of T76's variable-phase version of the T69 pooled sum.  Its sign is
the displayed `+`; its coefficient is the natural triangular weight `H-r`. -/
def pooledTerm (H h r k : ℕ) (α : ℝ) : ℂ :=
  ((H - r : ℕ) : ℂ) *
    Theory.PiDigits.T27.phase (pooledFrequency h r k : ℤ) α

theorem adjacentTerms_equal (H r k : ℕ) (α : ℝ) :
    pooledTerm H 10 r k α = pooledTerm H 1 r (k + 1) α := by
  simp only [pooledTerm, adjacentFrequency_eq]

/-- The equal-frequency pair adds with coefficient `2*(H-r)`; there is no
minus sign available for cancellation inside the T69 pooled expression. -/
theorem adjacentTerms_add (H r k : ℕ) (α : ℝ) :
    pooledTerm H 10 r k α + pooledTerm H 1 r (k + 1) α =
      ((2 * (H - r) : ℕ) : ℂ) *
        Theory.PiDigits.T27.phase (pooledFrequency 1 r (k + 1) : ℤ) α := by
  rw [adjacentTerms_equal]
  unfold pooledTerm
  push_cast
  ring

theorem adjacentCoefficient_pos {H r : ℕ} (hr : r < H) :
    0 < 2 * (H - r) := by omega

/-- The `h=1,k=0` endpoint has no equal-frequency partner in the finite
`0 <= k < L` domain. -/
theorem leftBoundary_frequencyClass
    {L r h' l : ℕ} (hL : 0 < L) (hr : 1 ≤ r)
    (hh'1 : 1 ≤ h') (hh'10 : h' ≤ 10) (hl : l < L) :
    pooledFrequency 1 r 0 = pooledFrequency h' r l ↔
      h' = 1 ∧ l = 0 := by
  rw [finite_frequencyClass_iff (by omega) (by omega) hh'1 hh'10 hr hL hl]
  simp

/-- The `h=10,k=L-1` endpoint has no equal-frequency partner in the finite
`0 <= k < L` domain. -/
theorem rightBoundary_frequencyClass
    {L r h' l : ℕ} (hL : 0 < L) (hr : 1 ≤ r)
    (hh'1 : 1 ≤ h') (hh'10 : h' ≤ 10) (hl : l < L) :
    pooledFrequency 10 r (L - 1) = pooledFrequency h' r l ↔
      h' = 10 ∧ l = L - 1 := by
  rw [finite_frequencyClass_iff (by omega) (by omega) hh'1 hh'10 hr
    (by omega) hl]
  constructor
  · rintro (hsame | hforward | hbackward)
    · exact hsame
    · omega
    · omega
  · exact Or.inl

/-- The exact unequal-orbit common cutoff arising when channels of shifts
`r,r'` are simultaneously active at one orbit index. -/
theorem unequalCutoff_iff {N r r' k : ℕ} :
    (k < N - r ∧ k < N - r') ↔ k < N - max r r' := by
  omega

/-- The paired coefficient mass on the even-scale parameter `q`, written in a
subtraction-free form after the bijection `r=q-j`, `0<=j<q`. -/
def pairedMass (q : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range q,
    ((j + 1 : ℕ) : ℝ) * ((q ^ 2 - q + j : ℕ) : ℝ)

/-- The same mass in the original shift coordinate `r=j+1`.  At the even
scale, the factors are exactly `H-r=q-j` and `N-r-1=q^2-(j+1)`. -/
def originalPairedMass (q : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range q,
    ((q - j : ℕ) : ℝ) * ((q ^ 2 - (j + 1) : ℕ) : ℝ)

theorem pairedMass_eq_original (q : ℕ) (hq : 1 ≤ q) :
    pairedMass q = originalPairedMass q := by
  have hqq : q ≤ q ^ 2 := by nlinarith
  unfold pairedMass originalPairedMass
  congr 1
  rw [← Finset.sum_range_reflect
    (fun j => ((q - j : ℕ) : ℝ) * ((q ^ 2 - (j + 1) : ℕ) : ℝ)) q]
  apply Finset.sum_congr rfl
  intro j hj
  have hjq : j < q := Finset.mem_range.mp hj
  have hfirst : q - (q - 1 - j) = j + 1 := by omega
  have hsecond : q ^ 2 - (q - 1 - j + 1) = q ^ 2 - q + j := by omega
  rw [hfirst, hsecond]

theorem pairedMass_formula (q : ℕ) (hq : 1 ≤ q) :
    pairedMass q =
      (q : ℝ) * (q + 1) * (q - 1) * (3 * q + 2) / 3 := by
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hsumOne :
      (∑ j ∈ Finset.range q, ((j : ℝ) + 1)) =
        (q : ℝ) * ((q : ℝ) + 1) / 2 := by
    calc
      (∑ j ∈ Finset.range q, ((j : ℝ) + 1)) =
          (∑ j ∈ Finset.range q, ((j : ℕ) : ℝ)) +
            ∑ _j ∈ Finset.range q, (1 : ℝ) := by
              rw [← Finset.sum_add_distrib]
      _ = (q : ℝ) * ((q : ℝ) - 1) / 2 + q := by
        rw [sum_range_id_real]
        simp
      _ = (q : ℝ) * ((q : ℝ) + 1) / 2 := by ring
  have hsumProduct :
      (∑ j ∈ Finset.range q,
        ((j : ℝ) + 1) * (j : ℝ)) =
          (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) + 1) / 3 := by
    calc
      (∑ j ∈ Finset.range q,
          ((j : ℝ) + 1) * (j : ℝ)) =
          (∑ j ∈ Finset.range q, (j : ℝ) ^ 2) +
            ∑ j ∈ Finset.range q, (j : ℝ) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (q : ℝ) * ((q : ℝ) - 1) * (2 * (q : ℝ) - 1) / 6 +
          (q : ℝ) * ((q : ℝ) - 1) / 2 := by
            rw [sum_range_sq_real, sum_range_id_real]
      _ = (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) + 1) / 3 := by ring
  unfold pairedMass
  push_cast [Nat.cast_sub hqq]
  calc
    2 * ∑ j ∈ Finset.range q,
        ((j : ℝ) + 1) * ((q : ℝ) ^ 2 - q + j) =
        2 * (((q : ℝ) ^ 2 - q) *
          (∑ j ∈ Finset.range q, ((j : ℝ) + 1)) +
          ∑ j ∈ Finset.range q, ((j : ℝ) + 1) * (j : ℝ)) := by
            congr 1
            rw [Finset.mul_sum]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = 2 * (((q : ℝ) ^ 2 - q) *
          ((q : ℝ) * ((q : ℝ) + 1) / 2) +
        (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) + 1) / 3) := by
          rw [hsumOne, hsumProduct]
    _ = (q : ℝ) * (q + 1) * (q - 1) * (3 * q + 2) / 3 := by
      ring

/-- The square root parameter on the infinite even-scale family. -/
def evenScaleBase (m : ℕ) : ℕ := 2 ^ (m + 1)

theorem N_evenScale (m : ℕ) :
    N (2 * m) = evenScaleBase m ^ 2 + 1 := by
  simp [N, evenScaleBase, pow_add, pow_two]
  ring

theorem evenScaleBase_two_le (m : ℕ) : 2 ≤ evenScaleBase m := by
  simpa [evenScaleBase, pow_succ] using
    Nat.mul_le_mul_right 2 (one_le_pow₀ (by omega : 1 ≤ 2))

theorem H_evenScale (m : ℕ) : H (2 * m) = evenScaleBase m + 1 := by
  let q := evenScaleBase m
  have hq : 2 ≤ q := evenScaleBase_two_le m
  have hsqrtLower : (q : ℝ) < Real.sqrt ((q ^ 2 + 1 : ℕ) : ℝ) := by
    rw [Real.lt_sqrt (by positivity)]
    push_cast
    nlinarith
  have hsqrtUpper : Real.sqrt ((q ^ 2 + 1 : ℕ) : ℝ) ≤ (q + 1 : ℕ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · push_cast
      nlinarith
  unfold H
  rw [N_evenScale]
  change Nat.ceil (Real.sqrt (((q ^ 2 + 1 : ℕ) : ℝ))) = q + 1
  apply (Nat.ceil_eq_iff (by omega)).2
  constructor
  · simpa using hsqrtLower
  · exact hsqrtUpper

theorem pairedMass_normalized (q : ℕ) (hq : 1 ≤ q) :
    pairedMass q /
        (((q + 1 : ℕ) : ℝ) * ((q ^ 2 + 1 : ℕ) : ℝ)) =
      (q : ℝ) * (q - 1) * (3 * q + 2) /
        (3 * ((q : ℝ) ^ 2 + 1)) := by
  rw [pairedMass_formula q hq]
  push_cast
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 + 1 := by positivity
  field_simp

theorem pairedMass_normalized_lower (q : ℕ) (hq : 2 ≤ q) :
    (4 / 5 : ℝ) * ((q : ℝ) - 1) ≤
      pairedMass q /
        (((q + 1 : ℕ) : ℝ) * ((q ^ 2 + 1 : ℕ) : ℝ)) := by
  rw [pairedMass_normalized q (by omega)]
  have hden : (0 : ℝ) < 3 * ((q : ℝ) ^ 2 + 1) := by positivity
  apply (le_div_iff₀ hden).2
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
  have hpoly : (0 : ℝ) ≤ 3 * (q : ℝ) ^ 2 + 10 * q - 12 := by
    nlinarith
  have hprod := mul_nonneg hq1 hpoly
  nlinarith

/-- On every even T69 scale, the paired family has the normalized lower bound
`(4/5)*(q-1)`, where `q=2^(m+1)`. -/
theorem evenScale_normalized_lower (m : ℕ) :
    (4 / 5 : ℝ) * ((evenScaleBase m : ℝ) - 1) ≤
      pairedMass (evenScaleBase m) /
        ((H (2 * m) : ℝ) * N (2 * m)) := by
  rw [H_evenScale, N_evenScale]
  exact pairedMass_normalized_lower _ (evenScaleBase_two_le m)

/-- The mass is the literal sum of the two equal coefficients for every
`1 <= r < H_t`, with the exact interior length `N_t-r-1`. -/
theorem pairedMass_evenScale_literal (m : ℕ) :
    pairedMass (evenScaleBase m) =
      2 * ∑ j ∈ Finset.range (H (2 * m) - 1),
        ((H (2 * m) - (j + 1) : ℕ) : ℝ) *
          ((N (2 * m) - (j + 1) - 1 : ℕ) : ℝ) := by
  let q := evenScaleBase m
  have hq : 2 ≤ q := evenScaleBase_two_le m
  rw [pairedMass_eq_original q (by omega)]
  unfold originalPairedMass
  rw [H_evenScale, N_evenScale]
  change 2 * ∑ j ∈ Finset.range q,
      ((q - j : ℕ) : ℝ) * ((q ^ 2 - (j + 1) : ℕ) : ℝ) =
    2 * ∑ j ∈ Finset.range q,
      ((q + 1 - (j + 1) : ℕ) : ℝ) *
        ((q ^ 2 + 1 - (j + 1) - 1 : ℕ) : ℝ)
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjq : j < q := Finset.mem_range.mp hj
  congr 2 <;> omega

theorem evenScale_mass_exceeds
    (m : ℕ) (C : ℝ)
    (hC : C < (4 / 5 : ℝ) * ((evenScaleBase m : ℝ) - 1)) :
    C * ((H (2 * m) : ℝ) * N (2 * m)) <
      pairedMass (evenScaleBase m) := by
  have htarget : (0 : ℝ) < (H (2 * m) : ℝ) * N (2 * m) := by
    exact mul_pos (by exact_mod_cast H_pos (2 * m))
      (by exact_mod_cast (show 0 < N (2 * m) by
        have := five_le_N (2 * m)
        omega))
  have hratio : C < pairedMass (evenScaleBase m) /
      ((H (2 * m) : ℝ) * N (2 * m)) :=
    hC.trans_le (evenScale_normalized_lower m)
  exact (lt_div_iff₀ htarget).mp hratio

/-- Quantitative refutation exit: for every proposed constant, an even T69
scale has paired equal-frequency coefficient mass larger than `C*H_t*N_t`. -/
theorem exists_evenScale_mass_exceeds (C : ℝ) :
    ∃ m : ℕ,
      C * ((H (2 * m) : ℝ) * N (2 * m)) <
        pairedMass (evenScaleBase m) := by
  obtain ⟨m, hm⟩ :=
    pow_unbounded_of_one_lt ((5 / 4 : ℝ) * C + 1)
      (by norm_num : (1 : ℝ) < 2)
  have hmono : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) := by
    rw [pow_succ]
    have hp : (0 : ℝ) ≤ 2 ^ m := by positivity
    nlinarith
  have hbase : (5 / 4 : ℝ) * C + 1 < (evenScaleBase m : ℝ) := by
    rw [show (evenScaleBase m : ℝ) = (2 : ℝ) ^ (m + 1) by
      simp [evenScaleBase]]
    exact hm.trans_le hmono
  refine ⟨m, evenScale_mass_exceeds m C ?_⟩
  nlinarith

end Theory.PiDigits.LongLagBlockCollisionDecay.T81

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.adjacentSwap_mem
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.adjacentSwap_involutive
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.adjacentSwap_ne
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.equalFrequencyClass_exact
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.adjacentFrequency_eq
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.adjacentTerms_add
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.adjacentCoefficient_pos
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.leftBoundary_frequencyClass
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.rightBoundary_frequencyClass
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.unequalCutoff_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.N_evenScale
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.H_evenScale
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.pairedMass_evenScale_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.pairedMass_formula
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.pairedMass_normalized_lower
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T81.exists_evenScale_mass_exceeds
