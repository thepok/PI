import Mathlib

/-!
# T16: finite sparse-decimal arithmetic and weighted GCD

Canonical local source: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated problem has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module contains only the finite arithmetic sector suggested by the
unverified T15 note. It asserts no estimate for pi, no analytic tail bound,
and no almost-everywhere statement.

All exponent ranges are half-open `0 <= a < N`. Frequency ranges are the
inclusive interval `1 <= h <= 10^m`. Two-token signs are `(+,-)` and
four-token signs are `(+,+,-,-)`. Opposite signs may not occur at the same
exponent in a noncancelling form; equal-sign repetitions are allowed.
-/

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T16

noncomputable section

open Finset
open scoped BigOperators

/-- The inclusive frequency range `1 <= h <= 10^m`. -/
def decimalFrequencyDomain (m : ℕ) : Finset ℕ := Finset.Icc 1 (10 ^ m)

/-- The largest exponent `v` for which `10^v` divides `n` (zero at `n = 0`). -/
def tenValuation (n : ℕ) : ℕ := padicValNat 10 n

/-- The part left after removing the largest power of ten from `n`. -/
def tenPrimitivePart (n : ℕ) : ℕ := n.divMaxPow 10

/-- Exact composite-base reduction. This uses `divMaxPow`, not a
prime-only multiplicativity theorem for a 10-adic valuation. -/
theorem ten_reduction (n : ℕ) :
    10 ^ tenValuation n * tenPrimitivePart n = n := by
  exact Nat.pow_padicValNat_mul_divMaxPow 10 n

/-- A positive integer's base-ten primitive part is not divisible by ten. -/
theorem ten_not_dvd_primitivePart {n : ℕ} (hn : 0 < n) :
    ¬10 ∣ tenPrimitivePart n := by
  exact Nat.not_dvd_divMaxPow (by omega) (Nat.ne_of_gt hn)

/-- Membership audit for the inclusive decimal frequency domain. -/
theorem mem_decimalFrequencyDomain_iff {m h : ℕ} :
    h ∈ decimalFrequencyDomain m ↔ 1 ≤ h ∧ h ≤ 10 ^ m := by
  simp [decimalFrequencyDomain]

/-- Every legal frequency has valuation at most `m`; the endpoint `10^m`
is the only legal frequency with valuation exactly `m`. -/
theorem decimalFrequency_valuation_cases {m h : ℕ}
    (hh : h ∈ decimalFrequencyDomain m) :
    tenValuation h ≤ m ∧
      (tenValuation h = m ↔ h = 10 ^ m) ∧
      (tenValuation h < m ∨ h = 10 ^ m) := by
  have hrange := mem_decimalFrequencyDomain_iff.mp hh
  have hh0 : h ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hrange.1)
  have hdvd : 10 ^ tenValuation h ∣ h := pow_padicValNat_dvd
  have hpowle : 10 ^ tenValuation h ≤ h := Nat.le_of_dvd (by positivity) hdvd
  have hval : tenValuation h ≤ m := by
    by_contra hnot
    have hlt : m < tenValuation h := Nat.lt_of_not_ge hnot
    have hp_lt : 10 ^ m < 10 ^ tenValuation h := by
      exact Nat.pow_lt_pow_right (by omega) hlt
    omega
  have hendpoint : tenValuation h = m ↔ h = 10 ^ m := by
    constructor
    · intro hv
      have hp_le_h : 10 ^ m ≤ h := by
        rw [← hv]
        exact hpowle
      omega
    · rintro rfl
      simp [tenValuation]
  exact ⟨hval, hendpoint, hval.lt_or_eq.imp_right hendpoint.mp⟩

/-- Exact valuation after displaying a factorization by a power of ten and a
primitive factor. This is valid for composite base ten. -/
theorem tenValuation_pow_mul_of_not_dvd
    {ell k : ℕ} (hk : k ≠ 0) (hprimitive : ¬10 ∣ k) :
    tenValuation (10 ^ ell * k) = ell := by
  have hspec := Nat.maxPowDvdDiv_of_pow_mul_eq
    (p := 10) (n := 10 ^ ell * k) (k := ell) (l := k)
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) hk) rfl hprimitive
  exact congrArg Prod.fst hspec

/-- Complete lowest-coefficient cases for a noncancelling signed decimal
vector. Residues `1,2,8,9` are exactly `+1,+2,-2,-1` modulo ten. In every
case the 10-adic valuation is the lowest occupied exponent; no claim is made
that the remaining factor is odd or coprime to five separately. -/
theorem tenValuation_lowDecimalCoefficient
    (ell A c : ℕ) (hc : c = 1 ∨ c = 2 ∨ c = 8 ∨ c = 9) :
    tenValuation (10 ^ ell * (c + 10 * A)) = ell := by
  apply tenValuation_pow_mul_of_not_dvd
  · rcases hc with rfl | rfl | rfl | rfl <;> omega
  · rw [Nat.dvd_iff_mod_eq_zero]
    rcases hc with rfl | rfl | rfl | rfl <;> norm_num

/-- A positive decimal repunit is not divisible by ten. -/
theorem ten_not_dvd_pow_sub_one {r : ℕ} (hr : 1 ≤ r) :
    ¬10 ∣ 10 ^ r - 1 := by
  intro hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hadd : 10 ^ r - 1 + 1 = 10 ^ r :=
    Nat.sub_add_cancel (one_le_pow₀ (by norm_num))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_comm 1 k, Nat.pow_succ] at hq hadd
  omega

/-- Exact valuation and primitive part of every cancellation value
`10^v(10^r-1)`, with the complete range `v >= 0`, `r >= 1`. -/
theorem cancellationValue_ten_reduction (v r : ℕ) (hr : 1 ≤ r) :
    tenValuation (10 ^ v * (10 ^ r - 1)) = v ∧
      tenPrimitivePart (10 ^ v * (10 ^ r - 1)) = 10 ^ r - 1 := by
  have hrep_pos : 0 < 10 ^ r - 1 := by
    have : 1 < 10 ^ r := Nat.one_lt_pow (Nat.ne_of_gt hr) (by norm_num)
    omega
  have hspec := Nat.maxPowDvdDiv_of_pow_mul_eq
    (p := 10) (n := 10 ^ v * (10 ^ r - 1))
    (k := v) (l := 10 ^ r - 1)
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.ne_of_gt hrep_pos))
    rfl (ten_not_dvd_pow_sub_one hr)
  exact ⟨congrArg Prod.fst hspec, congrArg Prod.snd hspec⟩

/-- Evaluation of a labeled signed decimal token form. `true` is positive
and `false` is negative. -/
def signedDecimalValue {s : ℕ} (sign : Fin s → Bool)
    (exponent : Fin s → ℕ) : ℤ :=
  ∑ i, if sign i then (10 : ℤ) ^ exponent i else -((10 : ℤ) ^ exponent i)

/-- No exponent carries tokens of opposite signs. Equal-sign repetitions are
allowed, as required for coefficients `+2` and `-2`. -/
def Noncancelling {s : ℕ} (sign : Fin s → Bool)
    (exponent : Fin s → ℕ) : Prop :=
  ∀ i j, exponent i = exponent j → sign i = sign j

/-- The prescribed signs `(+,-)` for a cancellation value. -/
def twoTokenSign (i : Fin 2) : Bool := i.1 = 0

/-- The prescribed signs `(+,+,-,-)` for a primitive four-token value. -/
def fourTokenSign (i : Fin 4) : Bool := i.1 < 2

/-- A positive natural value extracted from a signed token form. Positivity
is always retained explicitly in theorem hypotheses. -/
def signedDecimalNatValue {s : ℕ} (sign : Fin s → Bool)
    (exponent : Fin s → ℕ) : ℕ :=
  (signedDecimalValue sign exponent).toNat

/-- Full reduced-ratio height `max(x,y)/gcd(x,y)`. It retains every ordinary
2-adic, 5-adic, odd, and cyclotomic common factor. -/
def reducedRatioHeight (x y : ℕ) : ℚ :=
  (Nat.max x y : ℚ) / (Nat.gcd x y : ℚ)

/-- The explicit reduced-ratio condition used by the sparse-neighbor lemma. -/
def ReducedRatioAtMost (x y K : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ reducedRatioHeight x y ≤ K

/-- The graph joining distinct decimal tokens whose exponents differ by less than `J`. -/
def proximityGraph {n : ℕ} (a : Fin n → ℕ) (J : ℕ) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => Nat.dist (a i) (a j) < J

/-- Adjacency in `proximityGraph` is exactly distinctness and exponent distance below `J`. -/
theorem proximityGraph_adj_iff {n : ℕ} (a : Fin n → ℕ) (J : ℕ)
    (i j : Fin n) :
    (proximityGraph a J).Adj i j ↔
      i ≠ j ∧ Nat.dist (a i) (a j) < J := by
  simp [proximityGraph, Nat.dist_comm]

/-- A token whose exponent lies between two connected token exponents belongs to their component. -/
theorem proximity_reachable_of_between
    {n J : ℕ} (a : Fin n → ℕ) (hJ : 0 < J) {x y z : Fin n}
    (hreach : (proximityGraph a J).Reachable x z)
    (hxy : a x ≤ a y) (hyz : a y ≤ a z) :
    (proximityGraph a J).Reachable x y := by
  rcases hreach with ⟨w⟩
  induction w with
  | @nil u =>
      by_cases huy : u = y
      · subst y
        exact SimpleGraph.Reachable.rfl
      · exact ((proximityGraph_adj_iff a J u y).mpr
          ⟨huy, by simp [Nat.le_antisymm hxy hyz, hJ]⟩).reachable
  | @cons u v z huv w ih =>
      by_cases hyv : a y ≤ a v
      · by_cases huy : u = y
        · subst y
          exact SimpleGraph.Reachable.rfl
        · apply ((proximityGraph_adj_iff a J u y).mpr ⟨huy, ?_⟩).reachable
          have huv' := (proximityGraph_adj_iff a J u v).mp huv
          rw [Nat.dist_eq_sub_of_le (hxy.trans hyv)] at huv'
          rw [Nat.dist_eq_sub_of_le hxy]
          omega
      · exact huv.reachable.trans (ih (by omega) hyz)

/-- A decimal upper sum vanishes when it is separated from all lower exponents by a `J`-gap.
The `q < J` branch is handled by proving that the lower sum is empty. -/
theorem decimal_upper_sum_eq_zero
    {n K J q : ℕ} (a : Fin n → ℕ) (c : Fin n → ℤ)
    (hc : ∀ i, (c i).natAbs ≤ K)
    (hscale : n * K < 10 ^ J)
    (hsum : ∑ i, c i * (10 : ℤ) ^ a i = 0)
    (hgap : ∀ i, a i < q → J ≤ q - a i) :
    ∑ i ∈ Finset.univ.filter (fun i => q ≤ a i),
      c i * (10 : ℤ) ^ a i = 0 := by
  classical
  let upper : Finset (Fin n) := Finset.univ.filter (fun i => q ≤ a i)
  let lower : Finset (Fin n) := Finset.univ.filter (fun i => a i < q)
  have hpart : lower = upperᶜ := by
    ext i
    simp [upper, lower]
  have htotal :
      (∑ i ∈ upper, c i * (10 : ℤ) ^ a i) +
        ∑ i ∈ lower, c i * (10 : ℤ) ^ a i = 0 := by
    rw [hpart, Finset.sum_add_sum_compl]
    exact hsum
  have hdiv : (10 : ℤ) ^ q ∣ ∑ i ∈ upper, c i * (10 : ℤ) ^ a i := by
    apply Finset.dvd_sum
    intro i hi
    have hqi : q ≤ a i := (Finset.mem_filter.mp hi).2
    exact dvd_mul_of_dvd_right (pow_dvd_pow (10 : ℤ) hqi) _
  by_contra hne
  have hpow_le : 10 ^ q ≤
      (∑ i ∈ upper, c i * (10 : ℤ) ^ a i).natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hne
  have heqabs :
      (∑ i ∈ upper, c i * (10 : ℤ) ^ a i).natAbs =
        (∑ i ∈ lower, c i * (10 : ℤ) ^ a i).natAbs := by
    have heq := eq_neg_of_add_eq_zero_left htotal
    rw [heq, Int.natAbs_neg]
  have hlower_bound :
      (∑ i ∈ lower, c i * (10 : ℤ) ^ a i).natAbs ≤
        n * K * 10 ^ (q - J) := by
    calc
      (∑ i ∈ lower, c i * (10 : ℤ) ^ a i).natAbs
          ≤ ∑ i ∈ lower, (c i * (10 : ℤ) ^ a i).natAbs :=
        Int.natAbs_sum_le lower fun i => c i * (10 : ℤ) ^ a i
      _ = ∑ i ∈ lower, (c i).natAbs * 10 ^ a i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Int.natAbs_mul, Int.natAbs_pow]
        norm_num
      _ ≤ ∑ _i ∈ lower, K * 10 ^ (q - J) := by
        apply Finset.sum_le_sum
        intro i hi
        have hai : a i < q := (Finset.mem_filter.mp hi).2
        by_cases hqJ : q < J
        · have : q - a i < J := by omega
          exact (not_lt_of_ge (hgap i hai) this).elim
        · have haiq : a i ≤ q - J := by
            have := hgap i hai
            omega
          exact Nat.mul_le_mul (hc i) (Nat.pow_le_pow_right (by omega) haiq)
      _ = lower.card * (K * 10 ^ (q - J)) := by simp
      _ ≤ n * (K * 10 ^ (q - J)) := by
        gcongr
        simpa using lower.card_le_univ
      _ = n * K * 10 ^ (q - J) := by simp [Nat.mul_assoc]
  by_cases hqJ : q < J
  · have hempty : lower = ∅ := by
      ext i
      constructor
      · intro hi
        have hai : a i < q := (Finset.mem_filter.mp hi).2
        have hsmall : q - a i < J := by omega
        exact (not_lt_of_ge (hgap i hai) hsmall).elim
      · simp
    have hzeroabs :
        (∑ i ∈ upper, c i * (10 : ℤ) ^ a i).natAbs = 0 := by
      simpa [hempty] using heqabs
    exact hne (Int.natAbs_eq_zero.mp hzeroabs)
  · have hpowpos : 0 < 10 ^ (q - J) := by positivity
    have hm := Nat.mul_lt_mul_of_pos_right hscale hpowpos
    rw [← pow_add] at hm
    have hJq : J + (q - J) = q := by omega
    have hstrict : n * K * 10 ^ (q - J) < 10 ^ q := by
      simpa [hJq, Nat.mul_assoc] using hm
    rw [heqabs] at hpow_le
    omega

/-- The finite vertex set of the proximity component containing `v`. -/
noncomputable def proximityComponent {n : ℕ}
    (a : Fin n → ℕ) (J : ℕ) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    (proximityGraph a J).connectedComponentMk i =
      (proximityGraph a J).connectedComponentMk v

/-- Every proximity component of a bounded-coefficient zero decimal sum has sum zero. -/
theorem proximity_component_sum_eq_zero
    {n K J : ℕ} (a : Fin n → ℕ) (c : Fin n → ℤ)
    (hc : ∀ i, (c i).natAbs ≤ K)
    (hK : 1 ≤ K)
    (hscale : n * K < 10 ^ J)
    (hsum : ∑ i, c i * (10 : ℤ) ^ a i = 0)
    (v : Fin n) :
    ∑ i ∈ proximityComponent a J v,
      c i * (10 : ℤ) ^ a i = 0 := by
  classical
  let G := proximityGraph a J
  letI : DecidableEq G.ConnectedComponent := Classical.decEq _
  let C : Finset (Fin n) := proximityComponent a J v
  have hJ : 0 < J := by
    by_contra h
    have hJ0 : J = 0 := by omega
    simp [hJ0] at hscale
    have hn : 0 < n := Nat.zero_lt_of_lt v.isLt
    omega
  have hvC : v ∈ C := by simp [C, proximityComponent]
  have hCne : C.Nonempty := ⟨v, hvC⟩
  have hAne : (C.image a).Nonempty := hCne.image a
  let r := (C.image a).min' hAne
  let R := (C.image a).max' hAne
  have hrmem : r ∈ C.image a := by exact Finset.min'_mem _ _
  have hRmem : R ∈ C.image a := by exact Finset.max'_mem _ _
  obtain ⟨vr, hvrC, havr⟩ := Finset.mem_image.mp hrmem
  obtain ⟨vR, hvRC, havR⟩ := Finset.mem_image.mp hRmem
  have hrR : r ≤ R := by
    exact (C.image a).min'_le _ hRmem
  have hr_le {i : Fin n} (hi : i ∈ C) : r ≤ a i := by
    exact (C.image a).min'_le (a i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hle_R {i : Fin n} (hi : i ∈ C) : a i ≤ R := by
    exact (C.image a).le_max' (a i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hvrvR : G.Reachable vr vR := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    have hvr : G.connectedComponentMk vr = G.connectedComponentMk v :=
      by simpa [C, proximityComponent, G] using hvrC
    have hvR : G.connectedComponentMk vR = G.connectedComponentMk v :=
      by simpa [C, proximityComponent, G] using hvRC
    exact hvr.trans hvR.symm
  have hinterval {i : Fin n} (hri : r ≤ a i) (hiR : a i ≤ R) : i ∈ C := by
    have hreach : G.Reachable vr i := by
      apply proximity_reachable_of_between a hJ hvrvR
      · simpa [havr] using hri
      · simpa [havR] using hiR
    have hcomp : G.connectedComponentMk i = G.connectedComponentMk vr :=
      (SimpleGraph.ConnectedComponent.eq.mpr hreach).symm
    have hvr : G.connectedComponentMk vr = G.connectedComponentMk v :=
      by simpa [C, proximityComponent, G] using hvrC
    simpa [C, proximityComponent, G] using hcomp.trans hvr
  have hgap_r : ∀ i, a i < r → J ≤ r - a i := by
    intro i hir
    by_contra hgap
    have hdist : Nat.dist (a i) (a vr) < J := by
      rw [havr, Nat.dist_eq_sub_of_le hir.le]
      omega
    have hine : i ≠ vr := by
      intro heq
      subst i
      omega
    have hadj : G.Adj i vr := by
      exact (proximityGraph_adj_iff a J i vr).mpr ⟨hine, hdist⟩
    have hicomp : G.connectedComponentMk i = G.connectedComponentMk v := by
      have hivr := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have hvr : G.connectedComponentMk vr = G.connectedComponentMk v :=
        by simpa [C, proximityComponent, G] using hvrC
      exact hivr.trans hvr
    have hiC : i ∈ C := by simpa [C, proximityComponent, G] using hicomp
    exact (not_lt_of_ge (hr_le hiC) hir)
  have habove_gap {i : Fin n} (hRi : R < a i) : R + J ≤ a i := by
    by_contra hgap
    have hdist : Nat.dist (a vR) (a i) < J := by
      rw [havR, Nat.dist_eq_sub_of_le hRi.le]
      omega
    have hine : vR ≠ i := by
      intro heq
      subst i
      omega
    have hadj : G.Adj vR i := by
      exact (proximityGraph_adj_iff a J vR i).mpr ⟨hine, hdist⟩
    have hicomp : G.connectedComponentMk i = G.connectedComponentMk v := by
      have hvRi := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have hvR : G.connectedComponentMk vR = G.connectedComponentMk v :=
        by simpa [C, proximityComponent, G] using hvRC
      exact hvRi.symm.trans hvR
    have hiC : i ∈ C := by simpa [C, proximityComponent, G] using hicomp
    exact (not_lt_of_ge (hle_R hiC) hRi)
  have hgap_R : ∀ i, a i < R + J → J ≤ R + J - a i := by
    intro i hiq
    by_contra hgap
    have hRi : R < a i := by omega
    have := habove_gap hRi
    omega
  have hupper_r := decimal_upper_sum_eq_zero a c hc hscale hsum hgap_r
  have hupper_R := decimal_upper_sum_eq_zero a c hc hscale hsum hgap_R
  let U : Finset (Fin n) := Finset.univ.filter (fun i => R + J ≤ a i)
  have hdecomp : Finset.univ.filter (fun i => r ≤ a i) = C ∪ U := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hri
      by_cases hiR : a i ≤ R
      · exact Or.inl (hinterval hri hiR)
      · exact Or.inr (by simpa [U] using habove_gap (by omega))
    · rintro (hiC | hiU)
      · exact hr_le hiC
      · have : R + J ≤ a i := by simpa [U] using hiU
        omega
  have hdisj : Disjoint C U := by
    apply Finset.disjoint_left.mpr
    intro i hiC hiU
    have haiR := hle_R hiC
    have : R + J ≤ a i := by simpa [U] using hiU
    omega
  have hsum_decomp :
      (∑ i ∈ Finset.univ.filter (fun i => r ≤ a i), c i * (10 : ℤ) ^ a i) =
        (∑ i ∈ C, c i * (10 : ℤ) ^ a i) +
          ∑ i ∈ U, c i * (10 : ℤ) ^ a i := by
    rw [hdecomp, Finset.sum_union hdisj]
  have hUzero : ∑ i ∈ U, c i * (10 : ℤ) ^ a i = 0 := by
    simpa [U] using hupper_R
  have hCzero : ∑ i ∈ C, c i * (10 : ℤ) ^ a i = 0 := by
    rw [hsum_decomp, hUzero, add_zero] at hupper_r
    exact hupper_r
  simpa [C] using hCzero

/-- A nonempty subsum of at most four noncancelling signed decimal tokens is nonzero. -/
theorem noncancelling_subsum_ne_zero
    {n : ℕ} (hn : n ≤ 4) (sign : Fin n → Bool) (a : Fin n → ℕ)
    (hnc : Noncancelling sign a) (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∑ i ∈ S, (if sign i then (10 : ℤ) ^ a i else -((10 : ℤ) ^ a i)) ≠ 0 := by
  classical
  have hAne : (S.image a).Nonempty := hS.image a
  let r := (S.image a).min' hAne
  have hrmem : r ∈ S.image a := Finset.min'_mem _ _
  obtain ⟨i0, hi0S, hai0⟩ := Finset.mem_image.mp hrmem
  let M := S.filter fun i => a i = r
  let H := S.filter fun i => r < a i
  have hi0M : i0 ∈ M := by simp [M, hi0S, hai0]
  have hMne : M.Nonempty := ⟨i0, hi0M⟩
  have hr_le {i : Fin n} (hi : i ∈ S) : r ≤ a i := by
    exact (S.image a).min'_le (a i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hpart : S = M ∪ H := by
    ext i
    simp only [M, H, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hiS
      have := hr_le hiS
      rcases this.eq_or_lt with heq | hlt
      · exact Or.inl ⟨hiS, heq.symm⟩
      · exact Or.inr ⟨hiS, hlt⟩
    · rintro (⟨hiS, _⟩ | ⟨hiS, _⟩) <;> exact hiS
  have hdisj : Disjoint M H := by
    apply Finset.disjoint_left.mpr
    intro i hiM hiH
    have hei : a i = r := (Finset.mem_filter.mp hiM).2
    have hri : r < a i := (Finset.mem_filter.mp hiH).2
    omega
  have hsign {i : Fin n} (hiM : i ∈ M) : sign i = sign i0 := by
    apply hnc
    have hi : a i = r := (Finset.mem_filter.mp hiM).2
    omega
  let low : ℤ := ∑ i ∈ M,
    (if sign i then (10 : ℤ) ^ a i else -((10 : ℤ) ^ a i))
  let high : ℤ := ∑ i ∈ H,
    (if sign i then (10 : ℤ) ^ a i else -((10 : ℤ) ^ a i))
  have hlow : low = if sign i0 then (M.card : ℤ) * (10 : ℤ) ^ r
      else -((M.card : ℤ) * (10 : ℤ) ^ r) := by
    dsimp [low]
    by_cases hs : sign i0
    · simp only [hs, ↓reduceIte]
      calc
        ∑ i ∈ M, (if sign i then (10 : ℤ) ^ a i else -((10 : ℤ) ^ a i)) =
            ∑ _i ∈ M, (10 : ℤ) ^ r := by
          apply Finset.sum_congr rfl
          intro i hiM
          simp [hsign hiM, hs, (Finset.mem_filter.mp hiM).2]
        _ = (M.card : ℤ) * (10 : ℤ) ^ r := by simp
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      calc
        ∑ i ∈ M, (if sign i then (10 : ℤ) ^ a i else -((10 : ℤ) ^ a i)) =
            ∑ _i ∈ M, -((10 : ℤ) ^ r) := by
          apply Finset.sum_congr rfl
          intro i hiM
          simp [hsign hiM, hs, (Finset.mem_filter.mp hiM).2]
        _ = -((M.card : ℤ) * (10 : ℤ) ^ r) := by simp
  have hlow_ne : low ≠ 0 := by
    rw [hlow]
    have hcardpos : 0 < M.card := Finset.card_pos.mpr hMne
    have hcastpos : (0 : ℤ) < M.card := by exact_mod_cast hcardpos
    split
    · exact mul_ne_zero (ne_of_gt hcastpos) (pow_ne_zero _ (by norm_num))
    · exact neg_ne_zero.mpr (mul_ne_zero (ne_of_gt hcastpos) (pow_ne_zero _ (by norm_num)))
  have hlow_abs : low.natAbs = M.card * 10 ^ r := by
    rw [hlow]
    split <;> simp only [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast,
      Int.natAbs_pow] <;> norm_num
  have hhigh_div : (10 : ℤ) ^ (r + 1) ∣ high := by
    dsimp [high]
    apply Finset.dvd_sum
    intro i hiH
    have hri : r < a i := (Finset.mem_filter.mp hiH).2
    split
    · exact pow_dvd_pow (10 : ℤ) (by omega)
    · exact dvd_neg.mpr (pow_dvd_pow (10 : ℤ) (by omega))
  intro hzero
  have htotal : low + high = 0 := by
    dsimp [low, high]
    rw [← Finset.sum_union hdisj, ← hpart]
    exact hzero
  have hlow_div : (10 : ℤ) ^ (r + 1) ∣ low := by
    have heq : low = -high := eq_neg_of_add_eq_zero_left htotal
    rw [heq]
    exact dvd_neg.mpr hhigh_div
  have hp_le : 10 ^ (r + 1) ≤ low.natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hlow_div hlow_ne
  have hcard : M.card ≤ 4 := (M.card_le_univ.trans (by simpa using hn))
  have habs_lt : low.natAbs < 10 ^ (r + 1) := by
    rw [hlow_abs, pow_succ]
    have hp : 0 < 10 ^ r := by positivity
    nlinarith
  omega

/-- A bounded reduced-ratio height supplies positive bounded cross-multipliers. -/
theorem reducedRatio_exists_coefficients {x y K : ℕ}
    (h : ReducedRatioAtMost x y K) :
    ∃ p q : ℕ, 1 ≤ p ∧ p ≤ K ∧ 1 ≤ q ∧ q ≤ K ∧ p * x = q * y := by
  obtain ⟨hx, hy, hheight⟩ := h
  let g := Nat.gcd x y
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hgx : g ∣ x := Nat.gcd_dvd_left x y
  have hgy : g ∣ y := Nat.gcd_dvd_right x y
  have hgmax : g ∣ Nat.max x y := by
    by_cases hxy : x ≤ y
    · simpa [Nat.max_eq_right hxy] using hgy
    · simpa [Nat.max_eq_left (le_of_not_ge hxy)] using hgx
  have hquot : Nat.max x y / g ≤ K := by
    have hcast : ((Nat.max x y / g : ℕ) : ℚ) ≤ K := by
      rw [Nat.cast_div hgmax (by positivity)]
      simpa [reducedRatioHeight, g] using hheight
    exact_mod_cast hcast
  refine ⟨y / g, x / g, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.gcd_le_right x hy) hg
  · exact (Nat.div_le_div_right (Nat.le_max_right x y)).trans hquot
  · exact Nat.div_pos (Nat.gcd_le_left y hx) hg
  · exact (Nat.div_le_div_right (Nat.le_max_left x y)).trans hquot
  · have hxred : g * (x / g) = x := Nat.mul_div_cancel' hgx
    have hyred : g * (y / g) = y := Nat.mul_div_cancel' hgy
    calc
      (y / g) * x = (y / g) * (g * (x / g)) := by rw [hxred]
      _ = (x / g) * (g * (y / g)) := by ac_rfl
      _ = (x / g) * y := by rw [hyred]

/-- Triangle inequality for `Nat.dist`. -/
theorem nat_dist_triangle (a b c : ℕ) :
    Nat.dist a c ≤ Nat.dist a b + Nat.dist b c := by
  rcases le_total a c with hac | hca
  · rw [Nat.dist_eq_sub_of_le hac]
    rcases le_total a b with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      rcases le_total b c with hbc | hcb
      · rw [Nat.dist_eq_sub_of_le hbc]
        omega
      · rw [Nat.dist_comm b c, Nat.dist_eq_sub_of_le hcb]
        omega
    · rw [Nat.dist_comm a b, Nat.dist_eq_sub_of_le hba]
      rw [Nat.dist_eq_sub_of_le (hba.trans hac)]
      omega
  · rw [Nat.dist_comm a c, Nat.dist_eq_sub_of_le hca]
    rcases le_total a b with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      rw [Nat.dist_comm b c]
      rcases le_total c b with hcb | hbc
      · rw [Nat.dist_eq_sub_of_le hcb]
        omega
      · rw [Nat.dist_comm c b, Nat.dist_eq_sub_of_le hbc]
        omega
    · rw [Nat.dist_comm a b, Nat.dist_eq_sub_of_le hba]
      rw [Nat.dist_comm b c]
      rcases le_total c b with hcb | hbc
      · rw [Nat.dist_eq_sub_of_le hcb]
        omega
      · rw [Nat.dist_comm c b, Nat.dist_eq_sub_of_le hbc]
        omega

/-- Exponent distance along a proximity-graph walk is bounded by its length times `J - 1`. -/
theorem proximity_walk_dist_le
    {n J : ℕ} (a : Fin n → ℕ) {x y : Fin n}
    (p : (proximityGraph a J).Walk x y) :
    Nat.dist (a x) (a y) ≤ p.length * (J - 1) := by
  induction p with
  | @nil u => simp
  | @cons u v w huv p ih =>
      have hedge : Nat.dist (a u) (a v) ≤ J - 1 := by
        have := (proximityGraph_adj_iff a J u v).mp huv
        omega
      calc
        Nat.dist (a u) (a w) ≤ Nat.dist (a u) (a v) + Nat.dist (a v) (a w) :=
          nat_dist_triangle _ _ _
        _ ≤ (J - 1) + p.length * (J - 1) := Nat.add_le_add hedge ih
        _ = (SimpleGraph.Walk.cons huv p).length * (J - 1) := by
          simp [Nat.add_mul, Nat.add_comm]

/-- Sparse-decimal rational-neighbor estimate. All token-count, positivity,
noncancellation, reduced-ratio, and scale hypotheses are explicit. The
conclusion is the T15 radius `(s+u-1)(J-1)`, including the cases `s,u <= 4`.
-/
theorem sparseDecimal_rationalNeighbor
    {s u K J : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ)
    (sy : Fin u → Bool) (ay : Fin u → ℕ)
    (hxc : Noncancelling sx ax)
    (hyc : Noncancelling sy ay)
    (hx : 0 < signedDecimalValue sx ax)
    (hy : 0 < signedDecimalValue sy ay)
    (hK : 1 ≤ K)
    (hscale : (s + u) * K < 10 ^ J)
    (hratio : ReducedRatioAtMost
      (signedDecimalNatValue sx ax) (signedDecimalNatValue sy ay) K) :
    ∀ i : Fin u, ∃ j : Fin s,
      Nat.dist (ay i) (ax j) ≤ (s + u - 1) * (J - 1) := by
  classical
  let x := signedDecimalNatValue sx ax
  let y := signedDecimalNatValue sy ay
  obtain ⟨p, q, hp, hpK, hq, hqK, hpq⟩ :=
    reducedRatio_exists_coefficients (x := x) (y := y) hratio
  let a : Fin (s + u) → ℕ := Fin.addCases ax ay
  let c : Fin (s + u) → ℤ := Fin.addCases
    (fun j => if sx j then (p : ℤ) else -(p : ℤ))
    (fun i => if sy i then -(q : ℤ) else (q : ℤ))
  have hc : ∀ v, (c v).natAbs ≤ K := by
    intro v
    refine Fin.addCases (fun j => ?_) (fun i => ?_) v
    · simp only [c, Fin.addCases_left]
      split <;> simp_all
    · simp only [c, Fin.addCases_right]
      split <;> simp_all
  have hxcast : (x : ℤ) = signedDecimalValue sx ax := by
    simp [x, signedDecimalNatValue, Int.toNat_of_nonneg hx.le]
  have hycast : (y : ℤ) = signedDecimalValue sy ay := by
    simp [y, signedDecimalNatValue, Int.toNat_of_nonneg hy.le]
  have hpqZ : (p : ℤ) * signedDecimalValue sx ax =
      (q : ℤ) * signedDecimalValue sy ay := by
    rw [← hxcast, ← hycast]
    exact_mod_cast hpq
  have hsum : ∑ v, c v * (10 : ℤ) ^ a v = 0 := by
    rw [Fin.sum_univ_add]
    simp only [a, c, Fin.addCases_left, Fin.addCases_right]
    have hxsum :
        (∑ j, (if sx j then (p : ℤ) else -(p : ℤ)) * (10 : ℤ) ^ ax j) =
          (p : ℤ) * signedDecimalValue sx ax := by
      rw [signedDecimalValue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hsxj : sx j <;> simp [hsxj]
    have hysum :
        (∑ i, (if sy i then -(q : ℤ) else (q : ℤ)) * (10 : ℤ) ^ ay i) =
          -((q : ℤ) * signedDecimalValue sy ay) := by
      rw [signedDecimalValue, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hsyk : sy k <;> simp [hsyk]
    rw [hxsum, hysum]
    exact sub_eq_zero.mpr hpqZ
  intro i
  let vy : Fin (s + u) := Fin.natAdd s i
  let C : Finset (Fin (s + u)) := proximityComponent a J vy
  have hCsum : ∑ v ∈ C, c v * (10 : ℤ) ^ a v = 0 := by
    exact proximity_component_sum_eq_zero a c hc hK hscale hsum vy
  have hex : ∃ j : Fin s, Fin.castAdd u j ∈ C := by
    by_contra hnone
    push Not at hnone
    let S : Finset (Fin u) := Finset.univ.filter fun k => Fin.natAdd s k ∈ C
    have hiS : i ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [C, proximityComponent, vy]
    have hSne : S.Nonempty := ⟨i, hiS⟩
    have hcompare :
        (∑ v ∈ C, c v * (10 : ℤ) ^ a v) =
          -((q : ℤ) * ∑ k ∈ S,
            (if sy k then (10 : ℤ) ^ ay k else -((10 : ℤ) ^ ay k))) := by
      have hrewrite : (∑ v ∈ C, c v * (10 : ℤ) ^ a v) =
          ∑ v, if v ∈ C then c v * (10 : ℤ) ^ a v else 0 := by
        simp
      rw [hrewrite]
      rw [Fin.sum_univ_add]
      have hxzero :
          (∑ j : Fin s,
            if Fin.castAdd u j ∈ C then
              c (Fin.castAdd u j) * (10 : ℤ) ^ a (Fin.castAdd u j) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp [hnone j]
      rw [hxzero, zero_add]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      have hrhs :
          (∑ k ∈ S, -((q : ℤ) *
            (if sy k then (10 : ℤ) ^ ay k else -((10 : ℤ) ^ ay k)))) =
          ∑ k, if Fin.natAdd s k ∈ C then
            c (Fin.natAdd s k) * (10 : ℤ) ^ a (Fin.natAdd s k) else 0 := by
        rw [show S = Finset.univ.filter (fun k => Fin.natAdd s k ∈ C) by rfl]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hmem : Fin.natAdd s k ∈ C
        · simp only [hmem, ↓reduceIte, a, c, Fin.addCases_right]
          by_cases hsy : sy k <;> simp [hsy]
        · simp [hmem]
      exact hrhs.symm
    have hsubzero : ∑ k ∈ S,
        (if sy k then (10 : ℤ) ^ ay k else -((10 : ℤ) ^ ay k)) = 0 := by
      have hprod : (q : ℤ) * ∑ k ∈ S,
          (if sy k then (10 : ℤ) ^ ay k else -((10 : ℤ) ^ ay k)) = 0 := by
        have := hCsum
        rw [hcompare] at this
        simpa using neg_eq_zero.mp this
      exact (mul_eq_zero.mp hprod).resolve_left (by positivity)
    exact (noncancelling_subsum_ne_zero hu4 sy ay hyc S hSne) hsubzero
  obtain ⟨j, hjC⟩ := hex
  have hreach : (proximityGraph a J).Reachable vy (Fin.castAdd u j) := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    have hjcomp : (proximityGraph a J).connectedComponentMk (Fin.castAdd u j) =
        (proximityGraph a J).connectedComponentMk vy := by
      simpa [C, proximityComponent] using hjC
    exact hjcomp.symm
  obtain ⟨path, hpath⟩ := hreach.exists_isPath
  have hlength : path.length ≤ s + u - 1 := by
    have := hpath.length_lt
    simp only [Fintype.card_fin] at this
    omega
  have hdist := proximity_walk_dist_le a path
  have ha_vy : a vy = ay i := by simp [a, vy]
  have ha_x : a (Fin.castAdd u j) = ax j := by simp [a]
  rw [ha_vy, ha_x] at hdist
  exact ⟨j, hdist.trans (Nat.mul_le_mul_right (J - 1) hlength)⟩

/-- Exponent vectors in the exact half-open box `0 <= a_i < N`. -/
abbrev BoundedExponentVector (s N : ℕ) := Fin s → Fin N

/-- Coerce a bounded exponent vector to natural exponents. -/
def exponentNat {s N : ℕ} (a : BoundedExponentVector s N) : Fin s → ℕ :=
  fun i => (a i).1

/-- Exponents in `Fin N` lying within natural distance `R` of `center`. -/
def exponentNeighborhood (N center R : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun a => Nat.dist a.1 center ≤ R

/-- Membership in a one-center exponent neighborhood. -/
theorem mem_exponentNeighborhood_iff {N center R : ℕ} {a : Fin N} :
    a ∈ exponentNeighborhood N center R ↔ Nat.dist a.1 center ≤ R := by
  simp [exponentNeighborhood]

/-- A natural number within distance `R` of `center` lies in the corresponding
inclusive integer interval. -/
theorem nat_bounds_of_dist_le {a center R : ℕ} (h : Nat.dist a center ≤ R) :
    center - R ≤ a ∧ a ≤ center + R := by
  rcases le_total a center with hac | hca
  · rw [Nat.dist_eq_sub_of_le hac] at h
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hca] at h
    omega

/-- A radius-`R` exponent neighborhood contains at most `2R+1` points. -/
theorem exponentNeighborhood_card_le (N center R : ℕ) :
    (exponentNeighborhood N center R).card ≤ 2 * R + 1 := by
  classical
  let values := (exponentNeighborhood N center R).image fun a => a.1
  have hvalues : values ⊆ Finset.Icc (center - R) (center + R) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Icc.mpr
      (nat_bounds_of_dist_le (mem_exponentNeighborhood_iff.mp hb))
  calc
    (exponentNeighborhood N center R).card = values.card := by
      dsimp [values]
      exact (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.Icc (center - R) (center + R)).card := Finset.card_le_card hvalues
    _ ≤ 2 * R + 1 := by
      rw [Nat.card_Icc]
      omega

/-- The union, inside `Fin N`, of radius-`R` neighborhoods around all labeled
source exponents. -/
def sourceExponentNeighborhood {s : ℕ} (ax : Fin s → ℕ) (N R : ℕ) :
    Finset (Fin N) :=
  Finset.univ.biUnion fun j => exponentNeighborhood N (ax j) R

/-- Membership in the source-neighborhood union is witnessed by a labeled
source exponent. -/
theorem mem_sourceExponentNeighborhood_iff {s N R : ℕ} {ax : Fin s → ℕ}
    {a : Fin N} :
    a ∈ sourceExponentNeighborhood ax N R ↔
      ∃ j : Fin s, Nat.dist a.1 (ax j) ≤ R := by
  classical
  simp [sourceExponentNeighborhood, mem_exponentNeighborhood_iff]

/-- The union of `s` radius-`R` exponent neighborhoods has cardinality at most
`s(2R+1)`. -/
theorem sourceExponentNeighborhood_card_le {s : ℕ} (ax : Fin s → ℕ) (N R : ℕ) :
    (sourceExponentNeighborhood ax N R).card ≤ s * (2 * R + 1) := by
  classical
  simpa [sourceExponentNeighborhood] using
    (Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin s))
      (fun j => exponentNeighborhood N (ax j) R) (2 * R + 1)
      (fun j _ => exponentNeighborhood_card_le N (ax j) R))

/-- All labeled target exponent vectors whose coordinates lie in the union of
the source-centered radius-`R` neighborhoods. -/
def sourceExponentVectorNeighborhood {s u N : ℕ} (ax : Fin s → ℕ) (R : ℕ) :
    Finset (BoundedExponentVector u N) :=
  Fintype.piFinset fun _ : Fin u => sourceExponentNeighborhood ax N R

/-- Membership in the vector neighborhood is pointwise membership in the
source-neighborhood union. -/
theorem mem_sourceExponentVectorNeighborhood_iff {s u N R : ℕ}
    {ax : Fin s → ℕ} {a : BoundedExponentVector u N} :
    a ∈ sourceExponentVectorNeighborhood ax R ↔
      ∀ i : Fin u, ∃ j : Fin s, Nat.dist (a i).1 (ax j) ≤ R := by
  classical
  simp [sourceExponentVectorNeighborhood, mem_sourceExponentNeighborhood_iff]

/-- The finite rational-neighbor domain for a fixed source form and prescribed
target signs. Target noncancellation, positivity, and reduced-ratio height are
part of membership. -/
def sparseDecimalRationalNeighborDomain {s u : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (N K : ℕ) : Finset (BoundedExponentVector u N) := by
  classical
  exact Finset.univ.filter fun a =>
    Noncancelling sy (exponentNat a) ∧
      0 < signedDecimalValue sy (exponentNat a) ∧
      ReducedRatioAtMost (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a)) K

/-- Membership audit for the finite rational-neighbor domain. -/
theorem mem_sparseDecimalRationalNeighborDomain_iff {s u N K : ℕ}
    {sx : Fin s → Bool} {ax : Fin s → ℕ} {sy : Fin u → Bool}
    {a : BoundedExponentVector u N} :
    a ∈ sparseDecimalRationalNeighborDomain sx ax sy N K ↔
      Noncancelling sy (exponentNat a) ∧
        0 < signedDecimalValue sy (exponentNat a) ∧
        ReducedRatioAtMost (signedDecimalNatValue sx ax)
          (signedDecimalNatValue sy (exponentNat a)) K := by
  simp [sparseDecimalRationalNeighborDomain]

/-- Cardinality of a source-vector neighborhood, bounded by independent
coordinate choices from the union of source-centered intervals. -/
theorem sourceExponentVectorNeighborhood_card_le {s u N : ℕ}
    (ax : Fin s → ℕ) (R : ℕ) :
    (sourceExponentVectorNeighborhood (u := u) (N := N) ax R).card ≤
      (s * (2 * R + 1)) ^ u := by
  classical
  rw [sourceExponentVectorNeighborhood, Fintype.card_piFinset_const]
  exact Nat.pow_le_pow_left (sourceExponentNeighborhood_card_le ax N R) u

/-- Every finite sparse-decimal rational neighbor lies in the pointwise
source-neighborhood vector domain. -/
theorem sparseDecimalRationalNeighborDomain_subset_vectorNeighborhood
    {s u K J N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ)
    (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax)
    (hK : 1 ≤ K)
    (hscale : (s + u) * K < 10 ^ J) :
    sparseDecimalRationalNeighborDomain sx ax sy N K ⊆
      sourceExponentVectorNeighborhood ax ((s + u - 1) * (J - 1)) := by
  classical
  intro a ha
  obtain ⟨hnc, hpos, hratio⟩ :=
    mem_sparseDecimalRationalNeighborDomain_iff.mp ha
  apply mem_sourceExponentVectorNeighborhood_iff.mpr
  exact sparseDecimal_rationalNeighbor hs0 hs4 hu0 hu4 sx ax sy
    (exponentNat a) hxc hnc hx hpos hK hscale hratio

/-- The finite rational-neighbor count obtained from the union of `s` integer
intervals of radius `(s+u-1)(J-1)` in each of the `u` labeled coordinates. -/
theorem sparseDecimalRationalNeighborDomain_card_le
    {s u K J N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ)
    (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax)
    (hK : 1 ≤ K)
    (hscale : (s + u) * K < 10 ^ J) :
    (sparseDecimalRationalNeighborDomain sx ax sy N K).card ≤
      (s * (2 * ((s + u - 1) * (J - 1)) + 1)) ^ u := by
  exact (Finset.card_le_card
    (sparseDecimalRationalNeighborDomain_subset_vectorNeighborhood
      hs0 hs4 hu0 hu4 sx ax sy hxc hx hK hscale)).trans
    (sourceExponentVectorNeighborhood_card_le ax
      ((s + u - 1) * (J - 1)))

/-- All positive, noncancelling four-token vectors with signs
`(+,+,-,-)` and every exponent in `0,...,N-1`. -/
def primitiveFourTokenDomain (N : ℕ) : Finset (BoundedExponentVector 4 N) :=
  by
    classical
    exact Finset.univ.filter fun a =>
      Noncancelling fourTokenSign (exponentNat a) ∧
        0 < signedDecimalValue fourTokenSign (exponentNat a)

/-- Every positive labeled four-token form with signs `(+,+,-,-)`, including
forms with opposite-sign cancellation. -/
def allPositiveFourTokenDomain (N : ℕ) : Finset (BoundedExponentVector 4 N) := by
  classical
  exact Finset.univ.filter fun a =>
    0 < signedDecimalValue fourTokenSign (exponentNat a)

/-- Positive four-token forms that contain at least one opposite-sign
cancellation. -/
def cancellingFourTokenDomain (N : ℕ) : Finset (BoundedExponentVector 4 N) := by
  classical
  exact Finset.univ.filter fun a =>
    0 < signedDecimalValue fourTokenSign (exponentNat a) ∧
      ¬Noncancelling fourTokenSign (exponentNat a)

/-- Membership audit for all positive four-token forms. -/
theorem mem_allPositiveFourTokenDomain_iff {N : ℕ}
    {a : BoundedExponentVector 4 N} :
    a ∈ allPositiveFourTokenDomain N ↔
      (∀ i : Fin 4, (a i).1 < N) ∧
        0 < signedDecimalValue fourTokenSign (exponentNat a) := by
  constructor
  · intro ha
    exact ⟨fun i => (a i).2, (Finset.mem_filter.mp ha).2⟩
  · rintro ⟨_hrange, hpos⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩

/-- Membership audit for cancelling positive four-token forms. -/
theorem mem_cancellingFourTokenDomain_iff {N : ℕ}
    {a : BoundedExponentVector 4 N} :
    a ∈ cancellingFourTokenDomain N ↔
      (∀ i : Fin 4, (a i).1 < N) ∧
      0 < signedDecimalValue fourTokenSign (exponentNat a) ∧
      ¬Noncancelling fourTokenSign (exponentNat a) := by
  classical
  constructor
  · intro ha
    have hm := Finset.mem_filter.mp ha
    exact ⟨fun i => (a i).2, hm.2.1, hm.2.2⟩
  · rintro ⟨_hrange, hpos, hcancel⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, hcancel⟩

/-- Exact partition of all positive four-token forms into noncancelling and
cancelling forms. -/
theorem allPositiveFourTokenDomain_partition (N : ℕ) :
    allPositiveFourTokenDomain N =
      primitiveFourTokenDomain N ∪ cancellingFourTokenDomain N := by
  classical
  ext a
  simp only [allPositiveFourTokenDomain, primitiveFourTokenDomain,
    cancellingFourTokenDomain, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  tauto

/-- The two halves of the positive four-token partition are disjoint. -/
theorem primitiveFourTokenDomain_disjoint_cancellingFourTokenDomain (N : ℕ) :
    Disjoint (primitiveFourTokenDomain N) (cancellingFourTokenDomain N) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a hprimitive hcancelling
  exact (Finset.mem_filter.mp hcancelling).2.2
    (Finset.mem_filter.mp hprimitive).2.1

/-- A positive label among the prescribed signs `(+,+,-,-)`. -/
def positiveFourLabel (p : Fin 2) : Fin 4 := ⟨p.1, by omega⟩

/-- A negative label among the prescribed signs `(+,+,-,-)`. -/
def negativeFourLabel (n : Fin 2) : Fin 4 := ⟨n.1 + 2, by omega⟩

/-- The other element of `Fin 2`. -/
def otherFinTwo (i : Fin 2) : Fin 2 := ⟨1 - i.1, by omega⟩

/-- The fixed labeled cancellation case selecting positive label `p` and
negative label `n` at an equal exponent. -/
def cancellingFourTokenCaseDomain (N : ℕ) (p n : Fin 2) :
    Finset (BoundedExponentVector 4 N) := by
  classical
  exact Finset.univ.filter fun a =>
    0 < signedDecimalValue fourTokenSign (exponentNat a) ∧
      a (positiveFourLabel p) = a (negativeFourLabel n)

/-- Membership in a fixed labeled cancellation case exposes every finite
range, positivity, and the selected equal-exponent condition. -/
theorem mem_cancellingFourTokenCaseDomain_iff {N : ℕ} {p n : Fin 2}
    {a : BoundedExponentVector 4 N} :
    a ∈ cancellingFourTokenCaseDomain N p n ↔
      (∀ i : Fin 4, (a i).1 < N) ∧
      0 < signedDecimalValue fourTokenSign (exponentNat a) ∧
      a (positiveFourLabel p) = a (negativeFourLabel n) := by
  constructor
  · intro ha
    have hm := Finset.mem_filter.mp ha
    exact ⟨fun i => (a i).2, hm.2.1, hm.2.2⟩
  · rintro ⟨_hrange, hpos, heq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, heq⟩

/-- Union of the four choices of a positive and a negative cancellation label. -/
def allCancellingFourTokenCases (N : ℕ) : Finset (BoundedExponentVector 4 N) := by
  classical
  exact Finset.univ.biUnion fun p : Fin 2 =>
    Finset.univ.biUnion fun n : Fin 2 => cancellingFourTokenCaseDomain N p n

/-- The residual two-token vector left after cancelling selected labels. -/
def cancellationResidual {N : ℕ} (p n : Fin 2)
    (a : BoundedExponentVector 4 N) : BoundedExponentVector 2 N :=
  fun i => if i.1 = 0 then a (positiveFourLabel (otherFinTwo p))
    else a (negativeFourLabel (otherFinTwo n))

/-- Reconstruct a four-token cancellation case from the remaining positive
and negative exponents and the hidden cancelled exponent. -/
def cancellationCaseVector {N : ℕ} (p n : Fin 2)
    (residual : BoundedExponentVector 2 N) (hidden : Fin N) :
    BoundedExponentVector 4 N :=
  fun i =>
    if i = positiveFourLabel p then hidden
    else if i = negativeFourLabel n then hidden
    else if i = positiveFourLabel (otherFinTwo p) then residual 0
    else residual 1

/-- The selected positive and negative labels of a reconstructed case have
the same hidden exponent. -/
theorem cancellationCaseVector_selected_eq {N : ℕ} (p n : Fin 2)
    (residual : BoundedExponentVector 2 N) (hidden : Fin N) :
    cancellationCaseVector p n residual hidden (positiveFourLabel p) =
      cancellationCaseVector p n residual hidden (negativeFourLabel n) := by
  simp [cancellationCaseVector, positiveFourLabel, negativeFourLabel]

/-- Residual extraction is a left inverse to cancellation-case reconstruction. -/
theorem cancellationResidual_caseVector {N : ℕ} (p n : Fin 2)
    (residual : BoundedExponentVector 2 N) (hidden : Fin N) :
    cancellationResidual p n (cancellationCaseVector p n residual hidden) = residual := by
  funext i
  fin_cases p <;> fin_cases n <;> fin_cases i <;>
    simp [cancellationResidual, cancellationCaseVector, positiveFourLabel,
      negativeFourLabel, otherFinTwo]

/-- A vector in a fixed cancellation case is reconstructed from its residual
and selected hidden exponent. -/
theorem cancellationCaseVector_residual_hidden {N : ℕ} (p n : Fin 2)
    (a : BoundedExponentVector 4 N)
    (heq : a (positiveFourLabel p) = a (negativeFourLabel n)) :
    cancellationCaseVector p n (cancellationResidual p n a)
      (a (positiveFourLabel p)) = a := by
  funext i
  fin_cases p <;> fin_cases n <;> fin_cases i <;>
    simp [cancellationCaseVector, cancellationResidual, positiveFourLabel,
      negativeFourLabel, otherFinTwo] at heq ⊢ <;> simp [heq]

/-- Cancelling one selected positive/negative pair preserves the exact signed value. -/
theorem cancellationResidual_signedValue_eq {N : ℕ} (p n : Fin 2)
    (a : BoundedExponentVector 4 N)
    (heq : a (positiveFourLabel p) = a (negativeFourLabel n)) :
    signedDecimalValue twoTokenSign (exponentNat (cancellationResidual p n a)) =
      signedDecimalValue fourTokenSign (exponentNat a) := by
  fin_cases p <;> fin_cases n <;>
    simp [signedDecimalValue, exponentNat, cancellationResidual, positiveFourLabel,
      negativeFourLabel, otherFinTwo, twoTokenSign, fourTokenSign,
      Fin.sum_univ_succ] at heq ⊢ <;> simp [heq] <;> ring

/-- Cancelling one selected pair preserves the extracted natural value. -/
theorem cancellationResidual_natValue_eq {N : ℕ} (p n : Fin 2)
    (a : BoundedExponentVector 4 N)
    (heq : a (positiveFourLabel p) = a (negativeFourLabel n)) :
    signedDecimalNatValue twoTokenSign (exponentNat (cancellationResidual p n a)) =
      signedDecimalNatValue fourTokenSign (exponentNat a) := by
  simp only [signedDecimalNatValue]
  rw [cancellationResidual_signedValue_eq p n a heq]

/-- Reconstruction preserves the exact signed value of its residual. -/
theorem cancellationCaseVector_signedValue_eq {N : ℕ} (p n : Fin 2)
    (residual : BoundedExponentVector 2 N) (hidden : Fin N) :
    signedDecimalValue fourTokenSign
        (exponentNat (cancellationCaseVector p n residual hidden)) =
      signedDecimalValue twoTokenSign (exponentNat residual) := by
  have h := cancellationResidual_signedValue_eq p n
    (cancellationCaseVector p n residual hidden)
    (cancellationCaseVector_selected_eq p n residual hidden)
  rw [cancellationResidual_caseVector] at h
  exact h.symm

/-- Reconstruction preserves the exact natural value of its residual. -/
theorem cancellationCaseVector_natValue_eq {N : ℕ} (p n : Fin 2)
    (residual : BoundedExponentVector 2 N) (hidden : Fin N) :
    signedDecimalNatValue fourTokenSign
        (exponentNat (cancellationCaseVector p n residual hidden)) =
      signedDecimalNatValue twoTokenSign (exponentNat residual) := by
  simp only [signedDecimalNatValue]
  rw [cancellationCaseVector_signedValue_eq]

/-- Every positive two-token form with signs `(+,-)` is noncancelling. -/
theorem twoToken_noncancelling_of_pos {a : Fin 2 → ℕ}
    (hpos : 0 < signedDecimalValue twoTokenSign a) :
    Noncancelling twoTokenSign a := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    change a 0 = a 1 at hij
    have hp := hpos
    simp [signedDecimalValue, twoTokenSign, Fin.sum_univ_succ] at hp
    rw [hij] at hp
    omega
  · exfalso
    change a 1 = a 0 at hij
    have hp := hpos
    simp [signedDecimalValue, twoTokenSign, Fin.sum_univ_succ] at hp
    rw [hij] at hp
    omega
  · rfl

/-- A selected cancellation residual is positive, noncancelling, and has the
same natural value as the original positive four-token form. -/
theorem cancellationResidual_spec {N : ℕ} (p n : Fin 2)
    (a : BoundedExponentVector 4 N)
    (hpos : 0 < signedDecimalValue fourTokenSign (exponentNat a))
    (heq : a (positiveFourLabel p) = a (negativeFourLabel n)) :
    Noncancelling twoTokenSign (exponentNat (cancellationResidual p n a)) ∧
    0 < signedDecimalValue twoTokenSign (exponentNat (cancellationResidual p n a)) ∧
    signedDecimalNatValue twoTokenSign (exponentNat (cancellationResidual p n a)) =
      signedDecimalNatValue fourTokenSign (exponentNat a) := by
  have hvalue := cancellationResidual_signedValue_eq p n a heq
  have hrespos :
      0 < signedDecimalValue twoTokenSign (exponentNat (cancellationResidual p n a)) := by
    rw [hvalue]
    exact hpos
  exact ⟨twoToken_noncancelling_of_pos hrespos, hrespos,
    cancellationResidual_natValue_eq p n a heq⟩

/-- Every fixed cancellation case consists of cancelling positive forms. -/
theorem cancellingFourTokenCaseDomain_subset_cancelling {N : ℕ} (p n : Fin 2) :
    cancellingFourTokenCaseDomain N p n ⊆ cancellingFourTokenDomain N := by
  intro a ha
  obtain ⟨_hrange, hpos, heq⟩ := mem_cancellingFourTokenCaseDomain_iff.mp ha
  apply mem_cancellingFourTokenDomain_iff.mpr
  refine ⟨fun i => (a i).2, hpos, ?_⟩
  intro hnc
  have hsign := hnc (positiveFourLabel p) (negativeFourLabel n)
    (congr_arg Fin.val heq)
  have hpSign : fourTokenSign (positiveFourLabel p) = true := by
    simp [fourTokenSign, positiveFourLabel]
    omega
  have hnSign : fourTokenSign (negativeFourLabel n) = false := by
    simp [fourTokenSign, negativeFourLabel]
  rw [hpSign, hnSign] at hsign
  contradiction

/-- Every cancelling positive four-token vector belongs to one of the four
labeled cancellation cases. -/
theorem cancellingFourTokenDomain_subset_allCases (N : ℕ) :
    cancellingFourTokenDomain N ⊆ allCancellingFourTokenCases N := by
  classical
  intro a ha
  obtain ⟨_hrange, hpos, hcancel⟩ := mem_cancellingFourTokenDomain_iff.mp ha
  rw [Noncancelling] at hcancel
  push Not at hcancel
  obtain ⟨i, j, hij, hsign⟩ := hcancel
  by_cases hi : i.1 < 2
  · have hj : ¬j.1 < 2 := by
      intro hj
      apply hsign
      simp [fourTokenSign, hi, hj]
    let p : Fin 2 := ⟨i.1, hi⟩
    let n : Fin 2 := ⟨j.1 - 2, by omega⟩
    have hip : i = positiveFourLabel p := by ext; simp [p, positiveFourLabel]
    have hjn : j = negativeFourLabel n := by ext; simp [n, negativeFourLabel]; omega
    rw [allCancellingFourTokenCases, Finset.mem_biUnion]
    refine ⟨p, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨n, Finset.mem_univ _, ?_⟩
    apply mem_cancellingFourTokenCaseDomain_iff.mpr
    refine ⟨fun k => (a k).2, hpos, ?_⟩
    apply Fin.ext
    simpa [← hip, ← hjn] using hij
  · have hj : j.1 < 2 := by
      by_contra hj
      apply hsign
      simp [fourTokenSign, hi, hj]
    let p : Fin 2 := ⟨j.1, hj⟩
    let n : Fin 2 := ⟨i.1 - 2, by omega⟩
    have hjp : j = positiveFourLabel p := by ext; simp [p, positiveFourLabel]
    have hin : i = negativeFourLabel n := by ext; simp [n, negativeFourLabel]; omega
    rw [allCancellingFourTokenCases, Finset.mem_biUnion]
    refine ⟨p, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨n, Finset.mem_univ _, ?_⟩
    apply mem_cancellingFourTokenCaseDomain_iff.mpr
    refine ⟨fun k => (a k).2, hpos, ?_⟩
    apply Fin.ext
    simpa [← hjp, ← hin] using hij.symm

/-- The four labeled cancellation cases cover the cancelling domain exactly. -/
theorem cancellingFourTokenDomain_eq_allCases (N : ℕ) :
    cancellingFourTokenDomain N = allCancellingFourTokenCases N := by
  apply Finset.Subset.antisymm (cancellingFourTokenDomain_subset_allCases N)
  intro a ha
  rw [allCancellingFourTokenCases, Finset.mem_biUnion] at ha
  obtain ⟨p, hp, ha⟩ := ha
  rw [Finset.mem_biUnion] at ha
  obtain ⟨n, hn, ha⟩ := ha
  exact cancellingFourTokenCaseDomain_subset_cancelling p n ha

/-- A fixed labeled cancellation case has at most `N^3` vectors: two residual
exponents and one hidden cancelled exponent. -/
theorem cancellingFourTokenCaseDomain_card_le (N : ℕ) (p n : Fin 2) :
    (cancellingFourTokenCaseDomain N p n).card ≤ N ^ 3 := by
  classical
  let encode : BoundedExponentVector 4 N →
      BoundedExponentVector 2 N × Fin N := fun a =>
    (cancellationResidual p n a, a (positiveFourLabel p))
  have hinj : Set.InjOn encode (cancellingFourTokenCaseDomain N p n) := by
    intro a ha b hb hab
    have hae := (mem_cancellingFourTokenCaseDomain_iff.mp ha).2.2
    have hbe := (mem_cancellingFourTokenCaseDomain_iff.mp hb).2.2
    have hres : cancellationResidual p n a = cancellationResidual p n b :=
      congrArg Prod.fst hab
    have hhidden : a (positiveFourLabel p) = b (positiveFourLabel p) :=
      congrArg Prod.snd hab
    rw [← cancellationCaseVector_residual_hidden p n a hae,
      ← cancellationCaseVector_residual_hidden p n b hbe]
    simp only [hres, hhidden]
  calc
    (cancellingFourTokenCaseDomain N p n).card =
        ((cancellingFourTokenCaseDomain N p n).image encode).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (BoundedExponentVector 2 N × Fin N)).card :=
      Finset.card_le_card (fun _ _ => Finset.mem_univ _)
    _ = N ^ 3 := by simp; ring

/-- The complete cancelling four-token domain has cardinality at most `4N^3`. -/
theorem cancellingFourTokenDomain_card_le (N : ℕ) :
    (cancellingFourTokenDomain N).card ≤ 4 * N ^ 3 := by
  classical
  rw [cancellingFourTokenDomain_eq_allCases, allCancellingFourTokenCases]
  have hinner : ∀ p : Fin 2,
      ((Finset.univ : Finset (Fin 2)).biUnion fun n =>
        cancellingFourTokenCaseDomain N p n).card ≤ 2 * N ^ 3 := by
    intro p
    simpa using
      (Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 2))
        (fun n => cancellingFourTokenCaseDomain N p n) (N ^ 3)
        (fun n _ => cancellingFourTokenCaseDomain_card_le N p n))
  have houter :=
    Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 2))
      (fun p => (Finset.univ : Finset (Fin 2)).biUnion fun n =>
        cancellingFourTokenCaseDomain N p n) (2 * N ^ 3)
      (fun p _ => hinner p)
  calc
    ((Finset.univ : Finset (Fin 2)).biUnion fun p =>
      (Finset.univ : Finset (Fin 2)).biUnion fun n =>
        cancellingFourTokenCaseDomain N p n).card ≤ 2 * (2 * N ^ 3) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using houter
    _ = 4 * N ^ 3 := by ring

/-- All positive, noncancelling two-token vectors with signs `(+,-)` and
every exponent in `0,...,N-1`. -/
def cancellationTwoTokenDomain (N : ℕ) : Finset (BoundedExponentVector 2 N) :=
  by
    classical
    exact Finset.univ.filter fun a =>
      Noncancelling twoTokenSign (exponentNat a) ∧
        0 < signedDecimalValue twoTokenSign (exponentNat a)

/-- Value of a primitive four-token exponent vector. -/
def primitiveFourTokenValue {N : ℕ} (a : BoundedExponentVector 4 N) : ℕ :=
  signedDecimalNatValue fourTokenSign (exponentNat a)

/-- Value of a cancellation two-token exponent vector. -/
def cancellationTwoTokenValue {N : ℕ} (a : BoundedExponentVector 2 N) : ℕ :=
  signedDecimalNatValue twoTokenSign (exponentNat a)

/-- The ordinary GCD kernel. Its zero cases are explicit in the definition;
all weighted theorems below sum only positive token values. -/
def gcdKernel (x y : ℕ) : ℚ :=
  (Nat.gcd x y : ℚ) / (Nat.max x y : ℚ)

/-- Positive noncancelling decimal forms with prescribed signs in the exact
target exponent box `Fin u → Fin N`. -/
def positiveNoncancellingDecimalDomain {u : ℕ} (sy : Fin u → Bool) (N : ℕ) :
    Finset (BoundedExponentVector u N) := by
  classical
  exact Finset.univ.filter fun a =>
    Noncancelling sy (exponentNat a) ∧
      0 < signedDecimalValue sy (exponentNat a)

/-- Membership audit for the generic positive noncancelling target domain. -/
theorem mem_positiveNoncancellingDecimalDomain_iff {u N : ℕ}
    {sy : Fin u → Bool} {a : BoundedExponentVector u N} :
    a ∈ positiveNoncancellingDecimalDomain sy N ↔
      Noncancelling sy (exponentNat a) ∧
        0 < signedDecimalValue sy (exponentNat a) := by
  simp [positiveNoncancellingDecimalDomain]

/-- The natural reduced-ratio quotient `max(x,y)/gcd(x,y)`. -/
def reducedRatioNat (x y : ℕ) : ℕ := Nat.max x y / Nat.gcd x y

/-- The GCD divides the maximum of two natural numbers. -/
theorem gcd_dvd_max (x y : ℕ) : Nat.gcd x y ∣ Nat.max x y := by
  by_cases hxy : x ≤ y
  · simpa [Nat.max_eq_right hxy] using Nat.gcd_dvd_right x y
  · simpa [Nat.max_eq_left (le_of_not_ge hxy)] using Nat.gcd_dvd_left x y

/-- For positive inputs, the natural reduced-ratio quotient is positive. -/
theorem reducedRatioNat_pos {x y : ℕ} (hx : 0 < x) : 0 < reducedRatioNat x y := by
  apply Nat.div_pos
  · exact (Nat.gcd_le_left y hx).trans (Nat.le_max_left x y)
  · exact Nat.gcd_pos_of_pos_left y hx

/-- The natural quotient coerces exactly to the rational reduced-ratio height. -/
theorem reducedRatioNat_cast_eq_reducedRatioHeight {x y : ℕ} (hx : 0 < x) :
    (reducedRatioNat x y : ℚ) = reducedRatioHeight x y := by
  rw [reducedRatioNat, reducedRatioHeight,
    Nat.cast_div (gcd_dvd_max x y) (by
      exact_mod_cast (Nat.gcd_pos_of_pos_left y hx).ne')]

/-- For positive inputs, the GCD kernel is the reciprocal natural
reduced-ratio quotient. -/
theorem gcdKernel_eq_inv_reducedRatioNat {x y : ℕ} (hx : 0 < x) :
    gcdKernel x y = 1 / (reducedRatioNat x y : ℚ) := by
  have hg : (Nat.gcd x y : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left y hx).ne'
  have hmax : (Nat.max x y : ℚ) ≠ 0 := by positivity
  rw [gcdKernel, reducedRatioNat_cast_eq_reducedRatioHeight hx,
    reducedRatioHeight]
  field_simp

/-- For positive inputs, a natural quotient bound is equivalent to the
rational reduced-ratio condition. -/
theorem reducedRatioAtMost_iff_reducedRatioNat_le {x y K : ℕ}
    (hx : 0 < x) (hy : 0 < y) :
    ReducedRatioAtMost x y K ↔ reducedRatioNat x y ≤ K := by
  rw [ReducedRatioAtMost, and_iff_right hx, and_iff_right hy,
    ← reducedRatioNat_cast_eq_reducedRatioHeight hx]
  exact_mod_cast Iff.rfl

/-- The decimal shell index for a nontrivial natural reduced ratio. -/
def reducedRatioShellIndex (x y : ℕ) : ℕ :=
  Nat.log 10 (reducedRatioNat x y - 1)

/-- A nontrivial reduced ratio lies between the consecutive decimal powers
selected by `reducedRatioShellIndex`. -/
theorem reducedRatioShellIndex_spec {x y : ℕ}
    (hxy : 1 < reducedRatioNat x y) :
    10 ^ reducedRatioShellIndex x y < reducedRatioNat x y ∧
      reducedRatioNat x y ≤ 10 ^ (reducedRatioShellIndex x y + 1) := by
  let H := reducedRatioNat x y
  have hsub : H - 1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 10 hsub
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) (H - 1)
  dsimp [reducedRatioShellIndex, H] at hlo hhi ⊢
  omega

/-- The generic weighted row over positive noncancelling target forms. -/
def sparseDecimalWeightedRow {s u : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool) (N : ℕ) : ℚ :=
  ∑ a ∈ positiveNoncancellingDecimalDomain sy N,
    gcdKernel (signedDecimalNatValue sx ax)
      (signedDecimalNatValue sy (exponentNat a))

/-- Elementary exponential domination used in the decimal-shell series. -/
theorem add_two_pow_four_le_twentyOne_mul_four_pow (j : ℕ) :
    (j + 2) ^ 4 ≤ 21 * 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        norm_num
      · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
        have hsq : (j + 3) ^ 2 ≤ 2 * (j + 2) ^ 2 := by nlinarith
        calc
          (j + 1 + 2) ^ 4 = ((j + 3) ^ 2) ^ 2 := by ring
          _ ≤ (2 * (j + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left hsq 2
          _ = 4 * (j + 2) ^ 4 := by ring
          _ ≤ 4 * (21 * 4 ^ j) := Nat.mul_le_mul_left 4 ih
          _ = 21 * 4 ^ (j + 1) := by ring

/-- Each quartic decimal-shell term is bounded by a geometric term of ratio `2/5`. -/
theorem quarticDecimalTerm_le_geometric (j : ℕ) :
    ((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j ≤
      21 * ((2 : ℚ) / 5) ^ j := by
  have hnat := add_two_pow_four_le_twentyOne_mul_four_pow j
  have hcast : (((j + 2) ^ 4 : ℕ) : ℚ) ≤ (21 * 4 ^ j : ℕ) := by
    exact_mod_cast hnat
  calc
    ((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j =
        (((j + 2) ^ 4 : ℕ) : ℚ) / (10 : ℚ) ^ j := by norm_num
    _ ≤ ((21 * 4 ^ j : ℕ) : ℚ) / (10 : ℚ) ^ j := by
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = 21 * ((2 : ℚ) / 5) ^ j := by
      push_cast
      rw [mul_div_assoc, ← div_pow]
      norm_num

/-- A finite geometric-tail invariant for the quartic decimal series. -/
theorem quarticDecimalSeries_add_tail_le (r : ℕ) :
    (∑ j ∈ Finset.range r, ((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) +
      35 * ((2 : ℚ) / 5) ^ r ≤ 35 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [Finset.sum_range_succ,
        show ((2 : ℚ) / 5) ^ (r + 1) =
          ((2 : ℚ) / 5) ^ r * ((2 : ℚ) / 5) by rw [pow_succ]]
      calc
        (∑ j ∈ Finset.range r, ((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) +
              ((r + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ r +
              35 * (((2 : ℚ) / 5) ^ r * ((2 : ℚ) / 5))
            ≤ (∑ j ∈ Finset.range r,
                ((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) +
              21 * ((2 : ℚ) / 5) ^ r +
              35 * (((2 : ℚ) / 5) ^ r * ((2 : ℚ) / 5)) := by
          gcongr
          exact quarticDecimalTerm_le_geometric r
        _ = (∑ j ∈ Finset.range r,
              ((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) +
            35 * ((2 : ℚ) / 5) ^ r := by ring
        _ ≤ 35 := ih

/-- Uniform finite bound for the quartic decimal-shell series. -/
theorem quarticDecimalSeries_le_forty (r : ℕ) :
    (∑ j ∈ Finset.range r, ((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) ≤ 40 := by
  have h := quarticDecimalSeries_add_tail_le r
  have htail : 0 ≤ 35 * ((2 : ℚ) / 5) ^ r := by positivity
  linarith

/-- For `u ≤ 4`, the shifted `u`-th power is dominated by the quartic power. -/
theorem shifted_pow_le_fourth {u : ℕ} (hu4 : u ≤ 4) (j : ℕ) :
    (j + 2) ^ u ≤ (j + 2) ^ 4 := by
  exact Nat.pow_le_pow_right (by omega) hu4

/-- Positivity passes from a signed decimal value to its natural extraction. -/
theorem signedDecimalNatValue_pos {u : ℕ} {sy : Fin u → Bool} {ay : Fin u → ℕ}
    (h : 0 < signedDecimalValue sy ay) :
    0 < signedDecimalNatValue sy ay := by
  have hcast : (0 : ℤ) < (signedDecimalValue sy ay).toNat := by
    simpa [Int.toNat_of_nonneg h.le] using h
  exact_mod_cast hcast

/-- Targets in the weighted row whose natural reduced ratio is exactly one. -/
def reducedRatioDiagonalDomain {s u : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool) (N : ℕ) :
    Finset (BoundedExponentVector u N) :=
  (positiveNoncancellingDecimalDomain sy N).filter fun a =>
    reducedRatioNat (signedDecimalNatValue sx ax)
      (signedDecimalNatValue sy (exponentNat a)) = 1

/-- Targets in decimal reduced-ratio shell `j`. -/
def reducedRatioShellDomain {s u : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (N j : ℕ) : Finset (BoundedExponentVector u N) :=
  (positiveNoncancellingDecimalDomain sy N).filter fun a =>
    1 < reducedRatioNat (signedDecimalNatValue sx ax)
      (signedDecimalNatValue sy (exponentNat a)) ∧
    reducedRatioShellIndex (signedDecimalNatValue sx ax)
      (signedDecimalNatValue sy (exponentNat a)) = j

/-- Membership audit for the reduced-ratio diagonal. -/
theorem mem_reducedRatioDiagonalDomain_iff {s u N : ℕ}
    {sx : Fin s → Bool} {ax : Fin s → ℕ} {sy : Fin u → Bool}
    {a : BoundedExponentVector u N} :
    a ∈ reducedRatioDiagonalDomain sx ax sy N ↔
      Noncancelling sy (exponentNat a) ∧
      0 < signedDecimalValue sy (exponentNat a) ∧
      reducedRatioNat (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a)) = 1 := by
  simp [reducedRatioDiagonalDomain, mem_positiveNoncancellingDecimalDomain_iff,
    and_assoc]

/-- Membership audit for a decimal reduced-ratio shell. -/
theorem mem_reducedRatioShellDomain_iff {s u N j : ℕ}
    {sx : Fin s → Bool} {ax : Fin s → ℕ} {sy : Fin u → Bool}
    {a : BoundedExponentVector u N} :
    a ∈ reducedRatioShellDomain sx ax sy N j ↔
      Noncancelling sy (exponentNat a) ∧
      0 < signedDecimalValue sy (exponentNat a) ∧
      1 < reducedRatioNat (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a)) ∧
      reducedRatioShellIndex (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a)) = j := by
  simp [reducedRatioShellDomain, mem_positiveNoncancellingDecimalDomain_iff,
    and_assoc]

/-- The reduced-ratio diagonal has at most `s^u` labeled target vectors. -/
theorem reducedRatioDiagonalDomain_card_le
    {s u N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) :
    (reducedRatioDiagonalDomain sx ax sy N).card ≤ s ^ u := by
  classical
  have hxnat : 0 < signedDecimalNatValue sx ax := signedDecimalNatValue_pos hx
  have hsubset : reducedRatioDiagonalDomain sx ax sy N ⊆
      sparseDecimalRationalNeighborDomain sx ax sy N 1 := by
    intro a ha
    obtain ⟨hnc, hpos, hratio⟩ := mem_reducedRatioDiagonalDomain_iff.mp ha
    apply mem_sparseDecimalRationalNeighborDomain_iff.mpr
    refine ⟨hnc, hpos, ?_⟩
    apply (reducedRatioAtMost_iff_reducedRatioNat_le hxnat
      (signedDecimalNatValue_pos hpos)).mpr
    omega
  refine (Finset.card_le_card hsubset).trans ?_
  simpa using
    (sparseDecimalRationalNeighborDomain_card_le
      (K := 1) (J := 1) (N := N) hs0 hs4 hu0 hu4 sx ax sy hxc hx
      (by norm_num) (by norm_num; omega))

/-- Cardinality of decimal shell `j`, with quartic-ready polynomial growth. -/
theorem reducedRatioShellDomain_card_le
    {s u N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) (j : ℕ) :
    (reducedRatioShellDomain sx ax sy N j).card ≤
      ((2 * s * (s + u - 1)) * (j + 2)) ^ u := by
  classical
  have hxnat : 0 < signedDecimalNatValue sx ax := signedDecimalNatValue_pos hx
  have hsubset : reducedRatioShellDomain sx ax sy N j ⊆
      sparseDecimalRationalNeighborDomain sx ax sy N (10 ^ (j + 1)) := by
    intro a ha
    obtain ⟨hnc, hpos, hratio, hindex⟩ := mem_reducedRatioShellDomain_iff.mp ha
    apply mem_sparseDecimalRationalNeighborDomain_iff.mpr
    refine ⟨hnc, hpos, ?_⟩
    apply (reducedRatioAtMost_iff_reducedRatioNat_le hxnat
      (signedDecimalNatValue_pos hpos)).mpr
    have hspec := (reducedRatioShellIndex_spec hratio).2
    simpa [hindex] using hspec
  have hscale : (s + u) * 10 ^ (j + 1) < 10 ^ (j + 2) := by
    have hsu : s + u ≤ 8 := by omega
    have hp : 0 < 10 ^ (j + 1) := by positivity
    calc
      (s + u) * 10 ^ (j + 1) ≤ 8 * 10 ^ (j + 1) :=
        Nat.mul_le_mul_right _ hsu
      _ < 10 * 10 ^ (j + 1) := Nat.mul_lt_mul_of_pos_right (by norm_num) hp
      _ = 10 ^ (j + 2) := by
        rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
        omega
  have hcard := (Finset.card_le_card hsubset).trans
    (sparseDecimalRationalNeighborDomain_card_le
      (K := 10 ^ (j + 1)) (J := j + 2) (N := N)
      hs0 hs4 hu0 hu4 sx ax sy hxc hx
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hscale)
  have hd : 1 ≤ s + u - 1 := by omega
  have hbase :
      s * (2 * ((s + u - 1) * ((j + 2) - 1)) + 1) ≤
        (2 * s * (s + u - 1)) * (j + 2) := by
    have hone : 1 ≤ 2 * (s + u - 1) := by omega
    have hinner :
        2 * ((s + u - 1) * (j + 1)) + 1 ≤
          2 * (s + u - 1) * (j + 2) := by
      calc
        2 * ((s + u - 1) * (j + 1)) + 1 ≤
            2 * ((s + u - 1) * (j + 1)) + 2 * (s + u - 1) :=
          Nat.add_le_add_left hone _
        _ = 2 * (s + u - 1) * (j + 2) := by ring
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left s hinner
  exact hcard.trans (Nat.pow_le_pow_left hbase u)

/-- The GCD kernel is nonnegative. -/
theorem gcdKernel_nonneg (x y : ℕ) : 0 ≤ gcdKernel x y := by
  exact div_nonneg (by positivity) (by positivity)

/-- On the natural reduced-ratio diagonal, the GCD kernel equals one. -/
theorem gcdKernel_eq_one_of_reducedRatioNat_eq_one {x y : ℕ}
    (hx : 0 < x) (h : reducedRatioNat x y = 1) : gcdKernel x y = 1 := by
  rw [gcdKernel_eq_inv_reducedRatioNat hx, h]
  norm_num

/-- The kernel on decimal shell `j` is at most `10⁻ʲ`. -/
theorem gcdKernel_le_inv_pow_of_shell {x y j : ℕ}
    (hx : 0 < x) (hxy : 1 < reducedRatioNat x y)
    (hindex : reducedRatioShellIndex x y = j) :
    gcdKernel x y ≤ 1 / (10 : ℚ) ^ j := by
  rw [gcdKernel_eq_inv_reducedRatioNat hx]
  apply one_div_le_one_div_of_le (by positivity)
  have hpow := (reducedRatioShellIndex_spec hxy).1.le
  rw [hindex] at hpow
  exact_mod_cast hpow

/-- Total kernel contribution from the reduced-ratio diagonal. -/
theorem reducedRatioDiagonalDomain_sum_le
    {s u N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) :
    (∑ a ∈ reducedRatioDiagonalDomain sx ax sy N,
      gcdKernel (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a))) ≤ s ^ u := by
  have hxnat : 0 < signedDecimalNatValue sx ax := signedDecimalNatValue_pos hx
  calc
    (∑ a ∈ reducedRatioDiagonalDomain sx ax sy N,
      gcdKernel (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a))) =
        ∑ _a ∈ reducedRatioDiagonalDomain sx ax sy N, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact gcdKernel_eq_one_of_reducedRatioNat_eq_one hxnat
        (mem_reducedRatioDiagonalDomain_iff.mp ha).2.2
    _ = (reducedRatioDiagonalDomain sx ax sy N).card := by simp
    _ ≤ s ^ u := by
      exact_mod_cast reducedRatioDiagonalDomain_card_le
        hs0 hs4 hu0 hu4 sx ax sy hxc hx

/-- Total kernel contribution from decimal shell `j`. -/
theorem reducedRatioShellDomain_sum_le
    {s u N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) (j : ℕ) :
    (∑ a ∈ reducedRatioShellDomain sx ax sy N j,
      gcdKernel (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a))) ≤
      (((2 * s * (s + u - 1)) * (j + 2)) ^ u : ℕ) / (10 : ℚ) ^ j := by
  have hxnat : 0 < signedDecimalNatValue sx ax := signedDecimalNatValue_pos hx
  calc
    (∑ a ∈ reducedRatioShellDomain sx ax sy N j,
      gcdKernel (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a))) ≤
        ∑ _a ∈ reducedRatioShellDomain sx ax sy N j, 1 / (10 : ℚ) ^ j := by
      apply Finset.sum_le_sum
      intro a ha
      have hm := mem_reducedRatioShellDomain_iff.mp ha
      exact gcdKernel_le_inv_pow_of_shell hxnat hm.2.2.1 hm.2.2.2
    _ = ((reducedRatioShellDomain sx ax sy N j).card : ℚ) / (10 : ℚ) ^ j := by
      simp [div_eq_mul_inv]
    _ ≤ (((2 * s * (s + u - 1)) * (j + 2)) ^ u : ℕ) / (10 : ℚ) ^ j := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast reducedRatioShellDomain_card_le
        hs0 hs4 hu0 hu4 sx ax sy hxc hx j

/-- Quartic domination of the generic shell contribution for `u ≤ 4`. -/
theorem reducedRatioShellDomain_sum_le_quartic
    {s u N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) (j : ℕ) :
    (∑ a ∈ reducedRatioShellDomain sx ax sy N j,
      gcdKernel (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a))) ≤
      ((2 * s * (s + u - 1)) ^ u : ℕ) *
        (((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) := by
  refine (reducedRatioShellDomain_sum_le
    hs0 hs4 hu0 hu4 sx ax sy hxc hx j).trans ?_
  let A := 2 * s * (s + u - 1)
  calc
    (((A * (j + 2)) ^ u : ℕ) : ℚ) / (10 : ℚ) ^ j =
        ((A ^ u : ℕ) : ℚ) * (((j + 2) ^ u : ℕ) : ℚ) / (10 : ℚ) ^ j := by
      rw [mul_pow]
      push_cast
      norm_num
    _ ≤ ((A ^ u : ℕ) : ℚ) * (((j + 2) ^ 4 : ℕ) : ℚ) / (10 : ℚ) ^ j := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast shifted_pow_le_fourth hu4 j
    _ = ((A ^ u : ℕ) : ℚ) *
        (((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) := by
      push_cast
      ring

/-- One plus the largest shell index occurring in the finite target domain. -/
def weightedRowShellRange {s u : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool) (N : ℕ) : ℕ :=
  (positiveNoncancellingDecimalDomain sy N).sup (fun a =>
    reducedRatioShellIndex (signedDecimalNatValue sx ax)
      (signedDecimalNatValue sy (exponentNat a))) + 1

/-- The finite union of all nontrivial reduced-ratio shells occurring in a row. -/
def reducedRatioShellUnion {s u : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool) (N : ℕ) :
    Finset (BoundedExponentVector u N) := by
  classical
  exact (Finset.range (weightedRowShellRange sx ax sy N)).biUnion fun j =>
    reducedRatioShellDomain sx ax sy N j

/-- The positive target domain is the disjoint union of the natural-ratio
diagonal and all decimal shells. -/
theorem positiveNoncancellingDecimalDomain_eq_diagonal_union_shells
    {s u N : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hx : 0 < signedDecimalValue sx ax) :
    positiveNoncancellingDecimalDomain sy N =
      reducedRatioDiagonalDomain sx ax sy N ∪
        reducedRatioShellUnion sx ax sy N := by
  classical
  have hxnat : 0 < signedDecimalNatValue sx ax := signedDecimalNatValue_pos hx
  ext a
  constructor
  · intro ha
    have hbase := mem_positiveNoncancellingDecimalDomain_iff.mp ha
    let H := reducedRatioNat (signedDecimalNatValue sx ax)
      (signedDecimalNatValue sy (exponentNat a))
    have hHpos : 0 < H := reducedRatioNat_pos hxnat
    by_cases hH : H = 1
    · apply Finset.mem_union_left
      exact mem_reducedRatioDiagonalDomain_iff.mpr ⟨hbase.1, hbase.2, hH⟩
    · apply Finset.mem_union_right
      rw [reducedRatioShellUnion, Finset.mem_biUnion]
      let idx := reducedRatioShellIndex (signedDecimalNatValue sx ax)
        (signedDecimalNatValue sy (exponentNat a))
      have hidxle : idx ≤ (positiveNoncancellingDecimalDomain sy N).sup (fun b =>
          reducedRatioShellIndex (signedDecimalNatValue sx ax)
            (signedDecimalNatValue sy (exponentNat b))) := by
        exact Finset.le_sup (f := fun b =>
          reducedRatioShellIndex (signedDecimalNatValue sx ax)
            (signedDecimalNatValue sy (exponentNat b))) ha
      refine ⟨idx, ?_, ?_⟩
      · simp [weightedRowShellRange]
        omega
      · apply mem_reducedRatioShellDomain_iff.mpr
        exact ⟨hbase.1, hbase.2, by omega, rfl⟩
  · intro ha
    rcases Finset.mem_union.mp ha with hdiag | hshells
    · have hm := mem_reducedRatioDiagonalDomain_iff.mp hdiag
      exact mem_positiveNoncancellingDecimalDomain_iff.mpr ⟨hm.1, hm.2.1⟩
    · rw [reducedRatioShellUnion, Finset.mem_biUnion] at hshells
      obtain ⟨j, hj, haShell⟩ := hshells
      have hm := mem_reducedRatioShellDomain_iff.mp haShell
      exact mem_positiveNoncancellingDecimalDomain_iff.mpr ⟨hm.1, hm.2.1⟩

/-- Distinct decimal shell domains are disjoint. -/
theorem reducedRatioShellDomains_pairwiseDisjoint
    {s u N : ℕ} (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool) :
    (Finset.range (weightedRowShellRange sx ax sy N) : Set ℕ).PairwiseDisjoint
      (fun j => reducedRatioShellDomain sx ax sy N j) := by
  classical
  intro j hj k hk hjk
  apply Finset.disjoint_left.mpr
  intro a haj hak
  have hja := (mem_reducedRatioShellDomain_iff.mp haj).2.2.2
  have hka := (mem_reducedRatioShellDomain_iff.mp hak).2.2.2
  exact hjk (hja.symm.trans hka)

/-- The reduced-ratio diagonal is disjoint from the union of nontrivial shells. -/
theorem reducedRatioDiagonal_disjoint_shellUnion
    {s u N : ℕ} (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool) :
    Disjoint (reducedRatioDiagonalDomain sx ax sy N)
      (reducedRatioShellUnion sx ax sy N) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a hdiag hshells
  have hratio := (mem_reducedRatioDiagonalDomain_iff.mp hdiag).2.2
  rw [reducedRatioShellUnion, Finset.mem_biUnion] at hshells
  obtain ⟨j, hj, haShell⟩ := hshells
  have hgt := (mem_reducedRatioShellDomain_iff.mp haShell).2.2.1
  omega

/-- Exact finite decomposition of a weighted row into its diagonal and shell sums. -/
theorem sparseDecimalWeightedRow_eq_diagonal_add_shells
    {s u N : ℕ}
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hx : 0 < signedDecimalValue sx ax) :
    sparseDecimalWeightedRow sx ax sy N =
      (∑ a ∈ reducedRatioDiagonalDomain sx ax sy N,
        gcdKernel (signedDecimalNatValue sx ax)
          (signedDecimalNatValue sy (exponentNat a))) +
      ∑ j ∈ Finset.range (weightedRowShellRange sx ax sy N),
        ∑ a ∈ reducedRatioShellDomain sx ax sy N j,
          gcdKernel (signedDecimalNatValue sx ax)
            (signedDecimalNatValue sy (exponentNat a)) := by
  classical
  rw [sparseDecimalWeightedRow,
    positiveNoncancellingDecimalDomain_eq_diagonal_union_shells sx ax sy hx,
    Finset.sum_union (reducedRatioDiagonal_disjoint_shellUnion sx ax sy)]
  congr 1
  rw [reducedRatioShellUnion,
    Finset.sum_biUnion (reducedRatioShellDomains_pairwiseDisjoint sx ax sy)]

/-- Generic finite weighted-row bound obtained from the natural reduced-ratio
diagonal, decimal shells, sparse-neighbor counting, and the quartic series. -/
theorem sparseDecimalWeightedRow_le
    {s u N : ℕ}
    (hs0 : 1 ≤ s) (hs4 : s ≤ 4)
    (hu0 : 1 ≤ u) (hu4 : u ≤ 4)
    (sx : Fin s → Bool) (ax : Fin s → ℕ) (sy : Fin u → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) :
    sparseDecimalWeightedRow sx ax sy N ≤
      ((s ^ u : ℕ) : ℚ) +
        40 * (((2 * s * (s + u - 1)) ^ u : ℕ) : ℚ) := by
  rw [sparseDecimalWeightedRow_eq_diagonal_add_shells sx ax sy hx]
  apply add_le_add
  · simpa only [Nat.cast_pow] using
      (reducedRatioDiagonalDomain_sum_le (N := N)
        hs0 hs4 hu0 hu4 sx ax sy hxc hx)
  · let r := weightedRowShellRange sx ax sy N
    let A := 2 * s * (s + u - 1)
    calc
      (∑ j ∈ Finset.range r,
        ∑ a ∈ reducedRatioShellDomain sx ax sy N j,
          gcdKernel (signedDecimalNatValue sx ax)
            (signedDecimalNatValue sy (exponentNat a))) ≤
          ∑ j ∈ Finset.range r,
            ((A ^ u : ℕ) : ℚ) *
              (((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact reducedRatioShellDomain_sum_le_quartic
          hs0 hs4 hu0 hu4 sx ax sy hxc hx j
      _ = ((A ^ u : ℕ) : ℚ) *
          ∑ j ∈ Finset.range r,
            (((j + 2 : ℕ) : ℚ) ^ 4 / (10 : ℚ) ^ j) := by
        rw [Finset.mul_sum]
      _ ≤ ((A ^ u : ℕ) : ℚ) * 40 := by
        exact mul_le_mul_of_nonneg_left (quarticDecimalSeries_le_forty r) (by positivity)
      _ = 40 * (((2 * s * (s + u - 1)) ^ u : ℕ) : ℚ) := by
        dsimp [A]
        ring

/-- Four-token source to four-token target weighted-row bound. -/
theorem sparseDecimalWeightedRow_four_four_le
    {N : ℕ}
    (sx : Fin 4 → Bool) (ax : Fin 4 → ℕ) (sy : Fin 4 → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) :
    sparseDecimalWeightedRow sx ax sy N ≤ 393380096 := by
  convert sparseDecimalWeightedRow_le
    (s := 4) (u := 4) (N := N) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) sx ax sy hxc hx using 1
  all_goals norm_num

/-- Two-token source to four-token target weighted-row bound. -/
theorem sparseDecimalWeightedRow_two_four_le
    {N : ℕ}
    (sx : Fin 2 → Bool) (ax : Fin 2 → ℕ) (sy : Fin 4 → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) :
    sparseDecimalWeightedRow sx ax sy N ≤ 6400016 := by
  convert sparseDecimalWeightedRow_le
    (s := 2) (u := 4) (N := N) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) sx ax sy hxc hx using 1
  all_goals norm_num

/-- Two-token source to two-token target weighted-row bound. -/
theorem sparseDecimalWeightedRow_two_two_le
    {N : ℕ}
    (sx : Fin 2 → Bool) (ax : Fin 2 → ℕ) (sy : Fin 2 → Bool)
    (hxc : Noncancelling sx ax)
    (hx : 0 < signedDecimalValue sx ax) :
    sparseDecimalWeightedRow sx ax sy N ≤ 5764 := by
  convert sparseDecimalWeightedRow_le
    (s := 2) (u := 2) (N := N) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) sx ax sy hxc hx using 1
  all_goals norm_num

/-- Exact finite parameters for one cancellation case: a positive
noncancelling two-token residual and one hidden exponent. -/
def cancellationCaseParameterDomain (N : ℕ) :
    Finset (BoundedExponentVector 2 N × Fin N) :=
  positiveNoncancellingDecimalDomain twoTokenSign N ×ˢ Finset.univ

/-- A fixed labeled cancellation case is exactly the image of its residual
and hidden-exponent parameter domain. -/
theorem cancellingFourTokenCaseDomain_eq_image_parameters
    (N : ℕ) (p n : Fin 2) :
    cancellingFourTokenCaseDomain N p n =
      (cancellationCaseParameterDomain N).image fun q =>
        cancellationCaseVector p n q.1 q.2 := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨_hrange, hpos, heq⟩ := mem_cancellingFourTokenCaseDomain_iff.mp ha
    have hspec := cancellationResidual_spec p n a hpos heq
    apply Finset.mem_image.mpr
    refine ⟨(cancellationResidual p n a, a (positiveFourLabel p)), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨
        mem_positiveNoncancellingDecimalDomain_iff.mpr ⟨hspec.1, hspec.2.1⟩,
        Finset.mem_univ _⟩
    · exact cancellationCaseVector_residual_hidden p n a heq
  · intro ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    have hres := mem_positiveNoncancellingDecimalDomain_iff.mp
      (Finset.mem_product.mp hq).1
    apply mem_cancellingFourTokenCaseDomain_iff.mpr
    exact ⟨fun i => (cancellationCaseVector p n q.1 q.2 i).2,
      by simpa [cancellationCaseVector_signedValue_eq] using hres.2,
      cancellationCaseVector_selected_eq p n q.1 q.2⟩

/-- Cancellation-case reconstruction is injective in the residual and hidden exponent. -/
theorem cancellationCaseVector_injective {N : ℕ} (p n : Fin 2) :
    Function.Injective (fun q : BoundedExponentVector 2 N × Fin N =>
      cancellationCaseVector p n q.1 q.2) := by
  intro q r hqr
  apply Prod.ext
  · simpa only [cancellationResidual_caseVector] using
      congrArg (cancellationResidual p n) hqr
  · have hhidden := congrFun hqr (positiveFourLabel p)
    simpa [cancellationCaseVector, positiveFourLabel, negativeFourLabel] using hhidden

/-- Weighted row from a four-token source to primitive four-token targets. -/
def cancellingFourTokenPrimitiveRow {N : ℕ} (a : BoundedExponentVector 4 N) : ℚ :=
  ∑ b ∈ primitiveFourTokenDomain N,
    gcdKernel (signedDecimalNatValue fourTokenSign (exponentNat a))
      (signedDecimalNatValue fourTokenSign (exponentNat b))

/-- Weighted row from a four-token source to one fixed labeled cancellation case. -/
def cancellingFourTokenCaseRow {N : ℕ} (a : BoundedExponentVector 4 N)
    (p n : Fin 2) : ℚ :=
  ∑ b ∈ cancellingFourTokenCaseDomain N p n,
    gcdKernel (signedDecimalNatValue fourTokenSign (exponentNat a))
      (signedDecimalNatValue fourTokenSign (exponentNat b))

/-- Weighted row from a four-token source to all cancelling four-token targets. -/
def cancellingFourTokenRow {N : ℕ} (a : BoundedExponentVector 4 N) : ℚ :=
  ∑ b ∈ cancellingFourTokenDomain N,
    gcdKernel (signedDecimalNatValue fourTokenSign (exponentNat a))
      (signedDecimalNatValue fourTokenSign (exponentNat b))

/-- Every cancelling source exposes selected labels and a positive
noncancelling two-token residual with exact value preservation. -/
theorem cancellingFourToken_exists_residual {N : ℕ}
    {a : BoundedExponentVector 4 N} (ha : a ∈ cancellingFourTokenDomain N) :
    ∃ p n : Fin 2,
      a ∈ cancellingFourTokenCaseDomain N p n ∧
      Noncancelling twoTokenSign (exponentNat (cancellationResidual p n a)) ∧
      0 < signedDecimalValue twoTokenSign (exponentNat (cancellationResidual p n a)) ∧
      signedDecimalNatValue twoTokenSign (exponentNat (cancellationResidual p n a)) =
        signedDecimalNatValue fourTokenSign (exponentNat a) := by
  have hall := cancellingFourTokenDomain_subset_allCases N ha
  rw [allCancellingFourTokenCases, Finset.mem_biUnion] at hall
  obtain ⟨p, hp, hall⟩ := hall
  rw [Finset.mem_biUnion] at hall
  obtain ⟨n, hn, hcase⟩ := hall
  obtain ⟨_hrange, hpos, heq⟩ := mem_cancellingFourTokenCaseDomain_iff.mp hcase
  have hspec := cancellationResidual_spec p n a hpos heq
  exact ⟨p, n, hcase, hspec.1, hspec.2.1, hspec.2.2⟩

/-- A cancelling source row to primitive targets is controlled by its exact
two-token residual and the generic two/four row theorem. -/
theorem cancellingFourTokenPrimitiveRow_le {N : ℕ}
    {a : BoundedExponentVector 4 N} (ha : a ∈ cancellingFourTokenDomain N) :
    cancellingFourTokenPrimitiveRow a ≤ 6400016 := by
  obtain ⟨p, n, hcase, hnc, hpos, hvalue⟩ := cancellingFourToken_exists_residual ha
  have hrow := sparseDecimalWeightedRow_two_four_le (N := N)
    twoTokenSign (exponentNat (cancellationResidual p n a)) fourTokenSign hnc hpos
  simpa [cancellingFourTokenPrimitiveRow, sparseDecimalWeightedRow,
    primitiveFourTokenDomain, positiveNoncancellingDecimalDomain, hvalue] using hrow

/-- A fixed cancellation-case row is exactly `N` copies of the residual
two-token row, one for each hidden exponent. -/
theorem cancellingFourTokenCaseRow_eq_hidden_mul {N : ℕ}
    (source : BoundedExponentVector 2 N) (p n : Fin 2) :
    (∑ b ∈ cancellingFourTokenCaseDomain N p n,
      gcdKernel (signedDecimalNatValue twoTokenSign (exponentNat source))
        (signedDecimalNatValue fourTokenSign (exponentNat b))) =
      (N : ℚ) * sparseDecimalWeightedRow twoTokenSign
        (exponentNat source) twoTokenSign N := by
  classical
  rw [cancellingFourTokenCaseDomain_eq_image_parameters]
  rw [Finset.sum_image (fun _ _ _ _ h => cancellationCaseVector_injective p n h)]
  rw [cancellationCaseParameterDomain, Finset.sum_product]
  simp_rw [cancellationCaseVector_natValue_eq]
  rw [sparseDecimalWeightedRow]
  calc
    (∑ x ∈ positiveNoncancellingDecimalDomain twoTokenSign N,
      ∑ _h : Fin N,
        gcdKernel (signedDecimalNatValue twoTokenSign (exponentNat source))
          (signedDecimalNatValue twoTokenSign (exponentNat x))) =
        ∑ x ∈ positiveNoncancellingDecimalDomain twoTokenSign N,
          (N : ℚ) * gcdKernel (signedDecimalNatValue twoTokenSign (exponentNat source))
            (signedDecimalNatValue twoTokenSign (exponentNat x)) := by simp
    _ = (N : ℚ) * ∑ x ∈ positiveNoncancellingDecimalDomain twoTokenSign N,
          gcdKernel (signedDecimalNatValue twoTokenSign (exponentNat source))
            (signedDecimalNatValue twoTokenSign (exponentNat x)) := by
      rw [Finset.mul_sum]

/-- Each fixed cancellation-case row from a cancelling source is at most `5764N`. -/
theorem cancellingFourTokenCaseRow_le {N : ℕ}
    {a : BoundedExponentVector 4 N} (ha : a ∈ cancellingFourTokenDomain N)
    (p n : Fin 2) :
    cancellingFourTokenCaseRow a p n ≤ 5764 * N := by
  obtain ⟨ps, ns, hsourceCase, hnc, hpos, hvalue⟩ :=
    cancellingFourToken_exists_residual ha
  let source := cancellationResidual ps ns a
  have heq := cancellingFourTokenCaseRow_eq_hidden_mul source p n
  rw [hvalue] at heq
  rw [cancellingFourTokenCaseRow, heq]
  have hrow := sparseDecimalWeightedRow_two_two_le (N := N)
    twoTokenSign (exponentNat source) twoTokenSign hnc hpos
  nlinarith [mul_le_mul_of_nonneg_left hrow (show (0 : ℚ) ≤ N by positivity)]

/-- Sum over a finite union is bounded by the iterated sum when all summands
are nonnegative. -/
theorem sum_biUnion_le_sum_of_nonneg {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℚ)
    (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      have hunion : t i ∪ s.biUnion t = t i ∪ (s.biUnion t \ t i) := by
        ext a
        simp
      rw [hunion, Finset.sum_union (Finset.disjoint_sdiff)]
      exact add_le_add le_rfl
        ((Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun a _ _ => hf a)).trans ih)

/-- A cancelling source row to all cancelling targets is at most `23056N`. -/
theorem cancellingFourTokenRow_le {N : ℕ}
    {a : BoundedExponentVector 4 N} (ha : a ∈ cancellingFourTokenDomain N) :
    cancellingFourTokenRow a ≤ 23056 * N := by
  classical
  rw [cancellingFourTokenRow, cancellingFourTokenDomain_eq_allCases,
    allCancellingFourTokenCases]
  calc
    (∑ b ∈ (Finset.univ : Finset (Fin 2)).biUnion (fun p =>
      (Finset.univ : Finset (Fin 2)).biUnion fun n =>
        cancellingFourTokenCaseDomain N p n),
      gcdKernel (signedDecimalNatValue fourTokenSign (exponentNat a))
        (signedDecimalNatValue fourTokenSign (exponentNat b))) ≤
        ∑ p : Fin 2, ∑ n : Fin 2,
          cancellingFourTokenCaseRow a p n := by
      refine (sum_biUnion_le_sum_of_nonneg _ _ _
        (fun b => gcdKernel_nonneg _ _)).trans ?_
      apply Finset.sum_le_sum
      intro p hp
      exact sum_biUnion_le_sum_of_nonneg _ _ _ (fun b => gcdKernel_nonneg _ _)
    _ ≤ ∑ _p : Fin 2, ∑ _n : Fin 2, (5764 * N : ℚ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro n hn
      exact cancellingFourTokenCaseRow_le ha p n
    _ = 23056 * N := by norm_num; ring

/-- Primitive-to-primitive labeled weighted-GCD sum on the exact finite box. -/
def primitiveWeightedGCD (N : ℕ) : ℚ :=
  ∑ a ∈ primitiveFourTokenDomain N,
    ∑ b ∈ primitiveFourTokenDomain N,
      gcdKernel (primitiveFourTokenValue a) (primitiveFourTokenValue b)

/-- Cancellation-to-primitive labeled weighted-GCD sum. -/
def cancellationPrimitiveWeightedGCD (N : ℕ) : ℚ :=
  ∑ a ∈ cancellationTwoTokenDomain N,
    ∑ b ∈ primitiveFourTokenDomain N,
      gcdKernel (cancellationTwoTokenValue a) (primitiveFourTokenValue b)

/-- Cancellation-to-cancellation labeled weighted-GCD sum. -/
def cancellationWeightedGCD (N : ℕ) : ℚ :=
  ∑ a ∈ cancellationTwoTokenDomain N,
    ∑ b ∈ cancellationTwoTokenDomain N,
      gcdKernel (cancellationTwoTokenValue a) (cancellationTwoTokenValue b)

/-- Complete labeled finite weighted-GCD sum, with both mixed orientations. -/
def finiteWeightedGCD (N : ℕ) : ℚ :=
  primitiveWeightedGCD N + 2 * cancellationPrimitiveWeightedGCD N +
    cancellationWeightedGCD N

/-- Membership exposes every primitive index range, sign pattern,
noncancellation clause, and positivity clause. -/
theorem mem_primitiveFourTokenDomain_iff {N : ℕ}
    {a : BoundedExponentVector 4 N} :
    a ∈ primitiveFourTokenDomain N ↔
      (∀ i : Fin 4, (a i).1 < N) ∧
      Noncancelling fourTokenSign (exponentNat a) ∧
      0 < signedDecimalValue fourTokenSign (exponentNat a) := by
  classical
  constructor
  · intro ha
    have hfilter := Finset.mem_filter.mp ha
    exact ⟨fun i => (a i).2, hfilter.2.1, hfilter.2.2⟩
  · rintro ⟨_hrange, hnc, hpos⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnc, hpos⟩

/-- Membership exposes every cancellation index range, sign pattern,
noncancellation clause, and positivity clause. -/
theorem mem_cancellationTwoTokenDomain_iff {N : ℕ}
    {a : BoundedExponentVector 2 N} :
    a ∈ cancellationTwoTokenDomain N ↔
      (∀ i : Fin 2, (a i).1 < N) ∧
      Noncancelling twoTokenSign (exponentNat a) ∧
      0 < signedDecimalValue twoTokenSign (exponentNat a) := by
  classical
  constructor
  · intro ha
    have hfilter := Finset.mem_filter.mp ha
    exact ⟨fun i => (a i).2, hfilter.2.1, hfilter.2.2⟩
  · rintro ⟨_hrange, hnc, hpos⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnc, hpos⟩

/-- The named primitive domain is the generic positive noncancelling domain
with the prescribed signs `(+,+,-,-)`. -/
theorem primitiveFourTokenDomain_eq_positiveNoncancelling (N : ℕ) :
    primitiveFourTokenDomain N =
      positiveNoncancellingDecimalDomain fourTokenSign N := by
  rfl

/-- The named cancellation domain is the generic positive noncancelling
domain with the prescribed signs `(+,-)`. -/
theorem cancellationTwoTokenDomain_eq_positiveNoncancelling (N : ℕ) :
    cancellationTwoTokenDomain N =
      positiveNoncancellingDecimalDomain twoTokenSign N := by
  rfl

/-- At most `N^4` labeled four-token exponent vectors occur. -/
theorem primitiveFourTokenDomain_card_le (N : ℕ) :
    (primitiveFourTokenDomain N).card ≤ N ^ 4 := by
  calc
    (primitiveFourTokenDomain N).card ≤
        (Finset.univ : Finset (BoundedExponentVector 4 N)).card :=
      Finset.card_le_card (fun _ _ => Finset.mem_univ _)
    _ = N ^ 4 := by simp

/-- At most `N^2` labeled two-token exponent vectors occur. -/
theorem cancellationTwoTokenDomain_card_le (N : ℕ) :
    (cancellationTwoTokenDomain N).card ≤ N ^ 2 := by
  calc
    (cancellationTwoTokenDomain N).card ≤
        (Finset.univ : Finset (BoundedExponentVector 2 N)).card :=
      Finset.card_le_card (fun _ _ => Finset.mem_univ _)
    _ = N ^ 2 := by simp

/-- Primitive-to-primitive sector bound obtained from the four/four row
estimate and the exact `N^4` exponent box. -/
theorem primitiveWeightedGCD_le (N : ℕ) :
    primitiveWeightedGCD N ≤ 393380096 * (N : ℚ) ^ 4 := by
  classical
  unfold primitiveWeightedGCD
  calc
    (∑ a ∈ primitiveFourTokenDomain N,
        ∑ b ∈ primitiveFourTokenDomain N,
          gcdKernel (primitiveFourTokenValue a) (primitiveFourTokenValue b)) ≤
        ∑ _a ∈ primitiveFourTokenDomain N, (393380096 : ℚ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmem := mem_primitiveFourTokenDomain_iff.mp ha
      simpa [sparseDecimalWeightedRow,
        primitiveFourTokenDomain_eq_positiveNoncancelling,
        primitiveFourTokenValue] using
        (sparseDecimalWeightedRow_four_four_le (N := N)
          fourTokenSign (exponentNat a) fourTokenSign hmem.2.1 hmem.2.2)
    _ = (primitiveFourTokenDomain N).card * (393380096 : ℚ) := by simp
    _ ≤ (N ^ 4 : ℕ) * (393380096 : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right 393380096
        (primitiveFourTokenDomain_card_le N)
    _ = 393380096 * (N : ℚ) ^ 4 := by push_cast; ring

/-- Cancellation-to-primitive sector bound obtained from the two/four row
estimate and the exact `N^2` source box. -/
theorem cancellationPrimitiveWeightedGCD_le (N : ℕ) :
    cancellationPrimitiveWeightedGCD N ≤ 6400016 * (N : ℚ) ^ 2 := by
  classical
  unfold cancellationPrimitiveWeightedGCD
  calc
    (∑ a ∈ cancellationTwoTokenDomain N,
        ∑ b ∈ primitiveFourTokenDomain N,
          gcdKernel (cancellationTwoTokenValue a) (primitiveFourTokenValue b)) ≤
        ∑ _a ∈ cancellationTwoTokenDomain N, (6400016 : ℚ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmem := mem_cancellationTwoTokenDomain_iff.mp ha
      simpa [sparseDecimalWeightedRow,
        primitiveFourTokenDomain_eq_positiveNoncancelling,
        cancellationTwoTokenValue, primitiveFourTokenValue] using
        (sparseDecimalWeightedRow_two_four_le (N := N)
          twoTokenSign (exponentNat a) fourTokenSign hmem.2.1 hmem.2.2)
    _ = (cancellationTwoTokenDomain N).card * (6400016 : ℚ) := by simp
    _ ≤ (N ^ 2 : ℕ) * (6400016 : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right 6400016
        (cancellationTwoTokenDomain_card_le N)
    _ = 6400016 * (N : ℚ) ^ 2 := by push_cast; ring

/-- Cancellation-to-cancellation sector bound obtained from the two/two row
estimate and the exact `N^2` source box. -/
theorem cancellationWeightedGCD_le (N : ℕ) :
    cancellationWeightedGCD N ≤ 5764 * (N : ℚ) ^ 2 := by
  classical
  unfold cancellationWeightedGCD
  calc
    (∑ a ∈ cancellationTwoTokenDomain N,
        ∑ b ∈ cancellationTwoTokenDomain N,
          gcdKernel (cancellationTwoTokenValue a) (cancellationTwoTokenValue b)) ≤
        ∑ _a ∈ cancellationTwoTokenDomain N, (5764 : ℚ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmem := mem_cancellationTwoTokenDomain_iff.mp ha
      simpa [sparseDecimalWeightedRow,
        cancellationTwoTokenDomain_eq_positiveNoncancelling,
        cancellationTwoTokenValue] using
        (sparseDecimalWeightedRow_two_two_le (N := N)
          twoTokenSign (exponentNat a) twoTokenSign hmem.2.1 hmem.2.2)
    _ = (cancellationTwoTokenDomain N).card * (5764 : ℚ) := by simp
    _ ≤ (N ^ 2 : ℕ) * (5764 : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right 5764
        (cancellationTwoTokenDomain_card_le N)
    _ = 5764 * (N : ℚ) ^ 2 := by push_cast; ring

/-- Symmetry of the ordinary GCD kernel. -/
theorem gcdKernel_comm (x y : ℕ) : gcdKernel x y = gcdKernel y x := by
  simp [gcdKernel, Nat.gcd_comm, Nat.max_comm]

/-- Exact weighted-GCD sum over every positive labeled four-token vector in
the box `0 <= a_i < N`, including hidden opposite-sign cancellations. -/
def allPositiveFourTokenWeightedGCD (N : ℕ) : ℚ :=
  ∑ a ∈ allPositiveFourTokenDomain N,
    ∑ b ∈ allPositiveFourTokenDomain N,
      gcdKernel (signedDecimalNatValue fourTokenSign (exponentNat a))
        (signedDecimalNatValue fourTokenSign (exponentNat b))

/-- Exact long-difference witness domain. The vector represents the ordered
long pairs `q=(a₀,a₂)` and `q'=(a₃,a₁)`, with both weak lag constraints and
strictly positive difference. -/
def longDifferenceDomain (m N : ℕ) : Finset (BoundedExponentVector 4 N) := by
  classical
  exact Finset.univ.filter fun a =>
    m ≤ Nat.dist (a 0).1 (a 2).1 ∧
    m ≤ Nat.dist (a 3).1 (a 1).1 ∧
    0 < signedDecimalValue fourTokenSign (exponentNat a)

/-- Membership audit for the exact long-difference witness domain, including
all half-open exponent ranges, both weak lag constraints, and positivity. -/
theorem mem_longDifferenceDomain_iff {m N : ℕ}
    {a : BoundedExponentVector 4 N} :
    a ∈ longDifferenceDomain m N ↔
      (∀ i : Fin 4, (a i).1 < N) ∧
      m ≤ Nat.dist (a 0).1 (a 2).1 ∧
      m ≤ Nat.dist (a 3).1 (a 1).1 ∧
      0 < signedDecimalValue fourTokenSign (exponentNat a) := by
  constructor
  · intro ha
    have hm := Finset.mem_filter.mp ha
    exact ⟨fun i => (a i).2, hm.2.1, hm.2.2.1, hm.2.2.2⟩
  · rintro ⟨_hrange, hlag₁, hlag₂, hpos⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlag₁, hlag₂, hpos⟩

/-- Positive natural difference represented by a four-token witness. -/
def longDifferenceValue {N : ℕ} (a : BoundedExponentVector 4 N) : ℕ :=
  signedDecimalNatValue fourTokenSign (exponentNat a)

/-- The exact finite support of positive long-difference values. -/
def longDifferenceSupport (m N : ℕ) : Finset ℕ :=
  (longDifferenceDomain m N).image longDifferenceValue

/-- Membership in the value support is witnessed by an exact long-difference vector. -/
theorem mem_longDifferenceSupport_iff {m N d : ℕ} :
    d ∈ longDifferenceSupport m N ↔
      ∃ a ∈ longDifferenceDomain m N, longDifferenceValue a = d := by
  simp [longDifferenceSupport]

/-- Exact multiplicity `M(d)`, defined as the cardinality of the witness fiber. -/
def longDifferenceMultiplicity (m N d : ℕ) : ℕ :=
  ((longDifferenceDomain m N).filter fun a => longDifferenceValue a = d).card

/-- Fiber-cardinality audit for the exact multiplicity. -/
theorem longDifferenceMultiplicity_eq_card_filter (m N d : ℕ) :
    longDifferenceMultiplicity m N d =
      ((longDifferenceDomain m N).filter fun a => longDifferenceValue a = d).card :=
  rfl

/-- T15's finite multiplicity-form weighted GCD sum on the exact support. -/
def longDifferenceMultiplicityWeightedGCD (m N : ℕ) : ℚ :=
  ∑ d ∈ longDifferenceSupport m N,
    ∑ e ∈ longDifferenceSupport m N,
      (longDifferenceMultiplicity m N d : ℚ) *
        (longDifferenceMultiplicity m N e : ℚ) * gcdKernel d e

/-- Equivalent expansion over ordered pairs of exact long-difference witnesses. -/
def longDifferenceWitnessWeightedGCD (m N : ℕ) : ℚ :=
  ∑ q ∈ longDifferenceDomain m N ×ˢ longDifferenceDomain m N,
    gcdKernel (longDifferenceValue q.1) (longDifferenceValue q.2)

/-- A weighted sum over multiplicities equals the corresponding sum over
exact witnesses. -/
theorem longDifference_sum_multiplicity_eq_sum_witnesses
    (m N : ℕ) (F : ℕ → ℚ) :
    (∑ d ∈ longDifferenceSupport m N,
      (longDifferenceMultiplicity m N d : ℚ) * F d) =
      ∑ a ∈ longDifferenceDomain m N, F (longDifferenceValue a) := by
  classical
  calc
    (∑ d ∈ longDifferenceSupport m N,
      (longDifferenceMultiplicity m N d : ℚ) * F d) =
        ∑ d ∈ longDifferenceSupport m N,
          ∑ a ∈ longDifferenceDomain m N with longDifferenceValue a = d,
            F (longDifferenceValue a) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [longDifferenceMultiplicity]
      calc
        ((#{a ∈ longDifferenceDomain m N | longDifferenceValue a = d} : ℕ) : ℚ) * F d =
            ∑ _a ∈ (longDifferenceDomain m N).filter
              (fun a => longDifferenceValue a = d), F d := by simp
        _ = ∑ a ∈ (longDifferenceDomain m N).filter
              (fun a => longDifferenceValue a = d), F (longDifferenceValue a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a ∈ longDifferenceDomain m N, F (longDifferenceValue a) := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun a ha => Finset.mem_image_of_mem longDifferenceValue ha) _

/-- Exact equality between T15's multiplicity expansion and the ordered
witness-pair expansion. -/
theorem longDifferenceMultiplicityWeightedGCD_eq_witness
    (m N : ℕ) :
    longDifferenceMultiplicityWeightedGCD m N =
      longDifferenceWitnessWeightedGCD m N := by
  classical
  rw [longDifferenceMultiplicityWeightedGCD]
  calc
    (∑ d ∈ longDifferenceSupport m N,
      ∑ e ∈ longDifferenceSupport m N,
        (longDifferenceMultiplicity m N d : ℚ) *
          (longDifferenceMultiplicity m N e : ℚ) * gcdKernel d e) =
        ∑ d ∈ longDifferenceSupport m N,
          (longDifferenceMultiplicity m N d : ℚ) *
            ∑ b ∈ longDifferenceDomain m N,
              gcdKernel d (longDifferenceValue b) := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ e ∈ longDifferenceSupport m N,
          (longDifferenceMultiplicity m N d : ℚ) *
            (longDifferenceMultiplicity m N e : ℚ) * gcdKernel d e) =
            ∑ e ∈ longDifferenceSupport m N,
              (longDifferenceMultiplicity m N e : ℚ) *
                ((longDifferenceMultiplicity m N d : ℚ) * gcdKernel d e) := by
          apply Finset.sum_congr rfl
          intro e he
          ring
        _ = ∑ b ∈ longDifferenceDomain m N,
              (longDifferenceMultiplicity m N d : ℚ) *
                gcdKernel d (longDifferenceValue b) :=
          longDifference_sum_multiplicity_eq_sum_witnesses m N _
        _ = (longDifferenceMultiplicity m N d : ℚ) *
              ∑ b ∈ longDifferenceDomain m N,
                gcdKernel d (longDifferenceValue b) := by
          rw [Finset.mul_sum]
    _ = ∑ a ∈ longDifferenceDomain m N,
          ∑ b ∈ longDifferenceDomain m N,
            gcdKernel (longDifferenceValue a) (longDifferenceValue b) := by
      rw [longDifference_sum_multiplicity_eq_sum_witnesses]
    _ = longDifferenceWitnessWeightedGCD m N := by
      rw [longDifferenceWitnessWeightedGCD, Finset.sum_product]

/-- Every exact long-difference witness is an all-positive four-token witness. -/
theorem longDifferenceDomain_subset_allPositive (m N : ℕ) :
    longDifferenceDomain m N ⊆ allPositiveFourTokenDomain N := by
  intro a ha
  have hm := mem_longDifferenceDomain_iff.mp ha
  exact mem_allPositiveFourTokenDomain_iff.mpr ⟨hm.1, hm.2.2.2⟩

/-- The exact long-difference witness expansion is bounded by the complete
all-positive four-token weighted sum solely by domain inclusion and kernel
nonnegativity. -/
theorem longDifferenceWitnessWeightedGCD_le_allPositive (m N : ℕ) :
    longDifferenceWitnessWeightedGCD m N ≤ allPositiveFourTokenWeightedGCD N := by
  classical
  have hAll : allPositiveFourTokenWeightedGCD N =
      ∑ q ∈ allPositiveFourTokenDomain N ×ˢ allPositiveFourTokenDomain N,
        gcdKernel (longDifferenceValue q.1) (longDifferenceValue q.2) := by
    rw [allPositiveFourTokenWeightedGCD, Finset.sum_product]
    rfl
  rw [longDifferenceWitnessWeightedGCD, hAll]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.product_subset_product
      (longDifferenceDomain_subset_allPositive m N)
      (longDifferenceDomain_subset_allPositive m N)
  · intro q hqAll hqLong
    exact gcdKernel_nonneg _ _

/-- Cancelling-source to primitive-target sector with the hidden canceled
exponent retained in the four-token source. -/
def cancellingPrimitiveFourTokenWeightedGCD (N : ℕ) : ℚ :=
  ∑ a ∈ cancellingFourTokenDomain N, cancellingFourTokenPrimitiveRow a

/-- Cancelling-source to cancelling-target sector with both hidden canceled
exponents retained. -/
def cancellingFourTokenWeightedGCD (N : ℕ) : ℚ :=
  ∑ a ∈ cancellingFourTokenDomain N, cancellingFourTokenRow a

/-- Exact primitive/cancellation partition of the complete positive
four-token weighted sum. The factor two records both mixed orientations. -/
theorem allPositiveFourTokenWeightedGCD_eq_sectors (N : ℕ) :
    allPositiveFourTokenWeightedGCD N =
      primitiveWeightedGCD N +
        2 * cancellingPrimitiveFourTokenWeightedGCD N +
          cancellingFourTokenWeightedGCD N := by
  classical
  let P := primitiveFourTokenDomain N
  let C := cancellingFourTokenDomain N
  let value : BoundedExponentVector 4 N → ℕ := fun a =>
    signedDecimalNatValue fourTokenSign (exponentNat a)
  have hdisj : Disjoint P C := by
    simpa [P, C] using primitiveFourTokenDomain_disjoint_cancellingFourTokenDomain N
  have hcross :
      (∑ a ∈ P, ∑ b ∈ C, gcdKernel (value a) (value b)) =
        ∑ a ∈ C, ∑ b ∈ P, gcdKernel (value a) (value b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact gcdKernel_comm _ _
  rw [allPositiveFourTokenWeightedGCD,
    allPositiveFourTokenDomain_partition,
    Finset.sum_union hdisj]
  change
    (∑ a ∈ P, ∑ b ∈ P ∪ C, gcdKernel (value a) (value b)) +
      (∑ a ∈ C, ∑ b ∈ P ∪ C, gcdKernel (value a) (value b)) = _
  simp_rw [Finset.sum_union hdisj, Finset.sum_add_distrib]
  rw [hcross]
  simp only [P, C, value, primitiveWeightedGCD,
    primitiveFourTokenValue,
    cancellingPrimitiveFourTokenWeightedGCD,
    cancellingFourTokenPrimitiveRow,
    cancellingFourTokenWeightedGCD, cancellingFourTokenRow]
  ring

/-- Mixed sector bound with the hidden canceled exponent and all four labeled
cancellation choices included. -/
theorem cancellingPrimitiveFourTokenWeightedGCD_le (N : ℕ) :
    cancellingPrimitiveFourTokenWeightedGCD N ≤
      25600064 * (N : ℚ) ^ 3 := by
  classical
  unfold cancellingPrimitiveFourTokenWeightedGCD
  calc
    (∑ a ∈ cancellingFourTokenDomain N, cancellingFourTokenPrimitiveRow a) ≤
        ∑ _a ∈ cancellingFourTokenDomain N, (6400016 : ℚ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact cancellingFourTokenPrimitiveRow_le ha
    _ = (cancellingFourTokenDomain N).card * (6400016 : ℚ) := by simp
    _ ≤ (4 * N ^ 3 : ℕ) * (6400016 : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right 6400016
        (cancellingFourTokenDomain_card_le N)
    _ = 25600064 * (N : ℚ) ^ 3 := by push_cast; ring

/-- Cancelling/cancelling sector bound with both hidden canceled exponents
and all sixteen pairs of labeled cancellation choices included. -/
theorem cancellingFourTokenWeightedGCD_le (N : ℕ) :
    cancellingFourTokenWeightedGCD N ≤ 92224 * (N : ℚ) ^ 4 := by
  classical
  unfold cancellingFourTokenWeightedGCD
  calc
    (∑ a ∈ cancellingFourTokenDomain N, cancellingFourTokenRow a) ≤
        ∑ _a ∈ cancellingFourTokenDomain N, (23056 * N : ℚ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact cancellingFourTokenRow_le ha
    _ = (cancellingFourTokenDomain N).card * (23056 * N : ℚ) := by simp
    _ ≤ (4 * N ^ 3 : ℕ) * (23056 * N : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right (23056 * N)
        (cancellingFourTokenDomain_card_le N)
    _ = 92224 * (N : ℚ) ^ 4 := by push_cast; ring

/-- Unconditional finite weighted-GCD theorem. The sum is over the exact
half-open exponent boxes in `primitiveFourTokenDomain` and
`cancellationTwoTokenDomain`; signs, positivity, and noncancellation are
audited by their membership theorems. The proof uses the full reduced ratio,
all decimal shells, both mixed orientations, and the explicit T15 constant
`574913232`. There is no analytic, pi-specific, or conclusion-equivalent
hypothesis. -/
theorem finiteWeightedGCD_le (N : ℕ) :
    finiteWeightedGCD N ≤ 574913232 * (N : ℚ) ^ 4 := by
  have hpp := primitiveWeightedGCD_le N
  have hcp := cancellationPrimitiveWeightedGCD_le N
  have hcc := cancellationWeightedGCD_le N
  have hpow : (N : ℚ) ^ 2 ≤ (N : ℚ) ^ 4 := by
    by_cases hN : N = 0
    · simp [hN]
    · have hN1 : (1 : ℚ) ≤ N := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
      have hsquare : (1 : ℚ) ≤ (N : ℚ) ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (N : ℚ)) (sub_nonneg.mpr hsquare)]
  unfold finiteWeightedGCD
  nlinarith

/-- The complete primitive four-token weighted-GCD bound, now including every
opposite-sign cancellation and hidden canceled exponent. The constant is the
explicit T15 constant; the proof actually obtains the smaller coefficient
`444672448`. -/
theorem allPositiveFourTokenWeightedGCD_le (N : ℕ) :
    allPositiveFourTokenWeightedGCD N ≤ 574913232 * (N : ℚ) ^ 4 := by
  rw [allPositiveFourTokenWeightedGCD_eq_sectors]
  have hpp := primitiveWeightedGCD_le N
  have hcp := cancellingPrimitiveFourTokenWeightedGCD_le N
  have hcc := cancellingFourTokenWeightedGCD_le N
  have hpow : (N : ℚ) ^ 3 ≤ (N : ℚ) ^ 4 := by
    by_cases hN : N = 0
    · simp [hN]
    · have hN1 : (1 : ℚ) ≤ N := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
      have hcube_nonneg : (0 : ℚ) ≤ (N : ℚ) ^ 3 := by positivity
      nlinarith [mul_nonneg hcube_nonneg (sub_nonneg.mpr hN1)]
  have hcp' : cancellingPrimitiveFourTokenWeightedGCD N ≤
      25600064 * (N : ℚ) ^ 4 :=
    hcp.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  calc
    primitiveWeightedGCD N +
          2 * cancellingPrimitiveFourTokenWeightedGCD N +
        cancellingFourTokenWeightedGCD N ≤
        393380096 * (N : ℚ) ^ 4 +
          2 * (25600064 * (N : ℚ) ^ 4) +
            92224 * (N : ℚ) ^ 4 := by gcongr
    _ ≤ 574913232 * (N : ℚ) ^ 4 := by
      have hnonneg : (0 : ℚ) ≤ (N : ℚ) ^ 4 := by positivity
      nlinarith

/-- T16's named weighted-GCD theorem on the exact multiplicity support.
For every `m,N`, witnesses have all four exponents in `0,...,N-1`, both
ordered-pair lags satisfy the weak cutoff `m <= dist`, multiplicities are
fiber cardinalities of strictly positive differences, and the kernel uses the
full ordinary gcd. The constant `574913232` is explicit and no arithmetic or
analytic estimate is assumed. -/
theorem longDifferenceMultiplicityWeightedGCD_le (m N : ℕ) :
    longDifferenceMultiplicityWeightedGCD m N ≤
      574913232 * (N : ℚ) ^ 4 := by
  calc
    longDifferenceMultiplicityWeightedGCD m N =
        longDifferenceWitnessWeightedGCD m N :=
      longDifferenceMultiplicityWeightedGCD_eq_witness m N
    _ ≤ allPositiveFourTokenWeightedGCD N :=
      longDifferenceWitnessWeightedGCD_le_allPositive m N
    _ ≤ 574913232 * (N : ℚ) ^ 4 :=
      allPositiveFourTokenWeightedGCD_le N

end

end Theory.PiDigits.LongLagBlockCollisionDecay.T16

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T16.tenValuation_lowDecimalCoefficient
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T16.cancellationValue_ten_reduction
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T16.sparseDecimal_rationalNeighbor
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T16.sparseDecimalRationalNeighborDomain_card_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T16.longDifferenceMultiplicityWeightedGCD_le
