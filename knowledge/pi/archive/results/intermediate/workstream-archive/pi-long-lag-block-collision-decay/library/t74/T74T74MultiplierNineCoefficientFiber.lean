import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc

/-!
# T74: multiplier-nine coefficient-fiber obstruction

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module formalizes only a finite obstruction in the residual-A12, `m = 1`,
dyadic pooled double-shift algebra imported from T69.  It proves that the
coefficients of the characters `9*10^K` and `-9*10^K` do not cancel
coefficientwise.
It proves no fixed-pi estimate, no T69 aggregate premise, no T29 predicate,
and none of C3, C2, C1, or the canonical collision estimate.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T74

open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T66
open Theory.PiDigits.LongLagBlockCollisionDecay.T68
open Theory.PiDigits.LongLagBlockCollisionDecay.T69

/-- The repunit channel frequency before the orbit shift. -/
def q (h r : ℕ) : ℕ := h * (10 ^ r - 1)

/-- The signed difference of two ordered channels. -/
def qDiff (h r h' r' : ℕ) : ℤ := (q h r : ℤ) - q h' r'

/-- Every literal frequency and shift occurring in T69. -/
def channelDomain (t : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 10 ×ˢ Finset.Ico 1 (H t)

/-- T69's triangular product weight for an ordered pair of shifts. -/
def pairWeight (t r r' : ℕ) : ℕ := (H t - r) * (H t - r')

/-- The common endpoint of two unequal shifted orbit sums. -/
def commonLength (t r r' : ℕ) : ℕ := N t - max r r'

/-- The exact formal Laurent polynomial obtained by expanding the pooled
double-shift square.  Exponents are integers, so reversal is literal. -/
def pooledLaurent (t : ℕ) : ℤ →₀ ℕ :=
  ∑ y ∈ channelDomain t,
    ∑ x ∈ channelDomain t,
      ∑ k ∈ Finset.range (commonLength t x.2 y.2),
        Finsupp.single (qDiff x.1 x.2 y.1 y.2 * (10 : ℤ) ^ k)
          (pairWeight t x.2 y.2)

/-- Membership exposes both frequency domains and both strict shift domains. -/
theorem mem_channelDomain_iff {t h r : ℕ} :
    (h, r) ∈ channelDomain t ↔ 1 ≤ h ∧ h ≤ 10 ∧ 1 ≤ r ∧ r < H t := by
  simp [channelDomain, and_assoc]

/-- The polynomial definition exposes the triangular weight and the exact
unequal-length cutoff `k < N_t - max(r,r')`. -/
theorem pooledLaurent_literal (t : ℕ) :
    pooledLaurent t =
      ∑ h' ∈ Finset.Icc 1 10,
        ∑ r' ∈ Finset.Ico 1 (H t),
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r r'),
                Finsupp.single (qDiff h r h' r' * (10 : ℤ) ^ k)
                  ((H t - r) * (H t - r')) := by
  simp [pooledLaurent, channelDomain, commonLength, pairWeight,
    Finset.sum_product]

/-- Coefficient extraction from each displayed Laurent monomial. -/
theorem laurentMonomial_apply (e z : ℤ) (w : ℕ) :
    (Finsupp.single e w : ℤ →₀ ℕ) z = if e = z then w else 0 := by
  exact Finsupp.single_apply

/-- Coefficient extraction retains the complete five-variable finite sum. -/
theorem pooledLaurent_apply (t : ℕ) (z : ℤ) :
    pooledLaurent t z =
      ∑ h' ∈ Finset.Icc 1 10,
        ∑ r' ∈ Finset.Ico 1 (H t),
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r r'),
                if qDiff h r h' r' * (10 : ℤ) ^ k = z then
                  (H t - r) * (H t - r') else 0 := by
  rw [pooledLaurent_literal]
  simp only [Finset.sum_apply', Finsupp.single_apply]

/-- The four positive-orientation families in the multiplier-nine fiber. -/
inductive NineFamily
  | sameShift
  | crossFrequency
  | verticalOne
  | verticalTen
  deriving DecidableEq, Fintype

/-- Explicit positive-orientation family membership. -/
def PositiveFamily (family : NineFamily)
    (h r h' r' a : ℕ) : Prop :=
  match family with
  | .sameShift =>
      r = 1 ∧ r' = 1 ∧ a = 0 ∧ h = h' + 1 ∧ 1 ≤ h' ∧ h' ≤ 9
  | .crossFrequency =>
      h = 1 ∧ h' = 10 ∧ r = r' + 1 ∧ a = 0 ∧ 1 ≤ r'
  | .verticalOne =>
      h = 1 ∧ h' = 1 ∧ r = r' + 1 ∧ a = r' ∧ 1 ≤ r'
  | .verticalTen =>
      h = 10 ∧ h' = 10 ∧ r = r' + 1 ∧ a = r' + 1 ∧ 1 ≤ r'

instance instDecidablePositiveFamily (family : NineFamily)
    (h r h' r' a : ℕ) : Decidable (PositiveFamily family h r h' r' a) := by
  cases family <;> unfold PositiveFamily <;> infer_instance

/-- Reversal supplies the negative orientation without changing any domain,
weight, or cutoff. -/
def NegativeFamily (family : NineFamily)
    (h r h' r' a : ℕ) : Prop := PositiveFamily family h' r' h r a

/-- Every displayed positive family has the claimed base difference. -/
theorem positiveFamily_qDiff
    {family : NineFamily} {h r h' r' a : ℕ}
    (hf : PositiveFamily family h r h' r' a) :
    qDiff h r h' r' = 9 * (10 : ℤ) ^ a := by
  cases family <;> simp only [PositiveFamily] at hf
  · rcases hf with ⟨rfl, rfl, rfl, rfl, hj1, hj9⟩
    simp [q, qDiff]
    omega
  · rcases hf with ⟨rfl, rfl, rfl, rfl, hs⟩
    simp [q, qDiff, pow_succ]
    ring
  · rcases hf with ⟨rfl, rfl, rfl, rfl, hs⟩
    simp [q, qDiff, pow_succ]
    ring
  · rcases hf with ⟨rfl, rfl, rfl, rfl, hs⟩
    simp [q, qDiff, pow_succ]
    ring

/-- Reversing a positive family negates its multiplier-nine character. -/
theorem negativeFamily_qDiff
    {family : NineFamily} {h r h' r' a : ℕ}
    (hf : NegativeFamily family h r h' r' a) :
    qDiff h r h' r' = -(9 * (10 : ℤ) ^ a) := by
  have hp := positiveFamily_qDiff hf
  unfold qDiff at hp ⊢
  linarith

/-- Every positive repunit channel has residue `9*h` modulo ten. -/
theorem q_mod_ten (h r : ℕ) (hr : 1 ≤ r) :
    q h r % 10 = (9 * h) % 10 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp only [q, Nat.add_comm 1 s, pow_succ]
  have hpow : 1 ≤ 10 ^ s := one_le_pow₀ (by norm_num)
  have hrep : 10 ^ s * 10 - 1 = 10 * (10 ^ s - 1) + 9 := by omega
  rw [hrep, Nat.mul_add, Nat.add_mod, Nat.mul_mod]
  simp [Nat.mul_comm]

/-- A positive multiplier-nine difference with positive decimal valuation has
the same frequency multiplier on both channels. -/
theorem multiplier_eq_of_positiveExponent
    {h r h' r' a : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r') (ha : 1 ≤ a)
    (heq : qDiff h r h' r' = 9 * (10 : ℤ) ^ a) : h = h' := by
  have heq' : (q h r : ℤ) = 9 * (10 : ℤ) ^ a + q h' r' := by
    unfold qDiff at heq
    linarith
  have heqNat : q h r = 9 * 10 ^ a + q h' r' := by
    exact_mod_cast heq'
  have hmod := congrArg (fun n : ℕ => n % 10) heqNat
  change q h r % 10 = (9 * 10 ^ a + q h' r') % 10 at hmod
  rw [q_mod_ten h r hr, Nat.add_mod, q_mod_ten h' r' hr'] at hmod
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp only [Nat.add_comm 1 b, pow_succ] at hmod
  simp [Nat.mul_mod, Nat.add_mod] at hmod
  interval_cases h <;> interval_cases h' <;> norm_num at *

/-- At exponent zero, the bounded residue alternatives are exactly the nine
adjacent multipliers and the wraparound pair `(1,10)`. -/
theorem multiplier_pair_of_zeroExponent
    {h r h' r' : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (heq : qDiff h r h' r' = 9) :
    (h = h' + 1 ∧ 1 ≤ h' ∧ h' ≤ 9) ∨ (h = 1 ∧ h' = 10) := by
  have heq' : (q h r : ℤ) = 9 + q h' r' := by
    unfold qDiff at heq
    linarith
  have heqNat : q h r = 9 + q h' r' := by exact_mod_cast heq'
  have hmod := congrArg (fun n : ℕ => n % 10) heqNat
  change q h r % 10 = (9 + q h' r') % 10 at hmod
  rw [q_mod_ten h r hr, Nat.add_mod, q_mod_ten h' r' hr'] at hmod
  simp [Nat.mul_mod, Nat.add_mod] at hmod
  interval_cases h <;> interval_cases h' <;> norm_num at *

/-- Every channel with shift at least two has its last two decimal digits
equal to those of `99*h`. -/
theorem q_mod_hundred (h r : ℕ) (hr : 2 ≤ r) :
    q h r % 100 = (99 * h) % 100 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp only [q, pow_add]
  norm_num only [pow_two]
  have hpow : 1 ≤ 10 ^ s := one_le_pow₀ (by norm_num)
  have hrep : 100 * 10 ^ s - 1 = 100 * (10 ^ s - 1) + 99 := by omega
  rw [hrep, Nat.mul_add, Nat.add_mod, Nat.mul_mod]
  simp [Nat.mul_comm]

/-- The adjacent-multiplier zero-valuation branch forces both shifts to be
the first shift. -/
theorem adjacent_zeroExponent_shifts
    {h r h' r' : ℕ}
    (hh : h = h' + 1) (hh' : 1 ≤ h') (hh'9 : h' ≤ 9)
    (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (heq : qDiff h r h' r' = 9) : r = 1 ∧ r' = 1 := by
  have heq' : (q h r : ℤ) = 9 + q h' r' := by
    unfold qDiff at heq
    linarith
  have heqNat : q h r = 9 + q h' r' := by exact_mod_cast heq'
  subst h
  by_cases hr1 : r = 1
  · subst r
    simp [q, Nat.add_mul] at heqNat
    have hm : h' * 9 = h' * (10 ^ r' - 1) := by
      omega
    have hrep : 9 = 10 ^ r' - 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega) hm
    have hp : 10 ^ r' = 10 ^ 1 := by norm_num at hrep ⊢; omega
    exact ⟨rfl, Nat.pow_right_injective (by norm_num) hp⟩
  · by_cases hr1' : r' = 1
    · subst r'
      simp [q, Nat.add_mul] at heqNat
      have hm' : h' * (10 ^ r - 1) + (10 ^ r - 1) = h' * 9 + 9 := by
        omega
      have hm : (h' + 1) * (10 ^ r - 1) = (h' + 1) * 9 := by
        calc
          (h' + 1) * (10 ^ r - 1) = h' * (10 ^ r - 1) + (10 ^ r - 1) := by ring
          _ = h' * 9 + 9 := hm'
          _ = (h' + 1) * 9 := by ring
      have hrep : 10 ^ r - 1 = 9 :=
        Nat.eq_of_mul_eq_mul_left (by omega) hm
      have hp : 10 ^ r = 10 ^ 1 := by norm_num at hrep ⊢; omega
      exact ⟨Nat.pow_right_injective (by norm_num) hp, rfl⟩
    · have hr2 : 2 ≤ r := by omega
      have hr2' : 2 ≤ r' := by omega
      have hmod := congrArg (fun n : ℕ => n % 100) heqNat
      change q (h' + 1) r % 100 = (9 + q h' r') % 100 at hmod
      rw [q_mod_hundred _ _ hr2, Nat.add_mod, q_mod_hundred _ _ hr2'] at hmod
      interval_cases h' <;> norm_num at *

/-- The wraparound zero-valuation branch is exactly the adjacent cross-
frequency family. -/
theorem cross_zeroExponent_shifts
    {r r' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (heq : qDiff 1 r 10 r' = 9) : r = r' + 1 := by
  have heq' : (q 1 r : ℤ) = 9 + q 10 r' := by
    unfold qDiff at heq
    linarith
  have heqNat : q 1 r = 9 + q 10 r' := by exact_mod_cast heq'
  have hp : 10 ^ r = 10 ^ (r' + 1) := by
    simp only [q, one_mul] at heqNat
    rw [pow_succ]
    have hpow : 1 ≤ 10 ^ r := one_le_pow₀ (by norm_num)
    have hpow' : 1 ≤ 10 ^ r' := one_le_pow₀ (by norm_num)
    omega
  exact Nat.pow_right_injective (by norm_num) hp

/-- Complete positive-orientation classification at decimal valuation zero. -/
theorem positive_zeroExponent_classification
    {h r h' r' : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (heq : qDiff h r h' r' = 9) :
    PositiveFamily .sameShift h r h' r' 0 ∨
      PositiveFamily .crossFrequency h r h' r' 0 := by
  rcases multiplier_pair_of_zeroExponent hh hh10 hh' hh'10 hr hr' heq with
    hadj | hcross
  · rcases adjacent_zeroExponent_shifts hadj.1 hadj.2.1 hadj.2.2 hr hr' heq with
      ⟨rfl, rfl⟩
    left
    exact ⟨rfl, rfl, rfl, hadj.1, hadj.2.1, hadj.2.2⟩
  · rcases hcross with ⟨rfl, rfl⟩
    right
    exact ⟨rfl, rfl, cross_zeroExponent_shifts hr hr' heq, rfl, hr'⟩

/-- For a positive multiplier, the repunit channel is strictly increasing in
its shift. -/
theorem q_strictMono (h : ℕ) (hh : 1 ≤ h) : StrictMono (q h) := by
  intro r r' hrr'
  have hp : 10 ^ r < 10 ^ r' :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).2 hrr'
  have hs : 10 ^ r - 1 < 10 ^ r' - 1 := by
    have h1 : 1 ≤ 10 ^ r := one_le_pow₀ (by norm_num)
    have h1' : 1 ≤ 10 ^ r' := one_le_pow₀ (by norm_num)
    omega
  exact (Nat.mul_lt_mul_left hh).2 hs

/-- A small positive multiplier times a positive repunit remains primitive
with respect to the composite base ten. -/
theorem small_mul_repunit_not_dvd_ten
    {h d : ℕ} (hh : 1 ≤ h) (hh9 : h ≤ 9) (hd : 1 ≤ d) :
    ¬ 10 ∣ h * (10 ^ d - 1) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hm := q_mod_ten h d hd
  change (h * (10 ^ d - 1)) % 10 = (9 * h) % 10 at hm
  interval_cases h <;> norm_num at * <;> omega

/-- Factoring two same-multiplier channels isolates the exact decimal
valuation and the positive repunit gap. -/
theorem sameMultiplier_factorization
    {h r r' a : ℕ} (hh : 1 ≤ h) (hrlt : r' < r)
    (heq : qDiff h r h r' = 9 * (10 : ℤ) ^ a) :
    10 ^ r' * (h * (10 ^ (r - r') - 1)) = 9 * 10 ^ a := by
  have heq' : (q h r : ℤ) = 9 * (10 : ℤ) ^ a + q h r' := by
    unfold qDiff at heq
    linarith
  have heqNat : q h r = 9 * 10 ^ a + q h r' := by exact_mod_cast heq'
  have hpow : 1 ≤ 10 ^ r := one_le_pow₀ (by norm_num)
  have hpow' : 1 ≤ 10 ^ r' := one_le_pow₀ (by norm_num)
  have hhpow : h ≤ h * 10 ^ r := by
    simpa using Nat.mul_le_mul_left h hpow
  have hhpow' : h ≤ h * 10 ^ r' := by
    simpa using Nat.mul_le_mul_left h hpow'
  have hlarge : h * 10 ^ r = 9 * 10 ^ a + h * 10 ^ r' := by
    unfold q at heqNat
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib] at heqNat
    omega
  have hpows : 10 ^ r' ≤ 10 ^ r :=
    (Nat.pow_le_pow_iff_right (by norm_num)).2 (Nat.le_of_lt hrlt)
  have hmulpows : h * 10 ^ r' ≤ h * 10 ^ r := Nat.mul_le_mul_left h hpows
  have hdiff : h * (10 ^ r - 10 ^ r') = 9 * 10 ^ a := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hrEq : r' + (r - r') = r := Nat.add_sub_of_le (Nat.le_of_lt hrlt)
  have hfactor : 10 ^ r - 10 ^ r' = 10 ^ r' * (10 ^ (r - r') - 1) := by
    calc
      10 ^ r - 10 ^ r' = 10 ^ (r' + (r - r')) - 10 ^ r' := by rw [hrEq]
      _ = 10 ^ r' * 10 ^ (r - r') - 10 ^ r' := by rw [pow_add]
      _ = 10 ^ r' * (10 ^ (r - r') - 1) := by
        rw [Nat.mul_sub_left_distrib]
        simp
  rw [hfactor] at hdiff
  simpa [mul_assoc, mul_left_comm, mul_comm] using hdiff

/-- Complete positive-orientation classification at positive decimal
valuation: only the two vertical families occur. -/
theorem positive_positiveExponent_classification
    {h r h' r' a : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r') (ha : 1 ≤ a)
    (heq : qDiff h r h' r' = 9 * (10 : ℤ) ^ a) :
    PositiveFamily .verticalOne h r h' r' a ∨
      PositiveFamily .verticalTen h r h' r' a := by
  have hmult := multiplier_eq_of_positiveExponent
    hh hh10 hh' hh'10 hr hr' ha heq
  subst h'
  have hq : q h r' < q h r := by
    have heq' : (q h r : ℤ) = 9 * (10 : ℤ) ^ a + q h r' := by
      unfold qDiff at heq
      linarith
    have heqNat : q h r = 9 * 10 ^ a + q h r' := by exact_mod_cast heq'
    have hpos : 0 < 9 * 10 ^ a := mul_pos (by norm_num) (pow_pos (by norm_num) _)
    omega
  have hrr' : r' < r := (q_strictMono h hh).lt_iff_lt.mp hq
  let d := r - r'
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hfactor := sameMultiplier_factorization hh hrr' heq
  change 10 ^ r' * (h * (10 ^ d - 1)) = 9 * 10 ^ a at hfactor
  by_cases hten : h = 10
  · subst h
    right
    have hrep0 : 10 ^ d - 1 ≠ 0 := by
      have := Nat.one_lt_pow (Nat.ne_of_gt hd) (by norm_num : 1 < 10)
      omega
    have hprimitive : ¬ 10 ∣ 10 ^ d - 1 := ten_not_dvd_pow_sub_one hd
    have hleft : 10 ^ (r' + 1) * (10 ^ d - 1) = 9 * 10 ^ a := by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hfactor
    have hval := congrArg tenValuation hleft
    rw [tenValuation_pow_mul_of_not_dvd hrep0 hprimitive] at hval
    have hnine : (9 : ℕ) ≠ 0 := by norm_num
    have hninePrimitive : ¬ 10 ∣ (9 : ℕ) := by norm_num
    have hrightVal : tenValuation (9 * 10 ^ a) = a := by
      rw [mul_comm]
      exact tenValuation_pow_mul_of_not_dvd hnine hninePrimitive
    rw [hrightVal] at hval
    have haEq : a = r' + 1 := hval.symm
    subst a
    have hrep : 10 ^ d - 1 = 9 := by
      rw [mul_comm 9 (10 ^ (r' + 1))] at hleft
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hleft
    have hp : 10 ^ d = 10 ^ 1 := by norm_num at hrep ⊢; omega
    have hdEq : d = 1 := Nat.pow_right_injective (by norm_num) hp
    have hrEq : r = r' + 1 := by dsimp [d] at hdEq; omega
    exact ⟨rfl, rfl, hrEq, rfl, hr'⟩

  · left
    have hh9 : h ≤ 9 := by omega
    have hk0 : h * (10 ^ d - 1) ≠ 0 := by
      have hrep : 0 < 10 ^ d - 1 := by
        have := Nat.one_lt_pow (Nat.ne_of_gt hd) (by norm_num : 1 < 10)
        omega
      positivity
    have hkPrimitive := small_mul_repunit_not_dvd_ten hh hh9 hd
    have hval := congrArg tenValuation hfactor
    rw [tenValuation_pow_mul_of_not_dvd hk0 hkPrimitive] at hval
    have hnine : (9 : ℕ) ≠ 0 := by norm_num
    have hninePrimitive : ¬ 10 ∣ (9 : ℕ) := by norm_num
    have hrightVal : tenValuation (9 * 10 ^ a) = a := by
      rw [mul_comm]
      exact tenValuation_pow_mul_of_not_dvd hnine hninePrimitive
    rw [hrightVal] at hval
    have haEq : a = r' := hval.symm
    subst a
    rw [mul_comm 9 (10 ^ r')] at hfactor
    have hk : h * (10 ^ d - 1) = 9 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hfactor
    have hrepLower : 9 ≤ 10 ^ d - 1 := by
      have hp : 10 ^ 1 ≤ 10 ^ d :=
        (Nat.pow_le_pow_iff_right (by norm_num)).2 hd
      norm_num at hp
      omega
    have hmulLower : h * 9 ≤ h * (10 ^ d - 1) :=
      Nat.mul_le_mul_left h hrepLower
    have hEq : h = 1 := by omega
    subst h
    simp only [one_mul] at hk
    have hp : 10 ^ d = 10 ^ 1 := by norm_num at hk ⊢; omega
    have hdEq : d = 1 := Nat.pow_right_injective (by norm_num) hp
    have hrEq : r = r' + 1 := by dsimp [d] at hdEq; omega
    exact ⟨rfl, rfl, hrEq, rfl, hr'⟩

/-- Exhaustive positive-orientation classification, including valuation zero
and every positive valuation. -/
theorem positive_orientation_classification
    {h r h' r' a : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r') :
    qDiff h r h' r' = 9 * (10 : ℤ) ^ a ↔
      ∃ family : NineFamily, PositiveFamily family h r h' r' a := by
  constructor
  · intro heq
    rcases a with _ | a
    · rcases positive_zeroExponent_classification hh hh10 hh' hh'10 hr hr' (by simpa using heq) with
        hs | hc
      · exact ⟨.sameShift, hs⟩
      · exact ⟨.crossFrequency, hc⟩
    · rcases positive_positiveExponent_classification hh hh10 hh' hh'10 hr hr'
          (by omega) heq with hv1 | hv10
      · exact ⟨.verticalOne, hv1⟩
      · exact ⟨.verticalTen, hv10⟩
  · rintro ⟨family, hf⟩
    exact positiveFamily_qDiff hf

/-- Exhaustive negative orientation is exactly reversal of the same four
families. -/
theorem negative_orientation_classification
    {h r h' r' a : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r') :
    qDiff h r h' r' = -(9 * (10 : ℤ) ^ a) ↔
      ∃ family : NineFamily, NegativeFamily family h r h' r' a := by
  constructor
  · intro heq
    have hrev : qDiff h' r' h r = 9 * (10 : ℤ) ^ a := by
      unfold qDiff at heq ⊢
      linarith
    rcases (positive_orientation_classification hh' hh'10 hh hh10 hr' hr).mp hrev with
      ⟨family, hf⟩
    exact ⟨family, hf⟩
  · rintro ⟨family, hf⟩
    exact negativeFamily_qDiff hf

/-- Classification after the orbit shift: every raw monomial contributing to
`9*10^K` has `k <= K`, and its unshifted channels belong to exactly one of the
four families at valuation `K-k`. -/
theorem shifted_positive_orientation_classification
    {h r h' r' k K : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r') :
    qDiff h r h' r' * (10 : ℤ) ^ k = 9 * (10 : ℤ) ^ K ↔
      k ≤ K ∧ ∃ family : NineFamily,
        PositiveFamily family h r h' r' (K - k) := by
  constructor
  · intro heq
    have hpowZ : (0 : ℤ) < 10 ^ k := pow_pos (by norm_num) _
    have htargetZ : (0 : ℤ) < 9 * 10 ^ K := mul_pos (by norm_num) (pow_pos (by norm_num) _)
    have hprod : 0 < qDiff h r h' r' * (10 : ℤ) ^ k := heq.symm ▸ htargetZ
    have hqpos : 0 < qDiff h r h' r' := by
      rcases mul_pos_iff.mp hprod with hp | hn
      · exact hp.1
      · exact (not_lt_of_ge hpowZ.le hn.2).elim
    have hqle : q h' r' ≤ q h r := by
      unfold qDiff at hqpos
      omega
    have hcast : qDiff h r h' r' = (q h r - q h' r' : ℕ) := by
      unfold qDiff
      rw [Nat.cast_sub hqle]
    have heqNat : (q h r - q h' r') * 10 ^ k = 9 * 10 ^ K := by
      rw [hcast] at heq
      exact_mod_cast heq
    have hdvd : 10 ^ k ∣ 9 * 10 ^ K := by
      refine ⟨q h r - q h' r', ?_⟩
      simpa [mul_comm] using heqNat.symm
    have hnine : (9 : ℕ) ≠ 0 := by norm_num
    have hninePrimitive : ¬10 ∣ (9 : ℕ) := by norm_num
    have hval : tenValuation (9 * 10 ^ K) = K := by
      rw [mul_comm]
      exact tenValuation_pow_mul_of_not_dvd hnine hninePrimitive
    have htarget0 : 9 * 10 ^ K ≠ 0 := mul_ne_zero hnine (pow_ne_zero _ (by norm_num))
    have hkK : k ≤ K := by
      have hv := (Nat.pow_dvd_iff_le_padicValNat
        (p := 10) (k := k) (n := 9 * 10 ^ K) (by norm_num) htarget0).mp hdvd
      simpa [tenValuation] using hval ▸ hv
    have hK : k + (K - k) = K := Nat.add_sub_of_le hkK
    have hbaseNat : q h r - q h' r' = 9 * 10 ^ (K - k) := by
      have hpowFactor : 10 ^ K = 10 ^ (K - k) * 10 ^ k := by
        calc
          10 ^ K = 10 ^ ((K - k) + k) := by congr 1; omega
          _ = 10 ^ (K - k) * 10 ^ k := by rw [pow_add]
      have heqMul : (q h r - q h' r') * 10 ^ k =
          (9 * 10 ^ (K - k)) * 10 ^ k := by
        rw [heqNat, hpowFactor]
        ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) k) heqMul
    have hbase : qDiff h r h' r' = 9 * (10 : ℤ) ^ (K - k) := by
      rw [hcast]
      exact_mod_cast hbaseNat
    exact ⟨hkK, (positive_orientation_classification hh hh10 hh' hh'10 hr hr').mp hbase⟩
  · rintro ⟨hkK, family, hf⟩
    have hbase := positiveFamily_qDiff hf
    have hK : k + (K - k) = K := Nat.add_sub_of_le hkK
    have hpowFactor : (10 : ℤ) ^ K = 10 ^ (K - k) * 10 ^ k := by
      calc
        (10 : ℤ) ^ K = 10 ^ ((K - k) + k) := by congr 1; omega
        _ = 10 ^ (K - k) * 10 ^ k := by rw [pow_add]
    calc
      qDiff h r h' r' * (10 : ℤ) ^ k =
          (9 * (10 : ℤ) ^ (K - k)) * 10 ^ k := by rw [hbase]
      _ = 9 * (10 : ℤ) ^ K := by rw [hpowFactor]; ring

/-- Endpoint-truncated sum of the literal adjacent triangular products. -/
def prefixWeight (H x : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 (min (H - 2) x), (H - s - 1) * (H - s)

/-- The fully saturated triangular prefix. -/
def fullWeight (H : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico 2 H, (j - 1) * j

/-- Once the truncation parameter reaches `H-2`, the prefix is full. -/
theorem prefixWeight_eq_fullWeight
    {H x : ℕ} (hH : 2 ≤ H) (hx : H - 2 ≤ x) :
    prefixWeight H x = fullWeight H := by
  have hmin : min (H - 2) x = H - 2 := min_eq_left hx
  rw [prefixWeight, hmin, fullWeight]
  classical
  apply Finset.sum_bij (fun s _ => H - s)
  · intro s hs
    rw [Finset.mem_Ico]
    have hs' := Finset.mem_Icc.mp hs
    omega
  · intro s hs s' hs' heq
    have hsBounds := Finset.mem_Icc.mp hs
    have hsBounds' := Finset.mem_Icc.mp hs'
    omega
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    refine ⟨H - j, Finset.mem_Icc.mpr ?_, ?_⟩
    · omega
    · omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    congr 1 <;> omega

/-- Exact cubic identity for the complete adjacent triangular mass. -/
theorem three_mul_fullWeight (H : ℕ) :
    3 * fullWeight H = H * (H - 1) * (H - 2) := by
  rcases H with _ | _ | H
  · simp [fullWeight]
  · simp [fullWeight]
  induction H with
  | zero => simp [fullWeight]
  | succ H ih =>
      have htop : 2 ≤ H + 2 := by omega
      rw [fullWeight, Finset.sum_Ico_succ_top htop]
      change 3 * (fullWeight (H + 2) + (H + 2 - 1) * (H + 2)) =
        (H + 3) * (H + 3 - 1) * (H + 3 - 2)
      have ih' : 3 * fullWeight (H + 2) = (H + 2) * (H + 1) * H := by
        simpa [Nat.add_assoc] using ih
      have hs1 : H + 2 - 1 = H + 1 := by omega
      have hs2 : H + 3 - 1 = H + 2 := by omega
      have hs3 : H + 3 - 2 = H + 1 := by omega
      rw [hs1, hs2, hs3, mul_add, ih']
      ring

/-- The exact endpoint-truncated coefficient predicted by the exhaustive
four-family classification.  All four terminal cutoffs are explicit. -/
def endpointCoefficient (t K : ℕ) : ℕ :=
  (if K ≤ N t - 2 then 9 * (H t - 1) ^ 2 else 0) +
  (if K ≤ N t - 3 then prefixWeight (H t) (N t - K - 2) else 0) +
  (if K ≤ N t - 2 then prefixWeight (H t) K else 0) +
  (if 2 ≤ K ∧ K ≤ N t - 1 then prefixWeight (H t) (K - 1) else 0)

/-- Formula (including all endpoint indicators) for every nonnegative
multiplier-nine exponent. -/
theorem endpointCoefficient_formula (t K : ℕ) :
    endpointCoefficient t K =
      (if K ≤ N t - 2 then 9 * (H t - 1) ^ 2 else 0) +
      (if K ≤ N t - 3 then prefixWeight (H t) (N t - K - 2) else 0) +
      (if K ≤ N t - 2 then prefixWeight (H t) K else 0) +
      (if 2 ≤ K ∧ K ≤ N t - 1 then prefixWeight (H t) (K - 1) else 0) := by
  rfl

/-- Same-shift part of the positive multiplier-nine Laurent sector. -/
def sameShiftSector (t : ℕ) : ℤ →₀ ℕ :=
  ∑ j ∈ Finset.Icc 1 9,
    ∑ k ∈ Finset.range (N t - 1),
      Finsupp.single (9 * (10 : ℤ) ^ k) ((H t - 1) ^ 2)

/-- Adjacent cross-frequency part of the positive sector. -/
def crossFrequencySector (t : ℕ) : ℤ →₀ ℕ :=
  ∑ s ∈ Finset.Icc 1 (H t - 2),
    ∑ k ∈ Finset.range (N t - s - 1),
      Finsupp.single (9 * (10 : ℤ) ^ k)
        ((H t - s - 1) * (H t - s))

/-- Vertical `h=1` part of the positive sector. -/
def verticalOneSector (t : ℕ) : ℤ →₀ ℕ :=
  ∑ s ∈ Finset.Icc 1 (H t - 2),
    ∑ k ∈ Finset.range (N t - s - 1),
      Finsupp.single (9 * (10 : ℤ) ^ (s + k))
        ((H t - s - 1) * (H t - s))

/-- Vertical `h=10` part, including its exceptional terminal exponent
`K=N_t-1`. -/
def verticalTenSector (t : ℕ) : ℤ →₀ ℕ :=
  ∑ s ∈ Finset.Icc 1 (H t - 2),
    ∑ k ∈ Finset.range (N t - s - 1),
      Finsupp.single (9 * (10 : ℤ) ^ (s + 1 + k))
        ((H t - s - 1) * (H t - s))

/-- The positive multiplier-nine sector reconstructed from all four
classified families. -/
def positiveNineSector (t : ℕ) : ℤ →₀ ℕ :=
  sameShiftSector t + crossFrequencySector t + verticalOneSector t +
    verticalTenSector t

theorem nine_mul_ten_pow_injective {k K : ℕ} :
    (9 : ℤ) * 10 ^ k = 9 * 10 ^ K ↔ k = K := by
  constructor
  · intro h
    have hp : (10 : ℤ) ^ k = 10 ^ K := by nlinarith
    have hpNat : 10 ^ k = 10 ^ K := by exact_mod_cast hp
    exact Nat.pow_right_injective (by norm_num) hpNat
  · rintro rfl
    rfl

theorem sameShiftSector_apply (t K : ℕ) :
    sameShiftSector t (9 * (10 : ℤ) ^ K) =
      if K ≤ N t - 2 then 9 * (H t - 1) ^ 2 else 0 := by
  have hN5 := five_le_N t
  rw [sameShiftSector]
  simp only [Finset.sum_apply', Finsupp.single_apply, nine_mul_ten_pow_injective]
  by_cases hK : K < N t - 1
  · have hK' : K ≤ N t - 2 := by omega
    simp [Finset.sum_ite_eq', hK, hK']
  · have hK' : ¬K ≤ N t - 2 := by omega
    simp [Finset.sum_ite_eq', hK, hK']

theorem crossFrequencySector_apply (t K : ℕ) :
    crossFrequencySector t (9 * (10 : ℤ) ^ K) =
      if K ≤ N t - 3 then prefixWeight (H t) (N t - K - 2) else 0 := by
  have hN5 := five_le_N t
  rw [crossFrequencySector]
  simp only [Finset.sum_apply', Finsupp.single_apply, nine_mul_ten_pow_injective,
    Finset.sum_ite_eq', Finset.mem_range]
  by_cases hK : K ≤ N t - 3
  · rw [if_pos hK, prefixWeight]
    let S := Finset.Icc 1 (H t - 2)
    let T := Finset.Icc 1 (min (H t - 2) (N t - K - 2))
    have hcond (s : ℕ) : K < N t - s - 1 ↔ s ≤ N t - K - 2 := by omega
    simp_rw [hcond]
    have hset : S.filter (fun s => s ≤ N t - K - 2) = T := by
      ext s
      simp [S, T]
      omega
    change (∑ s ∈ S, if s ≤ N t - K - 2 then
      (H t - s - 1) * (H t - s) else 0) = ∑ s ∈ T,
        (H t - s - 1) * (H t - s)
    rw [← Finset.sum_filter, hset]
  · rw [if_neg hK]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [Finset.mem_Icc] at hs
    have hnot : ¬K < N t - s - 1 := by omega
    simp [hnot]

theorem sum_range_add_eq (s L K w : ℕ) :
    (∑ k ∈ Finset.range L, if s + k = K then w else 0) =
      if s ≤ K ∧ K - s < L then w else 0 := by
  by_cases h : s ≤ K ∧ K - s < L
  · rw [if_pos h, Finset.sum_eq_single (K - s)]
    · simp [h]
    · intro b hb hbne
      simp only [Finset.mem_range] at hb
      have hneq : ¬s + b = K := by
        intro heq
        apply hbne
        omega
      simp [hneq]
    · simp [h]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    simp only [Finset.mem_range] at hb
    have hneq : ¬s + b = K := by
      intro heq
      apply h
      constructor <;> omega
    simp [hneq]

theorem verticalOneSector_apply (t K : ℕ) :
    verticalOneSector t (9 * (10 : ℤ) ^ K) =
      if K ≤ N t - 2 then prefixWeight (H t) K else 0 := by
  have hN5 := five_le_N t
  rw [verticalOneSector]
  simp only [Finset.sum_apply', Finsupp.single_apply, nine_mul_ten_pow_injective]
  simp_rw [sum_range_add_eq]
  by_cases hK : K ≤ N t - 2
  · rw [if_pos hK, prefixWeight]
    let S := Finset.Icc 1 (H t - 2)
    let T := Finset.Icc 1 (min (H t - 2) K)
    have hcond (s : ℕ) (hs : s ∈ S) :
        (s ≤ K ∧ K - s < N t - s - 1) ↔ s ≤ K := by
      have hs' := Finset.mem_Icc.mp hs
      constructor
      · exact And.left
      · intro hsK
        exact ⟨hsK, by omega⟩
    change (∑ s ∈ S, if s ≤ K ∧ K - s < N t - s - 1 then
      (H t - s - 1) * (H t - s) else 0) =
        ∑ s ∈ T, (H t - s - 1) * (H t - s)
    have hrewrite : (∑ s ∈ S, if s ≤ K ∧ K - s < N t - s - 1 then
        (H t - s - 1) * (H t - s) else 0) =
        ∑ s ∈ S, if s ≤ K then (H t - s - 1) * (H t - s) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [hcond s hs]
    rw [hrewrite]
    have hset : S.filter (fun s => s ≤ K) = T := by
      ext s
      simp [S, T]
      omega
    rw [← Finset.sum_filter, hset]
  · rw [if_neg hK]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [Finset.mem_Icc] at hs
    have hnot : ¬(s ≤ K ∧ K - s < N t - s - 1) := by
      intro h
      omega
    simp [hnot]

theorem verticalTenSector_apply (t K : ℕ) :
    verticalTenSector t (9 * (10 : ℤ) ^ K) =
      if 2 ≤ K ∧ K ≤ N t - 1 then prefixWeight (H t) (K - 1) else 0 := by
  have hN5 := five_le_N t
  rw [verticalTenSector]
  simp only [Finset.sum_apply', Finsupp.single_apply, nine_mul_ten_pow_injective]
  simp_rw [sum_range_add_eq]
  by_cases hK : 2 ≤ K ∧ K ≤ N t - 1
  · rw [if_pos hK, prefixWeight]
    let S := Finset.Icc 1 (H t - 2)
    let T := Finset.Icc 1 (min (H t - 2) (K - 1))
    have hcond (s : ℕ) (hs : s ∈ S) :
        (s + 1 ≤ K ∧ K - (s + 1) < N t - s - 1) ↔ s ≤ K - 1 := by
      have hs' := Finset.mem_Icc.mp hs
      constructor
      · intro h
        omega
      · intro hsK
        constructor <;> omega
    change (∑ s ∈ S, if s + 1 ≤ K ∧ K - (s + 1) < N t - s - 1 then
      (H t - s - 1) * (H t - s) else 0) =
        ∑ s ∈ T, (H t - s - 1) * (H t - s)
    have hrewrite : (∑ s ∈ S,
        if s + 1 ≤ K ∧ K - (s + 1) < N t - s - 1 then
          (H t - s - 1) * (H t - s) else 0) =
        ∑ s ∈ S, if s ≤ K - 1 then (H t - s - 1) * (H t - s) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [hcond s hs]
    rw [hrewrite]
    have hset : S.filter (fun s => s ≤ K - 1) = T := by
      ext s
      simp [S, T]
      omega
    rw [← Finset.sum_filter, hset]
  · rw [if_neg hK]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [Finset.mem_Icc] at hs
    have hnot : ¬(s + 1 ≤ K ∧ K - (s + 1) < N t - s - 1) := by
      intro h
      apply hK
      constructor <;> omega
    have hnot' : ¬(s < K ∧ K - (s + 1) < N t - s - 1) := by
      omega
    simp [hnot']

/-- Exact endpoint formula for the independently reconstructed positive
four-family multiplier-nine sector. -/
theorem positiveNineSector_apply (t K : ℕ) :
    positiveNineSector t (9 * (10 : ℤ) ^ K) = endpointCoefficient t K := by
  rw [positiveNineSector, Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    sameShiftSector_apply, crossFrequencySector_apply, verticalOneSector_apply,
    verticalTenSector_apply]
  rfl

/-- Negation embedding used for ordered-channel reversal. -/
def negIntEmbedding : ℤ ↪ ℤ := ⟨fun z => -z, neg_injective⟩

/-- The reversed orientation has the same coefficients at negated Laurent
exponents. -/
def negativeNineSector (t : ℕ) : ℤ →₀ ℕ :=
  Finsupp.embDomain negIntEmbedding (positiveNineSector t)

theorem negativeNineSector_apply (t K : ℕ) :
    negativeNineSector t (-(9 * (10 : ℤ) ^ K)) = endpointCoefficient t K := by
  change Finsupp.embDomain negIntEmbedding (positiveNineSector t)
      (negIntEmbedding (9 * (10 : ℤ) ^ K)) = endpointCoefficient t K
  rw [Finsupp.embDomain_apply_self, positiveNineSector_apply]

/-- Both ordered orientations of the classified sector. -/
def twoSidedNineSector (t : ℕ) : ℤ →₀ ℕ :=
  positiveNineSector t + negativeNineSector t

theorem twoSidedNineSector_coefficients (t K : ℕ) :
    positiveNineSector t (9 * (10 : ℤ) ^ K) = endpointCoefficient t K ∧
    negativeNineSector t (-(9 * (10 : ℤ) ^ K)) = endpointCoefficient t K := by
  exact ⟨positiveNineSector_apply t K, negativeNineSector_apply t K⟩

/-- Literal raw pooled-domain tuple classification.  This theorem joins the
T69 frequency and shift domains, triangular expansion cutoff, and exhaustive
family theorem before any coefficient summation. -/
theorem pooled_multiplierNine_tuple_iff
    {t h r h' r' k K : ℕ} :
    (h, r) ∈ channelDomain t ∧ (h', r') ∈ channelDomain t ∧
        k < N t - max r r' ∧
        qDiff h r h' r' * (10 : ℤ) ^ k = 9 * (10 : ℤ) ^ K ↔
      (1 ≤ h ∧ h ≤ 10 ∧ 1 ≤ r ∧ r < H t) ∧
      (1 ≤ h' ∧ h' ≤ 10 ∧ 1 ≤ r' ∧ r' < H t) ∧
      k < N t - max r r' ∧ k ≤ K ∧
      ∃ family : NineFamily, PositiveFamily family h r h' r' (K - k) := by
  rw [mem_channelDomain_iff, mem_channelDomain_iff]
  constructor
  · rintro ⟨hd, hd', hk, heq⟩
    have hc := (shifted_positive_orientation_classification
      hd.1 hd.2.1 hd'.1 hd'.2.1 hd.2.2.1 hd'.2.2.1).mp heq
    exact ⟨hd, hd', hk, hc⟩
  · rintro ⟨hd, hd', hk, hK, family, hf⟩
    refine ⟨hd, hd', hk, ?_⟩
    exact (shifted_positive_orientation_classification
      hd.1 hd.2.1 hd'.1 hd'.2.1 hd.2.2.1 hd'.2.2.1).mpr
        ⟨hK, family, hf⟩

theorem exists_positiveFamily_iff (h r h' r' a : ℕ) :
    (∃ family : NineFamily, PositiveFamily family h r h' r' a) ↔
      PositiveFamily .sameShift h r h' r' a ∨
      PositiveFamily .crossFrequency h r h' r' a ∨
      PositiveFamily .verticalOne h r h' r' a ∨
      PositiveFamily .verticalTen h r h' r' a := by
  constructor
  · rintro ⟨family, hf⟩
    cases family
    · exact Or.inl hf
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr (Or.inl hf))
    · exact Or.inr (Or.inr (Or.inr hf))
  · intro h
    rcases h with hs | hc | hv1 | hv10
    · exact ⟨.sameShift, hs⟩
    · exact ⟨.crossFrequency, hc⟩
    · exact ⟨.verticalOne, hv1⟩
    · exact ⟨.verticalTen, hv10⟩

set_option maxHeartbeats 2000000

theorem ite_or_four_of_pairwise
    (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S]
    (w : ℕ) (hPQ : ¬(P ∧ Q)) (hPR : ¬(P ∧ R)) (hPS : ¬(P ∧ S))
    (hQR : ¬(Q ∧ R)) (hQS : ¬(Q ∧ S)) (hRS : ¬(R ∧ S)) :
    (if P ∨ Q ∨ R ∨ S then w else 0) =
      (if P then w else 0) + (if Q then w else 0) +
        (if R then w else 0) + (if S then w else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> by_cases hS : S <;>
    simp_all

theorem raw_multiplierNine_indicator_decompose
    {h r h' r' k K w : ℕ}
    (hh : 1 ≤ h) (hh10 : h ≤ 10) (hh' : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hr' : 1 ≤ r') :
    (if qDiff h r h' r' * (10 : ℤ) ^ k = 9 * (10 : ℤ) ^ K then w else 0) =
      (if k ≤ K ∧ PositiveFamily .sameShift h r h' r' (K - k) then w else 0) +
      (if k ≤ K ∧ PositiveFamily .crossFrequency h r h' r' (K - k) then w else 0) +
      (if k ≤ K ∧ PositiveFamily .verticalOne h r h' r' (K - k) then w else 0) +
      (if k ≤ K ∧ PositiveFamily .verticalTen h r h' r' (K - k) then w else 0) := by
  classical
  simp only [shifted_positive_orientation_classification hh hh10 hh' hh'10 hr hr',
    exists_positiveFamily_iff]
  by_cases hk : k ≤ K
  · simp only [hk, true_and]
    apply ite_or_four_of_pairwise <;> simp [PositiveFamily] <;> omega
  · simp [hk]

theorem verticalTen_raw_family_sum (t K : ℕ) :
    (∑ h' ∈ Finset.Icc 1 10,
      ∑ r' ∈ Finset.Ico 1 (H t),
        ∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r r'),
              if k ≤ K ∧ PositiveFamily .verticalTen h r h' r' (K - k) then
                (H t - r) * (H t - r') else 0) =
      ∑ s ∈ Finset.Icc 1 (H t - 2),
        ∑ k ∈ Finset.range (N t - s - 1),
          if s + 1 + k = K then (H t - s - 1) * (H t - s) else 0 := by
  classical
  rw [Finset.sum_eq_single 10]
  · simp only [PositiveFamily, true_and]
    let S := Finset.Ico 1 (H t)
    let T := Finset.Icc 1 (H t - 2)
    let f := fun s => ∑ k ∈ Finset.range (N t - s - 1),
      if s + 1 + k = K then (H t - s - 1) * (H t - s) else 0
    have hinner (s : ℕ) (hs : s ∈ S) :
        (∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r s),
              if k ≤ K ∧ h = 10 ∧ r = s + 1 ∧ K - k = s + 1 ∧ 1 ≤ s then
                (H t - r) * (H t - s) else 0) =
          if s ≤ H t - 2 then f s else 0 := by
      have hs' := Finset.mem_Ico.mp hs
      by_cases hs2 : s ≤ H t - 2
      · rw [if_pos hs2, Finset.sum_eq_single 10]
        · rw [Finset.sum_eq_single (s + 1)]
          · dsimp [f]
            have hmax : max (s + 1) s = s + 1 := max_eq_left (by omega)
            rw [hmax]
            have hweight : H t - (s + 1) = H t - s - 1 := by omega
            rw [hweight]
            apply Finset.sum_congr rfl
            intro k hk
            split_ifs <;> omega
          · intro b hb hbne
            simp [hbne]
          · simp
            omega
        · intro b hb hbne
          simp [hbne]
        · norm_num
      · rw [if_neg hs2]
        apply Finset.sum_eq_zero
        intro h hh
        apply Finset.sum_eq_zero
        intro r hr
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_Ico] at hr
        have hne : ¬(k ≤ K ∧ h = 10 ∧ r = s + 1 ∧ K - k = s + 1 ∧ 1 ≤ s) := by
          intro h
          omega
        simp [hne]
    change (∑ s ∈ S, _) = ∑ s ∈ T, f s
    calc
      (∑ s ∈ S,
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r s),
                if k ≤ K ∧ h = 10 ∧ r = s + 1 ∧ K - k = s + 1 ∧ 1 ≤ s then
                  (H t - r) * (H t - s) else 0) =
          ∑ s ∈ S, if s ≤ H t - 2 then f s else 0 := by
            apply Finset.sum_congr rfl
            exact hinner
      _ = ∑ s ∈ T, f s := by
        have hset : S.filter (fun s => s ≤ H t - 2) = T := by
          ext s
          simp [S, T]
          omega
        rw [← Finset.sum_filter, hset]
  · intro b hb hbne
    simp [PositiveFamily, hbne]
  · norm_num

theorem sameShift_raw_family_sum (t K : ℕ) :
    (∑ h' ∈ Finset.Icc 1 10,
      ∑ r' ∈ Finset.Ico 1 (H t),
        ∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r r'),
              if k ≤ K ∧ PositiveFamily .sameShift h r h' r' (K - k) then
                (H t - r) * (H t - r') else 0) =
      ∑ j ∈ Finset.Icc 1 9,
        ∑ k ∈ Finset.range (N t - 1),
          if k = K then (H t - 1) ^ 2 else 0 := by
  classical
  have hH3 := three_le_H t
  let S := Finset.Icc 1 10
  let T := Finset.Icc 1 9
  let f := fun _j : ℕ => ∑ k ∈ Finset.range (N t - 1),
    if k = K then (H t - 1) ^ 2 else 0
  have hinner (j : ℕ) (hj : j ∈ S) :
      (∑ r' ∈ Finset.Ico 1 (H t),
        ∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r r'),
              if k ≤ K ∧ PositiveFamily .sameShift h r j r' (K - k) then
                (H t - r) * (H t - r') else 0) =
        if j ≤ 9 then f j else 0 := by
    have hj' := Finset.mem_Icc.mp hj
    by_cases hj9 : j ≤ 9
    · rw [if_pos hj9, Finset.sum_eq_single 1]
      · rw [Finset.sum_eq_single (j + 1)]
        · rw [Finset.sum_eq_single 1]
          · dsimp [f]
            simp only [PositiveFamily]
            simp only [pow_two]
            apply Finset.sum_congr rfl
            intro k hk
            have hmax : max 1 1 = 1 := rfl
            split_ifs <;> simp_all <;> omega
          · intro b hb hbne
            simp [PositiveFamily, hbne]
          · simp
            omega
        · intro b hb hbne
          simp [PositiveFamily, hbne]
        · simp
          omega
      · intro b hb hbne
        simp [PositiveFamily, hbne]
      · simp
        omega
    · rw [if_neg hj9]
      apply Finset.sum_eq_zero
      intro r' hr'
      apply Finset.sum_eq_zero
      intro h hh
      apply Finset.sum_eq_zero
      intro r hr
      apply Finset.sum_eq_zero
      intro k hk
      simp [PositiveFamily, hj9]
  change (∑ j ∈ S, _) = ∑ j ∈ T, f j
  calc
    (∑ j ∈ S,
      ∑ r' ∈ Finset.Ico 1 (H t),
        ∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r r'),
              if k ≤ K ∧ PositiveFamily .sameShift h r j r' (K - k) then
                (H t - r) * (H t - r') else 0) =
        ∑ j ∈ S, if j ≤ 9 then f j else 0 := by
          apply Finset.sum_congr rfl
          exact hinner
    _ = ∑ j ∈ T, f j := by
      have hset : S.filter (fun j => j ≤ 9) = T := by
        ext j
        simp [S, T]
        omega
      rw [← Finset.sum_filter, hset]

theorem crossFrequency_raw_family_sum (t K : ℕ) :
    (∑ h' ∈ Finset.Icc 1 10,
      ∑ r' ∈ Finset.Ico 1 (H t),
        ∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r r'),
              if k ≤ K ∧ PositiveFamily .crossFrequency h r h' r' (K - k) then
                (H t - r) * (H t - r') else 0) =
      ∑ s ∈ Finset.Icc 1 (H t - 2),
        ∑ k ∈ Finset.range (N t - s - 1),
          if k = K then (H t - s - 1) * (H t - s) else 0 := by
  classical
  rw [Finset.sum_eq_single 10]
  · simp only [PositiveFamily, true_and]
    let S := Finset.Ico 1 (H t)
    let T := Finset.Icc 1 (H t - 2)
    let f := fun s => ∑ k ∈ Finset.range (N t - s - 1),
      if k = K then (H t - s - 1) * (H t - s) else 0
    have hinner (s : ℕ) (hs : s ∈ S) :
        (∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r s),
              if k ≤ K ∧ h = 1 ∧ r = s + 1 ∧ K - k = 0 ∧ 1 ≤ s then
                (H t - r) * (H t - s) else 0) =
          if s ≤ H t - 2 then f s else 0 := by
      have hs' := Finset.mem_Ico.mp hs
      by_cases hs2 : s ≤ H t - 2
      · rw [if_pos hs2, Finset.sum_eq_single 1]
        · rw [Finset.sum_eq_single (s + 1)]
          · dsimp [f]
            have hmax : max (s + 1) s = s + 1 := max_eq_left (by omega)
            rw [hmax]
            have hweight : H t - (s + 1) = H t - s - 1 := by omega
            rw [hweight]
            apply Finset.sum_congr rfl
            intro k hk
            split_ifs <;> omega
          · intro b hb hbne
            simp [hbne]
          · simp
            omega
        · intro b hb hbne
          simp [hbne]
        · norm_num
      · rw [if_neg hs2]
        apply Finset.sum_eq_zero
        intro h hh
        apply Finset.sum_eq_zero
        intro r hr
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_Ico] at hr
        have hne : ¬(k ≤ K ∧ h = 1 ∧ r = s + 1 ∧ K - k = 0 ∧ 1 ≤ s) := by
          intro h
          omega
        simp [hne]
    change (∑ s ∈ S, _) = ∑ s ∈ T, f s
    calc
      (∑ s ∈ S,
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r s),
                if k ≤ K ∧ h = 1 ∧ r = s + 1 ∧ K - k = 0 ∧ 1 ≤ s then
                  (H t - r) * (H t - s) else 0) =
          ∑ s ∈ S, if s ≤ H t - 2 then f s else 0 := by
            apply Finset.sum_congr rfl
            exact hinner
      _ = ∑ s ∈ T, f s := by
        have hset : S.filter (fun s => s ≤ H t - 2) = T := by
          ext s
          simp [S, T]
          omega
        rw [← Finset.sum_filter, hset]
  · intro b hb hbne
    simp [PositiveFamily, hbne]
  · norm_num

theorem verticalOne_raw_family_sum (t K : ℕ) :
    (∑ h' ∈ Finset.Icc 1 10,
      ∑ r' ∈ Finset.Ico 1 (H t),
        ∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r r'),
              if k ≤ K ∧ PositiveFamily .verticalOne h r h' r' (K - k) then
                (H t - r) * (H t - r') else 0) =
      ∑ s ∈ Finset.Icc 1 (H t - 2),
        ∑ k ∈ Finset.range (N t - s - 1),
          if s + k = K then (H t - s - 1) * (H t - s) else 0 := by
  classical
  rw [Finset.sum_eq_single 1]
  · simp only [PositiveFamily, true_and]
    let S := Finset.Ico 1 (H t)
    let T := Finset.Icc 1 (H t - 2)
    let f := fun s => ∑ k ∈ Finset.range (N t - s - 1),
      if s + k = K then (H t - s - 1) * (H t - s) else 0
    have hinner (s : ℕ) (hs : s ∈ S) :
        (∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r s),
              if k ≤ K ∧ h = 1 ∧ r = s + 1 ∧ K - k = s ∧ 1 ≤ s then
                (H t - r) * (H t - s) else 0) =
          if s ≤ H t - 2 then f s else 0 := by
      have hs' := Finset.mem_Ico.mp hs
      by_cases hs2 : s ≤ H t - 2
      · rw [if_pos hs2, Finset.sum_eq_single 1]
        · rw [Finset.sum_eq_single (s + 1)]
          · dsimp [f]
            have hmax : max (s + 1) s = s + 1 := max_eq_left (by omega)
            rw [hmax]
            have hweight : H t - (s + 1) = H t - s - 1 := by omega
            rw [hweight]
            apply Finset.sum_congr rfl
            intro k hk
            split_ifs <;> omega
          · intro b hb hbne
            simp [hbne]
          · simp
            omega
        · intro b hb hbne
          simp [hbne]
        · norm_num
      · rw [if_neg hs2]
        apply Finset.sum_eq_zero
        intro h hh
        apply Finset.sum_eq_zero
        intro r hr
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_Ico] at hr
        have hne : ¬(k ≤ K ∧ h = 1 ∧ r = s + 1 ∧ K - k = s ∧ 1 ≤ s) := by
          intro h
          omega
        simp [hne]
    change (∑ s ∈ S, _) = ∑ s ∈ T, f s
    calc
      (∑ s ∈ S,
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r s),
                if k ≤ K ∧ h = 1 ∧ r = s + 1 ∧ K - k = s ∧ 1 ≤ s then
                  (H t - r) * (H t - s) else 0) =
          ∑ s ∈ S, if s ≤ H t - 2 then f s else 0 := by
            apply Finset.sum_congr rfl
            exact hinner
      _ = ∑ s ∈ T, f s := by
        have hset : S.filter (fun s => s ≤ H t - 2) = T := by
          ext s
          simp [S, T]
          omega
        rw [← Finset.sum_filter, hset]
  · intro b hb hbne
    simp [PositiveFamily, hbne]
  · norm_num

/-- The raw pooled Laurent coefficient at a positive multiplier-nine
character equals the independently reconstructed four-family coefficient. -/
theorem pooledLaurent_positive_multiplierNine (t K : ℕ) :
    pooledLaurent t (9 * (10 : ℤ) ^ K) = endpointCoefficient t K := by
  classical
  rw [pooledLaurent_apply]
  apply Eq.trans ?_ (positiveNineSector_apply t K)
  rw [positiveNineSector, sameShiftSector, crossFrequencySector,
    verticalOneSector, verticalTenSector]
  simp only [Finsupp.add_apply, Finset.sum_apply', Finsupp.single_apply,
    nine_mul_ten_pow_injective]
  have hsplit :
      (∑ h' ∈ Finset.Icc 1 10,
        ∑ r' ∈ Finset.Ico 1 (H t),
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r r'),
                if qDiff h r h' r' * (10 : ℤ) ^ k = 9 * (10 : ℤ) ^ K then
                  (H t - r) * (H t - r') else 0) =
      ∑ h' ∈ Finset.Icc 1 10,
        ∑ r' ∈ Finset.Ico 1 (H t),
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r r'),
                ((if k ≤ K ∧ PositiveFamily .sameShift h r h' r' (K - k) then
                    (H t - r) * (H t - r') else 0) +
                (if k ≤ K ∧ PositiveFamily .crossFrequency h r h' r' (K - k) then
                    (H t - r) * (H t - r') else 0) +
                (if k ≤ K ∧ PositiveFamily .verticalOne h r h' r' (K - k) then
                    (H t - r) * (H t - r') else 0) +
                (if k ≤ K ∧ PositiveFamily .verticalTen h r h' r' (K - k) then
                    (H t - r) * (H t - r') else 0)) := by
    apply Finset.sum_congr rfl
    intro h' hh'
    apply Finset.sum_congr rfl
    intro r' hr'
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hh hh'
    simp only [Finset.mem_Ico] at hr hr'
    exact raw_multiplierNine_indicator_decompose
      hh.1 hh.2 hh'.1 hh'.2 hr.1 hr'.1
  rw [hsplit]
  simp only [Finset.sum_add_distrib]
  rw [sameShift_raw_family_sum, crossFrequency_raw_family_sum,
    verticalOne_raw_family_sum, verticalTen_raw_family_sum]

theorem qDiff_reverse (h r h' r' : ℕ) :
    qDiff h' r' h r = -qDiff h r h' r' := by
  unfold qDiff
  ring

/-- Ordered-channel reversal proves equality of the positive and negative raw
pooled Laurent coefficients. -/
theorem pooledLaurent_neg_apply (t : ℕ) (z : ℤ) :
    pooledLaurent t (-z) = pooledLaurent t z := by
  rw [pooledLaurent_apply, pooledLaurent_apply]
  calc
    (∑ h' ∈ Finset.Icc 1 10,
      ∑ r' ∈ Finset.Ico 1 (H t),
        ∑ h ∈ Finset.Icc 1 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ∑ k ∈ Finset.range (N t - max r r'),
              if qDiff h r h' r' * (10 : ℤ) ^ k = -z then
                (H t - r) * (H t - r') else 0) =
      ∑ h' ∈ Finset.Icc 1 10,
        ∑ r' ∈ Finset.Ico 1 (H t),
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r r'),
                if qDiff h' r' h r * (10 : ℤ) ^ k = z then
                  (H t - r) * (H t - r') else 0 := by
        apply Finset.sum_congr rfl
        intro h' hh'
        apply Finset.sum_congr rfl
        intro r' hr'
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro k hk
        rw [qDiff_reverse]
        congr 1
        apply propext
        constructor <;> intro hz <;> nlinarith
    _ = ∑ h' ∈ Finset.Icc 1 10,
        ∑ r' ∈ Finset.Ico 1 (H t),
          ∑ h ∈ Finset.Icc 1 10,
            ∑ r ∈ Finset.Ico 1 (H t),
              ∑ k ∈ Finset.range (N t - max r r'),
                if qDiff h r h' r' * (10 : ℤ) ^ k = z then
                  (H t - r) * (H t - r') else 0 := by
      let D := Finset.Icc 1 10 ×ˢ Finset.Ico 1 (H t)
      let F := fun x y : ℕ × ℕ =>
        ∑ k ∈ Finset.range (N t - max y.2 x.2),
          if qDiff x.1 x.2 y.1 y.2 * (10 : ℤ) ^ k = z then
            (H t - y.2) * (H t - x.2) else 0
      have hcomm : (∑ x ∈ D, ∑ y ∈ D, F x y) =
          ∑ y ∈ D, ∑ x ∈ D, F x y := Finset.sum_comm
      simpa [D, F, Finset.sum_product, max_comm, mul_comm] using hcomm

theorem pooledLaurent_negative_multiplierNine (t K : ℕ) :
    pooledLaurent t (-(9 * (10 : ℤ) ^ K)) = endpointCoefficient t K := by
  rw [pooledLaurent_neg_apply, pooledLaurent_positive_multiplierNine]

/-- Above the last `verticalTen` endpoint every classified multiplier-nine
coefficient vanishes. -/
theorem endpointCoefficient_eq_zero_of_N_le
    (t K : ℕ) (hK : N t ≤ K) : endpointCoefficient t K = 0 := by
  have hN5 := five_le_N t
  have h2 : ¬K ≤ N t - 2 := by omega
  have h3 : ¬K ≤ N t - 3 := by omega
  have h1 : ¬K ≤ N t - 1 := by omega
  simp [endpointCoefficient, h2, h3, h1]

theorem prefixWeight_zero (H : ℕ) : prefixWeight H 0 = 0 := by
  simp [prefixWeight]

theorem prefixWeight_one {H : ℕ} (hH : 3 ≤ H) :
    prefixWeight H 1 = (H - 2) * (H - 1) := by
  have hmin : min (H - 2) 1 = 1 := min_eq_right (by omega)
  simp [prefixWeight, hmin]
  congr 1 <;> omega

/-- Explicit low and terminal truncations, including the exceptional final
`verticalTen` coefficient. -/
theorem endpointCoefficient_boundary_values (t : ℕ) :
    endpointCoefficient t 0 = 9 * (H t - 1) ^ 2 + fullWeight (H t) ∧
    endpointCoefficient t 1 =
      9 * (H t - 1) ^ 2 + fullWeight (H t) + (H t - 2) * (H t - 1) ∧
    endpointCoefficient t (N t - 2) =
      9 * (H t - 1) ^ 2 + 2 * fullWeight (H t) ∧
    endpointCoefficient t (N t - 1) = fullWeight (H t) := by
  have hH3 := three_le_H t
  have hN5 := five_le_N t
  have hHN := H_le_N t
  have hHltN : H t < N t := by
    have hceil := H_lt_sqrt_N_add_one t
    have hN0 : (0 : ℝ) ≤ N t := by positivity
    have hs2 : (Real.sqrt (N t : ℝ)) ^ 2 = (N t : ℝ) := Real.sq_sqrt hN0
    have hreal : Real.sqrt (N t : ℝ) + 1 < N t := by
      have hs0 := Real.sqrt_nonneg (N t : ℝ)
      have hN5' : (5 : ℝ) ≤ N t := by exact_mod_cast hN5
      nlinarith
    exact_mod_cast (lt_trans hceil hreal)
  have hfullN2 : H t - 2 ≤ N t - 2 := by omega
  have hfullN3 : H t - 2 ≤ N t - 3 := by omega
  constructor
  · rw [endpointCoefficient]
    simp only [if_pos (by omega : 0 ≤ N t - 2), if_pos (by omega : 0 ≤ N t - 3),
      if_neg (by omega : ¬(2 ≤ 0 ∧ 0 ≤ N t - 1)), prefixWeight_zero, add_zero]
    rw [prefixWeight_eq_fullWeight (by omega) (by omega : H t - 2 ≤ N t - 0 - 2)]
  constructor
  · rw [endpointCoefficient]
    have h1N2 : 1 ≤ N t - 2 := by omega
    have h1N3 : 1 ≤ N t - 3 := by omega
    simp only [if_pos h1N2, if_pos h1N3,
      if_neg (by omega : ¬(2 ≤ 1 ∧ 1 ≤ N t - 1))]
    rw [prefixWeight_eq_fullWeight (by omega) (by omega : H t - 2 ≤ N t - 1 - 2),
      prefixWeight_one hH3]
    omega
  constructor
  · rw [endpointCoefficient]
    simp only [if_pos (by omega : N t - 2 ≤ N t - 2),
      if_neg (by omega : ¬N t - 2 ≤ N t - 3),
      if_pos (by omega : 2 ≤ N t - 2 ∧ N t - 2 ≤ N t - 1), zero_add]
    have harg : N t - 2 - 1 = N t - 3 := by omega
    rw [harg]
    rw [prefixWeight_eq_fullWeight (by omega) hfullN2,
      prefixWeight_eq_fullWeight (by omega) hfullN3]
    omega
  · rw [endpointCoefficient]
    simp only [if_neg (by omega : ¬N t - 1 ≤ N t - 2),
      if_neg (by omega : ¬N t - 1 ≤ N t - 3),
      if_pos (by omega : 2 ≤ N t - 1 ∧ N t - 1 ≤ N t - 1), zero_add]
    have harg : N t - 1 - 1 = N t - 2 := by omega
    rw [harg, prefixWeight_eq_fullWeight (by omega) hfullN2]

/-- The ceiling cutoff satisfies the upper square bound `N_t <= H_t^2`. -/
theorem N_le_H_sq (t : ℕ) : N t ≤ H t ^ 2 := by
  have hs := sqrt_N_le_H t
  have hN0 : (0 : ℝ) ≤ N t := by positivity
  have hs0 : 0 ≤ Real.sqrt (N t : ℝ) := Real.sqrt_nonneg _
  have hsq := mul_self_le_mul_self hs0 hs
  have hs2 : (Real.sqrt (N t : ℝ)) ^ 2 = (N t : ℝ) := Real.sq_sqrt hN0
  have hsq' : (N t : ℝ) ≤ (H t : ℝ) ^ 2 := by
    rw [← hs2]
    simpa [pow_two] using hsq
  exact_mod_cast hsq'

/-- The opposite strict square bound supplied by the ceiling. -/
theorem H_pred_sq_lt_N (t : ℕ) : (H t - 1) ^ 2 < N t := by
  have hceil := H_lt_sqrt_N_add_one t
  have hHpos := H_pos t
  have hpred : ((H t - 1 : ℕ) : ℝ) < Real.sqrt (N t : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ H t)]
    norm_num
    linarith
  have hpred0 : (0 : ℝ) ≤ (H t - 1 : ℕ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (N t : ℝ) := Real.sqrt_nonneg _
  have hN0 : (0 : ℝ) ≤ N t := by positivity
  have hs2 : (Real.sqrt (N t : ℝ)) ^ 2 = (N t : ℝ) := Real.sq_sqrt hN0
  have hsq : (((H t - 1 : ℕ) : ℝ)) ^ 2 < N t := by
    rw [← hs2]
    nlinarith
  exact_mod_cast hsq

/-- Every exponent in the literal interior interval has the same exact
positive cubic coefficient. -/
theorem interior_endpointCoefficient
    (t K : ℕ) (hKlo : H t - 1 ≤ K) (hKhi : K ≤ N t - H t) :
    endpointCoefficient t K = (H t - 1) * (H t ^ 2 + 7 * H t - 9) := by
  have hH3 := three_le_H t
  have hKN3 : K ≤ N t - 3 := by omega
  have hKN2 : K ≤ N t - 2 := by omega
  have hK2 : 2 ≤ K := by omega
  have hKN1 : K ≤ N t - 1 := by omega
  have hlast : 2 ≤ K ∧ K ≤ N t - 1 := ⟨hK2, hKN1⟩
  have hcross : H t - 2 ≤ N t - K - 2 := by omega
  have hv1 : H t - 2 ≤ K := by omega
  have hv10 : H t - 2 ≤ K - 1 := by omega
  rw [endpointCoefficient]
  simp only [if_pos hKN2, if_pos hKN3, if_pos hlast]
  rw [prefixWeight_eq_fullWeight (by omega) hcross,
    prefixWeight_eq_fullWeight (by omega) hv1,
    prefixWeight_eq_fullWeight (by omega) hv10]
  have hfull := three_mul_fullWeight (H t)
  have hnine : 9 ≤ H t ^ 2 + 7 * H t := by nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  have hfullZ : (3 : ℤ) * fullWeight (H t) =
      (H t : ℤ) * (H t - 1 : ℕ) * (H t - 2 : ℕ) := by
    exact_mod_cast hfull
  have hsub1Z : (((H t - 1 : ℕ) : ℤ)) = (H t : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ H t)]
    norm_num
  have hsub2Z : (((H t - 2 : ℕ) : ℤ)) = (H t : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ H t)]
    norm_num
  have hsub9Z : (((H t ^ 2 + 7 * H t - 9 : ℕ) : ℤ)) =
      (H t : ℤ) ^ 2 + 7 * H t - 9 := by
    rw [Nat.cast_sub hnine]
    push_cast
    ring
  rw [hsub1Z, hsub2Z] at hfullZ
  rw [hsub1Z, hsub9Z]
  calc
    (9 : ℤ) * ((H t : ℤ) - 1) ^ 2 + fullWeight (H t) +
        fullWeight (H t) + fullWeight (H t) =
      9 * ((H t : ℤ) - 1) ^ 2 + 3 * fullWeight (H t) := by ring
    _ = 9 * ((H t : ℤ) - 1) ^ 2 +
        (H t : ℤ) * ((H t : ℤ) - 1) * ((H t : ℤ) - 2) := by rw [hfullZ]
    _ = ((H t : ℤ) - 1) * ((H t : ℤ) ^ 2 + 7 * H t - 9) := by ring

/-- The cubic interior coefficient is strictly positive. -/
theorem interior_endpointCoefficient_pos
    (t K : ℕ) (hKlo : H t - 1 ≤ K) (hKhi : K ≤ N t - H t) :
    0 < endpointCoefficient t K := by
  rw [interior_endpointCoefficient t K hKlo hKhi]
  have hH3 := three_le_H t
  have hleft : 0 < H t - 1 := by omega
  have hbase : 9 < H t ^ 2 + 7 * H t := by nlinarith
  have hright : 0 < H t ^ 2 + 7 * H t - 9 := by omega
  exact mul_pos hleft hright

/-- Number of integer exponents in the inclusive interior interval. -/
def interiorCard (t : ℕ) : ℕ := N t + 2 - 2 * H t

/-- Two-sided mass after retaining both ordered orientations. -/
def twoSidedInteriorMass (t : ℕ) : ℕ :=
  2 * interiorCard t * ((H t - 1) * (H t ^ 2 + 7 * H t - 9))

/-- The literal two-sided mass of the positive and negative coefficients of
the raw pooled Laurent polynomial over the inclusive interior interval. -/
def pooledTwoSidedCoefficientMass (t : ℕ) : ℕ :=
  ∑ K ∈ Finset.Icc (H t - 1) (N t - H t),
    (pooledLaurent t (9 * (10 : ℤ) ^ K) +
      pooledLaurent t (-(9 * (10 : ℤ) ^ K)))

/-- Exact identification of the literal coefficient sum with the closed
two-sided mass formula. -/
theorem pooledTwoSidedCoefficientMass_exact (t : ℕ) :
    pooledTwoSidedCoefficientMass t = twoSidedInteriorMass t := by
  have hH3 := three_le_H t
  have hsq := H_pred_sq_lt_N t
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hH3
  have hquad : 2 * H t - 2 ≤ (H t - 1) ^ 2 := by
    rw [hu]
    norm_num
    nlinarith [sq_nonneg u]
  have hNwide : 2 * H t - 1 ≤ N t := by omega
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hNwide
  have hinterval : H t - 1 ≤ N t - H t := by
    omega
  have hcard : (Finset.Icc (H t - 1) (N t - H t)).card = interiorCard t := by
    rw [Nat.card_Icc]
    unfold interiorCard
    rw [hv]
    omega
  unfold pooledTwoSidedCoefficientMass
  simp_rw [pooledLaurent_positive_multiplierNine,
    pooledLaurent_negative_multiplierNine]
  calc
    (∑ K ∈ Finset.Icc (H t - 1) (N t - H t),
        (endpointCoefficient t K + endpointCoefficient t K)) =
      ∑ K ∈ Finset.Icc (H t - 1) (N t - H t),
        2 * ((H t - 1) * (H t ^ 2 + 7 * H t - 9)) := by
          apply Finset.sum_congr rfl
          intro K hK
          have hKB := Finset.mem_Icc.mp hK
          rw [interior_endpointCoefficient t K hKB.1 hKB.2]
          ring
    _ = (Finset.Icc (H t - 1) (N t - H t)).card *
        (2 * ((H t - 1) * (H t ^ 2 + 7 * H t - 9))) := by
          simp
    _ = twoSidedInteriorMass t := by
      rw [hcard]
      unfold twoSidedInteriorMass
      ring

/-- The interior interval is nonempty and has at least `(H_t-2)^2` points. -/
theorem interiorCard_lower (t : ℕ) : (H t - 2) ^ 2 ≤ interiorCard t := by
  have hsq := H_pred_sq_lt_N t
  have hH3 := three_le_H t
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hH3
  have hid : (H t - 2) ^ 2 + 2 * H t = (H t - 1) ^ 2 + 3 := by
    rw [hu]
    have hs2 : 3 + u - 2 = u + 1 := by omega
    have hs1 : 3 + u - 1 = u + 2 := by omega
    rw [hs2, hs1]
    ring
  have hlin : (H t - 2) ^ 2 + 2 * H t ≤ N t + 2 := by
    omega
  unfold interiorCard
  omega

/-- Explicit two-sided coefficient-mass lower bound. -/
theorem twoSidedInteriorMass_lower (t : ℕ) :
    2 * (H t - 2) ^ 2 * (H t - 1) * H t ^ 2 ≤
      twoSidedInteriorMass t := by
  have hcard := interiorCard_lower t
  have hH3 := three_le_H t
  unfold twoSidedInteriorMass
  have hcubic : H t ^ 2 ≤ H t ^ 2 + 7 * H t - 9 := by omega
  calc
    2 * (H t - 2) ^ 2 * (H t - 1) * H t ^ 2 =
        2 * (H t - 2) ^ 2 * ((H t - 1) * H t ^ 2) := by ring
    _ ≤ 2 * interiorCard t * ((H t - 1) * (H t ^ 2 + 7 * H t - 9)) := by
      gcongr
    _ = 2 * interiorCard t * ((H t - 1) * (H t ^ 2 + 7 * H t - 9)) := rfl

/-- The exact two-sided interior mass exceeds the post-Cauchy target scale
`H_t^2*N_t`; this is only a coefficient-space comparison. -/
theorem targetScale_lt_twoSidedInteriorMass (t : ℕ) :
    H t ^ 2 * N t < twoSidedInteriorMass t := by
  have hH3 := three_le_H t
  have hNup := N_le_H_sq t
  have hcard := interiorCard_lower t
  unfold twoSidedInteriorMass
  by_cases hH : H t = 3
  · have hNlo := five_le_N t
    simp [hH, interiorCard] at *
    omega
  · have hH4 : 4 ≤ H t := by omega
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hH4
    have hpoly : H t ^ 2 < 2 * (H t - 2) ^ 2 * (H t - 1) := by
      rw [hu]
      have hs2 : 4 + u - 2 = u + 2 := by omega
      have hs1 : 4 + u - 1 = u + 3 := by omega
      rw [hs2, hs1]
      have hu3 : 0 ≤ u ^ 2 * u := mul_nonneg (sq_nonneg u) (Nat.zero_le u)
      nlinarith [sq_nonneg u]
    have hcubic : H t ^ 2 ≤ H t ^ 2 + 7 * H t - 9 := by omega
    calc
      H t ^ 2 * N t ≤ H t ^ 2 * H t ^ 2 := Nat.mul_le_mul_left _ hNup
      _ < (2 * (H t - 2) ^ 2 * (H t - 1)) * H t ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hpoly (pow_pos (by omega) _)
      _ ≤ (2 * interiorCard t * (H t - 1)) *
          (H t ^ 2 + 7 * H t - 9) := by gcongr
      _ = 2 * interiorCard t * ((H t - 1) * (H t ^ 2 + 7 * H t - 9)) := by ring

/-- The literal raw-polynomial coefficient mass has the same strict target
scale comparison. -/
theorem targetScale_lt_pooledTwoSidedCoefficientMass (t : ℕ) :
    H t ^ 2 * N t < pooledTwoSidedCoefficientMass t := by
  rw [pooledTwoSidedCoefficientMass_exact]
  exact targetScale_lt_twoSidedInteriorMass t

/-- Final scope: the positive interior coefficient and its reversed negative
counterpart are nonzero, so coefficientwise multiplier-nine telescoping fails.
No statement about evaluation at `pi` follows. -/
theorem coefficientwise_multiplierNine_telescope_fails (t : ℕ) :
    ∀ K, H t - 1 ≤ K → K ≤ N t - H t →
      pooledLaurent t (9 * (10 : ℤ) ^ K) =
          (H t - 1) * (H t ^ 2 + 7 * H t - 9) ∧
      pooledLaurent t (-(9 * (10 : ℤ) ^ K)) =
          (H t - 1) * (H t ^ 2 + 7 * H t - 9) ∧
      0 < pooledLaurent t (9 * (10 : ℤ) ^ K) ∧
      H t ^ 2 * N t < pooledTwoSidedCoefficientMass t := by
  intro K hKlo hKhi
  have hc := interior_endpointCoefficient t K hKlo hKhi
  have hp := interior_endpointCoefficient_pos t K hKlo hKhi
  rw [pooledLaurent_positive_multiplierNine,
    pooledLaurent_negative_multiplierNine]
  exact ⟨hc, hc, hp, targetScale_lt_pooledTwoSidedCoefficientMass t⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T74

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.pooledLaurent_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.pooledLaurent_apply
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.positive_orientation_classification
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.negative_orientation_classification
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.pooled_multiplierNine_tuple_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.pooledLaurent_positive_multiplierNine
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.pooledLaurent_negative_multiplierNine
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.endpointCoefficient_formula
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.endpointCoefficient_boundary_values
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.interior_endpointCoefficient
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.interior_endpointCoefficient_pos
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.pooledTwoSidedCoefficientMass_exact
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.interiorCard_lower
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.twoSidedInteriorMass_lower
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.targetScale_lt_pooledTwoSidedCoefficientMass
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T74.coefficientwise_multiplierNine_telescope_fails
