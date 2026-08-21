import TheoryLib.PiQuantitativeBlockHitting.T44T44MachinTotalTwoAdicForcing
import Mathlib.Data.ZMod.Basic

/-!
# T45: interior-prime survival in the actual sampled Machin forcing

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T40 writes one sampled Machin forcing increment as six base-5 Taylor terms
and six base-239 Taylor terms.  If a prime `p > 12`, distinct from the two
Machin bases, occupies one of the possible interior prime slots, exactly one
term from each window has linear denominator `p`.  This module proves that
these two singular terms do not cancel: after their natural denominator is
cleared, Fermat's theorem reduces their numerator to the fixed residue

`4 * (-1)^k * (4 * 239 - 5) = 4 * (-1)^k * 951`.

The slot congruences exclude the only prime factor `317 > 12` of `951`.
Every other term in the twelve-term block is `p`-integral, so the complete
actual rational forcing has `p`-adic valuation exactly `-1`.

This is exact local arithmetic.  It does not imply an archimedean cylinder
hit, recurrence, density, normality, or the every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinPrimeSurvival

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinLocalForcing

/-- The integer left after combining the two terms with shared linear
denominator `p`, apart from the harmless factor `4 * (-1)^k`. -/
def machinCancellationFactor (p : ℕ) : ℤ :=
  4 * (239 : ℤ) ^ p - (5 : ℤ) ^ p

/-- Fermat's theorem turns the cancellation factor into the fixed residue
`951 = 4 * 239 - 5` modulo `p`. -/
theorem machinCancellationFactor_cast_zmod (p : ℕ) (hp : p.Prime) :
    (machinCancellationFactor p : ZMod p) = 951 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [machinCancellationFactor, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_pow]
  rw [ZMod.pow_card, ZMod.pow_card]
  norm_num

/-- None of the three admissible interior slots can contain the exceptional
prime `317`. -/
lemma eligibleInteriorPrime_ne_317
    (N k p : ℕ) (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    p ≠ 317 := by
  rcases hk with rfl | rfl | rfl <;> omega

/-- An admissible interior prime greater than twelve cannot divide `951`.
The factorization is `951 = 3 * 317`; the slot congruences exclude `317`. -/
lemma eligibleInteriorPrime_not_dvd_951
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    ¬ p ∣ 951 := by
  intro h
  have hsplit : p ∣ 3 ∨ p ∣ 317 := by
    apply hp.dvd_mul.mp
    norm_num at h ⊢
    exact h
  rcases hsplit with h3 | h317
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h1 | h3eq
    · exact hp.ne_one h1
    · omega
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 317)).mp h317 with h1 | h317eq
    · exact hp.ne_one h1
    · exact eligibleInteriorPrime_ne_317 N k p hpdef hk h317eq

/-- The cancellation factor is nonzero modulo every admissible interior
prime greater than twelve. -/
theorem machinCancellationFactor_cast_zmod_ne_zero
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    (machinCancellationFactor p : ZMod p) ≠ 0 := by
  rw [machinCancellationFactor_cast_zmod p hp]
  intro hzero
  have hzero' : (((951 : ℤ) : ZMod p)) = 0 := by
    norm_num at hzero ⊢
    exact hzero
  have hdvd : (p : ℤ) ∣ (951 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (951 : ℤ) p).mp hzero'
  have hdvdNat : p ∣ 951 := by
    exact_mod_cast hdvd
  exact eligibleInteriorPrime_not_dvd_951 N k p hp hpgt hpdef hk hdvdNat

/-- Integer form of the same noncancellation theorem. -/
theorem machinCancellationFactor_not_dvd
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    ¬ (p : ℤ) ∣ machinCancellationFactor p := by
  intro hdvd
  have hz : (machinCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (machinCancellationFactor p) p).2 hdvd
  exact machinCancellationFactor_cast_zmod_ne_zero
    N k p hp hpgt hpdef hk hz

/-- The base-5 term at local index `j` in the actual twelve-term block. -/
def baseFiveWindowTermRat (N j : ℕ) : ℚ :=
  16 * (-1 : ℚ) ^ j /
    (((12 * N + 5 + 2 * j : ℕ) : ℚ) * 5 ^ (12 * N + 5 + 2 * j))

/-- The base-239 term at local index `j` after accounting for both the odd
starting Taylor sign and Machin's coefficient `-4`. -/
def base239WindowTermRat (N j : ℕ) : ℚ :=
  4 * (-1 : ℚ) ^ j /
    (((12 * N + 7 + 2 * j : ℕ) : ℚ) * 239 ^ (12 * N + 7 + 2 * j))

/-- The unscaled inner twelve-term block in the actual forcing. -/
def actualMachinBlockRat (N : ℕ) : ℚ :=
  ∑ j ∈ range 6, baseFiveWindowTermRat N j
    + ∑ j ∈ range 6, base239WindowTermRat N j

/-- The exact combination of the two terms whose linear denominator is the
same interior prime `p`. -/
def interiorSingularPairRat (p k : ℕ) : ℚ :=
  (4 * (-1 : ℚ) ^ k * (machinCancellationFactor p : ℚ)) /
    ((p : ℚ) * 5 ^ p * 239 ^ p)

/-- The ten terms remaining after deleting the two terms with shared linear
denominator `p = 12*N+5+2*k`. -/
def interiorRegularBlockRat (N k : ℕ) : ℚ :=
  ∑ j ∈ (range 6).erase k, baseFiveWindowTermRat N j
    + ∑ j ∈ (range 6).erase (k - 1), base239WindowTermRat N j

lemma interiorSingularPairRat_eq_two_terms
    (p k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    interiorSingularPairRat p k =
      16 * (-1 : ℚ) ^ k / ((p : ℚ) * 5 ^ p) +
        4 * (-1 : ℚ) ^ (k - 1) / ((p : ℚ) * 239 ^ p) := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hp
  have hpow : (-1 : ℚ) ^ k = (-1 : ℚ) ^ (k - 1) * (-1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  have hsign : (-1 : ℚ) ^ (k - 1) = -((-1 : ℚ) ^ k) := by
    rw [hpow]
    ring
  rw [hsign]
  simp only [interiorSingularPairRat, machinCancellationFactor]
  push_cast
  field_simp
  ring

lemma baseFiveWindowTermRat_at_interior
    (N k p : ℕ) (hpdef : p = 12 * N + 5 + 2 * k) :
    baseFiveWindowTermRat N k =
      16 * (-1 : ℚ) ^ k / ((p : ℚ) * 5 ^ p) := by
  subst p
  rfl

lemma base239WindowTermRat_at_interior
    (N k p : ℕ) (hpdef : p = 12 * N + 5 + 2 * k) (hk : 1 ≤ k) :
    base239WindowTermRat N (k - 1) =
      4 * (-1 : ℚ) ^ (k - 1) / ((p : ℚ) * 239 ^ p) := by
  have he : 12 * N + 7 + 2 * (k - 1) = p := by omega
  simp only [base239WindowTermRat]
  rw [he]

/-- The actual twelve-term block is the sum of its ten regular terms and the
two explicitly combined singular terms. -/
theorem actualMachinBlockRat_eq_regular_add_singular
    (N k p : ℕ) (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    actualMachinBlockRat N =
      interiorRegularBlockRat N k + interiorSingularPairRat p k := by
  have hkpos : 1 ≤ k := by
    rcases hk with rfl | rfl | rfl <;> omega
  have hk6 : k < 6 := by
    rcases hk with rfl | rfl | rfl <;> omega
  have hkmem : k ∈ range 6 := mem_range.2 hk6
  have hkm1mem : k - 1 ∈ range 6 := mem_range.2 (by omega)
  have hfive := sum_erase_add (range 6) (baseFiveWindowTermRat N) hkmem
  have h239 := sum_erase_add (range 6) (base239WindowTermRat N) hkm1mem
  rw [interiorSingularPairRat_eq_two_terms p k (by omega) hkpos,
    ← baseFiveWindowTermRat_at_interior N k p hpdef,
    ← base239WindowTermRat_at_interior N k p hpdef hkpos]
  unfold actualMachinBlockRat interiorRegularBlockRat
  rw [← hfive, ← h239]
  ring

lemma padicValRat_natCast_eq_zero_of_not_dvd
    {p n : ℕ} (hn : ¬ p ∣ n) :
    padicValRat p (n : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  simpa using padicValNat.eq_zero_of_not_dvd hn

lemma padicValRat_intCast_eq_zero_of_not_dvd
    {p : ℕ} {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) :
    padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  simpa using padicValInt.eq_zero_of_not_dvd hz

lemma machinCancellationFactor_ratCast_ne_zero
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    (machinCancellationFactor p : ℚ) ≠ 0 := by
  have hz : machinCancellationFactor p ≠ 0 := by
    intro hz
    apply machinCancellationFactor_not_dvd N k p hp hpgt hpdef hk
    rw [hz]
    exact dvd_zero _
  exact_mod_cast hz

lemma prime_gt_twelve_not_dvd_four
    (p : ℕ) (hp : p.Prime) (hpgt : 12 < p) :
    ¬ p ∣ 4 := by
  intro h
  have h2 : p ∣ 2 := by
    apply hp.dvd_of_dvd_pow (n := 2)
    norm_num at h ⊢
    exact h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2 with h1 | htwo
  · exact hp.ne_one h1
  · omega

lemma prime_gt_twelve_not_dvd_sixteen
    (p : ℕ) (hp : p.Prime) (hpgt : 12 < p) :
    ¬ p ∣ 16 := by
  intro h
  have h2 : p ∣ 2 := by
    apply hp.dvd_of_dvd_pow (n := 4)
    norm_num at h ⊢
    exact h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2 with h1 | htwo
  · exact hp.ne_one h1
  · omega

lemma prime_gt_twelve_not_dvd_five
    (p : ℕ) (hp : p.Prime) (hpgt : 12 < p) :
    ¬ p ∣ 5 := by
  intro h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h1 | hfive
  · exact hp.ne_one h1
  · omega

lemma prime_ne_239_not_dvd_239
    (p : ℕ) (hp : p.Prime) (hpne : p ≠ 239) :
    ¬ p ∣ 239 := by
  intro h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 239)).mp h with h1 | h239
  · exact hp.ne_one h1
  · exact hpne h239

lemma eq_of_dvd_of_pos_of_lt_two_mul
    {p a : ℕ} (hp : 0 < p) (ha : 0 < a) (halt : a < 2 * p)
    (hpa : p ∣ a) :
    a = p := by
  have hple : p ≤ a := Nat.le_of_dvd ha hpa
  have hqpos : 0 < a / p := Nat.div_pos hple hp
  have hqlt : a / p < 2 :=
    (Nat.div_lt_iff_lt_mul hp).2 (by simpa [mul_comm] using halt)
  have hq : a / p = 1 := by omega
  calc
    a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
    _ = p := by rw [hq, mul_one]

lemma prime_not_dvd_regular_five_exponent
    (N k p j : ℕ) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hj : j ∈ (range 6).erase k) :
    ¬ p ∣ 12 * N + 5 + 2 * j := by
  intro hdvd
  have hj6 : j < 6 := mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have heq : 12 * N + 5 + 2 * j = p :=
    eq_of_dvd_of_pos_of_lt_two_mul
      (by omega) (by omega) (by omega) hdvd
  apply hjne
  omega

lemma prime_not_dvd_regular_239_exponent
    (N k p j : ℕ) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hj : j ∈ (range 6).erase (k - 1)) (hk : 1 ≤ k) :
    ¬ p ∣ 12 * N + 7 + 2 * j := by
  intro hdvd
  have hj6 : j < 6 := mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k - 1 := ne_of_mem_erase hj
  have heq : 12 * N + 7 + 2 * j = p :=
    eq_of_dvd_of_pos_of_lt_two_mul
      (by omega) (by omega) (by omega) hdvd
  apply hjne
  omega

lemma padicValRat_signed_fraction_eq_zero
    (p c q a j : ℕ) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hq : ¬ p ∣ q) (ha : ¬ p ∣ a)
    (hc0 : c ≠ 0) (hq0 : q ≠ 0) (ha0 : a ≠ 0) :
    padicValRat p
      ((c : ℚ) * (-1 : ℚ) ^ j / ((a : ℚ) * q ^ a)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  have hneg : (-1 : ℚ) ≠ 0 := by norm_num
  have hnum : (c : ℚ) * (-1 : ℚ) ^ j ≠ 0 :=
    mul_ne_zero hcq (pow_ne_zero _ hneg)
  have hden : (a : ℚ) * q ^ a ≠ 0 :=
    mul_ne_zero haq (pow_ne_zero _ hqq)
  have hvalc := padicValRat_natCast_eq_zero_of_not_dvd hc
  have hvalq := padicValRat_natCast_eq_zero_of_not_dvd hq
  have hvala := padicValRat_natCast_eq_zero_of_not_dvd ha
  have hvalneg : padicValRat p (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  rw [padicValRat.div hnum hden,
    padicValRat.mul hcq (pow_ne_zero _ hneg),
    padicValRat.pow hneg, hvalc, hvalneg,
    padicValRat.mul haq (pow_ne_zero _ hqq),
    padicValRat.pow hqq, hvala, hvalq]
  norm_num

lemma padicValRat_regular_five_term_eq_zero
    (N k p j : ℕ) (hp : p.Prime) (hpgt : 12 < p)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hj : j ∈ (range 6).erase k) :
    padicValRat p (baseFiveWindowTermRat N j) = 0 := by
  unfold baseFiveWindowTermRat
  exact padicValRat_signed_fraction_eq_zero
    p 16 5 (12 * N + 5 + 2 * j) j hp
    (prime_gt_twelve_not_dvd_sixteen p hp hpgt)
    (prime_gt_twelve_not_dvd_five p hp hpgt)
    (prime_not_dvd_regular_five_exponent N k p j hpgt hpdef hj)
    (by norm_num) (by norm_num) (by omega)

lemma padicValRat_regular_239_term_eq_zero
    (N k p j : ℕ) (hp : p.Prime) (hpgt : 12 < p) (hpne : p ≠ 239)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hj : j ∈ (range 6).erase (k - 1)) (hk : 1 ≤ k) :
    padicValRat p (base239WindowTermRat N j) = 0 := by
  unfold base239WindowTermRat
  exact padicValRat_signed_fraction_eq_zero
    p 4 239 (12 * N + 7 + 2 * j) j hp
    (prime_gt_twelve_not_dvd_four p hp hpgt)
    (prime_ne_239_not_dvd_239 p hp hpne)
    (prime_not_dvd_regular_239_exponent N k p j hpgt hpdef hj hk)
    (by norm_num) (by norm_num) (by omega)

lemma padicValRat_sum_nonneg
    {p : ℕ} (hp : p.Prime) {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ)
    (hf : ∀ a ∈ s, 0 ≤ padicValRat p (f a))
    (hs : ∑ a ∈ s, f a ≠ 0) :
    0 ≤ padicValRat p (∑ a ∈ s, f a) := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  induction s using Finset.induction with
  | empty => simp at hs
  | @insert a s ha ih =>
      rw [sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · simp [hfa] at hs ⊢
        exact ih (fun b hb => hf b (mem_insert_of_mem hb)) hs
      by_cases hsum : ∑ b ∈ s, f b = 0
      · simp [hsum]
        exact hf a (mem_insert_self a s)
      · have htail := ih (fun b hb => hf b (mem_insert_of_mem hb)) hsum
        exact le_trans (le_min (hf a (mem_insert_self a s)) htail)
          (padicValRat.min_le_padicValRat_add hs)

lemma padicValRat_interiorRegularBlockRat_nonneg
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p) (hpne : p ≠ 239)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4)
    (hregular : interiorRegularBlockRat N k ≠ 0) :
    0 ≤ padicValRat p (interiorRegularBlockRat N k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hkpos : 1 ≤ k := by
    rcases hk with rfl | rfl | rfl <;> omega
  let F : ℚ := ∑ j ∈ (range 6).erase k, baseFiveWindowTermRat N j
  let G : ℚ := ∑ j ∈ (range 6).erase (k - 1), base239WindowTermRat N j
  have hF (hF0 : F ≠ 0) : 0 ≤ padicValRat p F := by
    apply padicValRat_sum_nonneg hp
    · intro j hj
      rw [padicValRat_regular_five_term_eq_zero N k p j hp hpgt hpdef hj]
    · exact hF0
  have hG (hG0 : G ≠ 0) : 0 ≤ padicValRat p G := by
    apply padicValRat_sum_nonneg hp
    · intro j hj
      rw [padicValRat_regular_239_term_eq_zero
        N k p j hp hpgt hpne hpdef hj hkpos]
    · exact hG0
  change 0 ≤ padicValRat p (F + G)
  have hFG : F + G ≠ 0 := by
    simpa [F, G, interiorRegularBlockRat] using hregular
  by_cases hF0 : F = 0
  · simp [hF0] at hFG ⊢
    exact hG hFG
  by_cases hG0 : G = 0
  · simp [hG0]
    exact hF hF0
  exact le_trans (le_min (hF hF0) (hG hG0))
    (padicValRat.min_le_padicValRat_add hFG)

/-- The two singular terms have exact `p`-adic valuation `-1`: their shared
factor `p` in the denominator survives the actual signed cancellation. -/
theorem padicValRat_interiorSingularPairRat
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p) (hpne : p ≠ 239)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    padicValRat p (interiorSingularPairRat p k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h50q : (5 : ℚ) ≠ 0 := by norm_num
  have h2390q : (239 : ℚ) ≠ 0 := by norm_num
  have hfactor0 : (machinCancellationFactor p : ℚ) ≠ 0 :=
    machinCancellationFactor_ratCast_ne_zero N k p hp hpgt hpdef hk
  have hnum0 :
      4 * (-1 : ℚ) ^ k * (machinCancellationFactor p : ℚ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (by norm_num))) hfactor0
  have hden0 : (p : ℚ) * 5 ^ p * 239 ^ p ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hp0q (pow_ne_zero _ h50q))
      (pow_ne_zero _ h2390q)
  have hvalFactor :
      padicValRat p (machinCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (machinCancellationFactor_not_dvd N k p hp hpgt hpdef hk)
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_twelve_not_dvd_four p hp hpgt)
  have hvalNegOne : padicValRat p (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hval5 : padicValRat p (5 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_gt_twelve_not_dvd_five p hp hpgt)
  have hval239 : padicValRat p (239 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (prime_ne_239_not_dvd_239 p hp hpne)
  unfold interiorSingularPairRat
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (by norm_num))) hfactor0,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.pow (by norm_num), hval4, hvalNegOne, hvalFactor,
    padicValRat.mul (mul_ne_zero hp0q (pow_ne_zero _ h50q))
      (pow_ne_zero _ h2390q),
    padicValRat.mul hp0q (pow_ne_zero _ h50q),
    padicValRat.self hp.one_lt,
    padicValRat.pow h50q, hval5,
    padicValRat.pow h2390q, hval239]
  norm_num

/-- The complete unscaled actual twelve-term block has exact `p`-adic
valuation `-1` at every admissible interior prime other than the Machin base
`239`. -/
theorem padicValRat_actualMachinBlockRat
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p) (hpne : p ≠ 239)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    padicValRat p (actualMachinBlockRat N) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [actualMachinBlockRat_eq_regular_add_singular N k p hpdef hk]
  have hsing :=
    padicValRat_interiorSingularPairRat N k p hp hpgt hpne hpdef hk
  have hsing0 : interiorSingularPairRat p k ≠ 0 := by
    intro hzero
    simp [hzero] at hsing
  by_cases hregular : interiorRegularBlockRat N k = 0
  · simp [hregular, hsing]
  have hregularVal :=
    padicValRat_interiorRegularBlockRat_nonneg
      N k p hp hpgt hpne hpdef hk hregular
  have hsum :
      interiorSingularPairRat p k + interiorRegularBlockRat N k ≠ 0 := by
    intro hzero
    have heq : interiorRegularBlockRat N k = -interiorSingularPairRat p k := by
      linarith
    have hvaleq := congrArg (padicValRat p) heq
    rw [padicValRat.neg, hsing] at hvaleq
    omega
  rw [add_comm]
  calc
    padicValRat p
        (interiorSingularPairRat p k + interiorRegularBlockRat N k) =
        padicValRat p (interiorSingularPairRat p k) :=
      padicValRat.add_eq_of_lt hsum hsing0 hregular
        (by rw [hsing]; omega)
    _ = -1 := hsing

lemma sixteen_mul_arctanTermRat_eq_baseFiveWindowTermRat
    (N j : ℕ) :
    16 * arctanTermRat 5 (6 * N + 2 + j) =
      baseFiveWindowTermRat N j := by
  have hsign : (-1 : ℚ) ^ (6 * N + 2 + j) = (-1 : ℚ) ^ j := by
    rw [pow_add]
    have he : 6 * N + 2 = 2 * (3 * N + 1) := by omega
    rw [he, pow_mul]
    norm_num
  have hexp : 2 * (6 * N + 2 + j) + 1 = 12 * N + 5 + 2 * j := by
    omega
  unfold arctanTermRat baseFiveWindowTermRat
  rw [hsign, hexp]
  simp only [inv_pow]
  push_cast
  field_simp
  ring

lemma neg_four_mul_arctanTermRat_eq_base239WindowTermRat
    (N j : ℕ) :
    -4 * arctanTermRat 239 (6 * N + 3 + j) =
      base239WindowTermRat N j := by
  have hsign :
      (-1 : ℚ) ^ (6 * N + 3 + j) = -((-1 : ℚ) ^ j) := by
    rw [pow_add]
    have he : 6 * N + 3 = 2 * (3 * N + 1) + 1 := by omega
    rw [he, pow_succ, pow_mul]
    norm_num
  have hexp : 2 * (6 * N + 3 + j) + 1 = 12 * N + 7 + 2 * j := by
    omega
  unfold arctanTermRat base239WindowTermRat
  rw [hsign, hexp]
  simp only [inv_pow]
  push_cast
  field_simp
  ring

/-- Identification of the explicit twelve-term block with T40's two signed
six-term Taylor windows. -/
theorem machinTwelveTermBlock_eq_actualMachinBlockRat (N : ℕ) :
    16 * sixTermArctanWindowRat 5 (6 * N + 2) -
        4 * sixTermArctanWindowRat 239 (6 * N + 3) =
      actualMachinBlockRat N := by
  rw [sixTermArctanWindowRat, sixTermArctanWindowRat, mul_sum, mul_sum]
  unfold actualMachinBlockRat
  rw [sub_eq_add_neg]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro j hj
    rw [sixteen_mul_arctanTermRat_eq_baseFiveWindowTermRat]
  · rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simpa only [neg_mul] using
      neg_four_mul_arctanTermRat_eq_base239WindowTermRat N j

/-- T40's complete rational forcing is the outer decimal power times the
explicit actual block used in this module. -/
theorem sampledMachinForcingRat_eq_actualMachinBlockRat (N : ℕ) :
    sampledMachinForcingRat N =
      (10 : ℚ) ^ (N + 1) * actualMachinBlockRat N := by
  rw [sampledMachinForcingRat,
    machinTwelveTermBlock_eq_actualMachinBlockRat]

/-- Main prime-survival theorem: an admissible interior prime occurs to
exactly the first power in the reduced denominator of the actual sampled
Machin forcing. -/
theorem padicValRat_prime_sampledMachinForcingRat
    (N k p : ℕ) (hp : p.Prime) (hpgt : 12 < p) (hpne : p ≠ 239)
    (hpdef : p = 12 * N + 5 + 2 * k)
    (hk : k = 1 ∨ k = 3 ∨ k = 4) :
    padicValRat p (sampledMachinForcingRat N) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [sampledMachinForcingRat_eq_actualMachinBlockRat]
  have hblockVal :=
    padicValRat_actualMachinBlockRat N k p hp hpgt hpne hpdef hk
  have hblock0 : actualMachinBlockRat N ≠ 0 := by
    intro hzero
    simp [hzero] at hblockVal
  have htenNotDvd : ¬ p ∣ 10 := by
    intro hdvd
    have hle : p ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have htenVal : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd htenNotDvd
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hblock0,
    padicValRat.pow (by norm_num), htenVal, hblockVal]
  norm_num

end Theory.PiDigits.MachinPrimeSurvival

#print axioms
  Theory.PiDigits.MachinPrimeSurvival.machinCancellationFactor_cast_zmod
#print axioms
  Theory.PiDigits.MachinPrimeSurvival.machinCancellationFactor_not_dvd
#print axioms
  Theory.PiDigits.MachinPrimeSurvival.padicValRat_interiorSingularPairRat
#print axioms
  Theory.PiDigits.MachinPrimeSurvival.padicValRat_actualMachinBlockRat
#print axioms
  Theory.PiDigits.MachinPrimeSurvival.padicValRat_prime_sampledMachinForcingRat
