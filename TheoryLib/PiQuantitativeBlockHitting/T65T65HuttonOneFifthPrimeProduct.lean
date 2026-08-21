import TheoryLib.PiQuantitativeBlockHitting.T64T64HuttonOneThirdPrimeProduct

/-!
# T65: one-fifth-band prime survival for the rational Hutton shadows

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Put `R = 4*K+3`.  In the band `R/5 < p <= R/3`, the only Hutton
exponents divisible by the odd prime `p` are `p` and `3*p`.  Combining both
singular pairs and reducing by Fermat gives the fixed numerator residue
`21778 = 2 * 10889`.  Thus, outside the genuine exceptional prime `10889`,
every prime `p > 7` in this band occurs exactly once in the reduced
denominator.  Their complete squarefree product divides that denominator.

This is exact finite denominator arithmetic.  It supplies no asymptotic
estimate, selected-numerator distribution, decimal-cylinder hit, or
every-word theorem for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.HuttonOneFifthPrimeProduct

open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.MachinAllPrimeSurvival
open Theory.PiDigits.MachinSeedUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonEligiblePrimeProduct

/-- Taylor index whose odd exponent is three times the exponent at `k`. -/
def huttonSecondBandIndex (k : ℕ) : ℕ := 3 * k + 1

/-- Integer numerator factor obtained after combining the Hutton pairs at
exponents `p` and `3*p`, with `4 * (-1)^k` removed. -/
def huttonOneThreeCancellationFactor (p : ℕ) : ℤ :=
  3 * (huttonCancellationFactor p : ℤ) * 3 ^ (2 * p) * 7 ^ (2 * p) -
    (huttonCancellationFactor (3 * p) : ℤ)

/-- Fermat reduction of the one-three cancellation factor. -/
def huttonOneThreeFixedResidue : ℤ := 21778

theorem huttonOneThreeFixedResidue_eq_factorization :
    huttonOneThreeFixedResidue = 2 * 10889 := by
  norm_num [huttonOneThreeFixedResidue]

theorem huttonOneThree_exception_prime : Nat.Prime 10889 := by
  norm_num

/-- Fermat's theorem makes the combined cancellation factor constant modulo
the selected prime. -/
theorem huttonOneThreeCancellationFactor_cast_zmod
    (p : ℕ) (hp : p.Prime) :
    (huttonOneThreeCancellationFactor p : ZMod p) =
      huttonOneThreeFixedResidue := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [huttonOneThreeCancellationFactor, huttonOneThreeFixedResidue,
    huttonCancellationFactor, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow]
  rw [show 2 * p = p * 2 by omega, show 3 * p = p * 3 by omega]
  simp only [pow_mul]
  norm_num

lemma prime_not_dvd_huttonOneThreeFixedResidue
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp10889 : p ≠ 10889) :
    ¬ (p : ℤ) ∣ huttonOneThreeFixedResidue := by
  intro hdvdInt
  have hdvd : p ∣ 2 * 10889 := by
    have hdvd' : (p : ℤ) ∣ 2 * 10889 := by
      rw [← huttonOneThreeFixedResidue_eq_factorization]
      exact hdvdInt
    exact_mod_cast hdvd'
  rcases hp.dvd_mul.mp hdvd with h2 | h10889
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · rcases (Nat.dvd_prime huttonOneThree_exception_prime).mp h10889 with h1 | heq
    · exact hp.ne_one h1
    · exact hp10889 heq

lemma huttonOneThreeCancellationFactor_not_dvd
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp10889 : p ≠ 10889) :
    ¬ (p : ℤ) ∣ huttonOneThreeCancellationFactor p := by
  intro hdvd
  have hz : (huttonOneThreeCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (huttonOneThreeCancellationFactor p) p).2 hdvd
  rw [huttonOneThreeCancellationFactor_cast_zmod p hp] at hz
  have hdvdFixed : (p : ℤ) ∣ huttonOneThreeFixedResidue :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd huttonOneThreeFixedResidue p).mp hz
  exact prime_not_dvd_huttonOneThreeFixedResidue
    p hp hpgt hp10889 hdvdFixed

lemma huttonOneThreeCancellationFactor_ratCast_ne_zero
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p) (hp10889 : p ≠ 10889) :
    (huttonOneThreeCancellationFactor p : ℚ) ≠ 0 := by
  have hz : huttonOneThreeCancellationFactor p ≠ 0 := by
    intro hzero
    apply huttonOneThreeCancellationFactor_not_dvd p hp hpgt hp10889
    rw [hzero]
    exact dvd_zero _
  exact_mod_cast hz

/-- The four Hutton terms at odd exponents `p` and `3*p`. -/
def huttonOneThreeSingularBlockRat (k : ℕ) : ℚ :=
  (huttonThreeTermRat k + huttonSevenTermRat k) +
    (huttonThreeTermRat (huttonSecondBandIndex k) +
      huttonSevenTermRat (huttonSecondBandIndex k))

/-- All Hutton terms except the four terms at exponents `p` and `3*p`. -/
def huttonOneThreeRegularBlockRat (K k : ℕ) : ℚ :=
  (∑ j ∈ ((range (huttonTermCount K)).erase k).erase
      (huttonSecondBandIndex k), huttonThreeTermRat j) +
    ∑ j ∈ ((range (huttonTermCount K)).erase k).erase
      (huttonSecondBandIndex k), huttonSevenTermRat j

lemma hutton_second_band_sign (k : ℕ) :
    (-1 : ℚ) ^ (huttonSecondBandIndex k) = -((-1 : ℚ) ^ k) := by
  unfold huttonSecondBandIndex
  rw [show 3 * k + 1 = 2 * k + (k + 1) by omega,
    pow_add, pow_mul, pow_succ]
  norm_num
  rw [pow_succ]
  ring

/-- Exact combination of the four singular terms. -/
theorem huttonOneThreeSingularBlockRat_eq_fraction
    (p k : ℕ) (hpdef : p = 2 * k + 1) :
    huttonOneThreeSingularBlockRat k =
      (4 * (-1 : ℚ) ^ k * (huttonOneThreeCancellationFactor p : ℚ)) /
        ((3 : ℚ) * (p : ℚ) * 3 ^ (3 * p) * 7 ^ (3 * p)) := by
  have hseconddef :
      3 * p = 2 * huttonSecondBandIndex k + 1 := by
    simp [huttonSecondBandIndex]
    omega
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  unfold huttonOneThreeSingularBlockRat
  rw [hutton_singular_pair_eq p k hpdef,
    hutton_singular_pair_eq
      (3 * p) (huttonSecondBandIndex k) hseconddef]
  unfold huttonOneThreeCancellationFactor
  rw [hutton_second_band_sign]
  push_cast
  have hpow3 : (3 : ℚ) ^ (3 * p) = 3 ^ p * 3 ^ (2 * p) := by
    rw [show 3 * p = p + 2 * p by omega, pow_add]
  have hpow7 : (7 : ℚ) ^ (3 * p) = 7 ^ p * 7 ^ (2 * p) := by
    rw [show 3 * p = p + 2 * p by omega, pow_add]
  simp_rw [hpow3, hpow7]
  field_simp [hpq]
  ring

/-- Below `5*p`, an odd Hutton exponent divisible by `p` has cofactor one or
three; both indices have been erased. -/
lemma oneFifthPrime_not_dvd_other_hutton_exponent
    (K k p j : ℕ)
    (hpLower : 4 * K + 3 < 5 * p)
    (hpdef : p = 2 * k + 1)
    (hj : j ∈ ((range (huttonTermCount K)).erase k).erase
      (huttonSecondBandIndex k)) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjInner : j ∈ (range (huttonTermCount K)).erase k :=
    mem_of_mem_erase hj
  have hjlt : j < huttonTermCount K :=
    mem_range.1 (mem_of_mem_erase hjInner)
  have hjne : j ≠ k := ne_of_mem_erase hjInner
  have hjsecondne : j ≠ huttonSecondBandIndex k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 5 * p := by
    unfold huttonTermCount at hjlt
    omega
  rcases hdvd with ⟨t, ht⟩
  have hpPos : 0 < p := by omega
  have hpt : p * t < p * 5 := by
    calc
      p * t = 2 * j + 1 := ht.symm
      _ < 5 * p := hexplt
      _ = p * 5 := by omega
  have htlt : t < 5 := (Nat.mul_lt_mul_left hpPos).mp hpt
  interval_cases t
  all_goals simp_all [huttonSecondBandIndex]
  all_goals omega

/-- Exact decomposition into the regular block and the four singular terms. -/
theorem huttonLowerRat_eq_oneThreeRegular_add_singular
    (K k p : ℕ) (hpdef : p = 2 * k + 1)
    (h3pUpper : 3 * p ≤ 4 * K + 3) :
    huttonLowerRat K = huttonOneThreeRegularBlockRat K k +
      huttonOneThreeSingularBlockRat k := by
  have hk : k < huttonTermCount K := by
    unfold huttonTermCount
    omega
  have hsecond : huttonSecondBandIndex k < huttonTermCount K := by
    unfold huttonTermCount huttonSecondBandIndex
    omega
  have hkmem : k ∈ range (huttonTermCount K) := mem_range.2 hk
  have hsecondmem :
      huttonSecondBandIndex k ∈ range (huttonTermCount K) :=
    mem_range.2 hsecond
  have hsecondne : huttonSecondBandIndex k ≠ k := by
    simp [huttonSecondBandIndex]
    omega
  have hsecondErase :
      huttonSecondBandIndex k ∈ (range (huttonTermCount K)).erase k :=
    mem_erase.mpr ⟨hsecondne, hsecondmem⟩
  have hthreeFirst :=
    sum_erase_add (range (huttonTermCount K)) huttonThreeTermRat hkmem
  have hthreeSecond :=
    sum_erase_add ((range (huttonTermCount K)).erase k)
      huttonThreeTermRat hsecondErase
  have hsevenFirst :=
    sum_erase_add (range (huttonTermCount K)) huttonSevenTermRat hkmem
  have hsevenSecond :=
    sum_erase_add ((range (huttonTermCount K)).erase k)
      huttonSevenTermRat hsecondErase
  rw [huttonLowerRat_eq_term_sums, ← hthreeFirst, ← hthreeSecond,
    ← hsevenFirst, ← hsevenSecond]
  unfold huttonOneThreeRegularBlockRat huttonOneThreeSingularBlockRat
  ring

/-- The combined four-term singular block has exact valuation `-1`. -/
theorem padicValRat_huttonOneThreeSingularBlockRat
    (p k : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp10889 : p ≠ 10889) (hpdef : p = 2 * k + 1) :
    padicValRat p (huttonOneThreeSingularBlockRat k) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h3q : (3 : ℚ) ≠ 0 := by norm_num
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4q : (4 : ℚ) ≠ 0 := by norm_num
  have h7q : (7 : ℚ) ≠ 0 := by norm_num
  have hsign0 : (-1 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfactor0 : (huttonOneThreeCancellationFactor p : ℚ) ≠ 0 :=
    huttonOneThreeCancellationFactor_ratCast_ne_zero
      p hp hpgt hp10889
  have hnum0 :
      4 * (-1 : ℚ) ^ k * (huttonOneThreeCancellationFactor p : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4q hsign0) hfactor0
  have h3pow0 : (3 : ℚ) ^ (3 * p) ≠ 0 := pow_ne_zero _ h3q
  have h7pow0 : (7 : ℚ) ^ (3 * p) ≠ 0 := pow_ne_zero _ h7q
  have hden0 :
      (3 : ℚ) * (p : ℚ) * 3 ^ (3 * p) * 7 ^ (3 * p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h3q hpq) h3pow0) h7pow0
  have hp4 : ¬ p ∣ 4 := by
    intro h
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
    omega
  have hp3 : ¬ p ∣ 3 := by
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
    omega
  have hp7 : ¬ p ∣ 7 := by
    intro h
    have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) h
    omega
  have hval4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp4
  have hvalSign : padicValRat p ((-1 : ℚ) ^ k) = 0 := by
    rw [padicValRat.pow (by norm_num), padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat p (huttonOneThreeCancellationFactor p : ℚ) = 0 :=
    padicValRat_intCast_eq_zero_of_not_dvd
      (huttonOneThreeCancellationFactor_not_dvd
        p hp hpgt hp10889)
  have hval3 : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp3
  have hval7 : padicValRat p (7 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp7
  rw [huttonOneThreeSingularBlockRat_eq_fraction p k hpdef,
    padicValRat.div hnum0 hden0,
    padicValRat.mul (mul_ne_zero h4q hsign0) hfactor0,
    padicValRat.mul h4q hsign0,
    padicValRat.mul (mul_ne_zero (mul_ne_zero h3q hpq) h3pow0) h7pow0,
    padicValRat.mul (mul_ne_zero h3q hpq) h3pow0,
    padicValRat.mul h3q hpq,
    padicValRat.self hp.one_lt,
    padicValRat.pow h3q, padicValRat.pow h7q,
    hval4, hvalSign, hvalFactor, hval3, hval7]
  norm_num

/-- Every nonsingular Hutton term is `p`-integral in the one-fifth band. -/
lemma padicValRat_huttonOneThreeRegularBlockRat_nonneg
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hpLower : 4 * K + 3 < 5 * p)
    (hpdef : p = 2 * k + 1)
    (hregular : huttonOneThreeRegularBlockRat K k ≠ 0) :
    0 ≤ padicValRat p (huttonOneThreeRegularBlockRat K k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let A := ((range (huttonTermCount K)).erase k).erase
    (huttonSecondBandIndex k)
  let F : ℚ := ∑ j ∈ A, huttonThreeTermRat j
  let G : ℚ := ∑ j ∈ A, huttonSevenTermRat j
  have hF : F = 0 ∨ 0 ≤ padicValRat p F := by
    by_cases hF0 : F = 0
    · exact Or.inl hF0
    · apply Or.inr
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_huttonThreeTermRat_eq_zero p j hp hpgt
          (oneFifthPrime_not_dvd_other_hutton_exponent
            K k p j hpLower hpdef (by simpa [A] using hj))]
      · exact hF0
  have hG : G = 0 ∨ 0 ≤ padicValRat p G := by
    by_cases hG0 : G = 0
    · exact Or.inl hG0
    · apply Or.inr
      apply padicValRat_sum_nonneg hp
      · intro j hj
        rw [padicValRat_huttonSevenTermRat_eq_zero p j hp hpgt
          (oneFifthPrime_not_dvd_other_hutton_exponent
            K k p j hpLower hpdef (by simpa [A] using hj))]
      · exact hG0
  change 0 ≤ padicValRat p (F + G)
  apply padicValRat_add_nonneg_of_each_nonneg p hp hF hG
  simpa [F, G, A, huttonOneThreeRegularBlockRat] using hregular

/-- Main one-fifth-band valuation theorem. -/
theorem padicValRat_huttonLowerRat_oneFifthPrime
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp10889 : p ≠ 10889)
    (hpLower : 4 * K + 3 < 5 * p)
    (h3pUpper : 3 * p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    padicValRat p (huttonLowerRat K) = -1 := by
  rw [huttonLowerRat_eq_oneThreeRegular_add_singular
    K k p hpdef h3pUpper]
  apply padicValRat_add_eq_neg_one_of_nonneg p hp
  · exact padicValRat_huttonOneThreeSingularBlockRat
      p k hp hpgt hp10889 hpdef
  · by_cases hregular : huttonOneThreeRegularBlockRat K k = 0
    · exact Or.inl hregular
    · exact Or.inr
        (padicValRat_huttonOneThreeRegularBlockRat_nonneg
          K k p hp hpgt hpLower hpdef hregular)

theorem oneFifthPrime_dvd_huttonLowerRat_den
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp10889 : p ≠ 10889)
    (hpLower : 4 * K + 3 < 5 * p)
    (h3pUpper : 3 * p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    p ∣ (huttonLowerRat K).den := by
  apply dvd_rat_den_of_padicValRat_neg
  rw [padicValRat_huttonLowerRat_oneFifthPrime
    K k p hp hpgt hp10889 hpLower h3pUpper hpdef]
  norm_num

theorem padicValNat_huttonLowerRat_den_oneFifthPrime
    (K k p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hp10889 : p ≠ 10889)
    (hpLower : 4 * K + 3 < 5 * p)
    (h3pUpper : 3 * p ≤ 4 * K + 3)
    (hpdef : p = 2 * k + 1) :
    padicValNat p (huttonLowerRat K).den = 1 := by
  let q := huttonLowerRat K
  change padicValNat p q.den = 1
  have hval : padicValRat p q = -1 :=
    padicValRat_huttonLowerRat_oneFifthPrime
      K k p hp hpgt hp10889 hpLower h3pUpper hpdef
  have hden : p ∣ q.den :=
    oneFifthPrime_dvd_huttonLowerRat_den
      K k p hp hpgt hp10889 hpLower h3pUpper hpdef
  have hcop : Nat.Coprime p q.num.natAbs :=
    (Nat.Coprime.of_dvd_right hden q.reduced).symm
  have hnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum
  rw [padicValRat_def, hvnum] at hval
  omega

/-- Exact finite set of one-fifth-band primes. -/
def huttonOneFifthPrimeSet (K : ℕ) : Finset ℕ :=
  (range (4 * K + 4)).filter fun p =>
    p.Prime ∧ 7 < p ∧ p ≠ 10889 ∧
      4 * K + 3 < 5 * p ∧ 3 * p ≤ 4 * K + 3

def huttonOneFifthPrimeProduct (K : ℕ) : ℕ :=
  (huttonOneFifthPrimeSet K).prod id

theorem mem_huttonOneFifthPrimeSet_iff (K p : ℕ) :
    p ∈ huttonOneFifthPrimeSet K ↔
      p.Prime ∧ 7 < p ∧ p ≠ 10889 ∧
        4 * K + 3 < 5 * p ∧ 3 * p ≤ 4 * K + 3 := by
  rw [huttonOneFifthPrimeSet, mem_filter, mem_range]
  constructor
  · rintro ⟨_, hpPrime, hpgt, hp10889, hpLower, h3pUpper⟩
    exact ⟨hpPrime, hpgt, hp10889, hpLower, h3pUpper⟩
  · rintro ⟨hpPrime, hpgt, hp10889, hpLower, h3pUpper⟩
    exact ⟨by omega, hpPrime, hpgt, hp10889, hpLower, h3pUpper⟩

theorem huttonOneFifthPrime_dvd_huttonLowerRat_den
    (K p : ℕ) (hp : p ∈ huttonOneFifthPrimeSet K) :
    p ∣ (huttonLowerRat K).den := by
  rcases (mem_huttonOneFifthPrimeSet_iff K p).1 hp with
    ⟨hpPrime, hpgt, hp10889, hpLower, h3pUpper⟩
  have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
  let k := p / 2
  have hpdef : p = 2 * k + 1 :=
    (Nat.two_mul_div_two_add_one_of_odd hpOdd).symm
  exact oneFifthPrime_dvd_huttonLowerRat_den
    K k p hpPrime hpgt hp10889 hpLower h3pUpper hpdef

theorem huttonOneFifthPrimeSet_pairwise_coprime (K : ℕ) :
    (huttonOneFifthPrimeSet K : Set ℕ).Pairwise Nat.Coprime := by
  intro p hp q hq hpq
  have hpPrime := ((mem_huttonOneFifthPrimeSet_iff K p).1 hp).1
  have hqPrime := ((mem_huttonOneFifthPrimeSet_iff K q).1 hq).1
  exact (Nat.coprime_primes hpPrime hqPrime).2 hpq

theorem huttonOneFifthPrimeProduct_dvd_huttonLowerRat_den (K : ℕ) :
    huttonOneFifthPrimeProduct K ∣ (huttonLowerRat K).den := by
  unfold huttonOneFifthPrimeProduct
  apply finset_prod_id_dvd_of_pairwise_coprime
    (huttonOneFifthPrimeSet K) (huttonLowerRat K).den
  · exact huttonOneFifthPrimeSet_pairwise_coprime K
  · exact huttonOneFifthPrime_dvd_huttonLowerRat_den K

end Theory.PiDigits.HuttonOneFifthPrimeProduct

#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonSecondBandIndex
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeCancellationFactor
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeFixedResidue
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeFixedResidue_eq_factorization
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThree_exception_prime
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeCancellationFactor_cast_zmod
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.prime_not_dvd_huttonOneThreeFixedResidue
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeCancellationFactor_not_dvd
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeCancellationFactor_ratCast_ne_zero
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeSingularBlockRat
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeRegularBlockRat
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.hutton_second_band_sign
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneThreeSingularBlockRat_eq_fraction
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.oneFifthPrime_not_dvd_other_hutton_exponent
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonLowerRat_eq_oneThreeRegular_add_singular
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.padicValRat_huttonOneThreeSingularBlockRat
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.padicValRat_huttonOneThreeRegularBlockRat_nonneg
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.padicValRat_huttonLowerRat_oneFifthPrime
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.oneFifthPrime_dvd_huttonLowerRat_den
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.padicValNat_huttonLowerRat_den_oneFifthPrime
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneFifthPrimeSet
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneFifthPrimeProduct
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.mem_huttonOneFifthPrimeSet_iff
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneFifthPrime_dvd_huttonLowerRat_den
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneFifthPrimeSet_pairwise_coprime
#print axioms Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneFifthPrimeProduct_dvd_huttonLowerRat_den
