import TheoryLib.PiQuantitativeBlockHitting.T65T65HuttonOneFifthPrimeProduct

open Finset

namespace T65IndependentChecks

open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonUpperHalfPrimeSurvival
open Theory.PiDigits.HuttonOneFifthPrimeProduct
open Theory.PiDigits.MachinGridStability

/-! Re-derive the four-term identity from the older T61 pair identity rather
than invoking T65's exported four-term theorem. -/
theorem fourTermCombination_replay
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

/-! Re-run the Fermat reduction without using T65's exported residue
theorem. -/
theorem fixedResidue_replay (p : ℕ) (hp : p.Prime) :
    (huttonOneThreeCancellationFactor p : ZMod p) = 21778 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [huttonOneThreeCancellationFactor, huttonCancellationFactor,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]
  rw [show 2 * p = p * 2 by omega, show 3 * p = p * 3 by omega]
  simp only [pow_mul]
  norm_num

-- The fixed residue has exactly one prime divisor above seven.
theorem onlyLargePrimeDivisor_replay
    (p : ℕ) (hp : p.Prime) (hpgt : 7 < p)
    (hdvd : (p : ℤ) ∣ huttonOneThreeCancellationFactor p) :
    p = 10889 := by
  have hz : (huttonOneThreeCancellationFactor p : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (huttonOneThreeCancellationFactor p) p).2 hdvd
  rw [fixedResidue_replay p hp] at hz
  have hdvdNat : p ∣ 2 * 10889 := by
    have hdvdInt : (p : ℤ) ∣ 2 * 10889 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * 10889) p).mp (by
        simpa using hz)
    exact_mod_cast hdvdInt
  rcases hp.dvd_mul.mp hdvdNat with h2 | h10889
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 10889)).mp h10889 with
      h1 | heq
    · exact (hp.ne_one h1).elim
    · exact heq

-- The named exception really zeros the fixed residue/cancellation factor.
example : (10889 : ℤ) ∣ huttonOneThreeCancellationFactor 10889 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd
    (huttonOneThreeCancellationFactor 10889) 10889).mp
  calc
    (huttonOneThreeCancellationFactor 10889 : ZMod 10889) = 21778 :=
      fixedResidue_replay 10889 (by norm_num)
    _ = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (21778 : ℤ) 10889).2
      (by norm_num)

-- It is arithmetically admissible at the closed endpoint R = 3*p.
example :
    3 * 10889 ≤ 4 * 8166 + 3 ∧ 4 * 8166 + 3 < 5 * 10889 := by
  norm_num

example :
    huttonSecondBandIndex 5444 < huttonTermCount 8166 := by
  norm_num [huttonSecondBandIndex, huttonTermCount]

-- Explicit parity kernel used by the erased-index argument.
lemma oddCofactorBelowFive_replay
    (k j t : ℕ)
    (heq : 2 * j + 1 = (2 * k + 1) * t)
    (htlt : t < 5) :
    t = 1 ∨ t = 3 := by
  interval_cases t <;> omega

/-! Re-prove the erased-index isolation via the explicit cofactor parity
lemma.  This checks both erased indices rather than calling T65's isolation
theorem. -/
theorem erasedIndexIsolation_replay
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
  have heq : 2 * j + 1 = (2 * k + 1) * t := by
    calc
      2 * j + 1 = p * t := ht
      _ = (2 * k + 1) * t := by rw [hpdef]
  rcases oddCofactorBelowFive_replay k j t heq htlt with ht1 | ht3
  · subst t
    apply hjne
    omega
  · subst t
    apply hjsecondne
    unfold huttonSecondBandIndex
    omega

-- Small exact set/product replay in the interior of the band.
example : huttonOneFifthPrimeSet 8 = {11} := by decide

example : huttonOneFifthPrimeProduct 8 = 11 := by decide

-- At K = 9, R = 39 = 3*13: the lower band endpoint is included.
example : huttonOneFifthPrimeSet 9 = {11, 13} := by decide

example : 13 ∈ huttonOneFifthPrimeSet 9 := by decide

example : padicValRat 13 (huttonLowerRat 9) = -1 := by
  exact padicValRat_huttonLowerRat_oneFifthPrime
    9 6 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

example : padicValNat 13 (huttonLowerRat 9).den = 1 := by
  exact padicValNat_huttonLowerRat_den_oneFifthPrime
    9 6 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

-- At K = 13, R = 55 = 5*11: strictness of R < 5*p excludes p = 11.
example : 11 ∉ huttonOneFifthPrimeSet 13 := by decide

-- At the excluded equality, exponent 5*p really remains after both erasures.
example :
    27 ∈ ((range (huttonTermCount 13)).erase 5).erase
      (huttonSecondBandIndex 5) := by decide

example : 11 ∣ 2 * 27 + 1 := by norm_num

-- Direct rational normalization, independent of the valuation theorem.
example : (huttonLowerRat 8).den % 11 = 0 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

example : (huttonLowerRat 8).den % 121 ≠ 0 := by
  norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]

end T65IndependentChecks

#print axioms
  Theory.PiDigits.HuttonOneFifthPrimeProduct.padicValRat_huttonLowerRat_oneFifthPrime
#print axioms
  Theory.PiDigits.HuttonOneFifthPrimeProduct.huttonOneFifthPrimeProduct_dvd_huttonLowerRat_den
