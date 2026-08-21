import TheoryLib.PiQuantitativeBlockHitting.T61T61HuttonUpperHalfPrimeSurvival

open Finset

namespace Scratch

open Theory.PiDigits.HuttonUpperHalfPrimeSurvival

lemma oneThirdPrime_not_dvd_other_hutton_exponent
    (K k p j : ℕ)
    (hpLower : 4 * K + 3 < 3 * p)
    (hpdef : p = 2 * k + 1)
    (hj : j ∈ (range (huttonTermCount K)).erase k) :
    ¬ p ∣ 2 * j + 1 := by
  intro hdvd
  have hjlt : j < huttonTermCount K :=
    mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have hexplt : 2 * j + 1 < 3 * p := by
    unfold huttonTermCount at hjlt
    omega
  rcases hdvd with ⟨t, ht⟩
  have hpt : p * t < p * 3 := by
    rw [← ht]
    simpa [mul_comm] using hexplt
  have hpPos : 0 < p := by omega
  have htlt : t < 3 := (Nat.mul_lt_mul_left hpPos).mp hpt
  interval_cases t <;> omega

end Scratch
