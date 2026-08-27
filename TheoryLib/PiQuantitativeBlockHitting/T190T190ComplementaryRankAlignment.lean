import TheoryLib.PiQuantitativeBlockHitting.T189T189SignedHorizonSectorBridge

/-!
# T190: complementary rank alignment

Among the ten decimal digits, a set of at least `k` digits and a set of at
least `11 - k` digits must overlap.  Applying this elementary cardinality
fact to lower bounds for two real-valued digit scores preserves one digit as
a common witness and turns positive complementary thresholds into the two
strict inequalities needed downstream.
-/

namespace Theory.PiDigits.T190ComplementaryRankAlignment

open Finset

/-- Complementary rank bounds on ten decimal digits share a witness.  The
same digit has positive `D`-score and positive combined `G + D`-score. -/
theorem exists_digit_D_pos_and_G_add_D_pos_of_complementary_card
    (D G : Fin 10 → Real) (k : Nat) (a b : Real)
    (hk_one : 1 ≤ k) (hk_ten : k ≤ 10)
    (ha : 0 < a) (hab : 0 < a + b)
    (hD : k ≤ ((univ : Finset (Fin 10)).filter fun d ↦ a ≤ D d).card)
    (hG : 11 - k ≤
      ((univ : Finset (Fin 10)).filter fun d ↦ b ≤ G d).card) :
    ∃ d : Fin 10, 0 < D d ∧ 0 < G d + D d := by
  let SD := (univ : Finset (Fin 10)).filter fun d ↦ a ≤ D d
  let SG := (univ : Finset (Fin 10)).filter fun d ↦ b ≤ G d
  have hcard : 11 ≤ SD.card + SG.card := by
    dsimp [SD, SG]
    omega
  have hnot_disjoint : ¬ Disjoint SD SG := by
    intro hdisjoint
    have hunion_card : (SD ∪ SG).card = SD.card + SG.card :=
      card_union_of_disjoint hdisjoint
    have hunion_subset : SD ∪ SG ⊆ (univ : Finset (Fin 10)) := by
      simp [SD, SG]
    have hunion_le_ten := card_le_card hunion_subset
    rw [hunion_card] at hunion_le_ten
    simp only [card_univ, Fintype.card_fin] at hunion_le_ten
    omega
  obtain ⟨d, hdD, hdG⟩ := not_disjoint_iff.mp hnot_disjoint
  simp only [SD, mem_filter, mem_univ, true_and] at hdD
  simp only [SG, mem_filter, mem_univ, true_and] at hdG
  refine ⟨d, ?_, ?_⟩ <;> linarith

end Theory.PiDigits.T190ComplementaryRankAlignment

#print axioms
  Theory.PiDigits.T190ComplementaryRankAlignment.exists_digit_D_pos_and_G_add_D_pos_of_complementary_card
