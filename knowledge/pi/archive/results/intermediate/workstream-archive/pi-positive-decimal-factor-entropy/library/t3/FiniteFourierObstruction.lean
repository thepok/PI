import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev
import TheoryLib.PiPositiveDecimalFactorEntropy.T1CanonicalEntropy
import TheoryLib.PiQuantitativeBlockHitting.T16T16DecimalBoundaryWordObstruction

/-!
# T3: finite Fourier obstruction for decimal factor entropy

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The Fourier transform below is unnormalized. Thus a probability distribution
has zero-frequency coefficient one. The final theorem is conditional on the
literal failure of the canonical eventual-exponential statement C1; it makes
no unconditional assertion about pi or its factor entropy.

These coefficients average over distinct occupied decimal cells. They are not
identified here with the existing time-indexed orbit sums; such an
identification would require a separate weighted transfer lemma.
-/

noncomputable section

set_option maxHeartbeats 800000

open Finset Filter Set
open scoped BigOperators ComplexConjugate

namespace DecimalFactorEntropy.FiniteFourierObstruction

open DecimalFactorComplexity

/-- The unnormalized Fourier coefficient of a real function on a finite
abelian group. Frequencies are all complex additive characters. -/
def finiteFourier {G : Type*} [AddCommGroup G] [Fintype G]
    (p : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ a : G, (p a : ℂ) * ψ a

/-- The character product occurring in the Parseval expansion. -/
lemma conj_apply_mul_apply {G : Type*} [AddCommGroup G] [Fintype G]
    (ψ : AddChar G ℂ) (a b : G) :
    conj (ψ a) * ψ b = ψ (b - a) := by
  rw [← AddChar.map_neg_eq_conj, mul_comm, ← ψ.map_add_eq_mul]
  congr 1
  abel

lemma sum_sum_sum_rotate {A B C M : Type*} [Fintype A] [Fintype B]
    [Fintype C] [AddCommMonoid M] (f : A → B → C → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [sum_comm]
  apply sum_congr rfl
  intro b _hb
  rw [sum_comm]

lemma conj_finiteFourier {G : Type*} [AddCommGroup G] [Fintype G]
    (p : G → ℝ) (ψ : AddChar G ℂ) :
    conj (finiteFourier p ψ) = ∑ a : G, (p a : ℂ) * conj (ψ a) := by
  classical
  rw [finiteFourier, map_sum]
  apply sum_congr rfl
  intro a _ha
  rw [map_mul, Complex.conj_ofReal]

lemma conj_mul_finiteFourier_eq_doubleSum
    {G : Type*} [AddCommGroup G] [Fintype G]
    (p : G → ℝ) (ψ : AddChar G ℂ) :
    conj (finiteFourier p ψ) * finiteFourier p ψ =
      ∑ a : G, ∑ b : G,
        (p a : ℂ) * conj (ψ a) * ((p b : ℂ) * ψ b) := by
  classical
  rw [conj_finiteFourier, finiteFourier, Finset.sum_mul]
  apply sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]

lemma weighted_character_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (p : G → ℝ) (a b : G) :
    (∑ ψ : AddChar G ℂ,
        (p a : ℂ) * conj (ψ a) * ((p b : ℂ) * ψ b)) =
      ((p a : ℂ) * p b) * ∑ ψ : AddChar G ℂ, ψ (b - a) := by
  classical
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro ψ _hψ
  calc
    (p a : ℂ) * conj (ψ a) * ((p b : ℂ) * ψ b) =
        ((p a : ℂ) * p b) * (conj (ψ a) * ψ b) := by ring
    _ = ((p a : ℂ) * p b) * ψ (b - a) := by
      rw [conj_apply_mul_apply]

/-- Complex-valued Parseval identity before taking real norms. -/
lemma finiteFourier_conj_mul_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (p : G → ℝ) :
    ∑ ψ : AddChar G ℂ, conj (finiteFourier p ψ) * finiteFourier p ψ =
      (Fintype.card G : ℂ) * ∑ a : G, ((p a) ^ 2 : ℂ) := by
  classical
  rw [show (∑ ψ : AddChar G ℂ,
      conj (finiteFourier p ψ) * finiteFourier p ψ) =
      ∑ ψ : AddChar G ℂ, ∑ a : G, ∑ b : G,
        (p a : ℂ) * conj (ψ a) * ((p b : ℂ) * ψ b) by
    apply sum_congr rfl
    intro ψ _hψ
    exact conj_mul_finiteFourier_eq_doubleSum p ψ]
  rw [Finset.mul_sum]
  rw [sum_sum_sum_rotate (fun (ψ : AddChar G ℂ) (a b : G) =>
    (p a : ℂ) * conj (ψ a) * ((p b : ℂ) * ψ b))]
  simp_rw [weighted_character_sum]
  simp_rw [AddChar.sum_apply_eq_ite]
  simp [sub_eq_zero]
  apply sum_congr rfl
  intro a _ha
  ring

lemma complex_cast_norm_sq (z : ℂ) :
    ((‖z‖ : ℂ) ^ 2) = conj z * z := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]

/-- Parseval for the unnormalized finite Fourier transform. -/
theorem finiteFourier_parseval {G : Type*} [AddCommGroup G] [Fintype G]
    (p : G → ℝ) :
    ∑ ψ : AddChar G ℂ, ‖finiteFourier p ψ‖ ^ 2 =
      (Fintype.card G : ℝ) * ∑ a : G, p a ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [complex_cast_norm_sq]
  exact finiteFourier_conj_mul_sum p

/-- The finite support of a real function. -/
def realSupport {G : Type*} [Fintype G] (p : G → ℝ) : Finset G :=
  Finset.univ.filter fun a => p a ≠ 0

/-- A real probability distribution on a finite type. -/
def IsProbability {G : Type*} [Fintype G] (p : G → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

lemma sum_realSupport {G : Type*} (p : G → ℝ) [Fintype G] :
    ∑ a ∈ realSupport p, p a = ∑ a, p a := by
  classical
  unfold realSupport
  rw [sum_filter]
  apply sum_congr rfl
  intro a _ha
  by_cases h : p a = 0 <;> simp [h]

lemma sum_sq_realSupport {G : Type*} (p : G → ℝ) [Fintype G] :
    ∑ a ∈ realSupport p, p a ^ 2 = ∑ a, p a ^ 2 := by
  classical
  unfold realSupport
  rw [sum_filter]
  apply sum_congr rfl
  intro a _ha
  by_cases h : p a = 0 <;> simp [h]

/-- A probability distribution supported on at most `s` points has collision
mass at least `1/s`. -/
theorem one_div_supportSize_le_sum_sq {G : Type*} [Fintype G]
    (p : G → ℝ) (s : ℕ) (hs : 0 < s)
    (hmass : ∑ a, p a = 1)
    (hsupport : (realSupport p).card ≤ s) :
    (1 : ℝ) / s ≤ ∑ a, p a ^ 2 := by
  let S := realSupport p
  have hsumS : ∑ a ∈ S, p a = 1 := by
    rw [show S = realSupport p from rfl, sum_realSupport, hmass]
  have hcs : (∑ a ∈ S, p a) ^ 2 ≤
      (S.card : ℝ) * ∑ a ∈ S, p a ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hsumS, one_pow, show S = realSupport p from rfl,
    sum_sq_realSupport] at hcs
  have hnonneg : 0 ≤ ∑ a, p a ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcard : (S.card : ℝ) ≤ s := by exact_mod_cast hsupport
  have hone : (1 : ℝ) ≤ (s : ℝ) * ∑ a, p a ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard hnonneg)
  rw [div_le_iff₀ (by exact_mod_cast hs)]
  simpa [mul_comm] using hone

/-- Parseval plus the support bound, with the ambient cell count and support
bound both explicit. -/
theorem finiteFourier_energy_ge_card_div_supportSize
    {G : Type*} [AddCommGroup G] [Fintype G]
    (p : G → ℝ) (s : ℕ) (hs : 0 < s)
    (hmass : ∑ a, p a = 1)
    (hsupport : (realSupport p).card ≤ s) :
    (Fintype.card G : ℝ) / s ≤
      ∑ ψ : AddChar G ℂ, ‖finiteFourier p ψ‖ ^ 2 := by
  rw [finiteFourier_parseval]
  have hcollision := one_div_supportSize_le_sum_sq p s hs hmass hsupport
  have hcard : 0 ≤ (Fintype.card G : ℝ) := by positivity
  calc
    (Fintype.card G : ℝ) / s =
        (Fintype.card G : ℝ) * ((1 : ℝ) / s) := by ring
    _ ≤ (Fintype.card G : ℝ) * ∑ a, p a ^ 2 :=
      mul_le_mul_of_nonneg_left hcollision hcard

/-- Some value on a nonempty finite set is at least its average, in a
division-free form. -/
lemma exists_sum_le_card_mul_of_nonempty {ι : Type*} [Fintype ι]
    (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ S, ∑ j ∈ S, f j ≤ (S.card : ℝ) * f i := by
  obtain ⟨i, hi, himax⟩ := S.exists_max_image f hS
  refine ⟨i, hi, ?_⟩
  simpa [nsmul_eq_mul] using S.sum_le_card_nsmul f (f i) himax

lemma finiteFourier_zero_of_mass_one {G : Type*} [AddCommGroup G]
    [Fintype G] (p : G → ℝ) (hmass : ∑ a, p a = 1) :
    finiteFourier p 0 = 1 := by
  simp only [finiteFourier, AddChar.zero_apply, mul_one]
  exact_mod_cast hmass

/-- Explicit nonzero-frequency obstruction on `q` cyclic cells. The
unnormalized transform has total energy at least `q/s`; after removing its
unit zero coefficient, one of the `q-1` nonzero frequencies has the displayed
squared-norm lower bound. -/
theorem zmod_exists_nonzero_frequency
    (q s : ℕ) [NeZero q] (hq : 1 < q) (hs : 0 < s)
    (p : ZMod q → ℝ) (hmass : ∑ a, p a = 1)
    (hsupport : (realSupport p).card ≤ s) :
    ∃ ψ : AddChar (ZMod q) ℂ, ψ ≠ 0 ∧
      (((q : ℝ) / s - 1) / ((q : ℝ) - 1)) ≤
        ‖finiteFourier p ψ‖ ^ 2 := by
  let energy : AddChar (ZMod q) ℂ → ℝ := fun ψ => ‖finiteFourier p ψ‖ ^ 2
  let S : Finset (AddChar (ZMod q) ℂ) := Finset.univ.erase 0
  have hcardS : S.card = q - 1 := by
    dsimp [S]
    rw [card_erase_of_mem (mem_univ 0), card_univ, AddChar.card_eq, ZMod.card]
  have hS : S.Nonempty := by
    rw [← card_pos, hcardS]
    omega
  obtain ⟨ψ, hψS, havg⟩ :=
    exists_sum_le_card_mul_of_nonempty S hS energy
  have hψ0 : ψ ≠ 0 := by
    simpa [S] using hψS
  have htotal : (q : ℝ) / s ≤ ∑ ψ, energy ψ := by
    dsimp [energy]
    simpa [ZMod.card] using
      finiteFourier_energy_ge_card_div_supportSize p s hs hmass hsupport
  have hzero : energy 0 = 1 := by
    dsimp [energy]
    rw [finiteFourier_zero_of_mass_one p hmass]
    norm_num
  have hsplit : (∑ ψ ∈ S, energy ψ) + 1 = ∑ ψ, energy ψ := by
    rw [← hzero]
    exact Finset.sum_erase_add Finset.univ energy (mem_univ 0)
  have hlower : (q : ℝ) / s - 1 ≤ ∑ ψ ∈ S, energy ψ := by
    linarith
  have hcardSreal : (S.card : ℝ) = (q : ℝ) - 1 := by
    rw [hcardS, Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  refine ⟨ψ, hψ0, ?_⟩
  rw [div_le_iff₀ (sub_pos.mpr (by exact_mod_cast hq))]
  have hcombined := hlower.trans havg
  simpa [energy, hcardSreal, mul_comm] using hcombined

/-- The complete finite cyclic-group obstruction with `q`, `s`, total
Parseval energy, and the nonzero-frequency lower bound all visible. -/
theorem zmod_probability_parseval_obstruction
    (q s : ℕ) [NeZero q] (hq : 1 < q) (hs : 0 < s)
    (p : ZMod q → ℝ) (hprob : IsProbability p)
    (hsupport : (realSupport p).card ≤ s) :
    (q : ℝ) / s ≤
        ∑ ψ : AddChar (ZMod q) ℂ, ‖finiteFourier p ψ‖ ^ 2 ∧
      ∃ ψ : AddChar (ZMod q) ℂ, ψ ≠ 0 ∧
        (((q : ℝ) / s - 1) / ((q : ℝ) - 1)) ≤
          ‖finiteFourier p ψ‖ ^ 2 := by
  constructor
  · simpa [ZMod.card] using
      finiteFourier_energy_ge_card_div_supportSize
        p s hs hprob.2 hsupport
  · exact zmod_exists_nonzero_frequency q s hq hs p hprob.2 hsupport

/-- A real upper bound `B` for the support-size parameter gives a lower bound
depending only on `q` and `B`. -/
theorem zmod_probability_exists_nonzero_of_supportSize_le_real
    (q s : ℕ) [NeZero q] (hq : 1 < q) (hs : 0 < s)
    (p : ZMod q → ℝ) (hprob : IsProbability p)
    (hsupport : (realSupport p).card ≤ s)
    (B : ℝ) (hB : (s : ℝ) ≤ B) :
    ∃ ψ : AddChar (ZMod q) ℂ, ψ ≠ 0 ∧
      (((q : ℝ) / B - 1) / ((q : ℝ) - 1)) ≤
        ‖finiteFourier p ψ‖ ^ 2 := by
  obtain ⟨ψ, hψ0, hψ⟩ :=
    zmod_exists_nonzero_frequency q s hq hs p hprob.2 hsupport
  refine ⟨ψ, hψ0, ?_⟩
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hquot : (q : ℝ) / B ≤ (q : ℝ) / s :=
    div_le_div_of_nonneg_left hqnonneg hspos hB
  have hqreal : (1 : ℝ) < q := by exact_mod_cast hq
  have hden : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hdiv := (div_le_div_iff_of_pos_right hden).2
    (sub_le_sub_right hquot 1)
  exact hdiv.trans hψ

/-- Natural base-ten label of a length-`n` decimal block, regarded modulo the
number `10^n` of decimal cells. -/
def decimalBlockCode {n : ℕ} (w : Block (Fin 10) n) : ZMod (10 ^ n) :=
  Theory.PiDigits.T20.wordValue (List.ofFn w)

theorem decimalBlockCode_injective (n : ℕ) :
    Function.Injective (decimalBlockCode (n := n)) := by
  intro u v huv
  have hvalue := congrArg ZMod.val huv
  change
    (Theory.PiDigits.T20.wordValue (List.ofFn u) : ZMod (10 ^ n)).val =
      (Theory.PiDigits.T20.wordValue (List.ofFn v) : ZMod (10 ^ n)).val at hvalue
  have hu_lt : Theory.PiDigits.T20.wordValue (List.ofFn u) < 10 ^ n := by
    simpa using Theory.PiDigits.T20.wordValue_lt_pow_length (List.ofFn u)
  have hv_lt : Theory.PiDigits.T20.wordValue (List.ofFn v) < 10 ^ n := by
    simpa using Theory.PiDigits.T20.wordValue_lt_pow_length (List.ofFn v)
  rw [ZMod.val_natCast_of_lt hu_lt, ZMod.val_natCast_of_lt hv_lt] at hvalue
  have hlists : List.ofFn u = List.ofFn v :=
    Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_injective_of_length
      (by simp) hvalue
  exact List.ofFn_inj.mp hlists

/-- Natural decimal-cell label of an occurring factor. -/
def factorCellCode (x : Stream (Fin 10)) (n : ℕ) :
    Factor x n → ZMod (10 ^ n) :=
  fun w => decimalBlockCode w.1

theorem factorCellCode_injective (x : Stream (Fin 10)) (n : ℕ) :
    Function.Injective (factorCellCode x n) := by
  intro u v huv
  apply Subtype.ext
  exact decimalBlockCode_injective n huv

noncomputable instance factorFintype (x : Stream (Fin 10)) (n : ℕ) :
    Fintype (Factor x n) := Fintype.ofFinite (Factor x n)

/-- The occupied length-`n` decimal cells of a stream. -/
def factorCellSet (x : Stream (Fin 10)) (n : ℕ) : Finset (ZMod (10 ^ n)) :=
  Finset.univ.image (factorCellCode x n)

theorem factorCellSet_card (x : Stream (Fin 10)) (n : ℕ) :
    (factorCellSet x n).card = canonicalFactorComplexity x n := by
  classical
  rw [factorCellSet, card_image_iff.mpr]
  · simp [canonicalFactorComplexity, Nat.card_eq_fintype_card]
  · exact (factorCellCode_injective x n).injOn

/-- Uniform probability on the distinct occupied length-`n` decimal cells. -/
def factorCellDistribution (x : Stream (Fin 10)) (n : ℕ)
    (a : ZMod (10 ^ n)) : ℝ :=
  if a ∈ factorCellSet x n then ((factorCellSet x n).card : ℝ)⁻¹ else 0

theorem factorCellDistribution_mass_one (x : Stream (Fin 10)) (n : ℕ) :
    ∑ a, factorCellDistribution x n a = 1 := by
  classical
  have hp : (canonicalFactorComplexity x n : ℝ) ≠ 0 := by
    exact_mod_cast
      (DecimalFactorEntropy.canonicalFactorComplexity_pos x n).ne'
  simp [factorCellDistribution, factorCellSet_card, hp]

theorem factorCellDistribution_isProbability (x : Stream (Fin 10)) (n : ℕ) :
    IsProbability (factorCellDistribution x n) := by
  refine ⟨?_, factorCellDistribution_mass_one x n⟩
  intro a
  unfold factorCellDistribution
  split_ifs <;> positivity

theorem realSupport_factorCellDistribution (x : Stream (Fin 10)) (n : ℕ) :
    realSupport (factorCellDistribution x n) = factorCellSet x n := by
  classical
  have hp : canonicalFactorComplexity x n ≠ 0 :=
    (DecimalFactorEntropy.canonicalFactorComplexity_pos x n).ne'
  ext a
  simp [realSupport, factorCellDistribution, factorCellSet_card, hp]

theorem factorCellDistribution_support_card (x : Stream (Fin 10)) (n : ℕ) :
    (realSupport (factorCellDistribution x n)).card =
      canonicalFactorComplexity x n := by
  rw [realSupport_factorCellDistribution, factorCellSet_card]

/-- The cell-label Fourier coefficient of the uniform distribution on the
distinct occurring length-`n` factors. -/
def factorCellFourier (x : Stream (Fin 10)) (n : ℕ)
    (ψ : AddChar (ZMod (10 ^ n)) ℂ) : ℂ :=
  finiteFourier (factorCellDistribution x n) ψ

/-- At every positive length, a stream with factor complexity `s` has a
nonzero decimal-cell frequency satisfying the exact support-size bound. -/
theorem exists_nonzero_factorCell_frequency (x : Stream (Fin 10))
    (n : ℕ) (hn : 0 < n) :
    ∃ ψ : AddChar (ZMod (10 ^ n)) ℂ, ψ ≠ 0 ∧
      (((10 ^ n : ℕ) : ℝ) /
          canonicalFactorComplexity x n - 1) /
            (((10 ^ n : ℕ) : ℝ) - 1) ≤
        ‖factorCellFourier x n ψ‖ ^ 2 := by
  have hq : 1 < 10 ^ n := by
    have : 10 ≤ 10 ^ n := by
      simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hn
    omega
  have hs : 0 < canonicalFactorComplexity x n :=
    DecimalFactorEntropy.canonicalFactorComplexity_pos x n
  have hsupport :
      (realSupport (factorCellDistribution x n)).card ≤
        canonicalFactorComplexity x n := by
    rw [factorCellDistribution_support_card]
  simpa [factorCellFourier] using
    zmod_exists_nonzero_frequency (10 ^ n) (canonicalFactorComplexity x n)
      hq hs (factorCellDistribution x n)
      (factorCellDistribution_mass_one x n) hsupport

/-- Replace the exact factor-complexity denominator by any real upper bound
`B`; this is the form used with a subexponential complexity estimate. -/
theorem exists_nonzero_factorCell_frequency_of_complexity_le
    (x : Stream (Fin 10)) (n : ℕ) (hn : 0 < n) (B : ℝ)
    (hcomplexity : (canonicalFactorComplexity x n : ℝ) ≤ B) :
    ∃ ψ : AddChar (ZMod (10 ^ n)) ℂ, ψ ≠ 0 ∧
      ((((10 ^ n : ℕ) : ℝ) / B - 1) /
          (((10 ^ n : ℕ) : ℝ) - 1)) ≤
        ‖factorCellFourier x n ψ‖ ^ 2 := by
  have hq : 1 < 10 ^ n := by
    have : 10 ≤ 10 ^ n := by
      simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hn
    omega
  have hs : 0 < canonicalFactorComplexity x n :=
    DecimalFactorEntropy.canonicalFactorComplexity_pos x n
  have hsupport :
      (realSupport (factorCellDistribution x n)).card ≤
        canonicalFactorComplexity x n := by
    rw [factorCellDistribution_support_card]
  simpa [factorCellFourier] using
    zmod_probability_exists_nonzero_of_supportSize_le_real
      (10 ^ n) (canonicalFactorComplexity x n) hq hs
      (factorCellDistribution x n) (factorCellDistribution_isProbability x n)
      hsupport B hcomplexity

/-- Explicit all-rates formulation of subexponential factor complexity. -/
def SubexponentialFactorComplexity (x : Stream (Fin 10)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (canonicalFactorComplexity x n : ℝ) < (10 : ℝ) ^ (ε * (n : ℝ))

/-- Failure of eventual exponential growth forces the factor complexity below
every fixed positive exponential rate at every sufficiently large length. -/
theorem not_eventuallyExponential_implies_subexponential
    (x : Stream (Fin 10))
    (hfailure : ¬ DecimalFactorEntropy.EventuallyExponentialFactorGrowth x) :
    SubexponentialFactorComplexity x := by
  have hnotpos : ¬ 0 < DecimalFactorEntropy.entropyBaseTen x := by
    intro hpos
    exact hfailure
      ((DecimalFactorEntropy.positive_entropy_iff_eventually_exponential x).mp hpos)
  have hentropy : DecimalFactorEntropy.entropyBaseTen x ≤ 0 := le_of_not_gt hnotpos
  intro ε hε
  have hlimit : DecimalFactorEntropy.entropyBaseTen x < ε := hentropy.trans_lt hε
  have hevent : ∀ᶠ n : ℕ in atTop,
      DecimalFactorEntropy.entropyRatio x n < ε :=
    (DecimalFactorEntropy.entropyRatio_tendsto x).eventually
      (Iio_mem_nhds hlimit)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro n hn
  have hnN₀ : N₀ ≤ n := (le_max_right 1 N₀).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 N₀).trans hn)
  have hratio := hN₀ n hnN₀
  rw [DecimalFactorEntropy.entropyRatio] at hratio
  have hden : 0 < (n : ℝ) * Real.log 10 :=
    mul_pos (by exact_mod_cast hnpos) (Real.log_pos (by norm_num))
  have hlog :
      Real.log (canonicalFactorComplexity x n : ℝ) <
        ε * ((n : ℝ) * Real.log 10) :=
    (div_lt_iff₀ hden).mp hratio
  have hp : (0 : ℝ) < canonicalFactorComplexity x n := by
    exact_mod_cast DecimalFactorEntropy.canonicalFactorComplexity_pos x n
  apply (Real.lt_rpow_iff_log_lt hp (by norm_num)).2
  simpa [mul_assoc] using hlog

/-- Conditional pi specialization. Literal failure of current C1 gives, for
every positive rate, one threshold after which both the subexponential factor
bound and an explicit nonzero cell-label Fourier obstruction hold at every
length. The premise is not proved here. -/
theorem pi_failure_C1_implies_eventual_nonzero_factorCell_frequency
    (hfailure :
      ¬ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        (10 : ℝ) ^ (η * (n : ℝ)) ≤
          (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ) <
          (10 : ℝ) ^ (ε * (n : ℝ)) ∧
        ∃ ψ : AddChar (ZMod (10 ^ n)) ℂ, ψ ≠ 0 ∧
          (((10 ^ n : ℕ) : ℝ) /
              ((10 : ℝ) ^ (ε * (n : ℝ))) - 1) /
                (((10 ^ n : ℕ) : ℝ) - 1) ≤
            ‖factorCellFourier Theory.PiDigits.piDigit n ψ‖ ^ 2 := by
  have hfailure' :
      ¬ DecimalFactorEntropy.EventuallyExponentialFactorGrowth
        Theory.PiDigits.piDigit := by
    simpa [DecimalFactorEntropy.EventuallyExponentialFactorGrowth,
      Theory.PiDigits.FactorComplexity.piFactorComplexity] using hfailure
  have hsub := not_eventuallyExponential_implies_subexponential
    Theory.PiDigits.piDigit hfailure'
  intro ε hε
  obtain ⟨N, hN, hbound⟩ := hsub ε hε
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hN.trans hn)
  have hcomplexity :
      (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ) <
        (10 : ℝ) ^ (ε * (n : ℝ)) := by
    simpa [Theory.PiDigits.FactorComplexity.piFactorComplexity] using hbound n hn
  constructor
  · exact hcomplexity
  · simpa [Theory.PiDigits.FactorComplexity.piFactorComplexity] using
      exists_nonzero_factorCell_frequency_of_complexity_le
        Theory.PiDigits.piDigit n hnpos
        ((10 : ℝ) ^ (ε * (n : ℝ))) hcomplexity.le

end DecimalFactorEntropy.FiniteFourierObstruction

#print axioms DecimalFactorEntropy.FiniteFourierObstruction.finiteFourier_parseval
#print axioms DecimalFactorEntropy.FiniteFourierObstruction.one_div_supportSize_le_sum_sq
#print axioms DecimalFactorEntropy.FiniteFourierObstruction.zmod_probability_parseval_obstruction
#print axioms DecimalFactorEntropy.FiniteFourierObstruction.factorCellSet_card
#print axioms DecimalFactorEntropy.FiniteFourierObstruction.exists_nonzero_factorCell_frequency
#print axioms DecimalFactorEntropy.FiniteFourierObstruction.not_eventuallyExponential_implies_subexponential
#print axioms DecimalFactorEntropy.FiniteFourierObstruction.pi_failure_C1_implies_eventual_nonzero_factorCell_frequency
