import TheoryLib.PiQuantitativeBlockHitting.T62T62HuttonEligiblePrimeProduct

/-!
# T63: exact five-adic transient in the rational Hutton shadows

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Put `R = 4*K+3` and choose the unique `e` with
`5^e <= R < 5^(e+1)`.  Among the odd exponents at most `R`, the only
ones of five-adic order `e` are `5^e` and, when it lies in the prefix,
`3*5^e`.  After scaling by `5^e`, their residues modulo five are `3`
and `1`, respectively, so the minimum layer never cancels.  Consequently

`padicValRat 5 (huttonLowerRat K) = -e`

and the reduced denominator contains five to exact multiplicity `e`.
The result includes `K=0`, where `e=0`.

This is exact denominator arithmetic.  It proves no decimal-cylinder hit,
prefix discrepancy, distribution statement, or every-word theorem for pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.HuttonFiveAdicTransient

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.HuttonRationalShadow
open Theory.PiDigits.HuttonAdjacentIncrement
open Theory.PiDigits.HuttonUpperHalfPrimeSurvival

/-- The two Hutton terms sharing Taylor index `k`, combined as one rational. -/
def huttonPairRat (k : ℕ) : ℚ :=
  huttonThreeTermRat k + huttonSevenTermRat k

/-- The Hutton cancellation factor at an odd exponent is always a five-unit. -/
lemma five_not_dvd_huttonCancellationFactor (p : ℕ) (hp : Odd p) :
    ¬ 5 ∣ huttonCancellationFactor p := by
  intro hd
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz : ((huttonCancellationFactor p : ℕ) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hd
  have hcast : ((huttonCancellationFactor p : ℕ) : ZMod 5) = 2 ^ p := by
    unfold huttonCancellationFactor
    push_cast
    have h7 : (7 : ZMod 5) = 2 := by decide
    have h3 : (3 : ZMod 5) = -2 := by decide
    rw [h7, h3, hp.neg_pow]
    ring
  rw [hcast] at hz
  exact (pow_ne_zero p (by decide : (2 : ZMod 5) ≠ 0)) hz

/-- Closed fraction for a combined Hutton pair. -/
lemma huttonPairRat_eq_fraction (k : ℕ) :
    huttonPairRat k =
      4 * (-1 : ℚ) ^ k *
        (huttonCancellationFactor (2 * k + 1) : ℚ) /
      (((2 * k + 1 : ℕ) : ℚ) *
        3 ^ (2 * k + 1) * 7 ^ (2 * k + 1)) := by
  unfold huttonPairRat
  exact hutton_singular_pair_eq (2 * k + 1) k rfl

/-- A combined Hutton pair has valuation minus the five-adic order of its
odd linear exponent. -/
theorem padicValRat_five_huttonPairRat (k : ℕ) :
    padicValRat 5 (huttonPairRat k) =
      -(padicValNat 5 (2 * k + 1) : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [huttonPairRat_eq_fraction]
  have hrq : ((2 * k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have h3q : (3 : ℚ) ≠ 0 := by norm_num
  have h7q : (7 : ℚ) ≠ 0 := by norm_num
  have hfactorNat : huttonCancellationFactor (2 * k + 1) ≠ 0 := by
    unfold huttonCancellationFactor
    positivity
  have hfactorQ :
      (huttonCancellationFactor (2 * k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast hfactorNat
  have hnum0 :
      4 * (-1 : ℚ) ^ k *
        (huttonCancellationFactor (2 * k + 1) : ℚ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hfactorQ
  have hden0 :
      ((2 * k + 1 : ℕ) : ℚ) *
          3 ^ (2 * k + 1) * 7 ^ (2 * k + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hrq (pow_ne_zero _ h3q))
      (pow_ne_zero _ h7q)
  have hval4 : padicValRat 5 (4 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalNegOne : padicValRat 5 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num
  have hvalFactor :
      padicValRat 5
          (huttonCancellationFactor (2 * k + 1) : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd
      (five_not_dvd_huttonCancellationFactor
        (2 * k + 1) ⟨k, by omega⟩)
  have hval3 : padicValRat 5 (3 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hval7 : padicValRat 5 (7 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd (by norm_num)
  have hvalr :
      padicValRat 5 (((2 * k + 1 : ℕ) : ℚ)) =
        (padicValNat 5 (2 * k + 1) : ℤ) := by
    rw [padicValRat.of_nat]
  rw [padicValRat.div hnum0 hden0,
    padicValRat.mul
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hfactorQ,
    padicValRat.mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    padicValRat.pow (by norm_num), hval4, hvalNegOne, hvalFactor,
    padicValRat.mul (mul_ne_zero hrq (pow_ne_zero _ h3q))
      (pow_ne_zero _ h7q),
    padicValRat.mul hrq (pow_ne_zero _ h3q), hvalr,
    padicValRat.pow h3q, hval3, padicValRat.pow h7q, hval7]
  norm_num

/-- Below `5^(e+1)`, a nonzero integer has five-adic order at most `e`. -/
lemma padicValNat_five_le_of_lt_pow_succ
    (u e : ℕ) (hu : u ≠ 0) (hlt : u < 5 ^ (e + 1)) :
    padicValNat 5 u ≤ e := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra hnot
  have he : e + 1 ≤ padicValNat 5 u := by omega
  have hdvd : 5 ^ (e + 1) ∣ u :=
    (padicValNat_dvd_iff_le hu).2 he
  have hle : 5 ^ (e + 1) ≤ u :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hdvd
  omega

/-- In an interval ending before `5^(e+1)`, an odd exponent of exact
five-adic order `e` is either `5^e` or `3*5^e`. -/
lemma odd_maximal_five_adic_shape
    (u R e : ℕ) (hu : 0 < u) (huodd : Odd u)
    (huR : u ≤ R) (hhigh : R < 5 ^ (e + 1))
    (hval : padicValNat 5 u = e) :
    u = 5 ^ e ∨ u = 3 * 5 ^ e := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : 5 ^ e ∣ u :=
    (padicValNat_dvd_iff_le (Nat.ne_of_gt hu)).2 (by omega)
  obtain ⟨c, hc⟩ := hdvd
  have hpowpos : 0 < 5 ^ e := by positivity
  have hcpos : 0 < c := by
    by_contra hnot
    have hczero : c = 0 := by omega
    simp [hczero] at hc
    omega
  have hclt : c < 5 := by
    rw [pow_succ] at hhigh
    rw [hc] at huR
    have hmullt : 5 ^ e * c < 5 ^ e * 5 := by omega
    exact (Nat.mul_lt_mul_left hpowpos).mp hmullt
  rcases huodd with ⟨t, ht⟩
  interval_cases c
  · left
    simpa using hc
  · omega
  · right
    omega
  · omega

/-- Every power of five is one modulo four, with an explicit quotient. -/
lemma five_pow_eq_four_mul_add_one (e : ℕ) :
    ∃ t : ℕ, 5 ^ e = 4 * t + 1 := by
  induction e with
  | zero => exact ⟨0, by norm_num⟩
  | succ e ih =>
      rcases ih with ⟨t, ht⟩
      exact ⟨5 * t + 1, by rw [pow_succ, ht]; ring⟩

/-- Indices of the two possible minimum-layer exponents, including their
parities and hence the signs of their Hutton terms. -/
lemma fivePrimaryIndices (e : ℕ) :
    ∃ k l : ℕ,
      5 ^ e = 2 * k + 1 ∧ Even k ∧
      3 * 5 ^ e = 2 * l + 1 ∧ Odd l := by
  rcases five_pow_eq_four_mul_add_one e with ⟨t, ht⟩
  refine ⟨2 * t, 6 * t + 1, ?_, ⟨t, by omega⟩, ?_, ⟨3 * t, by omega⟩⟩
  · omega
  · omega

/-- Any pair outside the two possible minimum-layer exponents has valuation
at least `1-e`. -/
lemma padicValRat_five_regularPair_ge
    (j R e : ℕ)
    (huR : 2 * j + 1 ≤ R)
    (hhigh : R < 5 ^ (e + 1))
    (hne1 : 2 * j + 1 ≠ 5 ^ e)
    (hne3 : 2 * j + 1 ≠ 3 * 5 ^ e) :
    (1 : ℤ) - e ≤ padicValRat 5 (huttonPairRat j) := by
  have hu : 0 < 2 * j + 1 := by omega
  have hult : 2 * j + 1 < 5 ^ (e + 1) :=
    lt_of_le_of_lt huR hhigh
  have hle :=
    padicValNat_five_le_of_lt_pow_succ
      (2 * j + 1) e (by omega) hult
  have hne : padicValNat 5 (2 * j + 1) ≠ e := by
    intro heq
    rcases odd_maximal_five_adic_shape
        (2 * j + 1) R e hu ⟨j, by omega⟩ huR hhigh heq with
      h1 | h3
    · exact hne1 h1
    · exact hne3 h3
  have hlt : padicValNat 5 (2 * j + 1) < e := by omega
  rw [padicValRat_five_huttonPairRat]
  exact_mod_cast (show (1 : ℤ) - e ≤
      -(padicValNat 5 (2 * j + 1) : ℤ) by omega)

/-- A finite sum of rationals above a common five-adic threshold is either
zero or remains above that threshold. -/
lemma padicValRat_five_sum_lower
    {S : Finset ℕ} (f : ℕ → ℚ) (c : ℤ)
    (hf : ∀ x ∈ S, c ≤ padicValRat 5 (f x)) :
    (∑ x ∈ S, f x) = 0 ∨
      c ≤ padicValRat 5 (∑ x ∈ S, f x) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hxs ih =>
      rw [sum_insert hxs]
      have hxval := hf x (mem_insert_self x S)
      have hsprop := ih (fun y hy => hf y (mem_insert_of_mem hy))
      by_cases hx0 : f x = 0
      · simpa [hx0] using hsprop
      by_cases hs0 : (∑ y ∈ S, f y) = 0
      · simp [hs0, hx0, hxval]
      rcases hsprop with hsprop | hsval
      · exact False.elim (hs0 hsprop)
      by_cases hsum0 : f x + ∑ y ∈ S, f y = 0
      · exact Or.inl hsum0
      · refine Or.inr (le_trans (le_min hxval hsval) ?_)
        exact padicValRat.min_le_padicValRat_add hsum0

/-- The prefix after removing the `5^e`-indexed minimum pair. -/
def huttonFiveRegularOneRat (K k : ℕ) : ℚ :=
  ∑ j ∈ (range (huttonTermCount K)).erase k, huttonPairRat j

/-- The prefix after removing both possible minimum-layer pairs. -/
def huttonFiveRegularTwoRat (K k l : ℕ) : ℚ :=
  ∑ j ∈ ((range (huttonTermCount K)).erase k).erase l,
    huttonPairRat j

/-- The lower Hutton shadow is the sum of its combined equal-index pairs. -/
theorem huttonLowerRat_eq_pair_sum (K : ℕ) :
    huttonLowerRat K =
      ∑ j ∈ range (huttonTermCount K), huttonPairRat j := by
  rw [huttonLowerRat_eq_term_sums, ← sum_add_distrib]
  rfl

/-- Exact one-minimum-layer decomposition. -/
lemma huttonLowerRat_eq_regularOne_add
    (K k : ℕ) (hk : k < huttonTermCount K) :
    huttonLowerRat K = huttonFiveRegularOneRat K k + huttonPairRat k := by
  have hm : k ∈ range (huttonTermCount K) := mem_range.2 hk
  rw [huttonLowerRat_eq_pair_sum]
  unfold huttonFiveRegularOneRat
  exact (sum_erase_add (range (huttonTermCount K)) huttonPairRat hm).symm

/-- Exact two-minimum-layer decomposition. -/
lemma huttonLowerRat_eq_regularTwo_add
    (K k l : ℕ)
    (hk : k < huttonTermCount K) (hl : l < huttonTermCount K)
    (hkl : k ≠ l) :
    huttonLowerRat K =
      huttonFiveRegularTwoRat K k l +
        (huttonPairRat k + huttonPairRat l) := by
  have hkm : k ∈ range (huttonTermCount K) := mem_range.2 hk
  have hlm : l ∈ (range (huttonTermCount K)).erase k := by
    exact mem_erase.2 ⟨hkl.symm, mem_range.2 hl⟩
  have h1 :=
    sum_erase_add (range (huttonTermCount K)) huttonPairRat hkm
  have h2 :=
    sum_erase_add ((range (huttonTermCount K)).erase k) huttonPairRat hlm
  rw [huttonLowerRat_eq_pair_sum, ← h1, ← h2]
  unfold huttonFiveRegularTwoRat
  ring

/-- In the one-minimum case, the regular remainder is zero or has valuation
at least `1-e`. -/
lemma padicValRat_huttonFiveRegularOne_ge_or_zero
    (K e k : ℕ)
    (hhigh : 4 * K + 3 < 5 ^ (e + 1))
    (hk : 5 ^ e = 2 * k + 1)
    (hthree : 4 * K + 3 < 3 * 5 ^ e) :
    huttonFiveRegularOneRat K k = 0 ∨
      (1 : ℤ) - e ≤
        padicValRat 5 (huttonFiveRegularOneRat K k) := by
  unfold huttonFiveRegularOneRat
  apply padicValRat_five_sum_lower
  intro j hj
  have hjlt : j < huttonTermCount K :=
    mem_range.1 (mem_of_mem_erase hj)
  have hjne : j ≠ k := ne_of_mem_erase hj
  have huR : 2 * j + 1 ≤ 4 * K + 3 := by
    unfold huttonTermCount at hjlt
    omega
  apply padicValRat_five_regularPair_ge j (4 * K + 3) e
  · exact huR
  · exact hhigh
  · intro heq
    apply hjne
    omega
  · intro heq
    omega

/-- In the two-minimum case, the regular remainder is zero or has valuation
at least `1-e`. -/
lemma padicValRat_huttonFiveRegularTwo_ge_or_zero
    (K e k l : ℕ)
    (hhigh : 4 * K + 3 < 5 ^ (e + 1))
    (hk : 5 ^ e = 2 * k + 1)
    (hl : 3 * 5 ^ e = 2 * l + 1) :
    huttonFiveRegularTwoRat K k l = 0 ∨
      (1 : ℤ) - e ≤
        padicValRat 5 (huttonFiveRegularTwoRat K k l) := by
  unfold huttonFiveRegularTwoRat
  apply padicValRat_five_sum_lower
  intro j hj
  have hj0 : j ∈ (range (huttonTermCount K)).erase k :=
    mem_of_mem_erase hj
  have hjlt : j < huttonTermCount K :=
    mem_range.1 (mem_of_mem_erase hj0)
  have hjnel : j ≠ l := ne_of_mem_erase hj
  have hjnek : j ≠ k := ne_of_mem_erase hj0
  apply padicValRat_five_regularPair_ge j (4 * K + 3) e
  · unfold huttonTermCount at hjlt
    omega
  · exact hhigh
  · intro heq
    apply hjnek
    omega
  · intro heq
    apply hjnel
    omega

/-- Every combined Hutton pair is nonzero. -/
lemma huttonPairRat_ne_zero (k : ℕ) : huttonPairRat k ≠ 0 := by
  rw [huttonPairRat_eq_fraction]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
    · exact_mod_cast
        (show huttonCancellationFactor (2 * k + 1) ≠ 0 by
          unfold huttonCancellationFactor
          positivity)
  · exact mul_ne_zero
      (mul_ne_zero (by positivity) (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by norm_num))

/-- Adding a remainder at least one valuation step above a nonzero minimum
layer preserves the minimum valuation. -/
lemma padicValRat_add_eq_minLayer
    (minimal regular : ℚ) (e : ℕ)
    (hmin : padicValRat 5 minimal = -(e : ℤ))
    (hmin0 : minimal ≠ 0)
    (hreg : regular = 0 ∨
      (1 : ℤ) - e ≤ padicValRat 5 regular) :
    padicValRat 5 (regular + minimal) = -(e : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hreg0 : regular = 0
  · simpa [hreg0] using hmin
  have hregval := hreg.resolve_left hreg0
  have hsum0 : minimal + regular ≠ 0 := by
    intro hzero
    have heq : regular = -minimal := by linarith
    have hvals := congrArg (padicValRat 5) heq
    rw [padicValRat.neg, hmin] at hvals
    omega
  rw [add_comm]
  calc
    padicValRat 5 (minimal + regular) = padicValRat 5 minimal := by
      apply padicValRat.add_eq_of_lt hsum0 hmin0 hreg0
      rw [hmin]
      omega
    _ = -(e : ℤ) := hmin

/-- Integer numerator of the two-pair minimum layer after multiplication by
`5^e` and passage to one common five-unit denominator. -/
def fiveMinimumLayerNumerator (e : ℕ) : ℤ :=
  let L := 5 ^ e
  4 * (3 * (huttonCancellationFactor L : ℤ) *
      3 ^ (2 * L) * 7 ^ (2 * L) -
    (huttonCancellationFactor (3 * L) : ℤ))

/-- Common denominator of the scaled two-pair minimum layer. -/
def fiveMinimumLayerDenominator (e : ℕ) : ℕ :=
  let L := 5 ^ e
  3 * 3 ^ (3 * L) * 7 ^ (3 * L)

/-- Frobenius iteration in `ZMod 5`: raising to `5^e` fixes every residue. -/
lemma zmod_five_pow_five_pow (a : ZMod 5) (e : ℕ) :
    a ^ (5 ^ e) = a := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

/-- The common numerator of the scaled two-pair layer is `2` modulo five,
so the residues `3` and `1` do not cancel. -/
theorem fiveMinimumLayerNumerator_cast_zmod (e : ℕ) :
    (fiveMinimumLayerNumerator e : ZMod 5) = 2 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let L := 5 ^ e
  have hL3 : (3 : ZMod 5) ^ L = 3 :=
    zmod_five_pow_five_pow 3 e
  have hL7 : (7 : ZMod 5) ^ L = 7 :=
    zmod_five_pow_five_pow 7 e
  have hF1 : (huttonCancellationFactor L : ZMod 5) = 2 := by
    change ((huttonCancellationFactor L : ℕ) : ZMod 5) = 2
    unfold huttonCancellationFactor L
    push_cast
    rw [show (7 : ZMod 5) ^ (5 ^ e) = 7 by
        exact zmod_five_pow_five_pow 7 e,
      show (3 : ZMod 5) ^ (5 ^ e) = 3 by
        exact zmod_five_pow_five_pow 3 e]
    decide
  have hF3 :
      (huttonCancellationFactor (3 * L) : ZMod 5) = 3 := by
    change ((huttonCancellationFactor (3 * L) : ℕ) : ZMod 5) = 3
    unfold huttonCancellationFactor
    push_cast
    rw [show (7 : ZMod 5) ^ (3 * L) = 7 ^ 3 by
        rw [Nat.mul_comm, pow_mul, hL7],
      show (3 : ZMod 5) ^ (3 * L) = 3 ^ 3 by
        rw [Nat.mul_comm, pow_mul, hL3]]
    decide
  unfold fiveMinimumLayerNumerator
  dsimp only
  push_cast
  rw [hF1, hF3,
    show (3 : ZMod 5) ^ (2 * L) = 3 ^ 2 by
      rw [Nat.mul_comm, pow_mul, hL3],
    show (7 : ZMod 5) ^ (2 * L) = 7 ^ 2 by
      rw [Nat.mul_comm, pow_mul, hL7]]
  decide

/-- Exact common-fraction identity for the scaled two-pair minimum layer. -/
theorem five_minimum_two_scaled_eq
    (e k l : ℕ)
    (hk : 5 ^ e = 2 * k + 1)
    (hl : 3 * 5 ^ e = 2 * l + 1)
    (hkEven : Even k) (hlOdd : Odd l) :
    (5 ^ e : ℚ) * (huttonPairRat k + huttonPairRat l) =
      (fiveMinimumLayerNumerator e : ℚ) /
        fiveMinimumLayerDenominator e := by
  let L := 5 ^ e
  have hL : L = 2 * k + 1 := hk
  have h3L : 3 * L = 2 * l + 1 := hl
  rw [show huttonPairRat k =
      4 * (-1 : ℚ) ^ k * (huttonCancellationFactor L : ℚ) /
        ((L : ℚ) * 3 ^ L * 7 ^ L) by
      unfold huttonPairRat
      exact hutton_singular_pair_eq L k hL,
    show huttonPairRat l =
      4 * (-1 : ℚ) ^ l *
          (huttonCancellationFactor (3 * L) : ℚ) /
        (((3 * L : ℕ) : ℚ) *
          3 ^ (3 * L) * 7 ^ (3 * L)) by
      unfold huttonPairRat
      exact hutton_singular_pair_eq (3 * L) l h3L,
    hkEven.neg_one_pow, hlOdd.neg_one_pow]
  have hLcast : (5 : ℚ) ^ e = (L : ℚ) := by norm_num [L]
  rw [hLcast]
  change (L : ℚ) *
    (4 * 1 * (huttonCancellationFactor L : ℚ) /
        ((L : ℚ) * 3 ^ L * 7 ^ L) +
      4 * -1 * (huttonCancellationFactor (3 * L) : ℚ) /
        (((3 * L : ℕ) : ℚ) *
          3 ^ (3 * L) * 7 ^ (3 * L))) =
      (fiveMinimumLayerNumerator e : ℚ) /
        fiveMinimumLayerDenominator e
  unfold fiveMinimumLayerNumerator fiveMinimumLayerDenominator
  dsimp only
  push_cast
  dsimp [L] at *
  have hL0 : (L : ℚ) ≠ 0 := by positivity
  have h30 : (3 : ℚ) ≠ 0 := by norm_num
  have h70 : (7 : ℚ) ≠ 0 := by norm_num
  field_simp
  rw [show 3 * (5 ^ e) = 5 ^ e + 2 * (5 ^ e) by omega,
    pow_add, pow_add]
  ring

/-- The two-pair common numerator is a five-unit. -/
lemma five_not_dvd_minimumLayerNumerator (e : ℕ) :
    ¬ (5 : ℤ) ∣ fiveMinimumLayerNumerator e := by
  intro hd
  have hz : (fiveMinimumLayerNumerator e : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
  rw [fiveMinimumLayerNumerator_cast_zmod] at hz
  exact (by decide : (2 : ZMod 5) ≠ 0) hz

/-- The two-pair common denominator is a five-unit. -/
lemma five_not_dvd_minimumLayerDenominator (e : ℕ) :
    ¬ 5 ∣ fiveMinimumLayerDenominator e := by
  have hp : Nat.Prime 5 := by norm_num
  have h3 : ¬ 5 ∣ 3 ^ (3 * 5 ^ e) := by
    intro hd
    exact (by norm_num : ¬ 5 ∣ 3) (hp.dvd_of_dvd_pow hd)
  have h7 : ¬ 5 ∣ 7 ^ (3 * 5 ^ e) := by
    intro hd
    exact (by norm_num : ¬ 5 ∣ 7) (hp.dvd_of_dvd_pow hd)
  unfold fiveMinimumLayerDenominator
  dsimp only
  simp only [hp.dvd_mul]
  aesop

/-- The scaled two-pair minimum layer is a five-adic unit. -/
theorem padicValRat_five_two_minimum_scaled
    (e k l : ℕ)
    (hk : 5 ^ e = 2 * k + 1)
    (hl : 3 * 5 ^ e = 2 * l + 1)
    (hkEven : Even k) (hlOdd : Odd l) :
    padicValRat 5
      ((5 : ℚ) ^ e * (huttonPairRat k + huttonPairRat l)) = 0 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [show (5 : ℚ) ^ e * (huttonPairRat k + huttonPairRat l) =
      (fiveMinimumLayerNumerator e : ℚ) /
          fiveMinimumLayerDenominator e by
    norm_num [five_minimum_two_scaled_eq e k l hk hl hkEven hlOdd]]
  have hn0 : (fiveMinimumLayerNumerator e : ℚ) ≠ 0 := by
    intro hz
    have hz' : fiveMinimumLayerNumerator e = 0 := by exact_mod_cast hz
    exact five_not_dvd_minimumLayerNumerator e (by simp [hz'])
  have hd0 : (fiveMinimumLayerDenominator e : ℚ) ≠ 0 := by
    exact_mod_cast
      (show fiveMinimumLayerDenominator e ≠ 0 by
        unfold fiveMinimumLayerDenominator
        dsimp only
        positivity)
  rw [padicValRat.div hn0 hd0,
    padicValRat_intCast_eq_zero_of_not_dvd
      (five_not_dvd_minimumLayerNumerator e),
    padicValRat_natCast_eq_zero_of_not_dvd
      (five_not_dvd_minimumLayerDenominator e)]
  norm_num

/-- The sum of the two possible minimum-layer pairs is nonzero. -/
lemma huttonPairRat_two_minimum_ne_zero
    (e k l : ℕ)
    (hk : 5 ^ e = 2 * k + 1)
    (hl : 3 * 5 ^ e = 2 * l + 1)
    (hkEven : Even k) (hlOdd : Odd l) :
    huttonPairRat k + huttonPairRat l ≠ 0 := by
  intro hzero
  have heq := five_minimum_two_scaled_eq e k l hk hl hkEven hlOdd
  rw [hzero, mul_zero] at heq
  have hn0 : (fiveMinimumLayerNumerator e : ℚ) ≠ 0 := by
    intro hz
    have hz' : fiveMinimumLayerNumerator e = 0 := by exact_mod_cast hz
    exact five_not_dvd_minimumLayerNumerator e (by simp [hz'])
  have hd0 : (fiveMinimumLayerDenominator e : ℚ) ≠ 0 := by
    exact_mod_cast
      (show fiveMinimumLayerDenominator e ≠ 0 by
        unfold fiveMinimumLayerDenominator
        dsimp only
        positivity)
  exact (div_ne_zero hn0 hd0) heq.symm

/-- The two-pair minimum layer has exact valuation `-e`. -/
theorem padicValRat_five_two_minimum
    (e k l : ℕ)
    (hk : 5 ^ e = 2 * k + 1)
    (hl : 3 * 5 ^ e = 2 * l + 1)
    (hkEven : Even k) (hlOdd : Odd l) :
    padicValRat 5 (huttonPairRat k + huttonPairRat l) =
      -(e : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsum0 :=
    huttonPairRat_two_minimum_ne_zero e k l hk hl hkEven hlOdd
  have hv :=
    padicValRat_five_two_minimum_scaled e k l hk hl hkEven hlOdd
  have hval5 : padicValRat 5 (5 : ℚ) = 1 :=
    padicValRat.self (by norm_num)
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hsum0,
    padicValRat.pow (by norm_num), hval5] at hv
  omega

/-- Main exact transient theorem.  If `5^e <= 4*K+3 < 5^(e+1)`, then the
lower Hutton shadow has five-adic valuation exactly `-e`. -/
theorem padicValRat_five_huttonLowerRat
    (K e : ℕ)
    (hlow : 5 ^ e ≤ 4 * K + 3)
    (hhigh : 4 * K + 3 < 5 ^ (e + 1)) :
    padicValRat 5 (huttonLowerRat K) = -(e : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases fivePrimaryIndices e with ⟨k, l, hk, hkEven, hl, hlOdd⟩
  have hkRange : k < huttonTermCount K := by
    unfold huttonTermCount
    omega
  by_cases hthree : 3 * 5 ^ e ≤ 4 * K + 3
  · have hlRange : l < huttonTermCount K := by
      unfold huttonTermCount
      omega
    have hkl : k ≠ l := by omega
    rw [huttonLowerRat_eq_regularTwo_add K k l hkRange hlRange hkl]
    apply padicValRat_add_eq_minLayer
      (huttonPairRat k + huttonPairRat l)
      (huttonFiveRegularTwoRat K k l) e
    · exact padicValRat_five_two_minimum e k l hk hl hkEven hlOdd
    · exact huttonPairRat_two_minimum_ne_zero e k l hk hl hkEven hlOdd
    · exact padicValRat_huttonFiveRegularTwo_ge_or_zero
        K e k l hhigh hk hl
  · rw [huttonLowerRat_eq_regularOne_add K k hkRange]
    apply padicValRat_add_eq_minLayer
      (huttonPairRat k) (huttonFiveRegularOneRat K k) e
    · rw [padicValRat_five_huttonPairRat,
        show padicValNat 5 (2 * k + 1) = e by
          rw [← hk, padicValNat.prime_pow]]
    · exact huttonPairRat_ne_zero k
    · exact padicValRat_huttonFiveRegularOne_ge_or_zero
        K e k hhigh hk (by omega)

/-- Every lower Hutton shadow is strictly positive. -/
lemma huttonLowerRat_pos (K : ℕ) : 0 < huttonLowerRat K := by
  induction K with
  | zero =>
      norm_num [huttonLowerRat, arctanPartialRat, arctanTermRat]
  | succ K ih =>
      exact lt_trans ih (huttonLowerRat_strictMono_step K)

/-- For a nonzero reduced rational of valuation `-e`, the denominator has
exact prime multiplicity `e`.  This formulation also covers `e=0`. -/
lemma padicValNat_den_eq_of_padicValRat_neg
    (q : ℚ) (e : ℕ) (hq0 : q ≠ 0)
    (hval : padicValRat 5 q = -(e : ℤ)) :
    padicValNat 5 q.den = e := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnumZ : q.num ≠ 0 := by
    intro hz
    apply hq0
    rw [← q.num_div_den, hz]
    norm_num
  have hnumAbs : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnumZ
  have hnumNot : ¬ 5 ∣ q.num.natAbs := by
    intro hnumDiv
    have hcop : Nat.Coprime 5 q.den :=
      Nat.Coprime.of_dvd_left hnumDiv q.reduced
    have hdenNot : ¬ 5 ∣ q.den :=
      (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mp hcop
    have hvden : padicValNat 5 q.den = 0 :=
      padicValNat.eq_zero_of_not_dvd hdenNot
    have hvnumNat : 1 ≤ padicValNat 5 q.num.natAbs :=
      (padicValNat_dvd_iff_le hnumAbs).1 (by simpa using hnumDiv)
    have hvnumInt : (1 : ℤ) ≤ padicValInt 5 q.num := by
      simpa [padicValInt] using hvnumNat
    rw [padicValRat_def, hvden] at hval
    omega
  have hvnumInt : padicValInt 5 q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnumNot
  rw [padicValRat_def, hvnumInt] at hval
  omega

/-- Exact reduced-denominator transient, including `K=0` and `e=0`. -/
theorem padicValNat_five_huttonLowerRat_den
    (K e : ℕ)
    (hlow : 5 ^ e ≤ 4 * K + 3)
    (hhigh : 4 * K + 3 < 5 ^ (e + 1)) :
    padicValNat 5 (huttonLowerRat K).den = e := by
  apply padicValNat_den_eq_of_padicValRat_neg
  · exact ne_of_gt (huttonLowerRat_pos K)
  · exact padicValRat_five_huttonLowerRat K e hlow hhigh

end Theory.PiDigits.HuttonFiveAdicTransient

#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonPairRat
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.five_not_dvd_huttonCancellationFactor
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonPairRat_eq_fraction
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_huttonPairRat
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValNat_five_le_of_lt_pow_succ
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.odd_maximal_five_adic_shape
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.five_pow_eq_four_mul_add_one
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.fivePrimaryIndices
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_regularPair_ge
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_sum_lower
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonFiveRegularOneRat
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonFiveRegularTwoRat
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonLowerRat_eq_pair_sum
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonLowerRat_eq_regularOne_add
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonLowerRat_eq_regularTwo_add
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_huttonFiveRegularOne_ge_or_zero
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_huttonFiveRegularTwo_ge_or_zero
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonPairRat_ne_zero
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_add_eq_minLayer
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.fiveMinimumLayerNumerator
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.fiveMinimumLayerDenominator
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.zmod_five_pow_five_pow
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.fiveMinimumLayerNumerator_cast_zmod
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.five_minimum_two_scaled_eq
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.five_not_dvd_minimumLayerNumerator
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.five_not_dvd_minimumLayerDenominator
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_two_minimum_scaled
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.huttonPairRat_two_minimum_ne_zero
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_two_minimum
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.padicValRat_five_huttonLowerRat
#print axioms Theory.PiDigits.HuttonFiveAdicTransient.huttonLowerRat_pos
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.padicValNat_den_eq_of_padicValRat_neg
#print axioms
  Theory.PiDigits.HuttonFiveAdicTransient.padicValNat_five_huttonLowerRat_den
