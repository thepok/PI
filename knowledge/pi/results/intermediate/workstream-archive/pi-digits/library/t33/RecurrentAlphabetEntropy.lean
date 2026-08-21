import TheoryLib.PiDigits.T9PiDigitsV3Reduction
import TheoryLib.PiDigits.T13PiDigitsTwoRecurrentDigits
import TheoryLib.PiDigits.T22ChampernowneDisjunctive
import TheoryLib.PiDigits.T32FactorEntropyObstruction

/-!
# T33: recurrent alphabets and the sharp entropy threshold for sibling V3

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file concerns sibling V3, not canonical V1. It proves a conditional
sufficient entropy criterion for T7's exact pi stream, but proves no entropy
lower bound for that stream. Consequently it resolves neither V1 nor V3 for
pi unconditionally. The generic V3 bridge is imported from T9, concatenation
machinery is imported from T22, and factor entropy is imported from T32.
-/

open Filter

namespace Theory.PiDigits.T33

open DecimalFactorComplexity
open Theory.PiDigits.V3Reduction
open Theory.PiDigits.T22
open Theory.PiDigits.T32

/-- The set of digits occurring at or beyond every threshold. -/
def recurrentDigits (s : Stream (Fin 10)) : Set (Fin 10) :=
  {d | ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ s n = d}

/-- The finite type of recurrent digits of `s`. -/
abbrev RecurrentDigit (s : Stream (Fin 10)) :=
  {d : Fin 10 // d ∈ recurrentDigits s}

/-- The number of recurrent decimal digits. -/
noncomputable def recurrentDigitCount (s : Stream (Fin 10)) : ℕ :=
  Nat.card (RecurrentDigit s)

/-- Finiteness of the decimal alphabet gives one cutoff beyond which every
stream value belongs to the recurrent alphabet. -/
theorem exists_recurrent_cutoff (s : Stream (Fin 10)) :
    ∃ C : ℕ, ∀ n : ℕ, C ≤ n → s n ∈ recurrentDigits s := by
  classical
  have hthreshold : ∀ d : Fin 10, ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → s n = d → d ∈ recurrentDigits s := by
    intro d
    by_cases hd : d ∈ recurrentDigits s
    · exact ⟨0, fun _ _ _ ↦ hd⟩
    · simp only [recurrentDigits, Set.mem_setOf_eq, not_forall] at hd
      obtain ⟨N, hN⟩ := hd
      push Not at hN
      exact ⟨N, fun n hn hsn ↦ (hN n hn hsn).elim⟩
  let cutoff : Fin 10 → ℕ := fun d ↦ (hthreshold d).choose
  let C : ℕ := Finset.univ.sup cutoff
  refine ⟨C, fun n hn ↦ ?_⟩
  have hcutoff : cutoff (s n) ≤ C :=
    Finset.le_sup (Finset.mem_univ (s n))
  exact (hthreshold (s n)).choose_spec n (hcutoff.trans hn) rfl

/-- At least one decimal digit recurs arbitrarily late in every stream. -/
theorem recurrentDigitCount_pos (s : Stream (Fin 10)) :
    0 < recurrentDigitCount s := by
  obtain ⟨d, hd⟩ :=
    Theory.PiDigits.TwoRecurrentDigits.exists_occursArbitrarilyLate s
  let d' : RecurrentDigit s := ⟨d, hd⟩
  letI : Nonempty (RecurrentDigit s) := ⟨d'⟩
  exact Nat.card_pos

/-- Code a factor either by a transient starting position or by a word over
the recurrent alphabet. -/
noncomputable def recurrentFactorCode (s : Stream (Fin 10)) (C n : ℕ)
    (hC : ∀ i : ℕ, C ≤ i → s i ∈ recurrentDigits s) :
    Factor s n → Fin C ⊕ (Fin n → RecurrentDigit s) := by
  classical
  intro v
  by_cases hv : ∀ j : Fin n, v.1 j ∈ recurrentDigits s
  · exact Sum.inr (fun j ↦ ⟨v.1 j, hv j⟩)
  · exact Sum.inl ⟨firstOccurrence v, by
      by_contra hnot
      have hstart : C ≤ firstOccurrence v := Nat.le_of_not_gt hnot
      push Not at hv
      obtain ⟨j, hj⟩ := hv
      have hs := hC (firstOccurrence v + j) (by omega)
      rw [← firstOccurrence_spec v j] at hs
      exact hj hs⟩

theorem recurrentFactorCode_eq_inr (s : Stream (Fin 10)) (C n : ℕ)
    (hC : ∀ i : ℕ, C ≤ i → s i ∈ recurrentDigits s)
    (v : Factor s n) (hv : ∀ j : Fin n, v.1 j ∈ recurrentDigits s) :
    recurrentFactorCode s C n hC v =
      Sum.inr (fun j ↦ (⟨v.1 j, hv j⟩ : RecurrentDigit s)) := by
  classical
  simp [recurrentFactorCode, hv]

theorem recurrentFactorCode_eq_inl (s : Stream (Fin 10)) (C n : ℕ)
    (hC : ∀ i : ℕ, C ≤ i → s i ∈ recurrentDigits s)
    (v : Factor s n) (hv : ¬∀ j : Fin n, v.1 j ∈ recurrentDigits s) :
    ∃ i : Fin C, recurrentFactorCode s C n hC v = Sum.inl i ∧
      i.val = firstOccurrence v := by
  classical
  rw [recurrentFactorCode]
  simp only [dif_neg hv]
  exact ⟨_, rfl, rfl⟩

/-- The transient/recurrent factor code is injective. -/
theorem recurrentFactorCode_injective (s : Stream (Fin 10)) (C n : ℕ)
    (hC : ∀ i : ℕ, C ≤ i → s i ∈ recurrentDigits s) :
    Function.Injective (recurrentFactorCode s C n hC) := by
  intro v w heq
  by_cases hv : ∀ j : Fin n, v.1 j ∈ recurrentDigits s
  · by_cases hw : ∀ j : Fin n, w.1 j ∈ recurrentDigits s
    · rw [recurrentFactorCode_eq_inr s C n hC v hv,
        recurrentFactorCode_eq_inr s C n hC w hw] at heq
      simp only [Sum.inr.injEq] at heq
      apply Subtype.ext
      funext j
      exact congrArg Subtype.val (congrFun heq j)
    · obtain ⟨i, hi, _⟩ := recurrentFactorCode_eq_inl s C n hC w hw
      rw [recurrentFactorCode_eq_inr s C n hC v hv, hi] at heq
      cases heq
  · by_cases hw : ∀ j : Fin n, w.1 j ∈ recurrentDigits s
    · obtain ⟨i, hi, _⟩ := recurrentFactorCode_eq_inl s C n hC v hv
      rw [hi, recurrentFactorCode_eq_inr s C n hC w hw] at heq
      cases heq
    · obtain ⟨iv, hiv, hivalue⟩ := recurrentFactorCode_eq_inl s C n hC v hv
      obtain ⟨iw, hiw, hiwvalue⟩ := recurrentFactorCode_eq_inl s C n hC w hw
      rw [hiv, hiw] at heq
      have hfirst : firstOccurrence v = firstOccurrence w := by
        rw [← hivalue, ← hiwvalue]
        exact congrArg Fin.val (Sum.inl.inj heq)
      apply Subtype.ext
      funext j
      calc
        v.1 j = s (firstOccurrence v + j) := firstOccurrence_spec v j
        _ = s (firstOccurrence w + j) := by rw [hfirst]
        _ = w.1 j := (firstOccurrence_spec w j).symm

/-- A finite transient prefix contributes only `C` exceptional factors;
all other length-`n` factors are words over the recurrent alphabet. -/
theorem factorComplexity_le_transient_add_recurrent_pow
    (s : Stream (Fin 10)) (C : ℕ)
    (hC : ∀ i : ℕ, C ≤ i → s i ∈ recurrentDigits s) (n : ℕ) :
    canonicalFactorComplexity s n ≤
      C + recurrentDigitCount s ^ n := by
  have hcard := Nat.card_le_card_of_injective
    (recurrentFactorCode s C n hC)
    (recurrentFactorCode_injective s C n hC)
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fun, Nat.card_fin] at hcard
  simpa [canonicalFactorComplexity, recurrentDigitCount] using hcard

/-- The full positive-length factor entropy is bounded by the logarithm of
the recurrent alphabet size. The proof includes the finite transient prefix. -/
theorem factorEntropy_le_log_recurrentDigitCount (s : Stream (Fin 10)) :
    factorEntropy s ≤ Real.log (recurrentDigitCount s : ℕ) := by
  obtain ⟨C, hC⟩ := exists_recurrent_cutoff s
  let r := recurrentDigitCount s
  have hr : 0 < r := recurrentDigitCount_pos s
  let D : ℝ := Real.log (C + 1 : ℕ)
  let envelope : ℕ → ℝ := fun n ↦ Real.log r + D / (n + 1 : ℝ)
  have hpointwise : ∀ n, factorEntropyTerm s n ≤ envelope n := by
    intro n
    let N := n + 1
    have hN : 0 < N := by simp [N]
    have hrone : 1 ≤ r := hr
    have hrpow : 1 ≤ r ^ N := one_le_pow₀ hrone
    have hCp : C ≤ C * r ^ N := by
      simpa using Nat.mul_le_mul_left C hrpow
    have hrough : C + r ^ N ≤ (C + 1) * r ^ N := by
      calc
        C + r ^ N ≤ C * r ^ N + r ^ N := Nat.add_le_add_right hCp _
        _ = (C + 1) * r ^ N := by ring
    have hcomplexity : canonicalFactorComplexity s N ≤
        (C + 1) * r ^ N := by
      exact (factorComplexity_le_transient_add_recurrent_pow s C hC N).trans
        (by simpa [r] using hrough)
    have hp : 0 < (canonicalFactorComplexity s N : ℝ) := by
      exact_mod_cast one_le_canonicalFactorComplexity s N
    have hcast : (canonicalFactorComplexity s N : ℝ) ≤
        (((C + 1) * r ^ N : ℕ) : ℝ) := by
      exact_mod_cast hcomplexity
    have hlog := Real.log_le_log hp hcast
    have hproduct :
        Real.log (((C + 1) * r ^ N : ℕ) : ℝ) =
          Real.log (C + 1 : ℕ) + (N : ℝ) * Real.log r := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    calc
      factorEntropyTerm s n =
          Real.log (canonicalFactorComplexity s N : ℝ) / (N : ℝ) := by
            simp [factorEntropyTerm, N]
      _ ≤ Real.log (((C + 1) * r ^ N : ℕ) : ℝ) / (N : ℝ) :=
        (div_le_div_iff_of_pos_right hNreal).2 hlog
      _ = Real.log r + Real.log (C + 1 : ℕ) / (N : ℝ) := by
        rw [hproduct]
        field_simp
        ring
      _ = envelope n := by simp [envelope, D, N]
  have heventual : factorEntropyTerm s ≤ᶠ[atTop] envelope :=
    Filter.Eventually.of_forall hpointwise
  have hnonneg : ∀ n, 0 ≤ factorEntropyTerm s n := by
    intro n
    exact div_nonneg
      (Real.log_natCast_nonneg (canonicalFactorComplexity s (n + 1))) (by positivity)
  have hcobounded :
      atTop.IsCoboundedUnder (· ≤ ·) (factorEntropyTerm s) :=
    Filter.isCoboundedUnder_le_of_le atTop hnonneg
  have henvelope : Tendsto envelope atTop (nhds (Real.log r)) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ D) atTop (nhds D) :=
      tendsto_const_nhds
    have hreciprocal : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hsmall : Tendsto (fun n : ℕ ↦ D * (1 / ((n : ℝ) + 1)))
        atTop (nhds 0) := by
      simpa using hconstant.mul hreciprocal
    have hc : Tendsto (fun _ : ℕ ↦ Real.log r) atTop (nhds (Real.log r)) :=
      tendsto_const_nhds
    simpa [envelope, div_eq_mul_inv] using hc.add hsmall
  calc
    factorEntropy s = limsup (factorEntropyTerm s) atTop := rfl
    _ ≤ limsup envelope atTop :=
      limsup_le_limsup heventual hcobounded henvelope.isBoundedUnder_le
    _ = Real.log r := henvelope.limsup_eq
    _ = Real.log (recurrentDigitCount s : ℕ) := rfl

/-- Named `r`-digit form of the recurrent-alphabet entropy bound. -/
theorem recurrent_alphabet_entropy_bound (s : Stream (Fin 10)) (r : ℕ)
    (hr : recurrentDigitCount s = r) :
    factorEntropy s ≤ Real.log r := by
  simpa [hr] using factorEntropy_le_log_recurrentDigitCount s

/-- Failure of generic decimal V3 omits at least one recurrent digit, so the
factor entropy is at most `log 9`. -/
theorem not_genericV3_implies_factorEntropy_le_logNine
    (s : Stream (Fin 10)) (hV3 : ¬ EveryStreamIsSubsequence s) :
    factorEntropy s ≤ Real.log 9 := by
  have hlate : ¬ EveryDigitOccursArbitrarilyLate s := by
    intro h
    exact hV3
      (everyStreamIsSubsequence_of_everyDigitOccursArbitrarilyLate s h)
  simp only [EveryDigitOccursArbitrarilyLate, not_forall] at hlate
  obtain ⟨d, hd⟩ := hlate
  obtain ⟨N, hN⟩ := hd
  push Not at hN
  have hdnot : d ∉ recurrentDigits s := by
    intro hdrec
    obtain ⟨n, hn, hsd⟩ := hdrec N
    exact hN n hn hsd
  let withoutD := {e : Fin 10 // e ≠ d}
  let forgetMissing : RecurrentDigit s → withoutD := fun e ↦
    ⟨e, fun hed ↦ hdnot (by simpa [hed] using e.property)⟩
  have hinjective : Function.Injective forgetMissing := by
    intro e f hef
    apply Subtype.ext
    exact congrArg (fun x : withoutD ↦ x.val) hef
  have hcount : recurrentDigitCount s ≤ 9 := by
    have hcard := Nat.card_le_card_of_injective forgetMissing hinjective
    have hwithout : Nat.card withoutD = 9 := by
      rw [Nat.card_eq_fintype_card]
      simp [withoutD, Fintype.card_subtype_compl]
    change Nat.card (RecurrentDigit s) ≤ 9
    exact hcard.trans_eq hwithout
  have hcountpos : 0 < recurrentDigitCount s := recurrentDigitCount_pos s
  have hlog : Real.log (recurrentDigitCount s : ℕ) ≤ Real.log 9 := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hcountpos)
    · exact Set.mem_Ioi.mpr (by norm_num)
    · exact_mod_cast hcount
  exact (factorEntropy_le_log_recurrentDigitCount s).trans hlog

/-- Generic contrapositive: entropy strictly above `log 9` forces V3. -/
theorem factorEntropy_gt_logNine_implies_genericV3
    (s : Stream (Fin 10)) (hentropy : Real.log 9 < factorEntropy s) :
    EveryStreamIsSubsequence s := by
  by_contra hV3
  exact (not_le_of_gt hentropy)
    (not_genericV3_implies_factorEntropy_le_logNine s hV3)

/-- Exact T7/T9 specialization. This is conditional and supplies no entropy
lower bound for the decimal digits of pi. -/
theorem pi_factorEntropy_gt_logNine_implies_exact_V3
    (hentropy : Real.log 9 < factorEntropy Theory.PiDigits.piDigit) :
    Theory.PiDigits.V3 := by
  apply everyDigitOccursArbitrarilyLate_implies_siblingV3
  exact everyDigitOccursArbitrarilyLate_of_everyStreamIsSubsequence _
    (factorEntropy_gt_logNine_implies_genericV3 _ hentropy)

/-- Enumerate all finite words over nine symbols, with a leading symbol so
every block supplied to T22's concatenation machinery is nonempty. -/
noncomputable def nineBlocks (k : ℕ) : List (Fin 9) :=
  0 :: (Encodable.decode k : Option (List (Fin 9))).getD []

theorem nineBlocks_ne_nil (k : ℕ) : nineBlocks k ≠ [] := by
  simp [nineBlocks]

/-- Every finite nine-symbol word is one of the enumerated blocks after its
leading padding symbol. -/
theorem nineBlocks_encode (w : List (Fin 9)) :
    nineBlocks (Encodable.encode w) = 0 :: w := by
  simp [nineBlocks, Encodable.encodek]

/-- Inject the nine-symbol alphabet as decimal digits `0,...,8`. -/
def nineEmbed (d : Fin 9) : Fin 10 :=
  ⟨d, by omega⟩

/-- A universal nine-digit decimal stream formed with T22's concatenation. -/
noncomputable def nineDigit : Stream (Fin 10) := fun n ↦
  nineEmbed (concatStream nineBlocks n)

/-- The artificial stream starts with its padding digit zero. -/
theorem nineDigit_zero : nineDigit 0 = 0 := by
  apply Fin.ext
  simp [nineDigit, nineEmbed, concatStream, finiteConcat, nineBlocks]

/-- T7's exact floor-based pi stream starts with decimal digit one. -/
theorem piDigit_zero : Theory.PiDigits.piDigit 0 = 1 := by
  apply Fin.ext
  simp only [Theory.PiDigits.piDigit, Fin.val_mk]
  have hfloor : ⌊Real.pi * (10 : ℝ)⌋₊ = 31 := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · norm_num
      nlinarith [Real.pi_gt_d2]
    · norm_num
      nlinarith [Real.pi_lt_d2]
  norm_num [hfloor]

/-- The constructed counterexample is extensionally different from T7's pi
digit stream, already at index zero. -/
theorem nineDigit_ne_piDigit :
    nineDigit ≠ Theory.PiDigits.piDigit := by
  intro heq
  have hzero := congrFun heq 0
  rw [nineDigit_zero, piDigit_zero] at hzero
  norm_num at hzero

/-- Every finite word over the nine used digits occurs contiguously. -/
theorem nineDigit_everyFiniteWord (w : List (Fin 9)) :
    ∃ start : ℕ, ∀ i : ℕ, ∀ hi : i < w.length,
      nineDigit (start + i) = nineEmbed (w.get ⟨i, hi⟩) := by
  let k := Encodable.encode w
  have hblock : nineBlocks k = 0 :: w := nineBlocks_encode w
  let offset := (finiteConcat nineBlocks k).length
  refine ⟨offset + 1, fun i hi ↦ ?_⟩
  have hj : i + 1 < (nineBlocks k).length := by
    rw [hblock, List.length_cons]
    omega
  have hcoverage := enumeratedBlock_occursAt_concatStream
    nineBlocks nineBlocks_ne_nil k (i + 1) hj
  change nineEmbed (concatStream nineBlocks ((offset + 1) + i)) = _
  rw [show (offset + 1) + i = offset + (i + 1) by omega, hcoverage]
  apply congrArg nineEmbed
  have hget := congrArg (fun l : List (Fin 9) ↦ l[i + 1]?) hblock
  simp [hi] at hget
  rw [List.getElem?_eq_getElem hj] at hget
  exact Option.some.inj hget

/-- Every output digit is one of `0,...,8`. -/
theorem nineDigit_lt_nine (n : ℕ) : (nineDigit n).val < 9 := by
  exact (concatStream nineBlocks n).isLt

/-- The range is exactly the nine decimal digits `0,...,8`. -/
theorem nineDigit_uses_exactly_nine_digits (d : Fin 10) :
    (∃ n : ℕ, nineDigit n = d) ↔ d.val < 9 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact nineDigit_lt_nine n
  · intro hd
    let e : Fin 9 := ⟨d.val, hd⟩
    obtain ⟨start, hstart⟩ := nineDigit_everyFiniteWord [e]
    refine ⟨start, ?_⟩
    have h := hstart 0 (by simp)
    apply Fin.ext
    simpa [nineEmbed, e] using congrArg Fin.val h

/-- Every word over `Fin 9` determines an occurring decimal factor. -/
noncomputable def nineWordFactor {n : ℕ} (w : Fin n → Fin 9) :
    Factor nineDigit n := by
  refine ⟨fun j ↦ nineEmbed (w j), ?_⟩
  obtain ⟨start, hstart⟩ := nineDigit_everyFiniteWord (List.ofFn w)
  refine ⟨start, fun j ↦ ?_⟩
  simpa using (hstart j (by simp)).symm

/-- The map from nine-symbol words to occurring factors is injective. -/
theorem nineWordFactor_injective (n : ℕ) :
    Function.Injective (nineWordFactor (n := n)) := by
  intro u v huv
  funext j
  have h := congrArg (fun f : Factor nineDigit n ↦ (f.1 j).val) huv
  exact Fin.ext h

/-- Decode every factor back to a word over the nine used symbols. -/
noncomputable def nineFactorWord {n : ℕ} (v : Factor nineDigit n) :
    Fin n → Fin 9 := fun j ↦ ⟨(v.1 j).val, by
  obtain ⟨start, hstart⟩ := v.2
  rw [hstart j]
  exact nineDigit_lt_nine (start + j)⟩

/-- Decoding factors to nine-symbol words is injective. -/
theorem nineFactorWord_injective (n : ℕ) :
    Function.Injective (nineFactorWord (n := n)) := by
  intro u v huv
  apply Subtype.ext
  funext j
  apply Fin.ext
  simpa [nineFactorWord] using congrArg Fin.val (congrFun huv j)

/-- The sharp stream has exactly `9^n` factors of every length `n`. -/
theorem nineDigit_factorComplexity (n : ℕ) :
    canonicalFactorComplexity nineDigit n = 9 ^ n := by
  apply Nat.le_antisymm
  · have h := Nat.card_le_card_of_injective
      (nineFactorWord (n := n)) (nineFactorWord_injective n)
    rw [Nat.card_fun, Nat.card_fin, Nat.card_fin] at h
    simpa [canonicalFactorComplexity] using h
  · have h := Nat.card_le_card_of_injective
      (nineWordFactor (n := n)) (nineWordFactor_injective n)
    rw [Nat.card_fun, Nat.card_fin, Nat.card_fin] at h
    simpa [canonicalFactorComplexity] using h

/-- The sharp stream's full factor entropy is exactly `log 9`. -/
theorem nineDigit_factorEntropy :
    factorEntropy nineDigit = Real.log 9 := by
  have hterm : factorEntropyTerm nineDigit = fun _ ↦ Real.log 9 := by
    funext n
    simp only [factorEntropyTerm, nineDigit_factorComplexity, Nat.cast_pow,
      Nat.cast_ofNat, Real.log_pow]
    field_simp
    push_cast
    rfl
  rw [factorEntropy, hterm]
  exact tendsto_const_nhds.limsup_eq

/-- The sharp stream fails generic decimal V3 because digit `9` is absent. -/
theorem nineDigit_fails_genericV3 :
    ¬ EveryStreamIsSubsequence nineDigit := by
  intro hV3
  have hlate :=
    everyDigitOccursArbitrarilyLate_of_everyStreamIsSubsequence nineDigit hV3
  let d : Fin 10 := ⟨9, by omega⟩
  obtain ⟨n, _, hn⟩ := hlate d 0
  have hlt := nineDigit_lt_nine n
  rw [hn] at hlt
  change (9 : ℕ) < 9 at hlt
  omega

/-- Sharpness at the threshold: exactly nine digits are used, every finite
word over them occurs, entropy is `log 9`, yet decimal V3 fails. -/
theorem nineDigit_sharp_counterexample :
    (∀ d : Fin 10, (∃ n : ℕ, nineDigit n = d) ↔ d.val < 9) ∧
    (∀ w : List (Fin 9), ∃ start : ℕ, ∀ i : ℕ, ∀ hi : i < w.length,
      nineDigit (start + i) = nineEmbed (w.get ⟨i, hi⟩)) ∧
    factorEntropy nineDigit = Real.log 9 ∧
    ¬ EveryStreamIsSubsequence nineDigit ∧
    nineDigit ≠ Theory.PiDigits.piDigit := by
  exact ⟨nineDigit_uses_exactly_nine_digits, nineDigit_everyFiniteWord,
    nineDigit_factorEntropy, nineDigit_fails_genericV3, nineDigit_ne_piDigit⟩

end Theory.PiDigits.T33

#print axioms Theory.PiDigits.T33.recurrent_alphabet_entropy_bound
#print axioms Theory.PiDigits.T33.not_genericV3_implies_factorEntropy_le_logNine
#print axioms Theory.PiDigits.T33.pi_factorEntropy_gt_logNine_implies_exact_V3
#print axioms Theory.PiDigits.T33.nineDigit_factorEntropy
#print axioms Theory.PiDigits.T33.nineDigit_sharp_counterexample
