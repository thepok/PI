import TheoryLib.PiDigits.T7Statements
import TheoryLib.PiDigits.T11PiDigitFactorComplexity

/-!
# T32: factor-complexity and entropy obstruction from an omitted decimal word

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The generic results below are conditional on a decimal stream omitting a fixed
nonempty word.  The final specialization starts from the literal negation of
T7's canonical `V1`.  No theorem in this file proves `V1` or sibling `V3` for
the decimal expansion of pi.
-/

open Filter

namespace Theory.PiDigits.T32

open DecimalFactorComplexity

/-- A decimal word of length `k`, represented using the generic block type
imported transitively by T11. -/
abbrev DecimalBlock (k : ℕ) := Block (Fin 10) k

/-- The stream has no contiguous occurrence of `w` at any starting position. -/
def OmitsBlock (s : Stream (Fin 10)) {k : ℕ} (w : DecimalBlock k) : Prop :=
  ¬ Occurs s w

/-- The finite alphabet of length-`k` decimal blocks other than `w`. -/
def AllowedBlocks {k : ℕ} (w : DecimalBlock k) :=
  {v : DecimalBlock k // v ≠ w}

noncomputable instance allowedBlocksFintype {k : ℕ} (w : DecimalBlock k) :
    Fintype (AllowedBlocks w) := by
  classical
  unfold AllowedBlocks
  infer_instance

/-- The `r`th consecutive length-`k` chunk of a block of length `m * k`. -/
def factorChunk {α : Type*} {k m : ℕ} (v : Block α (m * k))
    (r : Fin m) : Block α k :=
  fun j ↦ v ⟨r * k + j, by
    have hr : (r + 1) * k ≤ m * k :=
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt r.isLt)
    have hj : r * k + j < (r + 1) * k := by
      simpa [Nat.add_mul] using Nat.add_lt_add_left j.isLt (r * k)
    exact hj.trans_le hr⟩

/-- Every chunk of an occurring factor avoids a globally omitted block. -/
lemma factorChunk_ne_of_omits {s : Stream (Fin 10)} {k m : ℕ}
    {w : DecimalBlock k} (homit : OmitsBlock s w)
    (v : Factor s (m * k)) (r : Fin m) : factorChunk v.1 r ≠ w := by
  intro heq
  apply homit
  obtain ⟨i, hi⟩ := v.2
  refine ⟨i + r * k, ?_⟩
  intro j
  have hfactor := hi ⟨r * k + j, by
    have hr : (r + 1) * k ≤ m * k :=
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt r.isLt)
    have hj : r * k + j < (r + 1) * k := by
      simpa [Nat.add_mul] using Nat.add_lt_add_left j.isLt (r * k)
    exact hj.trans_le hr⟩
  rw [← heq]
  simpa [factorChunk, Nat.add_assoc] using hfactor

/-- Encode a length-`m*k` factor by its `m` consecutive allowed chunks. -/
def factorCode {s : Stream (Fin 10)} {k m : ℕ} {w : DecimalBlock k}
    (homit : OmitsBlock s w) : Factor s (m * k) → Fin m → AllowedBlocks w :=
  fun v r ↦ ⟨factorChunk v.1 r, factorChunk_ne_of_omits homit v r⟩

/-- Chunk encoding is injective when the chunk length is positive. -/
lemma factorCode_injective {s : Stream (Fin 10)} {k m : ℕ}
    {w : DecimalBlock k} (hk : 0 < k) (homit : OmitsBlock s w) :
    Function.Injective (factorCode (m := m) homit) := by
  intro v₁ v₂ hcode
  apply Subtype.ext
  funext q
  let r : Fin m := ⟨q / k, (Nat.div_lt_iff_lt_mul hk).2 q.isLt⟩
  let j : Fin k := ⟨q % k, Nat.mod_lt q hk⟩
  have hchunks := congrFun hcode r
  have hvalues := congrArg Subtype.val hchunks
  have hletter := congrFun hvalues j
  simp only [factorCode, factorChunk, r, j] at hletter
  have hlt : q / k * k + q % k < m * k := by
    rw [Nat.div_add_mod']
    exact q.isLt
  have hindex :
      (⟨q / k * k + q % k, hlt⟩ :
        Fin (m * k)) = q := by
    apply Fin.ext
    exact Nat.div_add_mod' q k
  simpa [hindex] using hletter

/-- Exactly `10^k - 1` length-`k` decimal blocks differ from a fixed block. -/
lemma card_allowedBlocks {k : ℕ} (w : DecimalBlock k) :
    Nat.card (AllowedBlocks w) = 10 ^ k - 1 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [AllowedBlocks, DecimalBlock, Block, Fintype.card_subtype_compl]

/-- If a decimal stream omits a nonempty length-`k` word, then for every
`m ≥ 1` its exact length-`m*k` factor complexity is at most
`(10^k - 1)^m`. -/
theorem factorComplexity_mul_le_pow_of_omits
    (s : Stream (Fin 10)) {k : ℕ} (hk : 0 < k) (w : DecimalBlock k)
    (homit : OmitsBlock s w) (m : ℕ) (_hm : 1 ≤ m) :
    canonicalFactorComplexity s (m * k) ≤ (10 ^ k - 1) ^ m := by
  have hcard := Nat.card_le_card_of_injective
    (factorCode (m := m) homit) (factorCode_injective hk homit)
  rw [Nat.card_fun, Nat.card_fin, card_allowedBlocks] at hcard
  simpa [canonicalFactorComplexity] using hcard

/-- Every factor complexity is positive because the factor beginning at zero
exists. -/
lemma one_le_canonicalFactorComplexity (s : Stream (Fin 10)) (n : ℕ) :
    1 ≤ canonicalFactorComplexity s n := by
  letI : Nonempty (Factor s n) := ⟨factorAt s n 0⟩
  change 1 ≤ Nat.card (Factor s n)
  exact Nat.card_pos

/-- Canonical factor complexity is monotone in the factor length. -/
lemma canonicalFactorComplexity_monotone (s : Stream (Fin 10)) :
    Monotone (canonicalFactorComplexity s) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [canonical_factorComplexity] using
    factorComplexity_mono s (canonicalComplexityData s) n

/-- The normalized logarithmic factor complexity at positive length `n+1`. -/
noncomputable def factorEntropyTerm (s : Stream (Fin 10)) (n : ℕ) : ℝ :=
  Real.log (canonicalFactorComplexity s (n + 1) : ℝ) / (n + 1 : ℝ)

/-- Full factor entropy, defined as the limsup over all positive lengths. -/
noncomputable def factorEntropy (s : Stream (Fin 10)) : ℝ :=
  limsup (factorEntropyTerm s) atTop

/-- A pointwise upper envelope obtained by moving length `n+1` to the next
multiple of the omitted word length. -/
lemma factorEntropyTerm_le_of_omits
    (s : Stream (Fin 10)) {k : ℕ} (hk : 0 < k) (w : DecimalBlock k)
    (homit : OmitsBlock s w) (n : ℕ) :
    factorEntropyTerm s n ≤
      Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) +
        Real.log (10 ^ k - 1 : ℕ) / (n + 1 : ℝ) := by
  let N := n + 1
  let A := 10 ^ k - 1
  let q := N / k
  have hN : 0 < N := by simp [N]
  have hpow : 10 ≤ 10 ^ k := by
    simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hk
  have hA : 0 < A := by
    dsimp [A]
    omega
  have hAone : 1 ≤ A := hA
  have hnext : N ≤ (q + 1) * k := by
    exact ((Nat.div_lt_iff_lt_mul hk).1 (Nat.lt_succ_self q)).le
  have hmono : canonicalFactorComplexity s N ≤
      canonicalFactorComplexity s ((q + 1) * k) :=
    canonicalFactorComplexity_monotone s hnext
  have hmultiple : canonicalFactorComplexity s ((q + 1) * k) ≤ A ^ (q + 1) := by
    simpa [A] using
      factorComplexity_mul_le_pow_of_omits s hk w homit (q + 1)
        (Nat.succ_le_succ (Nat.zero_le q))
  have hcomplexity : canonicalFactorComplexity s N ≤ A ^ (q + 1) :=
    hmono.trans hmultiple
  have hp : 0 < (canonicalFactorComplexity s N : ℝ) := by
    exact_mod_cast (one_le_canonicalFactorComplexity s N)
  have hcast : (canonicalFactorComplexity s N : ℝ) ≤ (A ^ (q + 1) : ℕ) := by
    exact_mod_cast hcomplexity
  have hlog : Real.log (canonicalFactorComplexity s N : ℝ) ≤
      ((q + 1 : ℕ) : ℝ) * Real.log A := by
    have := Real.log_le_log hp hcast
    simpa [Nat.cast_pow, Real.log_pow] using this
  have hqmul : q * k ≤ N := Nat.div_mul_le_self N k
  have hq : (q : ℝ) ≤ (N : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hk)]
    exact_mod_cast hqmul
  have hlogA : 0 ≤ Real.log (A : ℝ) := Real.log_natCast_nonneg A
  have hqlog : (q : ℝ) * Real.log A ≤
      ((N : ℝ) / (k : ℝ)) * Real.log A :=
    mul_le_mul_of_nonneg_right hq hlogA
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have henvelope :
      ((q + 1 : ℕ) : ℝ) * Real.log A / (N : ℝ) ≤
        Real.log A / (k : ℝ) + Real.log A / (N : ℝ) := by
    calc
      ((q + 1 : ℕ) : ℝ) * Real.log A / (N : ℝ) =
          ((q : ℝ) * Real.log A) / (N : ℝ) + Real.log A / (N : ℝ) := by
            push_cast
            ring
      _ ≤ (((N : ℝ) / (k : ℝ)) * Real.log A) / (N : ℝ) +
          Real.log A / (N : ℝ) :=
        add_le_add ((div_le_div_iff_of_pos_right hNreal).2 hqlog) le_rfl
      _ = Real.log A / (k : ℝ) + Real.log A / (N : ℝ) := by
        field_simp
  have hnormalized :
      Real.log (canonicalFactorComplexity s N : ℝ) / (N : ℝ) ≤
        Real.log A / (k : ℝ) + Real.log A / (N : ℝ) :=
    ((div_le_div_iff_of_pos_right hNreal).2 hlog).trans henvelope
  simpa [factorEntropyTerm, N, A] using hnormalized

/-- Omitting a nonempty length-`k` decimal word forces the full limsup factor
entropy below the logarithmic block-alphabet bound. -/
theorem factorEntropy_le_of_omits
    (s : Stream (Fin 10)) {k : ℕ} (hk : 0 < k) (w : DecimalBlock k)
    (homit : OmitsBlock s w) :
    factorEntropy s ≤ Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) := by
  let c : ℝ := Real.log (10 ^ k - 1 : ℕ) / (k : ℝ)
  let D : ℝ := Real.log (10 ^ k - 1 : ℕ)
  let envelope : ℕ → ℝ := fun n ↦ c + D / (n + 1 : ℝ)
  have hpointwise : ∀ n, factorEntropyTerm s n ≤ envelope n := by
    intro n
    simpa [c, D, envelope] using factorEntropyTerm_le_of_omits s hk w homit n
  have heventual : factorEntropyTerm s ≤ᶠ[atTop] envelope :=
    Filter.Eventually.of_forall hpointwise
  have hnonneg : ∀ n, 0 ≤ factorEntropyTerm s n := by
    intro n
    exact div_nonneg
      (Real.log_natCast_nonneg (canonicalFactorComplexity s (n + 1))) (by positivity)
  have hcobounded :
      atTop.IsCoboundedUnder (· ≤ ·) (factorEntropyTerm s) :=
    Filter.isCoboundedUnder_le_of_le atTop hnonneg
  have henvelope : Tendsto envelope atTop (nhds c) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ D) atTop (nhds D) :=
      tendsto_const_nhds
    have hreciprocal : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hsmall : Tendsto (fun n : ℕ ↦ D * (1 / ((n : ℝ) + 1))) atTop (nhds 0) :=
      by simpa using hconstant.mul hreciprocal
    have hc : Tendsto (fun _ : ℕ ↦ c) atTop (nhds c) := tendsto_const_nhds
    simpa [envelope, div_eq_mul_inv] using hc.add hsmall
  calc
    factorEntropy s = limsup (factorEntropyTerm s) atTop := rfl
    _ ≤ limsup envelope atTop :=
      limsup_le_limsup heventual hcobounded henvelope.isBoundedUnder_le
    _ = c := henvelope.limsup_eq
    _ = Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) := rfl

/-- The entropy bound forced by omitting a nonempty word is strictly below the
full decimal entropy `log 10`. -/
theorem omittedBlock_entropyBound_lt_logTen {k : ℕ} (hk : 0 < k) :
    Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) < Real.log 10 := by
  have hpow : 10 ≤ 10 ^ k := by
    simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hk
  have hA : 0 < 10 ^ k - 1 := by omega
  have hpowpos : 0 < 10 ^ k := pow_pos (by norm_num) k
  have hlt : 10 ^ k - 1 < 10 ^ k := Nat.sub_lt hpowpos (by norm_num)
  have hloglt : Real.log (10 ^ k - 1 : ℕ) < Real.log (10 ^ k : ℕ) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hA)
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hpowpos)
    · exact_mod_cast hlt
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [div_lt_iff₀ hkreal]
  rw [Nat.cast_pow, Real.log_pow] at hloglt
  simpa [mul_comm] using hloglt

/-- Convert a list to the extensionally identical T11 block. -/
def listBlock (u : List (Fin 10)) : DecimalBlock u.length :=
  fun i ↦ u.get i

/-- The literal negation of T7's canonical V1 is exactly the existence of a
nonempty finite block omitted by T7's `piDigit` stream. -/
theorem not_canonicalV1_iff_exists_omitted_nonemptyBlock :
    ¬ Theory.PiDigits.V1 ↔
      ∃ k : ℕ, 0 < k ∧ ∃ w : DecimalBlock k,
        OmitsBlock Theory.PiDigits.piDigit w := by
  constructor
  · intro hnot
    rw [Theory.PiDigits.V1] at hnot
    push Not at hnot
    obtain ⟨u, hu⟩ := hnot
    have hlength : 0 < u.length := by
      obtain ⟨i, hi, _⟩ := hu 0
      omega
    refine ⟨u.length, hlength, listBlock u, ?_⟩
    intro hoccur
    obtain ⟨n, hn⟩ := hoccur
    obtain ⟨i, hi, hne⟩ := hu n
    exact hne (by simpa [listBlock] using (hn ⟨i, hi⟩).symm)
  · rintro ⟨k, hk, w, homit⟩ hV1
    obtain ⟨n, hn⟩ := hV1 (List.ofFn w)
    apply homit
    refine ⟨n, ?_⟩
    intro j
    have hdigit := hn (j : ℕ) (by simp)
    simpa using hdigit.symm

/-- Exact T7 specialization. If canonical V1 fails, one omitted nonempty word
simultaneously gives the requested finite bounds and a strict full factor
entropy deficit. This implication does not prove `¬V1`, `V1`, or `V3` for pi. -/
theorem not_canonicalV1_implies_factorEntropy_deficit
    (hnot : ¬ Theory.PiDigits.V1) :
    ∃ k : ℕ, 0 < k ∧ ∃ w : DecimalBlock k,
      OmitsBlock Theory.PiDigits.piDigit w ∧
      (∀ m : ℕ, 1 ≤ m →
        Theory.PiDigits.FactorComplexity.piFactorComplexity (m * k) ≤
          (10 ^ k - 1) ^ m) ∧
      factorEntropy Theory.PiDigits.piDigit ≤
        Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) ∧
      Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) < Real.log 10 := by
  obtain ⟨k, hk, w, homit⟩ :=
    not_canonicalV1_iff_exists_omitted_nonemptyBlock.mp hnot
  refine ⟨k, hk, w, homit, ?_, factorEntropy_le_of_omits _ hk w homit,
    omittedBlock_entropyBound_lt_logTen hk⟩
  intro m hm
  simpa [Theory.PiDigits.FactorComplexity.piFactorComplexity] using
    factorComplexity_mul_le_pow_of_omits Theory.PiDigits.piDigit hk w homit m hm

end Theory.PiDigits.T32

#print axioms Theory.PiDigits.T32.factorComplexity_mul_le_pow_of_omits
#print axioms Theory.PiDigits.T32.factorEntropy_le_of_omits
#print axioms Theory.PiDigits.T32.omittedBlock_entropyBound_lt_logTen
#print axioms Theory.PiDigits.T32.not_canonicalV1_iff_exists_omitted_nonemptyBlock
#print axioms Theory.PiDigits.T32.not_canonicalV1_implies_factorEntropy_deficit
