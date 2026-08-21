import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
import TheoryLib.PiLongLagBlockCollisionDecay.T49T49PrimitiveIncidenceAssembly
import TheoryLib.PiLongLagBlockCollisionDecay.T59T59CompleteSignedPrimitivePartition
import TheoryLib.PiLongLagBlockCollisionDecay.T60T60DefectLaurentPolynomial

/-!
# T63: exact finite fourth-moment identity

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module proves only an exact finite identity for the residual A12 primitive
sector.  The named fixed-pi fourth-moment frontier at the end is a proposition,
not a theorem.  No asymptotic estimate, C2, C3, C1, or canonical collision
claim is proved here.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T63

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T49
open Theory.PiDigits.LongLagBlockCollisionDecay.T56
open Theory.PiDigits.LongLagBlockCollisionDecay.T59
open Theory.PiDigits.LongLagBlockCollisionDecay.T60

/-- The exact base point `u_k = exp(2*pi^2*i*10^k)`. -/
def u (k : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) ^ 2 * Complex.I * (10 : ℂ) ^ k)

/-- `T_h(N)`, with the index set `0 <= k < N` represented by `range N`. -/
def T (h N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, u k ^ h

/-- `X_h(N) = |T_h(N)|^2`. -/
def X (h N : ℕ) : ℝ := Complex.normSq (T h N)

/-- The exact positive primitive representatives at the dyadic one-block
scale `L=2^t`, `m=1`, `N=4*L+1`, for one literal frequency `h`. -/
def C (Q0 t h : ℕ) : ℝ :=
  ∑ p ∈ primitiveRecordDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
      (⟨1, t + 2⟩ : DyadicBlock),
    Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (blockDifferenceValue p : ℝ))

/-- The base point is literally the required exponential. -/
theorem u_literal (k : ℕ) :
    u k = Complex.exp (2 * (Real.pi : ℂ) ^ 2 * Complex.I * (10 : ℂ) ^ k) := by
  rfl

/-- The requested power convention agrees with the imported phase convention. -/
theorem u_pow_eq_phase (k h : ℕ) :
    u k ^ h = Theory.PiDigits.T27.phase (h : ℤ) ((10 : ℝ) ^ k * Real.pi) := by
  rw [Theory.PiDigits.T27.phase_nat_eq_pow]
  unfold u Theory.PiDigits.T27.phase
  congr 1
  push_cast
  ring

/-- Hence `T_h(N)` is exactly the existing decimal orbit sum. -/
theorem T_eq_decimalOrbitSum (h N : ℕ) : T h N = decimalOrbitSum N h := by
  unfold T decimalOrbitSum
  apply Finset.sum_congr rfl
  intro k hk
  exact u_pow_eq_phase k h

/-- Exact dyadic substitution and literal one-block endpoints. -/
theorem dyadic_one_block_audit (t : ℕ) :
    boxLength t = 2 ^ t ∧
    boxEndpoint t = 4 * 2 ^ t + 1 ∧
    boxBlock t = (⟨1, t + 2⟩ : DyadicBlock) ∧
    translatedCanonicalBlocks (4 * 2 ^ t + 1) =
      [(⟨1, t + 2⟩ : DyadicBlock)] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simpa only [boxEndpoint, boxLength, boxBlock] using
    translatedCanonicalBlocks_boxEndpoint t

/-- At the one-block scale, the block record domain is exactly all ordered
unequal coordinate pairs below the literal endpoint. -/
theorem mem_boxOrderedDomain_iff (Q0 t : ℕ) (q : OrderedLongPair) :
    q ∈ blockOrderedDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
        (⟨1, t + 2⟩ : DyadicBlock) ↔
      orderedFirst q < 4 * 2 ^ t + 1 ∧
      orderedSecond q < 4 * 2 ^ t + 1 ∧
      orderedFirst q ≠ orderedSecond q := by
  rw [blockOrderedDomain, Finset.mem_filter]
  constructor
  · intro h
    exact (mem_orderedLongPairDomain_eight_one_one_iff
      Q0 (4 * 2 ^ t + 1) q).mp h.1
  · intro h
    refine ⟨(mem_orderedLongPairDomain_eight_one_one_iff
      Q0 (4 * 2 ^ t + 1) q).mpr h, ?_⟩
    rcases q with ⟨b, ⟨r, n⟩⟩
    cases b <;>
      simp only [orderedFirst, orderedSecond, Bool.false_eq_true, ↓reduceIte]
        at h ⊢ <;>
      simp only [frequencyEndpoint, DyadicBlock.finish,
        DyadicBlock.blockLength, pow_add] <;>
      omega

/-- For the prescribed signs `(+,+,-,-)`, noncancellation is exactly the four
opposite-sign inequalities below. After the two within-record diagonals are
removed, the remaining two are the nonattacking exclusions. Equal-sign
repetitions are not excluded. -/
theorem noncancelling_four_iff (a b c d : ℕ) :
    Noncancelling fourTokenSign
        (![a, d, b, c] : Fin 4 → ℕ) ↔
      a ≠ b ∧ a ≠ c ∧ d ≠ b ∧ d ≠ c := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hab
      have hs := h (0 : Fin 4) (2 : Fin 4) hab
      simp [fourTokenSign] at hs
    · intro hac
      have hs := h (0 : Fin 4) (3 : Fin 4) hac
      simp [fourTokenSign] at hs
    · intro hdb
      have hs := h (1 : Fin 4) (2 : Fin 4) hdb
      simp [fourTokenSign] at hs
    · intro hdc
      have hs := h (1 : Fin 4) (3 : Fin 4) hdc
      simp [fourTokenSign] at hs
  · rintro ⟨hab, hac, hdb, hdc⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [fourTokenSign]

/-- Membership exposes the complete finite domain: both records, their
ordered coordinates below `N=4*2^t+1`, the within-record diagonal exclusions,
the strict positive orientation, the `(+,+,-,-)` signs, and the primitive
nonattacking exclusion. -/
theorem mem_C_domain_iff
    (Q0 t : ℕ) (p : PrimitiveRecordPair) :
    p ∈ primitiveRecordDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
        (⟨1, t + 2⟩ : DyadicBlock) ↔
      orderedFirst p.1 < 4 * 2 ^ t + 1 ∧
      orderedSecond p.1 < 4 * 2 ^ t + 1 ∧
      orderedFirst p.1 ≠ orderedSecond p.1 ∧
      orderedFirst p.2 < 4 * 2 ^ t + 1 ∧
      orderedSecond p.2 < 4 * 2 ^ t + 1 ∧
      orderedFirst p.2 ≠ orderedSecond p.2 ∧
      signedDecimalFrequency p.2 < signedDecimalFrequency p.1 ∧
      Noncancelling fourTokenSign
        (![orderedFirst p.1, orderedSecond p.2,
          orderedSecond p.1, orderedFirst p.2] : Fin 4 → ℕ) := by
  unfold primitiveRecordDomain primitiveBlockDifferenceDomain
    blockPositiveDifferenceDomain
  simp only [Finset.mem_filter, Finset.mem_product]
  rw [mem_boxOrderedDomain_iff, mem_boxOrderedDomain_iff]
  simp only [blockDifferenceExponent]
  tauto

/-- Primitive means precisely that the opposite-sign coordinates do not
attack. Equal-sign repetitions remain allowed. -/
theorem mem_C_domain_iff_nonattacking
    (Q0 t : ℕ) (p : PrimitiveRecordPair) :
    p ∈ primitiveRecordDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
        (⟨1, t + 2⟩ : DyadicBlock) ↔
      orderedFirst p.1 < 4 * 2 ^ t + 1 ∧
      orderedSecond p.1 < 4 * 2 ^ t + 1 ∧
      orderedFirst p.2 < 4 * 2 ^ t + 1 ∧
      orderedSecond p.2 < 4 * 2 ^ t + 1 ∧
      orderedFirst p.1 ≠ orderedSecond p.1 ∧
      orderedFirst p.2 ≠ orderedSecond p.2 ∧
      orderedFirst p.1 ≠ orderedFirst p.2 ∧
      orderedSecond p.1 ≠ orderedSecond p.2 ∧
      signedDecimalFrequency p.2 < signedDecimalFrequency p.1 := by
  rw [mem_C_domain_iff]
  rw [noncancelling_four_iff]
  tauto

/-- Both signed orientations are present, with signs `+d` and `-d`. -/
theorem both_orientations_sign_audit
    {Q0 t : ℕ} {p : PrimitiveRecordPair}
    (hp : p ∈ primitiveRecordDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
      (⟨1, t + 2⟩ : DyadicBlock)) (b : Bool) :
    signedDecimalFrequency (orientPositiveDifference (b, p)).1 -
        signedDecimalFrequency (orientPositiveDifference (b, p)).2 =
      (if b then -1 else 1) * (blockDifferenceValue p : ℤ) := by
  simpa [phaseOrientationSign] using orientPositiveDifference_sign hp b

/-- Ordered unequal index pairs below `N`. -/
def orderedIndexPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N) ×ˢ Finset.range N).filter fun q => q.1 ≠ q.2

/-- The complete signed primitive/nonattacking quartet domain. Each component
is an ordered unequal pair, and opposite signs may not share their first or
second coordinate. -/
def nonattackingOrderedQuartets (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (orderedIndexPairs N ×ˢ orderedIndexPairs N).filter fun qr =>
    qr.1.1 ≠ qr.2.1 ∧ qr.1.2 ≠ qr.2.2

/-- One ordered-pair character `u_a^h * conj(u_b^h)`. -/
def pairCharacter (h : ℕ) (q : ℕ × ℕ) : ℂ :=
  u q.1 ^ h * conj (u q.2 ^ h)

/-- Full membership audit for the complete signed quartet domain. -/
theorem mem_nonattackingOrderedQuartets_iff
    (N : ℕ) (qr : (ℕ × ℕ) × (ℕ × ℕ)) :
    qr ∈ nonattackingOrderedQuartets N ↔
      qr.1.1 < N ∧ qr.1.2 < N ∧ qr.2.1 < N ∧ qr.2.2 < N ∧
      qr.1.1 ≠ qr.1.2 ∧ qr.2.1 ≠ qr.2.2 ∧
      qr.1.1 ≠ qr.2.1 ∧ qr.1.2 ≠ qr.2.2 := by
  simp [nonattackingOrderedQuartets, orderedIndexPairs]
  tauto

theorem normSq_u_pow (k h : ℕ) : Complex.normSq (u k ^ h) = 1 := by
  rw [u_pow_eq_phase, Complex.normSq_eq_norm_sq,
    Theory.PiDigits.T27.norm_phase]
  norm_num

/-- The row calculation behind both attacking-coordinate corrections. -/
theorem sum_normSq_T_sub_u (h N : ℕ) :
    ∑ a ∈ Finset.range N, Complex.normSq (T h N - u a ^ h) =
      (N : ℝ) * X h N + N - 2 * X h N := by
  change ∑ a ∈ Finset.range N, Complex.normSq (T h N - u a ^ h) =
    (N : ℝ) * Complex.normSq (T h N) + N - 2 * Complex.normSq (T h N)
  simp_rw [Complex.normSq_sub, normSq_u_pow]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const]
  rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum, ← map_sum]
  change _ = _
  rw [show (∑ x ∈ Finset.range N, u x ^ h) = T h N from rfl]
  rw [Complex.mul_conj, Complex.ofReal_re]
  simp

theorem orderedIndexPairs_eq_offDiag (N : ℕ) :
    orderedIndexPairs N = (Finset.range N).offDiag := by
  ext q
  simp [orderedIndexPairs]
  tauto

theorem orderedIndexPairs_card (N : ℕ) :
    (orderedIndexPairs N).card = N * (N - 1) := by
  rw [orderedIndexPairs_eq_offDiag, Finset.offDiag_card]
  simp
  rw [Nat.mul_sub_left_distrib]
  simp

theorem normSq_pairCharacter (h : ℕ) (q : ℕ × ℕ) :
    Complex.normSq (pairCharacter h q) = 1 := by
  rw [pairCharacter, Complex.normSq_mul, Complex.normSq_conj,
    normSq_u_pow, normSq_u_pow]
  norm_num

theorem sum_pairCharacter_eq (h N : ℕ) :
    ∑ q ∈ orderedIndexPairs N, pairCharacter h q =
      ((X h N - N : ℝ) : ℂ) := by
  have horbit := spectralSum_eight_one_one_eq_fullDomain 0 N h
  have hnorm := spectralSum_eight_one_one_eq_normSq_sub 0 N h
  rw [horbit] at hnorm
  change (∑ q ∈ fullOrderedPairDomain N,
      Theory.PiDigits.T27.phase (h : ℤ)
        (((10 : ℝ) ^ q.1 - (10 : ℝ) ^ q.2) * Real.pi)) = _ at hnorm
  rw [show orderedIndexPairs N = fullOrderedPairDomain N from rfl]
  calc
    (∑ q ∈ fullOrderedPairDomain N, pairCharacter h q) =
        ∑ q ∈ fullOrderedPairDomain N,
          Theory.PiDigits.T27.phase (h : ℤ)
            (((10 : ℝ) ^ q.1 - (10 : ℝ) ^ q.2) * Real.pi) := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold pairCharacter
      rw [u_pow_eq_phase, u_pow_eq_phase,
        phase_mul_conj_phase_eq_sub_real]
      congr 1
      ring
    _ = (Complex.normSq (decimalOrbitSum N h) : ℂ) - (N : ℂ) := hnorm
    _ = ((X h N - N : ℝ) : ℂ) := by
      rw [← T_eq_decimalOrbitSum]
      norm_num [X]

/-- Finite inclusion-exclusion for the two attacking-coordinate conditions. -/
theorem sum_nonattacking_inclusion_exclusion
    {α : Type} [DecidableEq α]
    (P : Finset α) (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (f : α → ℂ) :
    (∑ x ∈ P.filter fun x => ¬A x ∧ ¬B x, f x) =
      (∑ x ∈ P, f x) - (∑ x ∈ P.filter A, f x) -
        (∑ x ∈ P.filter B, f x) +
          ∑ x ∈ P.filter (fun x => A x ∧ B x), f x := by
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x <;> by_cases hB : B x <;> simp [hA, hB]

/-- The first-coordinate attacking sum is the row norm-square correction. -/
def firstRowDomain (N a : ℕ) : Finset (ℕ × ℕ) :=
  (orderedIndexPairs N).filter fun q => q.1 = a

def firstRowSum (h N a : ℕ) : ℂ :=
  ∑ q ∈ firstRowDomain N a, pairCharacter h q

theorem firstRowSum_eq
    {N a : ℕ} (ha : a ∈ Finset.range N) (h : ℕ) :
    firstRowSum h N a = u a ^ h * conj (T h N - u a ^ h) := by
  have hdomain : firstRowDomain N a =
      ((Finset.range N).filter (fun b => b ≠ a)).image (fun b => (a, b)) := by
    ext q
    rcases q with ⟨x, y⟩
    simp [firstRowDomain, orderedIndexPairs]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, hxa⟩
      refine ⟨⟨hy, ?_⟩, hxa.symm⟩
      intro hya
      exact hxy (hxa.trans hya.symm)
    · rintro ⟨⟨hy, hya⟩, hax⟩
      refine ⟨⟨⟨hax ▸ Finset.mem_range.mp ha, hy⟩, ?_⟩, hax.symm⟩
      intro hxy
      exact hya (hxy.symm.trans hax.symm)
  rw [firstRowSum, hdomain,
    Finset.sum_image (fun b _ c _ hbc => congrArg Prod.snd hbc)]
  simp only [pairCharacter]
  rw [← Finset.mul_sum, ← map_sum]
  have hremove :
      (∑ b ∈ (Finset.range N).filter (fun b => b ≠ a), u b ^ h) =
        T h N - u a ^ h := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun b => b ≠ a) (fun b => u b ^ h)
    have hsingle :
        (∑ b ∈ (Finset.range N).filter (fun b => ¬b ≠ a), u b ^ h) =
          u a ^ h := by
      have heq : (Finset.range N).filter (fun b => ¬b ≠ a) = {a} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨hb, hba⟩
          exact Classical.not_not.mp hba
        · intro hba
          subst b
          exact ⟨Finset.mem_range.mp ha, by simp⟩
      rw [heq]
      simp
    rw [eq_sub_iff_add_eq, ← hsingle]
    simpa only [T] using hsplit
  rw [hremove]

theorem first_attack_sum (h N : ℕ) :
    (∑ qr ∈ (orderedIndexPairs N ×ˢ orderedIndexPairs N).filter
        (fun qr => qr.1.1 = qr.2.1),
      pairCharacter h qr.1 * conj (pairCharacter h qr.2)) =
      ((N : ℝ) * X h N + N - 2 * X h N : ℂ) := by
  let Q := orderedIndexPairs N
  rw [Finset.sum_filter, Finset.sum_product]
  have hinner (q : ℕ × ℕ) :
      (∑ r ∈ Q, if q.1 = r.1 then
          pairCharacter h q * conj (pairCharacter h r) else 0) =
        pairCharacter h q * conj (firstRowSum h N q.1) := by
    rw [← Finset.sum_filter]
    have heq : Q.filter (fun r => q.1 = r.1) = firstRowDomain N q.1 := by
      ext r
      simp [Q, firstRowDomain, eq_comm]
    rw [heq, ← Finset.mul_sum, ← map_sum]
    rfl
  calc
    (∑ q ∈ Q, ∑ r ∈ Q, if (q, r).1.1 = (q, r).2.1 then
        pairCharacter h (q, r).1 * conj (pairCharacter h (q, r).2) else 0) =
        ∑ q ∈ Q, pairCharacter h q * conj (firstRowSum h N q.1) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hinner q
    _ = ∑ a ∈ Finset.range N,
        ∑ q ∈ Q.filter (fun q => q.1 = a),
          pairCharacter h q * conj (firstRowSum h N q.1) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := Q) (t := Finset.range N) (g := Prod.fst)
        (fun q hq => (Finset.mem_product.mp
          (Finset.mem_filter.mp hq).1).1)
        (fun q => pairCharacter h q * conj (firstRowSum h N q.1))
    _ = ∑ a ∈ Finset.range N,
        firstRowSum h N a * conj (firstRowSum h N a) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ q ∈ Q.filter (fun q => q.1 = a),
            pairCharacter h q * conj (firstRowSum h N q.1)) =
            ∑ q ∈ Q.filter (fun q => q.1 = a),
              pairCharacter h q * conj (firstRowSum h N a) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [(Finset.mem_filter.mp hq).2]
        _ = firstRowSum h N a * conj (firstRowSum h N a) := by
          rw [firstRowSum, firstRowDomain, Finset.sum_mul]
    _ = ∑ a ∈ Finset.range N,
        (Complex.normSq (T h N - u a ^ h) : ℂ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [firstRowSum_eq ha h, Complex.mul_conj]
      rw [Complex.normSq_mul, normSq_u_pow, Complex.normSq_conj]
      simp
    _ = ((N : ℝ) * X h N + N - 2 * X h N : ℂ) := by
      exact_mod_cast sum_normSq_T_sub_u h N

/-- The second-coordinate attacking sum is the same correction. -/
def secondRowDomain (N a : ℕ) : Finset (ℕ × ℕ) :=
  (orderedIndexPairs N).filter fun q => q.2 = a

def secondRowSum (h N a : ℕ) : ℂ :=
  ∑ q ∈ secondRowDomain N a, pairCharacter h q

theorem secondRowSum_eq
    {N a : ℕ} (ha : a ∈ Finset.range N) (h : ℕ) :
    secondRowSum h N a = (T h N - u a ^ h) * conj (u a ^ h) := by
  have hdomain : secondRowDomain N a =
      ((Finset.range N).filter (fun b => b ≠ a)).image (fun b => (b, a)) := by
    ext q
    rcases q with ⟨x, y⟩
    simp [secondRowDomain, orderedIndexPairs]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, hya⟩
      refine ⟨⟨hx, ?_⟩, hya.symm⟩
      intro hxa
      exact hxy (hxa.trans hya.symm)
    · rintro ⟨⟨hx, hxa⟩, hay⟩
      refine ⟨⟨⟨hx, hay ▸ Finset.mem_range.mp ha⟩, ?_⟩, hay.symm⟩
      intro hxy
      exact hxa (hxy.trans hay.symm)
  rw [secondRowSum, hdomain,
    Finset.sum_image (fun b _ c _ hbc => congrArg Prod.fst hbc)]
  simp only [pairCharacter]
  rw [← Finset.sum_mul]
  have hremove :
      (∑ b ∈ (Finset.range N).filter (fun b => b ≠ a), u b ^ h) =
        T h N - u a ^ h := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun b => b ≠ a) (fun b => u b ^ h)
    have hsingle :
        (∑ b ∈ (Finset.range N).filter (fun b => ¬b ≠ a), u b ^ h) =
          u a ^ h := by
      have heq : (Finset.range N).filter (fun b => ¬b ≠ a) = {a} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨hb, hba⟩
          exact Classical.not_not.mp hba
        · intro hba
          subst b
          exact ⟨Finset.mem_range.mp ha, by simp⟩
      rw [heq]
      simp
    rw [eq_sub_iff_add_eq, ← hsingle]
    simpa only [T] using hsplit
  rw [hremove]

theorem second_attack_sum (h N : ℕ) :
    (∑ qr ∈ (orderedIndexPairs N ×ˢ orderedIndexPairs N).filter
        (fun qr => qr.1.2 = qr.2.2),
      pairCharacter h qr.1 * conj (pairCharacter h qr.2)) =
      ((N : ℝ) * X h N + N - 2 * X h N : ℂ) := by
  let Q := orderedIndexPairs N
  rw [Finset.sum_filter, Finset.sum_product]
  have hinner (q : ℕ × ℕ) :
      (∑ r ∈ Q, if q.2 = r.2 then
          pairCharacter h q * conj (pairCharacter h r) else 0) =
        pairCharacter h q * conj (secondRowSum h N q.2) := by
    rw [← Finset.sum_filter]
    have heq : Q.filter (fun r => q.2 = r.2) = secondRowDomain N q.2 := by
      ext r
      simp [Q, secondRowDomain, eq_comm]
    rw [heq, ← Finset.mul_sum, ← map_sum]
    rfl
  calc
    (∑ q ∈ Q, ∑ r ∈ Q, if (q, r).1.2 = (q, r).2.2 then
        pairCharacter h (q, r).1 * conj (pairCharacter h (q, r).2) else 0) =
        ∑ q ∈ Q, pairCharacter h q * conj (secondRowSum h N q.2) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hinner q
    _ = ∑ a ∈ Finset.range N,
        ∑ q ∈ Q.filter (fun q => q.2 = a),
          pairCharacter h q * conj (secondRowSum h N q.2) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := Q) (t := Finset.range N) (g := Prod.snd)
        (fun q hq => (Finset.mem_product.mp
          (Finset.mem_filter.mp hq).1).2)
        (fun q => pairCharacter h q * conj (secondRowSum h N q.2))
    _ = ∑ a ∈ Finset.range N,
        secondRowSum h N a * conj (secondRowSum h N a) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ q ∈ Q.filter (fun q => q.2 = a),
            pairCharacter h q * conj (secondRowSum h N q.2)) =
            ∑ q ∈ Q.filter (fun q => q.2 = a),
              pairCharacter h q * conj (secondRowSum h N a) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [(Finset.mem_filter.mp hq).2]
        _ = secondRowSum h N a * conj (secondRowSum h N a) := by
          rw [secondRowSum, secondRowDomain, Finset.sum_mul]
    _ = ∑ a ∈ Finset.range N,
        (Complex.normSq (T h N - u a ^ h) : ℂ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [secondRowSum_eq ha h, Complex.mul_conj]
      rw [Complex.normSq_mul, Complex.normSq_conj, normSq_u_pow]
      simp
    _ = ((N : ℝ) * X h N + N - 2 * X h N : ℂ) := by
      exact_mod_cast sum_normSq_T_sub_u h N

theorem all_pair_product_sum (h N : ℕ) :
    (∑ qr ∈ orderedIndexPairs N ×ˢ orderedIndexPairs N,
      pairCharacter h qr.1 * conj (pairCharacter h qr.2)) =
      (((X h N - N) ^ 2 : ℝ) : ℂ) := by
  rw [Finset.sum_product]
  have hsum := sum_pairCharacter_eq h N
  calc
    (∑ q ∈ orderedIndexPairs N,
        ∑ r ∈ orderedIndexPairs N,
          pairCharacter h q * conj (pairCharacter h r)) =
        (∑ q ∈ orderedIndexPairs N, pairCharacter h q) *
          (∑ r ∈ orderedIndexPairs N, conj (pairCharacter h r)) := by
      rw [Finset.sum_mul_sum]
    _ = ((X h N - N : ℝ) : ℂ) *
          conj (((X h N - N : ℝ) : ℂ)) := by
      rw [hsum, ← map_sum, hsum]
    _ = (((X h N - N) ^ 2 : ℝ) : ℂ) := by
      norm_num
      ring

theorem both_attack_sum (h N : ℕ) :
    (∑ qr ∈ (orderedIndexPairs N ×ˢ orderedIndexPairs N).filter
        (fun qr => qr.1.1 = qr.2.1 ∧ qr.1.2 = qr.2.2),
      pairCharacter h qr.1 * conj (pairCharacter h qr.2)) =
      ((N * (N - 1) : ℕ) : ℂ) := by
  let Q := orderedIndexPairs N
  have heq : (Q ×ˢ Q).filter
      (fun qr => qr.1.1 = qr.2.1 ∧ qr.1.2 = qr.2.2) =
      Q.image (fun q => (q, q)) := by
    ext qr
    constructor
    · intro hqr
      have hm := Finset.mem_filter.mp hqr
      have hp := Finset.mem_product.mp hm.1
      have hpair : qr.1 = qr.2 := Prod.ext hm.2.1 hm.2.2
      exact Finset.mem_image.mpr ⟨qr.1, hp.1, Prod.ext rfl hpair⟩
    · intro hqr
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hqr
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hq, hq⟩, rfl, rfl⟩
  rw [show orderedIndexPairs N ×ˢ orderedIndexPairs N = Q ×ˢ Q from rfl,
    heq, Finset.sum_image (fun q _ r _ hqr => congrArg Prod.fst hqr)]
  simp_rw [Complex.mul_conj, normSq_pairCharacter]
  have hcard : Q.card = N * (N - 1) := orderedIndexPairs_card N
  rw [Finset.sum_const, nsmul_eq_mul, hcard]
  norm_num

/-- Inclusion-exclusion on the two attacking coordinates. This is the full
two-orientation form, before choosing positive primitive representatives. -/
theorem complete_nonattacking_identity (h N : ℕ) :
    (∑ qr ∈ nonattackingOrderedQuartets N,
      pairCharacter h qr.1 * conj (pairCharacter h qr.2)) =
      ((X h N ^ 2 - 4 * (N - 1) * X h N +
        2 * (N : ℝ) ^ 2 - 3 * N : ℝ) : ℂ) := by
  unfold nonattackingOrderedQuartets
  rw [sum_nonattacking_inclusion_exclusion
    (P := orderedIndexPairs N ×ˢ orderedIndexPairs N)
    (A := fun qr => qr.1.1 = qr.2.1)
    (B := fun qr => qr.1.2 = qr.2.2)
    (f := fun qr => pairCharacter h qr.1 * conj (pairCharacter h qr.2))]
  rw [all_pair_product_sum, first_attack_sum, second_attack_sum,
    both_attack_sum]
  have hcardCast : (((N * (N - 1) : ℕ) : ℂ)) =
      (N : ℂ) ^ 2 - N := by
    cases N with
    | zero => norm_num
    | succ n =>
        push_cast
        ring
  rw [hcardCast]
  push_cast
  ring

/-- Ordered coordinates of one T8/T49 record. -/
def recordCoordinates (q : OrderedLongPair) : ℕ × ℕ :=
  (orderedFirst q, orderedSecond q)

/-- The four ordered coordinates of a record pair. -/
def recordPairCoordinates (p : PrimitiveRecordPair) : (ℕ × ℕ) × (ℕ × ℕ) :=
  (recordCoordinates p.1, recordCoordinates p.2)

/-- T59's two-orientation primitive domain is exactly the block-product domain
with the two opposite-sign attacks excluded. -/
theorem mem_signedPrimitiveDomain_iff (Q0 t : ℕ) (p : PrimitiveRecordPair) :
    p ∈ signedPrimitiveDomain Q0 t ↔
      p.1 ∈ blockOrderedDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
        (⟨1, t + 2⟩ : DyadicBlock) ∧
      p.2 ∈ blockOrderedDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
        (⟨1, t + 2⟩ : DyadicBlock) ∧
      orderedFirst p.1 ≠ orderedFirst p.2 ∧
      orderedSecond p.1 ≠ orderedSecond p.2 := by
  classical
  constructor
  · intro hp
    obtain ⟨⟨b, r⟩, hb, rfl⟩ := Finset.mem_image.mp hp
    have hr := Finset.mem_product.mp hb |>.2
    have hcoords := (mem_C_domain_iff_nonattacking Q0 t r).mp hr
    have hblock1 := (mem_boxOrderedDomain_iff Q0 t r.1).mpr
      ⟨hcoords.1, hcoords.2.1, hcoords.2.2.2.2.1⟩
    have hblock2 := (mem_boxOrderedDomain_iff Q0 t r.2).mpr
      ⟨hcoords.2.2.1, hcoords.2.2.2.1, hcoords.2.2.2.2.2.1⟩
    cases b
    · simpa [orientPositiveDifference] using
        And.intro hblock1 (And.intro hblock2
          (And.intro hcoords.2.2.2.2.2.2.1 hcoords.2.2.2.2.2.2.2.1))
    · simpa [orientPositiveDifference] using
        And.intro hblock2 (And.intro hblock1
          (And.intro hcoords.2.2.2.2.2.2.1.symm
            hcoords.2.2.2.2.2.2.2.1.symm))
  · rintro ⟨hp, hq, hfirst, hsecond⟩
    have hpCoords := (mem_boxOrderedDomain_iff Q0 t p.1).mp hp
    have hqCoords := (mem_boxOrderedDomain_iff Q0 t p.2).mp hq
    have hfreq : signedDecimalFrequency p.1 ≠ signedDecimalFrequency p.2 := by
      intro heq
      have hpEq := signedDecimalFrequency_injOn_block
        8 1 Q0 1 (4 * 2 ^ t + 1) (⟨1, t + 2⟩ : DyadicBlock)
        hp hq heq
      exact hfirst (congrArg (fun r => orderedFirst r) hpEq)
    rcases lt_or_gt_of_ne hfreq with hlt | hgt
    · have hr : p.swap ∈ primitiveRecordDomain 8 1 Q0 1
          (4 * 2 ^ t + 1) (⟨1, t + 2⟩ : DyadicBlock) := by
        apply (mem_C_domain_iff_nonattacking Q0 t p.swap).mpr
        change orderedFirst p.2 < 4 * 2 ^ t + 1 ∧
          orderedSecond p.2 < 4 * 2 ^ t + 1 ∧
          orderedFirst p.1 < 4 * 2 ^ t + 1 ∧
          orderedSecond p.1 < 4 * 2 ^ t + 1 ∧
          orderedFirst p.2 ≠ orderedSecond p.2 ∧
          orderedFirst p.1 ≠ orderedSecond p.1 ∧
          orderedFirst p.2 ≠ orderedFirst p.1 ∧
          orderedSecond p.2 ≠ orderedSecond p.1 ∧
          signedDecimalFrequency p.1 < signedDecimalFrequency p.2
        exact ⟨hqCoords.1, hqCoords.2.1, hpCoords.1,
          hpCoords.2.1, hqCoords.2.2, hpCoords.2.2,
          hfirst.symm, hsecond.symm, hlt⟩
      exact Finset.mem_image.mpr
        ⟨(true, p.swap), Finset.mem_product.mpr ⟨Finset.mem_univ _, hr⟩,
          by simp [orientPositiveDifference]⟩
    · have hr : p ∈ primitiveRecordDomain 8 1 Q0 1
          (4 * 2 ^ t + 1) (⟨1, t + 2⟩ : DyadicBlock) := by
        apply (mem_C_domain_iff_nonattacking Q0 t p).mpr
        exact ⟨hpCoords.1, hpCoords.2.1, hqCoords.1, hqCoords.2.1,
          hpCoords.2.2, hqCoords.2.2, hfirst, hsecond, hgt⟩
      exact Finset.mem_image.mpr
        ⟨(false, p), Finset.mem_product.mpr ⟨Finset.mem_univ _, hr⟩,
          by simp [orientPositiveDifference]⟩

/-- No quotient is hidden: ordered coordinates biject T59's complete signed
primitive domain with the literal nonattacking quartet domain. -/
theorem signedPrimitive_coordinates_image (Q0 t : ℕ) :
    (signedPrimitiveDomain Q0 t).image recordPairCoordinates =
      nonattackingOrderedQuartets (4 * 2 ^ t + 1) := by
  classical
  ext qr
  constructor
  · intro hqr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hqr
    have hm := (mem_signedPrimitiveDomain_iff Q0 t p).mp hp
    have hpCoords := (mem_boxOrderedDomain_iff Q0 t p.1).mp hm.1
    have hqCoords := (mem_boxOrderedDomain_iff Q0 t p.2).mp hm.2.1
    apply (mem_nonattackingOrderedQuartets_iff _ _).mpr
    exact ⟨hpCoords.1, hpCoords.2.1, hqCoords.1, hqCoords.2.1,
      hpCoords.2.2, hqCoords.2.2, hm.2.2.1, hm.2.2.2⟩
  · intro hqr
    have hm := (mem_nonattackingOrderedQuartets_iff _ _).mp hqr
    have hpPair : qr.1 ∈ fullOrderedPairDomain (4 * 2 ^ t + 1) := by
      change qr.1 ∈ orderedIndexPairs (4 * 2 ^ t + 1)
      exact (Finset.mem_product.mp
        (Finset.mem_filter.mp hqr).1).1
    have hqPair : qr.2 ∈ fullOrderedPairDomain (4 * 2 ^ t + 1) := by
      change qr.2 ∈ orderedIndexPairs (4 * 2 ^ t + 1)
      exact (Finset.mem_product.mp
        (Finset.mem_filter.mp hqr).1).2
    obtain ⟨p, hp, hpCoord⟩ := exists_orderedLongPair_at_one
      Q0 (4 * 2 ^ t + 1) hpPair
    obtain ⟨q, hq, hqCoord⟩ := exists_orderedLongPair_at_one
      Q0 (4 * 2 ^ t + 1) hqPair
    have hpFirst : orderedFirst p = qr.1.1 := by
      simpa using congrArg Prod.fst hpCoord
    have hpSecond : orderedSecond p = qr.1.2 := by
      simpa using congrArg Prod.snd hpCoord
    have hqFirst : orderedFirst q = qr.2.1 := by
      simpa using congrArg Prod.fst hqCoord
    have hqSecond : orderedSecond q = qr.2.2 := by
      simpa using congrArg Prod.snd hqCoord
    have hpBlock : p ∈ blockOrderedDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
        (⟨1, t + 2⟩ : DyadicBlock) :=
      (mem_boxOrderedDomain_iff Q0 t p).mpr
        (by rw [hpFirst, hpSecond]
            exact ⟨hm.1, hm.2.1, hm.2.2.2.2.1⟩)
    have hqBlock : q ∈ blockOrderedDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
        (⟨1, t + 2⟩ : DyadicBlock) :=
      (mem_boxOrderedDomain_iff Q0 t q).mpr
        (by rw [hqFirst, hqSecond]
            exact ⟨hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.2.1⟩)
    have hpq : (p, q) ∈ signedPrimitiveDomain Q0 t :=
      (mem_signedPrimitiveDomain_iff Q0 t (p, q)).mpr
        ⟨hpBlock, hqBlock, by
            rw [hpFirst, hqFirst]
            exact hm.2.2.2.2.2.2.1,
          by
            rw [hpSecond, hqSecond]
            exact hm.2.2.2.2.2.2.2⟩
    exact Finset.mem_image.mpr ⟨(p, q), hpq, by
      simp [recordPairCoordinates, recordCoordinates, hpCoord, hqCoord]⟩

theorem recordPairCoordinates_injOn (Q0 t : ℕ) :
    Set.InjOn recordPairCoordinates (signedPrimitiveDomain Q0 t : Set _) := by
  intro p hp q hq heq
  have hpMem := (mem_signedPrimitiveDomain_iff Q0 t p).mp hp
  have hqMem := (mem_signedPrimitiveDomain_iff Q0 t q).mp hq
  have hp1 := (Finset.mem_filter.mp hpMem.1).1
  have hp2 := (Finset.mem_filter.mp hpMem.2.1).1
  have hq1 := (Finset.mem_filter.mp hqMem.1).1
  have hq2 := (Finset.mem_filter.mp hqMem.2.1).1
  apply Prod.ext
  · apply orderedCoordinates_injective_at_one hp1 hq1
    exact congrArg Prod.fst heq
  · apply orderedCoordinates_injective_at_one hp2 hq2
    exact congrArg Prod.snd heq

/-- Character attached to one signed ordered record pair. -/
def recordPairCharacter (h : ℕ) (p : PrimitiveRecordPair) : ℂ :=
  pairCharacter h (recordCoordinates p.1) *
    conj (pairCharacter h (recordCoordinates p.2))

theorem pairCharacter_record_eq (h : ℕ) (q : OrderedLongPair) :
    pairCharacter h (recordCoordinates q) =
      Theory.PiDigits.T27.phase (h : ℤ)
        ((signedDecimalFrequency q : ℝ) * Real.pi) := by
  unfold pairCharacter recordCoordinates
  rw [u_pow_eq_phase, u_pow_eq_phase,
    phase_mul_conj_phase_eq_sub_real]
  rw [signedDecimalFrequency_eq_orderedPhaseFrequency]
  unfold orderedPhaseFrequency
  congr 1
  push_cast
  ring

theorem recordPairCharacter_eq_phase
    {Q0 t : ℕ} {p : PrimitiveRecordPair}
    (hp : p ∈ primitiveRecordDomain 8 1 Q0 1 (4 * 2 ^ t + 1)
      (⟨1, t + 2⟩ : DyadicBlock)) (h : ℕ) :
    recordPairCharacter h p =
      Theory.PiDigits.T27.phase ((h : ℤ) * (blockDifferenceValue p : ℤ))
        Real.pi := by
  unfold recordPairCharacter
  rw [pairCharacter_record_eq, pairCharacter_record_eq,
    phase_mul_conj_phase_eq_sub_real]
  have hcast := blockPositiveDifferenceValue_cast
    (primitiveBlockDifferenceDomain_subset hp)
  have hcastR : (blockDifferenceValue p : ℝ) =
      (signedDecimalFrequency p.1 : ℝ) -
        (signedDecimalFrequency p.2 : ℝ) := by
    exact_mod_cast hcast
  unfold Theory.PiDigits.T27.phase
  congr 1
  push_cast
  have hcastC : (blockDifferenceValue p : ℂ) =
      (signedDecimalFrequency p.1 : ℂ) -
        (signedDecimalFrequency p.2 : ℂ) := by
    exact_mod_cast hcast
  rw [← sub_mul, ← hcastC]
  ring

theorem recordPairCharacter_swap (h : ℕ) (p : PrimitiveRecordPair) :
    recordPairCharacter h p.swap = conj (recordPairCharacter h p) := by
  rcases p with ⟨p, q⟩
  unfold recordPairCharacter
  change pairCharacter h (recordCoordinates q) *
      conj (pairCharacter h (recordCoordinates p)) =
    conj (pairCharacter h (recordCoordinates p) *
      conj (pairCharacter h (recordCoordinates q)))
  simp only [map_mul, starRingEnd_self_apply]
  ring

theorem phase_re_eq_literal_cosine (h d : ℕ) :
    (Theory.PiDigits.T27.phase ((h : ℤ) * (d : ℤ)) Real.pi).re =
      Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ)) := by
  unfold Theory.PiDigits.T27.phase
  have harg :
      (2 * (Real.pi : ℂ) * Complex.I *
          (((h : ℤ) * (d : ℤ) : ℤ) : ℂ) * (Real.pi : ℂ)) =
        (((2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I]
  rw [Complex.add_re, Complex.mul_re]
  norm_num only [Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  norm_num

theorem signedPrimitive_sum_eq_two_C (Q0 t h : ℕ) :
    (∑ p ∈ signedPrimitiveDomain Q0 t, recordPairCharacter h p) =
      ((2 * C Q0 t h : ℝ) : ℂ) := by
  rw [signedPrimitiveDomain]
  simp only [boxEndpoint, boxLength, boxBlock]
  unfold primitiveRecordDomain
  rw [Finset.sum_image (fun a ha b hb hab =>
    orientPositiveDifference_injOn_block 8 1 Q0 1
      (4 * 2 ^ t + 1) (⟨1, t + 2⟩ : DyadicBlock)
      (Finset.mem_product.mpr ⟨(Finset.mem_product.mp ha).1,
        primitiveBlockDifferenceDomain_subset (Finset.mem_product.mp ha).2⟩)
      (Finset.mem_product.mpr ⟨(Finset.mem_product.mp hb).1,
        primitiveBlockDifferenceDomain_subset (Finset.mem_product.mp hb).2⟩) hab)]
  rw [Finset.sum_product]
  simp
  rw [← Finset.sum_add_distrib]
  unfold C
  unfold primitiveRecordDomain
  rw [Complex.ofReal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [orientPositiveDifference, Bool.false_eq_true, ↓reduceIte]
  rw [recordPairCharacter_swap, recordPairCharacter_eq_phase hp]
  rw [add_comm, Complex.add_conj]
  rw [phase_re_eq_literal_cosine]
  norm_num

theorem nonattacking_sum_eq_two_C (Q0 t h : ℕ) :
    (∑ qr ∈ nonattackingOrderedQuartets (4 * 2 ^ t + 1),
      pairCharacter h qr.1 * conj (pairCharacter h qr.2)) =
      ((2 * C Q0 t h : ℝ) : ℂ) := by
  rw [← signedPrimitive_coordinates_image Q0 t]
  rw [Finset.sum_image (fun p hp q hq hpq =>
    recordPairCoordinates_injOn Q0 t hp hq hpq)]
  change (∑ p ∈ signedPrimitiveDomain Q0 t, recordPairCharacter h p) = _
  exact signedPrimitive_sum_eq_two_C Q0 t h

/-- The exact candidate identity, independently kernel-checked at every
dyadic one-block scale and each literal frequency `1 <= h <= 10`. -/
theorem C_eq_fourthMoment
    (Q0 t h : ℕ) (_hh : h ∈ Finset.Icc 1 10) :
    C Q0 t h =
      (X h (4 * 2 ^ t + 1) ^ 2 -
        4 * ((4 * 2 ^ t + 1 : ℕ) - 1) * X h (4 * 2 ^ t + 1) +
        2 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
        3 * (4 * 2 ^ t + 1 : ℕ)) / 2 := by
  have hfull := complete_nonattacking_identity h (4 * 2 ^ t + 1)
  rw [nonattacking_sum_eq_two_C Q0 t h] at hfull
  have hreal :
      2 * C Q0 t h =
        X h (4 * 2 ^ t + 1) ^ 2 -
          4 * ((4 * 2 ^ t + 1 : ℕ) - 1) * X h (4 * 2 ^ t + 1) +
          2 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
          3 * (4 * 2 ^ t + 1 : ℕ) := by
    exact_mod_cast hfull
  linarith

/-- Exact finite recombination of the T59 selected and unmatched-defect
positive representatives. The factor `2` is the two signed orientations;
frequencies are literally `1,...,10`, and the denominator is the literal
T29 width `sqrt((4*2^t+1)^2-1)`. -/
theorem complete_selected_defect_recombination (Q0 t : ℕ) :
    (2 : ℝ) * (
      (∑ p ∈ selectedRecordDomain t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1)) +
      (∑ p ∈ unmatchedDefect Q0 t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1))) =
      (1 / Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1)) *
        ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          (X h (4 * 2 ^ t + 1) ^ 2 -
            4 * ((4 * 2 ^ t + 1 : ℕ) - 1) * X h (4 * 2 ^ t + 1) +
            2 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
            3 * (4 * 2 ^ t + 1 : ℕ)) := by
  have hw := boxWidth_literal t
  simp only [boxEndpoint, boxLength] at hw
  rw [← hw]
  let K : PrimitiveRecordPair → ℕ → ℝ := fun p h =>
    Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
      (blockDifferenceValue p : ℝ))
  have hpart := selected_defect_exhaustive_partition Q0 t
  have hrecords :
      (∑ p ∈ selectedRecordDomain t,
          ∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) +
        (∑ p ∈ unmatchedDefect Q0 t,
          ∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) =
        ∑ p ∈ primitiveRecordDomain 8 1 Q0 1
          (4 * 2 ^ t + 1) (⟨1, t + 2⟩ : DyadicBlock),
            ∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h := by
    rw [← Finset.sum_union hpart.2.1]
    simpa only [boxEndpoint, boxLength, boxBlock] using
      congrArg (fun s : Finset PrimitiveRecordPair =>
        ∑ p ∈ s, ∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) hpart.2.2.symm
  have hcommute :
      (∑ p ∈ primitiveRecordDomain 8 1 Q0 1
          (4 * 2 ^ t + 1) (⟨1, t + 2⟩ : DyadicBlock),
            ∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) =
        ∑ h ∈ Finset.Icc (1 : ℕ) 10, C Q0 t h := by
    unfold C
    exact Finset.sum_comm
  have hsubstitute :
      (∑ h ∈ Finset.Icc (1 : ℕ) 10, C Q0 t h) =
        ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          (X h (4 * 2 ^ t + 1) ^ 2 -
            4 * ((4 * 2 ^ t + 1 : ℕ) - 1) * X h (4 * 2 ^ t + 1) +
            2 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
            3 * (4 * 2 ^ t + 1 : ℕ)) / 2 := by
    apply Finset.sum_congr rfl
    intro h hh
    exact C_eq_fourthMoment Q0 t h hh
  change 2 * ((∑ p ∈ selectedRecordDomain t,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) /
        widthWeight (boxBlock t)) +
    ∑ p ∈ unmatchedDefect Q0 t,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) /
        widthWeight (boxBlock t)) = _
  rw [← Finset.sum_div, ← Finset.sum_div]
  calc
    2 * (((∑ p ∈ selectedRecordDomain t,
          ∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) /
            widthWeight (boxBlock t)) +
        ((∑ p ∈ unmatchedDefect Q0 t,
          ∑ h ∈ Finset.Icc (1 : ℕ) 10, K p h) /
            widthWeight (boxBlock t))) =
        (2 / widthWeight (boxBlock t)) *
          ∑ h ∈ Finset.Icc (1 : ℕ) 10, C Q0 t h := by
      rw [← hcommute, ← hrecords]
      ring
    _ = (1 / widthWeight (boxBlock t)) *
        ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          (X h (4 * 2 ^ t + 1) ^ 2 -
            4 * ((4 * 2 ^ t + 1 : ℕ) - 1) * X h (4 * 2 ^ t + 1) +
            2 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
            3 * (4 * 2 ^ t + 1 : ℕ)) := by
      rw [hsubstitute]
      rw [← Finset.sum_div]
      ring

/-- The remaining fixed-pi frontier. This is deliberately only a proposition:
no declaration in this module supplies a witness or proves it. -/
def FixedPiDyadicFourthMomentBound : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℕ,
    ∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1) ^ 2 ≤
      A * (4 * 2 ^ t + 1 : ℕ) ^ 2

end Theory.PiDigits.LongLagBlockCollisionDecay.T63

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.u_pow_eq_phase
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.dyadic_one_block_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.mem_C_domain_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.mem_C_domain_iff_nonattacking
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.both_orientations_sign_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.mem_nonattackingOrderedQuartets_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.complete_nonattacking_identity
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.mem_signedPrimitiveDomain_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.signedPrimitive_coordinates_image
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.recordPairCoordinates_injOn
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.signedPrimitive_sum_eq_two_C
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.nonattacking_sum_eq_two_C
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.C_eq_fourthMoment
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T63.complete_selected_defect_recombination
