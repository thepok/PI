import TheoryLib.PiPositiveLowerBlockDensity.T1PiPositiveLowerBlockDensity
import TheoryLib.PiPositiveLowerBlockDensity.T8T8AlignedEntropyDeficit
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# T9: finite-prefix entropy deficit under failure of C1

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only a necessary consequence of the literal negation of
canonical C1. It makes no unconditional assertion about pi or C1. A word of
length `L` is sampled from the first `N` digits only at starts `n` satisfying
`n + L ≤ N`; thus every sampled word is fully contained. "Aligned" refers to
the decomposition of each sampled length-`m * ell` word into `m` consecutive
length-`ell` chunks, not to a restriction on the sample starts.
-/

noncomputable section

open Filter Finset Set Topology

namespace Theory.PiDigits.PositiveLowerBlockDensity.T9

open Theory.PiDigits.PositiveLowerBlockDensity

/-- Starts of length-`L` words fully contained in a prefix of length `N`.
When `L ≤ N`, these are exactly `0 ≤ n ≤ N - L`. -/
abbrev FullyContainedStart (N L : ℕ) := Fin (N + 1 - L)

/-- The length-`L` word beginning at a fully contained start. -/
def prefixWord (s : ℕ → Fin 10) (N L : ℕ) (n : FullyContainedStart N L) :
    Fin L → Fin 10 :=
  fun i => s (n.val + i.val)

/-- Number of fully contained samples of a specified length-`L` word. -/
def fullyContainedWordCount (s : ℕ → Fin 10) (N L : ℕ)
    (u : Fin L → Fin 10) : ℕ :=
  (Finset.univ.filter fun n : FullyContainedStart N L =>
    prefixWord s N L n = u).card

/-- Empirical probability of a length-`L` word among all fully contained
samples from a prefix of length `N`. -/
def fullyContainedWordProbability (s : ℕ → Fin 10) (N L : ℕ)
    (u : Fin L → Fin 10) : ℝ :=
  fullyContainedWordCount s N L u / ((N + 1 - L : ℕ) : ℝ)

/-- Shannon entropy (natural logarithm) of the fully contained empirical
length-`L` word distribution in a prefix of length `N`. -/
def fullyContainedShannonEntropy (s : ℕ → Fin 10) (N L : ℕ) : ℝ :=
  ∑ u : Fin L → Fin 10,
    Real.negMulLog (fullyContainedWordProbability s N L u)

/-- Exact full-containment bookkeeping, including the sample count and the
inequality which excludes the discarded suffix. -/
theorem fullContainment_bookkeeping {N L : ℕ} (hLN : L ≤ N) :
    Fintype.card (FullyContainedStart N L) = N + 1 - L ∧
      (∀ n : FullyContainedStart N L, n.val + L ≤ N) := by
  constructor
  · simp [FullyContainedStart]
  · intro n
    have hn : n.val < N + 1 - L := n.isLt
    omega

theorem fullyContainedWordProbability_nonneg (s : ℕ → Fin 10)
    (N L : ℕ) (u : Fin L → Fin 10) :
    0 ≤ fullyContainedWordProbability s N L u := by
  exact div_nonneg (by positivity) (by positivity)

/-- The fully contained empirical word probabilities sum to one whenever at
least one fully contained start exists. -/
theorem sum_fullyContainedWordProbability (s : ℕ → Fin 10)
    {N L : ℕ} (hLN : L ≤ N) :
    ∑ u : Fin L → Fin 10, fullyContainedWordProbability s N L u = 1 := by
  classical
  have hcount :
      ∑ u : Fin L → Fin 10, fullyContainedWordCount s N L u = N + 1 - L := by
    have hfiber := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (FullyContainedStart N L)))
      (t := (Finset.univ : Finset (Fin L → Fin 10)))
      (f := prefixWord s N L) (by simp)
    simpa [fullyContainedWordCount] using hfiber.symm
  have hden : ((N + 1 - L : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N + 1 - L ≠ 0)
  simp only [fullyContainedWordProbability, ← Finset.sum_div]
  rw [← Nat.cast_sum, hcount]
  exact div_self hden

/-- A finite probability vector whose exceptional mass is at most `q` and
whose ordinary support has size at most `A` has entropy at most
`log A + log 2 + q log B`, where `B` bounds the full alphabet size. -/
theorem contaminatedSupport_entropy_bound {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → ℝ) (good : Finset ι)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {A B : ℕ} (hgoodCard : good.card ≤ A)
    (hfullCard : Fintype.card ι ≤ B) {q : ℝ}
    (hq : ∑ i ∈ goodᶜ, p i ≤ q) :
    ∑ i, Real.negMulLog (p i) ≤
      Real.log A + Real.log 2 + q * Real.log B := by
  classical
  have entropy_subset_le (S : Finset ι) (M : ℕ) (hcard : S.card ≤ M) :
      (∑ i ∈ S, Real.negMulLog (p i)) ≤
        Real.negMulLog (∑ i ∈ S, p i) +
          (∑ i ∈ S, p i) * Real.log M := by
    by_cases hS : S.Nonempty
    · have hScard : 0 < S.card := Finset.card_pos.mpr hS
      have hweights : (∑ _i ∈ S, ((S.card : ℝ)⁻¹)) = 1 := by
        simp [hScard.ne']
      have hjensen := Real.concaveOn_negMulLog.le_map_sum
        (t := S) (w := fun _i => (S.card : ℝ)⁻¹) (p := p)
        (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg S.card)) hweights
        (fun i _ => hp0 i)
      have hjensen' :
          (S.card : ℝ)⁻¹ * (∑ i ∈ S, Real.negMulLog (p i)) ≤
            Real.negMulLog ((S.card : ℝ)⁻¹ * (∑ i ∈ S, p i)) := by
        simpa only [smul_eq_mul, Function.comp_apply, ← Finset.mul_sum] using hjensen
      have hcardReal : 0 < (S.card : ℝ) := by exact_mod_cast hScard
      have hcardReal_ne : (S.card : ℝ) ≠ 0 := hcardReal.ne'
      have hinvEntropy :
          (S.card : ℝ) * Real.negMulLog (S.card : ℝ)⁻¹ =
            Real.log S.card := by
        rw [Real.negMulLog, Real.log_inv]
        field_simp
      have hraw :
          (∑ i ∈ S, Real.negMulLog (p i)) ≤
            Real.negMulLog (∑ i ∈ S, p i) +
              (∑ i ∈ S, p i) * Real.log S.card := by
        calc
          (∑ i ∈ S, Real.negMulLog (p i)) =
              (S.card : ℝ) *
                ((S.card : ℝ)⁻¹ *
                  (∑ i ∈ S, Real.negMulLog (p i))) := by
                    field_simp
          _ ≤ (S.card : ℝ) *
                Real.negMulLog
                  ((S.card : ℝ)⁻¹ * (∑ i ∈ S, p i)) :=
              mul_le_mul_of_nonneg_left hjensen' hcardReal.le
          _ = Real.negMulLog (∑ i ∈ S, p i) +
                (∑ i ∈ S, p i) * Real.log S.card := by
              rw [mul_comm (S.card : ℝ)⁻¹, Real.negMulLog_mul]
              calc
                (S.card : ℝ) *
                    ((S.card : ℝ)⁻¹ *
                        Real.negMulLog (∑ i ∈ S, p i) +
                      (∑ i ∈ S, p i) *
                        Real.negMulLog (S.card : ℝ)⁻¹) =
                    ((S.card : ℝ) * (S.card : ℝ)⁻¹) *
                        Real.negMulLog (∑ i ∈ S, p i) +
                      (∑ i ∈ S, p i) *
                        ((S.card : ℝ) *
                          Real.negMulLog (S.card : ℝ)⁻¹) := by
                    ring
                _ = _ := by
                  rw [mul_inv_cancel₀ hcardReal_ne, one_mul, hinvEntropy]
      have hlog : Real.log S.card ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast hScard) (by exact_mod_cast hcard)
      have hmass : 0 ≤ ∑ i ∈ S, p i :=
        Finset.sum_nonneg fun i _ => hp0 i
      exact hraw.trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hmass))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp
  let r := ∑ i ∈ good, p i
  let t := ∑ i ∈ goodᶜ, p i
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun i _ => hp0 i
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => hp0 i
  have hrt : r + t = 1 := (good.sum_add_sum_compl p).trans hp1
  have hr : r = 1 - t := by linarith
  have hgood := entropy_subset_le good A hgoodCard
  have hbad := entropy_subset_le goodᶜ B
    ((goodᶜ).card_le_univ.trans hfullCard)
  calc
    ∑ i, Real.negMulLog (p i) =
        (∑ i ∈ good, Real.negMulLog (p i)) +
          ∑ i ∈ goodᶜ, Real.negMulLog (p i) :=
      (good.sum_add_sum_compl _).symm
    _ ≤ (Real.negMulLog r + r * Real.log A) +
          (Real.negMulLog t + t * Real.log B) := add_le_add hgood hbad
    _ = Real.binEntropy t + r * Real.log A + t * Real.log B := by
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, ← hr]
      ring
    _ ≤ Real.log 2 + Real.log A + q * Real.log B := by
      have hr1 : r ≤ 1 := by linarith
      have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
      have hlogB : 0 ≤ Real.log B := Real.log_natCast_nonneg B
      have hAr : r * Real.log A ≤ Real.log A := by
        simpa using mul_le_mul_of_nonneg_right hr1 hlogA
      have hBq : t * Real.log B ≤ q * Real.log B :=
        mul_le_mul_of_nonneg_right hq hlogB
      linarith [Real.binEntropy_le_log_two (p := t)]
    _ = Real.log A + Real.log 2 + q * Real.log B := by ring

/-- The `j`th consecutive length-`ell` chunk of a length-`m * ell` word. -/
def alignedChunk {ell m : ℕ} (u : Fin (m * ell) → Fin 10) (j : Fin m) :
    Fin ell → Fin 10 :=
  fun i => u ⟨j.val * ell + i.val, by
    have hj : (j.val + 1) * ell ≤ m * ell :=
      Nat.mul_le_mul_right ell (Nat.succ_le_of_lt j.isLt)
    have hi : j.val * ell + i.val < (j.val + 1) * ell := by
      simpa [Nat.add_mul] using Nat.add_lt_add_left i.isLt (j.val * ell)
    exact hi.trans_le hj⟩

/-- Long words all of whose aligned chunks avoid a specified word. -/
def OrdinaryWord {ell m : ℕ} (w : Fin ell → Fin 10) :=
  {u : Fin (m * ell) → Fin 10 // ∀ j : Fin m, alignedChunk u j ≠ w}

/-- The ordinary words as a finset in the full length-`m * ell` alphabet. -/
def ordinaryWords {ell m : ℕ} (w : Fin ell → Fin 10) :
    Finset (Fin (m * ell) → Fin 10) :=
  Finset.univ.filter fun u => ∀ j : Fin m, alignedChunk u j ≠ w

/-- Aligned chunks determine the whole long word when `ell > 0`. -/
theorem alignedChunks_injective {ell m : ℕ} (hell : 0 < ell) :
    Function.Injective
      (fun u : Fin (m * ell) → Fin 10 => fun j : Fin m => alignedChunk u j) := by
  intro u v huv
  funext q
  let j : Fin m := ⟨q.val / ell, (Nat.div_lt_iff_lt_mul hell).2 q.isLt⟩
  let i : Fin ell := ⟨q.val % ell, Nat.mod_lt q.val hell⟩
  have hvalue := congrFun (congrFun huv j) i
  have hindex : q.val / ell * ell + q.val % ell = q.val :=
    Nat.div_add_mod' q.val ell
  simpa [alignedChunk, j, i, hindex] using hvalue

/-- At most `(10^ell - 1)^m` words avoid one specified word in all `m`
aligned chunks. -/
theorem ordinaryWords_card_le {ell m : ℕ} (hell : 0 < ell)
    (w : Fin ell → Fin 10) :
    (ordinaryWords (m := m) w).card ≤ (10 ^ ell - 1) ^ m := by
  classical
  let allowed := {v : (Fin ell → Fin 10) // v ≠ w}
  let target : Finset (Fin m → allowed) := Finset.univ
  let encode : (ordinaryWords (m := m) w : Finset _) → target := fun u =>
    ⟨fun j => ⟨alignedChunk u.1 j, by
      exact (Finset.mem_filter.mp u.2).2 j⟩, by simp [target]⟩
  have hinjective : Function.Injective encode := by
    intro u v huv
    apply Subtype.ext
    apply alignedChunks_injective hell
    funext j
    exact congrArg Subtype.val
      (congrFun (congrArg Subtype.val huv) j)
  have hcard := Finset.card_le_card_of_injective hinjective
  have hallowed : Fintype.card allowed = 10 ^ ell - 1 := by
    simp [allowed, Fintype.card_subtype_compl]
  simpa [target, Fintype.card_congr (Equiv.refl allowed), hallowed] using hcard

/-- Fully contained starts whose `j`th aligned chunk equals `w`. -/
def badStartsAt (s : ℕ → Fin 10) (N ell m : ℕ)
    (w : Fin ell → Fin 10) (j : Fin m) :
    Finset (FullyContainedStart N (m * ell)) :=
  Finset.univ.filter fun n =>
    alignedChunk (prefixWord s N (m * ell) n) j = w

/-- Fully contained starts carrying the forbidden word in at least one of
their `m` aligned positions. -/
def contaminatedStarts (s : ℕ → Fin 10) (N ell m : ℕ)
    (w : Fin ell → Fin 10) : Finset (FullyContainedStart N (m * ell)) :=
  Finset.univ.filter fun n => ∃ j : Fin m,
    alignedChunk (prefixWord s N (m * ell) n) j = w

/-- For a fixed aligned position, shifting a sample start to the corresponding
word start injects into T1's overlapping block count. -/
theorem badStartsAt_card_le_blockCount (s : ℕ → Fin 10)
    {N ell m : ℕ} (hell : 0 < ell) (hfull : m * ell ≤ N)
    (w : Fin ell → Fin 10) (j : Fin m) :
    (badStartsAt s N ell m w j).card ≤
      blockCount s (List.ofFn w) N := by
  classical
  let target : Finset (Fin N) := Finset.univ.filter fun r =>
    ∀ i : Fin ell, s (r.val + i.val) = w i
  let shift : {n // n ∈ badStartsAt s N ell m w j} →
      {r // r ∈ target} := fun n => by
    have hnfull : n.val.val + m * ell ≤ N :=
      (fullContainment_bookkeeping hfull).2 n.val
    have hjlt : j.val * ell < m * ell :=
      Nat.mul_lt_mul_of_pos_right j.isLt hell
    have hshiftlt : n.val.val + j.val * ell < N :=
      (Nat.add_lt_add_left hjlt n.val.val).trans_le hnfull
    refine ⟨⟨n.val.val + j.val * ell, hshiftlt⟩, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    have hchunk := congrFun (Finset.mem_filter.mp n.2).2 i
    simpa [alignedChunk, prefixWord, Nat.add_assoc] using hchunk
  have hinjective : Function.Injective shift := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg (fun x : {r // r ∈ target} => x.val.val) hab
    dsimp [shift] at hval
    apply Fin.ext
    exact Nat.add_right_cancel hval
  have hcard := Finset.card_le_card_of_injective hinjective
  have htarget : target.card = blockCount s (List.ofFn w) N := by
    unfold target blockCount
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h i
      simpa only [List.get_ofFn] using
        h (Fin.cast (by simp) i)
    · intro h i
      simpa only [List.get_ofFn] using
        h (Fin.cast (by simp) i)
  simpa [htarget] using hcard

/-- Finite contamination bound: at most `m` times the overlapping count of
the forbidden length-`ell` word can contaminate fully contained long samples. -/
theorem contaminatedStarts_card_le (s : ℕ → Fin 10)
    {N ell m : ℕ} (hell : 0 < ell) (hfull : m * ell ≤ N)
    (w : Fin ell → Fin 10) :
    (contaminatedStarts s N ell m w).card ≤
      m * blockCount s (List.ofFn w) N := by
  classical
  have heq : contaminatedStarts s N ell m w =
      (Finset.univ : Finset (Fin m)).biUnion
        (badStartsAt s N ell m w) := by
    ext n
    simp [contaminatedStarts, badStartsAt]
  rw [heq]
  calc
    ((Finset.univ : Finset (Fin m)).biUnion
        (badStartsAt s N ell m w)).card ≤
        ∑ j : Fin m, (badStartsAt s N ell m w j).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin m, blockCount s (List.ofFn w) N := by
      apply Finset.sum_le_sum
      intro j _
      exact badStartsAt_card_le_blockCount s hell hfull w j
    _ = m * blockCount s (List.ofFn w) N := by simp

/-- The empirical mass outside the ordinary-word finset is exactly the
fraction of contaminated fully contained starts. -/
theorem exceptionalMass_eq_contaminatedFraction (s : ℕ → Fin 10)
    {N ell m : ℕ} (_hfull : m * ell ≤ N) (w : Fin ell → Fin 10) :
    (∑ u ∈ (ordinaryWords (m := m) w)ᶜ,
        fullyContainedWordProbability s N (m * ell) u) =
      (contaminatedStarts s N ell m w).card /
        ((N + 1 - m * ell : ℕ) : ℝ) := by
  classical
  let good := ordinaryWords (m := m) w
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (FullyContainedStart N (m * ell))))
    (t := goodᶜ) (g := prefixWord s N (m * ell))
  have hfiltered :
      (Finset.univ.filter fun n : FullyContainedStart N (m * ell) =>
          prefixWord s N (m * ell) n ∈ goodᶜ) =
        contaminatedStarts s N ell m w := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    simp [good, ordinaryWords, contaminatedStarts]
  have hcount :
      (∑ u ∈ goodᶜ, fullyContainedWordCount s N (m * ell) u) =
        (contaminatedStarts s N ell m w).card := by
    rw [← hfiltered]
    simpa [fullyContainedWordCount] using hfiber
  simp only [fullyContainedWordProbability, ← Finset.sum_div]
  rw [← Nat.cast_sum, hcount]

/-- With room for twice the long-word length, discarding the suffix costs at
most a factor two. Hence the exceptional mass is bounded by twice `m` times
T1's overlapping forbidden-word frequency. -/
theorem exceptionalMass_le_two_mul_blockFrequency (s : ℕ → Fin 10)
    {N ell m : ℕ} (hell : 0 < ell) (hroom : 2 * (m * ell) ≤ N)
    (w : Fin ell → Fin 10) :
    (∑ u ∈ (ordinaryWords (m := m) w)ᶜ,
        fullyContainedWordProbability s N (m * ell) u) ≤
      2 * m * blockFrequency s (List.ofFn w) N := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [ordinaryWords]
  have hfull : m * ell ≤ N := by omega
  rw [exceptionalMass_eq_contaminatedFraction s hfull w]
  have hcard := contaminatedStarts_card_le s hell hfull w
  have hN : 0 < N := by
    have hmell : 0 < m * ell := Nat.mul_pos (Nat.pos_of_ne_zero hm) hell
    omega
  have hsample : 0 < N + 1 - m * ell := by omega
  have hcastCard :
      ((contaminatedStarts s N ell m w).card : ℝ) ≤
        (m * blockCount s (List.ofFn w) N : ℕ) := by
    exact_mod_cast hcard
  have hfirst :
      (contaminatedStarts s N ell m w).card /
          ((N + 1 - m * ell : ℕ) : ℝ) ≤
        (m * blockCount s (List.ofFn w) N : ℕ) /
          ((N + 1 - m * ell : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right hcastCard (by positivity)
  have hdenCompare :
      (1 : ℝ) / (N + 1 - m * ell : ℕ) ≤ 2 / (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num
    exact_mod_cast (by omega : N ≤ 2 * (N + 1 - m * ell))
  calc
    (contaminatedStarts s N ell m w).card /
        ((N + 1 - m * ell : ℕ) : ℝ) ≤
      (m * blockCount s (List.ofFn w) N : ℕ) /
        ((N + 1 - m * ell : ℕ) : ℝ) := hfirst
    _ = ((m * blockCount s (List.ofFn w) N : ℕ) : ℝ) *
        (1 / (N + 1 - m * ell : ℕ)) := by ring
    _ ≤ ((m * blockCount s (List.ofFn w) N : ℕ) : ℝ) *
        (2 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hdenCompare (by positivity)
    _ = 2 * m * blockFrequency s (List.ofFn w) N := by
      unfold blockFrequency
      push_cast
      ring

/-- Finite entropy bound obtained from the contaminated ordinary support. -/
theorem finitePrefix_alignedShannonEntropy_bound (s : ℕ → Fin 10)
    {N ell m : ℕ} (hell : 0 < ell) (hroom : 2 * (m * ell) ≤ N)
    (w : Fin ell → Fin 10) :
    fullyContainedShannonEntropy s N (m * ell) ≤
      Real.log ((10 ^ ell - 1) ^ m : ℕ) + Real.log 2 +
        (2 * m * blockFrequency s (List.ofFn w) N) *
          Real.log (10 ^ (m * ell) : ℕ) := by
  classical
  let p : (Fin (m * ell) → Fin 10) → ℝ :=
    fullyContainedWordProbability s N (m * ell)
  let good := ordinaryWords (m := m) w
  have hp0 : ∀ u, 0 ≤ p u := fun u =>
    fullyContainedWordProbability_nonneg s N (m * ell) u
  have hfull : m * ell ≤ N := by omega
  have hp1 : ∑ u, p u = 1 :=
    sum_fullyContainedWordProbability s hfull
  have hgood : good.card ≤ (10 ^ ell - 1) ^ m :=
    ordinaryWords_card_le hell w
  have hcard : Fintype.card (Fin (m * ell) → Fin 10) ≤
      10 ^ (m * ell) := by simp
  have hq : ∑ u ∈ goodᶜ, p u ≤
      2 * m * blockFrequency s (List.ofFn w) N := by
    exact exceptionalMass_le_two_mul_blockFrequency s hell hroom w
  exact contaminatedSupport_entropy_bound p good hp0 hp1 hgood hcard hq

/-- Literal failure of canonical C1 supplies a nonempty word whose T1 lower
frequency is exactly zero. -/
theorem not_C1_exists_zero_liminf
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ell : ℕ, 0 < ell ∧ ∃ w : Fin ell → Fin 10,
      liminf (blockFrequency Theory.PiDigits.piDigit (List.ofFn w)) atTop = 0 := by
  have hnotExplicit : ¬ ∀ ell : ℕ, 1 ≤ ell → ∀ w : Fin ell → Fin 10,
      0 < liminf
        (blockFrequency Theory.PiDigits.piDigit (List.ofFn w)) atTop := by
    intro h
    exact hnot (piPositiveLowerBlockDensity_iff_A1_quantifiers.mpr h)
  push Not at hnotExplicit
  obtain ⟨ell, hell, w, hw⟩ := hnotExplicit
  let f := blockFrequency Theory.PiDigits.piDigit (List.ofFn w)
  have hfnonneg : ∀ N, 0 ≤ f N :=
    blockFrequency_nonneg Theory.PiDigits.piDigit (List.ofFn w)
  have hfle : ∀ N, f N ≤ 1 :=
    blockFrequency_le_one Theory.PiDigits.piDigit (List.ofFn w)
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·) f :=
    Filter.isCoboundedUnder_ge_of_le atTop hfle
  have hliminf_nonneg : 0 ≤ liminf f atTop :=
    le_liminf_of_le hcobounded (Filter.Eventually.of_forall hfnonneg)
  refine ⟨ell, hell, w, ?_⟩
  apply le_antisymm
  · exact hw
  · exact hliminf_nonneg

/-- Zero liminf yields an arbitrarily late cutoff below every positive error. -/
theorem arbitrarilyLate_blockFrequency_le
    (w : List (Fin 10))
    (hzero : liminf
      (blockFrequency Theory.PiDigits.piDigit w) atTop = 0)
    (B : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, B ≤ N ∧
      blockFrequency Theory.PiDigits.piDigit w N ≤ eps := by
  let f := blockFrequency Theory.PiDigits.piDigit w
  have hfle : ∀ N, f N ≤ 1 := blockFrequency_le_one _ _
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·) f :=
    Filter.isCoboundedUnder_ge_of_le atTop hfle
  have hfrequent : ∃ᶠ N : ℕ in atTop, f N < eps :=
    frequently_lt_of_liminf_lt hcobounded (by simpa [f, hzero] using heps)
  obtain ⟨N, hBN, hN⟩ := hfrequent.forall_exists_of_atTop B
  exact ⟨N, hBN, hN.le⟩

/-- Recursive simultaneous diagonalization. At stage `j`, select a cutoff
past both `requirement j` and the preceding cutoff, while meeting `error j`. -/
def selectedPrefixCutoffs (f error : ℕ → ℝ) (requirement : ℕ → ℕ)
    (hwitness : ∀ j B : ℕ, ∃ N : ℕ,
      B ≤ N ∧ f N ≤ error j) : ℕ → ℕ
  | 0 => Classical.choose (hwitness 0 (requirement 0))
  | j + 1 => Classical.choose
      (hwitness (j + 1)
        (max (requirement (j + 1))
          (selectedPrefixCutoffs f error requirement hwitness j + 1)))

theorem selectedPrefixCutoffs_strictMono (f error : ℕ → ℝ)
    (requirement : ℕ → ℕ)
    (hwitness : ∀ j B : ℕ, ∃ N : ℕ,
      B ≤ N ∧ f N ≤ error j) :
    StrictMono (selectedPrefixCutoffs f error requirement hwitness) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hspec := Classical.choose_spec
    (hwitness (j + 1)
      (max (requirement (j + 1))
        (selectedPrefixCutoffs f error requirement hwitness j + 1)))
  exact Nat.lt_of_succ_le ((le_max_right _ _).trans hspec.1)

theorem selectedPrefixCutoffs_requirement (f error : ℕ → ℝ)
    (requirement : ℕ → ℕ)
    (hwitness : ∀ j B : ℕ, ∃ N : ℕ,
      B ≤ N ∧ f N ≤ error j) (j : ℕ) :
    requirement j ≤ selectedPrefixCutoffs f error requirement hwitness j := by
  cases j with
  | zero => exact (Classical.choose_spec (hwitness 0 (requirement 0))).1
  | succ j =>
      exact (le_max_left _ _).trans (Classical.choose_spec
        (hwitness (j + 1)
          (max (requirement (j + 1))
            (selectedPrefixCutoffs f error requirement hwitness j + 1)))).1

theorem selectedPrefixCutoffs_error (f error : ℕ → ℝ)
    (requirement : ℕ → ℕ)
    (hwitness : ∀ j B : ℕ, ∃ N : ℕ,
      B ≤ N ∧ f N ≤ error j) (j : ℕ) :
    f (selectedPrefixCutoffs f error requirement hwitness j) ≤ error j := by
  cases j with
  | zero => exact (Classical.choose_spec (hwitness 0 (requirement 0))).2
  | succ j =>
      exact (Classical.choose_spec
        (hwitness (j + 1)
          (max (requirement (j + 1))
            (selectedPrefixCutoffs f error requirement hwitness j + 1)))).2

/-- Explicit slowly growing block scales. -/
def divergingBlockScales (M : ℕ) (j : ℕ) : ℕ := M + j + 1

theorem divergingBlockScales_strictMono (M : ℕ) :
    StrictMono (divergingBlockScales M) := by
  intro i j hij
  simp only [divergingBlockScales]
  omega

theorem divergingBlockScales_tendsto_atTop (M : ℕ) :
    Tendsto (divergingBlockScales M) atTop atTop :=
  (divergingBlockScales_strictMono M).tendsto_atTop

/-- The gap between full decimal entropy for `ell` digits and the logarithm
of the alphabet obtained by forbidding one length-`ell` word. -/
def entropyNumeratorGap (ell : ℕ) : ℝ :=
  (ell : ℝ) * Real.log 10 - Real.log (10 ^ ell - 1 : ℕ)

theorem entropyNumeratorGap_pos {ell : ℕ} (hell : 0 < ell) :
    0 < entropyNumeratorGap ell := by
  have hpow : 10 ≤ 10 ^ ell := by
    simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hell
  have hA : 0 < 10 ^ ell - 1 := by omega
  have hpowpos : 0 < 10 ^ ell := pow_pos (by norm_num) ell
  have hlt : 10 ^ ell - 1 < 10 ^ ell := Nat.sub_lt hpowpos (by norm_num)
  have hloglt : Real.log (10 ^ ell - 1 : ℕ) <
      Real.log (10 ^ ell : ℕ) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hA)
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hpowpos)
    · exact_mod_cast hlt
  rw [Nat.cast_pow, Real.log_pow] at hloglt
  unfold entropyNumeratorGap
  exact sub_pos.mpr hloglt

/-- Per-digit gap used in the final finite-prefix estimate. -/
def normalizedEntropyGap (ell : ℕ) : ℝ :=
  entropyNumeratorGap ell / (2 * ell)

theorem normalizedEntropyGap_pos {ell : ℕ} (hell : 0 < ell) :
    0 < normalizedEntropyGap ell := by
  exact div_pos (entropyNumeratorGap_pos hell) (by positivity)

/-- A sufficiently sparse forbidden word gives the explicit normalized finite
entropy gap. This isolates the real-algebra step from the cutoff selection. -/
theorem finitePrefix_entropy_gap_of_frequency_small
    {N ell m : ℕ} (hell : 0 < ell) (hm : 0 < m)
    (hroom : 2 * (m * ell) ≤ N) (w : Fin ell → Fin 10)
    (hoverhead : Real.log 2 ≤
      (m : ℝ) * entropyNumeratorGap ell / 4)
    (hfrequency :
      blockFrequency Theory.PiDigits.piDigit (List.ofFn w) N ≤
        entropyNumeratorGap ell /
          (8 * (m : ℝ) * (ell : ℝ) * Real.log 10)) :
    fullyContainedShannonEntropy Theory.PiDigits.piDigit N (m * ell) ≤
      (m * ell : ℕ) * (Real.log 10 - normalizedEntropyGap ell) := by
  have hfinite := finitePrefix_alignedShannonEntropy_bound
    Theory.PiDigits.piDigit hell hroom w
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlogLong :
      Real.log (10 ^ (m * ell) : ℕ) =
        ((m * ell : ℕ) : ℝ) * Real.log 10 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogOrdinary :
      Real.log ((10 ^ ell - 1) ^ m : ℕ) =
        (m : ℝ) * Real.log (10 ^ ell - 1 : ℕ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hmult : 0 ≤
      2 * (m : ℝ) * Real.log (10 ^ (m * ell) : ℕ) := by
    positivity
  have hcontamination :
      (2 * m * blockFrequency Theory.PiDigits.piDigit (List.ofFn w) N) *
          Real.log (10 ^ (m * ell) : ℕ) ≤
        (m : ℝ) * entropyNumeratorGap ell / 4 := by
    calc
      (2 * m * blockFrequency Theory.PiDigits.piDigit (List.ofFn w) N) *
          Real.log (10 ^ (m * ell) : ℕ) =
        blockFrequency Theory.PiDigits.piDigit (List.ofFn w) N *
          (2 * (m : ℝ) * Real.log (10 ^ (m * ell) : ℕ)) := by
            push_cast
            ring
      _ ≤ (entropyNumeratorGap ell /
          (8 * (m : ℝ) * (ell : ℝ) * Real.log 10)) *
          (2 * (m : ℝ) * Real.log (10 ^ (m * ell) : ℕ)) :=
        mul_le_mul_of_nonneg_right hfrequency hmult
      _ = (m : ℝ) * entropyNumeratorGap ell / 4 := by
        rw [hlogLong]
        push_cast
        field_simp
        ring
  calc
    fullyContainedShannonEntropy Theory.PiDigits.piDigit N (m * ell) ≤
        Real.log ((10 ^ ell - 1) ^ m : ℕ) + Real.log 2 +
          (2 * m * blockFrequency Theory.PiDigits.piDigit (List.ofFn w) N) *
            Real.log (10 ^ (m * ell) : ℕ) := hfinite
    _ ≤ (m : ℝ) * Real.log (10 ^ ell - 1 : ℕ) +
          ((m : ℝ) * entropyNumeratorGap ell / 4) +
          ((m : ℝ) * entropyNumeratorGap ell / 4) := by
      rw [hlogOrdinary]
      gcongr
    _ = (m * ell : ℕ) *
          (Real.log 10 - normalizedEntropyGap ell) := by
      unfold normalizedEntropyGap entropyNumeratorGap
      push_cast
      field_simp
      ring

/-- A nonnegative sequence bounded by `C/(j+1)` tends to zero. -/
theorem tendsto_zero_of_nonneg_le_const_div_succ (q : ℕ → ℝ) (C : ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq : ∀ j, q j ≤ C / (j + 1 : ℕ)) :
    Tendsto q atTop (𝓝 0) := by
  apply squeeze_zero hq0 hq
  convert (tendsto_const_div_atTop_nhds_zero_nat C).comp
    (tendsto_add_atTop_nat 1) using 1

/-- Necessary-only T9 conclusion. Literal failure of canonical C1 yields
strictly increasing finite pi prefixes and diverging aligned block scales with
vanishing contamination and an explicit positive normalized entropy gap. No
failure or truth of C1 is asserted. -/
theorem not_piPositiveLowerBlockDensity_implies_finitePrefixEntropyGap
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ell : ℕ, 1 ≤ ell ∧ ∃ w : Fin ell → Fin 10,
      ∃ delta : ℝ, delta = normalizedEntropyGap ell ∧ 0 < delta ∧
      ∃ cutoffs scales : ℕ → ℕ,
        StrictMono cutoffs ∧ StrictMono scales ∧
        Tendsto scales atTop atTop ∧
        (∀ j, 2 * (scales j * ell) ≤ cutoffs j) ∧
        (∀ j, (ordinaryWords (m := scales j) w).card ≤
          (10 ^ ell - 1) ^ scales j) ∧
        (∃ C : ℝ, 0 < C ∧
          (∀ j,
            (∑ u ∈ (ordinaryWords (m := scales j) w)ᶜ,
                fullyContainedWordProbability Theory.PiDigits.piDigit
                  (cutoffs j) (scales j * ell) u) ≤ C / (j + 1 : ℕ)) ∧
          Tendsto (fun j =>
            ∑ u ∈ (ordinaryWords (m := scales j) w)ᶜ,
              fullyContainedWordProbability Theory.PiDigits.piDigit
                (cutoffs j) (scales j * ell) u) atTop (𝓝 0)) ∧
        (∀ j,
          fullyContainedShannonEntropy Theory.PiDigits.piDigit
              (cutoffs j) (scales j * ell) ≤
            (scales j * ell : ℕ) * (Real.log 10 - delta)) := by
  obtain ⟨ell, hell, w, hzero⟩ := not_C1_exists_zero_liminf hnot
  let G := entropyNumeratorGap ell
  have hG : 0 < G := entropyNumeratorGap_pos hell
  let delta := normalizedEntropyGap ell
  have hdelta : 0 < delta := normalizedEntropyGap_pos hell
  obtain ⟨M, hMraw⟩ := exists_nat_ge (4 * Real.log 2 / G)
  have hM : 4 * Real.log 2 ≤ (M : ℝ) * G := by
    rw [div_le_iff₀ hG] at hMraw
    exact hMraw
  let scales := divergingBlockScales M
  let error : ℕ → ℝ := fun j =>
    G / (8 * (scales j : ℝ) * (ell : ℝ) * Real.log 10 * (j + 1 : ℕ))
  let requirement : ℕ → ℕ := fun j => 2 * (scales j * ell)
  have herrorPos (j : ℕ) : 0 < error j := by
    dsimp [error, scales, divergingBlockScales]
    positivity
  have hwitness : ∀ j B : ℕ, ∃ N : ℕ,
      B ≤ N ∧
        blockFrequency Theory.PiDigits.piDigit (List.ofFn w) N ≤ error j := by
    intro j B
    exact arbitrarilyLate_blockFrequency_le (List.ofFn w) hzero B (herrorPos j)
  let cutoffs := selectedPrefixCutoffs
    (blockFrequency Theory.PiDigits.piDigit (List.ofFn w))
    error requirement hwitness
  have hcutoffs : StrictMono cutoffs := by
    exact selectedPrefixCutoffs_strictMono _ _ _ hwitness
  have hscales : StrictMono scales := divergingBlockScales_strictMono M
  have hscalesTop : Tendsto scales atTop atTop :=
    divergingBlockScales_tendsto_atTop M
  have hroom (j : ℕ) : 2 * (scales j * ell) ≤ cutoffs j := by
    simpa [cutoffs, requirement] using
      selectedPrefixCutoffs_requirement
        (blockFrequency Theory.PiDigits.piDigit (List.ofFn w))
        error requirement hwitness j
  have hfrequency (j : ℕ) :
      blockFrequency Theory.PiDigits.piDigit (List.ofFn w) (cutoffs j) ≤
        error j := by
    exact selectedPrefixCutoffs_error _ _ _ hwitness j
  let C := G / (4 * (ell : ℝ) * Real.log 10)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let q : ℕ → ℝ := fun j =>
    ∑ u ∈ (ordinaryWords (m := scales j) w)ᶜ,
      fullyContainedWordProbability Theory.PiDigits.piDigit
        (cutoffs j) (scales j * ell) u
  have hq0 (j : ℕ) : 0 ≤ q j := by
    dsimp [q]
    exact Finset.sum_nonneg fun u _ =>
      fullyContainedWordProbability_nonneg _ _ _ u
  have hq (j : ℕ) : q j ≤ C / (j + 1 : ℕ) := by
    have hfirst := exceptionalMass_le_two_mul_blockFrequency
      Theory.PiDigits.piDigit hell (hroom j) w
    have hmul : 0 ≤ (2 * (scales j : ℝ)) := by positivity
    calc
      q j ≤ 2 * scales j *
          blockFrequency Theory.PiDigits.piDigit (List.ofFn w) (cutoffs j) :=
        hfirst
      _ ≤ 2 * scales j * error j := by
        exact mul_le_mul_of_nonneg_left (hfrequency j) hmul
      _ = C / (j + 1 : ℕ) := by
        have hs : (scales j : ℝ) ≠ 0 := by
          dsimp [scales, divergingBlockScales]
          positivity
        dsimp [error, C]
        field_simp [hs]
        ring
  have hqTop : Tendsto q atTop (𝓝 0) :=
    tendsto_zero_of_nonneg_le_const_div_succ q C hq0 hq
  have hordinary (j : ℕ) :
      (ordinaryWords (m := scales j) w).card ≤
        (10 ^ ell - 1) ^ scales j :=
    ordinaryWords_card_le hell w
  have hscalePos (j : ℕ) : 0 < scales j := by
    dsimp [scales, divergingBlockScales]
    omega
  have hoverhead (j : ℕ) : Real.log 2 ≤
      (scales j : ℝ) * entropyNumeratorGap ell / 4 := by
    have hMscale : (M : ℝ) ≤ scales j := by
      exact_mod_cast (by
        dsimp [scales, divergingBlockScales]
        omega : M ≤ scales j)
    have hprod := mul_le_mul_of_nonneg_right hMscale hG.le
    dsimp [G] at hM hprod ⊢
    nlinarith
  have hfrequencyBase (j : ℕ) :
      blockFrequency Theory.PiDigits.piDigit (List.ofFn w) (cutoffs j) ≤
        entropyNumeratorGap ell /
          (8 * (scales j : ℝ) * (ell : ℝ) * Real.log 10) := by
    apply (hfrequency j).trans
    dsimp [error, G]
    have hbaseNonneg : 0 ≤ entropyNumeratorGap ell :=
      (entropyNumeratorGap_pos hell).le
    apply div_le_div_of_nonneg_left hbaseNonneg (by
      have := hscalePos j
      positivity)
    have hj : (1 : ℝ) ≤ (j + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hfactor : 0 ≤
        8 * (scales j : ℝ) * (ell : ℝ) * Real.log 10 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hj hfactor]
  have hentropy (j : ℕ) :
      fullyContainedShannonEntropy Theory.PiDigits.piDigit
          (cutoffs j) (scales j * ell) ≤
        (scales j * ell : ℕ) * (Real.log 10 - delta) := by
    exact finitePrefix_entropy_gap_of_frequency_small hell (hscalePos j)
      (hroom j) w (hoverhead j) (hfrequencyBase j)
  refine ⟨ell, hell, w, delta, rfl, hdelta, cutoffs, scales, hcutoffs, hscales,
    hscalesTop, hroom, hordinary, ?_, hentropy⟩
  refine ⟨C, hC, hq, ?_⟩
  simpa [q] using hqTop

end Theory.PiDigits.PositiveLowerBlockDensity.T9

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.fullContainment_bookkeeping
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.contaminatedSupport_entropy_bound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.ordinaryWords_card_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.contaminatedStarts_card_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.exceptionalMass_le_two_mul_blockFrequency
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.finitePrefix_alignedShannonEntropy_bound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.selectedPrefixCutoffs_strictMono
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.divergingBlockScales_tendsto_atTop
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.normalizedEntropyGap_pos
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T9.not_piPositiveLowerBlockDensity_implies_finitePrefixEntropyGap
