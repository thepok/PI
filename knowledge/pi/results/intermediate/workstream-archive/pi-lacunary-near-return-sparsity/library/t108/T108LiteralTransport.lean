import TheoryLib.PiLacunaryNearReturnSparsity.T100T100UniversalCharging
import TheoryLib.PiLongLagBlockCollisionDecay.T2T2UniformLongLagResidual
import TheoryLib.PiPositiveDecimalFactorEntropy.T61T61VaalerAnalytic

/-!
# T108: literal T83/T100 transport

This file imports T100's kernel-checked exact-word charging theorem and
transports it to T83's program-qualified decimal statistic.  The transport to
the carry-thickened near-return count uses the checked three-cylinder cover;
the transport to the complete weighted Fejer statistic uses T27's checked
factor-17 count-to-energy theorem.  Effective irrationality and a residual
long-sector estimate remain explicit premises.

The Vaaler interface is audited separately below.  Its proved direction is
strict incidence `<=` majorant, so no reverse majorant bound is claimed.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T108LiteralTransport

open DecimalFactorComplexity
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.SparseLongBandFejer
open DecimalFactorComplexity.SparseMicroscopicEquivalence
open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T61VaalerAnalytic
open DecimalFactorComplexity.T83LiteralStatisticAudit
open DecimalFactorComplexity.T100UniversalCharging
open Theory.PiDigits.LongLagBlockCollisionDecay
open Theory.PiDigits.LongLagBlockCollisionDecay.T2
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- T83's literal number of starts. -/
abbrev literalSampleLength (n : ℕ) : ℕ :=
  DecimalFactorComplexity.T83LiteralStatisticAudit.sampleLength n

/-- T83/T61's literal Fourier bandwidth. -/
abbrev literalBandwidth (n : ℕ) : ℕ := shortBandwidth n

/-- The shortest finite decimal word containing every length-`n` block at the
`literalSampleLength n` prescribed starts. -/
def piPrefixWord (n : ℕ) :
    Fin (literalSampleLength n + n - 1) → Fin 10 :=
  fun i => piDecimalStream i

/-- T100 and T83 use exactly the same decimal sample length. -/
theorem t100_sampleLength_eq_literalSampleLength (n : ℕ) :
    DecimalFactorComplexity.T100UniversalCharging.sampleLength 10 n =
      literalSampleLength n := by
  rfl

/-- The finite decimal prefix has exactly T100's required endpoint. -/
theorem piPrefixWord_legal (n : ℕ) :
    LegalWordLength 10 n (literalSampleLength n + n - 1) := by
  unfold LegalWordLength
  rw [t100_sampleLength_eq_literalSampleLength]

/-- Clause-by-clause reconstruction of the masked T83/T61 statistic.

The first two clauses expose the strict short and remote lag ranges.  The next
three expose both ordered orientations, the complete arithmetic mask, and the
signed Vaaler expansion.  The final four clauses record the strict endpoint:
the incidence indicator vanishes there while the majorant contributes one.
-/
theorem literal_masked_vaaler_clause_audit
    (μ c : ℝ) (Q0 n r : ℕ) (hn : 1 ≤ n) :
    (r ∈ shortResidualLags n (literalSampleLength n) ↔
      0 < r ∧ r < n ∧ r < literalSampleLength n) ∧
    (r ∈ longResidualLags n (literalSampleLength n) ↔
      0 < r ∧ n ≤ r ∧ r < literalSampleLength n) ∧
    shortResidualPairCount μ c Q0 n (literalSampleLength n) =
      2 * strictResidualIncidenceCount μ c Q0 n ∧
    (strictResidualIncidenceCount μ c Q0 n : ℝ) =
      ∑ q ∈ shortResidualLags n (literalSampleLength n),
        ∑ j ∈ residualStartDomain μ c Q0 n q,
          strictCentralIndicator (literalBandwidth n)
            ((structuredDenominator j q : ℝ) * Real.pi) ∧
    structuredVaalerMajorantTotal μ c Q0 n =
      2 / (literalBandwidth n : ℝ) * residualStructuredCard μ c Q0 n +
        2 * ∑ h ∈ Finset.Ico 1 (literalBandwidth n),
          vaalerCoefficient (literalBandwidth n) h *
            ∑ q ∈ shortResidualLags n (literalSampleLength n),
              ∑ j ∈ residualStartDomain μ c Q0 n q,
                Real.cos (2 * Real.pi * (h : ℝ) *
                  ((structuredDenominator j q : ℝ) * Real.pi)) ∧
    strictCentralIndicator (literalBandwidth n)
      ((2 * (literalBandwidth n : ℝ))⁻¹) = 0 ∧
    strictCentralIndicator (literalBandwidth n)
      (-((2 * (literalBandwidth n : ℝ))⁻¹)) = 0 ∧
    periodicVaalerMajorant (literalBandwidth n)
      ((2 * (literalBandwidth n : ℝ))⁻¹) = 1 ∧
    periodicVaalerMajorant (literalBandwidth n)
      (-((2 * (literalBandwidth n : ℝ))⁻¹)) = 1 := by
  refine ⟨literal_short_sector_range, mem_sparse_long_sector_iff, ?_, ?_, ?_, ?_⟩
  · exact shortResidualPairCount_eq_two_mul_strictResidualIncidenceCount μ c Q0 n
  · exact strictResidualIncidenceCount_cast_eq_indicatorSum μ c Q0 n
  · exact structuredVaalerMajorantTotal_eq_completeExpression μ c Q0 n
  · have hH : 2 ≤ literalBandwidth n := two_le_shortBandwidth n hn
    exact ⟨strictCentralIndicator_endpoint_pos _ hH,
      strictCentralIndicator_endpoint_neg _ hH,
      periodicVaalerMajorant_endpoint_pos _ hH,
      periodicVaalerMajorant_endpoint_neg _ hH⟩

/-- The literal Vaaler theorem has the majorizing direction only. -/
theorem literal_incidence_le_vaaler_majorant
    (μ c : ℝ) (Q0 n : ℕ) (hn : 1 ≤ n) :
    (strictResidualIncidenceCount μ c Q0 n : ℝ) ≤
      structuredVaalerMajorantTotal μ c Q0 n := by
  exact strictResidualIncidenceCount_le_majorantTotal μ c Q0 n hn

/-- Literal complete Fejer statistic: every signed integer frequency with
strict `|h| < H_n` occurs, including zero, with triangular weight
`1 - |h|/H_n`. -/
theorem literal_fejer_clause_audit
    (n : ℕ) (hn : 1 ≤ n) (h : ℤ) :
    completePiFejerEnergy (literalSampleLength n) (literalBandwidth n) =
      ∑ q ∈ DecimalFactorComplexity.FejerSpectralCriterion.fejerFrequencies
          (literalBandwidth n),
        (1 - (q.natAbs : ℝ) / (literalBandwidth n : ℝ)) *
          ‖∑ j : Fin (literalSampleLength n),
            DecimalFactorComplexity.FejerSpectralCriterion.phase q
              (piDecimalShiftOrbit j)‖ ^ 2 ∧
    (h ∈ DecimalFactorComplexity.FejerSpectralCriterion.fejerFrequencies
        (literalBandwidth n) ↔ h.natAbs < literalBandwidth n) := by
  refine ⟨completePiFejerEnergy_eq_complete_band _ _, ?_⟩
  exact mem_completePiFejerEnergy_frequencies_iff
    (show 1 ≤ literalBandwidth n by
      have hH := two_le_shortBandwidth n hn
      exact (by norm_num : 1 ≤ 2).trans hH)

/-- Every block used by T100's finite specialization is literally the
corresponding block of the decimal stream; the arbitrary extension is never
read. -/
theorem extend_piPrefixWord_blockAt
    (n i : ℕ) (hi : i < literalSampleLength n) :
    blockAt
        (extendFiniteWord (b := 10) (wordLength := literalSampleLength n + n - 1)
          (by norm_num) (piPrefixWord n)) n i =
      blockAt piDecimalStream n i := by
  funext t
  unfold blockAt extendFiniteWord piPrefixWord
  rw [dif_pos]
  omega

/-- The block fibers of the legal finite prefix and the infinite decimal
stream coincide at all prescribed starts. -/
theorem occurrenceStarts_extend_piPrefixWord
    (n : ℕ) (u : Block (Fin 10) n) :
    occurrenceStarts
        (extendFiniteWord (b := 10) (wordLength := literalSampleLength n + n - 1)
          (by norm_num) (piPrefixWord n)) n (literalSampleLength n) u =
      occurrenceStarts piDecimalStream n (literalSampleLength n) u := by
  classical
  ext i
  simp only [occurrenceStarts, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hblock⟩
    exact ⟨hi, (extend_piPrefixWord_blockAt n i hi).symm.trans hblock⟩
  · rintro ⟨hi, hblock⟩
    exact ⟨hi, (extend_piPrefixWord_blockAt n i hi).trans hblock⟩

/-- The set of occurring block labels is unchanged by the legal finite
extension. -/
theorem occurringBlocks_extend_piPrefixWord (n : ℕ) :
    occurringBlocks
        (extendFiniteWord (b := 10) (wordLength := literalSampleLength n + n - 1)
          (by norm_num) (piPrefixWord n)) n (literalSampleLength n) =
      occurringBlocks piDecimalStream n (literalSampleLength n) := by
  classical
  unfold occurringBlocks
  apply Finset.image_congr
  intro i hi
  exact extend_piPrefixWord_blockAt n i (Finset.mem_range.mp hi)

/-- T100's finite strict-short statistic on the shortest legal decimal prefix
is exactly its stream statistic on the prescribed starts. -/
theorem finiteExactShortPairCount_piPrefixWord (n : ℕ) :
    finiteExactShortPairCount (by norm_num) (piPrefixWord n) n =
      DecimalFactorComplexity.T100UniversalCharging.exactShortPairCount
        piDecimalStream n (literalSampleLength n) := by
  classical
  unfold finiteExactShortPairCount
  rw [t100_sampleLength_eq_literalSampleLength]
  unfold DecimalFactorComplexity.T100UniversalCharging.exactShortPairCount
  rw [occurringBlocks_extend_piPrefixWord]
  apply Finset.sum_congr rfl
  intro u _hu
  unfold shortPairsFor
  rw [occurrenceStarts_extend_piPrefixWord]

/-- T100's finite remote statistic likewise reads exactly the decimal stream
and retains the boundary lag `n`. -/
theorem finiteExactRemotePairCount_piPrefixWord (n : ℕ) :
    finiteExactRemotePairCount (by norm_num) (piPrefixWord n) n =
      exactRemotePairCount piDecimalStream n (literalSampleLength n) := by
  classical
  unfold finiteExactRemotePairCount
  rw [t100_sampleLength_eq_literalSampleLength]
  unfold exactRemotePairCount
  rw [occurringBlocks_extend_piPrefixWord]
  apply Finset.sum_congr rfl
  intro u _hu
  unfold remotePairsFor
  rw [occurrenceStarts_extend_piPrefixWord]

/-- Ordered remote pairs carrying one raw block label. -/
def orderedRemoteStartsFor {b : ℕ} (y : Stream (Fin b)) (n L : ℕ)
    (u : Block (Fin b) n) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range L ×ˢ Finset.range L).filter fun ij =>
    blockAt y n ij.1 = u ∧ blockAt y n ij.2 = u ∧
      ij.2 ≠ ij.1 ∧ n ≤ Nat.dist ij.1 ij.2

/-- T100's local remote sum is exactly the cardinality of the corresponding
ordered pair fiber. -/
theorem remotePairsFor_eq_orderedRemoteStartsFor_card
    {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) (u : Block (Fin b) n) :
    remotePairsFor y n L u = (orderedRemoteStartsFor y n L u).card := by
  classical
  let S := orderedRemoteStartsFor y n L u
  let A := occurrenceStarts y n L u
  have hmaps : Set.MapsTo Prod.fst (S : Set (ℕ × ℕ)) (A : Set ℕ) := by
    intro ij hij
    change ij ∈ orderedRemoteStartsFor y n L u at hij
    rw [orderedRemoteStartsFor, Finset.mem_filter, Finset.mem_product] at hij
    exact Finset.mem_filter.mpr ⟨hij.1.1, hij.2.1⟩
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := A) (f := Prod.fst) hmaps
  have hfiber (i : ℕ) (hi : i ∈ A) :
      (S.filter fun ij => ij.1 = i).card =
        (A.filter fun j => j ≠ i ∧ n ≤ Nat.dist i j).card := by
    have hi' := Finset.mem_filter.mp hi
    rw [show S.filter (fun ij => ij.1 = i) =
        {i} ×ˢ (A.filter fun j => j ≠ i ∧ n ≤ Nat.dist i j) by
      ext ij
      rcases ij with ⟨a, j⟩
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
        Finset.mem_filter]
      constructor
      · rintro ⟨haS, hai⟩
        change (a, j) ∈ orderedRemoteStartsFor y n L u at haS
        rw [orderedRemoteStartsFor, Finset.mem_filter,
          Finset.mem_product] at haS
        rcases haS with ⟨⟨haL, hjL⟩, haU, hjU, hji, hremote⟩
        simp only at hai haL hjL haU hjU hji hremote ⊢
        subst a
        exact ⟨rfl, Finset.mem_filter.mpr ⟨hjL, hjU⟩, hji, hremote⟩
      · rintro ⟨hai, hjA, hji, hremote⟩
        simp only at hai hjA hji hremote ⊢
        subst a
        have hjA' := Finset.mem_filter.mp hjA
        refine ⟨?_, rfl⟩
        change (i, j) ∈ orderedRemoteStartsFor y n L u
        rw [orderedRemoteStartsFor, Finset.mem_filter,
          Finset.mem_product]
        exact ⟨⟨hi'.1, hjA'.1⟩, hi'.2, hjA'.2, hji, hremote⟩]
    simp
  unfold remotePairsFor
  change (∑ i ∈ A, _) = S.card
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hfiber i hi).symm

/-- All ordered off-diagonal equal-block pairs in T100's remote range. -/
def orderedRemoteStarts {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range L ×ˢ Finset.range L).filter fun ij =>
    blockAt y n ij.1 = blockAt y n ij.2 ∧
      ij.2 ≠ ij.1 ∧ n ≤ Nat.dist ij.1 ij.2

/-- T100's total remote statistic is exactly the literal ordered pair set. -/
theorem exactRemotePairCount_eq_orderedRemoteStarts_card
    {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    exactRemotePairCount y n L = (orderedRemoteStarts y n L).card := by
  classical
  let S := orderedRemoteStarts y n L
  let B := occurringBlocks y n L
  have hmaps : Set.MapsTo (fun ij => blockAt y n ij.1)
      (S : Set (ℕ × ℕ)) (B : Set (Block (Fin b) n)) := by
    intro ij hij
    change ij ∈ orderedRemoteStarts y n L at hij
    rw [orderedRemoteStarts, Finset.mem_filter, Finset.mem_product] at hij
    exact Finset.mem_image.mpr ⟨ij.1, hij.1.1, rfl⟩
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := B) (f := fun ij => blockAt y n ij.1) hmaps
  have hfiber (u : Block (Fin b) n) (hu : u ∈ B) :
      (S.filter fun ij => blockAt y n ij.1 = u).card =
        remotePairsFor y n L u := by
    rw [show S.filter (fun ij => blockAt y n ij.1 = u) =
        orderedRemoteStartsFor y n L u by
      ext ij
      simp only [Finset.mem_filter]
      change (ij ∈ orderedRemoteStarts y n L ∧ blockAt y n ij.1 = u) ↔
        ij ∈ orderedRemoteStartsFor y n L u
      rw [orderedRemoteStarts, orderedRemoteStartsFor,
        Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hprod, heq, hne, hremote⟩, hfirst⟩
        exact ⟨hprod, hfirst, heq.symm.trans hfirst, hne, hremote⟩
      · rintro ⟨hprod, hfirst, hsecond, hne, hremote⟩
        exact ⟨⟨hprod, hfirst.trans hsecond.symm, hne, hremote⟩, hfirst⟩]
    exact (remotePairsFor_eq_orderedRemoteStartsFor_card y n L u).symm
  unfold exactRemotePairCount
  change (∑ u ∈ B, remotePairsFor y n L u) = S.card
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro u hu
  exact (hfiber u hu).symm

/-- T1's decimal-cylinder labels agree exactly when the corresponding raw
length-`n` decimal blocks agree. -/
theorem B_pi_eq_iff_blockAt_eq (n i j : ℕ) :
    B_pi i n = B_pi j n ↔
      blockAt piDecimalStream n i = blockAt piDecimalStream n j := by
  rw [B_pi, B_pi, piCylinderCode_eq_iff_factorAt_eq]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- T100's ordered remote set on the decimal stream is literally T1's
`R_pi`, including lag exactly `n`. -/
theorem orderedRemoteStarts_pi_card_eq_R_pi
    (n L : ℕ) (hn : 1 ≤ n) :
    (orderedRemoteStarts piDecimalStream n L).card = R_pi n L := by
  classical
  unfold R_pi
  apply Finset.card_bij
      (fun ij hij =>
        (⟨ij.1, by
          rw [orderedRemoteStarts, Finset.mem_filter,
            Finset.mem_product] at hij
          exact Finset.mem_range.mp hij.1.1⟩,
         ⟨ij.2, by
          rw [orderedRemoteStarts, Finset.mem_filter,
            Finset.mem_product] at hij
          exact Finset.mem_range.mp hij.1.2⟩))
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [orderedRemoteStarts, Finset.mem_filter,
      Finset.mem_product] at hij
    exact ⟨hij.2.2.2, (B_pi_eq_iff_blockAt_eq n ij.1 ij.2).2 hij.2.1⟩
  · intro a ha b hb hab
    apply Prod.ext
    · exact congrArg (fun ij : Fin L × Fin L => (ij.1 : ℕ)) hab
    · exact congrArg (fun ij : Fin L × Fin L => (ij.2 : ℕ)) hab
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    let a : ℕ × ℕ := (ij.1, ij.2)
    have ha : a ∈ orderedRemoteStarts piDecimalStream n L := by
      rw [orderedRemoteStarts, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Finset.mem_range.mpr ij.1.isLt,
        Finset.mem_range.mpr ij.2.isLt⟩, ?_, ?_, hij.1⟩
      · exact (B_pi_eq_iff_blockAt_eq n ij.1 ij.2).1 hij.2
      · intro heq
        change (ij.2 : ℕ) = (ij.1 : ℕ) at heq
        have hzero : Nat.dist (ij.1 : ℕ) (ij.2 : ℕ) = 0 := by simp [heq]
        omega
    refine ⟨a, ha, ?_⟩
    apply Prod.ext <;> rfl

/-- T100's finite remote statistic on the legal decimal prefix is exactly
T1's ordered `R_pi` statistic. -/
theorem finiteExactRemotePairCount_piPrefixWord_eq_R_pi
    (n : ℕ) (hn : 1 ≤ n) :
    finiteExactRemotePairCount (by norm_num) (piPrefixWord n) n =
      R_pi n (literalSampleLength n) := by
  rw [finiteExactRemotePairCount_piPrefixWord,
    exactRemotePairCount_eq_orderedRemoteStarts_card,
    orderedRemoteStarts_pi_card_eq_R_pi n (literalSampleLength n) hn]

/-- Ordered strict-short pairs carrying one raw block label. -/
def orderedShortStartsFor {b : ℕ} (y : Stream (Fin b)) (n L : ℕ)
    (u : Block (Fin b) n) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range L ×ˢ Finset.range L).filter fun ij =>
    blockAt y n ij.1 = u ∧ blockAt y n ij.2 = u ∧
      ij.2 ≠ ij.1 ∧ Nat.dist ij.1 ij.2 < n

/-- T100's local strict-short sum is the matching ordered pair fiber. -/
theorem shortPairsFor_eq_orderedShortStartsFor_card
    {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) (u : Block (Fin b) n) :
    shortPairsFor y n L u = (orderedShortStartsFor y n L u).card := by
  classical
  let S := orderedShortStartsFor y n L u
  let A := occurrenceStarts y n L u
  have hmaps : Set.MapsTo Prod.fst (S : Set (ℕ × ℕ)) (A : Set ℕ) := by
    intro ij hij
    change ij ∈ orderedShortStartsFor y n L u at hij
    rw [orderedShortStartsFor, Finset.mem_filter, Finset.mem_product] at hij
    exact Finset.mem_filter.mpr ⟨hij.1.1, hij.2.1⟩
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := A) (f := Prod.fst) hmaps
  have hfiber (i : ℕ) (hi : i ∈ A) :
      (S.filter fun ij => ij.1 = i).card =
        (A.filter fun j => j ≠ i ∧ Nat.dist i j < n).card := by
    have hi' := Finset.mem_filter.mp hi
    rw [show S.filter (fun ij => ij.1 = i) =
        {i} ×ˢ (A.filter fun j => j ≠ i ∧ Nat.dist i j < n) by
      ext ij
      rcases ij with ⟨a, j⟩
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
        Finset.mem_filter]
      constructor
      · rintro ⟨haS, hai⟩
        change (a, j) ∈ orderedShortStartsFor y n L u at haS
        rw [orderedShortStartsFor, Finset.mem_filter,
          Finset.mem_product] at haS
        rcases haS with ⟨⟨haL, hjL⟩, haU, hjU, hji, hshort⟩
        simp only at hai haL hjL haU hjU hji hshort ⊢
        subst a
        exact ⟨rfl, Finset.mem_filter.mpr ⟨hjL, hjU⟩, hji, hshort⟩
      · rintro ⟨hai, hjA, hji, hshort⟩
        simp only at hai hjA hji hshort ⊢
        subst a
        have hjA' := Finset.mem_filter.mp hjA
        refine ⟨?_, rfl⟩
        change (i, j) ∈ orderedShortStartsFor y n L u
        rw [orderedShortStartsFor, Finset.mem_filter,
          Finset.mem_product]
        exact ⟨⟨hi'.1, hjA'.1⟩, hi'.2, hjA'.2, hji, hshort⟩]
    simp
  unfold shortPairsFor
  change (∑ i ∈ A, _) = S.card
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hfiber i hi).symm

/-- All ordered off-diagonal equal-block pairs in T100's strict-short range. -/
def orderedShortStarts {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range L ×ˢ Finset.range L).filter fun ij =>
    blockAt y n ij.1 = blockAt y n ij.2 ∧
      ij.2 ≠ ij.1 ∧ Nat.dist ij.1 ij.2 < n

/-- T100's total strict-short statistic is its literal ordered pair set. -/
theorem exactShortPairCount_eq_orderedShortStarts_card
    {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    DecimalFactorComplexity.T100UniversalCharging.exactShortPairCount y n L =
      (orderedShortStarts y n L).card := by
  classical
  let S := orderedShortStarts y n L
  let B := occurringBlocks y n L
  have hmaps : Set.MapsTo (fun ij => blockAt y n ij.1)
      (S : Set (ℕ × ℕ)) (B : Set (Block (Fin b) n)) := by
    intro ij hij
    change ij ∈ orderedShortStarts y n L at hij
    rw [orderedShortStarts, Finset.mem_filter, Finset.mem_product] at hij
    exact Finset.mem_image.mpr ⟨ij.1, hij.1.1, rfl⟩
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := B) (f := fun ij => blockAt y n ij.1) hmaps
  have hfiber (u : Block (Fin b) n) (hu : u ∈ B) :
      (S.filter fun ij => blockAt y n ij.1 = u).card =
        shortPairsFor y n L u := by
    rw [show S.filter (fun ij => blockAt y n ij.1 = u) =
        orderedShortStartsFor y n L u by
      ext ij
      simp only [Finset.mem_filter]
      change (ij ∈ orderedShortStarts y n L ∧ blockAt y n ij.1 = u) ↔
        ij ∈ orderedShortStartsFor y n L u
      rw [orderedShortStarts, orderedShortStartsFor,
        Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hprod, heq, hne, hshort⟩, hfirst⟩
        exact ⟨hprod, hfirst, heq.symm.trans hfirst, hne, hshort⟩
      · rintro ⟨hprod, hfirst, hsecond, hne, hshort⟩
        exact ⟨⟨hprod, hfirst.trans hsecond.symm, hne, hshort⟩, hfirst⟩]
    exact (shortPairsFor_eq_orderedShortStartsFor_card y n L u).symm
  unfold DecimalFactorComplexity.T100UniversalCharging.exactShortPairCount
  change (∑ u ∈ B, shortPairsFor y n L u) = S.card
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro u hu
  exact (hfiber u hu).symm

/-- All ordered equal-block pairs, including the diagonal. -/
def orderedCollisionStarts {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range L ×ˢ Finset.range L).filter fun ij =>
    blockAt y n ij.1 = blockAt y n ij.2

/-- Literal diagonal/strict-short/remote partition.  Both off-diagonal
statistics are ordered, short uses `< n`, and remote uses `n <=`. -/
theorem orderedCollisionStarts_card_eq_length_add_short_add_remote
    {b : ℕ} (y : Stream (Fin b)) (n L : ℕ) :
    (orderedCollisionStarts y n L).card =
      L + (orderedShortStarts y n L).card +
        (orderedRemoteStarts y n L).card := by
  classical
  let C := orderedCollisionStarts y n L
  let D := C.filter fun ij => ij.1 = ij.2
  let O := C.filter fun ij => ij.1 ≠ ij.2
  let S := O.filter fun ij => Nat.dist ij.1 ij.2 < n
  let R := O.filter fun ij => ¬ Nat.dist ij.1 ij.2 < n
  have hDO : D.card + O.card = C.card := by
    simpa [D, O] using Finset.card_filter_add_card_filter_not
      (s := C) (p := fun ij => ij.1 = ij.2)
  have hSR : S.card + R.card = O.card := by
    simpa [S, R] using Finset.card_filter_add_card_filter_not
      (s := O) (p := fun ij => Nat.dist ij.1 ij.2 < n)
  have hD : D.card = L := by
    rw [show D = (Finset.range L).image (fun i => (i, i)) by
      ext ij
      rcases ij with ⟨i, j⟩
      simp only [D, C, orderedCollisionStarts, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨hi, hj⟩, _hblock⟩, hij⟩
        subst j
        exact ⟨i, hi, rfl⟩
      · rintro ⟨k, hk, hpair⟩
        injection hpair with hi hj
        subst i
        subst j
        exact ⟨⟨⟨hk, hk⟩, rfl⟩, rfl⟩]
    rw [Finset.card_image_iff.mpr (by
      intro i _hi j _hj h
      exact congrArg Prod.fst h)]
    exact Finset.card_range L
  have hS : S = orderedShortStarts y n L := by
    ext ij
    simp only [S, O, C, orderedCollisionStarts, orderedShortStarts,
      Finset.mem_filter, Finset.mem_product]
    tauto
  have hR : R = orderedRemoteStarts y n L := by
    ext ij
    simp only [R, O, C, orderedCollisionStarts, orderedRemoteStarts,
      Finset.mem_filter, Finset.mem_product, not_lt]
    tauto
  rw [← hDO, ← hSR, hD, hS, hR]
  omega

/-- The raw decimal block-pair set is exactly the accepted finite decimal
cylinder energy. -/
theorem orderedCollisionStarts_pi_card_eq_energy (n L : ℕ) :
    (orderedCollisionStarts piDecimalStream n L).card =
      piCylinderCollisionEnergy n L := by
  classical
  rw [piCylinderCollisionEnergy_eq_blockPairCount]
  apply Finset.card_bij
      (fun ij hij =>
        (⟨ij.1, by
          rw [orderedCollisionStarts, Finset.mem_filter,
            Finset.mem_product] at hij
          exact Finset.mem_range.mp hij.1.1⟩,
         ⟨ij.2, by
          rw [orderedCollisionStarts, Finset.mem_filter,
            Finset.mem_product] at hij
          exact Finset.mem_range.mp hij.1.2⟩))
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [orderedCollisionStarts, Finset.mem_filter,
      Finset.mem_product] at hij
    exact (B_pi_eq_iff_blockAt_eq n ij.1 ij.2).2 hij.2
  · intro a ha b hb hab
    apply Prod.ext
    · exact congrArg (fun ij : Fin L × Fin L => (ij.1 : ℕ)) hab
    · exact congrArg (fun ij : Fin L × Fin L => (ij.2 : ℕ)) hab
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    let a : ℕ × ℕ := (ij.1, ij.2)
    have ha : a ∈ orderedCollisionStarts piDecimalStream n L := by
      rw [orderedCollisionStarts, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_range.mpr ij.1.isLt,
        Finset.mem_range.mpr ij.2.isLt⟩,
        (B_pi_eq_iff_blockAt_eq n ij.1 ij.2).1 hij⟩
    refine ⟨a, ha, ?_⟩
    apply Prod.ext <;> rfl

/-- Exact T100 partition of the accepted decimal collision energy.  The
diagonal is `L_n`; strict-short and remote are ordered and off-diagonal. -/
theorem piCylinderCollisionEnergy_eq_t100_partition
    (n : ℕ) :
    piCylinderCollisionEnergy n (literalSampleLength n) =
      literalSampleLength n +
        finiteExactShortPairCount (by norm_num) (piPrefixWord n) n +
          finiteExactRemotePairCount (by norm_num) (piPrefixWord n) n := by
  rw [← orderedCollisionStarts_pi_card_eq_energy]
  rw [orderedCollisionStarts_card_eq_length_add_short_add_remote]
  rw [← exactShortPairCount_eq_orderedShortStarts_card,
    ← exactRemotePairCount_eq_orderedRemoteStarts_card]
  rw [← finiteExactShortPairCount_piPrefixWord,
    ← finiteExactRemotePairCount_piPrefixWord]

/-- T100's explicit decimal charging constant, without rounding. -/
theorem chargingConstant_ten :
    chargingConstant 10 = (17800 / 243 : ℝ) := by
  norm_num [chargingConstant]

/-- Kernel-checked T100 charging, specialized to the shortest legal decimal
prefix and rewritten as a bound for the accepted exact collision energy. -/
theorem t100_controls_exact_decimal_energy
    (n : ℕ) (hn : 1 ≤ n) :
    (piCylinderCollisionEnergy n (literalSampleLength n) : ℝ) ≤
      (18043 / 243 : ℝ) * (literalSampleLength n : ℝ) +
        (5 / 2 : ℝ) * (R_pi n (literalSampleLength n) : ℝ) := by
  let S := finiteExactShortPairCount (by norm_num) (piPrefixWord n) n
  let R := finiteExactRemotePairCount (by norm_num) (piPrefixWord n) n
  have hcharge := universal_finite_word_charging
    (b := 10) (n := n)
    (wordLength := literalSampleLength n + n - 1)
    (by norm_num) hn (piPrefixWord n) (piPrefixWord_legal n)
  rw [t100_sampleLength_eq_literalSampleLength, chargingConstant_ten] at hcharge
  change (2 : ℝ) * S ≤ 3 * R +
    2 * (17800 / 243 : ℝ) * literalSampleLength n at hcharge
  have hremote : R = R_pi n (literalSampleLength n) := by
    exact finiteExactRemotePairCount_piPrefixWord_eq_R_pi n hn
  have hdecompNat := piCylinderCollisionEnergy_eq_t100_partition n
  have hdecomp :
      (piCylinderCollisionEnergy n (literalSampleLength n) : ℝ) =
        (literalSampleLength n : ℝ) + (S : ℝ) + (R : ℝ) := by
    exact_mod_cast hdecompNat
  rw [hremote] at hcharge hdecomp
  rw [hdecomp]
  nlinarith

/-- The checked three-cylinder cover transports T100 to T83's literal
ordered, diagonal-inclusive, strict circle-near-return count. -/
theorem t100_controls_literal_nearReturn_count
    (n : ℕ) (hn : 1 ≤ n) :
    (Q_pi n (literalSampleLength n) : ℝ) ≤
      (18043 / 81 : ℝ) * (literalSampleLength n : ℝ) +
        (15 / 2 : ℝ) * (R_pi n (literalSampleLength n) : ℝ) := by
  have hthree :=
    (piCylinderCollisionEnergy_le_Q_pi_le_three_mul
      n (literalSampleLength n)).2
  have hthreeReal :
      (Q_pi n (literalSampleLength n) : ℝ) ≤
        3 * (piCylinderCollisionEnergy n (literalSampleLength n) : ℝ) := by
    exact_mod_cast hthree
  have henergy := t100_controls_exact_decimal_energy n hn
  calc
    (Q_pi n (literalSampleLength n) : ℝ) ≤
        3 * (piCylinderCollisionEnergy n (literalSampleLength n) : ℝ) :=
      hthreeReal
    _ ≤ 3 * ((18043 / 243 : ℝ) * (literalSampleLength n : ℝ) +
        (5 / 2 : ℝ) * (R_pi n (literalSampleLength n) : ℝ)) := by
      gcongr
    _ = (18043 / 81 : ℝ) * (literalSampleLength n : ℝ) +
        (15 / 2 : ℝ) * (R_pi n (literalSampleLength n) : ℝ) := by
      ring

/-- Under the explicit effective-irrationality premise, the exact remote
count is charged to T83's masked remote residual statistic with no orientation
loss and with lag `n` retained. -/
theorem t100_controls_literal_nearReturn_by_longResidual
    {μ c : ℝ} {Q0 : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (hIrr : EffectiveIrrationality Real.pi μ c Q0) :
    (Q_pi n (literalSampleLength n) : ℝ) ≤
      (18043 / 81 : ℝ) * (literalSampleLength n : ℝ) +
        (15 / 2 : ℝ) *
          (longResidualPairCount μ c Q0 n (literalSampleLength n) : ℝ) := by
  have hQ := t100_controls_literal_nearReturn_count n hn
  have hremoteNat := R_pi_le_longResidualPairCount
    (μ := μ) (c := c) (Q0 := Q0) (m := n)
    (N := literalSampleLength n) hn hIrr
  have hremote :
      (R_pi n (literalSampleLength n) : ℝ) ≤
        (longResidualPairCount μ c Q0 n (literalSampleLength n) : ℝ) := by
    exact_mod_cast hremoteNat
  exact hQ.trans (by gcongr)

/-- The explicit coefficient multiplying `L_n` after a remote residual bound
`T_n <= K L_n`. -/
def literalTransportConstant (K : ℝ) : ℝ :=
  18043 / 81 + (15 / 2) * K

theorem literalTransportConstant_pos {K : ℝ} (hK : 0 ≤ K) :
    0 < literalTransportConstant K := by
  unfold literalTransportConstant
  positivity

/-- Constant-explicit literal transport theorem.

The only unproved mathematical inputs are displayed: effective irrationality
and an eventual linear estimate for T83's masked remote residual count.  The
first conclusion is the carry-thickened ordered count.  The second is the
complete signed Fejer energy, whose strict frequency range, triangular weights,
zero mode, and endpoints are exposed by `completePiFejerEnergy_eq_complete_band`
and `literal_masked_vaaler_clause_audit` above.
-/
theorem literal_deterministic_transport
    {μ c K : ℝ} {Q0 N : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hK : 0 ≤ K) (hN : 1 ≤ N)
    (hLong : ∀ n : ℕ, N ≤ n →
      (longResidualPairCount μ c Q0 n (literalSampleLength n) : ℝ) ≤
        K * (literalSampleLength n : ℝ)) :
    (∀ n : ℕ, N ≤ n →
      (Q_pi n (literalSampleLength n) : ℝ) ≤
        literalTransportConstant K * (literalSampleLength n : ℝ)) ∧
    (∀ n : ℕ, N ≤ n →
      completePiFejerEnergy (literalSampleLength n) (literalBandwidth n) ≤
        (17 * literalTransportConstant K) * (literalBandwidth n : ℝ) *
          (literalSampleLength n : ℝ)) := by
  have hQ : ∀ n : ℕ, N ≤ n →
      (Q_pi n (literalSampleLength n) : ℝ) ≤
        literalTransportConstant K * (literalSampleLength n : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := hN.trans hn
    have hbase := t100_controls_literal_nearReturn_by_longResidual n hn1 hIrr
    calc
      (Q_pi n (literalSampleLength n) : ℝ) ≤
          (18043 / 81 : ℝ) * (literalSampleLength n : ℝ) +
            (15 / 2 : ℝ) *
              (longResidualPairCount μ c Q0 n (literalSampleLength n) : ℝ) :=
        hbase
      _ ≤ (18043 / 81 : ℝ) * (literalSampleLength n : ℝ) +
          (15 / 2 : ℝ) * (K * (literalSampleLength n : ℝ)) := by
        gcongr
        exact hLong n hn
      _ = literalTransportConstant K * (literalSampleLength n : ℝ) := by
        unfold literalTransportConstant
        ring
  refine ⟨hQ, ?_⟩
  exact piSparseMicroscopicQBound_implies_C7_explicit
    (literalTransportConstant K) (literalTransportConstant_pos hK)
    N hN hQ

end DecimalFactorComplexity.T108LiteralTransport

#print axioms DecimalFactorComplexity.T108LiteralTransport.literal_masked_vaaler_clause_audit
#print axioms DecimalFactorComplexity.T108LiteralTransport.literal_incidence_le_vaaler_majorant
#print axioms DecimalFactorComplexity.T108LiteralTransport.literal_fejer_clause_audit
#print axioms DecimalFactorComplexity.T108LiteralTransport.finiteExactShortPairCount_piPrefixWord
#print axioms DecimalFactorComplexity.T108LiteralTransport.finiteExactRemotePairCount_piPrefixWord
#print axioms DecimalFactorComplexity.T108LiteralTransport.remotePairsFor_eq_orderedRemoteStartsFor_card
#print axioms DecimalFactorComplexity.T108LiteralTransport.exactRemotePairCount_eq_orderedRemoteStarts_card
#print axioms DecimalFactorComplexity.T108LiteralTransport.finiteExactRemotePairCount_piPrefixWord_eq_R_pi
#print axioms DecimalFactorComplexity.T108LiteralTransport.exactShortPairCount_eq_orderedShortStarts_card
#print axioms DecimalFactorComplexity.T108LiteralTransport.orderedCollisionStarts_card_eq_length_add_short_add_remote
#print axioms DecimalFactorComplexity.T108LiteralTransport.piCylinderCollisionEnergy_eq_t100_partition
#print axioms DecimalFactorComplexity.T108LiteralTransport.chargingConstant_ten
#print axioms DecimalFactorComplexity.T108LiteralTransport.t100_controls_exact_decimal_energy
#print axioms DecimalFactorComplexity.T108LiteralTransport.t100_controls_literal_nearReturn_count
#print axioms DecimalFactorComplexity.T108LiteralTransport.t100_controls_literal_nearReturn_by_longResidual
#print axioms DecimalFactorComplexity.T108LiteralTransport.literal_deterministic_transport
