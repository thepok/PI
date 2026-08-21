import TheoryLib.PiLacunaryNearReturnSparsity.T26SharedResonanceChain
import TheoryLib.PiLacunaryNearReturnSparsity.T34MixedProductBridge
import TheoryLib.PiLacunaryNearReturnSparsity.T38FixedStratumFejerSpike
import TheoryLib.PiLacunaryNearReturnSparsity.T28AdjacentNodeCompatibility

/-!
# T55: signed multiplier-ten pairing at one T38 stratum

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module formalizes the finite multiplier-ten identities suggested by the
unverified T54 note.  The only analytic input is the explicitly named
`TopShellCorrelationHypothesis`; it is not proved here.  In particular, this
module proves no unconditional FSFS, adjacent compatibility, fixed-`pi`
estimate, canonical A1, C1, or C2 statement.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity
namespace SignedMultiplierTenPairingT55

open IteratedLagResonance
open FiniteInverseDichotomy
open SharedResonanceChain
open AdjacentNodeCompatibility
open MixedProductBridge
open FixedStratumFejerSpike

abbrev phase := Theory.PiDigits.T27.phase

/-- A signed frequency, its positive absolute-frequency label, and a stratum
index.  Labels are retained even when their resulting numerical frequencies
coincide. -/
abbrev PairingLabel := (ℤ × ℕ) × ℕ

/-- The actual signed integer frequency carried by a pairing label. -/
def labelFrequency (x : PairingLabel) : ℤ :=
  x.1.1 * (x.1.2 : ℤ)

/-- Literal signed source range for `(epsilon,u,t)` with `t=j+1`. -/
def PairingSource (ell H : ℕ) (x : PairingLabel) : Prop :=
  (x.1.1 = -1 ∨ x.1.1 = 1) ∧
    1 ≤ x.1.2 ∧ 10 * x.1.2 ≤ H ∧ 1 ≤ x.2 ∧ x.2 ≤ ell

/-- Literal signed target range for `(epsilon,10*u,j)`. -/
def PairingTarget (ell H : ℕ) (x : PairingLabel) : Prop :=
  (x.1.1 = -1 ∨ x.1.1 = 1) ∧
    1 ≤ x.1.2 ∧ x.1.2 ≤ H ∧ 10 ∣ x.1.2 ∧ x.2 < ell

/-- The label-level multiplier-ten map `(epsilon,u,j+1) ↦
(epsilon,10*u,j)`. -/
def multiplierTenPair (x : PairingLabel) : PairingLabel :=
  ((x.1.1, 10 * x.1.2), x.2 - 1)

/-- The inverse label map `(epsilon,v,j) ↦ (epsilon,v/10,j+1)`. -/
def multiplierTenUnpair (x : PairingLabel) : PairingLabel :=
  ((x.1.1, x.1.2 / 10), x.2 + 1)

/-- The signed pairing is a genuine bijection between its complete source and
target ranges. -/
def signedMultiplierTenPairing (ell H : ℕ) :
    {x : PairingLabel // PairingSource ell H x} ≃
      {x : PairingLabel // PairingTarget ell H x} where
  toFun x := ⟨multiplierTenPair x, by
    rcases x.property with ⟨hsign, hu1, huH, ht1, htell⟩
    unfold PairingTarget multiplierTenPair
    dsimp only
    exact ⟨hsign, by omega, huH, ⟨x.val.1.2, rfl⟩, by omega⟩⟩
  invFun x := ⟨multiplierTenUnpair x, by
    rcases x.property with ⟨hsign, hv1, hvH, hv10, hjell⟩
    have hmul : 10 * (x.val.1.2 / 10) = x.val.1.2 := Nat.mul_div_cancel' hv10
    have hquotPos : 1 ≤ x.val.1.2 / 10 := by
      by_contra hzero
      have : x.val.1.2 / 10 = 0 := by omega
      rw [this, mul_zero] at hmul
      omega
    unfold PairingSource multiplierTenUnpair
    dsimp only
    exact ⟨hsign, hquotPos, by omega, by omega, by omega⟩⟩
  left_inv x := by
    apply Subtype.ext
    rcases x.property with ⟨_hsign, _hu1, _huH, ht1, _htell⟩
    simp [multiplierTenPair, multiplierTenUnpair,
      Nat.sub_add_cancel ht1]
  right_inv x := by
    apply Subtype.ext
    rcases x.property with ⟨_hsign, _hv1, _hvH, hv10, _hjell⟩
    have hmul : 10 * (x.val.1.2 / 10) = x.val.1.2 := Nat.mul_div_cancel' hv10
    simp [multiplierTenPair, multiplierTenUnpair, hmul]

/-- Public bijectivity theorem for the complete signed label pairing. -/
theorem signedMultiplierTenPairing_bijective (ell H : ℕ) :
    Function.Bijective (signedMultiplierTenPairing ell H) :=
  (signedMultiplierTenPairing ell H).bijective

/-- A literal labeled T38 stratum phase. -/
def labeledPhase (beta : ℝ) (ell : ℕ) (u : ℤ) (j : ℕ) : ℂ :=
  phase u (beta * ((10 : ℝ) ^ ell - (10 : ℝ) ^ j))

/-- The complete labeled stratum block at signed frequency `u`. -/
def frequencyBlock (beta : ℝ) (ell : ℕ) (u : ℤ) : ℂ :=
  ∑ j ∈ range ell, labeledPhase beta ell u j

/-- The indispensable outer phase correcting transport from `10*u` to `u`. -/
def transportPhase (beta : ℝ) (ell : ℕ) (u : ℤ) : ℂ :=
  phase (-9 * u) (beta * (10 : ℝ) ^ ell)

/-- Exact phase transport on every signed source label. -/
theorem multiplierTen_phase_transport
    (beta : ℝ) (ell j : ℕ) (u : ℤ) :
    transportPhase beta ell u * labeledPhase beta ell (10 * u) j =
      labeledPhase beta ell u (j + 1) := by
  unfold transportPhase labeledPhase phase Theory.PiDigits.T27.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  rw [pow_succ]
  ring

/-- Multiplication by ten on labels is multiplication by ten on their actual
signed integer frequencies. -/
theorem labelFrequency_multiplierTenPair (x : PairingLabel) :
    labelFrequency (multiplierTenPair x) = 10 * labelFrequency x := by
  unfold labelFrequency multiplierTenPair
  push_cast
  ring

/-- The signed label bijection itself carries every source phase to its target
phase.  The source endpoint `t` and target endpoint `t-1` are both literal in
the type. -/
theorem multiplierTenPair_phase_transport_on_source
    (beta : ℝ) (ell H : ℕ) (x : PairingLabel)
    (hx : PairingSource ell H x) :
    transportPhase beta ell (labelFrequency x) *
        labeledPhase beta ell (labelFrequency (multiplierTenPair x))
          (multiplierTenPair x).2 =
      labeledPhase beta ell (labelFrequency x) x.2 := by
  rcases hx with ⟨_hsign, _hu1, _huH, ht1, _htell⟩
  rw [labelFrequency_multiplierTenPair]
  simpa only [multiplierTenPair, Nat.sub_add_cancel ht1] using
    multiplierTen_phase_transport beta ell (x.2 - 1) (labelFrequency x)

/-- The block is exactly T38's outer phase times its one-dimensional
lacunary sum. -/
theorem frequencyBlock_eq_t38_block
    (beta : ℝ) (ell : ℕ) (u : ℤ) :
    frequencyBlock beta ell u =
      phase u (beta * (10 : ℝ) ^ ell) *
        lacunaryPhaseSum beta ell u := by
  unfold frequencyBlock lacunaryPhaseSum
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  simpa only [labeledPhase] using
    phase_stratum_factorization beta ell j u

/-- Exact one-step telescope with the original lower endpoint `j=0` and the
auxiliary upper endpoint `j=ell`, neither discarded. -/
theorem multiplierTen_oneStep_telescope
    (beta : ℝ) (ell : ℕ) (u : ℤ) :
    frequencyBlock beta ell u -
        transportPhase beta ell u * frequencyBlock beta ell (10 * u) =
      labeledPhase beta ell u 0 - labeledPhase beta ell u ell := by
  unfold frequencyBlock
  rw [Finset.mul_sum]
  simp_rw [multiplierTen_phase_transport]
  have hfront := Finset.sum_range_succ'
    (fun j => labeledPhase beta ell u j) ell
  have hend := Finset.sum_range_succ
    (fun j => labeledPhase beta ell u j) ell
  linear_combination hfront - hend

/-- The two telescope endpoints in their fully explicit form. -/
theorem multiplierTen_endpoints_explicit
    (beta : ℝ) (ell : ℕ) (u : ℤ) :
    labeledPhase beta ell u 0 - labeledPhase beta ell u ell =
      phase u (beta * ((10 : ℝ) ^ ell - 1)) - 1 := by
  unfold labeledPhase
  norm_num [phase, Theory.PiDigits.T27.phase]

/-- T38's literal triangular coefficient for positive `u ≤ R-1`. -/
def triangularWeight (R u : ℕ) : ℝ :=
  1 - (u : ℝ) / (R : ℝ)

/-- The accumulated coefficient arriving at `u` along its unique chain of
predecessors under multiplication by ten. -/
noncomputable def orbitCoefficient
    (beta : ℝ) (ell R u : ℕ) : ℂ :=
  if hu : u = 0 then 0
  else
    (triangularWeight R u : ℂ) +
      if hdiv : 10 ∣ u then
        transportPhase beta ell (u / 10 : ℕ) *
          orbitCoefficient beta ell R (u / 10)
      else 0
termination_by u
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hu) (by norm_num)

/-- The coefficient arriving from the unique predecessor `u/10`, or zero
when `u` is not divisible by ten. -/
def predecessorCoefficient
    (beta : ℝ) (ell R u : ℕ) : ℂ :=
  if 10 ∣ u then
    transportPhase beta ell (u / 10 : ℕ) *
      orbitCoefficient beta ell R (u / 10)
  else 0

/-- The accumulated coefficient satisfies its explicit predecessor
recurrence at every positive frequency. -/
theorem orbitCoefficient_eq_weight_add_predecessor
    (beta : ℝ) (ell R u : ℕ) (hu : 1 ≤ u) :
    orbitCoefficient beta ell R u =
      (triangularWeight R u : ℂ) +
        predecessorCoefficient beta ell R u := by
  rw [orbitCoefficient, dif_neg (by omega : u ≠ 0)]
  rfl

/-- Positive frequencies that possess a successor inside T38's cutoff. -/
def pairingSourceShell (R : ℕ) : Finset ℕ :=
  Icc 1 ((R - 1) / 10)

/-- The exact unpaired top shell `(R-1)/10 < u ≤ R-1`. -/
def terminalShell (R : ℕ) : Finset ℕ :=
  Ioc ((R - 1) / 10) (R - 1)

/-- Every positive cutoff frequency lies in exactly one of the paired-source
and terminal shells. -/
theorem positiveCutoff_partition (R : ℕ) :
    Icc 1 (R - 1) = pairingSourceShell R ∪ terminalShell R := by
  ext u
  simp only [pairingSourceShell, terminalShell, mem_Icc, mem_union, mem_Ioc]
  omega

/-- Reindexing by `u ↦ 10*u` preserves every label and exactly identifies
the predecessor contribution on the full positive cutoff. -/
theorem predecessorSum_eq_successorSum
    (beta : ℝ) (ell R : ℕ) :
    (∑ v ∈ Icc 1 (R - 1),
        predecessorCoefficient beta ell R v *
          frequencyBlock beta ell (v : ℤ)) =
      ∑ u ∈ pairingSourceShell R,
        orbitCoefficient beta ell R u *
          transportPhase beta ell (u : ℤ) *
            frequencyBlock beta ell (10 * u : ℕ) := by
  classical
  unfold predecessorCoefficient pairingSourceShell
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun u _hu => 10 * u)
  · intro u hu
    simp only [mem_filter, mem_Icc] at hu ⊢
    have huH : u * 10 ≤ R - 1 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).mp hu.2
    exact ⟨⟨by omega, by omega⟩, ⟨u, rfl⟩⟩
  · intro a ha b hb hab
    omega
  · intro v hv
    simp only [mem_filter, mem_Icc] at hv
    obtain ⟨hvRange, hvDiv⟩ := hv
    have hmul : 10 * (v / 10) = v := Nat.mul_div_cancel' hvDiv
    refine ⟨v / 10, ?_, hmul⟩
    simp only [mem_Icc]
    constructor
    · by_contra hzero
      have : v / 10 = 0 := by omega
      rw [this, mul_zero] at hmul
      omega
    · exact Nat.div_le_div_right hvRange.2
  · intro u hu
    have hdiv : 10 * u / 10 = u := by omega
    rw [hdiv]
    push_cast
    ring

/-- The exact sum of all finite telescope endpoint terms. -/
def endpointSum (beta : ℝ) (ell R : ℕ) : ℂ :=
  ∑ u ∈ pairingSourceShell R,
    orbitCoefficient beta ell R u *
      (labeledPhase beta ell (u : ℤ) 0 -
        labeledPhase beta ell (u : ℤ) ell)

/-- The labeled terminal contribution.  Its support is literally
`(R-1)/10 < u ≤ R-1` and `0 ≤ j < ell`; no image or quotient can erase a
numerical frequency collision. -/
def terminalCorrelation (beta : ℝ) (ell R : ℕ) : ℂ :=
  ∑ u ∈ terminalShell R,
    orbitCoefficient beta ell R u * frequencyBlock beta ell (u : ℤ)

/-- The terminal shell membership test in literal inequalities. -/
theorem mem_terminalShell_iff {R u : ℕ} :
    u ∈ terminalShell R ↔ (R - 1) / 10 < u ∧ u ≤ R - 1 := by
  simp only [terminalShell, mem_Ioc]

/-- The terminal contribution flattened to the complete labeled `(u,j)`
domain.  Equal numerical frequencies therefore remain separate summands. -/
theorem terminalCorrelation_eq_labeled_sum
    (beta : ℝ) (ell R : ℕ) :
    terminalCorrelation beta ell R =
      ∑ u ∈ Ioc ((R - 1) / 10) (R - 1),
        ∑ j ∈ range ell,
          orbitCoefficient beta ell R u *
            labeledPhase beta ell (u : ℤ) j := by
  unfold terminalCorrelation terminalShell frequencyBlock
  apply sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]

/-- The universal endpoint budget obtained from `|X_{u,0}-X_{u,ell}| ≤ 2`. -/
def endpointBudget (beta : ℝ) (ell R : ℕ) : ℝ :=
  2 * ∑ u ∈ pairingSourceShell R, ‖orbitCoefficient beta ell R u‖

/-- Every endpoint term is bounded explicitly; no endpoint is dropped. -/
theorem norm_endpointSum_le_endpointBudget
    (beta : ℝ) (ell R : ℕ) :
    ‖endpointSum beta ell R‖ ≤ endpointBudget beta ell R := by
  unfold endpointSum endpointBudget
  calc
    ‖∑ u ∈ pairingSourceShell R,
        orbitCoefficient beta ell R u *
          (labeledPhase beta ell (u : ℤ) 0 -
            labeledPhase beta ell (u : ℤ) ell)‖ ≤
        ∑ u ∈ pairingSourceShell R,
          ‖orbitCoefficient beta ell R u *
            (labeledPhase beta ell (u : ℤ) 0 -
              labeledPhase beta ell (u : ℤ) ell)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u ∈ pairingSourceShell R,
        2 * ‖orbitCoefficient beta ell R u‖ := by
      apply sum_le_sum
      intro u hu
      rw [norm_mul]
      have hphase :
          ‖labeledPhase beta ell (u : ℤ) 0 -
            labeledPhase beta ell (u : ℤ) ell‖ ≤ 2 := by
        calc
          ‖labeledPhase beta ell (u : ℤ) 0 -
              labeledPhase beta ell (u : ℤ) ell‖ ≤
              ‖labeledPhase beta ell (u : ℤ) 0‖ +
                ‖labeledPhase beta ell (u : ℤ) ell‖ := norm_sub_le _ _
          _ = 2 := by
            simp [labeledPhase, Theory.PiDigits.T27.norm_phase]
            norm_num
      nlinarith [norm_nonneg (orbitCoefficient beta ell R u)]
    _ = 2 * ∑ u ∈ pairingSourceShell R,
        ‖orbitCoefficient beta ell R u‖ := by
      rw [Finset.mul_sum]

/-- Exact positive-frequency multiplier-ten reduction. -/
theorem positiveFrequencySum_eq_endpoint_add_terminal
    (beta : ℝ) (ell R : ℕ) :
    (∑ u ∈ Icc 1 (R - 1),
        (triangularWeight R u : ℂ) * frequencyBlock beta ell (u : ℤ)) =
      endpointSum beta ell R + terminalCorrelation beta ell R := by
  classical
  let positive := Icc 1 (R - 1)
  let source := pairingSourceShell R
  let terminal := terminalShell R
  let gamma := orbitCoefficient beta ell R
  let pred := predecessorCoefficient beta ell R
  let block : ℕ → ℂ := fun u => frequencyBlock beta ell (u : ℤ)
  have hdisjoint : Disjoint source terminal := by
    rw [disjoint_left]
    intro u hus hut
    simp only [source, pairingSourceShell, mem_Icc] at hus
    simp only [terminal, terminalShell, mem_Ioc] at hut
    omega
  have hpartition : positive = source ∪ terminal := by
    simpa [positive, source, terminal] using positiveCutoff_partition R
  have hsplit :
      (∑ u ∈ positive, gamma u * block u) =
        (∑ u ∈ source, gamma u * block u) +
          ∑ u ∈ terminal, gamma u * block u := by
    rw [hpartition, sum_union hdisjoint]
  have hrecurrence :
      (∑ u ∈ positive,
          (triangularWeight R u : ℂ) * block u) =
        ∑ u ∈ positive, (gamma u - pred u) * block u := by
    apply sum_congr rfl
    intro u hu
    have huPos : 1 ≤ u := by
      have hurange : 1 ≤ u ∧ u ≤ R - 1 := by
        simpa only [positive, mem_Icc] using hu
      exact hurange.1
    have hgamma := orbitCoefficient_eq_weight_add_predecessor
      beta ell R u huPos
    dsimp only [gamma, pred]
    rw [hgamma]
    ring
  have hsourceEndpoint :
      (∑ u ∈ source, gamma u * block u) -
          ∑ u ∈ source,
            gamma u * transportPhase beta ell (u : ℤ) *
              frequencyBlock beta ell (10 * u : ℕ) =
        endpointSum beta ell R := by
    rw [← sum_sub_distrib]
    unfold endpointSum
    apply sum_congr rfl
    intro u hu
    dsimp only [gamma, block]
    rw [show
      orbitCoefficient beta ell R u * frequencyBlock beta ell (u : ℤ) -
          orbitCoefficient beta ell R u *
            transportPhase beta ell (u : ℤ) *
              frequencyBlock beta ell (10 * u : ℕ) =
        orbitCoefficient beta ell R u *
          (frequencyBlock beta ell (u : ℤ) -
            transportPhase beta ell (u : ℤ) *
              frequencyBlock beta ell (10 * u : ℕ)) by ring]
    apply congrArg (fun z : ℂ => orbitCoefficient beta ell R u * z)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      multiplierTen_oneStep_telescope beta ell (u : ℤ)
  rw [hrecurrence]
  simp_rw [sub_mul]
  rw [sum_sub_distrib, hsplit]
  have hpred := predecessorSum_eq_successorSum beta ell R
  change (∑ v ∈ positive, pred v * block v) = _ at hpred
  rw [hpred]
  change
    ((∑ u ∈ source, gamma u * block u) +
        ∑ u ∈ terminal, gamma u * block u) -
      (∑ u ∈ source,
        gamma u * transportPhase beta ell (u : ℤ) *
          frequencyBlock beta ell (10 * u : ℕ)) = _
  rw [show
      (∑ u ∈ terminal, gamma u * block u) =
        terminalCorrelation beta ell R by rfl]
  rw [← hsourceEndpoint]
  ring

/-- One literal signed summand in T38's expansion. -/
def signedFourierTerm (beta : ℝ) (ell R : ℕ) (u : ℤ) : ℂ :=
  (triangularWeight R u.natAbs : ℂ) * frequencyBlock beta ell u

/-- Negating the signed label conjugates the complete labeled block. -/
theorem frequencyBlock_neg_eq_conj
    (beta : ℝ) (ell : ℕ) (u : ℤ) :
    frequencyBlock beta ell (-u) = conj (frequencyBlock beta ell u) := by
  unfold frequencyBlock
  rw [map_sum]
  apply sum_congr rfl
  intro j hj
  unfold labeledPhase
  exact Theory.PiDigits.T27.phase_neg u _

/-- The real part of a literal signed summand is even; this records the two
signed copies without identifying their labels. -/
theorem signedFourierTerm_re_even (beta : ℝ) (ell R : ℕ) :
    Function.Even (fun u : ℤ => (signedFourierTerm beta ell R u).re) := by
  intro u
  unfold signedFourierTerm
  change
    ((triangularWeight R (-u).natAbs : ℂ) *
        frequencyBlock beta ell (-u)).re =
      ((triangularWeight R u.natAbs : ℂ) *
        frequencyBlock beta ell u).re
  rw [Int.natAbs_neg, frequencyBlock_neg_eq_conj]
  simp only [Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.conj_re]

/-- The zero-frequency block has all `ell` labeled terms, each equal to one. -/
theorem signedFourierTerm_zero_re
    (beta : ℝ) (ell R : ℕ) :
    (signedFourierTerm beta ell R 0).re = ell := by
  simp [signedFourierTerm, triangularWeight, frequencyBlock, labeledPhase,
    Theory.PiDigits.T27.phase_zero]

/-- Exact signed-frequency aggregation: zero contributes `ell`, while each
positive label contributes twice its real part. -/
theorem signedFrequencySum_re_eq_zero_add_positive
    (beta : ℝ) (ell R : ℕ) (hR : 1 ≤ R) :
    (∑ u ∈ Fourier.signedFrequenciesZero (R - 1),
        signedFourierTerm beta ell R u).re =
      (ell : ℝ) + 2 *
        (∑ u ∈ Icc 1 (R - 1),
          (triangularWeight R u : ℂ) *
            frequencyBlock beta ell (u : ℤ)).re := by
  let f : ℤ → ℝ := fun u => (signedFourierTerm beta ell R u).re
  have hH : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hsigned := Finset.sum_Icc_of_even_eq_range
    (signedFourierTerm_re_even beta ell R) (R - 1)
  have hpositive :
      (∑ m ∈ range R, f m) =
        f 0 + ∑ u ∈ Icc 1 (R - 1), f u := by
    rw [← hH, Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    apply Finset.sum_bij (fun m _hm => m + 1)
    · intro m hm
      simp only [mem_Icc, mem_range] at hm ⊢
      omega
    · intro a ha b hb hab
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      refine ⟨u - 1, ?_, ?_⟩
      · simp only [mem_range]
        omega
      · omega
    · intro m hm
      rfl
  rw [Complex.re_sum]
  change (∑ u ∈ Fourier.signedFrequenciesZero (R - 1), f u) = _
  rw [show Fourier.signedFrequenciesZero (R - 1) =
      Icc (-(R - 1 : ℕ) : ℤ) (R - 1 : ℕ) by rfl]
  rw [hsigned]
  simp only [nsmul_eq_mul]
  rw [hH]
  rw [hpositive]
  have hf0 : f 0 = ell := signedFourierTerm_zero_re beta ell R
  rw [hf0]
  rw [signedFourierTerm_zero_re]
  dsimp only [f]
  rw [Complex.re_sum]
  unfold signedFourierTerm
  simp only [Int.natAbs_natCast]
  push_cast
  ring

/-- The numerical collision highlighted by T54 is real. -/
theorem numericalFrequency_collision :
    (10 : ℤ) * ((10 : ℤ) ^ 2 - 1) =
      11 * ((10 : ℤ) ^ 2 - 10) := by
  norm_num

/-- The colliding numerical frequencies arise from distinct labels and hence
occur with multiplicity in every labeled sum above. -/
theorem numericalFrequency_collision_labels_distinct :
    ((10, 0) : ℕ × ℕ) ≠ (11, 1) := by
  norm_num

/-- Exact T38 stratum sum after signed conjugate aggregation and the
multiplier-ten reduction.  The factor two records both signed copies. -/
theorem stratumFejerSum_eq_endpoint_add_topShell
    (beta : ℝ) (ell R : ℕ) (hR : 1 ≤ R) :
    ∑ j ∈ range ell,
        fejerKernel (R - 1)
          (beta * ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) =
      (ell : ℝ) +
        2 * (endpointSum beta ell R +
          terminalCorrelation beta ell R).re := by
  classical
  have hexpansion := stratumFejerSum_eq_lacunaryExpansion beta ell R hR
  have hre := congrArg Complex.re hexpansion
  simp only [Complex.ofReal_re] at hre
  rw [hre]
  have hliteral : lacunaryExpansion beta ell R =
      ∑ u ∈ Fourier.signedFrequenciesZero (R - 1),
        signedFourierTerm beta ell R u := by
    unfold lacunaryExpansion signedFourierTerm triangularWeight
    apply sum_congr rfl
    intro u hu
    rw [frequencyBlock_eq_t38_block]
    ring
  rw [hliteral]
  rw [signedFrequencySum_re_eq_zero_add_positive beta ell R hR]
  rw [positiveFrequencySum_eq_endpoint_add_terminal]

/-- The sole unproved analytic input: a strict lower bound for the terminal
correlation on the literal T38 top shell. -/
def TopShellCorrelationHypothesis
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (ell : ℕ) : Prop :=
  let R := stratumOrder chain k ell
  let delta := stratumDelta chain k ell
  (terminalCorrelation (chain.nodeCoefficient k) ell R).re >
    (ell : ℝ) / (8 * (R : ℝ) * delta ^ 2) -
      (ell : ℝ) / 2 +
        endpointBudget (chain.nodeCoefficient k) ell R

/-- The top-shell hypothesis and the displayed endpoint bound imply T38's
literal strict analytic threshold, with every domain visible in the type. -/
theorem topShellCorrelation_implies_strict_t38_threshold
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d}
    (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hdepth : ell < commonDepth chain k)
    (htop : TopShellCorrelationHypothesis chain k ell) :
    (ell : ℝ) /
        (4 * (stratumOrder chain k ell : ℝ) *
          (stratumDelta chain k ell) ^ 2) <
      ∑ j ∈ range ell,
        fejerKernel (stratumOrder chain k ell - 1)
          (chain.nodeCoefficient k *
            ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) := by
  have _hlegalDepth := hdepth
  let beta : ℝ := chain.nodeCoefficient k
  let R : ℕ := stratumOrder chain k ell
  let delta : ℝ := stratumDelta chain k ell
  have hdelta : 0 < delta := by
    simpa only [delta] using stratumDelta_pos chain k ell hD
  have hR : 1 ≤ R := by
    simpa only [R] using stratumOrder_pos chain k ell hD
  have hsum := stratumFejerSum_eq_endpoint_add_topShell beta ell R hR
  have hendNorm := norm_endpointSum_le_endpointBudget beta ell R
  have hendAbs :
      |(endpointSum beta ell R).re| ≤ endpointBudget beta ell R :=
    (Complex.abs_re_le_norm _).trans hendNorm
  have hendLower :
      -endpointBudget beta ell R ≤ (endpointSum beta ell R).re :=
    (abs_le.mp hendAbs).1
  have htop' :
      (terminalCorrelation beta ell R).re >
        (ell : ℝ) / (8 * (R : ℝ) * delta ^ 2) -
          (ell : ℝ) / 2 + endpointBudget beta ell R := by
    simpa only [TopShellCorrelationHypothesis, beta, R, delta] using htop
  have hdouble :
      2 * ((ell : ℝ) / (8 * (R : ℝ) * delta ^ 2)) =
        (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) := by
    have hRreal : (R : ℝ) ≠ 0 := by positivity
    have hdeltaSq : delta ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  change (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) < _
  rw [hsum]
  rw [Complex.add_re]
  nlinarith

/-- The strict threshold theorem, together with the three literal legality
conditions, packages exactly T38's FSFS predicate. -/
theorem topShellCorrelation_implies_FSFS
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d}
    (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hdepth : ell < commonDepth chain k)
    (htop : TopShellCorrelationHypothesis chain k ell) :
    FSFS chain k ell := by
  exact ⟨hD, hell, hdepth,
    topShellCorrelation_implies_strict_t38_threshold
      hD hell hdepth htop⟩

/-- Conditional T38/T34 payoff: the same hypothesis gives the strict
zero-cutoff mixed-sum premise. -/
theorem topShellCorrelation_implies_mixedSumLowerBound_zero
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d}
    (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hdepth : ell < commonDepth chain k)
    (htop : TopShellCorrelationHypothesis chain k ell) :
    MixedSumLowerBound chain k 0 0 := by
  exact (topShellCorrelation_implies_FSFS hD hell hdepth htop).implies_mixedSumLowerBound_zero

/-- Conditional T34 payoff with the equal-index witness exposed. -/
theorem topShellCorrelation_implies_adjacentPairCompatible
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d}
    (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hdepth : ell < commonDepth chain k)
    (htop : TopShellCorrelationHypothesis chain k ell) :
    ∃ j s : ℕ, ∃ a0 a1 : ℤ,
      AdjacentPairCompatible chain k j s j s a0 a1 := by
  exact mixedSumLowerBound_implies_adjacentPairCompatible chain k 0 0
    (topShellCorrelation_implies_mixedSumLowerBound_zero hD hell hdepth htop)

/-- Fully conditional T28 payoff.  The irrationality and closing hypotheses,
as well as positivity of the original T26 multipliers, remain explicit. -/
theorem topShellCorrelation_and_T28_bounds_false
    {M D K d h r ell Q8 J S : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d}
    (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hdepth : ell < commonDepth chain k)
    (htop : TopShellCorrelationHypothesis chain k ell)
    (hh : 1 ≤ h) (hr : 1 ≤ r)
    (hirr : ExponentEightLowerBound Q8)
    (hclosing : ∀ j s : ℕ, ∀ a0 a1 : ℤ,
      AdjacentPairCompatible chain k j s j s a0 a1 →
        ExponentEightClosingBounds Q8 J S chain k j s j s a0) :
    False := by
  obtain ⟨j, s, a0, a1, hcompatible⟩ :=
    topShellCorrelation_implies_adjacentPairCompatible hD hell hdepth htop
  exact compatible_pair_contradicts_exponentEight chain k hh hr hirr
    hcompatible (hclosing j s a0 a1 hcompatible)

end SignedMultiplierTenPairingT55
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.multiplierTen_phase_transport
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.signedMultiplierTenPairing_bijective
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.multiplierTenPair_phase_transport_on_source
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.multiplierTen_oneStep_telescope
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.norm_endpointSum_le_endpointBudget
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.positiveFrequencySum_eq_endpoint_add_terminal
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.terminalCorrelation_eq_labeled_sum
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.stratumFejerSum_eq_endpoint_add_topShell
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.topShellCorrelation_implies_strict_t38_threshold
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.topShellCorrelation_implies_FSFS
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.topShellCorrelation_implies_mixedSumLowerBound_zero
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.topShellCorrelation_implies_adjacentPairCompatible
#print axioms DecimalFactorComplexity.SignedMultiplierTenPairingT55.topShellCorrelation_and_T28_bounds_false
