import TheoryLib.PiLacunaryNearReturnSparsity.T55SignedMultiplierTenPairing

/-!
# T61: direct-label adjacent phase variance

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module formalizes the direct-label core of the unverified T58 note.  It
uses T26's genuine adjacent coefficient and T55's literal terminal shell.  No
phase in the direct term is replaced by its norm.  The valuation-expanded
predecessor mass called `X` in T58 is explicitly weakened to the norm of the
exact predecessor remainder.  No fixed-pi, A1, C1, C2, FSFS, or T28 claim is
made.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity
namespace DirectLabelAdjacentPhaseVarianceT61

open IteratedLagResonance
open FiniteInverseDichotomy
open SharedResonanceChain
open FixedStratumFejerSpike
open SignedMultiplierTenPairingT55

abbrev phase := Theory.PiDigits.T27.phase
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-- T58's integer frequency `m_{u,j}=u(10^ell-10^j)`. -/
def directFrequency (ell u j : ℕ) : ℤ :=
  (u : ℤ) * ((10 : ℤ) ^ ell - (10 : ℤ) ^ j)

/-- The preceding-node character `chi_0(m)=e(beta_0 m)`. -/
def precedingCharacter (beta0 : ℝ) (m : ℤ) : ℂ :=
  phase m beta0

/-- The literal terminal direct-label contribution before adjacent pullback. -/
def directTerminalCorrelation (beta : ℝ) (ell R : ℕ) : ℂ :=
  ∑ u ∈ terminalShell R, ∑ j ∈ range ell,
    (triangularWeight R u : ℂ) * labeledPhase beta ell (u : ℤ) j

/-- The exact terminal remainder after removing the `a=0` direct labels.
This is the formal weakening of T58's valuation-expanded predecessor sum. -/
def predecessorRemainder (beta : ℝ) (ell R : ℕ) : ℂ :=
  terminalCorrelation beta ell R - directTerminalCorrelation beta ell R

/-- A public, exact budget for the predecessor remainder. -/
def predecessorRemainderBudget (beta : ℝ) (ell R : ℕ) : ℝ :=
  ‖predecessorRemainder beta ell R‖

/-- The direct positive mass, with the terminal shell and block cutoff visible. -/
def directTerminalMass (ell R : ℕ) : ℝ :=
  ∑ u ∈ terminalShell R, ∑ _j ∈ range ell, triangularWeight R u

/-- The next legal node after `k`, under T58's strict adjacent-node premise. -/
def nextNode {d : ℕ} (k : Fin d) (hk : k.val + 1 < d) : Fin d :=
  ⟨k.val + 1, hk⟩

/-- The incoming shift from prefix node `k` to prefix node `k+1`, defined
directly from T26's chain data. -/
def incomingShift
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) : ℕ :=
  chain.shifts.get ⟨k.val, by simpa [chain.length_eq] using k.isLt⟩

/-- T58 equation (3.2), proved directly from T26's shift list. -/
theorem take_succ_eq_take_append_incomingShift
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) :
    chain.shifts.take (k.val + 1) =
      chain.shifts.take k.val ++ [incomingShift chain k] := by
  have hk : k.val < chain.shifts.length := by
    simpa [chain.length_eq] using k.isLt
  simpa [incomingShift, List.get_eq_getElem] using
    (List.take_append_getElem hk).symm

/-- T58 equation (3.3), derived directly from T26's literal coefficient
definition rather than imported from an adjacent-compatibility module. -/
theorem nodeCoefficient_succ_exact
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) :
    chain.nodeCoefficient (k.val + 1) =
      ((10 : ℝ) ^ incomingShift chain k - 1) *
        chain.nodeCoefficient k.val := by
  unfold GeometricResonanceChain.nodeCoefficient
  rw [take_succ_eq_take_append_incomingShift chain k,
    List.map_append, List.prod_append]
  simp only [List.map_singleton, List.prod_singleton]
  ring

/-- T58's exact two-factor pullback of all direct labels through one genuine
T26 adjacent step.  The support remains the labeled product
`terminalShell R × range ell`. -/
def directAdjacentCorrelation
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) : ℂ :=
  ∑ u ∈ terminalShell R, ∑ j ∈ range ell,
    (triangularWeight R u : ℂ) *
      (precedingCharacter (chain.nodeCoefficient k)
          ((10 : ℤ) ^ (incomingShift chain k) *
            directFrequency ell u j) *
        conj (precedingCharacter (chain.nodeCoefficient k)
          (directFrequency ell u j)))

/-- T58's direct-label adjacent phase variance, retaining every label even
when two labels have the same numerical frequency. -/
def directAdjacentVariance
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) : ℝ :=
  ∑ u ∈ terminalShell R, ∑ j ∈ range ell,
    triangularWeight R u *
      ‖precedingCharacter (chain.nodeCoefficient k)
          ((10 : ℤ) ^ (incomingShift chain k) *
            directFrequency ell u j) -
        precedingCharacter (chain.nodeCoefficient k)
          (directFrequency ell u j)‖ ^ 2

/-- A labeled T55 phase is the character at T58's direct integer frequency. -/
theorem labeledPhase_eq_directFrequency
    (beta : ℝ) (ell u j : ℕ) :
    labeledPhase beta ell (u : ℤ) j = phase (directFrequency ell u j) beta := by
  unfold labeledPhase directFrequency
  simp only [Theory.PiDigits.T27.phase]
  congr 1
  push_cast
  ring

/-- Exact adjacent autocorrelation identity with both complex factors kept. -/
theorem phase_adjacent_pullback (beta0 : ℝ) (s : ℕ) (m : ℤ) :
    phase m (((10 : ℝ) ^ s - 1) * beta0) =
      phase ((10 : ℤ) ^ s * m) beta0 * conj (phase m beta0) := by
  change Theory.PiDigits.T27.phase m (((10 : ℝ) ^ s - 1) * beta0) =
    Theory.PiDigits.T27.phase ((10 : ℤ) ^ s * m) beta0 *
      conj (Theory.PiDigits.T27.phase m beta0)
  rw [show
    Theory.PiDigits.T27.phase ((10 : ℤ) ^ s * m) beta0 *
        conj (Theory.PiDigits.T27.phase m beta0) =
      conj (Theory.PiDigits.T27.phase m beta0) *
        Theory.PiDigits.T27.phase ((10 : ℤ) ^ s * m) beta0 by ring]
  rw [Theory.PiDigits.T27.phase_sub]
  simp only [Theory.PiDigits.T27.phase]
  congr 1
  push_cast
  ring

/-- One genuine T26 adjacent coefficient step pulls a literal T55 direct
label back to the two preceding-node characters, with no absolute-value
replacement. -/
theorem labeledPhase_adjacent_pullback
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell u j : ℕ) :
    labeledPhase (chain.nodeCoefficient (k.val + 1)) ell (u : ℤ) j =
      precedingCharacter (chain.nodeCoefficient k)
          ((10 : ℤ) ^ (incomingShift chain k) *
            directFrequency ell u j) *
        conj (precedingCharacter (chain.nodeCoefficient k)
          (directFrequency ell u j)) := by
  rw [labeledPhase_eq_directFrequency]
  rw [nodeCoefficient_succ_exact chain k]
  exact phase_adjacent_pullback _ _ _

/-- Summing the preceding theorem on the literal terminal shell preserves
the complete `(u,j)` label multiplicity and the Fourier cutoff `R-1`. -/
theorem directAdjacentCorrelation_eq_directTerminalCorrelation
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) :
    directAdjacentCorrelation chain k ell R =
      directTerminalCorrelation (chain.nodeCoefficient (k.val + 1)) ell R := by
  unfold directAdjacentCorrelation directTerminalCorrelation
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro j hj
  rw [labeledPhase_adjacent_pullback chain k ell u j]

/-- The pulled-back correlation with T55's half-open terminal shell and the
block cutoff written literally.  The nested sum retains collision
multiplicity. -/
theorem directAdjacentCorrelation_eq_labeled_sum
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) :
    directAdjacentCorrelation chain k ell R =
      ∑ u ∈ Ioc ((R - 1) / 10) (R - 1), ∑ j ∈ range ell,
        (triangularWeight R u : ℂ) *
          (precedingCharacter (chain.nodeCoefficient k)
              ((10 : ℤ) ^ (incomingShift chain k) *
                directFrequency ell u j) *
            conj (precedingCharacter (chain.nodeCoefficient k)
              (directFrequency ell u j))) := by
  rfl

/-- The variance with every terminal-shell endpoint and Fourier cutoff
written literally.  Numerically colliding `(u,j)` labels remain distinct. -/
theorem directAdjacentVariance_eq_labeled_sum
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) :
    directAdjacentVariance chain k ell R =
      ∑ u ∈ Ioc ((R - 1) / 10) (R - 1), ∑ j ∈ range ell,
        triangularWeight R u *
          ‖precedingCharacter (chain.nodeCoefficient k)
              ((10 : ℤ) ^ (incomingShift chain k) *
                directFrequency ell u j) -
            precedingCharacter (chain.nodeCoefficient k)
              (directFrequency ell u j)‖ ^ 2 := by
  rfl

/-- The exact terminal split.  No terminal coefficient or endpoint is
discarded. -/
theorem terminalCorrelation_eq_direct_add_predecessorRemainder
    (beta : ℝ) (ell R : ℕ) :
    terminalCorrelation beta ell R =
      directTerminalCorrelation beta ell R + predecessorRemainder beta ell R := by
  unfold predecessorRemainder
  ring

/-- The exact remainder is the complete labeled sum of T55's predecessor
coefficients.  This proves that the direct term removed above is genuinely
the `triangularWeight` summand in T55's coefficient recurrence. -/
theorem predecessorRemainder_eq_labeled_sum
    (beta : ℝ) (ell R : ℕ) :
    predecessorRemainder beta ell R =
      ∑ u ∈ Ioc ((R - 1) / 10) (R - 1), ∑ j ∈ range ell,
        predecessorCoefficient beta ell R u *
          labeledPhase beta ell (u : ℤ) j := by
  unfold predecessorRemainder directTerminalCorrelation terminalShell
  rw [terminalCorrelation_eq_labeled_sum]
  rw [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro u hu
  rw [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have huPos : 1 ≤ u := by
    simp only [mem_Ioc] at hu
    omega
  rw [orbitCoefficient_eq_weight_add_predecessor beta ell R u huPos]
  ring

/-- The real part of the exact predecessor remainder is bounded below by its
explicit norm budget. -/
theorem predecessorRemainder_re_ge_neg_budget
    (beta : ℝ) (ell R : ℕ) :
    -predecessorRemainderBudget beta ell R ≤
      (predecessorRemainder beta ell R).re := by
  unfold predecessorRemainderBudget
  exact neg_le_of_abs_le (Complex.abs_re_le_norm _)

/-- The elementary unit-circle identity used by T58's variance reduction. -/
theorem phase_pair_re_eq_one_sub_half_norm_sq
    (beta : ℝ) (q m : ℤ) :
    (phase q beta * conj (phase m beta)).re =
      1 - ‖phase q beta - phase m beta‖ ^ 2 / 2 := by
  let z := phase q beta
  let y := phase m beta
  have hz : ‖z‖ = 1 := by
    simpa only [z] using Theory.PiDigits.T27.norm_phase q beta
  have hy : ‖y‖ = 1 := by
    simpa only [y] using Theory.PiDigits.T27.norm_phase m beta
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = 1 := by rw [hz]; norm_num
  have hysq : y.re ^ 2 + y.im ^ 2 = 1 := by
    calc
      y.re ^ 2 + y.im ^ 2 = Complex.normSq y := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖y‖ ^ 2 := Complex.normSq_eq_norm_sq y
      _ = 1 := by rw [hy]; norm_num
  change (z * conj y).re = 1 - ‖z - y‖ ^ 2 / 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  nlinarith

/-- Exact direct-label variance identity from T58, equation (6.4), on the
literal shell and cutoff. -/
theorem directAdjacentCorrelation_re_eq_mass_sub_half_variance
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) :
    (directAdjacentCorrelation chain k ell R).re =
      directTerminalMass ell R - directAdjacentVariance chain k ell R / 2 := by
  unfold directAdjacentCorrelation directTerminalMass directAdjacentVariance
  simp_rw [Complex.re_sum]
  calc
    (∑ u ∈ terminalShell R, ∑ j ∈ range ell,
        ((triangularWeight R u : ℂ) *
          (precedingCharacter (chain.nodeCoefficient k)
              ((10 : ℤ) ^ (incomingShift chain k) *
                directFrequency ell u j) *
            conj (precedingCharacter (chain.nodeCoefficient k)
              (directFrequency ell u j)))).re) =
        ∑ u ∈ terminalShell R, ∑ j ∈ range ell,
          (triangularWeight R u - triangularWeight R u *
            ‖precedingCharacter (chain.nodeCoefficient k)
                ((10 : ℤ) ^ (incomingShift chain k) *
                  directFrequency ell u j) -
              precedingCharacter (chain.nodeCoefficient k)
                (directFrequency ell u j)‖ ^ 2 / 2) := by
      apply sum_congr rfl
      intro u hu
      apply sum_congr rfl
      intro j hj
      unfold precedingCharacter
      rw [show ∀ w : ℝ, ∀ z : ℂ, ((w : ℂ) * z).re = w * z.re by
        intro w z
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]]
      rw [phase_pair_re_eq_one_sub_half_norm_sq]
      ring
    _ = (∑ u ∈ terminalShell R, ∑ _j ∈ range ell,
          triangularWeight R u) -
        (∑ u ∈ terminalShell R, ∑ j ∈ range ell,
          triangularWeight R u *
            ‖precedingCharacter (chain.nodeCoefficient k)
                ((10 : ℤ) ^ (incomingShift chain k) *
                  directFrequency ell u j) -
              precedingCharacter (chain.nodeCoefficient k)
                (directFrequency ell u j)‖ ^ 2) / 2 := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_div]

/-- T58's explicit phase-variance premise with every budget stated.  Compared
with the note, `predecessorRemainderBudget` is an explicit weakening of `X`:
it is the norm of the exact remainder rather than a valuation-expanded upper
bound. -/
def DirectLabelAdjacentPhaseVarianceWithExactRemainder
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) (delta : ℝ) : Prop :=
  directAdjacentVariance chain k ell R <
    (ell : ℝ) + 2 * directTerminalMass ell R -
      2 * predecessorRemainderBudget
        (chain.nodeCoefficient (k.val + 1)) ell R -
      2 * endpointBudget (chain.nodeCoefficient (k.val + 1)) ell R -
      (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2)

/-- The explicit weakened DLAPV premise implies T55's literal strict Fejer
threshold at the adjacent coefficient. -/
theorem directLabelAdjacentPhaseVariance_implies_fejer_threshold
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) (delta : ℝ)
    (hR : 1 ≤ R)
    (hvar : DirectLabelAdjacentPhaseVarianceWithExactRemainder
      chain k ell R delta) :
    (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) <
      ∑ j ∈ range ell, fejerKernel (R - 1)
        (chain.nodeCoefficient (k.val + 1) *
          ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) := by
  unfold DirectLabelAdjacentPhaseVarianceWithExactRemainder at hvar
  let beta := chain.nodeCoefficient (k.val + 1)
  have hsum := stratumFejerSum_eq_endpoint_add_topShell beta ell R hR
  have hendNorm := norm_endpointSum_le_endpointBudget beta ell R
  have hendLower :
      -endpointBudget beta ell R ≤ (endpointSum beta ell R).re := by
    exact neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hendNorm)
  have hremLower := predecessorRemainder_re_ge_neg_budget beta ell R
  have hsplit := terminalCorrelation_eq_direct_add_predecessorRemainder beta ell R
  have hpull := directAdjacentCorrelation_eq_directTerminalCorrelation chain k ell R
  have hdirect := directAdjacentCorrelation_re_eq_mass_sub_half_variance
    chain k ell R
  have hterminal :
      directTerminalMass ell R - directAdjacentVariance chain k ell R / 2 -
          predecessorRemainderBudget beta ell R ≤
        (terminalCorrelation beta ell R).re := by
    rw [hsplit, Complex.add_re, ← hpull, hdirect]
    linarith
  change (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) < _
  rw [hsum, Complex.add_re]
  dsimp only [beta] at hendLower hterminal hvar ⊢
  nlinarith

/-- Chain-shaped form of the threshold theorem.  The incoming node `k`, the
adjacent legal T55 node `q=k+1`, the legal stratum, and T55's literal `R` and
`delta` are all exposed. -/
theorem directLabelAdjacentPhaseVariance_implies_strict_t38_threshold
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    (k : Fin d) (hk : k.val + 1 < d)
    (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hdepth : ell < commonDepth chain (nextNode k hk))
    (hvar : DirectLabelAdjacentPhaseVarianceWithExactRemainder chain k ell
      (stratumOrder chain (nextNode k hk) ell)
      (stratumDelta chain (nextNode k hk) ell)) :
    (ell : ℝ) /
        (4 * (stratumOrder chain (nextNode k hk) ell : ℝ) *
          stratumDelta chain (nextNode k hk) ell ^ 2) <
      ∑ j ∈ range ell,
        fejerKernel (stratumOrder chain (nextNode k hk) ell - 1)
          (chain.nodeCoefficient (nextNode k hk) *
            ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) := by
  have _ := hell
  have _ := hdepth
  have hR : 1 ≤ stratumOrder chain (nextNode k hk) ell :=
    stratumOrder_pos chain (nextNode k hk) ell hD
  simpa only [nextNode] using
    directLabelAdjacentPhaseVariance_implies_fejer_threshold
      chain k ell (stratumOrder chain (nextNode k hk) ell)
        (stratumDelta chain (nextNode k hk) ell) hR hvar

/-- At zero preceding coefficient every direct adjacent phase difference is
zero.  This is a kernel-checked interface test, not a fixed-pi example. -/
theorem directAdjacentVariance_eq_zero_of_nodeCoefficient_eq_zero
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ)
    (hbeta : chain.nodeCoefficient k = 0) :
    directAdjacentVariance chain k ell R = 0 := by
  unfold directAdjacentVariance precedingCharacter
  simp only [hbeta, Theory.PiDigits.T27.phase]
  simp

/-- The literal direct mass at the smallest nonempty cutoff. -/
theorem directTerminalMass_one_two : directTerminalMass 1 2 = 1 / 2 := by
  norm_num [directTerminalMass, terminalShell, triangularWeight]

/-- The endpoint shell is empty at `R=2`. -/
theorem endpointBudget_one_two (beta : ℝ) : endpointBudget beta 1 2 = 0 := by
  norm_num [endpointBudget, pairingSourceShell]

/-- An explicit arithmetic test of the weakened DLAPV constants at
`ell=1`, `R=2`, and `delta=1`.  The two zero premises isolate the phase and
predecessor inputs; the preceding theorem proves the phase premise whenever
the preceding node coefficient is zero.  This is not a fixed-pi claim. -/
theorem directLabelAdjacentPhaseVariance_one_two_test
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d)
    (hvariance : directAdjacentVariance chain k 1 2 = 0)
    (hremainder : predecessorRemainderBudget
      (chain.nodeCoefficient (k.val + 1)) 1 2 = 0) :
    DirectLabelAdjacentPhaseVarianceWithExactRemainder chain k 1 2 1 := by
  unfold DirectLabelAdjacentPhaseVarianceWithExactRemainder
  rw [hvariance, hremainder, directTerminalMass_one_two,
    endpointBudget_one_two]
  norm_num

end DirectLabelAdjacentPhaseVarianceT61
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.labeledPhase_eq_directFrequency
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.take_succ_eq_take_append_incomingShift
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.nodeCoefficient_succ_exact
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.phase_adjacent_pullback
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.labeledPhase_adjacent_pullback
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directAdjacentCorrelation_eq_directTerminalCorrelation
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directAdjacentCorrelation_eq_labeled_sum
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directAdjacentVariance_eq_labeled_sum
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.terminalCorrelation_eq_direct_add_predecessorRemainder
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.predecessorRemainder_eq_labeled_sum
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directAdjacentCorrelation_re_eq_mass_sub_half_variance
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directLabelAdjacentPhaseVariance_implies_fejer_threshold
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directLabelAdjacentPhaseVariance_implies_strict_t38_threshold
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directAdjacentVariance_eq_zero_of_nodeCoefficient_eq_zero
#print axioms DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directLabelAdjacentPhaseVariance_one_two_test
