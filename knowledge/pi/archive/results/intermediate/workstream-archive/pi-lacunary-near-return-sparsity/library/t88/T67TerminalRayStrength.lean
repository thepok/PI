import TheoryLib.PiDigits.T26WeylCancellationV1
import TheoryLib.PiLacunaryNearReturnSparsity.T4ClusterNearReturns
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy
import TheoryLib.PiLacunaryNearReturnSparsity.T55SignedMultiplierTenPairing
import TheoryLib.PiLacunaryNearReturnSparsity.T61DirectLabelAdjacentPhaseVariance
import TheoryLib.PiPositiveDecimalFactorEntropy.T3FiniteFourierObstruction

/-!
# T67: finite terminal-ray strength and Walsh collision energy

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module does not import the unverified T60 note. It defines genuine finite
empirical Fourier coefficients of a real decimal ray, proves a T61-compatible
uniform defect implication on T55's literal labeled terminal shell, and proves
the exact finite Walsh/cylinder-collision identity for the pi digit orbit.

The final separator witnesses are deliberately typed as arbitrary finite
complex arrays. They are not probability measures, Fourier transforms, or
empirical orbits, and no nonimplication for an actual orbit follows from them.
No theorem below asserts a fixed-pi cancellation estimate, C1, C2, normality,
equidistribution, or pair correlation.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity
namespace TerminalRayStrengthT67

open ClusterNearReturns
open FiniteCylinderEnergy
open SharedResonanceChain
open FixedStratumFejerSpike
open SignedMultiplierTenPairingT55
open DirectLabelAdjacentPhaseVarianceT61
open DecimalFactorEntropy.FiniteFourierObstruction

abbrev phase := Theory.PiDigits.T27.phase
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-! ## Genuine finite empirical Fourier variables -/

/-- The genuine base-ten circle orbit of an arbitrary real parameter. -/
def decimalRayOrbit (beta : ℝ) (j : ℕ) : UnitAddCircle :=
  (((10 : ℝ) ^ j * beta : ℝ) : UnitAddCircle)

/-- Positive-sign Fourier coefficient of the first `N` points of a real
decimal ray. The empirical interpretation below always assumes `1 ≤ N`. -/
def finiteEmpiricalFourier (beta : ℝ) (N : ℕ) (h : ℤ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ range N, phase h ((10 : ℝ) ^ j * beta)

/-- One-step multiplier-ten invariance defect of a genuine finite empirical
coefficient. -/
def finiteEmpiricalInvarianceDefect
    (beta : ℝ) (N : ℕ) (m : ℤ) : ℂ :=
  finiteEmpiricalFourier beta N (10 * m) -
    finiteEmpiricalFourier beta N m

/-- The finite sum above is exactly the checked empirical-mean interface. -/
theorem finiteEmpiricalFourier_eq_circleEmpiricalMean
    (beta : ℝ) (N : ℕ) (h : ℤ) :
    finiteEmpiricalFourier beta N h =
      Theory.PiDigits.T26.circleEmpiricalMean
        (decimalRayOrbit beta) (fourier h) N := by
  unfold finiteEmpiricalFourier Theory.PiDigits.T26.circleEmpiricalMean
  congr 1
  apply sum_congr rfl
  intro j hj
  simp only [decimalRayOrbit, fourier_coe_apply, phase,
    Theory.PiDigits.T27.phase]
  congr 1
  norm_num

/-- Multiplication by ten in frequency shifts the decimal-ray sample index by
one. -/
theorem phase_ten_mul_shift (beta : ℝ) (m : ℤ) (j : ℕ) :
    phase (10 * m) ((10 : ℝ) ^ j * beta) =
      phase m ((10 : ℝ) ^ (j + 1) * beta) := by
  unfold phase Theory.PiDigits.T27.phase
  congr 1
  push_cast
  rw [pow_succ]
  ring

/-- Exact endpoint-sensitive empirical invariance identity. -/
theorem length_mul_finiteEmpiricalInvarianceDefect
    (beta : ℝ) (N : ℕ) (m : ℤ) (hN : 1 ≤ N) :
    (N : ℂ) * finiteEmpiricalInvarianceDefect beta N m =
      phase ((10 : ℤ) ^ N * m) beta - phase m beta := by
  have hNc : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hN)
  unfold finiteEmpiricalInvarianceDefect finiteEmpiricalFourier
  rw [mul_sub]
  simp only [← mul_assoc, mul_inv_cancel₀ hNc, one_mul]
  simp_rw [phase_ten_mul_shift]
  let f : ℕ → ℂ := fun j => phase m ((10 : ℝ) ^ j * beta)
  have hfront := Finset.sum_range_succ' f N
  have hend := Finset.sum_range_succ f N
  have hphaseN : f N = phase ((10 : ℤ) ^ N * m) beta := by
    unfold f phase Theory.PiDigits.T27.phase
    congr 1
    push_cast
    ring
  have hphase0 : f 0 = phase m beta := by
    simp [f]
  change (∑ j ∈ range N, f (j + 1)) - ∑ j ∈ range N, f j = _
  rw [hphase0] at hfront
  rw [hphaseN] at hend
  have hshifted : (∑ j ∈ range N, f (j + 1)) =
      (∑ j ∈ range (N + 1), f j) - phase m beta := by
    rw [eq_sub_iff_add_eq]
    exact hfront.symm
  have hbase : (∑ j ∈ range N, f j) =
      (∑ j ∈ range (N + 1), f j) - phase ((10 : ℤ) ^ N * m) beta := by
    rw [eq_sub_iff_add_eq]
    exact hend.symm
  rw [hshifted, hbase]
  ring

/-- Norm form of the endpoint identity, retaining the empirical factor `N`. -/
theorem norm_endpointDifference_eq_length_mul_defect
    (beta : ℝ) (N : ℕ) (m : ℤ) (hN : 1 ≤ N) :
    ‖phase ((10 : ℤ) ^ N * m) beta - phase m beta‖ =
      (N : ℝ) * ‖finiteEmpiricalInvarianceDefect beta N m‖ := by
  have h := congrArg norm
    (length_mul_finiteEmpiricalInvarianceDefect beta N m hN)
  rw [norm_mul, norm_natCast] at h
  exact h.symm

/-! ## Primitive decimal rays and the literal T55 shell -/

/-- Positive primitive bases for multiplication by ten. Primitive means
`10 ∤ v`, not coprimality with ten. -/
def primitiveDecimalBases (H : ℕ) : Finset ℕ :=
  (Icc 1 H).filter fun v => ¬ 10 ∣ v

/-- Frequencies on the ray `10^a v` which lie in the exact half-open terminal
interval `(H/10,H]`. -/
def primitiveDecimalRayShell (H v : ℕ) : Finset ℕ :=
  by
    classical
    exact (Ioc (H / 10) H).filter fun u => ∃ a : ℕ, u = 10 ^ a * v

theorem mem_primitiveDecimalBases_iff {H v : ℕ} :
    v ∈ primitiveDecimalBases H ↔ 1 ≤ v ∧ v ≤ H ∧ ¬ 10 ∣ v := by
  simp [primitiveDecimalBases, and_assoc]

theorem mem_primitiveDecimalRayShell_iff {H v u : ℕ} :
    u ∈ primitiveDecimalRayShell H v ↔
      H / 10 < u ∧ u ≤ H ∧ ∃ a : ℕ, u = 10 ^ a * v := by
  simp [primitiveDecimalRayShell, and_assoc]

/-- T55's cutoff `R-1` becomes exactly `(H/10,H]` at `R=H+1`. -/
theorem terminalShell_succ_eq (H : ℕ) :
    terminalShell (H + 1) = Ioc (H / 10) H := by
  simp [terminalShell]

/-! ## T61-compatible qualified UPRID -/

/-- The exact-remainder margin appearing literally on the right side of T61's
variance premise. This is intentionally not identified with T60's unformalized
valuation-expanded predecessor budget. -/
def exactRemainderMargin
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) (delta : ℝ) : ℝ :=
  (ell : ℝ) + 2 * directTerminalMass ell R -
    2 * predecessorRemainderBudget
      (chain.nodeCoefficient (k.val + 1)) ell R -
    2 * endpointBudget (chain.nodeCoefficient (k.val + 1)) ell R -
    (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2)

/-- Uniform Primitive-Ray Invariance Defect, qualified to T61's exact
predecessor remainder. The pointwise bound is on the unchanged labeled domain
`u ∈ Ioc ((R-1)/10) (R-1)` and `j ∈ range ell`; numerical frequency
collisions are not quotiented. -/
def T61QualifiedUPRID
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) (delta : ℝ) : Prop :=
  ∃ eta : ℝ, 0 ≤ eta ∧
    directTerminalMass ell R * eta ^ 2 <
      exactRemainderMargin chain k ell R delta ∧
    ∀ u ∈ terminalShell R, ∀ j ∈ range ell,
      (incomingShift chain k : ℝ) *
          ‖finiteEmpiricalInvarianceDefect
            (chain.nodeCoefficient k) (incomingShift chain k)
              (directFrequency ell u j)‖ ≤ eta

/-- T61's adjacent variance is exactly a weighted sum of squared genuine
empirical invariance defects, with every `(u,j)` label retained. -/
theorem directAdjacentVariance_eq_empiricalDefectSum
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ)
    (hshift : 1 ≤ incomingShift chain k) :
    directAdjacentVariance chain k ell R =
      ∑ u ∈ terminalShell R, ∑ j ∈ range ell,
        triangularWeight R u *
          ((incomingShift chain k : ℝ) *
            ‖finiteEmpiricalInvarianceDefect
              (chain.nodeCoefficient k) (incomingShift chain k)
                (directFrequency ell u j)‖) ^ 2 := by
  unfold directAdjacentVariance precedingCharacter
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro j hj
  rw [norm_endpointDifference_eq_length_mul_defect _ _ _ hshift]

/-- T55's triangular weights are nonnegative on its literal terminal shell. -/
theorem triangularWeight_nonneg_of_mem_terminalShell
    {R u : ℕ} (hR : 1 ≤ R) (hu : u ∈ terminalShell R) :
    0 ≤ triangularWeight R u := by
  rw [mem_terminalShell_iff] at hu
  unfold triangularWeight
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have huR : (u : ℝ) ≤ R := by exact_mod_cast hu.2.trans (Nat.sub_le R 1)
  have hdiv : (u : ℝ) / (R : ℝ) ≤ 1 := (div_le_one hRreal).2 huR
  linarith

/-- Qualified UPRID implies T61's literal exact-remainder variance premise. -/
theorem t61QualifiedUPRID_implies_literal_T61_premise
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) (delta : ℝ)
    (hR : 1 ≤ R) (hshift : 1 ≤ incomingShift chain k)
    (huprid : T61QualifiedUPRID chain k ell R delta) :
    DirectLabelAdjacentPhaseVarianceWithExactRemainder
      chain k ell R delta := by
  obtain ⟨eta, heta, hbudget, huniform⟩ := huprid
  unfold DirectLabelAdjacentPhaseVarianceWithExactRemainder
  change directAdjacentVariance chain k ell R <
    exactRemainderMargin chain k ell R delta
  rw [directAdjacentVariance_eq_empiricalDefectSum chain k ell R hshift]
  calc
    (∑ u ∈ terminalShell R, ∑ j ∈ range ell,
        triangularWeight R u *
          ((incomingShift chain k : ℝ) *
            ‖finiteEmpiricalInvarianceDefect
              (chain.nodeCoefficient k) (incomingShift chain k)
                (directFrequency ell u j)‖) ^ 2) ≤
        ∑ u ∈ terminalShell R, ∑ _j ∈ range ell,
          triangularWeight R u * eta ^ 2 := by
      apply sum_le_sum
      intro u hu
      apply sum_le_sum
      intro j hj
      have hpoint := huniform u hu j hj
      have hpointNonneg : 0 ≤ (incomingShift chain k : ℝ) *
          ‖finiteEmpiricalInvarianceDefect
            (chain.nodeCoefficient k) (incomingShift chain k)
              (directFrequency ell u j)‖ := by positivity
      have hsquare : ((incomingShift chain k : ℝ) *
          ‖finiteEmpiricalInvarianceDefect
            (chain.nodeCoefficient k) (incomingShift chain k)
              (directFrequency ell u j)‖) ^ 2 ≤ eta ^ 2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hsquare
        (triangularWeight_nonneg_of_mem_terminalShell hR hu)
    _ = directTerminalMass ell R * eta ^ 2 := by
      unfold directTerminalMass
      simp_rw [← Finset.sum_mul]
    _ < exactRemainderMargin chain k ell R delta := hbudget

/-- Qualified UPRID reaches the literal strict T61 Fejer threshold. -/
theorem t61QualifiedUPRID_implies_literal_T61_threshold
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (k : Fin d) (ell R : ℕ) (delta : ℝ)
    (hR : 1 ≤ R) (hshift : 1 ≤ incomingShift chain k)
    (huprid : T61QualifiedUPRID chain k ell R delta) :
    (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) <
      ∑ j ∈ range ell, fejerKernel (R - 1)
        (chain.nodeCoefficient (k.val + 1) *
          ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) := by
  exact directLabelAdjacentPhaseVariance_implies_fejer_threshold
    chain k ell R delta hR
      (t61QualifiedUPRID_implies_literal_T61_premise
        chain k ell R delta hR hshift huprid)

/-! ## Exact Walsh/cylinder-collision identity -/

/-- The digitwise base-10 Walsh group at word length `m`. -/
abbrev WalshWord (m : ℕ) := Fin m → ZMod 10

/-- The actual length-`m` word beginning at the `i`th pi digit, embedded
digitwise in the Walsh group. -/
def piWalshWord (m N : ℕ) (i : Fin N) : WalshWord m :=
  fun r => ((Theory.PiDigits.piDigit (i.val + r.val)).val : ZMod 10)

/-- Occupancy of one actual pi word among starts `0,...,N-1`. -/
def piWalshOccupancy (m N : ℕ) (w : WalshWord m) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter fun i => piWalshWord m N i = w).card

/-- Empirical word probability, with the literal `1/N` normalization. -/
def piWalshProbability (m N : ℕ) (w : WalshWord m) : ℝ :=
  (piWalshOccupancy m N w : ℝ) / (N : ℝ)

/-- Unnormalized digitwise Walsh coefficient of the empirical word law. -/
def piWalshCoefficient (m N : ℕ) (psi : AddChar (WalshWord m) ℂ) : ℂ :=
  finiteFourier (piWalshProbability m N) psi

theorem sum_piWalshProbability (m N : ℕ) (hN : 1 ≤ N) :
    ∑ w : WalshWord m, piWalshProbability m N w = 1 := by
  classical
  have hpartition : N = ∑ w : WalshWord m, piWalshOccupancy m N w := by
    simpa [piWalshOccupancy] using Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset (WalshWord m)))
      (f := piWalshWord m N) (by simp)
  unfold piWalshProbability
  rw [← Finset.sum_div]
  have hpartitionR : (N : ℝ) =
      ∑ w : WalshWord m, (piWalshOccupancy m N w : ℝ) := by
    exact_mod_cast hpartition
  rw [← hpartitionR]
  exact div_self (by exact_mod_cast (Nat.ne_zero_of_lt hN))

/-- Word equality in the Walsh group is exactly T7's half-open cylinder-code
equality for the actual pi orbit. -/
theorem piWalshWord_eq_iff_piCylinderCode_eq
    (m N : ℕ) (i j : Fin N) :
    piWalshWord m N i = piWalshWord m N j ↔
      piCylinderCode m i = piCylinderCode m j := by
  rw [piCylinderCode_eq_iff_factorAt_eq]
  constructor
  · intro hword
    apply Subtype.ext
    funext r
    have hr := congrFun hword r
    have hval : (Theory.PiDigits.piDigit (i.val + r.val)).val =
        (Theory.PiDigits.piDigit (j.val + r.val)).val := by
      change ((Theory.PiDigits.piDigit (i.val + r.val)).val : ZMod 10) =
        ((Theory.PiDigits.piDigit (j.val + r.val)).val : ZMod 10) at hr
      have hv := congrArg ZMod.val hr
      rw [ZMod.val_natCast_of_lt
          (Theory.PiDigits.piDigit (i.val + r.val)).isLt,
        ZMod.val_natCast_of_lt
          (Theory.PiDigits.piDigit (j.val + r.val)).isLt] at hv
      exact hv
    simpa [factorAt, blockAt, piDecimalStream,
      Theory.PiDigits.T20.decimalDigit_pi] using
        Fin.ext hval
  · intro hfactor
    funext r
    have hr := congrFun (congrArg Subtype.val hfactor) r
    have hdigit : Theory.PiDigits.piDigit (i.val + r.val) =
        Theory.PiDigits.piDigit (j.val + r.val) := by
      simpa [factorAt, blockAt, piDecimalStream,
        Theory.PiDigits.T20.decimalDigit_pi] using hr
    simp only [piWalshWord]
    rw [hdigit]

/-- The unnormalized pi Walsh occupancies count exactly the ordered,
diagonal-inclusive equal-cylinder pairs. -/
theorem sum_sq_piWalshOccupancy_eq_piCylinderCollisionEnergy (m N : ℕ) :
    (∑ w : WalshWord m, piWalshOccupancy m N w ^ 2) =
      piCylinderCollisionEnergy m N := by
  classical
  let S := piCylinderEqualPairs m N
  have hpartition : S.card =
      ∑ w : WalshWord m,
        (S.filter fun ij => piWalshWord m N ij.1 = w).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (WalshWord m)))
      (f := fun ij => piWalshWord m N ij.1) (by simp)
  rw [piCylinderCollisionEnergy_eq_equalPairs_card, hpartition]
  apply Finset.sum_congr rfl
  intro w hw
  rw [pow_two]
  unfold piWalshOccupancy
  rw [← Finset.card_product]
  apply congrArg Finset.card
  ext ij
  simp only [Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and, S, piCylinderEqualPairs]
  constructor
  · rintro ⟨hi, hj⟩
    exact ⟨(piWalshWord_eq_iff_piCylinderCode_eq m N ij.1 ij.2).mp
      (hi.trans hj.symm), hi⟩
  · rintro ⟨hij, hi⟩
    have hword := (piWalshWord_eq_iff_piCylinderCode_eq m N ij.1 ij.2).mpr hij
    exact ⟨hi, hword.symm.trans hi⟩

/-- Squared empirical Walsh-word probabilities are exactly T7's normalized
ordered, diagonal-inclusive half-open cylinder collision energy. -/
theorem sum_sq_piWalshProbability_eq_normalizedCylinderEnergy
    (m N : ℕ) (hN : 1 ≤ N) :
    ∑ w : WalshWord m, piWalshProbability m N w ^ 2 =
      normalizedPiCylinderCollisionEnergy m N := by
  have _hN := hN
  unfold piWalshProbability normalizedPiCylinderCollisionEnergy
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  have henergyR :
      (∑ w : WalshWord m, (piWalshOccupancy m N w : ℝ) ^ 2) =
        (piCylinderCollisionEnergy m N : ℝ) := by
    exact_mod_cast sum_sq_piWalshOccupancy_eq_piCylinderCollisionEnergy m N
  rw [henergyR]

/-- Exact centered Walsh Parseval identity. The middle term is T7's actual
half-open cylinder energy; the right side removes only the trivial character.
Ordered pairs and all diagonal pairs remain present through T7's normalization. -/
theorem walsh_centeredEnergy_eq_cylinderCollision_eq_nontrivial
    (m N : ℕ) (hN : 1 ≤ N) :
    (10 ^ m : ℝ) *
        (∑ w : WalshWord m,
          (piWalshProbability m N w - (10 ^ m : ℝ)⁻¹) ^ 2) =
      (10 ^ m : ℝ) *
        (normalizedPiCylinderCollisionEnergy m N - (10 ^ m : ℝ)⁻¹) ∧
    (10 ^ m : ℝ) *
        (normalizedPiCylinderCollisionEnergy m N - (10 ^ m : ℝ)⁻¹) =
      ∑ psi ∈ (Finset.univ : Finset (AddChar (WalshWord m) ℂ)).erase 0,
        ‖piWalshCoefficient m N psi‖ ^ 2 := by
  classical
  let p : WalshWord m → ℝ := piWalshProbability m N
  let q : ℝ := (10 ^ m : ℝ)
  have hmass : ∑ w : WalshWord m, p w = 1 :=
    sum_piWalshProbability m N hN
  have hcollision : ∑ w : WalshWord m, p w ^ 2 =
      normalizedPiCylinderCollisionEnergy m N :=
    sum_sq_piWalshProbability_eq_normalizedCylinderEnergy m N hN
  have hcard : Fintype.card (WalshWord m) = 10 ^ m := by
    simp [WalshWord]
  have hqpos : 0 < q := by positivity
  have hqne : q ≠ 0 := hqpos.ne'
  have hcross : (∑ w : WalshWord m, 2 * p w * q⁻¹) =
      2 * (∑ w : WalshWord m, p w) * q⁻¹ := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hconst : (∑ _w : WalshWord m, q⁻¹ ^ 2) =
      q * q⁻¹ ^ 2 := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [hcard]
    norm_num [q]
  have hcenter : (∑ w : WalshWord m, (p w - q⁻¹) ^ 2) =
      (∑ w : WalshWord m, p w ^ 2) - q⁻¹ := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hconst, hmass]
    field_simp
    ring
  constructor
  · change q * (∑ w : WalshWord m, (p w - q⁻¹) ^ 2) =
      q * (normalizedPiCylinderCollisionEnergy m N - q⁻¹)
    rw [hcenter, hcollision]
  · let energy : AddChar (WalshWord m) ℂ → ℝ := fun psi =>
      ‖piWalshCoefficient m N psi‖ ^ 2
    have hparseval : (∑ psi : AddChar (WalshWord m) ℂ, energy psi) =
        q * ∑ w : WalshWord m, p w ^ 2 := by
      dsimp only [energy, piWalshCoefficient, p]
      rw [finiteFourier_parseval]
      rw [hcard]
      norm_num [q, p]
    have hzero : energy 0 = 1 := by
      dsimp only [energy, piWalshCoefficient, p]
      rw [finiteFourier_zero_of_mass_one _ hmass]
      norm_num
    have hsplit :
        (∑ psi ∈ (Finset.univ : Finset (AddChar (WalshWord m) ℂ)).erase 0,
          energy psi) + 1 = ∑ psi : AddChar (WalshWord m) ℂ, energy psi := by
      rw [← hzero]
      exact Finset.sum_erase_add Finset.univ energy (mem_univ 0)
    change q * (normalizedPiCylinderCollisionEnergy m N - q⁻¹) =
      ∑ psi ∈ (Finset.univ : Finset (AddChar (WalshWord m) ℂ)).erase 0,
        energy psi
    rw [← hcollision]
    have hqinv : q * q⁻¹ = 1 := mul_inv_cancel₀ hqne
    linarith

/-! ## Abstract-array separators (not orbit witnesses) -/

/-- An unconstrained complex array on the exact positive cutoff `1,...,H`.
No empirical, measure-theoretic, invariance, or realizability condition is part
of this type. -/
abbrev AbstractFourierCutoffArray (H : ℕ) :=
  {u : ℕ // u ∈ Icc 1 H} → ℂ

/-- The abstract array supported only at the top frequency `H`. -/
def abstractTopRaySpike (H : ℕ) : AbstractFourierCutoffArray H :=
  fun u => if u.val = H then 1 else 0

def cutoffLabelOfTerminal {H u : ℕ} (hu : u ∈ terminalShell (H + 1)) :
    {v : ℕ // v ∈ Icc 1 H} :=
  ⟨u, by
    rw [terminalShell_succ_eq] at hu
    simp only [mem_Ioc, mem_Icc] at hu ⊢
    omega⟩

@[simp] theorem cutoffLabelOfTerminal_val {H u : ℕ}
    (hu : u ∈ terminalShell (H + 1)) :
    (cutoffLabelOfTerminal (H := H) (u := u) hu).val = u := rfl

/-- Unweighted mean square on the literal terminal shell `(H/10,H]`. -/
def abstractTerminalMeanSquare
    (H : ℕ) (a : AbstractFourierCutoffArray H) : ℝ :=
  (∑ u : ↥(terminalShell (H + 1)),
      ‖a (cutoffLabelOfTerminal (H := H) (u := u.val) u.property)‖ ^ 2) /
    ((terminalShell (H + 1)).card : ℝ)

/-- Triangularly weighted mean square on the exact full positive cutoff. -/
def abstractTriangularMeanSquare
    (H : ℕ) (a : AbstractFourierCutoffArray H) : ℝ :=
  (∑ u : ↥(Icc 1 H),
      triangularWeight (H + 1) u.val * ‖a u‖ ^ 2) /
    (∑ u : ↥(Icc 1 H), triangularWeight (H + 1) u.val)

theorem top_mem_terminalShell_succ (H : ℕ) (hH : 1 ≤ H) :
    H ∈ terminalShell (H + 1) := by
  rw [terminalShell_succ_eq]
  simp only [mem_Ioc, le_rfl, and_true]
  exact Nat.div_lt_self (by omega) (by norm_num)

theorem terminalShell_succ_card (H : ℕ) :
    (terminalShell (H + 1)).card = H - H / 10 := by
  rw [terminalShell_succ_eq]
  simp

/-- Exact total triangular mass on the full positive cutoff. -/
theorem positiveCutoff_triangularWeight_sum (H : ℕ) :
    (∑ u : ↥(Icc 1 H), triangularWeight (H + 1) u.val) =
      (H : ℝ) / 2 := by
  classical
  simp only [Finset.univ_eq_attach]
  rw [Finset.sum_attach]
  have hreindex :
      (∑ k ∈ range H, triangularWeight (H + 1) (k + 1)) =
        ∑ u ∈ Icc 1 H, triangularWeight (H + 1) u := by
    apply Finset.sum_bij (fun k _hk => k + 1)
    · intro k hk
      simp only [mem_range] at hk
      simp only [mem_Icc]
      omega
    · intro a ha b hb hab
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      refine ⟨u - 1, ?_, ?_⟩
      · simp only [mem_range]
        omega
      · omega
    · intro k hk
      rfl
  rw [← hreindex]
  unfold triangularWeight
  rw [Finset.sum_sub_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hsumTwoNat :
      (∑ k ∈ range H, (k + 1)) * 2 = H * (H + 1) := by
    clear hreindex
    induction H with
    | zero => simp
    | succ H ih =>
        rw [Finset.sum_range_succ]
        calc
          ((∑ k ∈ range H, (k + 1)) + (H + 1)) * 2 =
              (∑ k ∈ range H, (k + 1)) * 2 + (H + 1) * 2 := by ring
          _ = H * (H + 1) + (H + 1) * 2 := by rw [ih]
          _ = (H + 1) * (H + 1 + 1) := by ring
  have hsumTwoReal :
      (∑ k ∈ range H, ((k + 1 : ℕ) : ℝ)) * 2 =
        (H : ℝ) * (H + 1 : ℝ) := by
    exact_mod_cast hsumTwoNat
  have hden : (H + 1 : ℝ) ≠ 0 := by positivity
  have hfrac :
      (∑ k ∈ range H, ((k + 1 : ℕ) : ℝ) / (H + 1 : ℝ)) =
        (H : ℝ) / 2 := by
    rw [← Finset.sum_div]
    field_simp
    nlinarith
  norm_num only [Nat.cast_add, Nat.cast_one] at hfrac ⊢
  rw [hfrac]
  ring

/-- Sparse-ray separator on the exact abstract shell: the supremum is one but
the unweighted shell mean square is exactly the reciprocal shell cardinality.
This theorem has no actual-orbit witness. -/
theorem abstract_sparseRay_separator_exact
    (H : ℕ) (hH : 1 ≤ H) (hprimitive : ¬ 10 ∣ H) :
    (∃ u : ↥(terminalShell (H + 1)),
      ‖abstractTopRaySpike H
        (cutoffLabelOfTerminal (H := H) (u := u.val) u.property)‖ = 1) ∧
    abstractTerminalMeanSquare H (abstractTopRaySpike H) =
      1 / ((H - H / 10 : ℕ) : ℝ) := by
  classical
  have _ := hprimitive
  let top : ↥(terminalShell (H + 1)) :=
    ⟨H, top_mem_terminalShell_succ H hH⟩
  have htop : ‖abstractTopRaySpike H
      (cutoffLabelOfTerminal (H := H) (u := top.val) top.property)‖ = 1 := by
    simp [top, abstractTopRaySpike]
  refine ⟨⟨top, htop⟩, ?_⟩
  unfold abstractTerminalMeanSquare
  rw [terminalShell_succ_card]
  have hsum : (∑ u : ↥(terminalShell (H + 1)),
      ‖abstractTopRaySpike H
        (cutoffLabelOfTerminal (H := H) (u := u.val) u.property)‖ ^ 2) = 1 := by
    rw [Fintype.sum_eq_single top]
    · rw [htop]
      norm_num
    · intro u hu
      have hval : u.val ≠ H := by
        intro huv
        apply hu
        apply Subtype.ext
        simpa [top] using huv
      simp [abstractTopRaySpike, hval]
  rw [hsum]

/-- Bulk-shell separator on the exact abstract positive cutoff: the same unit
top ray has normalized triangular mean square `2/(H*(H+1))`. This theorem has
no actual-orbit witness. -/
theorem abstract_bulkShell_separator_exact
    (H : ℕ) (hH : 1 ≤ H) (hprimitive : ¬ 10 ∣ H) :
    (∃ u : ↥(terminalShell (H + 1)),
      ‖abstractTopRaySpike H
        (cutoffLabelOfTerminal (H := H) (u := u.val) u.property)‖ = 1) ∧
    abstractTriangularMeanSquare H (abstractTopRaySpike H) =
      2 / ((H : ℝ) * (H + 1 : ℝ)) := by
  classical
  let top : ↥(Icc 1 H) := ⟨H, by simp [hH]⟩
  have hexists := (abstract_sparseRay_separator_exact H hH hprimitive).1
  refine ⟨hexists, ?_⟩
  unfold abstractTriangularMeanSquare
  rw [positiveCutoff_triangularWeight_sum]
  have hnum : (∑ u : ↥(Icc 1 H),
      triangularWeight (H + 1) u.val *
        ‖abstractTopRaySpike H u‖ ^ 2) = 1 / (H + 1 : ℝ) := by
    rw [Fintype.sum_eq_single top]
    · simp [top, abstractTopRaySpike, triangularWeight]
      field_simp
      ring
    · intro u hu
      have hval : u.val ≠ H := by
        intro huv
        apply hu
        apply Subtype.ext
        simpa [top] using huv
      simp [abstractTopRaySpike, hval]
  rw [hnum]
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  field_simp

end TerminalRayStrengthT67
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.finiteEmpiricalFourier_eq_circleEmpiricalMean
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.length_mul_finiteEmpiricalInvarianceDefect
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.norm_endpointDifference_eq_length_mul_defect
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.mem_primitiveDecimalRayShell_iff
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.terminalShell_succ_eq
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.directAdjacentVariance_eq_empiricalDefectSum
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.t61QualifiedUPRID_implies_literal_T61_premise
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.t61QualifiedUPRID_implies_literal_T61_threshold
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.piWalshWord_eq_iff_piCylinderCode_eq
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.sum_sq_piWalshProbability_eq_normalizedCylinderEnergy
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.walsh_centeredEnergy_eq_cylinderCollision_eq_nontrivial
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.positiveCutoff_triangularWeight_sum
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.abstract_sparseRay_separator_exact
#print axioms DecimalFactorComplexity.TerminalRayStrengthT67.abstract_bulkShell_separator_exact
