import TheoryLib.PiLacunaryNearReturnSparsity.T55SignedMultiplierTenPairing
import TheoryLib.PiLacunaryNearReturnSparsity.T61DirectLabelAdjacentPhaseVariance

/-!
# T62: closed decimal valuation expansion and predecessor-depth regrouping

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module derives finite identities from the kernel-checked T55 and T61
interfaces. It does not import the unverified T58 note and makes no covariance,
FSFS, compatibility, fixed-`pi`, C1, or C2 claim.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity
namespace ClosedExpansionPredecessorRegroupingT62

open SignedMultiplierTenPairingT55
open DirectLabelAdjacentPhaseVarianceT61

abbrev phase := Theory.PiDigits.T27.phase

/-- The exponent of the largest power of the composite base ten dividing a
positive integer. The value at zero is irrelevant to the public formulas. -/
def decimalValuation (u : ℕ) : ℕ :=
  padicValNat 10 u

/-- Decimal valuation is bounded by its positive argument. This supplies a
literal finite box for every predecessor-depth label below cutoff `R-1`. -/
theorem decimalValuation_le_self (u : ℕ) : decimalValuation u ≤ u := by
  by_cases hu : u = 0
  · simp [hu, decimalValuation]
  · have hdvd : 10 ^ decimalValuation u ∣ u := by
      exact pow_padicValNat_dvd
    have hpowLe : 10 ^ decimalValuation u ≤ u :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hdvd
    have hindexLePow : ∀ n : ℕ, n ≤ 10 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ]
          have hpowPos : 1 ≤ 10 ^ n := one_le_pow₀ (by norm_num)
          omega
    exact (hindexLePow (decimalValuation u)).trans hpowLe

/-- The contribution arriving from predecessor depth `a`. The signed phase
frequency is displayed as `u / 10^a - u`, including the direct depth `a=0`. -/
def closedOrbitTerm
    (beta : ℝ) (ell R u a : ℕ) : ℂ :=
  (triangularWeight R (u / 10 ^ a) : ℂ) *
    phase (((u / 10 ^ a : ℕ) : ℤ) - (u : ℤ))
      (beta * (10 : ℝ) ^ ell)

/-- One multiplier-ten predecessor step shifts the closed term from depth `a`
to depth `a+1`, retaining the transport phase and its negative sign. -/
theorem transport_mul_closedOrbitTerm
    (beta : ℝ) (ell R q a : ℕ) :
    transportPhase beta ell (q : ℤ) * closedOrbitTerm beta ell R q a =
      closedOrbitTerm beta ell R (10 * q) (a + 1) := by
  have hdiv : (10 * q) / 10 ^ (a + 1) = q / 10 ^ a := by
    rw [pow_succ' (10 : ℕ) a]
    exact Nat.mul_div_mul_left q (10 ^ a) (by norm_num)
  unfold transportPhase closedOrbitTerm
  rw [hdiv]
  rw [show ∀ w z t : ℂ, t * (w * z) = w * (t * z) by
    intro w z t
    ring]
  rw [← Theory.PiDigits.T27.phase_add]
  apply congrArg (fun m : ℤ =>
    (triangularWeight R (q / 10 ^ a) : ℂ) *
      phase m (beta * (10 : ℝ) ^ ell))
  push_cast
  ring

/-- At depth zero the closed term is exactly T55's triangular coefficient. -/
theorem closedOrbitTerm_zero
    (beta : ℝ) (ell R u : ℕ) :
    closedOrbitTerm beta ell R u 0 = (triangularWeight R u : ℂ) := by
  simp [closedOrbitTerm, Theory.PiDigits.T27.phase_zero]

/-- Public closed base-10 valuation expansion of T55's recursive coefficient.
The range is literally `0 ≤ a ≤ nu_10(u)`, represented by
`range (decimalValuation u + 1)`. -/
theorem orbitCoefficient_eq_closed_decimal_expansion
    (beta : ℝ) (ell R u : ℕ) (hu : 1 ≤ u) :
    orbitCoefficient beta ell R u =
      ∑ a ∈ range (decimalValuation u + 1),
        (triangularWeight R (u / 10 ^ a) : ℂ) *
          phase (((u / 10 ^ a : ℕ) : ℤ) - (u : ℤ))
            (beta * (10 : ℝ) ^ ell) := by
  change orbitCoefficient beta ell R u =
    ∑ a ∈ range (decimalValuation u + 1),
      closedOrbitTerm beta ell R u a
  induction u using Nat.strong_induction_on with
  | h u ih =>
      rw [orbitCoefficient_eq_weight_add_predecessor beta ell R u hu]
      unfold predecessorCoefficient
      by_cases hdiv : 10 ∣ u
      · rw [if_pos hdiv]
        let q := u / 10
        have hmul : 10 * q = u := Nat.mul_div_cancel' hdiv
        have hqPos : 1 ≤ q := by
          by_contra hq
          have : q = 0 := by omega
          rw [this, mul_zero] at hmul
          omega
        have hqLt : q < u := by
          exact Nat.div_lt_self (by omega) (by norm_num)
        have hclosed := ih q hqLt hqPos
        have hval : decimalValuation u = decimalValuation q + 1 := by
          unfold decimalValuation
          rw [← hmul]
          exact padicValNat_base_mul (by norm_num) (by omega)
        rw [hclosed, hval]
        have hquot : u / 10 = q := rfl
        rw [hquot]
        have hsplit := Finset.sum_range_succ'
          (fun a => closedOrbitTerm beta ell R u a)
          (decimalValuation q + 1)
        rw [hsplit]
        rw [Finset.mul_sum]
        simp_rw [transport_mul_closedOrbitTerm]
        rw [← hmul]
        rw [closedOrbitTerm_zero]
        ring
      · rw [if_neg hdiv]
        have huNe : u ≠ 0 := by omega
        have hval : decimalValuation u = 0 := by
          unfold decimalValuation
          by_contra hne
          have hone : 1 ≤ padicValNat 10 u := by omega
          have hdvd : 10 ^ 1 ∣ u :=
            (Nat.pow_dvd_iff_le_padicValNat (by norm_num) huNe).2 hone
          norm_num at hdvd
          exact hdiv hdvd
        rw [hval]
        simp only [zero_add, sum_range_one]
        rw [closedOrbitTerm_zero]
        ring

/-- A natural-number label carrier. Original order is `(u,(a,j))`; depth-first
order is `(a,(u,j))`. -/
abbrev DepthLabel := ℕ × (ℕ × ℕ)

/-- A predecessor label in T61's original order: terminal frequency `u`,
positive predecessor depth `a`, and block index `j`. -/
def PredecessorLabel (ell R : ℕ) (x : DepthLabel) : Prop :=
  (R - 1) / 10 < x.1 ∧ x.1 ≤ R - 1 ∧
    1 ≤ x.2.1 ∧ x.2.1 ≤ decimalValuation x.1 ∧ x.2.2 < ell

/-- The same labels in depth-first order. Every shell endpoint, valuation
endpoint, block endpoint, and cutoff remains literal. -/
def DepthFirstLabel (ell R : ℕ) (x : DepthLabel) : Prop :=
  1 ≤ x.1 ∧ x.1 ≤ decimalValuation x.2.1 ∧
    (R - 1) / 10 < x.2.1 ∧ x.2.1 ≤ R - 1 ∧ x.2.2 < ell

/-- The common finite ambient box. Both frequency and predecessor depth are
strictly below `R`, while the block index is strictly below `ell`. -/
def predecessorLabelBox (ell R : ℕ) : Finset DepthLabel :=
  (range R).product ((range R).product (range ell))

/-- Original-order predecessor labels inside the explicit finite box. -/
def predecessorLabels (ell R : ℕ) : Finset DepthLabel :=
  by
    classical
    exact (predecessorLabelBox ell R).filter (PredecessorLabel ell R)

/-- Depth-first predecessor labels inside the same explicit finite box. -/
def depthFirstLabels (ell R : ℕ) : Finset DepthLabel :=
  by
    classical
    exact (predecessorLabelBox ell R).filter (DepthFirstLabel ell R)

/-- The explicit finite label bijection `(u,(a,j)) ↦ (a,(u,j))` used to
regroup by predecessor depth. It changes no label and merges no collisions. -/
def predecessorDepthEquiv (ell R : ℕ) :
    {x : DepthLabel // x ∈ predecessorLabels ell R} ≃
      {x : DepthLabel // x ∈ depthFirstLabels ell R} := by
  let swapUA : DepthLabel ≃ DepthLabel :=
    { toFun := fun x => (x.2.1, (x.1, x.2.2))
      invFun := fun x => (x.2.1, (x.1, x.2.2))
      left_inv := by rintro ⟨u, a, j⟩; rfl
      right_inv := by rintro ⟨a, u, j⟩; rfl }
  exact swapUA.subtypeEquiv (fun x => by
    rcases x with ⟨u, a, j⟩
    change (u, (a, j)) ∈ predecessorLabels ell R ↔
      (a, (u, j)) ∈ depthFirstLabels ell R
    simp [predecessorLabels, depthFirstLabels, predecessorLabelBox,
      PredecessorLabel, DepthFirstLabel, and_left_comm, and_comm]
    tauto)

/-- Public pointwise description of the finite bijection. -/
theorem predecessorDepthEquiv_apply
    (ell R : ℕ)
    (x : {x : DepthLabel // x ∈ predecessorLabels ell R}) :
    (predecessorDepthEquiv ell R x).val =
      (x.val.2.1, (x.val.1, x.val.2.2)) := by
  rfl

/-- Public bijectivity theorem for the complete finite label permutation. -/
theorem predecessorDepthEquiv_bijective (ell R : ℕ) :
    Function.Bijective (predecessorDepthEquiv ell R) :=
  (predecessorDepthEquiv ell R).bijective

/-- The fully expanded predecessor summand. Its phase displays the minus sign,
the decimal predecessor `u/10^a`, and the Fourier block index `j`. -/
def predecessorDepthTerm
    (beta : ℝ) (ell R u a j : ℕ) : ℂ :=
  (triangularWeight R (u / 10 ^ a) : ℂ) *
    phase (((u / 10 ^ a : ℕ) : ℤ) * (10 : ℤ) ^ ell -
      (u : ℤ) * (10 : ℤ) ^ j) beta

/-- Multiplying one closed coefficient term by T55's labeled block phase gives
the displayed predecessor-depth phase, with no norm or absolute-value step. -/
theorem closedOrbitTerm_mul_labeledPhase
    (beta : ℝ) (ell R u a j : ℕ) :
    closedOrbitTerm beta ell R u a *
        labeledPhase beta ell (u : ℤ) j =
      predecessorDepthTerm beta ell R u a j := by
  unfold closedOrbitTerm labeledPhase predecessorDepthTerm phase
    SignedMultiplierTenPairingT55.phase Theory.PiDigits.T27.phase
  rw [show ∀ w z t : ℂ, (w * z) * t = w * (z * t) by
    intro w z t
    ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Reindexing `0 ≤ k < n` by `a=k+1` gives the literal positive interval
`1 ≤ a ≤ n`. This helper exposes the endpoint conversion used below. -/
theorem sum_range_succ_eq_sum_Icc_one
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    (∑ k ∈ range n, f (k + 1)) = ∑ a ∈ Icc 1 n, f a := by
  apply Finset.sum_bij (fun k _hk => k + 1)
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro a ha
    simp only [mem_Icc] at ha
    refine ⟨a - 1, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro k hk
    rfl

/-- T55's predecessor coefficient is exactly the positive-depth part of the
closed decimal expansion. The range `1 ≤ a ≤ nu_10(u)` is literal. -/
theorem predecessorCoefficient_eq_positive_depths
    (beta : ℝ) (ell R u : ℕ) (hu : 1 ≤ u) :
    predecessorCoefficient beta ell R u =
      ∑ a ∈ Icc 1 (decimalValuation u),
        closedOrbitTerm beta ell R u a := by
  have hrec := orbitCoefficient_eq_weight_add_predecessor beta ell R u hu
  have hexp := orbitCoefficient_eq_closed_decimal_expansion beta ell R u hu
  change orbitCoefficient beta ell R u =
    ∑ a ∈ range (decimalValuation u + 1),
      closedOrbitTerm beta ell R u a at hexp
  rw [Finset.sum_range_succ'] at hexp
  rw [sum_range_succ_eq_sum_Icc_one, closedOrbitTerm_zero] at hexp
  linear_combination hexp - hrec

/-- T61's exact predecessor remainder expanded in its original `(u,a,j)`
order. The terminal shell, positive valuation depths, block range, and cutoff
`R-1` all occur in the theorem type. -/
theorem predecessorRemainder_eq_frequency_depth_block_sum
    (beta : ℝ) (ell R : ℕ) :
    predecessorRemainder beta ell R =
      ∑ u ∈ Ioc ((R - 1) / 10) (R - 1),
        ∑ a ∈ Icc 1 (decimalValuation u),
          ∑ j ∈ range ell,
            (triangularWeight R (u / 10 ^ a) : ℂ) *
              phase (((u / 10 ^ a : ℕ) : ℤ) * (10 : ℤ) ^ ell -
                (u : ℤ) * (10 : ℤ) ^ j) beta := by
  change predecessorRemainder beta ell R =
    ∑ u ∈ Ioc ((R - 1) / 10) (R - 1),
      ∑ a ∈ Icc 1 (decimalValuation u),
        ∑ j ∈ range ell, predecessorDepthTerm beta ell R u a j
  rw [predecessorRemainder_eq_labeled_sum]
  apply sum_congr rfl
  intro u huShell
  have hu : 1 ≤ u := by
    simp only [mem_Ioc] at huShell
    omega
  rw [predecessorCoefficient_eq_positive_depths beta ell R u hu]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro j hj
  exact closedOrbitTerm_mul_labeledPhase beta ell R u a j

/-- Flattening the three literal finite ranges gives exactly the finite source
label subtype used by `predecessorDepthEquiv`. -/
theorem predecessorLabel_sum_eq_nested
    {A : Type*} [AddCommMonoid A]
    (f : DepthLabel → A) (ell R : ℕ) :
    (∑ x : {x : DepthLabel // x ∈ predecessorLabels ell R}, f x.val) =
      ∑ u ∈ Ioc ((R - 1) / 10) (R - 1),
        ∑ a ∈ Icc 1 (decimalValuation u),
          ∑ j ∈ range ell, f (u, (a, j)) := by
  classical
  simp only [Finset.univ_eq_attach]
  rw [Finset.sum_attach]
  calc
    (∑ x ∈ predecessorLabels ell R, f x) =
        ∑ u ∈ Ioc ((R - 1) / 10) (R - 1),
          ∑ aj ∈ (Icc 1 (decimalValuation u)).product (range ell),
            f (u, aj) := by
      apply Finset.sum_finset_product
      intro p
      rcases p with ⟨u, a, j⟩
      simp only [predecessorLabels, predecessorLabelBox, mem_filter,
        PredecessorLabel, mem_Ioc]
      constructor
      · rintro ⟨hbox, hlo, hup, ha1, haval, hj⟩
        refine ⟨⟨hlo, hup⟩, ?_⟩
        simpa using ⟨⟨ha1, haval⟩, hj⟩
      · rintro ⟨⟨hlo, hup⟩, haj⟩
        have haj' : (1 ≤ a ∧ a ≤ decimalValuation u) ∧ j < ell := by
          simpa using haj
        have hval := decimalValuation_le_self u
        have huR : u < R := by omega
        have haR : a < R := by omega
        refine ⟨?_, hlo, hup, haj'.1.1, haj'.1.2, haj'.2⟩
        simpa using ⟨huR, haR, haj'.2⟩
    _ = ∑ u ∈ Ioc ((R - 1) / 10) (R - 1),
          ∑ a ∈ Icc 1 (decimalValuation u),
            ∑ j ∈ range ell, f (u, (a, j)) := by
      apply sum_congr rfl
      intro u hu
      exact Finset.sum_product (Icc 1 (decimalValuation u)) (range ell)
        (fun aj => f (u, aj))

/-- The depth-first finite subtype expands to a literal outer depth interval,
the original terminal shell, the valuation membership test, and `range ell`. -/
theorem depthFirstLabel_sum_eq_nested
    {A : Type*} [AddCommMonoid A]
    (f : DepthLabel → A) (ell R : ℕ) :
    (∑ x : {x : DepthLabel // x ∈ depthFirstLabels ell R}, f x.val) =
      ∑ a ∈ Icc 1 (R - 1),
        ∑ u ∈ (Ioc ((R - 1) / 10) (R - 1)).filter
            (fun u => a ≤ decimalValuation u),
          ∑ j ∈ range ell, f (a, (u, j)) := by
  classical
  simp only [Finset.univ_eq_attach]
  rw [Finset.sum_attach]
  calc
    (∑ x ∈ depthFirstLabels ell R, f x) =
        ∑ a ∈ Icc 1 (R - 1),
          ∑ uj ∈ ((Ioc ((R - 1) / 10) (R - 1)).filter
              (fun u => a ≤ decimalValuation u)).product (range ell),
            f (a, uj) := by
      apply Finset.sum_finset_product
      intro p
      rcases p with ⟨a, u, j⟩
      simp only [depthFirstLabels, predecessorLabelBox, mem_filter,
        DepthFirstLabel, mem_Icc]
      constructor
      · rintro ⟨hbox, ha1, haval, hlo, hup, hj⟩
        have hbox' : a < R ∧ u < R ∧ j < ell := by
          simpa using hbox
        refine ⟨⟨ha1, ?_⟩, ?_⟩
        · omega
        · apply Finset.mem_product.mpr
          refine ⟨Finset.mem_filter.mpr ?_, Finset.mem_range.mpr hj⟩
          exact ⟨Finset.mem_Ioc.mpr ⟨hlo, hup⟩, haval⟩
      · rintro ⟨⟨ha1, haR⟩, huj⟩
        rcases Finset.mem_product.mp huj with ⟨huFiltered, hjRange⟩
        rcases Finset.mem_filter.mp huFiltered with ⟨huShell, haval⟩
        have hus := Finset.mem_Ioc.mp huShell
        have hj := Finset.mem_range.mp hjRange
        have huR : u < R := by omega
        have haLtR : a < R := by omega
        refine ⟨?_, ha1, haval, hus.1, hus.2, hj⟩
        simpa using ⟨haLtR, huR, hj⟩
    _ = ∑ a ∈ Icc 1 (R - 1),
          ∑ u ∈ (Ioc ((R - 1) / 10) (R - 1)).filter
              (fun u => a ≤ decimalValuation u),
            ∑ j ∈ range ell, f (a, (u, j)) := by
      apply sum_congr rfl
      intro a ha
      exact Finset.sum_product
        ((Ioc ((R - 1) / 10) (R - 1)).filter
          (fun u => a ≤ decimalValuation u))
        (range ell) (fun uj => f (a, uj))

/-- Depth-first regrouping of T61's exact predecessor remainder. The explicit
predicate keeps the depth range, terminal-shell endpoints, multiplicity, block
endpoint, and Fourier cutoff visible while putting `a` before `u`. -/
theorem predecessorRemainder_eq_predecessorDepth_regrouping
    (beta : ℝ) (ell R : ℕ) :
    predecessorRemainder beta ell R =
      ∑ x : {x : DepthLabel // x ∈ depthFirstLabels ell R},
        predecessorDepthTerm beta ell R x.val.2.1 x.val.1 x.val.2.2 := by
  rw [predecessorRemainder_eq_frequency_depth_block_sum]
  change (∑ u ∈ Ioc ((R - 1) / 10) (R - 1),
      ∑ a ∈ Icc 1 (decimalValuation u),
        ∑ j ∈ range ell, predecessorDepthTerm beta ell R u a j) = _
  rw [← predecessorLabel_sum_eq_nested
    (fun x => predecessorDepthTerm beta ell R x.1 x.2.1 x.2.2)]
  exact Fintype.sum_equiv (predecessorDepthEquiv ell R)
    (fun x => predecessorDepthTerm beta ell R
      x.val.1 x.val.2.1 x.val.2.2)
    (fun x => predecessorDepthTerm beta ell R
      x.val.2.1 x.val.1 x.val.2.2)
    (fun x => by
      change predecessorDepthTerm beta ell R
          x.val.1 x.val.2.1 x.val.2.2 =
        predecessorDepthTerm beta ell R
          (predecessorDepthEquiv ell R x).val.2.1
          (predecessorDepthEquiv ell R x).val.1
          (predecessorDepthEquiv ell R x).val.2.2
      rw [predecessorDepthEquiv_apply])

/-- Public depth-structured form with every endpoint in the theorem type.
Depth satisfies `1 ≤ a ≤ R-1`; frequency remains in the half-open terminal
shell; the filter says exactly `a ≤ nu_10(u)`; and `0 ≤ j < ell` is literal. -/
theorem predecessorRemainder_eq_literal_depth_regrouping
    (beta : ℝ) (ell R : ℕ) :
    predecessorRemainder beta ell R =
      ∑ a ∈ Icc 1 (R - 1),
        ∑ u ∈ (Ioc ((R - 1) / 10) (R - 1)).filter
            (fun u => a ≤ decimalValuation u),
          ∑ j ∈ range ell,
            (triangularWeight R (u / 10 ^ a) : ℂ) *
              phase (((u / 10 ^ a : ℕ) : ℤ) * (10 : ℤ) ^ ell -
                (u : ℤ) * (10 : ℤ) ^ j) beta := by
  rw [predecessorRemainder_eq_predecessorDepth_regrouping]
  change (∑ x : {x : DepthLabel // x ∈ depthFirstLabels ell R},
      predecessorDepthTerm beta ell R x.val.2.1 x.val.1 x.val.2.2) =
    ∑ a ∈ Icc 1 (R - 1),
      ∑ u ∈ (Ioc ((R - 1) / 10) (R - 1)).filter
          (fun u => a ≤ decimalValuation u),
        ∑ j ∈ range ell, predecessorDepthTerm beta ell R u a j
  rw [depthFirstLabel_sum_eq_nested
    (fun x => predecessorDepthTerm beta ell R x.2.1 x.1 x.2.2)]

end ClosedExpansionPredecessorRegroupingT62
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.ClosedExpansionPredecessorRegroupingT62.orbitCoefficient_eq_closed_decimal_expansion
#print axioms DecimalFactorComplexity.ClosedExpansionPredecessorRegroupingT62.predecessorDepthEquiv_apply
#print axioms DecimalFactorComplexity.ClosedExpansionPredecessorRegroupingT62.predecessorDepthEquiv_bijective
#print axioms DecimalFactorComplexity.ClosedExpansionPredecessorRegroupingT62.predecessorCoefficient_eq_positive_depths
#print axioms DecimalFactorComplexity.ClosedExpansionPredecessorRegroupingT62.predecessorRemainder_eq_frequency_depth_block_sum
#print axioms DecimalFactorComplexity.ClosedExpansionPredecessorRegroupingT62.predecessorRemainder_eq_predecessorDepth_regrouping
#print axioms DecimalFactorComplexity.ClosedExpansionPredecessorRegroupingT62.predecessorRemainder_eq_literal_depth_regrouping
