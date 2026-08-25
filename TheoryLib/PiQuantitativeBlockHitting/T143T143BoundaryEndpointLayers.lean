import TheoryLib.PiQuantitativeBlockHitting.T139T139PrimitiveRayBoundaryConsumer
import TheoryLib.PiQuantitativeBlockHitting.T142T142BoundaryCoefficientAbel

/-!
# T143: exact valuation-layer decomposition of the T139 endpoint

This module only reindexes the two literal endpoint blocks by decimal
valuation layers.  It contains no endpoint estimate or interval consumer.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.BoundaryEndpointLayers

open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer

abbrev phase := Theory.PiDigits.T27.phase
abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- The coefficient polynomial on the positive frequencies divisible by
`10^s`, written with the quotient frequency as index. -/
def boundaryLayerPolynomial (q s : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 ((2 * q - 1) / 10 ^ s),
    (positiveBoundaryCoefficient q (10 ^ s * m) : ℂ) * phase (m : ℤ) t

/-- The literal initial endpoint half in T139. -/
def initialBoundaryEndpoint (q A : ℕ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q,
    centeredBoundaryTerm q A h *
      Theory.PiDigits.T27.exponentialSum piOrbit (tenValuation h)
        (tenPrimitivePart h : ℤ)

/-- The literal terminal endpoint half in T139. -/
def terminalBoundaryEndpoint (q A N : ℕ) : ℂ :=
  ∑ h ∈ positiveBoundarySupport q,
    centeredBoundaryTerm q A h *
      ∑ j ∈ range (tenValuation h),
        phase (tenPrimitivePart h : ℤ) (piOrbit (N + j))

/-- T139's endpoint is literally terminal minus initial. -/
theorem primitiveBoundaryEndpoint_eq_terminal_sub_initial (q A N : ℕ) :
    primitiveBoundaryEndpoint q A N =
      terminalBoundaryEndpoint q A N - initialBoundaryEndpoint q A := by
  unfold primitiveBoundaryEndpoint primitiveShiftEndpointBlock
    terminalBoundaryEndpoint initialBoundaryEndpoint
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro h hh
  ring

private def endpointIndexSet (q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (positiveBoundarySupport q).sigma fun h => range (tenValuation h)

private def layerIndexSet (k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 k).sigma fun s => Icc 1 ((2 * 10 ^ k - 1) / 10 ^ s)

private def endpointToLayer (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  ⟨tenValuation x.1 - x.2, 10 ^ x.2 * tenPrimitivePart x.1⟩

private def layerToEndpoint (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  ⟨10 ^ x.1 * x.2, tenValuation x.2⟩

private lemma ten_pow_mul_decomposition (s m : ℕ) (hm : 0 < m) :
    tenValuation (10 ^ s * m) = s + tenValuation m ∧
      tenPrimitivePart (10 ^ s * m) = tenPrimitivePart m := by
  have hmred := ten_reduction m
  have hprim := ten_not_dvd_primitivePart hm
  have hpart0 : tenPrimitivePart m ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmred
    omega
  have heq : 10 ^ (s + tenValuation m) * tenPrimitivePart m = 10 ^ s * m := by
    rw [pow_add, mul_assoc, hmred]
  have hspec := Nat.maxPowDvdDiv_of_pow_mul_eq
    (p := 10) (n := 10 ^ s * m) (k := s + tenValuation m)
    (l := tenPrimitivePart m) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hm.ne')
    heq hprim
  have hfst : tenValuation (10 ^ s * m) = s + tenValuation m := by
    change (Nat.maxPowDvdDiv 10 (10 ^ s * m)).1 = s + tenValuation m
    rw [hspec]
  have hsnd : tenPrimitivePart (10 ^ s * m) = tenPrimitivePart m := by
    change (Nat.maxPowDvdDiv 10 (10 ^ s * m)).2 = tenPrimitivePart m
    rw [hspec]
  exact ⟨hfst, hsnd⟩

private lemma tenValuation_le_scale
    (k h : ℕ) (hh0 : 1 ≤ h) (hhsupp : h ≤ 2 * 10 ^ k - 1) :
    tenValuation h ≤ k := by
  have hdvd : 10 ^ tenValuation h ∣ h := pow_padicValNat_dvd
  have hpow : 10 ^ tenValuation h ≤ h := Nat.le_of_dvd (by omega) hdvd
  by_contra hnot
  have hkp : k + 1 ≤ tenValuation h := by omega
  have hpow' : 10 ^ (k + 1) ≤ 10 ^ tenValuation h := Nat.pow_le_pow_right (by omega) hkp
  rw [pow_succ] at hpow'
  have hkpow : 0 < 10 ^ k := pow_pos (by omega) _
  omega

private lemma endpointToLayer_mem
    (k : ℕ) (x : Σ _ : ℕ, ℕ) (hx : x ∈ endpointIndexSet (10 ^ k)) :
    endpointToLayer x ∈ layerIndexSet k := by
  obtain ⟨hh, hj⟩ := mem_sigma.mp hx
  have hh' := (mem_Icc.mp hh)
  have hj' := mem_range.mp hj
  have hval := tenValuation_le_scale k x.1 hh'.1 hh'.2
  have hs0 : 1 ≤ tenValuation x.1 - x.2 := by omega
  have hsk : tenValuation x.1 - x.2 ≤ k := by omega
  have hm0 : 1 ≤ 10 ^ x.2 * tenPrimitivePart x.1 := by
    have hred := ten_reduction x.1
    have hpart0 : 0 < tenPrimitivePart x.1 := by
      by_contra hz
      simp only [not_lt] at hz
      have : tenPrimitivePart x.1 = 0 := Nat.eq_zero_of_le_zero hz
      rw [this, mul_zero] at hred
      omega
    exact Nat.mul_pos (pow_pos (by omega) _) hpart0
  have hfreq :
      10 ^ (tenValuation x.1 - x.2) *
          (10 ^ x.2 * tenPrimitivePart x.1) = x.1 := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hj'), ten_reduction]
  apply mem_sigma.mpr
  refine ⟨mem_Icc.mpr ⟨hs0, hsk⟩, mem_Icc.mpr ⟨hm0, ?_⟩⟩
  apply (Nat.le_div_iff_mul_le (pow_pos (by omega) _)).2
  dsimp [endpointToLayer]
  rw [Nat.mul_comm, hfreq]
  exact hh'.2

private lemma layerToEndpoint_mem
    (k : ℕ) (x : Σ _ : ℕ, ℕ) (hx : x ∈ layerIndexSet k) :
    layerToEndpoint x ∈ endpointIndexSet (10 ^ k) := by
  obtain ⟨hs, hm⟩ := mem_sigma.mp hx
  have hs' := mem_Icc.mp hs
  have hm' := mem_Icc.mp hm
  have hm0 : 0 < x.2 := by omega
  have hdecomp := ten_pow_mul_decomposition x.1 x.2 hm0
  apply mem_sigma.mpr
  refine ⟨?_, mem_range.mpr ?_⟩
  · apply mem_Icc.mpr
    refine ⟨Nat.mul_pos (pow_pos (by omega) _) hm0, ?_⟩
    dsimp [layerToEndpoint]
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (pow_pos (by omega) _)).1 hm'.2
  · dsimp [layerToEndpoint]
    rw [hdecomp.1]
    omega

private lemma layer_endpoint_inverse
    (q : ℕ) (x : Σ _ : ℕ, ℕ) (hx : x ∈ endpointIndexSet q) :
    layerToEndpoint (endpointToLayer x) = x := by
  obtain ⟨hh, hj⟩ := mem_sigma.mp hx
  have hh0 := (mem_Icc.mp hh).1
  have hj' := mem_range.mp hj
  apply Sigma.ext
  · dsimp [layerToEndpoint, endpointToLayer]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel]
    · exact ten_reduction x.1
    · exact Nat.le_of_lt hj'
  · apply heq_of_eq
    dsimp [layerToEndpoint, endpointToLayer]
    have hpart0 : 0 < tenPrimitivePart x.1 := by
      have hred := ten_reduction x.1
      by_contra hz
      simp only [not_lt] at hz
      have : tenPrimitivePart x.1 = 0 := Nat.eq_zero_of_le_zero hz
      rw [this, mul_zero] at hred
      omega
    rw [tenValuation_pow_mul_of_not_dvd hpart0.ne'
      (ten_not_dvd_primitivePart (lt_of_lt_of_le Nat.zero_lt_one hh0))]

private lemma endpoint_layer_inverse
    (k : ℕ) (x : Σ _ : ℕ, ℕ) (hx : x ∈ layerIndexSet k) :
    endpointToLayer (layerToEndpoint x) = x := by
  obtain ⟨hs, hm⟩ := mem_sigma.mp hx
  have hm' := mem_Icc.mp hm
  have hm0 : 0 < x.2 := by omega
  have hdecomp := ten_pow_mul_decomposition x.1 x.2 hm0
  apply Sigma.ext
  · dsimp [endpointToLayer, layerToEndpoint]
    rw [hdecomp.1]
    omega
  · apply heq_of_eq
    dsimp [endpointToLayer, layerToEndpoint]
    rw [hdecomp.2]
    exact ten_reduction x.2

private lemma initial_phase_reindex
    (q A : ℕ) (x : Σ _ : ℕ, ℕ) (hx : x ∈ endpointIndexSet q) :
    centeredBoundaryTerm q A x.1 *
        phase (tenPrimitivePart x.1 : ℤ) (piOrbit x.2) =
      (positiveBoundaryCoefficient q (10 ^ (endpointToLayer x).1 *
          (endpointToLayer x).2) : ℂ) *
        phase ((endpointToLayer x).2 : ℤ)
          (Real.pi - 10 ^ (endpointToLayer x).1 * decimalCylinderCenter q A) := by
  obtain ⟨hh, hj⟩ := mem_sigma.mp hx
  have hj' := mem_range.mp hj
  have hfreq : 10 ^ (endpointToLayer x).1 * (endpointToLayer x).2 = x.1 := by
    dsimp [endpointToLayer]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hj'), ten_reduction]
  rw [hfreq]
  unfold centeredBoundaryTerm
  rw [mul_assoc]
  congr 1
  unfold phase Theory.PiDigits.T27.phase piOrbit Theory.PiDigits.T27.piFractionalOrbit
  rw [Theory.PiDigits.T29.phase_fract_eq_phase]
  rw [← Complex.exp_add]
  congr 1
  dsimp [endpointToLayer]
  push_cast
  have hfreqC : (x.1 : ℂ) =
      (10 : ℂ) ^ (tenValuation x.1 - x.2) *
        ((10 : ℂ) ^ x.2 * tenPrimitivePart x.1) := by
    exact_mod_cast hfreq.symm
  rw [hfreqC]
  ring

private lemma terminal_phase_reindex
    (q A N : ℕ) (x : Σ _ : ℕ, ℕ) (hx : x ∈ endpointIndexSet q) :
    centeredBoundaryTerm q A x.1 *
        phase (tenPrimitivePart x.1 : ℤ) (piOrbit (N + x.2)) =
      (positiveBoundaryCoefficient q (10 ^ (endpointToLayer x).1 *
          (endpointToLayer x).2) : ℂ) *
        phase ((endpointToLayer x).2 : ℤ)
          ((10 : ℝ) ^ N * Real.pi -
            10 ^ (endpointToLayer x).1 * decimalCylinderCenter q A) := by
  obtain ⟨hh, hj⟩ := mem_sigma.mp hx
  have hj' := mem_range.mp hj
  have hfreq : 10 ^ (endpointToLayer x).1 * (endpointToLayer x).2 = x.1 := by
    dsimp [endpointToLayer]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hj'), ten_reduction]
  rw [hfreq]
  unfold centeredBoundaryTerm
  rw [mul_assoc]
  congr 1
  unfold phase Theory.PiDigits.T27.phase piOrbit Theory.PiDigits.T27.piFractionalOrbit
  rw [Theory.PiDigits.T29.phase_fract_eq_phase]
  rw [← Complex.exp_add]
  congr 1
  dsimp [endpointToLayer]
  push_cast
  have hfreqC : (x.1 : ℂ) =
      (10 : ℂ) ^ (tenValuation x.1 - x.2) *
        ((10 : ℂ) ^ x.2 * tenPrimitivePart x.1) := by
    exact_mod_cast hfreq.symm
  rw [hfreqC, pow_add]
  ring

/-- Generic scalar form of the valuation-layer partition.  Each supported
frequency `h` occurs once for every `j < tenValuation h`; on the right it is
written uniquely as `h = 10^s * m` with `1 <= s <= k`. -/
theorem sum_valuation_eq_sum_decimal_layers
    {R : Type*} [AddCommMonoid R] (k : ℕ) (f : ℕ → R) :
    (∑ h ∈ positiveBoundarySupport (10 ^ k),
        ∑ _j ∈ range (tenValuation h), f h) =
      ∑ s ∈ Icc 1 k,
        ∑ m ∈ Icc 1 ((2 * 10 ^ k - 1) / 10 ^ s), f (10 ^ s * m) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  change (∑ x ∈ endpointIndexSet (10 ^ k), f x.1) =
    ∑ x ∈ layerIndexSet k, f (10 ^ x.1 * x.2)
  apply Finset.sum_bij' (fun x _ => endpointToLayer x) (fun x _ => layerToEndpoint x)
  · exact endpointToLayer_mem k
  · exact layerToEndpoint_mem k
  · intro x hx
    exact layer_endpoint_inverse (10 ^ k) x hx
  · intro x hx
    exact endpoint_layer_inverse k x hx
  · intro x hx
    congr 1
    exact congrArg Sigma.fst (layer_endpoint_inverse (10 ^ k) x hx) |>.symm

/-- Exact valuation-layer decomposition of the literal initial endpoint. -/
theorem initialBoundaryEndpoint_eq_sum_layers
    (k A : ℕ) :
    initialBoundaryEndpoint (10 ^ k) A =
      ∑ s ∈ Icc 1 k,
        boundaryLayerPolynomial (10 ^ k) s
          (Real.pi - 10 ^ s * decimalCylinderCenter (10 ^ k) A) := by
  classical
  unfold initialBoundaryEndpoint boundaryLayerPolynomial
    Theory.PiDigits.T27.exponentialSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij' (fun x _ => endpointToLayer x) (fun x _ => layerToEndpoint x)
  · exact endpointToLayer_mem k
  · exact layerToEndpoint_mem k
  · intro x hx
    exact layer_endpoint_inverse (10 ^ k) x hx
  · intro x hx
    exact endpoint_layer_inverse k x hx
  · intro x hx
    exact initial_phase_reindex (10 ^ k) A x hx

/-- Exact valuation-layer decomposition of the literal terminal endpoint. -/
theorem terminalBoundaryEndpoint_eq_sum_layers
    (k A N : ℕ) :
    terminalBoundaryEndpoint (10 ^ k) A N =
      ∑ s ∈ Icc 1 k,
        boundaryLayerPolynomial (10 ^ k) s
          ((10 : ℝ) ^ N * Real.pi -
            10 ^ s * decimalCylinderCenter (10 ^ k) A) := by
  classical
  unfold terminalBoundaryEndpoint boundaryLayerPolynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij' (fun x _ => endpointToLayer x) (fun x _ => layerToEndpoint x)
  · exact endpointToLayer_mem k
  · exact layerToEndpoint_mem k
  · intro x hx
    exact layer_endpoint_inverse (10 ^ k) x hx
  · intro x hx
    exact endpoint_layer_inverse k x hx
  · intro x hx
    exact terminal_phase_reindex (10 ^ k) A N x hx

/-- Exact layer-polynomial formula for T139's complete endpoint. -/
theorem primitiveBoundaryEndpoint_eq_layer_terminal_sub_initial
    (k A N : ℕ) :
    primitiveBoundaryEndpoint (10 ^ k) A N =
      (∑ s ∈ Icc 1 k,
        boundaryLayerPolynomial (10 ^ k) s
          ((10 : ℝ) ^ N * Real.pi -
            10 ^ s * decimalCylinderCenter (10 ^ k) A)) -
      ∑ s ∈ Icc 1 k,
        boundaryLayerPolynomial (10 ^ k) s
          (Real.pi - 10 ^ s * decimalCylinderCenter (10 ^ k) A) := by
  rw [primitiveBoundaryEndpoint_eq_terminal_sub_initial,
    terminalBoundaryEndpoint_eq_sum_layers, initialBoundaryEndpoint_eq_sum_layers]

end Theory.PiDigits.BoundaryEndpointLayers

#print axioms Theory.PiDigits.BoundaryEndpointLayers.sum_valuation_eq_sum_decimal_layers
#print axioms Theory.PiDigits.BoundaryEndpointLayers.initialBoundaryEndpoint_eq_sum_layers
#print axioms Theory.PiDigits.BoundaryEndpointLayers.terminalBoundaryEndpoint_eq_sum_layers
#print axioms Theory.PiDigits.BoundaryEndpointLayers.primitiveBoundaryEndpoint_eq_layer_terminal_sub_initial
