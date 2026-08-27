import TheoryLib.PiLacunaryNearReturnSparsity.T13IteratedLagResonance
import TheoryLib.PiLacunaryNearReturnSparsity.T24FiniteInverseDichotomy

/-!
# T26: one shared autocorrelation chain with nodewise inverse witnesses

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module preserves every intermediate resonance from one T13
autocorrelation recursion and applies T24 at each node of that same chain.
All results from literal failure of canonical A1 are necessary-only. They do
not assert compatibility of inverse witnesses, a uniform or depth-independent
preperiod bound, A1, or an irrationality contradiction.
-/

noncomputable section

open Finset
open scoped ComplexConjugate Real

namespace DecimalFactorComplexity
namespace SharedResonanceChain

open IteratedLagResonance
open FiniteInverseDichotomy

/-- A depth-`d` autocorrelation chain. Node `k` uses the first `k` shifts of
one shared list, so all intermediate large-sum inequalities are retained. -/
structure AutocorrelationChain
    (z : ℕ → ℂ) (M D B K d : ℕ) (F : Finset ℕ) where
  shifts : List ℕ
  length_eq : shifts.length = d
  nodup : shifts.Nodup
  shift_lower : ∀ s ∈ shifts, B ≤ s
  shift_avoids : ∀ s ∈ shifts, s ∉ F
  final_residual : K ≤ M - shifts.sum
  node_resonance : ∀ k : ℕ, k ≤ d →
    (((M - (shifts.take k).sum : ℕ) : ℝ) / densityDenominator D k <
      ‖∑ j ∈ range (M - (shifts.take k).sum),
        iteratedDifference z (shifts.take k) j‖)

/-- Residual length at node `k` of one shared chain. -/
def AutocorrelationChain.nodeResidual
    {z : ℕ → ℂ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : AutocorrelationChain z M D B K d F) (k : ℕ) : ℕ :=
  M - (chain.shifts.take k).sum

/-- Density denominator at node `k`. -/
def nodeDensity (D k : ℕ) : ℕ := densityDenominator D k

/-- Construct a chain while retaining the large-sum inequality at every
recursive extraction state. -/
theorem exists_autocorrelationChain
    (z : ℕ → ℂ) (M D B K d : ℕ) (F : Finset ℕ)
    (hz : ∀ j, ‖z j‖ = 1) (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hM : iterationLengthThresholdAux D B K F.card d ≤ M)
    (hlarge : (M : ℝ) / D < ‖∑ j ∈ range M, z j‖) :
    Nonempty (AutocorrelationChain z M D B K d F) := by
  induction d generalizing z M D F with
  | zero =>
      refine ⟨⟨[], rfl, List.nodup_nil, ?_, ?_, ?_, ?_⟩⟩
      · intro s hs
        simp at hs
      · intro s hs
        simp at hs
      · simpa [iterationLengthThresholdAux] using hM
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        simpa [densityDenominator, iteratedDifference] using hlarge
  | succ d ih =>
      let R := iterationLengthThresholdAux
        (nextDensityDenominator D) B K (F.card + 1) d
      have hstep : oneStepLengthThreshold D B F.card R ≤ M := by
        simpa [iterationLengthThresholdAux, R] using hM
      obtain ⟨s, hsRange, hsF, hsLarge⟩ :=
        oneStep_autocorrelation_extraction z M D B R F hz hD hstep hlarge
      have hsBounds := mem_Icc.mp hsRange
      have hR : R ≤ M - s := by omega
      let z' : ℕ → ℂ := fun j => z (j + s) * conj (z j)
      have hz' : ∀ j, ‖z' j‖ = 1 := by
        intro j
        simp [z', hz]
      have hcard : (insert s F).card = F.card + 1 := by
        rw [card_insert_of_notMem hsF]
      have hM' : iterationLengthThresholdAux (nextDensityDenominator D) B K
          (insert s F).card d ≤ M - s := by
        rw [hcard]
        exact hR
      have hlarge' :
          (((M - s : ℕ) : ℝ) / nextDensityDenominator D <
            ‖∑ j ∈ range (M - s), z' j‖) := by
        simpa [autocorrelation, z'] using hsLarge
      obtain ⟨tail⟩ := ih z' (M - s) (nextDensityDenominator D) (insert s F)
        hz' (nextDensityDenominator_pos D hD) hM' hlarge'
      refine ⟨⟨s :: tail.shifts, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp [tail.length_eq]
      · rw [List.nodup_cons]
        constructor
        · intro hsTail
          exact tail.shift_avoids s hsTail (mem_insert_self s F)
        · exact tail.nodup
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hsBounds.1
        · exact tail.shift_lower t ht
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hsF
        · exact fun htF => tail.shift_avoids t ht (mem_insert_of_mem htF)
      · simpa [List.sum_cons, Nat.sub_sub] using tail.final_residual
      · intro k hk
        cases k with
        | zero =>
            simpa [densityDenominator, iteratedDifference] using hlarge
        | succ k =>
            have hkTail : k ≤ d := by omega
            simpa [List.take_succ_cons, List.sum_cons, Nat.sub_sub,
              densityDenominator, iteratedDifference, z'] using
                tail.node_resonance k hkTail

/-- A geometric chain exposes the coefficient at every prefix node. -/
structure GeometricResonanceChain
    (c : ℝ) (M D B K d : ℕ) (F : Finset ℕ) where
  shifts : List ℕ
  length_eq : shifts.length = d
  nodup : shifts.Nodup
  shift_lower : ∀ s ∈ shifts, B ≤ s
  shift_avoids : ∀ s ∈ shifts, s ∉ F
  final_residual : K ≤ M - shifts.sum
  node_resonance : ∀ k : ℕ, k ≤ d →
    (((M - (shifts.take k).sum : ℕ) : ℝ) / densityDenominator D k <
      ‖∑ j ∈ range (M - (shifts.take k).sum),
        geometricPhase
          (c * ((shifts.take k).map
            (fun s => (10 : ℝ) ^ s - 1)).prod) j‖)

/-- The explicit real phase coefficient at a geometric-chain node. -/
def GeometricResonanceChain.nodeCoefficient
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F) (k : ℕ) : ℝ :=
  c * ((chain.shifts.take k).map
    (fun s => (10 : ℝ) ^ s - 1)).prod

/-- The explicit residual length at a geometric-chain node. -/
def GeometricResonanceChain.nodeResidual
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F) (k : ℕ) : ℕ :=
  M - (chain.shifts.take k).sum

/-- Specialize the retained autocorrelation chain to explicit geometric
coefficients. -/
theorem exists_geometricResonanceChain
    (c : ℝ) (M D B K d : ℕ) (F : Finset ℕ)
    (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hM : iterationLengthThresholdAux D B K F.card d ≤ M)
    (hlarge : (M : ℝ) / D <
      ‖∑ j ∈ range M, geometricPhase c j‖) :
    Nonempty (GeometricResonanceChain c M D B K d F) := by
  have hz : ∀ j, ‖geometricPhase c j‖ = 1 := by
    intro j
    simpa [geometricPhase, Theory.PiDigits.T27.phase] using
      Theory.PiDigits.T27.norm_phase (1 : ℤ) ((10 : ℝ) ^ j * c)
  obtain ⟨chain⟩ := exists_autocorrelationChain
    (geometricPhase c) M D B K d F hz hD hB hM hlarge
  refine ⟨⟨chain.shifts, chain.length_eq, chain.nodup,
    chain.shift_lower, chain.shift_avoids, chain.final_residual, ?_⟩⟩
  intro k hk
  simpa only [iteratedDifference_geometricPhase] using
    chain.node_resonance k hk

/-- The final requested length used to make T24 available at every node. -/
def chainLengthRequest (D d : ℕ) : ℕ :=
  2 * densityDenominator D d ^ 2

/-- Normalized resonance density at node `k`. -/
def nodeDelta (D k : ℕ) : ℝ :=
  (densityDenominator D k : ℝ)⁻¹

/-- Correlation threshold at node `k`. -/
def nodeTau (D k : ℕ) : ℝ :=
  1 / (8 * (densityDenominator D k : ℝ) ^ 2)

lemma densityDenominator_le_succ (D d : ℕ) (hD : 1 ≤ D) :
    densityDenominator D d ≤ densityDenominator D (d + 1) := by
  induction d generalizing D with
  | zero =>
      simp only [densityDenominator]
      unfold nextDensityDenominator
      nlinarith
  | succ d ih =>
      simp only [densityDenominator]
      exact ih (nextDensityDenominator D) (nextDensityDenominator_pos D hD)

lemma densityDenominator_mono (D : ℕ) (hD : 1 ≤ D) :
    Monotone (densityDenominator D) :=
  monotone_nat_of_le_succ fun d => densityDenominator_le_succ D d hD

lemma GeometricResonanceChain.prefix_sum_le
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F) (k : ℕ) :
    (chain.shifts.take k).sum ≤ chain.shifts.sum := by
  have h := congrArg List.sum (List.take_append_drop k chain.shifts)
  simp only [List.sum_append] at h
  omega

lemma GeometricResonanceChain.finalResidual_le_nodeResidual
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F) (k : ℕ) :
    M - chain.shifts.sum ≤ chain.nodeResidual k := by
  unfold GeometricResonanceChain.nodeResidual
  have hsum := chain.prefix_sum_le k
  omega

/-- T24 applied at every node of one fixed geometric chain. The alternatives
are nodewise necessary conditions only; this theorem adds no compatibility
between the cycle or positive-preperiod witnesses selected at different
nodes. -/
theorem GeometricResonanceChain.nodewise_inverse_necessaryOnly
    {c : ℝ} {M D B K d : ℕ} {F : Finset ℕ}
    (chain : GeometricResonanceChain c M D B K d F)
    (hD : 1 ≤ D) (hrequest : chainLengthRequest D d ≤ K) :
    ∀ k : ℕ, k ≤ d →
      CycleApproximation (chain.nodeCoefficient k) (nodeTau D k)
          (chain.nodeResidual k) ∨
        (¬ CycleApproximation (chain.nodeCoefficient k) (nodeTau D k)
            (chain.nodeResidual k) ∧
          PositivePreperiodApproximation
            (chain.nodeCoefficient k) (nodeTau D k)
              (chain.nodeResidual k)) := by
  intro k hk
  let Dk : ℕ := densityDenominator D k
  let Mk : ℕ := chain.nodeResidual k
  let beta : ℝ := chain.nodeCoefficient k
  have hDk : 1 ≤ Dk := by
    exact FiniteInverseDichotomy.densityDenominator_pos D k hD
  have hDmono : Dk ≤ densityDenominator D d := by
    exact densityDenominator_mono D hD hk
  have hsquare : Dk ^ 2 ≤ densityDenominator D d ^ 2 :=
    Nat.pow_le_pow_left hDmono 2
  have hfinal : K ≤ Mk := by
    exact chain.final_residual.trans (chain.finalResidual_le_nodeResidual k)
  have hMrequest : 2 * Dk ^ 2 ≤ Mk := by
    have hterminal : 2 * Dk ^ 2 ≤ chainLengthRequest D d := by
      simpa [chainLengthRequest] using Nat.mul_le_mul_left 2 hsquare
    exact hterminal.trans (hrequest.trans hfinal)
  have hDreal : 0 < (Dk : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hDk)
  have hDone : (1 : ℝ) ≤ (Dk : ℝ) := by exact_mod_cast hDk
  have hdelta : 0 < nodeDelta D k := by
    simpa [nodeDelta, Dk] using inv_pos.mpr hDreal
  have htauPos : 0 < nodeTau D k := by
    unfold nodeTau
    positivity
  have htauDelta : nodeTau D k < nodeDelta D k := by
    have hlocal : 1 / (8 * (Dk : ℝ) ^ 2) < 1 / (Dk : ℝ) := by
      apply one_div_lt_one_div_of_lt hDreal
      nlinarith
    simpa [nodeTau, nodeDelta, Dk, one_div] using hlocal
  have hdeltaOne : nodeDelta D k ≤ 1 := by
    rw [nodeDelta]
    simpa [Dk, one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hDone)
  have henergy :
      (Mk : ℝ) + 2 * nodeTau D k * (Mk : ℝ) ^ 2 ≤
        (nodeDelta D k * (Mk : ℝ)) ^ 2 := by
    simpa [nodeTau, nodeDelta, Dk] using
      stage_energy_inequality Dk Mk hDk hMrequest
  have hlarge :
      nodeDelta D k * (Mk : ℝ) <
        ‖∑ j ∈ range Mk, geometricPhase beta j‖ := by
    have hnode := chain.node_resonance k hk
    simpa [nodeDelta, Dk, Mk, beta,
      GeometricResonanceChain.nodeResidual,
      GeometricResonanceChain.nodeCoefficient,
      div_eq_mul_inv, mul_comm] using hnode
  simpa [Mk, beta] using
    finite_cycle_or_positivePreperiod_inverse
      beta (nodeDelta D k) (nodeTau D k) Mk
        htauPos htauDelta hdeltaOne henergy hlarge

/-- T13's initial density denominator before any chain shift. -/
def initialDensity (A n : ℕ) : ℕ := 131072 * A ^ 2 * n ^ 2

/-- T13's initial coefficient before any chain shift. -/
def initialCoefficient (h r : ℕ) : ℝ :=
  (h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi

/-- Literal failure of canonical A1 supplies arbitrarily deep chains. For a
fixed requested depth, the returned record contains one shift list and every
prefix resonance from its construction. This is a necessary-only statement;
it does not assert literal failure of A1. -/
theorem literal_not_A1_implies_shared_chain_necessaryOnly
    (hnotA1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ ∀ d : ℕ,
        let D := initialDensity A n
        let K := chainLengthRequest D d
        let L := iterationLengthThresholdAux D 1 K 1 d
        ∃ N r h : ℕ,
          ∃ chain : GeometricResonanceChain
              (initialCoefficient h r) (N - r) D 1 K d {r},
            chain.shifts.length = d ∧
            N = 16 * A * n * L ∧
            r ∈ Icc 1 (N - 1) ∧
            h ∈ Icc 1 (256 * A * n) := by
  obtain ⟨A, hA, hinitial⟩ :=
    literal_not_A1_implies_arbitrarily_long_initial_resonance hnotA1
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hinitialn⟩ := hinitial n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  intro d
  let D : ℕ := initialDensity A n
  let K : ℕ := chainLengthRequest D d
  let L : ℕ := iterationLengthThresholdAux D 1 K 1 d
  have hD : 1 ≤ D := by
    dsimp [D, initialDensity]
    have hpos : 0 < 131072 * A ^ 2 * n ^ 2 := by positivity
    omega
  have hK : 1 ≤ K := by
    dsimp [K, chainLengthRequest]
    have hdenom := FiniteInverseDichotomy.densityDenominator_pos D d hD
    have hpos : 0 < 2 * densityDenominator D d ^ 2 := by positivity
    omega
  have hL : 1 ≤ L := by
    exact iterationLengthThresholdAux_pos D 1 K 1 d hD hK
  obtain ⟨N, r, h, hN, hr, hLlength, hh, hresonance⟩ :=
    hinitialn L hL
  let c : ℝ := initialCoefficient h r
  have hphase (j : ℕ) :
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
            (((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi : ℝ) : ℂ)) =
        geometricPhase c j := by
    unfold geometricPhase c initialCoefficient
    congr 1
    push_cast
    ring
  have hresonance' :
      (((N - r : ℕ) : ℝ) / D <
        ‖∑ j ∈ range (N - r), geometricPhase c j‖) := by
    have hDcast : (D : ℝ) =
        131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      dsimp [D, initialDensity]
      push_cast
      ring
    rw [hDcast]
    simpa only [hphase] using hresonance
  have hthreshold :
      iterationLengthThresholdAux D 1 K ({r} : Finset ℕ).card d ≤ N - r := by
    simpa [L] using hLlength
  obtain ⟨chain⟩ := exists_geometricResonanceChain
    c (N - r) D 1 K d {r} hD (by norm_num) hthreshold hresonance'
  refine ⟨N, r, h, ?_, ?_, ?_, hr, hh⟩
  · simpa [c] using chain
  · exact chain.length_eq
  · simpa [L] using hN

/-- Main T26 conclusion. Literal failure of canonical A1 necessarily supplies
one shared depth-`d` chain and a T24 cycle-or-positive-preperiod alternative at
every prefix node. The alternatives are not asserted to be compatible across
nodes. There is no uniform preperiod bound, proof of A1, or irrationality
contradiction. -/
theorem literal_not_A1_implies_shared_chain_nodewise_inverse_necessaryOnly
    (hnotA1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ ∀ d : ℕ,
        let D := initialDensity A n
        let K := chainLengthRequest D d
        let L := iterationLengthThresholdAux D 1 K 1 d
        ∃ N r h : ℕ,
          ∃ chain : GeometricResonanceChain
              (initialCoefficient h r) (N - r) D 1 K d {r},
            chain.shifts.length = d ∧
            N = 16 * A * n * L ∧
            r ∈ Icc 1 (N - 1) ∧
            h ∈ Icc 1 (256 * A * n) ∧
            ∀ k : Fin (d + 1),
              let nodePrefix := chain.shifts.take k
              let beta := initialCoefficient h r *
                (nodePrefix.map (fun s => (10 : ℝ) ^ s - 1)).prod
              let Mk := N - r - nodePrefix.sum
              let tau := 1 /
                (8 * (densityDenominator D k : ℝ) ^ 2)
              CycleApproximation beta tau Mk ∨
                (¬ CycleApproximation beta tau Mk ∧
                  PositivePreperiodApproximation beta tau Mk) := by
  obtain ⟨A, hA, hchains⟩ :=
    literal_not_A1_implies_shared_chain_necessaryOnly hnotA1
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hchainsn⟩ := hchains n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  intro d
  let D : ℕ := initialDensity A n
  let K : ℕ := chainLengthRequest D d
  let L : ℕ := iterationLengthThresholdAux D 1 K 1 d
  obtain ⟨N, r, h, chain, hlength, hN, hr, hh⟩ := hchainsn d
  have hD : 1 ≤ D := by
    dsimp [D, initialDensity]
    have hpos : 0 < 131072 * A ^ 2 * n ^ 2 := by positivity
    omega
  have hinverse := chain.nodewise_inverse_necessaryOnly hD
    (show chainLengthRequest D d ≤ K by rfl)
  refine ⟨N, r, h, chain, hlength, ?_, hr, hh, ?_⟩
  · simpa [L] using hN
  · intro k
    have hk : k.val ≤ d := by omega
    simpa [GeometricResonanceChain.nodeCoefficient,
      GeometricResonanceChain.nodeResidual, nodeTau] using
        hinverse k.val hk

end SharedResonanceChain
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.SharedResonanceChain.exists_autocorrelationChain
#print axioms DecimalFactorComplexity.SharedResonanceChain.exists_geometricResonanceChain
#print axioms DecimalFactorComplexity.SharedResonanceChain.GeometricResonanceChain.nodewise_inverse_necessaryOnly
#print axioms DecimalFactorComplexity.SharedResonanceChain.literal_not_A1_implies_shared_chain_necessaryOnly
#print axioms DecimalFactorComplexity.SharedResonanceChain.literal_not_A1_implies_shared_chain_nodewise_inverse_necessaryOnly
