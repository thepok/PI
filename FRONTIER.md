# π decimal disjunctivity frontier

Target status (V1): `conjecture`
Last audited: 2026-09-03 UTC

## Target and ladder

[`Theory.PiDigits.V1`](TheoryLib/PiDigits/T7Statements.lean) states `∀ s : List (Fin 10), ∃ n : ℕ, ∀ i < s.length, piDigit (n+i) = s[i]`.
Leading-zero words and overlaps are included; the empty word is vacuous.
For `x_n={10^n*pi}`, the constant-word benchmarks are `proof sketch`, directly from decimal cylinders:
`CW0: every word 0^k occurs <-> liminf x_n = 0`.
`CW9: every word 9^k occurs <-> limsup x_n = 1`.
`E: liminf ||10^n*pi||=0` is equivalent only to `CW0 or CW9`; `CW0 and CW9` is the constant-word rung below V1, and none of E, CW0, CW9, or V1 is proved.

## The wall

1. No known proved Diophantine or analytic property of π supplies a prescribed decimal target sign.
2. Index entry `docA` records the separator article and its currently available repository stub.
3. Index entry `docB` records the technical companion's exact reformulations and route audits.
4. Theorem A gives badly approximable transcendental word-avoiders with irrationality exponent 2.
5. Such avoiders share the finite-exponent and central-return premises used by T191–T194.
6. Exact identities, rational shadows, positive errors, valuations, and unsigned energies can also retain the missing orientation.
7. Finite computation can falsify or refine a route but cannot prove an unbounded word-occurrence claim.
8. Therefore separator-first testing precedes construction of any new Lean rung.
9. Every candidate must identify exactly where actual-π target-signed information enters.
10. A premise shared by a recorded digit-avoider cannot prove V1.

## Machine-checked status (generated from INDEX.yaml)

| ID | Label | Lean name | What it does not show |
|---|---|---|---|
| T16 | machine-checked | `Theory.PiDigits.DecimalBoundaryWordObstruction.not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance` | C1 remains undecided. |
| T17 | machine-checked | `Theory.PiDigits.PowerTenDiophantineReduction.not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine` | The premise and C1 remain open. |
| T69 | machine-checked | `Theory.PiDigits.T69FixedSixteenReturn.v1_iff_fixedSixteenReturn` | Density and return remain open. |
| T102 | machine-checked | `Theory.PiDigits.T102BBPKernelIntegral.intervalIntegral_bbpKernel` | No series interchange follows. |
| T104 | machine-checked | `Theory.PiDigits.T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi` | No digit distribution follows. |
| T128 | machine-checked | `Theory.PiDigits.BoundaryMatchedKernel.finite_decimalInterval_hit_of_boundary_explicit_smallness` | No π cancellation follows. |
| T130 | machine-checked | `Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.normalized_boundary_lt_jackson` | No π cancellation follows. |
| T138 | machine-checked | `Theory.PiDigits.PrimitiveRayCoefficientGap.primitiveBoundaryLoad_pow_ten_lt_positiveBoundaryLoad_sub_gap` | No π cancellation follows. |
| T139 | machine-checked | `Theory.PiDigits.PrimitiveRayBoundaryConsumer.piOrbit_hit_of_uniform_primitiveCancellation_pow_ten` | Its hypotheses remain open. |
| T142 | machine-checked | `Theory.PiDigits.BoundaryCoefficientAbel.sampled_positiveBoundaryCoefficient_abel_lt` | No endpoint theorem follows. |
| T143 | machine-checked | `Theory.PiDigits.BoundaryEndpointLayers.primitiveBoundaryEndpoint_eq_layer_terminal_sub_initial` | No endpoint bound follows. |
| T144 | machine-checked | `Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass_pow_ten_eq` | No orbit estimate follows. |
| T146 | machine-checked | `Theory.PiDigits.BoundaryPhaseTorusBounds.decimal_phase_distance_dichotomy` | No endpoint consumer follows. |
| T147 | machine-checked | `Theory.PiDigits.BoundaryEndpointContraction.primitiveBoundaryEndpoint_norm_lt_two_budget_sub` | No primitive-sum bound follows. |
| T148 | machine-checked | `Theory.PiDigits.ImprovedPrimitiveBoundaryConsumer.piOrbit_hit_of_improved_primitiveBoundary_smallness_pow_ten` | Its threshold remains open. |
| T150 | machine-checked | `Theory.PiDigits.BoundaryKernelFloors.boundaryMinorant_re_gt_neg_eight_mul_sq_div` | No orbit cancellation follows. |
| T151 | machine-checked | `Theory.PiDigits.BoundaryProjectedLayerFloor.divisibleBoundaryPolynomial_re_gt` | No recurrence follows. |
| T153 | machine-checked | `Theory.PiDigits.BoundaryRootGridNaturalConsumer.piOrbit_hit_of_rootGrid_primitiveBoundary_ge` | Its lower bound remains open. |
| T156 | machine-checked | `Theory.PiDigits.BoundaryNaturalThresholdClosure.piOrbit_hit_of_primitiveBoundary_ge_neg_861` | Its primitive bound remains open. |
| T157 | machine-checked | `Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPRat_five_val_eq` | No occurrence follows. |
| T159 | machine-checked | `Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrime_val_eq_neg_one` | No cancellation follows. |
| T169 | machine-checked | `Theory.PiDigits.T169SingleRateMachinPhaseTransfer.norm_shiftedPositiveBoundaryPiScore_sub_machin_le` | No carrier cancellation follows. |
| T170 | machine-checked | `Theory.PiDigits.T170MachinFixedPointIntervals.pi_mem_decimalCylinder_100` | No recurrence follows. |
| T172 | machine-checked | `Theory.PiDigits.PositiveLeftExtensionTransport.primitiveBoundaryFourierSum_leftExtension` | No prescribed child follows. |
| T173 | machine-checked | `Theory.PiDigits.T173MachinIntegerCertificate10015.pi_mem_decimalCylinder_10015` | No distribution follows. |
| T174 | machine-checked | `Theory.PiDigits.FinitePrimitiveScoreIdentity.two_mul_primitiveBoundaryFourierSum_re_eq_finite_score` | No positive π-score follows. |
| T175 | machine-checked | `Theory.PiDigits.T175DecimalSuffixCylinder.piOrbit_mem_certified_suffixCylinder` | Only finite replay follows. |
| T176 | machine-checked | `Theory.PiDigits.SignedBlockBellmanTransport.exists_leftExtension_prefix_bellman_gt` | Neither digit nor root positivity is prescribed. |
| T177 | machine-checked | `Theory.PiDigits.PredecessorDigitDFT.ten_mul_child_re_eq_zeroSector_add_nonzero` | No favorable sign follows. |
| T178 | machine-checked | `Theory.PiDigits.SignedPredecessorRay.exists_infinite_signed_predecessor_ray` | No root positivity,natural horizon,or V1 follows. |
| T179 | machine-checked | `Theory.PiDigits.PredecessorLagOneCorrelation.predecessorDigitSector_eq_lagOneCorrelation` | No cancellation estimate follows. |
| T180 | machine-checked | `Theory.PiDigits.T180ReflectedTrigIntervalCore.checked_trig_bounds` | No production payload follows. |
| T181 | machine-checked | `Theory.PiDigits.T181ReflectedIntervalArithmetic.checkDiv_sound` | No π-score follows. |
| T185 | machine-checked | `Theory.PiDigits.T185BoundaryMinorantSineBridge.two_mul_primitiveBoundaryFourierSum_re_eq_closed_sine_score` | No payload or sign follows. |
| T187 | machine-checked | `Theory.PiDigits.T187ReflectedTrigShard9965.shard_sound` | The full score is absent. |
| T189 | machine-checked | `Theory.PiDigits.SignedHorizonSectorBridge.signedPrefixSurplus_child_pos_of_horizon_sector_gt` | Its π-sector premise remains open. |
| T190 | machine-checked | `Theory.PiDigits.T190ComplementaryRankAlignment.exists_digit_D_pos_and_G_add_D_pos_of_complementary_card` | Both rank premises remain open. |
| T191 | machine-checked | `Theory.PiDigits.T191CentralBoundaryKernelFloor.boundaryMinorant_re_gt_4859_div_10000` | No orbit premise follows. |
| T192 | machine-checked | `Theory.PiDigits.T192PrimitiveValuationShells.primitiveValuationShell_zero_re_gt` | Positive shells remain open. |
| T193 | machine-checked | `Theory.PiDigits.T193PositiveValuationShellAggregate.central_unitBlock_surplus_gt_three_div_twenty` | Recurrence/timing remain open. |
| T194 | machine-checked | `Theory.PiDigits.T194CentralPiReturnSeed.exists_central_pi_unitBlock_surplus` | Target,timing,and ray remain open. |
| T198 | machine-checked | `Theory.PiDigits.T198MachinBracketPack.machinMC0_iff_piCW0` | Neither MC0 nor CW0 follows. |
| T199 | machine-checked | `Theory.PiDigits.T199BBPShadowPack.bbp10_soh0_iff_piCW0` | Neither CW0 nor CW9 follows. |
| T200 | machine-checked | `Theory.PiDigits.T200BaileyCrandallCoboundary.Y_add_tau_eq_pow_mul_pi` | No base-16 density follows. |
| T202 | machine-checked | `Theory.PiDigits.T202RamanujanDyadicRamp.lambda_prefix_ramp` | No positive tail/target follows. |
| T204 | machine-checked | `Theory.PiDigits.T204ConstantRunBound.measureBelow_implies_exponentAtMost`<br>`Theory.PiDigits.T204ConstantRunBound.nineRun_eventually_bounded` | Zero-run bounds and run existence remain open. |
| T206 | machine-checked | `Theory.PiDigits.T206EndpointBridge.CWord_symmDiff_KWordReal_subset_E10` | No occurrence,density,or prefix analogue follows. |

## [Open problems](knowledge/pi/workstreams/OPEN_PROBLEMS.md)

- **P1-FD** — ∀(m,w,A,c)∈𝔓₁:dim_H(C_w∩BA∩ALA_(A,c))=d_w.
- **P1-PD** — ∀(m,w,A,c)∈𝔓₁:dim_H(C_w∩BA∩ALA_(A,c))>0.
- **P1-NE** — ∀(m,w,A,c)∈𝔓₁:C_w∩BA∩ALA_(A,c)≠∅.
- **P1-FD-loc** — ∀(m,w,A,c)∈𝔓₁,finite P:C_w∩I(P)≠∅⇒dim_H(X(w,A,c)∩I(P))=d_w.
- **P1′** — ∀b≥2,Σ∈SFT_b,F sparse/entropy-neutral,0<s<d_Σ,∃κ>0:dim_H(K_(Σ,F)∩BA(κ))≥s.
- **MC0** — ∀k≥1,∃m,n≥0:10^kR^M_(m,n)+10^(n+k)Δ_m<D^M_m.
- **SOH-3/7** — ∀k,M≥1,∃m≥M,n≥0:10^kR^M_(m,n)+10^(n+k)Δ_m<D^M_m.
- **SOH-BBP-10-0** — ∀k,N≥1,∃n≥max(N,2):0<r_n/D^B_n+E_n−a<10^(−k).
- **BBP-V1** — ∀ℓ≥1,v,N≥1,∃n≥max(N,2):2η_n<10^(−ℓ)∧r_n/D^B_n∈J(v)^[−η_n].
- **P3** — ∃q,s,B>0,Z∈ℤ,(a_m),(n_j,L_j,h_j):the-displayed absolutely-summable,base-10^s,divisible-block,positive-tail conditions.
- **P4** — ∀α∈{π,√2,e,log2},δ∈{0,9},k≥1,∃a length-k decimal δ-run in α.
- **P5** — ∀N≥0:closure({y_n:n≥N})=[0,1],where y_(n+1)={16y_n+R(n)}.

## [Closed routes](knowledge/pi/workstreams/ATTEMPT_LEDGER.md)

- **route-generic-lacunary** — Generic premises select no fixed decimal target/diagonal.
- **route-bbp-rational-shadows** — The moving-modulus lift/oriented residue remains unknown.
- **route-bbp-base16** — The changing-modulus carry is the unknown digit.
- **route-machin-pade-carriers** — Positivity/approximation does not choose orientation or lift.
- **route-cm-modular** — Modular order is target-blind and restores the unresolved phase.
- **route-gamma-e-functions** — Multiplication retains zero-character data; reflection loses orientation.
- **route-theta-automorphic** — Reindexing degenerates/becomes unsigned; modular maps miss ×10.
- **route-new-kernels** — Cross-energy/equivalent consumers are not child-hereditary.
- **route-finite-prefix** — Finite signs are computed,not implied; continuations avoid targets.
- **route-coarse-statistics** — Coarse statistics lose phase and same-digit alignment.
- **route-zero-sector** — Scalar summaries retain all nine inverse-character remainders.
- **route-pair-dc1** — Nonzero gives no sign; uniform Pair/DC1 is false.
- **route-separate-marginals** — Separate witnesses lose the digit; one ray need not be disjunctive.
- **route-machin-37** — Long residue orbits give close pairs,not endpoint hits.
- **route-erdos-carry** — No Λ<256 reciprocal bound; signed tails lose positivity.
- **route-run-bounds** — Irrationality exponents bound existing runs,not occurrence/direction.
- **route-endpoint-coding** — Endpoint localization supplies no recurrence/sign/occurrence/dimension.

## Rules for new candidates

T189 is frozen as the finished consumer. A new candidate enters the active frontier only if all three tests hold:

1. it is false for a suitable word-avoiding replacement constant;
2. a named arithmetic property special to π makes it plausibly true for π;
3. it directly yields a prescribed target hit or the literal same-child signed horizon inequality.

**Separator first.** Before building a Lean rung, run the numerical word-avoider check on its premise.

## Pointers

[Index](knowledge/pi/INDEX.yaml) · [specification](knowledge/pi/workstreams/TARGET_SPECIFICATION_v1.md) · [ledger](knowledge/pi/workstreams/ATTEMPT_LEDGER.md) · [bounty](BOUNTY.md)
