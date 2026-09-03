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
4. Theorem A of the separator article (`proof sketch`, not Lean) gives badly approximable transcendental word-avoiders with irrationality exponent 2.
5. Such avoiders share the finite-exponent and central-return premises used by T191–T194.
6. Exact identities, rational shadows, positive errors, valuations, and unsigned energies can also retain the missing orientation.
7. Finite computation can falsify or refine a route but cannot prove an unbounded word-occurrence claim.
8. Therefore separator-first testing precedes construction of any new Lean rung.
9. Every candidate must identify exactly where actual-π target-signed information enters.
10. A premise shared by a recorded digit-avoider cannot prove V1.

## Machine-checked status (generated from INDEX.yaml)

| ID | Label | Lean name | What it does not show |
|---|---|---|---|
| T16 | machine-checked | `Theory.PiDigits.DecimalBoundaryWordObstruction.not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance` | Not-proved:C1-or-¬C1. |
| T17 | machine-checked | `Theory.PiDigits.PowerTenDiophantineReduction.not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine` | Not-proved:Diophantine-premise-or-C1. |
| T69 | machine-checked | `Theory.PiDigits.T69FixedSixteenReturn.v1_iff_fixedSixteenReturn` | Not-proved:density-or-return. |
| T102 | machine-checked | `Theory.PiDigits.T102BBPKernelIntegral.intervalIntegral_bbpKernel` | Not-proved:series-interchange. |
| T104 | machine-checked | `Theory.PiDigits.T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi` | Not-proved:digit-distribution. |
| T128 | machine-checked | `Theory.PiDigits.BoundaryMatchedKernel.finite_decimalInterval_hit_of_boundary_explicit_smallness` | Not-proved:π-cancellation. |
| T130 | machine-checked | `Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.normalized_boundary_lt_jackson` | Not-proved:π-cancellation. |
| T138 | machine-checked | `Theory.PiDigits.PrimitiveRayCoefficientGap.primitiveBoundaryLoad_pow_ten_lt_positiveBoundaryLoad_sub_gap` | Not-proved:π-cancellation. |
| T139 | machine-checked | `Theory.PiDigits.PrimitiveRayBoundaryConsumer.piOrbit_hit_of_uniform_primitiveCancellation_pow_ten` | Not-proved:its-hypotheses. |
| T142 | machine-checked | `Theory.PiDigits.BoundaryCoefficientAbel.sampled_positiveBoundaryCoefficient_abel_lt` | Not-proved:endpoint-theorem. |
| T143 | machine-checked | `Theory.PiDigits.BoundaryEndpointLayers.primitiveBoundaryEndpoint_eq_layer_terminal_sub_initial` | Not-proved:endpoint-bound. |
| T144 | machine-checked | `Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass_pow_ten_eq` | Not-proved:orbit-estimate. |
| T146 | machine-checked | `Theory.PiDigits.BoundaryPhaseTorusBounds.decimal_phase_distance_dichotomy` | Not-proved:endpoint-consumer. |
| T147 | machine-checked | `Theory.PiDigits.BoundaryEndpointContraction.primitiveBoundaryEndpoint_norm_lt_two_budget_sub` | Not-proved:primitive-sum-bound. |
| T148 | machine-checked | `Theory.PiDigits.ImprovedPrimitiveBoundaryConsumer.piOrbit_hit_of_improved_primitiveBoundary_smallness_pow_ten` | Not-proved:threshold. |
| T150 | machine-checked | `Theory.PiDigits.BoundaryKernelFloors.boundaryMinorant_re_gt_neg_eight_mul_sq_div` | Not-proved:orbit-cancellation. |
| T151 | machine-checked | `Theory.PiDigits.BoundaryProjectedLayerFloor.divisibleBoundaryPolynomial_re_gt` | Not-proved:recurrence. |
| T153 | machine-checked | `Theory.PiDigits.BoundaryRootGridNaturalConsumer.piOrbit_hit_of_rootGrid_primitiveBoundary_ge` | Not-proved:lower-bound. |
| T156 | machine-checked | `Theory.PiDigits.BoundaryNaturalThresholdClosure.piOrbit_hit_of_primitiveBoundary_ge_neg_861` | Not-proved:primitive-bound. |
| T157 | machine-checked | `Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPRat_five_val_eq` | Not-proved:occurrence. |
| T159 | machine-checked | `Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrime_val_eq_neg_one` | Not-proved:cancellation. |
| T169 | machine-checked | `Theory.PiDigits.T169SingleRateMachinPhaseTransfer.norm_shiftedPositiveBoundaryPiScore_sub_machin_le` | Not-proved:carrier-cancellation. |
| T170 | machine-checked | `Theory.PiDigits.T170MachinFixedPointIntervals.pi_mem_decimalCylinder_100` | Not-proved:recurrence. |
| T172 | machine-checked | `Theory.PiDigits.PositiveLeftExtensionTransport.primitiveBoundaryFourierSum_leftExtension` | Not-proved:prescribed-child. |
| T173 | machine-checked | `Theory.PiDigits.T173MachinIntegerCertificate10015.pi_mem_decimalCylinder_10015` | Not-proved:distribution. |
| T174 | machine-checked | `Theory.PiDigits.FinitePrimitiveScoreIdentity.two_mul_primitiveBoundaryFourierSum_re_eq_finite_score` | Not-proved:positive-π-score. |
| T175 | machine-checked | `Theory.PiDigits.T175DecimalSuffixCylinder.piOrbit_mem_certified_suffixCylinder` | Only-proved:finite-replay. |
| T176 | machine-checked | `Theory.PiDigits.SignedBlockBellmanTransport.exists_leftExtension_prefix_bellman_gt` | Not-prescribed:digit-or-root-positivity. |
| T177 | machine-checked | `Theory.PiDigits.PredecessorDigitDFT.ten_mul_child_re_eq_zeroSector_add_nonzero` | Not-proved:favorable-sign. |
| T178 | machine-checked | `Theory.PiDigits.SignedPredecessorRay.exists_infinite_signed_predecessor_ray` | Not-proved:root-positivity/natural-horizon/V1. |
| T179 | machine-checked | `Theory.PiDigits.PredecessorLagOneCorrelation.predecessorDigitSector_eq_lagOneCorrelation` | Not-proved:cancellation. |
| T180 | machine-checked | `Theory.PiDigits.T180ReflectedTrigIntervalCore.checked_trig_bounds` | Not-provided:production-payload. |
| T181 | machine-checked | `Theory.PiDigits.T181ReflectedIntervalArithmetic.checkDiv_sound` | Not-proved:π-score. |
| T185 | machine-checked | `Theory.PiDigits.T185BoundaryMinorantSineBridge.two_mul_primitiveBoundaryFourierSum_re_eq_closed_sine_score` | Not-provided:payload-or-sign. |
| T187 | machine-checked | `Theory.PiDigits.T187ReflectedTrigShard9965.shard_sound` | Not-provided:full-score. |
| T189 | machine-checked | `Theory.PiDigits.SignedHorizonSectorBridge.signedPrefixSurplus_child_pos_of_horizon_sector_gt` | Not-proved:π-sector-premise. |
| T190 | machine-checked | `Theory.PiDigits.T190ComplementaryRankAlignment.exists_digit_D_pos_and_G_add_D_pos_of_complementary_card` | Not-proved:rank-premises. |
| T191 | machine-checked | `Theory.PiDigits.T191CentralBoundaryKernelFloor.boundaryMinorant_re_gt_4859_div_10000` | Not-proved:orbit-premise. |
| T192 | machine-checked | `Theory.PiDigits.T192PrimitiveValuationShells.primitiveValuationShell_zero_re_gt` | Not-proved:positive-shells. |
| T193 | machine-checked | `Theory.PiDigits.T193PositiveValuationShellAggregate.central_unitBlock_surplus_gt_three_div_twenty` | Not-proved:recurrence/timing. |
| T194 | machine-checked | `Theory.PiDigits.T194CentralPiReturnSeed.exists_central_pi_unitBlock_surplus` | Not-proved:target/timing/ray. |
| T198 | machine-checked | `Theory.PiDigits.T198MachinBracketPack.machinMC0_iff_piCW0` | Not-proved:MC0-or-CW0. |
| T199 | machine-checked | `Theory.PiDigits.T199BBPShadowPack.bbp10_soh0_iff_piCW0` | Not-proved:CW0-or-CW9. |
| T200 | machine-checked | `Theory.PiDigits.T200BaileyCrandallCoboundary.Y_add_tau_eq_pow_mul_pi` | Not-proved:base-16-density. |
| T202 | machine-checked | `Theory.PiDigits.T202RamanujanDyadicRamp.lambda_prefix_ramp` | Not-proved:positive-tail/target. |
| T204 | machine-checked | `Theory.PiDigits.T204ConstantRunBound.measureBelow_implies_exponentAtMost`<br>`Theory.PiDigits.T204ConstantRunBound.nineRun_eventually_bounded` | Not-proved:zero-run-bound/run-existence. |
| T206 | machine-checked | `Theory.PiDigits.T206EndpointBridge.CWord_symmDiff_KWordReal_subset_E10` | Not-proved:occurrence/density/prefix-analogue. |

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

- **route-generic-lacunary** — Missing:fixed-target/diagonal-selection.
- **route-bbp-rational-shadows** — Missing:oriented-moving-modulus-lift.
- **route-bbp-base16** — Missing:canonical-carry-digit-control.
- **route-machin-pade-carriers** — Missing:orientation/integer-lift-selection.
- **route-cm-modular** — Missing:target-character-orientation.
- **route-gamma-e-functions** — Missing:reflected-character-orientation.
- **route-theta-automorphic** — Missing:oriented-decimal-modular-branch.
- **route-new-kernels** — Missing:child-heredity.
- **route-finite-prefix** — Missing:fresh-unbounded-π-information.
- **route-coarse-statistics** — Missing:phase/same-digit-alignment.
- **route-zero-sector** — Missing:joint-inverse-character-control.
- **route-pair-dc1** — Missing:evaluated-sign/pathwise-admissibility.
- **route-separate-marginals** — Missing:joint-digit/word-coverage.
- **route-machin-37** — Missing:one-sided-endpoint-hit.
- **route-erdos-carry** — Missing:Λ<256-bound/positive-tail.
- **route-run-bounds** — Missing:run-occurrence/direction.
- **route-endpoint-coding** — Missing:recurrence/sign/occurrence/dimension.

## Rules for new candidates

T189 is frozen as the finished consumer. A new candidate enters the active frontier only if all three tests hold:

1. it is false for a suitable word-avoiding replacement constant;
2. a named arithmetic property special to π makes it plausibly true for π;
3. it directly yields a prescribed target hit or the literal same-child signed horizon inequality.

**Separator first.** Before building a Lean rung, run the numerical word-avoider check on its premise.

## Pointers

[Index](knowledge/pi/INDEX.yaml) · [specification](knowledge/pi/workstreams/TARGET_SPECIFICATION_v1.md) · [ledger](knowledge/pi/workstreams/ATTEMPT_LEDGER.md) · [bounty](BOUNTY.md)
