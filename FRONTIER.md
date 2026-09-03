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
| T16 | machine-checked | `Theory.PiDigits.DecimalBoundaryWordObstruction.not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance` | It proves neither C1 nor its failure. |
| T17 | machine-checked | `Theory.PiDigits.PowerTenDiophantineReduction.not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine` | It does not prove the Diophantine premise or C1. |
| T69 | machine-checked | `Theory.PiDigits.T69FixedSixteenReturn.v1_iff_fixedSixteenReturn` | It proves neither the density premise nor the return. |
| T102 | machine-checked | `Theory.PiDigits.T102BBPKernelIntegral.intervalIntegral_bbpKernel` | It does not justify the BBP series interchange. |
| T104 | machine-checked | `Theory.PiDigits.T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi` | It gives no decimal-orbit distribution. |
| T128 | machine-checked | `Theory.PiDigits.BoundaryMatchedKernel.finite_decimalInterval_hit_of_boundary_explicit_smallness` | It proves no π-orbit cancellation. |
| T130 | machine-checked | `Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.normalized_boundary_lt_jackson` | It supplies no decimal-orbit cancellation. |
| T138 | machine-checked | `Theory.PiDigits.PrimitiveRayCoefficientGap.primitiveBoundaryLoad_pow_ten_lt_positiveBoundaryLoad_sub_gap` | It proves no π cancellation. |
| T139 | machine-checked | `Theory.PiDigits.PrimitiveRayBoundaryConsumer.piOrbit_hit_of_uniform_primitiveCancellation_pow_ten` | It does not prove either hypothesis. |
| T142 | machine-checked | `Theory.PiDigits.BoundaryCoefficientAbel.sampled_positiveBoundaryCoefficient_abel_lt` | It contains no endpoint theorem. |
| T143 | machine-checked | `Theory.PiDigits.BoundaryEndpointLayers.primitiveBoundaryEndpoint_eq_layer_terminal_sub_initial` | It gives no endpoint estimate. |
| T144 | machine-checked | `Theory.PiDigits.BoundaryLayerMass.boundaryLayerMass_pow_ten_eq` | It gives no orbit estimate. |
| T146 | machine-checked | `Theory.PiDigits.BoundaryPhaseTorusBounds.decimal_phase_distance_dichotomy` | It contains no endpoint consumer. |
| T147 | machine-checked | `Theory.PiDigits.BoundaryEndpointContraction.primitiveBoundaryEndpoint_norm_lt_two_budget_sub` | It does not control the primitive sum. |
| T148 | machine-checked | `Theory.PiDigits.ImprovedPrimitiveBoundaryConsumer.piOrbit_hit_of_improved_primitiveBoundary_smallness_pow_ten` | It does not prove the threshold. |
| T150 | machine-checked | `Theory.PiDigits.BoundaryKernelFloors.boundaryMinorant_re_gt_neg_eight_mul_sq_div` | It gives no orbit cancellation. |
| T151 | machine-checked | `Theory.PiDigits.BoundaryProjectedLayerFloor.divisibleBoundaryPolynomial_re_gt` | It supplies no recurrence. |
| T153 | machine-checked | `Theory.PiDigits.BoundaryRootGridNaturalConsumer.piOrbit_hit_of_rootGrid_primitiveBoundary_ge` | It does not prove that lower bound. |
| T156 | machine-checked | `Theory.PiDigits.BoundaryNaturalThresholdClosure.piOrbit_hit_of_primitiveBoundary_ge_neg_861` | It does not prove the primitive lower bound. |
| T157 | machine-checked | `Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPRat_five_val_eq` | It gives no digit hit or distribution. |
| T159 | machine-checked | `Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrime_val_eq_neg_one` | It gives no cancellation or occurrence. |
| T169 | machine-checked | `Theory.PiDigits.T169SingleRateMachinPhaseTransfer.norm_shiftedPositiveBoundaryPiScore_sub_machin_le` | It supplies no carrier cancellation. |
| T170 | machine-checked | `Theory.PiDigits.T170MachinFixedPointIntervals.pi_mem_decimalCylinder_100` | It proves no digit recurrence. |
| T172 | machine-checked | `Theory.PiDigits.PositiveLeftExtensionTransport.primitiveBoundaryFourierSum_leftExtension` | It does not select a prescribed child. |
| T173 | machine-checked | `Theory.PiDigits.T173MachinIntegerCertificate10015.pi_mem_decimalCylinder_10015` | It is finite and proves no distribution. |
| T174 | machine-checked | `Theory.PiDigits.FinitePrimitiveScoreIdentity.two_mul_primitiveBoundaryFourierSum_re_eq_finite_score` | It asserts no positive π score. |
| T175 | machine-checked | `Theory.PiDigits.T175DecimalSuffixCylinder.piOrbit_mem_certified_suffixCylinder` | It only replays a finite prefix. |
| T176 | machine-checked | `Theory.PiDigits.SignedBlockBellmanTransport.exists_leftExtension_prefix_bellman_gt` | It does not prescribe d or give root positivity. |
| T177 | machine-checked | `Theory.PiDigits.PredecessorDigitDFT.ten_mul_child_re_eq_zeroSector_add_nonzero` | It supplies no favorable digit sign. |
| T178 | machine-checked | `Theory.PiDigits.SignedPredecessorRay.exists_infinite_signed_predecessor_ray` | It does not give root positivity, natural horizons, or V1. |
| T179 | machine-checked | `Theory.PiDigits.PredecessorLagOneCorrelation.predecessorDigitSector_eq_lagOneCorrelation` | It is an identity, not a cancellation estimate. |
| T180 | machine-checked | `Theory.PiDigits.T180ReflectedTrigIntervalCore.checked_trig_bounds` | It contains no production payload. |
| T181 | machine-checked | `Theory.PiDigits.T181ReflectedIntervalArithmetic.checkDiv_sound` | It supplies no π-specific score. |
| T185 | machine-checked | `Theory.PiDigits.T185BoundaryMinorantSineBridge.two_mul_primitiveBoundaryFourierSum_re_eq_closed_sine_score` | It has no numerical payload or sign. |
| T187 | machine-checked | `Theory.PiDigits.T187ReflectedTrigShard9965.shard_sound` | It is one finite shard, not the full score. |
| T189 | machine-checked | `Theory.PiDigits.SignedHorizonSectorBridge.signedPrefixSurplus_child_pos_of_horizon_sector_gt` | It proves no π-specific sector inequality. |
| T190 | machine-checked | `Theory.PiDigits.T190ComplementaryRankAlignment.exists_digit_D_pos_and_G_add_D_pos_of_complementary_card` | It supplies neither rank premise. |
| T191 | machine-checked | `Theory.PiDigits.T191CentralBoundaryKernelFloor.boundaryMinorant_re_gt_4859_div_10000` | It contains no orbit or cancellation premise. |
| T192 | machine-checked | `Theory.PiDigits.T192PrimitiveValuationShells.primitiveValuationShell_zero_re_gt` | It does not estimate positive shells. |
| T193 | machine-checked | `Theory.PiDigits.T193PositiveValuationShellAggregate.central_unitBlock_surplus_gt_three_div_twenty` | It contains no recurrence or timing input. |
| T194 | machine-checked | `Theory.PiDigits.T194CentralPiReturnSeed.exists_central_pi_unitBlock_surplus` | The target is unprescribed and no timing or ray follows. |
| T198 | machine-checked | `Theory.PiDigits.T198MachinBracketPack.machinMC0_iff_piCW0` | It proves neither MC0 nor CW0. |
| T199 | machine-checked | `Theory.PiDigits.T199BBPShadowPack.bbp10_soh0_iff_piCW0` | It proves neither CW0 nor CW9. |
| T200 | machine-checked | `Theory.PiDigits.T200BaileyCrandallCoboundary.Y_add_tau_eq_pow_mul_pi` | It proves no base-16 density or occurrence. |
| T202 | machine-checked | `Theory.PiDigits.T202RamanujanDyadicRamp.lambda_prefix_ramp` | It supplies neither a positive tail nor a target hit. |
| T204 | machine-checked | `Theory.PiDigits.T204ConstantRunBound.measureBelow_implies_exponentAtMost`<br>`Theory.PiDigits.T204ConstantRunBound.nineRun_eventually_bounded` | The zero-run mirror and every run-existence claim remain open. |
| T206 | machine-checked | `Theory.PiDigits.T206EndpointBridge.CWord_symmDiff_KWordReal_subset_E10` | It proves no occurrence, density, or prefix-cylinder analogue. |

## [Open problems](knowledge/pi/workstreams/OPEN_PROBLEMS.md)

- **P1-FD** — For every (m,w,A,c)∈𝔓₁, dim_H(C_w∩BA∩ALA_(A,c))=d_w.
- **P1-PD** — For every (m,w,A,c)∈𝔓₁, dim_H(C_w∩BA∩ALA_(A,c))>0.
- **P1-NE** — For every (m,w,A,c)∈𝔓₁, C_w∩BA∩ALA_(A,c) is nonempty.
- **P1-FD-loc** — For every (m,w,A,c)∈𝔓₁ and finite P with C_w∩I(P) nonempty, dim_H(X(w,A,c)∩I(P))=d_w.
- **P1′** — For every nonempty one-sided base-b SFT, every sparse entropy-neutral forced-block datum, and 0<s<d_Σ, some κ>0 gives dim_H(K_(Σ,F)∩BA(κ))≥s.
- **MC0** — For every k≥1, some m,n≥0 satisfy 10^k R^M_(m,n)+10^(n+k)Δ_m<D^M_m.
- **SOH-3/7** — For every k,M≥1, some m≥M and n≥0 satisfy 10^k R^M_(m,n)+10^(n+k)Δ_m<D^M_m.
- **SOH-BBP-10-0** — For every k,N≥1, some n≥max(N,2) satisfies 0<r_n/D^B_n+E_n−a<10^(−k).
- **BBP-V1** — For every length ℓ≥1, word v, and N≥1, some n≥max(N,2) has 2η_n<10^(−ℓ) and r_n/D^B_n in the η_n-shrunken arc J(v).
- **P3** — There exist q,s,B>0, Z∈ℤ, absolutely summable integer coefficients, and increasing blocks with B=10^s, π/q=Z+Σa_mB^(−m), h_j→∞, block divisibility, and tail in (0,B^(−h_j)).
- **P4** — For every α∈{π,√2,e,log 2} and δ∈{0,9}, every k≥1 occurs as a length-k decimal δ-run in α.
- **P5** — For every N≥0, the closure of {y_n:n≥N} for y_(n+1)={16y_n+R(n)} is [0,1].

## [Closed routes](knowledge/pi/workstreams/ATTEMPT_LEDGER.md)

- **route-generic-lacunary** — Generic central capital, mixed recurrence, finite irrationality exponent, and escaping-offset equidistribution do not select a fixed decimal target or diagonal branch.
- **route-bbp-rational-shadows** — Valuations, positive tails, filters, and rational shadows leave the moving-modulus integer lift and oriented residue unknown.
- **route-bbp-base16** — The changing-modulus carry is exactly the unknown digit, with one canonical numerator and no averaging variable.
- **route-machin-pade-carriers** — Approximation and coefficient positivity do not sign the target-rotated distinguished embedding or choose the integer lift.
- **route-cm-modular** — Root order and modular identities retain a target-blind dominant real direction; correction restores the original unresolved decimal phase.
- **route-gamma-e-functions** — Multiplication controls only the zero character; reflection restores target characters as recodings with unresolved orientation.
- **route-theta-automorphic** — Reindexing degenerates or becomes unsigned, and no rational modular map realizes decimal multiplication with target orientation.
- **route-new-kernels** — Cross-energy and equivalent consumers are not hereditary along legal children.
- **route-finite-prefix** — The full fresh sign is computed rather than implied, and any finite prefix admits target-avoiding transcendental continuations.
- **route-coarse-statistics** — Coarse statistics lose relative multi-sector phase and same-digit alignment.
- **route-zero-sector** — All nine inverse characters survive scalar endpoint potentials, and scalar summaries cannot eliminate their joint remainder.
- **route-pair-dc1** — Formal nonzero gives no sign; uniform Pair/DC1 and convex-mask transport fail on the tested completion space.
- **route-separate-marginals** — Separate witnesses lose the common digit, and one coherent ray need not be disjunctive.
- **route-machin-37** — A long invertible residue orbit gives close pairs, not a one-sided endpoint hit.
- **route-erdos-carry** — No bound |ρ_n|≤CΛ^n with Λ<256 is proved, and signed reciprocal coefficients remove automatic positive tails.
- **route-run-bounds** — An irrationality exponent bounds a run only if it exists and does not select zero or nine.
- **route-endpoint-coding** — Endpoint localization removes coding ambiguity but supplies no recurrence, sign, occurrence, or dimension mechanism.

## Rules for new candidates

T189 is frozen as the finished consumer. A new candidate enters the active frontier only if all three tests hold:

1. it is false for a suitable word-avoiding replacement constant;
2. a named arithmetic property special to π makes it plausibly true for π;
3. it directly yields a prescribed target hit or the literal same-child signed horizon inequality.

**Separator first.** Before building a Lean rung, run the numerical word-avoider check on its premise.

## Pointers

[Index](knowledge/pi/INDEX.yaml) · [specification](knowledge/pi/workstreams/TARGET_SPECIFICATION_v1.md) · [ledger](knowledge/pi/workstreams/ATTEMPT_LEDGER.md) · [bounty](BOUNTY.md)
