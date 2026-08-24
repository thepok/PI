# Negative-results index

This directory records routes that were explicitly falsified or reduced to a
durable obstruction. These artifacts prevent future workers from repeatedly
spending tokens on the same dead ends.

- `ultrapi/bbp_fiber_matching_no_go*`: failed fiber-matching route with replay checks.
- `bbp_three_adic_fiber_archimedean_density_no_go_20260821.md`:
  reviewed same-fiber density separator; finite three-adic BBP residue data
  cannot constrain the real decimal phase without exact numerator/denominator
  or coefficient coupling.
- `20260824-bbp-universal-grid-period-shadow-no-go.md`: audited BBP
  denominator-and-remainder obstruction; surviving primes make the universal
  decimal-grid certificate cover asymptotically at most a
  `log(4)-1 < 1` fraction of one rational period, while the exact archived
  two-adic denominator formula makes every post-preperiod one-sided
  magnitude-only radius full-circle for every `K >= 3`.  Exact tail phase and
  signed carry/Fourier cancellation remain outside its scope.
- `20260824-scalar-uniform-coboundary-carry-budget-no-go.md`: a fixed-point
  obstruction forces every pointwise scalar coboundary residual above the
  carry budget, although explicit ray spreading makes its `L2` norm
  arbitrarily small.
- `20260824-ten-channel-branch-average-pathwise-separator.md`: the exact
  fixed path `x_n = 4/9` keeps every true carry character fully coherent even
  though the corresponding Fejer branch-average operator has a strict
  zero-sum spectral gap; cyclic-label-invariant contraction data therefore do
  not control a prescribed pathwise carry class.
- `appearance_ratio_route_no_go_20260821.md`: reviewed scoped separator for
  the T28–T29 route; even optimal appearance ratio leaves a constant bound on
  a moving selected frequency set, and maximal recurrent language/entropy does
  not control first-appearance delay.
- `t116_raw_gcd_small_support_bounds_no_go_20260821.md`: exact canonical
  sampled-BBP census rejecting raw-gcd prime-support, divisibility-by-10, and
  uniform-size hypotheses; records the marker-gate false positive and the
  normalized excess-gcd direction that remains open.
- `t117_unscaled_q_workflow_false_positive_20260821.md`: rejects an Ox
  normalized-census artifact whose generator and verifier both omitted the
  required `10^N` scaling in `Q_N`; records the exact guard and independent
  endpoint checks now required before any T117 census may run.
- `20260822-t136-three-growth-scalar-kernel-and-census.md`: proves at
  proof-sketch level that one exact entry-eliminating scalar relation cannot
  obstruct independent literal BAD arcs, and records an exact 64-base
  experiment in which the last-three-growth cylinder excludes both canonical
  and comparator entries, providing no transversality diagnostic.
- `20260822-t137-tail-origin-gauge-q-balance.md`: derives the exact tail-origin
  Q-balance/leakage criterion and closes nonnegative same-jump signed-variation
  arguments on an unbounded four-jump family, within a carefully limited
  finite-window affine/conic proof class; mixed-jump balance remains open.
- `20260822-t138-plucker-normal-form-and-content-census.md`: reduces each
  fixed-numeric-Q minor algebra to seven translated carry coordinates and
  exactly falsifies a universal nonunit raw-minor-content claim on both known
  five-checkpoint all-BAD runs; the symbolic weighted class remains open.
- `ultrapi/bbp_odd_lcm_carry_no_go*`: failed odd-LCM carry route with independent audit.
- `ultrapi/machin_chebotarev_anchor_obstruction*`: obstruction to the proposed Chebotarev anchor.
- `ultrapi/*adversarial*`: adversarial checks against fixed-modulus and multiprime routes.

These are research records, not Lean theorems unless a corresponding declaration
also appears in `TheoryLib/` and the axiom audit.
