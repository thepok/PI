# Negative-results index

This directory records routes that were explicitly falsified or reduced to a
durable obstruction. These artifacts prevent future workers from repeatedly
spending tokens on the same dead ends.

- `ultrapi/bbp_fiber_matching_no_go*`: failed fiber-matching route with replay checks.
- `bbp_three_adic_fiber_archimedean_density_no_go_20260821.md`:
  reviewed same-fiber density separator; finite three-adic BBP residue data
  cannot constrain the real decimal phase without exact numerator/denominator
  or coefficient coupling.
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
- `ultrapi/bbp_odd_lcm_carry_no_go*`: failed odd-LCM carry route with independent audit.
- `ultrapi/machin_chebotarev_anchor_obstruction*`: obstruction to the proposed Chebotarev anchor.
- `ultrapi/*adversarial*`: adversarial checks against fixed-modulus and multiprime routes.

These are research records, not Lean theorems unless a corresponding declaration
also appears in `TheoryLib/` and the axiom audit.
