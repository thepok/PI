# Negative-results index

This directory records routes that were explicitly falsified or reduced to a
durable obstruction. These artifacts prevent future workers from repeatedly
spending tokens on the same dead ends.

- `ultrapi/bbp_fiber_matching_no_go*`: failed fiber-matching route with replay checks.
- `ultrapi/bbp_odd_lcm_carry_no_go*`: failed odd-LCM carry route with independent audit.
- `ultrapi/machin_chebotarev_anchor_obstruction*`: obstruction to the proposed Chebotarev anchor.
- `ultrapi/*adversarial*`: adversarial checks against fixed-modulus and multiprime routes.

These are research records, not Lean theorems unless a corresponding declaration
also appears in `TheoryLib/` and the axiom audit.
