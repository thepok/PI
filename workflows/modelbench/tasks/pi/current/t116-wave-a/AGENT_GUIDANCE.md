# T116 gcd-support and exact-census guidance

Work skeptically. This wave must test actual arithmetic structure after T115;
do not add another representation identity.

For Lean, the binding claim is a prime-support restriction on the precise
cross-normalization gcd. From reduced pairs `(A,D)` and `(C,E)`, use
`U = 10*A*E + C*D`, `V = D*E`, and the exact `Int.gcd U V`. A prime in this
gcd must divide `D`, and it must divide either `E` or `10`. Preserve signs and
full denominators. Cross multiplication, existence of an unspecified factor,
or a claim only about 2/5-adic valuations is insufficient.

For the census, use one exact canonical generator and one independent verifier.
Freeze discovery at N=0..255 and holdout at N=256..511. Compute actual reduced
`Q_N`, actual reduced forcing `F_N`, raw `U_N,V_N`, and exact `g_N`; never use
floating-point approximations or unreduced shadow pairs. Record prime-source
classes and cancellation ratios. One exact counterexample rejects a proposed
universal law. Finite survival is only `experiment`, never a proof.

Reject same-fiber replacements, marginal CRT data, numerator-only or
denominator-only projections, Parseval/energy proxies, post-hoc exception
lists, finite-to-asymptotic upgrades, and any occupancy/density/V1 claim.
