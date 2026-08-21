# T117 common-denominator/excess-gcd guidance

Work skeptically on the exact reduced-pair algebra after T116.  Do not infer
size, occupancy, density, or V1 claims.

For signed numerators `A,C` and natural denominators `D,E`, define
`H=gcd D E`, `d=D/H`, `e=E/H`,
`X=10*A*e+C*d`, `U=10*A*E+C*D`, `V=D*E`,
`k=Int.gcd X (H*d)`, and `g=Int.gcd U V` with the exact casts in the binding
contract. Prove the complete decomposition `U=H*X`, `V=H^2*d*e`, `g=H*k`,
`k|D`, `k|10H`, and both exact quotient identities.

The generic contract deliberately permits zero denominators. Split `H=0`
explicitly. When `D=E=0`, all H/d/e/X/U/V/k/g values are zero under Lean's
natural division conventions. If exactly one denominator is zero, reducedness
forces the matching numerator absolute value to be one. Do not silently add
positivity assumptions or replace the contracted theorem with a Rat-only one.

In the positive-H branch, prove `D=H*d`, `E=H*e`, `Coprime d e`, and that X
is coprime to e. Remove e from `gcd(X,H*d*e)`. Preserve valuations through
the exact `g=H*k`; T116's prime-support statement alone is insufficient.

For the normalized census workflow, K1 is `k^2≤e` and K2 is `k^2≤d*e`.
Neither is a theorem. One exact witness rejects a law; finite survival remains
only `experiment`. Preserve the canonical inclusive `bbpPartial` convention
and the anchor `Q_0=47/15`. Controller-pinned code and checkpoint hashes, not
pod self-reports, define the trust boundary. The full range is partitioned
before inspection into exactly 42 half-open shards covering `[512,4096)`.
