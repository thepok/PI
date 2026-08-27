# T117 common-denominator and excess-gcd decomposition

Status: `machine-checked`

Date: 2026-08-21 UTC

Canonical source:
[`T117T117CommonDenominatorExcessGCD.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T117T117CommonDenominatorExcessGCD.lean)

For reduced integer/natural pairs `(A,D)` and `(C,E)`, put
`H=gcd(D,E)`, `d=D/H`, `e=E/H`,
`X=10*A*e+C*d`, `U=10*A*E+C*D`, `V=D*E`,
`k=gcd(X,H*d)`, and `g=gcd(U,V)`. T117 proves exactly

- `U=H*X` and `V=H^2*d*e`;
- `g=H*k`, preserving the excess factor with its valuations;
- `k ∣ D` and `k ∣ 10*H`;
- `V/g=H*d*e/k=D*e/k`.

The generic theorem includes zero denominators. Its `H=0` branch explicitly
reduces `D=E=d=e=X=U=V=k=g=0`; the helper coprimality statements use the
necessary hypothesis `0<H`.

The audited candidate and the exact gate-appended type checks compiled
directly against the canonical tree with only the accepted axiom footprint.
The candidate's stored isolated-gate attempt failed while copying its
environment because that temporary filesystem was full; it is not recorded
as a successful isolated gate. After integration,
`workflows/verification/check.ps1` passed its kernel build, exploit scan, and
exact-allowlist axiom audit.

This is exact rational arithmetic only. It proves no bound on `k`, no
cancellation, cell occupancy, density, normality, V1, or decimal-word
occurrence. Any successor must control the normalized numerator across
indices, rather than continue denominator-only bookkeeping.
