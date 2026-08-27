# T116 sampled-BBP normalization-gcd prime support

Status: `machine-checked`

Canonical source:
`TheoryLib/PiQuantitativeBlockHitting/T116T116SampledBBPGCDPrimeSupport.lean`

Canonical SHA-256:
`c73a7368d4015e7122cbb319abf78d8cc07421c4d1ae9894099b13eef91bbfd3`

## Result

For reduced integer/natural pairs `(A,D)` and `(C,E)`, put
`U = 10*A*E + C*D` and `V = D*E`. T116 proves that every prime `p` dividing
`gcd(U,V)` satisfies `p ∣ D` and (`p ∣ E` or `p ∣ 10`).

It specializes this statement to the actual reduced rationals
`Q_N = 10^N*bbpPartial(7N)` and `F_N = sampledBBPForcingRat N` using the
genuine `Q_N.reduced` and `F_N.reduced` invariants. Thus any off-base prime in
the T114 normalization gcd must be shared by the two full reduced
denominators. Signed and zero numerators, `N=0`, and primes 2 and 5 need no
extra hypotheses.

## Verification and provenance

- Free Ox artifact SHA-256:
  `4aef03cf868786d30782cc1403951ac0d3c0b69d2926f99a17bb7886ae14c317`.
- Isolated pod gate SHA-256:
  `cfcb32302e4d061848179bfbc44aadc70168caa893ff548c47fbd3cc8fca90a6`.
- Independent integration review checked the frozen signatures,
  reduced-rational specialization, divisibility transports, imports, and
  edge cases; an independent compile passed.
- Both public declarations are registered in `audit/AxiomAudit.lean`.
- `pwsh workflows/verification/check.ps1` passed on 2026-08-21: all 8,770
  kernel build jobs, the exploit scan, and the exact-allowlist axiom audit
  succeeded.

## Boundary

This is a support lemma, not a useful size estimate alone. It permits
off-base primes shared by `Q_N.den` and `F_N.den`, which the exact census finds
immediately. It proves no gcd-size or valuation bound, cancellation estimate,
cell hit, occupancy, density, C1, V1, normality, or decimal-digit conclusion.
