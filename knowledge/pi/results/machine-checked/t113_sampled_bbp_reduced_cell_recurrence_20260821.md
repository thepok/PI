# T113 sampled-BBP reduced-cell recurrence

Status: `machine-checked`

Canonical source:
`TheoryLib/PiQuantitativeBlockHitting/T113T113SampledBBPReducedCellRecurrence.lean`

Canonical SHA-256:
`1ae6b4f775380d3cd4e087ea87655d5b3609333797021eee3c763caffc7ac76b`

## Result

For the synchronized reduced rational

`Q_N = 10^N * bbpPartial (7*N)`, 

T113 proves three exact identities:

1. `Q_(N+1) = 10*Q_N + sampledBBPForcingRat N`;
2. that forcing is exactly the next seven BBP terms, each written as one
   rational fraction over the four-pole denominator; and
3. for every natural modulus `q`, the cyclic cell of `sampledBBPOrbit N` is
   exactly
   `((q * (Q_N.num mod Q_N.den)) / Q_N.den) mod q`.

The third theorem uses the actual normalized numerator and positive
denominator supplied by Lean's rational type.  Its generic supporting identity
was checked for arbitrary signed numerators and also covers `q = 0`, `N = 0`,
and integral rationals without extra hypotheses.

## Verification and provenance

- The two successor identities were retained from a free Oxzen candidate with
  artifact SHA-256
  `ad080d9b65524ec99f10e16d9e10e0bd1fa551f4a622d083ecddc1c5574420c7`
  and isolated gate-log SHA-256
  `6986d68f0382623c6dde8a15aa81adb9f93008372663dcd79ceb78ecff0a0d8a`.
- The cell bridge was independently synthesized from two passing free-model
  candidates.  One retained candidate has artifact SHA-256
  `f727f168b65244b9003fcd967557a0bceb7f9fac02eae60d69c452117a06515`
  and isolated gate-log SHA-256
  `88621e2a08f6215fcf6c467e1e61cdc59e7a246aa8d3b2f7e679b0e49cfb3bae`.
- Independent integration review simplified the cell bridge to two private
  helpers and one public theorem, and checked the sign, cast, floor, modulus,
  and synchronization edge cases.
- All three public declarations are registered in `audit/AxiomAudit.lean`.
- `pwsh workflows/verification/check.ps1` passed on 2026-08-21: all 8,767
  kernel build jobs, the exploit scan, and the exact-allowlist axiom audit
  succeeded.

## Boundary

This is exact arithmetic infrastructure, not an orbit-distribution estimate.
It identifies the concrete reduced rational state and its observed cell but
does not prove that any cell is hit, control the gcd in the next normalized
state, bound a character sum, establish density, or imply V1.  The next
non-tautological frontier is the cancellation structure in the reduced
numerator/denominator successor, rather than another reformulation of cell
occupancy.
