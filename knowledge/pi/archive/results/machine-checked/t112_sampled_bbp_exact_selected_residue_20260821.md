# T112 sampled-BBP exact selected residue

Status: `machine-checked`

Canonical source:
`TheoryLib/PiQuantitativeBlockHitting/T112T112SampledBBPSelectedResidue.lean`

Canonical SHA-256:
`151b84e1f4d2d502d92568887cad631713ae6ad2aad6b4c7bf86b30b4ecedca9`

## Result

For the synchronized rational

`q_N = 10^N * bbpPartial (7*N)`,

T112 proves four exact identities:

1. any rational circle point is represented by its reduced numerator modulo
   its full reduced denominator;
2. `sampledBBPOrbit N` is exactly that circle point for `q_N`;
3. every integer-frequency phase agrees with the selected-residue phase;
4. the full finite exponential sum is exactly the sum of those phases.

The same `N` and the same actual reduced rational are used throughout.  The
statements include negative rationals, `N = 0`, zero frequency, and the empty
sum without extra hypotheses.

## Verification and provenance

- The canonical proof was distilled from free Oxzen candidate SHA-256
  `622283cb485be06e479f8a7512018439c2ed5901216a368b0a6883f9c0552055`.
- Its recorded isolated gate log has SHA-256
  `4d1a01009949b49e6c68fc3f004a2764939ad842e6b452637424dd3cb02e3e0c`.
- A second independently produced candidate later passed its isolated gate
  (artifact SHA-256
  `c237e596a54ce0023981bbf5b76fbe72348eccf029b0e9e0c891d3ad5d62cf0b`;
  gate-log SHA-256
  `cfc1bcd4287f768f63af4b037e95ba76d3d9bb63aacac766cedf0d1c407905d0`).
  It was not selected because it was longer and exposed an unnecessary public
  theorem.
- Independent semantic review checked exact synchronization, true reduced
  numerator/denominator semantics, and the edge cases above.
- The canonical source removes two private circle-lifting lemmas by reusing
  mathlib's `AddCircle.coe_fract`.
- All four public declarations are registered in `audit/AxiomAudit.lean`.
- `pwsh workflows/verification/check.ps1` passed on 2026-08-21: the full
  kernel build, exploit scan, and exact-allowlist axiom audit all succeeded.

## Boundary

This is an exact representation interface, not a cancellation estimate.  It
does not bound a Fourier sum, hit a mesh cell, prove orbit density, or imply
V1.  Its purpose is to ensure that subsequent work retains precisely the
numerator/denominator information that finite residue-fiber replacements lose.
