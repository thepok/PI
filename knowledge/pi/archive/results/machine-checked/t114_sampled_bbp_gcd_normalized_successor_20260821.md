# T114 sampled-BBP gcd-normalized successor

Status: `machine-checked`

Canonical source:
`TheoryLib/PiQuantitativeBlockHitting/T114T114SampledBBPGCDNormalizedSuccessor.lean`

Canonical SHA-256:
`4a0a9502aba631ebeaa91df08a0b94866ed76a9584a508385b66008efe01b78c`

## Result

Let `Q_N = 10^N*bbpPartial(7N)` and let `F_N` be the exact seven-term
sampled forcing from T106.  From their actual reduced pairs define

`U_N = 10*Q_N.num*F_N.den + F_N.num*Q_N.den`,

`V_N = Q_N.den*F_N.den`, and `g_N = gcd(U_N,V_N)`.

T114 proves that the actual reduced pair at the next sample is exactly

`Q_(N+1).num = U_N/g_N` and `Q_(N+1).den = V_N/g_N`.

It then substitutes this normalized pair into T113 and obtains an exact
formula for `cyclicCell q (sampledBBPOrbit (N+1))`.  Thus the next observed
cell visibly depends on the cross-coupled numerator and its full cancellation
with the product denominator.  The generic normalization handles signed and
zero raw numerators; positivity of the rational denominators prevents division
by zero.

## Verification and provenance

- A free Ox candidate passed its isolated compiler and axiom gate on its first
  attempt (artifact SHA-256
  `e55ce28a46cf15987f074e0f6d4b22309398e2e5f1443b28dd723dc9acf7758c`;
  gate-log SHA-256
  `f5bac07636486490ea70ca2949273dc8cf7c872113aca5bc32bb58e628b725f3`).
- An independent free Oxzen candidate passed after three attempts (artifact
  SHA-256
  `72fd8d595af3da291a35fbe1d012ec58ce312749afe09b12a5227a92231941b5`;
  gate-log SHA-256
  `ea7f16067ef5bf5f05e300b2398e564de57412f9a07c1f94332a459705cfe8cf`).
- Independent integration review found and repaired a scoped-notation/cast
  weakness in an earlier Oxzen attempt, shortened the rational equality proof,
  checked the zero and negative-numerator cases, and added the next-cell
  corollary.  Its compiling replay had SHA-256
  `01626744965f7b6d89c38a7fd299bbcd0f1135afeeb043859ad1244a86aac100`.
- Both public T114 declarations are registered in `audit/AxiomAudit.lean`.
- `pwsh workflows/verification/check.ps1` passed on 2026-08-21: all 8,768
  kernel build jobs, the exploit scan, and the exact-allowlist axiom audit
  succeeded.

## Boundary

T114 exposes the exact cancellation factor; it proves no bound, pattern, or
recurrence for `g_N`.  The next-cell identity is still a representation, not
a cell hit.  Nothing here proves a character-sum estimate, occupancy, cover,
density, normality, C1, V1, or a decimal-digit result.  Further representation
work should stop after the exact floor-defect phase bridge unless it leads to
a falsifiable nontrivial property of this actual normalized sequence.
