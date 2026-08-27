# T110 post-T17 tail cancellation criterion

Status: `machine-checked`

Canonical source:
`TheoryLib/PiQuantitativeBlockHitting/T110T110PostT17CancellationCriterion.lean`

Canonical SHA-256:
`c37007545873098709a3fc118de3953c0499416a41cd02a8d764c5f74a92a25d`

## Result

Under the explicit premise `PowerTenDiophantine Real.pi mu A`, with
`1 ≤ mu` and `1 ≤ C`, T110 proves the strict tail contrapositive of T17.  If
T17's exact aggregated Fourier quantity is strictly below `N/(2*q)` at every
sufficiently large admissible scale, then `C1` holds.  All of T17's parameters
`mu`, `A`, `C`, `K`, `k`, `q`, `D`, `N`, `r`, and `M` remain explicit.

An arbitrary unbounded set of upper-bound scales is insufficient: it need not
meet T17's unbounded witness set.  Without extra structure on those witnesses,
an admissible tail is the sharp generic set-of-scales condition.  The upper
bound must also be strict because T17's obstruction is non-strict in the
opposite direction.

## Verification and provenance

- External GPTPro task GP-0002 supplied the theorem candidate and quantifier
  audit, while conservatively leaving it outside the canonical track when its
  environment could not run Lean.
- The main operator independently compiled the staged candidate, cleaned its
  canonical module header, imported it in `TheoryLib.lean`, and registered the
  theorem in `audit/AxiomAudit.lean`.
- `pwsh workflows/verification/check.ps1` passed on 2026-08-21: the full
  8,766-job kernel build, exploit scan, and exact-allowlist axiom audit all
  succeeded.
- The theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This is a conditional reduction, not a cancellation theorem and not a
resolution of the Pi digit problem.  The Diophantine input remains an explicit
hypothesis.  Nothing here establishes the required strict Fourier upper bound
for the fixed orbit of pi, `C1`, V1, decimal disjunctivity, or novelty.
