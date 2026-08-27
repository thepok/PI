# T51 third-band fixed-seed audit

Audit date: **2026-08-12 UTC**  
Status: `machine-checked` for the local theorem stated below; **not** a proof
that every finite decimal word occurs in \(\pi\).

## Source and provenance

- Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
- Target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Marcel's local question has no external source URL; none is invented here.
- Formal module:
  [`T51T51MachinSeedThirdBandPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean)
- Module SHA-256:
  `62d481ff6d7f0e10db8462fb439c8579f9d1cf75679f5fea1a840fa4366682d1`

## Exact theorem scope

Write \(d=12N+15\) and

\[
Y_N=\operatorname{sampledMachinValueRat}(N+1)
   =10^{N+1}M_{3(N+1)}.
\]

T51 proves:

> If `p.Prime`, `7 < p`, `p != 239`,
> `p` is not one of `19, 37, 79, 48049, 3586217`, and
> `5*p <= 12*N+15 < 7*p`, then
> `padicValRat p Y_N = -1` and
> `padicValNat p Y_N.den = 1`.

The final theorem is
`padicValRat_sampledMachinValueRat_thirdBandPrime_closedEndpoint`; it has no
endpoint nondivisibility hypothesis.

The proof isolates exactly the common Taylor exponents \(p,3p,5p\).  Their
localized coefficient is checked as

\[
\frac{38279241713339684}{12184551018734375},
\qquad
38279241713339684
=2^2\cdot19\cdot37\cdot79\cdot48049\cdot3586217.
\]

If the extra base-239 endpoint is singular, the band and parity force
\(12N+17=7p\), hence \(p\equiv11\pmod {12}\).  The adjusted coefficient is

\[
\frac{15305839961353732690848}{4871956171187883640625},
\]

whose numerator factors as

\[
2^5 3^2\cdot13\cdot29\cdot8429\cdot35533\cdot470668789.
\]

Lean checks that the five odd factors displayed here are prime and that none
is \(11\pmod {12}\), so the endpoint residue cannot cancel.

## Verification

- The module contains **9 definitions** and **37 propositions** (theorems or
  lemmas).
- All 37 propositions are registered exactly once in
  [`audit/AxiomAudit.lean`](../../audit/AxiomAudit.lean).
- `TheoryLib.lean` imports the module.
- `lake env lean
  TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean`
  passed.
- `lake build
  TheoryLib.PiQuantitativeBlockHitting.T51T51MachinSeedThirdBandPrimeSurvival`
  passed with `Build completed successfully (8567 jobs)`.
- `lake env lean audit/AxiomAudit.lean` passed after the module build.
- `pwsh -NoProfile -File scripts/check.ps1` passed with
  `PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.`
- Every T51 proposition reports only the allowlisted axioms `propext`,
  `Classical.choice`, and/or `Quot.sound` (some arithmetic equalities need
  only `propext`).
- A focused scan found no `sorry`, `admit`, `native_decide`, new `axiom`,
  `unsafe`, or `opaque` declaration in T51.

The verified result is a stronger local denominator-survival theorem.  It
does not determine the complementary numerator/CRT phase and therefore does
not imply a decimal cylinder hit, normality, disjunctivity, or the canonical
every-word target.
