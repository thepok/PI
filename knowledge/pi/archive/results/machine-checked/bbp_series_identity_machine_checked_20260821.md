# BBP real-series identity milestone (2026-08-21 UTC)

Claim label: `machine-checked`.

The verified track now proves the classical real BBP series identity in
`Theory.PiDigits.T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi`:

```lean
HasSum T100BBPRealBridge.bbpRealTerm Real.pi
```

The proof chain is:

- T101: summability of the canonical real BBP term by geometric comparison;
- T102: exact elementary evaluation of the canonical BBP kernel integral as
  `Real.pi`;
- T103: exact integral of each kernel term, numerator factorization,
  nonnegativity, and the pointwise geometric kernel sum;
- T104: dominated-convergence interchange and the resulting `HasSum` theorem.

The full `scripts/check.ps1` gate passed after T104: kernel build, exploit
scan, and exact-allowlist axiom audit. Every public theorem added in T101--T104
is registered in `audit/AxiomAudit.lean`; the reported dependencies are only
`propext`, `Classical.choice`, and `Quot.sound`. An independent trusted audit
also compiled T104 and checked the dominated-convergence premises and exact
T100/T102/T103 interfaces.

Pinned source hashes at the passing state:

- T101: `35a6b9b0ba2b5b1de1a34efaa2d818eb5ac975d9950aca78d3c91afe431f584d`
- T102: `9e4aec193e13f22bfa36ff34560af29038bdde69b8ff2b8eaa8fd331baf5ec74`
- T103: `727dbe48f5c8d4b140659f516b6ca1c187499e8b1410f7a60127d433a482d93f`
- T104: `a2aaabd081a83d1c7db88432b0014df67e5678e3117db517fc79cd25fa46df5b`

## Claim firewall

This is not a resolution of `local:pi-digits` V1. T104 removes the formerly
explicit BBP-series premise from the oversampled decimal-grid stability
bridge, but that bridge still retains the externally sourced proposition
`IrrationalityMeasureBelow Real.pi 8`. More importantly, eventual agreement
between BBP partial-sum codes and pi codes proves stability, not coverage,
mixing, density, normality, SP1, or V1. The canonical problem remains open.

Three model artifacts that compiled as generic geometric sums were rejected
because they silently substituted different kernel numerators. They were not
integrated. The canonical proof uses only the pinned numerator
`4*sqrt 2 - 8*x^3 - 4*sqrt 2*x^4 - 8*x^5`.
