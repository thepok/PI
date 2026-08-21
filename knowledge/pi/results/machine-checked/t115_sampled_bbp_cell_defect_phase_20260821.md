# T115 sampled-BBP cell-defect phase

Status: `machine-checked`

Canonical source:
`TheoryLib/PiQuantitativeBlockHitting/T115T115SampledBBPCellDefectPhase.lean`

Canonical SHA-256:
`febf6440a3a5aeec8921b50ad9adf89ace22c3371b5d9be05e3e4f981623b8c2`

## Result

For the synchronized reduced rational
`Q_N = 10^N*bbpPartial(7N)`, T115 defines its actual integer residue `r_N`,
positive denominator `D_N`, mesh quotient `c_(q,N)`, remainder `e_(q,N)`,
and normalized real floor defect

`delta_(q,N) = e_(q,N)/(q*D_N)`.

It proves the exact Euclidean identity `q*r_N = D_N*c_(q,N)+e_(q,N)` and
the zero-mesh degeneration.  For every nonzero mesh and `a,h : ZMod q`, it
then proves the pointwise centered-character factorization

`chi(h*(cell-a)) = chi(-(h*a)) * phase(+h,r_N/D_N) * phase(-h,delta_(q,N))`.

The signs are forced by `c/q = r/D - e/(qD)`.  The left side uses the actual
`cyclicCell q (sampledBBPOrbit N)`, connected through T113 rather than defined
as an arithmetic alias.

## Verification and provenance

- The corrected arithmetic base came from a free Ox artifact with SHA-256
  `d5fa0cd3c03f02174db6e91f2c919829ee293511ec8e3713e2359a24944acf8d`
  and isolated gate-log SHA-256
  `3a7a94dc557d95bfd1dd151b35072f689019c178ad9890017990d528501651c3`.
- An earlier loose-contract artifact passed Lean while replacing the required
  normalized real defect by an integer remainder.  Independent semantic
  review rejected it.  The workflow was hardened first to pin the exact real
  denominator, then to pin integer types for residue, quotient, and remainder.
  This is why a green candidate gate alone was not treated as acceptance.
- A partial free Oxzen character attempt retained the intended proof shape but
  contained `sorry` and changed the integer API to naturals; it was rejected as
  an integration source.
- The independent integrator combined only the validated arithmetic and proof
  ideas into a placeholder-free scratch proof, SHA-256
  `093c33231e0d84290879b7dda22c9cf4cfb3eeca78af4f1375d2e46759b6f210`,
  which compiled before canonical promotion.
- All three public theorems are registered in `audit/AxiomAudit.lean`.
- `pwsh workflows/verification/check.ps1` passed on 2026-08-21: all 8,769
  kernel build jobs, the exploit scan, and the exact-allowlist axiom audit
  succeeded.

## Boundary

T115 is exact pointwise algebra, not a cancellation estimate.  It takes no
sum over samples or frequencies and proves no DFT trough, cell multiplicity,
occupancy, cover, density, normality, C1, V1, or digit result.  The normalized
defect can have order-one phase at frequencies comparable with the mesh, so it
cannot be discarded as a generic small error.  Representation-only extensions
should now stop unless they establish or falsify a nontrivial property of the
actual normalized sequence.
