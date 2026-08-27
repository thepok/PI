# T119 sampled-BBP same-cell cross determinant

Status: `machine-checked`

Date: 2026-08-22 UTC

Canonical source:
[`T119T119SampledBBPSameCellCrossDeterminant.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T119T119SampledBBPSameCellCrossDeterminant.lean)

T119 proves the exact generic interval consequence that two signed integer
residues over positive denominators in one endpoint-exact half-open `q`-cell
satisfy

`q * |R₁*W₂ - R₂*W₁| < W₁*W₂`.

It then applies canonical T118 independently at two sampled-BBP successor
indices. Conditional on both successors lying in the same explicitly named
cell, their normalized Euclidean remainders and positive denominators satisfy
the same strict cross-determinant inequality.

The approved Oxzen candidate has SHA-256
`a356d728b7a9ba99347d8c411b937366f4a7b35de7c260dbe25e48b028f7fd88`.
Its original isolated gate log has SHA-256
`cd7c9cf01012206037dad838b41fb3d94c5aa5b74bb40e6695f13e277095af06`.
An independent source audit preferred it over five other gate-passing
candidates because it is the shortest symmetric proof, uses every endpoint
and positivity hypothesis, and compiles warning-free. Both public theorems
are registered in the central axiom audit.

This is a conditional representation theorem. It proves no same-cell pair
exists, repeats, or is frequent, and no pair-count bound, finite or
arbitrarily-late occupancy, density, cancellation, normality, decimal-word
occurrence, V1, or resolution of the Pi problem.
