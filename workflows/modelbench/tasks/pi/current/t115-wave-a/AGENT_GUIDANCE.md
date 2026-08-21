# T115 exact floor-defect phase guidance

Work skeptically. The exact theorem types in `TASK_CONTRACT.md` are binding.
Create only `Contribution.lean` and `REPORT.md`, and compile before reporting.

Use the single synchronized reduced rational
`Q_N = 10^N * bbpPartial (7*N)` throughout. Its residue is the actual
`Q_N.num % Q_N.den`. The cell quotient and remainder come from Euclidean
division of `q * residue` by the full positive reduced denominator, and the
real defect denominator is exactly `q * Q_N.den`.

For the character task, the sign pattern is binding:

`stdAddChar (-(h*a)) * phase (+h) residue * phase (-h) defect`.

The identity follows from `q*r = D*c+e`, hence
`c/q = r/D - e/(q*D)`. Handle the zero mesh only through the separate
arithmetic degeneracy theorem; the character theorem uses `[NeZero q]`.

Reject aliases of `cyclicCell`, three-adic fibers, marginal CRT coordinates,
numerator-only or denominator-only projections, reindexing, Parseval, norms,
inequalities, or any occupancy/cancellation/density/V1 claim. No placeholders,
new axioms, unsafe declarations, metaprogramming, unrelated public
declarations, or additional imports are allowed.
