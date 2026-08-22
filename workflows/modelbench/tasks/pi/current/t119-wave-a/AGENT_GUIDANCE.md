# T119 same-cell cross-determinant guidance

Work only on the conditional representation consequence of canonical T118.
Import exactly
`TheoryLib.PiQuantitativeBlockHitting.T118T118SampledBBPNormalizedExcessCell`.

First prove the frozen generic integer lemma: two fractions `R₁/W₁` and
`R₂/W₂` in the same endpoint-exact half-open `q`-cell satisfy

`q * |R₁*W₂ - R₂*W₁| < W₁*W₂`.

Keep `q`, the cell representative `a`, residues, and denominators in `ℤ` in
that lemma. Both denominator-positivity hypotheses and the strict upper cell
endpoints are required. Do not weaken the conclusion or silently assume that
residues are natural numbers.

Then specialize the generic lemma to indices `N` and `M`. Use T118's theorem
`sampledBBPSuccessor_cell_eq_iff_normalizedExcess_interval` independently at
both indices. Preserve the exact T118 definitions of `Q,F,H,d,e,X,k,W,R`, the
signed numerator, Euclidean remainder, natural-to-integer casts, `0<q`,
`a<q`, and the two explicit same-cell hypotheses.

This task does not prove that a same-cell pair exists, repeats, or is frequent.
It proves no occupancy, density, cancellation, normality, decimal occurrence,
V1, or Pi result. Do not add examples, searches, finite experiments, public
aliases, extra public declarations, or stronger statements.

Deliver only `Contribution.lean` and a concise `REPORT.md`. The Lean file must
declare exactly the two frozen public theorems in the contracted namespace,
use only the allowed import, contain no command output or forbidden shortcut,
and compile with the exact contracted types.
