# T120 window-13 research-direction gate

Date: 2026-08-22 UTC

Status: `proof sketch` (direction analysis) and planned `experiment`

## Decision

T120 window 13 remains the best next finite computation, but only as a cheap,
preregistered calibration or kill test of the machine-checked T119 lane. It is
not evidence for decimal distribution. Run only after the staged controller
trust gates pass, and inspect `[3840,4096)` before any holdout window.

## Outcome routing

- Any route, byte, replay, T118, or T119 mismatch invalidates the experiment.
  It has no mathematical interpretation.
- An actually missing cell is an `experiment` counterexample to a universal
  256-step decimal-cell cover. By contrast, `9*J >= 65536` with all ten cells
  present only kills this Cauchy--Schwarz certificate.
- If `J` passes but `A_sum > 3512`, stop determinant-only counting at the
  frozen threshold. T119's necessary near-determinant condition is too lossy;
  do not open holdouts or fit exceptional lags.
- If a distinct pair has zero cross determinant, stop and audit the exact
  rational-phase repeat. One repeat does not imply periodicity because the BBP
  forcing is nonautonomous.
- If window 13 has `9*J < 65536`, `A_sum <= 3512`, and no zero determinant,
  this authorizes only the frozen windows 0--12. It is not yet a change in
  research direction.

The only admissible determinant-route refinement after `A_sum > 3512` would
be a cutoff-independent BBP predicate `P(N,M)`, frozen before holdout access,
with a theorem of the form

`sameCell N M -> nearDet N M and P N M`

and a pair-count target at most 3512. No such canonical predicate is currently
known, so the skeptical default is to stop rather than invent one from the
observed window.

## Strongest symbolic frontier after a full GO

First isolate the generic finite shell: for each base `B`, define the exact
T119 near-pair set on `0 <= i < j < 256` and prove that cardinality at most
3512 forces all ten sampled-BBP cells to occur. This combines T119,
`C_sum <= A_sum`, `J = 256 + 2*C_sum <= 7280`, and the strict nine-cell
Cauchy bound.

The actual research frontier is then the cutoff-independent statement

`for all B >= B0, card (NearPairs10 B) <= 3512`.

Only such an actual-sequence anti-concentration theorem would turn the finite
calibration into uniform sampled-orbit cell hitting. A separate buffered
argument would still be required to transfer through T106's geometric error
to the true decimal orbit of pi.

Finite survival, including survival of all fourteen windows, remains only an
`experiment` unless it yields this or another independently justified
symbolic mechanism. Nothing here proves normality, decimal-word occurrence,
V1, or a resolution of the Pi problem.
