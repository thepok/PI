# T120 actual window-13 direct experiment

Date: 2026-08-22 UTC

Status: `experiment`

## Executive result

Two arithmetically disjoint exact routes agree on every normalized T118 point
for the actual window `3840 <= N < 4096`:

- combined single-fraction/Horner route;
- literal-four-pole global-LCM integer-lift route.

Their ordered 256-record `{n,r,w,cell}` projections have the identical
SHA-256

`4f5be54cf3eb309f67271bd54914708e15de1b339417ca8cd0a4cee93d4b3288`.

The exact finite statistics are

```text
cell counts = [23,31,31,22,23,27,37,19,24,19]
J           = 6860
9*J         = 61740 < 65536
C_sum       = 3302
A_sum       = 6319
Z_sum       = 0
```

Thus every decimal cell occurs in this checked window and the frozen strict-J
test passes. There is no exact rational-phase repeat. However
`A_sum=6319>3512`, so the preregistered window-13 rule selects
`STOP-determinant-only-route`. The T119 necessary near-determinant predicate
is too lossy to prove the required same-cell pair bound by itself. Earlier
windows were not opened.

## Exact point evidence

Correct combined route, OpenRouter Ox run `t120-window13-direct-wave-ox-combined-r0`:

- script SHA-256:
  `1b94c4cd4b7a7cff2c8d3faa891d4c3546b355e80bbb518ef880cdaccea2c856`;
- raw output SHA-256:
  `a6a4b0052f0a5777a4e50bf20cddf4696a2aa832f8197b37ed8342c32ee24732`.

The tightened-contract combined rerun `t120-window13-direct-wave-ox-combined-r5`
used a separately generated script with SHA-256
`1739938485b414ee66ba9c0dfd79aa793be309e099dee3c64941a96ae00dee80`
and reproduced the same raw output SHA-256 `a6a4b005...`.

Correct global-LCM route, Oxzen run `t120-window13-direct-wave-oxzen-global-r1`:

- script SHA-256:
  `2895f28e68feb5d19fc1cbcf9348922623992cbe5fdcbde690a35ed1325e582a`;
- raw output SHA-256:
  `4c0b827aa11bdff393bea872f8973b9cdb69637ff1d28b5146d723c1432fa1d4`.

The raw JSON hashes differ only because the route metadata differs. Extracting
each `.points` array with canonical compact JSON gives the common projection
hash above. Denominators range from 101280 to 108084 decimal digits.

The computation tasks and exact formulas are committed under
`workflows/modelbench/tasks/pi/current/t120-window13-direct-experiment/`.
Disposable 53.6 MB raw outputs remain under `workflows/state/runs/` and are not
committed.

## Independent statistic checks

Three exact branch calculations agreed:

1. sequential pair enumeration on the correct combined artifact;
2. eight-process pair enumeration on the same artifact;
3. an independently organized cell-bucket calculation on the global-LCM
   artifact.

The first two used the machine-checked cell geometry to skip pairs whose cells
differ by at least two. They each tested exactly 9399 same/adjacent-cell pairs
and skipped 23241 impossible pairs. The third enumerated same-cell buckets and
adjacent-cell cross-products directly. It decomposed

`A_sum = C_sum + adjacent_near = 3302 + 3017 = 6319`.

All three found `Z_sum=0` and the same frozen branch
`A_sum_gt_3512`. A slower exact all-pairs replay subsequently completed all
255 lags and independently returned the same `J=6860`, `C_sum=3302`,
`A_sum=6319`, `Z_sum=0`, cell counts, and branch. Its compact output SHA-256 is
`ea3c643afc445ca96c468c1d16325776251a67e3ed717da67eee99073acb1e26`.
The exact loaded script was recovered from the runner's immutable first-call
patch after detecting a three-second pathname-overwrite race; its SHA-256 was
`f991ebb10ace3413069c7a700848e133c63da6331785230496d9bbc1df4380b3`.
A cleaned equivalent replay is committed at
[`replay_full_stats.py`](../../../../workflows/experiments/t120_window13/replay_full_stats.py).
The maximum-ratio field is non-decisive and is not used for the branch.

## Rejected artifacts and workflow correction

Two independently written scripts initially scaled the first point by
`10^START_N` instead of the required `10^(START_N+1)`:

- combined run `t120-window13-direct-wave-ox-combined-r3`;
- literal-four-pole run `t120-window13-direct-wave-oxzen-literal-r2`.

Their wrong point projections agree exactly at SHA-256
`3736621e17e4619a85c57ddfb78cd5621dbfb98dbb389a7c187f3aaa612ad5c1`.
They are rejected, not votes. Exact comparison confirmed that applying one
additional factor of ten to every rejected rational yields the accepted
combined points. The task contract now requires a literal
`10**(START_N+1)` production initialization and forbids `10**START_N`.

Two early statistic tools were also rejected because they substituted cell
ordering for the definitions of `A_l` and `Z_l`, and one maximized the wrong
ratio. The corrected task now states the literal formulas

`Delta=r_i*w_j-r_j*w_i`,
`10*abs(Delta)<w_i*w_j`, and `Delta=0`.

## Research consequence

This experiment kills only the determinant-only counting strategy at its
frozen threshold. A continuation would require a cutoff-independent,
BBP-specific predicate `P(N,M)`, fixed without fitting held-out windows, such
that

`sameCell(N,M) -> nearDet(N,M) and P(N,M)`

and the refined pair count is uniformly at most 3512 in every 256-block. No
such predicate is known. Free-model and Pro research has therefore been
redirected to finding such a mechanism or proving that a broad natural family
of refinements cannot work.

## Nonclaims

This is finite `experiment` evidence. It proves no later cell hitting, density,
equidistribution, normality, decimal-word occurrence, V1 statement, or
resolution of the PI problem.
