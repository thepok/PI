# T116 raw normalization-gcd small-support bounds fail

Status: `experiment`

Date: 2026-08-21 UTC

## Executive finding

An exact frozen census of the canonical synchronized sampled-BBP recurrence
for all `N=0..511` rejects three simple universal hypotheses about the raw T114
normalization gcd `g_N = gcd(|U_N|,V_N)`:

- G1, every prime of `g_N` lies in `{2,5}`: rejected at `N=0`, where
  `g_0=15` has offending prime 3.
- G2, `g_N ∣ 10`: rejected by the same witness `g_0=15`.
- G4, `g_N ≤ 10^6`: rejected at `N=1`, where
  `g_1=287694389770023075840`.
- G3, `g_N^2 ≤ V_N`: no counterexample occurred in `N=0..511`; this is only
  finite survival and remains an `experiment`.

The discovery range was frozen at `N=0..255` and the holdout at `N=256..511`.
G1, G2, and G4 also fail inside the holdout, first at `N=256`; G3 survives the
holdout only as finite data.

## Exact recurrence and replay

The validated generator uses the canonical inclusive finite sum
`bbpPartial(M) = sum_{k=0}^{M} bbpCombinedTerm(k)`, so
`Q_0=bbpPartial(0)=47/15`. It computes reduced `Q_N` and `F_N`, then
`U_N = 10*Q_N.num*F_N.den + F_N.num*Q_N.den`,
`V_N = Q_N.den*F_N.den`, and `g_N = gcd(|U_N|,V_N)` with exact arithmetic.

The retained workflow is
`workflows/research/pi/experiments/t116-gcd-census/`; the reproducible 24 MB
JSON payload is generated on demand rather than committed. Independent replay
checked 512 ordered unique records in about 30 seconds with about 93 MB peak
resident memory. The generated JSON SHA-256 was
`08e798cede42ae4c9de9ff01df39d4c0929938b188dd68ea7b114fc21a870847`,
and its records payload SHA-256 was
`d3af4c9b9170068fc40e81070b4754fef62a8728ed70a4e0f18707871bc3f413`.
A mutated gcd was rejected. The retained verifier additionally enforces the
exact index sequence, metadata boundary, prime-product checks, and the T116
prime-support invariant.

## Rejected false-positive artifact

One Ox artifact passed the old marker-only artifact contract but silently
defined `bbpPartial(0)=0` and summed from `k=1`, contradicting the canonical
inclusive definition. Its report SHA-256 was
`d89fcfb23957ffb7cce37caaf7521ae933a43e0d82705542eb7210384db0c084`.
It is rejected in full despite internally consistent self-checks. The gate
now has trusted JSON anchors (`Q_0=47/15`, `g_0=15`) and exact ordered-range
checks with regression coverage.

## Consequence and next direction

The huge raw gcd is dominated by the automatic common denominator. With
`H=gcd(D,E)`, `d=D/H`, `e=E/H`, and `X=10*A*e+C*d`, isolate
`k=gcd(X,H*d)`, for which `g=H*k`. A derived readout of the 512 validated
records found `k=1` at 461 indices and maximum `k=55193` at `N=91`; the
sharper candidate `k^2≤e` survived all 512 points only as an `experiment`.
That normalized inequality, not another raw-gcd bound, is the next falsifier.

Nothing here proves asymptotics, denominator growth, character cancellation,
cell occupancy, density, normality, C1, V1, or decimal-word occurrence.
