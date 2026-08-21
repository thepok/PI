# T50 certified bounded fixed-pi resonance experiment

Status: `experiment` (finite heuristic evidence only).

## Scope

The vendored canonical statement is byte-identical and hash-pinned. Its question
retains `forall A, exists n0, forall n>=n0, exists N`, ordered pairs, the
diagonal, strict circle distance, fixed pi, and base 10. This experiment is the
bounded A14 sibling only. It does not instantiate the failure-derived parameter
provenance of T26; it exhausts the explicitly configured structural
`GeometricResonanceChain` domain.

## Declared bounds

- `M in [3]`, `D in [4]`.
- `r in [2]`, `h in [1]`.
- Depth `1`, shifts `[[1]]`, `B=1`, `K=2`.
- Every legal consecutive node and every `1 <= ell < min(M_k,M_(k+1))` is evaluated.
- Boundary loss uses `H0=H1=R-1` for each target stratum and the full common pair domain.

## Certification

Pi is enclosed by exact rational alternating-series bounds in Machin's formula.
Every phase is reduced by certified interval arithmetic, and sine/cosine use
rational Taylor polynomials with explicit derivative remainders. Resonance
comparisons use squared norms. Strict predicates are labeled true only when the
entire left interval is strictly on the required side; overlaps are unresolved.
All T26 list/range predicates and all denominator formulas are exact integers.

## Results

| dataset | candidates | witnesses | strata | FSFS true | APC true | unresolved predicates |
|---|---:|---:|---:|---:|---:|---:|
| pi | 1 | 1 | 1 | 0 | 0 | 0 |
| rational_cycle | 1 | 1 | 1 | 1 | 1 | 0 |
| seeded_random | 1 | 1 | 1 | 0 | 0 | 0 |

`raw_output.json` contains every candidate, every witness node interval, every
legal denominator stratum, every primitive-class contribution, every common-domain
joint-good classification, and certified boundary-loss/APC/FSFS enclosures.
The primitive regrouping and APC terminology are taken from the unverified T43
note and are used only as an interval-consistency cross-check; T38's Fejer sum is computed
independently through a certified geometric-series identity.

## Replay

Run `bash reproduce.sh` from a directory containing only these artifacts.
It hash-checks all pinned inputs, regenerates and byte-compares the JSON and this
report, validates exact table structure, and runs a separate floating-point naive
implementation on all declared `M=3` cases. Requirements are Python 3.11+ and
standard Unix `bash`, `sha256sum`, `cmp`, and `mktemp`; no network is used.
Declared budget: 300 seconds and 2048 MiB.

## Required limitation

Every conclusion is finite heuristic evidence. Successes or failures prove neither
FSFS nor its negation beyond the listed tuples, neither adjacent compatibility nor
its negation, neither C1 nor canonical A1, and no asymptotic property of pi.
The rational-cycle and seeded-random rows are controls, not transfers to fixed pi.
