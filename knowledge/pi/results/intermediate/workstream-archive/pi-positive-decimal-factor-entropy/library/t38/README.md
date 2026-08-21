# T38 feasible-core experiment

Status: `experiment`.

This bundle computes finite symbolic entropy-gap certificates and shallow exact
transversal-time probes. It makes no claim about the decimal expansion of pi,
and finite computation is not evidence for a universal statement about pi.

## One-command replay

Run from a directory containing only these delivered artifacts:

```sh
sh ./verify.sh
```

The command regenerates every generated file in a temporary artifact-only
directory, compares it byte-for-byte with the delivery, and then checks every
integer matrix and exact rational certificate.

## Definitions and conventions

Let `D={0,...,9}`. For a nonempty word `w` of length at most three, `K_w` is
the one-sided symbolic decimal subshift consisting of infinite strings in
`D^N` that avoid `w`. For `q` in `{9,11,16}`, multiplication is represented by
the bounded carry relation

```text
q*a_j + c_(j+1) = b_j + 10*c_j,   0 <= c_j < q.
```

The finite presentation is read most-significant digit first, so an edge runs
from `(c_j,r_j,s_j)` to `(c_(j+1),r_(j+1),s_(j+1))`; `r` and `s` are KMP
states for input and output avoidance. Parallel digit-labelled edges are
counted in the integer adjacency matrix. Initial states are `(c,0,0)` for all
`0<=c<q`. A finite path is retained exactly when it can reach a directed
cycle, hence admits an infinite symbolic continuation.

This symbolic convention deliberately makes no assertion about which decimal
expansion represents a terminating circle point. Such endpoint choices affect
only exceptional eventually-zero/eventually-nine strings and not the reported
Perron entropy, but they can affect literal finite-cylinder membership. The tau
probes below are therefore explicitly symbolic, not circle-endpoint claims.

For each pair `(w,q)`, the bundle presents the forbidden-word matrix `A_w` and
the carry-product matrix `B_(w,q)` through deterministic reconstruction code.
It certifies their Perron roots by exact Collatz-Wielandt inequalities. For an
irreducible nonnegative SCC matrix `M` and delivered positive integer vector
`v`, the verifier checks exactly

```text
min_i (Mv)_i/v_i <= rho(M) <= max_i (Mv)_i/v_i.
```

All SCCs are checked, so taking maxima gives exact rational enclosures for the
graph spectral radius. The certified entropy-gap enclosure is obtained from

```text
rho(A_w)_lower / rho(B_wq)_upper
  <= exp(Delta_wq) <=
rho(A_w)_upper / rho(B_wq)_lower.
```

Natural-log endpoints are certified by an exact rational atanh series with a
geometric tail bound and outward decimal rounding. Gamma minima and the
multiplier ranking are checked directly from exact rational ratio intervals
before any logarithm is evaluated.

For the tau probes, define `tau_(w,q)(ell)` as the least `M>=0` such that the
union, for `0<=m<=M`, of the length-`ell` prefix languages of
`T_(q^m)(K_w)` contains every decimal word of length `ell`. A claimed value is
made only when the exact uncovered set becomes empty. A prefix is covered
exactly when at least one compatible path ends at a carry/KMP state admitting
an infinite continuation.

## Files

- `t38_experiment.py`: deterministic generator and exact verifier.
- `entropy_certificates.json.gz`: 3,330 cases containing 6,666 SCC/vector
  Perron certificates.
- `delta_table.csv`: all Delta enclosures in exact ratios and display logs.
- `summary.json`: all nine Gamma enclosures and certified multiplier ranking.
- `tau_probes.json`: exact shallow tau entries and feasibility-frontier data.
- `pi-positive-decimal-factor-entropy.txt`: byte-exact canonical statement.
- `verify.sh`: one-command artifact-only replay.

## Computed result

All 3,330 certified lower bounds for `exp(Delta_(w,q))` exceed one. At the
decisive length-three frontier, the certified Gamma intervals in natural-log
units are approximately:

| q | certified Gamma_3(q) interval |
|---:|---:|
| 11 | `[0.000824117199542483, 0.000824117199543719]` |
| 9 | `[0.000806543783430394, 0.000806543783432948]` |
| 16 | `[0.000786402650867599, 0.000786402650869274]` |

The underlying exact rational Perron-ratio intervals are in `summary.json`.
They are pairwise disjoint, so exact cross-multiplication certifies the
worst-case ranking `11 > 9 > 16`; rounded display decimals are not used.

The bundle claims 81 exact shallow tau entries: all one-digit forbidden words
for all three multipliers at depths one and two, plus seven overlap-sensitive
length-two/three forbidden words at depth one. The complete per-entry values
and generated state-count frontiers are in `tau_probes.json`.

The feasibility diagnostic uses the same explicit live-carry/KMP graph builder
as the tau probes on `(q,w)=(16,0)`. It fixes a deterministic budget of 500,000
candidate transitions and therefore constructs exponents zero through three.
For every constructed layer replay checks the vertex count, actual directed
edge count, and live-state count. Exponent four is recorded as the first
unbuilt layer because its 6,553,600 candidates exceed the declared budget.
This operation-count cutoff is reproducible and makes no wall-clock or memory
claim.

## Self-checks

Replay exhaustively checks the local carry equation, all fixed-width integer
multiplications through three digits, direct substring avoidance against KMP
on overlap-sensitive examples, and baseline path counts against brute force.
It reconstructs all graphs, SCCs, matrices, ratio bounds, Delta rows, Gamma
minima, ranking inequalities, tau probes, and feasibility-frontier graphs.

## Scope and extrapolation

No bounded, logarithmic, linear, or other asymptotic growth classification is
claimed for tau. Any extrapolation from the shallow exact probes is heuristic.
There is no pi claim.
