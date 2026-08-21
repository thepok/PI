# T85 complete T29 finite experiment

Classification: `experiment`.

Every observation in this package is finite and heuristic. The computations
neither prove nor refute C2, C1, or C3. In particular, a ratio below one at the
tested points does not supply one constant at all positive `m,N`, and it gives
no conclusion about the canonical collision count.

## Statement and scope

`CANONICAL_STATEMENT.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`. Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The local statement has no external source URL; its provenance is included in
the file. The canonical question asks for one `C_s` after each `0<s<1` and
before every positive `m,N`, for ordered nonoverlapping decimal-block
collisions and with the additive `N` term. This package instead evaluates
T29's residual sparse-Fourier sibling A12 at finitely many points. It does not
replace, weaken, or answer the canonical question.

The tested T29 parameters are `(mu,c,alpha)=(8,1,pi)`. Although `Q0=0` is
printed, the tested domains do not depend on `Q0`: if `1<=m<=5`, `r>=m`, and
`q=10^n(10^r-1)`, then

```text
q >= 10^m-1,  q^7 > 10^m,
```

so T79's second arithmetic-exclusion conjunct `10^(-m) <= q^(-7)` is false.
The replay checks these integer inequalities.

The vendored T22, T29, T49, T59, and T63 files are byte-exact copies of the
kernel-checked interfaces. They are inspectable sources, not new Lean claims.
Their hashes are pinned both in `replay.py` and `SHA256SUMS`.

## Exact observable

For a canonical half-open block `B=[a,b)`, let

```text
w_B = sqrt(b^2-a^2),
z_k = exp(2*pi^2*i*10^k),
L_E(h) = 2*Re(z_E^h * conj(sum_(j=0)^(E-m) z_j^h)).
```

The sum is empty for `E<m`. The factor two is exactly T22's two signed
orientations. Strict cutoff `N` contains endpoint layers `E<N`, so

```text
V_B(h) = sum_(E=a)^(b-1) L_E(h),
T29(m,N) = sum_B (1/w_B) * sum_(h=1)^(10^m) V_B(h)^2.
```

This retains every canonical block, literal width, orientation, and inclusive
frequency. It costs `O(N*10^m)` phase-frequency steps rather than enumerating
quadratically many records and then quadratically many record pairs.

The independent brute-force oracle enumerates every ordered `(i,j)` satisfying

```text
0 <= i,j < N,  |i-j| >= m,  a <= max(i,j) < b,
```

and compares its fixed-point character sum exactly with `V_B(h)`. The declared
cases `(1,5)`, `(2,6)`, `(3,7)`, `(4,6)`, and `(5,7)` check every inclusive
frequency through `10^m`.

## Signed sectors

For one block, records sharing a first coordinate or a second coordinate form
T49's cancelling sector. If

```text
J_B(i) = {j : |i-j|>=m and a<=max(i,j)<b},
Q_B,i(h) = sum_(j in J_B(i)) z_j^h,
d_B,i = |J_B(i)|,
```

then the cancelling contribution before division by `w_B` is

```text
2 * sum_h sum_i (|Q_B,i(h)|^2-d_B,i).
```

The record-pair diagonal is `10^m` times the oriented record count. For general
`m`, the primitive nonattacking interval is conservatively certified as the
residual of the direct, diagonal, and independently evaluated cancelling
intervals; it is not a second independent primitive evaluator. `results.json`
reports all three signed pieces, their complete complement to the primitive
sector, and an interval recombination that encloses the direct T29 interval at
every reported case. The independent primitive reconciliation below applies
only at `m=1`.

For `m=1`, `N=4*2^t+1`, there is one block and, with
`X_h=|sum_(k<N)z_k^h|^2`, the replay also checks the independent T63 formulas

```text
direct:    sum_(h=1)^10 (X_h-N)^2 / sqrt(N^2-1),
primitive: sum_(h=1)^10
  (X_h^2-4*(N-1)*X_h+2*N^2-3*N) / sqrt(N^2-1),
cancelling: sum_(h=1)^10 2*(N-2)*(X_h-N) / sqrt(N^2-1).
```

The primitive polynomial is T63's complete selected-plus-defect sector. Each
of the three independently computed intervals must intersect its generic
recurrence interval. This is checked for every `6<=t<=16`.

## Interval certificate

`pi_digits.txt` and `pi_certificate.json` are T84's 262224-digit exact-integer
Chudnovsky certificate. Full replay regenerates the binary split, alternating
remainder bound, square-root enclosure, decimal digits, and certificate before
using them. Every shifted pi interval must remain inside one rational
eighth-turn interval.

Trigonometric values use integer scale `10^40` and 24 Taylor recurrence steps.
No floating-point value enters a result. If `e` is the certified base component
error, the Euclidean error for a repeatedly multiplied phase is bounded by

```text
E_h = h*(2*e+10^(-40))/(1-2*h*e).
```

The replay verifies the induction inequality
`E_(h+1)>=(1+2e)*E_h+(2e+10^-40)` and uses the conservative common `E_(10^m)`
for each case. Dot products, row norms, squares, sector subtraction, widths,
and target division propagate exact `Fraction` endpoints. Every serialized
decimal endpoint is rounded outward and reparsed. `results.json` contains 894
reported interval objects after the complete-complement fields are included.

The literal benchmark is

```text
10^m * (N + N^2*10^(-m/2)).
```

For odd `m`, `sqrt(10)` is enclosed by integer square root. Frequency decade
bins and canonical block contributions are nonnegative. Endpoint-layer ranges
use the signed additive attribution `U_range(h)*V_B(h)/w_B`; summing all ranges
recombines to enclose the direct value. The output also lists the top twenty
individual frequencies.

## Replay

Use a directory containing only the delivered files. Python 3.11 or newer is
recommended. No third-party package or network access is used.

```bash
python3 replay.py --verify
```

This one command:

1. verifies every pinned source and pi-certificate hash;
2. regenerates the exact pi certificate;
3. checks canonical blocks for every `1<=N<=512`;
4. runs all declared brute-force comparisons;
5. evaluates all requested cases and interval containments;
6. checks every T63 reconciliation and signed-sector recombination;
7. verifies `SHA256SUMS`; and
8. compares regenerated `results.json` byte for byte.

The implementation is deterministic, single-process, and writes no file in
`--verify` mode. The final measured producer run was 564.97 seconds. This is within
the acceptance budget of 4 CPUs, 32 GB RAM, and 21600 seconds; the replay uses
one CPU and memory linear in the largest `N`.

`python3 replay.py --quick` checks all delivered hashes without recomputation.
`--generate` is producer mode and overwrites only `results.json`.

## Finite findings

All fifteen direct ratios are certified below one at the literal `s=1/2`
benchmark. The four transition ratios are approximately

```text
(2,11):  0.5094242695
(3,33):  0.3847793851
(4,101): 0.7486593445
(5,317): 0.9331530813
```

The `(5,317)` value is closest to the benchmark and its mass is spread across
all five canonical blocks; `results.json` gives exhaustive block and endpoint
range localization. Signed primitive and cancelling sectors change sign across
the finite cases, so neither sector alone is representative of the complete
nonnegative observable. These are heuristic finite observations only and
neither prove nor refute C2, C1, or C3.
