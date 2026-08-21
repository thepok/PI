# T98: Champernowne Boundary-Scale Obstruction

## Status and source discipline

This is an **experiment** plus an elementary construction-level obstruction.
It concerns only the base-10 Champernowne digit stream

```text
1234567891011121314...
```

formed by concatenating the ordinary decimal representations of the positive
integers.  The sole dated primary source is pinned in `SOURCE_MANIFEST.md`.
The calculation and argument below do not use normality as a premise: the
stream is generated directly in `t98_replay.py`.  The copied canonical problem
statement has SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.

## Imported parameter and convention audit

The accepted-library import hashes and exact locators are in
`LIBRARY_IMPORT_AUDIT.md`. The imported T56 sparse parameters are retained
literally:

\[
 L_n=10^{\lfloor n/2\rfloor},\qquad H_n=10^n/2.
\]

T56's lag triangle is retained literally: positive lags satisfy
`1 <= r < L_n`, and at lag `r` the start range is
`0 <= j < L_n-r`.  The count is ordered and diagonal-inclusive, hence is

\[
 L_n+2\sum_{r=1}^{L_n-1}
 \#\{0\le j<L_n-r:b_j=b_{j+r}\}.
\]

Here `b_j` is the fixed-length length-`n` base-10 block beginning at digit
position `j`, encoded in `[0,10^n)`.  Leading zeroes remain part of the block.
The replay uses the strict circular **block** cutoff

\[
 \min(|b_i-b_j|,10^n-|b_i-b_j|)<1.
\]

Its left side is an integer, so it is equivalent to `b_i=b_j`.  This gives an
exact finite digit-block analogue of T56's strict-cutoff ordered lag statistic;
it is not identified with real-circle proximity of two infinite decimal
suffixes.

For comparison, the imported C7 form has the full signed strict band
`|h| < H_n`, including `h=0`, triangular weight `1-|h|/H_n`, and scale
normalization `H_n L_n`; in the original literal it uses
`x_j=frac(10^j*pi)`:

\[
 \sum_{|h|<H_n}\left(1-\frac{|h|}{H_n}\right)
 \left|\sum_{j<L_n}e^{2\pi i h x_j}\right|^2
 \ \le C H_nL_n.
\]

The replay does **not** substitute the block count for this energy and does
not numerically truncate its frequency band.  It records `H_n` and the whole
band convention to prevent that invalid substitution.  The exact block count
is useful only for displaying the scale at which a digit-counting normality
argument would have to control boundaries.

## Deterministic construction and counts

For each row, the program appends `str(1)`, `str(2)`, and so on until it has
`L_n+n-1` digits; it then forms every overlapping length-`n` block at starts
`0,...,L_n-1`.  It groups equal block codes.  A group with positions
`p_1<...<p_a` contributes one to the positive-lag count at every difference
`p_v-p_u`, `u<v`; the final count is the displayed diagonal plus twice their
sum.  Thus the program directly checks the lag endpoints, triangular start
range, ordered-pair factor two, and strict integer cutoff.

`B` is the number of starts whose length-`n` block crosses at least one
integer-concatenation boundary.  `Q` is the ordered, diagonal-inclusive block
count.  The full structured output, including every nonzero-lag witness, is
in `replay_expected.json`.

| n | L_n | H_n | B | distinct blocks | Q | positive-lag total |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 10 | 50 | 9 | 10 | 10 | 0 |
| 3 | 10 | 500 | 10 | 10 | 10 | 0 |
| 4 | 100 | 5,000 | 100 | 100 | 100 | 0 |
| 5 | 100 | 50,000 | 100 | 100 | 100 | 0 |
| 6 | 1,000 | 500,000 | 1,000 | 1,000 | 1,000 | 0 |
| 7 | 1,000 | 5,000,000 | 1,000 | 1,000 | 1,000 | 0 |
| 8 | 10,000 | 50,000,000 | 10,000 | 9,996 | 10,008 | 4 |
| 9 | 10,000 | 500,000,000 | 10,000 | 10,000 | 10,000 | 0 |
| 10 | 100,000 | 5,000,000,000 | 100,000 | 99,992 | 100,016 | 8 |
| 11 | 100,000 | 50,000,000,000 | 100,000 | 99,997 | 100,006 | 3 |
| 12 | 1,000,000 | 500,000,000,000 | 1,000,000 | 999,994 | 1,000,012 | 6 |

These rows are finite evidence only.  In particular, their small collision
counts neither prove a uniform all-`n` estimate nor evaluate C7's energy.

## Exact boundary-scale obstruction

The fixed-word, integer-epoch mechanism relevant to normality fixes a word
length `k`, takes an integer-length epoch `m` with `m >= k`, counts internal
occurrences in each `m`-digit integer, and treats the at most `k-1` boundary
starts per adjacent pair separately.  That separation can yield a negligible
boundary proportion only in the fixed-`k`, `m -> infinity` order of limits.

The T56 scale reverses that relation.  For `n >= 4`, put
`L=10^(n//2)`.  The first `L+n-1` stream digits occur before the decimal
representation of `10^(n-1)`: indeed

\[
 L+n-1\le 10^{\lfloor n/2\rfloor}+n-1\le10^{n-1}-1,
\]

and the concatenation through `10^(n-1)-1` has at least `10^(n-1)-1` digits.
Every constituent integer relevant to a length-`n` block therefore has at
most `n-1` digits.  No length-`n` block can lie inside one constituent
integer, so every one of the `L` starts crosses a boundary.  This direct
inequality explains the `B=L` rows from `n=4` onward (and the replay also
checks the exceptional small rows).

Thus the boundary portion is not a lower-order error at the literal T56
sample scale: it has cardinality exactly `L_n`.  Moreover, the normality proof
requires an epoch length at least the word length, whereas the integer lengths
visible by digit position `L_n` are far below `n`.  Fixed-word frequency
normality consequently gives no bound for the joint family of all length-`n`
blocks and all lags in the T56 triangle, and it gives no bound for the
complete C7 triangular energy.  This is a boundary/scale obstruction to
transferring that normality mechanism, not a claim that the Champernowne
analogue fails a quantitative estimate by some other argument.

## Terminal form: explicit obstruction

**Boundary/scale obstruction.** At the literal sparse scale `L_n`, every
length-`n` Champernowne block is boundary-crossing for `n >= 4`; hence the
fixed-word, within-epoch normality argument has no vanishing boundary error
and does not control the displayed strict ordered block-collision statistic or
the complete C7 Fejer energy.  This report states no conclusion about pi,
C7, C2, or C1, makes no identification between block equality and infinite
suffix proximity, and schedules no follow-up.
