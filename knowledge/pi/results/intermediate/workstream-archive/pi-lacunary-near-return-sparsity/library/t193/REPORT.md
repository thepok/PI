# T193: bounded adjacent explicit-arithmetic scout

## Scope and normalization

This is a `literature-checked` source transcription plus elementary algebraic
screens and one finite calculation. It is a related-model survey only. It
makes no assertion about the decimal orbit of pi or about any named program
conjecture.

`canonical_statement.txt` is byte-identical to the supplied canonical problem
statement; its SHA-256 is
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
The canonical count there uses ordered pairs and includes diagonal pairs.

For a word `x`, define the ordered, diagonal-inclusive length-`m` block energy

```text
E_x(m,N) = sum_w c_x(w;m,N)^2,
c_x(w;m,N) = |{0 <= j < N : x_j ... x_(j+m-1) = w}|.
```

There are exactly `N` overlapping starts, so this is the required normalization.
At the common algebraic screen size `N=10^16`,

```text
m = floor((1/4) log_10 N) = floor(4) = 4.
```

The comparison value `N^2 10^(-m)` is only a decimal-uniform related-model
benchmark. No inference about pi is made from it.

## Bounded search and comparison boundary

Exactly three dated primary source/theorem tuples were inspected, one in each
of the three required domains; see `SOURCE_LEDGER.csv`. Thus the eight-tuple
cap is met (`3 <= 8`) and domain coverage is exact (`3` distinct domains).
Each retained card has a distinct source, locator, and normalized mechanism
fingerprint. `ACCEPTED_RECORDS.csv` is the complete accepted-record index
through T190 in the supplied library snapshot. `ACCEPTED_BOUNDARIES.csv`
records the family-level comparison boundary. Both are exclusion maps, not
mathematical premises.
In particular, the source identifiers and fingerprints in `SOURCE_LEDGER.csv`
are absent from its reserved-source and closed-family rows. No source already
audited there is presented as new.

## F: ternary product coefficient recurrence

**Domain.** Mahler or functional-equation constants with explicit coefficient
recurrences.

**Pinned source and locator.** Han--Wu, *Explicit evaluations of the Hankel
determinants of a Thue--Morse-like sequence*, arXiv:1406.1594v1, dated
2014-06-06, PDF p. 2 / text lines 74--88, defines
`P_3(x;J)=product_{k>=0}(1+J x^(3^k))=sum c_n x^n`, where
`J=(-1+i sqrt(3))/2`, and gives the exact all-`n>=0` recurrence

```text
c_0=1,  c_(3n)=c_n,  c_(3n+1)=J c_n,  c_(3n+2)=0.                 (F.1)
```

The same source's Theorem 1, PDF p. 3 / text lines 104--137, gives a separate
all-`n>=0` recurrence for its Hankel determinants. The retained mechanism here
is (F.1), not its determinant conclusion.

**Fingerprint and nonduplication.**
`ternary_product_functional_equation -> zero_digit_coefficient_recurrence`.
The nearest accepted closed branch is the general Mahler/automatic symbolic
family recorded in `ACCEPTED_BOUNDARIES.csv`; this card does not use a
substitution Fourier ray, a Mahler-value approximation theorem, or a
previously recorded source tuple.

**Algebraic discriminator at logarithmic depth.** The alphabet in (F.1) is
contained in `{0,1,J,J^2}`, so at `m=4` there are at most `4^4=256` blocks.
Cauchy--Schwarz gives the exact all-prefix inequality

```text
E_c(4,N) >= N^2/256.
```

At `N=10^16`, this is `N^2/256`, at least `10000/256 = 39.0625` times the
decimal-uniform benchmark `N^2/10000`. This is an algebraic model rejection,
not finite evidence.

**Additional unproved transfer hypothesis (conjecture).** To apply this toward
T7, there would have to be a carry-safe, all-prefix factor map from the decimal
orbit to a coding whose length-`m` multiplicities are *upper* controlled by an
effective refinement of (F.1), uniformly at every required depth and prefix.
Neither the source nor this survey supplies such a map or such an upper bound.

**Verdict: close.** The available finite-alphabet recurrence enforces a lower
energy floor in the opposite direction.

## H: apwenian Hankel/Pade mechanism

**Domain.** Pade or Hankel-determinant irrationality mechanisms for explicit
constants.

**Pinned source and locator.** Guo--Han--Wu, *Criteria for apwenian sequences*,
arXiv:2001.10246v5, dated 2021-06-28, defines
`f_p(z)=product_{i>=0} P(z^(p^i))` for integer `p>=2`,
`P(z)=sum_{r=0}^{p-1}v_r z^r`, `v_0=1`, and `v_r in {-1,1}`. Theorem 1.3
(PDF p. 4 / text lines 176--183) states: for odd `p>=3`, `b>=2`, with
`P(b^(-p^i)) != 0` for every `i>=0`, periodic extension of the `v_r`, and
the displayed congruences for every `0<=j<=p-2`, `f_p(1/b)` is transcendental
and has irrationality exponent exactly 2. The source's Pade prerequisite is
also explicit: nonzero `H_n` yields the `[n-1/n]` approximant and its stated
error expansion (PDF p. 2 / text lines 65--83).

For the concrete source-admissible model take `p=3`,
`P(z)=1+z-z^2`, and `b=2`. The two displayed congruences are respectively
`(1+1-1-(-1))/2=1` and `(1+(-1)-1-1)/2=-1`, both `1 mod 2`. For every
`i>=0`, `x=2^(-3^i)` satisfies `0<x<=1/2`, so
`P(x)=1+x-x^2>=1+x/2>0`; hence the source condition
`P(b^(-p^i)) != 0` is checked at the required powers `2^(-3^i)`. Thus every
hypothesis of Theorem 1.3 is stated and checked.

**Fingerprint and nonduplication.**
`apwenian_nonzero_Hankel -> Pade_approximants -> rational_irrationality_exponent`.
The nearest accepted closed branch is the recorded Pade/interpolation
determinant-occupancy boundary. The new tuple is not a replay of that source;
its discriminator is the source's scalar rational-approximation output, which
does not encode an ordered block-energy upper bound or a lacunary sum.

**Algebraic discriminator at logarithmic depth.** Its coefficient word has
alphabet `{ -1,1 }`; hence exactly as above

```text
E_d(4,N) >= N^2/2^4 = N^2/16.
```

At `N=10^16`, this is `10000/16=625` times the benchmark. The calculation is
an elementary alphabet-cardinality bound, not a claim that the theorem implies
this energy statement.

**Additional unproved transfer hypothesis (conjecture).** To reach T10 or T64,
one would need a uniform, carry-safe representation of every required decimal
lacunary phase as source-admissible Pade data, together with a theorem turning
its denominator/error data into the needed all-frequency exponential-sum bound.
The source only treats one scalar value at rational `1/b`; it gives neither
uniform phase representation nor that conversion.

**Verdict: close.** Scalar irrationality exponent information and the binary
energy floor both fail the required directional transfer.

## R: rational-diagonal automatic residues

**Domain.** Base-compatible rational or automatic generating functions.

**Pinned source and locator.** Rowland--Yassawi, *Automatic congruences for
diagonals of rational functions*, arXiv:1310.8635v2, dated 2014-04-23,
Theorem 2.1, PDF p. 7 / text lines 314--387: for polynomials
`R,Q in Z_p[x_1,...,x_k]` with `Q(0,...,0) not congruent to 0 mod p` and every
`alpha>=1`, the coefficient sequence of `D(R/Q) mod p^alpha` is `p`-automatic.

Take `p=2`, `alpha=1`, `R=1`, and `Q=1-x-y`. The denominator condition holds.
The diagonal coefficient is `a_n=binom(2n,n)`, since
`(1-x-y)^(-1)=sum_{r>=0}(x+y)^r`; therefore the theorem applies and yields a
base-2 automatic residue word. The identity
`binom(2n,n)=2*binom(2n-1,n-1)` gives `a_0=1` and `a_n=0 mod 2` for `n>=1`.

**Fingerprint and nonduplication.**
`rational_diagonal -> prime_power_decimation_automaton -> residue_word`.
The nearest accepted closed branch is the automatic rational-phase family in
the boundary ledger. This is distinct: it uses a rational diagonal and its
decimation automaton, not an automatic coefficient against a rational phase.

**Explicit discriminator at logarithmic depth.** For all `N>=1`, the length-4
blocks among starts `0,...,N-1` are one `1000` block and `N-1` copies of
`0000`. Consequently

```text
E_a(4,N) = 1 + (N-1)^2.
```

At `N=10^16`, this exceeds the benchmark by more than `9999`; the exact integer
is independently reproduced by `calculation.py`. This is a finite calculation
of the model plus an elementary formula, never evidence about pi.

**Additional unproved transfer hypothesis (conjecture).** To use this toward
T7, the decimal orbit would need a carry-safe factor through a rational
diagonal modulo powers compatible with decimal cylinder equality, and a
uniform anti-concentration theorem for that factor. The displayed model instead
has a single dominant residue block; the source supplies no decimal factor map.

**Verdict: close.** This base-compatible rational mechanism is maximally
concentrated at the screen scale.

## Endpoint

There are exactly three retained candidates and exactly one verdict on each,
all `close`. The three normalized fingerprints are distinct, every transfer is
explicitly a conjecture, and the finite calculation is labeled as such. No
candidate survives, so no successor is selected.

Replay from a directory containing only these artifacts:

```text
python3 verify_t193.py
python3 calculation.py
sha256sum -c SHA256SUMS
```
