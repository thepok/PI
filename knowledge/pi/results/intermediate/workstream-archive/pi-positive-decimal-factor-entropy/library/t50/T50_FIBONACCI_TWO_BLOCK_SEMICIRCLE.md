# T50: exact semicircle classification for Fibonacci two-block digit codings

Status: `proof sketch` with a replayed exact 720-case `experiment`.

Scope: **non-pi sibling classification only**. Nothing in this note concerns
the decimal expansion of pi. In particular, it gives no resonance
amplification, Fejer-energy density, C1, or fixed-pi estimate.

The unverified T47 note suggested using rotation endpoints. No statement from
T47 is a premise here: every symbolic, extremal, decimal, and circle claim
used below is proved again.

## 1. Provenance

- Canonical local statement: `pi-positive-decimal-factor-entropy.txt`, copied
  byte-for-byte beside this note.
- Original source URL: none. The canonical question was formulated locally.
- Required SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Hash rechecked on 2026-08-02 by `verify.sh`.
- T50 is a sibling calculation. It does not alter or answer the canonical
  open question about pi.

## 2. Normalized statement and ambiguities

Put

```text
alpha = (3-sqrt(5))/2,    beta = 1-alpha,    delta = 1-2*alpha.
```

Thus `0 < delta < alpha < beta < 1`; `alpha` is irrational; and
`3*alpha > 1`. Define the zero-indexed Fibonacci word by

```text
f_n = floor((n+2)*alpha)-floor((n+1)*alpha),    n >= 0.    (2.1)
```

It begins `010010100100101...`. At every position use the *overlapping*
length-two factor and name the three possible factors

```text
A = 00,    B = 01,    C = 10.                              (2.2)
```

An ordered injective coding is a function `c` with

```text
a = c(A),    b = c(B),    c = c(C)                         (2.3)
```

three distinct members of `{0,...,9}`. The reuse of the letter `c` for both
the function and its value on `C` is avoided in the checker, where the digit
map is a dictionary; in displayed formulas lower-case `c` always means the
digit `c(C)`.

Define

```text
z_n = c(f_n f_(n+1)),
x_j = sum_(n>=0) z_(j+n)/10^(n+1),
K_c = closure in R/Z of {x_j : j>=0}.                       (2.4)
```

A closed semicircle is the image in `R/Z` of a closed real interval of length
at most `1/2`. T50 asks, separately for every coding, whether some such arc
contains `K_c`.

The conventions and potentially ambiguous quantifiers are:

1. The coding is ordered. The tuple `(a,b,c)` means the values on
   `(00,01,10)` in exactly that order.
2. There are `10*9*8=720` codings; no quotient by digit reflection, symbol
   reversal, or translation is taken.
3. Blocks overlap at every position. This is not a coding on disjoint pairs or
   on substitution boundaries.
4. Every suffix is used, including suffixes beginning with a leading zero.
5. Decimal values are defined by the series in (2.4), so no convention about
   suppressing leading zeroes is involved.
6. Closure is taken after circle projection. Section 8 proves that it is also
   the continuous image of the symbolic suffix closure.
7. The containing arc may depend on the coding.
8. Endpoints are included. An exact gap of length `1/2` gives a positive
   verdict.
9. The assertion is only this finite family classification. No statement is
   made about all two-block systems, other low-complexity words, or pi.

## 3. Fibonacci convention and factor language

This section verifies both the standard morphic convention and (2.2).

### Lemma 3.1 (mechanical and morphic words agree)

Let `sigma(0)=01` and `sigma(1)=0`. The word (2.1) satisfies
`sigma(f)=f`, begins in `0`, and is therefore the increasing-prefix limit of
`sigma^k(0)`.

Proof. Telescoping (2.1) shows that the number of ones in positions `0` through
`n` is `floor((n+2)*alpha)`. Hence the zero-indexed position of the `k`-th one
is

```text
p_k = floor(k/alpha)-1 = floor(k*phi^2)-1,                  (3.1)
```

where `phi=(1+sqrt(5))/2`, `alpha=1/phi^2`, and
`beta=1-alpha=1/phi`. Irrationality gives

```text
1-f_n = floor((n+2)*beta)-floor((n+1)*beta).
```

Thus the `k`-th zero is at

```text
m_k = floor(k/beta)-1 = floor(k*phi)-1.                    (3.2)
```

Every input letter in `sigma(f)` contributes an initial zero, and precisely
an input zero contributes a following one. The one following the `k`-th zero
therefore occurs at

```text
m_k + (k-1) + 1
  = floor(k*phi)-1+k
  = floor(k*phi^2)-1
  = p_k.                                                    (3.3)
```

So `sigma(f)` and `f` have the same one positions. Since `sigma(0)` starts in
`0`, the iterates of `0` are nested prefixes; fixedness and the initial zero
identify their limit with `f`. QED.

### Lemma 3.2 (exact length-two language)

The length-two factor language of `f` is exactly `{00,01,10}`.

Proof. Inside an image under `sigma`, the only length-two factor is `01`.
Every image starts with `0`. At a boundary, the preceding image ends in `1`
if its source letter was `0`, producing `10`, and ends in `0` if its source
letter was `1`, producing `00`. Thus no other pair can occur in the fixed
word. All three occur in the prefix `010010`. QED.

We will also use that `000` does not occur, including in the suffix closure.
For any intercept `t`, the sum of three consecutive mechanical digits is
`floor(t+3*alpha)-floor(t)`, after translating `t` by an integer if needed.
Since `3*alpha>1`, this sum is at least one. Therefore three consecutive
zeroes are impossible in every suffix. The set of binary words beginning in
`000` is a product-topology cylinder, so if a limit word in the suffix closure
contained `000` at a later position, all sufficiently close suffixes would
contain the same finite block there. Thus `000` is also impossible throughout
the closure.

## 4. Rotation model and density

For `0<=t<1`, define the lower mechanical word

```text
W(t)_n = floor(t+(n+1)*alpha)-floor(t+n*alpha).             (4.1)
```

Equation (2.1) says `f=W(alpha)`, and cancellation of integer parts gives

```text
shift^j(f) = W(frac((j+1)*alpha)).                          (4.2)
```

The forward orbit of an irrational rotation is dense. Here is the needed
self-contained argument. The closure of all integer multiples of `alpha` in
`R/Z` is a closed subgroup. If a closed subgroup has positive elements
arbitrarily close to zero, integer multiples of one such element make an
arbitrarily fine circle net, so the subgroup is the whole circle. Otherwise
it has a least positive element, which generates a finite cyclic subgroup.
The finite alternative would make a positive multiple of `alpha` integral,
contrary to irrationality. Compactness supplies positive multiples tending
to zero, so negative multiples are also limits of forward multiples. Hence
the forward orbit is dense.

### Lemma 4.1 (binary lexicographic monotonicity)

If `0<=s<t<1`, then `W(s)<_lex W(t)`.

Proof. The first `m` digit sum telescopes:

```text
sum_(n=0)^(m-1) W(t)_n = floor(t+m*alpha).                 (4.3)
```

For `s<t`, the difference between the two sides of (4.3) is always zero or
one. Density supplies an `m` for which an integer lies strictly between
`s+m*alpha` and `t+m*alpha`, so the words are not equal. At the first `m`
where their prefix sums differ, all earlier digits agree and the new digit is
zero for `W(s)` and one for `W(t)`. QED.

Let `X` be the product-topology closure of all binary suffixes of `f`. Density,
(4.2), and coordinatewise one-sided limits imply that the extrema of any
intercept interval belong to `X`; no unrecorded endpoint convention is being
assumed.

## 5. The three intercept cylinders and six endpoints

The first bit of `W(t)` is one exactly for `t>=beta`. Applying the same test
after one rotation gives the first two-block partition

```text
A=00 for 0 <= t < delta,
B=01 for delta <= t < beta,
C=10 for beta <= t < 1.                                   (5.1)
```

The exact one-sided endpoint words are

| intercept limit | binary word |
|---|---|
| `0` | `0f` |
| `delta-` | `001f` |
| `delta+` | `010f` |
| `beta-` | `01f` |
| `beta+` | `10f` |
| `1-` | `1f` |

For example, at `delta=1-2*alpha`, the two one-sided initial words are `001`
and `010`; for `n>=3` the common tail digit is

```text
floor((n-1)*alpha)-floor((n-2)*alpha) = f_(n-3).
```

At `beta=1-alpha`, the two initial words are `01` and `10`, followed by `f`;
at zero and one the initial digits are zero and one, followed by `f`. This
proves the complete table directly from (4.1). Density from the indicated
side puts all six words in `X`.

Let `P(u)_n=u_nu_(n+1)` be the overlapping-pair map and put

```text
Z = P(f) = BCABCBCA... .                                   (5.2)
```

Applying `P` to the endpoint table gives

| binary endpoint | pair-symbol endpoint |
|---|---|
| `0f` | `AZ` |
| `001f` | `ABCZ` |
| `010f` | `BCAZ` |
| `01f` | `BCZ` |
| `10f` | `CAZ` |
| `1f` | `CZ` |

These identities can also be checked letter by letter; the replay checks
their first 60 symbols as a convention guard, but their infinite validity is
the algebraic pair-map identity just proved.

## 6. Exact coded lexicographic extrema

The relative positions of `a` and `b` determine orientation inside every
first-symbol cylinder.

### Lemma 6.1 (only A and B can first disagree internally)

Suppose `P(u)` and `P(v)` have the same first symbol. At their first later
pair-symbol disagreement, the two symbols are `A=00` and `B=01`.

Proof. If the first disagreement is at position `k>=1`, equality of all
earlier overlapping pairs implies equality of the underlying bits through
position `k`. The differing pairs have the same first bit. If that bit were
one, both next bits would have to be zero because `11` is forbidden. Thus the
common bit is zero and the differing pairs are `00` and `01`. QED.

Combining Lemmas 4.1 and 6.1 with the endpoint table gives the exact extrema:

| cylinder | minimum if `a<b` | maximum if `a<b` | minimum if `b<a` | maximum if `b<a` |
|---|---|---|---|---|
| `A` | `AZ` | `ABCZ` | `ABCZ` | `AZ` |
| `B` | `BCAZ` | `BCZ` | `BCZ` | `BCAZ` |
| `C` | `CAZ` | `CZ` | `CZ` | `CAZ` |

For completeness, these inequalities pass from actual suffixes to `X` because
lexicographic lower and upper order intervals are closed in the product
topology: the complement is the union of cylinders witnessing a first
difference in the wrong direction. Every suffix intercept in a cylinder lies
between its two one-sided endpoints, closure preserves those inequalities,
and density supplies suffix intercepts converging to each endpoint. Thus both
bounds in every table entry are attained.

This is the complete lexicographic-extremum classification. The location of
`C` among the three output digits determines the order of the cylinders, but
not their internal orientation.

Decimal evaluation preserves these strict orders. At a first differing digit,
the leading difference is at least `10^(-(k+1))`; the entire later decimal
tail can cancel at most that amount. Equality would require one pair-symbol
tail to be constantly the digit 9 and the other constantly the digit 0.
Constant `B` and `C` tails violate overlap, while a constant `A` tail would
give `000`, excluded at the end of Section 3. Thus the decimal order is
strict, including when digits 0 and 9 are used.

## 7. Exact endpoint values and finite suffix bounds

Write

```text
zeta = sum_(n>=0) c(Z_n)/10^(n+1).                         (7.1)
```

The six endpoint values are exactly

```text
E(AZ)   = (a+zeta)/10,
E(ABCZ) = (100a+10b+c+zeta)/1000,
E(BCAZ) = (100b+10c+a+zeta)/1000,
E(BCZ)  = (10b+c+zeta)/100,
E(CAZ)  = (10c+a+zeta)/100,
E(CZ)   = (c+zeta)/10.                                    (7.2)
```

Every endpoint is therefore an affine expression `q+r*zeta` with rational
coefficients. Let

```text
m = min(a,b,c),    M = max(a,b,c).
```

Since `Z` begins in `B`, direct bounding of every later digit gives

```text
b/10 + m/90 <= zeta <= b/10 + M/90.                        (7.3)
```

This is not a numerical approximation. It is the exact geometric-series
bound

```text
sum_(n>=1) m/10^(n+1) <= tail <= sum_(n>=1) M/10^(n+1).
```

For an affine expression `q+r*zeta`, its exact certified interval is obtained
by substituting the two endpoints of (7.3), reversing them when `r<0`. The
checker uses Python `Fraction`, so every numerator, denominator, and comparison
in `certificates.json` is integer-exact.

## 8. Symbolic closure equals the infinite decimal suffix closure

Let `Y=P(X)` after applying the digit coding. The pair map, digit map, and
decimal evaluation are continuous in the product topology: agreement through
position `N-1` changes a decimal value by at most `10^(-N)`. Since `X` is
compact, its image is compact. Therefore

```text
K_c = {sum_(n>=0) y_n/10^(n+1) : y in Y}.                  (8.1)
```

Indeed, continuity sends every convergent suffix subsequence to its decimal
limit, and compactness supplies a convergent symbolic subsequence for every
limit of decimal suffix values. Thus the endpoint extrema above concern the
actual infinite closure in the acceptance sentence, not merely finite
suffixes or an enlarged cover.

## 9. Exhaustive circle-gap reduction

Sort the symbols `A,B,C` by their three distinct output digits. Values in a
lower first-digit cylinder precede values in a higher one on the real interval
`[0,1]`. The exact extrema in Section 6 therefore give two bounded gaps between
successive cylinders and one exterior circle gap from the last cylinder back
through `1=0` to the first. Their endpoints belong to `K_c`.

Every other complementary component lies inside the real convex hull of one
first-digit cylinder. Two points in such a cylinder have the same first digit,
so its diameter is at most

```text
sum_(n>=1) (M-m)/10^(n+1) = (M-m)/90 <= 1/10.              (9.1)
```

Hence no internal gap can have length `1/2`. There is no missing deeper-scale
case: every complementary component is one of the three top-level gaps or is
bounded by (9.1).

For a nonempty compact circle set, containment in a closed arc of length at
most `1/2` is equivalent to the complement containing an open arc of length
at least `1/2`. In one direction take the complementary open arc; in the other
take the closed complement of the vacant arc. Equality is valid because the
containing arc is closed. Consequently

```text
K_c is in a closed semicircle
iff at least one of the three top-level gaps has length >= 1/2.   (9.2)
```

This proves both directions needed by each certificate: one certified large
gap proves containment, while strict upper bounds below `1/2` for all three,
together with (9.1), prove non-containment.

## 10. The six exact gap triples

The following table expands (7.2) and the cylinder-extremum table. Each row is
ordered as exterior gap, first internal gap, second internal gap, where the
internal cylinders follow the displayed digit order.

| digit order | exterior gap | first internal gap | second internal gap |
|---|---|---|---|
| `A<B<C` | `1+(a-c)/10` | `9(10b+c-11a)/1000` | `(9c+a-10b)/100` |
| `A<C<B` | `1+(10a-10b-c+9zeta)/100` | `(99c-90a-10b+9zeta)/1000` | `(100b-90c+a-99zeta)/1000` |
| `B<A<C` | `1+(10b-9c-a)/100` | `9(11a-10b-c)/1000` | `(c-a)/10` |
| `B<C<A` | `1+(-10a+10b+c-9zeta)/100` | `(90c-100b-a+99zeta)/1000` | `(90a+10b-99c-9zeta)/1000` |
| `C<A<B` | `1+(a-10b+9c)/100` | `(a-c)/10` | `9(10b+c-11a)/1000` |
| `C<B<A` | `1+(c-a)/10` | `(10b-9c-a)/100` | `9(11a-10b-c)/1000` |

Only the two orders with `C` in the middle involve `zeta`. For those rows the
checker applies (7.3) with the sign of the displayed coefficient. In all 720
cases this one-symbol tail bound already decides (9.2); there are no unresolved
intervals.

The table can be audited without trusting handwritten algebra: the checker
constructs every endpoint from the prefix in (7.2), subtracts the appropriate
maximum from the next minimum, and records the resulting affine coefficients.

## 11. Exact checker and classification

Run

```text
python3 t50_checker.py --verify certificates.json
```

or run `./verify.sh`, which first verifies artifact hashes. The checker:

1. enumerates `itertools.permutations(range(10),3)` in `(A,B,C)` order;
2. rejects no cases and asserts there are exactly 720 distinct tuples;
3. constructs the six affine endpoint values from their finite prefixes;
4. selects cylinder orientation from the exact comparison `a<b`;
5. sorts the cylinders by their output digits;
6. constructs the two bounded and one exterior gap by exact affine
   subtraction;
7. bounds every gap using (7.3), with rational sign handling;
8. gives `contained` only when a gap lower bound is at least `1/2`;
9. gives `not_contained` only when all top-level upper bounds and (9.1) are
   strictly below `1/2`;
10. fails if a coding is duplicated, omitted, or unresolved;
11. recomputes and compares every field of `certificates.json`.

The replayed classification is:

| relative digit order | codings | contained | not contained | exact-half cases |
|---|---:|---:|---:|---:|
| `A<B<C` | 120 | 90 | 30 | 20 |
| `A<C<B` | 120 | 80 | 40 | 0 |
| `B<A<C` | 120 | 90 | 30 | 10 |
| `B<C<A` | 120 | 80 | 40 | 0 |
| `C<A<B` | 120 | 90 | 30 | 10 |
| `C<B<A` | 120 | 90 | 30 | 20 |
| **total** | **720** | **520** | **200** | **60** |

The 60 equality cases are exactly characterized as follows. If `C>A`, they
have `C-A=5` and `B<C`. If `C<A`, they have `A-C=5` and `B>C`. The chosen gap
then has exact affine coefficient of `zeta` equal to zero and exact length
`1/2`; the certificate records zero margin. The other 460 contained cases have
a strictly positive certified margin. Every one of the 200 negative cases has
strict certified upper bounds for all circle gaps.

`certificates.json` contains, for every coding:

- the digit tuple and relative order;
- the exact rational interval for `zeta`;
- all six symbolic cylinder extrema;
- each top-level gap as `q+r*zeta`;
- exact rational lower and upper bounds for each gap;
- the internal-gap upper bound;
- the verdict and the decisive rational margin.

Thus the JSON is a replayable case split, not a table of asserted verdicts.

## 12. Literature and infrastructure search

Search date: 2026-08-02.

| Search | Result and use |
|---|---|
| arXiv `Sturmian lexicographic order` | Bucci, De Luca, and Zamboni, *Some characterizations of Sturmian words in terms of the lexicographic order*, arXiv:1205.5946, `https://arxiv.org/abs/1205.5946`, journal DOI `10.3233/FI-2012-665`. This confirms that lexicographic Sturmian questions have literature, but no theorem from the paper is used here. |
| Local Lean/mathlib search for mechanical/Sturmian infrastructure | No reusable project theorem encoding the required mechanical-word endpoints was found. No Lean artifact is claimed. |
| Search for this exact 720-case decimal semicircle classification | No exact source was identified. This is not a novelty claim and the item is not labeled `literature-checked`. |

Because the proof above is elementary and self-contained, no external
mathematical assertion is imported from this search.

## 13. Scope and status

The prose argument is a `proof sketch` pending independent skeptical review.
The 720-case arithmetic is an exact replayed `experiment`; finite arithmetic
alone is not the proof of the infinite claim. Its connection to the infinite
closure is supplied by Sections 4-9: density and one-sided endpoints give the
exact symbolic extrema, continuity identifies the closure, and the universal
diameter bound exhausts all deeper gaps.

The resulting sibling classification is:

```text
520 of the 720 injective two-block Fibonacci digit codings have suffix-orbit
closures contained in a closed semicircle; 200 do not.
```

This statement is solely about the fixed Fibonacci sibling family. It gives
no conclusion about pi, C1, resonance amplification, Fejer energy, or any
fixed-pi estimate.
