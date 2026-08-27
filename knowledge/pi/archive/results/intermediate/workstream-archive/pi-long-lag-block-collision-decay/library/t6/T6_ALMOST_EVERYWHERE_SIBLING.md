# Ordered long-lag block collisions in a random decimal stream

Status: `proof sketch` (a complete prose proof of an almost-everywhere sibling,
not machine-checked and not a claim about pi).

## Provenance and scope

- Agenda item: T6, serving G2.
- Canonical local statement:
  `knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`.
- Canonical SHA-256, verified on 2026-07-24:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
- Original source URL: none. The canonical file says that the problem was
  formulated locally by this system on 2026-07-23.
- External literature is not used as a premise. The proof below uses only the
  elementary first-moment bound, a directly proved dependency-graph variance
  bound, Markov's inequality, Chebyshev's inequality, and the first
  Borel--Cantelli lemma.

The canonical question concerns the one prescribed decimal stream of pi and is
OPEN. This note proves a sibling statement for an i.i.d. stream, equivalently
for Lebesgue-almost every real number. An almost-everywhere theorem cannot be
specialized to pi.

## 1. Normalized sibling statement

Let `(X_k)_(k>=1)` be independent random variables, each uniform on
`D={0,...,9}`. For integers `i>=0` and `m>=1`, put

```text
B(i,m)=(X_(i+1),...,X_(i+m)).
```

For positive integers `m,N`, define the **ordered** count

```text
R(m,N)=#{(i,j) in {0,...,N-1}^2:
          |i-j|>=m and B(i,m)=B(j,m)}.
```

Thus the diagonal and every pair of overlapping compared blocks are excluded.
The blocks belonging to two different comparison events may nevertheless
overlap; this is the dependence handled in Section 4.

**Almost-everywhere sibling claim.** With probability one,

```text
for every real s with 0<s<1,
  there exists a real C=C(X,s)>=1 such that
    for every pair of integers m,N>=1,
      R(m,N) <= C*(N+N^2*10^(-s*m)).                 (1.1)
```

Under decimal coding, the same assertion holds for Lebesgue-almost every real
`alpha`, with `C=C(alpha,s)`. In particular, the constant is selected after
`alpha` and `s`, but before both `m` and `N`.

The quantifier order, additive `N`, ordered-pair convention, and weak lag
inequality in (1.1) are all part of the claim. We do not assert the endpoint
`s=1`, a constant independent of `alpha` or `s`, or the claim for every stream.

## 2. Recorded ambiguities resolved

1. `C` may depend on the realized stream (equivalently `alpha`) and on `s`, but
   not on `m` or `N`.
2. Both orientations `(i,j)` and `(j,i)` are counted.
3. The cutoff is exactly `|i-j|>=m`, so each individual comparison uses two
   disjoint length-`m` digit intervals.
4. The right side is the sum `N+N^2*10^(-s*m)`, not only its second term.
5. The assertion is simultaneous over all positive `m,N`, not asymptotic in
   either variable.
6. Decimal rationals have two expansions. They form a countable null set and
   are removed when passing from product measure to Lebesgue measure.

## 3. Reduction to unordered indicators and the first moment

Fix `m,N>=1` and write

```text
p=p_m=10^(-m).
```

Let `E_(m,N)` be the set of unordered pairs `e={i,j}` with
`0<=i<j<N` and `j-i>=m`. For `e={i,j}`, let

```text
I_e = 1_{B(i,m)=B(j,m)},       U(m,N)=sum_(e in E_(m,N)) I_e.
```

### Reduction 3.1 (ordered versus unordered)

Every admissible unordered pair has exactly two orientations, so, pointwise,

```text
R(m,N)=2U(m,N).                                      (3.1)
```

If `N<=m`, both sides vanish. If `N>m`, the number `M=|E_(m,N)|` is

```text
M=sum_(r=m)^(N-1) (N-r)
 =(N-m)(N-m+1)/2 <= N^2/2.                          (3.2)
```

### Estimate 3.2 (one comparison)

For `e={i,j}` in `E_(m,N)`, the two digit intervals are disjoint because
`j-i>=m`. After the first block is exposed, the independent second block has
exactly one favorable value among `10^m` equally likely words. Hence

```text
P(I_e=1)=p=10^(-m).                                  (3.3)
```

It follows from (3.1)--(3.3) that

```text
E[R(m,N)]=2Mp <= N^2 p.                              (3.4)
```

No independence among all the `I_e` is asserted here.

## 4. Explicit dependency range and variance

For a start `a`, the block `B(a,m)` uses digit coordinates
`{a+1,...,a+m}`. A block starting at `b` intersects it only if

```text
|a-b| <= m-1.
```

There are at most `2m-1` valid starts `b` with this property, after truncation
to `{0,...,N-1}`.

### Estimate 4.1 (dependency degree)

Fix `e={i,j}`. A comparison `f={k,l}` has digit support intersecting that of
`e` only if at least one of `k,l` is among the starts whose block intersects
the block at `i` or the block at `j`. The union of those possible starts has
size at most

```text
2(2m-1)=4m-2.
```

For each such start there are fewer than `N` choices for the other endpoint.
This overcounts and also retains pairs that fail the long-lag condition, so it
is a valid upper bound. Thus every `I_e` has at most

```text
D=(4m-2)N < 4mN                                    (4.1)
```

other potentially dependent indicators. If the two digit supports are
disjoint, the corresponding indicators are functions of disjoint families of
independent digits and therefore are independent.

### Estimate 4.2 (variance with overlaps retained)

For every `e`, `Var(I_e)<=E[I_e]=p`. For distinct dependent `e,f`, no favorable
joint probability estimate is assumed; the crude bound

```text
Cov(I_e,I_f) <= E[I_e I_f] <= E[I_e]=p              (4.2)
```

is enough. There are at most `MD/2` unordered dependent pairs `{e,f}`. Using
zero covariance for disjoint supports, (4.2) for the rest, and (3.2),

```text
Var(U)
 = sum_e Var(I_e) + 2 sum_{e<f} Cov(I_e,I_f)
 <= Mp + 2*(MD/2)*p
 = Mp(1+D).                                          (4.3)
```

Since `R=2U`, (3.2), (4.1), and `mN>=1` give the explicit bound

```text
Var(R)
 =4 Var(U)
 <=2N^2 p(1+4mN)
 <=10mN^3 p.                                         (4.4)
```

This is where all dependencies caused by overlapping comparison events are
accounted for. The estimate is deliberately coarse, but its `N^3` loss is
still summable after the scale split below.

## 5. Dyadic tail bounds at one exponent

Fix for this section one real `s` with `0<s<1`. Let

```text
D_2={1,2,4,8,...}.
```

For each `m`, retain `p=10^(-m)` and split dyadic `N` at `p^(-s)=10^(sm)`.

### Estimate 5.1 (sparse regime)

Suppose `N` is dyadic and `N<p^(-s)`. Markov's inequality and (3.4) imply

```text
P(R(m,N)>N) <= E[R(m,N)]/N <= Np.                   (5.1)
```

For every `A>0`, the sum of all dyadic positive integers strictly below `A`
is less than `2A`. Therefore, for each fixed `m`,

```text
sum_{N in D_2, N<p^(-s)} P(R(m,N)>N)
 <= p * sum_{N in D_2, N<p^(-s)} N
 < 2p*p^(-s)
 = 2p^(1-s).                                         (5.2)
```

### Estimate 5.2 (dense regime)

Suppose `N` is dyadic and `N>=p^(-s)`. Because `0<p<1` and `s<1`,
`p<=p^s`; hence (3.4) gives `E[R]<=N^2p^s`. Thus

```text
{R(m,N)>3N^2p^s}
 subseteq {R(m,N)-E[R(m,N)]>2N^2p^s}.
```

Chebyshev's inequality and (4.4) now give

```text
P(R(m,N)>3N^2p^s)
 <= (10mN^3p)/(4N^4p^(2s))
 = (5/2)m*p^(1-2s)/N.                               (5.3)
```

If `N_0` is the least dyadic integer at least `A`, then
`sum_(N in D_2,N>=A) 1/N=2/N_0<=2/A`. Taking `A=p^(-s)` in (5.3) yields

```text
sum_{N in D_2, N>=p^(-s)} P(R(m,N)>3N^2p^s)
 <= 5m*p^(1-s).                                      (5.4)
```

### Estimate 5.3 (summability over every block length)

Put `rho=10^(-(1-s))`, so `0<rho<1` and `p^(1-s)=rho^m`. Adding (5.2) and
(5.4), then summing over every integer `m>=1`, gives the explicit finite bound

```text
sum_{m>=1} (2+5m)rho^m
 = 2rho/(1-rho) + 5rho/(1-rho)^2
 < infinity.                                         (5.5)
```

The first Borel--Cantelli lemma requires no independence between these bad
events. Equation (5.5) therefore says that, with probability one, only
finitely many dyadic pairs `(m,N)` violate their applicable estimate:

```text
R(m,N)<=N                    when N<p^(-s),           (5.6)
R(m,N)<=3N^2p^s              when N>=p^(-s).          (5.7)
```

## 6. Uniform dyadic constant and all positive N

Fix a stream in the probability-one event obtained in Section 5. Let `F_s` be
its finite set of exceptional dyadic pairs. Define, with the inner maximum
omitted when `F_s` is empty,

```text
K_s=max(3,
        max_{(m,N) in F_s}
          R(m,N)/(N+N^2*10^(-s*m))).                 (6.1)
```

The denominator is positive and `F_s` is finite, so `K_s` is finite. Outside
`F_s`, either (5.6) or (5.7) applies, and each is at most
`3(N+N^2*10^(-s*m))`. By (6.1), for every positive `m` and every dyadic `N`,

```text
R(m,N)<=K_s*(N+N^2*10^(-s*m)).                       (6.2)
```

### Reduction 6.1 (dyadic N to every N)

For an arbitrary positive integer `N`, choose the least dyadic `n>=N`. Then
`N<=n<2N`. Enlarging the set of allowed starts cannot decrease the collision
count, so `R(m,N)<=R(m,n)`. Applying (6.2),

```text
R(m,N)
 <= K_s*(n+n^2*10^(-s*m))
 <= K_s*(2N+4N^2*10^(-s*m))
 <= 4K_s*(N+N^2*10^(-s*m)).                          (6.3)
```

Thus for this fixed `s`, one may take `C_s=4K_s>=12`, selected before all
positive `m,N`.

## 7. Countable-exponent reduction

Section 5 was proved for an arbitrary fixed `s`, so it supplies a
probability-one set `Omega_q` for each rational `q` in `(0,1)`. The set

```text
Omega_* = intersection_{q rational, 0<q<1} Omega_q
```

still has probability one because the intersection is countable.

Fix a stream in `Omega_*` and an arbitrary real `s` with `0<s<1`. Choose a
rational `q` with `s<q<1`. Section 6 supplies one `C_q` such that for all
positive `m,N`,

```text
R(m,N)<=C_q*(N+N^2*10^(-q*m))
       <=C_q*(N+N^2*10^(-s*m)),                      (7.1)
```

because `10^(-q*m)<=10^(-s*m)`. Set `C(X,s)=C_q`. This proves the exact order

```text
with probability one: forall s, exists C(X,s), forall m,N.
```

It does not interchange the full-measure set with an uncountable intersection;
the rational exponent reduction is precisely what avoids that error.

## 8. Passage to Lebesgue-almost every alpha

The decimal coding map

```text
Phi(X)=sum_(k>=1) X_k*10^(-k)
```

is `[0,1]`-valued (the all-9 stream maps to `1`) and pushes the uniform product
measure on `D^N` to Lebesgue measure on `[0,1]`:
every length-`L` decimal cylinder has product probability `10^(-L)` and maps,
apart from endpoints, to an interval of the same length; these cylinders
generate the Borel sigma-algebra. The numbers with two decimal expansions are
decimal rationals, together with the harmless endpoint coding, form a
countable Lebesgue-null set. Consequently the digits of Lebesgue-almost every
`alpha` in `[0,1)` have the product law used above.

Applying the result to the fractional part, then taking the countable union of
null exceptional sets over integer translates, gives the same conclusion for
Lebesgue-almost every real `alpha`.

## 9. Conclusion and non-specialization warning

**Verdict: complete almost-everywhere sibling proof at prose level.** The
argument establishes (1.1) for an i.i.d. uniform decimal stream and hence for
Lebesgue-almost every real `alpha`. Its explicit dependence estimate is
`D<4mN`, its variance estimate is (4.4), and its total fixed-exponent bad-event
sum is bounded by (5.5).

This result is labeled `proof sketch` under the project vocabulary because it
is a prose note awaiting independent checking; it is not `machine-checked`.
Most importantly, it does **not** establish, refute, or heuristically confirm
the canonical claim for pi. Membership of pi in this full-measure set is not
known and does not follow from normality, finite computation, or the fact that
the exceptional set has Lebesgue measure zero. The fixed-pi canonical question
therefore remains OPEN.
