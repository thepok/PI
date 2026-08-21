# T93: the fixed Stoneham sibling alpha_(10,7)

Date: 2026-08-09 UTC.

Result label: `proof sketch`. The exact bibliographic statements and locators
are `literature-checked` against the bounded two-source corpus in
`SOURCE_PINS.md`; no exhaustive-search or novelty claim is made. This note
gives an elementary, fully quantified argument, but no Lean formalization. It
is a sibling model under canonical ambiguity A13. It makes no conclusion about
`pi`, C1, or C2.

## 1. Immutable statement and scope

The byte-exact canonical statement is delivered as `canonical_statement.txt`.
Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The canonical question concerns the ordered, diagonal-inclusive, strict
circle-distance statistic for the fixed base-10 orbit of `pi`, with quantifiers
`forall A, exists n0, forall n >= n0, exists N`. This note changes the named
point and studies the stronger off-diagonal pair-correlation statistic. It does
not establish or refute the canonical question.

Fix

```text
alpha = alpha_(10,7) = sum_(k>=1) 1/(7^k * 10^(7^k)),
x_n = {10^n * alpha}, n >= 1.
```

For real `s >= 0` and integer `N >= 1`, define

```text
F_N(s) = (1/N) * #{(i,j): 1 <= i != j <= N,
                            ||x_i-x_j||_(R/Z) <= s/N}.
```

Pairs are ordered, the diagonal is excluded, distance is circular, and the
inequality is non-strict, exactly as in the pinned source definition. The
sequence has Poissonian pair correlation (PPC) iff

```text
for every real s >= 0, lim_(N->infinity) F_N(s) = 2*s.       (1.1)
```

We prove the negation with `s=1` and the integer subsequence `N=10^w`:

```text
liminf_(w->infinity) F_(10^w)(1) >= 54/19 > 2.              (1.2)
```

This is stronger than finite statistics and does not use normality.

### Quantifier and normalization ambiguities

1. The source indexes its PPC statistic by `1 <= l != m <= N`; (1.1) uses the
   same positive-index convention.
2. An auxiliary count below uses indices `0,...,N-1`. All retained pairs from
   that count have indices at least 7, so they are also pairs in `1,...,N` at
   the same threshold `1/N`; no asymptotic shift assertion is assumed.
3. Equality of rational truncations is only a device. The actual irrational
   orbit points are not asserted to be equal.
4. The proof supplies a lower bound from selected pairs. It does not classify
   all close pairs and does not infer a weak near-return conclusion.

## 2. Exact primary-source theorem

Larcher--Stockinger define PPC on preprint pp. 1--2, equation (1), and state on
preprint p. 4, Theorem 3:

```text
The sequence ({2^n alpha_(2,3)})_(n in N) does not have
Poissonian pair correlations,
```

where

```text
alpha_(2,3) = sum_(m>=1) 1/(3^m * 2^(3^m)).
```

The proof is on preprint pp. 14--16 (`larcher-stockinger-...txt`, lines
723--840). It chooses `s=1`, `N=2^w`, and compares repeated rational-period
residues with the small omitted tail. The source theorem is only about
`(2,3)`; it is not cited as a theorem about `(10,7)`.

Stoneham's original paper defines on journal p. 372, equation (1.0), the
family

```text
w(g,p) = sum_(k>=1) 1/(p^k * g^(p^k))
```

for odd prime `p` and primitive root `g modulo p^2`. Thus the fixed number in
this note is the member `w(10,7)`. Stoneham's normality statement is not used.

## 3. Multiplicative order at every power of 7

### Lemma 3.1

For every integer `q >= 1`,

```text
ord_(7^q)(10) = 6 * 7^(q-1) = phi(7^q).                    (3.1)
```

### Proof

Modulo 7,

```text
10 = 3, 3^2 = 2, 3^3 = -1, 3^6 = 1,
```

so the order is 6. Also

```text
10^6 - 1 = 999999 = 7 * 142857,
142857 = 1 (mod 7),
```

and hence `v_7(10^6-1)=1`.

For completeness, the needed lifting calculation is elementary. If
`U=1+7c` with `7` not dividing `c`, binomial expansion gives inductively

```text
v_7(U^(7^r)-1) = r+1.                                    (3.2)
```

Indeed, if `V=1+7^(r+1)d` with `7` not dividing `d`, then the linear term in
`V^7-1` is `7^(r+2)d`; every term of degree at least two is divisible by
`7^(r+3)`. If `m=7^r c0` with `7` not dividing `c0`, a second binomial
expansion after raising to `c0` leaves the valuation unchanged. Applying this
to `U=10^6` yields

```text
v_7(10^(6m)-1) = 1 + v_7(m).                              (3.3)
```

If `10^d=1 (mod 7^q)`, reduction modulo 7 first gives `6 | d`; write `d=6m`.
Equation (3.3) then forces `7^(q-1) | m`. Conversely (3.3) shows that
`d=6*7^(q-1)` works. This proves (3.1), not merely primitivity modulo 7 or 49.

One consequence used later is

```text
v_7(10^Pq - 1) = q, Pq := 6*7^(q-1).                     (3.4)
```

## 4. Rational skeleton and tail

For `n >= 0`, let `q(n)=0` if `n<7`, and otherwise let `q(n)` be the unique
integer `q>=1` with `7^q <= n < 7^(q+1)`. Define

```text
z_n   = {sum_(1<=k<=q(n)) 10^(n-7^k)/7^k},
tau_n =  sum_(k>q(n))      10^(n-7^k)/7^k.               (4.1)
```

For `q=q(n)>=1`, `z_n` is a multiple of `1/7^q`, so
`z_n <= 1-1/7^q`. Since `n <= 7^(q+1)-1`,

```text
0 < tau_n <= (1/10) * sum_(k=q+1)^infinity 1/7^k
          = 1/(60*7^q) < 1/7^q.                          (4.2)
```

For `q=0`, `z_n=0` and the same direct geometric bound is below 1. Therefore
there is no hidden wrap modulo one:

```text
x_n = z_n + tau_n.                                       (4.3)
```

Multiplying active terms by 10 gives the exact recurrence

```text
z_0 = 0,
z_n = {10*z_(n-1) + r_n},
r_n = 1/n if n=7^q for some q>=1, and r_n=0 otherwise.    (4.4)
```

At an injection time, write `z_(7^q-1)=a/7^(q-1)` (also valid with `a=0`
when `q=1`). Then

```text
z_(7^q) = {(70*a+1)/7^q} = u_q/7^q,
u_q = 1 (mod 7).                                         (4.5)
```

Thus `u_q` is a unit. There is no further injection in the block

```text
B_q = {7^q,...,7^(q+1)-1},
```

so, for `0 <= j < 6*7^q`,

```text
z_(7^q+j) = (u_q * 10^j mod 7^q)/7^q.                   (4.6)
```

By (3.1), one period of length `P_q=6*7^(q-1)` visits every unit residue
modulo `7^q` once. The block length is exactly `7*P_q`. Hence:

```text
Every reduced residue of exact denominator 7^q occurs exactly seven times
among (z_n)_(n in B_q), at indices separated by multiples of P_q. (4.7)
```

Also `z_0=...=z_6=0`. Values from different blocks cannot coincide because
their fractions have different reduced denominators.

## 5. Exact repeated-pair count below N=10^w

Fix an integer `w>=1`, put `N=10^w`, and let `ell>=1` be uniquely determined
by

```text
A := 7^ell < N < 7^(ell+1).                              (5.1)
```

The inequalities are strict because powers of 7 and positive powers of 10
cannot agree. Put

```text
P := 6*7^(ell-1) = 6*A/7,
H := N-A = a*P+b, 0 <= b < P.                            (5.2)
```

As `0<H<7P`, the quotient satisfies `a in {0,...,6}`.

Among `z_0,...,z_(A-1)`, equations (4.7) and the initial zero block give
exactly `A/7` distinct values, each with multiplicity seven. Their ordered,
off-diagonal repeated-pair count is therefore

```text
(A/7)*7*6 = 6*A.                                         (5.3)
```

In the partial block `B_ell`, the first `H=aP+b` terms make `a` complete
periods and then visit `b` residues once more. Exactly `b` residues have
multiplicity `a+1`, and `P-b` have multiplicity `a`. Their ordered count is

```text
(P-b)*a*(a-1) + b*(a+1)*a = P*a*(a-1)+2*a*b.             (5.4)
```

Thus the exact number of ordered pairs `(n,m)`, `0<=n!=m<N`, with `z_n=z_m`
is

```text
C_z(N) = 6*A + P*a*(a-1) + 2*a*b.                        (5.5)
```

No asymptotic equidistribution or finite-data inference occurs in (5.5).

## 6. All but O(w log N) repeated pairs are close

Suppose `n<m` belong to the same block `B_q` and `z_n=z_m`. The tail starts
at the same `k=q+1`, so

```text
tau_m = 10^(m-n)*tau_n,
0 < x_m-x_n = tau_m-tau_n < tau_m.                       (6.1)
```

If the later index satisfies `m <= 7^(q+1)-w`, then every tail exponent is at
most `-w`, and

```text
tau_m <= 10^(-w) * sum_(k=q+1)^infinity 1/7^k
      = 10^(-w)/(6*7^q) < 1/N.                           (6.2)
```

Consequently the actual orbit pair has ordinary, hence circular, distance
strictly below `1/N`.

It remains to count what (6.2) discards. For each block `B_q`, only its final
at most `w` indices can be bad later indices. Each has at most six other
indices with the same `z` value, and ordered counting costs a factor two.
There are `ell` blocks `B_1,...,B_ell` intersecting `0,...,N-1`. Discard all
42 ordered pairs from the initial zero block as well. Therefore at most

```text
E_w := 12*ell*w + 42                                     (6.3)
```

of the pairs counted by (5.5) are not certified by (6.2). Every retained
index is at least 7 and at most `N-1`, so every retained pair belongs to the
positive-index source window `1,...,N`. Hence, without a shift-limit argument,

```text
F_N(1) >= (C_z(N)-E_w)/N, N=10^w.                        (6.4)
```

Since `7^ell<N`, we have `ell < log_7 N = w*log_7 10`, and thus

```text
E_w/N <= (12*w^2*log_7(10)+42)/10^w -> 0.                (6.5)
```

## 7. Uniform arithmetic lower bound

Set `theta=b/P`, so `0<=theta<1`. Dividing (5.5) and (5.2) by `A` gives

```text
C_z(N)/N =
 [6 + (6/7)*(a*(a-1)+2*a*theta)] /
 [1 + (6/7)*(a+theta)].                                  (7.1)
```

For each of the seven possible integer values of `a`, this is a
linear-fractional function of `theta`. Its endpoint lower bounds are

```text
a=0: 42/13;  a=1: 54/19;  a=2: 54/19;  a=3: 78/25;
a=4: 114/31; a=5: 162/37; a=6: 222/43.                  (7.2)
```

Here endpoints with `theta=1` are interpreted as infima; `theta<1` only makes
the relevant inequality strict. An equivalent check, avoiding decimal
approximations, is to multiply `19*C_z-54*N` by `7/A`. Its constant and
`theta` coefficients are

```text
420 + 114*a^2 - 438*a,   228*a - 324.                    (7.3)
```

For `a=0,1` the minimum is at `theta=1`, giving respectively 96 and 0; for
`a>=2` it is at `theta=0`, giving 0 at `a=2` and a positive value thereafter.
Thus

```text
C_z(N)/N >= 54/19.                                       (7.4)
```

Combining (6.4), (6.5), and (7.4) proves (1.2). If PPC held, (1.1) at `s=1`
would force every subsequence to tend to 2, contradicting
`54/19>2`. Therefore:

```text
The fixed sequence ({10^n*alpha_(10,7)})_(n>=1)
does not have Poissonian pair correlation.                (7.5)
```

This is a `proof sketch` for a sibling model, not a machine-checked result.

## 8. What fails in a literal (2,3) replay

The first literal substitution failure occurs at source proof lines 747--753
(preprint p. 14). From the fact that a length-`1/N` cell contains at most one
rational grid point, the source says its prefix contains either three copies
of that `z_n` value or none. At `(10,7)`, a completed level has seven copies,
while a partial final level has `a` or `a+1` copies by (5.2)--(5.4). Thus the
corresponding assertion "either seven or none" is false for a general
truncated prefix `7^ell<N<7^(ell+1)`.

The first base-dependent failure of the source's upper-count route is at lines
793--805. For `(2,3)`, triples motivate an attempted deficiency below the
Poisson value 2. At `(10,7)`, the completed old prefix alone contributes
`6*7^ell` ordered repeated pairs. Near `N=7^ell` this is about `6N`, so an
upper bound below `2N` is impossible. Equations (5.5)--(7.4) repair the replay
in the opposite direction: sevenfold repetition gives a lower excess above
2. This note does not rely on the source's unquantified word "most" or claim
to audit its `(2,3)` proof; (6.2)--(6.5) supply the needed quantifiers anew.

## 9. Exact boundary of any transfer toward T7 or T10

A route back toward a T7 collision or T10 lag-resonance frontier would require
a new, point-specific hypothesis. One fully quantified version is:

```text
There exists a real gamma>0 such that for infinitely many integers w>=1,
with N=10^w, there exists an integer q>=1 satisfying
7^q<N<7^(q+1) for which the set

S_w = {(n,h): 1<=h<=6, 1<=n<n+h*P_q<=N,
       ||(10^(h*P_q)-1)*10^n*pi||_(R/Z) <= 1/N}

has cardinality at least gamma*N.                         (H_pi)
```

together with decimal-boundary control if these metric pairs are to become
same-cylinder pairs. This is only a transfer hypothesis, not an assertion
about `pi`.

The smallest modular calculation showing why the Stoneham proof does not
automatically supply `(H_pi)` is (3.4):

```text
10^P_q - 1 = 7^q*v_q with 7 not dividing v_q.            (9.1)
```

For `alpha_(10,7)`, the factor `7^q` exactly cancels the denominator of the
level-`q` rational skeleton, and the specially placed later summands give the
tail estimate (6.2). For an arbitrary named real, (9.1) merely rewrites the
required phase as

```text
||7^q*v_q*10^n*pi||_(R/Z);                               (9.2)
```

it gives no smallness. Thus the denominator cancellation and tail placement,
not primitive-root status alone, are the unavailable transfer certificate.
No claim about the value of (9.2), T7 for `pi`, T10 for `pi`, C1, or C2 is
made.

## 10. Replay boundary

Run, from a directory containing only the delivered files,

```text
python3 verify_t93.py
sha256sum --check SHA256SUMS
```

The verifier checks source and canonical hashes, source theorem markers, the
order formula for the displayed finite audit range, exact skeleton
multiplicities through level 4, all seven rational endpoint calculations, and
required scope/quantifier markers. These computations audit the formulas; the
universal proof is Sections 3--7, not finite computation.
