# T96: a non-Poissonian Stoneham family for every prime p >= 5

Date: 2026-08-09 UTC.

Result label: `proof sketch`. The bounded source statements and locators in
`SOURCE_PINS.md` are `literature-checked`; no exhaustive literature search or
novelty claim is made. The family theorem below is proved from first principles
in this note and is not imported from the unverified T93 note. There is no Lean
formalization.

Every conclusion concerns an A13 sibling of the immutable fixed-pi question.
Nothing here establishes or refutes a statement about `pi`, C1, or C2.

## 1. Immutable statement, normalization, and ambiguities

The byte-exact canonical statement is included as `canonical_statement.txt`.
Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The canonical question fixes `pi`, base 10, a strict radius `10^(-n)`, ordered
pairs, the diagonal, and quantifiers

```text
forall A >= 1, exists n0 >= 1, forall n >= n0, exists N >= 1.
```

This note changes the point, allows another integer base, excludes the diagonal,
and studies the stronger pair-correlation scale `s/N`. It is therefore exactly
the sibling situation recorded as A13, not a reformulation of the canonical
question.

The following choices are fixed throughout:

1. `p` is an odd prime, `b >= 2` is an integer, and
   `ord_(p^2)(b)=p*(p-1)`.
2. Orbit indices in the pair-correlation statistic are `1,...,N`.
3. Pairs are ordered and off-diagonal.
4. Distance is distance modulo one and the threshold is non-strict, matching
   the pinned source definition.
5. An auxiliary skeleton is indexed by `0,...,N-1`; all pairs retained for the
   final lower bound have indices in `1,...,N-1`, so no shift argument is used.
6. Equality is asserted only for rational skeleton values, never for the actual
   irrational orbit values.

## 2. Bounded primary-source audit

Stoneham, journal p. 372, equation (1.0), defines

```text
w(g,p) = sum_(q>=1) 1/(p^q*g^(p^q))
```

for an odd prime `p` and a primitive root `g modulo p^2`; the immediately
following sentence states normality and stronger arithmetic properties. The
hypothesis `ord_(p^2)(b)=p*(p-1)` says exactly that `b` is such a primitive
root. Thus every number considered here is already covered by Stoneham's
family definition and normality statement. Normality is not used below.

Larcher--Stockinger define PPC on preprint pp. 1--2, equation (1), and state on
preprint p. 4, Theorem 3, only that

```text
({2^n*alpha_(2,3)})_(n in N) does not have Poissonian pair correlations,
alpha_(2,3) = sum_(q>=1) 1/(3^q*2^(3^q)).
```

Their proof is on preprint pp. 14--16, text-derivative lines 723--840. It uses
`s=1`, `N=2^w`, and threefold rational-skeleton repetition. The theorem does
not state the `p>=5` family result below. Their general Theorem 1 is a gap
criterion, but the paper supplies no displayed verification of that criterion
for all `alpha_(b,p)`.

This audit inspected the pinned primary-source bytes directly. Its bounded
corpus is exactly these two sources, selected by the query class `Stoneham`
plus `Poissonian pair correlation`. It supports an exact source-coverage map,
not a claim that no broader theorem exists elsewhere. T93 served only as
motivation and a locator map; none of its mathematical claims is a premise.

## 3. Terminal family theorem

For admissible `b,p`, define

```text
alpha_(b,p) = sum_(q>=1) 1/(p^q*b^(p^q)),
x_n = {b^n*alpha_(b,p)}, n>=1,

F_N(s) = (1/N) * #{(i,j): 1<=i!=j<=N,
                            ||x_i-x_j||_(R/Z) <= s/N}.
```

PPC means that, for every real `s>=0`, `F_N(s)` tends to `2*s` as `N` tends
to infinity.

### Theorem 3.1 (quantified A13 sibling)

For every odd prime `p>=5` and every integer `b>=2` satisfying
`ord_(p^2)(b)=p*(p-1)`, put

```text
Delta_p = (p^2-5*p+2)/p^2 > 0.
```

Then

```text
liminf_(w->infinity) F_(b^w)(1) >= 2+Delta_p > 2.          (3.1)
```

Consequently `({b^n*alpha_(b,p)})_(n>=1)` does not have Poissonian pair
correlation.

All quantifiers and constants in (3.1) are literal. The proof occupies
Sections 4--9.

## 4. Order lifting from the stated hypothesis

### Lemma 4.1

For every admissible odd prime `p`, integer `b`, and integer `q>=1`,

```text
ord_(p^q)(b) = (p-1)*p^(q-1) = phi(p^q).                  (4.1)
```

### Proof

Let `d=ord_p(b)`. Fermat gives `d | p-1`. If `b^d=1+p*c`, then binomial
expansion gives `(b^d)^p=1 (mod p^2)`, whether or not `p|c`. Hence
`ord_(p^2)(b) | p*d`. The hypothesis `ord_(p^2)(b)=p*(p-1)` forces
`d=p-1`.

Write

```text
b^(p-1) = 1+p*c.
```

Here `p` does not divide `c`; otherwise the order modulo `p^2` would divide
`p-1`, contrary to the hypothesis. For `U=1+p*c`, with `p` odd and `p` not
dividing `c`, binomial expansion gives inductively

```text
v_p(U^(p^r)-1)=r+1, r>=0.                                 (4.2)
```

Indeed, if `V=1+p^(r+1)*c_r` with `p` not dividing `c_r`, the linear term in
`V^p-1` has valuation `r+2`; every term of degree at least two has valuation at
least `r+3` (also when `r=0`, because `p` is odd). Raising afterward to an
integer prime to `p` leaves the valuation unchanged. Therefore, for every
integer `m>=1`,

```text
v_p(b^((p-1)*m)-1)=1+v_p(m).                              (4.3)
```

If `b^e=1 (mod p^q)`, reduction modulo `p` first gives `p-1 | e`; write
`e=(p-1)*m`. Equation (4.3) forces `p^(q-1)|m`. Conversely (4.3) shows that
`e=(p-1)*p^(q-1)` works. This proves (4.1) for every `q`, not only for a
finite audit range.

## 5. Rational skeleton and truncation error

For `n>=0`, put `q(n)=0` when `n<p`; otherwise let `q(n)>=1` be the unique
integer satisfying

```text
p^q(n) <= n < p^(q(n)+1).
```

Define

```text
z_n   = {sum_(1<=k<=q(n)) b^(n-p^k)/p^k},
tau_n =  sum_(k>q(n))     b^(n-p^k)/p^k.                  (5.1)
```

If `q=q(n)>=1`, then `z_n` is a multiple of `1/p^q`. Section 6 proves that its
numerator is a unit, so `z_n<=1-1/p^q`. Since
`n<=p^(q+1)-1`, every omitted exponent is at most `-1`, and

```text
0 < tau_n <= (1/b)*sum_(k=q+1)^infinity 1/p^k
          = 1/(b*(p-1)*p^q) < 1/p^q.                     (5.2)
```

For `q=0`, `z_n=0` and the same geometric estimate is below one. Thus there is
no hidden wrap modulo one:

```text
x_n = z_n+tau_n.                                          (5.3)
```

The active terms give the exact recurrence

```text
z_0=0,
z_n={b*z_(n-1)+r_n},
r_n=1/n if n=p^q for an integer q>=1, and r_n=0 otherwise. (5.4)
```

## 6. Complete repeated-residue multiplicity

At an injection time, write `z_(p^q-1)=c/p^(q-1)` (with `c=0` for `q=1`).
Then

```text
z_(p^q) = {(b*p*c+1)/p^q} = u_q/p^q,
u_q=1 (mod p).                                             (6.1)
```

Thus `u_q` is a unit modulo `p^q`. There is no new injection in

```text
B_q={p^q,...,p^(q+1)-1}.
```

Put

```text
P_q=(p-1)*p^(q-1).
```

By (4.1), for `0<=j<(p-1)*p^q=p*P_q`,

```text
z_(p^q+j)=(u_q*b^j mod p^q)/p^q.                          (6.2)
```

Each interval of `P_q` consecutive exponents visits every unit residue modulo
`p^q` exactly once. The block has exactly `p` such periods. Therefore:

```text
Every reduced residue of exact denominator p^q occurs exactly p times
among (z_n)_(n in B_q), at indices separated by P_q.       (6.3)
```

Also `z_0=...=z_(p-1)=0`, again exactly `p` copies. Values belonging to
different blocks cannot coincide because their reduced denominators differ.
This accounts for every skeleton value and every multiplicity; no
equidistribution estimate is being substituted for the count.

## 7. Exact repeated-spacing count for N=b^w

Fix an integer `w>=1` sufficiently large that `N=b^w>p`. Since the order
hypothesis implies `gcd(b,p)=1`, a positive power of `b` cannot be a positive
power of `p`. There is therefore a unique integer `ell>=1` with

```text
A:=p^ell < N < p^(ell+1).                                 (7.1)
```

Put

```text
P=(p-1)*p^(ell-1)=(p-1)*A/p,
H=N-A=a*P+r, 0<=r<P.                                      (7.2)
```

Because `0<H<p*P`, the quotient satisfies

```text
a in {0,1,...,p-1}.                                       (7.3)
```

Among `z_0,...,z_(A-1)`, Section 6 gives exactly `A/p` distinct values,
each with multiplicity `p`. Their ordered off-diagonal repeated-pair count is

```text
(A/p)*p*(p-1)=(p-1)*A.                                   (7.4)
```

The first `H=a*P+r` values of block `B_ell` comprise `a` full periods and the
first `r` residues of one further period. Exactly `r` residues have
multiplicity `a+1`, and the remaining `P-r` residues have multiplicity `a`.
Their complete ordered off-diagonal count is

```text
(P-r)*a*(a-1)+r*(a+1)*a=P*a*(a-1)+2*a*r.                 (7.5)
```

Different levels have different reduced denominators, so there are no missing
cross-terms. The exact total is

```text
C_z(N)=(p-1)*A+P*a*(a-1)+2*a*r.                          (7.6)
```

Equation (7.6), including `a=0`, is the complete repeated-spacing count.

## 8. Tail control for all but an explicit error

Suppose `n<m` lie in the same block `B_q` and `z_n=z_m`. Their tails begin at
the same summand, so

```text
tau_m=b^(m-n)*tau_n,
0<x_m-x_n=tau_m-tau_n<tau_m.                              (8.1)
```

If

```text
m<=p^(q+1)-w,                                             (8.2)
```

then every exponent in `tau_m` is at most `-w`. Since `N=b^w`,

```text
tau_m <= b^(-w)*sum_(k=q+1)^infinity 1/p^k
      = 1/(N*(p-1)*p^q) < 1/N.                           (8.3)
```

Thus every such ordered pair has circular distance strictly below `1/N`.

For each block, only its final at most `w` possible later indices fail (8.2).
Each has at most `p-1` partners with the same skeleton value, and restoring
both orders costs a factor two. There are `ell` relevant noninitial blocks.
Discarding all `p*(p-1)` ordered pairs in the initial zero block as well gives
the explicit upper bound

```text
E_w=2*(p-1)*ell*w+p*(p-1).                                (8.4)
```

Every retained index is at least `p` and at most `N-1`, hence lies in the
source window `1,...,N`. It follows directly, without an index-shift limit,
that

```text
F_N(1)>=(C_z(N)-E_w)/N, N=b^w.                            (8.5)
```

From `p^ell<N=b^w`,

```text
ell<w*log_p(b),
E_w/N < [2*(p-1)*w^2*log_p(b)+p*(p-1)]/b^w -> 0.          (8.6)
```

## 9. Uniform excess above the Poisson value

Let `t=r/P`, so `0<=t<1`, and put `c=(p-1)/p`. Dividing (7.6) and (7.2) by
`A` gives

```text
C_z(N)/A=(p-1)+c*[a*(a-1)+2*a*t],
N/A=1+c*(a+t).                                            (9.1)
```

Subtracting twice the second line from the first yields

```text
C_z(N)/A-2*N/A
  =p-3+c*[a*(a-3)+2*(a-1)*t].                            (9.2)
```

Define

```text
d_p=p-3-2*c=(p^2-5*p+2)/p.                               (9.3)
```

The complete case check is symbolic:

```text
a=0: expression = p-3-2*c*t             >= d_p;
a=1: expression = p-3-2*c               =  d_p;
a=2: expression = p-3-2*c+2*c*t         >= d_p;
a>=3: expression >= p-3                 >  d_p.
```

For every prime `p>=5`, `p^2-5*p+2>0`, hence `d_p>0`. Also (7.1) gives
`N/A<p`. Consequently

```text
C_z(N)/N-2
  =[C_z(N)/A-2*N/A]/(N/A)
  >d_p/p=(p^2-5*p+2)/p^2=Delta_p.                        (9.4)
```

Combine (8.5), (8.6), and (9.4) to obtain

```text
liminf_(w->infinity) F_(b^w)(1)>=2+Delta_p>2.
```

If PPC held, its defining limit at `s=1` would force this subsequence to tend
to `2`. This contradiction proves Theorem 3.1.

## 10. Displayed p=3 obstruction

The preceding lower-excess argument cannot include `p=3`. At `a=0`, the exact
ratio from (9.1) is

```text
R_(3,0)(t)=2/(1+(2/3)*t), 0<=t<1,
inf_(0<=t<1) R_(3,0)(t)=6/5<2.                            (10.1)
```

Equivalently `d_3=-4/3`. Thus the complete repeated-skeleton count alone has no
uniform lower excess above two when `p=3`. Equation (10.1) is an obstruction to
this proof route, not a claim that any particular orbit has PPC and not a claim
that a given sequence of powers `b^w` realizes `t->1`.

The pinned Larcher--Stockinger theorem handles the single pair `(b,p)=(2,3)`
by a different, upper-deficiency argument. This note neither generalizes that
argument to every primitive root modulo 9 nor asserts a classification for
`p=3`.

## 11. Coverage and fixed-pi boundary

The exact bounded coverage map is:

| Claim | Stoneham 1973 | Larcher--Stockinger 2020 | This note |
|---|---|---|---|
| Definition of every admissible `alpha_(b,p)` | Yes, p. 372, (1.0) | Only recalls `(2,3)` | Uses the definition |
| Normality of every admissible family member | Yes, sentence after (1.0) | Recalls `(2,3)` | Not used |
| Non-PPC for `(b,p)=(2,3)` | No | Yes, Theorem 3 | Only source map |
| Non-PPC for every `p>=5` under the displayed order hypothesis | Not stated | Not stated | Proof sketch, Theorem 3.1 |

The arithmetic certificate is denominator cancellation: by (4.1), the period
`P_q` makes `b^P_q-1` divisible by exactly `p^q`, while the specially placed
tail satisfies (8.3). For `pi`, the same factorization only rewrites a phase
such as

```text
||(b^P_q-1)*b^n*pi||_(R/Z)
```

and gives no smallness. No hypothesis about this phase is asserted. Therefore
Theorem 3.1 is a sibling result only and has no implication for fixed `pi`, the
canonical question, C1, or C2.

## 12. Replay and evidence labels

From a directory containing only the delivered files, run

```text
python3 verify_t96.py
sha256sum --check SHA256SUMS
```

The script verifies the vendored hashes and source markers, then performs
finite exact checks of order lifting, skeleton multiplicities, prefix counts,
tail inequalities, the symbolic endpoint inequalities, and the `p=3`
obstruction. These are explicitly `sanity checks`. They are not evidence for
the universal quantifiers; Sections 4--9 contain the universal proof sketch.
