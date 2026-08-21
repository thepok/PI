# T102: all coprime order profiles in the generalized Stoneham-type series

Date: 2026-08-09 UTC.

Result label: `proof sketch`. The two-source audit in `SOURCE_PINS.md` is
`literature-checked` within its explicitly bounded corpus. The universal
argument below is elementary but has not been formalized in Lean. The replay
script supplies `experiment` checks only; finite computation is not proof of
the universal quantifiers.

This note is exclusively an A13 sibling of the immutable fixed-pi question.
It changes the point, may change the base, excludes the diagonal, and uses a
pair-correlation radius `s/N` rather than the strict canonical radius
`10^(-n)`. It makes no claim about pi, canonical A1, C1, C2, superlinear
decimal factor complexity, or `local:pi-digits`.

## 1. Provenance, normalized statement, and ambiguities

The byte-exact canonical statement is `canonical_statement.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

Its canonical quantifiers are

```text
for every A >= 1, there exists n0 >= 1, for every n >= n0,
there exists N >= 1.
```

They are not the quantifiers studied here. Fix an odd prime `p` and an integer
`b>=2` with `gcd(b,p)=1`, and define

```text
alpha_(b,p) = sum_(q>=1) 1/(p^q*b^(p^q)),
x_n = {b^n*alpha_(b,p)}, n>=0.                             (1.1)
```

For real `s>=0` and integer `N>=1`, put

```text
F_N(s) = (1/N) * #{(i,j): 1<=i!=j<=N,
                            ||x_i-x_j||_(R/Z) <= s/N}.      (1.2)
```

Pairs are ordered and off-diagonal, distance is circular, and the threshold
is non-strict. Poissonian pair correlation (PPC) means

```text
for every real s>=0, lim_(N->infinity) F_N(s)=2*s.          (1.3)
```

The ambiguities are resolved as follows.

1. Both `p` and `b` are fixed before `N` tends to infinity. Constants may
   depend on this fixed pair.
2. The term "Stoneham" is source-scoped. Stoneham considers (1.1) when `b` is
   a primitive root modulo `p^2`. For arbitrary coprime `b`, this note studies
   the same algebraic formula as a *generalized Stoneham-type coprime series*;
   it does not extend Stoneham's normality theorem by attribution.
3. Equality below concerns rational skeleton values, never equality of the
   actual orbit points.
4. Auxiliary indices are `0,...,N-1`. Every pair retained in the final metric
   lower bound has both indices in `p,...,N-1`, hence lies in the source window
   `1,...,N` without an index-shift limit.
5. The proof gives a lower bound for actual close pairs. It does not classify
   close pairs whose rational skeleton values differ.

Set

```text
d      = ord_p(b),
lambda = v_p(b^d-1),
h      = (p-1)/d,
M      = h*p^lambda = (p-1)*p^lambda/d.                    (1.4)
```

Here `d|p-1`, `lambda>=1`, and consequently `M` is an integer with `M>=p`.

## 2. Exact source boundary

Stoneham, journal p. 372, equation (1.0), considers

```text
w(g,p) = sum_(q>=1) 1/(p^q*g^(p^q))
```

for an odd prime `p` and a primitive root `g modulo p^2`; the following
sentence states transcendental, non-Liouville, and normal properties. In the
parameters (1.4), that cited primitive-root scope is exactly

```text
d=p-1 and lambda=1.                                       (2.1)
```

Stoneham's normality assertion is not used, and no pair-correlation theorem is
attributed to that paper.

Larcher--Stockinger define the normalization (1.2)--(1.3) on preprint pp. 1--2,
equation (1). Their Theorem 3 on p. 4 states non-PPC only for
`({2^n*alpha_(2,3)})`. It does not quantify over all `b`, all coprime pairs, or
all primitive roots modulo 9. Their general Theorem 1 is a gap criterion, but
the paper gives no displayed verification of it for the T102 family.

The T93, T96, and T99 notes are unverified `proof sketch` artifacts. They are
used only as source locators and mechanism fingerprints. No mathematical claim
from those notes is a premise here.

## 3. Terminal classification theorem

### Theorem 3.1 (all coprime profiles; A13 sibling)

For every odd prime `p` and every integer `b>=2` with `gcd(b,p)=1`, define
(1.1)--(1.4), and set

```text
s_p = 1/[p*(p-1)].                                        (3.1)
```

Then

```text
liminf_(w->infinity) F_(b^w)(s_p)
    >= (M-1)/p
     = ((p-1)*p^lambda/d-1)/p.                            (3.2)
```

The guaranteed normalized excess above the Poisson value is therefore

```text
Delta_(p,d,lambda)
  = (M-1)/p - 2/[p*(p-1)]
  >= [(p-1)^2-2]/[p*(p-1)] > 0.                           (3.3)
```

Consequently `({b^n*alpha_(b,p)})_(n>=1)` does not have PPC. Sections 4--9
prove the theorem, including every order, multiplicity, tail, and endpoint
case.

## 4. Exact order lifting for every d and lambda

### Lemma 4.1

For every integer `m>=1`,

```text
v_p(b^(d*m)-1) = lambda+v_p(m).                            (4.1)
```

Consequently, for every integer `q>=1`,

```text
ord_(p^q)(b) = d*p^max(0,q-lambda)
             = d,                 1<=q<=lambda,
             = d*p^(q-lambda),    q>lambda.               (4.2)
```

### Proof

Write `b^d=1+p^lambda*c` with `p` not dividing `c`. If
`V=1+p^k*u`, where `k>=1` and `p` does not divide `u`, binomial expansion gives

```text
V^p-1 = p^(k+1)*u + sum_(j=2)^p binom(p,j)*p^(k*j)*u^j.
```

The first term has valuation `k+1`. For `2<=j<p`, the corresponding term has
valuation at least `1+2*k>=k+2`; the final term has valuation
`p*k>=k+2`, because `p` is odd. Thus

```text
v_p(V^p-1)=k+1.                                           (4.3)
```

Induction gives valuation `lambda+r` after raising `b^d` to `p^r`. Raising
afterward to an integer `u` prime to `p` preserves that valuation: the linear
term in `(1+p^k*c)^u-1` has valuation `k`, while all later terms have larger
valuation. Writing `m=p^r*u` proves (4.1).

If `b^e=1 (mod p^q)`, reduction modulo `p` first forces `d|e`; write `e=d*m`.
Equation (4.1) says this is possible exactly when
`v_p(m)>=max(0,q-lambda)`. The smallest positive such `m` is
`p^max(0,q-lambda)`, proving both cases of (4.2).

## 5. Rational skeleton, tail, and no hidden wrap

For `n>=0`, put `q(n)=0` when `n<p`; otherwise let `q(n)>=1` be the unique
integer with

```text
p^q(n) <= n < p^(q(n)+1).
```

Define

```text
z_n   = {sum_(1<=k<=q(n)) b^(n-p^k)/p^k},
tau_n =  sum_(k>q(n))     b^(n-p^k)/p^k.                  (5.1)
```

When `q=q(n)>=1`, `z_n` is a multiple of `1/p^q`. Section 6 shows that its
numerator is a unit, hence `z_n<=1-1/p^q`. Since
`n<=p^(q+1)-1`, every omitted exponent is at most `-1`, so

```text
0 < tau_n <= (1/b)*sum_(k=q+1)^infinity 1/p^k
          = 1/[b*(p-1)*p^q] < 1/p^q.                     (5.2)
```

For `q=0`, `z_n=0` and the same direct bound is below one. Thus adding the
tail never crosses one:

```text
x_n=z_n+tau_n.                                            (5.3)
```

The active terms also give the exact recurrence

```text
z_0=0,
z_n={b*z_(n-1)+r_n},
r_n=1/n if n=p^q for some q>=1, and r_n=0 otherwise.       (5.4)
```

## 6. Complete residue-orbit multiplicities

At an injection time write `z_(p^q-1)=c/p^(q-1)`, taking `c=0` for `q=1`.
Then

```text
z_(p^q)={(b*p*c+1)/p^q}=u_q/p^q,
u_q=1 (mod p).                                             (6.1)
```

Thus the numerator is a unit. There is no new injection in

```text
B_q={p^q,...,p^(q+1)-1},
```

whose length is `L_q=(p-1)*p^q`. Put

```text
D_q = ord_(p^q)(b)=d*p^max(0,q-lambda),
M_q = L_q/D_q.                                             (6.2)
```

For `0<=j<L_q`,

```text
z_(p^q+j)=(u_q*b^j mod p^q)/p^q.                          (6.3)
```

The visited numerators form the single coset `u_q*<b>` in the unit group.
This is generally not the set of all units. Each of its `D_q` values occurs
exactly `M_q` times, where every order profile is

```text
M_q = h*p^q,       1<=q<=lambda,
M_q = M,           q>=lambda.                             (6.4)
```

The formulas agree at `q=lambda`. Only the maximal profile
`d=p-1, lambda=1` visits all units and has multiplicity `p`.

Also `z_0=...=z_(p-1)=0`, exactly `p` copies. Values in different positive
blocks cannot coincide because their reduced denominators are distinct.

For a prefix of `B_q` of length

```text
H=a*D_q+r, 0<=r<D_q, 0<=a<=M_q,                           (6.5)
```

exactly `r` orbit values have multiplicity `a+1`, and the other `D_q-r` have
multiplicity `a`. Therefore the complete ordered off-diagonal collision count
in that prefix is

```text
C_q(H)=D_q*a*(a-1)+2*a*r.                                 (6.6)
```

This includes `a=0`, `r=0`, every pre-stable level, and every stable level.

## 7. Exact full-prefix and endpoint formulas

Let `A=p^ell`. The complete skeleton collision count among
`z_0,...,z_(A-1)` is exactly

```text
S_ell = p*(p-1)
      + sum_(q=1)^(ell-1) (p-1)*p^q*(M_q-1).              (7.1)
```

The first term is the initial zero block. For `ell>=lambda`, define the fixed
integer

```text
K = p*(p-1)
  + (p-1)*sum_(q=1)^(lambda-1) p^q*(h*p^q-1)
  - (M-1)*p^lambda.                                       (7.2)
```

An empty sum is zero. Summing the stable levels `q=lambda,...,ell-1` gives
the exact identity

```text
S_ell=(M-1)*A+K.                                          (7.3)
```

Now set `N=b^w`. Since `gcd(b,p)=1`, `N` is not a power of `p`. For all large
`w`, there is a unique `ell>=lambda` with

```text
A=p^ell<N<p^(ell+1)=p*A.                                  (7.4)
```

The current block is stable. Put

```text
P=D_ell=d*p^(ell-lambda),
N-A=a*P+r, 0<=r<P.                                        (7.5)
```

Because the full block has length `M*P`, `a` lies in `{0,...,M-1}`. Equations
(6.6) and (7.3) give the complete exact count of equal skeleton values in
`z_0,...,z_(N-1)`:

```text
C_z(N)=(M-1)*A+K+P*a*(a-1)+2*a*r.                         (7.6)
```

For a normalized exact form put

```text
rho=d/p^lambda=(p-1)/M,
t=r/P, 0<=t<1.                                             (7.7)
```

Then

```text
C_z(N)/N =
 [M-1+K/A+rho*(a*(a-1)+2*a*t)]/[1+rho*(a+t)].             (7.8)
```

Thus every partial-period and endpoint case is explicit in `d` and `lambda`.
Ignoring only the vanishing `K/A`, each linear-fractional segment has endpoint
values

```text
[M-1+rho*k*(k-1)]/[1+rho*k], k=0,...,M.                  (7.9)
```

No equality between (7.9) and the actual pair-correlation liminf is claimed:
unequal skeleton values may contribute additional close pairs.

## 8. Every tail and endpoint loss

Suppose `n<m` belong to the same block `B_q` and `z_n=z_m`. Their omitted
sums begin at the same `k=q+1`, so

```text
tau_m=b^(m-n)*tau_n,
0<x_m-x_n=tau_m-tau_n<tau_m.                              (8.1)
```

If

```text
m<=p^(q+1)-w,                                             (8.2)
```

then every omitted exponent is at most `-w`. Since `N=b^w`,

```text
tau_m <= b^(-w)*sum_(k=q+1)^infinity 1/p^k
      = 1/[N*(p-1)*p^q]
      <= 1/[N*p*(p-1)] = s_p/N, q>=1.                    (8.3)
```

The strict inequality in (8.1) certifies the non-strict metric threshold in
(1.2).

For exact endpoint bookkeeping, define

```text
e_(q,w,N) =
  max(0, min(p^(q+1),N)
       -max(p^q,p^(q+1)-w+1)).                            (8.4)
```

This is exactly the number of possible later indices `m` in
`B_q intersect {0,...,N-1}` that fail (8.2), and

```text
0<=e_(q,w,N)<=w-1.                                        (8.5)
```

Each such later index has at most `M_q-1<=M-1` partners with the same skeleton
value. Restoring both orientations costs a factor two. We discard all
`p*(p-1)` pairs from the initial zero block, where the `q>=1` scale in (8.3)
is unavailable. Therefore the exact displayed upper bound on uncertified
skeleton pairs is

```text
E_w = p*(p-1)
    + 2*sum_(q=1)^ell (M_q-1)*e_(q,w,N)
   <= p*(p-1)+2*(M-1)*ell*(w-1).                          (8.6)
```

`E_w` is an explicit upper bound, not an assertion that every discarded pair
is far. Every retained index is in `p,...,N-1`, so every retained pair belongs
to the positive source window. Hence

```text
F_N(s_p)>=[C_z(N)-E_w]/N, N=b^w.                          (8.7)
```

From `p^ell<N=b^w`,

```text
ell<w*log_p(b),
E_w/N <= [p*(p-1)+2*(M-1)*w*(w-1)*log_p(b)]/b^w -> 0.     (8.8)
```

This accounts for the initial block, every terminal block endpoint, both pair
orientations, and every pre-stable multiplicity.

## 9. Proof of the uniform excess

The current-block term in (7.6) is nonnegative. Equations (7.3)--(7.4) give,
for sufficiently large `w`,

```text
C_z(N)/N >= [(M-1)*A+K]/N.
```

Since `N/A<p` and `K/A->0`,

```text
liminf_(w->infinity) C_z(b^w)/b^w >= (M-1)/p.             (9.1)
```

Combining (8.7), (8.8), and (9.1) proves (3.2). Finally, `d<=p-1` and
`lambda>=1` imply `M>=p`, so

```text
(M-1)/p - 2*s_p
 >= (p-1)/p - 2/[p*(p-1)]
  = [(p-1)^2-2]/[p*(p-1)] > 0                            (9.2)
```

for every odd `p>=3`. If PPC held, (1.3) at the fixed value `s=s_p` would
force every subsequence, including `N=b^w`, to tend to `2*s_p`, contradicting
(3.2) and (9.2). This proves Theorem 3.1.

## 10. Exact defective-order cases

These are symbolic examples of the cases already covered by the proof. The
replay checks them with exact integer and rational arithmetic.

### 10.1 Smallest defective order: (p,b)=(3,4)

Using lexicographic order by odd `p` and then `b`, this is the smallest base
with `d<p-1`:

```text
d=ord_3(4)=1,
lambda=v_3(4-1)=1,
M=2*3=6,
ord_(3^q)(4)=1,3,9,27 for q=1,2,3,4.                     (10.1)
```

Here `K=-9`. Already modulo 3 the order is one rather than two. Each positive
block visits one subgroup coset, not all units, and every visited value occurs
six times. This is the cheapest exact failure of the maximal-order transfer
used in the T93/T96/T99 mechanism maps. It does not obstruct Theorem 3.1.

### 10.2 Smallest higher valuation: (p,b)=(3,8)

```text
d=ord_3(8)=2,
lambda=v_3(8^2-1)=v_3(63)=2,
M=9,
ord_(3^q)(8)=2,2,6,18 for q=1,2,3,4.                     (10.2)
```

Here `K=-54`. Level `q=1` has multiplicity three, while every level `q>=2`
has multiplicity nine. Thus applying the stabilized multiplicity before
`q=lambda` is exactly false.

### 10.3 Smallest simultaneous defects: (p,b)=(3,10)

```text
d=1, lambda=v_3(9)=2, M=18,
ord_(3^q)(10)=1,1,3,9 for q=1,2,3,4.                     (10.3)
```

This combines non-maximal `d` with higher `lambda`. Level `q=1` has
multiplicity six; levels `q>=2` have multiplicity eighteen. None of these
three cases is in Stoneham's cited primitive-root-modulo-`p^2` scope.

## 11. Mechanism fingerprint and fixed-pi boundary

The comparison is mechanism-level only. T93, T96, and T99 remain unverified
notes.

| Artifact | Profile used | Multiplicity | Scale and claimed mechanism |
|---|---|---:|---|
| T93 note | `(p,b)=(7,10)`, `d=6, lambda=1` | 7 | Argues for lower excess at `s=1` |
| T96 note | `p>=5`, `d=p-1, lambda=1` | `p` | Argues for lower excess at `s=1` |
| T99 note | `p=3`, `d=2, lambda=1` | 3 | Argues for lower excess at `s=1/6` |
| T102 | every `d|p-1`, every `lambda>=1` | stable `M=(p-1)p^lambda/d` | Proves in this sketch a lower excess at `s_p=1/[p(p-1)]` |

The common fingerprint is a rational skeleton with repeated residues plus an
orbit tail smaller than `1/N`. T102 shows that maximal order is unnecessary:
smaller `d` or larger `lambda` increases the stable repetition `M`. What fails
outside maximal order is the assertion that every unit residue is visited,
not the repeated-skeleton mechanism.

A route toward the named fixed-pi finite-prefix frontier T7 would require an
additional pi-specific rational-skeleton and orbit-tail hypothesis. One exact
metric version is:

```text
There exist fixed s>0 and eta>0, integers N_k->infinity,
rationals rho_k, and sets
S_k subset {(i,j):0<=i!=j<N_k} such that

{10^i*rho_k}={10^j*rho_k} for every (i,j) in S_k,          (H1)
|S_k| >= (2*s+eta)*N_k,                                   (H2)
max_((i,j) in S_k)
  ||(10^i-10^j)*(pi-rho_k)||_(R/Z) <= s/N_k.              (H3)
```

Then the selected rational-skeleton pairs transfer conditionally to metric
pairs for the decimal orbit of pi. To approach T7's same-decimal-cylinder
statistic, one must additionally require decimal-boundary control ensuring
that both transferred coordinates remain in the same half-open cylinder;
metric closeness alone does not provide this. No part of (H1)--(H3), the
boundary condition, or its conclusion is asserted for pi. It would concern a
non-PPC obstruction, not canonical A1, C1, or C2.

The cheap arithmetic kill for a proposed rational `rho=a/q` in lowest terms is
also exact. Write

```text
q=2^u*5^v*m, gcd(m,10)=1, e=max(u,v),
P=1 if m=1 and P=ord_m(10) otherwise.
```

There are no repeated decimal-orbit residues involving an index below `e`.
After that preperiod, repetitions require lag divisible by `P`. If
`L=max(N-e,0)=c*P+r`, `0<=r<P`, the exact ordered off-diagonal collision count
is

```text
P*c*(c-1)+2*c*r.                                          (11.1)
```

In particular `L<=P` kills (H2). Independently, failure of the pairwise error
bound (H3) kills the orbit-tail transfer. These are conditional tests, not
computations about pi.

## 12. Replay and terminal disposition

From a directory containing only the delivered files, run

```text
python3 verify_t102.py
sha256sum --check SHA256SUMS
```

The verifier checks the four pinned input hashes and line-addressable source
markers in the Larcher--Stockinger derivative. Stoneham's image-only equation
locator necessarily remains a documented visual check rather than a
machine-checked locator. The verifier then performs finite exact checks of the
order formula, pre-stable and stable multiplicities (including a direct
`lambda=3` case), exact prefix formulas, no-wrap, tail and endpoint bounds,
normalized inequalities, the three displayed defective cases, and
rational-period kill counts. These are `experiment` sanity checks only. The
universal `proof sketch` is Sections 4--9.

Terminal outcome: a quantified non-Poissonian theorem for every stated
coprime order profile, at proof-sketch level.

Disposition: `develop` as a clean A13 model. It supplies no pi, A1, C1, or C2
claim.
