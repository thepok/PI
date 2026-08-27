# T114: interpolation-determinant occupancy scout

Status of source statements: `literature-checked` on 2026-08-10 against the
eight delivered primary PDFs. Status of every transfer, determinant
specialization, and exponent comparison below: `proof sketch`. This report
proves nothing about pi, C1, C2, or the canonical question.

```text
PRIMARY_SOURCE_COUNT: 8
PRIMARY_SOURCE_CAP: 12
SEARCHED_LANE_COUNT: 4
RETAINED_CANDIDATE_COUNT: 4
RETAINED_CANDIDATE_CAP: 4
SUCCESSOR_COUNT: 0
DELIVERY_READINESS: READY
COMPARISON_REFRESH: T112_AND_T113_INSPECTED
```

This revision inspects the final accepted T112 literature artifact and the
staged T113 exploration note. T112's source claims may be used at their
recorded `literature-checked` level, but its transfers remain `proof sketch`.
The T113 note is unverified exploration: below it is cited only as "the T113
note argues (unverified)" and none of its deductions is a premise. The source
and candidate corpora are unchanged from the bounded clean-context search.

No unnamed primary source was inspected. Prior T-items are comparison history,
not additional primary sources. Exact URLs, hashes, and locators are in
`SOURCE_PINS.md`; the bounded query and disposition log is in `SEARCH_LOG.md`.

## 1. Immutable statement and normalized target

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

There is no original Erdős Problems URL: this is the locally formulated
canonical question whose provenance is recorded in that file. It asks whether

```text
for every integer A >= 1 there is n0 >= 1 such that
for every integer n >= n0 there is N >= 1 such that
                 A*n*Q_pi(n,N) <= N^2.
```

The pairs in `Q_pi` are ordered, include all `N` diagonal pairs, use strict
circle distance `<10^(-n)`, and allow `N` to depend on `A,n`. Almost-everywhere,
different-constant, unordered, diagonal-free, infinitely-many-`n`, and
prescribed-`N` readings are not substituted.

Put

```text
D_N = {10^i-10^j : 0 <= i,j < N},
Omega(n,N) = {d in D_N : ||d*pi||_(R/Z) < 10^(-n)}.
```

Every nonzero ordered difference is unique: its sign fixes the order and its
10-adic valuation and remaining factor fix the smaller index and the lag.
Hence

```text
|D_N| = N*(N-1)+1,
Q_pi(n,N) = N + |Omega(n,N)| - 1.                 (1.1)
```

The diagonal alone implies the necessary regime

```text
N >= A*n.                                          (1.2)
```

Writing `K=|Omega(n,N)|-1` for nonzero occupied differences, the exact desired
occupancy cap is

```text
K <= B(A,n,N),   B(A,n,N)=N^2/(A*n)-N.             (1.3)
```

No candidate below is allowed to replace (1.3) by a scalar irrationality
statement, an eventually-always avoidance result, a generic parameter theorem,
or an estimate for a different point.

## 2. Common literal determinant and complete exponent ledger

Let `d_1,...,d_r` be distinct nonzero elements of `Omega(n,N)`. The nearest
integers `m_a` are unique because `10^(-n)<1/2`; write

```text
epsilon_a = d_a*pi-m_a,       |epsilon_a| < 10^(-n),
H_N = max{|d|:d in D_N} = 10^(N-1)-1.              (2.1)
```

The literal `D_N` interpolation matrix and determinant are

```text
M_r(d,m)[a,k] = d_a^(r-1-k)*m_a^k,  0 <= k < r,
Delta_r(d,m) = det M_r(d,m)
             = product_(a<b) (d_a*m_b-d_b*m_a)
             = product_(a<b) (d_b*epsilon_a-d_a*epsilon_b).   (2.2)
```

This is the homogeneous Veronese/Vandermonde identity. It gives the complete
ledger

```text
dimension                 r,
raw coordinate height     max(|d_a|,|m_a|) <= 4*H_N,
integer lower bound        |Delta_r| >= 1 if Delta_r != 0,
near-integer upper bound   |Delta_r|
                           < (2*H_N*10^(-n))^(r*(r-1)/2), r>=2. (2.3)
```

Thus increasing `r` multiplies both the coefficient-height exponent and the
near-integer exponent by exactly `binom(r,2)`; it never changes their ratio.
For `r=1`, `M_1=(1)` and `Delta_1=1`, so the strict estimate (2.3) is not
asserted and there is no pairwise determinant content.
Taking base-10 logarithms of the base in (2.3) gives

```text
E(N,n) = N-1-n + log10(2*(1-10^(1-N))).             (2.4)
```

For `A>=2`, (1.2) gives `N>=2n`, and

```text
2*H_N*10^(-n) >= 2*(10^(2n-1)-1)*10^(-n) > 1       (n>=1).   (2.5)
```

Consequently the upper estimate (2.3) is not below the arithmetic lower bound
for any `r>=2`: this determinant cannot close. This is not asymptotic
shorthand; the smallest case is `A=2,n=1,N=2`, where the base is `18/10>1`.

The remaining canonical edge `A=1` also supplies no determinant certificate.
If `N=n`, then `B=0`, a violation may contain only one nonzero occupied
difference, and (2.6) gives `r=1`, where `Delta_1=1` has no smallness. If
`N>=n+1`, monotonicity in `N` gives

```text
2*H_N*10^(-n) >= 2*(10^n-1)*10^(-n)
                 = 2*(1-10^(-n)) > 1.               (2.5a)
```

Thus the `A=1` regime splits into a rank-one endpoint and the same wrong-sign
pairwise estimate; together (2.5) and (2.5a) cover every integer `A>=1`.

To connect dimension literally to occupancy, a violation of (1.3) supplies

```text
r(A,n,N) = floor(B(A,n,N))+1                       (2.6)
```

distinct occupied nonzero differences. If every resulting `Delta_r` were
nonzero and the base in (2.3) were below one, (2.3) would contradict the
integer lower bound and prove (1.3). At `r=1` this determinant has no pairwise
content; at `r>=2`, (2.5) or (2.5a), according to `A`, kills the required
smallness. Nonvanishing is also false as a universal combinatorial premise:
`10d` can again lie in `D_N`, and
if both errors satisfy `epsilon_(10d)=10 epsilon_d`, then
`d*m_(10d)-(10d)*m_d=0`.

This common calculation is reused explicitly, not re-derived, in Cards C1-C4.

## 3. Candidate C1: Laurent interpolation determinant

### Source theorem and all hypotheses

Laurent, *Linear forms in two logarithms and interpolation determinants*,
printed pp. 181-183 and 188-194: Theorem 3, Lemmas 4-8. Let `alpha_1,alpha_2`
be real algebraic numbers at least one, multiplicatively independent; let
`D=[Q(alpha_1,alpha_2):Q]`; choose `a_i>1` with
`h(alpha_i)<=log a_i`; and integers `b_1,b_2>=1`. Choose integers `K>=2` and
`L,R_1,R_2,S_1,S_2>=1`, and real `rho>=1`, with

```text
R_1*S_1 >= max(K,L),       R_2*S_2 >= 2*K*L.        (3.1)
```

Put

```text
R=R_1+R_2-1,  S=S_1+S_2-1,  gamma=R*S/(K*L),
g=1/4-1/(12*gamma)
  +max(1/(4*gamma*L^2),gamma/(4*L*R^2),gamma/(4*L*S^2)),
b=((R-1)*b_2+(S-1)*b_1)
  *(product_(1<=k<K) k!)^(-2/(K^2-K)).              (3.1a)
```

Require all `r*b_2+s*b_1` for `0<=r<R,0<=s<S` to be pairwise distinct and
require the full printed inequality

```text
K*(L-1)*log(rho)+(K-3)*log 2
 > 2*D*log(K*L)+D*(K-1)*log b
   +g*L*((rho-1)*(R*log alpha_1+S*log alpha_2)
          +2*D*(R*log a_1+S*log a_2)).               (3.1b)
```

Writing `Lambda=b_2 log alpha_2-b_1 log alpha_1`, the conclusion is

```text
|Lambda_0| >= rho^(-K*L+1/2),
Lambda_0 = Lambda*max(
  L*S*exp(L*S*|Lambda|/(2*b_2))/(2*b_2),
  L*R*exp(L*R*|Lambda|/(2*b_1))/(2*b_1)).             (3.1c)
```

The source's literal `KL x RS` matrix is

```text
A_((k,l),(r,s)) = binom(r*b_2+s*b_1,k)*alpha_1^(l*r)*alpha_2^(l*s),
0<=k<K, 0<=l<L, 0<=r<R, 0<=s<S.                    (3.2)
```

Lemma 4 says `rank A=KL`. For `q=KL`, a nonzero minor is

```text
Delta_L = det(A_((k_i,l_i),(r_j,s_j)))_(1<=i,j<=q). (3.3)
```

Lemma 5 gives the full arithmetic lower bound printed on p. 189, including
the `-(D-1)log(q!)`, algebraic-height, and binomial-height terms. In particular
the polynomial representing the minor has

```text
L(P) <= q!*b^((K-1)q/2).                            (3.4)
```

Lemma 6 assumes `|Lambda_0|<=rho^(-q+1/2)` and under that hypothesis gives
the upper bound

```text
|Delta_L| <= rho^(-q(q-1)/2)*2^q*q!*(rho*b/2)^((K-1)q/2)
             *alpha_1^(M_1+rho*G_1)*alpha_2^(M_2+rho*G_2).    (3.5)
```

Lemma 7 supplies the interpolation exponent: a `nu`-row auxiliary determinant
vanishes to order at least `nu(nu-1)/2`.

### Literal D_N witness and comparison

The literal witness (2.2) is an independently derived homogeneous
Vandermonde analogue, not a specialization of Laurent's matrix (3.2). Its
dimension `r` is the number of selected occupied `D_N` elements, and its
height, upper bound, lower bound, and occupancy dimension are exactly
(2.3)-(2.6). It shares Laurent's numerical `binom(r,2)` interpolation exponent,
but no source theorem transfers Laurent's arithmetic lower bound to it. For
this analogue, the identical height multiplicity gives the wrong sign in
(2.5) and (2.5a).

Moreover Laurent's lower bound requires algebraic `alpha_1,alpha_2` and their
multiplicative independence. The additive data `d*pi=m_d+epsilon_d` do not
provide algebraic exponentials or logarithms satisfying those hypotheses.

PI-SPECIFIC TRANSFER PREMISE C1: one would need a theorem proving that every
`r(A,n,N)`-tuple extracted from an overoccupied `Omega(n,N)` has a nonzero
minor with an upper bound `10^(-c*n*r(r-1)/2)` and height cost
`10^(c'*N*r(r-1)/2)` where `c*n>c'*N`, while also supplying a valid algebraic
lower bound at pi. No source supplies this.

CHEAP KILL C1: already `r=2` requires

```text
2*(10^(N-1)-1)*10^(-n) < 1.                        (3.6)
```

Equation (2.5) refutes this certificate throughout `N>=A*n` for `A>=2`.
Scaling chains can additionally make the minor zero.

Disposition: rejected at the exact height exponent and algebraicity gates.

## 4. Candidate C2: Väänänen-Wu fixed three-column Mahler determinants

### Source theorem and all hypotheses

Väänänen-Wu, *On linear independence measures of the values of Mahler
functions*, preprint pp. 4-8, equations (8)-(25), Lemma 1 and Theorem 6.
Fix integers `d>=2,b>=2`. Functions `F,G in Q[[z]]` converge in a disk and satisfy

```text
P(z)F(z^d)=P_11(z)F(z)+P_12(z)G(z)+P_10(z),
P(z)G(z^d)=P_21(z)F(z)+P_22(z)G(z)+P_20(z),          (4.1)
```

where `P,P_ij in Z[z]` and
`P_11 P_22-P_12 P_21` is not the zero polynomial. At a nonzero rational
`a/b` in the convergence disk, require every iterate in equation (19) to avoid
the zeros of `P*(P_11 P_22-P_12 P_21)`. For the selected Hermite-Padé triples
choose positive integer indices satisfying

```text
k_(l,1)<k_(l,2)<k_(l,3),
k_(l,3)<=k_(l+1,1) for l<L,       k_(L,3)<=d*k_(1,1). (4.1a)
```

For every `l`, require `D(k(l),z)` nonzero and, for every selected `k`, a
threshold `m_0(k)`
after which the integer forms

```text
a_(k,m)*gamma_1+b_(k,m)*gamma_2+c_(k,m)=r_(k,m),
max(|a_(k,m)|,|b_(k,m)|) <= c_1(k)b^(E(k)d^m),
|r_(k,m)| <= c_2(k)b^(-V(k)d^m).                    (4.2)
```

Here `c_1(k),c_2(k)` are positive and independent of `m`. With `tau` the
maximum polynomial degree in (4.1), `o(k)` the Padé remainder order,
`ebar(k)` the degree parameter from equation (20), and arbitrary auxiliary
`delta_1,delta_2>0`, the source defines

```text
E(k)=ebar(k)+tau/(d-1)+delta_1,
V(k)=(1-lambda)*o(k)-ebar(k)-tau/(d-1)-delta_2,       (4.2a)
```

and requires the resulting values positive where used.

The literal source determinant is

```text
Delta_VW(k(l),m)=det((a_(k_(l,i),m),b_(k_(l,i),m),c_(k_(l,i),m)))_(1<=i<=3)
  != 0 for every l and every m>=max_i m_0(k_(l,i)).    (4.3)
```

Define

```text
theta(l)=max_(i<j)(E(k_(l,i))+E(k_(l,j))),
nu(l)=min_(i!=j)(V(k_(l,i))-E(k_(l,j))).             (4.4)
```

Theorem 6 additionally requires
`0<nu(1)<...<nu(L)<d*nu(1)`. For the nonzero rational point `a/b` in the
convergence disk, put `lambda=log|a|/log b`; the theorem supplies
`lambda_0>0` and requires exactly `0<=lambda<lambda_0`. It concludes, for
every nonzero integer triple,

```text
|h_0+h_1 F(a/b)+h_2 G(a/b)| > C*H^(-mu),
mu=max_l theta(l+1)/nu(l),  theta(L+1)=d*theta(1).   (4.5)
```

Here `h_0,h_1,h_2` are integers not all zero and
`H=max(|h_1|,|h_2|,H_0)` for the source threshold `H_0`.

### Literal D_N rank witness and comparison

For `d_1,d_2 in Omega(n,N)`, the intended evaluation vector is

```text
v_D=(1,d_1*pi,d_2*pi),
(0,d_2,-d_1) dot v_D = 0.                            (4.6)
```

Thus `rank_Q(v_D)<=2`, whereas (4.3)-(4.5) require rank three. A putative
source-shaped witness built from `D_N` would be the determinant (4.3) after
setting `gamma_i=d_i*pi`; equation (4.6) proves that not all source hypotheses
can survive this specialization. The source dimension is fixed at three, so
even an otherwise valid instance would not scale with the occupancy threshold
`r(A,n,N)`.

PI-SPECIFIC TRANSFER PREMISE C2: two genuinely independent Mahler values would
have to encode the two nearest-integer errors for `d_1*pi,d_2*pi`, with (4.3),
(4.4), equation (19), and all constants uniform over enough `D_N` pairs.

CHEAP KILL C2: the exact integer relation (4.6), with coefficient height at
most `H_N`, makes the lower bound (4.5) read `0>C*H^(-mu)`. Hence the literal
specialization is impossible before any asymptotic comparison.

Disposition: rejected as fixed-dimensional and rank-incompatible.

## 5. Candidate C3: scalable q-difference determinants

### Source theorem and all hypotheses

Amou-Matala-aho-Väänänen, *On Siegel-Shidlovskii's theory for q-difference
equations*, printed pp. 318-322, equations (5.1)-(6.8), Theorem 5.1 and
Theorem 6.1. Let `K` be a number field of degree `kappa`, `v` a place, and
`q in K*` with `||q||_v<1`; let

```text
z^s y(qz)=a(z)C y(z)+b(z),                           (5.1)
```

where `s>=0`, `C in GL(m,K)`, `a in K[z]`, `a(0)!=0`, `deg a<=s`, and every
component of `b in K[z]^m` has degree at most `s`. Require
`1,f_1,...,f_m` linearly independent over `K(z)`, `alpha in K*`, and
`a(alpha*q^k)!=0` for every `k>=0`. With `0<delta<1`, define

```text
K_0=m^2/2+((m+1-delta)^3-m^3)/(6*delta),
A(tau)=s*tau^2/2+m*tau+K_0,
B(tau)=s*tau^2/2+(m+1-delta)*tau,                    (5.1a)
```

and let `rho_0` be the positive root of

```text
s*(1-delta)*rho^2+(s*(1-delta)*delta*m-2*s*K_0)*rho
 -(s*delta*m+2*(m+1-delta))*K_0=0.                   (5.1b)
```

Require

```text
-B(rho_0)/A(rho_0) < lambda <= -1,                  (5.2)
```

where `lambda=log H(q)/log ||q||_v`. Theorem 5.1 gives the stated linear
independence and

```text
|l_0+sum_i l_i f_i(alpha)|_v
  > C/(H^(mu*kappa/kappa_v)*H^(D*(log H)^(-1/2))),
mu=B(rho_0)/(B(rho_0)+lambda*A(rho_0)).              (5.3)
```

At `lambda=-1,delta=1/2`, equation (5.6) gives

```text
mu <= (8m/(8m-1))*(8s*m^2+(s+4)m+s/3+2).            (5.4)
```

The general theorem uses forms `L_(n,T)=B_(n,T)Theta+A_(n,T)` with
`B_(n,T) in K`, `A_(n,T),L_(n,T) in K^m`, local bounds

```text
max(||B_(n,T)||_w*,||A_(n,T)||_w*) <= P_w(n,T) for every place w,
||L_(n,T)||_v <= R_v(n,T),                            (5.4a)
```

and positive constants `rho_1<rho_2,c_4` such that, for every `n>=c_4`, some
integer `T in [rho_1*n,rho_2*n-m]` makes the literal `(m+1)x(m+1)` determinant

```text
Delta_AMV(n,T)=det[
  (-B_(n,T+j))_(0<=j<=m);
  (A_(n,T+j,i))_(1<=i<=m,0<=j<=m)
] != 0                                                (5.5)
```

nonzero. It further requires bounded positive functions `A_0(tau),B_0(tau)`
on `[rho_1,rho_2]` and constants `c_5,c_6>=1,c_7>0` such that

```text
product_w P_w(n,tau*n) <= c_5^n*H(q)^(A_0(tau)*n^2),
R_v(n,tau*n) <= c_6^n*||q||_v^(B_0(tau)*n^2),
B_0(tau)+lambda*A_0(tau) >= c_7.                    (5.5a)
```

Theorem 6.1 then uses
`mu=sup B_0(tau)/(B_0(tau)+lambda*A_0(tau))` and gives (5.3) for the
abstract tuple `Theta`.

### Literal D_N rank witness and comparison

For distinct occupied `d_1,...,d_m`, put `Theta_i=d_i*pi`. The literal rank
witness is

```text
rank_Q(1,Theta_1,...,Theta_m) <= 2,
d_j*Theta_i-d_i*Theta_j=0.                            (5.6)
```

Thus the linear-independence premise and determinant application fail for
every `m>=2`. The source theorem fixes the system and `m`; it supplies no
uniform growing-dimension theorem. Even under the unsupported optimistic
extrapolation, the required dimension is literally

```text
m=r(A,n,N)=floor(N^2/(A*n)-N)+1.                     (5.6a)
```

Equation (5.4) gives only the dimension-dependent calibration
`mu=O(s*m^2+(s+1)*m+1)`. At raw height `H about 10^N`, (5.3) is no stronger
than the conservative scale

```text
10^(-O((s*m^2+(s+1)*m+1)*N + D*sqrt(N))),            (5.7)
```

whereas the individual near-integer errors are `10^(-n)` with `n<=N/A`.
More directly, the source has `B(rho_0)>A(rho_0)` and (5.2) keeps the
denominator positive, so `mu>1`; the lower-bound exponent at height `10^N`
already exceeds `N`, while `n<=N/A`. The bounds are compatible. In the
illustrative subregime `N=t*A*n` with fixed `t>1`, (5.6a) gives `m=Theta(N)`:
the displayed upper calibration is cubic in `N` when `s>=1` and quadratic
when `s=0`. This extrapolation is explicitly not a sourced uniform theorem.

PI-SPECIFIC TRANSFER PREMISE C3: one would need `m` functionally independent
q-difference values whose Padé forms equal the errors `d_i*pi-m_i`, determinant
(5.5) nonzero, and constants uniform as `m` grows to (2.6).

CHEAP KILL C3: equation (5.6) kills the literal tuple at `m=2`. Even ignoring
rank, compare `n<=N/A` with the lower-bound exponent `mu*N`; already
`mu>=1` cannot improve the common determinant sign in (2.5), and the sourced
bound worsens quadratically with `m`.

Disposition: rejected at rank, uniformity, and exponent gates.

## 6. Candidate C4: Varjú-Yu fixed-lag recurrence rank

### Source theorem and all hypotheses

Varjú-Yu, *Fourier decay of self-similar measures and self-similar sets of
uniqueness*, preprint pp. 4-5 and 8-11, Definition 1.9, Theorem 1.10, and
Lemmas 3.1-3.2. For algebraic real `lambda>1` and `gamma` not Liouville over
`Q(lambda)`, Theorem 1.10 gives constants `epsilon,C>0` such that, for every
`x>e^e`,

```text
DC(x,lambda,epsilon)+DC(x*gamma,lambda,epsilon)
  >= C*log log x.                                     (6.1)
```

Here `DC` is exactly Definition 1.9's fixed-threshold count. Lemma 3.1 assumes
`alpha in [1,lambda]\Q(lambda)`, and supplies constants `epsilon,H,C_1,C_2`
depending only on `lambda`: if `n,K>H` and the complete block satisfies

```text
max_(n<=j<=K*n) ||alpha*lambda^j|| <= epsilon,        (6.2)
```

then some `beta in Q(lambda)` has

```text
h(beta)<=C_1*n,       |alpha-beta|<=exp(-C_2*K*n).    (6.3)
```

For `d=deg(lambda)`, Lemma 3.2's literal rank witness is the Vandermonde

```text
V(lambda)=(lambda_i^(j-1))_(1<=i,j<=d),
det V=product_(i<j)(lambda_j-lambda_i) != 0.          (6.4)
```

### Literal D_N rank witness and comparison

Fix a lag `h>=1` and define the `D_N` chain

```text
d_(h,j)=(10^h-1)*10^j in D_N,       0<=j<N-h.
```

For occupied consecutive terms, the literal integer recurrence witness is

```text
R_(h,j)=m_(h,j+1)-10*m_(h,j)
       =10*epsilon_(h,j)-epsilon_(h,j+1).             (6.5)
```

For `n>=2`, `|R_(h,j)|<11*10^(-n)<1`; hence arithmetic integrality forces
`R_(h,j)=0`. This is the degree-one specialization of the rank mechanism:
at `lambda=10`, (6.4) is only the `1x1` determinant `(1)`.

The height is `|m_(h,j)|<=4H_N`, the near-integer upper bound is
`11*10^(-n)`, and the nonzero arithmetic lower bound would be one. It controls
complete consecutive blocks at one fixed lag, not the number of arbitrary
occupied elements across all lags. Indeed, selecting every other `j` in every
lag produces order `N^2` abstract positions with no consecutive witness (6.5).
This is a combinatorial certificate test, not a claim that pi realizes that
pattern. Theorem 1.10 itself gives a lower bound on fixed-threshold changes,
not an upper bound on near-return occupancy.

PI-SPECIFIC TRANSFER PREMISE C4: global overoccupancy above (1.3) would have to
force, at one lag, a complete block (6.2) whose length beats the source's
height constants, uniformly in the moving lag and threshold `10^(-n)`.

CHEAP KILL C4: cardinality alone cannot force even two adjacent indices in a
lag until occupancy exceeds half that lag; taking alternating indices over all
lags has quadratic total size. Thus no exponent from (6.3) can be invoked from
the required aggregate occupancy premise.

Disposition: rejected as a consecutive-block scalar degeneration, not a
simultaneous occupancy cap.

## 7. Candidate comparison matrix

| Card | Literal `D_N` witness | Dimension | Coefficient height | Near-integer upper bound | Arithmetic lower bound | Resulting occupancy statement |
|---|---|---:|---|---|---|---|
| C1 Laurent | `Delta_r` in (2.2) | `r=floor(B)+1` on a violating set | coordinates `<=4H_N`; determinant height factor `H_N^binom(r,2)` | `(2H_N*10^-n)^binom(r,2)` | `1` if nonzero | would prove `K<=B` only if every selected minor is nonzero and (3.6) holds; both gates fail |
| C2 Väänänen-Wu | source-shaped `Delta_VW` plus rank relation (4.6) | fixed `3` | `b^(E(k)d^m)` per source form; target coordinates `<=4H_N` | source remainder `b^(-V(k)d^m)`; target common bound (2.3) | integer determinant in the source, yielding `C H^-mu` | none: the literal `D_N` tuple has rank at most two and fixed dimension cannot cap `K` |
| C3 Amou-Matala-aho-Väänänen | `Delta_AMV` and relations (5.6) | `m+1` for a fixed system | `c_5^n H(q)^(A_0(tau)n^2)` globally; target `<=4H_N` | `c_6^n||q||_v^(B_0(tau)n^2)`; optimistically target `10^-n` | (5.3); conservative exponent `O((s*m^2+(s+1)m+1)N)` | none: rank fails at `m=2`; there is no sourced growing-dimension occupancy theorem |
| C4 Varjú-Yu | recurrence integer `R_(h,j)` in (6.5) | source `deg(lambda)`; exactly `1` at `lambda=10` | `|m_(h,j)|<=4H_N` | `11*10^-n` for adjacent occupied indices | `1` if `R_(h,j)!=0` | forces recurrence only on a complete fixed-lag block; no aggregate cap over `D_N` |

## 8. Four inspected sources screened before retention

These are not additional candidates. Their relevant applicability hypotheses
are recorded to make the exclusions auditable.

### S3: Zorin, arbitrary-dimensional Mahler zero estimates

Zorin, preprint pp. 1-6 and 23, system (1), Theorem 1, equation (8), Theorem
30, equation (43). The analytic tuple has algebraic coefficients and satisfies

```text
a(z)f(z)=A(z)f(p(z))+B(z),
p in Qbar(z), ord_0 p=delta>=2, det A not identically zero,               (7.1)
```

with `a,A,B` algebraic-polynomial data and transcendence degree
`t=trdeg_(C(z)) C(f_1,...,f_n)>=1`. Theorem 1 further requires polynomial
`p`, algebraic `y` in the analytic neighborhood, `p^[h](y)->0`, and no iterate
a zero of `z det A(z)`; it applies to projective varieties of dimension
`k<t+1-log(d)/log(delta)` and gives the printed distance lower bound (8).
Theorem 30 assumes the first `t` functions algebraically independent and gives

```text
ord_0 P(f) <= K_1*(deg_X' P+deg_X P+1)*(deg_X P+1)^t
```

unless `P(f)=0`. For the literal tuple `(1,d_1*pi,...,d_m*pi)`, the relations
(5.6) give rational rank at most two and no growing transcendence degree.
No Mahler representation of pi or dimension-uniform height constant is
supplied. Screen: rank-deficient/unproved pi representation.

### S4: Zudilin, scalar Hankel determinant

Zudilin, preprint pp. 3 and 5-8, Theorem 1, equations (6)-(8). Assume integer
`|p|>1`, nonzero rational `x,z`, `x` not in `{p,p^2,...}`, and `|z|<|p|`.
The theorem proves irrationality of the single generalized q-logarithm value.
Its literal determinant is

```text
V_r(mu)=det(v_(j+l)(mu))_(0<=j,l<r).                 (7.2)
```

For the source value, row operations give

```text
ord_q V_r* >= r(r-1)(2r-1)/6,
|V_r| <= |p|^(-r^3/3)*exp(O(r^2)),                   (7.3)
```

Under the contradiction hypothesis that the source q-logarithm value is
rational, denominator clearing costs `exp(O(r^2))`, and Kronecker
nonvanishing gives a nonzero integer lower bound along infinitely many `r`.
Every entry concerns the same scalar; replacing it by pi discards the Padé
identity and gives no `D_N` family or occupancy cap. Screen: scalar
irrationality only.

### S6: Schleischitz, unique rounding

Schleischitz, printed p. 9, Theorem 3.12 and equation (10). For real
`zeta>1,epsilon>0` with `(zeta+1)epsilon<1/2`, the set of nonzero `alpha`
with `||alpha*zeta^j||<=epsilon` for every sufficiently large `j` is at most
countable. Equality is allowed unless `zeta` is rational with even reduced
denominator. The witness is the successor inequality

```text
|zeta*M_j-M_(j+1)| <= (zeta+1)*epsilon,              (7.4)
```

which uniquely determines the next integer. There is no determinant, height
lower bound, named-point exclusion, or finite-prefix occupancy cap. Screen:
eventually-always/variable-path avoidance only.

### S8: Konyagin-Shparlinski, short modular powers

Konyagin-Shparlinski, printed pp. 11-12 and 16-19, Theorem 1 and equations
(11)-(14). For prime `p`, primitive root `g mod p`, positive integer `L<p`,
and nonzero `lambda mod p`, put

```text
S_(g,p)(lambda,L)=sum_(1<=j<=L) e_p(lambda*g^j).
```

The theorem gives

```text
|S| <= p^(1/8+o(1))*L^(71/96),       L<=p^(1/2),
|S| <= p^(23/96+o(1))*L^(49/96),     p^(1/2)<L<p.    (7.5)
```

The proof uses Parseval, a fourth moment, and small-product-set estimates;
there is no interpolation determinant or arithmetic nonvanishing. Squaring
the first bound beats `L^2` only when

```text
L > p^(12/25+o(1)),                                  (7.6)
```

whereas a real-to-modular approximation at coefficient height `10^N` leaves
the target length `N` logarithmic in the modulus. It also needs `10` primitive
and the actual numerator controlled. Screen: excluded energy/flattening route
and polynomial-length mismatch.

## 9. Prior-fingerprint exclusions

Verification levels are part of this table. Notes are navigation only and are
not treated as discharged premises.

| Prior item | Level used | Normalized fingerprint | T114 comparison |
|---|---|---|---|
| T81 | unverified `proof sketch` with pinned source and checked imported interfaces | scalar irrationality packing has exponential coefficient-height capacity and no compatibility | C1 independently recovers the sharper determinant base (2.3); C2-C4 fail rank or block aggregation, so no scalar-packing result is promoted |
| T87 | mixed source audit and unverified synthesis | charging leaves a long sector; restricted scalar approximation misses its threshold; conductor bounds exceed logarithmic length | no charging or rational conductor is used; the common exponent (2.5) independently closes determinant nonvanishing at the occupancy scale |
| T104 | source claims `literature-checked`, transfers `proof sketch` | Mahler radial coherence, ambient Fourier decay, and metric/fixed-fiber gaps | C2-C3 use arithmetic Padé determinants, not radial or ambient-measure decay; their exact rank failure prevents a claimed fixed-pi advance |
| T105 | source claims `literature-checked`, transfers `proof sketch` | additive energy, flattening, and modular geometric sums fail at prescribed character/logarithmic length | S8 is explicitly screened as that energy route; C1-C4 rely only on determinant/rank witnesses |
| T110 | source claims `literature-checked`, transfers `proof sketch` | fixed-order digital uniformity and metric higher correlations do not evaluate the exponential-in-index pi phase | no Gowers or q-multiplicative estimate is used; T114's obstruction is arithmetic rank and height rather than phase uniformity |
| active T112 (now accepted) | source statements `literature-checked`; carry packaging, T107 substitutions, and native transfer remain `proof sketch` | finite carry/local-limit models and an explicitly centered finite-state twisted-transition operator for the pi digit path; the conjectural `H-G19-twisted-cocycle` keeps the T107 boundary premise separate and pays a dimension factor in the operator-to-sum bound | C1-C4 use no carry state, stationary reference, boundary load, or operator norm. Their literal obstruction is instead determinant height and rational rank. T112's conjectural transfer is not used as a premise and is not duplicated by a determinant nonvanishing claim |
| active T113 (now staged note) | sources reported `literature-checked`; all decimal-difference deductions are an unverified `proof sketch` | the T113 note argues (unverified) that Moshchevitin's variable-`H` avoidance theorem can be instantiated on the increasing positive magnitudes of `D_N` to obtain an unnamed sibling point with diagonal-only collisions; transfer to pi is the unproved scalar premise `PI-AVOID` | this is exactly a variable-threshold avoidance fingerprint, with no interpolation determinant or arithmetic nonvanishing. T114 independently screens avoidance-only mechanisms and does not use the note's ordering, constants, sibling conclusion, or pi premise |
| terminal obstruction memory | unverified audit ledger | scalar bounds, exact regrouping, finite classification, and many children do not create compatible fixed-pi cancellation | respected as a warning only; equations (2.2)-(2.5) independently instantiate the scalar/rank obstruction |

The comparison therefore excludes known scalar, avoidance, ambient-measure,
energy, digital-uniformity, and finite-state routes without using any
unverified note as a premise. T112 and T113 are fingerprint comparators only;
neither discharges a determinant, occupancy, or pi-specific hypothesis here.

## 10. Pi-specific frontier and endpoint

All four retained cards fail. The strongest common sufficient transfer premise
would be:

```text
For every A and all sufficiently large n, some N>=A*n has the property that
if K>B(A,n,N), then among the K occupied nonzero elements there are
r=floor(B)+1 elements whose literal determinant Delta_r is nonzero and obeys
|Delta_r| <= 10^(-c*n*binom(r,2)+c'*N*binom(r,2))
with c*n>c'*N, together with an arithmetic lower bound >=1.               (9.1)
```

This premise is not known for pi. It is stronger than source nonvanishing,
must survive scaling chains in `D_N`, and must reverse the independently
derived homogeneous-determinant height sign. The smallest kill is the `2x2`
calculation

```text
1 <= |d_1*m_2-d_2*m_1|
   < 2*(10^(N-1)-1)*10^(-n),                         (9.2)
```

whose right side is already greater than one throughout `N>=A*n` for `A>=2`.
For `A=1`, the split after (2.5a) gives either the content-free `r=1` endpoint
or the same inequality. No larger determinant of the homogeneous form (2.2)
improves this ratio; this report does not claim to exclude every imaginable
determinant architecture. C2-C3 additionally die from exact rational rank one
among the multiples of pi; C4 does not convert occupancy to a complete lag
block.

No survivor reaches T7's literal occupancy input or T10's prescribed adaptive
exponential sum. The related Mahler, q-difference, logarithmic, and lacunary
results remain results about their own constants or model systems. They are
not progress on pi, C1, or C2.

TERMINAL VERDICT (1/1): **CLOSE.** This closes only the audited determinant-
nonvanishing fingerprint at the required collision scale. There is no bounded
successor. Reopen only if a theorem directly reverses (2.5) with a pi-specific,
scaling-resistant simultaneous determinant or supplies an equivalent literal
occupancy cap without passing through scalar irrationality, avoidance, energy,
generic metric behavior, or an unproved analytic premise.
