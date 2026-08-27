# T82: Chudnovsky certification carries and the T64 synchronization test

Status: `proof sketch` with source-pinned inputs and exact-arithmetic replay.

Date: 2026-08-09 UTC.

## 0. Result and non-claims

This note reaches the agenda's permitted **exact legal-state obstruction**
endpoint, with deliberately narrow scope.

The source-pinned T17 Chudnovsky computation produces two exact rational
endpoints for `pi*10^D`, where `D=1048596`. After unscaling, they are legal
decimal certification states bracketing pi and sharing all D certified
fractional digits. On every preterminal common-digit transition through
`0 <= j <= D-2`, their circle separation is multiplied by exactly 10.
Consequently this legal family disproves every pointwise certification-carry
contraction with factor `kappa<10`, in particular every contraction with
`0 <= kappa<1`.

This closes only the proposal that Chudnovsky **certification uncertainty
itself** contracts under decimal carry propagation. It does not refute a
different Chudnovsky-based averaged transfer operator, cancellation theorem,
or relation among different truncations. It proves no T64 boundary estimate,
no T64 Fourier estimate, no T14 triangular family, no C1, no C2, no
normality statement, and no canonical near-return estimate.

Finite checks in `verify_note.py` are sanity checks only. The numbered algebra
below is the proof sketch. There is no Lean theorem in this delivery.

## 1. Canonical target and ambiguities

The byte-exact statement is `canonical_statement.txt`, SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For real `x`, let `||x||_(R/Z)=inf_(z in Z)|x-z|`. For integers `n,N>=1`,

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2 :
  ||(10^i-10^j)*pi||_(R/Z) < 10^(-n)}.
```

The canonical question is

```text
for every integer A>=1, there exists n0>=1 such that
for every integer n>=n0, there exists N>=1 such that
  A*n*Q_pi(n,N) <= N^2.
```

Pairs are ordered, the diagonal is included, the circle inequality is strict,
the base is 10, powers are consecutive, and `N` may depend on `A,n`. This note
does not use an infinitely-many-`n`, fixed-`A`, prescribed-`N`, unordered,
off-diagonal, non-strict, finite-data, or almost-everywhere sibling.

## 2. Endpoints declared before derivation

### 2.1 SUCCESS endpoint required by the agenda

A success would consist of fixed constants and objects

```text
0 <= kappa < 1,
0 < d, 0 <= B, m0,k0 in N,
N : N -> N strictly increasing with N(k)>0,
nu a probability measure on R/Z,
```

such that the empirical measures at the one prefix sequence `N(k)` converge
weakly to `nu`, and for every `k>=k0` and every `m0<=m<=k`, at least
`d*m-B` levels `1<=ell<m` admit an explicit contraction of actual
Chudnovsky-derived carry states which quantitatively proves both literal T64
premises at `(ell,N(k))`. The checked T64 implication would then give the
splitting constants

```text
mu = 3281/7281, eta = 1/100,
```

on those levels and hence the checked T14 frontier on the same triangle and
prefix sequence. Merely approximating each T64 variable numerically would not
meet this endpoint.

No such success is proved here.

### 2.2 FALSIFICATION endpoint tested here

The concrete proposal tested is **pointwise certification-carry contraction**:
there is a `kappa<1` such that every pair of legal normalized decimal states
obtained from a Chudnovsky certification bracket satisfies

```text
rho(T(x),T(y)) <= kappa*rho(x,y)
```

at every common-digit transition used to propagate the bracket, where
`T(x)=fract(10*x)` and `rho` is circle distance.

Falsification means one exact legal pair or family for which every such
`kappa` fails. Sections 7-8 produce a stronger family: the ratio is exactly 10
at every one of `D-1` transitions. This is the terminal endpoint of the note.

The quantified proposal is intentionally narrower than all imaginable
carry-based operators. The note does not turn its falsification into a claim
that T64 itself is false or inaccessible.

## 3. Source-pinned Chudnovsky identity

Put

```text
C = 640320, A = 13591409, B = 545140134,
u_k = (-1)^k*(6k)!*(A+B*k) / ((3k)!*(k!)^3*C^(3k)),
S = sum_(k>=0) u_k.
```

Milla, Theorem 10.12, printed/PDF page 44, gives the Chudnovsky identity in
the equivalent form

```text
sqrt(C^3)/(12*pi) = S.
```

The exact integer identity

```text
C^3 = (12*426880)^2*10005
```

therefore yields

```text
pi = 426880*sqrt(10005)/S.                       (3.1)
```

All radicals are positive. `SOURCE_PINS.md` records the proof source, original
attribution, URLs, hashes, and page/equation locators. No digit-distribution
claim is attributed to either source.

## 4. Exact binary-splitting recurrence

For `r>=1`, set

```text
p_r = (6r-5)*(2r-1)*(6r-1),
q_r = r^3*C^3/24,
t_r = (-1)^r*p_r*(A+B*r).
```

For `r=0`, set `(p_0,q_0,t_0)=(1,1,A)`. For integers `0<=a<b`, define

```text
P_[a,b) = product_(a<=r<b) p_r,
Q_[a,b) = product_(a<=r<b) q_r,

T_[a,b)/Q_[a,b) =
  sum_(a<=r<b) (product_(a<=s<r) p_s/q_s)*(t_r/q_r).       (4.1)
```

Empty products are one. Splitting at `a<c<b`, direct distributivity gives

```text
P_[a,b) = P_[a,c)*P_[c,b),
Q_[a,b) = Q_[a,c)*Q_[c,b),
T_[a,b) = T_[a,c)*Q_[c,b) + P_[a,c)*T_[c,b).              (4.2)
```

This is exactly `t17_certify_pi.py` lines 30-44. Equation (4.1) also corrects
a possible overreading of the implementation's short docstring: for `a>0`,
`T/Q` is a locally normalized tail. At the root `a=0`, cancellation gives

```text
product_(1<=r<=k) p_r/q_r
  = (6k)! / ((3k)!*(k!)^3*C^(3k)),
```

so

```text
T_[0,N)/Q_[0,N) = sum_(0<=k<N) u_k = S_N.         (4.3)
```

Proof of the product identity: the three factors in `p_r` over `1<=r<=k`
are exactly the factors of `(6k)!` left after canceling `(3k)!` and three
copies of `k!`; `24^k` from the `q_r` denominator supplies the corresponding
power-of-two cancellation. Equivalently, checking the ratio of the two sides
from `k` to `k+1` gives `p_(k+1)/q_(k+1)`, and both sides are one at `k=0`.

Thus (4.2) is a summation recurrence for one scalar series. It is not by
itself a decimal carry recurrence or an ensemble over orbit indices.

## 5. Exact recurrence-to-certificate construction

T17 takes

```text
D = 1048596, M = 10^D, N_terms = 74919.
```

The elementary ratio bound retained in T17 is

```text
|u_(k+1)/u_k| < 6^6*42/C^3
              = 1959552/262537412640768000 < 1.            (5.1)
```

Therefore adjacent partial sums bracket the alternating series. Since
`N_terms` is odd, the exact order is

```text
S_(N_terms+1) < S < S_(N_terms).                           (5.2)
```

Let

```text
R = floor(sqrt(10005)*M).
```

Exact integer squaring checks

```text
R^2 <= 10005*M^2 < (R+1)^2.                               (5.3)
```

The left inequality is strict after taking square roots: `10005` is not a
square because `100^2<10005<101^2`, so `10005*M^2` is not a square.

Combining (3.1), (5.2), and (5.3), with the adjacent partial sums written as
positive integer ratios, gives exact rational endpoints

```text
L_s < pi*M < U_s.                                          (5.4)
```

The four endpoint integers are vendored in `t17_interval_endpoints.hex`. The
subscript `s` means **scaled**: these rationals bracket `pi*M`, not pi. Write

```text
L_s = L_num/L_den, U_s = U_num/U_den,
lambda = L_s/M, upsilon = U_s/M.                           (5.5)
```

Then

```text
lambda < pi < upsilon.                                     (5.6)
```

The distinction between (5.4) and (5.6) is essential in every carry formula.

## 6. Strong exact property of the retained endpoints

Define

```text
K = floor(L_s).
```

Cross multiplication of the retained integers proves the stronger chain

```text
K < L_s < U_s < K+1.                                       (6.1)
```

The original certification check only needed that `K` was the unique integer
forced between the endpoint bounds. Equation (6.1) additionally proves that
both rational endpoints are nonintegral and have the same scaled floor.
`verify_note.py` checks every strict inequality in (6.1) directly on the
vendored integers.

It follows that `lambda` and `upsilon` share the integer part and all D digits
after the decimal point encoded by `K=floor(10^D*x)`. This is a property of
the actual retained endpoint pair, not a statistical inference from the
certified pi digits.

## 7. Normalized decimal carry states and influence operator

### 7.1 Real states and rational representatives

For every real `x`, define the normalized decimal state

```text
c_j(x) = fract(10^j*x),
d_j(x) = floor(10*c_j(x)).                                 (7.1)
```

Then, for every real state,

```text
c_(j+1)(x) = 10*c_j(x)-d_j(x) = T(c_j(x)),                 (7.2)
```

where `T(x)=fract(10*x)`.

For a nonnegative rational `x=a/b`, `b>0`, these states have the exact integer
representation

```text
Q_j(x) = floor(10^j*x),
r_j(x) = 10^j*a - Q_j(x)*b,
c_j(x) = r_j(x)/b,
d_j(x) = floor(10*r_j(x)/b).                               (7.3)
```

Then `0<=r_j<b`, `d_j` is the next decimal digit, and Euclidean division gives

```text
Q_(j+1) = 10*Q_j+d_j,
r_(j+1) = 10*r_j-d_j*b,
c_(j+1) = 10*c_j-d_j.                                      (7.4)
```

### 7.2 Pair carry-influence operator

For two rational states `x_-=a_-/b_-` and `x_+=a_+/b_+`, define their exact
cross-denominator influence

```text
E_j = r_j(x_+)*b_- - r_j(x_-)*b_+.                         (7.5)
```

Thus `E_j/(b_-*b_+)=c_j(x_+)-c_j(x_-)`. Define the pair update operator

```text
C((r_-,b_-),(r_+,b_+)) =
  ((10*r_- - d_-*b_-, b_-),
   (10*r_+ - d_+*b_+, b_+)),                               (7.6)
```

where `d_sigma=floor(10*r_sigma/b_sigma)`. Substitution into (7.3) proves the
exact influence recurrence

```text
E_(j+1) = 10*E_j - (d_j(x_+)-d_j(x_-))*b_-*b_+.            (7.7)
```

At a common-digit transition this becomes

```text
d_j(x_+)=d_j(x_-)  ==>  E_(j+1)=10*E_j.                   (7.8)
```

This `C` is the literal normalized decimal carry-influence operator tested by
the falsification endpoint. It is derived from the recurrence-produced
endpoints, not from rational-approximation moduli or multiplicative orders.

## 8. Exact legal-state obstruction

Let `w=U_s-L_s`. Equation (6.1) gives

```text
0 < w < 1.                                                  (8.1)
```

Since `L_s<pi*M<U_s`, every real pair

```text
lambda <= x < y <= upsilon                               (8.2)
```

also satisfies `K<10^D*x<10^D*y<K+1`. For every integer
`0<=j<=D`, division by the integer `10^(D-j)` gives

```text
floor(10^j*x) = floor(10^j*y)
  = floor(K/10^(D-j)).                                     (8.3)
```

Indeed, writing `K=q*10^(D-j)+r` with
`0<=r<10^(D-j)`, the added fractional part from either endpoint is strictly
less than `1/10^(D-j)` and cannot reach the next integer.

Subtracting the equal integer parts in (8.3) gives the exact representative
separation

```text
c_j(y)-c_j(x) = 10^j*(y-x).                                (8.4)
```

For `0<=j<=D-2`, both the current and next separations are below `1/2`:

```text
0 < 10^j*(y-x) < 1/100,
0 < 10^(j+1)*(y-x) < 1/10,                                (8.5)
```

because `0<y-x<=upsilon-lambda=w/10^D` and (8.1) holds.

Therefore circle distance equals the displayed positive representative, and
(8.4) proves

```text
rho(c_(j+1)(x),c_(j+1)(y))
  = 10*rho(c_j(x),c_j(y))                                  (8.6)
```

for every `0<=j<=D-2`.

### Theorem 8.1: sharp falsification

Let the exact endpoint family be

```text
L_D = {(c_j(lambda),c_j(upsilon)) : 0<=j<=D-2}.
```

Then

```text
for every real kappa<10 and every 0<=j<=D-2,
  rho(c_(j+1)(lambda),c_(j+1)(upsilon))
    > kappa*rho(c_j(lambda),c_j(upsilon)).                 (8.7)
```

Proof: the right-hand distance is positive by (8.4), and (8.6) makes the ratio
exactly 10. QED.

The same exact identity applies to the actual T64 state pair
`(x,y)=(lambda,pi)` because `lambda<pi<upsilon`. Thus

```text
rho(c_(j+1)(lambda),c_(j+1)(pi))
  = 10*rho(c_j(lambda),c_j(pi)), 0<=j<=D-2.                (8.8)
```

Equation (8.8) connects the legal recurrence endpoint directly to the actual
pi carry states. It still does not assert anything about cancellation after
summing phases over `j`.

In particular, for every `0<=kappa<1`, the proposed pointwise
certification-carry contraction fails on every member of this exact legal
family. The threshold 10 is sharp: the decimal map is globally 10-Lipschitz
in circle distance and locally attains factor 10 here.

This is an algebraic family statement for the source-pinned endpoint integers,
not a conclusion inferred from a finite digit experiment.

## 9. Exact identity with T64 variables

Put

```text
e(t) = exp(2*pi*i*t),
piOrbit(j) = fract(10^j*pi) = c_j(pi),
Z_P^x(h) = sum_(0<=j<P) e(h*c_j(x)), h in Z.                (9.1)
```

Integer-frequency periodicity gives the exact identity

```text
fullSampleSpectrum(piOrbit,P,h)
  = Z_P^pi(h)
  = sum_(0<=j<P) e(h*10^j*pi).                             (9.2)
```

Thus T64's empirical Fourier coefficient is `Z_P^pi(h)/P`; T64 itself uses
the unnormalized `Z_P^pi(h)`.

For a base state `x` and a real perturbation `delta`, define the spectral
carry-influence operator

```text
I_(P,h)(x,delta) = sum_(0<=j<P)
  e(h*c_j(x))*(e(h*10^j*delta)-1).                         (9.3)
```

Since `e(h*c_j(x))=e(h*10^j*x)`, multiplication of phases proves

```text
Z_P^(x+delta)(h)-Z_P^x(h) = I_(P,h)(x,delta).               (9.4)
```

In particular, with `x=lambda` and `delta=pi-lambda`,

```text
Z_P^pi(h) = Z_P^lambda(h)+I_(P,h)(lambda,pi-lambda).       (9.5)
```

For `0<=j<=min(P-1,D-2)`, the `j`-th summand in (9.3) is exactly

```text
e(h*c_j(pi))-e(h*c_j(lambda)),                             (9.6)
```

and its underlying carry-state separation obeys (8.8). Equations (9.3)-(9.6)
are the exact recurrence-endpoint-to-T64 identity. They expose the narrow
obstruction: the endpoint spectrum `Z_P^lambda` is **not** the T64 spectrum,
and the correction contains all expanding decimal state differences. The
elementary absolute bound

```text
|I_(P,h)(lambda,pi-lambda)|
  <= 2*pi*|h|*(pi-lambda)*(10^P-1)/9
  <= 2*pi*|h|*(upsilon-lambda)*(10^P-1)/9                 (9.7)
```

certifies approximation when the bracket is sufficiently narrow but supplies
no cancellation or sign for the actual spectrum.

## 10. Literal T64 tensor, ranges, boundaries, and constants

This section records the checked interface without reproving its generic
cross-row coefficient algebra. The controlling source is the vendored
`T64AggregateFejerCriterion.lean`.

Fix

```text
1 <= ell < m <= k, P=N(k)>0, q=10^ell.                    (10.1)
```

The parent and successor Fejer orders and boundary widths are

```text
H0 = 40*q^3,      delta0 = 1/(4*q^2),
H1 = 8000*q^3,    delta1 = 1/(400*q^2).                   (10.2)
```

For `Q,H` and `|h|<=H`, let

```text
a_(Q,H)(0)=1/Q,
a_(Q,H)(h)=(1-|h|/(H+1))*sin(pi*h/Q)/(pi*h), h!=0,

C_(Q,H)(h,r) =
  Q*a_(Q,H)(h)*a_(Q,H)(r)*e(-(h+r)/(2Q)) if Q divides h+r,
  0 otherwise.                                             (10.3)
```

Every divisibility alias is retained. With only `(h,r)=(0,0)` deleted,
T64's remainder is exactly

```text
R_(ell,P) =
  sum_(|h|,|r|<=H1; (h,r)!=(0,0))
    C_(10*q,H1)(h,r)*Z_P^pi(h)*Z_P^pi(r)
  - (1/2)*sum_(|h|,|r|<=H0; (h,r)!=(0,0))
    C_(q,H0)(h,r)*Z_P^pi(h)*Z_P^pi(r).                    (10.4)
```

There is no complex conjugate in (10.4). The literal Fourier premise is

```text
|R_(ell,P)| <= P^2/(10*q).                                (10.5)
```

Let `B_succ` count visits among `j<P` within `delta1` of either endpoint of
the unique active half-open successor cylinder at depth `ell+1`, and let
`B_parent` use `delta0` at depth `ell`. The literal boundary premise is

```text
B_succ+(1/2)*B_parent <= P/(40*q).                         (10.6)
```

T64 machine-checks from (10.1), (10.5), and (10.6) that

```text
QuantitativeSplittingLevel ell P (3281/7281) (1/100),
rowThreshold ell P (1/100) (3281/7281).                   (10.7)
```

The exact defect calculation retained by T64 is

```text
E_(ell+1)(P)-(1/2)*E_ell(P) <=
  -2*P^2/(5*q) + |R_(ell,P)|
  + 4*P*(B_succ+(1/2)*B_parent)
  + 800*q^2*P^2/(8000*q^3+1)
  + 4*q^2*P^2/(40*q^3+1).                                (10.8)
```

Neither (10.5) nor (10.6) is established here. Substitution of (9.5) into
(10.4) is exact but leaves the actual phase corrections (9.3); taking only
their approximation norms merely reproduces a rational-approximation error
budget and cannot create the negative defect in (10.8).

## 11. Every triangular quantifier and the quantitative T14 substitution

T14's checked fixed-parameter predicate is

```text
PiCoherentPositiveDensitySplittingAt mu eta d B m0 k0 N nu
```

and means exactly

```text
0<mu<1, 0<eta<=1/10, 0<d, 0<=B,
StrictMono N, for every k: N(k)>0,
piDecimalEmpiricalMeasure(N(k)) -> nu weakly,
for every k>=k0, for every m>=m0 with m<=k:
  d*m-B <= piSplittingLevelCount(m,N(k),mu,eta).           (11.1)
```

The count includes exactly levels `ell<m`. All constants and the sequence
`N` are fixed before `k,m,ell`; separate row-dependent prefixes are not enough.

If, for one such `N`, at least `d*m-B` levels `1<=ell<m` satisfied both
(10.5) and (10.6) for every triangle entry in (11.1), T64 would substitute

```text
mu=3281/7281, eta=1/100                                   (11.2)
```

on exactly the same prefixes. Together with the positivity, monotonicity, and
weak-limit clauses, this would establish the T14 frontier. This conditional
sentence is only an audit of the checked interface; T82 supplies none of its
pi-specific antecedents.

The finite T17 value `D` cannot satisfy (11.1), which has unbounded `k` and
`m` on one infinite sequence. More fundamentally, (8.6) shows that the tested
certification-carry propagation expands rather than contracts even inside its
finite valid range.

## 12. Negative inventory and semantic checks

`DEPENDENCIES.md` records the accepted library, T63/T68/T78/T79 inventory, and
all relevant semantic obstruction cards with their verification levels. The
constraints used here are:

1. T17 certification is scalar computation, not fixed-pi Fourier
   cancellation.
2. One-row coefficient collection is already machine-checked in T64 and is
   not repeated as a new result.
3. Exact multiplier-ten or Walsh regrouping does not imply ordinary circle
   Fourier decay.
4. Fixed-frequency averaging or irrationality estimates do not evaluate the
   adaptive fixed-pi tensor.
5. Isolated rows, moving windows, and finite prefixes do not meet T14's one
   increasing triangular sequence.
6. T63/T68 concern Zudilin, T78 concerns a factorial series, and T79 concerns
   a Machin specialization. None is cited as a Chudnovsky obstruction.

All conclusions borrowed from proof-sketch notes remain labeled unverified and
are not premises of Theorem 8.1.

## 13. Terminal classification

**Exact legal-state obstruction, limited to certification carries.**

The source-pinned Chudnovsky leaf/merge recurrence and integer square-root
bracket produce the exact legal endpoint pair `(lambda,upsilon)`. Its
normalized decimal carry states satisfy the all-index identity (8.6), so every
pointwise contraction factor `kappa<10`, and hence every required
`0<=kappa<1`, is false on every transition `0<=j<=D-2`.

Therefore Chudnovsky's use in T17 as a decimal **certifier** carries no
pointwise contraction of the tested strength. The exact identities
(8.8)-(10.4) show that the tested contraction cannot be used as the missing
T64 synchronization step: certification writes the actual pi spectrum as an
endpoint spectrum plus corrections whose underlying state separations expand.
This does not prove that the summed corrections are large; they may cancel.
Accuracy bounds the correction but does not bound the endpoint tensor or
create the cancellation required by T64.

This endpoint does not promote C1 or C2 and does not claim that all
Chudnovsky-specific mechanisms are impossible. A future proposal would have
to introduce a genuinely different averaged or phase-sensitive operator and
prove its fixed-pi relation to (10.4), rather than reuse endpoint uncertainty
as if it were a contracting state.

## 14. Replay

From a directory containing only these delivered artifacts, run

```bash
python3 verify_note.py
sha256sum -c SHA256SUMS
```

The first command checks all pinned input hashes, source and interface anchors,
regenerates the full 74,919-term T17 endpoint file byte-for-byte, checks small
exact binary-split identities, every retained endpoint inequality, and
exact factor-10 carry updates near the terminal end. The bounded recurrence and
carry checks are sanity checks. The all-`N` split proof and all-index carry
proof are the displayed algebra in Sections 4 and 8.

## 15. Formalization and review map

- Lean statement: none; this agenda item is a note.
- New axioms or unsafe declarations: none.
- Machine-checked dependencies: T14 and T64 only in the conditional uses
  explicitly identified above.
- Main new endpoint: Theorem 8.1, `proof sketch` pending independent review.
- Literature status: Chudnovsky identity and attribution are source-pinned;
  no novelty claim is made.
- Independent statement, proof, and novelty review: pending.
