# T118: private cyclotomic prime powers and exact-numerator short orbits

Audit date: 2026-08-10 UTC.

Status: source statements are `literature-checked`; the elementary order
argument and transfer calculations are a `proof sketch`; the replayed finite
factorizations and numerical sums are `experiment`. The transfer from a
modular estimate to the prescribed real orbit remains a `conjectural transfer`
unless every displayed premise below is proved for an infinite family.

This is a bounded negative applicability audit. It proves no statement about
the canonical fixed-pi question, C1, or C2.

## 1. Scope and immutable statement

`canonical_statement.txt` is byte-exact and has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question keeps ordered pairs, includes the diagonal, uses
circle distance and consecutive decimal powers, and asks

```text
for every A>=1, there exists n0 such that for every n>=n0,
there exists N>=1, allowed to depend on A,n, with
A*n*Q_pi(n,N)<=N^2.
```

T118 does not alter those quantifiers. It audits only a proposed sufficient
Fourier input. A rational modular orbit, a bounded factorization, or a theorem
for almost every numerator is a sibling/model calculation, not the canonical
conclusion.

The source and mechanism caps are exact:

```text
primary sources inspected: 4 (cap 8)
theorem mechanisms retained: 3 (cap 3)
```

They are enumerated in `SOURCE_PINS.md`; `SEARCH_LOG.md` records the bounded
search boundary.

## 2. Canonical private prime-power selection

### 2.1 Definitions

Fix an integer `r>=1` and put

```text
M_r = 10^r-1,
e_r(p) = v_p(M_r).
```

Define the finite order-separated private set

```text
Priv(r) = {p^e_r(p) : p is prime, e_r(p)>0,
                         ord_p(10)=r}.                    (2.1)
```

The retained modulus is total and canonical:

```text
P_r = max Priv(r), if Priv(r) is nonempty;
P_r = 1,           if Priv(r) is empty.                   (2.2)
```

There is no tie: distinct prime powers have distinct prime bases and hence
cannot be equal. The choice uses the largest *whole p-primary component* of
`M_r`, not an arbitrary prime divisor and not a product selected after seeing
the exponential sum.

For every `r`, define

```text
a_r = nint(P_r*pi),                                       (2.3)
```

where `nint(x)` is the unique nearest integer. Uniqueness follows because pi
is irrational, so `P_r*pi` is not a half-integer. If `P_r=1`, the associated
modular character is trivial and the candidate is rejected before any order
or cancellation theorem. If `P_r>1`, put

```text
L_r = ceil(log_10 P_r),
S(P_r,a_r,h;u,L) = sum_(0<=j<L)
  exp(2*pi*i*h*a_r*10^(u+j)/P_r).                         (2.4)
```

### 2.2 Private and cyclotomic are the same here

This paragraph is an elementary `proof sketch`, independent of the four
literature theorems. If `ord_p(10)=r`, then `p|10^r-1`, while
`p` divides no `10^d-1` for `1<=d<r`. In

```text
10^r-1 = product_(d|r) Phi_d(10),                         (2.5)
```

all the `p`-valuation is therefore in `Phi_r(10)`. Hence each member
`p^e_r(p)` of (2.1) exactly divides the private part of `Phi_r(10)`. Conversely,
a prime divisor of `M_r` absent from every earlier `10^d-1` has order exactly
`r`. Thus (2.1) is a definition by order of the intended private cyclotomic
prime powers; it avoids a hidden exception convention for primes dividing
`r`.

No primitive-divisor existence theorem is used. Empty `Priv(r)` is explicitly
handled by the sentinel `P_r=1`.

### 2.3 Exact prime-power order, including lifting

Let `P_r=p^e>1` be selected. By construction,

```text
ord_p(10)=r,               p^e | 10^r-1.                  (2.6)
```

Reduction modulo `p` shows

```text
r = ord_p(10) | ord_(p^e)(10).                            (2.7)
```

The second part of (2.6) shows

```text
ord_(p^e)(10) | r.                                        (2.8)
```

Therefore

```text
boxed: ord_(P_r)(10)=r.                                   (2.9)
```

This proves every order asserted by the construction. It also handles a
generic order-lifting failure: if passing from `p` to `p^e` would multiply the
order, then `p^e` could not divide `10^r-1`; such an exponent is never selected.

Exceptional primes are explicit. Neither `2` nor `5` divides `M_r`, so every
active `P_r` is coprime to 10. The prime `3` has `ord_3(10)=1`, so it can enter
only `Priv(1)`; its full component is `3^2=9`, and indeed
`ord_9(10)=1`. There is no omitted power-of-2 or power-of-5 transient.

Finally, `P_r|10^r-1<10^r` gives

```text
L_r=ceil(log_10 P_r)<=r.                                  (2.10)
```

Thus the canonical test length is logarithmic in the modulus and lies within
one exact period. The replay checks (2.1)-(2.10) for `1<=r<=18`; those checks
are `experiment`, not an existence proof for all `r`.

### 2.4 CRT loss

The retained modulus is one prime power, so its CRT loss is exactly `1`.
Taking the product of all private components would not improve this audit:
the additive character modulo a product factors into a product of component
characters inside each summand, and separate component upper bounds do not
give pointwise cancellation of the sum of those products. Triangle inequality
would retain trivial factors for uncontrolled components. This is the exact
reason (2.2) selects one component rather than silently claiming a lossless
CRT recombination.

## 3. Literal T64/T107 budget

This section expands machine-checked definitions; it does not assert either
analytic premise for the prescribed orbit. The controlling T64/T107 module
hashes and line locators are in `SOURCE_PINS.md`.

Write `q=10^ell`, and use `X>0` for the orbit-prefix cutoff so it cannot be
confused with the modular prime power `P_r`. T64 uses

```text
H_p = 40q^3,      Q_p=q,
H_c = 8000q^3,    Q_c=10q.                                (3.1)
```

The exact parent/child active-boundary load is

```text
B_p = activeBoundaryCount(piOrbit,X,q,parentCode,1/(4q^2)),
B_c = activeBoundaryCount(piOrbit,X,10q,childCode,1/(400q^2)),
L_boundary = B_c+(1/2)B_p.                                (3.2)
```

The literal boundary premise and normalized boundary defect are

```text
L_boundary <= X/(40q),
D_boundary = 40q*L_boundary/X.                            (3.3)
```

T64's collected Fourier remainder keeps all signed aliases and deletes only
the zero pair:

```text
R_ell(X) = R_child-(1/2)R_parent,
|R_ell(X)| <= X^2/(10q),
D_Fourier = 10q*|R_ell(X)|/X^2.                           (3.4)
```

T107's row defect is

```text
rowAnalyticDefect(ell,X)=max(D_boundary,D_Fourier).        (3.5)
```

Therefore Fourier cancellation cannot compensate for excessive boundary
load.

For completeness, T107 averages this same maximum over exactly
`1<=ell<m`. If one common prefix family made both normalized components at
most `theta<1` on every level in a triangle, then

```text
sum_(ell=1)^(m-1) rowAnalyticDefect(ell,X)
 <= theta*(m-1)
 = (m-1)-((1-theta)*m-(1-theta)).                         (3.5a)
```

Thus its affine defect parameters would be `d=B=1-theta`. This is only
bookkeeping: no mechanism below supplies the boundary component, the common
prefix sequence, or the complete triangle.

For the exact collected coefficient weights put

```text
A_c = 2+log(800q^2+1),
A_p = 2+log(40q^2+1),
W_ell = A_c^2+(1/2)A_p^2.                                 (3.6)
```

T64's checked collected-`L1` bound is `16A_c^2` at the child scale and
`16A_p^2` at the parent scale. Its divisibility selector makes every
one-zero/nonzero alias vanish. Consequently the following is a sufficient,
not necessary, substitution:

```text
|sum_(0<=j<X) exp(2*pi*i*h*10^j*pi)| <= epsilon*X
for every 0<|h|<=H_c

implies

|R_ell(X)| <= 16W_ell*epsilon^2*X^2,
D_Fourier <= 160qW_ell*epsilon^2.                         (3.7)
```

For a desired Fourier share `0<theta<=1`, the literal individual-sum target is

```text
epsilon_ell(theta)=sqrt(theta/(160qW_ell)).                (3.8)
```

The boundary constants are not a cosmetic remainder. Uniform circle points
have child boundary length `1/(20q)` and parent boundary length `1/(2q)`, so
their expected weighted load is

```text
X*(1/(20q)+(1/2)*(1/(2q)))=3X/(10q),
D_boundary=12.                                            (3.9)
```

This does not prove that the actual prefix has defect 12. It proves that an
ordinary uniform or mixing benchmark does not supply (3.3); a successful
prefix needs boundary depletion by a factor twelve.

## 4. Transfer inequality derived before theorem use

This section is an elementary `proof sketch`. It precedes all cancellation
theorem substitutions.

For an active `P=P_r`, write `a=a_r` and

```text
Delta_r = |pi-a/P| <= 1/(2P).                              (4.1)
```

Define the actual real block and its modular model by

```text
T_real(h;u,L) = sum_(0<=j<L) exp(2*pi*i*h*10^(u+j)*pi),
T_mod(h;u,L)  = S(P,a,h;u,L).                             (4.2)
```

Using `|exp(2*pi*i*x)-exp(2*pi*i*y)|<=2*pi*|x-y|` term by
term gives the complete phase error

```text
|T_real-T_mod|
 <= 2*pi*|h|*Delta_r*sum_(0<=j<L)10^(u+j)
 = (2*pi/9)|h|*Delta_r*10^u*(10^L-1).                    (4.3)
```

Suppose a source theorem gives the pointwise bound

```text
|T_mod(h;u,L)| <= B_h(P,u,L).                             (4.4)
```

To enter the literal sufficient T64 budget (3.7)-(3.8), it is enough, and for
this triangle-inequality transfer exactly required, that for every
`0<|h|<=H_c`,

```text
B_h(P,u,L)+(2*pi/9)|h|*Delta_r*10^u*(10^L-1)
 <= epsilon_ell(theta)*L.                                 (4.5)
```

Thus one must first have `B_h<epsilon_ell(theta)L`, and the exact simultaneous
approximation requirement is

```text
Delta_r <= min_(0<|h|<=H_c)
  9*(epsilon_ell(theta)*L-B_h(P,u,L))
  / (2*pi*|h|*10^u*(10^L-1)).                            (4.6)
```

If one has only a uniform `B_h<=B_*`, the coarser literal test is

```text
B_*<epsilon_ell(theta)L,
Delta_r <= 9*(epsilon_ell(theta)*L-B_*)
 / (2*pi*H_c*10^u*(10^L-1)).                             (4.7)
```

Equations (4.5)-(4.7) include frequencies, geometric growth, and the exact
T64 weight through (3.8). For the actual T64 prefix take `u=0,L=X`. A shifted
block can be audited with its displayed `10^u` loss, but it does not replace
the full prefix without a separate decomposition and boundary argument.

Even in the optimistic case `B_*=0`, using only the rounding guarantee in
(4.1) would require

```text
pi*H_c*10^u*(10^L-1)/(9P)
 <= epsilon_ell(theta)*L.                                 (4.8)
```

No source supplies (4.8). Since `L=L_r` has `P<=10^L<10P`, the required upper
bound in (4.7) has base scale

```text
Delta_r << epsilon_ell(theta)*L/(H_c*10^u*P),             (4.9)
```

before paying any positive modular cost.

The cancellation sources below estimate neither `B_c` nor `B_p`. Closeness of
two orbit points could move a boundary visit by at most the phase error in
(4.3), but it cannot prove the depleted count (3.3). Thus even a successful
(4.5) would leave the independent boundary half of (3.5) open.

## 5. Irrationality scale comparison

This source application is `literature-checked` for the quoted theorem and a
`proof sketch` for the substitution.

Put

```text
d_r=gcd(a_r,P_r),       Q_r=P_r/d_r.                      (5.1)
```

Then `a_r/P_r` reduces to denominator `Q_r`. Zeilberger--Zudilin define the
irrationality exponent with the eventual inequality and prove

```text
M=mu(pi)<=7.1032053341370017275... .                       (5.2)
```

For every fixed `eta>0` and all sufficiently large reduced denominators,

```text
Delta_r > Q_r^(-(M+eta)).                                 (5.3)
```

Combining (4.1) and (5.3) gives

```text
Q_r > (2P_r)^(1/(M+eta)).                                 (5.4)
```

This is a lower bound, not the upper approximation required by (4.6). It does
not certify any favorable nearest-integer event. At `L_r=Theta(log P_r)`,
(4.9) asks at least for a near-`P_r^(-1)` upper approximation, with additional
frequency loss. The accepted lower barrier is only of order
`P_r^(-(M+eta))` when `Q_r` is comparable to `P_r`; the exponents leave a wide
unresolved interval.

For an explicit conditional exponent comparison, if
`q=P_r^(beta+o(1))`, `u=0`, `L=L_r`, and `Q_r=P_r^(1+o(1))`, then (3.1),
(3.8), and (4.9) require

```text
Delta_r <= P_r^(-(1+(7/2)beta)+o(1)).                     (5.5)
```

This would contradict (5.3) only if

```text
1+(7/2)beta > M+eta.                                      (5.6)
```

Neither comparability assumption is established here. Equations (5.5)-(5.6)
are a scale diagnostic, not a fixed-pi conclusion.

## 6. Mechanism M1: Bailey--Crandall completion

### 6.1 Exact source statement and substitution

Bailey--Crandall Lemma 4.5, printed p. 13, fixes coprime `b,c>1`, defines
`c1(c)` in Lemma 4.3, and for

```text
d=gcd(H,c)<c/c1(c),       1<=J<=ord(b,c),                 (6.1)
```

proves

```text
|sum_(0<=j<J) exp(2*pi*i*H*b^j/c)|
 < sqrt(c/d)*(1+log(c/d)).                                (6.2)
```

Substitute, without changing the numerator,

```text
b=10, c=P_r, H=h*a_r*10^u,
d_h=gcd(h*a_r,P_r), Q_h=P_r/d_h, J=L.                    (6.3)
```

Because `P_r` is coprime to 10, the gcd is independent of `u`. Equations
(2.9)-(2.10) give `L<=ord_(P_r)(10)=r`. The remaining source hypothesis is

```text
Q_h>c1(P_r).                                              (6.4)
```

For the canonical full private component this hypothesis can be evaluated
exactly. Bailey--Crandall Lemma 4.3 takes

```text
tau_1=ord_p(10)=r,
beta=v_p(10^tau_1-1)=v_p(10^r-1)=e.
```

The even-modulus correction is absent. With `P_r=p^e`, the lemma therefore
gives

```text
c1(P_r)=p^min(e,beta)=p^e=P_r.                            (6.5)
```

But `d_h=gcd(h*a_r,P_r)>=1`, so

```text
d_h < P_r/c1(P_r)=1                                      (6.6)
```

is impossible. Equivalently, `Q_h<=P_r=c1(P_r)`, contrary to (6.4).
Bailey--Crandall Lemma 4.5 is therefore unavailable for every canonical
active modulus and every frequency. This exact unmet source hypothesis is the
first rejection; no bound from the lemma is applied.

### 6.2 Counterfactual scale screen

If one deletes the failed `c1` hypothesis and optimistically grants the shape
of the source output, it would be

```text
B_h=sqrt(Q_h)*(1+log Q_h).                                (6.7)
```

This is not a theorem application to `P_r`; it is a deliberately stronger
counterfactual test. T64 needs `h=1`, and equations (5.4) and (6.7) would give

```text
B_1 > (2P_r)^(1/(2(M+eta))).                              (6.8)
```

The right side is a positive power of `P_r`, whereas

```text
epsilon_ell(theta)*L_r <= L_r = O(log P_r).               (6.9)
```

Hence even this unlicensed optimistic bound would fail the prerequisite in
(4.6):

```text
B_1 < epsilon_ell(theta)*L_r                              (6.10)
```

for all sufficiently large active moduli. This does not assert that the
actual sum is large. It records that removing the source-hypothesis failure
would still leave the familiar positive conductor exponent.

Bailey--Crandall Theorem 4.6 does not repair (6.10): it fixes one base modulus
`c` and lets `c^n` grow, while `P_r` may have varying prime base; its leading
term has the same square-root-modulus scale. No averaging over numerators is
used, but the pointwise bound is too long-scale.

## 7. Mechanism M2: Kerr ordered prime prefixes

### 7.1 Exact source statement and character

Kerr Theorem 2, printed p. 2, treats prime modulus `p`, an element `g` of
order `t`, and `N<=t`. Its source sum starts at exponent one. Therefore M2
applies only when the canonical modulus has exponent `e=1`, and the exact
substitution is

```text
p=P_r, g=10, t=r, N=L,
lambda = h*a_r*10^(u-1) mod p.                            (7.1)
```

Here `10^(-1)` is modulo `p`. Source applicability requires

```text
p does not divide h*a_r,          L<=r.                   (7.2)
```

For uniform T64 frequencies, (7.2) already requires `p>H_c` and
`p` not dividing `a_r`; otherwise one legal `h` gives the zero character and
the modular sum equals `L`. If these hypotheses fail, M2 stops at (7.2).

When they hold, Kerr's three branches become

```text
B_h <= p^(1/8)L^(71/96+o(1)),
    L<=r^(1/2);                                           (7.3a)

B_h <= p^(1/8)r^(-1/96)L^(73/96+o(1)),
    r^(1/2)<L<=p^(1/2);                                   (7.3b)

B_h <= p^(1/4)r^(-1/96)L^(49/96+o(1)),
    p^(1/2)<L<r.                                          (7.3c)
```

The `o(1)` source notation also supplies no literal finite constant for
(4.5); the following exponent test is already fatal.

### 7.2 All branch rejections at logarithmic length

For (7.3a) even beating the trivial `L` requires

```text
p^(1/8)L^(71/96+o(1))<L
iff L>p^(12/25+o(1)).                                     (7.4)
```

This fails for `L=L_r=O(log p)`.

In branch (7.3b), the branch condition gives `r<L^2`. Thus
`r^(-1/96)>L^(-2/96)`, and nontriviality again forces

```text
p^(1/8)L^(71/96+o(1))<L,
```

which is the same failed inequality (7.4). Branch (7.3c) requires
`L>p^(1/2)` before its bound is available, directly contradicting
`L=O(log p)` for large `p`.

Thus no branch reaches even `B_h<L`, much less
`B_h<epsilon_ell(theta)L`. The theorem is pointwise and uses the correct
ordered prefix, but it is prime-only and polynomial-length.

## 8. Mechanism M3: Bourgain sum-product

Bourgain Theorem 3.2, equation (22), fixes `epsilon>0`, works modulo a prime,
and assumes

```text
ord_p(theta_i)>p^epsilon,
ord_p(theta_i*theta_j^(-1))>p^epsilon,
t>p^epsilon.                                              (8.1)
```

It then gives a pointwise bound `p^(-delta)t` uniformly over nonzero
coefficients. For the one-base T118 sum, the ratio condition is vacuous and
the exact substitution (again only for `P_r=p`) is

```text
theta_1=10, ord_p(10)=r, t=L,
coefficient=h*a_r*10^(u-1) mod p.                         (8.2)
```

In addition to the nonzero-character condition from (7.2), the source needs

```text
r>p^epsilon,       L>p^epsilon.                           (8.3)
```

For every fixed `epsilon>0`, the second inequality in (8.3) fails at
`L=L_r=O(log p)`. Letting `epsilon` depend on `p` is not licensed: the source
quantifies with fixed `epsilon`, and `delta` depends on it. M3 therefore fails
before its cancellation exponent can be compared with (3.8). It has no stated
prime-power extension.

## 9. Complete-period, averaging, scalar, and CRT screens

The following rejections are part of the audit rather than omitted searches.

| proposed repair | exact rejection |
|---|---|
| complete period | `L=r` is legal, but a complete-subgroup estimate with `r>p^theta` violates logarithmic `L=O(log p)`; a complete estimate with no ordered-prefix consequence does not bound (2.4) for `L<r` |
| numerator average | T64 prescribes every `h*a_r`; a moment over numerators, moduli, or `r` does not locate these characters |
| replace `a_r` | any theorem for an unrelated numerator breaks (4.2), so (4.3) no longer transfers it to the prescribed real block |
| scalar avoidance | a lower bound on one phase distance does not upper-bound a signed sum and supplies no collected remainder cancellation |
| product private part | component characters multiply inside each summand; separate bounds do not combine without uncontrolled CRT factors, while (2.2) has loss exactly one |
| zero character | if a legal `h` annihilates the numerator modulo the retained modulus, the modular sum is exactly `L`, violating (3.8) |
| finite factorization | it is an `experiment` and cannot establish an infinite order or cancellation family |

## 10. T78/T79/T85 scale barrier

These three prior reports are notes; their new deductions are unverified
`proof sketch` material and are not premises here.

The T78 note argues that its factorial reduced modulus leaves a
square-root-modulus cost larger than the entire transferred length. The T79
note isolates an exact prime-power component and exact numerator orbit but no
pointwise logarithmic bound. The T85 note repairs a least-valuation step,
exhibits numerator sensitivity, and records that a uniform all-numerator
logarithmic theorem is false in its model while the special numerator remains
open.

M1 actually fails earlier at the sourced hypothesis (6.6). As an explicitly
counterfactual comparison only, deleting that hypothesis and combining the
optimistic shape (6.7) with accepted irrationality gives (6.8):

```text
sqrt(Q_r) > P_r^(1/(2(M+eta)))
```

up to constants, while (6.9)-(6.10) leave only `O(log P_r)` length. This is not
an application of Bailey--Crandall. It shows that even repairing M1's first
source failure without improving its bound would retain the prior scale wall.
Order separation removes transient, lifting, and CRT ambiguity, but it does
not create special-numerator cancellation.

## 11. Novelty and nearest fingerprints

Verification levels are explicit. Notes are comparison memory only and are
not used as discharged premises.

The accepted T116 report is vendored byte-exactly as `t116-report.md`,
SHA-256
`573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1`,
so its comparison below does not depend on an external library snapshot.

| item | level used | normalized fingerprint | relation to T118 |
|---|---|---|---|
| T63 | `literature-checked` applicability audit | pi representations -> rational phase -> generic modular orbit estimate; moving frequencies and square-root cost remain | T118 changes to native private prime powers and fixes `a_r`; M1 first fails because `c1(P_r)=P_r`, with the square-root barrier retained only as a counterfactual screen |
| T68 | `machine-checked` route-specific obstruction | exact removal of a power-of-5 transient and incompatible tail inequalities | T118 primes are coprime to 10 and have no transient; (2.9) is a different direct order argument |
| T78 | source component `literature-checked`, deductions `proof sketch`, replay `experiment` | factorial rational approximants with exact order/collision data and square-root scale failure | T118 is not factorial and has loss-one prime-power order separation; M1 fails at (6.6), while only the counterfactual (6.7)-(6.10) reproduces the scale obstruction |
| T79 | `proof sketch` literature/exact-arithmetic audit | Machin rational tail with a forced prime-power component and exact orbit sum, no bound | T118 makes the component canonical across `r` and fixes nearest numerator rather than a representation numerator |
| T85 | `proof sketch`; replay `experiment` | tie-complete valuation analysis and special-numerator gap | T118 directly tests that gap; no retained theorem exploits the nearest numerator |
| T87 | sources `literature-checked`, synthesis/substitutions `proof sketch` | numerator-conductor cancellation for the exact adaptive sum, killed by logarithmic length | nearest prior fingerprint; T118 removes CRT ambiguity, but M1 fails its exact `c1` condition and its optimistic bound still has positive-power cost |
| T104 | sources `literature-checked`, transfers `proof sketch` | ambient/model Fourier decay with fixed-fiber membership missing | T118 is pointwise modular arithmetic, not an ambient measure, but its real transfer is still unproved |
| T105 | sources `literature-checked`, deductions `proof sketch`, replay `experiment` | Kerr and complete-subgroup estimates fail at prescribed character/logarithmic length | M2 sharpens the same card with canonical `P_r,a_r` and all three Kerr branches; no survivor results |
| terminal T109 | only secondary T113 fingerprint available: sources reported `literature-checked`, transports `proof sketch`, rejected record | Markov-law/shadowing/Wasserstein robustness transport; sufficient certificate was incorrectly treated as necessary | no readable T109 artifact was supplied; T118 uses direct phase error (4.3), not model shadowing, and makes no novelty claim against unavailable details |
| T113 | sources `literature-checked`, deductions `proof sketch`, replay `experiment` | variable-threshold scalar avoidance constructs an unnamed sibling; `PI-AVOID` remains unproved | avoidance is explicitly rejected in Section 9; no cancellation or private modulus overlap |
| T114 | sources `literature-checked`, determinant transfers `proof sketch` | Padé/interpolation determinant rank and height screens | disjoint from order-separated modular sums; T118 has no determinant premise |
| T115 | sources `literature-checked`, recurrences/transfers `proof sketch`, replay `experiment` | exact Riesz recursion gives a persistent decimal Fourier ray | model recurrence is not a modular pointwise estimate; both leave fixed-orbit transfer explicit |
| T116 | sources `literature-checked`, selector deductions `proof sketch`, replay `experiment` | computable variable-depth dyadic avoidance selects an artificial sibling point with all-difference lower bounds; its fixed-pi `PI-RS` transfer remains unproved | disjoint: T118 fixes the prescribed nearest numerator and audits a modular character sum, whereas T116 constructs a different point and supplies no private prime-power modulus, multiplicative-order estimate, prescribed-character cancellation, or T64/T107 bound; T118 supplies no effective selector branch, so neither mechanism discharges the other's transfer |
| T117 | no readable artifact in the supplied library or record snapshot | unavailable | no content inferred and no premise used |
| obstruction memory | unverified ledger | order, regrouping, scalar bounds, and finite classification are not cancellation | obeyed: (2.9) is not promoted to a sum bound, and every cancellation failure is sourced independently |

The normalized T118 fingerprint is

```text
exact-order private p-primary component of 10^r-1
 -> canonical largest prime power P_r with ord_(P_r)(10)=r
 -> nearest fixed numerator a_r=nint(P_r*pi)
 -> pointwise ordered orbit at L_r=ceil(log_10 P_r)
 -> literal phase transfer into T64/T107 weights and frequencies.
```

The first three arrows are exact definitions and elementary order arithmetic.
The fourth and fifth arrows require cancellation and approximation estimates
that none of M1-M3 supplies.

## 12. Replay and classification boundary

From a directory containing only the delivered files, run

```text
python3 verify_t118.py
sha256sum -c SHA256SUMS
```

The script verifies all source and canonical hashes, text anchors, caps,
labels, comparison rows, and terminal markers. It factors `10^r-1` for
`1<=r<=18`, constructs (2.1)-(2.3), checks `P_r|Phi_r(10)`, verifies every
computed prime and prime-power order, evaluates the fixed-numerator modular
sum at `L_r`, and prints one optimistic literal transfer comparison. All such
finite output is `experiment` only.

The source theorem tests are negative but informative: private order
separation makes Bailey--Crandall's `c1` condition impossible and does not
solve restricted approximation, logarithmic-length cancellation,
special-numerator sensitivity, or the independent boundary budget. No
retained mechanism reaches the first T64 Fourier prerequisite.

SCOPED VERDICT: close

BOUNDED SUCCESSOR: none
