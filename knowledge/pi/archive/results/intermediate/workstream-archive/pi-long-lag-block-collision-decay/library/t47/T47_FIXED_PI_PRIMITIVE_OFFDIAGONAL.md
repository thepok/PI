# T47: the exact fixed-pi primitive off-diagonal sector

Status: `proof sketch`. The finite identities used from T16, T29, T31, and
T32 are machine-checked. The regrouping and elementary estimates written in
this note are inspectable finite arguments, but this note has not been
formalized in Lean.

## 1. Scope, source, and claim boundary

The canonical local problem has no external source URL. A byte-exact copy is
delivered as `CANONICAL_STATEMENT.txt`. Its SHA-256, checked in this session,
is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

That source asks for the all-scale ordered long-lag collision bound for the
decimal digits of `pi`. This note treats only the primitive, noncancelling
part of the off-diagonal contribution to T29's residual width-weighted square
function at the fixed phase `Real.pi`. It is therefore a result about sibling
A12 of the canonical statement, not the canonical collision count.

Fix real parameters `mu,c`, a natural onset `Q0`, and positive natural
numbers `m,N`. The intended C2 specialization fixes `(mu,c,Q0)` before `m,N`.
Nothing below permits these parameters to vary with a block, record,
frequency, or stratum.

The following possible ambiguities are resolved as follows.

1. Every record pair is ordered until T31's two-to-one orientation regrouping
   is applied explicitly.
2. Every canonical block is half-open. Its left endpoint is retained and its
   right endpoint is excluded.
3. The frequency set is exactly `1,...,10^m`; zero is absent and `10^m` is
   present.
4. "Primitive" means T16/T31 noncancelling for the signs `(+,+,-,-)`. It does
   not mean coprime to every prime.
5. The primitive contribution is signed. The terminal incidence expression
   controls its absolute value and hence its upper contribution.
6. The normalized exponent-`36/5` irrationality estimate in Section 8 is the
   explicit consequence of the source-pinned Zeilberger--Zudilin result
   recorded in `T47_SOURCE_PIN.md`. It is literature evidence, not derived
   from the four permitted kernel-checked files, and is used only to audit
   that method's strength.
7. No assertion of T29's all-scale predicate, C2, C1, or the canonical
   collision estimate is made.

## 2. Exact kernel-checked input

The only kernel-checked interfaces used are the following copies from the
accumulated library. Their SHA-256 values were checked in this session.

```text
T16FiniteWeightedGCD.lean
4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec

T29WidthWeightedSquareFunction.lean
2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358

T31CrossBlockAlmostEverywhere.lean
535a43fc06ac84d9b61760300c642fc05dbd797dc7cedb25f0ed30156bf10380

T32AllBlockFixedPiRange.lean
3bb7e8a1fc13a87dd6decba4edd7dd1aa4daef51233b585e2e48e81bb2e78fdc
```

The exact public interfaces used are:

1. T16: `ten_reduction`, `decimalFrequency_valuation_cases`,
   `tenValuation_lowDecimalCoefficient`, `Noncancelling`,
   `fourTokenSign`, and the primitive four-token domain.
2. T29: `inclusiveFrequencies`, `translatedCanonicalBlocks`, `widthWeight`,
   `blockSquaredEnergy`, and `widthWeightedSquareFunction`.
3. T31: `blockOrderedDomain`, `blockPositiveDifferenceDomain`,
   `blockDifferenceExponent`, `blockDifferenceValue`,
   `primitiveBlockDifferenceDomain`, `blockPositiveDifferenceValue_cast`,
   and `sum_blockOffDiagonal_eq_orient`.
4. T32: `blockRecordDomain`, `mem_blockRecordDomain_iff`,
   `blockRecordDomain_both_orientations`, `inclusiveDirichletKernel`,
   `blockSquaredEnergy_eq_diagonal_add_offDiagonal`, and
   `widthWeightedSquareFunction_eq_diagonal_add_offDiagonal`.

T31's almost-everywhere conclusion and weighted-GCD integral estimate are not
used as fixed-phase estimates. They supply finite definitions and
regroupings only.

## 3. Canonical blocks, records, signs, and weights

Put

```text
H = 10^m,
B_N = translatedCanonicalBlocks N
    = canonicalDyadicPartition N.                           (3.1)
```

The sum over `B in B_N` below means the finite list sum, with each canonical
block occurring once. A block `B` has

```text
B = [a,b),
b = a + 2^(B.level),
w(B) = sqrt(b^2-a^2) > 0.                                  (3.2)
```

For `B in B_N`, T29 gives `1<=a<b<=N`. The literal denominator in every
formula below is `w(B)`; it is never replaced by a block length or an
asymptotic equivalent.

An ordered record is

```text
q = (eps,(r,n)),
endpoint(q) = n+r,
F(q) = +10^n(10^r-1), if eps=true,
     = -10^n(10^r-1), if eps=false.                         (3.3)
```

T32's exact block record set is

```text
Q_B = {q:
         0<r,
         m<=r,
         not ArithmeticExcluded(mu,c,Q0,m,n,r),
         a<=n+r<b}.                                         (3.4)
```

Thus (3.4) retains the weak long-lag boundary `m<=r`, every arithmetic
exclusion, and both Bool orientations. T32's
`blockRecordDomain_both_orientations` says that `(false,(r,n))` and
`(true,(r,n))` satisfy exactly the same membership conditions and have
opposite nonzero frequencies.

T31 defines `blockOrderedDomain` by first imposing strict endpoint `<N` and
then filtering to `[a,b)`. For a canonical block, this is exactly `Q_B`:

```text
blockOrderedDomain(mu,c,Q0,m,N,B) = Q_B.                    (3.5)
```

Indeed, membership in either side exposes admissibility and `a<=endpoint<b`.
The T31 side additionally says `endpoint<N`, which follows from `b<=N`; the
T32 side implies the same inequality for the same reason. Hence no records
are added or lost when T31's positive-difference interfaces are used below.

## 4. Exact inclusive-frequency expansion

Write

```text
e(x) = exp(2*pi*i*x),
D_m(t) = sum_(h=1)^H e(h*t*pi).                             (4.1)
```

In T32 notation, for an integer `d`,

```text
D_m(d) = inclusiveDirichletKernel m d Real.pi.              (4.2)
```

The endpoint `h=H` is included and `h=0` is absent. In particular,
`D_m(0)=H`, not `H+1`.

For a canonical block, T32 gives the exact identity

```text
blockSquaredEnergy(mu,c,Q0,m,B,pi)
 = H*card(Q_B) + O_B,                                      (4.3)

O_B
 = sum_((q,r) in Q_B x Q_B; q!=r) D_m(F(r)-F(q)).           (4.4)
```

Both sides of (4.3) are written in `C` by T32. The left side and diagonal
are real, and the off-diagonal terms occur in conjugate pairs, so `O_B` is
real.

T31 selects exactly one member of each unordered off-diagonal pair by

```text
Delta_B = {(q_plus,q_minus) in Q_B x Q_B:
             F(q_minus)<F(q_plus)}.                         (4.5)
```

For `p=(q_plus,q_minus) in Delta_B`, let

```text
d(p) = F(q_plus)-F(q_minus) in Z_(>0).                      (4.6)
```

T31's `blockPositiveDifferenceValue_cast` identifies this positive integer
with `blockDifferenceValue p`. Its exact orientation theorem gives

```text
O_B = sum_(p in Delta_B) [D_m(-d(p)) + D_m(d(p))]
    = 2*sum_(p in Delta_B) Re D_m(d(p)).                    (4.7)
```

The factor two in the second line is exactly the two ordered orientations
`(q_plus,q_minus)` and `(q_minus,q_plus)`. There is no additional sign,
orientation, diagonal, or frequency factor.

## 5. The exact primitive noncancelling contribution

For `p=(q_plus,q_minus)`, T31's labeled exponent vector is

```text
a_0 = orderedFirst(q_plus),
a_1 = orderedSecond(q_minus),
a_2 = orderedSecond(q_plus),
a_3 = orderedFirst(q_minus),                                (5.1)
```

and its signs are exactly

```text
(+,+,-,-).                                                  (5.2)
```

Consequently

```text
d(p) = 10^(a_0) + 10^(a_1) - 10^(a_2) - 10^(a_3) > 0.     (5.3)
```

Every exponent lies in the half-open finite range `0<=a_i<N`. Equal
exponents among the two positive labels or among the two negative labels are
allowed. T16/T31 call `p` primitive precisely when no exponent carries both
a positive and a negative label. Define

```text
P_B = {p in Delta_B: Noncancelling(+,+,-,-; a(p))}.         (5.4)
```

The requested fixed-pi primitive off-diagonal contribution is therefore the
following completely explicit sub-sum of (4.7):

```text
O_prim(mu,c,Q0;m,N)
 = sum_(B in B_N) 1/w(B)
     * sum_(p in P_B) [D_m(-d(p)) + D_m(d(p))].             (5.5)
```

Formula (5.5), not a newly named unspecified remainder, is the exact T29
fixed-pi noncancelling off-diagonal contribution. The complementary part of
(4.7) is the cancelling sector, but no assertion about that sector is needed
to define or audit (5.5).

## 6. Primitive decimal strata

Fix `p in P_B` and put

```text
ell(p) = min{a_0,a_1,a_2,a_3}.                              (6.1)
```

At exponent `ell`, noncancellation says that all labels present there have
one sign. There are one or two such labels. Thus the generic signed lowest
coefficient is one of

```text
+1, +2, -1, -2.                                            (6.2)
```

The `+2` case is empty in the positive four-token domain. It would use both
positive labels at exponent `ell`; noncancellation would then put both
negative labels at exponent at least `ell+1`, making
`d<=2*10^ell-2*10^(ell+1)<0`. After excluding this empty case and factoring
out `10^ell`, positivity converts the two negative possibilities by borrowing
one ten:

```text
-1 + 10A' = 9 + 10(A'-1),
-2 + 10A' = 8 + 10(A'-1).                                 (6.3)
```

In a negative case positivity forces `A'>=1`. Thus there is a unique realized
residue

```text
rho(p) in {1,8,9}                                         (6.4)
```

and a natural `A(p)` such that

```text
d(p) = 10^(ell(p)) * (rho(p) + 10*A(p)).                   (6.5)
```

The complete generic correspondence, including the empty positive stratum,
is

```text
+1 -> 1,  +2 -> 2 (empty),  -2 -> 8,  -1 -> 9.            (6.6)
```

T16's `tenValuation_lowDecimalCoefficient` now gives

```text
tenValuation(d(p)) = ell(p),
10 does not divide rho(p)+10*A(p).                          (6.7)
```

For `0<=ell<N` and `rho in {1,2,8,9}`, define the finite stratum

```text
P_B(ell,rho) = {p in P_B: ell(p)=ell and rho(p)=rho}.       (6.8)
```

The sets in (6.8) are pairwise disjoint and their union over the four generic
residues and `ell<N` is exactly `P_B`; every `rho=2` summand is empty.

## 7. Complete inclusive frequency valuation audit

For every retained frequency `h in {1,...,H}`, T16 gives

```text
e(h) = tenValuation(h) <= m,
e(h)=m iff h=H,
e(h)<m or h=H.                                             (7.1)
```

Write T16's exact reduction as

```text
h = 10^(e(h))*u(h),  10 does not divide u(h).               (7.2)
```

There are two top-level cases.

1. Endpoint: `h=H`, `e(h)=m`, and `u(h)=1`.
2. Interior: `1<=h<H`, `0<=e(h)<m`, and `10` does not divide
   `u(h)`.

Base-ten valuation is not generally additive on the primitive factors. To
make the missing cases explicit, let `nu_2` and `nu_5` denote the ordinary
prime valuations of positive integers and put

```text
v(p) = rho(p)+10*A(p),
tau(h,p)
 = min(nu_2(u(h))+nu_2(v(p)),
       nu_5(u(h))+nu_5(v(p))).                              (7.3)
```

Then the exact product valuation is

```text
tenValuation(h*d(p)) = e(h)+ell(p)+tau(h,p).                (7.4)
```

The residue restriction makes the complete cases sharper than the generic
product split. In every stratum, `5` does not divide `v`.

1. If `rho in {1,9}`, then `v` is divisible by neither `2` nor `5`, so
   `tau=0` for every legal `u`.
2. The generic `rho=2` stratum is empty by Section 6.
3. If `rho=8`, then `2|v` and `5 not|v`. If `5 not|u`, the total
   `5`-valuation vanishes and `tau=0`.
4. If `rho=8` and `5|u`, then `10 not|u` forces `2 not|u`, and this is
   the unique positive cross-valuation case:

   ```text
   tau(h,p) = min(nu_5(u(h)),nu_2(v(p))) > 0.               (7.5)
   ```

5. At the inclusive endpoint `h=H`, `u=1`, so `tau=0` and
   `tenValuation(H*d(p))=m+ell(p)`.

These cases are exhaustive. The realizable primitive value `v=18`, obtained
from `10+10-1-1`, together with `u=5`, shows why silently replacing (7.4)
by `e+ell` would be false. The formally possible generic complementary case
`2|u,5|v` is empty here because `v mod 10` belongs to `{1,2,8,9}`.

Equations (5.5), (6.8), and (7.1) may therefore be expanded, without changing
any term, first over `(ell,rho)`, then over the endpoint/interior frequency
cases, and in the interior over `tau=0` and the unique positive cross-case
(7.5). This records every decimal valuation case while retaining the
literal inclusive frequency endpoint.

## 8. Dirichlet constant and the irrationality scaling obstruction

For a real `x`, write `||x||` for distance to the nearest integer. The finite
geometric-series identity and `|sin(pi*x)|>=2||x||` give, for every positive
integer `d`,

```text
|D_m(d)| <= min(H, 1/(2*||d*pi||)).                         (8.1)
```

The constant `1/2` is literal. Since `pi` is irrational and `d>0`, the
denominator is nonzero. Also `D_m(-d)=conj(D_m(d))`. Hence (5.5) gives

```text
|O_prim|
 <= 2 * sum_(B in B_N) 1/w(B)
          * sum_(p in P_B) min(H,1/(2*||d(p)*pi||)).        (8.2)
```

The external input is Doron Zeilberger and Wadim Zudilin, *The Irrationality
Measure of Pi is at most 7.103205334137...*, Moscow Journal of Combinatorics
and Number Theory 9 (2020), 407--419,
DOI <https://doi.org/10.2140/moscow.2020.9.407>. The delivered publisher PDF
`zeilberger-zudilin-moscow-2020-9-407.pdf` has SHA-256
`3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
Physical PDF page 2 (journal page 407) gives the quantified definition of
irrationality measure; physical PDF page 13 (journal page 418), under "World
record", bounds the irrationality measure of `pi` above by
`7.10320533413700172750577342281...`, strictly below `36/5=7.2`. Exact URLs,
locators, retained-file metadata, and replay instructions are recorded in
`T47_SOURCE_PIN.md` and `SOURCE_SHA256SUMS`.

For completeness, choose the positive gap between that upper bound and
`36/5` as epsilon in the source definition. There is therefore a positive
natural onset `Qstar` such that for every positive integer `d>=Qstar` and
every integer `p`,

```text
|pi-p/d| > d^(-36/5).                                      (8.0)
```

Taking `p` to be a nearest integer to `d*pi` and multiplying (8.0) by the
positive number `d` yields the normalized external estimate used below:

```text
for every positive integer d>=Qstar,
||d*pi|| >= d^(-31/5).                                     (IE)
```

Thus (IE) is a precise source-pinned consequence, not a premise silently
discharged by T16, T29, T31, or T32. The argument from this point is
conditional on the cited publication's result. Even granting (IE), (8.1)
supplies only

```text
|D_m(d)| <= min(H, d^(31/5)/2),  d>=Qstar.                 (8.3)
```

The failure is quantitative. For `p in P_B`, let

```text
k(p) = max{a_0,a_1,a_2,a_3}.                               (8.4)
```

First, `k` cannot be zero: then all four exponents would be zero, contradicting
noncancellation because both signs occur. Thus `k>=1`. Noncancellation and
positivity force a positive label at exponent `k`. Otherwise at most two
positive labels, each at exponent at most `k-1`, could not dominate a
negative `10^k`. The two negative labels are each at most `10^(k-1)`. Hence

```text
(4/5)*10^k <= d(p) <= 2*10^k.                              (8.5)
```

The lower coefficient is optimal uniformly in `k` for this elementary token
estimate: `10^k-2*10^(k-1)=(4/5)10^k`, and the unavoidable second positive
token changes this by only a lower-order amount. From (8.5), the nontrivial
cap in (8.3) obeys

```text
d(p)^(31/5)/2
 >= (1/2)*(4/5)^(31/5)*10^(31k/5)
 > (1/10)*10^(31k/5).                                     (8.6)
```

For the last strict inequality, since `0<4/5<1` and `31/5<7`,

```text
(1/2)*(4/5)^(31/5)
 > (1/2)*(4/5)^7
 = 8192/78125
 > 1/10.                                                    (8.7)
```

Consequently, for every primitive record satisfying the onset condition and
the explicit scale range

```text
d(p) >= Qstar,
5m <= 31k(p)-5,                                            (8.8)
```

the right side of (8.6) is at least `10^m=H`, and (8.3) reduces exactly to
the trivial bound `|D_m(d)|<=H`.

For onset-qualified records in the remaining strict-supercritical boundary
strip

```text
d(p) >= Qstar,
31k(p)-4 <= 5m < 31k(p),                                   (8.9)
```

put `g=31k-5m`, so `g in {1,2,3,4}`. Equations (8.6)-(8.7) show

```text
[d(p)^(31/5)/2]/H > (1/10)*10^(g/5) > 1/10.                (8.10)
```

Thus for every onset-qualified record satisfying `5m<31k`, the termwise
majorant produced by (IE) is never smaller than one tenth of the trivial
kernel bound; on the large subrange (8.8) it is exactly the trivial bound.
The sufficient height-only onset condition
`(4/5)*10^k>=Qstar` follows from (8.5). Records with `d<Qstar` receive no
estimate at all from (IE). Therefore this external irrationality estimate
cannot, term by term, provide a scale-decaying saving for the primitive
sector. It does not refute the desired aggregate bound; the calculation gives
an explicit scaling obstruction for this method within this proof sketch.

## 9. One narrower aggregate primitive-incidence inequality

The remaining input can be stated without naming an unspecified remainder.
Let `J_m` be the least natural `J` such that

```text
H <= 2^J.                                                   (9.1)
```

For `delta in (0,1/2]`, define disjoint shells with every endpoint fixed:

```text
S_0(m):       0 < delta <= H^(-1),

S_j(m): 2^(j-1)H^(-1) < delta
          <= min(2^j H^(-1),1/2),  1<=j<=J_m.              (9.2)
```

Shell zero is closed at `H^(-1)`. Every positive shell is open below and
closed above. The cap `1/2` is retained. Empty terminal shells are allowed.
These shells partition `(0,1/2]` exactly.

For `B in B_N`, `0<=ell<N`, `rho in {1,2,8,9}`, and `0<=j<=J_m`, define the
finite primitive incidence counts

```text
C_(B,ell,rho,j)
 = card{p in P_B(ell,rho): ||d(p)*pi|| lies in S_j(m)}.     (9.3)
```

Define the literal width-weighted aggregate

```text
I_prim(mu,c,Q0;m,N)
 = sum_(B in B_N) 1/w(B)
     * sum_(0<=ell<N) sum_(rho in {1,2,8,9})
         [C_(B,ell,rho,0)
          + sum_(j=1)^J_m 2^(-j) C_(B,ell,rho,j)].          (9.4)
```

This is an explicit incidence expression. Its finite domains are (3.4),
(4.5), (5.4), (6.8), and (9.2); its signs are (5.2); its two orientations
are already accounted for by (4.7); and its denominator is the literal
canonical width (3.2).

If `delta` lies in `S_0`, (8.1) is at most `H`. If it lies in `S_j` for
`j>=1`, then

```text
1/(2*delta) < H/2^j.                                       (9.5)
```

The disjoint primitive strata and shells therefore turn (8.2) into the
following finite domination derived in this proof sketch:

```text
|O_prim(mu,c,Q0;m,N)|
 <= 2*H*I_prim(mu,c,Q0;m,N).                               (9.6)
```

The factor `2` is solely the two ordered off-diagonal orientations. There is
no suppressed constant in (9.6).

The one terminal fixed-pi input isolated by this note is the following
`conjecture`.

```text
(API_prim)

For every fixed real mu,c, every fixed natural Q0, and every real s with
0<s<1, there exists C_(mu,c,Q0,s)>=0 such that for every natural m,N with
1<=m and 1<=N,

  I_prim(mu,c,Q0;m,N)
    <= C_(mu,c,Q0,s) * [N + N^2*10^(-s*m)].                (9.7)
```

This is strictly narrower in sector and structure than T29's premise: it
contains only primitive positive differences, no diagonal, no cancelling
forms, no complex phases, and no frequency sum. It is a sufficient
strengthening for this sector because it takes absolute values before
aggregation; it is not claimed equivalent to the signed primitive bound.

## 10. Audit and final verdict

The finite reconstruction checks the following data explicitly.

1. Domains: positive `m,N`; canonical list `B_N`; exact records (3.4);
   strict positive differences (4.5); primitive records (5.4); strata (6.8).
2. Orientations and signs: both Bool record orientations in (3.3)-(3.4), both
   off-diagonal pair orientations in (4.7), and signs `(+,+,-,-)` in (5.2).
3. Weights: the literal `sqrt(b^2-a^2)` in every block denominator.
4. Frequencies: exactly `1<=h<=10^m`, with the endpoint `h=10^m` retained.
5. Decimal cases: residues `1,2,8,9`; endpoint/interior frequency valuation;
   zero and the unique admissible positive cross-valuation in (7.3)-(7.5).
6. Constants and ranges: Dirichlet constant `1/2`, token constant `4/5`,
   obstruction constant `1/10`, onset `d>=Qstar`, range (8.8), and boundary
   strip (8.9).
7. Claim boundary: no extension of T32's full square-function range and no
   assertion of C2 or C1.
8. External source: DOI, publisher URL, exact retained PDF hash, physical and
   journal page locators, and the exponent conversion (8.0)--(IE) are all
   supplied in this artifact set.

The honest outcome is the explicit scaling obstruction (8.8)-(8.10), not a
full all-scale contribution bound: for onset-qualified records, the
normalized exponent-`36/5` estimate gives no termwise scale decay in the
fixed-pi supercritical primitive sector; below onset it gives no estimate.
The exact narrower aggregate primitive-incidence target, with all constants
displayed, is

```text
I_prim(mu,c,Q0;m,N)
  <= C_(mu,c,Q0,s) * [N + N^2*10^(-s*m)],

which, conditional on (9.7), the finite inequality (9.6) gives

|O_prim(mu,c,Q0;m,N)|
  <= 2*C_(mu,c,Q0,s)*10^m*[N + N^2*10^(-s*m)].             (FINAL)
```
