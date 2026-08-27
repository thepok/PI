# T87: exact start truncation and the distinct late-frequency obstruction

Status: **INSUFFICIENT**. This document is a `proof sketch` for the new
elementary derivations below. The named T61 and T86 declarations are
`machine-checked`; the Zeilberger--Zudilin input is quoted from the pinned
primary source with an exact locator. T60 and T83 were used only as unverified roadmaps.
No assertion from either note is a premise. No unconditional claim about pi,
C7, C2, C1, or positive decimal factor entropy is made.

## 1. Provenance, normalized target, and ambiguities

The canonical question is locally formulated and has no original external
source URL. Its byte-exact copy is delivered as
`pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6.
```

It asks whether one fixed `eta>0` gives
`p_pi(n)>=10^(eta*n)` for every sufficiently large `n`. T87 neither changes
nor resolves that question. It audits the start-truncation route to T61's
short-sector premise.

The following potentially ambiguous choices are fixed.

1. Natural-number division is used in `n/2` and `10^n/2`.
2. The letter `c` in T61 is the irrationality constant. It is specialized to
   `c_irr=1`. The new start-cutoff slope is denoted `kappa`.
3. "Optimized" means the unique linear slope whose cutoff contains every
   complete start column in the pinned arithmetic-exclusion wedge while adding
   no complete column already outside that wedge. This criterion is checked in
   Section 5.
4. Every strict range and the residual mask remain in force after splitting.
5. T61's route to C7 requires an eventual all-scale signed bound. An estimate
   on merely infinitely many scales is not silently substituted for it.
6. T86's grouped square is coefficient-space control. It is not interpreted
   as point-evaluation control at the fixed seed `pi`.

## 2. Imported checked boundary and pinned source

The proof uses the following checked declarations rather than recreating
their content.

| Item | Declaration | Exact role |
|---|---|---|
| T61 | `sampleLength`, `shortBandwidth` | `L_n=10^(n/2)` and `H_n=10^n/2` |
| T61 | `mem_residualShortRectangle_iff` | lag, start, strict endpoint, and residual mask |
| T61 | `vaalerCoefficient_explicit` | literal signed weight |
| T61 | `structuredVaalerMajorantTotal_eq_completeExpression` | zero mode plus signed sum |
| T61 | `strictCentralIndicator_endpoint_pos`, `_neg` | equality at both endpoints is excluded |
| T61 | `decimalCutoff_eq_centralRadius` | `10^(-n)=1/(2H_n)` |
| T61 | `strictResidualIncidenceCount_le_majorantTotal` | incidence-to-majorant inequality |
| T61 | `shortResidualPairCount_eq_two_mul_strictResidualIncidenceCount` | restores both orientations |
| T61 | `signedStructuredDenominatorPremise_iff_quantifiers` | one constant for every sufficiently large scale |
| T86 | `mem_residualTupleDomain_iff` | exact `(h,r,j)` tuple domain |
| T86 | `tupleFrequency_eq`, `tupleWeight_explicit` | frequency and signed weight |
| T86 | `normalized_frequency_grouping` | exact `2/L_n` grouping |
| T86 | `frequencyFiber_card_le` | at most `n(n-1)` tuples per frequency |
| T86 | `oneScaleEnergy_le_fiber_weight`, `oneScaleEnergy_lt` | fiberwise square bound |
| T86 | `finite_envelope_sum_lt`, `groupedSquare_lt_fortyTwo` | cumulative constant `<42` |

The imported files have SHA-256 values

```text
T61VaalerAnalytic.lean   61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993
T86GroupedSquareBound.lean 29106f3d3d96a0342a50571d3cd62f1d64d4dbd13b5c9c11f514e5993d45f87b
```

Zeilberger and Zudilin define the irrationality measure on printed p. 407 and
prove on printed p. 418, using Propositions 7--8, that

```text
mu(pi) <= 7.10320533413700172750577342281... < 7.104.
```

The source is D. Zeilberger and W. Zudilin, *The irrationality measure of pi
is at most 7.103205334137...*, Moscow Journal of Combinatorics and Number
Theory 9 (2020), 407--419,
<https://doi.org/10.2140/moscow.2020.9.407>. The delivered PDF has SHA-256

```text
3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5.
```

Taking the rational exponent strictly above the published bound gives

```text
mu=888/125,        lambda=mu-1=763/125,

there exists Q0>=2 such that, for every D>=Q0 and P in Z,
  D^(-888/125) < |pi-P/D|.                              (2.1)
```

Replacing the source onset by its maximum with 2 gives `Q0>=2`. The source
does not print a numerical `Q0`.

## 3. Complete T61 range-and-weight crosswalk

Fix `n>=1`, and put

```text
L_n=10^(floor(n/2)),       H_n=10^n/2,
q_(j,r)=10^j*(10^r-1).                                  (3.1)
```

For the specialization `(mu,c_irr)=(888/125,1)`, the exact residual label set
is

```text
R_n={ (r,j):
  0<r, r<n, r<L_n, 0<=j<L_n-r,
  not ArithmeticExcluded(888/125,1,Q0,n,j,r) }.         (3.2)
```

The `r<L_n` condition is explicit even when it follows from `r<n`. The start
endpoint `j=L_n-r` is excluded. T61's positive multiplier and literal signed
weight are

```text
1<=h<H_n,

a_n(h)=H_n^(-1)*[
  sin(pi*h/H_n)/pi
  +2*(1-h/H_n)*cos(pi*h/H_n)].                          (3.3)
```

The endpoint `h=H_n` is excluded. The weight is not replaced by its absolute
value in the signed expression. T61 machine-checks one sign-transition ratio
in `(1/2,1)`; both signs are therefore retained here.

Writing `d_n=|R_n|`, the complete checked finite expression is

```text
Z_n=2*d_n/H_n,

S_n(x)=2*sum_(1<=h<H_n) a_n(h)
          *sum_((r,j) in R_n) cos(2*pi*h*q_(j,r)*x),

E_n(x)=Z_n+S_n(x).                                     (3.4)
```

At the fixed seed `x=pi`, the first `pi` in the cosine is the angular
constant and the final `pi` is the seed. The strict near-return radius is

```text
circleDistance(q_(j,r)*pi)<1/(2H_n)=10^(-n).           (3.5)
```

At both equality endpoints `+/-1/(2H_n)`, T61's strict indicator is zero and
the majorant equals one. Replacing `<` by `<=` would change the incidence
problem by adding equality cases, so no such replacement is made. T61 proves

```text
strictResidualIncidenceCount_n <= E_n(pi),
shortResidualPairCount_n=2*strictResidualIncidenceCount_n. (3.6)
```

The normalization relevant to the missing premise is exactly `E_n(pi)/L_n`.

For `(h,(r,j))`, T86 uses exactly

```text
Phi(h,r,j)=h*10^j*(10^r-1),
weight(h,r,j)=a_n(h),

B_n(q)=(2/L_n)*sum_(Phi(h,r,j)=q) a_n(h).               (3.7)
```

Frequency zero is absent from (3.7); `Z_n` remains separate. T86's grouping
identity is

```text
S_n(x)/L_n=sum_q B_n(q)*cos(2*pi*q*x).                  (3.8)
```

Every occurrence of `2/L_n` in what follows includes T61's outer factor two.

## 4. Exact consequence of the pinned irrationality estimate

For a positive integer `D>=Q0`, choosing a nearest integer `P` in (2.1)
gives

```text
||D*pi||_T > D^(-763/125).                              (4.1)
```

T61's arithmetic mask is defined by

```text
ArithmeticExcluded iff
  Q0<=q_(j,r) and 10^(-n)<=q_(j,r)^(-763/125).          (4.2)
```

All quantities are positive, so (4.2) is equivalently

```text
Q0<=q_(j,r) and q_(j,r)^763<=10^(125*n).                (4.3)
```

Equality belongs to the excluded side because the near return is strict.
Consequently the exact residual mask is

```text
q_(j,r)<Q0 or q_(j,r)^763>10^(125*n).                   (4.4)
```

This is the strongest uniform yes/no exclusion supplied by (2.1); no reduced
fraction assumption is used.

Define

```text
A_n=floor(125*n/763),       beta_n=125*n-763*A_n,
0<=beta_n<=762.                                          (4.5)
```

If `s=j+r`, then

```text
q_(j,r)=10^s*(1-10^(-r))<10^s.                          (4.6)
```

It follows immediately that every label with `j+r<=A_n` satisfies the power
comparison in (4.3). If `j+r>=A_n+2`, then

```text
q_(j,r)>=9*10^(A_n+1),
q_(j,r)^763>10^(763*A_n+762)>=10^(125*n),               (4.7)
```

so it fails that comparison. Only `j+r=A_n+1` is a boundary. Exact integer
comparison gives the complete boundary list:

```text
(r,j)=(1,A_n)     is power-eligible iff beta_n>=729;
(r,j)=(2,A_n-1)   is power-eligible iff A_n>=1 and beta_n>=760;
no r>=3 boundary label is power-eligible.               (4.8)
```

Indeed

```text
10^728 < 9^763 < 10^729,
10^(763+759) < 99^763 < 10^(763+760),
999^763 > 10^(2*763+762).                               (4.9)
```

For `r>=3`, the factor `1-10^(-r)` only increases. Equations (4.5)--(4.9)
therefore classify every label, not merely an asymptotic subset.

## 5. Optimized start cutoff and exact masked split

Set

```text
kappa_*=125/763,             J_n=floor(kappa_* n)=A_n.  (5.1)
```

Split the exact residual set, without changing its mask, by

```text
R_n^early={(r,j) in R_n:j<J_n},
R_n^late ={(r,j) in R_n:j>=J_n}.                        (5.2)
```

This cutoff is optimized in the following literal sense. Every complete start
column `j<A_n` contains some power-eligible labels, and all labels in the main
wedge `j+r<=A_n` lie in those columns. The next column `j=A_n` is already
outside the main wedge and contains only the exceptional boundary label
`(r,j)=(1,A_n)` for some residue classes of `n`. Thus (5.1) captures every
complete eligible column and adds no complete already-uncontrolled column.
Any smaller fixed slope eventually leaves a complete eligible column in the
late set; any larger fixed slope eventually adds complete uncontrolled
columns to the early set. The isolated first boundary pair could be captured
by `J_n=A_n+1`, but no cutoff of the required exact form
`floor(kappa*n)` realizes that additive correction without eventually adding
linearly many further starts. This proves the asserted optimum criterion.

For `n>=2`, the elementary inequality `L_n>=2*n` gives
`L_n-r>A_n` for every `1<=r<n`. Hence the unmasked early rectangle has exactly
`A_n(n-1)` labels. Put

```text
P_n(Q0)=|{(r,j):
  1<=r<n, 0<=j<A_n,
  q_(j,r)<Q0, q_(j,r)^763<=10^(125*n)}|.                (5.3)
```

The eligible main wedge contains `A_n(A_n+1)/2` early labels. The second
boundary pair in (4.8) is early; the first is late. Therefore the exact masked
early cardinality is

```text
d_n^early=|R_n^early|
 =A_n(n-1)-A_n(A_n+1)/2
  -1_(A_n>=1 and beta_n>=760)+P_n(Q0).                 (5.4)
```

The labels counted by `P_n(Q0)` are restored because the onset conjunct in
(4.3) fails. There are only finitely many positive `(r,j)` with `q_(j,r)<Q0`;
in particular `P_n(Q0)<=Q0^2`. Thus

```text
d_n^early
 =(175125/1164338)*n^2+O(n+Q0^2),                      (5.5)
d_n^early<=A_n(n-1)<=125*n^2/763.                      (5.6)
```

The unmasked late rectangle has exactly

```text
R_n^late=(n-1)(L_n-A_n)-n(n-1)/2.                      (5.7)
```

Only the first boundary pair in (4.8) can be arithmetically excluded there.
Consequently

```text
d_n^late=|R_n^late|
 =R_n^late
  -1_(beta_n>=729 and Q0<=9*10^A_n),                   (5.8)

d_n^late/L_n=n-1-O(n^2/L_n).                           (5.9)
```

The cutoff therefore removes a polynomial number of residual labels from an
order-`n*L_n` residual rectangle. It does not shrink the late label count by a
fixed proportion.

## 6. Early-start contribution is discharged

From (3.3), `pi>3`, and `|sin|,|cos|<=1`,

```text
sum_(1<=h<H_n)|a_n(h)|
 <sum_(1<=h<H_n) H_n^(-1)*[1/3+2*(1-h/H_n)]
 =4(H_n-1)/(3H_n)<4/3.                                 (6.1)
```

Let `S_n^early` be (3.4) restricted to `R_n^early`. Retaining every sign and
then applying the triangle inequality only for this estimate gives

```text
|S_n^early(pi)|/L_n
 <(8/3)*d_n^early/L_n
 <=(1000/2289)*n^2/L_n.                                (6.2)
```

The right side tends exponentially to zero. Thus the complete early-start
sector is uniformly harmless after the exact `L_n` normalization. The pinned
irrationality estimate sharpens its exact masked cardinality through (5.4),
but cardinality alone already makes every fixed-linear start strip `o(1)`
after division by `L_n`.

The normalized zero mode is also harmless:

```text
0<=Z_n/L_n=2*d_n/(H_n*L_n)<=2(n-1)/H_n.                (6.3)
```

## 7. Masked late-start T86 grouping

Define the exact late tuple set

```text
Omega_n^late={ (h,(r,j)):
  1<=h<H_n, (r,j) in R_n, j>=A_n }.                    (7.1)
```

For a positive integer frequency `q`, define

```text
B_n^late(q)=(2/L_n)*
  sum_(a in Omega_n^late, Phi(a)=q) a_n(a.h),           (7.2)

Q_n^late={q:the fiber in (7.2) is nonempty}.           (7.3)
```

This is T86's literal signed weight, residual mask, strict frequency range,
and `2/L_n` normalization, intersected only with `j>=A_n`. Its exact grouping
is

```text
S_n^late(x)/L_n=sum_(q in Q_n^late)
  B_n^late(q)*cos(2*pi*q*x).                            (7.4)
```

Here is the subset-stable reproof of the bounds needed below.

1. T86's frequency code `(r,j mod n)` is injective on each full frequency
   fiber. It remains injective after tuple deletion. Hence every late fiber
   has cardinality at most `n(n-1)`.
2. T86 proves `|a_n(h)|<3/H_n` on every legal tuple. This remains true on the
   late subset.
3. The late tuple set is contained in the full set, whose cardinality is at
   most `(H_n-1)(n-1)L_n`.
4. Fiberwise Cauchy--Schwarz therefore gives

```text
sum_q |B_n^late(q)|^2
 <=(4/L_n^2)*n(n-1)*sum_(a in Omega_n^late)|a_n(a.h)|^2
 <36*n^3/(H_n*L_n).                                   (7.5)
```

5. Replacing every `a_n(h)` by `|a_n(h)|` leaves all three preceding bounds
   unchanged. Denote the resulting nonnegative grouped coefficient by
   `B_n^abs(q)`.
6. T86's decimal-power comparison turns the right side of (7.5) into the
   square of `24*n^2/5^n`. Minkowski and the same exact telescope give, for
   every finite set of scales `I`,

```text
sum_q [sum_(n in I) B_n^abs(q)]^2
 <(sum_(n>=2)24*n^2/5^n)^2
 =(129/20)^2<42.                                       (7.6)
```

This is a reapplication of T86's checked argument to a subset, not a claim
that its existing theorem statement literally quantifies over arbitrary
subsets.

To separate duplicates, let a block record be
`alpha=(n,h,r,j)` with `n in I`, `(h,(r,j)) in Omega_n^late`, and set

```text
m_alpha=Phi(h,r,j),       b_alpha=2*a_n(h)/L_n.         (7.7)
```

Ordered record pairs split disjointly into:

```text
LIT: (h,r,j)=(h',r',j') (the scales may differ);
EQ:  (h,r,j)!=(h',r',j') but m_alpha=m_beta;
DIST:m_alpha!=m_beta.                                  (7.8)
```

The combined absolute mass of `LIT` and `EQ` is

```text
sum_q (sum_(alpha:m_alpha=q)|b_alpha|)^2<42            (7.9)
```

by (7.6). Since `LIT` and `EQ` are disjoint subcollections of nonnegative
absolute pair weights, each class separately has absolute mass `<42`.
Therefore literal duplicates and nonliteral exact frequency coincidences are
fully controlled, uniformly over every finite scale set. No injectivity of
`Phi` was assumed.

What remains at `x=pi` consists only of pairs in `DIST`. T86 does not control
those pairs: evaluation at one point is not a uniformly bounded functional on
coefficient `ell^2` as the finite support grows.

## 8. Explicit insufficiency calculation

Without distinct-frequency cancellation, (6.1), (5.8), and (7.4) give only

```text
|S_n^late(pi)|/L_n
 <(8/3)*d_n^late/L_n
 =(8/3)(n-1)+O(n^2/L_n).                               (8.1)
```

The exact remaining normalization loss is therefore linear in `n`; it is not
a fixed T61 constant.

Ordinary spacing does much worse. The largest frequency in the complete late
rectangle is bounded by

```text
M_n=(H_n-1)*10^(L_n-n)*(10^(n-1)-1),                   (8.2)

log10(M_n)=L_n+n-1-log10(2)
 +log10(1-2*10^(-n))+log10(1-10^(-(n-1))).             (8.3)
```

After absorbing the finitely many differences below `Q0` into a positive
nonnumerical constant, (4.1) bounds distinct phase spacing only by
`M_n^(-763/125)`. A one-row spacing relaxation consequently loses

```text
M_n^(763/125),                                          (8.4)

Lambda_spacing(n)=(763/125)*[
 L_n+n-1-log10(2)
 +log10(1-2*10^(-n))+log10(1-10^(-(n-1)))].            (8.5)
```

Its leading base-ten exponent is `(763/125)*L_n`. The optimized linear start
cutoff does not alter this leading term because the maximal starts remain in
the late set. Thus neither (8.1) nor the pinned spacing estimate supplies a
constant normalized bound.

## 9. Exactly one residual covariance premise

The remaining obstruction can be stated without including any duplicate
frequency. Define the ordered distinct late-frequency covariance

```text
Cov_n^late,dist(pi)=
 sum_(q,q' in Q_n^late, q!=q')
   B_n^late(q)*B_n^late(q')
   *cos(2*pi*q*pi)*cos(2*pi*q'*pi).                     (9.1)
```

Equivalently, each product of cosines in (9.1) is one half the sum of the
difference and sum phases

```text
cos(2*pi*(q-q')*pi)+cos(2*pi*(q+q')*pi).                (9.2)
```

All residual masks and all signed Vaaler weights remain inside the grouped
coefficients. The **single unproved residual covariance premise** is

```text
(Cov_pi^late,dist)
there exist a real C>0 and an integer N0>=2 such that, for every n>=N0,
  |Cov_n^late,dist(pi)|<=C.                             (9.3)
```

This is fully quantified and concerns only distinct late-start frequencies.
It does not include literal duplicates, nonliteral equal frequencies, the
early sector, or the zero mode.

For calibration, (7.5), (7.4), and (9.3) would give

```text
|S_n^late(pi)/L_n|^2
 <=sum_q|B_n^late(q)|^2+|Cov_n^late,dist(pi)|
 <36*n^3/(H_n*L_n)+C.                                  (9.4)
```

Together with (6.2)--(6.3), this would imply, for every sufficiently large
`n`,

```text
E_n(pi)/L_n<=sqrt(C+1)+1.                               (9.5)
```

Thus it would give T61's signed premise with the displayed fixed constant,
and (3.6) would give

```text
shortResidualPairCount_n<=2*(sqrt(C+1)+1)*L_n.         (9.6)
```

This is stronger than obtaining infinitely many good scales: it supplies the
eventual all-scale quantifier actually required by T61. Conditional also on
the separately retained long-sector premise
`SparseLongResidualLinearBound(888/125,1,Q0)`, the existing machine-checked
T61-to-T56-to-C7-to-C2-to-C1 chain would then apply. The long-sector premise
and (9.3) are unproved. This paragraph is only a constant-preserving
implication and asserts none of C7, C2, or C1.

## 10. Verdict

**INSUFFICIENT.** The exact optimized cutoff is `J_n=floor(125*n/763)`.
The source-pinned estimate completely classifies its arithmetic wedge, but the
remaining early residual contribution is small only because it has `O(n^2)`
labels against `L_n=10^(floor(n/2))`. The late mask still has
`(n-1)L_n-O(n^2)` labels.

The subset-stable T86 argument bounds the absolute contribution of every
literal duplicate and every nonliteral equal-frequency collision by the
uniform grouped-square constant `<42`. At fixed `pi`, it says nothing about
distinct frequencies. The direct estimate retains the exact linear loss
(8.1), while the pinned spacing relaxation incurs the exponent (8.5), led by
`(763/125)L_n`.

Accordingly the recorded start-truncation lead closes at exactly one frontier:
the distinct late-start fixed-pi covariance (9.3). No claim has been upgraded
beyond its verification level.

## 11. Replay

From a directory containing only the delivered artifacts, run

```sh
sh ./verify.sh
```

The dependency-free replay verifies all delivered hashes and source anchors,
the exact integer thresholds in (4.8)--(4.9), the cutoff identity, finite
instances of the complete arithmetic classification, the early/late count
formulas, and T86's rational telescope and `<42` constant. Finite checks are
`experiment` evidence only; the universal derivations are displayed above.
