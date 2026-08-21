# T61: unmatched-defect coefficient mass has an unbounded target ratio

Status: `proof sketch`. The T29, T56, T59, and T60 interfaces cited below are
`machine-checked`. The new explicit family, coefficient-mass identity, and
unbounded-ratio deduction are proved in this note and have not been formalized
in Lean.

## 1. Source, scope, and normalized claim

The canonical local question has no external source URL. Its original source is
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`. A byte-exact copy is
delivered as `CANONICAL_STATEMENT.txt`, with SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question asks whether, for every real `s` with `0<s<1`, one
constant `C_s>=1` controls the ordered long-lag decimal collision count for all
positive `m,N`:

```text
R_pi(m,N) <= C_s * (N + N^2*10^(-s*m)).                    (1.1)
```

T61 does not prove or refute (1.1). It concerns only the residual sparse-Fourier
sibling A12 and, more narrowly, the phase-uniform coefficient-envelope route
for T59's unmatched defect.

All quantifiers used below are explicit:

```text
t is any natural number;              L=2^t;
m=1;                                  N=4L+1;
Q0=0 in T60's D_t;                    0<s<1;
A>=0 is any proposed scale-uniform target constant.         (1.2)
```

The possible ambiguities are resolved as follows. The canonical block is
half-open, frequencies include both endpoints `1` and `10`, both Boolean phase
orientations are retained, coefficients are not deduplicated before summing,
and the denominator is the literal T29 width rather than block length. The
conclusion is not a statement about the value at `pi`, C2, C1, or (1.1).

## 2. Kernel-checked inputs

This note imports the following accepted modules as kernel-checked inputs; it
does not restate their proofs:

```text
TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
TheoryLib.PiLongLagBlockCollisionDecay.T56T56SignedPrimitiveResiduePairing
TheoryLib.PiLongLagBlockCollisionDecay.T59T59CompleteSignedPrimitivePartition
TheoryLib.PiLongLagBlockCollisionDecay.T60T60DefectLaurentPolynomial
```

The exact source hashes inspected for this build are

```text
T29WidthWeightedSquareFunction.lean
  2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358
T56SignedPrimitiveResiduePairing.lean
  18410d564deeaa07bd047699b7ca7e58dd7c685d866df0cd42951c664f3ffd95
T59CompleteSignedPrimitivePartition.lean
  efe26ea7141201081bcaa32d33dfb71688e643ea1a4630ff7beeaf69e47b765c
T60DefectLaurentPolynomial.lean
  6ca5c81dd9f367656f3e653e3afa3c07909702e2c4502a0c81fc122309397f86
```

The interfaces used are:

1. T56 `translatedCanonicalBlocks_boxEndpoint`, `boxBlock_endpoints`,
   `boxWidth_literal`, `boxWidth_pos`, `boxInclusiveFrequencies`,
   `mem_boxQuartetDomain_iff`, `boxQuartet_ordered`,
   `coordinateRecord_audit`, `coordinateRecord_eq_iff`,
   `boxQuartetDomain_card`, and the two exact ambient-fiber theorems
   `residueOne_ambientPrimitiveValueFiber_iff` and
   `residueNine_ambientPrimitiveValueFiber_iff`.
2. T59 `mem_unmatchedDefect_iff`, which retains the complete primitive record
   domain and excludes every literal residue-one and residue-nine selected
   value.
3. T60 `admissible_eight_one_one_iff`,
   `mem_defectCharacterDomain_iff`, `defectCharacterExponent_eq`,
   `defectCharacter_mem_exact_T59_fiber`,
   `defectCoefficient_eq_filter_sum`, and
   `defectLaurent_independent_Q0`.
4. T29 `widthWeightedSquareFunctionAt_iff_quantifiers`, together with T12's
   definition of `scaleMatchedTarget`.

The T52 note is unverified and is not a premise anywhere below.

## 3. Exact scale, block, and width

Put

```text
L=2^t,       N=4L+1,       B_t=boxBlock(t)=[1,N).           (3.1)
```

T56 proves that T29's complete canonical block list at this `N` is the
singleton `[B_t]`; this is not merely a block selected from a longer list. Its
literal width is

```text
w_t = widthWeight(B_t)
    = sqrt(N^2-1)
    = sqrt(16L^2+8L) > 0.                                  (3.2)
```

In particular,

```text
w_t < N,                                                     (3.3)
```

because both sides are positive and `w_t^2=N^2-1<N^2`.

## 4. Every coefficient fiber

Write

```text
U_t = unmatchedDefect(0,t).                                 (4.1)
```

This is T59's literal finite difference inside

```text
primitiveRecordDomain 8 1 0 1 N B_t.
```

For `p in U_t`, let `d(p)=blockDifferenceValue(p)`. Positivity of the
primitive domain gives `d(p)>0`. For a Boolean orientation define

```text
epsilon(false)=+1,       epsilon(true)=-1.                  (4.2)
```

T60's complete labeled character domain is exactly

```text
X_t = { (p,b,h) : p in U_t, b in Bool, 1<=h<=10 }.          (4.3)
```

There is no image or quotient in (4.3). Thus repeated exponents remain
separate labeled terms. The exact exponent of `x=(p,b,h)` is, by T60
`defectCharacterExponent_eq`,

```text
e_t(p,b,h) = epsilon(b) * h * d(p) in Z.                    (4.4)
```

For every integer `n`, define the complete coefficient fiber and its size by

```text
F_t(n) = { (p,b,h) in X_t : e_t(p,b,h)=n },
k_t(n) = |F_t(n)|.                                          (4.5)
```

Equations (4.1)-(4.5) retain every T59 domain condition, valuation and value
implicitly through the literal record `p`, its two record Booleans through
`p`, the extra phase orientation `b`, its sign, and every inclusive frequency.
If desired, T60 `defectCharacter_mem_exact_T59_fiber` places each labeled term
in the unique displayed valuation-value-record-orientation fiber indexed by

```text
(tenValuation(d(p)), d(p), recordOrientation(p)).           (4.6)
```

T60 defines `D_t=defectLaurent(0,t)` and `a_t(n)=D_t(n)`. Its kernel-checked
filter-sum formula gives the exact coefficient, not an estimate:

```text
a_t(n) = sum_(x in F_t(n)) 1/w_t = k_t(n)/w_t.              (4.7)
```

The orientation sign in (4.4) changes the Laurent exponent, not the scalar
coefficient. Every scalar summand in (4.7) is the same positive number
`1/w_t`. Consequently exponent collisions only add:

```text
a_t(n)>=0,       |a_t(n)|=a_t(n).                           (4.8)
```

For each fixed `p` there are exactly two orientations and exactly ten
frequencies. The fibers (4.5) are pairwise disjoint and exhaust (4.3), so

```text
sum_n k_t(n) = |X_t| = 2*10*|U_t| = 20|U_t|.               (4.9)
```

All sums over `n` mean the finite support of `D_t`. From (4.7)-(4.9), the
requested coefficient mass has the exact identity

```text
M_t := sum_n |a_t(n)| = 20|U_t|/w_t,                        (4.10)
w_t M_t = 20|U_t|.                                          (4.11)
```

This proves the coefficient accounting independently of whether different
records or frequencies produce the same integer exponent.

## 5. An explicit `L^4` unmatched family

Partition the coordinates into T56's four inclusive intervals

```text
I1=[1,L],          I2=[L+1,2L],
I3=[2L+1,3L],      I4=[3L+1,4L].                            (5.1)
```

For every `x=(x1,x2,x3,x4)` in `I1 x I2 x I3 x I4`, define

```text
q_+(x) = coordinateRecord(x4,x2),
q_-(x) = coordinateRecord(x1,x3),
P(x)   = (q_+(x),q_-(x)).                                   (5.2)
```

The intervals give

```text
1<=x1<x2<x3<x4<=4L<N.                                      (5.3)
```

### 5.1 Complete primitive-domain audit

Because `x2<x4` and `x1<x3`, the literal records in (5.2) are

```text
q_+(x) = (true,  (x4-x2,x2)),
q_-(x) = (false, (x3-x1,x1)).                               (5.4)
```

Their lags satisfy

```text
x4-x2 >= L+1 >= 1,       x3-x1 >= L+1 >= 1.                (5.5)
```

T60 `admissible_eight_one_one_iff` therefore supplies every arithmetic
admissibility condition at `(mu,c,Q0,m)=(8,1,0,1)`. Their frequency endpoints
are respectively `x4` and `x3`, so (5.3) puts both in the exact half-open block
`[1,N)` and below the global strict cutoff `N`.

T56 `coordinateRecord_audit` gives

```text
signedDecimalFrequency(q_+) = 10^x4-10^x2 > 0,
signedDecimalFrequency(q_-) = 10^x1-10^x3 < 0.              (5.6)
```

Hence T31's required strict orientation
`signedDecimalFrequency(q_-) < signedDecimalFrequency(q_+)` holds, and

```text
d(P(x)) = 10^x4+10^x3-10^x2-10^x1 > 0.                    (5.7)
```

By the literal definition of `blockDifferenceExponent`, its four entries are

```text
[x4,x3,x2,x1] with signs (+,+,-,-).                         (5.8)
```

All entries are distinct by (5.3), so no exponent carries opposite signs.
Thus `Noncancelling fourTokenSign` holds. Equations (5.4)-(5.8) verify every
condition in the exact T49/T59 primitive record domain:

```text
P(x) in primitiveRecordDomain 8 1 0 1 N B_t.                (5.9)
```

### 5.2 Exclusion from every selected value fiber

Let `y=(y1,y2,y3,y4)` be any member of `boxQuartetDomain(t)`. Suppose first
that

```text
d(P(x)) = residueOneValue(y).                               (5.10)
```

By (5.9) and T56 `residueOne_ambientPrimitiveValueFiber_iff`, (5.10) would
force `P(x)=residueOnePair(y,row)` for one of the four rows. T56's literal row
definitions and `coordinateRecord_eq_iff` give the following contradictions:

```text
row00: x1=y3, impossible because I1 and I3 are disjoint;
row01: x2=y3, impossible because I2 and I3 are disjoint;
row10: x4=y1, impossible because I4 and I1 are disjoint;
row11: x4=y1, impossible because I4 and I1 are disjoint.    (5.11)
```

Thus (5.10) is impossible. If instead

```text
d(P(x)) = residueNineValue(y),                              (5.12)
```

T56 `residueNine_ambientPrimitiveValueFiber_iff` similarly forces one of its
four literal rows, with contradictions

```text
row00: x2=y1, impossible because I2 and I1 are disjoint;
row01: x2=y3, impossible because I2 and I3 are disjoint;
row10: x4=y2, impossible because I4 and I2 are disjoint;
row11: x4=y2, impossible because I4 and I2 are disjoint.    (5.13)
```

Since `y` was arbitrary, (5.9), (5.11), and (5.13) are exactly the two sides
of T59 `mem_unmatchedDefect_iff`. Therefore

```text
P(x) in U_t.                                                 (5.14)
```

This step uses the kernel-checked ambient-fiber classifications, not the T52
note and not a residue heuristic.

### 5.3 Injectivity and count

If `P(x)=P(y)`, equality of the first records and
`coordinateRecord_eq_iff` recovers `x4=y4` and `x2=y2`; equality of the second
records recovers `x1=y1` and `x3=y3`. Hence `x=y`, so `P` is injective.

T56 `boxQuartetDomain_card` proves that the Cartesian box in (5.1) has exactly
`L^4` members. Therefore (5.14) gives, for every `t>=0`,

```text
|U_t| >= L^4 = 2^(4t).                                      (5.15)
```

Combining (4.10), (4.11), and (5.15) yields

```text
M_t >= 20L^4/w_t,          w_t M_t >= 20L^4.               (5.16)
```

## 6. Exact T29 comparison and unbounded ratio

T12 defines

```text
scaleMatchedTarget(s,m,N) = N + N^2*10^(-s*m).
```

At the exact T61 scales, put

```text
T_s(t) = (4L+1) + (4L+1)^2*10^(-s).                        (6.1)
```

The decimal frequency count at `m=1` is exactly ten. Because T56 proves that
`B_t` is the sole canonical block, T29's fixed-constant target specializes to

```text
blockSquaredEnergy(8,1,0,1,B_t,alpha)/w_t
  <= 10 A T_s(t).                                           (6.2)
```

The coefficient mass `M_t` also includes the same literal factor `1/w_t`.
The independently imposed phase-uniform coefficient-envelope bound at T29's
specialized right-hand-side scale is therefore

```text
M_t <= 10 A T_s(t).                                         (6.3)
```

Restoring, rather than dropping, the width multiplies both sides:

```text
w_t M_t <= 10 A w_t T_s(t).                                (6.4)
```

Accordingly the normalized ratios in (6.3) and (6.4) are identical. Comparing
`w_t M_t` directly with `10 A T_s(t)` would be an incorrect normalization.
Equation (6.3) is not a clause of T29 and does not follow from (6.2): T29 bounds
the complete nonnegative block energy, whereas `D_t` is one signed primitive
component and can cancel internally and against other centered components.
The point of (6.3) is only that it is a sufficient phase-uniform envelope at
the exact T29 scale.

For `0<s<1`, one has `10^(-s)<1`. Also `N>=5`, `N<=N^2`, (3.3) holds, and
`N=4L+1<=5L`. Therefore (5.16) gives the explicit chain

```text
M_t/(10 T_s(t))
  > (20L^4/N)/(20N^2)
  = L^4/N^3
  >= L/125
  = 2^t/125.                                                (6.5)
```

Here the first strict inequality uses both `w_t<N` and
`10T_s(t)<10(N+N^2)<=20N^2`; the last inequality uses `N<=5L`.

Thus the normalized coefficient-envelope ratio is unbounded on the explicit
infinite family `t=0,1,2,...`. More quantitatively, for every `A>=0`, choose
`t` with

```text
2^t > 125 A.                                                (6.6)
```

Then (6.5) proves

```text
M_t > 10 A ((4*2^t+1)+(4*2^t+1)^2*10^(-s)).                (6.7)
```

Consequently no constant `A` can make the phase-uniform coefficient-mass
bound (6.3) hold at all dyadic one-block scales.

## 7. What this does and does not prove

For a nonzero complex number `z`, define the Laurent evaluation explicitly by

```text
Eval_z(D_t) = sum_(n in support(D_t)) a_t(n) z^n,            (7.1)
```

where `z^n` is the integer power, including negative `n`. If `|z|=1`, then
`|z^n|=1`, so (4.8) and the finite triangle inequality give

```text
|Eval_z(D_t)| <= sum_n |a_t(n)| = M_t.                      (7.2)
```

The fixed-phase crosswalk can be checked directly from (4.3)-(4.4). Set

```text
z_alpha = exp(2*pi*i*alpha).
```

For each `p,h`, summing the two Boolean orientations gives

```text
z_alpha^(h*d(p)) + z_alpha^(-h*d(p))
  = 2*cos(2*pi*alpha*h*d(p)).                               (7.3)
```

Thus at `alpha=pi`, (7.1) equals the literal T59 unmatched-defect term

```text
(2/w_t) * sum_(p in U_t) sum_(h=1)^10
  cos(2*pi^2*h*d(p)),                                       (7.4)
```

including its factor `2`, width, and inclusive frequencies. This is also the
term displayed by T59 `defect_signed_regrouping` before its
valuation-value-record-orientation regrouping.

An unbounded upper envelope does not imply that `|Eval_z(D_t)|` is large at
any particular `z`. In particular, (6.7) proves only that genuine phase
cancellation is necessary if the T59 unmatched defect is to satisfy the T29
target at the fixed phase `pi`. It does not prove that such cancellation fails,
nor does it rule out cancellation between this defect and other centered
components.

Therefore T61 refutes only this phase-uniform sufficient route. It does not
refute the defect value at `pi`, T29's width-weighted square-function predicate
C2, the collision conjecture C1, or the canonical ordered long-lag estimate
(1.1). No finite computation is used as evidence for the universal conclusion.

## 8. Skeptic checklist

1. Source: `CANONICAL_STATEMENT.txt` is byte-exact and its hash is displayed.
2. Range: every natural `t`, `L=2^t`, `m=1`, and `N=4L+1` are explicit.
3. Block: the complete canonical partition is the singleton half-open block
   `[1,N)`.
4. Width: `w_t=sqrt(N^2-1)`, and it is retained on both sides of (6.4).
5. Domain: (5.4)-(5.9) audit both records, lags, endpoints, strict orientation,
   arithmetic admissibility, signs, and noncancellation.
6. Defect: (5.10)-(5.14) exclude every row of both complete selected ambient
   value fibers.
7. Frequencies and orientations: (4.2)-(4.5) retain both Boolean orientations
   and every integer frequency from `1` through `10`, inclusively.
8. Coefficients: (4.5)-(4.9) display every exact exponent fiber and explain why
   collisions add rather than cancel.
9. Count: injectivity and T56's exact box cardinality give `L^4` unmatched
   records, not a computational sample.
10. Constants: (6.5) displays the explicit unbounded lower bound `2^t/125`.
11. Boundary: Section 7 separates failure of the uniform envelope from every
   fixed-`pi`, C2, C1, and canonical collision claim.
