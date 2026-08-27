# T58: complete signed primitive partition and the exact T56 defect

Status: `proof sketch`. Every imported theorem named below is machine-checked
in T29, T31, T32, T34, T49, or T56. The finite regroupings in this note are
proved from those interfaces. This note is not a Lean artifact, so the new
notation and the assembled identities below remain at sketch verification
level until separately formalized.

## 1. Source, scope, and decision

The canonical local problem has no external source URL. Its byte-exact text is
delivered as `CANONICAL_STATEMENT.txt`, with SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That file asks for the canonical ordered long-lag collision estimate for the
decimal digits of pi. T58 does not prove or refute that estimate. It audits
only the residual sparse-Fourier sibling A12 encoded by T49, at
`(mu,c)=(8,1)` when T56 is invoked. It makes no T29 premise, C2, or C1 claim.

The decision is a corrected exhaustive partition, not a cancellation bound:

1. On every exact T49 block domain, primitive records split disjointly by
   decimal valuation, positive primitive value, and the two record Booleans.
2. Every positive primitive record has a unique two-element off-diagonal sign
   orbit. Its two terms are conjugates and add to twice a real kernel; they do
   not have opposite coefficients.
3. At T56's scales, every selected residue-1 or residue-9 value has exactly
   four positive primitive records. Simultaneous reversal splits those four
   records into two pairs; adding the negative swapped records completes two
   four-element squares. Each square reinforces rather than cancels.
4. The T56 selected contribution is exactly `16*EBox(t)/w_t`.
5. The unmatched part is the explicit finite set of T49 primitive records
   whose value is outside the two selected value images. It is itself
   exhaustively partitioned by valuation, value, and Boolean orientation, and
   its exact signed contribution is displayed in Section 9.

Thus T56 gives an infinite family disproving any phase-independent rule that
the four positive primitive rows cancel solely from their scalar coefficients
or simultaneous-reversal pairing. It does not control the selected sum at
`alpha=pi`, and it does not control the explicit unmatched defect.

### 1.1 Normalized quantifiers

Sections 2-4 fix arbitrary real `mu,c,alpha`, naturals `Q0,m,N`, and a block

```text
B in translatedCanonicalBlocks N.
```

No positivity of `m,N` is needed merely to state the finite partitions.
Whenever positivity of the width is used, block membership supplies T29's
theorem `canonical_widthWeight_pos`.

Sections 5-9 fix arbitrary naturals `Q0,t` and put

```text
L = 2^t,                 m = 1,
N_t = 4*L+1,             B_t = <start=1, level=t+2>,
alpha = pi.
```

Then `L>=1`, `N_t>=5`, and the construction exists for every `t`; hence its
endpoints are unbounded. No estimate uniform in `t` is asserted.

### 1.2 Terminology that must not be conflated

- `record orientation` is the pair of Booleans carried by the two T12 records.
- `positive orientation` means T31's strict ordering of the two signed
  frequencies.
- `swap` exchanges those two records and gives the negative off-diagonal term.
- `J` reverses both records and then swaps them, preserving the positive value.
- `primitive value` means the positive natural `blockDifferenceValue p`.
- `primitive residue` means the final decimal digit of
  `tenPrimitivePart (blockDifferenceValue p)`, not the final digit of the
  unscaled value.

## 2. Exact T49 data

Write

```text
Blocks_N = translatedCanonicalBlocks N.                    (2.1)
```

T29 proves that this list has no duplicates. For `B in Blocks_N`, define

```text
R_B = blockRecordDomain mu c Q0 m B,
D_B = primitiveRecordDomain mu c Q0 m N B.                 (2.2)
```

T49's `blockOrderedDomain_eq_blockRecordDomain` and
`mem_primitiveValuationStratum_iff` give the literal membership test. If
`p=(q_plus,q_minus)`, then

```text
p in D_B
iff
  q_plus in R_B,
  q_minus in R_B,
  signedDecimalFrequency(q_minus)
    < signedDecimalFrequency(q_plus),
  Noncancelling (+,+,-,-) (blockDifferenceExponent p).      (2.3)
```

T32's `mem_blockRecordDomain_iff` expands each record condition as

```text
AdmissibleOrderedFrequency mu c Q0 m q,
B.start <= frequencyEndpoint(q.core) < B.finish.            (2.4)
```

Thus (2.2)-(2.4) retain the positive lag, weak long-lag cutoff, arithmetic
survival, weak left block endpoint, strict right block endpoint, and both
literal record orientations. No ambient superset is used.

For `p in D_B`, put

```text
d(p)   = blockDifferenceValue p,
ell(p) = tenValuation(d(p)),
omega(p) = (q_plus.bool,q_minus.bool) in Bool x Bool.        (2.5)
```

Because `D_B` is a subset of T31's positive-difference domain,
`blockDifferenceValue_pos` gives

```text
d(p) > 0.                                                   (2.6)
```

The block weight is exactly

```text
w_B = widthWeight B
    = sqrt((B.finish)^2-(B.start)^2) > 0.                   (2.7)
```

The strict positivity is T29's `canonical_widthWeight_pos`. No block length,
upper bound, or comparable surrogate replaces `w_B` below.

Finally set

```text
K_m(d,alpha) = inclusiveRealKernel m d alpha
 = sum_(h in Icc 1 (10^m))
     Re phase(h*d,alpha).                                   (2.8)
```

Equation (2.8) is T34's `inclusiveRealKernel_frequency_audit`. In particular,
frequency zero is absent and the endpoint `h=10^m` is present.

T49's exact signed primitive contribution is

```text
P_prim(mu,c,Q0;m,N;alpha)
 = 2 * sum_(B in Blocks_N)
         sum_(p in D_B) K_m(d(p),alpha)/w_B.                (2.9)
```

This is the definition `primitiveSectorContribution`. It is a signed real
sum: `K_m` is not replaced by its absolute value or by a shell weight.

## 3. Exhaustive valuation-value-orientation partition

The following finite sets are defined from `D_B`; none is assumed to contain
all naturals:

```text
Lambda_B = image ell D_B,
V_B(ell0) = image d {p in D_B : ell(p)=ell0},               (3.1)

F_B(ell0,d0,omega0)
 = {p in D_B :
      ell(p)=ell0 and d(p)=d0 and omega(p)=omega0}.          (3.2)
```

Here `omega0` ranges over the literal four-element type `Bool x Bool`.
Membership is therefore exactly

```text
p in F_B(ell0,d0,omega0)
iff
  p in D_B and ell(p)=ell0 and d(p)=d0
    and omega(p)=omega0.                                   (3.3)
```

Define the multiplicity

```text
n_B(ell0,d0,omega0) = card F_B(ell0,d0,omega0).             (3.4)
```

### Proposition 3.1: finite partition

There is a disjoint equality

```text
D_B = disjoint_union_(ell0 in Lambda_B)
        disjoint_union_(d0 in V_B(ell0))
          disjoint_union_(omega0 in Bool x Bool)
            F_B(ell0,d0,omega0).                           (3.5)
```

Proof. Given `p in D_B`, its only possible indices are the three values in
(2.5). The image definitions put `ell(p)` in `Lambda_B` and `d(p)` in
`V_B(ell(p))`, while `omega(p)` is one of the four Boolean pairs. Thus `p`
occurs on the right. Conversely, (3.3) puts every right-hand element in
`D_B`. If one record lies in two displayed pieces, the three equalities in
(3.3) force equality of all three indices. This proves both exhaustiveness and
pairwise disjointness. Notice that this argument also handles an empty `D_B`.

Equivalently, for every function `f` on record pairs, three applications of
finite fiberwise summation give

```text
sum_(p in D_B) f(p)
 = sum_(ell0 in Lambda_B)
     sum_(d0 in V_B(ell0))
       sum_(omega0 in Bool x Bool)
         sum_(p in F_B(ell0,d0,omega0)) f(p).               (3.6)
```

Taking `f(p)=K_m(d(p),alpha)/w_B`, the summand is constant on each
`F_B(ell0,d0,omega0)`. Hence

```text
sum_(p in D_B) K_m(d(p),alpha)/w_B
 = (1/w_B) * sum_(ell0 in Lambda_B)
     sum_(d0 in V_B(ell0))
       sum_(omega0 in Bool x Bool)
         n_B(ell0,d0,omega0) K_m(d0,alpha).                 (3.7)
```

Substitution into (2.9) proves the requested all-block regrouping identity:

```text
P_prim(mu,c,Q0;m,N;alpha)
 = 2 * sum_(B in Blocks_N) (1/w_B)
     sum_(ell0 in Lambda_B)
       sum_(d0 in V_B(ell0))
         sum_(omega0 in Bool x Bool)
           n_B(ell0,d0,omega0) K_m(d0,alpha).               (3.8)
```

Every T49 primitive record occurs exactly once in (3.8). The valuation index
is redundant after `d0` is fixed, but retaining it exposes the exact T49
valuation fibers rather than silently coarsening them.

## 4. Complete off-diagonal sign orbits

Let `Q_B=blockOrderedDomain mu c Q0 m N B`, and let

```text
OD_B = {(q,r) in Q_B x Q_B : q != r}.                       (4.1)
```

T31's `blockOffDiagonal_eq_orient_image` and
`orientPositiveDifference_injOn_block` give a bijection

```text
Bool x blockPositiveDifferenceDomain  ->  OD_B,
(false,p) |-> p,
(true,p)  |-> swap(p).                                     (4.2)
```

Restricting the positive domain in (4.2) to `D_B` gives the full primitive
off-diagonal subdomain. For each `p in D_B`, define its sign-orbit Finset using
the literal finite Bool domain

```text
O_sign(p)
 = image (b |-> orientPositiveDifference(b,p)) (univ Bool)
 = {p,swap(p)}.                                             (4.3)
```

The strict inequality in (2.3) implies `p!=swap(p)`. The injectivity in (4.2)
implies that distinct positive records give disjoint sign orbits. Therefore
(4.3) is a complete, disjoint two-element orbit classification; there is no
zero-difference orbit.

For `d=d(p)>0` and one inclusive frequency `h`, T31's expansion gives

```text
phase(-h,d*alpha) + phase(h,d*alpha)
 = 2*Re phase(h,d*alpha).                                  (4.4)
```

Summing exactly over `h in Icc 1 (10^m)` gives

```text
contribution of O_sign(p) = 2*K_m(d,alpha).                 (4.5)
```

This proves the sole outer factor `2` in (2.9). Both orbit elements have
coefficient `+1`; the word "sign" refers to the phase frequencies `+d` and
`-d`, not to opposite scalar coefficients. In particular, at `alpha=0`, each
two-element sign orbit contributes `2` at every retained frequency, so these
orientations cannot support a phase-independent cancellation rule.

The Boolean record pattern `omega(p)=(b_plus,b_minus)` is changed by swap to
`(b_minus,b_plus)`, but (4.5) depends only on `d`. Thus the orientation
multiplicities in (3.8) are genuine positive integer multiplicities in a
signed kernel sum, not cancellation signs.

## 5. The T56 one-block family

Fix `Q0,t` and use the notation of Section 1. T56 proves

```text
translatedCanonicalBlocks N_t = [B_t],
B_t.start=1,                  B_t.finish=N_t,
w_t = widthWeight B_t = sqrt(N_t^2-1),
inclusiveFrequencies 1 = Icc 1 10.                         (5.1)
```

Partition the exact block endpoints into four inclusive intervals

```text
I1=[1,L],          I2=[L+1,2L],
I3=[2L+1,3L],     I4=[3L+1,4L].                            (5.2)
```

Let

```text
X_t = I1 x I2 x I3 x I4.                                   (5.3)
```

T56 proves `card X_t=L^4`. If `x=(x1,x2,x3,x4) in X_t`, then

```text
1 <= x1 < x2 < x3 < x4 < N_t.                              (5.4)
```

Put

```text
U(x)=10^x4-10^x3,              V(x)=10^x2-10^x1,
d1(x)=U(x)-V(x),                d9(x)=U(x)+V(x).             (5.5)
```

T56's `residueValues_positive` gives `d1(x)>0` and `d9(x)>0`.
Its exact valuation audit gives

```text
tenValuation(d1(x)) = x1,
tenPrimitivePart(d1(x)) mod 10 = 1,
tenValuation(d9(x)) = x1,
tenPrimitivePart(d9(x)) mod 10 = 9.                        (5.6)
```

Thus the two value images are disjoint.

At `m=1, alpha=pi`, (2.8) is literally

```text
K_1(d,pi) = sum_(h=1)^10 cos(2*pi^2*h*d).                  (5.7)
```

The endpoints `1` and `10`, including the latter, will remain visible in all
subsequent sums.

## 6. Complete selected primitive fibers

For unequal coordinates define T56's exact record

```text
R(x,y) = (true, (x-y,y))   if y<x,
         (false,(y-x,x))   if x<y.                          (6.1)
```

It has ordered coordinates `(x,y)`, signed frequency `10^x-10^y`, and
endpoint `max(x,y)`. By (5.4), every record below is in T49's exact block
record domain, not merely in an ambient coordinate box.

For a fixed `x in X_t`, T56's four rows for value `d1(x)` are

| row | positive record pair `(q_plus,q_minus)` | Boolean pattern |
|---|---|---|
| `00` | `(R(x4,x2),R(x3,x1))` | `TT` |
| `01` | `(R(x4,x3),R(x2,x1))` | `TT` |
| `10` | `(R(x1,x2),R(x3,x4))` | `FF` |
| `11` | `(R(x1,x3),R(x2,x4))` | `FF` |

The four rows for value `d9(x)` are

| row | positive record pair `(q_plus,q_minus)` | Boolean pattern |
|---|---|---|
| `00` | `(R(x4,x1),R(x3,x2))` | `TT` |
| `01` | `(R(x4,x3),R(x1,x2))` | `TF` |
| `10` | `(R(x2,x1),R(x3,x4))` | `TF` |
| `11` | `(R(x2,x3),R(x1,x4))` | `FF` |

The tables are exactly T56's `residueOne_orientation_signs` and
`residueNine_orientation_signs`, together with the defining rows. T56 also
proves for every row:

```text
row in D_(B_t),
d(row)=d1(x) or d(row)=d9(x),
Noncancelling (+,+,-,-) (blockDifferenceExponent row).      (6.2)
```

Most importantly, `residueOne_ambientPrimitiveValueFiber_iff` and its
residue-9 analogue prove the converses:

```text
{p in D_(B_t) : d(p)=d1(x)} = the four displayed d1 rows,
{p in D_(B_t) : d(p)=d9(x)} = the four displayed d9 rows.   (6.3)
```

Each set in (6.3) has cardinality exactly four. Therefore these are full
ambient T49 primitive-value fibers; there is no fifth orientation and no
unlisted record over either selected value.

### 6.1 No collisions between selected parameter values

The maps `x |-> d1(x)` and `x |-> d9(x)` are injective on `X_t`. This follows
without assuming uniqueness of signed decimal notation. Suppose, for example,
`d1(x)=d1(y)`. The row `p1,00(x)` lies in the full fiber over `d1(y)`, so (6.3)
makes it equal to `p1,r(y)` for some row `r`. T56's
`residueOnePair_injective_on_parameters` then gives `(x,00)=(y,r)`, hence
`x=y`. The residue-9 proof is identical. Equation (5.6) separates the two
images from one another.

Consequently the two selected record domains

```text
S1_t = residueOneRecordDomain t,
S9_t = residueNineRecordDomain t                           (6.4)
```

are disjoint and satisfy

```text
card S1_t = 4*L^4,       card S9_t = 4*L^4.                (6.5)
```

These are T56's exact Finset images, and its parameter injectivity theorem
proves that no deduplication changes the displayed cardinalities.

## 7. Simultaneous-reversal squares and their signs

Let `rev R(x,y)=R(y,x)` and, for a positive pair `p=(q_plus,q_minus)`, define

```text
J(p) = (rev(q_minus),rev(q_plus)).                           (7.1)
```

Reversing each record negates its signed frequency; the final swap in (7.1)
restores strict positive orientation. Thus `J` preserves `d(p)`. Direct
substitution in the two tables gives, for both residues `r in {1,9}`,

```text
J(p_r,00)=p_r,11,       J(p_r,11)=p_r,00,
J(p_r,01)=p_r,10,       J(p_r,10)=p_r,01.                  (7.2)
```

The strict coordinate inequalities in (5.4) make all four rows distinct.
Hence each positive four-fiber is the disjoint union of the two `J`-orbits

```text
{00,11} and {01,10}.                                       (7.3)
```

Now apply the off-diagonal swap `S(p)=swap(p)` from Section 4. Each `J`-orbit
completes to a four-element square

```text
Square_r,0(x) = {p_r,00,p_r,11,S(p_r,00),S(p_r,11)},
Square_r,1(x) = {p_r,01,p_r,10,S(p_r,01),S(p_r,10)}.        (7.4)
```

The two positive elements in each square have value `d_r(x)`; the two swapped
elements have signed difference `-d_r(x)`. By (4.5), at scale `m=1` each
square contributes exactly

```text
4*K_1(d_r(x),alpha)/w_t.                                   (7.5)
```

Both squares together contribute

```text
8*K_1(d_r(x),alpha)/w_t.                                   (7.6)
```

This is exactly four positive T49 records times its sole swap factor `2`.
There is no extra orientation factor and no cancellation between the two
Boolean patterns.

The family (7.4), for all `t` and all `x in X_t`, is an explicit infinite
counterfamily to a proposed rule that the four positive rows cancel from their
scalar coefficients or from `J`-pairing alone. At `alpha=0`, the general
definition (2.8) gives `K_1(d,0)=10`, so every square has positive contribution
`40/w_t`; therefore such cancellation cannot be an algebraic consequence of
the record signs. At `alpha=pi`, no sign of `K_1(d,pi)` is asserted.

## 8. Exact selected-plus-defect partition

Define the selected value sets

```text
V1_t = image d1 X_t,
V9_t = image d9 X_t,
Vsel_t = V1_t union V9_t.                                  (8.1)
```

By (5.6) and Section 6.1, `V1_t` and `V9_t` are disjoint, each has cardinality
`L^4`, and every value in either image has exactly the four records in (6.3).
It follows in both directions that

```text
S1_t union S9_t
 = {p in D_(B_t) : d(p) in Vsel_t}.                        (8.2)
```

Define the defect Finset, not merely a symbol for an unspecified remainder,
by either of the equal expressions

```text
E_t = D_(B_t) \ (S1_t union S9_t)
    = {p in D_(B_t) : d(p) notin Vsel_t}.                  (8.3)
```

The notation suppresses the already fixed `Q0`: `E_t`, `LambdaE_t`,
`VE_t`, and `e_t` all depend on `Q0` through `D_(B_t)`.

The second equality follows from (8.2). Thus the exact membership test is

```text
p in E_t
iff
  p in primitiveRecordDomain 8 1 Q0 1 N_t B_t
  and for every x in X_t,
        d(p) != d1(x) and d(p) != d9(x).                   (8.4)
```

Equation (8.4) classifies every unmatched fiber: an unmatched value is a
realized positive primitive value outside the two explicit images, and its
entire T49 fiber lies in `E_t`. Conversely, (6.3) proves that no record with a
selected value remains in `E_t`.

For a fully finite audit of the defect, define

```text
LambdaE_t = image ell E_t,
VE_t(ell0) = image d {p in E_t : ell(p)=ell0},

E_t(ell0,d0,omega0)
 = {p in E_t :
      ell(p)=ell0 and d(p)=d0 and omega(p)=omega0},

e_t(ell0,d0,omega0) = card E_t(ell0,d0,omega0).             (8.5)
```

The same unique-index proof as Proposition 3.1 gives the disjoint equality

```text
E_t = disjoint_union_(ell0 in LambdaE_t)
        disjoint_union_(d0 in VE_t(ell0))
          disjoint_union_(omega0 in Bool x Bool)
            E_t(ell0,d0,omega0).                           (8.6)
```

This is exhaustive even though no simpler arithmetic description of the
unmatched value set is presently proved.

## 9. Exact signed Fourier regrouping at the T56 scales

T56's `residue_cosine_pairing` proves, for every `x in X_t` and every natural
`h`, and hence for each of the literal frequencies `1<=h<=10`,

```text
cos(2*pi^2*h*d1(x)) + cos(2*pi^2*h*d9(x))
 = 2*cos(2*pi^2*h*U(x))*cos(2*pi^2*h*V(x)).                 (9.1)
```

Define exactly as T56

```text
EBox(t)
 = sum_(h in Icc 1 10) sum_(x in X_t)
     cos(2*pi^2*h*U(x))*cos(2*pi^2*h*V(x)).                 (9.2)
```

The four positive records per value, the swap factor `2`, and the pairing
factor `2` give T56's kernel-checked identity

```text
P_sel(Q0,t)
 = 2 * [sum_(p in S1_t) K_1(d(p),pi)/w_t
          + sum_(p in S9_t) K_1(d(p),pi)/w_t]
 = 16*EBox(t)/w_t.                                         (9.3)
```

The parameter `Q0` remains visible even though T56 proves the selected records
are admissible for every `Q0`.

Because (5.1) contains the entire canonical block list and (8.3) is a disjoint
partition of its exact primitive domain, finite sum additivity gives

```text
P_prim(8,1,Q0;1,N_t;pi)
 = P_sel(Q0,t)
   + 2*sum_(p in E_t) K_1(d(p),pi)/w_t.                    (9.4)
```

Substitute (8.5)-(8.6) and (9.3):

```text
P_prim(8,1,Q0;1,N_t;pi)
 = 16*EBox(t)/w_t
   + (2/w_t) * sum_(ell0 in LambdaE_t)
       sum_(d0 in VE_t(ell0))
         sum_(omega0 in Bool x Bool)
           e_t(ell0,d0,omega0) K_1(d0,pi).                 (9.5)
```

Expanding every kernel and the selected term gives the completely explicit
frequency form

```text
P_prim(8,1,Q0;1,N_t;pi)
 = (16/w_t) * sum_(h in Icc 1 10) sum_(x in X_t)
       cos(2*pi^2*h*U(x))*cos(2*pi^2*h*V(x))
   + (2/w_t) * sum_(ell0 in LambdaE_t)
       sum_(d0 in VE_t(ell0))
         sum_(omega0 in Bool x Bool)
           e_t(ell0,d0,omega0)
             sum_(h in Icc 1 10) cos(2*pi^2*h*d0).          (9.6)
```

Equations (8.4)-(8.6) and (9.6) are the corrected defect decomposition. They
specify every unmatched record, every realized valuation and value, all four
record orientations, the swapped phase signs, the literal width, and both
frequency endpoints. There is no unnamed remainder.

## 10. What this does and does not establish

The exhaustive general identity is (3.8). The complete T56 square-orbit
classification is (7.2)-(7.6). The exact selected-versus-unmatched partition
is (8.2)-(8.6), and its signed Fourier identity is (9.5)-(9.6).

These identities show precisely why T49's positive shell majorant cannot be
recovered by deleting residue 1 or residue 9: each selected primitive value
has four reinforcing positive-domain representations, not cancelling record
coefficients. At `alpha=pi`, however, their real kernels can have either sign.
T56's `EBoxBound` is an explicit unproved hypothesis, and no inspected theorem
bounds the defect sum in (9.6). Therefore T58 establishes no estimate for the
full signed primitive sector.

In particular, this note asserts none of the following:

- `EBoxBound C` for any `C`;
- a bound for the defect term;
- T49's `PrimitiveIncidence` predicate;
- T29's `WidthWeightedSquareFunction` at `Real.pi`;
- C2, C1, or the canonical collision estimate.

## 11. Skeptic's verification checklist

1. Source: compare `CANONICAL_STATEMENT.txt` with the hash in Section 1.
2. Scope: the result is explicitly the A12 Fourier sibling, not the canonical
   digit-collision statement.
3. Record domain: verify (2.3)-(2.4) against T49
   `mem_primitiveValuationStratum_iff`, T49
   `blockOrderedDomain_eq_blockRecordDomain`, and T32
   `mem_blockRecordDomain_iff`.
4. Positive value: verify (2.6) against T31
   `blockDifferenceValue_pos` after using T49's subset definition.
5. Weight: verify (2.7) against T29 `widthWeight` and
   `canonical_widthWeight_pos`.
6. Frequencies: verify (2.8) against T34
   `inclusiveRealKernel_frequency_audit`; zero is absent and `10^m` is
   included.
7. General partition: check (3.1)-(3.6) by membership and uniqueness of the
   three displayed indices.
8. Regrouping: specialize (3.6) to a value-constant summand to obtain
   (3.7)-(3.8), without absolute values.
9. Sign orbits: verify (4.2) against T31
   `blockOffDiagonal_eq_orient_image`,
   `orientPositiveDifference_injOn_block`, and
   `sum_blockOffDiagonal_eq_orient`.
10. T56 block: verify all of (5.1), including the singleton block list,
    half-open endpoints, square-root weight, and frequency 10.
11. Valuations: verify (5.6) against T56
    `residue_record_valuation_fiber_audit` and its exact value lemmas.
12. Fibers: verify the tables and (6.3) against T56's two
    `ambientPrimitiveValueFiber_iff` and two orientation-sign theorems.
13. No parameter collisions: check the short derivation in Section 6.1 using
    T56's two parameter-injectivity theorems.
14. Square orbits: substitute the record definitions into (7.1) to check
    (7.2), then apply the universal swap identity (4.5).
15. Defect: check both inclusions in (8.2), then Boolean membership in the
    Finset difference to obtain (8.3)-(8.4).
16. Defect exhaustiveness: apply Proposition 3.1's unique-index argument to
    the literal finite set `E_t` in (8.5).
17. Final equality: use disjoint sum additivity, T56
    `boxSignedContribution_eq_deduplicated`,
    `boxSignedContribution_eq_EBox`, and (8.6) to obtain (9.5)-(9.6).
18. Claim boundary: confirm that no absolute value, positive shell majorant,
    `EBoxBound`, T29 premise, C2, C1, or canonical collision conclusion appears
    in the asserted identities.

## 12. Final exhaustive signed partition

First, the positive representatives have the proved finite partition pattern,
at sketch verification level,

```text
D_(B_t)
 = (S1_t disjoint_union S9_t)
     disjoint_union
       disjoint_union_(ell0 in LambdaE_t)
         disjoint_union_(d0 in VE_t(ell0))
           disjoint_union_(omega0 in Bool x Bool)
             E_t(ell0,d0,omega0),                           (12.1)
```

Here `S1_t` and `S9_t` are respectively the disjoint unions, over `x in X_t`,
of the complete four-record fibers over `d1(x)` and `d9(x)`. The final pieces
satisfy the explicit membership test (8.4)-(8.5).

Define the full signed primitive off-diagonal Finset

```text
Dsign_t
 = image orientPositiveDifference ((univ Bool) x D_(B_t)). (12.2)
```

T31's injectivity theorem and (12.1) give the exhaustive disjoint signed
partition

```text
Dsign_t
 = [disjoint_union_(p in S1_t) O_sign(p)]
     disjoint_union
       [disjoint_union_(p in S9_t) O_sign(p)]
     disjoint_union
       [disjoint_union_(ell0 in LambdaE_t)
          disjoint_union_(d0 in VE_t(ell0))
            disjoint_union_(omega0 in Bool x Bool)
              disjoint_union_(p in E_t(ell0,d0,omega0))
                O_sign(p)].                                (12.3)
```

Every member of `Dsign_t` occurs exactly once: T31 chooses one strict positive
representative, (12.1) chooses one selected or defect fiber, and `univ Bool`
chooses that representative or its negative swap. Summing the phases over
(12.3) gives the exact signed identity

```text
P_prim(8,1,Q0;1,N_t;pi)
 = 16*EBox(t)/w_t
   + (2/w_t) * sum_(ell0 in LambdaE_t)
       sum_(d0 in VE_t(ell0))
         sum_(omega0 in Bool x Bool)
           e_t(ell0,d0,omega0) K_1(d0,pi).                 (12.4)
```

The infinite T56 family refutes cancellation based only on the four row
coefficients or `J`-pairing, while (12.3) and (12.4) give the corrected
exhaustive signed defect decomposition and its exact contribution. No
remainder is assumed or unnamed, and no C2 or C1 claim is made.
