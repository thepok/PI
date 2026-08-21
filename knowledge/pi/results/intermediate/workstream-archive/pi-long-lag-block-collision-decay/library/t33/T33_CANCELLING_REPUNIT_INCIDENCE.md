# T33: cancelling off-diagonal repunits and the missing incidence bound

Status: `proof sketch`. The imported T16, T29, T32, and T4 interfaces named
below are machine-checked. The new six-case regrouping and dyadic argument are
finite proofs in this note, not Lean theorems. The external assertion about the
irrationality measure of pi is source-pinned but remains an explicit premise.

This note treats only T32's cancelling off-diagonal sector. It obtains no
strict extension of T32's range. Instead, it gives a legal parameter family on
which every fixed source exponent `beta>max(mu_0,2)` misses the first useful
Dirichlet-kernel scale by the power `10^((beta-2)m)`, where `mu_0<8` is the
witness in the external premise. T4's coarsened
exponent-eight corollary loses exactly six powers. The note also states one
aggregate incidence inequality sufficient for this sector. It does not assert
T29 at all scales, the canonical collision estimate, or C1.

## 1. Provenance, normalized scope, and verification boundary

The canonical problem is the locally formulated question copied byte for byte
as `CANONICAL_STATEMENT.txt`; there is no original external source URL. Its
SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

The canonical question asks whether, for every real `0 < s < 1`, one constant
`C_s` works simultaneously for every pair of positive integers `m,N` in

```text
R_pi(m,N) <= C_s [N + N^2 10^(-s m)].                    (1.1)
```

Pairs in (1.1) are ordered and have lag at least `m`. The present note does not
estimate `R_pi`. It studies only one sector of the residual fixed-phase
square-function sibling A12.

The machine-checked inputs are:

1. T32,
   `TheoryLib.PiLongLagBlockCollisionDecay.T32T32AllBlockFixedPiRange`,
   SHA-256
   `3bb7e8a1fc13a87dd6decba4edd7dd1aa4daef51233b585e2e48e81bb2e78fdc`.
2. T16,
   `TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD`,
   SHA-256
   `4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec`.
3. T29,
   `TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction`,
   SHA-256
   `2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358`.
4. T4,
   `TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset`,
   retained knowledge-library SHA-256
   `73a70fc981bc5856e6c52f3c27143d1a54d84373f830c2b1d37faeb2fdbd71de`.

T32 itself imports the accepted T16, T22, T24, and T29 modules. The T13, T17,
T25, T28, and T30 documents in the knowledge library are unverified `proof
sketch` notes. They are not premises here, and no claim unique to them is
described as proved.

The external source is Doron Zeilberger and Wadim Zudilin, *The Irrationality
Measure of Pi is at most 7.103205334137...*, Moscow Journal of Combinatorics and
Number Theory 9 (2020), 407-419, DOI
<https://doi.org/10.2140/moscow.2020.9.407>. The retained publisher PDF is
`zeilberger-zudilin-moscow-2020-9-407.pdf`, SHA-256
`3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
The definition is on PDF page 2 (journal page 407), and the displayed bound
`7.10320533413700172750577342281... < 8` is on PDF page 13 (journal page
418). This is literature evidence, not a Lean theorem or axiom.

### Quantifier and convention audit

Throughout Sections 2-6, fix

```text
mu,c in R, Q0,m,N in N, m >= 1, N >= 1, H = 10^m.        (1.2)
```

Section 7 specializes to `(mu,c)=(8,1)` and to one `Q0` supplied conditionally
by T4 from `IrrationalityMeasureBelow pi 8`. The following choices are binding:

1. Both Bool orientations of every surviving record are retained.
2. A block includes its left endpoint and excludes its right endpoint.
3. The Fourier range is exactly `h=1,...,H`; `h=0` is absent and `h=H` is
   present.
4. The block weight is literally `sqrt(b^2-a^2)`, not block length.
5. A positive difference means `lambda(q1)-lambda(q0)>0` in that order.
6. "Cancelling" means an equality between opposite-sign tokens in the
   four-token difference. Equal-sign repetition is not cancellation.
7. `10^rho-1` is called the reduced repunit factor. The usual decimal repunit
   is `R_rho=(10^rho-1)/9`, so the exact coefficient is
   `9*10^v*R_rho`. This avoids a factor-nine ambiguity.
8. All sums below are finite. No limiting rearrangement is used.
9. The dyadic shells have explicit open and closed endpoints in Section 6.
10. The final incidence inequality concerns this sector only. It is not an
    all-scale T29 assertion.

## 2. The exact imported T32 object

For a lag `ell` and start `n`, put

```text
E(ell,n) = n+ell,
A(ell,n) = 10^(n+ell)-10^n = 10^n(10^ell-1) > 0.         (2.1)
```

An ordered T32 record is

```text
q=(epsilon,(ell,n)) in Bool x (N x N).                   (2.2)
```

Use `epsilon=+` for Lean's `true` orientation and `epsilon=-` for `false`.
Its signed frequency is

```text
lambda(+,ell,n)=+A(ell,n),
lambda(-,ell,n)=-A(ell,n).                               (2.3)
```

For a T24 dyadic block `B=[a_B,b_B)`, T32's `blockRecordDomain` is exactly

```text
Q_B={q=(epsilon,(ell,n)):
       ell>0, m<=ell,
       not ArithmeticExcluded mu c Q0 m n ell,
       a_B<=n+ell<b_B}.                                  (2.4)
```

This is T32's `mem_blockRecordDomain_iff` together with
`blockRecordDomain_both_orientations`. The coefficient of every record is one.
The two orientations occur together and have opposite nonzero frequencies.

For reference, with

```text
q(n,ell)=10^n(10^ell-1),                                 (2.5)
```

the imported exclusion predicate is literally

```text
ArithmeticExcluded mu c Q0 m n ell
 iff Q0<=q(n,ell) and
     H^(-1)<=q(n,ell) * [c/q(n,ell)^mu].                 (2.6)
```

T24's `translatedCanonicalBlocks N` are consecutive half-open power-of-two
blocks partitioning the endpoint interval `[1,N)`. If `B=[a_B,b_B)`, then

```text
b_B=a_B+2^j,
2^j divides a_B-1,
w_B=widthWeight(B)=sqrt(b_B^2-a_B^2)>0.                  (2.7)
```

T32 proves the useful universal lower bound `w_B>=sqrt(3)`, but the exact
weights will be kept in every identity and incidence count below.

Define

```text
e(x)=exp(2*pi*i*x),
K_H(x)=sum_(h=1)^H e(hx),
C_H(x)=Re K_H(x)=sum_(h=1)^H cos(2*pi*h*x).              (2.8)
```

The endpoint `h=H` is included, so `K_H(0)=H`, not `H+1`. T32's
`inclusiveFrequency_valuation_cases` also records

```text
v_10(h)<=m,
v_10(h)=m iff h=H,
otherwise v_10(h)<m.                                    (2.9)
```

Writing `a=v_10(h)` and `u=tenPrimitivePart(h)`, T16's exact reduction gives
`h=10^a u`. We do not use or assert
`v_10(hd)=v_10(h)+v_10(d)`: base ten is composite, and two factors not
individually divisible by ten can have a product divisible by ten.

T32's `canonicalBlockVector_eq_sum_blockRecords` and
`blockSquaredEnergy_eq_diagonal_add_offDiagonal` give the finite identity

```text
sum_(h=1)^H |sum_(q in Q_B) e(h lambda(q) alpha)|^2
 = H #Q_B
   + sum_(q0,q1 in Q_B; q0!=q1)
       K_H((lambda(q1)-lambda(q0)) alpha).                (2.10)
```

After division by (2.7) and summation over the canonical blocks, (2.10) is
exactly T32's `widthWeightedSquareFunction_eq_diagonal_add_offDiagonal`.
Nothing in that theorem estimates the off-diagonal kernels at `alpha=pi`.

T32's proved fixed-pi range is

```text
[(N-m)(N-m+1)]^2 <= N,                                  (2.11)
```

where subtraction is natural-number subtraction. In (2.11), T32 obtains the
T29 target scale with constant one. This note does not reconstruct that proof.

## 3. Cancelling pairs and six disjoint cases

Let

```text
q_i=(epsilon_i,(ell_i,n_i)), E_i=n_i+ell_i, i=0,1,       (3.1)
```

be distinct records in the same `Q_B`. Define exponents `X_i,Y_i` by

```text
lambda(q_i)=10^(X_i)-10^(Y_i),
(X_i,Y_i)=(E_i,n_i) if epsilon_i=+,
(X_i,Y_i)=(n_i,E_i) if epsilon_i=-.                     (3.2)
```

Because `ell_i>0`, one has `X_i!=Y_i`. For

```text
d=lambda(q1)-lambda(q0)>0,                              (3.3)
```

the four labelled tokens are

```text
d=10^(X_1)+10^(Y_0)-10^(Y_1)-10^(X_0).                 (3.4)
```

The only possible opposite-sign equalities in (3.4) are

```text
X_1=X_0 or Y_0=Y_1.                                     (3.5)
```

The other two comparisons are the impossible within-record equalities
`X_1=Y_1` and `Y_0=X_0`. Both equalities in (3.5) cannot hold for an
off-diagonal pair: they would give the same signed frequency, and T22's
machine-checked injectivity on admissible records would give `q0=q1`.
Therefore every cancelling positive pair has exactly one selected equality,
with no tie-breaking convention.

For `rho>=1`, `v>=0`, and a hidden cancelled exponent `z`, define the six
domains `C_(B,j)(v,rho,z)` to consist of pairs `(q0,q1) in Q_B^2` satisfying
the corresponding row below. Every equality and order condition is displayed.

| `j` | `(epsilon_0,epsilon_1)` | hidden cancellation and order | `(v,rho,z)` |
|---|---|---|---|
| `1` | `(+,+)` | `E_0=E_1`, `n_1<n_0` | `n_1=v`, `n_0=v+rho`, `E_0=z` |
| `2` | `(+,+)` | `n_0=n_1`, `E_0<E_1` | `E_0=v`, `E_1=v+rho`, `n_0=z` |
| `3` | `(-,-)` | `E_0=E_1`, `n_0<n_1` | `n_0=v`, `n_1=v+rho`, `E_0=z` |
| `4` | `(-,-)` | `n_0=n_1`, `E_1<E_0` | `E_1=v`, `E_0=v+rho`, `n_0=z` |
| `5` | `(-,+)` | `E_1=n_0` | `n_1=v`, `E_0=v+rho`, `E_1=z` |
| `6` | `(-,+)` | `E_0=n_1` | `n_0=v`, `E_1=v+rho`, `E_0=z` |

There is no positive row with orientations `(+,-)`, because then
`d=-A(ell_1,n_1)-A(ell_0,n_0)<0`. Those ordered pairs are the reversals of
the mixed rows 5 and 6.

In rows 1-4, the displayed strict order is exactly the condition `d>0`. In
row 5, `E_1=n_0`, so

```text
n_1<E_1=n_0<E_0;                                        (3.6)
```

in row 6, `n_0<E_0=n_1<E_1`. Thus positivity is automatic in both mixed
rows. Rows with different orientations are disjoint. Rows 1 and 2 (or 3 and
4) cannot overlap without `q0=q1`. Rows 5 and 6 cannot overlap, since that
would imply `E_1=n_0<E_0=n_1<E_1`. Hence all six domains are pairwise
disjoint.

This disjointness is specific to positive-lag T32 record pairs. T16's generic
cover by four labelled cancellation cases need not be disjoint, so that cover
is not used as a multiplicity formula here.

## 4. Exact valuation and reduced repunit parameters

Deleting the unique equal positive/negative token from any row in Section 3
leaves

```text
d=10^(v+rho)-10^v
 =10^v(10^rho-1)
 =9*10^v R_rho,                                         (4.1)
R_rho=(10^rho-1)/9=11...1 (rho decimal digits).         (4.2)
```

For the mixed rows, (3.6) also shows `rho=ell_0+ell_1`; thus no sign or lag
parameter is hidden in (4.1). Define the common outer parameter domain

```text
D_N={(v,rho) in N^2: 1<=rho and v+rho<N}.                (4.3)
```

This notation is unambiguous when `N=1`: `D_N` is then empty. Every hidden
exponent satisfies `0<=z<N`. The exact additional row conditions, obtained by
substituting the table in Section 3 into `Q_B`, are:

```text
rows 1,3: z-(v+rho)>=m;
           both records have endpoint z in [a_B,b_B);

rows 2,4: v-z>=m;
           both endpoints v and v+rho lie in [a_B,b_B);

rows 5,6: z-v>=m and v+rho-z>=m;
           both endpoints z and v+rho lie in [a_B,b_B),
           hence rho>=2m.                                (4.4)
```

All subtractions in (4.4) are justified by the displayed inequalities. In
each row, the two starts and lags are exactly those recovered from its
`(n_i,E_i)` entries in the Section 3 table. In addition, each of those two
start-lag pairs must satisfy its own literal
`not ArithmeticExcluded mu c Q0 m n_i ell_i` clause from (2.4). These block
and survival clauses are part of `C_(B,j)(v,rho,z)`, not conditions discarded
when passing to the outer envelope `D_N`.

T16's `cancellationValue_ten_reduction`, re-exported by T32 as
`cancellingDifference_valuation`, gives the exact composite-base statements

```text
v_10(d)=v,
tenPrimitivePart(d)=10^rho-1=9 R_rho.                   (4.5)
```

In particular, the pair `(v,rho)` is unique for a positive value `d`: (4.5)
first recovers `v`, and strict monotonicity of `10^rho-1` then recovers `rho`.
The hidden exponent `z`, cancellation row, block, and record multiplicity are
not determined by `d` and must not be discarded.

Define literal finite multiplicities

```text
M_(B,j)(v,rho,z)=# C_(B,j)(v,rho,z),
M_B(v,rho)=sum_(z=0)^(N-1) sum_(j=1)^6 M_(B,j)(v,rho,z),
W(v,rho)=sum_(B in translatedCanonicalBlocks N) M_B(v,rho)/w_B.
                                                                    (4.6)
```

These count record pairs, not distinct numerical coefficients. Every record
still satisfies the lag, arithmetic-survival, and half-open endpoint clauses
in (2.4). Every pair is internal to one block. Equal coefficients arising from
different hidden exponents or record pairs retain their full multiplicity.

## 5. Exact regrouping into weighted real Dirichlet kernels

Let `Can(mu,c,Q0;m,N;alpha)` be the part of T32's width-weighted
off-diagonal sum in which (3.4) has an opposite-sign cancellation:

```text
Can(alpha)
 =sum_B 1/w_B
   sum_(q0,q1 in Q_B; q0!=q1; cancelling)
     K_H((lambda(q1)-lambda(q0)) alpha).                 (5.1)
```

Swapping `(q0,q1)` negates the nonzero difference, preserves cancellation,
and stays in the same block. Since

```text
K_H(-x)=conj(K_H(x)),
K_H(x)+K_H(-x)=2 C_H(x),                                (5.2)
```

every unordered cancelling pair is represented by exactly one of the six
positive rows and its reverse. Substituting (4.1) into the finite sum proves
the exact identity

```text
Can(mu,c,Q0;m,N;alpha)
 =2 sum_((v,rho) in D_N)
      W(v,rho) C_H(10^v(10^rho-1) alpha).                (5.3)
```

Equivalently, with every block weight and multiplicity visible,

```text
Can(alpha)
 =2 sum_B 1/w_B
    sum_((v,rho) in D_N)
      M_B(v,rho) C_H(9*10^v R_rho alpha).                (5.4)
```

Equations (5.3)-(5.4) are real identities. No absolute value or pointwise
majorant has been inserted. The factor two is only the swap/conjugation
factor. It is not an additional Bool-orientation factor: all orientation rows
are already included in `M_B`.

At the fixed phase `alpha=pi`, the exact cancelling sector is therefore

```text
Can(pi)
 =2 sum_B 1/w_B sum_((v,rho) in D_N) M_B(v,rho)
    sum_(h=1)^H cos(2*pi*h*10^v(10^rho-1)*pi).            (5.5)
```

This is the requested finite regrouping. It is a sub-sum of T32's
off-diagonal term, not a reconstruction of T30 or T32.

## 6. Constant-tracked dyadic near-return criterion

For a real `x`, write `||x||_T` for its distance to the nearest integer. The
finite geometric-series formula and the chord bound
`|sin(pi*x)|>=2||x||_T` give, for `||x||_T>0`,

```text
|K_H(x)|<=min(H,1/[2||x||_T]),
|C_H(x)|<=min(H,1/[2||x||_T]).                           (6.1)
```

At distance zero the safe bound is `H`. For the positive integer arguments in
(5.5), distance zero does not occur because pi is irrational.

Let `K_m` be the least integer `K>=1` such that

```text
2^(K+1)>=H.                                              (6.2)
```

For a positive integer `d`, put `delta(d)=||d*pi||_T` and define disjoint
shells

```text
S_0={d: 0<=delta(d)<=1/H},                               (6.3)
S_j={d: 2^(j-1)/H<delta(d)
          <=min(2^j/H,1/2)}, 1<=j<=K_m.                 (6.4)
```

Equality at `1/H` belongs to `S_0`. For `j>=1`, equality at the upper dyadic
endpoint belongs to `S_j`, not `S_(j+1)`. Minimality in (6.2) gives
`2^(K_m-1)/H<1/2<=2^K_m/H`, so the last shell ends exactly at `1/2`.
Consequently (6.3)-(6.4) are pairwise disjoint and cover every possible
distance.

Define the exact weighted shell incidences

```text
I_j(mu,c,Q0;m,N)
 =sum_(B in translatedCanonicalBlocks N) 1/w_B
   sum_((v,rho) in D_N)
     M_B(v,rho)
     1_{10^v(10^rho-1) in S_j}.                         (6.5)
```

Thus `I_j` retains the block, literal weight, all six rows, hidden-exponent
multiplicity, both orientations through those rows, both arithmetic-survival
conditions, and the exact repunit value. It is not an unweighted count of
distinct `(v,rho)` pairs.

On `S_0`, (6.1) gives `|C_H|<=H`. On `S_j`, `j>=1`, its open lower endpoint
gives

```text
|C_H(d*pi)|<H/2^j.                                      (6.6)
```

Taking absolute values in (5.4), partitioning by the disjoint shells, and
using (6.6) proves the constant-tracked bound

```text
|Can(8,1,Q0;m,N;pi)|
 <=2H [I_0(8,1,Q0;m,N)
       +sum_(j=1)^K_m 2^(-j) I_j(8,1,Q0;m,N)].           (6.7)
```

The following is one precise, unproved aggregate premise sufficient for this
sector. Fix the `Q0` supplied by the external premise in Section 7:

```text
(ARI_cancel)
For every real s with 0<s<1, there exists C_s>=0 such that,
for every m,N>=1,

I_0(8,1,Q0;m,N)+sum_(j=1)^K_m 2^(-j) I_j(8,1,Q0;m,N)
 <=C_s [N+N^2 10^(-s m)].                               (6.8)
```

If `(ARI_cancel)` holds, combining (6.7) and (6.8) gives exactly

```text
|Can(8,1,Q0;m,N;pi)|
 <=2 C_s 10^m [N+N^2 10^(-s m)].                        (6.9)
```

Thus, conditionally on `(ARI_cancel)`, the sector constant is
`A_s^cancel=2C_s`. No `sqrt(3)` is lost because
(6.5) retains the literal weights. If one instead used unweighted incidences
`J_j`, T32's `w_B>=sqrt(3)` would give only `I_j<=J_j/sqrt(3)`.

## 7. Testing the external `mu(pi)<8` premise

Assume explicitly

```text
hSource: IrrationalityMeasureBelow pi 8.                 (7.1)
```

Unpacking (7.1) first supplies a witness `mu_0<8` such that, for every
`beta>mu_0`, there is an onset `Q_beta` for exponent `beta`. More explicitly,
putting `epsilon=beta-mu_0>0` in the source quantifiers and choosing a nearest
integer to `d*pi` gives, for every positive integer `d>=Q_beta`,

```text
||d*pi||_T>d^(1-beta),
|C_H(d*pi)|<=min(H,d^(beta-1)/2).                        (7.2)
```

T4's machine-checked conditional theorem makes the particular coarsened
choice `beta=8` and supplies a natural `Q0` with

```text
EffectiveIrrationality pi 8 1 Q0.                       (7.3)
```

For every positive integer `d>=Q0`, choose a nearest integer `p` to `d*pi`.
The exact inequality in (7.3) gives

```text
1/d^8<|pi-p/d|=||d*pi||_T/d,
||d*pi||_T>d^(-7).                                      (7.4)
```

Consequently the direct insertion of T4's exponent-eight corollary into (6.1)
is

```text
|C_H(d*pi)|<=min(H,d^7/2).                              (7.5)
```

For `1<=d<Q0`, (7.3) supplies no numerical lower bound. There are only
finitely many such integers for a fixed `Q0`, but (6.8) deliberately includes
them rather than hiding a `Q0`-dependent constant.

### A legal power-loss family

For every integer `j>=1`, set

```text
t=2^(j-1), m=t, N=2t+1, H=10^t.                         (7.6)
```

Since `N-1=2^j`, T24's canonical partition has exactly one block

```text
B=[1,N).                                                 (7.7)
```

Consider the positive-orientation records

```text
q0=(+,(t,0)), endpoint E0=t,   lambda(q0)=H-1,
q1=(+,(t+1,0)), endpoint E1=t+1, lambda(q1)=10H-1.       (7.8)
```

Both endpoints lie in (7.7), and both lags are at least `m`. Both records
survive T32's arithmetic filter for `(mu,c)=(8,1)`, independently of `Q0`.
Indeed their structured denominators are at least `H-1>=9`, and

```text
(H-1)^2>H,
q(n,ell)^7>H,
q(n,ell)^(-7)<H^(-1).                                   (7.9)
```

The second conjunct of `ArithmeticExcluded 8 1 Q0 m n ell` is therefore
false, whether or not its first conjunct `Q0<=q(n,ell)` holds.

The pair in (7.8) is row 2 of Section 3, with common cancelled start `z=0`,
and

```text
d=lambda(q1)-lambda(q0)=9H
 =10^t(10^1-1)=9*10^t R_1,
(v,rho,z)=(t,1,0).                                      (7.10)
```

The two negative orientations, ordered as the lag-`t+1` record followed by
the lag-`t` record, give row 4 with the same positive difference. Hence, for
the unique block,

```text
M_B(t,1)>=2,
w_B=sqrt(N^2-1)=2 sqrt(t(t+1)).                          (7.11)
```

Now fix any `beta` with

```text
max(mu_0,2)<beta<8.                                     (7.12)
```

Such a `beta` exists because `mu_0<8`. For every sufficiently large member of
the family, `d=9H` exceeds both `Q_beta` and `Q0`. The full source-level
consequence (7.2) gives

```text
||9H*pi||_T>(9H)^(1-beta).                              (7.13)
```

To make the geometric part of (6.1) improve on the triangle bound `H`, one
needs a lower bound exceeding `1/(2H)`. The guaranteed lower bound in (7.13)
is smaller than that transition scale by the exact factor

```text
 [1/(2H)] / [(9H)^(1-beta)]
 = [9^(beta-1)/2] H^(beta-2).                           (7.14)
```

Since `beta>2`, (7.14) is a quantified positive power loss. The corresponding
pointwise cap from (7.2), divided by the triangle bound, is the same factor:

```text
[d^(beta-1)/2]/H=[9^(beta-1)/2]H^(beta-2).              (7.15)
```

It therefore exceeds one for all sufficiently large members, so this
source-level pointwise estimate reduces to the trivial cap `H`.

For comparison, the exact coarsened exponent-eight corollary (7.4) gives

```text
||9H*pi||_T>(9H)^(-7).                                  (7.16)
```

To make the geometric part of (6.1) improve on the triangle bound `H`, one
needs a lower bound exceeding `1/(2H)`. The guaranteed lower bound in (7.16)
is smaller than that transition scale by the exact factor

```text
[1/(2H)] / [(9H)^(-7)] = (9^7/2) H^6
                         = (9^7/2) 10^(6m).              (7.17)
```

Against the deepest-shell endpoint `1/H`, the miss is `9^7 H^6`. Equivalently,
the nontrivial term inferred from irrationality is worse than the triangle
bound by

```text
[d^7/2]/H=(9^7/2)H^6.                                   (7.18)
```

so (7.5) reduces exactly to `|C_H(d*pi)|<=H` on this family. This exported
specialization has a six-power loss in `H=10^m`.

The family is outside T32's proved range. Here `N-m=t+1`, and

```text
[(N-m)(N-m+1)]^2=[(t+1)(t+2)]^2>2t+1=N.                (7.19)
```

Equations (7.13)-(7.18) do not show that the actual distance is small or that
the actual kernel is large. They show precisely that the pointwise
bound at any fixed source exponent `beta>2`, including a `beta` chosen just
above the cited `7.103205...` bound and T4's exported exponent eight, cannot
place these legal cancelling values outside the deepest shell. It therefore
does not yield a strict extension of T32 by this route.

## 8. Terminal status and exact missing input

The new conclusions have verification level `proof sketch`:

1. The six domains in Section 3 are an exhaustive disjoint partition of
   T32's positive cancelling off-diagonal record pairs.
2. Every such difference has the unique exact form
   `10^v(10^rho-1)=9*10^v R_rho`, with the exact outer and row-specific
   ranges (4.3)-(4.4) and valuation (4.5).
3. The cancelling sector has the exact real finite regrouping (5.3)-(5.5).
4. The dyadic incidences with all endpoints and constants exposed satisfy
   (6.7).
5. The full external premise at any selected `beta` in (7.12) loses the power
   `H^(beta-2)` on the legal family; T4's coarsened exponent-eight corollary
   loses exactly `(9^7/2)10^(6m)` at the transition scale.

No strict extension of T32's range is claimed. No actual near-return incidence
bound for pi is proved. In particular, this note makes no all-scale T29 claim,
no collision estimate, and no C1 claim. The single aggregate repunit-incidence
inequality whose proof would close exactly this cancelling sector is

```text
For every 0<s<1, there is C_s>=0 such that for all m,N>=1,

I_0(8,1,Q0;m,N)+sum_(j=1)^K_m 2^(-j) I_j(8,1,Q0;m,N)
 <= C_s [N+N^2 10^(-s m)],                              (ARI_cancel)

where K_m=min{K>=1:2^(K+1)>=10^m}, and I_j is exactly the
literal-width-weighted six-case multiplicity (6.5) at
||10^v(10^rho-1)pi||_T in the endpoint-pinned shell (6.3)-(6.4).
```
