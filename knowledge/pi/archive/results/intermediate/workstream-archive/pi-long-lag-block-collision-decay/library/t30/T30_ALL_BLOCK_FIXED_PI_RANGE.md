# T30: an all-block fixed-phase expansion and a growing-width range

Status: `proof sketch`. This note gives a checkable finite proof in prose from
the machine-checked T16, T22, and T24 inputs. The new argument has not been
formalized in Lean. It proves a restricted parameter-range estimate for the
exact all-block quantity at `alpha = pi`; it does not prove the all-parameter
fixed-`pi` square-function premise, any estimate for the decimal digits of
pi, or C1.

## 1. Provenance, normalized scope, and inputs

The canonical problem is the locally formulated question vendored byte for
byte as `CANONICAL_STATEMENT.txt`. It has no original external source URL. Its
SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

That problem asks whether, for every real `0<s<1`, one constant `C_s` works
for all positive integers `m,N` in the ordered long-lag collision estimate

```text
R_pi(m,N) <= C_s [N+N^2 10^(-sm)].                       (1.1)
```

The present note does not estimate `R_pi`. It studies the exact residual
sparse-Fourier square quantity at the fixed phase `alpha=pi`. This is a
conditional frontier related to the canonical statement's recorded sibling
A12, not a replacement for (1.1).

Fix throughout

```text
mu,c in R, Q0,m,N in N,  m>=1, N>=1,
alpha=pi, H=10^m, L=N-m (natural subtraction).           (1.2)
```

No sign or positivity condition is imposed on `mu` or `c`. Arithmetic
exclusions are always retained; they are dropped only when taking an upper
bound on a cardinality. Constants in the new estimate are uniform in
`mu,c,Q0,m,N`.

The only established inputs are these machine-checked modules:

1. T16,
   `TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD`,
   SHA-256
   `4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec`.
2. T22,
   `TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff`,
   SHA-256
   `73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713`.
3. T24,
   `TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction`,
   SHA-256
   `2795d228eab081360e236be14ae99c0dd8267153d39e680710732330ea586924`.

The T27 and T28 notes are unverified `proof sketch` motivation. No claim from
either note is used as a premise. The T25 note is also an unverified `proof
sketch`; it is used only to compare parameter ranges in Section 8.

### Binding conventions and ambiguities

1. The cutoff is strict: a record of endpoint `E` occurs in cutoff `E+1`,
   not cutoff `E`.
2. Both ordered orientations occur. They have opposite, nonzero signed
   frequencies and coefficient one.
3. Every frequency sum is inclusive, `h=1,...,10^m`. Frequency zero is absent
   and `h=10^m` is present.
4. Canonical blocks are T24's half-open blocks in `[1,N)`, aligned on the grid
   translated by one.
5. The width weight is literally `sqrt(b^2-a^2)`, not block length and not
   `sqrt(b-a)`.
6. All fixed-phase statements below concern `alpha=pi`. The universal `pi`
   occurring in `exp(2*pi*i*x)` is part of the character normalization.
7. The restricted range in Section 7 is a condition on the pair `(m,N)`.
   It is not an all-`m,N` assertion and is not promoted to C1.

These choices leave no suppressed orientation, endpoint, or quantifier
convention.

## 2. Exact T22 records and T24 canonical blocks

An ordered T22 record is

```text
q=(epsilon,(r,n)) in Bool x (N x N).                     (2.1)
```

Its lag is `r`, start is `n`, and endpoint is

```text
E(q)=n+r.                                                 (2.2)
```

For the parameters in (1.2), cutoff-independent admissibility is exactly

```text
r>0,  m<=r,
not ArithmeticExcluded mu c Q0 m n r.                   (2.3)
```

The positive core frequency is

```text
k(n,r)=10^(n+r)-10^n=10^n(10^r-1)>0.                   (2.4)
```

The `true` orientation has signed frequency `+k(n,r)` and represents the
ordered exponent pair `(n+r,n)`. The `false` orientation has signed frequency
`-k(n,r)` and represents `(n,n+r)`. Write the signed frequency as `omega(q)`.
T22 proves that `q -> omega(q)` is injective on admissible records and that
every surviving coefficient is one.

Write the nonzero binary digits of `N-1` in strictly decreasing order as

```text
j_1>...>j_t>=0,  N-1=sum_i 2^(j_i).                      (2.5)
```

T24's canonical partition `P(N)` consists of

```text
B_i=[a_i,b_i),
a_i=1+sum_(u<i) 2^(j_u),
b_i=a_i+2^(j_i).                                         (2.6)
```

The blocks are consecutive and disjoint, their union is `[1,N)`, and

```text
1<=a_i<b_i<=N,
b_i-a_i=2^(j_i),
2^(j_i) divides a_i-1.                                   (2.7)
```

For `N=1`, `P(N)` is empty. For every nonempty canonical block `B=[a,b)`, set

```text
w(B)=sqrt(b^2-a^2)=sqrt((b-a)(a+b)).                     (2.8)
```

Since `b-a>=1` and `a+b>=1+2=3`, every canonical block satisfies

```text
w(B)^2>=3,  w(B)>=sqrt(3)>0,  1/w(B)<=1/sqrt(3).         (2.9)
```

This lower bound, including the constant `sqrt(3)`, is the only geometric
weight estimate needed for the new range.

For `B=[a,b)` define the exact record and signed-frequency sets

```text
Q_B={q satisfying (2.3): a<=E(q)<b},
Gamma_B={omega(q):q in Q_B},
M_B=#Q_B=#Gamma_B.                                       (2.10)
```

The cardinality equality is T22 injectivity. Both orientations are included
in `Q_B` and `Gamma_B`.

## 3. Exact block vectors and the all-block quantity

Put

```text
e(x)=exp(2*pi*i*x),
P_K(h,alpha)=cutoffFourierSum mu c Q0 m K h alpha.        (3.1)
```

For `B=[a,b)` define

```text
Delta_B(h;alpha)=P_b(h,alpha)-P_a(h,alpha).              (3.2)
```

T22 coefficient one, its strict cutoff theorem, and T24 endpoint telescoping
give the literal finite identity

```text
Delta_B(h;alpha)=sum_(q in Q_B) e(h omega(q) alpha)
                =sum_(omega in Gamma_B) e(h omega alpha). (3.3)
```

Thus no coefficient multiplicity, endpoint layer, or orientation is hidden
in the notation.

The exact T30 all-block width-weighted quantity is

```text
X_pi(mu,c,Q0;m,N)
 :=sum_(B in P(N)) 1/w(B)
      sum_(h=1)^H |Delta_B(h;pi)|^2,  H=10^m.            (3.4)
```

The sum in (3.4) contains exactly `H` positive frequencies. It contains
`h=H=10^m` and does not contain `h=0`.

## 4. Diagonal and off-diagonal Dirichlet incidences

Define the one-sided Dirichlet kernel and its real part by

```text
D_H(x)=sum_(h=1)^H e(hx),
C_H(x)=Re D_H(x)=sum_(h=1)^H cos(2*pi*h*x).              (4.1)
```

Universally,

```text
D_H(0)=H,  D_H(-x)=conj(D_H(x)),  C_H(-x)=C_H(x).        (4.2)
```

Expanding (3.3), conjugating the second factor, and interchanging finite sums
gives, for every block,

```text
sum_(h=1)^H |Delta_B(h;pi)|^2
 =sum_(q,q' in Q_B) D_H((omega(q)-omega(q'))pi).         (4.3)
```

There are exactly `M_B` diagonal pairs `q=q'`; each contributes `D_H(0)=H`.
For `d>0`, define the ordered positive-difference multiplicity

```text
nu_B(d)=#{(q,q') in Q_B^2: omega(q)-omega(q')=d}.        (4.4)
```

Because the signed frequencies are distinct, every unordered pair has
exactly one ordering with positive difference. Pairing it with the reversed
ordering in (4.3) yields the exact real identity

```text
sum_(h=1)^H |Delta_B(h;pi)|^2
 =H M_B+2 sum_(d>0) nu_B(d) C_H(d pi).                  (4.5)
```

All sums over `d>0` are finite: only differences represented by `Q_B^2`
occur. Combining (3.4) and (4.5) gives the requested exact all-block
diagonal/off-diagonal expansion

```text
X_pi
 =H sum_(B in P(N)) M_B/w(B)
  +2 sum_(B in P(N)) 1/w(B)
       sum_(d>0) nu_B(d) C_H(d pi).                     (4.6)
```

The second term in (4.6) is a signed real sum; individual `C_H(d pi)` may be
negative. Equation (4.6), not its termwise absolute-value majorant, is the
fixed-point cancellation frontier.

## 5. Complete T16 valuation and decimal-shell audit

This section records how every positive difference in (4.4) enters T16. None
of these arithmetic facts is asserted to evaluate `C_H(d pi)`.

### 5.1 Four labeled tokens and both cancellation cases

Represent an ordered record by its ordered orbit exponents `(x,y)`, so that

```text
omega(q)=10^x-10^y,  m<=|x-y|,  0<=x,y<N.               (5.1)
```

If `omega(q)-omega(q')=d>0` and `q'` has exponents `(x',y')`, map the ordered
pair to

```text
Phi(q,q')=(x,y',y,x'),
value(Phi)=10^x+10^y'-10^y-10^x'=d.                    (5.2)
```

The signs in (5.2) are exactly `(+,+,-,-)`. Every exponent is in the
half-open box `0,...,N-1`, and the two weak long-lag conditions are exactly
`m<=|x-y|` and `m<=|x'-y'|`. Labeled coordinates recover both ordered
records, so `Phi` is injective. Hence every block witness is a member of the
exact T16 long-difference domain; arithmetic exclusion merely selects a
subset.

T16 partitions positive four-token witnesses into two disjoint cases.

1. **Noncancelling.** No exponent supports tokens of opposite signs.
   Equal-sign repetitions are allowed.
2. **Cancelling.** At least one positive label equals one negative label.
   There are four possible choices of a labeled positive/negative pair. These
   four cases form a covering and need not be disjoint, because one witness
   may exhibit more than one cancellation. After deleting a selected pair,
   positivity leaves a two-token residual
   `10^u-10^v` with `u>v`; the common cancelled exponent remains a hidden
   element of `0,...,N-1`.

This is exhaustive: a positive four-token value cannot have both residual
tokens cancel as well, since that would give value zero.

### 5.2 Composite-base 10-adic strata

For a positive integer `z`, T16 defines

```text
v_10(z)=padicValNat 10 z,
z_prim=z divMaxPow 10,
10^(v_10(z)) z_prim=z.                                  (5.3)
```

This is the composite-base `divMaxPow` identity. It is not a use of a
prime-base valuation theorem.

For a noncancelling value, let `ell` be the lowest occupied exponent. Its net
coefficient there is one of `+1,+2,-2,-1`, with residues modulo ten
`1,2,8,9`. None is divisible by ten, and T16's
`tenValuation_lowDecimalCoefficient` gives

```text
v_10(d)=ell.                                              (5.4)
```

For a cancelling value, the residual has the unique form

```text
d=10^v(10^r-1),  r>=1,                                  (5.5)
```

and T16's `cancellationValue_ten_reduction` gives exactly

```text
v_10(d)=v,  d_prim=10^r-1.                              (5.6)
```

Thus (5.4) and (5.6) cover every positive difference in (4.4).

The inclusive Fourier variable has its own complete T16 split:

```text
1<=h<=10^m,
v_10(h)<=m,
v_10(h)=m iff h=10^m,
otherwise v_10(h)<m.                                    (5.7)
```

In particular, the endpoint `h=10^m` is a separate, retained stratum. One
may partition every term of (4.3) by the pair of labels

```text
(v_10(h), primitive/cancelling, v_10(d)).                (5.8)
```

No identity `v_10(hd)=v_10(h)+v_10(d)` is used or asserted. Such an identity
is false for the composite base ten in general (primitive factors can supply
separate factors two and five). Keeping the two valuations separate is
therefore essential.

### 5.3 Full ordinary-GCD decimal shells

For positive differences `d,e`, T16 uses

```text
K(d,e)=gcd(d,e)/max(d,e),
R(d,e)=max(d,e)/gcd(d,e).                                (5.9)
```

Here `R(d,e)` is a positive integer and `K(d,e)=1/R(d,e)`. This is the full
ordinary GCD: powers of two, powers of five, odd primes, and cyclotomic
factors are all retained.

The diagonal shell is `R=1`, on which `K=1`. Every nontrivial ratio has the
unique decimal shell

```text
j=floor(log_10(R-1)),
10^j<R<=10^(j+1),
K(d,e)<=10^(-j).                                        (5.10)
```

For a positive noncancelling source with `S` labeled tokens and positive
noncancelling targets with `U` labeled tokens, `1<=S,U<=4`, T16 gives

```text
#(diagonal targets)<=S^U,
#(targets in shell j)<=[2S(S+U-1)(j+2)]^U.              (5.11)
```

Its finite shell series uses

```text
sum_(j=0)^(r-1) (j+2)^4/10^j <=40                       (5.12)
```

for every `r>=0`. Therefore the complete row is at most

```text
R_row(S,U)=S^U+40[2S(S+U-1)]^U.                         (5.13)
```

The exact specializations are

```text
R_row(4,4)=4^4+40*56^4=393380096,
R_row(2,4)=2^4+40*20^4=6400016,
R_row(2,2)=2^2+40*12^2=5764.                            (5.14)
```

A cancelling source has at most `6400016` total kernel weight to primitive
targets. To cancelling targets, the four labeled cancellation choices and
one hidden exponent give

```text
4*N*5764=23056N.                                        (5.15)
```

For reference, define the all-block weighted GCD incidence

```text
G(m,N)=sum_(B,C in P(N)) 1/[w(B)w(C)]
         sum_(d,e>0) nu_B(d)nu_C(e) K(d,e).              (5.16)
```

Equations (5.9)-(5.10) partition (5.16) exactly as

```text
G=G_diag+sum_(j>=0) G_j,                                (5.17)
```

where `G_diag` contains precisely `R(d,e)=1`, and `G_j` contains precisely
`1<R(d,e)`, `floor(log_10(R(d,e)-1))=j`. Only finitely many `G_j` are nonzero.

Images of witnesses from distinct canonical blocks are disjoint: either
record's endpoint recovers its unique block in the half-open partition.
Consequently, for every `d>0`, summing `nu_B(d)` over blocks gives at most
T16's full long-difference multiplicity at `d`. Since the GCD kernel is
nonnegative and `w(B)w(C)>=3`, expanding (5.16), discarding the block labels,
and enlarging both witness families to T16's complete domain gives

```text
G(m,N)<=(574913232/3)N^4=191637744N^4.                  (5.18)
```

The constant `574913232` includes the primitive/primitive, both mixed, and
cancelling/cancelling sectors and all shells. Equation (5.18) is recorded only
to locate the inherited arithmetic scale. It is not the progress claim of
this note. Most importantly, `G` is a GCD resonance incidence, not the
fixed-phase sum (4.6); T16 contains no valid implication from (5.18) to a
bound for `C_H(d pi)`.

## 6. A uniform all-block bound without fixed-point cancellation

We now prove the new estimate directly from (3.3). First count all records in
the canonical blocks. Since the blocks partition `[1,N)`, every record in
their union has endpoint

```text
m<=E=n+r<N.                                              (6.1)
```

For a fixed endpoint `E`, dropping the arithmetic exclusion leaves exactly

```text
n=0,...,E-m,
r=E-n=m,...,E,                                           (6.2)
```

so there are at most `E-m+1` cores and at most `2(E-m+1)` ordered records.
The factor two is exactly the two Bool orientations. If `N<=m`, no endpoint
satisfies (6.1). With natural subtraction `L=N-m`, both cases are summarized
by

```text
sum_(B in P(N)) M_B
 <=2 sum_(u=0)^(L-1) (u+1)
 =L(L+1).                                                (6.3)
```

The equality in (6.3) is the finite identity
`2(1+...+L)=L(L+1)`; for `L=0` both sides are zero.

For every `h`, all summands in (3.3) have complex norm one. Hence

```text
|Delta_B(h;pi)|<=M_B,
sum_(h=1)^H |Delta_B(h;pi)|^2<=H M_B^2.                 (6.4)
```

Using (2.9), (6.3), nonnegativity, and
`sum_B M_B^2<=(sum_B M_B)^2`, we obtain

```text
X_pi
 <=H sum_B M_B^2/w(B)
 <=H/sqrt(3) sum_B M_B^2
 <=H/sqrt(3) (sum_B M_B)^2
 <=H/sqrt(3) [L(L+1)]^2.                                (6.5)
```

This proves the following explicit finite proposition.

**Proposition 6.1 (all-block growing-width majorant).** For every real
`mu,c`, every natural `Q0`, and every positive natural `m,N`, with
`H=10^m` and `L=N-m` in natural subtraction,

```text
X_pi(mu,c,Q0;m,N)
 <=10^m [L(L+1)]^2/sqrt(3).                              (6.6)
```

No Diophantine property of pi, termwise Dirichlet-kernel estimate, GCD bound,
or assertion from an unverified note is used in (6.6). The estimate is valid
at `pi` only because it is valid at every real phase.

## 7. A uniform range with the target constant one

Assume in addition the explicit range condition

```text
[L(L+1)]^2<=N,  L=N-m.                                  (7.1)
```

Since `sqrt(3)>=1`, Proposition 6.1 gives

```text
X_pi(mu,c,Q0;m,N)<=10^m N.                              (7.2)
```

For every real `s` with `0<s<1`, positivity of the exponential factor gives

```text
N<=N+N^2 10^(-sm).                                      (7.3)
```

Combining (7.2)-(7.3) proves:

**Theorem 7.1 (phase-uniform restricted target scale, specialized to pi).** For every real
`mu,c,s`, every natural `Q0,m,N`, if

```text
m>=1, N>=1, 0<s<1,
L=N-m (natural subtraction),
[L(L+1)]^2<=N,                                          (7.4)
```

then the exact all-block quantity satisfies

```text
X_pi(mu,c,Q0;m,N)
 <=10^m [N+N^2 10^(-sm)].                               (7.5)
```

Thus the restricted range has the explicit constant `A=1`, independent of
`mu,c,Q0,s,m,N`. When `N<=m`, `L=0` and the quantity is in fact zero.

## 8. Why this range is strictly beyond bounded width

The T25 note argues, at verification level `proof sketch`, for one latest
endpoint layer in each fixed strip `m<=E<=m+K`, with a constant depending on
the fixed width `K`. T25's one-layer L1 quantity and this note's all-block
weighted L2 quantity are different, so Theorem 7.1 is not called a
strengthening of T25's proposition. The strict comparison required here is
only between parameter ranges: Theorem 7.1 controls the all-block quantity on
pairs whose allowed endpoint width is unbounded.

Indeed, for every integer `t>=1`, take

```text
L=t,
m=[t(t+1)]^2,
N=m+t.                                                   (8.1)
```

Then `N-m=L=t` and

```text
[L(L+1)]^2=m<=N,                                        (8.2)
```

so Theorem 7.1 applies with constant one. The latest possible endpoint is
`E=N-1`, whose distance above `m` is

```text
E-m=t-1 -> infinity.                                    (8.3)
```

Consequently no fixed `K` contains all pairs in (8.1). Equivalently, the
range permits `N-m` of order `N^(1/4)`, whereas a bounded-width strip requires
`N-m=O(1)`. This is the strict improvement in allowed parameter range required
here, not a direct comparison of the two different norm inequalities. It does
not assert that every record at every allowed endpoint survives the arithmetic
exclusion.

## 9. Remaining fixed-point obstruction and terminal status

The exact off-diagonal term left by (4.6) is

```text
Off_pi(m,N)
 :=2 sum_(B in P(N)) 1/w(B)
      sum_(d>0) nu_B(d) C_(10^m)(d pi).                 (9.1)
```

Theorem 7.1 controls (9.1) only indirectly, by the triangle inequality and
only under (7.4). Outside that range, T16's valuation and shell decomposition
controls relationships among the integer differences, but supplies no
fixed-point estimate for the kernels in (9.1). Proving cancellation in
(9.1), or replacing the triangle count in (6.5) by a genuinely fixed-orbit
estimate, remains necessary for an all-parameter result.

The conclusions and their verification levels are:

1. **Proof sketch in this note:** the exact block domain (2.10), all-block
   quantity (3.4), and diagonal/off-diagonal identities (4.3)-(4.6).
2. **Machine-checked imported arithmetic:** T16's complete valuation cases,
   decimal shells, row constants (5.14)-(5.15), and global constant
   `574913232`.
3. **Proof sketch in this note:** the all-parameter majorant (6.6).
4. **Proof sketch in this note:** the target-scale estimate (7.5) on the
   unbounded-width range (7.4), with constant one.
5. **Not claimed:** the all-`m,N` width-weighted premise at `alpha=pi`, any
   fixed-`pi` scale-matched L1 conclusion, any collision estimate, or C1.

Finite evidence is not used. The sole progress claim is the exact growing
parameter range in Theorem 7.1.
