# T28: the cross-block weighted GCD estimate

Status: `proof sketch`. This is a self-contained prose proof built from the
kernel-checked T16, T22, and T24 inputs listed below. The new argument in this
note has not been formalized in Lean. It proves the exact inequality called
`CROSS` in the unverified T27 note and closes the associated
Lebesgue-almost-everywhere square-function sibling. It proves no estimate at
the fixed phase `alpha=pi`, no assertion about the decimal digits of pi, and
no conclusion about C1.

## 1. Provenance and normalized scope

The canonical problem is the locally formulated statement vendored byte for
byte as `CANONICAL_STATEMENT.txt`. It has no original external source URL. Its
SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That canonical problem asks for a collision estimate for the fixed decimal
expansion of pi. This note addresses a sibling arithmetic quantity arising
from the variable-phase Fourier polynomial. The distinction is binding.

Fix throughout

```text
mu,c in R, Q0 in N, and m,N in N with m>=1 and N>=1.
```

The theorem proved below is uniform in all five parameters:

```text
G_(mu,c,Q0;m,N)
  <= 470226400 N^2 log(2N),                              (CROSS)
```

where `log` is the natural logarithm. In particular, the constant is
independent of `mu,c,Q0,m,N`. No sign or positivity condition is imposed on
`mu` or `c`.

The exact kernel-checked inputs are:

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

The T27 note is an unverified `proof sketch`. It supplies only the name
`CROSS` and motivation. No claim from T27 is used as a discharged premise.
All definitions and estimates needed for (CROSS) are reconstructed below.

### Quantifier and convention audit

There is no suppressed quantifier choice in this note:

1. T22's endpoint cutoff is strict: endpoint `E` belongs to cutoff `E+1`
   but not cutoff `E`.
2. Both ordered orientations occur and have opposite nonzero frequencies.
3. T24 blocks are half-open and aligned on the grid translated by one.
4. Every metric frequency sum is inclusive, `1<=h<=10^m`.
5. Arithmetic exclusions are retained. Dropping them is used only for upper
   bounds, never for an equality.
6. The almost-everywhere conclusion fixes `mu,c,Q0` before choosing the
   full-measure phase set. It does not produce one set uniform over all real
   `mu,c`.
7. Every assertion about a random phase is a sibling assertion. It says
   nothing about membership of `pi` in the resulting full-measure set.

## 2. Exact T22 frequency domain

Put

```text
q(n,r)=10^n(10^r-1).
```

The arithmetic exclusion used by T22 is exactly

```text
ArithmeticExcluded mu c Q0 m n r
 iff Q0 <= q(n,r) and
     10^(-m) <= q(n,r) * [c / q(n,r)^mu].                (2.1)
```

The powers and inequality in (2.1) are real after coercing `q(n,r)` to a
real number. T22's cutoff-independent admissibility condition for a core
`(r,n)` is

```text
r>0, m<=r, and not ArithmeticExcluded mu c Q0 m n r.    (2.2)
```

Its endpoint is

```text
E=n+r.                                                   (2.3)
```

The cutoff at `N` adds exactly `E<N`. The positive core frequency is

```text
k(n,r)=10^(n+r)-10^n=10^n(10^r-1)>0.                   (2.4)
```

It is useful to write each ordered record as an ordered pair of orbit
exponents `(x,y)`. The `true` orientation is `(E,n)` and has frequency

```text
omega(x,y)=10^x-10^y=+k(n,r),                           (2.5)
```

while the `false` orientation is `(n,E)` and has frequency `-k(n,r)`.
T22 proves that `omega` is injective on admissible ordered records. Therefore
each surviving signed frequency occurs with coefficient exactly one.

## 3. Exact T24 blocks and weights

Write the nonzero binary digits of `N-1` in decreasing order:

```text
j_1>...>j_t>=0,
N-1=sum_(i=1)^t L_i,  L_i=2^(j_i).                     (3.1)
```

Define

```text
a_i=1+sum_(u<i)L_u,  b_i=a_i+L_i,
B_i=[a_i,b_i).                                          (3.2)
```

These are exactly T24's `canonicalDyadicPartition N`. They are consecutive,
disjoint, and have union `[1,N)`. Every block satisfies

```text
1<=a_i<b_i<=N,
b_i-a_i=2^(j_i),
2^(j_i) divides a_i-1.                                  (3.3)
```

For `N=1`, the partition is empty. The weight of a nonempty block is

```text
w_i=sqrt(b_i^2-a_i^2)
   =sqrt((b_i-a_i)(a_i+b_i)).                            (3.4)
```

In particular,

```text
w_i^2>=1*(1+2)=3, so w_i>1.                              (3.5)
```

Two exact weight facts will be used.

### Lemma 3.1: square-weight telescope

For every `N>=1`,

```text
sum_(i=1)^t w_i^2=N^2-1.                                (3.6)
```

Indeed, `w_i^2=b_i^2-a_i^2`, and consecutiveness gives
`b_i=a_(i+1)`, `a_1=1`, and `b_t=N`. Thus (3.6) is a literal
telescope. This is also T24's endpoint telescope applied to `F(E)=E^2`.

### Lemma 3.2: linear weight budget

For every `N>=1`,

```text
sum_(i=1)^t w_i <= (3/2+sqrt(2))N < 3N.                 (3.7)
```

The assertion is immediate for `N=1`. For `N>=2`, let `L_1` be the first
and largest binary length, and let

```text
R=sum_(i=2)^t L_i=N-1-L_1.
```

Distinctness of the smaller powers gives `0<=R<L_1`, hence `R<N/2`.
The first block is `[1,1+L_1)`, so

```text
w_1=sqrt((L_1+1)^2-1)<=L_1+1=N-R.                      (3.8)
```

For every later block, `b_i<=N`, and consequently

```text
w_i^2=L_i(a_i+b_i)<=2NL_i.                              (3.9)
```

If distinct powers of two sum to `R`, then

```text
sum sqrt(L_i)<=(1+sqrt(2))sqrt(R).                       (3.10)
```

For completeness, remove the largest power `M` and call the remaining sum
`r<M`. Induction reduces (3.10) to

```text
sqrt(M)+(1+sqrt(2))sqrt(r)
  <=(1+sqrt(2))sqrt(M+r).
```

Both sides are nonnegative. Squaring and using
`(1+sqrt(2))^2-1=2(1+sqrt(2))` reduces this to
`sqrt(Mr)<=M`, which follows from `r<=M`.

Combining (3.8)-(3.10), and writing `x=R/N in [0,1/2]`, gives

```text
sum_i w_i
 <=N-R+(2+sqrt(2))sqrt(NR)
 =N[1-x+(2+sqrt(2))sqrt(x)].                            (3.11)
```

The bracket is increasing on `[0,1/2]`: for `0<=x<=y<=1/2`, its
difference is

```text
(sqrt(y)-sqrt(x))[(2+sqrt(2))-(sqrt(y)+sqrt(x))]>=0.
```

At `x=1/2` it equals `3/2+sqrt(2)`, proving (3.7).

### Lemma 3.3: number of canonical blocks

For `N>=2`,

```text
t<=2 log(2N).                                            (3.12)
```

Among all sums of `t` distinct nonnegative powers of two, the smallest is
`1+2+...+2^(t-1)=2^t-1`. Hence `N-1>=2^t-1`, or `N>=2^t`.
Thus `t log 2<=log N`. Finally,

```text
log 2 = integral_1^2 dx/x > 1/2,
```

so `t<2 log N<=2 log(2N)`. We will also use

```text
1<2 log(2N)                                              (3.13)
```

for every `N>=1`, by the same `log 2>1/2` estimate.

## 4. Block frequency sets

For a canonical block `B=[a,b)`, let `Q_B` be the set of all ordered records
`(x,y)` obtained from cores satisfying (2.2) and

```text
a<=max(x,y)=n+r<b.                                       (4.1)
```

Both orientations are included. Define

```text
Gamma_B={omega(x,y):(x,y) in Q_B},
M_B=|Gamma_B|=|Q_B|.                                     (4.2)
```

The equality of cardinalities uses T22 injectivity. At endpoint `E`, there
are at most `E` possible starts: if the endpoint contributes at all, then
`0<=n<=E-m`, whose cardinality is `E-m+1<=E` because `m>=1`.
Arithmetic exclusion can only remove starts. Including both orientations,

```text
M_B
 <=2 sum_(E=a)^(b-1) E
 =(b-a)(a+b-1)
 <(b-a)(a+b)=w(B)^2.                                    (4.3)
```

This is the only cardinality estimate on `Gamma_B` used below. It retains
the factor two for the two ordered orientations.

## 5. T16 decimal valuations and shells

This section records the complete arithmetic input behind the three row
constants used in the proof. It is included to make clear that no prime-base
valuation, omitted decimal shell, or hidden factor is being assumed.

### 5.1 Composite-base 10-adic reduction

For a positive natural number `z`, T16 uses

```text
v_10(z)=padicValNat 10 z,
z_prim=z divMaxPow 10,
10^(v_10(z)) z_prim=z.                                  (5.1)
```

This is the exact `divMaxPow` identity for the composite base ten; it does
not invoke a prime-only valuation theorem.

For the inclusive Fourier range `1<=h<=10^m`, the complete valuation split
is

```text
v_10(h)<=m,
v_10(h)=m iff h=10^m,
otherwise v_10(h)<m.                                    (5.2)
```

The endpoint `h=10^m` is therefore retained rather than silently folded into
the lower-valuation cases.

For a noncancelling form with at most four tokens and signs `(+,+,-,-)`, let
`ell` be its lowest occupied exponent. The net coefficient there is one of
`+1,+2,-2,-1`, whose residues modulo ten are respectively `1,2,8,9`.
None is divisible by ten. Thus T16's exact lowest-coefficient lemma gives

```text
v_10(value)=ell.                                         (5.3)
```

If opposite signs cancel, a positive residual is a two-token value

```text
10^u-10^v=10^v(10^(u-v)-1),  u>v.                       (5.4)
```

Since `10` does not divide `10^(u-v)-1`, its exact reduction is

```text
v_10(10^u-10^v)=v,
primitive part=10^(u-v)-1.                              (5.5)
```

Equations (5.3) and (5.5) are all valuation cases: same-sign repetitions
produce the coefficients `+/-2`, opposite-sign coincidences produce (5.4),
and no other lowest coefficient can occur with four prescribed tokens.

### 5.2 Full reduced-ratio shells

For positive values `x,y`, define

```text
K(x,y)=gcd(x,y)/max(x,y),
H(x,y)=max(x,y)/gcd(x,y).                                (5.6)
```

The quotient `H` is a positive integer and

```text
K(x,y)=1/H(x,y).                                         (5.7)
```

This is the ordinary GCD. It retains all powers of two, five, odd primes,
and cyclotomic factors.

The diagonal shell is `H=1`, on which `K=1`. For `H>1`, T16 assigns the
unique decimal shell

```text
j=floor(log_10(H-1)),
10^j<H<=10^(j+1),
K(x,y)<=10^(-j).                                         (5.8)
```

For a fixed positive noncancelling source with `S` labeled tokens and
positive noncancelling targets with `U` labeled tokens, where
`1<=S,U<=4`, T16's sparse decimal neighbor theorem and (5.3)-(5.5) give

```text
#(diagonal targets)<=S^U,
#(targets in shell j)
  <=[2S(S+U-1)(j+2)]^U.                                 (5.9)
```

The shell proof uses the reduced-ratio multipliers bounded by `10^(j+1)`;
the proximity radius is `(S+U-1)(j+1)`. It therefore covers every shell
`j>=0`, including the diagonal separately.

For `U<=4`, T16 bounds every finite partial shell series by

```text
sum_(j=0)^(r-1) (j+2)^4/10^j <=40 for every r>=0.         (5.10)
```

One explicit domination used there is

```text
(j+2)^4<=21*4^j,
21*4^j/10^j=21*(2/5)^j;
```

the geometric majorant sums to `35`, so the recorded constant `40` is
valid with slack.

Combining (5.8)-(5.10), the row sum over all targets is at most

```text
R(S,U)=S^U+40[2S(S+U-1)]^U.                              (5.11)
```

The three exact constants needed below are therefore

```text
C_44=R(4,4)
    =4^4+40*56^4
    =393380096,

C_24=R(2,4)
    =2^4+40*20^4
    =6400016,

C_22=R(2,2)
    =2^2+40*12^2
    =5764.                                               (5.12)
```

T16 machine-checks the finite statements summarized in (5.1)-(5.12). In its labeled four-token
cancellation domain, a cancelling target is represented by a two-token
residual, one hidden exponent in `0,...,N-1`, and at most four choices of
the cancelled positive/negative labels. Consequently its exact row bounds
are

```text
cancelling source -> primitive targets <=C_24,
cancelling source -> cancelling targets
  <=4N*C_22=23056N.                                     (5.13)
```

The hidden exponent and all four label choices in (5.13) are retained.

## 6. Exact difference witnesses

For `d>0`, define the within-block multiplicity

```text
nu_B(d)=#{(omega,omega') in Gamma_B^2: omega-omega'=d}.  (6.1)
```

Let `D_B` be the set of the ordered pairs counted over all `d>0`. If
`omega=10^x-10^y` and `omega'=10^x'-10^y'`, map the pair to the labeled
T16 four-token vector

```text
Phi(omega,omega')=(x,y',y,x').                           (6.2)
```

The signs of its four coordinates are `(+,+,-,-)`, and its value is

```text
10^x+10^y'-10^y-10^x'
  =omega-omega'=d>0.                                    (6.3)
```

Every exponent in (6.2) lies in `0,...,N-1`, because its record endpoint
lies in `[1,N)`. The two T16 weak long-lag conditions are exactly

```text
m<=|x-y| and m<=|x'-y'|.                                 (6.4)
```

The map `Phi` is injective: its four labeled coordinates recover both
ordered records, and T22 injectivity recovers both signed frequencies.
Images from different canonical blocks are disjoint because either record's
endpoint recovers its unique half-open block.

Since all elements of `Gamma_B` are distinct, every unordered pair of them
has exactly one ordering with positive difference. Hence

```text
|D_B|=binom(M_B,2).                                      (6.5)
```

Partition `D_B` into

```text
P_B={u in D_B: Phi(u) is noncancelling},
C_B={u in D_B: Phi(u) is cancelling}.                    (6.6)
```

Here `C_B` denotes cancelling witnesses, not the frequency cardinality
`M_B`.

### Lemma 6.1: total and cancelling witness counts

For every block,

```text
|P_B|+|C_B|=binom(M_B,2)<=w(B)^4/2,                      (6.7)
|C_B|<=N M_B<N w(B)^2.                                   (6.8)
```

Equation (6.7) follows from (4.3) and (6.5). For (6.8), observe from (6.2)
that an opposite-sign cancellation can only be

```text
x=x' or y=y'.                                            (6.9)
```

The other two possible opposite-sign equalities, `x=y` and `y'=x'`, are
impossible because both record lags are positive. For a fixed record
`(x,y)`, there are at most `N-1` other records sharing `x` and at most
`N-1` sharing `y`. A different record cannot share both coordinates.
Therefore the number of ordered cancellation incidences is at most
`2(N-1)M_B`. Each unordered pair is counted twice, and exactly one of its
two orders is the positive witness in `D_B`. Thus

```text
|C_B|<=(N-1)M_B<=N M_B,
```

which proves (6.8). This is the width-sensitive count lost in the global
`N^4` estimate.

## 7. The exact cross-block quantity

Define

```text
G_(mu,c,Q0;m,N)
 =sum_(B,C in P(N)) 1/[w(B)w(C)]
    sum_(d,e>0) nu_B(d)nu_C(e)
      gcd(d,e)/max(d,e).                                 (7.1)
```

All sums are finite. Grouping the fibers in (6.1), then applying the
injective map (6.2), gives the exact witness expansion

```text
G=sum_(B,C) sum_(u in D_B,v in D_C)
     K(value(Phi(u)),value(Phi(v)))/[w(B)w(C)].           (7.2)
```

No inequality has yet been used in (7.2). We now split it into the
primitive-primitive, two mixed, and cancelling-cancelling sectors.

### 7.1 Primitive-primitive sector

Write `a_u=1/w(B)` for `u in D_B`. For positive weights,

```text
a_u a_v<=(a_u^2+a_v^2)/2.                               (7.3)
```

The GCD kernel is symmetric. For each primitive source witness, the target
primitive witnesses form a subset of T16's complete primitive target domain,
so (5.12) bounds its row by `C_44`. Symmetrizing with (7.3),

```text
G_PP
 <=C_44 sum_B |P_B|/w(B)^2
 <=(C_44/2) sum_B w(B)^2
 =(C_44/2)(N^2-1).                                      (7.4)
```

The second line uses (6.7), and the last uses (3.6).

### 7.2 Mixed sectors

Fix a cancelling source witness. Its row to every primitive target in the
box is at most `C_24` by (5.13). Also every target weight satisfies
`1/w(B)<1` by (3.5). Therefore one mixed orientation obeys

```text
G_CP
 <=C_24 sum_B |C_B|/w(B)
 <=C_24 N sum_B w(B)
 <=3 C_24 N^2.                                          (7.5)
```

The second inequality is (6.8), and the third is (3.7). Kernel and weight
symmetry show that the other mixed orientation has the same value. Hence

```text
G_CP+G_PC<=6 C_24 N^2.                                  (7.6)
```

There is no omitted orientation factor: (7.6) explicitly includes both.

### 7.3 Cancelling-cancelling sector

For each cancelling source, (5.13) bounds its complete cancelling row by
`23056N`. Applying the same symmetrization (7.3), then (6.8), gives

```text
G_CC
 <=23056N sum_B |C_B|/w(B)^2
 <=23056N^2 t
 <=46112N^2 log(2N).                                    (7.7)
```

The final inequality is Lemma 3.3. Thus the sole logarithm records the
number of nonzero binary digits of `N-1`; it does not come from the decimal
shell series, which was summed absolutely in (5.10).

## 8. Proof of CROSS with an explicit constant

For `N=1`, the canonical partition is empty and `G=0`. Suppose `N>=2`.
By (3.13), `1<=2log(2N)`. Equations (7.4), (7.6), and (7.7) imply

```text
G_PP <= C_44 N^2 log(2N),
G_CP+G_PC <=12 C_24 N^2 log(2N),
G_CC <=46112 N^2 log(2N).                               (8.1)
```

Substituting (5.12),

```text
C_44+12C_24+46112
 =393380096+12*6400016+46112
 =470226400.                                             (8.2)
```

Adding the disjoint sectors proves, for every real `mu,c`, every natural
`Q0`, and all positive natural `m,N`,

```text
G_(mu,c,Q0;m,N)
  <=470226400 N^2 log(2N).                               (8.3)
```

This is `CROSS` with the absolute constant

```text
K=470226400.                                             (8.4)
```

The proof retained all arithmetic exclusions. Since they only select a
subset of the full T16 target boxes, the row bounds are uniform in their
values and hence in `mu,c,Q0,m`.

## 9. Exact random-phase moments

We now complete the metric sibling argument. Fix `mu,c,Q0` and let
`alpha` be Lebesgue-uniform on `[0,1)`. Put

```text
H_m=10^m,
e(z)=exp(2*pi*i*z),
Delta_B(h,alpha)=sum_(omega in Gamma_B)e(h omega alpha),

X_(m,N)(alpha)
 =sum_(B in P(N)) 1/w(B)
    sum_(h=1)^H_m |Delta_B(h,alpha)|^2.                  (9.1)
```

The symbol `pi` inside `e(z)` is the universal circle constant, not the
phase being tested. The frequency range in (9.1) is inclusive; `h=0` is
absent and `h=10^m` is present.

Integer-character orthogonality on `[0,1)` and T22 injectivity give, for
every `1<=h<=H_m`,

```text
integral |Delta_B(h,alpha)|^2 d alpha=M_B.               (9.2)
```

Consequently, by (4.3) and (3.7),

```text
E X_(m,N)
 =H_m sum_B M_B/w(B)
 <=H_m sum_B w(B)
 <=3H_m N.                                               (9.3)
```

Define the centered block energy

```text
Z_B=sum_(h=1)^H_m |Delta_B(h,alpha)|^2-H_m M_B.          (9.4)
```

For positive `d,e`, the number of positive integer pairs `h,k<=H_m`
satisfying `hd=ke` is exactly

```text
floor(H_m gcd(d,e)/max(d,e)).                            (9.5)
```

Indeed, after writing `d=g d_0`, `e=g e_0` with coprime `d_0,e_0`, every
solution is `h=e_0 ell`, `k=d_0 ell`. In the product `Z_B Z_C`, the two
opposite-sign character equations survive and the two same-sign equations
cannot vanish. Hence the exact covariance is

```text
integral Z_B Z_C d alpha
 =2 sum_(d,e>0) nu_B(d)nu_C(e)
    floor(H_m gcd(d,e)/max(d,e)).                        (9.6)
```

It follows from (7.1), `floor(x)<=x`, and (8.3) that

```text
Var X_(m,N)
 <=2H_m G_(m,N)
 <=940452800 H_m N^2 log(2N).                           (9.7)
```

No independence or covariance cancellation is used; all covariances in
(9.6) are nonnegative.

## 10. Borel-Cantelli closure

Fix a real `s` with `0<s<1`, and write

```text
rho=10^(-sm),
T_s(m,N)=N+N^2 rho=N(1+rho N).                           (10.1)
```

By (9.3), `E X<=3H_m T_s`. Therefore the event

```text
X_(m,N)>4H_m T_s(m,N)                                   (10.2)
```

forces `X-E X>H_m T_s`. Chebyshev's inequality and (9.7) give

```text
lambda{X_(m,N)>4H_m T_s(m,N)}
 <=2K log(2N)/[H_m(1+rho N)^2],                          (10.3)
```

where `K=470226400`.

We record the full summation estimate. For `0<rho<=1`, let
`M=ceil(1/rho)`. Then `M<=2/rho`, and

```text
sum_(N=1)^M log(2N)/(1+rho N)^2
 <=(2/rho)log(4/rho).                                   (10.4)
```

The function `log(2x)/x^2` is decreasing for `x>=1`, because its derivative
is `[1-2log(2x)]/x^3<0`. Thus

```text
sum_(N=M+1)^infinity log(2N)/(1+rho N)^2
 <=rho^(-2) integral_M^infinity log(2x)/x^2 dx
 =rho^(-2)[log(2M)+1]/M
 <=rho^(-1)[log(4/rho)+1].                              (10.5)
```

Since `log(4/rho)>1`, (10.4)-(10.5) imply

```text
sum_(N>=1) log(2N)/(1+rho N)^2
 <=(4/rho)log(4/rho).                                   (10.6)
```

Substituting `H_m=10^m` and `rho=10^(-sm)` into (10.3) and (10.6),

```text
sum_(m,N>=1) lambda{X_(m,N)>4H_m T_s(m,N)}
 <=8K sum_(m>=1) 10^(-(1-s)m)
      [log 4+s m log 10]
 <infinity.                                              (10.7)
```

The final series is a geometric series plus its first-moment series, with
ratio `10^{-(1-s)}<1`.

Each `X_(m,N)` is a finite sum of continuous trigonometric functions and is
measurable. The first Borel-Cantelli lemma, requiring no independence, now
shows that for almost every `alpha`, only finitely many pairs `(m,N)` violate
(10.2). If `F_s(alpha)` is that finite set, define

```text
A_s(alpha)=max(4,
  max_((m,N) in F_s(alpha))
    X_(m,N)(alpha)/[H_m T_s(m,N)]),                      (10.8)
```

with the inner maximum interpreted as zero when `F_s(alpha)` is empty. All
denominators are positive. Thus, for this fixed `s`, almost every `alpha`
satisfies

```text
X_(m,N)(alpha)<=A_s(alpha)H_m T_s(m,N)
for every m,N>=1.                                        (10.9)
```

Finally intersect the full-measure sets furnished by (10.9) over rational
`t in (0,1)`. Given any real `0<s<1`, choose rational `s<t<1`. Since

```text
T_t(m,N)<=T_s(m,N),                                      (10.10)
```

the bound at `t` implies the bound at `s`, using `A_s=A_t`. We have proved:

```text
For every fixed mu,c in R and Q0 in N, for Lebesgue-almost every
alpha in [0,1), and simultaneously for every real 0<s<1,
there is a finite A_s(alpha)>=0 such that for all m,N>=1,

  X_(m,N)(alpha)
    <=A_s(alpha) 10^m [N+N^2 10^(-sm)].                 (10.11)
```

This is the almost-everywhere compatibility of the exact width-weighted
square-function sibling.

## 11. Deterministic consequence and claim boundary

For completeness, let

```text
P_N(h,alpha)=cutoffFourierSum mu c Q0 m N h alpha.
```

T22's strict successor layer and T24's endpoint telescope identify the block
increment with `Delta_B` from (9.1) and give the exact identity

```text
P_N(h,alpha)=sum_(B in P(N)) Delta_B(h,alpha)             (11.1)
```

for `m,N>=1`; at `N=1` both sides are zero. The same weights have the
deterministic budget

```text
sum_B w(B)<3N.                                           (11.2)
```

Weighted Cauchy-Schwarz applied to the exact T24 block telescope gives

```text
[sum_(h=1)^H_m |P_N(h,alpha)|]^2
 <=H_m [sum_B w(B)] X_(m,N)(alpha).                      (11.3)
```

Combining (10.11), (11.2), and `N<=T_s(m,N)` yields, for almost every random
phase and each `s`,

```text
sum_(h=1)^H_m |P_N(h,alpha)|
 <=sqrt(3A_s(alpha)) H_m T_s(m,N).                       (11.4)
```

Equation (11.4) is a random-phase sibling statement. Although T22 identifies
`P_N(h,pi)` with the fixed spectral sum, no argument here proves that
`alpha=pi` belongs to the full-measure set in (10.11). Accordingly:

1. This note states no estimate for `P_N(h,pi)`.
2. This note states no estimate for decimal blocks of pi.
3. This note states no conclusion about C1.
4. The proved research claim has artifact verification level `proof sketch`,
   not `machine-checked`.

The substantive resolution of T28 is (8.3): the exact cross-block quantity
does satisfy `CROSS`, with explicit absolute constant `470226400`, and this
is sufficient for the complete almost-everywhere sibling closure in
(10.11).
