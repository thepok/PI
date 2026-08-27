# T63: finite AOC_4 data do not control the signed short-sector frontier

Status: `proof sketch` plus a replay-checked `experiment`.

## 0. Provenance, scope, and nonclaims

- Canonical statement: `pi-positive-decimal-factor-entropy.txt` in this
  artifact set.
- Canonical SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Original external source URL: none. The canonical question was formulated
  locally on 2026-07-22.
- The exact long-lag T43 source is vendored as
  `T43_AVERAGED_ORBIT_CORRELATION.md`, SHA-256
  `7b71b5f9dc7003f0d2d47861ad399db88a0ffaf920d669a97fda092df407afed`.
  It was recovered from the hash-addressed proof-ledger store after its
  original workflow record disappeared. T43 labels itself a `proof sketch`
  and `(AOC_4)` a `conjecture`. Nothing from it is treated as proved.
- The vendored T56, T58, and T61 Lean modules are `machine-checked`. T56 fixes
  the short rectangle, T58 checks its frequency map and collision expansion,
  and T61 checks the Vaaler polynomial, its endpoints, its complete expansion,
  and the conditional chain. None constructs a fixed-pi short-sector bound.
  Their respective SHA-256 values are
  `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc`,
  `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d`,
  and `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993`.
- The separation below is an arbitrary-phase finite model. It is not a
  counterexample to `(AOC_4)` at pi, not evidence against `(AOC_4)` at pi,
  and not a counterexample to T61's premise at pi.
- No instance of `(AOC_4)`, C7, C2, C1, or positive decimal factor entropy of
  pi is asserted. Every implication to those statements remains conditional.

The result is therefore:

> **INSUFFICIENT AT THE FINITE INTERFACE.** The centered AOC_4 bound does not
> yield T61's signed structured-denominator premise merely through the
> displayed finite ranges and weights. A scale-dependent finite phase family
> separates those inequalities. It does not decide whether the two fixed-pi
> predicates have an implication using additional arithmetic structure. The
> exact missing inequality is `(COV_63)` in Section 7.

## 1. Normalized canonical target and quantifier cautions

For the unique nonterminating decimal expansion

```text
pi = 3.d_1 d_2 d_3 ...,
```

let `p_pi(n)` be the number of length-`n` contiguous decimal factors. The
canonical open question is whether

```text
exists eta>0, exists N>=1, forall n>=N,
  p_pi(n) >= 10^(eta*n).
```

The following quantifiers must not be conflated.

1. In `(AOC_4)`, `Qstar` and `s` are fixed before its constant; the same
   constant then works for every positive pair `(m,N)`.
2. T61 fixes `(mu,c,Q0)` before choosing its eventual constant and cutoff.
3. T56's `n` is simultaneously decimal resolution and the short-lag cutoff.
   T43's `m` has that role only after the specialization `m=n`.
4. T43's capital `N` is a block endpoint. It becomes T56's sample length,
   not T56's bandwidth.
5. The finite separation assigns one phase to each label. It does not assert
   that all phases arise as `(10^k-10^v)*pi` from one common real number.

## 2. Literal finite AOC_4 predicate, restated from scratch

All definitions in this section are finite. Let `m,N` be natural numbers with
`m>=1` and `N>=1`.

### 2.1 Canonical blocks and width

Let

```text
B_N = dyadicPartitionFrom 0 ((N-1).bitIndices.reverse).
```

These are consecutive half-open integer blocks covering `[1,N)`. For
`1<=k<N`, write its unique block as

```text
B_N(k) = [a_N(k),b_N(k)),
W_N(k) = sqrt(b_N(k)^2-a_N(k)^2).
```

Thus

```text
1 <= a_N(k) <= k < b_N(k) <= N,  W_N(k)>0.
```

No asymptotic replacement of `W_N(k)` is part of `(AOC_4)`.

### 2.2 Geometric coefficient and onset set

For an integer `x`, put `[x]_+=max(x,0)`. For `0<=v<k<N`, define

```text
Lambda_(m,N)(v,k)
 = 1_(a_N(k)<=v<b_N(k)) [v-m+1]_+
   + [min(b_N(k),k-m+1)-max(a_N(k),v+m)]_+.
```

The second term is the cardinality of the half-open integer interval

```text
[max(a_N(k),v+m), min(b_N(k),k-m+1)).
```

For a natural `Qstar`, define

```text
V_(Qstar)(k)
 = {v : 0<=v<k and Qstar<=10^k-10^v},

g_(m,N)(v,k) = Lambda_(m,N)(v,k)/W_N(k),

G_(Qstar,m,N)(k)
 = sum_(v in V_(Qstar)(k)) g_(m,N)(v,k).
```

All `g` are nonnegative. The bound `G<k` used later is rederived in Section
5.2 rather than imported from the sketch-level T43 note.

### 2.3 Endpoint-pinned shells

For a real `x`, let

```text
delta(x)=|x-round(x)|,
K_m=clog_2(10^m)-1.
```

The shells are exactly

```text
S_0(m,x): 0<=delta(x)<=10^(-m),

S_j(m,x): 2^(j-1)/10^m < delta(x)
            <= min(2^j/10^m,1/2),  1<=j<=K_m.
```

The lower endpoint of every positive shell is open and its upper endpoint is
closed. The cap `1/2` is included. Define

```text
theta_m(d)
 = 1_(S_0(m,d*pi))
   + sum_(j=1)^K_m 2^(-j) 1_(S_j(m,d*pi)).
```

Exactly one shell is active, so `0<theta_m(d)<=1`. The shell-zero weight is
`1`; shell `j` has weight exactly `2^(-j)`.

### 2.4 Active range and centered statistics

Call `k` active when

```text
1<=k<N,  5m<31k,  and G_(Qstar,m,N)(k)>0.
```

The supercritical cutoff is strict. For active `k`, put

```text
n_k = card(V_(Qstar)(k)),
t_v = theta_m(10^k-10^v),
p_v = g_(m,N)(v,k)/G_(Qstar,m,N)(k),

mu_k  = (1/n_k) sum_v t_v,
Var_k = (1/n_k) sum_v (t_v-mu_k)^2,
Xi_k  = n_k sum_v (p_v-1/n_k)^2.
```

All sums here are over `v in V_(Qstar)(k)`. The `p_v` sum to one. There is an
exact centered identity and finite Cauchy-Schwarz bound:

```text
sum_v p_v t_v
 = mu_k + sum_v (p_v-1/n_k)(t_v-mu_k),

|sum_v (p_v-1/n_k)(t_v-mu_k)|
 <= sqrt(Xi_k Var_k).
```

### 2.5 Literal AOC_4

The predicate is:

```text
forall Qstar : Nat, forall s : Real with 0<s<1,
  exists C_(s,Qstar)>=0, forall m,N : Nat with m>=1 and N>=1,

  2 * sum_(1<=k<N; 5m<31k; G_(Qstar,m,N)(k)>0)
        G_(Qstar,m,N)(k) [mu_k+sqrt(Xi_k Var_k)]

  <= C_(s,Qstar) [N+N^2*10^(-s*m)].                 (AOC_4)
```

The factor `2`, both terms in the target, and every normalization above are
literal. There is no Vaaler frequency `h`, no T56 bandwidth, no arithmetic
mask `Q0`, and no T61 coefficient in `(AOC_4)`.

## 3. Literal T61 signed premise, restated from scratch

For every natural `n`, define

```text
L_n = 10^(n/2),       with natural-number division,
H_n = 10^n/2,         with natural-number division.
```

For fixed reals `mu,c` and a natural `Q0`, the residual T56 short rectangle is

```text
R_n(mu,c,Q0)
 = {(r,j) : 0<r<n,
              0<=j<L_n-r,
              not ArithmeticExcluded(mu,c,Q0,n,j,r)}.
```

Every endpoint is half-open. Put

```text
d_(j,r)=10^j(10^r-1).
```

For `H>=2` and `1<=h<H`, T61's coefficient is

```text
c_H(h)
 = H^(-1) [sin(pi*h/H)/pi
            + 2(1-h/H)cos(pi*h/H)].
```

These coefficients are signed rather than replaced by absolute values. The
strict cutoff is `h<H`; the coefficient at `h=H` is absent. T61's periodic
majorant is

```text
M_H(x)
 = 2/H + 2 sum_(1<=h<H) c_H(h) cos(2*pi*h*x).
```

T61 machine-checks that `M_H(x)>=0` and that it majorizes the strict indicator

```text
1_(circleDistance(x)<1/(2H)).
```

At the two endpoints `x=+/-1/(2H)`, the strict indicator is zero while
`M_H(x)=1`. For `n>=1`, T61 also machine-checks

```text
1/(2H_n)=10^(-n).
```

The complete finite expression is

```text
E_n(mu,c,Q0)
 = sum_((r,j) in R_n(mu,c,Q0)) M_(H_n)(d_(j,r)*pi)

 = [2/H_n] card(R_n(mu,c,Q0))
   + 2 sum_(1<=h<H_n) c_(H_n)(h)
       sum_((r,j) in R_n(mu,c,Q0))
         cos(2*pi*h*(d_(j,r)*pi)).
```

T61's `SignedStructuredDenominatorPremise(mu,c,Q0)` is exactly

```text
exists B>0, exists N0>=1, forall n>=N0,
  E_n(mu,c,Q0) <= B*L_n.                            (T61-SD)
```

It is called signed because the nonzero Fourier coefficients and cosines in
the second line are signed. The bounded object `E_n` itself is nonnegative.
No division by `H_n L_n` occurs in `(T61-SD)`.

## 4. Complete parameter-and-weight crosswalk

Specialize `(AOC_4)` by

```text
Qstar=0,  s=3/4,  m=n,  N=L_n.
```

For a T56 label `(r,j)`, set

```text
v=j,  k=j+r,  rho=r.
```

Then the following identities and differences are exact.

| Object | AOC_4 | T56/T61 | Crosswalk or mismatch |
|---|---|---|---|
| Decimal scale | `m` | `n` | `m=n` |
| Block endpoint/sample length | `N` | `L_n=10^(n/2)` | `N=L_n` |
| Bandwidth | none | `H_n=10^n/2` | absent from AOC_4 |
| Start | `v` | `j` | `v=j` |
| Endpoint | `k` | `j+r` | `k=j+r` |
| Lag | `rho=k-v` | `r` | `rho=r` |
| Label endpoint | `0<=v<k<N` | `0<r<n`, `j<L_n-r` | T61 is the subrange `1<=k-v<n` |
| Structured denominator | `10^k-10^v` | `10^j(10^r-1)` | exactly equal |
| Onset | `Qstar<=10^k-10^v` | none beyond the residual mask | automatic at `Qstar=0` |
| Supercritical cutoff | `5n<31k` | none | AOC_4 omits the complementary `k` range |
| Arithmetic mask | none | `not ArithmeticExcluded(mu,c,Q0,n,j,r)` | absent from AOC_4 |
| Canonical weight | `g=Lambda/W` | uniform label weight `1` | not equal |
| Fixed orbit profile | `theta_n(10^k-10^v)` | `M_(H_n)((10^k-10^v)*pi)` | different kernels |
| Frequency | none | `1<=h<H_n` | entire signed frequency band absent from AOC_4 |
| Fourier weight | none | `c_(H_n)(h)` | signed and absent from AOC_4 |
| Shell endpoints | closed zero shell; positive shells open below, closed above | strict central indicator, endpoints excluded | T61 majorant equals `1` at strict endpoints |
| Centering | uniform mean over `V_0(k)`, chi-square against `g/G` | none | does not center the residual selector |
| Outer normalization | unnormalized left side, target `L_n+L_n^2*10^(-3n/4)` | target `B L_n` | for `n>=2`, the AOC target is at most `2L_n` |

Indeed, for `n>=2`,

```text
L_n^2*10^(-3n/4) <= L_n.
```

Thus `(AOC_4)` at this specialization would give an `O(L_n)` bound for its
own geometrically weighted shell envelope. It does not identify that envelope
with T61's uniformly counted Vaaler total.

## 5. Replay-checked finite phase family

This section works in a scale-dependent arbitrary-phase finite model only. It retains the
literal scales, blocks, `Lambda/W` weights, shells, T56 short labels, and T61
majorant evaluation points. It replaces the common fixed phase pi by a phase
array `x_(n;k,v)` which may change with `n`. That replacement is precisely why
this is neither a pi-specific counterexample nor a model of the literal
all-scale common-phase predicate.

Take `n` divisible by `4`, `n>=16`, and put

```text
N=L_n=10^(n/2),  H=H_n=10^n/2.
```

Let `B` be the largest power of two with `B<=N-1`. The first canonical block
is exactly

```text
[1,B+1),  W=sqrt(B^2+2B),  (N-1)/2 < B <= N-1.
```

Let

```text
a=ceil(sqrt(n)),  K=floor(B/a).
```

Select the labels

```text
S_n = {(k,v) : 6n<=k<=K,
                 v=k-r for some 1<=r<n}.
```

There are exactly `(n-1)(K-6n+1)` selected labels. Assign

```text
x_(k,v)=0       on S_n,
x_(k,v)=1/2     on every other 0<=v<k<N.
```

Take every T56 arithmetic mask to be one in this abstract model.

### 5.1 Exact shells

At phase zero, the label is in `S_0` and has shell weight `1`. At phase
`1/2`, the label lies at the included upper endpoint of terminal shell `K_n`
and has weight

```text
tau_n=2^(-K_n),  10^(-n)<tau_n<=2*10^(-n)=1/H.
```

For a selected `k`, there are `q=n-1` entries of value `1` and `k-q` entries
of value `tau_n`. Therefore

```text
mu_k <= tau_n + q/k,
Var_k <= q/k <= n/k.                                  (5.1)
```

For an unselected `k`, all shell values equal `tau_n`, so `Var_k=0`.

### 5.2 Exact first-block geometry

For `k` in the selected interval and every `0<=v<k`, direct substitution into
the literal `Lambda` formula gives

```text
Lambda_(n,N)(v,k)
 = 1_(v>=n)(v-n+1) + [k-2n+1-v]_+.                    (5.2)
```

Since `k>=6n`, every value in (5.2) lies between

```text
k-3n+2  and  k-n.
```

Its range is at most `2n`. If `S=sum_v Lambda(v,k)`, then

```text
S >= k(k-3n+2) >= k^2/2,
G_k=S/W <= k^2/B.                                      (5.3)
```

The width cancels from the normalized probabilities `p_v`. Popoviciu's
finite variance bound applied to the interval of length at most `2n` yields

```text
Xi_k
 = k sum_v (Lambda(v,k)/S-1/k)^2
 <= 4n^2/k^2.                                          (5.4)
```

Combining (5.1), (5.3), and (5.4),

```text
G_k[mu_k+sqrt(Xi_k Var_k)]
 <= (k^2/B)[tau_n+n/k+2n^(3/2)/k^(3/2)].               (5.5)
```

For all unselected `k`, the geometric inequality `G_k<k` gives contribution
at most `tau_n k`. For completeness, that inequality follows directly from
the displayed definitions. If `B_N(k)=[a,a+ell)` and `d=k-a`, then
`Lambda_(m,N)<=Lambda_(1,N)` and direct evaluation gives

```text
sum_(v<k) Lambda_(1,N)(v,k)=d(2a+d-1).
```

The function `x(2a+x)/(a+x)` is increasing for `x>=0`; using `d<ell` and
`W^2=ell(2a+ell)` gives `d(2a+d)<kW`. Onset restriction can only reduce the
sum, so `0<=G_k<k`. This repeats the finite argument and does not assume the
T43 note's claim.

### 5.3 AOC-sized upper bound

Summing the sharper `q=n-1` form behind (5.5), using
`K<=B/sqrt(n)`, and including AOC_4's outer factor two, gives

```text
AOC_lhs
 <= tau_n N^2 + nK^2/B + 4n^(3/2)K^(3/2)/B
 <= 2 + B + 4n^(3/4)sqrt(B).                            (5.6)
```

The right side is `O(N)`. Thus, at each displayed finite scale and
`Qstar=0`, the AOC_4 left side is at most a fixed multiple of its literal
`s=3/4` target. No claim is made that assignments at different scales come
from one common phase or jointly satisfy the all-scale AOC_4 predicate.

### 5.4 T61 lower bound

At every selected label, `x=0`. T61's kernel-checked majorization gives

```text
M_H(0)>=1.
```

All other complete-majorant values are nonnegative. Hence the complete T61
total in this model is at least

```text
(n-1)(K-6n+1).                                          (5.8)
```

Since `B>(N-1)/2` and `a<=sqrt(n)+1`,

```text
(n-1)(K-6n+1)/N -> infinity                            (5.9)
```

along this sequence of finite phase families; quantitatively its main term is
at least approximately `sqrt(n)/2`. Thus no fixed multiple of `L_n=N` bounds
the complete T61 total in this phase family.

The signed positive-frequency part has the same divergence. The full short
rectangle contains

```text
(n-1)N - n(n-1)/2
```

labels, so removing its exact zero mode costs only

```text
[2/H][(n-1)N-n(n-1)/2]=o(N).
```

For every proposed finite comparison constant, one sufficiently large `n`
therefore gives a finite phase family with AOC-sized centered envelope and a
larger T61-to-`L_n` ratio. This proves only an arbitrary-phase finite-interface
separation, not a statement about the arithmetic phases generated by pi.

## 6. What AOC_4 and T58 each omit

The separation has three visible sources.

1. AOC_4 weights labels by `Lambda/W`; T61 counts each surviving short label
   with weight one.
2. AOC_4 centers `theta_n` against `g/G` over every `v<k`; it does not center
   the short-lag arithmetic selector against those weights.
3. AOC_4 contains no Vaaler multiplier `h` or signed coefficient `c_H(h)`.

T58's kernel-checked rectangle and frequency-collision identities do not fill
these gaps. Its prose rectangle estimate remains an unproved fixed-pi premise,
and variable-phase orthogonality does not evaluate one fixed phase.

## 7. Exact missing covariance hypothesis

This section states one exact sufficient repair without hiding any mismatch.
It is not asserted for pi.

Fix `(mu,c,Q0)`. At scale `n`, put `L=L_n`, `H=H_n`. For `1<=k<L` and
`0<=v<k`, define

```text
d_(k,v)=10^k-10^v,
t_(k,v)=theta_n(d_(k,v)),
y_(k,v)=M_H(d_(k,v)*pi),

epsilon_(k,v)
 = 1_(1<=k-v<n and
       not ArithmeticExcluded(mu,c,Q0,n,v,k-v)).
```

Let the AOC weight, extended by zero off its active range, be

```text
w_(k,v)
 = 1_(5n<31k and G_(0,n,L)(k)>0)
     Lambda_(n,L)(v,k)/W_L(k).
```

Put

```text
J_k=sum_(v<k) epsilon_(k,v),
A_k=sum_(v<k) w_(k,v),
ybar_k=(1/k)sum_(v<k)y_(k,v).
```

Define the exact cross-weight covariance defect

```text
D_k
 = (J_k-A_k)ybar_k

   + sum_(v<k)
       [(epsilon_(k,v)-J_k/k)-(w_(k,v)-A_k/k)]
       [y_(k,v)-ybar_k]

   + sum_(v<k) w_(k,v)[y_(k,v)-t_(k,v)].                (7.1)
```

There is no estimate in (7.1). It is an algebraic definition. Expanding the
centered sums gives the exact identity

```text
sum_(v<k) epsilon_(k,v)y_(k,v)
 = sum_(v<k) w_(k,v)t_(k,v) + D_k.                      (7.2)
```

The precise additional hypothesis is

```text
(COV_63)

exists D>=0, exists N0>=1, forall n>=N0,
  sum_(1<=k<L_n) D_k <= D*L_n.                           (7.3)
```

This is the missing covariance information in exact variables. Algebraically,
it is exactly the entire residual between the two finite totals, so (7.3) is a
transparent sufficient hypothesis rather than an independently established
estimate. Its first term measures total-mass mismatch between the residual short selector and T43's
geometric weight. Its second term is the centered covariance mismatch. Its
third term measures the kernel/frequency mismatch between the full Vaaler
response and the shell profile. The zero extension of `w` includes the
subcritical and `G=0` labels rather than silently discarding them.

Neither `(AOC_4)` nor T58's rectangle identity bounds (7.3).

Conversely, `(AOC_4)+(COV_63)` conditionally implies T61's premise. Choose
`Qstar=0`, `s=3/4`, `m=n`, and `N=L_n`. By finite Cauchy-Schwarz in AOC_4,

```text
2 sum_(k,v) w_(k,v)t_(k,v)
 <= AOC_lhs
 <= C_(3/4,0)[L_n+L_n^2*10^(-3n/4)]
 <= 2C_(3/4,0)L_n
```

for `n>=2`. Summing (7.2) and applying (7.3) gives

```text
E_n(mu,c,Q0)
 <= [C_(3/4,0)+D]L_n.
```

If the bracket is zero, replace it by any positive larger constant to match
T61's strict `B>0` convention. This is a valid conditional implication only;
neither premise is supplied here.

## 8. Replay

From a directory containing only these delivered artifacts, run

```sh
./verify.sh
```

The script first verifies every file hash, then runs

```sh
python3 t63_replay.py --write OUTPUT.json
cmp OUTPUT.json replay_expected.json
```

`t63_replay.py` uses only integers and `fractions.Fraction` for all decisions.
Displayed decimals are rounded only after the exact inequalities pass. It
checks scales `n=16,64,256,1024`; the complete T61 lower ratios are respectively

```text
2.516568150000,
6.388959025150,
13.809194765641,
18.018485481339,
```

while the certified AOC_4 constants at `s=3/4` remain below `1` at those
scales. These finite values are an `experiment`; the unbounded sequence of
finite comparison ratios is the algebraic argument in Section 5.

## 9. Conditional conclusion

The finite interfaces alone do not provide a derivation of

```text
AOC_4 => SignedStructuredDenominatorPremise.
```

The scale-dependent counterexample does not rule out an implication between
the actual fixed-pi predicates using additional arithmetic structure. The
exact algebra does provide the transparent conditional route

```text
AOC_4 + COV_63 => SignedStructuredDenominatorPremise.
```

Only after additionally supplying T56's separate effective-irrationality and
long-sector hypotheses would T61's machine-checked chain yield C7, then C2,
then C1. None of those hypotheses or conclusions is asserted here.
