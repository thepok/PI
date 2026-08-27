# T64: the centered AOC covariance does not control the T61 residual

Status: `proof sketch` with a replay-checked `experiment` and kernel-checked
T56/T58/T61 inputs. Conclusion: **INSUFFICIENT** for the universal finite
restricted-Schur inequality tested below. This is not a conclusion about the
fixed phase `pi` at any scale.

## 1. Statement, provenance, and quantifiers

The canonical statement is the delivered byte-exact file
`pi-positive-decimal-factor-entropy.txt`, SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
It has no original external URL; it was formulated locally on 2026-07-22.

The canonical question asks whether one fixed `eta>0` and one fixed `N>=1`
give `p_pi(n)>=10^(eta*n)` for every `n>=N`. T64 does not answer that
question. The following quantifier distinctions are binding.

1. A universal finite operator inequality quantifies over every finite scale
   and every decimal-orbit seed `alpha`.
2. A fixed-seed all-scale statement first fixes one seed, especially
   `alpha=pi`, and then quantifies over all sufficiently large scales.
3. Refuting the universal statement with `alpha=0` does not refute its
   restriction to `alpha=pi`.
4. T61's `SignedStructuredDenominatorPremise` is an eventual one-sided upper
   bound at `pi`, not an absolute-value universal operator inequality.
5. The arithmetic parameters `(mu,c,Q0)` are fixed before the scale. The
   counterexample uses `(2,0,0)` only to test the finite interface. Since
   `c=0`, it does not satisfy T56's separate `EffectiveIrrationality` premise.
6. The same seed `alpha=0` is used at every counterexample scale; the seed
   does not vary with scale.

T63 is an unverified note and is used only as motivation for which residual
to reconstruct. Every identity and estimate used below is rederived here.

## 2. Checked T56/T58/T61 data

For `n` a natural number, set

```text
L=L_n=10^(n/2),       H=H_n=10^n/2,
```

where both divisions are natural-number division. T56's checked short range
and T61's checked mask are

```text
0<r<n,  r<L,  0<=j<L-r,
not ArithmeticExcluded(mu,c,Q0,n,j,r).                    (2.1)
```

The condition `r<L` is redundant once `j<L-r` is inhabited, but it is part of
T56's literal `shortResidualLags` endpoint audit. Put

```text
q_(j,r)=10^j(10^r-1).                                     (2.2)
```

T58 checks that the positive frequency attached to `(h,j,r)` is
`h*q_(j,r)` and checks the exact triangular rectangle. For `H>=2`, T61's
coefficient and periodic majorant are

```text
c_H(h)=H^(-1)[sin(pi*h/H)/pi
                 +2(1-h/H)cos(pi*h/H)],   1<=h<H,          (2.3)

M_H(x)=2/H+2 sum_(1<=h<H)c_H(h)cos(2*pi*h*x).              (2.4)
```

The cutoff in (2.3)-(2.4) is strict. There is no `h=H` term. The zero mode is
exactly `2/H`; positive and negative frequencies have already been paired in
the factor `2`. T61 machine-checks

```text
1_(circleDistance(x)<1/(2H)) <= M_H(x),                    (2.5)
M_H(+1/(2H))=M_H(-1/(2H))=1,                              (2.6)
1_(circleDistance(+/-1/(2H))<1/(2H))=0.                   (2.7)
```

For `n>=1`, it checks `1/(2H_n)=10^(-n)`. Thus neither endpoint is silently
changed from strict to weak.

The public checked locators are:

- T56 `mem_sparse_short_sector_iff` and
  `sparse_short_sector_le_two_mul_length_mul_n`;
- T58 `mem_shortRectangle_iff`,
  `phi_eq_frequency_mul_structuredDenominator`, and
  `collisionSecondMoment_eq_diagonal_add_offDiagonal`;
- T61 `mem_residualShortRectangle_iff`,
  `vaalerCoefficient_explicit`,
  `periodicVaalerMajorant_finite_formula`,
  `structuredVaalerMajorantTotal_eq_completeExpression`,
  `decimalCutoff_eq_centralRadius`, and
  `strictCentralIndicator_le_periodicVaalerMajorant`.

No checked declaration asserts the missing fixed-pi signed estimate.

## 3. Finite decimal-orbit form

Fix a real seed `alpha` and define its decimal orbit

```text
x_i(alpha)=frac(10^i*alpha),  i>=0.                        (3.1)
```

For `1<=k<L` and `0<=v<k`, put

```text
r=k-v,  j=v,
d_(k,v)=10^k-10^v=10^v(10^(k-v)-1),                       (3.2)
z_(k,v;alpha)=x_k(alpha)-x_v(alpha) mod 1.                 (3.3)
```

Since all functions below are one-periodic, they may equivalently be
evaluated at `d_(k,v)*alpha`. Define the residual selector

```text
epsilon_(k,v)
 =1_(1<=k-v<n and
      not ArithmeticExcluded(mu,c,Q0,n,v,k-v)).            (3.4)
```

The map

```text
(r,j) -> (k,v)=(j+r,j),    (k,v) -> (r,j)=(k-v,v)          (3.5)
```

is a bijection between (2.1) and the labels selected by (3.4). Indeed,
`j<L-r` is exactly `k<L`, and `0<r<n` is exactly `1<=k-v<n`.

Let

```text
y_(k,v)=M_H(d_(k,v)*alpha).                                (3.6)
```

The T61 complete upper-triangular total generalized from `pi` to `alpha` is

```text
E_n(alpha)=sum_(1<=k<L) sum_(0<=v<k) epsilon_(k,v)y_(k,v). (3.7)
```

At `alpha=pi`, (3.5) and T61's checked finite expansion give exactly

```text
E_n(pi)
 = [2/H] sum_(k,v)epsilon_(k,v)
   +2 sum_(1<=h<H)c_H(h)
       sum_(k,v)epsilon_(k,v)
         cos(2*pi*h*d_(k,v)*pi).                           (3.8)
```

There is no division by `HL` in (3.7) or (3.8). T56's ordered pair count
would restore the reverse orientation with an additional factor `2`; T61's
premise uses the upper-triangular total (3.7).

## 4. AOC weights and exact normalization

This section defines the finite AOC object rather than treating the T43 or
T63 notes as proved. Let `B_L(k)=[a_L(k),b_L(k))` be the unique block in the
canonical binary partition of `[1,L)` containing `k`, and put

```text
W_L(k)=sqrt(b_L(k)^2-a_L(k)^2).                            (4.1)
```

For `0<=v<k<L`, define the positive-part notation `[u]_+=max(u,0)` and

```text
Lambda_(n,L)(v,k)
 =1_(a_L(k)<=v<b_L(k))[v-n+1]_+
  +[min(b_L(k),k-n+1)-max(a_L(k),v+n)]_+.                 (4.2)
```

At onset `Qstar=0`, every `v<k` is allowed because
`0<=10^k-10^v`. Put

```text
g_(k,v)=Lambda_(n,L)(v,k)/W_L(k),
G_k=sum_(0<=v<k)g_(k,v).                                  (4.3)
```

Call `k` active exactly when

```text
1<=k<L,  5n<31k,  G_k>0.                                 (4.4)
```

The supercritical inequality in (4.4) is strict. Extend the active AOC weight
by zero:

```text
w_(k,v)=1_(k active)g_(k,v).                              (4.5)
```

For `delta(u)=|u-round(u)|`, let

```text
K_n=clog_2(10^n)-1,

S_0: 0<=delta<=10^(-n),
S_s: 2^(s-1)/10^n<delta<=min(2^s/10^n,1/2),
     1<=s<=K_n.                                           (4.6)
```

The zero shell is closed. Every positive shell is open below and closed
above, including the cap `1/2`. Define

```text
t_(k,v)
 =1_(S_0(d_(k,v)alpha))
  +sum_(s=1)^K_n 2^(-s)1_(S_s(d_(k,v)alpha)).              (4.7)
```

For active `k`, define

```text
p_(k,v)=g_(k,v)/G_k,
mu_k=(1/k)sum_(v<k)t_(k,v),
Var_k=(1/k)sum_(v<k)(t_(k,v)-mu_k)^2,
Xi_k=k sum_(v<k)(p_(k,v)-1/k)^2.                           (4.8)
```

Here `k=card{v:0<=v<k}` because `Qstar=0`. The exact centered identity is

```text
sum_(v<k)p_(k,v)t_(k,v)
 =mu_k+sum_(v<k)(p_(k,v)-1/k)(t_(k,v)-mu_k).               (4.9)
```

Finite Cauchy-Schwarz gives

```text
abs(sum_(v<k)(p_(k,v)-1/k)(t_(k,v)-mu_k))
 <=sqrt(Xi_k Var_k).                                      (4.10)
```

The exact signed centered covariance occurring before Cauchy-Schwarz is

```text
Z_n(alpha)=2 sum_(k active)G_k
  sum_(v<k)(p_(k,v)-1/k)(t_(k,v)-mu_k).                   (4.11)
```

Its literal AOC Cauchy-Schwarz cost is

```text
Ctr_n(alpha)=2 sum_(k active)G_k sqrt(Xi_k Var_k),         (4.12)
```

and `|Z_n(alpha)|<=Ctr_n(alpha)`. Thus `Ctr_n` is not itself the exact signed
covariance; it is the orbit-generalized centered Cauchy-Schwarz cost appearing
in AOC_4.

For completeness, AOC_4 is a `conjecture`, not an input proved here. Its
literal specialization says: if AOC_4 holds, then there exists a real
`C_(3/4,0)>=0` such that for every natural `n>=1`,

```text
Qstar=0,  s=3/4,  m=n,  N=L_n,

U_AOC,n(pi)
 =2 sum_(k active)G_k[mu_k+sqrt(Xi_k Var_k)]
 <=C_(3/4,0)[L_n+L_n^2 10^(-3n/4)].                     (4.13)
```

For `n>=2`, its target is at most `2C_(3/4,0)L_n`. The exact geometric
envelope before centering is

```text
E_4^(alpha)(0;n,L_n)=2A_n(alpha),                         (4.14)
```

where `A_n` is defined in (5.1). The factor `2` in (4.13)-(4.14) pairs the
two corresponding T43 rows. It is not T56's separate factor `2` restoring
the reverse orientation of an upper-triangular pair count. T61's `E_n` and
the COV residual use one upper-triangular orientation, so `R_n=E_n-A_n`
compares T61 with half of (4.14), exactly as the COV interface requires.

Neither `Z_n` nor `Ctr_n` is the full AOC_4 left side: the latter also has
the mean term `2 sum G_k mu_k`. This distinction is essential below. For
`alpha` other than `pi`, these are finite decimal-orbit analogues, not an
assertion of the literal fixed-pi AOC_4 predicate.

The complete crosswalk is therefore:

| Object | Specialized AOC side | T56/T61 side | Exact relation |
|---|---|---|---|
| Decimal scale | `m=n` | `n` | identical |
| Prefix endpoint | `N=L_n` | sample length `L_n=10^(n/2)` | identical, natural division |
| Fourier bandwidth | absent | `H_n=10^n/2` | only T61 has it |
| Label | `0<=v<k<L_n` | `0<r<n`, `0<=j<L_n-r` | `v=j`, `k=j+r`, `r=k-v` |
| Denominator | `10^k-10^v` | `10^j(10^r-1)` | exactly equal |
| Onset | `Qstar=0` | none | automatic for every `v<k` |
| Supercritical endpoint | strict `5n<31k` | absent | encoded by zero extension of `w` |
| Arithmetic mask | absent | `not ArithmeticExcluded(mu,c,Q0,n,j,r)` | encoded only in `epsilon` |
| Label weight | `Lambda_(n,L)(v,k)/W_L(k)` | uniform surviving weight `1` | mass mismatch in (5.3) |
| Orbit kernel | shell `t_(k,v)` with endpoints (4.6) | `M_H(d alpha)` | kernel mismatch in (5.3) |
| Fourier range | absent | strict `1<=h<H_n` | coefficient (2.3) |
| Zero mode | absent | exactly `2/H_n` per label | included in `y` and (3.8) |
| Centering | uniform mean over all `v<k` at `Qstar=0` | uniform mean of `y` introduced in (5.2) | centered bilinear line of (5.3) |
| Outer factor | `2` pairs T43 rows | no factor in T61 upper triangle | `E_4=2A`; COV uses `E-A` |
| Other factor `2` | absent from this comparison | T56 ordered count restores orientation | distinct from T43 row pairing |
| AOC target | `C[L_n+L_n^2 10^(-3n/4)]` | T61 target `B L_n` | AOC target `<=2CL_n` for `n>=2` |

## 5. COV residual derived from scratch

Set

```text
A_n(alpha)=sum_(k,v)w_(k,v)t_(k,v),
R_n(alpha)=E_n(alpha)-A_n(alpha).                          (5.1)
```

This is the exact unoriented residual called `COV_63` in the motivating note.
No estimate is included in its definition. For each `k`, put

```text
J_k=sum_(v<k)epsilon_(k,v),
A_k=sum_(v<k)w_(k,v),
ybar_k=(1/k)sum_(v<k)y_(k,v).                              (5.2)
```

Because both centered coefficient vectors have sum zero, adding and
subtracting `ybar_k` gives the exact identity

```text
R_n(alpha)=sum_(1<=k<L) [
   (J_k-A_k)ybar_k

  +sum_(v<k)
     ((epsilon_(k,v)-J_k/k)-(w_(k,v)-A_k/k))
     (y_(k,v)-ybar_k)

  +sum_(v<k)w_(k,v)(y_(k,v)-t_(k,v)) ].                   (5.3)
```

To verify (5.3), expand its second line. The terms multiplied by `ybar_k`
sum to zero. The first two lines then equal
`sum_v(epsilon_(k,v)-w_(k,v))y_(k,v)`, and the third changes
`sum_v w_(k,v)y_(k,v)` to `sum_v w_(k,v)t_(k,v)`.

Equation (5.3) is a signed bilinear form. Its middle line is the inner product
of the centered selector-weight defect

```text
epsilon-J_k/k-(w-A_k/k)                                   (5.4)
```

with the centered Vaaler response `y-ybar_k`. The first line is the mass
mismatch and the third is the Vaaler-to-shell kernel mismatch. This is a
literal decomposition, not an appeal to T63.

## 6. Concrete restricted-Schur inequality

The tested universal finite inequality is:

```text
(RS_C)

There is a fixed C>=0 such that for every n>=16 divisible by 4 and every
real decimal-orbit seed alpha,

  |R_n(alpha)| <= Ctr_n(alpha)+C L_n.                      (6.1)
```

The arithmetic parameters in (6.1) are fixed as

```text
(mu,c,Q0)=(2,0,0).                                        (6.2)
```

This is a restricted-Schur proposal because it attempts to control the
bilinear residual (5.3) by the orbit-generalized centered AOC Cauchy-Schwarz cost (4.12)
and a linear remainder. It is intentionally concrete: the coefficient of
`Ctr_n` is exactly one and the only free constant is `C`, independent of
`n` and `alpha`.

The proposal is not T61's premise, not AOC_4, and not a claim previously
present in the library. We now disprove it exactly.

## 7. Fixed-seed decimal-orbit counterexample

Take the one fixed seed

```text
alpha=0.                                                   (7.1)
```

Then `x_i(alpha)=0` for every `i`, so this is a genuine decimal orbit and all
its prefixes are compatible. In particular,

```text
t_(k,v)=1,  mu_k=1,  Var_k=0,  Ctr_n(0)=0.                (7.2)
```

The equality `t=1` uses the closed zero shell in (4.6), not an endpoint
approximation.

### 7.1 The arithmetic mask is identically one

For every short label, `q=10^v(10^(k-v)-1)>0`. At (6.2), T25's literal
excluded predicate is

```text
0<=q and 10^(-n)<=q*(0/q^2).                              (7.3)
```

The right side in the second comparison is zero, while `10^(-n)>0`.
Therefore (7.3) is false and every short label survives. The exact short
cardinality is

```text
S_n=sum_(r=1)^(n-1)(L-r)
   =(n-1)L-n(n-1)/2
   <nL.                                                     (7.4)
```

For the displayed scales `L>n`, so every term in (7.4) is literal and no
natural subtraction truncates.

### 7.2 Uniform height bound for the checked Vaaler polynomial

At zero, (2.4) gives

```text
M_H(0)=2/H+2 sum_(1<=h<H)c_H(h).                           (7.5)
```

For `1<=h<H`, elementary `|sin|<=1`, `|cos|<=1`, `pi>2`, and
`1-h/H>=0` imply

```text
|c_H(h)|
 <=H^(-1)[1/pi+2(1-h/H)].                                 (7.6)
```

Since

```text
sum_(h=1)^(H-1)(1-h/H)=(H-1)/2,                           (7.7)
```

we obtain, preserving every constant,

```text
M_H(0)
 <=2/H+2/H[(H-1)/pi+(H-1)]
 =2+2(H-1)/(H*pi)
 <3.                                                       (7.8)
```

T61's checked majorization at zero also gives `1<=M_H(0)`, so no sign change
is hidden in using (7.8). Equations (7.4) and (7.8) yield

```text
0<=E_n(0)<3nL.                                             (7.9)
```

### 7.3 Quadratic geometric mass

Let `B` be the largest power of two with `B<=L-1`. The first canonical block
is exactly

```text
[1,B+1),  W=sqrt(B^2+2B),  B<=L-1<2B.                    (7.10)
```

Thus `B>L/4` for `L>2`, and `W<2B`. For every `k` in this block, direct
substitution in (4.2) gives

```text
Lambda_(n,L)(v,k)
 =1_(v>=n)(v-n+1)+[k-2n+1-v]_+.                           (7.11)
```

For every `0<=v<k`, splitting at `v=n` and at `v=k-2n` proves

```text
Lambda_(n,L)(v,k)>=k-3n+2.                                (7.12)
```

Select the exact half-open range

```text
B/2<=k<B.                                                  (7.13)
```

For `n>=16` divisible by four, `L=10^(n/2)` gives `B/2>=6n`.
At `n=16`, this follows from `B=2^26`. When `n` increases by four,
`L` is multiplied by `100`, the new largest binary block size is at least
`64B`, and hence its half-size grows by at least `64`, while `6n` grows only
additively by `24`. This proves the displayed bound by induction.
Consequently (7.12) is at least `k/2`. Every selected `k` obeys the strict
activity condition `5n<31k`, and `G_k>0`. Hence

```text
G_k=sum_(v<k)Lambda(v,k)/W
    >=k^2/(2W)
    >B/16.                                                 (7.14)
```

There are exactly `B/2` integers in (7.13). Since `t=1`, (7.14) gives

```text
A_n(0)>B^2/32>L^2/512.                                    (7.15)
```

Every inequality in (7.10)-(7.15) is integer or rational after the single
certified comparison `sqrt(B^2+2B)<2B`; squaring is legitimate because both
sides are positive.

### 7.4 Violation at arbitrarily large declared scales

Combining (7.2), (7.9), and (7.15), for every `n>=16` divisible by four,

```text
|R_n(0)|=A_n(0)-E_n(0)
         >(L/512-3n)L,                                    (7.16)
```

where positivity follows already at `n=16` and only increases along the
scale family.

For an explicit quantifier witness, given any real `C>=0`, let

```text
K=ceil(C),  n=4(K+4),  L=10^(2K+8).                       (7.17)
```

Then

```text
10^(2K+8)>512(13K+48),                                    (7.18)
```

and therefore `L/512-3n>K>=C`. Equation (7.18) holds at `K=0`; multiplying
its left side by `100` when `K` increases by one dominates the increase of
the affine right side, giving an elementary induction. Equations (7.16) and
(7.17) imply

```text
|R_n(0)|>C L,  while Ctr_n(0)=0.                           (7.19)
```

This disproves `(RS_C)` for every proposed constant. Indeed, taking
`K=ceil(C)+t` for any natural `t` supplies arbitrarily large violating scales,
not merely one scale. It supplies one fixed
seed, not a seed chosen separately at each scale. The prefixes have lengths
`L=10^(2K+8)` and are therefore arbitrarily large.

## 8. Exact missing premise

The failure is specifically a failure of pairwise centered AOC covariance to
control the three-term T61 residual. A componentwise sufficient repair at the
fixed phase `pi` is the following higher-order covariance/spacing premise:

```text
(HOC_64)

There are D_mass,D_sel,D_ker>=0 and N0>=1 such that for every n>=N0,

 sum_(1<=k<L_n) |J_k-A_k| |ybar_k| <=D_mass L_n,

 |sum_(1<=k<L_n) sum_(0<=v<k)
    ((epsilon_(k,v)-J_k/k)-(w_(k,v)-A_k/k))
    (y_(k,v)-ybar_k)| <=D_sel L_n,

 |sum_(1<=k<L_n) sum_(0<=v<k)
    w_(k,v)(y_(k,v)-t_(k,v))| <=D_ker L_n,                (8.1)
```

with every symbol evaluated at `alpha=pi` and the exact ranges (3.4)-(4.8).
By (5.3), `(HOC_64)` gives

```text
|R_n(pi)|<=(D_mass+D_sel+D_ker)L_n.                        (8.2)
```

The first line is a spacing/mass-matching condition between the short-lag
selector and canonical AOC geometry. The second is a genuinely higher-order
fixed-phase covariance coupling the arithmetic selector, geometric weights,
and Vaaler response. The third transfers the dyadic shell kernel to the full
signed Vaaler band. Centered AOC_4 does not itself supply these three
estimates. The zero orbit specifically violates the first line quadratically;
no separate counterexample to each of the other two lines is claimed.

The one-line alternative `|R_n(pi)|=O(L_n)` is exactly the original COV
premise, but (8.1) isolates its mathematical content rather than merely
renaming the residual.

## 9. Conclusion and scope

**INSUFFICIENT.** The concrete universal finite restricted-Schur inequality
`(RS_C)` is false, even on genuine decimal-orbit phase vectors. The exact
counterexample uses the same seed `alpha=0` at every scale, has zero centered
AOC covariance, and has residual larger than every fixed multiple of `L_n`
along the explicit scales (7.17).

At `alpha=0`, the full orbit-generalized AOC expression (4.13) is
`2 sum_k G_k=2A_n(0)`, which is quadratic. Thus the example does not satisfy
an AOC_4-sized full mean-plus-covariance bound and does not refute an
implication whose premise is full AOC_4. It refutes only the concrete
covariance-only restricted-Schur proposal (6.1).

This does not show that `COV_63`, `(HOC_64)`, or T61's signed premise fails for
the one fixed seed `pi`. It does not instantiate AOC_4, T56's effective
irrationality premise, or the separate long-sector premise. It makes no
unconditional claim about pi, C7, C2, C1, or positive decimal factor entropy.

## 10. Replay

From a directory containing only the delivered artifacts, run

```sh
./verify.sh
```

The script checks all delivered hashes, verifies the canonical statement
hash, and replays the integer and rational consequences of the note's
analytic derivation for declared scales
`n=16,32,64,128` and comparison constants `K=0,10,100,1000`. It accepts
additional exact constants, for example:

```sh
python3 t64_replay.py --constants 7 12345
```

The replay directly checks block endpoints, strict activity, the case
breakpoints in (7.11)-(7.12) at the two selected `k` endpoints,
short-rectangle cardinality, and the final
rational scale inequalities. It does not numerically evaluate the
trigonometric polynomial; the elementary proof of its height bound is
(7.5)-(7.8). Finite replay rows are an `experiment`; the universal conclusion
rests on the displayed algebraic family and induction, not on extrapolation
from the default rows.
