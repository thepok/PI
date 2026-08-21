# T60: Vaaler-grid separation and the sparse short-sector frontier

Status: `proof sketch` for the analytic derivations in this note;
`machine-checked` only for the imported T56 and T58 declarations identified
below; `literature-checked` for the two source statements with the dated,
pinned locators in `SOURCE_MANIFEST.md`. Final verdict: **INSUFFICIENT**.
No unconditional claim about C7, C2, C1, or the decimal digits of pi is made.

## 1. Provenance and exact task

The canonical question is locally formulated and has no original source URL.
Its byte-exact statement is included as
`pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

It asks whether one fixed `eta>0` satisfies
`p_pi(n)>=10^(eta*n)` for every sufficiently large `n`. This note does not
answer that question. It tests whether the strongest source-pinned ordinary
irrationality-measure estimate for pi controls the sparse short sector isolated
by kernel-checked T56 and T58.

The T59 note was used only to identify formulas worth checking. No assertion
from T59 is a premise. Sections 4-6 below derive the Vaaler specialization
directly from the pinned 1985 source.

## 2. Normalization and ambiguities

For every natural `n>=1`, define

```text
L=L_n:=10^(n/2),             H=H_n:=10^n/2,             (2.1)
q=q_(j,r):=10^j*(10^r-1).                               (2.2)
```

Division in the exponent and in `H` is natural-number division. Thus
`n/2=floor(n/2)`. Since `n>=1`, `10^n` is even and

```text
2H=10^n,                    1/(2H)=10^(-n).             (2.3)
```

The complete T56/T58 short rectangle and positive frequency range are

```text
0<r<n,   r<L,   0<=j<L-r,   1<=h<H.                    (2.4)
```

For `n>=2`, `L>=n`, so `r<L` follows from `r<n`; it is retained in (2.4)
because it is an explicit T56 endpoint. The endpoints `r=n`, `j=L-r`, and
`h=H` are excluded. All near-return inequalities are strict. Empty ranges at
small parameters have their usual value zero.

Write

```text
rho(x):=min_(m in Z)|x-m|,
||x-y||_T:=min_(m in Z)|x-y-m|.                        (2.5)
```

For fixed real `mu,c` and natural `Q0`, T56's residual mask is

```text
epsilon_n(r,j)=1 iff not ArithmeticExcluded(mu,c,Q0,n,j,r).
                                                               (2.6)
```

The mask is never silently removed below.

## 3. Kernel-checked boundary

The included byte copies `T56LagSectorAudit.lean` and
`T58TriangularFejerAudit.lean` are inspection copies of accepted library
modules. Their relevant checked declarations are:

```text
DecimalFactorComplexity.T56LagSectorAudit.mem_sparse_short_sector_iff
DecimalFactorComplexity.T56LagSectorAudit.sparseShortRepunitIncidenceBound_iff_quantifiers
DecimalFactorComplexity.T58TriangularFejerAudit.mem_positiveFejerFrequencies_iff
DecimalFactorComplexity.T58TriangularFejerAudit.mem_shortRectangle_iff
```

They check (2.4) and the target predicate

```text
exists A>0, exists N>=1, for every n>=N,
  shortResidualPairCount(mu,c,Q0,n,L_n) <= A*L_n.       (3.1)
```

The count in (3.1) is twice the number of upper-triangular masked strict near
returns:

```text
A_n:=|{(r,j): 0<r<n, r<L, 0<=j<L-r,
       epsilon_n(r,j)=1, rho(q_(j,r)*pi)<1/(2H)}|,

shortResidualPairCount(mu,c,Q0,n,L_n)=2*A_n.           (3.2)
```

Equation (3.2) is an unfolding of the finite definitions whose ranges are
checked by T56/T58; this prose note does not promote it to a new Lean theorem.

## 4. Source-level Vaaler inequality

Put `e(x):=exp(2*pi*i*x)` and use Vaaler's midpoint sawtooth

```text
psi(x)={x}-1/2  if x is not an integer,
       0        if x is an integer.                    (4.1)
```

This is Vaaler (6.6), printed p. 206. For `H>=2` and `0<|t|<1`, set

```text
W(t):=pi*t*(1-|t|)*cot(pi*t)+|t|,

J_H(x):=-sum_(0<|h|<H) W(h/H)/(2*pi*i*h) e(hx),

K_(H-1)(x):=sum_(|h|<H)(1-|h|/H)e(hx)
           =1/H*(sin(pi*H*x)/sin(pi*x))^2,             (4.2)
```

where the last expression has continuous value `H` at integers. Formula for
`W` is Vaaler (2.28), and the periodic Fejer normalization is (6.5), with
degree `N=H-1`.

Vaaler Theorem 18, (7.14), specialized with `N=H-1`, states for every real
`x` that

```text
|psi(x)-J_H(x)| <= K_(H-1)(x)/(2H).                   (4.3)
```

Set `delta=1/(2H)`. Directly from (4.1),

```text
chi_H#(x):=1/H+psi(x-delta)-psi(x+delta)
          =1    if rho(x)<delta,
           1/2  if rho(x)=delta,
           0    if rho(x)>delta.                      (4.4)
```

Applying (4.3) separately at `x-delta` and `x+delta` gives the degree-`H-1`
majorant

```text
M_H(x):=1/H+J_H(x-delta)-J_H(x+delta)
       +[K_(H-1)(x-delta)+K_(H-1)(x+delta)]/(2H),      (4.5)

1_(rho(x)<1/(2H)) <= chi_H#(x) <= M_H(x).             (4.6)
```

This proves `M_H(x)>=0`. It also preserves the strict endpoints:

```text
1_(rho(+-delta)<delta)=0,   chi_H#(+-delta)=1/2,
M_H(+-delta)=1.                                          (4.7)
```

For the last equality, (4.3) is exact at the Fejer grid:
`J_H(k/H)=psi(k/H)` for `1<=k<H`, because `K_(H-1)(k/H)=0`.
Together with `J_H(0)=0`, `K_(H-1)(0)=H`, this gives (4.7).

## 5. Every coefficient and its sign transition

Write `M_H(x)=sum_(h in Z)m_H(h)e(hx)`. The zero mode in (4.5) is

```text
m_H(0)=2/H.                                             (5.1)
```

For `0<|h|<H`, shifting the two `J_H` terms contributes

```text
W(h/H)*sin(pi*h/H)/(pi*h),                              (5.2)
```

and shifting the Fejer terms contributes

```text
1/H*(1-|h|/H)*cos(pi*h/H).                              (5.3)
```

Hence

```text
m_H(h)=W(h/H)*sin(pi*h/H)/(pi*h)
       +1/H*(1-|h|/H)*cos(pi*h/H),    0<|h|<H,
m_H(h)=0,                             |h|>=H.            (5.4)
```

These coefficients are real and even. Substituting `W` and simplifying gives,
for `1<=h<H`,

```text
c_H(h):=m_H(h)
 =1/H*[sin(pi*h/H)/pi+2*(1-h/H)*cos(pi*h/H)],           (5.5)

M_H(x)=2/H+2 Re sum_(h=1)^(H-1)c_H(h)e(hx).             (5.6)
```

There is one continuous sign transition. Define

```text
g(u):=sin(pi*u)/pi+2*(1-u)*cos(pi*u),   0<u<1.          (5.7)
```

It is positive on `(0,1/2]`. For `1/2<u<1`, put
`v=pi*(1-u)`. Then

```text
pi*g(u)=cos(v)*(tan(v)-2v).                              (5.8)
```

The function `tan(v)-2v` decreases on `(0,pi/4)`, is negative at `pi/4`, and
then increases strictly to infinity on `(pi/4,pi/2)`. It therefore has a
unique positive root

```text
v_*=1.165561185207...,
u_*:=1-v_*/pi=0.628990351796....                         (5.9)
```

Thus the complete coefficient classification is

```text
c_H(h)>0 iff h/H<u_*,
c_H(h)=0 iff h/H=u_*,
c_H(h)<0 iff h/H>u_*.                                   (5.10)
```

Thus the only continuous coefficient zero is `u_*`; a discrete zero could
occur only if the deterministic mesh hits it exactly. This note neither needs
nor assumes a separate transcendence theorem to exclude that equality. An
irrationality estimate for pi has no bearing on how the mesh `h/H` approaches
`u_*`.

## 6. Exact phase-grid zeros

The Fejer zeros are

```text
K_(H-1)(k/H)=0,                   1<=k<H.               (6.1)
```

The shifted Vaaler majorant has the full odd half-grid interpolation pattern

```text
M_H((2*l+1)/(2H))=0,              1<=l<=H-2,
M_H(1/(2H))=M_H((2H-1)/(2H))=1.                         (6.2)
```

Indeed the shifted arguments are `l/H` and `(l+1)/H`; both Fejer terms vanish
for interior `l`, and the two interpolating sawtooth values differ by exactly
`-1/H`, cancelling the constant in (4.5). The endpoint calculation is (4.7).

The zeros in (6.2) are zeros of `M_H(x)` in its base argument. In the short
sector that argument is `x=q*pi`, not `h*q*pi`. Hence actual separation from
the Vaaler zeros uses `h=1`, denominator `2H`, and odd numerators. The values
`h*q*pi` arise only inside the individual Fourier harmonics in (5.6); those
exponentials never vanish. This distinction is retained below.

## 7. The pinned irrationality estimate

Zeilberger and Zudilin define the irrationality measure on printed p. 407 and
prove on printed p. 418 that

```text
mu(pi) <= 7.10320533413700172750577342281... < 7.104.  (7.1)
```

The exact construction is in Propositions 7-8, printed pp. 417-418. Therefore
the source-level consequence used here is

```text
mu:=7.104=888/125,
lambda:=mu-1=6.104=763/125,

exists Q0 in N, for every integer D>=Q0 and every P in Z,
  1/D^mu < |pi-P/D|.                                  (7.2)
```

The source proves the asymptotic quantifier in (7.2), but prints no numerical
value of `Q0`. Thus (7.2) is an eventual source-pinned estimate, not a
numerically effective finite cutoff. This limitation does not affect the
asymptotic insufficiency calculation.

## 8. Complete grid-distance substitution

Let `a` be `1` or `2`. For every tuple in the complete ranges

```text
n>=1, 0<r<n, r<L, 0<=j<L-r, 1<=h<H, k in Z, a in {1,2},
q=10^j*(10^r-1), D=a*H*h*q,                            (8.1)
```

one has `q>=9` and `D>=9H`. Hence there is one `N0` such that `n>=N0`
implies `D>=Q0` simultaneously for every legal `a,h,j,r,k`.

Choose an integer `m` attaining the circle distance and put
`P=k+a*H*m`. Then

```text
||h*q*pi-k/(aH)||_T
 =h*q*|pi-P/(a*H*h*q)|
 >h*q/D^mu
 =1/[a*H*D^lambda].                                   (8.2)
```

No reduced-fraction assumption is needed because (7.2) quantifies over every
integer numerator and denominator. Formula (8.2) for `a=1` is exactly the
requested lower bound for
`||h*10^j*(10^r-1)*pi-k/H_n||_T`. The case `a=2` covers every odd half-grid
zero in (6.2).

The half-cell radius of the complete denominator-`aH` grid is `1/(2aH)`.
Dividing it by the lower bound in (8.2) gives the exact loss

```text
[1/(2aH)] / [1/(aH*D^lambda)] = D^lambda/2.            (8.3)
```

Thus ordinary irrationality separates each harmonic phase from exact rational
grid points, but its guaranteed separation is a factor `D^lambda/2` smaller
than a complete-grid half-cell neighborhood.

For the actual interior Vaaler zeros, specialize instead to `a=2,h=1,k` odd:

```text
||q*pi-k/(2H)||_T > 1/[2H*(2Hq)^lambda].               (8.4)
```

The odd zero lattice has spacing `1/H`. Relative to its natural half-spacing
`1/(2H)`, the exact loss is `(2Hq)^lambda`; relative to the smaller half-cell
`1/(4H)` of the complete denominator-`2H` grid, it is
`(2Hq)^lambda/2`. Neither comparison determines on which side of a zero the
base phase lies, nor does it bound the signed sum (5.6).

## 9. Exact loss at the T56 near-return window

The more direct comparison already fails at frequency `h=1`. A strict T56
near return supplies an integer `p` with

```text
|pi-p/q| < 10^(-n)/q.                                  (9.1)
```

The source lower bound `q^(-mu)` contradicts (9.1) only in the region

```text
q^lambda <= 10^n.                                      (9.2)
```

This is exactly T25's arithmetic-exclusion comparison for `c=1` and
`mu=7.104`, apart from its separately retained onset `q>=Q0`.

For every legal lag, the largest legal start is `j=L-r-1`, and

```text
q_max(n,r)=10^(L-r-1)*(10^r-1)
          =10^(L-1)*(1-10^(-r)).                       (9.3)
```

The base-10 exponent by which the near-return window in (9.1) exceeds the
ordinary lower bound is exactly

```text
E_T56(n,r)
 :=lambda*log_10(q_max(n,r))-n
 =lambda*[L-1+log_10(1-10^(-r))]-n.                    (9.4)
```

At `r=1`, this is

```text
E_T56(n,1)=6.104*[L-2+log_10(9)]-n
          =6.104*L-n+O(1).                             (9.5)
```

Since `L=10^floor(n/2)`, this loss is exponential in `n`, while the target
exponent is only `n`.

There is also an explicit coarse upper bound on how many positions can satisfy
the exponent comparison. Since

```text
q>=10^(j+r-1),
```

condition (9.2) implies

```text
763*(j+r-1) <= 125*n.                                  (9.6)
```

Consequently, over all `n-1` short lags, at most

```text
n*(floor(125*n/763)+2)                                 (9.7)
```

legal `(r,j)` positions can satisfy both the exponent comparison and the
onset `q>=Q0`. The finitely many structured denominators below `Q0` can be
handled individually using irrationality of pi; they add only a constant
depending on `Q0`, not a positive proportion of the rectangle. In contrast,
for `n>=2` the complete short rectangle has exactly

```text
M_n=sum_(r=1)^(n-1)(L-r)
   =(n-1)*L-n*(n-1)/2.                                 (9.8)
```

Thus ordinary irrationality directly controls only `O(n^2)` possible
positions out of a rectangle of order `nL`. It gives no upper bound on the
number of actual incidences among the remaining positions.

For the full all-harmonic rational-grid calculation, choose the legal endpoint
`j=L-r-1`, `h=H-1`. With `D=aH(H-1)q_max(n,r)`, the exact base-10 loss relative
to a complete-grid half-cell is

```text
E_grid(n,r,a)
 :=lambda*log_10(a*H*(H-1)*q_max(n,r))-log_10(2).       (9.9)
```

Uniformly at fixed `r`,

```text
E_grid(n,r,a)=6.104*L+12.208*n+O(1).                   (9.10)
```

Equivalently, this all-harmonic lower bound can be as small as
`10^[-6.104*L-13.208*n+O(1)]`, whereas grid neighborhoods have scale
`1/H=10^[-n+O(1)]`.

This is not the loss at a zero of `M_H`, because the majorant argument has no
internal `h`. At an actual Vaaler zero, use (8.4) and `q=q_max`; the complete
denominator-`2H` half-cell loss is

```text
lambda*log_10(2H*q_max)-log_10(2)
 =6.104*L+6.104*n+O(1),                                (9.11)
```

and the lower bound in (8.4) has scale
`10^[-6.104*L-7.104*n+O(1)]`.

## 10. Why this does not imply the Vaaler bound

Summing (4.6) over the masked rectangle gives

```text
A_n <= sum_((r,j) masked) M_H(q_(j,r)*pi).             (10.1)
```

Using (5.6), the right side is

```text
2*|X_n|/H
+2 Re sum_(h=1)^(H-1)c_H(h)
      sum_((r,j) masked)e(h*q_(j,r)*pi).                (10.2)
```

The zero mode is at most `2nL/H<=2L`. The unresolved term is the complete
signed fixed-pi sum in (10.2). Bounds (8.2) merely say that no individual phase
is exactly on a rational separator. Away from its isolated zeros, `M_H` can
remain of constant size, so summing a pointwise upper bound over (9.8) retains
the factor `n`. No cancellation or aggregate sparsity follows from (8.2).

In particular, neither the coefficient sign split (5.10) nor phase-grid
avoidance supplies the required estimate

```text
sum_((r,j) masked) M_H(q_(j,r)*pi)=O(L).               (10.3)
```

The direct pointwise-separation use of the source-pinned irrationality
estimate developed here therefore does not establish (3.1). This is an
insufficiency result for the audited route, not a counterexample or a logical
nonimplication theorem about every possible use of the published estimate.

## 11. Equivalent structured-denominator frontier

The exact aggregate exceptional-set form of the short-sector frontier is

```text
exists C>0, exists N>=1, for every n>=N,

2*|{(r,j): 0<r<n, r<L_n, 0<=j<L_n-r,
      epsilon_n(r,j)=1,
      exists p in Z,
        |pi-p/q_(j,r)| < 10^(-n)/q_(j,r)}|
  <= C*L_n.                                             (SI_pi)
```

By multiplying by the positive integer `q_(j,r)` and minimizing over `p`,
`(SI_pi)` is exactly (3.1), not an unproved strengthening disguised as a
consequence. It is "weakest" only in the tautological logical sense that the
target itself is implied by every sufficient premise. This audit does not
identify a strictly weaker, independently checkable irrationality hypothesis.

The equivalent complement formulation says that, for all but at most
`C*L_n/2` masked pairs,

```text
for every p in Z,
|pi-p/q_(j,r)| >= 10^(-n)/q_(j,r).                    (11.1)
```

Unlike the ordinary power law `q^(-7.104)`, (11.1) is scale-adaptive in both
`n` and the structured denominator. Requiring (11.1) for every masked pair,
with no exceptional set, is a genuinely stronger pointwise premise. An
all-frequency version requiring half-cell separation in (8.2) for every `h`
is stronger still.

## 12. Verdict

**INSUFFICIENT FOR THE AUDITED POINTWISE-SEPARATION ROUTE.** The strongest
pinned ordinary irrationality estimate gives the complete lower bound (8.2),
but loses the factors in (8.3)-(8.4) at the rational grids and the exact factor
`q^6.104/10^n` at the T56 near-return window. At the largest legal starts this
is the exponent loss (9.4)-(9.5); the actual Vaaler-zero loss is (9.11), while
the distinct all-harmonic calculation is (9.9)-(9.10). The estimate can
directly exclude only the `O(n^2)` initial positions in (9.7), not control the
order-`nL_n` residual rectangle. This does not prove that every conceivable
argument combining the published estimate with additional arithmetic input
must fail.

No instance of T56's `SparseShortRepunitIncidenceBound` has been established.
Even `(SI_pi)` would address only T56's short premise; T56's separate effective
irrationality and long-sector premises would still be required before its
conditional bridge to C7 could be invoked. This note asserts none of C7, C2,
or C1.

## 13. Replay

From a directory containing only the delivered artifacts:

```sh
sh ./verify.sh
```

The replay uses exact integer arithmetic for (2.1)-(2.4), (9.2), (9.6), and
(9.8), high-precision decimal arithmetic to display the losses, and binary64
bisection only to display the root in (5.9). Its finite instances are labeled
`experiment`; they are not proof of any universal or fixed-pi assertion.
