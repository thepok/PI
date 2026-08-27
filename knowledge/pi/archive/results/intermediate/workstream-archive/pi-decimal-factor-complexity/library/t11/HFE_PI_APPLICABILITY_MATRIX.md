# T11: applicability matrix for the fixed-pi weighted Fourier hypothesis

Status: **literature-checked** on 2026-07-22 for the bounded source set in
`SOURCE_MANIFEST.md`. This is a row-by-row applicability audit, not an
exhaustive assertion that no other theorem exists.

## 1. Immutable target and scope

The canonical problem is
`knowledge/pi/statements/pi-decimal-factor-complexity.txt`, SHA-256
`e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`.
It asks whether the number `p_pi(n)` of contiguous length-`n` factors starting
at arbitrary fractional decimal positions satisfies `p_pi(n)/n -> infinity`
(A1). T11 does not prove or disprove A1.

T11 audits the stronger sufficient analytic sibling `HFE_pi` from accepted
T10. Put

```text
e(t)       = exp(2*pi*i*t),
S_h(N,x)  = sum_{j=0}^{N-1} e(h*10^j*x),
H_A(n)    = ceil(A*n),
w(n,H,h)  = min(2*10^(-n) + 1/(H+1), 1/(pi*h)),
W(n,H,N,x)= sum_{h=1}^H w(n,H,h)*|S_h(N,x)|^2.
```

Here the `pi` in `1/(pi*h)` is the circle constant, and the final argument
`x=pi` is the named initial point. T10's formal definition at
`PiWeightedFourierReduction.lean:1085-1097` is exactly

```text
for every real A > 0,
for every real epsilon > 0,
there exists nstar in N with nstar >= 1 such that
for every n in N with n >= nstar,
there exists N in N with N >= 1 such that
W(n, ceil(A*n), N, pi) < epsilon*N^2/n.             (HFE_pi)
```

The order is

```text
forall A, forall epsilon, exists nstar, forall n >= nstar, exists N.
```

In particular, `N` may depend on `A`, `epsilon`, and `n`. There is no demand
for one sample size to work at every scale, nor for a computable `N`. At each
fixed `n`, however, cancellation must hold simultaneously in all integer
frequencies `1 <= h <= ceil(A*n)` with T10's exact positive weights.

Accepted T10, SHA-256
`45003707a7b30447c9dd9ed5843f8c899a7c7107814c99f9b7a7a9f4ab8bf4ff`,
machine-checks only

```text
HFE_pi -> C2 -> C1 -> A1.
```

It does not assert `HFE_pi`. Therefore no negative row below is evidence that
`HFE_pi`, C2, C1, or A1 is false.

## 2. Verdict policy and clause checklist

- **YES** means that the cited theorem, with every hypothesis verified,
  proves `HFE_pi` in the displayed quantifier order.
- **CONDITIONAL** means that a deterministic implication applies at the named
  point `pi`, but an explicitly stated additional premise remains unproved.
- **NO** means that the cited result fails at least one indispensable clause.
  The first failure is identified; later differences are retained to prevent
  accidental reuse under a different normalization.

Every row is checked against these clauses:

| Clause | Exact requirement |
|---|---|
| P | The initial point is the fixed named real `x=pi`, not almost every, random, generic, or merely some `x`. |
| QA | `A>0` and `epsilon>0` are arbitrary before `nstar` is chosen. |
| Qn | One `nstar` works for every integer `n>=nstar`. |
| QN | For each such `n`, one may choose `N=N(A,epsilon,n)>=1`. |
| F | The conclusion is simultaneous for every `1<=h<=ceil(A*n)`. |
| W | The bounded quantity uses `w(n,H,h)` and the sum of squared norms, or gives a proved upper bound implying it. |
| R | The saving is strictly `< epsilon*N^2/n`, not merely `o(N^2)` at each fixed frequency without a simultaneous finite-frequency argument. |

Effectiveness is recorded but is not itself an HFE clause because `HFE_pi`
is existential. An ineffective theorem would be sufficient if it applied to
the fixed point with all the displayed quantifiers.

## 3. Summary matrix

| ID and family | Exact source result | Point scope | Frequency, scale, and weights | Constants/effectiveness | Verdict and first unmatched clause |
|---|---|---|---|---|---|
| EG (fixed-frequency lacunary sum; reused T28) | Erdos--Gal I, main theorem, printed p. 65: for `n_(j+1)/n_j>=q>1`, `limsup |sum_{j<=N}e(n_j x)|/sqrt(N log log N)=1` for almost every `x`; Part II completes the proof. | A.e. `x` after the gap sequence is fixed, not fixed `pi`. | For each fixed `h`, take `n_j=h*10^(j-1)`, `q=10`. Countable intersection handles all integer `h`; a finite maximum handles `h<=ceil(A*n)` at each fixed `n`. No HFE weights occur, but the square-root bound is strong enough for the weighted sum. | Exact LIL constant `1`; pointwise threshold and exceptional set are not effective. | **NO. First failure P:** no theorem places `pi` in the conull set. All later HFE quantifiers can be matched for an a.e. analogue. |
| SZ (coefficient-weighted lacunary distribution) | Salem--Zygmund (1947), result (vi), printed p. 337: for a Hadamard-gap power series with complex coefficients, `C_N=(1/2 sum_{k<=N}|c_k|^2)^(1/2)`, `C_N->infinity`, and `c_N=o(C_N)`, the normalized real and imaginary parts converge jointly to the standard two-dimensional Gaussian distribution relative to every fixed positive-measure set. | Distribution as the source variable ranges over a positive-measure set; no conclusion for an individual point. | Taking `c_k=1`, `n_k=h*10^(k-1)`, and source variable `2*pi*x` matches T10's `j=0,...,N-1` sum for each fixed `h`. It neither supplies a pointwise bound nor a triangular estimate uniform in `h<=ceil(A*n)` and its coefficient weights are in `k`, not T10's outer frequency weights. | Exact Gaussian normalization; no rate of convergence. | **NO. First failure P:** it is a distribution theorem over the initial point, not a fixed-`pi` estimate. F and W also do not match directly. |
| PH-D (deterministic discrepancy bridge; reused T28) | Philipp (1975), equation (3.9), printed p. 250: for every finite point sequence, `|sum_{j<=N}e(x_j)| <= sqrt(32) N D_N`, with the note-added constant improved to `4`. | Deterministic and valid at `x_j=h*10^(j-1)*pi`. | Simultaneous frequencies follow if one has a common bound for `D_N({h*10^j*pi})` for `h<=ceil(A*n)`. The inequality contains no estimate of those discrepancies. | Explicit finite coefficient `4` in the note added; fully effective conditional on discrepancy data. | **CONDITIONAL. First missing clause R:** no pinned theorem supplies a sufficiently small fixed-`pi` discrepancy bound to its right side. |
| FU (base-10 discrepancy) | Fukuyama (2008), theorem and corollary, journal pp. 155-156: for fixed `theta>1` and a.e. `x`, `limsup N D_N({theta^j x})/sqrt(2N log log N)=Sigma_theta`; for `theta=10`, `Sigma_10=sqrt(220)/27`. | A.e. `x`, not fixed `pi`. | Extreme discrepancy is uniform over intervals and all sufficiently large `N`. Replacing the initial point by `h*x/10` and taking finite intersections handles every `h<=ceil(A*n)` for fixed `n`; PH-D then implies the required metric weighted cancellation. | Exact base-10 constant; no effective exceptional set or pointwise threshold. | **NO. First failure P:** the exact base-10 theorem does not establish its conclusion at `pi`. |
| RZ-PC (pair correlation and all local correlations) | Rudnick--Zaharescu, Theorems 1.1-1.2, preprint pp. 2-3 / journal pp. 692-693: every lacunary integer sequence has Poisson local spacing measures for a.e. `alpha`; on one full-measure set, for every `k>=2` and every smooth compactly supported test `f`, `R_k(f,N)(alpha)->integral f`. | A.e. `alpha` after the sequence is fixed. For this audit take `a(j)=10^j`. | Pair correlation is at radius `s/N`, excludes diagonal pairs, normalizes the count by `N`, and lets `N->infinity`. HFE fixes radius `10^(-n)`, includes a separate cutoff `h<=ceil(A*n)`, uses a positive Fourier-energy upper bound, and may choose one `N` separately at each `n`. | Limiting pair constant `2s` after standard smooth approximation. Membership and eventual thresholds are ineffective. | **NO. First failure P:** no result identifies `alpha=pi` as a good parameter. Scale and W are additional nonliteral matches, so pair correlation must not be quoted as HFE itself. |
| RZ-MS (primary mean-square/variance bound) | Rudnick--Zaharescu, Proposition 4.1, preprint p. 11: for every fixed smooth test and every `eta>0`, `int_0^1 |R_k(f,N)(alpha)-E R_k(f,N)|^2 d alpha <<_eta N^(-1+eta)`; Lemma 3.1 gives `E R_k(f,N)=fhat(0)+O_(f,eta)(N^(-1+eta))`. | An `L^2(d alpha)` estimate over initial points, not a pointwise estimate at `pi`. | It controls a smoothed correlation statistic with constants depending implicitly on fixed `f`, `k`, `eta`, and the lacunarity data. It is not T10's sum over `h<=ceil(A*n)` with `n`-varying weights. | Choosing `0<eta<1` gives a power saving, with unspecified implied constants; the source uses it to prove a.e. convergence. | **NO. First failure P:** parameter mean square cannot be evaluated at a named singleton. W is also a different quadratic form. |
| WM (exact averaged HFE energy; derived below) | Orthogonality gives `int_0^1 W(n,H,N,x) dx = N sum_{h<=H}w(n,H,h) <= N(1+2H*10^(-n))`. This is a self-contained calculation, not attributed as a new literature theorem. | Mean over `x`; it yields some good `x` and, with summable choices, an a.e. statement, not the fixed named `pi`. | Exact T10 frequencies, weights, and scale. Choosing `N_n` sufficiently large makes the bad-set measures summable and proves an a.e.-`x` HFE analogue with the full QA-QN order. | Exact finite identity and effective Markov bound; no method identifies `pi` outside the exceptional set. | **NO. First failure P:** exact matching of F, W, R, and all scale quantifiers under averaging does not specialize to `pi`. |
| ZZ (pointwise irrationality measure of pi) | Zeilberger--Zudilin (2020), printed pp. 407 and 418: the irrationality measure of `pi` is at most `mu0=7.103205334137001727...`. Equivalently, for every `nu>mu0`, `|pi-p/q|>q^(-nu)` for all integers `p` and all sufficiently large positive integers `q`. | The named fixed point `pi`; P matches. | Gives a lower bound on each phase distance `||h(10^j-10^i)pi||`, not cancellation of the collective sums `S_h`, no outer weighted sum, and no `N^2/n` saving. | Explicit exponent; the paper does not display a numerical denominator threshold `Q_0(nu)` or global finite constant. Effectiveness is irrelevant to the more basic cancellation gap. | **NO. First failure W:** pointwise phase separation is not a weighted Fourier-energy upper bound. The quantified deficit calculation in Section 6 misses R by a factor of order `n`. |
| T2-BC (pi-specific orbit route; reused T2) | Bailey--Crandall (2001), Hypothesis A and Theorem 1.1, audited in T2: an unproved dynamical hypothesis implies normality of `pi` in base 2; the paper also gives a conditional base-16 route. | Fixed `pi`, but only under an unproved hypothesis. | The conclusions concern bases 2/16, not the decimal orbit `10^j*pi`. Base-10 uniform distribution would imply HFE by Section 4, but the cited theorem does not prove it. | Conditional asymptotic statements; no verified decimal premise. | **NO. First failure F/object:** the source does not control the base-10 orbit. Its hypothesis is also unproved. |

There is no YES row in this bounded matrix.

## 4. Why the metric sum and discrepancy rows would otherwise suffice

This section checks that the almost-everywhere label, rather than a hidden
frequency or quantifier mismatch, is the first obstruction in EG and FU.

Fix `A>0`, `epsilon>0`, and an integer `n>=1`, and put `H=ceil(A*n)`.
Suppose for the moment that one fixed `x` satisfies, simultaneously for the
finite set `1<=h<=H`,

```text
|S_h(N,x)| <= C_H(x)*sqrt(N*log log N)
```

for every sufficiently large `N`. EG gives this for almost every `x`; finite
intersection over `h<=H` and a maximum of finitely many thresholds are valid.
Since

```text
w(n,H,h) <= 2*10^(-n) + 1/(H+1),
sum_{h=1}^H w(n,H,h) <= 2*H*10^(-n) + H/(H+1)
                             < 1 + 2*H*10^(-n),
```

we get

```text
W(n,H,N,x)
  <= C_H(x)^2*N*log log N*(1 + 2*H*10^(-n)).       (1)
```

For this fixed `n`, the right side of (1), divided by `N^2/n`, tends to zero.
Hence a sufficiently large `N=N(A,epsilon,n,x)` gives the strict HFE bound.
A countable intersection over all positive integer frequencies `h` first gives
one conull set on which the EG bound holds for every fixed `h`. For any real
`A`, every cutoff `ceil(A*n)` is then a finite subset of those frequencies;
take a finite maximum of thresholds after `n` is fixed. The choice of
`epsilon` affects only how large the existential `N` must be. Thus every real
`A,epsilon>0` is handled on that one conull set, with `nstar=1`. No uniform LIL
threshold in growing `H` is needed because HFE permits `N` to be chosen after
`n`.

FU plus PH-D gives the same conclusion. Take the countable intersection of
FU's conull sets at all initial-point multipliers `h/10`, `h>=1`. For fixed
`H`, the resulting discrepancy LILs give simultaneous square-root-scale sum
bounds, and then the preceding calculation applies for every real
`A,epsilon>0` exactly as above.

This proves only the corresponding **almost-everywhere analogue** of HFE. A
conull set may omit any prescribed singleton. Neither algebraicity,
transcendence, irrationality, nor finite decimal computation proves that `pi`
belongs to these conull sets.

## 5. Exact parameter-mean-square calculation

The following calculation uses T10's actual weights and makes the averaging
obstruction inspectable. For `h>=1`, orthogonality of distinct integer
frequencies gives

```text
integral_0^1 |S_h(N,x)|^2 dx
 = sum_{0<=j,k<N} integral_0^1 e(h*(10^j-10^k)*x) dx
 = N,                                                    (2)
```

because `10^j=10^k` exactly when `j=k`. Therefore

```text
integral_0^1 W(n,H,N,x) dx
 = N*sum_{h=1}^H w(n,H,h)
 < N*(1 + 2*H*10^(-n)).                                 (3)
```

For any `epsilon>0`, Markov's inequality and (3) give

```text
measure{x : W(n,H,N,x) >= epsilon*N^2/n}
 < n*(1+2*H*10^(-n))/(epsilon*N).                       (4)
```

For fixed `A,epsilon`, set `H=ceil(A*n)` and choose, for example,

```text
N_n > 2^n*n*(1+2*H*10^(-n))/epsilon.
```

Then the right side of (4) is `<2^(-n)`. The first Borel--Cantelli lemma
shows that, for each fixed `A,epsilon`, almost every `x` has only finitely many
failures at these selected `N_n`.

One extra domination is needed to put **all** real `A,epsilon` on one conull
set: the HFE weights are not monotone in `H`, because `1/(H+1)` changes. For
each positive integer `m`, define

```text
U(n,m,N,x) = sum_{h=1}^{m*n+1} |S_h(N,x)|^2/(pi*h).
```

If `0<A<=m`, then `ceil(A*n)<=m*n+1` and every HFE weight is at most
`1/(pi*h)`, so

```text
W(n,ceil(A*n),N,x) <= U(n,m,N,x).                         (5)
```

Orthogonality gives

```text
integral_0^1 U(n,m,N,x) dx
 = (N/pi)*sum_{h=1}^{m*n+1} 1/h
 <= (N/pi)*(1+log(m*n+1)).                               (6)
```

For each positive integer `m` and positive rational `rho`, choose integer
`N_(m,rho,n)` so large that Markov's upper bound for

```text
U(n,m,N,x) >= rho*N^2/n
```

is `<2^(-n)`. Borel--Cantelli and a countable intersection over `(m,rho)`
give one conull set. For `x` in it and arbitrary real `A,epsilon>0`, choose an
integer `m>=A` and a rational `0<rho<epsilon`; equations (5)-(6) give HFE at
all sufficiently large `n`, with the selected `N_(m,rho,n)`. Thus the full
QA-QN order holds for almost every `x` without any false cutoff monotonicity.

This exact weighted argument still says nothing about `x=pi`: integration,
Markov, and Borel--Cantelli produce an unspecified conull set. Finite
computations of `pi` cannot certify membership in it.

## 6. Quantified irrationality-measure comparison

Let

```text
mu0 = 7.10320533413700172750577342281...
```

be the upper bound proved by ZZ. By the source definition, for every fixed
`nu>mu0` there is an unspecified `Q_0(nu)` such that for all `q>=Q_0(nu)` and
all integers `p`,

```text
|pi-p/q| > q^(-nu).                                      (7)
```

For `0<=i<j`, `h>=1`, and `q=h*(10^j-10^i)`, choose `p` nearest to `q*pi`.
The irrationality estimate implies

```text
||h*(10^j-10^i)*pi|| > [h*(10^j-10^i)]^(1-nu)            (8)
```

once `q>=Q_0(nu)`. For example, any `nu=7.104` is allowed eventually, so the
right side has order at least `h^(-6.104)*10^(-6.104*j)` up to a fixed
base-10 factor.

Expand one square exactly:

```text
|S_h(N,pi)|^2
 = N + 2*sum_{0<=i<j<N} cos(2*pi*h*(10^j-10^i)*pi)
 = N^2 - 2*sum_{0<=i<j<N}(1-cos(2*pi*d_ij)),              (9)
```

where `d_ij=||h*(10^j-10^i)*pi||`. For `0<=d<=1/2`,
`1-cos(2*pi*d)>=8*d^2`. Direct termwise insertion of (8) into (9), restricted
to pairs for which `h*(10^j-10^i)>=Q_0(nu)`, therefore certifies the
subtraction

```text
sum_{0<=i<j<N, h*(10^j-10^i)>=Q_0(nu)}
  [h*(10^j-10^i)]^(-2*(nu-1))
  <= C_nu*h^(-2*(nu-1))*sum_{j<N} j*10^(-2*(nu-1)*j),    (10)
```

and the final series converges as `N->infinity`. Thus the upper bound obtained
by this direct termwise argument improves the trivial `N^2` bound only by a
certified bounded subtraction per fixed `h`. This does **not** bound the true
deficit in (9), which may be much larger; it says only that the irrationality
measure lower bounds alone do not certify `|S_h|=o(N)`, collective phase
cancellation, or a simultaneous growing-frequency estimate.

Indeed, the unconditional trivial bound `|S_h|<=N` and the exact weight sum
from Section 4 give only

```text
W(n,ceil(A*n),N,pi)
 < N^2*(1+2*ceil(A*n)*10^(-n)) = O_A(N^2),                (11)
```

where HFE requires `<epsilon*N^2/n`. The bounded subtraction certified by the
direct use of (8)-(10) does not supply the missing factor `1/n`, regardless of
how large the existential `N` is chosen.

This is a verdict on the direct applicability of the pinned pointwise
irrationality-measure theorem, not a theorem that no argument could combine it
with genuinely new distribution information.

## 7. Pair-correlation scale is not the HFE scale

RZ pair correlation uses

```text
(1/N) * #{1<=i!=j<=N : ||alpha*(10^j-10^i)|| <= s/N} -> 2*s.
```

HFE instead has an external digit length `n`, radius `10^(-n)`, cutoff
`ceil(A*n)`, a positive weighted Fourier sum, and an existential
`N=N(A,epsilon,n)`. Choosing `N` of order `10^n` can make `s/N` comparable
to `10^(-n)`, but it does not convert the pair-correlation limit into T10's
weighted inequality. More importantly, RZ is a.e. in `alpha` and supplies no
statement at `alpha=pi`.

No finite pair-count computation repairs either issue. A computation checks
only finitely many `n`, frequencies, and sample sizes, while HFE contains an
eventual universal quantifier over `n`.

## 8. Reuse of T2 and T28

This artifact does not reproduce their broader surveys.

- Accepted T2 already audits factor complexity, decimal normality, finite
  pi-digit statistics, and Bailey--Crandall. It establishes no verified
  base-10 normality or equidistribution hypothesis for `pi`.
- Recorded pi-digits T28 already pins and checks EG, Philipp, and Fukuyama
  against T27's different unweighted certificate. Its accepted audit, gate
  evidence, hash manifest, and primary PDFs are staged under `t28/`. T11
  reuses its theorem transcriptions and source pins, then performs only the
  new HFE weight and quantifier calculations in Sections 4-5.

Exact dependency paths and hashes are in `SOURCE_MANIFEST.md`.

## 9. Bounded conclusion

Within the bounded matrix, no pinned theorem proves `HFE_pi`.

- The strongest direct lacunary-sum and discrepancy estimates match the base,
  exponential sums, finite-frequency handling, and HFE quantifier order only
  for almost every initial point. Their first failure is fixed `x=pi`.
- The primary pair-correlation and variance results are also metric; their
  normalizations are additionally not T10's weighted energy.
- The deterministic discrepancy bridge is conditional on an unproved
  fixed-`pi` discrepancy estimate.
- The pointwise irrationality-measure theorem genuinely applies to `pi`, but
  supplies individual exponentially small phase-separation bounds rather than
  collective cancellation. Its direct bound remains on the `N^2` scale.

This all-negative result identifies applicability gaps only. It is not
evidence that `HFE_pi`, C2, C1, or canonical A1 is false, and it makes no
exhaustive novelty claim.
