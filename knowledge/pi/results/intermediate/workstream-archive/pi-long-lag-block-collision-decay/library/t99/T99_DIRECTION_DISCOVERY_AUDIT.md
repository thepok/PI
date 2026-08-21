# T99 bounded direction-discovery audit for G10

Audit date: 2026-08-09 UTC.

Claim labels:

- `machine-checked`: only the declarations in the copied T29 interface and
  other prior Lean files explicitly identified at that status.
- `literature-checked`: only the primary-source statements, pins, locators,
  and applicability comparisons in this report.
- `experiment`: only the finite T85 computations described in its replay note.

No theorem in this report establishes T29 at `alpha=pi`, C1, C2, or C3. No
almost-everywhere statement is specialized to pi.

## 1. Immutable statement and scope

`CANONICAL_STATEMENT.txt` is byte-exact and has SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

Its lines 1-10 ask for ordered, nonoverlapping decimal-block collisions and
one `C_s` for every `0<s<1`, selected before all positive `m,N`, with the
additive `N` term. T99 audits G10's distinct residual sparse-Fourier sibling,
the fixed-pi T29 premise. Establishing T29 would be a conditional route toward
the canonical problem; this report does not identify the two statements.

The corpus boundary is exact: the eight PDFs in `SOURCE_MANIFEST.md`, the
byte-exact T29 interface, and the prior artifacts pinned in Section 3. The
negative conclusion is limited to that corpus.

## 2. Literal T29 reconstruction

### 2.1 Parameters and quantifiers

The fixed-pi campaign uses

```text
(mu,c,alpha) = (8,1,Real.pi),  Q0 an arbitrary fixed natural number.
```

T29 itself is generic in `(mu,c,Q0,alpha)`. The later machine-checked T87/T90
specialization proves that for every `m>=1` and `r>=m`, `ArithmeticExcluded
8 1 Q0 m n r` is false, independently of `Q0`. Thus the literal G10
specialization keeps all lag/start cores below. It does not assume an
irrationality estimate at this point.

Write

```text
H = 10^m,
T_s(m,N) = N + N^2*10^(-s*m) = N + N^2*H^(-s).
```

The exact target is

```text
forall real s, 0<s<1 ->
  exists real A_s>=0,
  forall natural m,N, 1<=m -> 1<=N ->
    W(m,N;pi) <= A_s*H*T_s(m,N).                    (T29-pi)
```

One `A_s` is chosen before all `m,N`, blocks, frequencies, lags, and starts.
This is `WidthWeightedSquareFunction 8 1 Q0 Real.pi`, with the quantified
definition at T29 interface lines 70-83 and the fully unfolded form at lines
128-151.

### 2.2 Canonical blocks, frequencies, and records

T24's canonical partition is

```text
P(N) = canonicalDyadicPartition N
     = dyadicPartitionFrom 0 (N-1).bitIndices.reverse.
```

It partitions endpoint layers `[1,N)`. Each block is half-open `B=[a,b)` with

```text
a>=1, b=a+2^ell, and 2^ell divides a-1.
```

For each block define the core domain

```text
D(m,B) = {(r,n): 0<r, m<=r, a<=n+r<b}.
```

Every core has both Boolean orientations and signed frequencies

```text
k_(r,n,+) =  10^n*(10^r-1),
k_(r,n,-) = -10^n*(10^r-1).
```

The inclusive multiplier set is exactly

```text
h in {1,...,H}; h=0 is absent and h=H is present.
```

At `alpha=pi`, the two orientations give

```text
exp(2*pi*i*h*k*pi) + exp(-2*pi*i*h*k*pi)
  = 2*cos(2*pi^2*h*10^n*(10^r-1)).
```

Consequently, with

```text
S_B(h) = sum_((r,n) in D(m,B))
           cos(2*pi^2*h*10^n*(10^r-1)),
w_B = sqrt(b^2-a^2),
```

the literal observable is

```text
W(m,N;pi) = 4*sum_(B in P(N)) (1/w_B)*sum_(h=1)^H S_B(h)^2.   (2.1)
```

This substitution is independently visible in machine-checked T90, lines
66-129 and 157-217 of the vendored `T90_KERNEL_SPECIALIZATION.lean`; elimination
of the arithmetic exclusions is at lines 68-94 of
`T87_KERNEL_SPECIALIZATION.lean`. The T29 source itself defines the equivalent
complex block vector and square function at lines 41-68. No block, sign, or
endpoint is omitted in (2.1).

### 2.3 Quantitative sizes a candidate must see

For one endpoint `E=n+r`, there are `(E-m+1)_+` cores. Therefore

```text
K_B = |D(m,B)| = sum_(E=a)^(b-1) (E-m+1)_+,
number of signed records = 2*K_B.
```

For `E<N` and `h<=H`, every positive phase integer satisfies

```text
Q = h*10^n*(10^r-1) < 10^(m+N).
```

The target changes regime near `N=H^(s)`: it is `O_s(H*N)` below that
transition and `O_s(H^(1-s)*N^2)` above it. In the critical band used by T90,
`H<=N^2<=2H` and `s=1/2`, it is comparable to `H*N`. A theorem that only
prevents one `Q*pi` from being too close to an integer does not control the
positive sum of squared, pooled block sums in (2.1).

## 3. Duplication matrix

The pins below are members of the delivered `PRIOR_PINNED_CORPUS.tar`; the same
paths are workspace-relative to the T99 `knowledge_library`. The archive has
SHA-256 `68ed33e72b941db6c25664dcfdcf4d969d197ceee46e90120f898354df748b61`,
and `verify_sources.sh` extracts and checks every member hash. `proof sketch`
means an unverified note, not an established premise.

| Item | Status and pin | Actual overlap with T29 | First unmet condition at scale |
|---|---|---|---|
| T5 | Source applicability audit, `t5/APPLICABILITY_MATRIX.md`, SHA `ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406` | Metric lacunary discrepancy, pair correlation, shrinking targets, random strings, and conditional Bailey-Crandall; comparator is mainly residual near-return count, not (2.1) | Fixed pi and a nonasymptotic aggregate `O_s(N+N^2*10^(-sm))`; separate discrepancy errors can be `N^(3/2)*sqrt(log log N)`, not `O(N)` |
| T21 | Source applicability audit, `t21/T21_APPLICABILITY_AUDIT.md`, SHA `b468e509c4aa3b8bad7d833458578f94b4a5f0d95c53567a69a69e1598c525ae` | Vector/maximal and sparse large-sieve routes to T12's L1 sum, without T29 block increments or widths | `sum_(h<=H)|S_h(pi)| <= B_s*H*T_s(m,N)` uniformly in all `m,N`; norm/a.e. estimates give no pi trace |
| T63 | `machine-checked` finite identities, `t63/T63ExactFiniteFourthMoment.lean`, SHA `33521ed540153b2483b60d37edea6dd9b250dd304b56b4712d40e132e10ace8e` | Primitive selected-plus-defect sector only at `m=1`, `N_t=4*2^t+1`, one block, `h<=10` | Unproved `exists A forall t, sum_(h<=10) X_h(N_t)^2 <= A*N_t^2`, lines 951-956 |
| T68 | `machine-checked` conditional reduction, `t68/T68HalfArcDiscrepancy.lean`, SHA `65936350dad95e2b29435633d6ceabd5a5fc79ce9ac7ca19737126dbd1a9e0e4` | Same `m=1` dyadic primitive slice, through separate shifted half-arcs | One `Delta` before every `t,h<=10,r<H_t,y`, with excess `<=Delta*(N_t-r)/(H_t-1)`, lines 97-105 |
| T70 | Source audit, `t70/T70_SOURCE_PINNED_APPLICABILITY_AUDIT.md`, SHA `6f7f2260af4904dcea7b75c22833513313faa6e1a3b02cefd5c116b14450af17` | Averaged discrepancy, large sieve, finite-field, and sparse-modulus routes for the same T69 `m=1` pooled slice | `Re A_t(pi)<=C*H_t*N_t` uniformly in `t`, lines 395-419; rational transfer needs roughly `|pi-a/p|<=10^(-N_t)*N_t^(-O(1))` |
| T78 | No delivered mathematical artifact. `.research/orchestrator-escalations.json`, SHA `96818d8cbcf9c132ac4f666429ede133d997b6ae7d49a29f30e027ed9eded9e8`, lines 308-313 records only a malformed-result pipeline casualty | It cannot be counted as a route. The T80 sketch says it reconstructs staged T78, but that is retrospective and unverified | No T78 quantitative condition is replayable. Under the T80 reconstruction, the gap is still `|A_t(pi)|=O(H_t*N_t)` |
| T79 | `machine-checked` housekeeping, `t79/T79HousekeepingBridges.lean`, SHA `cd01d86a1b3e98791fd3e20a1fe69a612e0fc07e917d52e0f82e239d33dc2279` | Expands arithmetic exclusions and public finite instances; no new analytic route | The already named cancelling and primitive shell-incidence premises, each `O_s(T_s(m,N))` before T49 assembly |
| T80 | `proof sketch`, `notes/t80/T80_POSITIVE_WEIGHTED_CAUCHY_BARRIER.md`, SHA `4d422c17fb22b2d24ba934ca667ab7e43508a4bcb8ae96158cf5c7ada024caa1` | Positive-weight Cauchy on the T69 `m=1` pooled slice | The sketch argues an unsigned relative loss at least `sqrt((5/12)q)`, with `q asymp sqrt(N_t)`, while signed `|A_t(pi)|=O(H_t*N_t)` remains unproved |
| T81 | `machine-checked` coefficient obstruction, `t81/T81AdjacentIndexPairing.lean`, SHA `6a85bb7cece8c58cc945fc850b0257a646211ce31215b8cbeda3cbd020337d76` | Classifies `(10,k)<->(1,k+1)` equal-frequency pairings in the same pooled slice | Coefficients add rather than cancel; paired coefficient mass normalized by `H_t*N_t` grows at least on the order of `sqrt(N_t)`. Cancellation after evaluation at pi is still needed |
| T82 | `proof sketch`, `notes/t82/T82_SHIFT_SUMMATION_BY_PARTS.md`, SHA `1f7065745b8c35ea8c3a1b9cb44c1ec436bb49a84074715cfe56f779207ec878` | Multiplier-nine recurrence and Abel summation in the same T69 slice | Direct combined signed control of its `B_t+R_t`; separated positive mass is claimed to grow like `4^m*H_t*N_t`, so positive-cost estimates do not suffice |
| T85 | `experiment`, `t85/REPLAY.md`, SHA `421d1d304c7ed7da61e9a7fa34eb4d80c29e76c2affa2cbd2a46cf12d11447ff` | Closest finite evaluation of literal (2.1), all blocks and `h<=10^m`, at `(8,1,pi)` | Only `s=1/2`, `m=1` dyadic cases and four transitions through `(m,N)=(5,317)`; fifteen ratios below one give no `A_s` for all `m,N` |
| T90 | `machine-checked` exact critical-band reduction, delivered directly as `T90_KERNEL_SPECIALIZATION.lean`, SHA `0481de1cbdb9c8466efa6bff5ceb4ceb684536484ecdf6429f062ab2adc2ab90` | Full literal (2.1), but only `s=1/2` and `H<=N^2<=2H` | Unproved `CORR_pi`, lines 345-362. It would give `(5/2)*H*(N+N^2/sqrt(H))` only in that band; all other `s,N` remain |
| T93 | No T29 artifact. The only surviving T93 entry is for the different `pi-positive-decimal-factor-entropy` program and records a malformed-result pipeline casualty: escalation file above, lines 364-369 | No route or theorem can be mapped to T29 | Indeterminate; it is not evidence and not a duplicate |

### Recently audited pi-representation routes

| Route | Status and pin | First unmet quantitative condition |
|---|---|---|
| T13 many-anchor incidence | `proof sketch`, `notes/t13/T13_MANY_ANCHOR_INCIDENCE.md`, SHA `7c2298029c4f66b613d03405caefa60567e9b1a34632336e67e6cf3bfff12f1e` | The source-pinned irrationality measure gives a subcritical exponent below about `0.16385`; the sketch needs incidence `Q^(1-a+delta-o(1))` for some `delta>0`, not merely `Q^(1-a) log Q` |
| T35 cancelling repunits | `proof sketch`, `notes/t35/T35_SUBCRITICAL_CANCELLATION_SAVING.md`, SHA `e92c9cfcfae6a00842fc661f4bdcf827ddf076fc4a655d3a7cc60a380f26bfb1` | `ARI_super(36/5)`: all-scale weighted incidence `O_s(T_s(m,N))` on `d>=Q_*` and `31(v+rho)>5m` |
| T47 primitive off-diagonal | `proof sketch`, `notes/t47/T47_FIXED_PI_PRIMITIVE_OFFDIAGONAL.md`, SHA `e3ef74182bcd0996f134e0a1c4ea7d8e1fbd762aa7e0f80cf940277d244eac41` | `API_prim`: primitive shell incidence `O_s(T_s(m,N))`; the `36/5` pointwise estimate has no saving in the supercritical range |
| T92/T95/T97 variable phase | T92 and T95 are `proof sketch`, SHA `d5b6032a52f4bbe631eb89b8ba89c40cea0d34001d4c361085ea729c1ef82233` and `fbc6a0dd2c3b33be24dd539a61ec69cdf554751761398a78190b0ec93a1c1b9f`; T97 has a `machine-checked` bridge plus prose SHA `37ca19e081316174b5e5ebdc829ae14ba1ae63f63b4cead1ffdb9a97cf89a3a2` | The T97 bridge gives the second-moment bound. The T97 note argues an a.e. eventual critical-band conclusion as an unverified `proof sketch`; no theorem puts `pi` in the good set. Metric evidence is not a fixed-pi result |

The matrix has four exhausted clusters: metric/L1 (`T5,T21`), the `m=1`
pooled slice (`T63,T68,T70,T80-T82`), cancelling/primitive incidence
(`T35,T47`), and the critical band (`T90` plus variable-phase siblings).
T85 is finite evidence. T78 and T93 supply no replayable mathematical content.

## 4. Bounded external candidate audit

### Candidate P1: quantitative transcendence at pi

Zeilberger-Zudilin define the irrationality measure on physical page 2:

> the smallest number mu such that `|x-p/q| > 1/q^(mu+epsilon)` holds for
> any `epsilon>0` and all integers `p,q` with sufficiently large `q`.

Physical page 13, `World record`, concludes:

> the irrationality measure of pi is bounded above by
> `7.10320533413700172750577342281...`.

Let `mu0` denote that decimal. For every `eta>0` and sufficiently large `Q`,

```text
||Q*pi|| > Q^(-(mu0-1+eta)).                          (4.1)
```

Literal substitution uses

```text
Q = h*10^n*(10^r-1), h<=H, n+r<N, hence Q<10^(m+N).
```

Thus the worst guaranteed separation available from (4.1) is only of order

```text
10^(-(6.103205334137...+eta)*(m+N)).
```

First unmet condition: no source hypothesis fails, but the conclusion has the
wrong type and scale. It is an individual lower bound against resonance. T29
needs an upper bound for the positive aggregate (2.1) of size
`O_s(H*T_s(m,N))`. Individual nonresonance supplies no cancellation among the
`K_B` phases, no sum over `h`, and no block-width budget.

### Candidate P2: Archimedean logarithmic forms

Matveev physical page 1 defines

```text
Lambda = b_1 log(alpha_1)+...+b_n log(alpha_n),
b_j in Z, alpha_j in K*, K an algebraic number field.
```

Physical page 3, Theorem 2.1, assumes the logarithms are Z-linearly
independent and `b_n != 0`, and states

```text
log|Lambda| > -C(n)*C0*W0*D^2*Omega.                 (4.2)
```

The displayed definitions there require
`A_j>=max(D*h(alpha_j),|log(alpha_j)|)` and give the explicit `C(n),C0,W0`.

Attempt the exact pi phase with

```text
z = exp(2*pi^2*i), log z = 2*pi^2*i,
Lambda = Q*log z - 2*p*log(-1) = 2*pi*i*(Q*pi-p).
```

First unmet condition: Matveev requires `z` algebraic; no such fact is known.
Keeping the algebraic base `-1` instead puts the noninteger coefficient
`2*pi*Q` where the theorem requires an integer. The theorem fails before any
numerical scale is available. Even hypothetical algebraicity would yield an
individual power-law lower bound in `Q`, not (2.1).

### Candidate P3: sparse exact linear relations

Evertse-Schlickewei-Schmidt physical pages 1-2 consider

```text
a_1*x_1+...+a_n*x_n=1, x in Gamma subset (K*)^n,
```

where `K` is algebraically closed of characteristic zero and `Gamma` has
finite rank `r`. A solution is nondegenerate when no nonempty subsum vanishes.
Theorem 1.1 states exactly

```text
A(a_1,...,a_n;Gamma) <= exp((6*n)^(3*n)*(r+1)).       (4.3)
```

Put `z=exp(2*pi^2*i)`. Since pi is irrational, `z` has infinite
multiplicative order. Any exact sparse relation

```text
sum_(j=0)^(L-1) c_j*z^(q_j)=0
```

normalizes to (4.3) in `K=C` and a finite-rank group generated by `z`; no
algebraicity of `z` is required.

First unmet condition: the theorem counts exact nondegenerate zeros only. It
gives neither a lower bound for a nonzero sparse form nor an upper bound for
its modulus. T29 benefits from small sums, so exact-zero scarcity points in
the wrong direction. At one block `L` can be on the order of `K_B`, making
(4.3) enormous, while the required output remains `O_s(H*T_s(m,N))` after all
blocks and multipliers.

### Candidate P4: modular exponential sums

Garaev physical pages 1-3 take a prime `p`, an integer `g` of multiplicative
order `T mod p`, consecutive intervals of lengths `N0<=p` and `M<=T`, and the
additive character `e_p`. Section 2, Theorem 1 assumes `M<p^(2/3)` and writes

```text
sum_(n in I) |sum_(u in J) e_p(a*n*g^u)| = N0*M*Delta,
Delta <= p^(o(1))*[
  M^(-3/8)
  +(p/(N0*M^(5/2)))^(1/4)
  +(p/(N0^(4/3)*M^(7/3)))^(3/16)
  +(p/(N0^2*M^(3/2)))^(1/4)].                        (4.4)
```

For a single T29 channel, `g=10` and the geometric variable resembles the
start `n`, but (4.4) is an L1 sum of inner moduli, its outer multipliers are
consecutive rather than the sparse `h*(10^r-1)`, and it is at `a/p`, not pi.

To replace the largest real character of frequency below `10^(m+N)` by a
rational phase while keeping polynomial total coefficient error requires at
least

```text
|pi-a/p| <= 10^(-(m+N))*(m+N)^(-O(1)).               (4.5)
```

At ordinary `p^(-2)` approximation scale, (4.5) forces
`p >= 10^((m+N)/2)` up to polynomial factors. The T29 index lengths are then
`p^(o(1))`; every positive power of `p` in (4.4) is terminal, and the required
order of 10 modulo such approximating primes is unknown.

First unmet condition: the real fixed phase lacks the exponentially accurate
rational/modular transfer (4.5), together with the consecutive-support and
order hypotheses. This is a scale failure, not evidence that the real sum is
large.

### Candidate P5: averaged lacunary orthogonality

Aistleitner-Fukuyama physical page 7, Theorem 4, states for distinct positive
integers `n_1,...,n_L`, fixed `z in (0,1)`, and their centered periodized
interval indicator `I_[a,a+z]`:

```text
integral_0^1 integral_0^1
  (sum_(k=1)^L I_[a,a+z](n_k*x))^2 dx da
  = z*(1-z)*L.                                        (4.6)
```

For a fixed T29 block and multiplier, the positive integers
`n_(r,n)=h*10^n*(10^r-1)` are distinct. At `z=1/2`, (4.6) has the exact
linear average `L/4`, the random-model scale.

First unmet condition: both phase `x` and interval origin `a` are integrated.
The theorem gives no trace at `x=pi`, no supremum in `a`, and no pooled
cross-channel cancellation. The first missing quantitative passage is from a
linear `L2(dx da)` average to the point value (2.1) at pi uniformly over all
`m,N`. This candidate also concerns interval indicators, not directly the
complex block vector, so a fixed-trace theorem alone would still need an exact
output bridge.

### Candidate P6: expanding-map and Gibbs arithmetic dynamics

Chernov-Kleinbock physical page 3, Theorem 1.4, says condition `(SP)` implies

```text
S_N = E_N + O(E_N^(1/2)*log^(3/2+epsilon)(E_N))       (4.7)
```

for almost every point. Physical page 4, Theorem 1.7, applies this to
`T(x)=beta*x mod 1` with its smooth invariant measure and any divergent
sequence of subintervals. Physical page 6, Theorem 2.1, applies it to
`D`-nested cylinders in a Gibbs shift.

For `beta=10`, a decimal cylinder of length `m` has measure `10^(-m)`.
This matches the decimal dynamics, but T29 compares blocks generated by the
same prescribed orbit and pools all record frequencies.

First unmet condition: (4.7) is an invariant-measure almost-everywhere
statement and does not certify the orbit of pi. Its target cylinders are
prescribed; T29's collision target is self-generated. Quantitatively, the
onset and error are not uniform in growing `m,N`, and (4.7) does not bound the
width-weighted square function (2.1).

### Candidate P7: Fourier-decaying-measure pseudorandomness

Technau-Zafeiropoulos physical pages 2-3 assume

```text
|mu_hat(t)| << |t|^(-eta)                             (4.8)
```

for some `eta>0`. Their Theorem 1 says that for a lacunary integer sequence
`n_(k+1)/n_k>=q>1`, for `mu`-almost every `x`,

```text
1/4 <= limsup N*D_N(n_k*x)/sqrt(N*log log N) <= C,
C <= 166+664/(sqrt(q)-1).                             (4.9)
```

For fixed `(h,r)`, `n_k=h*(10^r-1)*10^k` has `q=10`.

First unmet condition: direct point-mass specialization would use `delta_pi`,
whose Fourier transform has modulus one and fails (4.8) at every scale. The
theorem's almost-everywhere conclusion for a Fourier-decaying measure does not
force inclusion of pi, and no theorem here separately proves pi is a good point.
Even an illicit channelwise specialization gives errors of order
`sqrt(L*log log L)` with separate onsets; summing channels loses the fixed
constant needed for `O_s(H*T_s(m,N))` and does not preserve pooled cancellation.

### Candidate P8: conditional fixed-pi digital dynamics

Bailey-Crandall PDF page 2, Hypothesis A, considers

```text
x_0=0,
x_n=(b*x_(n-1)+r_n) mod 1,
r_n=p(n)/q(n), 0<=deg p<deg q,
```

and hypothesizes that the orbit either has a finite attractor or is
equidistributed. Page 3, Theorem 1.1, states:

> On Hypothesis A, each of the constants pi, log 2, zeta(3) is normal to
> base 2, and log 2 is also normal to base 3.

First unmet condition: Hypothesis A is unproved. Even granting it, the pi
conclusion is base 2/base 16, not decimal. Normality gives, for each fixed
binary block length `m`, a collision asymptotic `N^2/2^m+o_m(N^2)` but no
finite-sample rate uniform in `m,N`, no decimal `h<=10^m` channels, and no
width-weighted estimate. It therefore fails before the T29 quantitative scale.

## 5. Three-program synthesis

The required synthesis is performed before any successor is considered.

1. Pointwise arithmetic program: P1 is genuinely pi-specific but only
   individual nonresonance. P2 fails algebraicity/integer-coefficient gates.
   P3 controls exact equations in the wrong direction. P4 loses the real phase
   at exponentially large modulus. None produces cancellation among a growing
   family of decimal frequencies.
2. Transfer/arithmetic-dynamics program: P5 has the correct linear averaged
   scale; P6 has quantitative recurrence for smooth/Gibbs typical points.
   Both stop at the fixed trace and neither handles the self-generated pooled
   square function.
3. Deterministic-pseudorandomness program: P7 quantifies typical lacunary
   discrepancy under Fourier decay, while P8 names pi only conditionally and
   in the wrong base. Neither gives a decimal, fixed-pi, all-scale rate.

The common missing object is not maximality, a block convention, or another
metric moment. It is a pi-specific theorem that controls simultaneous additive
cancellation for

```text
{h*10^n*(10^r-1): 1<=h<=10^m, m<=r, n+r<N}
```

after grouping by canonical endpoint blocks and paying the literal widths.
Stating that estimate is exactly T29 (or a previously named incidence/CORR
reformulation), so it is not a genuinely new route.

## 6. Source-pinned negative map

No genuinely new ranked pi-specific route survives in the audited corpus, so
no successor experiment or theorem is scheduled. P1 reaches fixed pi but
stops at individual separation of order at worst
`10^(-6.103...(m+N))`; P2 fails algebraicity; P3 counts exact zeros only; P4
requires exponentially accurate rational transfer and useful multiplicative
order; P5 and P6 average over phase or almost every orbit; P7 excludes the
point mass at pi and remains metric; P8 is conditional, binary, and lacks an
all-scale rate. This negative map is explicitly limited to primary sources
P1-P8 and prior pins in Section 3. It does not assert that no theorem outside
that corpus can prove T29, and it makes no fixed-pi claim from metric evidence.
