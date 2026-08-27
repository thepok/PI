# T112: finite carry-cocycle spectral and local-limit scout

Search date: 2026-08-10 UTC.

Claim labels: source statements checked against the five pinned primary PDFs
are `literature-checked`. The carry-matrix packaging where explicitly described
as derived, all T107 substitutions, all fingerprint comparisons, and the native
transfer implication are `proof sketch`. The deterministic replay is an
`experiment`; it checks transcription and finite arithmetic only.

This report proves no theorem about pi, canonical A1, C1, C2, normality, or
decimal factor complexity. Related-model local limits, spectral gaps, and
finite checks are not progress on any of those fixed-pi claims.

```text
PRIMARY_SOURCE_COUNT: 5
PRIMARY_SOURCE_CAP: 12
SEARCHED_LANE_COUNT: 4
CANDIDATE_COUNT: 4
CANDIDATE_CAP: 4
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

## 1. Immutable statement and normalized scope

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, the canonical question defines

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all diagonal pairs are included, the circle inequality is
strict, and the open quantifier order is

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 such that
A*n*Q_pi(n,N) <= N^2.
```

T112 studies A13/A14 model mechanisms only. Its finite carry laws average over
random integers or random digit columns, and its signed transducer model is an
explicit binary sequence. None is the fixed decimal orbit of pi. In
particular, local anti-concentration of a carry count is not automatically
anti-concentration of orbit points near decimal boundaries.

The following potentially ambiguous phrases are fixed here.

1. A primary source is counted once even when both its PDF and a `pdftotext`
   derivative are delivered.
2. A candidate is retained only when an explicit finite matrix, matrix
   recurrence, or transfer cocycle is displayed and a theorem quantitatively
   controls its law or sums.
3. Growing scale means `q=10^ell` with unbounded `ell`, not a fixed automaton
   checked at finitely many depths.
4. One triangular prefix family means the same positive `N(k)` must serve all
   `1<=ell<m<=k`; row-dependent prefixes do not qualify.
5. Constant-explicit means every numerical coefficient needed to compare with
   T107 is printed or derived. An unspecified source constant is recorded as a
   failed constant quantifier, not silently chosen.
6. The active T109 artifact was unavailable in the supplied library, so only
   its agenda-specified excluded fingerprint is used. The accepted T111 report
   was inspected as an unverified `proof sketch` note; none of its deductions
   is used as a discharged premise.

## 2. Bounded clean-context search

The search used four lanes and stopped after five primary papers:

1. symbolic entropy/collision theory: carry-increment local limits;
2. fixed-point lacunary dynamics: named finite-state binary cocycles;
3. arithmetic/fractal Fourier mechanisms: twisted finite-transducer operators,
   excluding ambient-measure decay;
4. short structured exponential sums: uniform unit-circle bounds for a named
   transducer sequence.

Exactly four candidates were retained. The fifth source was screened because
its general random-word transducer theorem clarifies the operator template but
does not add a different fixed-path mechanism. No source was added to fill a
cap. `SEARCH_LOG.md` records the bounded queries and stop decision.

| ID | Lane | Primary source | Role |
|---|---|---|---|
| S1 | symbolic carry local limit | Spiegelhofer--Wallner, *The binary digits of n+t* | F1 |
| S2 | decimal carry mixing | Hosten--Janvresse--de la Rue, *A central limit theorem for the variation of the sum of digits* | F2 |
| S3 | explicit carry chain | Diaconis--Fulman, *Carries, Shuffling, and an Amazing Matrix* | F3 |
| S4 | short structured sums | Balister, *Bounds on Rudin--Shapiro polynomials of arbitrary degree* | F4 |
| S5 | finite-transducer operator | Heuberger--Kropf--Wagner, *Variances and covariances in the Central Limit Theorem for the output of a transducer* | screened operator template |

Every URL, DOI, hash, theorem locator, and derivative locator is in
`SOURCE_PINS.md`. Five is below the cap twelve, and four candidates meet the
cap four.

## 3. Literal T64/T107 target

This section expands machine-checked local definitions; it does not assert
their premises for pi. The checked sources are
`knowledge_library/t64/AggregateFejerCriterion.lean`, SHA-256
`ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16`,
and `knowledge_library/t107/T107AveragedTriangularFejer.lean`, SHA-256
`45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`.

Put `q=10^ell`, let `P>0`, and write

```text
S_P(h) = sum_(0<=j<P) exp(2*pi*i*h*10^j*pi).
```

The child and parent active-boundary counts are

```text
B_c(ell,P) = activeBoundaryCount(piOrbit,P,10q,childCode,1/(400q^2)),
B_p(ell,P) = activeBoundaryCount(piOrbit,P,q,parentCode,1/(4q^2)).
```

The literal boundary load, budget, and normalized component are

```text
L_ell(P) = B_c(ell,P) + (1/2)B_p(ell,P),
L_ell(P) <= P/(40q),
D_boundary(ell,P) = 40q*L_ell(P)/P.                    (3.1)
```

The parent and child Fejer orders are

```text
H_p=40q^3, Q_p=q;       H_c=8000q^3, Q_c=10q.
```

T64's collected remainder is `R_ell(P)` with all signed aliases retained. Its
literal Fourier budget and normalized component are

```text
|R_ell(P)| <= P^2/(10q),
D_Fourier(ell,P) = 10q*|R_ell(P)|/P^2.                 (3.2)
```

T107 defines the row defect as the maximum of (3.1) and (3.2). Thus Fourier
cancellation cannot repair excessive boundary load.

For later calculations put

```text
A_c(ell)=2+log(800q^2+1),
A_p(ell)=2+log(40q^2+1),
W_ell=A_c(ell)^2+(1/2)A_p(ell)^2.
```

T64's kernel-checked collected `L1` estimate gives the following sufficient
condition. If

```text
|S_P(h)| <= epsilon*P for every 0<|h|<=8000q^3,
```

then

```text
D_Fourier(ell,P) <= 160q*W_ell*epsilon^2.              (3.3)
```

Consequently, for `0<theta<1`, the literal sufficient threshold is

```text
epsilon_ell(theta)=sqrt(theta/(160qW_ell)).             (3.4)
```

It is asymptotic to `q^(-1/2)/log q`, with all constants displayed.

### 3.1 Uniform boundary benchmark

For a uniform circle point, the boundary neighborhoods are disjoint at these
widths. Their exact total lengths are

```text
child:  2*(10q)*(1/(400q^2)) = 1/(20q),
parent: 2*q*(1/(4q^2))      = 1/(2q).
```

The expected weighted load is therefore

```text
P*(1/(20q)+(1/2)*(1/(2q))) = 3P/(10q),
D_boundary -> 40q*(3/(10q)) = 12.                       (3.5)
```

T107 needs `D_boundary<=1`. Hence ordinary equidistribution, an iid digit
model, or a stationary uniform carry input has the wrong natural boundary
constant by a factor of twelve. A usable mechanism would require selected
prefixes with sub-uniform boundary depletion, not merely a local limit.

### 3.2 Triangular bookkeeping

If one positive strictly increasing sequence `N(k)`, one weak empirical limit,
and one `0<theta<1` made both components at most `theta` for every
`k>=k0` and every `1<=ell<m<=k`, then

```text
sum_(ell=1)^(m-1) rowAnalyticDefect(ell,N(k))
  <= theta*(m-1)
  = (m-1)-((1-theta)*m-(1-theta)).                       (3.6)
```

Thus T107 would take `d=B=1-theta` and `m0=1`. Equation (3.6) is only
conditional bookkeeping. No candidate below supplies both components, the
weak limit, or the common triangle for pi.

## 4. F1: binary alternating-addend carry local limit

### 4.1 Exact source theorem and cocycle

S1 defines, for integers `t>=0` and `j in Z`,

```text
delta(j,t)=lim_(N->infinity) N^(-1)
  #{0<=n<N: s_2(n+t)-s_2(n)=j}.                           (4.1)
```

Equations (1.4)--(1.6), preprint p. 3, derivative lines 130--160, give

```text
delta(j,2t)=delta(j,t),
delta(j,2t+1)=(1/2)delta(j-1,t)+(1/2)delta(j+1,t+1).       (4.2)
```

For `gamma_t(v)=sum_j delta(j,t)exp(2*pi*i*j*v)`, (4.2) is the exact
two-state twisted carry cocycle

```text
(gamma_(2t),gamma_(2t+1))^T = A_0(v)(gamma_t,gamma_(t+1))^T,
(gamma_(2t+1),gamma_(2t+2))^T = A_1(v)(gamma_t,gamma_(t+1))^T,

A_0(v)=[[1,0],[exp(2*pi*i*v)/2,exp(-2*pi*i*v)/2]],
A_1(v)=[[exp(2*pi*i*v)/2,exp(-2*pi*i*v)/2],[0,1]].        (4.3)
```

The matrix packaging follows directly by Fourier transforming (4.2).

Let

```text
t_M=sum_(r=0)^(M-1) 2^(2r)=(4^M-1)/3.                    (4.4)
```

Its binary expansion is the named alternating word `101...01` and has exactly
`M` maximal one-blocks. S1 Theorem 1.2, preprint pp. 3--4, derivative lines
171--203, states that for `M>M0`, uniformly for every integer `j`,

```text
delta(j,t)=exp(-j^2/(2*kappa_2(t)))/sqrt(2*pi*kappa_2(t))
           + O(M^(-1)(log M)^4),                          (4.5)
M <= kappa_2(t) <= C*M.                                   (4.6)
```

The source says the error constant can be made explicit but does not print its
value in the theorem.

### 4.2 Literal T107 calculation and first failure

Even under the optimistic, unsupported identification of one boundary event
with one carry atom, split the target `1/(40q)` equally between the Gaussian
main term and error. From (4.5)--(4.6), a sufficient main-term condition is

```text
1/sqrt(2*pi*M) <= 1/(80q),
M >= (3200/pi)q^2 = 1018.5916... q^2.                    (4.7)
```

The error would additionally require, for the unprinted absolute constant
`C_LL`,

```text
C_LL*(log M)^4/M <= 1/(80q).                              (4.8)
```

Thus the source theorem gives a growing-scale form but not a literal numerical
threshold without extracting `C_LL` from its proof.

The first failed quantifier is earlier and structural: (4.1) averages the
integer input `n` while fixing an addend `t_M`. T107 averages the time index
`j` on the single orbit `{10^j*pi}`. No source map identifies a carry atom in
(4.1) with a parent or child decimal-boundary visit. Even a hypothetical
identification would address no Fourier remainder (3.2) and would vary `M`
with `ell` without supplying one common `N(k)`.

Cheapest kill test: demand the proposed map first on `M=1,2` and verify that
its source probability space is natural density over all integers, not the
first `P` shifts of one fixed decimal expansion. Failure of that domain map
rejects the transfer before any asymptotic constant is computed.

**Card assessment:** model calibration only. The source gives the sharpest
retained carry local limit, but its averaging variable and observable are
wrong.

## 5. F2: decimal addition carry mixing

### 5.1 Exact source theorem and matrices

Fix base `b>=2`. S2 takes Haar-random `b`-adic `x` and studies

```text
Delta^(r)(x)=s(x+r)-s(x)=s(r)-(b-1)*(number of carries).   (5.1)
```

For `r=b*rtilde+a`, `0<=a<b`, Proposition 3.1 and equation (19), preprint
p. 12, derivative lines 704--751, give

```text
mu^(b*rtilde+a)(d)
 =((b-a)/b)mu^(rtilde)(d-a)+(a/b)mu^(rtilde+1)(d+b-a).     (5.2)
```

Writing `F_r(u)=sum_d mu^(r)(d)exp(iud)`, (5.2) yields the exact derived
two-carry-state matrices

```text
(F_(bn+a),F_(bn+a+1))^T=M_a^(b)(u)(F_n,F_(n+1))^T,

M_a^(b)(u)=
 [[(b-a)e^(iau)/b,       a*e^(i(a-b)u)/b],
  [(b-a-1)e^(i(a+1)u)/b,(a+1)e^(i(a+1-b)u)/b]].           (5.3)
```

At `a=b-1`, the lower-left entry is zero and (5.3) remains valid. At `u=0`
the rows are stochastic and

```text
det M_a^(b)(0)=1/b; eigenvalues are 1 and 1/b.             (5.4)
```

S2 Theorem 1.2, preprint p. 3, derivative lines 115--120, says for every
`r>=1`,

```text
(b/4)rho(r) <= Var(mu^(r)) <= 2b^2 rho(r).                 (5.5)
```

Here `rho(r)` is the source's number of maximal zero blocks, maximal
`(b-1)` blocks, and intermediate singleton digits. Theorem 1.4, preprint
pp. 3--4, derivative lines 141--159, gives a base-dependent `K_b>0` with

```text
sup_x |F_r^cdf(x)-Phi(x)| <= K_b*rho(r)^(-1/8).            (5.6)
```

Lemma 4.3, preprint p. 22, derivative lines 1347--1370, gives the explicit
mixing bound

```text
phi(k) <= 2*((b-1)/b)^(k/2-1).                            (5.7)
```

Take the named decimal addends

```text
r_M=sum_(s=0)^(M-1)10^(2s)=(10^(2M)-1)/99.                (5.8)
```

Their decimal expansions are `101...01`; their source block counts are
`rho(r_M)=2M-1`.

### 5.2 Literal T107 calculation and first failure

For `b=10`, (5.5)--(5.6) imply the derived atom estimate

```text
max_d mu^(r)(d)
 <= 1/sqrt(5*pi*rho(r)) + 2*K_10*rho(r)^(-1/8).           (5.9)
```

Indeed a lattice atom is bounded by the corresponding Gaussian interval plus
two Kolmogorov errors, and `sigma_r^2>=(10/4)rho(r)`.

Splitting `1/(40q)` equally gives the explicit necessary sufficient tests

```text
rho(r) >= (1280/pi)q^2 = 407.4366... q^2,
rho(r) >= (160*K_10*q)^8.                                 (5.10)
```

The source does not print `K_10`, so (5.10) is not a numerically certified
threshold. More decisively, (5.2) averages Haar-random input digits when adding
`r`; it is not driven by successive digits of pi and does not represent the
event in (3.1). This averaging-variable/observable mismatch is the first
failed quantifier. The natural Haar benchmark also has defect 12 by (3.5), so
generic mixing points in the wrong direction for the unusually depleted T107
boundary budget.

Cheapest kill test: at `u=0`, compute the nontrivial eigenvalue `1/10`; then
compute the uniform boundary defect `12`. A proposal claiming that this
ordinary mixing gap directly proves a good T107 row fails because `12>1`,
before any frequency calculation.

**Card assessment:** model calibration only. It is the cleanest literal
decimal carry cocycle, but its stationary input is not the pi path and its
natural boundary normalization is incompatible with T107.

## 6. F3: Holte's base-ten carry chain

### 6.1 Exact source matrix and spectral theorem

S3 considers adding `n` independent base-`b` digit streams. If the incoming
carry is `i` and outgoing carry is `j`, formula (H1), printed p. 1, derivative
lines 20--43, gives

```text
P(i,j)=b^(-n) sum_(r=0)^(j-floor(i/b))
 (-1)^r binom(n+1,r) binom(n-1-i+(j+1-r)b,n).             (6.1)
```

The state space is `{0,...,n-1}`. Formula (H4), printed p. 2, gives stationary
law `pi_n(j)=A(n,j)/n!`; formula (H5), printed p. 2, derivative lines 66--97,
gives the complete spectrum

```text
1,b^(-1),b^(-2),...,b^(-(n-1)).                           (6.2)
```

Theorem 4.1, printed p. 9, derivative lines 453--485, gives the carry mean,
variance, and a Gaussian limit as `n->infinity`. Theorem 4.3, printed p. 10,
derivative lines 535--555, gives the asymptotic separation profile on the
cutoff window `r=2log_b(n)+log_b(c)` as `n` tends to infinity.

For the named two-addend base-ten chain, (6.1) is

```text
P_10=[[11/20,9/20],[9/20,11/20]],                         (6.3)
```

with stationary vector `(1/2,1/2)` and eigenvalues `1,1/10`.

### 6.2 Literal T107 calculation and first failure

The nontrivial spectral radius `1/10` is exact and dimension-free for the
first mode. It controls convergence of random-column carry states. It does not
control shrinking decimal-grid neighborhoods of `{10^j*pi}`. Even the most
optimistic identification of one boundary class with one state of (6.3) would
give stationary mass `1/2`, while T107's entire weighted boundary event has
budget `1/(40q)<=1/400` for `ell>=1`.

The first failed quantifier is the source premise that every digit in every
column is independent and uniform. The fixed pi orbit supplies neither fresh
columns nor the Markov transition (6.1). Moreover the state observable is a
carry value, not distance to a decimal boundary.

Cheapest kill test: verify (6.3), its stationary mass `1/2`, and the required
`1/(40q)`. Already at `q=10`, `1/2>1/400`; a state-identification transfer is
rejected by a factor 200. This does not refute a different pi-driven cocycle.

**Card assessment:** rejected as a transfer. The exact spectral gap is a
random-column model and its state masses have the wrong scale.

## 7. F4: Rudin--Shapiro Hadamard cocycle

### 7.1 Exact source theorem and named sequence

S4 defines

```text
P_0(z)=Q_0(z)=1,
P_(t+1)(z)=P_t(z)+z^(2^t)Q_t(z),
Q_(t+1)(z)=P_t(z)-z^(2^t)Q_t(z).                          (7.1)
```

This is the explicit matrix cocycle

```text
(P_(t+1),Q_(t+1))^T=A_t(z)(P_t,Q_t)^T,
A_t(z)=[[1,z^(2^t)],[1,-z^(2^t)]].                        (7.2)
```

For `|z|=1`, `A_t(z)^*A_t(z)=2I`. Proposition 4(a), preprint p. 3,
derivative lines 111--120, records the resulting energy identity

```text
|P_t(z)|^2+|Q_t(z)|^2=2^(t+1).                            (7.3)
```

The infinite coefficient sequence is the named Rudin--Shapiro sequence

```text
a_0=1, a_(2n)=a_n, a_(2n+1)=(-1)^n a_n.                  (7.4)
```

Theorem 1, preprint p. 2, derivative lines 55--75, proves for every `P>=1`
and every `|z|=1`,

```text
|sum_(j<P)a_j z^j| <= sqrt(6P-2)-1.                       (7.5)
```

Theorem 3, preprint p. 2, derivative lines 77--108, gives the arbitrary
interval bound `sqrt(10(n-m))`.

### 7.2 Literal T107 calculation and first failure

From (7.5), uniformly over every real linear frequency,

```text
P^(-1)|sum_(j<P)a_j exp(2*pi*i*alpha*j)| <= sqrt(6/P).     (7.6)
```

If this were the sum in (3.3), the exact sufficient prefix threshold would be

```text
P >= 6/epsilon_ell(theta)^2
  = (960/theta)qW_ell.                                    (7.7)
```

Thus the finite cocycle has more than enough all-frequency, all-prefix power:
there is no union-bound cost for `|h|<=8000q^3`.

The first failed quantifier is phase and weight, before frequency size. The
source controls the signed linear-phase sum `sum a_j z^j`; T107 needs the
unweighted lacunary phase `sum exp(2*pi*i*h*pi*10^j)`.

The cheapest exact identity test uses `a_0=a_1=a_2=1`. If for some nonzero
integer `h` there were constants `c,z` with

```text
exp(2*pi*i*h*pi*10^j)=c*a_j*z^j, j=0,1,2,
```

then `c=exp(2*pi*i*h*pi)` and `z=exp(2*pi*i*9h*pi)`. The
`j=2` equation would force `81h*pi` to be an integer, contradicting
irrationality of pi. This kills an exact geometric/Rudin--Shapiro transfer,
not an independently quantified approximation theorem.

No boundary observable occurs in (7.1)--(7.6), so even a phase conversion
would still need (3.1).

**Card assessment:** model calibration only. This is the strongest retained
finite cocycle at the Fourier scale, but it has the wrong phase fingerprint.

## 8. Screened operator template

S5 Definition 3.8, preprint p. 8, defines for a
finite transducer and input letter `epsilon`

```text
(M_epsilon(y))_(s,t)=y^delta
```

when there is a transition `s --epsilon|delta--> t`, and zero otherwise.
Theorem 3.9, preprint pp. 8--9, uses

```text
f(x,y,z)=det(I-(z/K)sum_epsilon x^epsilon M_epsilon(y))    (8.1)
```

to give linear means/covariances and a joint CLT for every complete,
subsequential, finally connected, finally aperiodic transducer under uniform
random input words. Example 4.1, preprint p. 13, applies it to width-`w`
non-adjacent form.

This source was not retained as a fifth candidate because its normalized
fingerprint is already exposed by F2 and F3: average over all input words,
obtain a finite Perron operator, and fail to control one named path. It supplies
no global off-zero spectral estimate uniform in a growing automaton or the
T107 boundary observable. It is retained in the source count because its exact
operator definition was inspected and supports the terminology used here.

## 9. Prior-fingerprint comparison

Verification levels are load-bearing. A `proof sketch` note is comparison
memory only and is never used as a discharged premise.

| Prior item | Status used | Normalized fingerprint | T112 separator |
|---|---|---|---|
| T64 | `machine-checked` one-row Fejer criterion | exact parent/child boundary and collected Fourier budgets imply one literal splitting row | T112 imports only these thresholds; it searches finite carry operators that might supply them and proves no T64 premise |
| T82 | unverified `proof sketch` with source-pinned Chudnovsky input | certification endpoint states expand by exactly factor 10 through common digits; finite certification does not synchronize T64 rows | F1--F3 average genuine arithmetic carries over random inputs; F4 is a signed cocycle. No certification bracket, perturbation, or endpoint coupling is used |
| T91 | source claims `literature-checked`, collision developments unverified `proof sketch` | exact finite-state block-collision recurrences for substitutions/paperfolding; aligned samples or representatives lose all-start mass | T112 studies carry-increment probability laws and a signed Fourier cocycle, never unsigned exact block equality or a representative atlas |
| T103 | source claims `literature-checked`, deductions unverified `proof sketch` | positive-entropy Toeplitz synchronization with periodic-hole towers and collision lower bounds | no entropy, tower, hole density, or periodic skeleton occurs here |
| T104 | source claims `literature-checked`, transfers unverified `proof sketch` | broad ambient Fourier decay, nonlinear Gibbs systems, metric lacunary correlations, and fixed-fiber failure | T112 excludes ambient measure decay; F1--F3 use finite carry states and F4 gives pointwise uniform circle bounds for a named digital weight |
| T105 | source claims `literature-checked`, transfers unverified `proof sketch` | additive energy, flattening, BSG, and modular geometric-sum estimates | no additive energy, subset extraction, modular approximation, or complete subgroup is used |
| active T109 | unavailable; no content inferred | perturbative coupling, excluded by agenda | no robustness or perturbation transfer is used; T82's interval correction is only a comparator |
| T110 | source claims `literature-checked`, T107 substitutions unverified `proof sketch` | higher-order Gowers uniformity, fixed-degree digital polynomial phases, and metric higher correlations | F4 is only a first-order all-circle square-root sum from a `2x2` Hadamard cocycle; no Gowers norm or growing order is invoked. F1--F3 are carry local limits |
| T111 | sources `literature-checked`; deductions unverified `proof sketch` | totally de Bruijn synchronization, odd-digit decimal-safe coding, and exact remote cyclic-label separation | no constructed boundary-avoiding sequence, safe-cylinder selection, or RD-pi premise is used |

The mandatory exclusions are therefore literal:

1. no perturbative coupling (active T109 fingerprint);
2. no broad ambient Fourier decay (T104);
3. no higher-order uniformity (T110);
4. no finite-state collision recurrence (T91);
5. no positive-entropy synchronization (T103);
6. no decimal-safe avoidance (T111 fingerprint).

F1/F2 are new only as finite carry **local-limit** models; F3 is an exact
random-column carry-chain gap; F4 is retained only as a short structured-sum
calibration. None changes a prior fixed-pi conclusion.

## 10. Native transfer hypothesis toward G19

The previous draft left a reference matrix and a "centered twisted product"
undefined. This replacement defines both, states their dimension-dependent
conversion, and gives constants that leave the required Fourier budget. It is
a reproducible Fourier-side spectral conjecture for the exact pi decimal-shift
recurrence and keeps the boundary side visibly separate. In particular, the
spectral conjecture is not a renamed assertion that pi avoids decimal
boundaries.

Let `d_j in {0,...,9}` be the decimal digits of pi after the decimal point. For
`L>=1`, put `D=10^L` and define the length-`L` sliding state

```text
x_j^(L)=sum_(r=0)^(L-1) d_(j+r)*10^(L-1-r) in {0,...,D-1},
x_(j+1)^(L) = 10*x_j^(L)+d_(j+L) mod D.                   (10.1)
```

Thus `x_j^(L)/D` is the `L`-digit truncation of `{10^j*pi}` and

```text
0 <= {10^j*pi}-x_j^(L)/D < 1/D.                           (10.2)
```

On `C^D`, with standard basis vectors `e_x`, define for every integer `h` the
fully specified twisted empirical transition operator

```text
T_(L,P)(h)
  = sum_(0<=j<P) exp(2*pi*i*h*x_j^(L)/D)
      e_(x_(j+1)^(L)) e_(x_j^(L))^*.                      (10.3)
```

This is a sparse `D`-state carry/shift cocycle determined only by the displayed
pi digit recurrence. For a nonnegative column-stochastic `D`-by-`D` matrix
`K` supported on the legal shift edges
`y=10x+a mod D`, `a in {0,...,9}`, and a stationary probability column vector
`v` (`K*v=v`), define

```text
zeta_h(x)=exp(2*pi*i*h*x/D),
J_(L,P)^(K,v)(h)=P*K*diag(v(x)*zeta_h(x)),
C_(L,P)^(K,v)(h)=T_(L,P)(h)-J_(L,P)^(K,v)(h).              (10.4)
```

The order of the factors is part of the definition. At `h=0`, `J` has total
mass `P`; at nonzero `h` it is the twisted stationary reference operator. If
`1_D` is the all-ones vector, column stochasticity gives exactly

```text
1_D^* T_(L,P)(h) 1_D
  = sum_(0<=j<P) exp(2*pi*i*h*x_j^(L)/D),
1_D^* J_(L,P)^(K,v)(h) 1_D=P*sum_x v(x)zeta_h(x),
|1_D^* C_(L,P)^(K,v)(h) 1_D|
  <= D*||C_(L,P)^(K,v)(h)||_(2->2),                        (10.5)
```

because `||1_D||_2=sqrt(D)`. This is the dimension-dependent conversion missing
from the previous draft.

Centering is necessary, not cosmetic. For fixed `h`, each observed transition
cell has one phase (the phase depends only on its source state), there are at
most `10D` possible source/next-digit cells, and their nonnegative counts sum
to `P`. Therefore

```text
||T_(L,P)(h)||_(2->2) >= max_(x,y)|T_(L,P)(h)_(y,x)|
  >= P/(10D).                                               (10.6)
```

An uncentered target `||T||<=epsilon*P/(2D)` would force
`epsilon>=1/5`, whereas (3.4) has `epsilon_ell(theta)<1/5` for every
`ell>=1` and `0<theta<1`. Thus the uncentered version is decisively refuted.

Fix `0<theta<1`, put `q=10^ell`, `H_ell=8000q^3`, and use the literal
`epsilon_ell(theta)` from (3.4). Define `Lambda_ell(theta)` to be the least
positive
integer `L` for which

```text
D_ell=10^L >= 4*pi*H_ell/epsilon_ell(theta).               (10.7)
```

For every `0<|h|<=H_ell`, (10.2), the elementary inequality
`|exp(iu)-exp(iv)|<=|u-v|`, and (10.7) give the explicit coding estimate

```text
|S_P(h)-1_D^*T_(L,P)(h)1_D|
  <= 2*pi*H_ell*P/D_ell
  <= (1/2)*epsilon_ell(theta)*P.                           (10.8)
```

**H-G19-twisted-cocycle (conjecture).** There exist `0<theta<1` and a
positive strictly increasing sequence `N(k)`, and for each `ell>=1` a concrete
column-stochastic legal-shift matrix `K_ell` and stationary probability vector
`v_ell`, such that, for every sufficiently large `k` and every `1<=ell<k`, with
`L=Lambda_ell(theta)` and `D=D_ell`:

```text
(H1-boundary, separate existing premise)
  L_ell(N(k)) <= theta*N(k)/(40q),
  where L_ell(P) is the literal weighted T107 load in (3.1);

(H2-native spectral premise)
  for every integer h with 0<|h|<=H_ell,
  |sum_x v_ell(x)zeta_h(x)| <= epsilon_ell(theta)/4,
  ||C_(L,N(k))^(K_ell,v_ell)(h)||_(2->2)
    <= epsilon_ell(theta)*N(k)/(4D);

(H3) the empirical circle measures at N(k) converge weakly.
```

Clause H1 is deliberately identified as the already-needed T107 boundary
premise; it is not claimed as a consequence of the cocycle and is not the new
transfer hypothesis. The native proposed input is H2: a stationary reference
Fourier bound and one centered operator-norm bound, uniform over a growing
frequency box, for the specified recurrence (10.1) and operators (10.3)--(10.4).
By (10.5), the two H2 inequalities each spend one quarter of the Fourier
amplitude budget; the deterministic coding bound (10.8) spends the remaining
half. Hence
`|S_(N(k))(h)|<=epsilon_ell(theta)N(k)` throughout the literal T64 frequency
box. Equation (3.3) then gives `D_Fourier<=theta`, while H1 gives
`D_boundary<=theta`. Therefore every such row has analytic defect at most
`theta`, and (3.6) applies with the explicit constants
`d=B=1-theta`, `m0=1`.

This is stronger than merely postulating the scalar exponential sums: H2
controls an entire `D_ell`-dimensional centered transition operator against a
fixed stationary reference at each scale. It is also
honestly incomplete as a boundary mechanism because H1 remains a separate
premise. No retained source proves H2 for pi. F1/F2 average a different input,
F3 uses iid columns, F4 has a signed linear phase, and S5 averages all words
rather than the path (10.1).

### Cheapest falsification test

For proposed `theta,N(k),K_ell,v_ell`, certified pi digits, and the smallest
declared `(k,ell)`, form the sparse operator (10.3), the explicit reference
(10.4), and compute

```text
R_boundary = 40q*L_ell(N(k))/(theta*N(k)),
R_reference = max_(0<|h|<=H_ell)
  4*|sum_x v_ell(x)zeta_h(x)|/epsilon_ell(theta),
R_centered = max_(0<|h|<=H_ell)
  4D_ell*||C_(Lambda_ell,N(k))^(K_ell,v_ell)(h)||_(2->2)
    /(epsilon_ell(theta)*N(k)),
R_entry(h) = 4D_ell*max_(x,y)
  |C_(Lambda_ell,N(k))^(K_ell,v_ell)(h)_(y,x)|
    /(epsilon_ell(theta)*N(k)),
R_coding = max_(0<|h|<=H_ell)
  2*|S_(N(k))(h)-1_D^*T_(Lambda_ell,N(k))(h)1_D|
    /(epsilon_ell(theta)*N(k)).                            (10.9)
```

The deterministic choice (10.7) guarantees `R_coding<=1`. A single instance
with `R_boundary>1` falsifies H1 for that proposed sequence, and one with
`R_reference>1` or `R_centered>1` falsifies the genuinely new H2. Still more
cheaply, since every
matrix entry is at most the operator norm, `R_entry(h)>1` for even one tested
frequency (start with `h=1`) already falsifies H2 without a singular-value
calculation or a sweep through the frequency box. The matrix need not be
allocated dense: `T` has at most `N(k)` observed entries and the legal reference
has at most `10D_ell` entries. A tested entry can be evaluated directly from
its observed count and its one reference weight. Passing finitely many
instances is only an `experiment` and proves neither H1 nor H2. The model-level rejection remains
(3.5): any proposal replacing H1 by ordinary uniform mixing has boundary
defect 12 and cannot meet `theta<1`.

## 11. Candidate matrix and first failed quantifiers

| Card | Named sequence/system | Explicit operator | Constant-explicit T107 test | First failed quantifier |
|---|---|---|---|---|
| F1 | `t_M=(4^M-1)/3`, binary `101...01` | two-state Fourier matrices (4.3) | main term needs `M>=(3200/pi)q^2`; source error constant is unprinted | natural-density integer input is not the fixed pi shift observable |
| F2 | `r_M=(10^(2M)-1)/99`, decimal `101...01` | two-state matrices (5.3), determinant `1/10` | (5.10), but `K_10` is unprinted; Haar boundary ratio is 12 | Haar-random addend input is not the pi path or boundary event |
| F3 | base-ten two-addend Holte chain | matrix (6.3), spectrum `{1,1/10}` | stationary state mass `1/2` already exceeds `1/(40q)` | iid random columns are absent for fixed pi; carry state is wrong observable |
| F4 | Rudin--Shapiro sequence (7.4) | Hadamard cocycle (7.2) | exact sufficient `P>=(960/theta)qW_ell` | signed linear phase is not unweighted exponential-in-index pi phase |

Every candidate fails before the complete T107 quantifier list. None supplies
one common increasing prefix sequence, the weak-limit clause, both boundary
and Fourier components, and every `1<=ell<m<=k`. The first failures are stated
rather than hidden behind a generic claim that local limits do not transfer.

## 12. Replay, scope firewall, and endpoint

From a directory containing only the delivered artifacts, run

```text
python3 verify_t112.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes, exact source anchors,
source/candidate caps, all required prior comparisons, the unique endpoint,
the factor-twelve boundary calculation, the F1/F2 threshold arithmetic, the
Holte matrix and eigenvalue, the Rudin--Shapiro finite recurrence and threshold,
and the definitions and constants in every H-G19 clause. Its finite checks are
`experiment`,
not evidence for universal source theorems or fixed-pi behavior.

The scope firewall is explicit:

1. none of S1--S5 states a theorem about pi;
2. no carry law is identified with `Q_pi` or a T107 boundary count;
3. no candidate proves C1, C2, canonical A1, normality, or digit occurrence;
4. related-model square-root cancellation is not fixed-pi cancellation;
5. finite replay checks cannot establish any asymptotic claim;
6. H-G19-twisted-cocycle is an unproved conjectural premise, not a result.

TERMINAL VERDICT (1/1): **HOLD AS MODEL.** F1 and F2 isolate genuine
finite-carry local-limit mechanisms, F3 gives an exact base-ten carry spectral
gap, and F4 shows that a finite cocycle can beat the literal growing-frequency
T107 Fourier threshold. None reaches the first fixed-pi observable/path
quantifier; iid or Haar spreading also has boundary defect 12 rather than at
most 1. The bounded scout therefore retains these as calibration models only.
There is no bounded successor (`SUCCESSOR_COUNT: 0`): a successor would merely
repeat the missing fixed-pi path premise unless a concrete operator satisfying
at least H1--H3 is first exhibited.
