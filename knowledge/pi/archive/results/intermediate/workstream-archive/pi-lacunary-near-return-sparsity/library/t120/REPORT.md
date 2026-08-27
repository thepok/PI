# T120: countable-state renewal scout

Audit date: 2026-08-10 UTC.

Claim labels are load-bearing. Statements attributed to the four pinned primary
papers are `literature-checked`. Sections 3--8 are `proof sketch` deductions
from those statements. The bounded replay is an `experiment`; it checks hashes,
markers, and finite arithmetic, not the universal deductions. Every premise
whose name begins `PI-` is a `conjectural transfer`, not an asserted property.

```text
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 12
CANDIDATE_COUNT: 4
CANDIDATE_CAP: 4
T7_OR_T107_CALCULATION_COUNT: 4
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

This report makes no claim about the named decimal orbit, either open
conjecture in the program context, normality, or decimal factor complexity.
The four systems below are A13/A14 related models only.

## 1. Immutable question and normalized scope

The delivered `canonical_statement.txt` is byte-exact. Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical statistic uses strict circle distance and counts ordered pairs,
including every diagonal pair. Its quantifiers are

```text
for every integer A>=1, there exists n0>=1 such that
for every integer n>=n0, there exists N>=1, allowed to depend on A,n,
with A*n*Q_pi(n,N)<=N^2.
```

The ambiguities material to this scout are fixed as follows.

1. A source is counted once although its PDF and `pdftotext -layout`
   derivative are both delivered.
2. A countable state space means a displayed countably infinite Markov
   partition or chain, not a finite automaton whose size grows with depth.
3. A return tail is the law of a displayed first-return or excursion time. A
   first-symbol tail is recorded separately and is not renamed a return tail.
4. A source theorem for an invariant measure, almost every point, or a random
   chain path is not a theorem for a prescribed point.
5. Collision counts below are ordered and diagonal-inclusive. Overlapping
   blocks are allowed and the cutoff restricts starts, not inspected symbols.
6. A fixed-depth mixing theorem is not uniform at growing depth unless its
   constants and threshold are uniform in every state and block in that range.
7. Failure of a sufficient calculation rejects only that displayed
   certificate. It is not evidence that every transfer or the underlying
   canonical statement fails.
8. The active T119 artifact was unavailable at the audit cutoff. The agenda's
   explicit collision-to-Hankel-rank exclusion is used as its comparison-level
   fingerprint; no unpublished theorem, calculation, or status is inferred.

## 2. Bounded corpus and common collision interface

The search stopped after four primary papers, one per retained candidate.

| ID | Lane | Named system | Primary source |
|---|---|---|---|
| R-LSV | fixed-point inducing | LSV map at `alpha=3/4` with countable return branches | Gouezel |
| R-FAR | fixed-point lacunary/continued fraction | Farey map induced to the Gauss map | Kessebohmer--Slassi |
| R-ISO | symbolic collision theory | Isola countdown renewal chain with zeta excursion law | Isola |
| R-JS | arithmetic/fractal Fourier | Minkowski Gauss Gibbs measure on the countable continued-fraction shift | Jordan--Sahlsten |

No finite-state carry operator, Toeplitz tower, substitution, Riesz recursion,
perturbative coupling certificate, cyclotomic modular sum, or
collision-to-Hankel-rank inversion is retained. The systems use, respectively,
a neutral-point return tower, a null-recurrent Farey renewal, an unbounded
countdown excursion state, and nonlinear countable Gauss branches.

For a finite-alphabet path `y=(y_t)`, depth `m>=1`, and `N>=1`, define

```text
L_y(w;m,N) = #{0<=i<N : (y_i,...,y_(i+m-1))=w},
C_y(m,N)   = sum_w L_y(w;m,N)^2.                           (2.1)
```

Then exactly

```text
C_y(m,N)=#{(i,j) in {0,...,N-1}^2:
             y_[i,i+m)=y_[j,j+m)}.                        (2.2)
```

Thus (2.2) is the literal T7-shaped ordered, diagonal-inclusive block
statistic, and `C_y(m,N)>=N`. It is a sibling statistic until a proved coding
identifies it with decimal cylinders. For a stationary process, put

```text
K_m(h)=Pr(y_[0,m)=y_[h,h+m)),
kappa_m=sum_w Pr(y_[0,m)=w)^2.
```

Stationarity gives the finite identity

```text
E C_y(m,N)=N+2*sum_(h=1)^(N-1) (N-h)K_m(h).               (2.3)
```

The first term is exactly the diagonal; the factor two restores both ordered
orientations. Equation (2.3) does not turn an expectation into a bound for a
named path.

## 3. R-LSV: intermittent countable return tower

### 3.1 Literature-checked system and tail

Gouezel, preprint p. 4, Corollary 1.5, and p. 31, Section 7.1 and Corollary
7.1, fixes `0<alpha<1` and the explicit LSV map

```text
T_alpha(x)=x*(1+2^alpha*x^alpha),  0<=x<=1/2,
T_alpha(x)=2*x-1,                  1/2<x<=1.               (3.1)
```

It has an invariant probability `m=h dx`. Put `x_0=1/2` and let `x_(i+1)` be
the left preimage of `x_i`. Preprint p. 31 gives the countable Markov
partition

```text
{(x_(i+1),x_i] : i>=0} union {(1/2,1]}.                   (3.2)
```

Inducing on `Y=(1/2,1]` gives countably many full return branches. If `phi_Y`
is the first return time, equations (9)--(10) and the paragraph after (10)
give the integrated tail, for every `0<alpha<1`,

```text
sum_(k=n+1)^infinity m(phi_Y>k)
 ~ C_alpha*n^(1-1/alpha),                                 (3.3)
C_alpha=(1/4)*h(1/2)*alpha^(-1/alpha)*(1/alpha-1)^(-1).
```

The source also gives correlation asymptotic `C_alpha*n^(1-1/alpha)` for
nonzero observables supported away from zero, and `O(n^(-1/alpha))` for a
zero-mean Lipschitz observable. The range is exactly `0<alpha<1`; the constants
depend on the fixed map and observables.

Because `m(phi_Y>k)` is decreasing, the monotone density consequence of (3.3)
is the `proof sketch` tail

```text
m(phi_Y>n) ~ (1/4)*h(1/2)*alpha^(-1/alpha)*n^(-1/alpha).
                                                                    (3.4)
```

### 3.2 Displayed T7 rejection

Retain the named specialization `alpha=3/4` and the binary renewal marker
`y_t=1_Y(T^t x)`. In the stationary tower, the probability `q_m` of the word
`0^m` is, up to an inessential one-index shift, the integrated return tail in
(3.3). Therefore

```text
q_m ~ C_(3/4)*m^(-1/3),
kappa_m >= q_m^2 ~ C_(3/4)^2*m^(-2/3),
m*kappa_m >= (1+o(1))*C_(3/4)^2*m^(1/3) -> infinity.       (3.5)
```

This rejects the stationary renewal-marker collision law as a source of an
`o(1/m)` T7 collision budget at this parameter. It does not prove that every
finite prefix of every LSV orbit is collision-rich.

The cheapest named-point discriminator is exact: `0` is a fixed point of
(3.1), its marker path is `000...`, and

```text
C_(000...)(m,N)=N^2                                       (3.6)
```

for every `m,N`. The invariant-measure theorem excludes no such exceptional
named path.

**PI-LSV premise (`conjectural transfer`, separately labeled).** One would
need an exact semiconjugacy from the prescribed decimal orbit to the LSV tower,
with decimal depth-`m` equality transported to equality of a declared renewal
word, plus an effective named-orbit theorem uniform for all depths in one
growing triangular prefix family. Gouezel supplies neither clause. This card is
rejected before that premise is used.

## 4. R-FAR: Farey/Gauss null renewal

### 4.1 Literature-checked system and exact tail

Kessebohmer--Slassi, preprint pp. 20--22, defines

```text
F(x)=x/(1-x), 0<=x<=1/2;
F(x)=1/x-1,   1/2<x<=1,                                  (4.1)
dmu(x)=dx/x.
```

The measure is infinite. The countable intervals and inducing set are

```text
K_n=(1/(n+1),1/n], n>=1;       K_1=(1/2,1].              (4.2)
```

The first entry time satisfies `kappa_1(x)=1+e(x)`, and the induced map
`S(x)=F^(e(x)+1)(x)` is exactly the Gauss map `1/x-floor(1/x)` on irrationals.
With `phi` the first return to `K_1`, the proof of Theorem 4.1 on p. 22 prints
the asymptotic calculation

```text
integral_((n+2)/(n+3))^1 dx/x
  =log((n+3)/(n+2)) ~ 1/n.                                (4.3)
```

The displayed source line labels its set `A_1`. It is not used here as an
exact finite-`n` set identity: at `n=0` that reading conflicts with the paper's
definition of `A_1`. Only its stated `1/n` asymptotic role is inherited.

For `x in K_1`, the source identity `phi(x)=kappa_1(Fx)` and the explicit
right branch in (4.1) give, by direct endpoint calculation,

```text
K_1 intersect {phi>0}=(1/2,1],
K_1 intersect {phi>n}=[(n+1)/(n+2),1] for n>=1,
Pr_(K_1)(phi>n)=log((n+2)/(n+1))/log 2 ~ 1/(n log 2)       (4.4)
```

for every integer `n>=0`; at `n=0` the probability is exactly one. Equation
(4.4) is a `proof sketch` deduction from the pinned source formulas, not the
integral printed in (4.3). Theorem 4.1 applies to the waiting-time process for the displayed Farey/Gauss
system; its distributional range is `n->infinity`, with part (2) quantified
over every initial density in the paper's class `D` and every fixed `x>0`.

### 4.2 Displayed T7 certificate rejection

There is no invariant probability on the full Farey system, so (4.4) cannot be
inserted into a stationary block collision law. Even granting the unsupported
and favorable substitution

```text
kappa_n := Pr_(K_1)(phi>n),
```

one obtains

```text
n*kappa_n -> 1/log 2 = 1.442695... > 1.                  (4.5)
```

Thus this literal tail-to-collision certificate misses even the normalized
`A=1` T7 target. Equation (4.5) rejects only that substitution. Return events
are not block-equality events, and a sufficient upper bound failing does not
prove the true collision count is large.

Again the named indifferent fixed point supplies an exact discriminator: the
binary `K_1` marker along `0` is constant zero, hence its ordered collision
count is `N^2` for every depth and cutoff.

**PI-FAR premise (`conjectural transfer`, separately labeled).** A usable
transfer would require a named exact coding of the prescribed decimal orbit by
Farey excursions, an invariant probability or finite-prefix normalization
compatible with (2.2), and a uniform growing-depth renewal theorem. The source
has an infinite invariant measure and distributional initial laws, not these
three clauses. The card is rejected before this premise is used.

## 5. R-ISO: explicit countdown renewal chain

### 5.1 Literature-checked chain and theorem

Isola, preprint pp. 14--15, gives the countable chain on
`S={1,2,...}` with

```text
P(1,j)=p_j,                  j>=1,
P(i,i-1)=1,                 i>=2.                          (5.1)
```

At state 1 the chain chooses an excursion height, then counts down
deterministically. The source states

```text
f_11^n=p_n,
d_n=sum_(j>n)p_j,
pi_n=pi_1*d_(n-1),
pi_1=(sum_(n>=1)n*p_n)^(-1).                              (5.2)
```

If `p_n ~ n^(-(d+2))L(n)`, the chain has ergodic degree `d`. Theorem 1,
preprint pp. 6--7, gives for `d>0`

```text
||nu P^n-pi||_1=O_epsilon(n^(-d)),                         (5.3)
```

when the initial signed distribution has P-order at least `d`. Here the source
defines `O_epsilon(n^(-d))` as `o(n^(-(d-epsilon)))` for every `epsilon>0`;
the decaying range is `0<epsilon<d`. Corollary 1 gives the same rate for two
fixed bounded state observables. Theorem 2(III), pp. 16--17, gives the fixed
observable leading asymptotic

```text
(nu P^n-pi).u ~ ((pi.u)*(nu.1)/(d*(d+1)*m_1))*n^(-d)L(n)  (5.4)
```

under its additional `u_i=o(1)`, `nu_i=o(pi_i)` hypotheses. Equation (3.4),
p. 18, is the renewal generating function

```text
P_11(z)=1/(1-sum_(n>=1)p_n*z^n).                           (5.5)
```

The remark on p. 13 explicitly says convergence is necessarily not uniform in
the departing state index.

### 5.2 Exact zeta specialization and return range

Choose the named one-parameter family

```text
p_n=1/(zeta(d+2)*n^(d+2)),       d>0.                     (5.6)
```

Direct substitution in (5.2), labeled `proof sketch`, gives

```text
Pr_1(tau=n)=1/(zeta(d+2)*n^(d+2)),
Pr_1(tau>n)=zeta(d+2,n+1)/zeta(d+2),
pi_k=zeta(d+2,k)/zeta(d+1).                               (5.7)
```

For every `n>=1`, the integral test gives the explicit range

```text
1/((d+1)zeta(d+2)(n+1)^(d+1))
 <= Pr_1(tau>n)
 <= 1/((d+1)zeta(d+2)n^(d+1)).                            (5.8)
```

Thus the excursion tail is uniform in integer `n>=1`, while the convergence
theorems (5.3)--(5.4) are only fixed-state/fixed-observable statements and
provide no effective threshold uniform at growing block depth.

### 5.3 Displayed ordered collision calculation

Observe only the renewal marker `y_t=1_{X_t=1}`. The word `0^m` occurs exactly
when `X_0>=m+1`. Its stationary probability is

```text
q_m=sum_(k=m+1)^infinity pi_k
   =[zeta(d+1,m+1)-m*zeta(d+2,m+1)]/zeta(d+1)
   ~ m^(-d)/(d*(d+1)*zeta(d+1)).                           (5.9)
```

Since this one word contributes its squared mass,

```text
kappa_m >= q_m^2.                                         (5.10)
```

At the explicit parameter `d=1/4`, (5.9)--(5.10) give

```text
p_n=1/(zeta(9/4)*n^(9/4)),
kappa_m >= (1+o(1))*256/(25*zeta(5/4)^2)*m^(-1/2),
m*kappa_m -> infinity.                                    (5.11)
```

This quantitatively rejects equilibrium renewal-marker collisions as an
`o(1/m)` T7 input at `d=1/4`. It does not reject exceptional finite prefixes.
The exact finite expectation remains (2.3).

The named admissible path `111...` is an even cheaper discriminator because
`p_1>0`. Every block on it agrees, so `C_y(m,N)=N^2`. The path has stationary
measure zero and does not contradict Isola's theorem.

**PI-ISO premise (`conjectural transfer`, separately labeled).** One would
need an exact finite observation of a named Isola path equal to the prescribed
decimal symbolic orbit, together with state- and cylinder-uniform bounds that
make (5.3) summable over all endpoint states and all depths in one triangle.
The explicit nonuniformity on p. 13 rules out reading such a conclusion from
the source. The card is rejected before this premise is used.

## 6. R-JS: Gauss Gibbs Fourier decay

### 6.1 Literature-checked countable coding and tail

Jordan--Sahlsten studies the Gauss map

```text
G(x)=1/x mod 1
```

on irrationals. Preprint pp. 6--8 identifies it with the full countable shift
on continued-fraction digits `a_j in {1,2,...}`; the inverse branch is
`G_a(x)=1/(x+a)`. The retained named measure is the Minkowski question-mark
Gibbs measure, a Bernoulli measure with

```text
Pr(a_1=a)=2^(-a),
Pr(a_1>=n)=2^(-n+1).                                      (6.1)
```

This is an exact first-branch tail, not a first-return tail. Its failure to
instantiate the requested renewal fingerprint is recorded rather than hidden.

Theorem 1.3(1), preprint p. 4, states that if a Gauss Gibbs measure has
Hausdorff dimension `s>1/2` and, for some arbitrary fixed `delta_tail>0`,

```text
mu(a_1>=n)=O(n^(-delta_tail)),                             (6.2)
```

then for some `eta>0`

```text
|mu_hat(xi)|=O(|xi|^(-eta)).                              (6.3)
```

Proposition 4.4, pp. 13--14, gives the exact tail/pressure range: every
`0<t<delta_tail/2` yields the displayed weighted summability (4.1), while
pressure finiteness at a positive `t` gives an `O(n^(-2t))` digit tail.
Corollary 1.6 concludes equidistribution of `(s_k x)` for `mu`-almost every
`x`, not for a named point.

### 6.2 Displayed T107 certificate rejection

For `q=10^ell` and `0<theta<1`, the literal sufficient individual-sum
threshold imported from T64/T107 is

```text
epsilon_ell(theta)=sqrt(theta/(160*q*W_ell)),
W_ell=[2+log(800*q^2+1)]^2
      +(1/2)*[2+log(40*q^2+1)]^2,                         (6.4)
```

uniformly for every integer `0<|h|<=H_ell=8000*q^3`. Thus
`epsilon_ell` has order `q^(-1/2)/log q`.

The proof of Theorem 1.3 displays on preprint p. 18

```text
eta_s=(2s^2-s)/((4-s)(1+2s)),
|mu_hat(xi)| << |xi|^(-eta_s+38*epsilon)
                + |xi|^(-delta_LD/(12*lambda)).           (6.5)
```

For `1/2<s<=1`, differentiation gives

```text
eta_s<=eta_1=1/9.                                         (6.6)
```

Even at the favorable top frequency `H_ell`, a power `kappa` can beat (6.4)
only if

```text
H_ell^(-kappa)=O(q^(-3*kappa))
  =o(q^(-1/2)/log q), hence 3*kappa>1/2.                  (6.7)
```

The displayed proof rate has `kappa<1/9<1/6`, so (6.5) does not certify
(6.4) even at the top of the box. More basically, the box contains `h=1`:
decay as `|xi|->infinity` gives no quantity tending to zero at that fixed
frequency as `ell` grows. Finally, T107's boundary component is a separate
maximum term; ambient Fourier decay supplies no decimal-grid boundary
depletion. These are quantitative failures of this theorem as a T107
certificate, not lower bounds on any actual exponential sum.

**PI-JS premise (`conjectural transfer`, separately labeled).** A literal
transfer would need effective convergence of the prescribed empirical
measures to this Gibbs measure uniformly over the growing box in (6.4), plus
the independent T107 boundary budget on one common triangular prefix family.
That premise already contains the missing named-point and boundary work, so it
is rejected as circular rather than selected as a successor.

## 7. Cross-candidate return and quantifier map

| Candidate | Countable state | Source tail and range | What tail controls | First fatal transfer point |
|---|---|---|---|---|
| R-LSV | intervals `(x_(i+1),x_i]`, `i>=0` | return tail `~c*n^(-1/alpha)`, every `0<alpha<1`; integrated tail (3.3) | invariant-probability excursions and correlations | named point and growing-depth collision uniformity |
| R-FAR | intervals `K_n`, `n>=1` | exact conditional return tail (4.4), every `n>=0`, asymptotic `1/(n log 2)` | null-recurrent waiting times under initial densities | no full invariant probability; named point; wrong event |
| R-ISO | countdown states `{1,2,...}` | exact zeta tail (5.7)--(5.8), `d>0`, every `n>=1` | regeneration and fixed-state convergence | source explicitly lacks state-uniformity; no named path theorem |
| R-JS | full shift on continued-fraction digits | digit tail (6.1), every `n>=1`; not a return tail | ambient Gibbs large deviations and Fourier decay | wrong tail type, almost-everywhere point, low frequencies, boundary |

Only R-LSV, R-FAR, and R-ISO pass the literal return-time fingerprint. R-LSV
and R-ISO are useful models, but their displayed specializations fail the
equilibrium `o(1/m)` collision screen. R-FAR fails even an optimistic tail
substitution and lacks a probability normalization. R-JS is retained as the
required fractal-Fourier lane rejection: its countable branch tail does not
become renewal data, and its theorem misses the T107 box quantitatively.

## 8. Cheap rejection ledger

| Candidate | Cheapest reproducible test | Result and scope |
|---|---|---|
| R-LSV | evaluate the marker at fixed point `0` | `C(m,N)=N^2`; rejects a pointwise theorem from tower admissibility. Equation (3.5) separately rejects the `alpha=3/4` stationary collision certificate |
| R-FAR | compute `n*log((n+2)/(n+1))/log 2` | tends to `1/log 2>1`; rejects the optimistic tail-as-collision certificate. Fixed point `0` also has `C=N^2` |
| R-ISO | set `d=1/4` in (5.9) | `m*kappa_m` grows like a positive constant times `sqrt(m)`; named path `111...` has `C=N^2` |
| R-JS | test the bottom and top of the T107 frequency box | `h=1` is outside asymptotic decay; at `H=8000q^3`, the displayed exponent is below `1/6`; rejects this Fourier certificate only |

Passing finitely many replay values would be only an `experiment`. None of
these tests is stated as a necessary condition for every conceivable transfer.

## 9. Required fingerprint comparison

Verification levels are part of each comparison. Prior reports are comparison
memory only; none of their `proof sketch` deductions is used as a discharged
premise.

| Comparator | R-LSV | R-FAR | R-ISO | R-JS |
|---|---|---|---|---|
| T39, sources `literature-checked`, report SHA `ff5ae4e...` | returns to one fixed inducing set, not a moving-root tangent; still lacks a named original orbit | fixed `K_1` avoids root drift, but infinite normalization blocks pullback | fixed regeneration state 1 avoids moving roots; no theorem for one named path | one fixed Gibbs measure, nearest to T39's conditional quasi-Bernoulli measure, but almost-everywhere points remain unnamed |
| T90, sources `literature-checked`, transfers `proof sketch`, SHA `730c5cda...` | invariant-measure intermittent statistics, not an explicit point with discrepancy | continued-fraction waiting laws, not base-ten discrepancy of an explicit point | random renewal paths, not a constructed expanding-map point | Corollary 1.6 is almost-everywhere equidistribution, unlike T90's explicit points |
| T103, sources `literature-checked`, deductions `proof sketch`, SHA `ed690a31...` | neutral excursions with shrinking tail, no periodic-hole tower | null returns, no Toeplitz skeleton or hole density | random excursion heights, no periodic skeleton | nonlinear Gauss branches, no tower periodicity or exact word repetition |
| rejected T109, sources `literature-checked`, transports `proof sketch`, report SHA `6b4f2746...`, skeptic SHA `987966c0...` | no perturbative coupling is used; the semiconjugacy premise is exposed and rejected | no shadowing or Wasserstein certificate | no Markov-kernel perturbation; this is the unperturbed countable chain | empirical-to-measure approximation would repeat T109's sufficient-certificate issue, so it is explicitly rejected as circular |
| T112, sources `literature-checked`, transfers `proof sketch`, SHA `72884fc7...` | countably many return branches, not finite carry states | countable Gauss digits and null recurrence, not random digit carries | genuinely unbounded countdown state, not a finite transducer | countable Möbius branches and continuants, not finite carry matrices |
| T115, sources `literature-checked`, deductions `proof sketch`, SHA `29cd0707...` | no substitution or exact Fourier coefficient recursion | no Riesz product or radix-aligned persistent ray | renewal generating function (5.5), not a substitution spectral recursion | nonlinear branch averaging gives decay, not a scalar Riesz recursion |
| T117, sources `literature-checked`, deductions `proof sketch`, SHA `ee697420...` | real interval return tails, no finite-field subset products | continued-fraction renewal, no finite period or character sum | countable Markov regeneration, no modular cancellation | real Fourier stationary phase over cylinders, no Weil bound or modular period |
| active T118, sources `literature-checked`, deductions `proof sketch`, vendored SHA `f7f2491e...`; rerun pending | no cyclotomic modulus, numerator, order, or phase transfer | no private prime power or modular orbit | no modular arithmetic | ambient real measure decay, semantically opposite to T118's fixed numerator modular sum |
| active T119, artifact unavailable; agenda-level collision-to-Hankel-rank fingerprint only | no moments, Hankel matrix, rank bound, or inversion | no moments, Hankel matrix, rank bound, or inversion | direct renewal probabilities and block atoms, not recovery from low Hankel rank | direct Fourier decay over countable cylinders, not collision moments or rank inversion |

T118's normalized fingerprint was read from the vendored report: private
`p`-primary components of `10^r-1`, exact order `r`, nearest numerator to the
named constant, logarithmic modular orbit, and attempted T64/T107 phase
transfer. Its prior review required a rerun for an unrelated stale T116
comparison; T120 uses it only as comparison memory.

For T119, the orchestration snapshot at the audit cutoff contained only an
active generation-1 lease and no report, source pins, artifact hash, or
verification status. Workspace, workflow-record, and proof-ledger artifact
searches found no readable T119 content. The four cells therefore compare only
with the agenda-specified collision-to-Hankel-rank exclusion. They are not
novelty claims or claims about T119's unpublished result. A later review must
replace this agenda-level comparison if a T119 artifact becomes readable
before adjudication.

The exclusions are semantic rather than vocabulary-based. Isola's generating
function is an infinite renewal resolvent, not T115's substitution recursion;
the Farey intervals are inducing states, not T103's Toeplitz levels; and
Jordan--Sahlsten's countable Möbius branches are neither T112's finite carry
operator nor T117/T118 modular arithmetic.

## 10. Negative map and endpoint

The bounded search isolates three separate obstructions.

1. Named-point availability kills all three actual renewal cards. Each source
   controls a measure or random path, while each system also contains an
   explicit exceptional constant-marker path with collision count `N^2`.
2. Tail size itself kills natural marker certificates for LSV at
   `alpha=3/4`, Farey at exponent one, and Isola at `d=1/4`. These are honest
   model rejections, not universal lower bounds for all finite prefixes.
3. Growing-depth uniformity remains absent even when a tail exponent is
   favorable. Isola explicitly rules out state-uniform convergence; Gouezel's
   constants are for fixed observables; Jordan--Sahlsten has a digit tail, not
   a renewal tail, and misses the literal T107 frequency box and boundary term.

The useful surviving information is model calibration: countable-state
regeneration can be quantitatively sharp, but return tails alone do not produce
ordered collision upper bounds. No bounded successor is selected because the
only possible next premise would be an effective named-orbit, growing-depth
genericity statement, which merely renames the missing input.

SCOPED VERDICT (1/1): **hold as model**.

`SUCCESSOR_COUNT: 0`.

## 11. Replay boundary

From a directory containing only the delivered artifacts, run

```text
python3 verify_t120.py
sha256sum -c SHA256SUMS
```

The verifier checks all source and canonical hashes, source anchors, caps,
candidate calculations, required comparison cells, premise labels, endpoint
counts, and package integrity. Its arithmetic checks are `experiment` only.
No Lean theorem is claimed or delivered.
