# T206 bounded clean-context cross-domain mechanism scout

Search date: 2026-08-19 UTC. Claim status: `literature-checked` for the
source statements and locators below; the displayed deductions are a `proof
sketch` with deterministic replay. Related-model theorems and all finite
calculations are non-evidentiary for pi. Nothing here proves a fixed-pi claim,
canonical C1, C2, G11, or G19.

## 1. Scope, statement, and provenance firewall

The vendored canonical statement has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
Its exact reading is: for every integer `A>=1`, every sufficiently large
decimal depth `n` admits a selectable `N=N(A,n)` such that
`A*n*Q_pi(n,N)<=N^2`; `Q_pi` uses strict circle distance, ordered pairs, and
includes all `N` diagonal pairs. No sibling reading is substituted.

`SEARCH_RECEIPT.json` records three fresh arXiv API queries and vendors their
complete Atom responses, not summaries reconstructed by this report. The
selected sources are from 2024-2026. `SOURCE_LEDGER.csv` contains exactly three
previously unaudited immutable source/theorem tuples, one in each required
domain, and exactly three normalized fingerprints. Exact arXiv identifiers and
titles were absent from the supplied accepted-library inventory. The separate
T87 threshold source below was already audited and is used only as a comparator;
it is not claimed as a fourth fresh tuple.

This package is independent of active T204. No T204 artifact is cited, compared,
required, anticipated, or used. The universal-charging and generalized-Stoneham
routes are outside scope. The only inherited boundary used is the explicitly
required T87 threshold, replayed below from a staged primary source rather than
accepted as a discharged claim from an unstaged note.

## 2. T87 source-checked comparator

The comparator is Bugeaud--Kim, arXiv:2510.02059v2, staged as
`t87-threshold-bugeaud-kim-2510.02059v2.pdf`, SHA-256
`fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330`.
Theorem 1.4, PDF p.3 / text lines 121-150, states

```
liminf p(n,xi,b)/n >= 1 + Delta(mu),
Delta(M)=(-M^3+2M^2+M-1)/(M^4-2M^3+3M^2-3M+1).
```

The source says strict nontriviality is exactly
`2 <= M < mu_1`, where `mu_1` is the root greater than 2 of
`M^3-2M^2-M+1=0`. Replay gives
`mu_1=2.246979603717467...`, `Delta(2)=1/7`, and
`Delta(mu_1)=0`; equality does not give strict gain. Lemma 4.1 and its
discussion, PDF pp.11-12 / text lines 587-611, exhibit the repetition
denominators `b^u(b^v-1)`. T87's replacement of ordinary `mu` by a restricted
exponent `nu_10` is therefore only a proof-sketch localization of that source,
not the wording of Theorem 1.4. The required T87 comparison is consequently:
a pi-specific bound `nu_10(pi)<=M<mu_1` would clear the recorded strict
threshold; no such bound is supplied here.

## 3. Card I: ordinary exponent equality versus the restricted threshold

**Tuple and fingerprint.** Bugeaud--Kaneko--Kim,
arXiv:2510.17177v3, Theorem 1.3, PDF p.3 / text lines 122-143.
Fingerprint: `ordinary-exponent-equality-versus-restricted-threshold`.
For an irrational `xi` and integer base `b>=2`, the concrete changed premise
is the exact ordinary equality `mu(xi)=2`; the conclusion is
`limsup_m p(m,xi,b)/m >= 4/3`. The paper explicitly says its method gives no
liminf estimate. This is a changed premise beyond T87's restricted upper-bound
premise, not a new theorem about `nu_10`.

**T87 exponent check.** Restricted denominators are a subset of all
denominators, hence conditionally `mu(pi)=2` would imply
`nu_10(pi)<=2<2.246979603717467...` and would clear the T87 threshold. The
source assumes `mu(xi)=2`; it does not establish `mu(pi)=2`. Its sourced
conclusion is also limsup complexity, not T87's liminf strict gain.

**Complete hypothesis card.** Met: integer base 10; irrational input; exact
source theorem and version. Unmet for pi: `mu(pi)=2`. Unmet for canonical C1:
an eventual pair-count upper bound; a metric-near-return comparison; and all
large depths rather than a subsequence.

**Candidate-specific ordered observable and logarithmic screen.** For the
base-10 word of `x`, put

```
C_I(m,L;x) = #{(i,j) in {0,...,L-1}^2 : x[i,i+m)=x[j,j+m)}.
```

This is ordered and its diagonal is exactly `L`. At genuine logarithmic
decimal depth `m=floor(log_10 L)`, Cauchy gives
`C_I(m,L;x) >= L^2/p(m,x,10)` (lower-bound direction) and the diagonal gives
`C_I>=L`. Theorem 1.3 gives only a subsequential lower bound on `p`, which
cannot reverse either inequality into the upper bound needed by C1. This is a
source-specific falsification screen, not a computation of `Q_pi`.

**Noncircular transfer and kill.** Transfer toward canonical C1 would require
both an independent proof of `mu(pi)=2` and a deterministic lemma converting
the theorem's subsequential complexity lower bound into eventual upper bounds
for the displayed ordered collision count, followed by a proved comparison to
metric `Q_pi`. The smallest killing lemma is the direction test: exhibit two
words with the same lower complexity bound but incompatible collision upper
bounds, or prove that no such conversion follows from `limsup p(m)/m`; either
failure kills this card before any pi calculation. **CLOSE.**

## 4. Card II: pointwise rough-rotation anti-clustering

**Tuple and fingerprint.** Hauke, arXiv:2506.01736v2, Definition 1 and
Theorem 1, PDF pp.2-3 / text lines 121-130 and 152-190, together with the
correlation definition on PDF p.1 / lines 38-47. The source's `k=2` proof
setup explicitly writes the circle-norm pair count across PDF pp.6-7 / lines 397-420.
Fingerprint:
`badly-approximable-rough-rotation-Poisson-correlation`.

Let `f(x)=x^r(x)`, where `r(x)` decreases to zero and for every `A>0`,
`r(x) >>_A (log log x)^A/log x`. Let `a_j^(f)` enumerate integers `a` with
smallest prime factor `P^-(a)>f(a)`. Theorem 1 states that for every badly
approximable `alpha`, `(a_j^(f) alpha mod 1)` has Poissonian correlations of all
orders. The source names the non-generic point
`Phi=(1+sqrt(5))/2` and the concrete choice
`f(x)=exp(sqrt(log x))`. Badly approximable points form a Lebesgue-null set;
this is pointwise arithmetic input, not an ambient almost-everywhere theorem.

**Complete hypothesis card.** Met in the model: the displayed `f` has
`r(x)=1/sqrt(log x)`, which decreases to zero and dominates every
`(log log x)^A/log x`; `Phi` is badly approximable; `a_j` is exactly the source's
rough-number enumeration. Unmet for pi: the sequence is not `(10^j)`; the
point is `Phi`, not pi; no source theorem transports this pair statistic between
those orbits.

**Candidate-specific ordered observable and logarithmic screen.** Put
`d_N=floor(log_10 N)`, `r_N=10^(-d_N)`, and

```
C_II(d_N,N) = #{(i,j) in {1,...,N}^2 :
                  ||a_i^(f)*Phi-a_j^(f)*Phi|| < r_N}.
```

The observable is ordered and diagonal-inclusive, with exact diagonal `N`.
Since `1/N <= r_N < 10/N`, the `k=2` theorem applied to rectangles
`(-1,1)` and `(-10,10)`, followed by monotonicity, gives the quantitative
logarithmic-depth anti-clustering screen

```
3 <= liminf_N C_II(d_N,N)/N
  <= limsup_N C_II(d_N,N)/N <= 21.
```

The off-diagonal limits at radii `1/N` and `10/N` are respectively `2` and
`20`; the extra `1` is exactly the diagonal. Strict and non-strict cutoffs
coincide here: equality would make the irrational `Phi` rational because
`a_i-a_j` is a nonzero integer and both cutoffs are rational. This is a
pair-count consequence, not return-rate convergence. In this related model the upper direction is
`C_II <= (21+o(1))N`; hence for fixed `A`, the canonical-shaped inequality
`A*d_N*C_II<=N^2` holds for all sufficiently large `N`. This remains
non-evidentiary for pi because both the orbit and point changed.

**Noncircular transfer and kill.** A sufficient structural transfer toward
canonical C1 would be: for every sufficiently large decimal depth `n`, with
`N=10^n`, there is a bijection `sigma_n` of `{1,...,N}` such that

```
max_j ||10^(j-1)*pi - a_(sigma_n(j))^(f)*Phi|| = o(1/N).
```

Triangle inequalities then sandwich pi's pair counts between the model counts
at radii `(1+o(1))/N`, and fixed-radius Poisson limits give the required linear
bound. This matching premise is pi-specific but not a restatement of a pair
count. The smallest killing lemma is a positive bottleneck lower bound
`liminf_n N*W_infinity(mu_pi,N,mu_model,N)>0` for the two empirical point sets;
it directly contradicts the displayed `o(1/N)` premise. No source supplies or
suggests the matching. **HOLD AS MODEL.**

## 5. Card III: exact logarithmic finite-field orbit energy

**Tuple and fingerprint.** Cheng--Gao, arXiv:2409.13515v2, equations
(2.1)-(2.2), Theorem 2.3, and Corollary 2.9, PDF pp.3-4 and 8-9 / text
lines 107-176, 196-210, and 499-536. Fingerprint:
`primitive-root-logarithmic-orbit-exact-evaluation`.

For odd primes `p,ell`, integer `m>=1`, `N=ell^m`, and `p` primitive modulo
`N`, the source sets `q=p^phi(N)`, takes an order-`N` element `xi` in `F_q`,
and defines the genuinely `N`-term sum
`S_N(a)=sum_(j=0)^(N-1) chi(a*xi^j)`. Equation (2.2) says
`S_N(a,0)=((q-1)/N)S_N(a)`; it does not make Theorem 2.3 a generic
`b`-dependent statement. Theorem 2.3 evaluates `S_N(a)` from the coordinates
of `a` in the `xi` basis.

**True range and complete hypothesis card.** Exactly

```
log q = phi(N) log p = ((ell-1)/ell) N log p,
N = ell*log(q)/((ell-1)*log(p)).
```

Thus `N=Theta(log q)` only when `p,ell` are fixed. Met: odd prime `p`, odd
prime `ell`, primitive-root condition, finite-field coordinate expansion, and
`b=0`. Unmet for pi: a characteristic-`p` encoding of decimal phases; a legal
source parameter carrying the adaptive pi numerator; and any sourced
cancellation bound for the resulting coordinates. No generic square-root
cancellation or ambient Fourier decay is invoked.

**Candidate-specific ordered energy and logarithmic screen.** Define

```
E_III(N,a) = |S_N(a)|^2
           = sum_(0<=i,j<N) chi(a*(xi^i-xi^j)).
```

This is an ordered diagonal-inclusive Fourier energy. The diagonal contribution
is exactly `N`; the total only satisfies `0<=E_III<=N^2`, not `E_III>=N`,
because off-diagonal terms can cancel. For the valid source parameters
`p=5, ell=3, m=1, N=3, q=25`, the decimal depth is
`d=floor(log_10 q)=1` and the exact range relation gives
`N=3=3*log(q)/(2*log(5))`. Corollary 2.9 gives, for `a in F_5`,

```
S_3(a)=2*zeta_5^(-a)+zeta_5^(2a),
E_III(3,0)=9,
E_III(3,1)=E_III(3,4)=4-sqrt(5),
E_III(3,2)=E_III(3,3)=4+sqrt(5).
```

The numerator changes the exact energy by `2*sqrt(5)` between `a=1` and
`a=2`. This finite exact calculation checks source applicability and
numerator sensitivity only; it is not evidence for pi.

**Noncircular transfer and kill.** Transfer toward G19 would require a
pi-specific algebraic representation that maps each relevant T64 row
coefficient, with controlled normalization and error, to `S_N(a)` for legal
fixed `p,ell` and explicit coordinate vectors `a=a(n)`. That is an exact
representation premise, not an assumed cancellation estimate. Once such a map
exists, Theorem 2.3 makes the row coefficient a finite coordinate expression at
the true logarithmic range. The smallest killing check is algebraic: attempt to
construct the phase-preserving map for one symbolic row and verify that it
respects multiplication by 10 and the additive character. Failure already on
the two generators `1` and `10` kills this source application. No such map is
known or supplied. **CLOSE.**

## 6. Explicit comparison with all closed branches

| card | finite-alphabet/Cauchy floor | ambient a.e. Fourier decay | substitution ray | return rate without anti-clustering | trace clock without observable | unsupported microscopic-to-mesoscopic extension | sublogarithmic character sum |
|---|---|---|---|---|---|---|---|
| I | Cauchy is used only in its lower direction and kills the desired upper inference | no metric theorem is used | no orbit substitution is made | no return theorem is used | no trace model occurs | limsup is not extended to all depths | no character sum occurs |
| II | exact diagonal `N` is added to an off-diagonal theorem | source is pointwise at a named null-set point, not a.e. | the rough orbit is kept explicitly as a related model | avoided: `k=2` gives an actual pair count | no trace model occurs | fixed `s/N` bounds are used only through a valid monotone sandwich | no character sum occurs |
| III | diagonal `N` is a summand, not a lower bound on total energy | no ambient decay is asserted | finite-field orbit is not relabeled decimal | no return theorem occurs | an exact energy observable is displayed | no complete sum is truncated: (2.1) itself has `N` terms | avoided: `N` is exactly proportional to `log q`; failure is the missing pi encoding |

## 7. Opportunity and negative map

Card I closes because its changed premise is unknown for pi and its complexity
output has the wrong quantifier and collision direction. Card III closes because
the corrected theorem is genuinely at logarithmic range and numerator-sensitive,
but no decimal/pi representation maps into it. Card II is a semantically new,
source-pinned related model with real anti-clustering at a named non-generic
point, but its explicit transfer premise has no support. Therefore no
noncircular pi transfer survives and **no successor is recommended**. This is a
source-pinned opportunity/negative map, not progress on fixed pi.
