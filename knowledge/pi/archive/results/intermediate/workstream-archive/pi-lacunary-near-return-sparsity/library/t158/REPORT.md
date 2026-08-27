# T158: empirical transition-gap occupancy scout

Audit date: 2026-08-12 UTC.

Statements attributed to S1--S4 and their exact locators in `SOURCE_PINS.md`
are `literature-checked`. Definitions and deductions made in this report are
`proof sketch`. `verify_t158.py` and `raw_output.txt` are a finite-test
`experiment`; they check examples and artifact invariants, not universal
mathematics. The fixed-pi premise in Section 9 is a `conjecture`, separately
qualified as an unproved pi-transfer, and is not asserted.

```text
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 8
SEARCHED_DOMAIN_COUNT: 4
SEPARATOR_TEST_COUNT: 5
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

This is a finite-word and random-chain mechanism audit. It proves no property
of the decimal expansion of pi.

## 1. Immutable question, normalized scope, and ambiguities

The canonical question has no external source URL. Its provenance says this
program formulated it on 2026-07-22. The delivered byte-exact
`canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It fixes the decimal orbit of pi and asks whether, for every integer `A>=1`,
every sufficiently large `n` admits an `N=N(A,n)` with
`A*n*Q_pi(n,N)<=N^2`; pairs are ordered, the diagonal is included, and the
circle cutoff is strict. T158 neither changes nor answers those quantifiers.
Equal symbolic blocks are the weaker A10 sibling; arbitrary words, random
chains, and other fixed points are A13/A14 siblings.

The agenda's ambiguous terms are fixed as follows.

1. The empirical order-`r` graph has length-`r` words as vertices and
   length-`r+1` words as directed edges. Thus it is a state-memory-`r` graph.
2. Every finite-word statistic uses the same first `M` nonwrapping starts.
   The supplied word has length `M+m-1`, so all depths through `m` exist.
3. A cyclic test identifies the state at start `M` with the state at start
   zero. A linear test records the two endpoint states explicitly.
4. Zero-outdegree states are omitted from the positive support. A gap on that
   support is never allowed to certify a constant word: the full-alphabet
   census error and support size remain separate inputs.
5. The gap is Paulin's pseudo-spectral gap, suitable for a nonreversible
   transition matrix. Ordinary right-edge spectral gap is not substituted.
6. Conductance is also recorded as a diagnostic, but no unsourced
   conductance-to-gap theorem is used.
7. A random path sampled from the row-normalized kernel is not identified
   with the deterministic word that supplied its edge counts.
8. A source theorem about a random initial point, a random path, or an
   ensemble of integers is not promoted to a pointwise theorem.

## 2. Complete exclusion ledger through T157

`EXCLUSION_LEDGER.csv` has exactly one consecutive row for every item
T89--T157. It was constructed before source retention by refreshing T155's
ledger against the supplied snapshot. The level abbreviations are:

```text
MC  machine-checked named Lean interface only
LC  source statement literature-checked
PS  unverified proof sketch
EXP finite experiment
```

The refreshed changes are load-bearing. T153 now has a readable accepted
literature report, whose source claims are LC and deductions PS. T154 now has a
readable unverified note and is PS/EXP, not an unavailable active item. T155 is
readable LC/PS/EXP. T157 is now a readable pinned literature artifact: its
source statements are LC, its collision translations are PS, and its replay is
EXP. T156 is not in the supplied knowledge library, but its rejected report is
recoverable from the supplied proof-ledger snapshot and is vendored as
`T156_REJECTED_REPORT.md`. That report labels its
source statements LC, deductions PS, and replay EXP; the recorded skeptic
rejected the delivery because one of eight papers duplicated T135, so T158
treats T156 as rejected comparison evidence, never as an accepted premise.
The pinned T157 report is vendored as `T157_REPORT.md`.

The ledger excludes the prior representation, finite-state, carry, broad
Fourier, global-L2, specification, Euler-tour, locality, census, entropy-LP,
and marked local-dependence branches. It also retains the exact duplicate
boundaries T104/T138 and T136/T146. `PRIOR_EVIDENCE.tar.gz` vendors the exact
reports used for the named comparisons in Section 8.

## 3. Graph, normalization, gap, endpoints, and collisions

Let `D={0,...,9}`, `1<=r<m`, and let
`z=z_0...z_(M+m-2)` be a word of length `M+m-1`. For every
`1<=ell<=m`, every `w in D^ell`, and the common start window
`I_M={0,...,M-1}`, define

```text
c_ell(w)=#{i in I_M:z_i...z_(i+ell-1)=w}.                 (3.1)
```

The order-`r` weighted de Bruijn/Rauzy graph has

```text
vertices u in D^r,
edge u -> v for e=ua in D^(r+1), v=shift(u,a),
edge weight W(u,v)=c_(r+1)(ua),
outweight d+(u)=sum_v W(u,v)=c_r(u).                       (3.2)
```

Parallel labels leading to the same `(u,v)` are added, although in the full
de Bruijn graph the appended digit determines the edge. Let
`S={u:d+(u)>0}`. The census is **transition-closed** when `W(u,v)>0` and
`u in S` imply `v in S`. Only in that case row-normalize on `S` by

```text
P(u,v)=W(u,v)/d+(u),             u,v in S.                (3.3)
```

If transition closure fails, (3.3) is not a stochastic matrix on `S`; its
pseudo-gap and stationary law are undefined for this audit. This is an
explicit applicability obstruction, not a reason to silently delete a
terminal edge. A cyclic census is transition-closed. A linear census may fail
closure when its final state has zero outweight.

For a cyclic census, the state at start `M` equals the state at start zero and
incoming and outgoing weights balance. Thus

```text
pi_emp(u)=c_r(u)/M,             pi_emp P=pi_emp.            (3.4)
```

If this cyclic `P` is irreducible, its unique stationary law is therefore
`pi_hat=pi_emp`.

For a linear census, if `s_i=z_i...z_(i+r-1)`, then exactly

```text
sum_u |d-(u)-d+(u)| <=2,
(pi_emp P)(u)-pi_emp(u)
  =[1_(s_M=u)-1_(s_0=u)]/M.                               (3.5)
```

Thus, when the linear census is transition-closed, the endpoint stationarity
defect is at most `2/M` in L1. This does **not** bound the stationary law by
`eta_r`; no stationary-perturbation theorem is asserted. Gap claims below use
the unique stationary law `pi_hat` of an explicitly irreducible aperiodic `P`,
whereas the census-to-path bound in Section 7 is restricted to the cyclic
balanced case `pi_hat=pi_emp`. If closure fails, no gap is assigned.

Following S2 equations (3.2)--(3.3), let `P*` be time reversal in
`L2(pi_hat)`. Define

```text
gamma_ps(P)=max_(k>=1) gamma((P*)^k P^k)/k,                (3.6)
```

where `gamma` is the reversible spectral gap and is zero when eigenvalue one
is not simple. Reducible closed kernels have `gamma_ps=0` by convention;
non-closed censuses have no `gamma_ps`. For a
directional diagnostic define

```text
Q(A,A^c)=sum_(u in A,v notin A) pi_hat(u)P(u,v),
Phi(P)=min_(0<pi_hat(A)<=1/2) Q(A,A^c)/pi_hat(A),           (3.7)
```

and set `Phi=0` for a reducible closed kernel. `Phi` is undefined for a
non-closed census. No implication between (3.6) and (3.7) is claimed here.

The explicit full-alphabet census errors are

```text
eta_r=max_(u in D^r)|c_r(u)/M-10^(-r)|,
eta_(r+1)=max_(e in D^(r+1))|c_(r+1)(e)/M-10^(-(r+1))|.   (3.8)
```

Finally, length-`m` maximum occupancy and collision energy are

```text
Cmax_m=max_(w in D^m)c_m(w),
E_m=sum_(w in D^m)c_m(w)^2
   =#{(i,j) in I_M^2:W_i^m=W_j^m}.                        (3.9)
```

The last count is ordered and includes all `M` diagonal pairs. Since
`sum_w c_m(w)=M`, the exact deterministic implication is

```text
E_m<=M*Cmax_m.                                             (3.10)
```

Consequently `Cmax_m<=M/(A*m)` would imply
`E_m<=M^2/(A*m)`. The scout tests whether (3.6), (3.8), and endpoints force
that occupancy premise.

## 4. What the pinned theorems actually supply

### 4.1 Weighted de Bruijn process

S1 equations (2.2)--(2.5) define a weighted continuous-time Markov process on
de Bruijn word states. Theorem 3 identifies its stationary vector; Theorem 12
factorizes its characteristic polynomial; Corollary 13 gives a Bernoulli
specialization. These are genuine random-process statements. S1 also records
the Euler-tour/de Bruijn-cycle correspondence on PDF p. 2, but it does not say
that every deterministic Eulerian ordering of fixed edge multiplicities has
the law of the Markov process.

### 4.2 Random-trajectory concentration

S2 Assumption 3.1 requires a homogeneous irreducible aperiodic Markov chain.
Its equations (3.1)--(3.3) define the gaps used here. Theorem 3.11 gives, for a
stationary random trajectory and bounded `f`, the explicit bound

```text
P(|sum_(i=1)^n f(X_i)-n*pi_hat(f)|>=t)
 <=2 exp[-t^2*gamma_ps/(8*(n+1/gamma_ps)*Var(f)+20*t*C)].  (4.1)
```

This can control occupancy of a fixed state along a sampled chain. A union
bound can control finitely many states if its dimension and gap losses are
paid. A length-`m` block is instead a path event, so applying (4.1) requires a
lift to path states and a bound for that lifted gap. Most importantly, the
deterministic edge ordering is not sampled from `P`. Neither lift nor
deterministic-typicality premise follows from the empirical graph.

### 4.3 Fixed target is not fixed starting path

S3 Theorem 7 gives an explicit exponential hitting-law approximation for a
rank-`n` set in an alpha-mixing symbolic process. Example 2 permits the target
cylinder to be centered at every prescribed sequence, even a periodic one.
The distribution is nevertheless over a random starting trajectory under the
invariant measure. Thus "around any point" does not bound the orbit of that
point. This exactly blocks a fixed-point inference from measure mixing.

### 4.4 Structured sums have the wrong ensemble

S4 Theorem 1.1 bounds sums modulo `q^gamma` in the nontrivial range

```text
q^(gamma^(2/3+epsilon)) <= X <= q^(A*gamma),               (4.2)
```

and Theorem 1.3 turns them into digit statistics for the ensemble
`{2^p-1:p<=X prime}`. Equations (3.9)--(3.11) display the interval/Fourier
conversion. The theorem fixes an odd prime base `q`, not decimal base ten, and
averages over primes rather than consecutive shifts of one point. It provides
no estimate for `sum_(j<M) exp(2*pi*i*h*10^j*pi)` and no ordering certificate
for (3.1).

## 5. Decisive quantitative applicability obstruction

Fix `r>=1`. Let `B` be any cyclic decimal de Bruijn word of order `r+1`, of
period

```text
P0=10^(r+1),                                                (5.1)
```

and repeat it `J>=1` times. Use all `M=J*P0` cyclic starts. Supply `m-1`
look-ahead digits by repeating the cycle, so the nonwrapping convention (3.1)
is literally satisfied.

Every length-`r+1` word occurs once per period and every length-`r` word has
ten extensions. Hence

```text
c_(r+1)(e)=J,             c_r(u)=10J,
eta_r=eta_(r+1)=0,
pi_emp(u)=10^(-r),        P(u,shift(u,a))=1/10.            (5.2)
```

After exactly `r` independent appended digits, the shift-register state has
forgotten its initial state. If `Pi` is projection onto constants, then

```text
P^r=Pi.                                                      (5.3)
```

Therefore `(P*)^r P^r=Pi`; on the mean-zero subspace it is zero, so its
reversible gap is one. By S2's definition (3.3),

```text
gamma_ps(P)>=1/r.                                           (5.4)
```

Thus this family has a quantitative gap, zero census error, full connected
support, and zero endpoint defect.

For every `m>=r+1`, the first `r+1` digits identify the phase because each
length-`r+1` word appears once per primitive period. Exactly `P0` length-`m`
blocks occur, each `J` times. Therefore

```text
Cmax_m=J=M/10^(r+1),
E_m=P0*J^2=M^2/10^(r+1).                                  (5.5)
```

Whenever `A*m>10^(r+1)`, both desired inequalities fail:

```text
Cmax_m>M/(A*m),             E_m>M^2/(A*m).                 (5.6)
```

Equations (5.2)--(5.6) are the applicability obstruction. The empirical
kernel describes what would happen if each outgoing edge were randomly
resampled. The observed word repeatedly follows one particular Eulerian edge
ordering. Gap, exact short census, connectivity, and endpoints do not remember
that ordering. The obstruction is overlap dependence, not an inadequate gap
or census estimate.

## 6. Five exact separator tests

### SPT1 constant word: rejected by support/census firewall

For `z=0^(M+m-1)`, `Cmax_m=M` and `E_m=M^2`. On positive support the kernel is
the one-state loop, so any convention declaring its gap maximal would be
vacuous. On the full `D^r` space it is reducible and has gap zero. Moreover
`eta_r>=1-10^(-r)`. The certificate must retain full-alphabet census error and
cannot certify this word by deleting zero-mass states.

### SPT2 periodic word: ordinary gap is insufficient

For the alternating binary word `0101...` with even `M` and `r=1`, the
positive-support transition matrix swaps `0` and `1`. It has eigenvalues
`1,-1`; in S2's convention ordinary reversible gap is two but absolute gap and
pseudo-gap are zero. For every `m>=1`, there are two phase blocks, each `M/2`
times, so `Cmax_m=M/2` and `E_m=M^2/2`. This is why (3.6) and aperiodicity,
not a one-sided eigenvalue gap, are mandatory.

### SPT3 repeated de Bruijn: decisive failure

The family in Section 5 passes full support, zero census error, zero endpoint
defect, and `gamma_ps>=1/r`, yet fails occupancy whenever
`A*m>10^(r+1)`. This rejects the proposed deterministic implication itself.

### SPT4 shared prefix: explicit census-rate obstruction

Let `R>=m`, begin a word with at least `R+m-1` zeros, and fill the remaining
starts with repetitions of a fixed order-`r+1` de Bruijn cycle, charging the
at most two splice transitions. Then

```text
Cmax_m>=R,
eta_r,eta_(r+1) <= (R+m+r)/M.                              (6.1)
```

Choose `R=ceil(M/sqrt(m))` and `M` so large that `R+m<=M/2`. The census error
tends to zero while `Cmax_m>=M/sqrt(m)>M/(A*m)` for all sufficiently large
`m`. The numerator in (6.1) safely charges every short start whose block meets
the replaced prefix and the splice. For `r=1`, the untouched suffix is a
contiguous segment of a period-100 order-two de Bruijn cycle. Each directed
edge therefore remains at least `floor((M-R-m)/100)` times. If
`R+m<=M/2` and `M>=600`, this is at least `M/300-1`; hence every nontrivial
cut retains a positive constant fraction of its uniform cross-edge weight.
The state masses differ from uniform by at most (6.1), so for the displayed
schedule the conductance is bounded below by a positive constant for all
sufficiently large `m`. Thus a qualitative conductance lower bound and merely
`eta=o(1)`
still do not suffice. Any usable census term must be at most order `1/(A*m)`,
the occupancy scale, and must still address edge ordering. This calculation is
self-contained; the unverified T147 note is comparison context only.

### SPT5 disconnected multi-core: correctly rejected by gap/endpoints

Take two long constant cores, one over digit `0` and one over digit `5`. If
the two linear splice transitions are omitted, the empirical support has two
closed classes, so `Phi=gamma_ps=0`. If all starts and cyclic endpoints are
retained, exactly two cross-core transitions remain among order-`M` total
weight, so `Phi=O(1/M)` rather than a positive uniform constant. Both cores
create length-`m` occupancies of order `M`. This test confirms that gap catches
disconnection only when endpoint transitions are not silently discarded; it
does not repair SPT3's connected obstruction.

```text
SEPARATOR_CONSTANT: reject-support-census
SEPARATOR_PERIODIC: reject-pseudo-gap
SEPARATOR_REPEATED_DEBRUIJN: reject-implication
SEPARATOR_SHARED_PREFIX: reject-census-rate-and-order
SEPARATOR_DISCONNECTED_MULTICORE: reject-gap-endpoints
```

## 7. The only valid occupancy bridge and its missing input

Assume in this section that the census is cyclic and balanced, its positive
support is closed, and `P` is irreducible. Then (3.4) gives
`pi_hat=pi_emp`, so the empirical kernel defines the Markov reference
probability for an `m`-word `w=w_0...w_(m-1)`:

```text
mu_P(w)=pi_hat(w_0...w_(r-1))
        * product_(t=r)^(m-1)
            P(w_(t-r)...w_(t-1),w_(t-r+1)...w_t).         (7.1)
```

Define the deterministic ordering discrepancy

```text
Delta_order(m)=max_(w in D^m)|c_m(w)/M-mu_P(w)|.           (7.2)
```

Then, tautologically but quantitatively,

```text
Cmax_m/M <= max_w mu_P(w)+Delta_order(m),
E_m/M^2 <= max_w mu_P(w)+Delta_order(m).                  (7.3)
```

If `eta_r<10^(-r)`, cyclic balance and (3.8) give the explicit path bound

```text
max_w mu_P(w)
 <=(10^(-r)+eta_r)
   *[(10^(-(r+1))+eta_(r+1))/(10^(-r)-eta_r)]^(m-r).      (7.4)
```

For a linear census, (7.4) is not asserted: (3.5) alone does not compare
`pi_hat` with `pi_emp`, and transition closure can fail. A valid linear
analogue would require a separately proved stationary-perturbation term or an
explicitly chosen nonstationary reference law; neither follows from the gap.

Equations (7.3)--(7.4), under the cyclic hypotheses just stated, would prove
the desired occupancy if their right side were at most `1/(A*m)`. But the repeated-de-Bruijn word has the ideal reference
`mu_P(w)=10^(-m)` while its actual occupied paths have mass `10^(-(r+1))`;
therefore `Delta_order(m)` is of that latter size. Neither S1 nor S2 bounds
(7.2) for a deterministic Euler ordering. Adding (7.2) is an ordering or
path-typicality premise, not a consequence of graph expansion.

## 8. Named prior comparisons

Prior prose deductions are comparison memory, not discharged premises.

| Item | Available level and fingerprint | T158 comparison |
|---|---|---|
| T121 | source claims LC; collision deductions PS; replay EXP; global Parseval/Walsh L2 and finite necklace energy | T158 does not estimate global L2 from Fourier data. Its counterexample shows a short-state gap cannot generate the long-block L2 bound. |
| T128 | source claims LC; block deductions PS; replay EXP; explicit nested de Bruijn prefixes and named-point discrepancy | T128 succeeds by constructing a particular coherent ordering. T158 shows this ordering information cannot be recovered from the empirical transition kernel. |
| T131 | source claims LC; graph deductions PS; replay EXP; circulation rounding and Euler-tour ordering | Nearest graph branch. T131 already separates edge counts from Euler ordering; T158 adds the exact positive pseudo-gap calculation (5.4) and shows that even an ideally mixing associated kernel does not control the chosen tour. |
| T153 | source claims LC; locality deductions PS; replay EXP; k-Abelian census and repeated-de-Bruijn locality obstruction | T158 does not import T153's deductions. It independently rebuilds the family and strengthens the tested certificate by giving the associated kernel zero census error and `gamma_ps>=1/r`; the obstruction survives. |
| T156 | rejected report recovered from the supplied proof-ledger snapshot; report labels sources LC, deductions PS, replay EXP | T156 audits inverse stability/templates at reuse scale. Its recorded rejection concerns duplicate source counting against T135. T158 imports no T156 claim and uses graph transition ordering rather than template coverage. |
| T157 | readable pinned artifact; source claims LC, collision translations PS, replay EXP | T157 closes inverse Littlewood--Offord substitutions at the zero difference vector. T158 instead tests a Markov-kernel gap; its repeated-de-Bruijn obstruction is independent of T157's inverse-concentration deductions. |

The duplication boundary is therefore explicit: graph weights and Euler tours
are nearest T131, while the repeated-de-Bruijn adversary is nearest T153/T149.
The only new retained conclusion is a negative applicability map for the
pseudo-gap-plus-census composition; it is not presented as a new positive
mechanism or a novelty claim.

## 9. Separate fixed-pi transfer premise

**PI-GRAPH-ORDER-T158 (`conjecture`; UNPROVED PI-TRANSFER; NOT ASSERTED).** For every integer
`A>=1` and every sufficiently large decimal depth `m`, there exist `M>=1` and
`1<=r<m` such that the actual first-`M` decimal block process of pi admits a
cyclic balanced comparison census with closed support and an irreducible
aperiodic empirical kernel, with explicitly positive `gamma_ps(P)`, census
errors satisfying the right side of (7.4), and, independently,

```text
max_w mu_P(w)+Delta_order(m) <= 1/(A*m).                  (9.1)
```

Then (7.3) would give `E_m^pi<=M^2/(A*m)`, a T7-shaped symbolic input. No
inspected source proves any part of (9.1) for pi. A literal linear-prefix
version would additionally need the stationary/endpoint repair excluded in
Section 7. The gap clause alone does not imply the ordering clause, by Section
5. Metric near returns would still need
the separately machine-checked T7 comparison and its constants. T107 requires
additional triangular boundary and Fourier budgets not supplied by (9.1).
There is no fixed-pi, A1, C1, or C2 claim.

## 10. Endpoint and replay

`SCOPED_VERDICT (1/1): close`.

Close weighted empirical transition-graph expansion as a deterministic
long-block occupancy mechanism. The obstruction already has full support,
zero short-census error, zero endpoint defect, and pseudo-spectral gap at least
`1/r`; what fails is deterministic edge ordering/overlap dependence. Markov
concentration remains valid for genuinely sampled trajectories, and the source
theorems are not contradicted. This verdict says nothing about pi or the
canonical question.

`SUCCESSOR (0/1): none`.

From a directory containing only delivered artifacts, run:

```bash
python3 verify_t158.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier checks source and canonical hashes, the 69 consecutive ledger
rows T89--T157, refreshed T156/T157 levels, report markers and source locators,
the cyclic/closed-support stationary firewall, exact de Bruijn counts and
collision identities on finite decimal examples, the five separator formulas,
one verdict, zero successors, and label separation. Those checks are an
`experiment`, not proof of the literature deductions or asymptotic claims.
