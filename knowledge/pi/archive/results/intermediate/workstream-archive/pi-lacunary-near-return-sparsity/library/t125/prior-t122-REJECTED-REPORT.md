# T122: constructive overlapping-block discrepancy scout

Search date: 2026-08-10 UTC.

```text
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 12
SEARCHED_LANE_COUNT: 4
RETAINED_CANDIDATE_COUNT: 4
RETAINED_CANDIDATE_CAP: 4
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 1
```

Claim labels are load-bearing. The source statements identified in
`SOURCE_PINS.md` are `literature-checked`. The incidence-vector reductions,
collision substitutions, and applicability tests in Sections 3-9 are `proof
sketch` deductions. The bounded checks performed by `verify_t122.py` are an
`experiment`; they check transcription and finite identities only.

This report concerns computable artificial digit streams. Every constructed
stream changes the prescribed point and is an A13 sibling. It is not evidence
about the decimal expansion of pi. No fixed-pi, C1, or C2 conclusion is made.

## 1. Immutable statement, normalization, and ambiguities

The delivered byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question fixes `x=pi`, radius `10^(-n)`, ordered pairs, and the
diagonal, and asks

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N) <= N^2.
```

T122 does not alter or answer those quantifiers. Its normalized sibling target
is narrower: construct one computable infinite word `x=(x_i)_(i>=0)` and one
coherent increasing prefix family on which ordered equal-block collisions have
`o(N^2/m)` growth at `m=floor(kappa*log_10 N)`.

The following ambiguities are fixed before source use.

1. One algorithm must output one infinite word. A new finite word, seed, or
   period at each `N` is not a survivor without a proved coherent splice.
2. `kappa>0` is fixed before `N`, and `log_10` is literal base-ten logarithm.
3. A prefix cutoff restricts starts only. A length-`m` word starting at `N-1`
   reads through digit `x_(N+m-2)` of the already fixed infinite word.
4. Windows overlap without restriction. Counts are ordered and include all
   diagonal pairs.
5. Exact block equality is not identified with strict circle near return for an
   arbitrary word. The comparison with T7 is a statistic-shape comparison.
6. Ordinary normality supplies fixed-depth limits only. It is not promoted to a
   moving-depth estimate.
7. A finite randomized success event does not name a computable infinite word.
8. A theorem for signs `+v/-v` does not automatically permit one of ten
   non-antipodal digit updates.
9. A premise already asserting the needed collision decay or the literal T107
   triangular defect is circular and is rejected.

## 2. Bounded cross-domain search

The search stopped after seven primary sources in four lanes. No source or
candidate was added to fill a cap.

| lane | inspected primary sources | retained candidate |
|---|---|---|
| symbolic collision theory and low-discrepancy words | S1 Becher-Carton | C-NPN |
| constructive pseudorandomness | S2 Alvarez-Becher | screened: computable but quantitatively dominated by C-NPN |
| online vector discrepancy | S3 Kulkarni-Reis-Rothvoss; S4 Alweiss-Liu-Sawhney | C-KRR; S4 screened as a weaker finite-horizon sign theorem |
| constructive colorful balancing | S5 Ambrus-Bozzai | C-AB |
| structured exponential sums and automatic words | S6 Drmota-Mauduit-Rivat; S7 Konieczny | C-DMR; S7 screens the unsampled low-complexity route |

Exact versions, URLs, SHA-256 values, printed-page locators, and extracted-text
anchors are in `SOURCE_PINS.md`. The candidate cap is exactly four:
`C-NPN`, `C-KRR`, `C-AB`, and `C-DMR`.

## 3. Common block-incidence and endpoint definitions

Let `x=(x_i)_(i>=0)` be one infinite decimal word. A candidate may use all
decimal words

```text
W_m={0,...,9}^m, q_m=10^m,
```

or, when explicitly stated, the binary admissible subset

```text
W_m={0,1}^m subset {0,...,9}^m, q_m=2^m.
```

In either case `W_m` contains every block realized by `x`; this is automatic
for the decimal candidates and follows from binary-valuedness for C-DMR.

For `m,N>=1` and `w in W_m`, define the overlapping start count

```text
A_x(N,m,w)=#{i in {0,...,N-1}:
                 (x_i,...,x_(i+m-1))=w}.                 (3.1)
```

There are exactly `N` starts. The endpoint convention in (3.1) reads the fixed
tail through `x_(N+m-2)`; it neither drops the last `m-1` starts nor wraps them.
The incidence vector and its centered version are

```text
b_i^(m)=e_((x_i,...,x_(i+m-1))) in R^(W_m),
p_m=q_m^(-1)*1_(W_m),
g_i^(m)=b_i^(m)-p_m,
delta_x(N,m)=sum_(0<=i<N) g_i^(m).                        (3.2)
```

Thus `delta_w=A_x(N,m,w)-N/q_m`, and the Euclidean and maximum norms are

```text
||delta||_2=(sum_w delta_w^2)^(1/2),
||delta||_infinity=max_w |delta_w|.                       (3.3)
```

Each centered update has the exact norm

```text
||g_i^(m)||_2^2=1-q_m^(-1).                              (3.4)
```

For simultaneous decimal depths `1<=r<=m`, use the direct sum

```text
G_i^(<=m)=direct_sum_(r=1)^m g_i^(r),
D_m=sum_(r=1)^m 10^r=(10^(m+1)-10)/9 < (10/9)10^m,
||G_i^(<=m)||_2^2=sum_(r=1)^m(1-10^(-r))<m.              (3.5)
```

The literal ordered, diagonal-inclusive equal-block statistic is

```text
E_x(N,m)=sum_(w in W_m) A_x(N,m,w)^2.                    (3.6)
```

Expanding around the uniform vector and using `sum_w delta_w=0` gives

```text
E_x(N,m)=N^2/q_m+||delta_x(N,m)||_2^2.                   (3.7)
```

Alternatively, if `Delta=||delta||_infinity`, then

```text
E_x(N,m)<=N*max_w A_x(N,m,w)<=N^2/q_m+N*Delta.           (3.8)
```

These formulas count a pair `(i,j)` once for every ordered pair of equal
blocks, including all `N` diagonal pairs.

T7's machine-checked pi statistic is the same sum of squared decimal-cylinder
occupancies, and T7 proves

```text
piCylinderCollisionEnergy(n,N) <= Q_pi(n,N)
Q_pi(n,N) <= 3*piCylinderCollisionEnergy(n,N).           (3.9)
```

Here (3.6) is only the corresponding A13 word statistic. No use of (3.9) is
made with `x` substituted for pi.

For a fixed `kappa>0`, every candidate is tested at

```text
m_N=floor(kappa*log_10 N).                               (3.10)
```

For large `N`, `N^kappa/10 < 10^m_N <= N^kappa`. The
T7-shaped sibling threshold is

```text
m_N*E_x(N,m_N)/N^2 -> 0.                                 (3.11)
```

### T107 boundary

T107's machine-checked literal levels are `L_m={ell:1<=ell<m}`. At positive
prefix `P`, its row defect is

```text
max(rowBoundaryLoad(ell,P)/(P/(40*10^ell)),
    ||rowFourierRemainder(ell,P)||/(P^2/(10*10^ell))).   (3.12)
```

Here `rowBoundaryLoad` is T107's weighted child-plus-parent active-boundary
count. Its conditional triangular premise requires `d>0`, `B>=0`, a strictly
increasing family `N(k)>0`, weak convergence of its empirical pi-orbit measures
to a specified probability measure, and, for every `k>=k0` and
`m0<=m<=k`, a sum of (3.12) over `L_m` at most `|L_m|-(d*m-B)`. None of
S1-S7 estimates T107's pi-specific boundary load or row Fourier remainder.
Assuming this triangular inequality for the sum of (3.12) would merely assume
the T107 premise, so all four candidates below use the literal T7-shaped
statistic (3.6) instead.

## 4. C-NPN: nested perfect-necklace discrepancy

### Definitions and source guarantee

For each prescribed order `s=2^d`, candidate `C-NPN` chooses the
lexicographically first base-ten `(s,s)`-nested perfect necklace and
concatenates those finite words in increasing `d`. Let the resulting real be
`y=0.d_0d_1...`, and define the candidate word by `x_i=d_(i+1)`. This aligns
start `i` exactly with the source orbit point `{10^(i+1)y}` and discards only
the first digit when naming the infinite sibling word. Its admissible family is
`W_m={0,...,9}^m`; its counts, endpoint, incidence vectors, and norms are
exactly (3.1)-(3.5).

S1 printed p. 2 defines a `(k,s)`-perfect necklace: every length-`k` word
occurs exactly `s` times at starts distinct modulo `s`; it then defines nested
perfect necklaces recursively. S1 Theorem 1, printed pp. 2-3, says that for
every base `b`, concatenating `(s,s)`-nested perfect necklaces at
`s=2^d`, `d=0,1,...`, gives one real `x` satisfying

```text
D_N(({b^n*x})_(n>=1))=O((log N)^2/N) for every N.         (4.1)
```

The discrepancy in S1 is the supremum over all half-open intervals `[alpha,beta)`.
A length-`m` decimal word `w` is exactly one half-open base-ten cylinder.
Consequently (4.1) gives one constant `C` and `N_0` such that, simultaneously
for every `N>=N_0`, every `m>=1`, and every decimal word `w`,

```text
|A_x(N,m,w)-N/10^m| <= C(log N)^2.                       (4.2)
```

The source does not label this lexicographic selection as a computability
theorem. Its computability is an elementary `proof sketch`: the
nested-perfect property is decidable for each finite word, and S1 Theorem 1's
construction supplies existence at every prescribed stage, so every finite
search terminates and emits one coherent infinite digit stream. The discrepancy
constant in (4.1) may depend on this selected word and base; that is sufficient.

### Displayed discrepancy-to-T7 calculation

From (3.8) and (4.2),

```text
E_x(N,m) <= N^2/10^m+C*N*(log N)^2.                       (4.3)
```

Set `m=m_N` from (3.10). Using `10^m>N^kappa/10` and
`m<=kappa*log_10 N`,

```text
m*E_x(N,m)/N^2
 <= 10*kappa*log_10(N)/N^kappa
    +C*kappa*log_10(N)*(log N)^2/N
 -> 0                                                     (4.4)
```

for every fixed `kappa>0`. This is stronger than needed in prefix coherence:
the same computable word and every sufficiently large `N` work, rather than a
new word or sparse endpoint family.

### Disposition

`C-NPN` survives as a related-model mechanism. It is quantitative
low-discrepancy cylinder balancing, not ordinary normality: the uniform
`O(log^2 N)` count error in moving depth is the essential input.

## 5. C-KRR: online subgaussian sign balancing

### Definitions and source guarantee

Candidate `C-KRR` seeks to control the simultaneous decimal incidence vector
(3.5) in `R^(D_m)` with the maximum norm. S3 Theorem 1 and Corollary 3(d),
printed pp. 2-3, apply to an obliviously fixed sequence `v_1,...,v_T`,
`||v_i||_2<=1`, and choose signs online so every prefix is 10-subgaussian and

```text
max_(t<=T)||sum_(i<=t) epsilon_i*v_i||_infinity
  =O(sqrt(log T)+sqrt(log(1/delta)))                      (5.1)
```

with probability at least `1-delta`. S3 Theorem 20, printed p. 14, is an
effective but enormous finite-horizon algorithm. S3 Section 7, Lemma 21 and
Theorem 22, printed pp. 15-16, obtains one horizon-free algorithm by compactness.
S4 Theorem 1.1, printed p. 2, was also inspected; its explicit finite-horizon
self-balancing walk has `O(log(nT/delta))` maximum discrepancy but likewise
requires oblivious vectors.

If one effective digit transducer supplied signed vectors
`G_i^(<=m)/sqrt(m)` coherently across all changing horizons and depths, then with
`T=N+O(m)` and `delta=N^(-2)`, (5.1), rescaling, and the start/ending-window
endpoint adjustment of at most `m-1` windows would give

```text
Delta=||delta_x(N,m)||_infinity
  =O(sqrt(m*log N)+m).                                    (5.2)
```

The incidence and norm conventions remain (3.1)-(3.5).

### Displayed hypothetical calculation and quantitative rejection

By the weaker coordinate estimate
`||delta||_2^2<=10^m*Delta^2`, (3.7) and (5.2) would give, at (3.10),

```text
m*E_x(N,m)/N^2
 <= m/10^m+O(10^m*m*(m*log N+m^2)/N^2)
 =O(log N/N^kappa+N^(kappa-2)*(log N)^4) -> 0             (5.3)
```

for every fixed `0<kappa<2`. Thus dimension growth would not kill the
hypothetical estimate.

The source theorem nevertheless cannot be invoked. Fix a current
length-`m-1` context `s`, put `d=10^m`, and let the centered update after
choosing digit `a` be

```text
g_a=e_(sa)-d^(-1)*1.                                      (5.4)
```

For distinct digits `a,b` and any word `w` not extending `s`, which exists for
`m>=2`,

```text
(g_a+g_b)_w=-2/d != 0.                                    (5.5)
```

The ten choices are not a pair `+v,-v`. Worse, `s` was produced by earlier
digit choices, so the update family is adaptive rather than obliviously fixed.
Antipodality of full direct-sum updates would imply antipodality after
projection to their depth-`m` component, so (5.5) also rules out that escape.
S4 printed p. 1 records an `Omega(sqrt(T))` adaptive-adversary obstruction.
Finally, S3's infinite consistency step is compactness, not an effective
infinite selector. Equation (5.3) is therefore a counterfactual calculation,
not a constructed word.

## 6. C-AB: static colorful vector balancing

### Definitions and source guarantee

Candidate `C-AB` is the closest source theorem allowing ten choices rather
than signs. It uses the Euclidean norm on the simultaneous incidence space
`R^(D_m)`. S5 Theorem 1.4, printed p. 3, says that fixed finite families
`V_1,...,V_N` in the Euclidean unit ball satisfying

```text
0 in sum_(i=1)^N conv(V_i)                                (6.1)
```

admit choices `v_i in V_i` with

```text
||sum_i v_i||_2 <= sqrt(D_m).                             (6.2)
```

S5 Theorem 2.3 and Proposition 3.1, printed pp. 5-7, expose the finite
linear-program extreme-point reduction and rounding argument.

### Displayed hypothetical calculation and quantitative rejection

If the ten digit updates at each start formed fixed families satisfying (6.1),
scale (3.5) by `1/sqrt(m)`. Equation (6.2) would imply

```text
||delta_x(N,m)||_2^2 <= m*D_m < (10/9)*m*10^m.            (6.3)
```

Then (3.7), (3.10), and `D_m<(10/9)10^m` give

```text
m*E_x(N,m)/N^2
 <= m/10^m+(10/9)*m^2*10^m/N^2
 =O(log N/N^kappa+N^(kappa-2)*(log N)^2) -> 0             (6.4)
```

for every fixed `0<kappa<2`.

But the required families are not fixed: at depth `m`, the options (5.4)
depend on the context selected by previous choices. Even locally,

```text
0 notin conv{g_a:a in {0,...,9}} for m>=2,                (6.5)
```

because every convex combination has coordinate `-1/10^m` at every word not
extending the current context. Projection from the simultaneous direct sum to
its depth-`m` component proves the same local obstruction for the full update.
This does not disprove S5's weaker global condition (6.1); rather, the actual
context-dependent families are not available as a fixed list, and verifying
their global condition would already require a fractional coherent
block-balancing certificate not supplied by S5.
Separate finite solutions also need not be nested prefixes of one word. Thus
(6.4) displays adequate numerical strength but (6.1) and static-family
coherence reject the application.

## 7. C-DMR: Thue-Morse along squares

### Definitions and source guarantee

Candidate `C-DMR` is the computable binary word

```text
x_i=t(i^2) in {0,1} subset {0,...,9}.                     (7.1)
```

Here `W_m={0,1}^m`, `q_m=2^m`; decimal words using another digit have zero
occupancy. Counts and endpoints are (3.1), the incidence vector lies in
`R^(2^m)`, and (3.4) reads `||g_i^(m)||_2^2=1-2^(-m)`.

S6 Theorem 2, printed p. 3, says that for each fixed `m>=1` and each nonzero
`alpha in {0,1}^m`, there exists `eta>0` such that the corresponding
length-`m` shifted sum-of-digits exponential sum is `O(N^(1-eta))`. S6
Lemma 1, the same page, expands each block indicator into all `2^m` Fourier
characters and proves normality. For each fixed `m`, finiteness therefore gives
some constants `C_m`, `eta_m>0`, and threshold `N_0(m)` such that

```text
Delta_m(N)=max_(w in {0,1}^m)|A_x(N,m,w)-N/2^m|
 <= C_m*N^(1-eta_m) for N>=N_0(m).                        (7.2)
```

### Displayed fixed-depth calculation and moving-depth rejection

At each fixed `m`, (3.8) and (7.2) give

```text
m*E_x(N,m)/N^2
 <= m/2^m+m*C_m*N^(-eta_m).                               (7.3)
```

The first term tends to zero when `m=m_N`. For the second term, the literal
condition needed at logarithmic depth is

```text
log(m_N*C_(m_N))-eta_(m_N)*log N -> -infinity,
and N>=N_0(m_N).                                          (7.4)
```

S6 has quantifier order `for every fixed m there exist eta_m,C_m,N_0(m)` and
states no bounds on their growth. It therefore gives no implication in (7.4).
This is exactly the word-family/depth loss that ordinary normality hides.

S7 was inspected as a complementary structured-sum screen. Its Theorems A and
B, printed pp. 1899 and 1901, likewise give `N^(-c(s))` Gowers decay only for
each fixed order `s`. More decisively, S7 printed p. 1897 records linear
subword complexity for the original automatic words. If an unsampled word has
at most `K*m` occupied length-`m` blocks, Cauchy-Schwarz gives

```text
E_x(N,m)>=N^2/(K*m),                                      (7.5)
```

which is not `o(N^2/m)`. C-DMR avoids (7.5) by square sampling but remains
blocked by (7.4).

## 8. Mandatory prior-fingerprint comparison

Verification levels are part of the comparison. No prose note is used as a
discharged premise.

| item | inspected pin and level | normalized fingerprint | T122 comparison |
|---|---|---|---|
| T2 | `NormalOrbitNearReturns.lean`, SHA `1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174`, machine-checked | fixed-depth base-ten normality implies the near-return quantifier pattern for generic normal streams and Champernowne | C-NPN supplies the missing moving-depth `O(log^2 N)` cylinder error; C-DMR illustrates why T2-style ordinary normality alone is insufficient; C-KRR/C-AB are vector-selection tests rather than normality arguments |
| T37/T49 | Lean SHAs `aa0979b629131c6e30c2d8a8dc8c70499ff03d98cd35b2f49841f7669585116c` and `61082f21330c21c22874e31b77af00f365c2995cdcd3909e5399ce89ed28cd93`, machine-checked | one hand-staged periodic-seed stream has coherent triangular splitting and Haar convergence but no fixed original-coordinate dominant branch | C-NPN balances every cylinder at every prefix via nested low-discrepancy necklaces, not repeated exhaustive seed stages; C-KRR/C-AB fail before constructing a stream; C-DMR uses one arithmetic subsequence and no splitting claim |
| T111 | report SHA `89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8`; sources literature-checked, deductions proof sketch | the report argues that totally de Bruijn synchronization plus odd-digit coding gives exact remote cyclic-label separation through `4^m` starts | C-NPN is adjacent but distinct: nested perfect necklaces give aggregate all-cylinder discrepancy at every `N`, with no odd-code adjacency exclusion; the vector candidates and C-DMR use neither T111 selector nor metric separation |
| T116 | report SHA `573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1`; sources literature-checked, deductions proof sketch | the report argues that effective weighted-tree avoidance constructs a sibling point with individual decimal-difference separation; its FMS card duplicates T111 | C-NPN controls aggregate block incidences instead of avoiding each difference; C-KRR/C-AB identify the absent adaptive balancing theorem; C-DMR is a fixed-depth exponential-sum model |
| T117 | report SHA `ee6974209f7e6064f30ec3ae83240cb1e7994e66566e920417dbf361da0ff30b`; sources literature-checked, deductions proof sketch | the report argues that finite Legendre periods have pointwise growing-word cancellation and low collisions for `m<0.5 log_2 p`, but no one coherent infinite word | C-NPN supplies one coherent all-prefix word without character sums; C-DMR supplies one arithmetic word but lacks growing-depth constants; C-KRR/C-AB test adaptive selectors rather than finite algebraic periods |
| rejected T109 | report SHA `6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf`; sources literature-checked, transfers proof sketch, final record rejected | the rejected report considered Markov-TV, shadowing, and Wasserstein robustness; its review found that certificate failures were incorrectly treated as necessary | T122 makes no model-to-pi robustness inference. C-NPN is only a sibling; the three rejections are sufficient-theorem applicability failures, not refutations of the target |
| rejected T119 | byte-exact delivered `prior-t119-REPORT.md`, SHA `72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a`; source statements literature-checked, deductions proof sketch, rejected | Sections 2 and 4-6 distinguish three rank notions; the rejected report argues at proof-sketch level that process-law collision concentration alone does not force low predictive, ordinary Hankel, or moment rank, but its review records that the process-law separator supplies no finite empirical bridge | T122 instead derives, at proof-sketch level, forward collision upper bounds from direct incidence discrepancy. C-NPN uses interval discrepancy, C-KRR/C-AB fail at the digit-update applicability step, and C-DMR fails at moving depth; none infers rank or uses T119's process-law separator as a premise |
| T120 | staged report SHA `8b375d1c06cbf9549e5f1919d25b227a9479be7bc3a5ed70955f5718a996dad5`; source statements literature-checked, deductions proof sketch, replay experiment | the report argues that countable-state renewal and inducing systems fail its return-tail, named-path, or fractal-Fourier collision certificates; no proof-sketch candidate supplies named-point growing-depth collision control | C-NPN is one explicit all-prefix word with direct cylinder discrepancy, not a stationary renewal law. C-KRR/C-AB test selectors rather than return tails, and C-DMR is a fixed arithmetic word. T122 uses no measure-to-named-point transfer and inherits no T120 deduction |
| T121 | staged report SHA `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2`; source statements literature-checked, deductions proof sketch, replay experiment | the report's proof sketches concern aggregate Walsh collisions for a finite Legendre model, finite-necklace endpoint charges, a Stoneham all-start model, and fixed-order automatic bounds | T121 Section 4 records Becher-Carton's all-prefix pointwise discrepancy as a screened source theorem, so C-NPN is not claimed as a novel fingerprint against T121. T122 isolates that literature-checked theorem's proof-sketch moving-depth incidence-to-collision chain. It does not use T121's aggregate Walsh, finite-block endpoint, Stoneham, or fixed-order Gowers deductions |

The normalized T122 survivor fingerprint is therefore

```text
one computably selected nested-perfect-necklace digit stream
  -> all-prefix interval discrepancy O((log N)^2/N)
  -> every overlapping cylinder count has O(log^2 N) error
  -> E_x(N,m)<=N^2/10^m+O(N log^2 N)
  -> logarithmic-depth ordered collisions are o(N^2/m).   (8.1)
```

This fingerprint is constructive aggregate balancing. It is not renewal
staging (T37/T49 or T120), remote exact separation (T111), individual avoidance
(T116), finite-period character cancellation (T117), perturbative transfer
(T109), low-rank inversion (T119), or T121's aggregate Walsh/finite-block
necklace calculation. T121 independently records the same Becher-Carton
all-prefix discrepancy theorem as a screened comparator, so no novelty claim is
made for C-NPN.

## 9. Separate pi-specific transfer certificate

No source connects its constructed word to pi. A mechanism-specific sufficient
certificate would have to be stated before any transfer:

```text
PI-ADMISSIBLE (not asserted):
there is an effective nested-necklace or adaptive vector-balancing state
whose invariant proves, uniformly for all sufficiently large N and every
1<=m<=floor(kappa*log_10 N),

  max_w |#{0<=i<N: the pi decimal block at i is w}-N/10^m|
    <= C(log N)^2,

and the actual next decimal digit of pi belongs at every step to the
state's certified admissible-digit set.                              (9.1)
```

A conditional-expectation variant must give a computable potential `Phi` and
prove that the actual pi digit always satisfies the one-step inequality that
keeps `Phi` within the bound yielding (9.1). Merely knowing that some digit has
nonpositive conditional increment constructs a sibling digit, not pi.

Certificate (9.1) is deliberately stronger than collision decay and is not
claimed to be necessary. Identifying every pi digit with the particular C-NPN
output would also suffice but is stronger still. Neither certificate is
provided, suggested, or tested here. Failure of either would reject only that
transfer certificate.

## 10. Replay, successor, and scope

From a directory containing only the delivered artifacts, run

```text
python3 verify_t122.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical, seven PDF, and vendored T119 report hashes,
the T119 card and verdict anchors, exact source anchors
and their page locations, both caps, four candidate cards and their calculation
or rejection markers, all mandatory prior rows, endpoint and incidence
definitions, algebraic collision identities, the non-antipodal and
local-convexity obstructions, uniqueness of the verdict and successor markers,
and the scope firewall. These are finite transcription checks, not proofs of
the asymptotic deductions.

BOUNDED_SUCCESSOR: Formalize the general interval-discrepancy-to-ordered-cylinder-collision lemma behind (3.8) and (4.4) for arbitrary base, without adding any pi premise.

TERMINAL_VERDICT: develop (C-NPN A13 sibling mechanism only; no fixed-pi, C1, or C2 conclusion)
