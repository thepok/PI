# T171: bounded clean-context G28 cross-domain mechanism scout

Audit date: 2026-08-13 UTC. Source statements below are
`literature-checked` against the three pinned primary PDFs and exact locators in
`SOURCE_LEDGER.csv`. All substitutions, comparisons, and applicability screens
are `proof sketch`. `verify_t171.py` is an `experiment` checking finite
arithmetic and artifact integrity; it proves no universal claim. Every transfer
toward pi is explicitly `unproved fixed-pi transfer`.

```text
PRIMARY_SOURCE_COUNT: 3
PRIMARY_SOURCE_CAP: 12
SEARCHED_DOMAIN_COUNT: 3
SEARCHED_DOMAIN_MINIMUM: 3
RETAINED_CANDIDATE_COUNT: 0
RETAINED_CANDIDATE_CAP: 4
EXCLUSION_LEDGER_RANGE: T89-T170
EXCLUSION_LEDGER_COUNT: 82
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement and normalized scope

The local canonical question has no external source URL; its provenance says
the program formulated it on 2026-07-22. The byte-exact
`canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks whether

```text
forall integer A>=1, exists n0>=1, forall integer n>=n0,
exists integer N>=1: A*n*Q_pi(n,N)<=N^2,
```

where `Q_pi` counts ordered pairs, includes every diagonal pair, uses strict
circle distance, and follows the prescribed fixed orbit `10^i*pi`. T171 studies
only A13/A14 adjacent literature and neither alters nor answers this question.

Ambiguities fixed before searching:

1. One primary PDF is one source; its text derivative is not another source.
2. Domains are source-native, not relabelings of one theorem.
3. "Previously unaudited" means exact stable identifier, PDF hash, and theorem
   locator absent from the supplied readable corpus; it is not a novelty claim.
4. A screened source does not count as a retained candidate. Zero candidates is
   permitted by the cap.
5. A metric almost-everywhere theorem does not locate pi.
6. Fourier decay of an ambient measure is not Fourier decay of `delta_pi`.
7. A signed binary pair correlation is not decimal block collision energy.
8. T164, T165, and T168-T170 are note-level `proof sketch` material; T166 is
   active/revising and T167 is pinned literature. No mathematical conclusion
   from a note-level item is used as a premise.

## 2. Bounded search and nonduplication boundary

The clean-context search stopped after exactly three previously unaudited PDFs,
one in each of these allowed domains:

1. Mahler or functional-equation constants;
2. restricted-denominator approximation;
3. arithmetic or fractal Fourier decay.

Exact-title, stable-ID, and PDF-name searches found none of `1710.03026`,
`1906.01151`, or `2408.02972` in the supplied knowledge library. The vendored
`PRIOR_THEOREM_SOURCE_LEDGER.txt` also contains none of those identifiers or the
three complete PDF hashes. This bounded corpus result establishes exact tuple
absence only. It does not establish global novelty.

No tuple is repeated within `SOURCE_LEDGER.csv`: the three stable IDs, full PDF
hashes, exact locator sets, and normalized fingerprints are pairwise distinct.
All three source cells are nevertheless screened because their operative
mechanisms enter prohibited prior lanes before reaching a fixed-pi frontier.
Therefore `RETAINED_CANDIDATE_COUNT` is zero.

## 3. Complete exclusion ledger through T170

`EXCLUSION_LEDGER.csv` contains exactly one consecutive row for every item
T89-T170. Its T89-T165 prefix is byte-for-byte the accepted T167 ledger,
vendored separately as `PRIOR_EXCLUSION_LEDGER.csv` with SHA-256
`85f31058e192d151117a7779d2c8d287a5c7033ae21aabf60c2855407e86b883`.
The appended rows are deliberately conservative:

- T166 is `active revise`, reserved by identifier, and hard-excluded as the
  power-free separation lane. Its unavailable/revising theorem is not imported.
- T167's four source/theorem tuples are reserved; T171 extends rather than
  reruns that scout.
- The T168 note argues, unverified, for iid mixed-lag collision-cluster ranks;
  this fingerprint is hard-excluded and supplies no premise.
- The T169 note argues, unverified, for sharp finite Champernowne counting;
  this fingerprint and the T165 lane are hard-excluded.
- The T170 note argues, unverified, for an iid third-cumulant expansion; this
  fingerprint and T159/T161 are hard-excluded.

The inherited rows exclude all earlier representation, invariant-measure,
finite-state, carry, additive-energy, determinant, avoidance, renewal,
global-L2, balancing, specification, tensorization, census, graph-expansion,
and recurrence mechanisms. The hard exclusions named in the agenda are thus
visible in one machine-readable ledger.

## 4. S1: automatic functional equation and large correlation

### Literature-checked source statement

Mérai and Winterhof, *On the pseudorandomness of automatic sequences*,
arXiv:1710.03026v1, Theorem 2 on PDF/printed p. 6 with proof pp. 6-7.
For an `F_2` sequence with generating function satisfying the displayed
algebraic equation

```text
h(x,y)=(x+1)^(2^ell)*((a1*x+a0)*y^2+y)+f(x),
ell>=0, deg f<=2^ell-1, (a1,a0)!=(0,0),
```

the order-two correlation measure satisfies

```text
C2(s,N)>N/(2^ell+2)-2 for every N>=2^(ell+1)+4.            (4.1)
```

Equations (6)-(7) extract exact dyadic coefficient recurrences. This is a
finite-prefix lower bound for a maximum over signed binary lag correlations.

### Quantitative screen (`proof sketch`)

The exact first discriminator is direction and observable. T7 requires an
upper bound on ordered, diagonal-inclusive decimal collision energy; T10
requires upper cancellation for each prescribed phase
`h*(10^r-1)*10^j*pi`. Equation (4.1) instead lower-bounds one maximized binary
signed correlation. No substitution identifies either target observable.
The normalized mechanism also lies in the prohibited finite-state/automatic
and fixed-order correlation cells nearest T110, T128, and T162.

`PI_S1_T10` (`unproved fixed-pi transfer`): prove that the parity projection of
pi's decimal digits has a generating function satisfying S1's exact algebraic
equation for one displayed `(ell,a0,a1,f)`, then prove a new sign-reversing
conversion from its resulting lower correlation to the required uniform upper
T10 exponential-sum bounds. S1 supplies neither premise; the directions are
opposed.

Disposition: `screened_close`.

## 5. S2: metric restricted-denominator counting

### Literature-checked source statement

Pollington, Velani, Zafeiropoulos, and Zorin, *Inhomogeneous Diophantine
Approximation on M0-Sets with Restricted Denominators*, arXiv:1906.01151v2,
Theorem 1 and equations (7)-(10), PDF/printed p. 3, under the introduction's
standing non-atomic convention. Let `(q_n)` be increasing and lacunary, meaning
`q_(n+1)/q_n>=K` for one `K>1`; let `gamma` be fixed and
`psi:N->[0,1]` positive. If a supporting probability measure has

```text
mu_hat(t)=O((log |t|)^(-B)) for some B>2,
```

then for every `epsilon>0`, for `mu`-almost every `x`,

```text
R(x,N)=2*Psi(N)+O(Psi(N)^(2/3)*log(Psi(N)+2)^(2+epsilon)).  (5.1)
```

No monotonicity of `psi` is stated. The theorem does not display the implied
constant or a finite starting index.

### Quantitative screen (`proof sketch` plus finite arithmetic)

Specialize only as a model to `q_j=10^j`, `gamma=0`, constant radius `10^-n`,
and `L` trials. Put `U=L*10^-n` and `epsilon=1`. Before the unknown big-O
constant, error divided by the main term is

```text
D(U)=0.5*U^(-1/3)*log(U+2)^3.                              (5.2)
D(10^10)>2.83;  D(10^20)<0.0106.
```

The replay recomputes these inequalities. Even where the nominal ratio is
small, (5.1) holds only for almost every point and supplies neither a membership
criterion for pi nor constants uniform in the growing lag/depth family. Its
route is ambient Fourier plus second moment, already prohibited by the
metric-Fourier and global-L2 exclusions nearest T104/T120/T167.

`PI_S2_T10` (`unproved fixed-pi transfer`): prove simultaneously for every
T10-required growing lag `r` that `(10^r-1)*pi` avoids S2's exceptional set,
with effective constants and starting ranges uniform in `r,n,L`, then aggregate
the resulting counts into T10's weighted Fourier budget. S2 supplies none of
this.

Disposition: `screened_close`.

## 6. S3: algebraic conjugates and self-similar Fourier decay

### Literature-checked source statement

Gao and Yip, *On the fractional parts of certain sequences of xi alpha^n*,
arXiv:2408.02972v2. The second part of Theorem 1.7, PDF/printed p. 3, says that
when algebraic `alpha>1` has a distinct conjugate outside the unit circle,
there are `delta4 in (0,1/2)` and `C(alpha)>0` such that, uniformly for
`1<=xi<=alpha` and every positive integer `N`, at least `floor(C log N)`
indices satisfy `||xi*alpha^n||>=delta4`. Theorem 4.2 and proof,
PDF/printed pp. 11-12, apply this to a non-atomic self-similar measure for an
IFS of `m>=2` maps `f_i(x)=r^(l_i)*x+a_i`, with positive integer `l_i`,
`gcd(l_i)=1`, the source-normalized `l1=l2` and `a1>a2`, and a non-degenerate
probability vector (`p_i>0`, `sum p_i=1`). If `r^(-1)` is algebraic and has a
distinct conjugate outside the unit circle, then some `gamma>0` satisfies

```text
|mu_hat(u)|=O((log |u|)^(-gamma)), |u|->infinity,           (6.1)
```

and `mu`-almost every point is normal to every integer base at least two.

### Quantitative screen (`proof sketch`)

The exact decimal specialization fails the source hypothesis before constants:
`r=1/10` gives `r^(-1)=10`, a degree-one algebraic number with no distinct
conjugate. Any indirect T10 use of (6.1) would again integrate a geometric sum
against an ambient measure, which is the prohibited global-L2/broad-Fourier
route nearest T104/T105/T136. It would still not select `pi` or all adaptive
frequencies.

`PI_S3_T10` (`unproved fixed-pi transfer`): construct a source-valid
self-similar model together with a proved quantitative coding of the prescribed
decimal orbit of pi into that model, preserving every adaptive T10 phase and
converting ambient Fourier decay to a pointwise maximal estimate at pi. No such
coding or exceptional-point removal is in S3.

Disposition: `screened_close`.

## 7. Endpoint and evidence separation

The literature layer consists only of the three statements with exact source
locators above. The applicability arguments are `proof sketch`. Equation (5.2)
and the verifier are finite `experiment` support only. Every named pi premise is
an `unproved fixed-pi transfer`. No related-model deduction is promoted to a
fixed-point statement.

`SCOPED VERDICT (1/1): CLOSE.`

This verdict closes only the three exact source/theorem/mechanism cells in
`SOURCE_LEDGER.csv`. There is no bounded successor. There is no fixed-pi result,
no A1 result, no C1 result, and no C2 result.

## 8. Artifact-only replay

From a directory containing only the delivered files:

```text
python3 verify_t171.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay checks all caps, exact PDF/text/canonical hashes, three distinct
domains, exact locator anchors, source tuple uniqueness and prior-ledger
absence, T89-T170 consecutive coverage, byte-preserved T89-T165 inheritance,
active T166 reservation, named hard exclusions, every screen and transfer ID,
finite arithmetic (5.2), exactly one scoped verdict, zero successors, and all
four no-claim markers. It is not a proof of a source theorem or transfer.
