# T181: bounded clean-context cross-domain mechanism scout

Audit date: 2026-08-13 UTC. Source statements below are
`literature-checked` against the pinned primary PDFs and exact ranges in
`SOURCE_LEDGER.csv`. Applicability comparisons and quantitative screens are
`proof sketch`. The replay is an `experiment`, not proof. No unverified note
claim is used as a premise.

```text
SEARCHED_DOMAIN_COUNT: 3
NEW_SOURCE_THEOREM_TUPLE_COUNT: 3
NEW_SOURCE_THEOREM_TUPLE_CAP: 12
RETAINED_FINGERPRINT_COUNT: 0
RETAINED_FINGERPRINT_CAP: 4
EXCLUSION_LEDGER_RANGE: T89-T180
EXCLUSION_LEDGER_COUNT: 92
T174_CLASSIFICATION: rejected
T166_CLASSIFICATION: machine-checked
T176_CLASSIFICATION: accepted pinned literature
T177_CLASSIFICATION: accepted sketch note
T178_CLASSIFICATION: accepted pinned literature
T179_CLASSIFICATION: accepted pinned literature
T180_CLASSIFICATION: accepted pinned literature
QUANTITATIVE_SCREEN_COUNT: 3
EXPLICIT_TRANSFER_PREMISE_COUNT: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Statement and scope

The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
Its provenance says this program formulated it on 2026-07-22, so there is no
external original-source URL to preserve. It asks whether, for the ordered,
diagonal-inclusive strict circle-distance count along the fixed decimal orbit
of pi,

```text
for every A>=1 there is n0>=1 such that every n>=n0 admits N>=1 with
A*n*Q_pi(n,N)<=N^2.
```

T181 changes neither the statement nor its quantifiers. It examines only A13
or A14 related mechanisms. In particular, an almost-everywhere theorem, a
constructed measure, or a weighted arithmetic short sum is not evidence for
the fixed pi orbit without the separately stated transfer premise.

Ambiguities fixed before source use:

1. One tuple is one versioned primary PDF and one exact theorem/proof range.
   A text extraction is not another source.
2. Previously unaudited means the exact stable-ID/theorem pair is absent from
   the readable source ledgers through accepted T180. This is a bounded-corpus
   statement, not global novelty.
3. A fingerprint records the operative quantitative mechanism, not a title.
   A new theorem whose mechanism is already reserved is closed, not retained.
4. Every test uses exactly `m=floor((1/4)*log_10 N)`, with the source's native
   size identified explicitly.
5. Retention requires source, theorem, and fingerprint nonduplication. No card
   survives, so retained-candidate obligations are vacuous; nevertheless each
   inspected card has one quantitative test and one explicit unproved transfer.
6. Sketch notes, including T173 and T177, supply exclusions only. Their
   mathematical claims are not imported. Rejected T174 supplies no premise.

## 2. Exclusion ledger and bounded search

`EXCLUSION_LEDGER.csv` has one consecutive row for each T89--T180. It records
T166 as machine-checked, T174 as rejected, T176 and T178 as accepted pinned
literature, and T177 as an accepted but unverified sketch note. The refreshed
snapshot now contains accepted pinned T179 and T180 artifacts. Their ten exact
source/theorem/fingerprint boundaries are transcribed in
`PRIOR_EXCLUSIONS.csv`: all six T179 tuples and all four T180 tuples are
reserved. No proof-sketch deduction from either report is treated as a premise.

The scout inspected exactly three new tuples and stopped:

1. Fixed-point lacunary dynamics: Peres--Yang, arXiv:2606.28860v1.
2. Arithmetic or fractal Fourier decay: Lai--Xie, arXiv:2601.03402v1.
3. Short structured exponential sums: Kim, arXiv:2603.23250v2.

The three stable IDs, PDF hashes, theorem ranges, and normalized fingerprints
are pairwise distinct. Exact-ID and theorem searches in the readable ledgers
through T180 found none of the three tuples. Semantic comparison closes S1 at
T178's maximal-gap branch, S2 at the recorded representation/invariant-measure
and ambient Fourier branches, and S3 at the broad structured-sum branches
T110/T160/T176 and T180-S4. Thus source/theorem novelty does not silently become
fingerprint novelty. T179's full-heavy-return-lag additive structure and every
T180 candidate remain excluded.

The hard exclusion also covers every recorded representation, finite-state,
carry, occupancy, census, cumulant, recurrence, invariant-measure,
generic-metric, and algorithmic-randomness mechanism. The source cap is
`3<=12`; the retained-fingerprint cap is `0<=4`.

## 3. S1: typical divisibility-chain maximal gaps

### Source statement (`literature-checked`)

Peres and Yang, *Maximal Gaps for Dilated Lacunary Integer Sequences*,
arXiv:2606.28860v1, Theorems 1.1--1.2 on printed pp. 2--3. The complete
Theorem 1.2 dependency range inspected is Section 5 setup and Proposition 5.2
on printed pp. 15--17, followed by the sharp upper and lower proofs on printed
pp. 17--21 (text lines 957--1382). For a Hadamard-lacunary integer sequence,
almost every dilation has maximal circular gap of order `log N/N`; under
`a_n | a_(n+1)`, the normalized gap tends to one.

Fingerprint: `typical_divisibility_chain_maximal_gap`. Its nearest prior branch
is T178's `fixed_dilation_nested_interval_maximal_gap`. The theorem's point
quantifier differs, but its operative statistic is still maximal-gap coverage
without multiplicity. It is theorem-nonduplicate but mechanism-duplicate and
is not retained.

### Test and transfer (`proof sketch`)

Take `N=10^12`, so `m=3` and `log(N)/N=2.76310211159e-11<10^-3`. Put
`M=ceil(N/log N)=36191206826`; use `M` roughly equally spaced points and repeat
one point `N-M` times. The maximal gap remains at most `1/M<=log(N)/N`, while
the relative ordered collision energy is at least
`(N-M)^2/N^2>0.9289`. Thus maximal-gap control alone fails the required
collision statistic.

Additional unproved premise toward T7: prove for fixed pi a uniform
decimal-cell second-moment occupancy estimate at depth `m`, strong enough for
ordered collision energy `O(N^2/m)`. The source supplies neither prescribed-
point membership nor multiplicity control.

## 4. S2: mixed-radix DEL Fourier summability

### Source statement (`literature-checked`)

Lai and Xie, *On Constructions of full-dimensional absolutely normal sets of
uniqueness*, arXiv:2601.03402v1, Theorem 1.7 on printed p. 8, proof setup in
Sections 3--5 on pp. 13--31, and final proof on pp. 31--33. They construct a
mixed-radix Cantor--Moran measure whose Davenport--Erdos--LeVeque double
Fourier-difference series converges for each integer base and nonzero integer
frequency; almost every supported point is absolutely normal.

Fingerprint: `mixed_radix_DEL_cross_frequency_summability`. The nearest prior
branches are T39/T103 invariant-measure models, T121 global Fourier L2, and
T132/T135 projection/tensor mechanisms. This is a constructed representation
and measure-level argument, both hard-excluded, so it is not retained.

### Test and transfer (`proof sketch`)

At `N=10^12`, `m=3`. Convergence of an infinite `N^-3` weighted series, with
base- and frequency-dependent constants, gives no stated finite cutoff or rate
that bounds one prefix's depth-three collisions. Qualitative normality also
gives no shrinking-depth rate. The quantitative screen fails.

Additional unproved premise toward T10: derive effective uniform finite-`N`
weighted Fourier bounds at all frequencies required at
`m=floor(log_10(N)/4)` for the fixed pi orbit. The source supplies neither
fixed-pi membership nor those rates.

## 5. S3: multiplicative-function short interval twists

### Source statement (`literature-checked`)

Jiseong Kim, *Short Exponential Sums and Ternary Correlations of Multiplicative
Functions*, arXiv:2603.23250v2. Definition 1.1 is on printed p. 2; Theorem 1.2
and Remarks 1.3--1.4 are on pp. 3--4; Lemma 2.1 and its complete proof are on
pp. 8--10 (text lines 406--601). For `g` in the defined divisor-bounded class
`F_k(0)`, a short interval of length `H`, and phase `a/q+gamma`, Theorem 1.2
gives, under its displayed analytic and scale hypotheses,

```text
sum g(r)e(r(a/q+gamma))
 << (q*|gamma|*X)^(1/2+epsilon^2)*H^(1/2)
    + H^eta*(log X)^(k^2-1).
```

This is genuinely a short structured exponential-sum theorem, not a complete
finite-field family. Fingerprint:
`multiplicative_L_second_moment_to_short_interval_additive_twist`. Its nearest
branches are T110/T160/T176's structured arithmetic phases and T180-S4's
short p-adic phase. The L-function input and additive twist differ from those
tuples, but broad structured-sum mechanisms are explicitly excluded, so it is
not retained.

### Test and transfer (`proof sketch`)

Identify source `H=N=10^72`, set `X=N^(4/3)=10^96`, `k=1`, `q=1`, `a=0`,
`epsilon=1/20`, `eta=3/4`, and `gamma=N^(-1/2)`. Then
`m=floor(log_10(N)/4)=18`, while
`gamma*N^(eta-epsilon/2)=N^(9/40)` tends to infinity. Ignoring the theorem's
implicit constant, its displayed terms have scales `N^(147/160)` and `N^(3/4)`,
and their sum is less than `N/m^2` at this test value. The raw exponent passes.
The screen still rejects transfer: the coefficients are divisor-bounded
multiplicative values and the phase is linear rational-plus-small, not the
unweighted geometric fixed-pi phase `e(h*pi*10^j)`.

Additional unproved premise toward T107: represent every required fixed-pi
decimal-ray sum as a source-admissible multiplicative-function short sum with
rational-plus-small linear phase, uniformly in T107's frequency range and with
effective constants below its boundary budget. The source provides no such
representation.

## 6. Scoped endpoint

**SCOPED VERDICT (1/1): CLOSE this T181 scout as a source-pinned negative map.**
The three exact source/mechanism cells are closed: S1 duplicates maximal-gap
coverage without multiplicity, S2 is a prohibited constructed-measure route,
and S3 has favorable raw cancellation but incompatible coefficients and phase.
No fingerprint is retained and no successor is selected. This closes neither
G28 nor any claim about fixed pi, A1, C1, or C2.

From a directory containing only delivered files, run:

```text
python3 verify_t181.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay checks pins, source anchors, caps, three domains, consecutive ledger
coverage, all accepted T179/T180 tuple exclusions, the three quantitative
screens, transfer-premise markers, exactly one scoped verdict, and no successor.
