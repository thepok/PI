# T180: bounded G28 cross-domain mechanism scout

Audit date: 2026-08-13 UTC. The four source statements below are
`literature-checked` against the pinned PDFs and exact ranges in
`SOURCE_LEDGER.csv`. Applicability comparisons and quantitative screens are
`proof sketch`. The replay is an `experiment` that checks pins, counts, and
declared finite inequalities; finite computation is not proof. No claim is made
about fixed pi, canonical A1, C1, or C2.

```text
SEARCHED_DOMAIN_COUNT: 4
SOURCE_THEOREM_TUPLE_COUNT: 4
SOURCE_THEOREM_TUPLE_CAP: 12
RETAINED_FINGERPRINT_COUNT: 0
RETAINED_FINGERPRINT_CAP: 4
EXCLUSION_LEDGER_RANGE: T89-T179
EXCLUSION_LEDGER_COUNT: 91
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable question and normalized scope

The local problem has no external source URL: its provenance states that this
system formulated it on 2026-07-22. The byte-exact `canonical_statement.txt`
has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether, for every integer `A>=1`, every sufficiently large integer
`n` admits an integer `N>=1` with

```text
A*n*Q_pi(n,N) <= N^2,
```

where `Q_pi` is the strict circle-distance count for the fixed orbit
`{10^j*pi}`, ordered and diagonal-inclusive. T180 does not change or answer
that question. All four cards are A13/A14 methodological siblings.

Conventions fixed before searching:

1. One tuple is one primary PDF plus the exact theorem/range inspected. Its
   text derivative is not another source.
2. The required screen uses the source's natural size variable `N` and
   `m=floor((1/4)*log_10 N)`. A candidate must survive in direction,
   multiplicity, and semantics, not merely have a favorable exponent.
3. A retained fingerprint must differ from every row of the inherited ledger,
   T177's algorithmic-randomness model, T178's exceptional-set/prescribed-point
   lane, and T179's additive structure of heavy return lags.
4. T178 has no artifact in the refreshed knowledge library and remains an
   active reserved cell. T179 is present only in refreshed recent-result
   metadata as a pinned, revision-required scout: its source tuples and
   heavy-return-lag fingerprint are reserved, but its stale T166 ledger claim
   and proof-sketch deductions are not imported.
5. Every transfer premise is an additional unproved premise, not evidence for
   pi. No conclusion from an unverified note is imported.

## 2. Bounded search and ledger

The clean-context scout inspected exactly four previously unaudited tuples in
four source-native domains and stopped:

| ID | Domain | Query/selection boundary |
|---|---|---|
| S1 | restricted-denominator approximation | deterministic approximation over represented denominators; selected arXiv:2504.09650v2 |
| S2 | fixed-point lacunary dynamics | pointwise rational-power orbit diameter; selected arXiv:2603.16794v3 |
| S3 | symbolic entropy or collision theory | overlapping maximal gapped repeats; selected arXiv:1802.10355v1 |
| S4 | short structured exponential sums | p-adic analytic short interval sums; selected arXiv:1407.4100v1 |

Searches of the supplied readable corpus found none of these four arXiv
identifiers, PDF hashes, or exact theorem tuples. This is bounded-corpus
nonduplication, not global novelty. `EXCLUSION_LEDGER.csv` contains exactly one
consecutive row for T89--T179. Its T89--T172 and T175 rows preserve T176's
mechanism inventory. T173 is refreshed to the readable unverified note now in
the library; T174 is refreshed to the rejected recent-result boundary without
importing its disputed locators or deductions; T176--T179 are appended with
their current verification boundaries. In particular, T166 is refreshed from
the staged Lean module: its machine-checked theorem gives separation of equal
factors in an externally certified power-free finite word and the consequent
maximum-multiplicity and collision-energy packing bounds. This does not
duplicate or subsume T179's full-heavy-lag additive-structure scout: T166
assumes a power-free certificate and bounds same-label positions by one-
dimensional separation, whereas T179 studies additive relations among a set of
heavy lags without that certificate. No T179 proof-sketch conclusion is used.

Hard exclusions applied to every card include representation, finite-state,
carry, occupancy, census, cumulant, recurrence, invariant-measure, and generic
metric mechanisms. T178 and T179 receive separate comparisons in each card.

## 3. S1: quadratic-form represented denominators

### Source statement (`literature-checked`)

Baier and Rahaman define `A_Q` on printed/PDF p. 2 as the positive integers
represented by a fixed positive-definite integral binary quadratic form `Q`.
Theorem 1, pp. 2-3, states that for every irrational `alpha` and every
`epsilon>0`, infinitely many `d in A_Q` satisfy

```text
||alpha*d|| < d^(-1/2+epsilon).
```

Theorem 4 and Corollary 1, pp. 3-4, make a weaker exponent quantitative. Under
the displayed convergent condition, with `2/5+3 epsilon <= beta < 1`, put
`X=q^(1+beta)` and `gamma=(1-beta)/(1+beta)`. Corollary 1 gives

```text
#{d in A_Q : d<=2X, ||alpha*d||<C1*d^(-gamma)}
  >> X^(1-gamma-C2/log log X).
```

The proof on pp. 9-11, equations (3.1)-(3.5), converts short residues modulo
`q` into the approximation bound.

### Quantitative screen and nonduplication (`proof sketch`)

Choose `epsilon=1/100` and `beta=1/2`, so the source condition
`2/5+3 epsilon<=beta` holds and `gamma=1/3`; write the source's scale as `N=X`.
The proof uses the weight from Theorem 4, supported on `[X,2X]`; therefore the
contributors to its lower bound have `X<=d<=2X`, not merely `d<=2X`. For
`m=floor((1/4)log_10 X)`, one has `10^(-m)>=X^(-1/4)`. Retaining the source's
constant, every such contributor obeys

```text
||alpha*d|| < C1*d^(-1/3) <= C1*X^(-1/3) <= 10^(-m)
```

whenever `X` is sufficiently large that `X^(1/12)>=C1`. Thus, only along the
Corollary 1 scales satisfying that explicit threshold, the proof supplies
`X^(2/3-o(1))` represented denominators at the requested distance scale.

This passes only a raw approximation-scale test. It is a lower bound for
returns in `A_Q`, whereas T7/T10 need upper collision or Fourier control on the
specific coefficients `10^i-10^j`. The nearest prior branch is T104/T171's
restricted-denominator lane. Unlike those metric sources, S1 is deterministic
for every irrational; unlike T179, it says nothing about additive structure of
heavy return lags. It also performs no T178 exceptional-set or prescribed-point
membership search. The denominator-family and direction gaps close the card.

Additional unproved transfer premise toward T10: prove a quantitative
intersection theorem placing enough decimal differences `10^i-10^j` in `A_Q`
with controlled pair multiplicity, and then convert the source's lower-return
statement into T10's required upper Fourier hypothesis. Neither step is in S1.

## 4. S2: alternating rational-power orbit diameter

### Source statement (`literature-checked`)

Lu and Zheng's Theorem 1.1, printed/PDF p. 2, states that for real
`xi!=0, eta`, integers `p>q>=1`, and `r=q/p`, assuming `xi` is irrational or
`p/q` is nonintegral,

```text
limsup {xi*(-p/q)^n+eta} - liminf {xi*(-p/q)^n+eta}
  >= (1+r-r^2)/p.
```

Theorem 1.2 and its proof on pp. 3-7 derive the bound from a bounded integer
sequence that is not ultimately periodic. Lemma 3.1 and the proof of Theorem
1.1 on pp. 7-8 use the floor-defect sequence
`s_n=-p floor(xi*(-p/q)^n+eta)-q floor(xi*(-p/q)^(n+1)+eta)`.

### Quantitative screen and nonduplication (`proof sketch`)

At `p=10,q=1,xi=pi`, S2 concerns the alternating sibling `(-10)^n*pi`, not the
canonical positive orbit. More decisively, a fixed macroscopic diameter does
not bound local multiplicity. Two sparse subsequences can realize the diameter
while `N-o(N)` points lie in one arc of length `10^(-m)`. Then

```text
Q(N,10^(-m)) >= (N-o(N))^2,
m*Q/N^2 ~ m,
```

so the requested screen fails sharply. The nearest branch is T91/T162's
symbolic recurrence lane, and S2 itself uses nonultimate periodicity and
subword complexity. It is therefore excluded recurrence/representation, not a
new fingerprint. It neither searches a T178 exceptional set nor analyzes
T179 heavy-lag additive structure.

Additional unproved transfer premise toward T7: prove both a positive-base
conversion from the alternating orbit and a uniform moving-arc bound
`Q(N,10^(-m))=o(N^2/m)`. Diameter alone supplies neither premise.

## 5. S3: maximal overlapping gapped repeats

### Source statement (`literature-checked`)

I and Koppl define finite words, segments, periods, and overlap conventions on
printed/PDF pp. 1-3. Corollary 2.2 is on p. 2. Lemmas 3.4-3.6 on pp. 5-7 map
maximal equal-arm repeats to endpoint-lag points and bound gamma-cover packings.
Theorem 3.7 and its proof on p. 7 state that for every word of length `L` and
real `alpha>1`, the number of maximal alpha-gapped repeats is less than

```text
3*(pi^2/6+5/2)*alpha*L.
```

### Quantitative screen and nonduplication (`proof sketch`)

For `N` legal length-`m` blocks, let `L=N+m-1` and `alpha=N/m`. The theorem
then gives `O(N^2/m)` maximal descriptors at the required
`m=floor((1/4)log_10 N)`. But collision energy counts every ordered equal-block
pair, not maximal descriptors. In the constant word the energy is `N^2`, while
maximal extension collapses many pairs into few descriptors. Thus the source
loses the exact multiplicity that T28 needs.

The nearest branch is T155/T160's run and closed-repeat charging; this is an
improved overlap-supporting implementation of the same descriptor-counting
cell. It is not T178's point-membership lane or T179's additive structure of
heavy return lags, but it remains prohibited census/recurrence charging.

Additional unproved transfer premise toward T28: uniformly charge every
ordered equal length-`m` pair to a maximal descriptor with `O(1)` load and then
transport exact block equality to T28's metric statistic. The constant-word
test refutes the first premise for general words.

## 6. S4: p-adic analytic B-process

### Source statement (`literature-checked`)

Milicevic's Definition 1, printed/PDF pp. 11-12, specifies a p-adically
analytic derivative class. Definition 2 on pp. 15-16 packages exponent data.
Theorem 4, pp. 32-33, proves the p-adic B-process and equation (36) gives the
square-root datum `omega_(1/2)`. The estimate is for short intervals of phases
`e(f(t)/p^n)` with the explicit valuation, length, and analyticity conditions in
Definitions 1-2 and equations (35)-(36).

### Quantitative screen and nonduplication (`proof sketch`)

Under the favorable but unjustified identification of interval length and
effective period with `N`, the square-root scale is

```text
N^(1/2)*log N = o(N/m^2)
```

at `m=floor((1/4)log_10 N)`. The exponent therefore passes a raw T10-shaped
screen. The source phase, however, is rational modulo `p^n` and lies in a
p-adic analytic derivative class. No theorem identifies it with
`e(h*pi*10^j)` uniformly in the T107 frequency range. The nearest branches are
T160/T176's trace-function and powerful-modulus short sums. This is another
broad structured phase family, not T178 point membership or T179 lag-additive
structure, and phase semantics close it.

Additional unproved transfer premise toward T107: construct, uniformly for
`0<|h|<=8000*10^(3m)`, a p-adic analytic representation of `e(h*pi*10^j)` with
total error below T107's Fourier budget, and separately prove T107's boundary
load. S4 supplies neither.

## 7. Endpoint

`SCOPED VERDICT (1/1): CLOSE.`

Close only the bounded proposition that one of these four exact tuples supplies
a genuinely unaudited mechanism ready for T7, T10, T28, or T107. S1 has a new
deterministic source statement but the wrong denominator family and direction;
S2 gives diameter rather than local multiplicity and uses excluded recurrence;
S3 counts maximal descriptors rather than ordered pairs; S4 has adequate raw
cancellation but the wrong phase semantics. No fingerprint is retained and no
successor is selected. This negative map says nothing
about whether pi satisfies the canonical estimate.

## 8. Artifact-only replay

From a directory containing only delivered files:

```text
python3 verify_t180.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay checks all source and canonical hashes, exact source anchors, four
domains, the twelve-source and four-fingerprint caps, consecutive T89--T179
coverage, T178/T179 nonduplication markers, one quantitative screen and one
transfer premise per card, exactly one verdict, no successor, and all no-claim
markers.
