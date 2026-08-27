# T175: bounded prescribed-point exceptional-cover audit

Audit date: 2026-08-13 UTC. Source statements in Section 4 are
`literature-checked` against the three pinned primary PDFs and exact locators in
`SOURCE_LEDGER.csv`. The grid cover, source applications, comparisons, and
transfer analysis are `proof sketch`. `verify_t175.py` is an `experiment` for
artifact integrity and finite symbolic checks; it proves no universal claim.

```text
SEARCHED_DOMAIN_COUNT: 3
NEW_SOURCE_THEOREM_TUPLE_COUNT: 3
NEW_SOURCE_THEOREM_TUPLE_CAP: 8
CANDIDATE_COUNT: 3
CANDIDATE_CAP: 3
PRESCRIBED_POINT_TEST_COUNT: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement and normalized scope

The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks, for the ordered diagonal-inclusive strict circle-distance count, whether

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N)<=N^2.
```

T175 changes the question to a finite A13/A14 exceptional-set audit and proves
nothing about that fixed-pi assertion. The canonical source URL is local: the
statement provenance says the program formulated it on 2026-07-22; no external
source URL exists to preserve.

Ambiguities fixed before the audit:

1. A source/theorem tuple is one primary PDF together with the exact theorem
   and locator range inspected; its text derivative is not another tuple.
2. Exactly three source-native domains are searched, not three labels for one
   theorem: restricted-denominator approximation; arithmetic or fractal Fourier
   decay; Mahler or functional-equation constants.
3. A candidate is one source theorem tested against the common bad set below.
   Retention for testing is not endorsement.
4. "Effective cover" here means a displayed finite rational interval list whose
   count, diameter, endpoint bit complexity, and parameter uniformity are known.
5. "Independent nonmembership" means a theorem whose conclusion is not a
   restatement of the required exponential-sum inequality. Irrationality,
   transcendence, support membership, almost-everywhere, dimension, winning,
   and constructive selection are tested literally and are not silently
   strengthened.
6. T113 is a readable unverified note under `notes/t113/REPORT.md`, SHA-256
   `30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445`;
   active T173-T174 are unavailable. No note claim is imported, and no content
   is inferred from an unavailable item.

## 2. Common bad set and explicit effective cover

Write `e(t)=exp(2*pi*i*t)`. For integers

```text
M>=1, R>=1, H>=1, eta in Q, 0<eta<=1,
1<=r<=R, 1<=|h|<=H,
```

put

```text
S_(M,r,h)(x)=sum_(j=0)^(M-1) e(h*(10^r-1)*10^j*x)

B(M,R,H,eta)={x in [0,1]:
  max_(1<=r<=R, 1<=|h|<=H) |S_(M,r,h)(x)| >= eta*M}.
```

This is exactly the finite maximum requested by the agenda. The signs are
retained even though absolute value makes `h` and `-h` redundant.

### 2.1 Lipschitz constant

For fixed `r,h`, differentiation and the triangle inequality give

```text
|S'_(M,r,h)(x)|
 <= 2*pi*|h|*(10^r-1)*sum_(j<M)10^j
 = (2*pi/9)*|h|*(10^r-1)*(10^M-1)
 <= L(M,R,H),

L(M,R,H)=(2*pi/9)*H*(10^R-1)*(10^M-1).
```

This holds uniformly for every legal `r,h` and every real `x`.

### 2.2 Rational grid cover

Set

```text
K=ceil(2*L(M,R,H)/(eta*M)),
I_k=[max(0,(k-1)/K), min(1,(k+2)/K)] for 0<=k<K.
```

Evaluate every legal sum at each rational grid point `x_k=k/K`. Retain `I_k`
if for at least one legal `(r,h)`

```text
|S_(M,r,h)(x_k)| >= eta*M/2.                    (2.1)
```

If `x` is bad, choose `k=floor(K*x)` (and `k=K-1` at `x=1`). Then
`|x-x_k|<=1/K<=eta*M/(2L)`, so the Lipschitz bound implies (2.1).
Consequently the retained rational intervals cover the whole bad set.

The parameters are explicit:

```text
cover count                    <= K,
interval diameter              <= 3/K <= 3*eta*M/(2L),
number of tested sums/grid     = 2*R*H,
number of terms                = M,
rational-phase term operations = at most 2*K*R*H*M,
rational endpoint bit length   <= 2+ceil(log_2 K).
```

The complex comparisons in (2.1) are decidable because `eta` and all phases are
rational:
every term is a `K`-th root of unity, so the squared magnitude is an explicitly
represented real algebraic number in the cyclotomic field of degree
`phi(K)<=K`. Exact cyclotomic arithmetic decides comparison with the rational
threshold; equality retains the interval. Thus the list uses at most
`2*K*R*H*M` root-of-unity additions before exact comparisons, with field degree
at most `K`, and no oracle or choice is hidden. The cover is uniform in every
displayed finite parameter, but its count and exact arithmetic are exponentially
large in `M+R` because `L` contains `10^(M+R)`.

This cover alone gives no cancellation and no prescribed-point exclusion. A
union bound, measure-zero limit, winning set, or selected point would still not
decide whether a named constant lies in `B(M,R,H,eta)`.

## 3. Bounded search and nonduplication

The search stopped after exactly one previously unaudited primary tuple in each
required domain. Full versioned URLs, SHA-256 values, exact theorem locators,
and theorem ranges are in `SOURCE_LEDGER.csv`. Exact stable-ID and title searches
against the supplied corpus found no prior audit of these three tuples. This is
only a bounded corpus statement, not a novelty claim.

The nearest existing cells are T104 and T171, which searched the same broad
domains using different exact tuples, and T167's algebraic-power repulsion. The
new source tuples are Tapia `2602.22512v1`, Algom--Rodriguez Hertz--Wang
`2109.13017v2`, and Kaibkhanov--Skopenkov `1204.5045v3`. Exactly three candidate
cards are retained for the required independent-point tests; all are rejected.

## 4. Candidate cards

### 4.1 C-RD: multiplicative restricted-denominator covers

**Literature.** Tapia defines

```text
M(psi)={x in [0,1]:
 ||a_n*x+c_n||*||b_n*x+d_n||<psi(n) infinitely often}.
```

Theorem 1, for positive integer sequences `a_n,b_n`, gives zero Hausdorff
`s`-measure for `0<s<1` under the two convergent series in equation (7), and a
Lebesgue-zero conclusion under its displayed logarithmic series. Lemmas 2-3
give a finite cover for
`F(eta,xi)={x:||a*x+c||<eta, ||b*x+d||<xi}` when
`0<eta,xi<1` and `1<=a<=b`: at most

```text
O((b*eta+a)*max(1,log(b)/a))
```

intervals of length `2*min(eta/a,xi/b)`. Exact ranges and locators are in S1.

**Related-model deduction.** S1 is genuinely about effective finite cover
complexity, but its sets impose products of two scalar near-integer events. It
does not contain the maximal exponential-sum bad set or a conversion from large
`|S|` to one such product event. The common cover in Section 2 applies without
claiming that S1 improves it.

**Independent prescribed-point test (one).** Name the Mahler constant

```text
mu=sum_(n>=0) 2^(-2^n).
```

Apply S3's independent transcendence theorem. It certifies that `mu` is
transcendental. Transcendence excludes roots of integer polynomials, but every
set `B(M,R,H,eta)` is defined by a finite trigonometric inequality. The source
gives no theorem that a transcendental number avoids these rational interval
covers. Therefore the test **fails to certify**
`mu notin B(M,R,H,eta)`. This premise is independent rather than T10-equivalent,
but too weak.

**Disposition:** reject C-RD. Hausdorff-zero limsup conclusions and scalar
restricted-denominator covers do not address the prescribed point or the
maximal sum.

### 4.2 C-FD: logarithmic Fourier decay of self-conformal measures

**Literature.** S2 defines self-conformal Bernoulli measures for an
orientation-preserving uniformly contracting `C^r` IFS. Theorem 1.1, for
`r>=2`, says that if one such measure lacks logarithmic Fourier decay, then the
IFS is `C^r`-conjugate to a linear non-Diophantine IFS. Equivalently, outside
that structural exception all its self-conformal measures have
`|mu_hat(q)|=O(|log|q||^(-alpha))` for some `alpha>0`. The theorem has no
separation assumption. Exact ranges and locators are in S2.

**Related-model deduction.** Inserting such decay into the second moment of a
fixed `S_(M,r,h)` controls an average over the ambient measure. Markov and a
finite union over `2RH` frequencies can bound the measure of the common bad set
for some parameter regimes. This remains an ambient-measure statement; the
grid cover supplies finite geometry but not membership of a named atom.

**Independent prescribed-point test (one).** Name the Mahler constant

```text
mu=sum_(n>=0) 2^(-2^n).
```

Apply S3's arithmetic theorem, independently of S2's ambient-measure theorem:
`mu` is transcendental. Transcendence neither identifies `mu` as generic for an
S2 self-conformal measure nor excludes it from a finite trigonometric-inequality
set. S3 therefore **fails to certify** `mu notin B(M,R,H,eta)`. This test is
independent of the Fourier-decay source and of T10 cancellation, but its
arithmetic conclusion is too weak.

**Disposition:** reject C-FD. Fourier decay of an ambient continuous measure
does not give prescribed-point nonmembership; `delta_mu` itself has Fourier
transform of modulus one.

### 4.3 C-MA: Mahler constant transcendence

**Literature.** S3 states and proves that

```text
mu=sum_(n>=0)2^(-2^n)
```

is transcendental. Its proof expands powers using representation counts and
uses the gaps in binary exponents. The final section extends the argument to
bounded integer coefficients with infinitely many nonzero terms and states a
sparse/loose exponent-sequence generalization. Exact ranges and locators are in
S3. This is a theorem about a named constant, not an almost-everywhere result.

**Related-model deduction.** Section 2 gives a completely effective cover of
`B(M,R,H,eta)` at this named `mu`; membership can be approximated for each fixed
tuple by certified interval arithmetic. What is absent is a theorem proving the
answer uniformly over growing `M,R,H`.

**Independent prescribed-point test (one).** Apply S3's own transcendence
theorem to its named `mu`. This is arithmetically independent of exponential-sum
cancellation: it says only that no nonzero integer polynomial vanishes at
`mu`. A bad-set interval generally contains transcendental points and a large
sum is an inequality, not an algebraic equality. Hence the theorem **fails to
certify** `mu notin B(M,R,H,eta)` for even one arbitrary parameter tuple.

**Disposition:** reject C-MA. Naming a functional-equation/Mahler constant and
proving transcendence does not remove it from the explicit bad cover.

## 5. Prior-item comparison

`PRIOR_COMPARISON.csv` records every mandated comparison and verification
level. In summary:

1. T3 records that its almost-everywhere lacunary sources do not identify the
   named point.
2. T45 blocks averaged or free-coefficient mixed inequalities; its regrouping
   is an unverified proof sketch and supplies no premise here.
3. T90 shows that changing to constructed fixed points solves only siblings.
4. T104 already separates ambient Fourier, Mahler, and restricted-denominator
   models from fixed-pi transfer; T175 uses different exact tuples and tests
   explicit covers plus nonmembership.
5. The readable T113 note argues, unverified, for variable-H avoidance and an
   unnamed sibling point. Nonemptiness does not locate the prescribed constant,
   and no T113 claim is used as a premise.
6. T116's effective selectors name artificial points, not the prescribed
   constant.
7. T167's effective algebraic-power theorem does not match decimal linear
   multiples; T175 does not repeat its source tuple.
8. T171 searched these three broad domains with three different exact tuples
   and retained no candidates; T175 tests a narrower cover/nonmembership
   fingerprint.
9. T173 and T174 are active but unavailable in the refreshed snapshot. Their
   identifiers are reserved, no proxy content is inferred, and no duplication
   claim is made against unknown content.

No prior note or proof-sketch conclusion is used as a discharged premise.

## 6. Honest unproved transfer toward T10

The literature and the elementary related-model deductions above stop before
the following hypothesis. A transfer toward T10 would require explicit
functions `eta(A,n)>0` with rational values, `M(A,n)>=1`, `R(A,n)>=1`, and
`H(A,n)>=1` covering the
exact legal T10 ranges, together with an **independent arithmetic theorem**
proving

```text
pi notin B(M(A,n),R(A,n),H(A,n),eta(A,n))
```

uniformly for every required `A,n`, where `eta*M` is no larger than the T10
cancellation budget. Merely computing the grid cover, proving its total length
tends to zero, constructing another point outside it, or asserting the displayed
nonmembership without independent arithmetic content is insufficient. If the
nonmembership premise is simply the same maximal exponential-sum bound, it is
equivalent to the desired cancellation and is rejected as circular.

No audited source provides this hypothesis. It is explicitly unproved and is
not asserted for pi.

## 7. Endpoint

`SCOPED VERDICT (1/1): CLOSE.`

Close only the audited fingerprint: combining the elementary finite grid cover
with these three exact source/theorem tuples does not yield prescribed-point
nonmembership. The decisive obstruction is unavailable arithmetic
nonmembership, not cover existence; the cover is explicit but exponentially
complex. No successor is selected (`SUCCESSOR_COUNT: 0`). This says nothing
about whether pi belongs to any bad set and makes no fixed-pi, A1, C1, or C2
claim.

## 8. Artifact-only replay

From a directory containing only the delivered files:

```text
python3 verify_t175.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay checks source and canonical hashes, exact counts, required domains,
locator/range fields, cover arithmetic on bounded integer samples, three
independent-test markers, all ten prior comparisons, exactly one verdict, and
zero successors. It is an `experiment`, not proof of the cited theorems or the
unproved transfer.
