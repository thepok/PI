# T178: bounded clean-context post-T175 G28 delta scout

Audit date: 2026-08-13 UTC. Source statements below are
`literature-checked` against the three pinned primary PDFs and exact locators in
`SOURCE_LEDGER.csv`. All specializations, screens, and transfer comparisons are
`proof sketch`. `verify_t178.py` and `raw_output.txt` are an `experiment` for
finite arithmetic and artifact integrity; finite evidence proves no universal
claim. Every route toward pi is an `unproved fixed-pi transfer`.

```text
SEARCHED_DOMAIN_COUNT: 3
NEW_SOURCE_THEOREM_TUPLE_COUNT: 3
NEW_SOURCE_THEOREM_TUPLE_CAP: 12
RETAINED_FINGERPRINT_COUNT: 1
RETAINED_FINGERPRINT_CAP: 4
EXCLUSION_LEDGER_RANGE: T89-T177
DUPLICATE_CHECK_THROUGH: T175
T174_CLASSIFICATION: rejected
T176_CLASSIFICATION: active reserved
T177_CLASSIFICATION: active reserved
QUANTITATIVE_SCREEN_COUNT: 3
EXPLICIT_TRANSFER_PREMISE_COUNT: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement and normalized scope

The canonical source is local; its provenance says the program formulated it
on 2026-07-22, so there is no external original-source URL to replace or
preserve. The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks whether, for the ordered diagonal-inclusive strict circle-distance
count along the fixed decimal orbit of pi,

```text
for every integer A>=1 there exists n0>=1 such that every integer n>=n0
admits an integer N>=1 with A*n*Q_pi(n,N)<=N^2.
```

T178 changes neither this statement nor its quantifiers. It audits A13/A14
adjacent mechanisms only and makes no fixed-pi, A1, C1, or C2 claim.

Ambiguities fixed before the search:

1. A source/theorem tuple is one versioned primary PDF plus one exact theorem,
   statement and proof ranges, and the internal dependencies actually inspected;
   its text derivative is not another tuple. External inputs cited by a source
   are named but are not silently counted as newly inspected tuples.
2. The exactly three source-native domains are fixed-point lacunary dynamics,
   restricted-denominator approximation, and arithmetic or fractal Fourier
   decay.
3. "Previously unaudited" means that the exact stable identifier and theorem
   tuple are absent from the readable through-T175 corpus. It is not a global
   novelty claim.
4. A retained fingerprint is a normalized mechanism absent from the ledger,
   not merely a new paper using an excluded mechanism.
5. `m=floor(kappa*log_10 N)` uses the screen's displayed `N` and `kappa`; it is
   a discriminator, not the canonical depth quantifier.
6. T172, T173, and other note entries are unverified `proof sketch` material.
   Their fingerprints are excluded, but no mathematical claim is imported.
7. T174 is rejected, while T176 and T177 are active unavailable reservations.
   No claim or fingerprint is inferred from any of those items.

## 2. Bounded search and exclusion ledger

The scout stopped after exactly three new primary source/theorem tuples, one in
each authorized domain. Exact-title, arXiv-ID, and source searches of the
readable through-T175 corpus found no prior audit of `2406.19802v1`,
`2409.18635v1`, or `1606.03495v2`. Li--Li--Wu is cited bibliographically in the
T163/T175 copies of Tapia but its exact theorem tuple was not audited there; a
reference mention is not a source/theorem tuple.

`EXCLUSION_LEDGER.csv` is the accepted T171 ledger through T170, extended by
one conservative row for each T171--T177. It has one consecutive row for every
item T89--T177 and therefore records the duplicate boundary through T175. In
particular:

- T171 and T175 reserve their exact pinned tuples and exclude functional/Mahler,
  generic metric, and ambient Fourier mechanisms.
- The T172 note argues, unverified, about fourth cumulants and occupancy; both
  are hard-excluded without importing its claims.
- The T173 note argues, unverified, about a prime-concatenation census; census
  is hard-excluded without importing its claims.
- T174 is classified `rejected`; its trace-product/Kifer cluster mechanism and
  comparator claims are not imported.
- T176 and T177 are classified `active unavailable` and reserved by identifier.

The inherited ledger also excludes every recorded representation,
invariant-measure, finite-state, carry, census, occupancy, recurrence, and
generic metric mechanism. The agenda additionally excludes algorithmic-
randomness tests, routine higher cumulants, and trace-product/Kifer cluster
corrections. None is retained here.

Exactly one fingerprint survives normalization:

```text
fixed_dilation_nested_interval_maximal_gap
```

S2 is a simultaneous limsup/Hausdorff-dimension mechanism nearest the recorded
metric/census cells. S3 is a complete finite-group orbit additive-growth
mechanism nearest T105/T117/T136; its one-dimensional T10 specialization is a
complete multiplicative orbit, not a new ordered-prefix mechanism. They are new
tuples but not retained fingerprints.

## 3. Candidate C-LAC: fixed-dilation maximal-gap construction

### Literature-checked statement

Stefanescu, *The dispersion of dilated lacunary sequences, with applications
in multiplicative Diophantine approximation*, arXiv:2406.19802v1, Definition 1
and Theorem 2.2 on printed p. 3, proof Section 4 on printed pp. 7--8.
For a real Hadamard-lacunary sequence `a_(n+1)>=r*a_n`, `r>1`, there exists one
fixed freely selected real `alpha` such that for every sufficiently large `N`,

```text
G({alpha*a_n mod 1:n<=N}) <<_r log(N)/N,                 (3.1)
```

where `G` is the maximal circular gap. The proof uses Theorem 2.1 and nested
intervals along `N_k=4^k`; equations (4.1)--(4.9) give the range. The source's
constants and onset are not numerical. Specializing to `a_n=10^n` constructs a
related-model point `alpha_10`, not pi.

Normalized fingerprint: `fixed_dilation_nested_interval_maximal_gap`.
Nearest prior branch: T116/T113's deterministic selector/avoidance lane. The
new distinction is one fixed selected dilation with quantitative all-large-N
coverage, rather than avoidance. This is retained as a related-model mechanism.

### Quantitative screen (`proof sketch` plus experiment)

Take `N=10^12`, `kappa=1/2`, and

```text
m=floor(kappa*log_10 N)=6,       10^(-m)=10^(-6).
```

Ignoring the unspecified source constant, the native scale is
`log(N)/N = 2.76310211149e-11`, far below `10^-m`; thus (3.1) can cover every
target at this subcritical depth for the selected point. But maximal gap has no
multiplicity control. A configuration with

```text
M=ceil(N/log N)=36191206826
```

roughly equally spaced distinct points and `N-M` additional copies at one point
has maximal gap at most `1/M <= log(N)/N`, while its ordered collision energy is
at least `(N-M)^2`, giving

```text
(N-M)^2/N^2 = 0.9289273898.
```

The T7 scale would require relative collision energy `O(1/m)` and eventually
tending to zero. Therefore maximal-gap coverage alone has the wrong statistic.

Explicit additional premise toward T7 (`unproved fixed-pi transfer`): prove
that the prescribed point pi, not a nested-interval-selected alpha, satisfies a
uniform local occupancy bound at every decimal interval of length `10^-m`, with
second-moment strength sufficient to give ordered collision energy `O(N^2/m)`.
The source supplies neither prescribed-point membership nor multiplicity.

Screen result: the fingerprint is retained for comparison because it is absent
from the ledger; the source does not supply the stated transfer premise.

## 4. Candidate C-RD: simultaneous power-denominator limsup dimension

### Literature-checked statement

Li, Li, and Wu, *Multiplicative Diophantine approximation with restricted
denominators*, arXiv:2409.18635v1, Theorem 1.3 on printed p. 4, proof Section 4
on printed pp. 15--16. For integers `b>a>=2` and positive
`psi:N->(0,1)`, define

```text
S_(a,b)(psi)={x:max(||a^n*x||,||b^n*x||)<psi(n) infinitely often}.
```

If the limit `tau=lim_(n->infinity) log_b(psi(n)^(-1))/n` exists and is greater
than one, then

```text
dim_H S_(a,b)(psi)=log_b(gcd(a,b))/(1+tau).              (4.1)
```

Normalized mechanism: simultaneous power-denominator limsup covering and
Hausdorff dimension. Nearest prior branch: T104/T150/T163/T175. It is not
retained because it is a generic limsup-size theorem and does not identify a
prescribed point.

### Quantitative screen (`proof sketch` plus experiment)

Take `N=10^12`, `kappa=1/2`, and `m=6` as above. To align the source threshold
with `10^-m=N^-kappa`, use its index `n=m` and constant
`psi(n)=10^-n=10^-m`. Choose `a=2`, `b=10`. Then

```text
tau=lim_(n->infinity) log_10(10^n)/n=1,
```

which fails the strict source hypothesis `tau>1`. If one strengthens to
`psi(n)=10^(-(1+epsilon)n)`, (4.1) is available but concerns an infinitely-often
set of Hausdorff dimension

```text
log_10(gcd(2,10))/(2+epsilon)=log_10(2)/(2+epsilon)<0.150515.
```

It still provides no membership decision for pi and no finite-prefix collision
upper bound. The theorem is therefore screened before any canonical transfer.

Explicit additional premise toward T28 (`unproved fixed-pi transfer`): prove
that pi belongs to a source-compatible simultaneous power-denominator class at
the required adaptive coefficients, with effective witnesses synchronized at
adjacent chain nodes and errors meeting T28's compatibility and closing
budgets. A Hausdorff-dimension identity supplies none of these data.

Screen result: the tuple is recorded, but its normalized mechanism is excluded
by the ledger and is not retained.

## 5. Candidate C-FD: finite-field orbit Fourier cancellation

### Literature-checked statement

Peluse, *On exponential sums over orbits in F_p^d*, arXiv:1606.03495v2,
Theorem 1.1 on printed p. 1, proof infrastructure pp. 3--11 and final proof
pp. 11--13. For fixed `d` and `delta,beta>0`, there is an existential
`epsilon(d,delta,beta)>0` such that if `H<=GL_d(F_p)` and the orbit `O=Hv`
satisfies

```text
|O|>=p^delta,
|O intersect P|<=|O|^(1-beta) for every hyperplane P,
```

then every nonzero additive Fourier coefficient of the complete orbit is at
most `p^(-epsilon)|O|`.

Normalized mechanism: complete finite-field group orbit plus hyperplane
nonconcentration and approximate-group growth gives pointwise Fourier saving.
Nearest prior branch: T105/T117/T136. In the T10-relevant specialization
that recorded branch. It is not retained as a new fingerprint.
`d=1`, `H=<10>`, the theorem is a complete multiplicative-orbit sum, already in
that recorded branch. It is not retained as a new fingerprint.
that recorded branch. It is not retained as a new fingerprint.

### Quantitative screen (`proof sketch` plus experiment)

Use the prime `p=1000000000039`, set the screen variable `N=p`, choose
`kappa=1/2`, and obtain

```text
m=floor(kappa*log_10 N)=6,
ord_p(10)=166666666673 > p^0.9.
```

Thus the complete one-dimensional orbit meets the size hypothesis with
`delta=0.9`. Affine hyperplanes in dimension one are singleton sets, and each
meets the orbit in at most one point. Fixing `beta=1/2`, the condition
`1<=|O|^(1-beta)` holds. Yet the first `m` ordered powers have no cancellation:

```text
|sum_(j<m) exp(2*pi*i*10^j/p)| = 5.999999999999842,
relative magnitude                     = 0.9999999999999737.
```

Deterministically, its distance from `m` is at most
`2*pi*(10^m-1)/(9p)=6.98131002639e-7`. Complete-orbit power saving therefore
does not truncate to logarithmic ordered prefixes.

Explicit additional premise toward T10 (`unproved fixed-pi transfer`): prove a
special-numerator incomplete-orbit estimate, uniform over T10's adaptive
`h,r`, for ordered prefixes of the residues nearest to
`h(10^r-1)pi` modulo compatible primes, together with a real-to-modular error
margin below T10's weighted budget. Peluse supplies only a complete-set bound
with an unspecified saving.

Screen result: the tuple is recorded, but its normalized mechanism is excluded
by the ledger and is not retained.

## 6. Scoped decision

**SCOPED VERDICT (1/1): HOLD AS MODEL.** This verdict applies only to the one
retained related-model fingerprint `fixed_dilation_nested_interval_maximal_gap`.
It does not claim that the mechanism applies to pi or approaches A1, C1, or C2
without the explicit unproved T7 transfer premise. The other two inspected
tuples are not retained because their normalized mechanisms already occur in
the exclusion ledger. No successor is selected.

## 7. Replay

Run in a directory containing only the delivered files:

```text
python3 verify_t178.py
```

The expected byte-for-byte output is `raw_output.txt`. The verifier checks the
canonical hash, source and text hashes, exactly three domains and tuples, the
caps, exact locator/range fields, consecutive ledger coverage T89--T177,
T174/T176/T177 classifications, one retained fingerprint, three numerical
screens, three explicit transfer premises, exactly one scoped verdict, no
successor, and the absence of fixed-pi/A1/C1/C2 claims.
