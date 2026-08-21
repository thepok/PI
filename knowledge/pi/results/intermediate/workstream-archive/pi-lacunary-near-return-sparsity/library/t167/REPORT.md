# T167: bounded G28 cross-domain mechanism scout

Audit date: 2026-08-13 UTC.

Statements attributed to S1-S4 are `literature-checked` against the pinned
primary PDFs and exact locators in `SOURCE_LEDGER.csv`. New comparisons,
substitutions, and transfer analyses are `proof sketch`. `verify_t167.py` is an
`experiment` checking artifact integrity and declared arithmetic; it proves no
universal mathematical claim. Every pi premise below is an `unproved pi
transfer`, not an assertion.

```text
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 12
SEARCHED_DOMAIN_COUNT: 4
SEARCHED_DOMAIN_MINIMUM: 3
RETAINED_CANDIDATE_COUNT: 2
RETAINED_CANDIDATE_CAP: 4
EXCLUSION_LEDGER_RANGE: T89-T165
EXCLUSION_LEDGER_COUNT: 77
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement and normalized scope

The canonical question has no external source URL; its provenance states that
this program formulated it on 2026-07-22. The byte-exact
`canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks whether every integer `A>=1` has `n0` such that every `n>=n0` admits
some `N>=1` with `A*n*Q_pi(n,N)<=N^2`, where pairs are ordered, the diagonal is
included, and circle distance is strict. T167 studies only A13/A14 adjacent
models and does not alter or answer the question.

Ambiguities fixed before the scout:

1. One PDF is one inspected primary source; its text derivative is not another.
2. A domain is source-native, not a relabeling of the target.
3. Exact tuple absence is checked only against the supplied through-T165
   corpus and is not a global novelty claim.
4. Entropy of a language is not collision/Renyi-2 entropy without a proved
   conversion.
5. A theorem for almost every base does not locate fixed pi.
6. T164 and T165 are `sketch` notes. The T164 note argues, unverified, for
   primitive-substitution power-freeness/return separation; the T165 note
   argues, unverified, for Champernowne alignment/carry fiber counting. Neither
   note supplies a premise. Both fingerprints are hard-excluded by the agenda.

## 2. Bounded search and exclusion ledger

The search stopped after four previously unaudited PDFs in four domains:
lacunary dynamics, symbolic return statistics, symbolic decimation, and
algebraic-power arithmetic. `SOURCE_LEDGER.csv` records every exact source hash,
locator, normalized fingerprint, disposition, and nearest prior branch.

`EXCLUSION_LEDGER.csv` has exactly one consecutive row for every T89-T165. Rows
T89-T162 preserve T163's latest accepted machine-readable ledger. Refreshed rows
record T163 as pinned literature, and T164/T165 at their actual `sketch` level.
No deduction from any prior report is imported.

The artifact vendors byte-exact T155's through-T154 concatenated
`PRIOR_THEOREM_SOURCE_LEDGER.txt`, SHA-256
`200fa591d845c0a4f3273a76cb79bacc007716443791a4c0a4953777bb909a37`,
so replay can check all four complete hashes and arXiv identifiers without
repository access. Later exact source-ledger pins checked before selection were:
T155 `42458421...`, T157 `f1140f51...`, T158 `5d48e9a3...`, T159 sketch note
`bdc5807c...`, T160 `1d8d7c88...`, T161 sketch note `857e5e7b...`, T162
`52f4b4ae...`, T163 `b8aa0ecf...`, and T164 sketch note `12312a2b...`.
T156 has no accepted artifact. T165 delivered no separate source ledger; its
report hash `a151ea4c...` pins the hard-excluded Champernowne fingerprint.

The hard exclusions are explicit: primitive-substitution power-freeness (T164),
Champernowne alignment/carry counting (T160/T165), graph expansion (T124/T158),
pair recurrence (T95/T100/T120/T155/T162), Palm-Stein clustering (T155/T159),
and shell Fourier decay (T104/T163). Earlier fingerprints in the ledger are also
excluded. S1 and S2 were inspected but screened because their normalized
mechanisms already occupy metric-correlation and pair-recurrence cells.

The four PDF and text hashes do not occur in the supplied prior theorem/source
ledger. This establishes only that these exact tuples were previously unaudited
in this clean context. C-DEC is nearest to T125/T131/T135 but uses source-native
arithmetic-progression interleaving entropy rather than correlations, Euler
ordering, or Renyi projection tensorization. C-POW is nearest to T127/T130 but
uses effective one-power repulsion rather than Mahler lifting or S-unit counts.

## 3. Candidate C-DEC: residue-class interleaving entropy

### Literature-checked claim and ranges

S3 fixes a finite alphabet. For arbitrary subsets `X_0,...,X_(q-1)` of the
one-sided shift, Theorem 2.18 states

```text
H_p(X_0 interleave ... interleave X_(q-1))
    <= (1/q) sum_(a<q) H_p(X_a).                           (3.1)
```

Theorem 2.19 gives equality when every factor has stable prefix entropy.
Theorem 2.20 says weakly shift-stable sets have stable prefix entropy equal to
topological entropy and therefore inherit the equality formula. These are set-
language support statements, not claims about one prescribed sequence.

### Quantitative rejection test (`proof sketch`)

At one finite depth, let `R_a` be the number of supported residue-factor words.
Interleaving gives only

```text
R <= product_(a<q) R_a,       log R <= sum_(a<q) log R_a.  (3.2)
```

Collision energy instead depends on multiplicities `c_w`:

```text
E_m = sum_w c_w^2.                                           (3.3)
```

For every `M>=2`, a supported language of size one permits multiplicity vector
`(M)` and energy `M^2`; a language of size `M` with vector `(1,...,1)` has
energy `M`. A support upper bound therefore supplies no upper bound improving
`E_m<=M^2`. In particular, it cannot imply the required

```text
E_m <= M^2/(A*m).                                           (3.4)
```

This fails before overlap, endpoints, or fixed-point issues arise.

### Additional unproved transfer toward T7

`PI-DEC-T7` (`unproved pi transfer`): on one unbounded family of actual pi
prefixes, prove conditional Renyi-2 bounds for every required residue
decimation and an overlap-compatible tensorization
`E_m <= product_a E_(a,m_a)` with constants strong enough to imply (3.4).
S3 provides only language support entropy and no pointwise pi statement.

Disposition: close C-DEC. The additional premise replaces the source invariant
with the missing quadratic invariant.

## 4. Candidate C-POW: effective algebraic-power repulsion

### Literature-checked claim and ranges

S4 Lemma 1.4 defines `C(alpha)` for real algebraic `alpha>1` from its minimal
polynomial and conjugates. Theorem 1.5 defines `N_alpha`: multiples of the least
positive `h` for which `alpha^h` is an integer or quadratic Pisot unit, if such
an `h` exists, and all positive integers otherwise. It states effectively
computable `tau(alpha)>0` and `n0(alpha)` such that

```text
||alpha^n|| >= C(alpha)^(-(1-tau(alpha))*n)
for n>n0(alpha), n in N_alpha.                             (4.1)
```

Theorems 1.1-1.3 and Lemma 1.4 record predecessor rational, ineffective, and
Liouville-type bounds. No claim here extends (4.1) beyond algebraic `alpha` or
its stated exponent set.

There is a source-text ambiguity worth recording rather than repairing:
`N_alpha` as printed includes integer-power exponents, where the displayed
positive lower bound appears incompatible with `||alpha^n||=0`; the surrounding
proof discusses nonmultiples in that case. T167 needs neither interpretation,
because every literal route to (4.2) fails already at the theorem's algebraic-
power input type. C-POW is retained as a source cell with this explicit caveat,
not as a discharged premise.

### Quantitative rejection test (`proof sketch`)

A literal T10 frequency has the shape

```text
||h*(10^r-1)*10^j*pi||.                                   (4.2)
```

Substituting `alpha=10` into S4 gives `||10^n||=0`, not (4.2). Substituting
`alpha=pi` would require a new verification of S4's algebraic-input hypothesis
and, in any case, yields `||pi^n||`, not (4.2). Choosing a base involving pi
still produces powers rather than the required linear multiples. Thus the
literal substitutions supplied by the source do not reach even one T10
summand. The mismatch is exact and precedes questions about the exponential
rate in (4.1).

```text
alpha=10:  source observable ||10^n|| = 0;
alpha=pi:  source hypothesis "alpha algebraic" is not available, and
           source observable ||pi^n|| != ||h(10^r-1)10^j*pi||;
therefore: no legal source substitution produces the T10 coefficient.       (4.3)
```

### Additional unproved transfer toward T10

`PI-POW-T10` (`unproved pi transfer`): prove, uniformly in the exact T10 ranges
of `h,r,j,k`, quantitative pairwise phase separation

```text
||h*(10^r-1)*(10^j-10^k)*pi|| >= rho(h,r,j,k)              (4.4)
```

and a deterministic large-sieve or differencing conversion from (4.4) to the
corresponding finite exponential-sum bound, with the resulting weighted sum and
boundary errors below T10's stated budget. Individual lower bounds such as
(4.1) do not themselves imply cancellation. Both (4.4) and the conversion are
absent from S4.

Disposition: close C-POW. Its sourced algebraic one-power theorem does not
touch the prescribed decimal ray.

## 5. Screened sources

S1 Theorem 1.1 proves Poissonian correlations of every finite order for
`({alpha^n})` for almost every `alpha>1`; Theorem 1.2 gives a more general
almost-every-parameter theorem under `(1.3)-(1.4)`. This is the metric
correlation fingerprint already bounded by T104/T110, and no exceptional-set
removal locates pi.

S2 defines first returns of balls/cylinders and studies distributions and Renyi
rates. Its own text labels the direct `p(n,k)` derivation around (21)-(25)
heuristic and attributes the cumulative theorem to prior work. More decisively,
first-return statistics are the prohibited pair-recurrence cell already
represented by T120/T155/T158/T162. No S2 claim is used as a premise.

## 6. Scope and endpoint

No candidate survives its first displayed discriminator. No successor is
selected. The negative map closes only these four exact source/theorem cells
and normalized fingerprints; it does not discourage a theorem that directly
controls prescribed pi collision multiplicity or the exact T10 coefficients.

`SCOPED VERDICT (1/1): CLOSE.`

There is no fixed-pi result, no A1 result, no C1 result, and no C2 result.
Literature statements, proof-sketch comparisons, the replay experiment, and
unproved pi transfers are separate throughout.

## 7. Artifact-only replay

From a directory containing only the delivered files:

```text
python3 verify_t167.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay checks hashes, four-domain/twelve-source/four-candidate caps,
consecutive T89-T165 coverage, exact locator presence, prior exact-tuple
absence against the vendored ledger, both candidate screens and transfer
markers, exactly one verdict, and zero successors. It is an `experiment`, not
a proof of a source theorem or transfer.
