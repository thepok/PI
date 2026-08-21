# T153: logarithmic-locality maximum-occupancy scout

Audit date: 2026-08-12 UTC.

The six source statements are `literature-checked` against the pinned primary
PDFs and exact locators in `SOURCE_PINS.md`. Every source substitution,
counterexample, novelty comparison, and transfer deduction newly made here is
a `proof sketch`. `verify_t153.py` and `raw_output.txt` are an `experiment`
checking finite instances, arithmetic, hashes, uniqueness, and report markers;
finite computation is not proof. The additional fixed-pi certificate in
Section 8 is an `unproved-transfer` and is not asserted.

```text
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 12
SEARCHED_DOMAIN_COUNT: 4
SEARCHED_DOMAIN_MINIMUM: 3
RETAINED_CANDIDATE_COUNT: 1
RETAINED_CANDIDATE_CAP: 4
KILL_TEST_COUNT: 5
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Provenance, normalized statement, and ambiguities

The canonical question has no external Erdos Problems URL. It was formulated
by this program on 2026-07-22. The delivered `canonical_statement.txt` is a
byte-exact copy with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

Canonical A1 asks whether every integer `A>=1` and every sufficiently large
`n` admit some `N>=1` such that `A*n*Q_pi(n,N)<=N^2`, where `Q_pi` counts
ordered, diagonal-inclusive metric circle near returns of the fixed orbit
`{10^j*pi}`. T153 does not answer or alter A1. Its block equality statistic is
the weaker A10/A13 sibling. An almost-everywhere, random-source, finite-word,
or artificial-word statement is A14 evidence only.

Quantifiers and conventions fixed before source selection:

1. The alphabet is `D={0,...,9}` and the finite word has exactly
   `L=M+m-1` digits, giving nonwrapping starts `0<=i<M`.
2. `m>=1`, `M>=1`, `A>=1`, and `K>=2`; the locality order is an integer
   `1<=r=r(m)<=m`, with the intended regime `r(m)=O(log m)`.
3. Short contiguous statistics mean all nonwrapping factor multiplicities for
   lengths at most `r`, with endpoints retained when a source theorem requires
   them. They do not mean arbitrary nonlocal coordinates.
4. The demanded implication is pointwise for every word satisfying a stated
   short-statistic certificate. A metric theorem does not become pointwise by
   selecting an unspecified typical path.
5. A candidate certificate may not assume maximum length-`m` atom, full-block
   min-entropy/no-repeat, T7, or T107. A source that does so fails circularity.
6. `O(log m)` includes constants small enough that `10^r<m`; this matters for
   the repeated-de-Bruijn kill test. A theorem requiring, for example,
   `r>2 log_10 m` is logarithmic in notation but does not obtain its conclusion
   from all logarithmic locality scales.

## 2. Exact occupancy and collision target

For `w in D^m`, put

```text
c_m(w)=#{0<=i<M:(x_i,...,x_(i+m-1))=w},
E_m=sum_(w in D^m)c_m(w)^2.
```

Expanding the squares gives the exact ordered, diagonal-inclusive identity

```text
E_m=#{(i,j) in {0,...,M-1}^2:W_i^m=W_j^m}.             (2.1)
```

Since `sum_w c_m(w)=M`,

```text
E_m=sum_w c_m(w)^2
   <=(max_w c_m(w))*sum_w c_m(w)
   =M*max_w c_m(w).                                     (2.2)
```

The candidate substitution demanded by the agenda is

```text
max_w c_m(w) <= M/(K*A*m)+B(M,m),                       (OCC-153)
B(M,m) <= M/(K*A*m).                                    (ERR-153)
```

Substituting every term, not suppressing constants, gives

```text
E_m <= M*(M/(K*A*m)+B(M,m))
    <= M*(M/(K*A*m)+M/(K*A*m))
     = 2*M^2/(K*A*m)
    <= M^2/(A*m),                                       (COLL-153)
```

where the last inequality uses `K>=2`. This is a sufficient symbolic collision
bound only. Neither `(OCC-153)` nor `(ERR-153)` is asserted for pi.

## 3. Bounded source and domain ledger

The scout stopped after six unique primary PDFs in four domains. Exact theorem
locators, URLs, hypotheses, hashes, and scope are in `SOURCE_PINS.md`.

| ID | Domain | Exact theorem tuple | Selection decision |
|---|---|---|---|
| S1 | symbolic collision | Karhumaki--Saarela--Zamboni, Definition 2.1, Lemmas 2.4/2.12, Theorem 2.14 | retained with S2 as one C-RABEL mechanism card |
| S2 | symbolic collision | Karhumaki--Puzynina--Rao--Whiteland, Proposition 3.3, Corollary 4.3, Propositions 4.7/5.3 | same source-family mechanism; merged, not a second card |
| S3 | symbolic/metric reconstruction | Levick--Shomorony, Definition 1, Theorem 1, Lemma 1 | screened: C-LCS/whole-block typicality duplicate |
| S4 | fixed-point lacunary dynamics | Coons--Evans--Manibo, Definition 1, Theorems 1/5, Corollary 2 and equation (10) | screened: exact T136/T146 NEG-M duplicate |
| S5 | arithmetic/fractal Fourier decay | Sahlsten--Stevens, Theorem 1.1 | screened: exact T104 F3/T150 duplicate |
| S6 | short structured exponential sums | Ostafe--Shparlinski--Voloch, equation (2.1), Theorem 2.4 and Remark 2.6 | screened: exact T136/T146 NEG-X duplicate |

No paper is counted twice. S1 and S2 are distinct papers but one normalized
mechanism: short factor census fixes a weighted de Bruijn flow and an Euler-path
equivalence class. They are therefore one candidate card, not two. S3--S6 are
not retained merely to fill the cap.

`SOURCE_ID_UNIQUENESS: PASS`
`THEOREM_TUPLE_UNIQUENESS: PASS`
`MECHANISM_CARD_UNIQUENESS: PASS`

## 4. Complete preselection novelty firewall

`PRIOR_INDEX.md` contains one explicit row for every item T89--T150 and was
completed before the Section 3 selection decisions. The comparator reports are
not mathematical premises. Literature statements retain their reports'
`literature-checked` label; prose deductions remain unverified `proof sketch`.

Mandatory exclusions are:

- T135 projection-to-full-law Renyi tensorization;
- T138 C-MINENT whole-block conditional min-entropy;
- T142 C-LCS metric longest-common-substring reconstruction;
- T144--T150 in their entirety;
- the T151 carry-cycle note, now readable but still an unverified `proof
  sketch`; T153 imports no conclusion from it;
- the T152 entropy-charging note, now readable but still an unverified `proof
  sketch`; T153 imports no conclusion from it.

Mechanical regression fixtures are explicitly caught:

- `DUPLICATE_FIXTURE_T104_T138: REJECTED`; T138 C-UDEXP repeats the exact
  Wang--Li--Li PDF SHA, Theorem 1.1 identity, and normalized restricted-power
  uniform-exponent mechanism screened in T104. Their supporting-definition
  locators are checked separately rather than falsely required to be identical:
  T104 uses the definition before (1.2) and equation (1.4), while T138 uses the
  definition of `v_hat_(b,A)`.
- `DUPLICATE_FIXTURE_T136_T146: REJECTED`; T146 repeats the exact three PDFs,
  load-bearing locator tuples, and normalized NEG-M/NEG-F/NEG-X mechanisms of
  T136: Coons--Evans--Manibo Corollary 2/Theorem 5, Baker--Banaji Theorems
  1.3/1.7, and Ostafe--Shparlinski--Voloch Theorem 2.4/Remark 2.6.

`verify_t153.py` reads the byte-pinned T104, T136, T138, and T146 fixture
reports from `PRIOR_EVIDENCE.tar.gz`, checks identifying anchors in each, and
checks each encoded source/theorem identity against the corresponding report or
vendored source-pin fixture. It then requires equality of the normalized
`(source SHA, theorem identity, mechanism ID)` records for all four duplicate
comparisons. Supporting locators are evidence-checked card by card. A fixture
hash or prose marker alone cannot pass these duplicate assertions.

The nearest nonduplicate boundaries for C-RABEL are T128's explicit nested de
Bruijn construction, T131's flow rounding/Euler tours, T144's one-depth types,
T147's shared-prefix adversary, and T149's repeated-de-Bruijn locality test.
C-RABEL differs only by pinning exact `k`-Abelian theorem identities and the
complete short-census equivalence class. It is retained as a negative
applicability card, not as a claimed new positive mechanism.

`NOVELTY_ROWS_T89_T150: 62/62`
`SKETCH_T151_EXCLUDED`
`SKETCH_T152_EXCLUDED`

## 5. Candidate C-RABEL: short census as de Bruijn flow

### 5.1 Exact source statement and pointwise scope

For fixed order `r`, S1 Definition 2.1 identifies equality of all contiguous
factor counts through length `r` with `r`-Abelian equivalence. S1 Lemma 2.12
says that after fixing the length-`r` count vector and the two length-`r-1`
endpoints, compatible words are exactly Euler paths through its weighted de
Bruijn graph. S2 Proposition 3.3 says the same equivalence class is generated
by finitely many `r`-switchings. S2 Corollary 4.3 identifies all class members
with Euler paths, Proposition 4.7 gives the exact class size, and Proposition
5.3 characterizes singleton classes by global uniqueness of every return
between occurring length-`r-1` factors.

These are deterministic pointwise theorems. They preserve overlap,
multiplicity, and endpoints. They do not say that a short census, even a
uniform one, bounds one specified length-`m` atom among the `M` starts.

### 5.2 Proposed noncircular certificate and failure

The strongest source-native certificate not mentioning a length-`m` atom is:

```text
RABEL-CERT(r): the complete length-r count vector and endpoints define a
connected balanced weighted de Bruijn graph, together with its exact Euler-path
class cardinality from S2 Proposition 4.7.                       (5.1)
```

This uses no maximum atom, full-block min-entropy, T7, or T107. It is therefore
formally noncircular as an input. It fails as a sufficient certificate: flow
balance guarantees realizability and the class formula counts rearrangements,
but neither controls how often one length-`m` block occurs in a particular
Euler path. Adding S2 Proposition 5.3 return uniqueness would reconstruct a
particular word, but still would not imply anti-concentration; the constant word
is a singleton and has maximum atom `M`. Thus reconstruction is not occupancy.

The source's Theorem 2.14 cannot repair this. It is a fixed-`r` asymptotic for
the number of census classes among all words, with constants depending on `r`.
It supplies neither uniformity for `r=r(m)` nor a pointwise fiber estimate.

### 5.3 Required constant substitution

No sourced implication furnishes `(OCC-153)`. If one appends the extra premise

```text
RABEL-ATOM(K,A,M,m):
max_w c_m(w) <= M/(K*A*m)+B_R(M,m),
B_R(M,m) <= M/(K*A*m),                                  (5.2)
```

then equations (2.2) and `(5.2)` give, term by term,

```text
E_m <= M*max_w c_m(w)
    <= M*(M/(K*A*m)+B_R(M,m))
    <= 2*M^2/(K*A*m)
    <= M^2/(A*m).
```

But `(5.2)` is exactly the forbidden maximum-atom premise under a new name.
It is shown only to expose the missing constant, and is rejected as circular.

## 6. All five kill tests

### K1. Repeated-de-Bruijn locality: FAIL

Fix `r>=1`, let `P=10^r`, choose a cyclic decimal de Bruijn word `B_r` of
order `r`, and repeat it to a finite word of length exactly `M+m-1`, where
`M=J*P`. For every census below, including every short depth `ell<=r` and the
length-`m` counts `c_m`, use exactly the same first-`M` start window
`{0,...,M-1}`. In particular, the short census does not use all
`M+m-ell` starts available in the look-ahead word. Over those first `M` starts,
every length-`ell` word occurs exactly `M/10^ell` times, so all contiguous
statistics through order `r` are perfectly uniform and the cyclic endpoint
flows balance.

For every `m>=r`, the first `r` digits identify the phase, so exactly `P`
length-`m` blocks occur, each `J=M/P` times. Hence

```text
max_w c_m(w)=M/10^r,      E_m=M^2/10^r.                 (6.1)
```

For any proposed universal constant in `r(m)=O(log m)` allowing
`10^r< K*A*m/2`, equation (6.1) contradicts `(OCC-153)` plus `(ERR-153)`, whose
right side is at most `2M/(K*A*m)`. This is an exact family calculation. The
finite replay is only an `experiment` corroborating it.

### K2. Scale: FAIL

S1 Theorem 2.14 fixes `r` before word length tends to infinity and hides
`r`-dependent constants while the exponent itself is `10^r-10^(r-1)`. S2's
exact formulas are finite but do not upper-bound a long atom. S3 is genuinely
logarithmic, but its threshold is in source length and is metric under iid
binary sampling. S4/S5 are fixed-system limiting theorems. S6's completion at
logarithmic orbit length is quantitatively larger than the trivial prefix
bound, as already recorded by T136. No retained theorem is uniform at the
required deterministic triangular scale.

### K3. Scope: FAIL

C-RABEL is pointwise but concludes only equivalence-class structure. S3 is
positive only with probability tending to one over iid sources. S4 and S5
concern limit or Gibbs measures. S6 concerns complete finite-field orbits and
completed prefixes. None concludes a pointwise base-10 maximum occupancy for
an arbitrary word, much less the prescribed decimal orbit of pi.

### K4. Circularity: FAIL

The only direct completion is `(5.2)`, the maximum-atom estimate itself.
Repeat-free reconstruction in S3 assumes the whole `k`-mer no-repeat event, a
full-block min-entropy/typicality mechanism matching excluded T142 C-LCS and
T138 C-MINENT. S2 singleton return uniqueness gives reconstruction but not
anti-concentration, as the constant singleton shows. T7 and T107 are not used.

### K5. Source/fingerprint novelty: FAIL for positive retention

S3 is the excluded C-LCS mechanism; S4 and S6 are exact T136/T146 duplicates;
S5 is an exact T104/T150 duplicate. C-RABEL has new exact source identities but
its de Bruijn flow/Euler-tour mechanism is nearest T128/T131/T144 and its
repeated-de-Bruijn failure is already the T149 boundary. It remains useful as
a source-pinned negative map, but it is not a novel positive mechanism.

```text
KILL_REPEATED_DEBRUIJN: fail
KILL_SCALE: fail
KILL_SCOPE: fail
KILL_CIRCULARITY: fail
KILL_SOURCE_FINGERPRINT_NOVELTY: fail-positive / retain-negative-map
```

## 7. Screened cards and exact rejection substitutions

### S3 / C-LCS metric reconstruction

S3 Theorem 1 assumes positive `alpha` and gives its displayed reconstruction
region for `n^alpha` independent sources; it does not include the formal
single-source endpoint `alpha=0`. Its Lemma 1 likewise gives a metric
repeat-free region by a union bound using probability `2^-k`, not a
deterministic inference from an observed short census. To force `(OCC-153)` one
would need a pointwise exceptional-set exclusion for the given word; that is
the unproved membership burden. The theorem is rejected mechanically as the
T142 C-LCS and T138 C-MINENT fingerprint, not retained.

### S4 fixed-point regular sequences

The theorem requires a finite `10`-kernel representation and a spectral gap for
the actual indicator sequence. No such representation is supplied for growing
decimal block indicators. It has the same source SHA and theorem tuple as T136
NEG-M and rejected T146. It is rejected before a candidate card is created.

### S5 fractal Fourier decay

The decimal map has derivative cocycle `log 10`, which is locally constant and
therefore fails total nonlinearity exactly. Even for a qualifying Gibbs measure,
Fourier decay is an ambient-measure statement, not a named-path occupancy cap.
The exact source SHA and Theorem 1.1 fingerprint duplicate T104 F3 and T150's
screen. It is rejected before a candidate card is created.

### S6 structured exponential sums

In dimension one T136 records the completed short-orbit estimate at
`tau~log q` as `q^(1/8)*(log q)^(7/4)`, whose ratio to the trivial length
`log q` is `q^(1/8)*(log q)^(3/4)->infinity`. Even useful character cancellation
would require an additional Fourier-to-pointwise block-atom inversion with all
`10^m` characters, which is neither sourced nor within logarithmic locality.
The exact source SHA and theorem tuple duplicate T136 NEG-X and rejected T146.

## 8. Separate additional fixed-pi certificate

**PI-LOCALITY-TRANSFER-T153 (`unproved-transfer`; NOT ASSERTED).** For every
integer `A>=1`, for every sufficiently large block depth `m`, there exist
`M>=1`, `K>=2`, and `1<=r(m)<=C log m` such that the actual nonwrapping decimal
prefix of pi satisfies a source-native pointwise logarithmic-locality
certificate which, without using maximum length-`m` atom, full-block
min-entropy, T7, or T107, implies

```text
max_w c_m^pi(w) <= M/(K*A*m)+B_pi(M,m),
B_pi(M,m) <= M/(K*A*m).                                 (PI-LOC-153)
```

Then the purely symbolic calculation in Section 2 would give
`E_m^pi<=M^2/(A*m)`. No inspected source supplies this certificate, verifies it
for pi, or transfers symbolic equality to all metric near returns. In fact,
`(PI-LOC-153)` deliberately states the missing conclusion and is not evidence.
There is no fixed-pi, A1, C1, or C2 claim.

## 9. Scoped endpoint

`SCOPED_VERDICT (1/1): close`.

Close this six-source route: `r`-Abelian/de Bruijn-flow data, metric substring
reconstruction, regular-sequence limits, ambient fractal Fourier decay, and
completed finite-field sums supply no noncircular pointwise occupancy theorem.
Repeated de Bruijn words additionally refute the universal implication in the
subcritical range `10^r<K*A*m/2` (in particular `10^r=o(m)`). This verdict does
not prove that every possible `r(m)=O(log m)` mechanism fails. It leaves open a
future deterministic theorem with an explicit stronger threshold such as
`r>=log_10 m+Omega(log log m)` plus genuinely new nonlocal/arithmetic structure,
and it does not address canonical A1.

`SUCCESSOR (0/1): none`.

## 10. Replay

From a directory containing only the delivered artifacts, run:

```bash
python3 verify_t153.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier checks the canonical hash, six source hashes and PDF anchors,
three-domain/twelve-source/four-candidate caps, unique source/theorem/mechanism
keys, all 62 novelty rows, refreshed sketch-level T151/T152 exclusions, and the
byte-pinned T104/T138 and T136/T146 fixture reports plus the vendored T138/T146
source pins. It mechanically compares their normalized source SHA, theorem
identity, and mechanism ID after checking every encoded supporting locator;
S2's T153 key includes every used result, including Corollary 4.3. It also
checks the exact occupancy-to-collision substitution, the shared first-`M`
repeated-de-Bruijn window, five kill tests, labels, one verdict, and zero
successors. These checks are an `experiment`, not proof of the literature
deductions or universal statements.
