# T160: pair-multiplicity-sensitive deterministic recurrence scout

Audit date: 2026-08-12 UTC. This is one bounded G28 related-model scout.

Source statements marked `literature-checked` were checked against the six
pinned primary PDFs and exact locators in `SOURCE_PINS.md`. Definitions and
deductions marked `proof sketch` are not machine-checked. Separator replay is
an `experiment`, hence finite evidence only. Conclusions about Champernowne are
`related-model conclusion`. The final fixed-pi bridge is separately labeled
`unproved pi transfer`.

```text
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 8
SEARCHED_DOMAIN_COUNT: 3
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
EXCLUSION_RANGE: T89-T157
EXCLUSION_ROW_COUNT: 69
RESERVATION_COUNT: 2
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
It asks whether every integer `A>=1` admits `n0` such that every `n>=n0`
has some `N=N(A,n)` satisfying

```text
A*n*Q_pi(n,N) <= N^2,
Q_pi(n,N)=#{(i,j) in {0,...,N-1}^2:
             ||(10^i-10^j)pi||_(R/Z)<10^(-n)}.
```

Pairs are ordered, the diagonal is included, and the inequality defining
`Q_pi` is strict. T160 does not alter or answer this question. Its audited
symbolic event is the A10/A13/A14 sibling of exact equality of overlapping
blocks in an arbitrary finite word, plus one named base-2 model.

Ambiguous quantifiers fixed before the scout:

1. A source theorem at one depth does not provide all logarithmic depths.
2. An almost-everywhere theorem does not locate a named point.
3. A count of repeat structures is not a count of ordered occurrences.
4. A lower bound for collisions is not an upper collision certificate.
5. A Fourier theorem applies only after its function and norm hypotheses are
   proved without assuming the desired collision decay.
6. T155's pair-weighting observation is an unverified lead only. No T155
   proof-sketch deduction is used as a premise.
7. Missing T156 content is not novelty evidence. In the refreshed snapshot,
   T158 is readable and literature-pinned, while T159 is a readable unverified
   note; neither artifact is imported as a mathematical premise.

## 2. Exact finite definitions (`proof sketch`)

Let `D={0,...,9}`. Fix integers `M,m>=1`, let `L=M+m-1`, and let
`x=(x_0,...,x_(L-1)) in D^L`. There is no wrapping or padding.

**Recurrence block.** For `0<=i<M`,

```text
B_x(i,m)=(x_i,...,x_(i+m-1)).                              (2.1)
```

**Endpoint.** The inclusive endpoint is `e(i,m)=i+m-1`; legality means
`0<=i<M` and `e(i,m)<=L-1`. The endpoint convention is part of every count.

**Overlap.** For starts `i,j`,

```text
ov(i,j;m)=max(0,m-|i-j|).                                  (2.2)
```

Thus `ov>0` records shared digit coordinates, but equality is always tested on
the full ordered blocks.

**First recurrence.** Put

```text
R_x(i,m)=min{d>=1:i+d<M and B_x(i,m)=B_x(i+d,m)},           (2.3)
```

with value `infinity` if the set is empty. A first-recurrence statistic records
only the next endpoint. It does not record all later matching starts.

**Multiplicity.** For `w in D^m`,

```text
c_x(w;m,M)=#{i in {0,...,M-1}:B_x(i,m)=w}.                 (2.4)
```

**Ordered-pair collision energy.** Define

```text
P_x(w;m,M)={(i,j):0<=i,j<M and B_x(i,m)=B_x(j,m)=w},
E_x(m,M)=sum_w |P_x(w;m,M)|=sum_w c_x(w;m,M)^2.            (2.5)
```

This includes exactly `M` diagonal pairs. The off-diagonal count is
`E_x-M=sum_w c_w(c_w-1)`. This quadratic multiplicity is the audited target.

**Logarithmic-depth range.** For `0<kappa<=1` and prefix size `N`,

```text
D_kappa(N)={m in Z:1<=m<=floor(kappa*log_10 N)}.            (2.6)
```

The T7-shaped symbolic screen at one depth is

```text
E_x(m,M) <= M^2/(A*m).                                     (2.7)
```

A useful multidepth certificate must hold on one increasing prefix family and
enough depths in (2.6), not on unrelated prefixes selected after each test.

## 3. Complete exclusion ledger and mandatory comparisons

`EXCLUSION_LEDGER.csv` has one row for every T89-T157, exactly 69 consecutive
identifiers, followed by explicit T158/T159 reservations. It distinguishes
machine-checked interfaces, literature-pinned statements, unverified notes,
experiments, rejected metadata, and unavailable content.

The closest mandatory boundaries are:

| Comparator | Available status | T160 boundary |
|---|---|---|
| T95/T100 | T95 note is unverified; T100 interface is machine-checked | C-CLOSED also charges positions, but only to next-occurrence structures; it does not duplicate the short-to-remote equality lemma and imports no T95 claim. |
| T119 | rejected LC/PS/EXP comparator | Pair multiplicity is a fiber cardinality, not predictive/Hankel/Prony rank. |
| T121 | source-pinned statements plus proof sketches | C-SHORT does not import global Walsh energy; requiring all block-indicator Fourier norms would merely assume its analytic input. |
| T131 | source-pinned statements plus proof sketches | Euler/de-Bruijn ordering appears only in a separator; no flow construction or nesting result is claimed. |
| T149 | source-pinned statements plus proof sketches | Maximum occupancy implies an energy bound, but is expressly rejected as a certificate here. |
| T152 | unverified note | Fractional-cover census is neither a premise nor an established comparator conclusion. |
| T153 | literature-pinned statements; deductions are proof sketches | Distinct local factors/k-Abelian flow can lose occurrence multiplicity. |
| T154 | unverified note | Reuse-capacity entropy LP is not a premise. |
| T155 | literature-pinned statements; deductions are proof sketches | Run count and Palm-Stein are excluded. Its pair-weighting suggestion is only the agenda's unverified lead. |
| T156 | result metadata only; package absent | All reported entropy/template content and source tuples are reserved. No nonduplication claim is made. |
| T157 | literature-pinned statements; deductions are proof sketches | GAP/LCD/Halasz structure maps collisions to zero vectors and loses zero-fiber multiplicity. |
| T158 | readable literature-pinned artifact; source statements literature-checked, deductions proof sketches, replay experiment | The T158 report argues (proof sketch) against pseudo-gap-plus-short-census control because deterministic Euler ordering is missing. T160 imports no deduction and continues to reserve graph conductance as a distinct mechanism. |
| T159 | readable accepted note; source statement literature-checked, all new deductions unverified proof sketches, replay finite test | The T159 note argues (unverified) that a direct Chen--Xia substitution is noninformative and retains only an iid Palm--Stein benchmark. T160 imports no such claim and continues to reserve stochastic collision-location approximation as a distinct mechanism. |

This scout rejects, by design, any output controlling only run count, distinct
repeats, total exponent, maximum occupancy, graph conductance, stochastic
collision locations, or a renamed premise asserting (2.7) or T107's row bounds.

The refreshed duplication boundary is exact. T158's retained fingerprint is an
empirical de-Bruijn transition kernel with pseudo-spectral gap and census error;
none of C-CLOSED, C-CHAMP, or C-SHORT asserts that mechanism. T159 intentionally
specializes T155's marked Palm--Stein lead to overlapping iid blocks; no T159
deduction is used here. C-CHAMP counts deterministic ordered pairs at a named
point, whereas T159 studies a random marked point process. C-SHORT studies
cyclic Fourier completion and does not use Chen--Xia. Thus T158/T159 remain
reserved comparators, not unavailable items and not evidence of novelty.

## 4. Candidate C-CLOSED: positional closed-repeat charging

**Literature-checked source.** S2 Main definition ties a nonempty repeat at
`[i,j]` to its closest later occurrence `[i',j']` and requires failed right/left
extension. S2 Theorem 1 proves at most `2L log_2 L` right closed repeats and the
same order for left closed repeats. Lemmas 1-2 order the next occurrences from
one start.

**Candidate ranges.** Recurrence is (2.3); overlap is unrestricted; endpoints
are nonwrapping; pairs in (2.5) are ordered; source multiplicity is one
next-occurrence structure per charged position; the theorem holds separately
for each finite `L`, with no uniform assertion over `D_kappa(N)`.

**Quantitative substitution (`proof sketch`).** Let

```text
U_m=sum_w max(c_w-1,0),                                    (4.1)
```

the number of non-rightmost occurrences among occupied block fibers. Extending
each such occurrence to one right closed repeat gives at best

```text
U_m <= 2*L*log_2 L.                                        (4.2)
```

The required off-diagonal energy is instead

```text
E_x-M=sum_w c_w(c_w-1)
     <= c_max*U_m
     <= 2*c_max*L*log_2 L,                                 (4.3)
```

where `c_max=max_w c_w`. The first failed inequality is precisely the missing
uniform conversion `c(c-1)<=C(c-1)`: no constant `C` works for unbounded `c`.
Using `c_max<=M` makes (4.3) order `M L log L`, not `M^2/(A m)`. Supplying
the exact sufficient scale (when its numerator is nonnegative)

```text
c_max <= (M^2/(A*m)-M)/(2*L*log_2 L)                      (4.4)
```

would be a prohibited maximum-occupancy premise already isolated at T149. For
`M` large compared with `A*m` and `L` comparable to `M`, (4.4) is roughly
`M/(A*m*log M)`, including the
logarithmic loss that a bare `M/(A*m)` cap would not pay. Hence S2 loses
quadratic multiplicity.

Disposition inside the audit: screened after an explicit failed inequality.

## 5. Candidate C-CHAMP: direct ordered pattern multiplicity

**Literature-checked source.** S3 Theorem 1 states that the named base-2
Champernowne orbit `({2^n alpha})` is not Poissonian. Its proof fixes

```text
d=2^e,  w=d+e,  N=2^(d+e),  s=1,                           (5.1)
```

counts ordered pairs of starts whose first `w` bits match, and obtains from one
central-binomial term

```text
P_match(d,e) >> sqrt(d)*2^(d+e)=sqrt(d)*N.                 (5.2)
```

After division by `N`, this tends to infinity. Remark 2 extends the negative
Poissonian conclusion to Champernowne constants in every base.

**Candidate ranges.** Recurrence is exact prefix matching in a named expanding
orbit; overlap crosses concatenated integer-word endpoints and is handled by
the proof's offset `z`; endpoints are the beginning of the block of words of
length `d+1`; pairs are explicitly ordered; multiplicity is squared through
the number of matching occurrences of each pattern; depth is the single sparse
choice `w=d+e=log_2 N`, with `d=2^e`, not a family of all depths in (2.6).

**Quantitative substitution (`proof sketch`).** Exact `w`-bit matching is a
subset of circle pairs at radius `1/N=2^(-w)`, so (5.2) is a deterministic
lower bound for a base-2 related-model collision count. The desired T7-shaped
direction would be

```text
E(w,N) <= N^2/(A*w).                                       (5.3)
```

But the ratio of the sourced lower bound to the right side of (5.3) is only

```text
(sqrt(d)*N)/(N^2/(A*w)) = A*w*sqrt(d)/N -> 0.              (5.4)
```

Thus (5.2) neither proves nor contradicts (5.3). The first failed inequality is
directional: a sparse lower bound cannot become the required upper bound.

**Related-model conclusion.** C-CHAMP is the only retained tuple that literally
preserves deterministic ordered-pair multiplicity and endpoint/carry overlap.
It is useful as a model of what a pair-sensitive arithmetic count looks like,
but it diagnoses excess recurrence for Champernowne and provides no fixed-pi
decay, no decimal result used here, and no logarithmic-depth uniformity.

## 6. Candidate C-SHORT: short trace-function sums

**Literature-checked source.** S6 Theorem 1.1 assumes a periodic function
`phi` modulo `q` with

```text
c=max(||phi||_infinity,||Fourier(phi)||_infinity)           (6.1)
```

and gives for intervals above the square-root range an explicit completion
bound of shape `c*sqrt(q)*log(4e^8 |I|/sqrt(q))`. Theorem 1.2 transfers a
partial-sum saving to the discrete Fourier transform. S5 Theorems 1.1 and 2.1
are the screened predecessor; its equation (2.3) explicitly contains
`max_a |C(phi,a)|^(1/3)`.

**Candidate ranges.** Recurrence and block overlap are absent from the source;
endpoints form an interval in a cyclic group; source sums are ordered by one
index, not block pairs; multiplicity appears only if encoded into `phi` or its
correlations; modulus and interval ranges are theorem-specific and supply no
uniform family `D_kappa(N)`.

**Quantitative substitution (`proof sketch`).** On a cyclicized prefix of size
`M`, fix an occupied block type `w` (`c_w>0`) and try the literal block indicator

```text
phi_w(i)=1[B_x(i,m)=w],  S(phi_w;all starts)=c_w.           (6.2)
```

With S6's normalized Fourier convention,

```text
Fourier(phi_w)(0)=c_w/sqrt(M),
||Fourier(phi_w)||_infinity=c_w/sqrt(M),
c=max(1,c_w/sqrt(M)).                                      (6.3)
```

The equality in (6.3) is exact: the triangle inequality bounds every Fourier
coefficient by `c_w/sqrt(M)`, and the zero coefficient attains it. Substitution
in the completion-scale bound splits into two tautological cases:

```text
c_w<=sqrt(M):  c_w <= sqrt(M)*log(...),
c_w> sqrt(M):  c_w <= c_w*log(...).                         (6.4)
```

The first case merely restates the assumed maximum-occupancy branch; the
second gives no saving. Centering removes the zero coefficient but then proving uniform
nonzero Fourier bounds for every `w` and enough `m` is the missing global
block-Fourier input, nearest T121/T107. In S5 equation (2.3), the correlation

```text
C(phi_w,a)=#{i:B_x(i,m)=B_x(i+a,m)=w}                      (6.5)
```

is already the lagged pair count to be bounded. The first failed inequality is
therefore the source hypothesis, not an exponent loss: applying either theorem
requires occupancy or correlation/Fourier decay that renames the target.
Unoccupied fibers have `phi_w=0`, `c=0`, and contribute zero to (2.5), so they
are omitted rather than forced into (6.3).

Disposition inside the audit: screened after a circular hypothesis failure.

## 7. Five separator tests (`proof sketch`; replay is `experiment`)

These tests concern arbitrary finite words or exact histograms, not pi.

1. **Exact constant test.** For `x=0^(M+m-1)`, one fiber has `c=M`, hence
   `E=M^2`. C-CLOSED has only a linearized next-occurrence charge; C-CHAMP is
   a different named word; C-SHORT has Fourier zero mode `M/sqrt(M)`.
2. **Primitive-periodic test.** Let a primitive period-`p` word repeat, take
   `p|M`, and `m>=p`. There are `p` block types with multiplicity `M/p`, so
   `E=M^2/p`. Run or distinct-repeat counts remain `O(p)` while pair energy is
   quadratic in `M/p`.
3. **Doubled-de-Bruijn test.** Take two copies of a base-`b` de Bruijn cycle
   of order `r`, then append the first `r-1` symbols of the cycle. Use all
   `M=2*b^r` nonwrapping starts at depth `r`. Every one
   of the `b^r` words occurs twice, so `E=4*b^r=2M`. The structure has perfect
   distinct-word coverage but nontrivial pair multiplicity; Euler ordering does
   not itself estimate higher repetitions.
4. **Shared-prefix test.** If the first `R+m-1` symbols are zero, the first `R`
   starts have one common block and contribute at least `R^2` to `E`, regardless
   of the remainder. Local structure counts can remain linear in `R`.
5. **Bounded multi-core test.** For fixed `K<=10`, place `K` long constant
   cores using distinct digits and separators. If each core supplies `R`
   internal legal starts at depth `m`, then `M_core=K*R` and the cores alone
   contribute `K*R^2=M_core^2/K`. A bounded number of cores, components, or
   repeat descriptors therefore cannot replace their squared multiplicities.

All five reject C-CLOSED's linearization. C-CHAMP passes only the conceptual
pair-weight discriminator, not the upper-bound direction or depth range.
C-SHORT fails before the separators because its required norm/correlation
hypothesis already contains their energy.

## 8. Unproved pi transfer (`conjecture`; NOT ASSERTED)

`PI-PAIR-CERT` is the separate hypothesis that would be needed to turn the
surviving model lesson into progress. For one increasing prefix family
`N_1<N_2<...`, a pi-specific arithmetic construction must, without assuming a
collision, occupancy, conductance, stochastic-location, or Fourier-decay bound:

1. assign every ordered equal decimal-block pair `(i,j)` at each admissible
   `(N_k,m)` to an explicit arithmetic witness `lambda(i,j,m)` derived from a
   pi-specific identity;
2. prove directly from that identity a fiber-capacity bound and a witness-count
   bound whose product is at most `N_k^2/(A*m)`;
3. do so uniformly for depth sets inside `D_kappa(N_k)` whose tail coverage is
   sufficient for every large `m` required by T7, or instead prove both named
   T107 triangular row budgets on a positive-density depth family; and
4. separately pay the already recorded symbolic-to-metric transfer.

This formulation asks for arithmetic witness capacities rather than assuming
collision decay. None of S1-S6 constructs such witnesses for pi. Assuming the
product bound would supply the missing T7 input; it is not evidence that pi has
it. No fixed-pi, A1, C1, or C2 claim is made.

## 9. Endpoint and replay

`SCOPED_VERDICT (1/1): HOLD AS MODEL.`

Hold only C-CHAMP's direct deterministic ordered-pattern multiplicity as a
related-model diagnostic. Close C-CLOSED as losing quadratic multiplicity and
C-SHORT as requiring the target correlation/Fourier input. The hold does not
assert a useful upper bound, does not promote the T155 lead, and does not close
G28 or the canonical problem.

`SUCCESSOR (0/1): NONE.`

From a directory containing only delivered artifacts:

```bash
python3 verify_t160.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The replay checks hashes, source anchors and S1/S3 physical-page anchors, exact
caps, the consecutive ledger, reservations, required definition/substitution
section markers, mandatory-comparison markers, five finite separator identities,
the label firewall, exactly one scoped verdict, and zero successors. It does not
verify the prose deductions or displayed substitutions and is not proof of a
universal mathematical statement.
