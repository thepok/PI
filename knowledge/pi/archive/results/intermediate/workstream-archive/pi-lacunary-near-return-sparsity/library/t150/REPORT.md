# T150: reuse-adjusted pressure and large-deviation audit

Audit date: 2026-08-12 UTC.

The six source statements below are `literature-checked` against the pinned
PDFs and exact locators in `SOURCE_PINS.md`. All substitutions, comparisons,
and finite-word deductions are `proof sketch`, except that finite replay output
is only an `experiment`. The surviving census is a **related-model** result for
all finite decimal words, conditional on the cited Gibbs concentration theorem;
it is not a statement about the digits of pi.

```text
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 8
DOMAIN_COUNT: 4
DOMAIN_MINIMUM: 3
THEOREM_CANDIDATE_COUNT: 3
THEOREM_CANDIDATE_CAP: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Provenance, normalized statement, and ambiguities

The canonical question has no external Erdos Problems URL. Its immutable
provenance says that this program formulated it on 2026-07-22. The byte-exact
`canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether every `A>=1` and every sufficiently large depth `n` admit some
`N` with `A*n*Q_pi(n,N)<=N^2`, where `Q_pi` counts ordered, diagonal-inclusive
metric circle near returns of the fixed orbit `{10^j*pi}`. T150 neither alters
nor answers that question. It audits an equal-block finite-word sibling under
recorded ambiguities A10 and A14. No finite-word or Gibbs-measure assertion is
silently transferred to pi.

Quantifiers fixed before the audit:

1. `N` tends to infinity and the maximum block depth grows as `O(log N)`.
2. Every depth uses the same `N` starts and the same look-ahead coordinates.
3. Equal-block pairs are ordered and include all `N` diagonal pairs.
4. A source theorem with a fixed observable, fixed dimension, or ambient
   almost-everywhere conclusion is not treated as uniform in this triangular
   regime.
5. A failed hypothesis means theorem inapplicability, not falsification of a
   possible census.
6. T144 and T147 are unverified `proof sketch` notes. Their claims are used as
   adversarial specifications only; no conclusion here treats them as proved.

## 2. Exact joint event

Let `D={0,...,9}`. For an integer `N` with

```text
k=floor((1/4)*log_10 N)>=2,   a=ceil(k/2),
S_k={a,...,k},                L=N+k-1,
```

take a word `x=(x_0,...,x_(L-1)) in D^L`. For `m in S_k`, define

```text
W_i^m(x)=(x_i,...,x_(i+m-1)),                 0<=i<N,
c_x(w;m)=#{0<=i<N:W_i^m(x)=w},                w in D^m,
E_x(m)=sum_(w in D^m)c_x(w;m)^2,
C_x(m)=E_x(m)/N^2.
```

The last endpoint is `N+k-2=L-1`; there is no wrapping or padding. Expanding
the squares gives exactly

```text
E_x(m)=#{(i,j) in {0,...,N-1}^2:W_i^m(x)=W_j^m(x)}.       (2.1)
```

Thus (2.1) is ordered and has exactly `N` diagonal pairs. The audited event is

```text
J_(N,k)={x in D^L:E_x(m)>=N^2/m for every m in S_k}.      (2.2)
```

Requiring every depth in the upper half is one precise simultaneous
positive-density census. It is the event used by the T147 note, not T144's
different one-depth endpoint convention and not T140's threshold/event.

## 3. Six-source, four-domain ledger

The bounded search stopped after six primary papers. Exact URLs, DOI data,
hashes, hypotheses, and page locators are in `SOURCE_PINS.md`.

| ID | domain | inspected primary result | role |
|---|---|---|---|
| S1 | thermodynamic formalism | Buzzi--Kloeckner--Leplaideur, Theorem A | Candidate P: nonlinear pressure |
| S2 | symbolic entropy/collision | Chazottes--Gabrielli, Theorem 3.1 | Candidate H: growing-block entropy LDP |
| S3 | structured large deviations | Chazottes--Gouezel, Theorem 2.1 with (1.1) | Candidate C: separately-Lipschitz Gibbs concentration |
| S4 | thermodynamic/structured LD | Varandas--Zhao, Theorem B | screen: non-additive potential scope |
| S5 | nonlinear large deviations | Eichelsbacher--Schmock, Theorems 1.7 and 1.10 | screen: fixed-order iid U/V statistics |
| S6 | arithmetic/fractal Fourier | Sahlsten--Stevens, Theorems 1.1, 2.1 and Lemma 5.6 | screen: nonlinear Gibbs nonconcentration |

No paper is counted twice and no secondary survey is counted. Exactly S1--S3
are theorem candidates. S4--S6 test whether a hidden subadditive, nonlinear
tuple, or Fourier/nonconcentration theorem repairs their failed hypotheses.

## 4. Candidate P: nonlinear pressure

### 4.1 Exact source hypotheses

S1 Theorem A starts with a continuous map `T:X->X` of a compact space and one
fixed continuous energy `E:P(X)->R`. It assumes abundance of ergodic measures.
It identifies nonlinear topological pressure, defined from weights
`exp(n*E(Delta_n^x))` on separated sets, with

```text
sup_{mu invariant} (h(T,mu)+E(mu)).                       (4.1)
```

For an expansive homeomorphism it also gives the fixed-expansivity limit.

### 4.2 Growing-depth substitution

On the full decimal shift, for each fixed `m` the continuous quadratic energy

```text
Q_m(mu)=sum_(w in D^m) mu([w])^2                         (4.2)
```

is the invariant-measure analogue of `C_x(m)`. For any fixed finite set of
depths, a continuous penalty of the vector `(Q_m)` fits S1. Overlap is not the
problem: the empirical measure uses all orbit starts.

For (2.2), however, both the energy and its cylinder range change with `N`:
there are `Theta(k)` constraints, maximum range `k=Theta(log N)`, and up to
`10^k=N^(1/4+o(1))` cylinder coordinates. S1 fixes `E` before `n->infinity`
and gives no error uniform in this range or dimension. It also computes a soft
weighted partition-function limit, not a finite hard-constraint cardinality.
Neither S4's asymptotically additive approximation (uniform `o(n)` error by
one fixed continuous potential) nor its subadditive weak-Bowen/equicontinuity
hypotheses are verified for the minimum of the growing quadratic constraints.

### 4.3 Cheap rejection tests

- Constant words: the invariant Dirac measures have `Q_m=1` at every depth;
  (4.1) permits them but gives no finite joint count.
- Periodic words: a period-`p` orbit has at most `p` blocks and
  `Q_m>=1/p`; pressure again records an invariant measure, not reuse cost.
- Repeated de Bruijn words: their block law is uniform through the design
  order, so they are correctly low-collision, but this does not supply a
  uniform hard-event estimate.
- T147 family: for each fixed `N`, its shared prefix can be inserted in an
  empirical energy, but S1 has no triangular theorem charging that prefix once.

**Candidate P result:** inapplicable at fixed-energy/uniform-finite-error scope.

## 5. Candidate H: growing-block empirical entropy LDP

### 5.1 Exact source hypotheses and legal scale

S2 Theorem 3.1 assumes a finite alphabet, a sample distributed according to a
`g`-measure, `k(n)->infinity`, and

```text
k(n) <= ((1-epsilon)/log |D|)*log n                       (5.1)
```

eventually, for some fixed `0<epsilon<1`. It proves speed-`n` scalar LDPs for
conditional empirical Shannon entropy and for `H_hat_k/k`, with rate function
`inf h(nu|rho)` subject to a scalar entropy value. The empirical process uses
all `n` cyclic overlapping starts.

Our `k=(1/4)log_10 N=(1/(4 log 10))*log N` satisfies (5.1), for example with
`epsilon=3/4`. Hence growing depth and overlap themselves pass this candidate.
Replacing cyclic closure by the `k-1` supplied look-ahead coordinates changes
at most `k-1` windows and has vanishing normalized endpoint cost.

### 5.2 Quadratic and reuse substitution

The load-bearing mismatch is the observable. S2 controls one scalar Shannon
entropy, not `sum p_w^2`, a threshold `1/m`, or a joint process over all
`m in S_k`. S5 confirms that nonlinear empirical-measure LDPs can cover fixed
order and bounded kernels for iid tuples, but its order `m` is fixed and its
tuples are distinct iid observations. Contiguous overlapping `k(N)`-blocks are
neither those tuples nor a uniform fixed-order kernel.

For the T147 shared-prefix scale `alpha=R/N=Theta(k^(-1/2))`, one block has
mass at least `alpha`, so collision is at least `alpha^2=Theta(1/k)`, exactly
the threshold scale. That collision certificate alone gives no fixed normalized
Shannon deficit: the abstract distribution assigning mass `alpha` to one of
`10^m` atoms and distributing `1-alpha` uniformly over the rest has collision
at least `alpha^2`, while its Shannon deficit divided by `m` is `O(alpha)` and
tends to zero. This distribution-level separator is not asserted to be the
exact block law of every T147 word; rather, S2 supplies no theorem converting
the T147 collision certificate into the fixed scalar Shannon deviation its LDP
would require.

### 5.3 Cheap rejection tests

- Constant and fixed-period words have normalized Shannon entropy tending to
  zero and are detected, but these are much cheaper than the target family.
- A repeated order-`k` de Bruijn word has uniform `m`-block laws for `m<=k`
  and is correctly outside (2.2).
- The T147 family passes the collision event, but neither its collision
  certificate nor S2 forces a fixed normalized-Shannon deviation; the abstract
  distribution above shows why such an implication needs additional structure.

**Candidate H result:** inapplicable because normalized Shannon entropy is too
coarse for a shrinking `1/k` collision spike and supplies no joint-depth rate.

## 6. Candidate C: reuse-adjusted Gibbs concentration

### 6.1 Exact source theorem

S3 defines separate Lipschitz constants `Lip_i(K)` and an exponential
concentration inequality, uniform in the number `L` of variables:

```text
P(|K-EK|>t) <= 2 exp(-t^2/(4*C*sum_i Lip_i(K)^2)).         (6.1)
```

Theorem 2.1 states that a topologically mixing one-sided subshift of finite type
with an invariant Gibbs measure satisfies this inequality for some system
constant `C>0`. The full decimal shift with uniform Bernoulli measure is such a
system. Under that measure every word of `D^L` has probability exactly `10^-L`.

### 6.2 Quadratic observable and exact reuse loss

Define the one-statistic encoding of all hard constraints

```text
K(x)=min_(m in S_k) m*C_x(m).                             (6.2)
```

Then `x in J_(N,k)` iff `K(x)>=1`. Changing one digit changes at most `m`
of the `N` sampled `m`-blocks. If `p,q` are the old and new empirical block
laws, `||p-q||_1<=2m/N`, and therefore

```text
|sum p_w^2-sum q_w^2|
 <=sum |p_w-q_w|(p_w+q_w)<=2||p-q||_1<=4m/N.
```

The minimum of functions with common oscillation bound has that same bound.
Consequently every one of the `L` digit coordinates has

```text
Lip_i(K)<=max_(m<=k) 4m^2/N=4k^2/N,
sum_(i<L)Lip_i(K)^2<=16*L*k^4/N^2.                        (6.3)
```

This is the explicit reuse loss: the same coordinate is charged once by (6.1),
but its influence includes every window and every depth through `k^2`.

For iid uniform digits, two distinct starts have equal length-`m` blocks with
probability `10^-m`, even when they overlap: the equality graph on the `m+d`
digits at lag `d` has exactly `m` independent equality constraints. Hence

```text
E[C_x(m)]=1/N+(1-1/N)*10^-m.
```

Since `K<=k*C_x(k)`, put

```text
eta_(N,k)=k*(1/N+(1-1/N)*10^-k),                          (6.4)
```

so `E[K]<=eta_(N,k)`. For `eta_(N,k)<1`, (6.1)--(6.4) give the displayed
**joint census**

```text
#J_(N,k)
 <= 2*10^L*exp(-(1-eta_(N,k))^2*N^2/(64*C*L*k^4)).        (JC-150)
```

This is an honest finite-`N` source-theorem consequence once the system
constant `C` is fixed. It is simultaneous, uses all overlapping starts, keeps
the quadratic ordered diagonal observable, and loses `k^4` for reuse. It gives
`10^(N+O(log N))*exp(-Omega(N/log^4 N))`, not an additive
`exp(-Omega(N*sqrt(log N)))` saving.

### 6.3 Counterfamily and cheap tests

1. **T147 shared zero prefix.** Along `N=10^(4k)`, let
   `R=ceil(N/sqrt(a))` and fix coordinates `0,...,R+k-2` to zero. The T147 note
   argues, without being imported as a proved premise, that this gives
   `10^(N-R)` words in (2.2). Independently, the displayed endpoint and energy
   calculation is immediate: the first `R` starts equal `0^m`, so
   `E_x(m)>=R^2>=N^2/m`. The lower-family logarithmic cost is
   `R*log 10=Theta(N/sqrt(k))`. The saving in (JC-150) is only
   `O_C(N/k^4)`. Therefore, for all sufficiently large `k` depending on `C`,
   the upper bound in (JC-150) is larger than `10^(N-R)` and does not contradict
   this family.
2. **Constant words.** All ten constant words lie in `J_(N,k)`. The right side
   of (JC-150) tends to infinity exponentially, so they are not excluded.
3. **Periodic words.** A word generated by a period `p<=a` has at most `p`
   distinct blocks, hence Cauchy gives `E_x(m)>=N^2/p>=N^2/m`; endpoint
   look-ahead uses the same periodic extension. There are at most `10^p` such
   generated words, again far below (JC-150).
4. **Repeated de Bruijn words.** If a cyclic decimal de Bruijn word of order
   `k` is repeated, `N` is a multiple of `10^k`, and the first `k-1` symbols
   are appended, every length-`k` block occurs `N/10^k` times. Thus
   `E_x(k)=N^2/10^k<N^2/k`; this family is outside `J_(N,k)`, as required.

**Candidate C result:** survives as a related-model, reuse-adjusted joint
census. It does not assert that a prescribed word avoids the counted set.

## 7. Comparison and duplication firewall

Exact comparator hashes and locators are in `PRIOR_INDEX.md`; the three reports
are archived only as comparison evidence. No sketch claim is a premise of
Sections 2 or 6.

| comparator | supplied level and fingerprint | T150 boundary |
|---|---|---|
| T140 | source theorems `literature-checked`; encodings/deductions `proof sketch` | T140 tests hypergraph containers for edge-rich transversals. T150 uses no container, fingerprint, codegree, or supersaturation claim. |
| T144 | unverified `proof sketch` | T144 selects one residue class at one depth and counts types. T150 Candidate C uses one multidepth Lipschitz statistic and does not import or sum its one-depth savings. |
| T147 | unverified `proof sketch` plus exact family specification | T150 accepts the shared-prefix reuse cost and obtains only `N/k^4`, explicitly compatible with its `N/sqrt(k)` family cost. It does not revive ADD-144. |
| T113/T116 avoidance | source-audited prose with deductions at most `proof sketch` | no point is selected by avoiding bad sets; (JC-150) counts the bad set only. |
| T120 renewal | sources `literature-checked`, deductions `proof sketch` | no regeneration, return-time tail, or countable-state path is used. |
| T121/T125 global L2 | sources `literature-checked`, deductions `proof sketch` | no Parseval expansion or arithmetic cancellation is used; the quadratic statistic is controlled by coordinate oscillation. |
| T119 rank | recovered incomplete `proof sketch` comparison memory | no Hankel, Prony, predictive, automaton, or matrix rank is inferred. |
| generic entropy/normality | prior reports only; no fixed-pi premise | Candidate H is rejected. Candidate C is a finite all-word cardinality bound via uniform word probability, not a typical-point or entropy-rate transfer. |
| active T148 | unavailable active carry-valuation lane | excluded; no content or distinction beyond its agenda label is inferred. |
| active T149 | unavailable active three-point-PSD lane | excluded; no content or distinction beyond its agenda label is inferred. |

S6's nonlinear derivative-cocycle route is also not retained: its total
nonlinearity and Gibbs regularity manufacture geometric nonconcentration for a
fixed expanding system. The decimal map has `log|T'|=log 10`, the forbidden
locally constant/cohomological case, and arbitrary finite words have no such
derivative observable. Reusing S6 would also duplicate the T104 fractal-Fourier
fingerprint already recorded.

## 8. Separate unproved pi-specific transfer toward T107

**PI-T107-TRANSFER-T150 (`conjecture`; UNPROVED PI-SPECIFIC TRANSFER PREMISE;
NOT ASSERTED).** There is one increasing sequence of pi-prefix cutoffs on which
(i) the exact look-ahead decimal words avoid the relevant high-collision joint
sets after a checked endpoint conversion, and (ii) this symbolic exclusion can
be converted, uniformly on a positive-density triangular family of levels, to
T107's two literal budgets

```text
rowBoundaryLoad(ell,P) <= P/(40*10^ell),
|rowFourierRemainder(ell,P)| <= P^2/(10*10^ell).
```

Neither (JC-150), a finite Gibbs probability/cardinality bound, nor any inspected source
places the prescribed decimal expansion of pi outside the exceptional census
or proves the T107 Fourier/boundary conversion. This additional premise carries
the named-point arithmetic burden and is logically separate from the related-
model census. No fixed-pi, A1, C1, or C2 claim follows here.

## 9. Endpoint

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t150.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The replay checks source and comparator pins, source/candidate/domain caps,
PDF theorem anchors, exact finite collision expectations and oscillation bounds,
constant/periodic/de-Bruijn tests, the T147 compatibility scale, and all verdict,
successor, transfer, and claim-firewall markers. Finite checks are experiments,
not proofs of the asymptotic deductions.

SCOPED_VERDICT (1/1): **develop**.

Develop only Candidate C's reuse-adjusted related-model census. Candidates P
and H are closed for this exact triangular substitution, and S4--S6 do not
repair them. This verdict does not develop a fixed-pi route.

SUCCESSOR (1/1): **Extract one explicit numerical concentration constant for
the uniform decimal full shift and optimize the threshold statistic, while
retaining the exact `N` starts and T147 compatibility test.** This is bounded to
one finite-probability lemma; it does not include pi membership or T107 transfer.
