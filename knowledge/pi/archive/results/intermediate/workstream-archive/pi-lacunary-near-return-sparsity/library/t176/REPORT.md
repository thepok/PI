# T176: logarithmic-depth functional-relation collision scout

Audit date: 2026-08-13 UTC. Source statements explicitly attributed to S1--S3
are `literature-checked` against the three pinned PDFs and exact ranges in
`SOURCE_LEDGER.csv`. The collision calculations and applicability screens are
`proof sketch`. The self-contained replay is an `experiment`; it is finite
evidence and artifact-integrity checking only. Every statement involving pi is
separately labeled an unproved transfer hypothesis.

```text
SEARCHED_DOMAIN_COUNT: 3
NEW_SOURCE_THEOREM_TUPLE_COUNT: 4
NEW_SOURCE_THEOREM_TUPLE_CAP: 6
CANDIDATE_CARD_COUNT: 3
RETAINED_FINGERPRINT_COUNT: 1
RETAINED_FINGERPRINT_CAP: 3
EXCLUSION_LEDGER_RANGE: T89-T175
EXCLUSION_LEDGER_COUNT: 87
RESERVED_ACTIVE_ITEMS: T173,T174
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement and normalized scope

The local statement has no external source URL; its provenance says the program
formulated it on 2026-07-22. The byte-exact `canonical_statement.txt` has
SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether, for the fixed decimal orbit of pi and the ordered,
diagonal-inclusive strict circle-distance count,

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N)<=N^2.
```

T176 studies only A13/A14 symbolic siblings. It neither changes nor answers the
canonical question.

Ambiguities fixed before searching:

1. A source/theorem tuple is one primary PDF plus the exact inspected theorem
   range. Its text derivative is not another source.
2. A searched domain is source-native. Exactly the three agenda domains are
   used; no restricted-denominator or ambient-measure lane is added.
3. For an infinite word `W=(w_i)_(i>=0)`, integers `M,m>=1`, and all legal
   nonwrapping starts `0<=i<M`, write

   ```text
   B_W(i,m)=(w_i,...,w_(i+m-1)),
   c_W(u;m,M)=#{0<=i<M:B_W(i,m)=u},
   E_m(W_M)=sum_(u)c_W(u;m,M)^2.
   ```

   Thus `W_M` means the inspected prefix through `M+m-2`, not truncation or
   wrapping. `E_m` counts ordered pairs and includes all `M` diagonal pairs.
4. A coherent logarithmic schedule means one infinite word, one increasing
   sequence `M_k`, one fixed `0<kappa<=1`, and
   `m_k=floor(kappa*log_10(M_k))>=1` eventually.
5. A repeated offset is a positive `d<M` for which some legal starts `i,i+d`
   have equal length-`m` blocks. "Positive-density repeated offsets" means at
   least `delta*M` distinct such `d` for one fixed `delta>0`; the collision floor
   is a separate multiplicity requirement. A single pair of equal long blocks
   is not enough.
6. A source may be retained as a related-model obstruction even when its
   mechanism is prohibited as a new route. Retention is not endorsement.
7. Constants may depend on the one fixed related model and on fixed `kappa`, but
   not on `k`, `M_k`, or `m_k`. A family with constants tending to zero is
   rejected.
8. Factor-complexity plus Cauchy--Schwarz, one finite prefix, finite-state
   periodicity, and unrelated prefixes at different depths are not survivors.
9. The T171 side finding named by the agenda is an `unverified lead` only. No
   mathematical statement from it is imported.

## 2. Bounded search and nonduplication

The clean-context search opened exactly one previously unaudited primary PDF in
the first two domains and two in the third, then stopped:

1. Mahler or functional-equation constants: arXiv query
   `"Cantor sequence" AND Mahler` selected S1.
2. Symbolic collision theory: arXiv query
   `"correlation measure" AND "automatic sequences"` selected S2.
3. Short structured exponential sums: arXiv queries
   `"exponential sums" AND "recurrence sequences"` and
   `"short Kloosterman sums"` first screened S4 because its theorem is a
   complete-period recurrence sum, then selected the genuinely incomplete S3.

Exact searches of the supplied readable corpus found none of the identifiers
`1507.02510`, `2408.14059`, `1604.02300`, or `2007.15482`, and none of the four
PDF hashes.
This proves absence only from the bounded supplied corpus, not global novelty.
The four stable identifiers, hashes, locators, and normalized fingerprints in
`SOURCE_LEDGER.csv` are pairwise distinct. Exactly four new tuples were
inspected, below the cap of six. S4 was screened before candidate retention, so
the three candidate cards below still correspond one-for-one to the three
required domains. Exactly one fingerprint is retained, below the cap of three.

## 3. Exclusion ledger and required comparisons

`EXCLUSION_LEDGER.csv` has exactly one consecutive row for each item T89--T175.
Its T89--T170 prefix is byte-preserved from T171. The six appended rows preserve
the refreshed verification boundary:

- T171 is pinned literature; its three tuples are reserved, while the agenda's
  side finding remains an unverified lead.
- T172 is a readable unverified note; no cumulant claim is imported.
- T173 and T174 are reserved as active/revising identifiers. Their artifacts are
  absent from the supplied knowledge library, so no theorem, tuple, or
  nonduplication claim is inferred.
- T175 is pinned literature; all three of its tuples are reserved.

Mandatory nearest comparisons:

| Comparator | Level used | Boundary for T176 |
|---|---|---|
| T91 | unverified `proof sketch` note | The note argues for substitution/paperfolding synchronization. F-CANTOR is not inferred from it, but its automatic finite-state ancestry prevents novelty. |
| T94 | unverified `proof sketch` plus experiment | Paperfolding tensor/profile recurrence is excluded; no tensor recurrence is imported. |
| T97 | unverified `proof sketch` plus experiment | Paperfolding diagonal-collision formulas are not premises; T176 performs its own Cantor support count. |
| T101 | unverified `proof sketch` plus experiment | The note argues that high paperfolding energy need not give successor splitting. T176 makes no splitting claim. |
| T115 | pinned sources, deductions `proof sketch` | Exact substitution Riesz recursions are already represented. T176 retains no Fourier-ray mechanism. |
| T119 | recovered incomplete `proof sketch` comparator | Predictive/Hankel/Prony rank is excluded. No rank inference is used. |
| T160 | pinned literature, deductions `proof sketch`, replay experiment | Pair multiplicity and the loss from first recurrence to all ordered pairs are already explicit. T176's only hold is an obstruction with a direct heavy fiber, not a new upper-bound route. |
| T171 | pinned bounded literature audit | Its automatic algebraic-equation tuple `1710.03026` differs from S1/S2, but the agenda-level side finding is unverified and supplies no premise. |

The broader inherited ledger also marks T89's sparse/Mahler constants, T104 and
T127's Mahler cells, T128's factor-complexity route, and T134's zero-heavy-fiber
audit. Consequently F-CANTOR is retained only as the requested source-pinned
related-model obstruction. It is not claimed as a new mechanism beyond those
cells.

## 4. Candidate C-MAHLER: Cantor Mahler relation

### 4.1 Literature-checked source statement

S1 studies degree-one Mahler functions satisfying

```text
p(z)+p0(z)F(z)+p1(z)F(z^d)=0, d>=2.
```

On PDF/printed pp. 1--2 it defines the Cantor coefficients `v_n in {0,1}` by
`v_n=1` exactly when the ternary expansion of `n` contains no digit `1`, and
defines `f_C(z)=sum_(n>=0)v_n z^n`. Products (1) on p. 2 define

```text
U_3(z)=product_(j>=0)(1+z^(2*3^j)),
```

and p. 3 identifies `U_3=f_C`. Splitting the first product factor gives the
exact Mahler relation

```text
f_C(z)=(1+z^2)f_C(z^3).                                  (4.1)
```

Theorem 1 and Corollary 2 prove algebraic independence statements for values at
nonzero algebraic points in the open unit disk. Those arithmetic conclusions
are source context only; the collision calculation uses the source-defined
coefficient support and (4.1), not algebraic independence.

### 4.2 Explicit logarithmic-depth collision calculation (`proof sketch`)

Let `W=(v_n)_(n>=0)`, fix `0<kappa<=1`, and set

```text
M_k=3^k,
m_k=floor(kappa*log_10(M_k))=floor(kappa*k*log_10(3)).     (4.2)
```

For all sufficiently large `k`, `m_k>=1`; also `m_k<=k`. Exactly `2^k` indices
in `[0,3^k)` have `v_n=1`, because each of the `k` ternary digits has the two
choices `0,2`. In the extra inspected interval `[3^k,3^k+m_k-2]` there are at
most `m_k` further ones.

A start `0<=i<M_k` fails to have the all-zero length-`m_k` block only if its
window contains a one. Each one contaminates at most `m_k` starts. Therefore,
with `Z_k` the number of all-zero starts,

```text
Z_k >= M_k-m_k*(2^k+m_k).                                 (4.3)
```

For `k>=7`, the elementary bound

```text
k*(2^k+k) <= 3^k/2                                        (4.4)
```

holds (the replay checks its base case and the induction inequality). Hence
`Z_k>=M_k/2`. All ordered pairs of these starts have the same block, so

```text
E_(m_k)(W_(M_k)) >= Z_k^2 >= M_k^2/4
                   >= (1/4)*M_k^2/m_k.                    (4.5)
```

If `A_k` is the set of those zero-block starts and `a=min A_k`, the distinct
differences `{i-a:i in A_k, i>a}` are repeated offsets. Consequently there are
at least `Z_k-1>=M_k/2-1` distinct repeated offsets. Thus this is coherent along
every sufficiently large `k`, has offset density tending to at least `1/2`, and
has the fixed collision constant `c=1/4`. It is not one finite prefix, and the
constant does not vanish with `m_k`.

### 4.3 Disposition

Equation (4.5) passes the literal target but fails the novelty discriminator.
Its cause is one overwhelmingly occupied all-zero fiber in a 3-automatic word.
It is exactly finite-state/heavy-fiber recurrence, nearest the inherited T89,
T91, T128, and T134 exclusions. It supplies a lower obstruction, not an upper
collision certificate and not an offset-sensitive mechanism beyond finite-state
recurrence.

**Disposition:** retain F-CANTOR only as a source-pinned related-model
obstruction; reject it as a successor route.

## 5. Candidate C-SYMBOLIC: Parry--Bertrand automatic correlation

### 5.1 Literature-checked source statement

S2 defines `C_k(s,N)` on PDF/printed p. 2 as a maximum of signed shifted sums.
Theorem 2, pp. 3--4, states that for fixed `k>=1`, a Parry number `beta`, and a
binary canonical Parry--Bertrand automatic sequence,

```text
C_(2k)(s,N) >> N,
```

with constant depending on `beta`, `k`, and automaton size. In the proof on
pp. 9--11, one product-automaton state collision yields two identical blocks of
length `U_beta(L)` at starts `p_u,p_v`; equations (2)--(4) make that block length
a positive proportion of the ambient cutoff. Theorem 3, pp. 7--8, gives the
analogous linear-correlation result for linearly recurrent words.

### 5.2 Explicit logarithmic-depth rejection (`proof sketch`)

Let the source proof give two equal blocks of length `L>=rho*M` inside one
prefix of size `M`, where `rho>0` is fixed for the one automaton. At

```text
m=floor(kappa*log_10 M),                                  (5.1)
```

the one repeated offset `d=p_v-p_u` certifies at most the two orientations of
each aligned start pair in those blocks:

```text
2*(L-m+1) <= 2M                                           (5.2)
```

ordered off-diagonal equal-block pairs, plus the unavoidable `M` diagonal
pairs. The requested floor has scale `c*M^2/m`; the ratio of (5.2) to that
scale is at most

```text
2M/(c*M^2/m)=2m/(c*M) -> 0.                               (5.3)
```

The source theorem maximizes a signed correlation over a delay tuple; it does
not state positive density of distinct repeated offsets or quadratic
multiplicity of block fibers. Adding the discussion's factor-complexity bound
and Cauchy--Schwarz would be exactly the prohibited route. Reusing all automaton
state collisions would require a new multiplicity theorem with constants
uniform in growing `m`; S2 does not state one.

**Disposition:** screened. The explicit source certificate is one long offset
and only linear pair mass at logarithmic depth.

## 6. Candidate C-SHORT: powerful-modulus Kloosterman sums

### 6.1 Literature-checked source statement

S3 defines on PDF/printed p. 1 the incomplete Kloosterman sum

```text
S_q(N;a,b,c)=sum_(c<n<=c+N,(n,q)=1)e_q(a*n^*+b*n),          (6.1)
```

where `n*n^*=1 (mod q)` and `(a,q)=1`. Put `d=product_(p|q)p`.
Theorem 1, PDF/printed p. 1, fixes `gamma_1=900`, `gamma=160^(-4)` and, for all
sufficiently large `q`, assumes

```text
max(d^15, exp(gamma_1*(log q)^(2/3))) <= N <= sqrt(q).      (6.2)
```

It concludes, uniformly in legal `a,b,c`,

```text
|S_q(N;a,b,c)| < N*exp(-gamma*(log N)^3/(log q)^2).        (6.3)
```

The complete proof is on PDF/printed pp. 2--7, using the displayed Postnikov
expansion and Lemmas 1--4.

### 6.2 Explicit logarithmic-depth rejection (`proof sketch`)

The theorem has no binary or finite-alphabet word `W`, no equality of
length-`m` blocks, and no repeated offset. Consequently its literal certified
collision contribution at

```text
m=floor(kappa*log_10 N)                                   (6.4)
```

is zero: neither (6.1) nor (6.3) identifies even one equal-block pair. Any
conversion would have to define a new coding `W^(q)` from the summands. For
fixed `q`, the legal interval length is bounded by `sqrt(q)`, hence supplies
only finitely many prefixes. Letting `q=q_k` grow creates different coded words
`W^(q_k)` and gives no nesting into one infinite word. Even the saving factor
in (6.3) depends on both `N` and `q`; it is a cancellation upper bound, not a
positive repeated-offset or collision lower bound.

**Disposition:** screened. The short sum is genuine and quantitative, but it
has no collision observable and no coherent infinite prefix family.

## 7. Separate unproved transfer hypothesis for pi

`PI-FUNCTIONAL-OFFSET-T176` (`conjecture`; unproved and not asserted): there
would have to exist fixed finite data, independent of depth, giving a
source-pinned algebraic, automatic, Mahler-functional, or finite annihilating
relation for the actual decimal digit word of pi, together with a proved
conversion having all of the following properties:

1. On one increasing prefix schedule `M_k`, with fixed `0<kappa<=1` and
   `m_k=floor(kappa*log_10 M_k)`, it produces an explicit set of length-`m_k`
   equal-block pairs.
2. The certificate is offset-sensitive: it proves either positive density of
   distinct repeated offsets or direct fiber multiplicities whose ordered
   square sum is at least `c*M_k^2/m_k` for one fixed `c>0`.
3. The proof does not pass only through factor complexity and
   Cauchy--Schwarz, one finite prefix, a constant tending to zero, or unrelated
   words/prefixes at different `k`.
4. The relation is established for pi's decimal orbit itself, and a separate
   proved symbolic-to-metric implication pays every carry and endpoint cost.

No audited source supplies the first premise for pi, much less the conversion.
This hypothesis makes no fixed-pi theorem, canonical A1, C1, or C2 claim.

## 8. Endpoint

`SCOPED VERDICT (1/1): CLOSE THE FINGERPRINT.`

Close only the bounded fingerprint that one of these three exact tuples supplies
an offset-sensitive logarithmic-depth collision floor beyond finite-state
recurrence and factor complexity. S1 gives a clean coherent floor, but solely
through a dominant zero fiber in an automatic word; S2 gives only one
linear-mass repeated offset; S3 gives a quantitative short-sum bound but no
collision observable or coherent coded word. F-CANTOR is retained as the one
source-pinned related-model obstruction. No successor is selected
(`SUCCESSOR_COUNT: 0`). Nothing here bears on whether pi satisfies or fails any
collision bound, and no A1, C1, or C2 claim is made.

## 9. Artifact-only replay

From a directory containing only the delivered files:

```text
python3 verify_t176.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay checks the canonical and source hashes, exact source anchors, exactly
three domains and tuples, caps, one retained fingerprint, consecutive T89--T175
coverage, active T173--T174 reservation, every mandatory comparison, the three
logarithmic-depth calculations/rejections, exactly one scoped verdict, no
successor, and all four no-claim markers. Its bounded arithmetic is an
`experiment`, not proof of a source theorem or universal transfer.
