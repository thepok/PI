# T184: d-bonacci every-window collision floor

Audit date: 2026-08-13 UTC. The statement attributed to the primary source is
`literature-checked` against the independently downloaded, pinned PDF and the
exact ranges in `SOURCE_LEDGER.csv`. Sections 4--6 are a `proof sketch`: every
step is written out, but no Lean formalization is claimed. The replay is an
`experiment` checking artifact integrity, exact finite recurrences, endpoints,
and sample collision energies; finite checks are not proof of the universal
deduction.

```text
PRIMARY_SOURCE_COUNT: 1
SCHEDULE: m_N=floor((1/4)*log_10(N))
COLLISION_ORDERING: ordered
COLLISION_DIAGONAL: included
OVERLAP: allowed
WRAPPING: forbidden
NAMED_RECURRENCE_GAP_COUNT: 1
SCOPED_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement and scope

The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
Its provenance says that this program formulated it on 2026-07-22, so there is
no external original-source URL to preserve. It asks whether, for the fixed
decimal orbit of pi and the strict circle-distance count with ordered pairs and
diagonal included,

```text
for every integer A>=1 there exists n_0>=1 such that every integer n>=n_0
admits an integer N>=1 with A*n*Q_pi(n,N)<=N^2.
```

T184 studies an A13/A14 sibling: an explicit finite-alphabet morphic word. It
does not replace the circle metric by symbolic equality inside the canonical
question. The canonical quantifiers, strict endpoint, and fixed point pi remain
untouched.

Ambiguities normalized before the proof:

1. `N` is the number of starts, not the length of a truncated word.
2. A start is legal exactly when `0<=i<N`; its window may overlap every other
   window and uses symbols through index `N+m-2`.
3. There is no cyclic wrapping and no deletion of a final partial window.
4. Collision pairs are ordered. Every `(i,i)` is included.
5. Source depth is renamed `m`, reserving `N` for the number of starts.
6. The schedule is exactly `m_N=floor((1/4)*log_10 N)` and is used only when
   `m_N>=1`.
7. The source result is about one fixed `d` and one infinite fixed point;
   constants may depend on `d`, although the bound below is uniform in `d`.

## 2. Independent source pin and reconstruction

The sole primary source is Kateřina Medková, Edita Pelantová, and Élise
Vandomme, *On non-repetitive complexity of Arnoux--Rauzy words*,
arXiv:2002.12593v1, <https://arxiv.org/pdf/2002.12593v1>. The independently
retrieved PDF has SHA-256
`9fb2ef592ef0986faaf8e4365dc6505e0387d4a92be026e9fc3e89a6375a22c5`;
the delivered `pdftotext -layout` derivative has SHA-256
`25168ffe1b2045c32d7786c016642a88a5b49407fccbd674a2fa55e583b67dd8`.

Fix an integer `d>=2` and alphabet `A={0,...,d-1}`. Example 3 on printed/PDF
p. 4 defines the `d`-bonacci morphism

```text
tau(a)=0(a+1) for 0<=a<=d-2,       tau(d-1)=0.              (2.1)
```

Because `tau(0)` begins in `0`, the nested prefixes `tau^r(0)` define an
infinite fixed point `t=t_0t_1...`, the `d`-bonacci word.

Printed/PDF p. 12 defines the source numbers by

```text
D_k=2^k                                  for 0<=k<=d-1,
D_k=sum_(j=1)^d D_(k-j)                  for k>=d,
D_(-1)=1,  D_(-r)=0                      for 2<=r<=d.       (2.2)
```

Lemma 19, printed/PDF pp. 13--14, proves `|tau^k(0)|=D_k`.

For positive `k`, define the integer endpoints

```text
L_k=(sum_(i=0)^(d-1) (d-i)D_(k-i-2)-d)/(d-1),
U_k=(sum_(i=0)^(d-1) (d-i)D_(k-i-1)-d)/(d-1).             (2.3)
```

Here `L_1=0` and direct index shifting gives `U_k=L_(k+1)`. The positive-depth
intervals are therefore left-open and right-closed:

```text
L_k < m <= U_k.                                            (2.4)
```

They are consecutive and cover every positive integer depth exactly once.

Definition 1, printed/PDF p. 2, defines `nrC_t(m)` as the largest `R` for
which some interval of `R` consecutive starts has pairwise distinct length-`m`
factors. Theorem 20, printed/PDF pp. 14--15, states that under (2.4),

```text
R=nrC_t(m)=D_(k+1)-1-U_k+m.                               (2.5)
```

Theorem 21 on p. 15 states `inrC_t(m)=D_k`. The present collision argument uses
Theorem 20, not Theorem 21; recording both prevents an initial-prefix quantity
from being mistaken for the every-window quantity.

## 3. Collision observable and endpoints

For integers `m,N>=1`, let

```text
B_t(i,m)=(t_i,t_(i+1),...,t_(i+m-1))             for 0<=i<N,
c_t(u;m,N)=#{i in {0,...,N-1}: B_t(i,m)=u},
E_t(m,N)=sum_u c_t(u;m,N)^2
        =#{(i,j) in {0,...,N-1}^2:B_t(i,m)=B_t(j,m)}.       (3.1)
```

Thus the symbol endpoint is `N+m-2`, starts `N-1` and `N` are respectively
included and excluded, overlaps are legal, and all `N` diagonal pairs occur.
Consequently `E_t(m,N)-N` is the ordered off-diagonal energy and is even.

## 4. Every-window floor (`proof sketch`)

Fix `m>=1`, choose the unique `k` satisfying (2.4), and put `R=nrC_t(m)`.
By maximality in Definition 1, no interval of `R+1` consecutive starts can
have all its length-`m` factors distinct. Hence every such interval contains
an unordered equal-factor pair.

Partition the legal starts into the disjoint full intervals

```text
{q(R+1),...,q(R+1)+R},   0<=q<floor(N/(R+1)).              (4.1)
```

Choose one unordered collision in each interval and count its two orientations.
The selected pairs are distinct because the intervals are disjoint. Therefore

```text
E_t(m,N)-N >= 2 floor(N/(R+1)).                            (4.2)
```

Equation (2.5) and the right endpoint `m<=U_k` give

```text
R+1=D_(k+1)-U_k+m <= D_(k+1).                             (4.3)
```

This proves the exact source-dependent every-window floor

```text
E_t(m,N)-N >= 2 floor(N/D_(k+1)).                         (4.4)
```

for the unique source index `k` at depth `m`. No endpoint is discarded: a
remainder interval shorter than `R+1` simply contributes no certified pair.

## 5. Uniform recurrence bound and logarithmic substitution (`proof sketch`)

The left endpoint `L_k<m`, after multiplying (2.3) by `d-1`, implies

```text
d D_(k-2) < (d-1)m+d,                                    (5.1)
```

because every omitted summand is nonnegative. From (2.2),
`D_(j+1)<=2D_j` for `j>=0`: it is equality in the initial powers-of-two range,
and afterward follows from `D_(j+1)=2D_j-D_(j-d)`. For `k=1,2` the same
three-step estimate is checked directly from the initial conventions; hence

```text
D_(k+1) <= 8D_(k-2).                                     (5.2)
```

Since `m>=1`, (5.1) gives `D_(k-2)<2m`; combining with (5.2),

```text
D_(k+1)<16m.                                              (5.3)
```

Equations (4.4) and (5.3) therefore give the explicit uniform bound

```text
E_t(m,N)-N >= 2 floor(N/(16m)).                           (5.4)
```

Now take exactly

```text
m_N=floor((1/4)*log_10 N).
```

For `N>=10^4`, `m_N>=1`, and (5.4) applies. Since
`m_N<=(1/4)log_10 N` and `floor x>=x-1`,

```text
E_t(m_N,N)-N >= 2 floor(N/(16m_N))
                 >= N/(2 log_10 N)-2.                    (5.5)
```

Thus the source theorem yields an explicit coherent
`Omega(N/log N)` ordered off-diagonal collision floor, uniformly for every
fixed `d>=2` and every `N>=10^4`. This is a lower bound, not an asymptotic and
not an upper collision estimate.

## 6. The single named recurrence gap

`NR-ENERGY-MULTIPLICITY` is the gap between (2.5) and any matching energy upper
bound or asymptotic. The statistic `nrC_t(m)=R` says:

```text
(i) some R consecutive starts are pairwise distinct;
(ii) every R+1 consecutive starts contain at least one collision.
```

Neither clause bounds the global fiber sizes `c_t(u;m,N)`. In particular, it
does not bound how many disjoint `(R+1)`-interval witnesses may carry the same
factor, nor how many additional cross-interval pairs that factor creates.
Since energy squares the fiber sizes, (4.2) cannot be reversed or upgraded to
`Theta(N/R)` from `nrC` alone. A matching result would require a new theorem
such as a uniform bound on every `c_t(u;m,N)`, or an exact return-time
distribution with controlled second moment. Theorems 20--21 state neither.

This is the only unresolved recurrence gap asserted by T184. The lower bound
(5.5) does not depend on closing it.

## 7. Direct comparison with T176, T180, and T181

`T176_SOURCE_LEDGER.csv`, `T180_SOURCE_LEDGER.csv`, and
`T181_SOURCE_LEDGER.csv` are byte-exact copies of the accepted pinned source
ledgers. `COMPARISON_LEDGER.csv` records source, theorem, and mechanism fields
separately. Conclusions below compare fingerprints only; no proof-sketch
deduction from a comparator is imported as a premise.

| Comparator | Direct tuple comparison | Boundary |
|---|---|---|
| T176 | T176 uses arXiv `1507.02510v1`, `2408.14059v1`, `1604.02300v1`, and `2007.15482v2`; T184 uses `2002.12593v1`, Theorems 20--21. T176's outputs are a Cantor Mahler support identity, automatic correlation, and structured sums; T184's is an exact `nrC` formula. | No source/theorem duplicate. T184 remains in T176's broad functional-relation collision-floor family, but replaces the heavy-zero-fiber or one-offset mechanisms by an every-window existential recurrence. It does not improve to an upper bound. |
| T180 | T180's four tuples are `2504.09650v2`, `2603.16794v3`, `1802.10355v1`, and `1407.4100v1`. The nearest, T180-S3, upper-bounds maximal gapped-repeat descriptors. | No source/theorem duplicate. Descriptor packing and `nrC` have opposite directions and different observables. Both lose ordered-pair multiplicity, which is exactly the named gap above rather than a claimed new upper mechanism. |
| T181 | T181's tuples are `2606.28860v1`, `2601.03402v1`, and `2603.23250v2`; none is retained there. They concern almost-everywhere maximal gaps, a constructed measure, and weighted short sums. | No source/theorem/fingerprint duplicate. T181-S1 also lacks multiplicity, but for circular coverage of almost-every dilation; T184 treats equal factors of one explicit morphic fixed point via exact maximal distinct-start windows. |

The primary PDF hash happens to equal the hash recorded in rejected T182, which
corroborates byte identity only. T184 imports no theorem, calculation,
comparison, or availability claim from T182; all operative material is present
in this artifact set.

## 8. Scope and endpoint

The result is related-model mathematics only. It makes no conclusion about
fixed pi, canonical A1, C1, or C2. Exact equality of factors in the `d`-bonacci
word is not circle-distance proximity for the decimal orbit of pi, and no
encoding or carry-safe transfer is asserted.

**SCOPED VERDICT (1/1): HOLD AS MODEL.**

Hold only the explicit every-window lower collision floor (5.5) and the named
`NR-ENERGY-MULTIPLICITY` boundary. The mechanism calibrates how far an exact
functional recurrence remains from a collision-energy asymptotic or upper
bound; it does not reopen a broad functional-equation scout.

## 9. Artifact-only replay

From a directory containing only the delivered files, run

```text
python3 verify_t184.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay verifies all pins, exact source anchors, comparator tuple IDs,
endpoint and verdict markers, recurrence identities over a bounded range, the
algebra behind (5.1)--(5.5), and direct collision energies of generated
`d`-bonacci prefixes. Those finite calculations are an `experiment`; the
universal argument is the inspectable proof sketch above.
