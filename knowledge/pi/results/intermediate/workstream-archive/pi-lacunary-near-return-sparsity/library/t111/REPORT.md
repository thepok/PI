# T111: explicit remote decimal-label separation scout

Search and audit date: 2026-08-10 UTC.

```text
PRIMARY_SOURCE_COUNT: 3
PRIMARY_SOURCE_CAP: 10
SEARCHED_LANE_COUNT: 3
RETAINED_CANDIDATE_COUNT: 2
RETAINED_CANDIDATE_CAP: 3
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 1
```

Claim labels are load-bearing. The statements attributed to S1-S3 in
`SOURCE_PINS.md` are `literature-checked`. Sections 3-8 are new elementary
`proof sketch` derivations: they are written in full but are not
machine-checked. The bounded replay from `verify_t111.py` is an `experiment`
and tests transcription only.

The result concerns explicit related-model decimals. It does not establish the
canonical statement for the prescribed constant, and it asserts no conclusion
for either named program conjecture.

## 1. Immutable statement and normalized sibling

The byte-exact file `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question fixes the decimal orbit of the prescribed constant,
uses strict circle radius `10^(-n)`, counts ordered pairs including the
diagonal, and asks

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q(n,N)<=N^2.
```

T111 changes the point and therefore treats an A13 sibling only.

For a real `x`, take `{y}` in `[0,1)`. For integers `m>=1` and `i>=0`, define

```text
M_m             = 10^m,
B_m^x(i)        = floor(M_m*{10^i*x}) in {0,...,M_m-1},
d_m(a,b)        = min((a-b) mod M_m, (b-a) mod M_m),
N_m(c)          = floor(exp(c*m)).
```

The residues in `d_m` are their representatives in `{0,...,M_m-1}`. For real
constants `K>0`, `c>0` and integer `m0>=1`, define

```text
P_x(K,c,m0):
  for every integer m>=m0 and all integers 0<=i,j<N_m(c),
  d_m(B_m^x(i),B_m^x(j))<=1 implies |i-j|<K*m.
```

Define the exact metric sibling count, for integers `m,N>=1`, by

```text
Q_x(m,N) = #{(i,j) in {0,...,N-1}^2:
              ||(10^i-10^j)*x||_(R/Z) < 10^(-m)}.
```

Pairs are ordered, all `N` diagonal pairs occur, overlaps are unrestricted,
and the metric inequality is strict. A prefix cutoff restricts starts only:
the length-`m` block at start `N-1` may inspect later digits.

### Normalized ambiguities

1. `K` and `c` are fixed before `m,i,j`; they do not depend on the scale.
2. `N_m(c)` is the literal floor of the real exponential.
3. Numeric adjacency is cyclic modulo `10^m`, so labels `0` and `10^m-1`
   are adjacent.
4. The decimal expansion used for a constructed point is the displayed
   digit stream. Neither retained stream is eventually 9, so there is no
   dual-expansion ambiguity.
5. Exact block equality is not silently identified with metric near return.
   Section 4 proves the required one-bin implication.
6. A finite test can falsify a universal candidate but cannot establish
   `P_x` without a universal construction argument or finite-state pumping
   theorem.

## 2. Bounded three-lane protocol

The search stopped after one primary source in each lane:

| lane | query fingerprint | primary source | use |
|---|---|---|---|
| synchronization and symbolic-collision coding | total/infinite de Bruijn extension, nested de Bruijn prefixes, decimal-safe code | S1 Fishman-Merrill-Simmons | retained survivor |
| explicit fixed-point marker or return time | computable characteristic Sturmian point, recurrence function, lacunary convergents | S2 Masakova-Pelantova | retained rejection model |
| restricted-denominator avoidance | Peres-Schlag, sublacunary avoidance, nested closed sets | S3 Moshchevitin | screened before candidate admission |

No source was added to fill the cap. `SOURCE_PINS.md` gives the exact versions,
URLs, hashes, and locators. All three PDFs and their `pdftotext -layout`
derivatives are delivered.

## 3. Cardinality and prefix-factor-complexity obstruction

This section is a new `proof sketch` valid for every real `x` satisfying the
displayed predicate.

Fix `m>=m0` and put `N=N_m(c)` and `H=ceil(K*m)`. For a label `a`, let

```text
F_a={i in {0,...,N-1}:B_m^x(i)=a}.
```

Any two members of `F_a` have cyclic label distance zero, so `P_x` says their
integer distance is strictly less than `K*m`. If `F_a` is nonempty and `u,v`
are its minimum and maximum, then `v-u<K*m`. Since `v-u` is an integer,

```text
v-u <= ceil(K*m)-1 = H-1,
|F_a| <= v-u+1 <= H.                                      (3.1)
```

Let `D_x(m,N)` be the number of distinct length-`m` decimal factors at the
first `N` starts. The fibers partition all starts. Thus

```text
D_x(m,N_m(c)) >= ceil(N_m(c)/ceil(K*m)).                   (3.2)
```

There are at most `10^m` labels, so another necessary condition is

```text
floor(exp(c*m)) <= 10^m*ceil(K*m) for every m>=m0.         (3.3)
```

If `c>log(10)`, the quotient of the left side by the right side grows
exponentially, contradicting (3.3). Therefore every instance of `P_x` obeys

```text
c <= log(10).                                               (3.4)
```

For a quantitative complexity statement, fix any real `c'` with `0<c'<c`.
Choose `m1` so that for every `m>=m1`,

```text
exp(c*m)>=2 and exp((c-c')*m)>=2*(K+1)*m.
```

Such an `m1` exists because an exponential dominates a linear function. Since
`floor(exp(c*m))>=exp(c*m)/2` and
`ceil(K*m)<=K*m+1<=(K+1)m`, (3.2) gives, for every
`m>=max(m0,m1)`,

```text
D_x(m,N_m(c)) >= exp(c'*m).                                (3.5)
```

Hence `P_x` forces exponential complexity already inside its declared prefix,
not merely somewhere in the language. In particular, periodic and
subexponential-complexity words fail before carry or metric questions arise.

## 4. Decimal bins, carries, and the displayed count

This section is a new `proof sketch` and supplies the presentation-appropriate
carry/borrow argument.

Put `M=10^m`, `y={10^i*x}`, `z={10^j*x}`, `a=floor(My)`, and `b=floor(Mz)`.
Write

```text
My=a+u, Mz=b+v, with 0<=u,v<1.                             (4.1)
```

### Metric near return implies cyclic label adjacency

If `||y-z||_(R/Z)<1/M`, some integer `q` satisfies

```text
|(a-b-qM)+(u-v)|<1.                                        (4.2)
```

Here `u-v` lies strictly between `-1` and `1`. The integer `a-b-qM` must
therefore be `-1`, `0`, or `1`; if its absolute value were at least two, the
left side of (4.2) would be strictly greater than one. Thus

```text
d_m(a,b)<=1.                                                (4.3)
```

This treats an ordinary boundary crossing and the `0`/`M-1` wrap uniformly.

### Cyclic label adjacency implies a two-bin metric bound

Conversely, if `d_m(a,b)<=1`, choose `q` so that
`a-b-qM` is `-1`, `0`, or `1`. Equation (4.1) gives

```text
||y-z||_(R/Z) < 2/M.                                       (4.4)
```

The constant is strictly two because `u-v` is in `(-1,1)`. This reverse
direction is used only for the restricted-denominator transfer in Section 8.

### P-to-Q implication with all quantifiers

Assume `P_x(K,c,m0)`. Then for every integer `m>=m0` and every integer
`N` with

```text
1<=N<=floor(exp(c*m)),                                      (4.5)
```

each pair counted by `Q_x(m,N)` satisfies (4.3), hence
`|i-j|<K*m`. For each fixed `i`, the number of integers `j` in the sample with
that property is at most `2*ceil(K*m)+1`. Summing over the ordered first
coordinate gives the required literal display

```text
Q_x(m,N) <= (2*ceil(K*m)+1)*N.                             (4.6)
```

The deliberately loose `+1` includes the diagonal and remains valid at both
sample endpoints.

There is also an exact canonical-quantifier sibling consequence. For every
integer `A>=1`, choose an integer `m_A>=m0` so that for every integer
`m>=m_A`,

```text
floor(exp(c*m)) >= A*m*(2*ceil(K*m)+1).                    (4.7)
```

This is possible because `c>0`. For every such `m`, take
`N=floor(exp(c*m))`. Equations (4.6)-(4.7) give

```text
A*m*Q_x(m,N)<=N^2.                                         (4.8)
```

This has the canonical order `every A`, `every sufficiently large m`, `some
N=N(A,m)`, but only for the explicitly changed point `x`.

## 5. Candidate FMS-odd: survivor

### Named computable nested decimal

Let `A={1,3,5,7}` with its usual order. Start with the lexicographically least
non-cyclic order-one de Bruijn word on `A`. Recursively, after choosing an
order-`n` word `w_n`, choose the lexicographically least order-`n+1` de Bruijn
word whose initial `4^n+n-1` digits equal `w_n`. Call the unique nested limit
`omega_FMS` and define

```text
x_FMS = 0.omega_FMS in base 10.                            (5.1)
```

This is the **FMS-odd decimal**. S1 Corollary 4.3, printed pp. 10-11,
constructs at least one extension for every order when `k>=4`; its proof first
adds the missing closing edge and then completes an Eulerian path. The
lexicographic specialization is a new deterministic choice, not source
terminology. It is computable: at stage `n`, enumerate the finite set of words
of length `4^(n+1)+n`, test the finite de Bruijn and prefix conditions, and
select the first; S1 proves termination. Every requested digit stabilizes in a
finite stage.

### Exact source card

| field | value |
|---|---|
| source version | S1 published version, 2018, DOI `10.1007/s00026-018-0384-2` |
| theorem locator | definition (2.1), printed pp. 3-4; Remark 3.3, p. 5; Corollary 4.3 and proof, pp. 10-11 |
| source hypotheses | finite alphabet cardinality `k>=4`; base `b>=2`; digit subset of size `k` |
| specialization | `b=10`, `A={1,3,5,7}`, `k=4` |
| source conclusion used | an order-`n` de Bruijn prefix has an order-`n+1` de Bruijn extension for every `n` |
| new constants | `K=1`, `c=log(4)`, `m0=1` |
| status | source theorem `literature-checked`; specialization and `P_x` derivation `proof sketch` |

S1 also proves that the set of totally de Bruijn expansions has positive
Hausdorff dimension. For this particular word, every word over `A` occurs, so
its orbit closure has the full four-symbol language and topological entropy
`log(4)`. This last sentence is an elementary new `proof sketch`, not a quoted
source theorem about the selected point.

### Exact separation proof

Fix `m>=1`. By construction, the prefix of length `4^m+m-1` is a non-cyclic
order-`m` de Bruijn word. Therefore the `4^m` factors

```text
omega_FMS[i,i+m), 0<=i<4^m,                               (5.2)
```

are pairwise distinct. Since
`floor(exp(log(4)*m))=4^m`, these are exactly the starts required by `P_x`.

The code `B_m^(x_FMS)(i)` is the ordinary integer represented by the `m`
digits in (5.2). Its last digit is in `{1,3,5,7}`, so every code is odd. The
modulus `10^m` is even. A difference of two odd codes is even, and adding a
multiple of the even modulus preserves parity. Hence it cannot be congruent
to `1` or `-1` modulo `10^m`. Cyclic distance at most one therefore forces
congruence zero, hence equality of the two representatives in
`{0,...,10^m-1}`. By (5.2), equality forces `i=j`, and then
`|i-j|=0<m`. Thus

```text
P_(x_FMS)(1,log(4),1).                                     (5.3)
```

Equations (4.6) and (5.3) give, for every `m>=1` and
`1<=N<=4^m`,

```text
Q_(x_FMS)(m,N) <= (2*m+1)*N.                               (5.4)
```

This is the sole survivor and the sole constant-explicit construction
derivation in the report.

## 6. Candidate Sturmian-lacunary: rejected

### Named computable nested decimal

Define an irrational continued fraction

```text
alpha=[0;1,a_2,a_3,...],
q_(-1)=0, q_0=1, q_1=1,
a_(r+1)=2^(q_r^2),
q_(r+1)=a_(r+1)*q_r+q_(r-1) for r>=1.                     (6.1)
```

Let

```text
s_n=floor((n+2)*alpha)-floor((n+1)*alpha) in {0,1},
x_St=0.s_0s_1s_2... in base 10.                            (6.2)
```

Call this the **Sturmian-lacunary decimal**. The continued fraction and each
mechanical digit are computable, so (6.2) is a named computable nested infinite
decimal. The unbounded directive sequence distinguishes it from the excluded
fixed-morphism and automatic mechanisms.

### Exact source card

| field | value |
|---|---|
| source version | S2 arXiv:0809.0603v2, 2008-09-05; DOI `10.1016/j.tcs.2009.04.003` |
| theorem locators | Sturmian complexity, printed p. 2; equation (5), p. 3; Theorem 4.1, p. 7 |
| source theorem | `C(m)=m+1`; if `q_r<=m<q_(r+1)`, then `R(m)=q_(r+1)+q_r+m-1` |
| specialization | mechanical word of the computable slope (6.1) |
| status | source statements `literature-checked`; specialization and rejection `proof sketch` |

S2 attributes Theorem 4.1 to Morse-Hedlund (1940). The delivered locator is
therefore a checked restatement, not an original-source pin; the failed direct
retrieval is recorded in `SOURCE_PINS.md`. The rejection below depends only on
the displayed Sturmian complexity statement, not on treating Theorem 4.1 as
original to S2.

At `m=q_r`, S2 Theorem 4.1 and equation (5) give a length-`q_r` factor with a
complete return of length

```text
R(q_r)+1=q_(r+1)+2*q_r,
```

so the two occurrence starts differ by `q_(r+1)+q_r`. By (6.1), this exceeds
`2^(q_r^2)*q_r`. Thus this point genuinely has explicit superexponential
selected return scales.

**First failed clause:** exponential prefix-factor complexity. S2 states that
there are only `m+1` length-`m` factors in the entire Sturmian language. For
any proposed `K,c>0`, eventually

```text
floor(exp(c*m)) > (m+1)*ceil(K*m).                         (6.3)
```

Applying the fiber argument (3.1) to the first `N_m(c)` starts forces two equal
length-`m` factors at distance at least `K*m`. Their decimal labels are equal,
so `P_(x_St)(K,c,m0)` fails for every choice of constants. Rare long returns do
not provide simultaneous separation of all factors in an exponential prefix.

## 7. Restricted-denominator lane and mandatory rejection map

### S3 applicability card

S3 Theorem 2 gives a nonempty set of reals satisfying variable lower bounds
`||t_n alpha||>delta(n)` under its explicit `H`, window-sum, and initial-sum
conditions. Section 6B gives full Hausdorff dimension for an avoidance set when
`t_n` has the displayed `exp(n^beta)` two-sided growth. These are
`literature-checked` statements at the locators in `SOURCE_PINS.md`.

**First failed clause:** a named computable nested infinite decimal. S3 proves
nonemptiness and dimension, but states no algorithm selecting a member and no
computable digit construction. Therefore no S3 point is retained as a T111
candidate. There is a second, later applicability gap: the source does not
instantiate Theorem 2 for the exact ordered set
`{10^i-10^j:i>j>=0}` with all floor-level constants. A dimension statement
alone cannot fill either gap.

### Required rejection classes

| rejected class | first failed clause |
|---|---|
| finite-only de Bruijn cycles or bounded searches | no one nested infinite decimal satisfying every `m>=m0`; finite verification is only an `experiment` |
| almost-everywhere points | no named computable fixed point; exceptional-set removal is absent |
| subexponential-complexity words | contradict (3.5), before adjacency or carry analysis |
| scalar irrationality or irrationality exponent | controls unrestricted denominator size, not `||(10^i-10^j)x||` uniformly over the exponential two-parameter box |
| previously audited automatic or fixed-morphic words | T91's source statements are `literature-checked`, but its collision formulas are an unverified note; aligned/canonical samples do not give conserved exponential-prefix separation |
| previously audited paperfolding mechanism | T94/T97/T101 are unverified `proof sketch` notes; T101 argues that its full-prefix successor splitting is uniformly obstructed, and none supplies decimal-safe metric separation |
| previously audited Toeplitz mechanism | T103 is source-pinned; its persistent holes give collision lower bounds and no upper remote-separation theorem |
| previously audited Stoneham mechanism | the prior notes use rational-period residue occupancy; exact repetition is the opposite of the required pairwise avoidance |

The survivor is not finite-only: one computable limit simultaneously nests the
de Bruijn prefixes of every order. It is not an almost-everywhere selection,
and parity proves numeric adjacency directly.

## 8. Pi-specific arithmetic transfer premise

The following is a `conjecture` interface stated in restricted-denominator
language. It is not asserted.

For fixed `K>0`, `c>0`, and integer `m0>=1`, let **RD-pi** be:

```text
for every integer m>=m0 and all integers 0<=j<i<floor(exp(c*m))
with i-j>=K*m,
||(10^i-10^j)*pi||_(R/Z) >= 2*10^(-m).                    (8.1)
```

If two labels at such starts had cyclic distance at most one, the reverse
bin estimate (4.4) would make the left side of (8.1) strictly smaller than
`2*10^(-m)`, a contradiction. Reordering unequal starts handles both
orientations. Therefore RD-pi would imply `P_pi(K,c,m0)`, and equations
(4.6)-(4.8)
would then give the corresponding metric sibling count with every constant
displayed.

No audited source proves RD-pi or identifies pi with the FMS-odd decimal. This
is the first failed transfer clause.

The cheapest kill test for proposed constants is finite and exact in logical
form: find one `m>=m0` and certified decimal blocks at
`0<=j<i<floor(exp(c*m))`, `i-j>=K*m`, whose integer codes have cyclic distance
at most one. Equation (4.4) then contradicts (8.1). Equivalently, rigorous
interval arithmetic is a second sufficient test: it may certify
`||(10^i-10^j)pi||<2*10^(-m)`. Such a witness would falsify those constants;
failure to find one is only an `experiment` and cannot prove RD-pi.

## 9. Prior-fingerprint comparison

Verification levels are explicit. Sketch notes are comparison memory only,
not discharged premises.

| prior item | inspected pin and level | normalized comparison |
|---|---|---|
| T37 | `ArtificialStreamObstruction.lean`, SHA `aa0979b629131c6e30c2d8a8dc8c70499ff03d98cd35b2f49841f7669585116c`, `machine-checked` | hand-staged stream repeats every seed in long periodic segments; FMS-odd instead nests one de Bruijn prefix at every order and has no repeated length-`m` factor in its first `4^m` starts |
| T91 | `REPORT.md`, SHA `a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e`; sources `literature-checked`, derivations `proof sketch` | automatic/morphic alignment and canonical paperfolding representatives lose full-prefix multiplicity; FMS-odd uses all starts and literal unique labels |
| T94/T97/T101 | report SHAs `f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10`, `fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e`, `ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e`; all mathematical developments `proof sketch` | finite-state paperfolding collision recurrences and their splitting obstruction are excluded rather than reused |
| T100 | `T100UniversalCharging.lean`, SHA `8fa767cf17deb3ff7b17f94d2d57679122c7cc46e1d9d7a2286846e12ae51787`, `machine-checked` | universally charges strict-short exact-word pairs to remote exact-word pairs at `10^(m/2)` starts; T111 constructs a point with no equal or adjacent remote labels through `4^m` starts and then counts metric pairs |
| T108 | `T108LiteralTransport.lean`, SHA `97f6333ee777b45b842530876ac5e6d29309cfe0987a1ce669690c86c8e5caee`, `machine-checked` | transports T100 through a three-cylinder cover with effective-irrationality and residual-long premises explicit; T111's odd-digit code removes adjacency for its sibling point but supplies neither of those premises for the prescribed orbit |
| T103 | `REPORT.md`, SHA `ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0`, source-pinned | explicit positive-entropy Toeplitz point has persistent hole density and only collision lower bounds; excluded fingerprint |
| T104 | `REPORT.md`, SHA `2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5`, source-pinned | broad cross-domain scout leaves fixed-fiber and named-point gaps; T111 adds a direct explicit symbolic survivor, not a transfer to the prescribed point |
| T105 | `REPORT.md`, SHA `ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f`, source-pinned | additive energy and modular orbit estimates do not reach logarithmic prescribed-character cancellation; T111 uses exact symbolic avoidance instead |

### T109/T110 active-state comparison

At the audit cutoff, the supplied runtime snapshot records active resource
leases for T109 and T110, but the workspace contains no T109/T110 record,
agenda text, candidate card, artifact, or result. The local proof-ledger copy
also contains no refreshable nodes. Thus the first failed comparison clause is
inspectability: assigning either active item a mathematical fingerprint would
be speculation. No T111 argument depends on their content, and no novelty
claim against them is made. The bounded successor below must poll their
completed artifacts before promotion. This runtime gap is recorded in the
problem telemetry, not silently treated as non-overlap.

The normalized T111 fingerprint is now realized for a related model:

```text
totally de Bruijn positive-entropy synchronization
  -> odd-terminal-digit decimal-safe coding
  -> exact remote cyclic-label separation through 4^m starts
  -> Q_x(m,N)<=(2*m+1)N for every N<=4^m.
```

## 10. Replay and boundary

From a directory containing only the delivered artifacts, run

```text
python3 verify_t111.py
sha256sum -c SHA256SUMS
```

The script checks the canonical hash, three PDF hashes, source text anchors,
caps and report markers, and one terminal classification. It also constructs
one deterministic corrected-FMS nested de Bruijn chain through order four and
checks uniqueness and cyclic-neighbor exclusion after odd-digit coding. This
bounded construction is an `experiment`; the universal argument is Sections
3-5.

TERMINAL_VERDICT: develop

The sole bounded successor is to formalize the universal fiber bound, the two
decimal-bin lemmas, the odd-code separation theorem, and the exact (4.6)
ordered-pair count after first polling completed T109/T110 artifacts. The
literature result itself remains a related-model construction pending
independent review.
