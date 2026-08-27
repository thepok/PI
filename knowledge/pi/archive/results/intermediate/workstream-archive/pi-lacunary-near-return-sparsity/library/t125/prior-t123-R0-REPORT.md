# T123: effective named-orbit block control

Audit date: 2026-08-10 UTC.

Claim labels are load-bearing. Statements attributed to S1-S7 in
`SOURCE_PINS.md` are `literature-checked` against the delivered primary PDFs.
The block-count and energy calculations in Sections 2-7 are `proof sketch`
deductions from those statements. `verify_t123.py` performs an `experiment`
checking pins, source anchors, markers, and finite arithmetic; it is not a proof of
the asymptotic deductions.

```text
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 12
SEARCHED_LANE_COUNT: 4
RETAINED_CANDIDATE_COUNT: 4
RETAINED_CANDIDATE_CAP: 4
LOG_DEPTH_CARD_COUNT: 4
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 1
```

Every point below changes the point fixed in the canonical question. Each is
therefore an A13 sibling. The report establishes no property of `pi` and no
conclusion about either program conjecture or decimal factor complexity.

## 1. Immutable question, normalized statistic, and ambiguities

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question counts ordered pairs, includes the diagonal, uses
strict circle distance, fixes base 10 and the point `pi`, and asks

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1, depending on A,n, with
A*n*Q_pi(n,N)<=N^2.
```

T123 does not alter or answer those quantifiers. It audits the A13 sibling
fingerprint in the agenda. For a nonterminating decimal expansion
`x=0.d_0 d_1 ...`, a word `w` of length `m`, and `N>=1`, define

```text
A_x(w;m,N) = #{0<=j<N : d_j...d_(j+m-1)=w},
E_x(m,N)   = sum_(w in {0,...,9}^m) A_x(w;m,N)^2.          (1.1)
```

Thus occurrences overlap, the final start is `N-1`, and a certified prefix
must contain `N+m-1` digits. Equivalently, if `a(w)` is the integer coded by
`w`, then the word cylinder is the left-closed, right-open interval

```text
I_w=[a(w)/10^m,(a(w)+1)/10^m),                            (1.2)
```

and `A_x(w;m,N)=#{0<=j<N:{10^j*x} in I_w}`. All retained
points are irrational, so no dual terminating expansion changes (1.2).
Equation (1.1) counts ordered equal-block pairs and all `N` diagonal pairs.

The following agenda ambiguities are fixed.

1. A primary source is counted once even though both its PDF and a temporary
   `pdftotext -layout` derivative were inspected.
2. A candidate is retained when it has an explicit point and construction and
   is close enough to admit a displayed logarithmic-depth substitution or a
   displayed quantitative rejection. Retention is not endorsement.
3. "Uniform for `m<=kappa*log_10 N`" means one bound holds simultaneously
   for every integer `1<=m<=floor(kappa*log_10 N)` at each declared prefix.
4. A coherent schedule means one increasing sequence of prefixes of one
   infinite point. Independent finite words do not qualify.
5. An effective rate must include both an explicit finite bound and a
   computable onset or modulus delivered by the source or this audit. A
   numerical coefficient with an unextracted "sufficiently large" threshold,
   or an asymptotic frequency with no modulus, does not pass.
6. A source theorem for almost every point or for an invariant measure does
   not name a usable orbit. Ordinary normality alone does not imply any rate
   in the growing word family.
7. A failed sufficient inequality rejects only the cited mechanism at the
   declared parameters. It is not a lower bound for unrelated points.

## 2. Common T7 substitution

Put `q=10^m` and `A_w=A_x(w;m,N)`. Since every start has one word,
`sum_w A_w=N`. If a point has the simultaneous cylinder upper bound

```text
A_w <= N/q + Delta(N),                                    (2.1)
```

then the ordered collision energy satisfies

```text
E_x(m,N) = sum_w A_w^2
         <= (max_w A_w)*sum_w A_w
         <= N^2/10^m + N*Delta(N).                        (2.2)
```

For full interval discrepancy `D_N`, one may take `Delta=N*D_N`; for star
discrepancy `D_N^*`, subtraction of two anchored intervals gives
`Delta=2*N*D_N^*`.

The staged T7 Lean module, SHA-256
`cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c`,
defines the same ordered, diagonal-inclusive sum of squared half-open decimal
cylinder occupancies. Its machine-checked theorem
`piCylinderCollisionEnergy_le_Q_pi_le_three_mul` gives, for the fixed pi
orbit only, `E_pi<=Q_pi<=3E_pi`. Here (2.2) is used only for sibling points;
no T7 fixed-point premise is imported.

The random-shape benchmark used below is

```text
E_x(m,N) <= C*(N + N^2*10^(-s*m))                         (2.3)
```

with fixed `0<s<=1`. The restriction `s<=1` is necessary because the
diagonal-inclusive energy is always at least `N^2/10^m`. If
`m<=kappa*log_10 N`, then
`N^2*10^(-s*m)>=N^(2-s*kappa)`. Every absorption below displays the condition
on `s*kappa` rather than hiding it in big-O notation.

## 3. C-UG: lexicographically selected Eulerian decimal

### 3.1 Source, point, construction, and endpoints

S1 printed pp. 167-168 defines the de Bruijn graph `B(b,k)`, identifies an
Eulerian path in `B(b,k)` with a Hamiltonian path in `B(b,k+1)`, and names the
numbers obtained by iterating `Ext` Eulerian numbers. Theorem 3 and its
algorithm, printed pp. 171-172, extend an order-`k` Hamiltonian prefix to an
order-`k+1` one for the stated alphabet range; decimal `b=10` is inside it.

Make the source's nondeterministic finite algorithm canonical: start with
`0123456789`; at each stage enumerate all finite valid outputs of `Ext` and
choose the lexicographically least. Call the unique resulting decimal point

```text
x_UG = 0.e_0 e_1 e_2 ... .                                (3.1)
```

This name is T123's canonical specialization, not terminology claimed from
S1. The finite graph search terminates by S1 Theorem 3. To compute `r` digits,
run stages until `10^n+n-1>=r`; hence (3.1) is a computable point with an
explicit convergence modulus `10^(-r)` from the first `r` digits.

At stage `n>=1`, the source prefix has length `10^n+n-1` and its `10^n`
overlapping length-`n` blocks at starts `0,...,10^n-1` are all distinct.
Use the coherent schedule

```text
N_n=10^n,  inspected endpoint=N_n+n-2,  prefix length=N_n+n-1. (3.2)
```

### 3.2 Exact growing-depth substitution

For every `1<=m<=n` and every decimal word `w` of length `m`, exactly
`10^(n-m)` of the distinct length-`n` words begin with `w`. Therefore

```text
A_(x_UG)(w;m,N_n)=10^(n-m)=N_n/10^m,                      (3.3)
E_(x_UG)(m,N_n)=10^m*(N_n/10^m)^2=N_n^2/10^m.             (3.4)
```

This is simultaneous for every

```text
1<=m<=log_10(N_n), so kappa=1 and s=1 in (2.3).           (3.5)
```

There are no clasp or right-end losses: the source's extra `n-1` symbols are
exactly what makes all `N_n` starts legal. Equations (3.3)-(3.5) are a proof
sketch consequence of the Hamiltonian-prefix statement, not S1's fixed-depth
normality theorem.

## 4. C-LEV: Levin's explicit Pascal point in base 10

### 4.1 Source, point, construction, and endpoints

S2 Theorem 2, printed pp. 100-101, fixes any integer `q>=2`. Write
`n=sum_j e_j(n)q^(j-1)`, reduce Pascal's triangle modulo 2 to `p_(i,j)`, and
put

```text
d_i(n) = sum_j p_(i,j)e_j(n) mod q,  0<=d_i(n)<q.          (4.1)
```

At stage `r>=1`, concatenate the `2^r` digits
`d_1(n)...d_(2^r)(n)` for all `0<=n<q^(2^r)`, in increasing `n`, and then
concatenate stages. The source formula (9) gives the exact stage offsets

```text
n_1=0,  n_r=sum_(1<=u<r) 2^u*q^(2^u).                     (4.2)
```

Set `q=10` and call the resulting source-defined point `x_LEV=alpha_10`.
Equations (4.1)-(4.2) are a terminating digit algorithm. On input digit
precision `R`, enumerate stages until their cumulative length reaches `R`;
the resulting rational truncation has error at most `10^(-R)`.

The orbit uses starts `0,...,N-1` and half-open cylinders. S2 defines star
discrepancy with the same starts and anchored intervals `[0,gamma)`. Its
Theorem 2 gives `D_N^*=O((log N)^2/N)` for every `N>=10`.

S2 also exposes an effective finite rate. Corollary 2, formulas (54)-(55),
bounds a partial stage by `5*q*2^(2r)` and a completed stage by `5*2^r` in
anchored count error. The final proof, printed p. 110, has

```text
2^r <= 2*log_q N.                                         (4.3)
```

Thus summing completed stages and the final partial stage gives the explicit,
deliberately coarse bound

```text
N*D_N^* <= 10*log_q N + 20*q*(log_q N)^2,  N>=q.          (4.4)
```

The source prints the sharper big-O conclusion; (4.4) is T123's proof-sketch
extraction from its displayed constants. S3 Theorem 1, preprint pp. 2-3,
independently identifies these stages as nested perfect necklaces. S4
Theorem 2, preprint pp. 3-4, gives a general explicit finite discrepancy
bound for concatenated nested semi-perfect necklaces. S3-S4 corroborate the
finite mechanism but are not needed as hidden premises for (4.4).

### 4.2 Logarithmic-depth substitution

By subtracting two anchored counts, every word and depth satisfy

```text
Delta_LEV(N)=20*log_10 N+400*(log_10 N)^2,                 (4.5)
|A_(x_LEV)(w;m,N)-N/10^m| <= Delta_LEV(N),  N>=10.        (4.6)
```

Equations (2.2) and (4.6) give, simultaneously for every `m>=1`,

```text
E_(x_LEV)(m,N)
 <= N^2/10^m + N*(20*log_10 N+400*(log_10 N)^2).          (4.7)
```

Fix `0<kappa<1`. For every
`1<=m<=floor(kappa*log_10 N)`, the second term in (4.7) is
`o(N^(2-kappa))`, so eventually

```text
E_(x_LEV)(m,N) <= N^2/10^m + N^2*10^(-m).                 (4.8)
```

More generally (2.3) follows whenever `0<s<=1` and `s*kappa<1`. At the joint endpoint
`s*kappa=1`, the displayed polylogarithm is not absorbed into the `N` term;
that endpoint is not claimed.

## 5. C-ABS: square-root-discrepancy orbit, threshold rejection

### 5.1 Source, point, construction, and endpoints

S5 Theorem 1, preprint p. 2, constructs one absolutely normal number `x` and
states, for every integer `b>=2`,

```text
D_N(({b^j*x})_(j>=0)) <= 3433*b/sqrt(N),  N>=N0(b).       (5.1)
```

The discrepancy is over all half-open intervals `[alpha_1,alpha_2)`, and
starts are `0,...,N-1`. Printed pp. 7-9 define computable nested binary
intervals `Omega_k`; printed p. 10 completes the inductive selection, and
Section 4.1, pp. 13-14, selects the leftmost dyadic
subinterval outside the finite bad sets. Their intersection has one point.
Call that source point `x_ABSS`. To compute its first `R` binary digits, run
through step `max(100,ceil(log_2 R))`; the maximum accounts for S5's
initialization `Omega_1=...=Omega_99=(0,1)`. S5 proves an
exponential-in-`R` operation bound.
The dyadic interval gives an explicit convergence modulus `2^(-R)`.

The theorem does not print a numerical `N0(10)` or an algorithm for it, and
its proof invokes several "sufficiently large" thresholds. The point
algorithm does not by itself compute a discrepancy modulus. T123 therefore
does not promote (5.1) to an effective all-prefix schedule: C-ABS is not
certified to meet the strict effective-rate requirement in this audit. This
is an audit-level applicability failure, not a proof that no threshold can be
extracted from a finer analysis of S5.

### 5.2 Logarithmic-depth substitution

At decimal base `b=10`, (5.1) directly gives, for every word and depth,

```text
Delta_ABSS(N)=34330*sqrt(N),             N>=N0(10),        (5.2)
E_(x_ABSS)(m,N) <= N^2/10^m + 34330*N^(3/2), N>=N0(10).  (5.3)
```

Fix `0<kappa<1/2`. Uniformly for every
`1<=m<=floor(kappa*log_10 N)`, the second term is
`o(N^(2-kappa))`; hence eventually

```text
E_(x_ABSS)(m,N) <= N^2/10^m + N^2*10^(-m).                (5.4)
```

As a noneffective eventual model calculation, (2.3) follows for `0<s<=1` and
`s*kappa<=1/2` because its constant `C` may absorb `34330`; the
unit-coefficient display (5.4) uses the strict range `kappa<1/2`. This does
not repair the missing effective `N0(10)`. The card is retained as the
fixed-point lacunary-dynamics rejection: unlike an almost-everywhere theorem,
S5 outputs one computable orbit and a pointwise eventual rate, but not the
effective threshold required here. Its construction uses finite bad-set
selection, not a game-theoretic avoidance theorem.

## 6. C-TM: decimal Thue-Morse Mahler point, rejected

### 6.1 Point, construction, endpoint convention, and source rate gap

S6 defines the Thue-Morse fixed point `t=t_0t_1...` of the uniform morphism
`0->01`, `1->10` (its `b=m=2` specialization). Equivalently,

```text
t_(2n)=t_n,  t_(2n+1)=1-t_n.                              (6.1)
```

Retain the decimal point

```text
x_TM=sum_(n>=0) t_n*10^(-(n+1))=0.0110100110... base 10.  (6.2)
```

On input `R`, parity of the binary digit sum computes each `t_n`, so the
first `R` decimal digits and an error at most `10^(-R)` are effective. If
`F(z)=sum_(n>=0)t_n*z^n`, splitting even and odd indices in (6.1) gives the
functional equation

```text
F(z)=(1-z)F(z^2)+z/(1-z^2),  x_TM=F(1/10)/10.             (6.3)
```

This is the Mahler/functional-equation lane. S6 Theorem 2.4 and Example 4.2,
preprint pp. 3 and 6-7, give algorithms for limiting factor frequencies, but
no finite-`N` modulus uniform in growing depth. The missing effective upper
rate alone blocks the requested positive certificate.

### 6.2 Displayed quantitative rejection

S7 preprint p. 3, immediately after Theorem 2, records
`p_TM(m)-p_TM(m-1)<=4`, where `p_TM(m)` is the number of distinct length-`m`
factors. Since `p_TM(1)=2`,

```text
p_TM(m)<=4m-2.                                             (6.4)
```

Only these words can have nonzero occupancy. Cauchy-Schwarz, for every
`N,m>=1`, gives the effective finite obstruction

```text
E_(x_TM)(m,N) >= N^2/p_TM(m) >= N^2/(4m-2).               (6.5)
```

At `m=floor(kappa*log_10 N)` for any fixed `kappa>0`, (6.5) is
`Omega_kappa(N^2/log N)`. For every fixed `s>0`,

```text
N + N^2*10^(-s*m) = O(N+N^(2-s*kappa))
                   = o(N^2/log N).                        (6.6)
```

Thus C-TM quantitatively fails (2.3) for every positive `s*kappa`. Exact
limiting factor frequencies cannot repair its linear word-family size. This
is a rejection of this automatic/Mahler point, not of all functional-equation
constants.

## 7. Four-card summary and exclusions

| card | lane | named point | construction | effective rate and range | T7-shaped result |
|---|---|---|---|---|---|
| C-UG | symbolic entropy/collision | `x_UG`, lexicographic Eulerian decimal | finite de Bruijn graph extension | exact (3.3), `N_n=10^n`, all `1<=m<=n`, endpoint `N_n+n-2` | exact `E=N_n^2/10^m`, `kappa=s=1` |
| C-LEV | structured exponential sums | Levin `alpha_10` | Pascal-mod-2 digit matrices, (4.1)-(4.2) | (4.5)-(4.6), every `N>=10`, all `m`; coherent schedule is every prefix | (4.8) for `kappa<1`; (2.3) for `0<s<=1`, `s*kappa<1` |
| C-ABS | fixed-point lacunary dynamics | S5's unique `x_ABSS` | leftmost nested dyadic interval after initialization through step 99 | source gives `34330/sqrt(N)` for `N>=N0(10)`, but no effective `N0(10)` | reject strict effectivity; noneffective model substitution has `0<s<=1`, `s*kappa<=1/2` |
| C-TM | Mahler/functional equation | decimal Thue-Morse `x_TM` | parity/morphism recurrence | no finite upper modulus in S6; exact lower obstruction (6.5) for all `N,m` | reject by (6.6) for every `s*kappa>0` |

The positive cards are not retained because they are merely normal. They are
retained because they have one named computable point, one coherent prefix
schedule, and a depth-uniform finite bound. The following nearby mechanisms
were excluded rather than renamed:

1. Ordinary normality and Champernowne-type fixed-depth convergence do not
   supply a uniform modulus over `10^m` growing words.
2. Measure-only genericity and almost-everywhere lacunary laws name no point.
3. Renewal tails without a named path were already separated in T120 and do
   not upper-bound overlapping word collisions.
4. Game-theoretic avoidance, including T116's avoidance card, targets
   separation rather than uniform block frequencies and is outside this scout.
5. Global-L2 existence arguments without an effective selector do not output
   the required orbit. S5 passes this named-point selector screen because it
   gives a deterministic leftmost-cell algorithm, but still fails T123's
   strict rate screen because this audit did not extract its onset.
6. Online vector balancing was not searched or imported.

## 8. Comparison with T2, T116, T120, T121, and T122

Verification levels are part of the comparison. No proof-sketch deduction
from a prior report is used as a discharged premise.

| comparator | C-UG | C-LEV | C-ABS | C-TM |
|---|---|---|---|---|
| T2, Lean SHA `1f0a50bc...`, machine-checked sibling theorem | T2 turns full normality into eventual near-return sparsity but has no rate uniform in growing depth; C-UG supplies exact coherent finite prefixes | C-LEV strengthens the input from asymptotic normality to explicit all-prefix discrepancy | C-ABS supplies an explicit point and square-root rate, while T2 needs only qualitative normality | C-TM is not normal and its linear factor complexity quantitatively separates it from T2's premise |
| T116 report SHA `573011bd...`, literature-checked sources and proof-sketch deductions | Closest to T116 C-FMS, but C-UG uses all ten symbols and exact uniform cylinder energy; C-FMS uses four odd digits to force diagonal-only metric returns. Both are artificial computable siblings | Unlike T116 C-RS avoidance, C-LEV controls every cylinder occupancy rather than forbidding decimal differences | C-ABS selects a point by nested bad-set removal, but unlike C-RS it proves discrepancy, not individual difference avoidance; it is not a Schmidt game | T116's selected points have strong separation; C-TM instead has forced collision concentration |
| T120 report SHA `8b375d1c...`, literature-checked sources and proof-sketch deductions | Gives a named deterministic path and exact word counts, repairing precisely the named-point/rate defects that killed renewal cards | All-prefix deterministic discrepancy replaces stationary expectation and fixed-observable mixing | Named computable orbit and uniform interval theorem replace measure-generic renewal behavior | Confirms T120's warning: limiting factor frequencies without a growing-depth finite modulus are insufficient; (6.5) is stronger negative data |
| active T121 | No T121 agenda, artifact, source pin, or result was staged; only an operational resource lease appears in `orchestrator-input.json`. Therefore no mathematical overlap or separation can honestly be asserted for any card | same availability boundary | same availability boundary | same availability boundary |
| active T122 | No T122 agenda, artifact, source pin, or result was staged; only an operational resource lease appears in `orchestrator-input.json`. Therefore no mathematical overlap or separation can honestly be asserted for any card | same availability boundary | same availability boundary | same availability boundary |

The T121/T122 rows are explicit comparisons with the only inspectable state:
both were active concurrent leases, but their fingerprints and verification
levels were unavailable. Inventing agenda content would violate citation
discipline. `SEARCH_LOG.md` records the negative inventory and paths searched.

T107 is also not silently imported. Its staged machine-checked module, SHA
`45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`,
requires separate boundary and Fourier row budgets over triangular depth
families. A cylinder discrepancy estimate alone does not identify its
collected Fourier remainder. T123 therefore uses the permitted T7 energy
substitution and makes no T107 triangular-defect claim.

## 9. Separately labeled pi-specific transfer premise

**PI-SPEC (`conjecture`, additional pi-specific premise).** There exist a
fixed `kappa>0`, an increasing computable prefix schedule `N_r`, and an
explicit error `Delta_r` such that, for every sufficiently large `r`, every
integer `1<=m<=floor(kappa*log_10 N_r)`, and every decimal word `w` of length
`m`,

```text
|A_pi(w;m,N_r)-N_r/10^m| <= Delta_r,
N_r*Delta_r = o(N_r^2/10^m) uniformly in that triangle.   (9.1)
```

Under (9.1), the elementary calculation (2.2) would give a fixed-pi T7 input.
No source in this scout states (9.1), and none of the constructed sibling
points supplies evidence that `pi` follows its construction. Identifying
`pi` with `x_UG`, `x_LEV`, `x_ABSS`, or `x_TM` would be a much stronger and
unsupported premise. Failure of (9.1) would reject only this transfer format,
not the canonical question.

## 10. Negative map and classification

C-UG is the literal fingerprint survivor: effective specification in the
decimal full shift produces one computable orbit with exact overlapping
block-frequency control through the information-theoretic endpoint on nested
prefixes. C-LEV shows the endpoint can be relaxed to every prefix with a
polylogarithmic count error. C-ABS shows a different computable lacunary
selection route, but this audit leaves the source's eventual threshold unextracted and
its model range loses to `kappa<1/2`. C-TM isolates growing word-family
size as a fatal obstruction: a computable fixed point and exact limiting
frequencies are not enough when only `O(m)` words occur.

These are model classifications only. The missing bridge is not another
normality theorem; it is the separately labeled arithmetic transfer (9.1) for
the prescribed point.

SCOPED_VERDICT: develop

SUCCESSOR: Formalize the C-UG implication from a nested order-`n` decimal de
Bruijn prefix to the simultaneous identities (3.3)-(3.4), including all
overlap endpoints, as an A13 sibling theorem with no fixed-point transfer.

## 11. Replay boundary

From a directory containing only the delivered artifacts, run

```text
python3 verify_t123.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and seven primary-source hashes, PDF magic,
source anchor phrases after fresh `pdftotext -layout` conversion when available,
the source/candidate caps, all four logarithmic-depth cards, all five required
comparison rows, the separate premise and scope markers, exact endpoint and
energy arithmetic on finite instances, and uniqueness of terminal markers.
Those finite checks are experiments only.
