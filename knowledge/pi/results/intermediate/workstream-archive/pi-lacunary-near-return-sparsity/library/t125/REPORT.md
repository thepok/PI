# T125: integer-multiplicative block-collision scout

Search date: 2026-08-10 UTC.

Statements attributed to S1-S5 and identified by exact locators in
`SOURCE_PINS.md` are `literature-checked`. The block-indicator identity,
source substitutions, failed inequalities, and conditional transfer
calculation are `proof sketch` deductions. The replay is an `experiment`: it
checks hashes, source anchors, finite identities, and marker invariants, but it
is not evidence for any asymptotic claim.

```text
PRIMARY_SOURCE_COUNT: 5
PRIMARY_SOURCE_CAP: 12
SEARCHED_DOMAIN_COUNT: 3
RETAINED_CANDIDATE_COUNT: 4
RETAINED_CANDIDATE_CAP: 4
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, normalized scope, and ambiguities

The delivered `canonical_statement.txt` is a byte-exact copy of the local
canonical question. Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, that question fixes the point pi, base 10, strict
circle distance, ordered pairs, and the diagonal in

```text
Q_pi(n,N)=#{(i,j) in {0,...,N-1}^2:
              ||(10^i-10^j)pi||_(R/Z)<10^(-n)}.
```

Its exact open quantifier order is

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N=N(A,n)>=1 with
A*n*Q_pi(n,N)<=N^2.
```

T125 does not alter or answer this question. It studies a binary A13/A14
related model: consecutive sign blocks in the named integer sequence

```text
lambda(n)=(-1)^Omega(n) in {-1,+1},
```

the Liouville function. The candidates concern ordinary integer starts,
logarithmic integer averages, interval-location averages, or shift/dilation
averages. None of those conventions is silently identified with another.

The agenda ambiguities are normalized as follows.

1. `log` in T125's scale `m=floor(kappa*log N)` is the natural logarithm.
   Thus `2^m=N^(kappa*log 2+o(1))`. Changing the logarithm base changes the
   numerical exponent and would be a different calibration.
2. `kappa>0` is fixed before `N->infinity`.
3. There are exactly `N` starts, `n=1,...,N`; a block reads the already-defined
   infinite sequence through `lambda(N+m)` and loses no endpoint.
4. Every block collision is ordered and diagonal-inclusive.
5. A source's fixed correlation order is fixed before its asymptotic variable.
   It is not a theorem at order `floor(kappa*log N)`.
6. A logarithmic average uses weight `1/n`; an interval-location average
   integrates or counts starting locations; a shift average sums additional
   shift parameters. None is an ordinary unweighted prescribed-shift average.
7. A candidate is a normalized theorem mechanism, not a source. S1 supports
   two distinct cards; S2-S3 jointly delimit one logarithmic-correlation card.
8. Failure of an available upper bound is an applicability rejection, not a
   lower bound for the actual Liouville collision statistic.
9. The prior reports are fingerprint comparators. Their source statements and
   proof-sketch deductions retain their original labels.

## 2. Bounded three-domain scout

The search inspected exactly five primary papers and retained exactly four
candidate cards. It stopped without filling either cap.

| Card | Domain | Source input | Mechanism tested |
|---|---|---|---|
| C-AVG | arithmetic correlations / pretentiousness | S1 Theorem 1.1 | ordinary correlations averaged over all ordered shift tuples |
| C-LOG | higher correlations and entropy decrement | S2 Theorem 1.2; S3 Theorem 1.1 | prescribed fixed shifts with logarithmic weight, at order two and every fixed odd order |
| C-SHORT | short structured exponential sums | S1 Theorem 1.3; S4 Theorem 1 and Corollary 2 | first-order short Fourier or mean cancellation, plus fixed-shift two-point separation from one |
| C-HIGH | higher uniformity and symbolic complexity | S5 Corollaries 1.6 and 1.11; Theorem 1.9 | fixed-order local Gowers uniformity, dilation-averaged correlations, and superpolynomial pattern support |

`SOURCE_PINS.md` gives titles, versioned URLs, DOI links, SHA-256 values,
pages, theorem numbers, ranges, and the bounded query log. The five comparator
reports do not count as opened primary literature.

## 3. Complete block-indicator and collision identity

Fix integers `N,m>=1`. For `1<=n<=N`, define the length-`m` block

```text
B_m(n)=(lambda(n+1),...,lambda(n+m)) in {-1,+1}^m.         (3.1)
```

For `w in {-1,+1}^m`, let

```text
A_w(N,m)=#{1<=n<=N:B_m(n)=w},
C_lambda(N,m)=sum_w A_w(N,m)^2.                            (3.2)
```

Thus `C_lambda` is exactly the number of ordered pairs `(n,n')` of starts
whose blocks agree, including every one of the `N` diagonal pairs.

Write `[m]={0,...,m-1}`. For every `S subset [m]`, define the ordinary,
unweighted, prescribed-shift correlation

```text
T_S(N)=sum_(1<=n<=N) product_(j in S) lambda(n+j+1),
T_empty(N)=N,       rho_S(N)=T_S(N)/N.                    (3.3)
```

For every start and word, the full indicator expansion is

```text
1_[B_m(n)=w]
 =2^(-m)*product_(j=0)^(m-1)(1+w_j*lambda(n+j+1))
 =2^(-m)*sum_(S subset [m])
      (product_(j in S)w_j)*(product_(j in S)lambda(n+j+1)). (3.4)
```

After summing over `n`,

```text
A_w=2^(-m)*sum_(S subset [m])(product_(j in S)w_j)*T_S.   (3.5)
```

Walsh orthogonality is

```text
sum_(w in {-1,+1}^m)
 (product_(j in S)w_j)*(product_(j in R)w_j)
 =2^m*1_[S=R].                                             (3.6)
```

Substituting (3.5) into (3.2), including all `2^m-1` nonempty subsets, gives
the exact identity

```text
C_lambda(N,m)
 =2^(-m)*sum_(S subset [m])T_S(N)^2
 =N^2/2^m+2^(-m)*sum_(nonempty S subset [m])T_S(N)^2.      (3.7)
```

No independence or correlation conjecture is used in (3.4)-(3.7). At
`m=floor(kappa*log N)`, the empty-subset term satisfies

```text
m/2^m -> 0.                                                (3.8)
```

Consequently the complete target for this sibling model is exactly

```text
C_lambda(N,m)=o(N^2/m)
iff
2^(-m)*sum_(nonempty S subset [m])rho_S(N)^2=o(1/m).       (3.9)
```

A sufficient, but not necessary, condition is

```text
max_(nonempty S subset [m]) |rho_S(N)|=o(m^(-1/2)).        (3.10)
```

More generally, if a theorem controls a family `G` by
`|rho_S|<=epsilon_N` and only the trivial bound `|rho_S|<=1` is available on
its complement, its literal substitution is

```text
2^(-m)*sum_(S nonempty)rho_S^2
 <=epsilon_N^2+|G^c|/2^m.                                 (3.11)
```

Thus a nonaggregate theorem must leave only `o(2^m/m)` uncontrolled subsets
and must have `epsilon_N^2=o(1/m)`. Every card is tested against (3.7)-(3.11).

## 4. C-AVG: correlations averaged over shift tuples

### 4.1 Exact sourced theorem

S1 PDF p. 2, Theorem 1.1, states that for every natural number `r` and every
`10<=H<=X`,

```text
sum_(1<=h_1,...,h_r<=H)
 |sum_(1<=n<=X) product_(i=1)^r lambda(n+h_i)|
 << r*R(X,H)*H^r*X,                                       (4.1)

R(X,H)=log log H/log H+1/log^(1/3000) X.                  (4.2)
```

The same theorem gives the anchored version with `lambda(n)` and `r-1`
shift parameters, costing `H^(r-1)`. Repetitions in the ordered shift tuples
are allowed. The paper's Section 1.3 makes the unadorned implied constant
absolute and holds other parameters fixed in little-o notation; PDF p. 6
states that the theorem constants are effective. The estimate is an ordinary
unweighted `n`-sum, but it has an additional counting average over every
ordered shift tuple.

### 4.2 Complete substitution

Set `X=N` and `H=m`, which is in the source range for all sufficiently large
`N`. For fixed `r`, every `r`-element subset `S subset [m]` appears exactly
`r!` times among the distinct ordered tuples `(h_1,...,h_r)` after setting
`h_i=j_i+1`. Therefore (4.1) implies

```text
sum_(|S|=r)|T_S(N)|
 << r*R(N,m)*m^r*N/r!.                                    (4.3)
```

Since `|T_S|<=N`, equations (3.7) and (4.3) give the theorem-derived bound

```text
sum_(|S|=r)T_S(N)^2
 <<r*R(N,m)*m^r*N^2/r!.                                   (4.4)
```

The independent trivial estimate is

```text
sum_(|S|=r)T_S(N)^2<=binomial(m,r)*N^2.                   (4.5)
```

Therefore the complete direct substitution, using the better estimate at
every order, would need

```text
D_AVG(N,m)
 =2^(-m)*sum_(r=1)^m
   min(binomial(m,r), C*r*R(N,m)*m^r/r!)
 =o(1/m),                                                  (4.6)
```

where `C` is the absolute implied constant in (4.1). Equation (4.6) is the
first failed inequality. Let `r_0=floor(m/2)`. The ratio of the sourced term
to the trivial term at this order is

```text
C*r_0*R(N,m)*m^r_0*(m-r_0)!/m!.
```

For all large `m`, the product factor in this ratio is at least
`(4/3)^(m/4+O(1))`, while
`R(N,m)>=log log m/log m`; hence the ratio tends to infinity and the minimum
in (4.6) selects the trivial central-order term. Since the largest of the
`m+1` binomial coefficients is at least their average,

```text
D_AVG(N,m)>=binomial(m,r_0)/2^m>=1/(m+1),                 (4.7)
```

which is not `o(1/m)`. Thus even the orderwise optimized direct substitution
does not close (3.9). Separately, at order two the anchored theorem only gives
an `L1` average over `m` possible shifts; extracting the prescribed adjacent
shift does not yield the sufficient pointwise rate (3.10). A single untreated
pair would itself be negligible after the `2^(-m)` normalization, so this last
observation is a source-shape mismatch, not an independent aggregate
obstruction.

Card result: C-AVG is quantitatively rejected. The source estimate is strong
for a typical shift tuple, but its `m^r` tuple volume is too large after every
subset order through `r=m` is inserted. This does not assert that the actual
left side of (3.9) is large.

## 5. C-LOG: logarithmically averaged fixed correlations

### 5.1 Exact sourced theorems

S2 PDF p. 2, Theorem 1.2, fixes natural `a_1,a_2`, integer `b_1,b_2` with
`a_1*b_2-a_2*b_1 != 0`, and any function `1<=omega(x)<=x` tending to
infinity, and proves

```text
sum_(x/omega(x)<n<=x)
 lambda(a_1*n+b_1)*lambda(a_2*n+b_2)/n
 =o(log omega(x)).                                        (5.1)
```

This is exactly order two, with fixed affine forms and qualitative decay.
The little-o may depend on the fixed coefficients and chosen `omega`.

S3 PDF p. 2, Theorem 1.1, proves for every fixed odd natural `r>=1` and fixed
natural affine coefficients

```text
(1/log x)*sum_(n<=x)
 product_(i=1)^r lambda(a_i*n+b_i)/n=o(1).                 (5.2)
```

Remark 1.2 removes nondegeneracy because `r` is odd. Footnote 1 gives the
equivalent moving-window convention normalized by `log omega(x)`. No rate is
uniform in `r` or in growing coefficients. Neither source treats even orders
`r>=4`.

### 5.2 Complete substitution and first failures

The quantities in (5.1)-(5.2) are logarithmically weighted; (3.3) is an
ordinary Cesaro sum. Partial summation runs from an ordinary bound to a
logarithmic bound, not conversely. A terminal interval `(N/2,N]` has ordinary
mass comparable to `N` but logarithmic mass only `log 2`. Thus the useful
pointwise conversion

```text
T_S(N)=o(N/sqrt(m))                                        (5.3)
```

for prescribed `S` is absent even at `S={0,1}`. The source itself describes
the logarithmic estimate as strictly weaker than ordinary Chowla. Condition
(5.3) is sufficient, not necessary: one or polynomially many uncontrolled
coefficients are harmless after the `2^(-m)` normalization. The fatal direct
substitution is instead the exponentially large untreated family below.

There is also a complete subset-order failure independent of that averaging
gap. Grant, counterfactually, perfect ordinary cancellation for every odd
subset and every pair. The unresolved even subsets of order at least four
still number

```text
B_even(m)=2^(m-1)-1-binomial(m,2).                         (5.4)
```

Using the only available bound `|rho_S|<=1` on this full family, (3.11)
requires

```text
B_even(m)/2^m=o(1/m).                                     (5.5)
```

Instead its left side tends to `1/2`. Equation (5.5) is the first failed
all-subset inequality even after granting a stronger average and zero error
on every sourced order. Taking odd order `r` proportional to `m` is outside
S3's fixed-order quantifiers.

Card result: C-LOG is quantitatively rejected because the positive-density
family of untreated even orders survives the complete substitution. The
logarithmic-to-Cesaro gap is an additional averaging mismatch, but is not by
itself fatal for an isolated coefficient. Entropy decrement is a proof
ingredient in S2; it does not supply a Renyi-2 block-collision theorem.

## 6. C-SHORT: short Fourier and first-order interval cancellation

### 6.1 Exact sourced theorems

S1 PDF p. 3, Theorem 1.3, states for every `10<=H<=X`

```text
sup_(alpha in R) integral_0^X
 |sum_(x<=n<=x+H)lambda(n)e(alpha*n)| dx
 <<(log log H/log H+1/log^(1/700)X)*H*X.                  (6.1)
```

The supremum is outside the interval-location integral. It is uniform in the
one common real frequency `alpha` and is a first-order linear statistic.

S4 PDF pp. 1-2, Theorem 1, says there are absolute `C,C'>1`, with
`C'=20000` admissible, such that for every multiplicative
`f:N->[-1,1]`, `2<=H<=X`, and `delta>0`,

```text
|H^(-1)*sum_(x<=n<=x+H)f(n)
 -X^(-1)*sum_(X<=n<=2X)f(n)|
 <=delta+C'*log log H/log H                               (6.2)
```

for all but at most

```text
C*X*((log H)^(1/3)/(delta^2*H^(delta/25))
     +1/(delta^2*(log X)^(1/50)))                         (6.3)
```

integer locations `x in [X,2X]`. Its Corollary 2 states that for every fixed
integer shift `h>=1` there is an unspecified `delta(h)>0` such that

```text
(1/X)*sum_(n<=X) lambda(n)lambda(n+h) <= 1-delta(h)        (6.4)
```

for all sufficiently large `X`. This is one-sided: the corollary does not put
an absolute value around the normalized correlation. It separates the
correlation from `+1`, but does not give decay to zero, a lower bound, or
uniformity in growing `h`.

### 6.2 Complete substitution and first failure

Both (6.1) and (6.2) apply at interval length `H=m`, so interval length is not
the first obstruction. They control one copy of `lambda`, corresponding at
best to singleton Walsh coefficients in (3.7). Corollary 2 concerns fixed
pairs, but not all growing shifts and not decay of their coefficients.

Grant the card much more than either source: suppose every singleton and
every pair correlation in (3.7) vanishes exactly. The still-uncontrolled
subsets of order at least three number

```text
B_short(m)=2^m-1-m-binomial(m,2).                          (6.5)
```

The complete trivial substitution is

```text
2^(-m)*sum_(|S|>=3)rho_S^2
 <=B_short(m)/2^m=1-o(1).                                 (6.6)
```

To prove (3.9), the right side available from (6.6) would have to be
`o(1/m)`, which is false. This is the first failed inequality after granting
perfect versions of all source-shaped singleton and pair information.
A Fourier estimate for `sum lambda(n)e(alpha*n)` does not become an estimate
for every nonlinear product `product_(j in S)lambda(n+j)`.

Card result: C-SHORT is quantitatively rejected by the nonlinear subset
family. Its linear-frequency uniformity and logarithmic interval length do
not repair the missing correlation order.

## 7. C-HIGH: higher Gowers uniformity and symbolic support

### 7.1 Exact sourced theorems

S5 PDF p. 6, Corollary 1.6, fixes an integer `r>=0` and `0<theta<=1` before
the limit and proves, for `H>=X^theta`,

```text
integral_X^(2X) ||lambda||_(U^(r+1)([x,x+H])) dx=o(X).     (7.1)
```

The Gowers norm is normalized as in S5 equation (8). The little-o may depend
on the fixed order and `theta`; no rate is uniform as `r` grows.

S5 PDF p. 11, Corollary 1.11, fixes order `r`, fixed distinct nonnegative
integers `a_1,...,a_r`, and fixed `epsilon>0`, and proves

```text
average_(h<=X^epsilon)
 |average_(n<=X) product_(i=1)^r lambda(n+a_i*h)|=o(1).   (7.2)
```

The source explicitly notes that bounded `h` would amount to Chowla. Thus
(7.2) has an additional dilation average and does not control the prescribed
case `h=1`.

S5 PDF p. 9, Theorem 1.9, defines `s(r)` as the number of length-`r` sign
patterns occurring somewhere in the Liouville sequence and proves

```text
s(r)>>_A r^A for every fixed A>=1.                        (7.3)
```

The implied constant depends on `A`. This is a support-size lower bound with
no frequency, prefix, entropy-rate, or collision upper bound.

### 7.2 Complete substitution and first failures

At T125's scale `H=m=floor(kappa*log X)`, one has `H<X^theta` for every
fixed `theta>0` and all sufficiently large `X`. Thus (7.1) is outside its
sourced interval range before any block substitution. S5 Proposition 1.7
identifies polylogarithmic local Gowers control as a sufficient unsolved input
for logarithmically averaged Chowla, not as a theorem of the paper.

There is also a growing-order obstruction. Grant exact ordinary cancellation
for every subset of order at most one fixed `R`. The unresolved fraction is

```text
B_high(m,R)/2^m
 =1-2^(-m)*sum_(r=0)^R binomial(m,r) -> 1.                (7.4)
```

The complete available bound from (3.11) therefore leaves `1-o(1)`, not
`o(1/m)`. To use fixed-order estimates with `R=m`, one would need explicit
uniform dependencies satisfying the all-order analogue of (3.9); S5 fixes
`R` before `X` and supplies no such dependencies. Equation (7.2) also averages
the dilation instead of selecting every prescribed subset.

Finally, (7.3) cannot upper-bound collision. For any support size `s>=2`, a
probability law may place mass `1/2` on one word and spread the remaining
mass over `s-1` words; its collision probability is at least `1/4` regardless
of how fast `s` grows. The target collision probability is `o(1/m)`. Hence
superpolynomial word support is not a Renyi-2 or min-entropy estimate.

Card result: C-HIGH is quantitatively rejected by the interval range, fixed
correlation order, dilation average, and support-versus-frequency mismatch.
It is not relabeled as the fixed-order Gowers mechanism already screened in
T110.

## 8. Four-card negative map

| Card | Exact averaging | Correlation order | Complete first failed condition | Classification |
|---|---|---|---|---|
| C-AVG | ordinary `n`, plus `L1` over ordered shift tuples | every `r`, but tuple volume `m^r` | optimized `D_AVG=o(1/m)` fails at central order by (4.7) | reject available tuple-average bound |
| C-LOG | logarithmic `1/n`; prescribed fixed affine forms | order two and every fixed odd order | untreated even-order fraction tends to `1/2`, and no Cesaro transfer | reject averaging and order |
| C-SHORT | average over interval location; one common Fourier frequency | first order; fixed-shift pair has only a one-sided upper separation from `+1` | even after zeroing orders one and two, unresolved fraction tends to `1` | reject nonlinear subset gap |
| C-HIGH | interval-location Gowers average or dilation average | separately fixed order | `H=log X` is outside `H>=X^theta`; fixed-order binomial tail tends to `1` | reject range, order, and entropy mismatch |

The source landscape therefore does not supply the fingerprint requested in
positive form:

```text
one named infinite integer-multiplicative sequence
 -> simultaneous ordinary correlations for all nonempty shifted subsets
    through order and shift diameter m=floor(kappa*log N)
 -> complete normalized squared-Walsh error o(1/m)
 -> ordered diagonal-inclusive block collisions o(N^2/m).
```

This is a negative applicability map, not a statement that Liouville fails
the displayed collision estimate. In particular, ordinary two-point Chowla
for the adjacent shifts remains open, and no source here can be promoted from
logarithmic or shift-averaged control to that assertion.

## 9. Required prior-fingerprint comparisons

The six readable reports are vendored byte-exactly. Verification levels are
part of every comparison; no prior proof sketch is used as a discharged
premise.

| Comparator | Pin and level | Normalized fingerprint | Explicit T125 separator |
|---|---|---|---|
| T110 | `prior-t110-REPORT.md`, SHA `4eaa088e...`; sources literature-checked, substitutions proof sketch | base-`q` digital multiplicativity, fixed-order Gowers decay, fixed-degree polynomial phases, and metric lacunary correlations | T125 uses the arithmetically completely multiplicative integer sequence `lambda(n)` and the exact all-subset block expansion. C-HIGH is closed, not retained, because its fixed-order Gowers input repeats T110's quantifier defect. No q-multiplicative digital or nilsequence mechanism is claimed. |
| T117 | `prior-t117-REPORT.md`, SHA `ee697420...`; sources literature-checked, deductions proof sketch | finite Legendre periods, squarefree shifted subset products, complete Weil bounds, pointwise word counts | T125 uses one infinite integer sequence and no finite field, character, trace function, complete-field sum, or prime-indexed period. It does not reuse T117's pointwise all-subset cancellation. |
| T121 | `prior-t121-REPORT.md`, SHA `01b97953...`; sources literature-checked, Walsh/collision deductions proof sketch | aggregate finite-period Walsh-Legendre orthogonality; Parseval squares complete character sums and cancels the subset count | Equation (3.7) is the universal binary identity, but T125 neither assumes a global-L2 discrepancy bound nor imports complete-period character estimates. It substitutes only the sourced integer correlation theorems and records their failure. Thus it is not a restatement of T121's survivor. |
| T122 | `prior-t122-REJECTED-REPORT.md`, SHA `6ea3b779...`; source statements literature-checked, reductions proof sketch; final workflow status rejected for duplicating T121's screened Becher-Carton mechanism | constructed nested-perfect-necklace stream, all-prefix discrepancy, and rejected adaptive/static balancing routes | T125 does not construct a digit stream, use interval discrepancy, or revive C-NPN. The superseded report's `develop` line is not adopted; T122 is treated as rejected. |
| T123 r0 | `prior-t123-R0-REPORT.md`, SHA `3eed8484...`; sources literature-checked, deductions proof sketch, revision requested | explicit de Bruijn/Eulerian and Levin-type decimal points with direct block discrepancy; r0 also screens low-complexity Thue-Morse | T125's named object is an existing arithmetic sequence on the integers, not a constructed real, de Bruijn prefix, nested necklace, direct discrepancy modulus, or automatic fixed point. T123 r0 is a pending-revision comparator, not an accepted theorem. |
| T124 | `prior-t124-REPORT.md`, SHA `461df405...`; source quotations literature-checked, deductions an unverified `proof sketch` | the T124 note argues (unverified) that arithmetic monodromy and all-modulus expansion give ordered collision control for a branching congruence-word model; it records decimal-modulus and deterministic-coding failures and a Rudin--Shapiro Mahler cocycle that freezes modulo `10^m` | Conditional on the note's stated calculations, T124 averages over exponentially many generator words and studies congruence labels. T125 instead averages ordinary integer starts in one fixed completely multiplicative sequence and expands equality into every shifted Liouville correlation. No monodromy walk, congruence quotient, Mahler cocycle, or branching-word spectral gap is used, so T125 does not rename the T124 fingerprint. |

These comparisons also enforce the agenda exclusions: finite-field mechanisms
are T117 territory; fixed-order Gowers/nilsequence mechanisms are T110
territory; assuming aggregate `L2` collision is T121 rather than an input;
constructive balancing is rejected T122 territory; and constructed named
orbits/direct discrepancy belong to T123 r0. No candidate is renamed to evade
those boundaries.

## 10. Separately labeled structural pi-transfer hypothesis

The following is a `conjecture` stated only to expose what an arithmetic
transfer would have to contain. It is not asserted and no source supplies it.

**PI-LIOUVILLE-FACTOR (conjectural transfer; not asserted).** There are fixed
`kappa>0`, increasing integers `N_r`, decimal depths `d_r->infinity`, explicit
permutations `sigma_r` of `{1,...,N_r}`, exceptional sets
`E_r subset {1,...,N_r}`, and explicitly specified maps

```text
Phi_r:{-1,+1}^(m_r)->{0,...,9}^(d_r),
m_r=floor(kappa*log N_r),                                  (10.1)
```

such that:

1. `Phi_r` is injective;
2. `d_r*|E_r|/N_r -> 0`;
3. for every `n notin E_r`, the actual length-`d_r` decimal block at pi start
   `n-1` equals `Phi_r(B_(m_r)(sigma_r(n)))`;
4. the formulas for `sigma_r` and `Phi_r` are fixed arithmetically before
   inspecting the empirical pi blocks, rather than selected to fit them; and
5. the Liouville model independently satisfies
   `d_r*C_lambda(N_r,m_r)/N_r^2 -> 0`.

This is structurally stronger than merely postulating decay of a collision or
Fourier statistic: it supplies an explicit almost-everywhere factor coding
that determines every decimal-block indicator from the model block and
transports the equality relation. It is not T7 or T67 with a new name. Clause
5 is not supplied by this scout; it records the independent model theorem
that would still be needed.

Define `E_decimal_pi(d,N)` here only as the ordered, diagonal-inclusive count
of pairs among starts `0,...,N-1` whose left-closed/right-open length-`d`
decimal words agree, using the nonterminating decimal expansion. This is an
exact-word sibling statistic, not the canonical circle-distance count.

Among starts outside `E_r`, injectivity gives

```text
equal decimal blocks => equal Liouville blocks.
```

Ordered pairs touching `E_r` number at most `2*N_r*|E_r|`. Therefore the
conditional bookkeeping is

```text
E_decimal_pi(d_r,N_r)
 <=C_lambda(N_r,m_r)+2*N_r*|E_r|,
d_r*E_decimal_pi(d_r,N_r)/N_r^2 -> 0.                     (10.2)
```

Equation (10.2) is conditional proof-sketch bookkeeping only. It is not a
conclusion about the prescribed point and is not upgraded to the canonical
circle-distance statistic.

**Cheap closure test.** Any concrete proposal must print formulas for
`sigma_r` and `Phi_r`. On a finite prefix, one pair of nonexceptional starts
with the same Liouville block but different decimal blocks disproves the
existence of a single `Phi_r` satisfying clause 3; one pair with different
Liouville blocks but the same decimal block disproves injectivity. A mismatch
rate not `o(1/d_r)` rejects clause 2 for that proposal. Passing finite tests is
only an `experiment`.
Merely proposing the desired collision inequality, T7/T67 decay, or an
arbitrary post-hoc lookup table fails clause 4 immediately and closes that
renamed frontier without a successor.

## 11. Replay, labels, and endpoint

From a directory containing only the sixteen delivered files, run

```text
python3 verify_t125.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical, five source-PDF, and six comparator-report
hashes; PDF magic and page-local theorem anchors after fresh
`pdftotext -layout` conversion; bibliographic and cap markers; the exact
finite Walsh collision identity on a bounded Liouville prefix; finite
subset-family identities; presence of all four cards and six comparator rows;
and the transfer, verdict, successor, and scope markers. These are finite
spot checks and transcription checks, not proofs of the asymptotic deductions
or transfer logic.

No bounded successor is proposed. A new literature task would only be
justified by a theorem with ordinary prescribed-shift control uniform for
almost all of the `2^m` Walsh family at `m` proportional to `log N`. None is
present here.

SCOPED_VERDICT (1/1): **CLOSE.** At the strength and averaging conventions of
the five inspected primary sources, integer-multiplicative Liouville results do
not yield logarithmic-depth ordered block-collision control. The first losses
are explicit: exponential ordered-shift volume for C-AVG, logarithmic weight
and untreated even orders for C-LOG, nonlinear subset products for C-SHORT,
and interval range plus fixed order for C-HIGH. This closes only the bounded
T125 fingerprint scout and makes no claim about fixed pi, C1, or C2.
