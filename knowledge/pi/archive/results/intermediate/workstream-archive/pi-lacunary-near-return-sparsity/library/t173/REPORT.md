# T173: sparse-census control for finite prime concatenations

Audit date: 2026-08-13 UTC.

The statement attributed to Dusart is `literature-checked` against the pinned
primary PDF and exact locator in `SOURCE_PINS.md`. Sections 3--10 are a new
`proof sketch`: every estimate is derived here, but none is machine-checked.
Section 11 is an `experiment` for bounded falsification and artifact integrity,
not proof. Every theorem in this report is `related-model mathematics` about
finite prime-concatenation words. Section 13 is an `unproved transfer`, not an
assertion.

```text
PRIMARY_SOURCE_COUNT: 1
PRIMARY_SOURCE_CAP: 8
CANONICAL_SHA256: cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
FINITE_CHECKS_ARE_PROOF: no
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

## 1. Immutable question, normalized scope, and ambiguities

The canonical question is the local source
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`; the byte-exact delivered
copy is `canonical_statement.txt` and has the displayed SHA-256. It asks

```text
for every integer A>=1, there exists n0>=1 such that every n>=n0
has some N>=1 with A*n*Q_pi(n,N)<=N^2,
```

where `Q_pi` counts strict circle near returns of the fixed decimal orbit of
pi, ordered and with the diagonal included. T173 changes the point and replaces
metric near returns by exact finite-word equality. It is therefore an A10/A13/
A14 sibling and does not answer, weaken, or repair the canonical question.

The agenda's potentially ambiguous conventions are fixed before the argument.

1. `dec(n)` is the ordinary decimal representation of the positive integer
   `n`, with no leading zero.
2. The prime-concatenation prefix ends after the largest prime below `10^d`.
   It contains no decimal point, separator, padding, or cyclic wrap.
3. Digit positions and starts are zero-based. Endpoints are inclusive.
4. Every legal overlapping start is retained, including starts crossing prime
   boundaries. Multiplicity counts occurrences, not distinct words.
5. Energy counts ordered pairs and includes every diagonal pair.
6. A prime interior start has its full block inside one prime. Every other
   legal start is a prime-boundary start, even if it crosses several boundaries.
7. A shell is determined by the digit length of the prime containing the
   start. The cutoff between earlier and mature shells is declared below.
8. All logarithms are natural except `log_10`. Every displayed division in an
   energy inequality is a real/rational inequality, not integer division.

## 2. Prefix, legal starts, endpoint, multiplicity, and energy

Define the prime-concatenation constant directly by

```text
alpha_P = 0.dec(2)dec(3)dec(5)dec(7)dec(11)... .
```

Let `P_d={p prime: p<10^d}`, in increasing order, and define its nested finite
prefix

```text
W_d = concatenation_(p in P_d) dec(p),
L_d = |W_d|.
```

For `1<=m<=L_d`, the legal starts, inclusive endpoint, block, multiplicity,
and energy are

```text
I_(d,m) = {0,1,...,L_d-m},
e(i,m) = i+m-1,
M_(d,m) = |I_(d,m)| = L_d-m+1,
B_(d,m)(i) = W_d[i]...W_d[e(i,m)],
c_(d,m)(w) = #{i in I_(d,m): B_(d,m)(i)=w},
E_(d,m) = sum_(w in {0,...,9}^m) c_(d,m)(w)^2.             (2.1)
```

Expanding the squares gives the exact identity

```text
E_(d,m)=#{(i,j) in I_(d,m)^2:B_(d,m)(i)=B_(d,m)(j)}.       (2.2)
```

Thus the count is ordered and contains exactly `M_(d,m)` diagonal pairs.
Blocks may overlap. The final legal start has endpoint `L_d-1`; the endpoint
deficit relative to all digit positions is exactly

```text
T_(d,m)=L_d-M_(d,m)=m-1.                                  (2.3)
```

For a finite multiset of blocks with profile `a=(a_w)_w`, write
`||a||_2=(sum_w a_w^2)^(1/2)`. If disjoint start classes have profiles
`a^(1),...,a^(r)`, their union has profile sum and therefore

```text
sqrt(E)=||sum_j a^(j)||_2 <= sum_j ||a^(j)||_2.            (2.4)
```

This profile triangle inequality is the aggregation device used below. It does
not assume independence and does not multiply energy by the number of shells.

## 3. BAD-WORD CENSUS T173 (`proof sketch`, independently derived)

This section rederives the finite-word census needed by T173. No definition,
lemma, or conclusion from the unverified T144 note is a premise.

For a decimal word `x` of length `s>=m`, put `q=s-m+1`, let `C_m(x,w)` count
its legal occurrences of `w`, and put

```text
F_m(x)=sum_w C_m(x,w)^2.
```

Call `x` **exceptional** when

```text
F_m(x)>q^2/m^2.                                             (3.1)
```

### 3.1 Residue extraction with endpoints

Partition all `q` starts by residues `r mod m`. Let `q_r` be the number of
starts in row `r`, let `C_(r,w)` be the row multiplicity, and let
`F_r=sum_w C_(r,w)^2`. Since `C_m(x,w)=sum_r C_(r,w)`, Cauchy--Schwarz gives

```text
F_m(x)<=m*sum_(r=0)^(m-1) F_r.                             (3.2)
```

Assume `q>=m`. The row sizes differ by at most one and

```text
sum_r q_r^2 <= ceil(q/m)*q <= 2q^2/m.                      (3.3)
```

If every row had `F_r<=q_r^2/(2m^2)`, then (3.2)--(3.3) would give
`F_m(x)<=q^2/m^2`, contrary to (3.1). Hence an exceptional word has a row with

```text
F_r>q_r^2/(2m^2).                                          (3.4)
```

Starts in one row differ by `m`, so their length-`m` blocks are pairwise
disjoint. Moreover

```text
q_r>=floor(q/m),
q_r*m>=q-m+1=s-2m+2>=s/2                                  (3.5)
```

when `s>=4m`. These inequalities expose every residue and endpoint loss.

### 3.2 Entropy deficit

Fix the heavy row, let `K=10^m`, and let `u=(u_1,...,u_K)` be its empirical
block law. Equation (3.4) says `sum_j u_j^2>1/(2m^2)`. Define

```text
H(u)=-sum_j u_j log u_j,
D(u)=log K-H(u).
```

Let `t=1/(2m^2)`, `S={j:u_j>t/2}`, and `alpha=sum_(j in S)u_j`. Outside `S`,
`sum u_j^2<=(t/2)sum u_j`; inside, `sum u_j^2<=alpha^2`. Thus

```text
alpha>sqrt(t/2)=1/(2m),       |S|<2/t=4m^2.                (3.6)
```

The log-sum inequality on `S` and its complement, followed by
`(1-alpha)log(1-alpha)>=-alpha`, gives

```text
D(u)>=alpha log(alpha*K/|S|)-alpha
    >alpha(log(alpha*K/(4m^2))-1).                         (3.7)
```

For `m>=3`, the right side is minimized on the relevant lower branch at
`alpha=1/(2m)` and exceeds

```text
[m log 10-log(8m^3)-1]/(2m)>1/100.                         (3.8)
```

If `alpha>1/2`, applying log-sum directly with `|S|<4m^2` gives an even larger
bound. For (3.8), the inequality holds at `m=3`; its left side before division
minus `m/50` has derivative
`log 10-3/m-1/50>0`. Thus every heavy row has `D(u)>1/100`.

### 3.3 Type count and census

A row of `q_r` disjoint blocks has at most `(q_r+1)^K<=(s+1)^K` empirical
types. For one type, the multinomial theorem gives at most `exp(q_r H(u))`
block sequences. The `s-q_r m` unselected digits are arbitrary. Therefore the
number of words for which one fixed row is heavy is at most

```text
10^s exp(-q_r/100+10^m log(s+1)).                          (3.9)
```

Using (3.5) and a union over `m` rows proves the census

```text
#Exceptional_(s,m)
 <=10^s exp(-s/(200m)+10^m log(s+1)+log m)                 (3.10)
```

for every `m>=3` and `s>=4m`. This census includes words with leading zero,
so it remains an upper bound when restricted to ordinary `s`-digit integers.

Set

```text
H_m=10^(8m).                                                (3.11)
```

For `s>=H_m`, `log(s+1)/s` decreases, and the elementary endpoint estimate

```text
10^m log(H_m+1)+log m <= H_m/(400m)                        (3.12)
```

holds for every `m>=3` (use `log(H_m+1)<=9m log 10` and
`10^(7m)>=400m(9m log 10+log m)`). Hence (3.10) simplifies uniformly to

```text
#Exceptional_(s,m) <= 10^s exp(-s/(400m)),  s>=H_m.        (3.13)
```

The constants are intentionally coarse. The point is a self-contained
exponential saving strong enough to beat the arithmetic subset size.

## 4. Prime-count comparison (`literature-checked` source plus proof sketch)

Let `A_s=pi(10^s)-pi(10^(s-1))`, the number of `s`-digit primes. Dusart S1,
Theorem 6.9, equation (6.5), states

```text
x/log x*(1+1/log x) <= pi(x)             for x>=599,
pi(x) <= x/log x*(1+1.2762/log x)        for x>1.           (4.1)
```

Subtracting the upper bound at `10^(s-1)` from the lower bound at `10^s`
and simplifying gives, for every integer `s>=4`,

```text
A_s >= 10^s/(2s log 10).                                  (4.2)
```

For inspectability, division by `10^s/(2s log 10)` reduces the required
inequality to

```text
2(1+1/(s log 10))
- (s/(5(s-1)))(1+1.2762/((s-1)log 10)) >= 1.              (4.3)
```

At `s=4` its left side exceeds `1.90`; dropping the positive `2/(s log 10)`
and bounding the subtracted factor by its `s=4` value already leaves more than
one, so (4.3) holds for all `s>=4`.

Every exceptional `s`-digit prime is an exceptional `s`-digit word. Combining
(3.13) and (4.2), the exceptional-prime proportion `theta_(s,m)` obeys

```text
theta_(s,m)
 <=2s log 10 exp(-s/(400m))
 <=eta_m:=2H_m log 10 exp(-H_m/(400m))                     (4.4)
```

for `m>=3` and `s>=H_m`. The last inequality uses that
`x exp(-x/(400m))` decreases for `x>=H_m>400m`.

This is the required exponent comparison: the arithmetic subset has size at
least `10^s/(2s log 10)`, whereas the independently counted bad set has size
at most `10^s exp(-s/(400m))`. Their ratio is the explicit `eta_m`.

## 5. Exact start partition for the prime concatenation

Fix `m>=3`, put `H=H_m`, and take an integer

```text
d>=2H.                                                      (5.1)
```

Every legal start belongs to exactly one of four disjoint classes.

1. **Good-prime interior:** the block is wholly inside a prime of digit length
   `s>=H`, and that prime's own length-`m` energy is at most
   `(s-m+1)^2/m^2`.
2. **Exceptional-prime interior:** the block is wholly inside an exceptional
   prime of digit length `s>=H`.
3. **Prime boundary:** the block crosses at least one boundary `dec(p)|dec(p')`
   between consecutive primes.
4. **Earlier digit-length shell:** the block is wholly inside a prime with
   fewer than `H` digits.

The classes are exhaustive: a block either stays in one prime or crosses a
prime boundary; an interior's prime has digit length below `H` or at least
`H`, and a mature prime is good or exceptional. This partition retains both
orientations only later, through the profile squares in (2.2); starts
themselves are not duplicated.

Write the four start masses as `G,X,B,R`, respectively, so

```text
G+X+B+R=M_(d,m).                                           (5.2)
```

The next four sections separately pay their profile norms.

## 6. GOOD-PRIME INTERIORS

An `s`-digit prime contributes exactly `q_s=s-m+1` interior starts. If it is
good, its profile has norm at most `q_s/m` by definition. Applying (2.4) over
all good primes and all mature shells gives

```text
||c_good||_2 <= sum_(good p) q_(|p|)/m = G/m <= M_(d,m)/m. (6.1)
```

No pooled occupancy profile is assumed: (6.1) is precisely the triangle
inequality, and the right side contains no factor equal to the number of
primes or shells.

## 7. EXCEPTIONAL-PRIME INTERIORS

For any prime, the profile norm is at most its number `q_s` of interior starts.
Within one mature shell every prime has the same `q_s`, so (4.4) says the
exceptional interior mass is at most `eta_m` times that shell's total interior
mass. Summing shells preserves the same proportion. Therefore

```text
||c_exceptional||_2 <= X <= eta_m*M_(d,m).                 (7.1)
```

This is where the word census and prime count meet. It does not assert that
prime digits are random or independent.

## 8. PRIME BOUNDARIES

One fixed digit boundary belongs to at most `m-1` legal blocks. A block that
crosses several boundaries is in the union of these sets and is still counted
at most by the union bound. Thus

```text
B <= (m-1)(pi(10^d)-1) <= m*pi(10^d).                      (8.1)
```

Dusart's upper bound (4.1), with
`1+1.2762/(d log 10)<=2`, gives

```text
pi(10^d)<=2*10^d/(d log 10).                               (8.2)
```

The last shell contains `d*A_d` digits. From (4.2), it contains at least
`10^d/(2 log 10)` digits. Since `m` is negligible compared with this displayed
quantity under (5.1), the legal-start count satisfies the deliberately coarse

```text
M_(d,m)>=10^d/(4 log 10).                                  (8.3)
```

Here is the omitted-digit calculation rather than an asymptotic shorthand.
Condition (5.1) implies `d>=m>=3`. The elementary inequality
`10^d>=4d log 10` holds at `d=3` and its left/right ratio increases with `d`.
Thus `m-1<=d<=10^d/(4 log 10)`. Subtracting the exact terminal deficit `m-1`
from the last-shell digit mass `10^d/(2 log 10)` proves (8.3).

Equations (8.1)--(8.3) yield the full boundary budget

```text
||c_boundary||_2 <= B <= (8m/d)M_(d,m).                    (8.4)
```

This pays ordinary prime boundaries, gaps of every size, transitions between
digit-length shells, and starts crossing multiple small-prime boundaries. No
carry or adjacency premise is hidden.

## 9. EARLIER DIGIT-LENGTH SHELLS and TERMINAL ENDPOINT

All primes with fewer than `H` digits lie below `10^H`. Their concatenation has
fewer than `H*10^H` digits, since there are fewer than `10^H` positive
integers and each has at most `H` digits. Hence the earlier-shell interior
profile obeys, using (8.3),

```text
||c_early||_2 <= R < H*10^H
 <=delta_(m,d) M_(d,m),
delta_(m,d):=4(log 10)H*10^(H-d).                          (9.1)
```

This is a pooled geometric shell budget; no shell count is multiplied into an
energy estimate.

The terminal endpoint is separate. Equation (2.3) gives exactly `m-1` omitted
starts relative to one start per digit. Again by (8.3),

```text
T_(d,m)/M_(d,m)=(m-1)/M_(d,m)
 <=rho_(m,d):=4(log 10)m*10^(-d).                          (9.2)
```

The terminal deficit is not part of `E_(d,m)`; (9.2) records the complete cost
of converting digit-mass estimates to the legal-start convention.

## 10. Final uniform exponent calculation (`proof sketch`)

Combine (2.4), (6.1), (7.1), (8.4), and (9.1):

```text
sqrt(E_(d,m))/M_(d,m)
 <= 1/m + eta_m + 8m/d + delta_(m,d).                      (10.1)
```

Thus, uniformly on the declared growing range

```text
m>=3,             H_m=10^(8m),             d>=2H_m,        (10.2)
```

the finite prime concatenations satisfy the explicit bound

```text
E_(d,m)/M_(d,m)^2
 <=[1/m
    +2H_m(log 10)exp(-H_m/(400m))
    +8m/d
    +4(log 10)H_m*10^(H_m-d)]^2.                           (10.3)
```

Every exponent is visible. At the smallest `d=2H_m`, the last three terms are
at most

```text
2H_m(log 10)exp(-H_m/(400m))
+4m/H_m
+4(log 10)H_m*10^(-H_m),                                  (10.4)
```

which is less than `1/m` for every `m>=3`. For a fully displayed absorption,
`H_m=10^(8m)` satisfies

```text
H_m >= 10000m^2,
log(8mH_m log 10) <= 25m                                  (10.5a)
```

for `m>=3`: the first holds at `m=3`, and the ratio
`H_m/(10000m^2)` is multiplied from `m` to `m+1` by
`10^8(m/(m+1))^2>=10^8(3/4)^2>1`, so it increases. For the second, define
`f(t)=6t-log(8t log 10)`. Direct substitution gives `f(3)>0`, while
`f'(t)=6-1/t>0` for `t>=3`; hence
`log(8m log 10)<=6m`. Also `8 log 10<19`, so

```text
log(8mH_m log 10)
 =8m log 10+log(8m log 10)<19m+6m=25m.
```

This repairs (10.5a) without using the insufficient `7m` estimate. Hence

```text
H_m/(400m) >= 25m >= log(8mH_m log 10),
2H_m(log 10)exp(-H_m/(400m)) <= 1/(4m).
```

Also `H_m>=16m^2` gives `4m/H_m<=1/(4m)`. For the last term, the same
monotonicity calculation as above gives `log(16m log 10)<=6m` for `m>=3`;
therefore

```text
log(16mH_m log 10)<19m+6m=25m<=H_m log 10.
```

Exponentiating the rearranged inequality gives
`4(log 10)H_m*10^(-H_m)<=1/(4m)`. Thus the three terms in
(10.4) total at most `3/(4m)<1/m`. As `d` increases, the exceptional term is
constant while the boundary and early-shell terms decrease, so their sum is
nonincreasing. Consequently the simpler uniform theorem is

```text
E_(d,m)/M_(d,m)^2 <= 4/m^2
for every m>=3 and d>=2*10^(8m).                           (10.5)
```

Equivalently, for every integer `A>=1`, every `m>=max(3,4A)`, and every
`d>=2*10^(8m)`,

```text
A*m*E_(d,m) <= M_(d,m)^2.                                  (10.6)
```

This is an explicit uniform collision bound for one nested family of finite
prefixes of the prime-concatenation constant. It is extremely sparse in the
outer digit-length parameter `d`; optimizing `H_m` is not claimed.

## 11. Finite replay (`experiment`, not proof)

From a directory containing only the delivered artifacts, run

```text
python3 verify_t173.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier checks four immutable/source/archive hashes embedded in its
source, all ten comparator-member hashes, and all source anchors; the separate
`sha256sum -c SHA256SUMS` command checks the eight non-manifest delivered
files. It exhaustively tests the
residue-extraction implication on small decimal words; constructs prime
concatenations through bounded digit lengths and checks legal starts, inclusive
endpoints, ordered energy, interior/boundary exhaustiveness, multi-boundary
union budgets, and the exact terminal deficit; and checks (3.8), (3.12), and
the Dusart subtraction over bounded arithmetic grids. These checks can falsify
indexing, constants, or classifications. They do not prove Sections 3--10 and
are not evidence for any statement about pi.

## 12. Mandatory nonduplication map

Verification levels are load-bearing. Sketch notes below are comparison memory,
not discharged premises. The exact comparator files are byte-vendored as
members of `prior-comparators.tar`; their member hashes are pinned in
`SOURCE_PINS.md` and checked by `verify_t173.py`, so the scope claims can be
checked without repository access.

| item | supplied level and normalized mechanism | exact T173 boundary |
|---|---|---|
| T2 | `machine-checked`; normal decimal streams, including Champernowne, give the every-A sibling near-return quantifiers through eventual block frequencies | T173 imports no normality theorem and proves only exact-block energy for explicit prime cutoffs using a finite bad-word census plus prime counts. T2 prevents advertising this as the first normal-concatenation sibling. |
| T89 | source claims `literature-checked`, deductions `proof sketch`; sparse Kempner and automatic Thue--Morse constants are collision-rich obstruction models; its agenda excluded concatenation-normality reuse | T173 uses neither pure-power truncation nor substitution complexity and makes no normality inference. Its invariant is exceptional prime-word cardinality versus an arithmetic subset count. |
| T111 | source claims `literature-checked`, deductions `proof sketch`; nested de Bruijn odd-digit coding gives remote cyclic-label separation | T173 permits repeated and adjacent blocks and proves an aggregate exact-equality energy bound; there is no de Bruijn extension or parity code. |
| T144 | unverified `proof sketch`; overlapping-block method-of-types census over arbitrary finite words | This is the nearest census overlap. T173 imports no T144 claim and independently derives a different threshold `q^2/m^2`, row threshold `q_r^2/(2m^2)`, entropy constant `1/100`, and exponent (3.10), then performs the new prime-count comparison and concatenation budgets. No novelty claim against the literature is made. |
| T160 | source claims `literature-checked`, deductions `proof sketch`; scouts pair multiplicity and retains a sparse base-2 Champernowne lower-bound diagnostic | T173 supplies a base-10 upper bound over a growing depth range. It uses a profile triangle inequality and exceptional-prime census, not next-recurrence charging or the sourced Champernowne lower bound. |
| T165 | unverified `proof sketch`; direct decimal successor/alignment/carry maximum-multiplicity bound for finite integer concatenations | T173 concatenates primes, where successors and carry intervals are unavailable. It controls each prime as a finite word and pays all boundaries globally; no T165 lemma is used. |
| T167 | source statements `literature-checked`, comparisons `proof sketch`; closes residue-interleaving support entropy and algebraic-power repulsion | T173 uses Renyi-2-to-Shannon deficit only inside a complete finite type count, then compares cardinality with primes. It does not infer collision energy from support entropy or use power repulsion. |
| T169 | unverified `proof sketch`; exact centered first-order energy asymptotic for consecutive-integer Champernowne prefixes | T173 proves only a coarse `4/m^2` upper bound and has no exact successor/carry multiplicity formula. Its theorem/source/mechanism tuple is sparse exceptional-word census + explicit prime density + profile shell aggregation. |
| T171 | source statements are `literature-checked`; substitutions and applicability screens are `proof sketch`; its three-domain scout closes automatic large-correlation, restricted-denominator, and fractal-Fourier candidates and retains none | T173 uses none of those three source/theorem tuples. Its source is Dusart's prime-count estimate and its mechanism is a self-contained exceptional-word census followed by arithmetic-subset density and concatenation budgets, not an automatic-correlation lower bound, rational-approximation restriction, or ambient-measure Fourier decay. |
| T172 | unverified `proof sketch` with finite `experiment`; ordinary fourth-cumulant expansion and an occupancy-only triangle-with-tail falsifier in an iid decimal model | T173 has no cumulant, connected-event, occupancy-only approximation, or iid premise. It directly bounds deterministic ordered block-collision energy of finite prime concatenations. T172's stale internal description of T171 is not imported and supplies no premise. |

The scoped semantic tuple established here is therefore

```text
independent high-energy finite-word census
 + explicit lower density of d-digit primes
 + per-prime interior profiles
 + global boundary and geometric shell budgets
 -> growing-depth exact-block collision bound for prime concatenations.
```

No prior sketch is a premise. Semantic nonduplication is established against
every named artifact by the table's theorem/source/mechanism comparison,
including the refreshed T171 and T172 reports. This is a bounded local
comparison, not a global novelty assertion.

## 13. UNPROVED TRANSFER TOWARD T7/T107 (`conjecture`; not asserted)

The theorem is about the artificial word `W_d`. A transfer toward the
machine-checked T7 symbolic interface for the fixed decimal orbit of pi would
need a pi-specific theorem that, for every sufficiently large depth `m`, places
an actual pi prefix outside an exceptional family with a strong enough
effective count, while retaining exactly the first `N` orbit starts and the
`N+m-1` look-ahead endpoint. Counting most finite words or most primes cannot
locate the one prescribed pi prefix.

For T107, even such exclusion would be insufficient: one must additionally
prove its common-prefix triangular synchronization, active-boundary budgets,
and collected Fourier remainder budgets with the stated constants. Prime
concatenation has literal prime boundaries and arithmetic subset density; pi
has neither structure. Exact block equality is also weaker than canonical
strict metric near return, so the checked symbolic-to-metric comparison must be
used in the correct direction.

No source, proof sketch, or computation here supplies these pi-specific inputs.
There is no fixed-pi, A1, C1, or C2 claim.

## 14. Endpoint

`SCOPED_VERDICT (1/1): HOLD AS MODEL.`

Hold the prime-concatenation family as a related-model example where an
exponentially sparse high-collision census can be compared with an explicit
arithmetic subset and survives interiors, exceptional elements, boundaries,
shell aggregation, and endpoints. The result is the proof-sketch bound (10.3)
and its coarse corollary (10.5), not a claim about pi. `SUCCESSOR (0/1): NONE.`
