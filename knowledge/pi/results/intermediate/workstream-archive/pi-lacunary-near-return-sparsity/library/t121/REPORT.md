# T121: aggregate word-collision L2 scout

Search date: 2026-08-10 UTC.

Statements attributed to the seven pinned primary papers are
`literature-checked`. The collision identities, source substitutions, and
transfer calculations below are `proof sketch` deductions. The replay is an
`experiment`: it checks finite identities, arithmetic, hashes, and package
invariants, but is not evidence for an asymptotic theorem. The one prescribed-
point transfer in Section 10 is a `conjectural transfer` and is not asserted.

```text
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 12
SEARCHED_DOMAIN_COUNT: 4
RETAINED_CANDIDATE_COUNT: 4
CANDIDATE_CAP: 4
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 1
```

This is a related-model mechanism report. It makes no fixed-pi, C1, or C2
claim.

## 1. Provenance, exact scope, and ambiguities

The canonical statement has no external source URL. It is the local question
formulated by this system on 2026-07-22. The delivered
`canonical_statement.txt` is byte-exact and has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It defines, for integers `n,N>=1`,

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are retained, the circle cutoff is
strict, and the open quantifier order is

```text
for every A>=1 there exists n0>=1 such that for every n>=n0
there exists N=N(A,n)>=1 with A*n*Q_pi(n,N)<=N^2.
```

T121 does not alter this statement. Every candidate below changes the point,
base, sequence family, or sampling convention and is therefore an A13/A14
sibling or mechanism model.

The agenda's ambiguous terms are fixed as follows.

1. A source is counted once even though a PDF may have been converted to text
   temporarily for inspection.
2. A candidate is one normalized mechanism card, not one source or one
   parameter value.
3. A linear word of length `m` in a finite digit string of length `N` has
   exactly `M=N-m+1` legal starts. No padding or wraparound is allowed.
4. A cyclic word has one start at every element of its period; all indices in
   that card are explicitly reduced modulo the period.
5. Orbit-prefix cards use all starts `0<=j<N` and look ahead in the infinite
   expansion. Thus their mass is `N`, not `N-m+1`.
6. Every collision energy is ordered and diagonal-inclusive.
7. A displayed implication to the T7 *shape* for another point or base remains
   a sibling result. It is not a statement about the prescribed orbit.
8. No result is called novel. The source cap is too small for a novelty claim.

## 2. Exact T6/T7 and T107 targets

The machine-checked T6 file `CylinderCollision.lean`, SHA-256
`ff8327cfcc73207141b84d6f35ecb4e66345d82c227facd2d37e1034340c44f6`,
defines half-open decimal-cylinder masses and their squared-mass sum at lines
140--147. Its theorem `cylinderCollisionEnergy_smallBall_comparison`, lines
419--426, places closed small-ball mass between one and three times cylinder
energy.

The machine-checked T7 file `FiniteCylinderEnergy.lean`, SHA-256
`cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c`,
uses starts `Fin N={0,...,N-1}` and half-open decimal codes. Lines 28--47 define
the fibers and

```text
E_pi(n,N)=sum_(w in {0,...,9}^n) A_w(n,N)^2.
```

Lines 126--171 identify this with ordered equal-factor pairs. Lines 292--344
give

```text
E_pi(n,N) <= Q_pi(n,N) <= 3*E_pi(n,N).
```

Lines 346--386 state the weakest literal finite-energy frontier:

```text
for every A>=1 there exists n0>=1 such that for every n>=n0
there exists N>=1 with A*n*E_pi(n,N)<=N^2.                 (T7)
```

No pointwise estimate for each word is required by T7.

For comparison only, machine-checked T107
`T107AveragedTriangularFejer.lean`, SHA-256
`45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`,
lines 31--69 and 88--113, makes a row good only when both its boundary load and
Fourier remainder pass the literal T64 budgets. Lines 150--160 require an
averaged positive-density triangle on one prefix family. None of F-LEG,
F-NECK, F-ST, or F-AUT below
controls that boundary statistic, so every quantitative substitution is made
against T7 rather than disguising a collision estimate as T107.

## 3. Universal collision/variance identity

Fix an alphabet of size `b`, a finite set `J` of legal starts of cardinality
`M`, and a word label `W_j in {0,...,b-1}^m` for each `j in J`. Define

```text
A_w = #{j in J: W_j=w},
Delta_w = A_w-M/b^m,
C_m = sum_w A_w^2.
```

Every start has exactly one label, so

```text
sum_w A_w=M,                 sum_w Delta_w=0.
```

Expanding squares gives the exact identity

```text
C_m = M^2/b^m + V_m,
V_m = sum_w Delta_w^2.                                  (3.1)
```

It counts ordered, diagonal-inclusive equal-word pairs. Formula (3.1) applies
to every card, but each card specifies `J`, `M`, and its endpoints again.

For binary signs `a_j in {-1,1}`, linear starts `J={0,...,M-1}`, and

```text
R_S=sum_(j in J) product_(t in S) a_(j+t),
S subset {0,...,m-1},
```

Walsh expansion and finite Parseval give the stronger exact identity

```text
C_m = 2^(-m) sum_S R_S^2,
V_m = 2^(-m) sum_(S nonempty) R_S^2.                    (3.2)
```

The same formula holds cyclically when every index is read modulo the period.
The significance of (3.2) is that correlations are squared before the `2^m`
subset family is averaged.

## 4. Source ledger and bounded search

Exactly seven primary papers were opened. `SOURCE_PINS.md` records every URL,
DOI, hash, theorem, equation, page, and role.

| ID | Domain | Primary source | Role |
|---|---|---|---|
| S1 | arithmetic character sums / symbolic patterns | Mauduit--Sarkozy (1997) | F-LEG load-bearing complete character bound |
| S2 | arithmetic Fourier analysis | Weil (1948) | F-LEG historical square-root mechanism |
| S3 | symbolic necklaces / explicit dynamics | Hofer--Larcher, arXiv:2211.04212v1 (2022; journal 2023) | F-NECK exact nested-perfect blocks |
| S4 | fixed-point lacunary dynamics | Larcher--Stockinger, arXiv:1803.05236v2 (2018; journal 2020) | F-ST Stoneham close-pair bound |
| S5 | short structured sums / digital cubes | Konieczny, arXiv:1611.09985v2 (2019 journal) | F-AUT fixed-order test |
| S6 | q-multiplicative structured sums | Fan--Konieczny, arXiv:1806.04267v2 (2019 journal) | F-AUT fixed-order test |
| S7 | explicit fixed lacunary point | Becher--Carton, arXiv:1805.03713v1 (2019 journal) | screened pointwise-discrepancy comparator |

The four searched domains were symbolic collision theory, arithmetic/Fourier
analysis, fixed-point lacunary dynamics, and short structured exponential
sums. S1 and S2 are older indispensable sources for the exact conductor bound;
five sources are from 2018--2023 versions or publications. Search stopped at
seven, below the cap twelve. Exactly four cards were retained, at the cap four.

S7 Theorem 1 gives a named explicit point with
`D_N=O_b((log N)^2/N)`. It was screened rather than admitted as a fifth card:
combining the pointwise cylinder bound with
`sum Delta_w^2 <= 2M max_w |Delta_w|` gives T7-shaped decay, but the mechanism
is stronger uniform pointwise discrepancy already represented by T90/T110.

## 5. F-LEG: aggregate Walsh--Legendre orthogonality

### 5.1 Endpoints and exact identities

Let `p` be an odd prime, let `chi_p(0)=0`, and define the binary cyclic word

```text
L_p(x)=1 if chi_p(x)=1, and L_p(x)=0 otherwise,
a_p(x)=2*L_p(x)-1=chi_p(x)-1_(x=0).
```

For `1<=m<p`, starts are all `x in F_p`; additions `x+t` are modulo `p`.
There are exactly `M=p` starts and no deleted endpoints. For
`w in {0,1}^m`, define

```text
A_w(p,m)=#{x in F_p:(L_p(x),...,L_p(x+m-1))=w},
Delta_w(p,m)=A_w(p,m)-p/2^m,
C_LEG(p,m)=sum_w A_w(p,m)^2.
```

Equations (3.1)--(3.2) become

```text
C_LEG(p,m)=p^2/2^m+sum_w Delta_w(p,m)^2
          =2^(-m) sum_(S subset [m]) K_S^2,              (5.1)
K_S=sum_(x in F_p) product_(t in S) a_p(x+t).
```

### 5.2 Sourced theorem and aggregate deduction

S1 p. 374, Lemma 3, equation (4.2), gives for the quadratic character and a
degree-`d` polynomial with a root of odd multiplicity

```text
|sum_(x in F_p) chi_p(f(x))| <= d*sqrt(p).                (5.2)
```

S1 pp. 375--376, equations (6.1)--(6.3), checks the distinct-root condition
for products of shifted linear factors. S2 pp. 205--207 supplies the primary
historical conductor/root-divisor square-root mechanism. The numerical
constant in (5.2) is taken from S1, not reconstructed from S2's image scan.

For nonempty `S subset {0,...,m-1}`, put
`f_S(X)=product_(t in S)(X+t)`. Because `m<p`, its roots are distinct, so
(5.2) applies with `d=|S|=s`. At the exactly `s` values `x=-t`, the true sign
product in `K_S` differs from `chi_p(f_S(x))`; every difference has modulus
one. Therefore

```text
|K_S| <= s*(sqrt(p)+1).                                  (5.3)
```

Using the exact binomial moment

```text
2^(-m) sum_(s=1)^m binom(m,s)*s^2 = m(m+1)/4,
```

(5.1)--(5.3) give the aggregate bound

```text
C_LEG(p,m) <= p^2/2^m + [m(m+1)/4]*(sqrt(p)+1)^2.         (5.4)
```

No maximum over words was taken. In particular, the `2^m` subset family is
cancelled by Parseval's `2^(-m)` normalization.

### 5.3 Logarithmic-depth calculation

Fix `0<kappa<1` and set `m=floor(kappa*log_2 p)`. Since
`2^(-m)<=2*p^(-kappa)`, (5.4) gives

```text
C_LEG(p,m)/p^2
 <= 2*p^(-kappa)+O_kappa((log p)^2/p),
m*C_LEG(p,m)/p^2
 = O_kappa((log p)*p^(-kappa)+(log p)^3/p) -> 0.          (5.5)
```

Thus the cyclic Legendre family passes the finite T7-shaped energy threshold
at every fixed `0<kappa<1`. More sharply,

```text
[C_LEG-p^2/2^m]/[p^2/2^m]
 = O_kappa((log p)^2*p^(kappa-1)) -> 0.                   (5.6)
```

The source's range permits `m` growing to this depth. This is a family of
finite binary models, not one fixed decimal orbit.

### 5.4 Relation to T117

T117 uses the same family and source, first bounds every word separately, and
then sums. Its reported relative error has size `m*2^m/sqrt(p)`, restricting
the random-baseline comparison to `kappa<1/2`. Formula (5.1) instead squares
each subset correlation before averaging and reaches `kappa<1`. The source is
reused rather than presented as new literature; the aggregate bookkeeping and
zero correction are the new `proof sketch` deduction.

Card result: retain for development as an aggregate arithmetic model.

## 6. F-NECK: nested-perfect necklace block energy

### 6.1 Sourced finite blocks and endpoints

S3 Definition 1, preprint p. 3, defines a base-`b` `(k,l)`-perfect necklace of
length `l*b^k` by requiring every length-`k` word to occur exactly `l` times
cyclically. It defines nested perfectness at the same locator. S3 Proposition
1, pp. 9--12, proves that its explicit prime-base affine necklace `A_s` is a
`(p^s,p^s)`-nested perfect `p`-ary necklace. Example 2, p. 7, names Levin's
choice of affine parameters. Corollary 2, p. 12, identifies the concatenation
as a fixed explicit normal point and gives its prefix discrepancy bound.

Fix prime base `p`, integers `s>=1` and `1<=t<=p^s`. Let `R=p^s*p^t`, and
define `B_(s,t)` to be the block in the 1-based positions `1,...,R` of `A_s`.
Its start is congruent to `1 modulo R`, exactly as required by S3 Definition
1's nested-perfect clause; it is not an arbitrary subblock. By Proposition 1,
`B_(s,t)` is a `(t,p^s)`-perfect necklace of cyclic length

```text
R=p^s*p^t=p^(s+t).
```

For cyclic starts `J=Z/RZ`, every `w in {0,...,p-1}^t` has

```text
A_w^cyc=p^s,  Delta_w^cyc=0,
C_NECK^cyc=R^2/p^t.                                      (6.1)
```

For the linear representative, legal starts are exactly
`J={0,...,R-t}`, so `M=R-t+1`. Let `r_w` count the deleted cyclic starts with
label `w`. Then `r_w>=0` and `sum_w r_w=t-1`, while

```text
A_w^lin=p^s-r_w,
Delta_w^lin=(t-1)/p^t-r_w.
```

Consequently the endpoint term is exact:

```text
V_NECK^lin=sum_w (Delta_w^lin)^2
 =sum_w r_w^2-(t-1)^2/p^t <= (t-1)^2,
C_NECK^lin=M^2/p^t+V_NECK^lin.                            (6.2)
```

This loses no unrecorded starts: all `R` cyclic starts or all `R-t+1` legal
linear starts are counted, and the `t-1` wrap starts are explicitly charged.

### 6.2 Logarithmic-depth calculation and rejection boundary

Let `q=s+t`, `R=p^q`, and choose `t=floor(kappa*q)` with fixed
`0<kappa<1`, `s=q-t`. The source range `t<=p^s` holds for all sufficiently
large `q`. From (6.2),

```text
t*C_NECK^lin/M^2
 <= t*p^(-t)+t*(t-1)^2/M^2
 = O_kappa((log R)*R^(-kappa)+(log R)^3/R^2) -> 0.         (6.3)
```

This is an exact logarithmic-depth T7-shaped calculation for explicit finite
necklace blocks. It does not by itself imply the prefix frontier for the one
infinite Levin point: the chosen level block begins at a stage-dependent
offset. S3 Theorem 2 can repair prefixes only through a stronger pointwise
discrepancy theorem, which is the already-screened T90/S7 route. Claiming that
the stage block represents the initial orbit prefix would lose the endpoint
and previous-stage mass and is rejected.

Card result: hold as an exact aggregate finite-block model; no prefix transfer
survives without reverting to pointwise discrepancy.

## 7. F-ST: Stoneham close-pair energy

### 7.1 Sourced orbit and endpoint convention

S4 p. 4, Theorem 3, studies the named Stoneham point

```text
alpha_(2,3)=sum_(r>=1) 1/(3^r*2^(3^r))
```

and states that `({2^j*alpha_(2,3)})` is not Poissonian. Its proof on pp.
14--16 chooses every `N=2^w`, uses `s=1`, and proves from the threefold
rational-period residues, with only `O(log N)` final exceptional pairs, the
upper estimate

```text
#{0<=i!=j<N: ||(2^i-2^j)alpha_(2,3)|| <= 1/N}
 <= (2+o(1))*N.                                           (7.1)
```

This proof estimate, not merely the theorem's negative-Poisson conclusion, is
the sourced input.

Use the nonterminating binary expansion of this irrational point. At depth
`m`, starts are all orbit indices `J={0,...,N-1}` with look-ahead in the
infinite expansion, so `M=N`; binary cylinders are half-open. Define

```text
A_w^ST(m,N)=#{0<=j<N: the next m binary digits equal w},
Delta_w^ST=A_w^ST-N/2^m,
C_ST(m,N)=sum_w (A_w^ST)^2
         =N^2/2^m+sum_w (Delta_w^ST)^2.                   (7.2)
```

There is no aligned or deleted-start convention.

### 7.2 Logarithmic-depth calculation

Two equal depth-`w` words place the corresponding orbit points in one
half-open dyadic interval of width `2^(-w)=1/N`, hence their circle distance is
strictly less than `1/N`. Restoring the `N` diagonal pairs in (7.1) gives

```text
C_ST(w,2^w) <= (3+o(1))*2^w.                              (7.3)
```

For `m<=w`, each depth-`m` count is a sum of `2^(w-m)` depth-`w` counts.
Cauchy--Schwarz therefore gives the exact coarsening inequality

```text
C_ST(m,N) <= 2^(w-m)*C_ST(w,N)
           <= (3+o(1))*N^2/2^m.                          (7.4)
```

Set `m=floor(kappa*w)` with fixed `0<kappa<=1`. Then

```text
m*C_ST(m,N)/N^2
 <= (3+o(1))*m*2^(-m)
 = O_kappa((log N)*N^(-kappa)) -> 0.                      (7.5)
```

Because `0<kappa<=1`, the nondecreasing sequence `floor(kappa*w)` has increments
at most one and tends to infinity, so every sufficiently large integer depth
is attained by some `w`. Thus (7.5) has the eventual-depth quantifier required
by the base-two T7 analogue. This is a single named explicit binary point and
an all-start T7 sibling. It
does not transfer across either the point or the base. Its rational-period
mechanism overlaps the Stoneham family audited in T90 and T93/T96/T99/T102;
the present extraction is useful aggregate calibration, not a new fingerprint.

Card result: hold as a sourced all-start model, closed for novelty and transfer.

## 8. F-AUT: fixed-order automatic Gowers bounds

### 8.1 Definitions and sourced range

For either the binary Thue--Morse or Rudin--Shapiro word, take a finite digit
prefix of length `N`, linear starts `J={0,...,M-1}` with `M=N-m+1`, and define
`A_w^AUT`, `Delta_w^AUT`, and `C_AUT` by (3.1). There is no wraparound and all
`M` legal starts are retained. With sign coding, (3.2) defines every fixed-
shift correlation `R_S` exactly.

S5 Theorems A and B, preprint pp. 3--4, state for each separately fixed Gowers
order `s` that Thue--Morse and Rudin--Shapiro have

```text
||f||_(U^s[N]) <= C_s*N^(-c_s),  c_s>0.                  (8.1)
```

The constants and threshold may depend on `s`. S6 Theorems A and B, p. 2,
bootstrap a q-multiplicative Gelfond estimate to every separately fixed
polynomial degree and Gowers order; its p. 9 convention again fixes the order
before the limit. Neither source gives usable bounds for `C_s,c_s,N_s` as
`s` grows.

### 8.2 Explicit logarithmic-depth rejection

There is already a statistic mismatch: a Gowers cube average is not every
fixed-shift correlation `R_S` in (3.2). Grant the candidate the stronger,
optimistic assumption that all terms with `|S|<=s0` are controlled for one
fixed `s0`. The unresolved fraction of the subset family is

```text
B(m,s0)=2^(-m) sum_(d=s0+1)^m binom(m,d)
       =1-O_s0(m^s0*2^(-m)).                              (8.2)
```

At `m=floor(kappa*log_2 N)`, (8.2) tends to one. Trivial bounds
`|R_S|<=M` on that family leave an order-`M^2` contribution in the only
available upper bound for `V_m`, whereas T7 needs `V_m=o(M^2/m)` along selected
prefixes. Equivalently, using (8.1) at growing order would require the
unsourced condition

```text
log C_m-c_m*log N -> -infinity.                            (8.3)
```

The unresolved exponent is `2`, with no logarithmic saving. F-AUT is therefore
quantitatively rejected. This is exactly T110's fixed-order higher-uniformity
fingerprint and is retained here only to show why it cannot be relabeled as
global word-family control.

Card result: close as a duplicate fixed-order mechanism.

## 9. Prior and active fingerprint comparison

Verification levels are load-bearing. Sketch-level notes are comparison memory
only and are never used as discharged premises.

| Comparator | Level used | Normalized fingerprint | T121 comparison |
|---|---|---|---|
| T6/T7 | `machine-checked` | half-open cylinder squared mass; finite all-start energy is equivalent to the canonical frontier up to the factor three | supplies the target only; (3.1) is the exact finite statistic, but no candidate is identified with the prescribed orbit |
| T72 | imported interfaces checked; metric calibration is `proof sketch` | one coupled Haar parameter controls all terminal decimal-ray phases; top-shell thresholds fail almost everywhere on fixed schedules | no terminal ray or Haar averaging occurs; F-LEG/F-NECK use exact word identities, F-ST uses one rational-period point |
| T91 | sources checked; collision deductions `proof sketch`; replay `experiment` | substitution/paperfolding aligned or representative collisions lose all-start mass or multiplicity | F-NECK records cyclic versus linear endpoints exactly; F-ST uses every orbit start; F-AUT's automatic ancestry is disclosed but its statistic is fixed-order signed cubes |
| T104 | sources `literature-checked`; transfers `proof sketch` | ambient/fractal Fourier decay, torus averages, and nonlinear Gibbs dynamics fail at a prescribed fiber | no ambient measure is specialized; F-ST is one named point, while F-LEG is a finite arithmetic family |
| T105 | sources checked; deductions `proof sketch` | additive energy/BSG and modular geometric sums fail at the prescribed character or logarithmic length | F-LEG uses complete character sums for all shifted products, not additive energy or `sum e_p(lambda*10^j)`; F-ST's rational period is a prior Stoneham overlap, not cancellation |
| T110 | sources checked; deductions `proof sketch` | fixed-order Gowers and q-multiplicative polynomial uniformity; metric higher correlations have wrong T107 boundary | F-AUT is the explicit duplicate rejection; F-LEG differs because source conductor cost is valid for every order through `m=O(log p)` |
| T112 | sources checked; transfers `proof sketch`; replay `experiment` | carry local limits and finite-state twisted operators miss the actual path or boundary budget | no carry distribution, stationary law, or T107 boundary premise occurs |
| T115 | sources checked; recurrences `proof sketch`; replay `experiment` | base-ten substitution Riesz recursion has a persistent decimal Fourier ray | word collision Parseval is not a Riesz coefficient recursion; no coefficientwise transfer is attempted |
| T117 | sources checked; collision deductions `proof sketch`; replay `experiment` | pointwise Legendre pattern discrepancy reaches `kappa<1/2` | nearest prior; F-LEG reuses its sources but replaces max-word summation by (5.1), reaching aggregate `kappa<1` |
| T118 | sources checked; order/transfer `proof sketch`; replay `experiment` | private prime powers, exact order, nearest numerator, and short modular orbit fail available sum bounds | no nearest numerator or base-ten multiplicative orbit occurs; F-LEG sums additive shifts of a character over the whole field |
| active T119 | unavailable in the supplied record and knowledge library | no readable artifact; no content inferred | excluded by task identifier only; no premise or novelty claim depends on it |
| active T120 | unavailable in the supplied record and knowledge library | no readable artifact; no content inferred | excluded by task identifier only; no premise or novelty claim depends on it |

The T119/T120 availability check searched the supplied record, its
`knowledge_library`, its `notes`, and readable workspace record names. The only
occurrence was the T121 agenda reference. Treating an absent active artifact as
a substantive fingerprint would violate citation discipline.

## 10. Separate prescribed-point premise

Only F-LEG is selected for possible development. A non-circular transfer would
need arithmetic coding, not the assertion that T7 already holds.

`PI-AGG` (`conjectural transfer`): fix `0<kappa<1`. For every sufficiently
large decimal depth `n`, there exist an odd prime `p`,
`m=floor(kappa*log_2 p)`, a set `B subset {0,...,p-1}`, and an injective map

```text
Phi:{0,1}^m -> {0,...,9}^n
```

such that, for every `j in {0,...,p-1}\B`,

```text
n=O(m),                       n*|B|/p -> 0,
decimalCode_n(10^j*pi)=Phi(W_j^LEG).                      (10.1)
```

This premise is not asserted and no source supplies it. It is structurally
stronger than distributional similarity: it asks for an injective arithmetic
coding of almost every actual start. It is not a renamed collision upper bound.

Conditionally on (10.1), equal decimal codes among good starts imply equal
Legendre words, while ordered pairs touching `B` number at most `2p|B|`.
Hence the `proof sketch` deduction is

```text
E_pi(n,p) <= C_LEG(p,m)+2p|B|,
n*E_pi(n,p)/p^2 -> 0                                      (10.2)
```

by (5.5) and the two rates in (10.1). Formula (10.2) explains why an injective
coding theorem would matter; it does not establish its antecedent or any
property of the prescribed point.

For F-NECK and F-ST, merely postulating that their collision bounds hold for the
prescribed decimal orbit would restate T7 and is rejected. A valid transfer
would first need an independently sourced stage-block or rational-period
representation preserving all starts and endpoint conventions. No such source
was found. F-AUT supplies no candidate estimate to transfer.

## 11. Labels, replay, and endpoint

Source checks: the seven source statements and locators in `SOURCE_PINS.md`.

Proof-sketch deductions: (3.1)--(3.2), (5.1)--(5.6), the linear endpoint
calculation (6.2)--(6.3), the Stoneham collision/coarsening translation
(7.2)--(7.5), the rejection (8.2)--(8.3), and conditional (10.2).

Finite tests: `verify_t121.py` checks the Walsh identity and Legendre bound for
small primes, the generic necklace endpoint identity, coarsening, binomial
mass, source hashes, counts, named comparisons, and endpoint markers. Its
deterministic output is `raw_output.txt`.

Conjectural transfer: only `PI-AGG` in (10.1).

Replay from a directory containing only the delivered files:

```text
python3 verify_t121.py
sha256sum -c SHA256SUMS
```

SCOPED VERDICT (1/1): **DEVELOP THE AGGREGATE LEGENDRE MODEL ONLY.** The
Walsh--character calculation is a genuine forward collision mechanism distinct
from pointwise word discrepancy, low-rank necklace inversion, renewal/rational
periods, fixed-order Gowers control, and ambient Fourier averaging. F-NECK and
F-ST remain useful exact models but overlap known necklace/Stoneham lanes; F-AUT is
quantitatively closed. This endpoint is scoped to related-model mechanism
development and makes no assertion about the prescribed decimal orbit or the
two open program conjectures.

BOUNDED SUCCESSOR (1/1): Formalize the finite Walsh collision identity and the
zero-position correction behind (5.1)--(5.4), with the complete character-sum
estimate supplied as an explicit hypothesis. Do not open another literature
scout or a prescribed-point transfer task.
