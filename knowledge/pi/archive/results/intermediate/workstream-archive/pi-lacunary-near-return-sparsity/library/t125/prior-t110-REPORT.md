# T110: higher-order uniformity scout

Search date: 2026-08-10 UTC.

Claim labels: source statements checked against the seven pinned primary PDFs are
`literature-checked`. The T107 substitutions, transfer implications, and
obstructions are `proof sketch`. No experiment is used as evidence. This report
makes no C1, C2, canonical A1, normality-of-pi, or other fixed-pi claim.

```text
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 10
SEARCHED_LANE_COUNT: 3
CANDIDATE_COUNT: 3
RETAINED_FINGERPRINT_COUNT: 2
CANDIDATE_CAP: 3
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

## 1. Immutable statement and normalized scope

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, the canonical question defines

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, and the circle-distance
inequality is strict. The open quantifier order is exactly

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 such that
A*n*Q_pi(n,N) <= N^2.
```

The candidates below change the weight, point, system, or statistic. They are
A13/A14 siblings or mechanism models only. In particular:

1. a bound for an explicit binary word is not a bound for the decimal orbit of
   pi;
2. an almost-everywhere multiplier theorem does not identify pi as a good
   multiplier;
3. fixed-order Gowers decay is not uniformity in a growing Gowers order;
4. coefficient-uniform polynomial phases in the index `j` do not include the
   exponential phase `h*pi*10^j`;
5. Fourier control cannot compensate for an excessive T107 boundary load,
   because the row defect is a maximum of its boundary and Fourier components.

## 2. Bounded search and source ledger

The search used exactly the following three lanes and then stopped:

1. symbolic entropy/collision and signed-cube uniformity;
2. fixed-point/lacunary dynamics and higher correlations;
3. short structured exponential sums and polynomial phases.

Exactly seven distinct primary sources were opened. S1--S3 support the three
candidate cards. S4 and S5 were screened as broader but redundant automatic
sequence results. S6 was an erroneous identifier returned during search; its
title and opening page immediately showed that it was irrelevant. S7 was
inspected to make the fixed-point lacunary lane literal: it gives an explicit
base-10 expanding-map point, but only discrepancy and no higher-order theorem.
All seven are counted and pinned rather than silently omitted. `SOURCE_PINS.md`
gives every URL, hash, locator, and role. `SEARCH_LOG.md` records the bounded
queries.

| ID | Lane | Source | Use |
|---|---|---|---|
| S1 | symbolic signed cubes | Konieczny, *Gowers norms for the Thue-Morse and Rudin-Shapiro sequences* | F1 |
| S2 | short structured sums | Fan--Konieczny, *On uniformity of q-multiplicative sequences* | F3 |
| S3 | lacunary higher correlation | Chaubey--Yesha, *The distribution of spacings of real-valued lacunary sequences modulo one* | F2 |
| S4 | automatic decomposition | Byszewski--Konieczny--Muellner, *Gowers norms for automatic sequences* | screened, redundant |
| S5 | automatic ergodic weights | Eisner--Konieczny, *Automatic sequences as good weights for ergodic theorems* | screened, weaker/qualitative |
| S6 | erroneous search return | Zeilberger, *What is Mathematics and What Should it Be?* | rejected at title/opening page |
| S7 | named fixed-point lacunary dynamics | Becher--Carton, *Normal numbers and nested perfect necklaces* | screened: explicit base-10 point, but discrepancy only; prior T90 fingerprint |

No unnamed primary paper was inspected. Counting S6 and S7, `7 <= 10`. Exactly
three candidate mechanisms are tested and two nonduplicate fingerprints are
retained, so both caps are respected.

## 3. Mandatory exclusions and fingerprint table

This table is a scope firewall, not a mathematical premise. Unverified notes
are identified as such and are not used to discharge any claim.

| Excluded branch/family | Verification status used | Excluded fingerprint | Why F1--F3 do not reuse it |
|---|---|---|---|
| T91 | unverified `proof sketch` note | finite-state exact block-collision recurrences, multiplicities, and synchronization | F1 uses signed `2^s`-vertex cube averages and a spectral gap, never an equality-collision recurrence; the shared automatic ancestry is disclosed |
| T104 | source claims `literature-checked`, transfers `proof sketch` | ambient-measure Fourier decay and Mahler/radial mechanisms | F1/F3 are deterministic digital weights; F2 is a metric higher-correlation theorem and is not used through ambient Fourier decay |
| T105 | source claims `literature-checked`, transfers `proof sketch` | additive energy, flattening, and modular geometric-sum bounds | no card uses additive energy, BSG, sum-product, or a modular reduction |
| active T109 | unavailable in the supplied library | perturbative robustness, excluded by agenda | no content is inferred and no perturbation argument is used |
| Stoneham family | prior source audits plus unverified developments | rational prime-power skeleton and repeated residues | no Stoneham point, order calculation, or rational tail appears |
| paperfolding family | prior source claims plus unverified collision notes | valuation/odd-part automata and paperfolding collision recurrences | no paperfolding sequence or decimation identity appears |
| Toeplitz family | T103 source claims `literature-checked`, deductions `proof sketch` | nested periodic-hole towers | no Toeplitz point, hole set, or tower height appears |
| universal charging | T100 machine-checked finite-word theorem | short-to-long exact-word charging | no charging inequality or exact-word transport is used |

The candidate fingerprint classifications are:

| Card | Named system | Normalized fingerprint | Nearest overlap and separator |
|---|---|---|---|
| F1 | binary Thue--Morse fixed point `t(j)=(-1)^(s_2(j))` | signed higher-order cubes -> finite graph spectral gap -> fixed-order `U^s` power decay | T91 has the same word but a different statistic: unsigned exact-word collisions rather than signed cubes |
| F2 | explicit Hadamard-lacunary times `a_j=10^j` with multiplier alpha | near-relation counting -> variance decay -> almost-sure Poisson correlations of every fixed order | duplicate comparator: T104 already inspected this exact theorem and classified the metric higher-correlation mechanism; only the new T107 boundary calculation is retained |
| F3 | generalized Thue--Morse `f_tau(j)=e(tau*s_2(j))`, `0<tau<1` | q-multiplicativity plus linear Gelfond decay -> all fixed polynomial degrees and Gowers orders | unlike F1's direct cube graph, F3 bootstraps all fixed orders from a linear-phase hypothesis |

Only F1 and F3 count toward `RETAINED_FINGERPRINT_COUNT: 2`. F2 remains a
candidate card because its exact T107 obstruction is required for the
fixed-point/lacunary lane, but its source mechanism is not claimed as new.

## 4. Exact T107 interface

This section is a `proof sketch` expansion of machine-checked local definitions,
not a new theorem. The checked files are:

```text
knowledge_library/t64/AggregateFejerCriterion.lean
SHA-256 ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16

knowledge_library/t107/T107AveragedTriangularFejer.lean
SHA-256 45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28
```

T107 lines 31--69 define the literal levels, boundary load, budgets, and row
defect. T107 lines 150--173 give the complete triangular quantifiers. T64 lines
82--216 define and evaluate the Fejer coefficients; lines 617--649 prove their
collected nonzero `L1` bound; lines 1633--1640 and 1715--1720 define the
one-scale and row remainders.

Put `q=10^ell` and

```text
S_P(h) = sum_(0<=j<P) e(h*10^j*pi),
H_p = 40*q^3,       Q_p = q,
H_c = 8000*q^3,     Q_c = 10*q.
```

For `Q,H`, T64's radial coefficient is

```text
r_(Q,H)(h) = 1/Q                                      if h=0,
             (1-|h|/(H+1))*sin(pi*h/Q)/(pi*h)         otherwise.
```

The collected coefficient has the exact alias restriction

```text
C_(Q,H)(h,k)
 = 1_(Q divides h+k) * Q*r_(Q,H)(h)*r_(Q,H)(k)
   * e(-(h+k)/(2Q)).                                    (4.1)
```

The nonzero one-scale remainder and the row remainder are

```text
R_(Q,H)(P) = sum_(|h|,|k|<=H, (h,k)!=(0,0))
               C_(Q,H)(h,k) S_P(h)S_P(k),

R_ell(P) = R_(10q,8000q^3)(P) - (1/2)R_(q,40q^3)(P).  (4.2)
```

If exactly one of `h,k` is zero, (4.1) vanishes: either the alias restriction
kills it or `sin(pi*k/Q)=0`. Thus no hidden `P*S_P(h)` term occurs.

Let `B_c(ell,P)` and `B_p(ell,P)` denote T107's active child and parent boundary
counts. Their exact widths are respectively `1/(400q^2)` among `10q`
cylinders and `1/(4q^2)` among `q` cylinders. Define

```text
L_ell(P) = B_c(ell,P) + (1/2)B_p(ell,P),
D_ell(P) = max(40q*L_ell(P)/P, 10q*|R_ell(P)|/P^2).     (4.3)
```

This is T107's literal `rowAnalyticDefect`. At `P>0`, `D_ell(P)<=1` is
equivalent to both exact T64 row budgets

```text
L_ell(P) <= P/(40q),        |R_ell(P)| <= P^2/(10q).    (4.4)
```

### 4.1 Uniform exponential-sum calculation

T64's collected coefficient estimate is

```text
sum_(nonzero h,k) |C_(Q,H)(h,k)|
 <= 16*(2+log(H/Q+1))^2.                                (4.5)
```

Set

```text
A_c(ell) = 2+log(800q^2+1),
A_p(ell) = 2+log(40q^2+1).
```

If

```text
|S_P(h)| <= epsilon*P for every 0<|h|<=8000q^3,         (4.6)
```

then (4.2), the triangle inequality, and (4.5) give

```text
|R_ell(P)|
 <= 16*A_c(ell)^2*epsilon^2*P^2
    + 8*A_p(ell)^2*epsilon^2*P^2,

10q*|R_ell(P)|/P^2
 <= 160q*(A_c(ell)^2+(1/2)A_p(ell)^2)*epsilon^2.        (4.7)
```

For `0<theta<1`, define the exact sufficient threshold

```text
epsilon_ell(theta)
 = sqrt(theta /
     (160q*(A_c(ell)^2+(1/2)A_p(ell)^2))).              (4.8)
```

Then (4.6) with `epsilon=epsilon_ell(theta)` makes the Fourier component
of (4.3) at most `theta`. This is approximately
`q^(-1/2)/(log q)`, not merely qualitative cancellation.

The thresholds decrease with `ell`. Hence a hypothetical frequency-uniform
power saving

```text
sup_(0<|h|<=8000*10^(3(k-1))) |S_(N(k))(h)|/N(k)
 <= C*N(k)^(-c) <= epsilon_(k-1)(theta)                 (4.9)
```

synchronizes the Fourier component for every `1<=ell<k`. A sufficient prefix
size is

```text
N(k) >= (C/epsilon_(k-1)(theta))^(1/c).                 (4.10)
```

Thus exponential prefix growth is allowed; the missing issue is a theorem for
the correct unweighted fixed-pi sums, not the size of the triangular frequency
box by itself.

### 4.2 Higher-correlation calculation

Define the alias-restricted fourth-moment quantity

```text
Gamma_(Q,H)(P)^2
 = sum_(0<|h|,|k|<=H, Q divides h+k) |S_P(h)S_P(k)|^2.
```

T64's collected coefficient `L2` bound is `6/sqrt(Q)`. Cauchy--Schwarz
therefore gives, with child and parent quantities `Gamma_c,Gamma_p`,

```text
|R_ell(P)| <= 6*Gamma_c/sqrt(10q) + 3*Gamma_p/sqrt(q).
```

Consequently the Fourier component of (4.3) is at most `theta` if

```text
Gamma_c/sqrt(10) + Gamma_p/2
 <= theta*P^2/(60*sqrt(q)).                              (4.11)
```

This is the exact higher-order target used to test F2. An unrestricted
fixed-order correlation limit is not (4.11): it must be quantitative, apply to
the Fourier-index family through `H=8000q^3`, and hold on one triangular prefix
sequence.

### 4.3 Averaged triangular defect

Fix `m0=1`. Suppose one positive strictly increasing prefix family `N(k)` and
one probability measure `nu` on the circle satisfy

```text
piDecimalEmpiricalMeasure(N(k)) -> nu weakly as k->infinity,             (4.12a)
```

and, for every `k>=k0`, every `1<=m<=k`, and every `1<=ell<m`,

```text
40*10^ell*L_ell(N(k))/N(k) <= theta.                    (4.12b)
```

and either (4.8)--(4.9) or (4.11) makes the Fourier component at most `theta`.
Then `D_ell(N(k))<=theta`, and exactly

```text
sum_(ell=1)^(m-1) D_ell(N(k))
 <= theta*(m-1)
  = (m-1) - ((1-theta)*m-(1-theta)).                    (4.13)
```

Thus the full T107 predicate `AveragedTriangularT64DefectAt` holds with

```text
d=1-theta,       B=1-theta,       m0=1,                 (4.14)
```

Equations (4.7)--(4.14) are conditional bookkeeping only. No source below
supplies (4.12a)--(4.12b) for pi, and none supplies the correct (4.9) or
(4.11) for pi.

## 5. F1: signed-cube spectral gap at the Thue--Morse point

### 5.1 Exact source theorem and quantifiers

S1 defines

```text
t(0)=1,       t(2n)=t(n),       t(2n+1)=-t(n),
```

equivalently `t(n)=(-1)^(s_2(n))`. Definition 1.1, preprint p. 2, lines
103--112 of the delivered text, defines `U^s[N]` by averaging the signed product
over every integral `s`-cube contained in `[N]={0,...,N-1}`.

Theorem A, preprint p. 3, delivered text lines 116--120, states:

```text
for every fixed integer s>=1 there exist c_s>0, C_s>0, N_s>=1
such that for every N>=N_s,
||t||_(U^s[N]) <= C_s*N^(-c_s).                          (5.1)
```

The discussion immediately after Theorem A, preprint p. 3, delivered lines
121--141, gives for every real polynomial `p` of degree `s-1`

```text
|(1/N) sum_(j<N) t(j)e(p(j))| << ||t||_(U^s[N]).         (5.2)
```

The generalized von Neumann inequality is coefficient-independent. Therefore,
for `s=2` and `s=3`, (5.1)--(5.2) are uniform over every real linear or
quadratic coefficient, even if the coefficients are selected from a growing
finite family. The constants and exponent are not uniform as `s` grows.

The same source gives qualitative dynamical orthogonality in equation (9), but
no rate uniform in the number of observables, polynomial degrees, system,
nilmanifold step/dimension, Lipschitz norm, or rationality complexity. Its
closing nilsequence discussion is contextual rather than a quantified
nilsequence-correlation theorem.

### 5.2 T107 substitution and first obstruction

At fixed `s=3`, S1 controls

```text
sum_(j<P) t(j)e(alpha*j^2+beta*j+gamma),                 (5.3)
```

uniformly in `alpha,beta,gamma`. T107 instead needs

```text
S_P(h)=sum_(j<P)e(h*pi*10^j)                             (5.4)
```

uniformly for `0<|h|<=8000*10^(3ell)`. Frequency magnitude is not the
obstruction: S1 permits arbitrary polynomial coefficients. The first failure is
phase shape and weight. The exponential `10^j` is not a fixed-degree
polynomial in `j`, and (5.4) has no Thue--Morse weight.

An explicit additional pi-specific transfer hypothesis would be: fix
`0<theta<1`, one strictly increasing positive `N(k)`, a probability measure
`nu` satisfying (4.12a), and for every `k>=k0`, `1<=ell<k`, and
`0<|h|<=8000*10^(3ell)` produce a real quadratic `p_(k,ell,h)` and error
`E_(k,ell,h)` such that

```text
S_(N(k))(h)
 = sum_(j<N(k)) t(j)e(p_(k,ell,h)(j)) + E_(k,ell,h),

C_3*N(k)^(-c_3) + |E_(k,ell,h)|/N(k)
 <= epsilon_(k-1)(theta),                                (TM-pi)
```

and also supply the boundary premise (4.12b). By (5.1)--(5.2), monotonicity of
(4.8), and (4.13), `(TM-pi)` would imply the T107 averaged defect with
`d=B=1-theta` and `m0=1`. S1 states no such representation, weak-limit, or
boundary theorem.

### 5.3 Cheap kill test

The exact version of the proposed quadratic representation is impossible. If
for some nonzero integer `h` and quadratic `p` one had

```text
e(h*pi*10^j)=t(j)e(p(j))
```

on four consecutive finite-difference positions, then the third multiplicative
difference would give

```text
e(729*h*10^j*pi) in {+1,-1},
```

because `Delta^3 10^j=(10-1)^3*10^j=729*10^j`,
`Delta^3 p=0`, and every Thue--Morse factor is a sign. Squaring would make
`1458*h*10^j*pi` an integer, contradicting irrationality of pi. This exact
four-position test kills an identity-based transfer. It does not rule out the
quantitative approximation `(TM-pi)`, which remains wholly unproved.

Card result: F1 survives only as a genuinely higher-order digital model. It
does not reach T107 or any fixed-pi statement.

## 6. F2: metric higher correlations for `a_j=10^j`

### 6.1 Exact source theorem and quantifiers

S3 calls a positive real sequence lacunary when there exists a fixed `c>1`
such that `a_(j+1)>=c*a_j` for every `j>=1`; see preprint p. 3, delivered
lines 139--143. For a compactly supported real smooth
`f:R^(r-1)->R`, its `r`-level sum is the distinct-index statistic in preprint
equation (1), delivered lines 82--101.

Theorem 1, preprint p. 3, delivered lines 118--125, states:

```text
for every positive real lacunary sequence (a_j), for Lebesgue-almost every
alpha in R, for every fixed integer r>=2, and every compactly supported real
smooth f:R^(r-1)->R,
R_r(f,(alpha*a_j),N) -> integral_(R^(r-1)) f as N->infinity. (6.1)
```

The printed wording says that for almost all `alpha`, the conclusion holds for
all `r>=2`; the countable intersection can therefore use one conull set. The
source gives no rate uniform in `r`, `f`, support size, derivative norms, or a
growing family of frequencies. Its proof allows constants to depend on `r`,
`f`, and the other fixed parameters; see delivered lines 127--136.

The explicit specialization `a_j=10^j` satisfies the ratio condition with
`c=10`. It is the fixed lacunary system tested here. The theorem's multiplier
remains almost-everywhere; it does not name a single explicit good `alpha` and
does not certify `alpha=pi`.

### 6.2 T107 test and triangular obstruction

Even granting named-point membership, (6.1) is a limit for each fixed order and
fixed test. It is not the alias fourth-moment estimate (4.11), whose frequency
box grows through `8000*10^(3ell)` and whose rows must share one `N(k)`.

There is a separate boundary obstruction before any fourth-moment conversion.
For an equidistributed orbit and fixed `ell`, the child boundary neighborhoods
are disjoint and have total circle length

```text
2*(10q)*(1/(400q^2)) = 1/(20q),
```

while the parent neighborhoods have total length

```text
2*q*(1/(4q^2)) = 1/(2q).
```

Therefore equidistribution gives

```text
B_c(ell,P)/P -> 1/(20q),
B_p(ell,P)/P -> 1/(2q),
L_ell(P)/P   -> 1/(20q)+(1/2)*(1/(2q)) = 3/(10q),
40q*L_ell(P)/P -> 12.                                    (6.2)
```

T107's boundary component must be at most `1`, or at most `theta<1` in
(4.12b). Thus the ordinary equidistribution behavior underlying the metric
Poisson model has the wrong boundary constant by a factor tending to `12`.
This fixed-level limit alone is not a theorem that every growing triangular
row fails: a positive-density family of growing levels is a different
synchronization question. It does prove that generic equidistribution cannot
be inserted as the missing T107 boundary premise.

The additional pi-specific transfer `(LAC-pi)` would have to assert one
`0<theta<1`, one strictly increasing positive `N(k)`, and one probability
measure `nu` satisfying (4.12a), such that for every `k>=k0`, every
`1<=m<=k`, and every `1<=ell<m`, the alias moment (4.11) and anti-boundary
estimate (4.12b) both hold for the actual orbit `{10^j*pi}`. It would also have
to prove that pi lies in the relevant quantitative exceptional-set complement.
S3 supplies none of these clauses.

### 6.3 Cheap kill test

Compute the normalized boundary expectation (6.2). A proposed direct route
from Poisson/equidistributed behavior to T107 is rejected immediately when the
answer is `12>1`; no Fourier or nilsequence calculation can repair that level
because (4.3) is a maximum. This is an exact constant test, not finite evidence.

Card result: F2 is a T104-duplicate higher-correlation comparator on the exact
lacunary times `10^j`. Its new T107 test fails first at named-point/rate
uniformity and has the wrong natural boundary load.

## 7. F3: q-multiplicative Gelfond bootstrap

### 7.1 Exact source theorem and quantifiers

S2, preprint p. 1, delivered lines 24--40, defines a unit-modulus sequence `f`
to be q-multiplicative when, for every `t>=0` and `m,n>=0` with
`m<q^t` and `q^t` dividing `n`,

```text
f(m+n)=f(m)f(n).                                          (7.1)
```

After fixing `q>=2` and `f`, its Gelfond-type premise has the exact big-O
quantifiers: there exist `c,C>0` and `N0>=1` such that, for every `N>=N0`,

```text
sup_(alpha in R) |(1/N)sum_(j<N)f(j)e(alpha*j)| <= C*N^(-c).
```

Theorem A, preprint p. 2, delivered lines 84--100, states; the constants may
depend on fixed `q,d,f` and its Gelfond data, but not on polynomial
coefficients or `N`:

```text
for every q-multiplicative unit-modulus f satisfying the Gelfond premise,
for every fixed integer d>=1, there exist c_d>0, C_d>0, N_d>=1 such that
for every N>=N_d,
sup_(p in R[x], deg p<=d)
|(1/N)sum_(j<N)f(j)e(p(j))| <= C_d*N^(-c_d).             (7.2)
```

Theorem B, delivered lines 100--115, says for every fixed `s>=2` there is
`kappa_s>0` such that

```text
||f||_(U^s[N]) << ||f||_(U^2[N])^(kappa_s).              (7.3)
```

The convention at preprint p. 9, delivered lines 490--494, fixes `q,s` and
allows all constants to depend on them. Neither (7.2) nor (7.3) is uniform as
degree/order grows.

The named family

```text
f_tau(j)=e(tau*s_2(j)),       0<tau<1,
```

is 2-multiplicative and satisfies the source's Gelfond premise; see preprint
pp. 4--5, delivered lines 223--263. The classical Thue--Morse point is
`tau=1/2`. This is pointwise in fixed `tau`, not uniform as `tau` approaches
`0` or `1`; the decay and Theorem A constants may depend on `tau`. The
fingerprint retained here is the bootstrap from uniform linear phases to every
separately fixed polynomial degree, not F1's direct signed-cube graph.

The source mentions bounded-complexity nilsequences only while describing an
inverse theorem and expressly declines to formulate a quantitative result;
preprint p. 9, delivered lines 480--488. No nilsequence complexity-uniform
estimate is available.

### 7.2 T107 substitution and first obstruction

The supremum in (7.2) is fully uniform in polynomial coefficients, so the
exponential size of T107's integer `h` is harmless if the phase is polynomial
in `j`. But `h*pi*10^j` has exponentially growing finite differences and is not
a polynomial of any fixed degree. Interpolating it on `P` indices requires
degree up to `P-1`; S2 fixes `d` before `N->infinity` and gives no constants for
`d=d(N)`.

A sufficient pi-specific transfer would fix `0<theta<1`, one prefix family
`N(k)`, one probability measure `nu` satisfying (4.12a), one generalized
Thue--Morse parameter `tau`, and, uniformly for every `k>=k0`, `1<=ell<k`,
and `0<|h|<=8000*10^(3ell)`, give a fixed-degree polynomial
`p_(k,ell,h)` and error `E_(k,ell,h)` with

```text
S_(N(k))(h)
 = sum_(j<N(k)) f_tau(j)e(p_(k,ell,h)(j)) + E_(k,ell,h),

C_d*N(k)^(-c_d) + |E_(k,ell,h)|/N(k)
 <= epsilon_(k-1)(theta),                                (QM-pi)
```

where one fixed `d` works for the whole triangle, together with (4.12b). Then
(7.2) and (4.7)--(4.14) would imply the T107 averaged defect. S2 supplies no
such phase conversion, no uniform approximation to the pi orbit, and no
weak-limit or boundary estimate.

### 7.3 Cheap kill test

The cheapest direct application would take

```text
f_h(j)=e(h*pi*10^j)
```

as the q-multiplicative weight. For any integer `q>=2`, use (7.1) with `t=1`,
`m=1`, and `n=q`. It would require

```text
e(h*pi*10^(q+1)) = e(h*pi*(10+10^q)),
```

so

```text
h*pi*(10^(q+1)-10^q-10) in Z.
```

The parenthesized coefficient is a nonzero integer and `h!=0`, contradicting
irrationality of pi. Thus the actual lacunary phase sequence is not
q-multiplicative for any `q>=2`. This exact three-index test kills the direct
substitution. It does not refute the much stronger approximate representation
`(QM-pi)`, which is not supplied.

Card result: F3 is coefficient-uniform at every fixed polynomial degree but
does not contain the exponential-in-index pi phase or T107 boundary behavior.

## 8. Candidate matrix and negative map

| Card | Exact sourced strength | Frequency-family test | First T107 failure | Pi-specific premise | Cheap kill |
|---|---|---|---|---|---|
| F1 | fixed-order `U^s` power decay for Thue--Morse; uniform fixed-degree polynomial coefficients | simultaneous growing coefficient sets pass at fixed degree | wrong weight and exponential phase shape; no boundary theorem | `(TM-pi)` plus (4.12a)--(4.12b) | third difference forces pi rational for an exact quadratic identity |
| F2 | all fixed Poisson correlation orders for a.e. multiplier of every positive lacunary sequence | no rate uniform in order, test, frequency box, or common triangular prefix | T104 duplicate; no named alpha; alias moment absent; generic boundary ratio tends to 12 | `(LAC-pi)`: named-point (4.11), (4.12a), and (4.12b) | normalized boundary expectation `12>1` |
| F3 | q-multiplicative linear Gelfond decay bootstraps to all separately fixed polynomial degrees/Gowers orders | coefficient size passes, growing degree fails | `10^j` is not fixed-degree polynomial and actual phase is not q-multiplicative | `(QM-pi)` plus (4.12a)--(4.12b) | `m=1,n=q,t=1` violates q-multiplicativity by irrationality of pi |

No card supplies a nilsequence estimate with step, dimension, Lipschitz norm,
rationality complexity, and frequency family uniform in a growing T107
triangle. No card reaches the boundary half of the defect. The first failures
are therefore explicit rather than hidden behind the phrase "higher-order
uniformity."

## 9. Scope firewall and endpoint

1. S1 and S2 prove theorems about digital weights, not about pi.
2. S3 proves an almost-everywhere theorem and does not identify pi.
3. Equations (4.7)--(4.14) are conditional `proof sketch` calculations based on
   checked T64/T107 interfaces; their hypotheses are not established.
4. The exact cheap tests reject only the displayed direct applications. They do
   not prove that every future higher-order mechanism must fail.
5. No assertion about C1, C2, canonical A1, or fixed-pi cancellation is made.

TERMINAL VERDICT (1/1): **HOLD AS MODEL.** Retain F1 as the cleanest genuinely
higher-order explicit digital model and F3 as a distinct fixed-degree
q-multiplicative bootstrap. F2 is not retained as a new fingerprint because it
duplicates T104, but its exact boundary calculation is the sharpest warning
that even Poissonian higher correlations have the wrong natural T107 boundary
load. None survives the named-point, weak-limit, triangular synchronization,
and boundary tests needed for T107. There is no bounded successor
(`SUCCESSOR_COUNT: 0`).
