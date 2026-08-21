# T132: weighted multi-modulus block-collision audit

Audit date: 2026-08-10 UTC.

Statements attributed to the seven pinned primary papers are
`literature-checked`. Sections 3--7 contain elementary `proof sketch`
deductions from definitions and those statements. The replay is an
`experiment`: it checks hashes, finite identities, cap counts, and displayed
arithmetic, but is not evidence for an asymptotic assertion. The premise
`PI-MEET` in Section 10 is a `conjecture` and is not asserted for pi.

```text
SEARCHED_DOMAIN_COUNT: 3
SEARCHED_DOMAIN_CAP: 3
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 8
RETAINED_CANDIDATE_COUNT: 2
RETAINED_CANDIDATE_CAP: 2
SURVIVOR_COUNT: 1
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

This is a bounded related-model audit. It proves no property of the decimal
orbit of pi and no canonical, C1, or C2 conclusion.

## 1. Immutable statement, provenance, and scope

The canonical question has no external source URL. It was formulated by this
program on 2026-07-22. The delivered `canonical_statement.txt` is a byte-exact
copy with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It defines, for integers `n,N>=1`,

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, the cutoff is strict,
and the open quantifier order is

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N=N(A,n)>=1 with
A*n*Q_pi(n,N) <= N^2.
```

T132 does not alter this question. The theorem candidate retained below is a
finite deterministic inequality for arbitrary multisets. Applying its
strict-gain branch to the actual overlapping blocks of pi at all required
depths needs the separately stated unproved premise in Section 10.

### 1.1 Ambiguities fixed before deduction

1. A primary source is counted once even when a PDF and a temporary text
   derivative were inspected. Exactly the seven PDFs listed in Section 2 were
   opened; no eighth primary paper was opened.
2. The three searched domains are exactly restricted-denominator/large-sieve
   approximation, symbolic collision/Renyi-2 theory, and short structured
   exponential sums.
3. A retained candidate is one normalized theorem card tested against the
   target, not every source screened. Exactly C-MEET and C-LS are retained.
4. A projection modulus is an integer `q>=1`. It is genuinely coarse only
   when `q<10^m`; for `q>=10^m`, reduction is injective on the block alphabet
   and `E_q=C_m`.
5. Weights are arbitrary nonnegative real numbers. This preserves repeated
   starts and heavier atoms. The literal orbit multiset has all weights one,
   total mass `N`, and is used in every parameter calculation.
6. Every energy counts ordered pairs and includes the weighted diagonal.
7. For a finite nonempty modulus family `Q`, `average_q E_q` means the
   unweighted arithmetic mean. Weighted convex averages obey the same trivial
   comparison.
8. Full marginal histograms are data; assuming that their collision energies
   already decay is not allowed. C-MEET takes arbitrary histograms and may or
   may not return a strict gain.
9. T124 is an unverified note. T130 and T131 are now readable accepted
   literature reports: their pinned source statements are `literature-checked`,
   their new deductions are `proof sketch`, and their replays are `experiment`.
   They are used only as fingerprint comparators, never as discharged premises.

## 2. Bounded three-domain source ledger

`SOURCE_PINS.md` gives URL, DOI where available, SHA-256, and exact locators.
`SEARCH_LOG.md` records the bounded searches. The seven opened papers are:

| ID | Domain | Primary source | Audit role |
|---|---|---|---|
| S1 | restricted denominator | Gallagher (1971), *A larger sieve* | support-only larger-sieve screen |
| S2 | restricted denominator | Montgomery--Vaughan (1973), *The large sieve* | retained weighted C-LS card |
| S3 | restricted denominator | Baier--Zhao (2007 preprint; 2008 journal), square-modulus large sieve | restricted-denominator direction check |
| S4 | symbolic collision/Renyi-2 | Cicalese--Gargano--Vaccaro (2019) | retained majorization C-MEET card |
| S5 | symbolic collision/Renyi-2 | Yadav--Shkel (2026 preprint) | finite-meet/Renyi lattice confirmation |
| S6 | short structured sums | Konieczny (2019 journal version) | fixed-order automatic-sequence screen |
| S7 | short structured sums | Fan--Konieczny (2019) | assumed-Fourier/fixed-order screen |

S1 is an image-only three-page scan. `pdftotext` returned no text and
`tesseract` was unavailable. Theorem 1 and formula (2) on printed p. 77 were
therefore checked visually against a 300 dpi rendering; the PDF is
authoritative. All other cited source windows were checked in text-bearing
PDFs. This limitation is recorded rather than replacing S1 silently.

## 3. Literal block and residue energies

Fix real `x`, integers `m,N>=1`, and put `M=10^m`. Let

```text
y_i = {10^i*x} in [0,1),
B_(i,m)(x) = floor(M*y_i) in {0,...,M-1},  0<=i<N.       (3.1)
```

Thus label `b` is the half-open cylinder

```text
I_b = [b/M,(b+1)/M),                                    (3.2)
```

including its left endpoint and excluding its right endpoint. Terminating
decimal points therefore enter the cylinder on their right, exactly as the
floor in (3.1) prescribes. No choice of decimal expansion is made.

Give start `i` weight `a_i>=0`, and define

```text
A_b = sum_(0<=i<N, B_(i,m)(x)=b) a_i,
C_m(x,N;a) = sum_(0<=b<M) A_b^2.                         (3.3)
```

Expanding the square gives the literal identity

```text
C_m(x,N;a)
 = sum_(0<=i,j<N) a_i*a_j*1[B_(i,m)(x)=B_(j,m)(x)].      (3.4)
```

The pairs are ordered. Its diagonal contribution is `sum_i a_i^2`; in the
unweighted case it is exactly `N`. Repeated block values are not collapsed.

For every integer `q>=1`, define the multiplicity-preserving residue fibers

```text
R_(q,r) = sum_(0<=b<M, b == r mod q) A_b,   0<=r<q,
E_q(x,m,N;a) = sum_(0<=r<q) R_(q,r)^2.                  (3.5)
```

Expanding each residue square and separating equal from unequal labels gives

```text
E_q = C_m
    + sum_r sum_(b!=c, b==c==r mod q) A_b*A_c >= C_m.   (3.6)
```

This proves, without a support or distinctness assumption,

```text
C_m <= E_q,
C_m <= min_(q in Q) E_q <= |Q|^(-1) sum_(q in Q) E_q.   (3.7)
```

The last two expressions are the two displayed trivial projection bounds.
They are sharp from scalar energy data alone: if every selected projection is
injective on the occupied labels, then every displayed quantity equals
`C_m`. Multiplying marginal collision probabilities would be false for this
diagonal coupling.

### 3.1 Exact Fourier identity and the Parseval pre-screen

For `e(t)=exp(2*pi*i*t)`, character orthogonality gives

```text
E_q = (1/q) sum_(0<=h<q)
      |sum_(0<=i<N) a_i e(h*B_(i,m)(x)/q)|^2.            (3.8)
```

This is an identity, not cancellation. Before source selection, every proposed
single-modulus theorem whose conclusion was merely an upper bound for the
right side of (3.8) was classified as a T121 residue-L2 duplicate. C-LS was
retained only because it is the canonical weighted large-sieve theorem; its
direction is tested explicitly in Section 7. No single-modulus residue-L2
bound survives.

## 4. Floors, carries, powers of ten, and endpoints

For `1<=ell<m`, the elementary identity

```text
floor(10^m*y)
 = 10^ell floor(10^(m-ell)*y)
   + floor(10^ell*{10^(m-ell)*y})                        (4.1)
```

holds also when either argument is an integer. With `y={10^i*x}` it yields

```text
B_(i,m)(x)
 = 10^ell B_(i,m-ell)(x) + B_(i+m-ell,ell)(x),           (4.2)
B_(i,m)(x) mod 10^ell = B_(i+m-ell,ell)(x).              (4.3)
```

There is no unrecorded carry: the second floor in (4.1) is precisely the lower
`ell` digits. Consequently a modulus `10^ell` merely gives the length-`ell`
block energy on the shifted starts `i+m-ell`. It is a shallower T7-shaped
energy, not a new multi-modulus mechanism, and is rejected.

For a general character bridge, integer-part bookkeeping gives

```text
B_(i,m)(x)
 = floor(10^(i+m)*x) - 10^m floor(10^i*x),               (4.4)
e(h*B_(i,m)(x)/q)
 = e(h*floor(10^(i+m)*x)/q)
   e(-h*10^m*floor(10^i*x)/q).                           (4.5)
```

If `q|10^m`, the second factor in (4.5) is one, but

```text
e(h*floor(10^(i+m)*x)/q)
 = e(h*10^(i+m)*x/q) e(-h*{10^(i+m)*x}/q).               (4.6)
```

The last factor is a varying carry phase. If `q` does not divide `10^m`, both
factors in (4.5) vary. None of S1--S3, S6, or S7 proves cancellation for this
literal weighted phase on the decimal orbit. Dropping either factor would be
an invalid floor-to-lacunary transfer.

## 5. Ordered near returns and the factor three

Define the sibling statistic, for real `x`,

```text
Q_x(m,N) = #{(i,j) in {0,...,N-1}^2:
 ||(10^i-10^j)x||_(R/Z) < 10^(-m)}.                      (5.1)
```

This is ordered and diagonal-inclusive. If two points have the same half-open
cell, their ordinary distance is strictly less than `1/M`, so

```text
C_m(x,N;1) <= Q_x(m,N).                                  (5.2)
```

Conversely, strict circle distance below `1/M` puts the two cell labels equal
or adjacent modulo `M`. In this section set every `a_i=1`, so `A_b` is the
ordinary number of starts in cell `b`. Therefore

```text
Q_x(m,N)
 <= sum_b A_b(A_(b-1)+A_b+A_(b+1))
 <= C_m + 2 sqrt(C_m*C_m) = 3 C_m.                       (5.3)
```

Indices in (5.3) are modulo `M`, and the final inequality is Cauchy--Schwarz
under cyclic reindexing. Boundary equality at distance exactly `1/M` is
excluded by (5.1); the half-open convention handles points on cell endpoints.
Thus

```text
C_m(x,N;1) <= Q_x(m,N) <= 3 C_m(x,N;1).                  (5.4)
```

This is only a deterministic comparison and asserts no bound for fixed pi.

## 6. Quantitative single-modulus screen

In the unweighted case, `sum_r R_(q,r)=N`, so Cauchy--Schwarz gives

```text
Delta_q := E_q-N^2/q >= 0.                               (6.1)
```

Fix integers `A,m,N>=1` and a coarse `q<10^m`. If a theorem actually implied

```text
q >= 6*A*m,
Delta_q <= N^2/(6*A*m),                                  (6.2)
```

with its constants and `N` range valid there, then

```text
E_q = N^2/q+Delta_q <= N^2/(3*A*m),
C_m <= E_q,
Q_x <= 3*C_m <= N^2/(A*m),
A*m*Q_x <= N^2.                                          (6.3)
```

The range is every positive `N` for which (6.2) is proved. It necessarily has
`N>=3*A*m`, because the unweighted diagonal gives `N<=C_m<=E_q` while (6.3)
gives `E_q<=N^2/(3*A*m)`. The replay checks the concrete admissible tuple
`(A,m,N,q,Delta)=(2,3,120,40,300)`.

No inspected source proves (6.2) for `B_(i,m)(pi)`. Taking `q>=10^m` makes
`E_q=C_m` and simply assumes the desired exact collision decay, so it is not a
coarse-projection gain.

## 7. Two retained theorem candidates

### 7.1 C-MEET: full-profile majorization meet

**Source statement.** S4 printed PDF p. 3, Definition 1, and printed PDF p. 4,
Fact 1, equations (3)--(5), and Lemma 2 prove that the vectorized joint PMF `r`
of any coupling of finite sorted marginals `p` and `q` is majorized by their
greatest lower bound `p meet q`. S4 PDF p. 10, equation (20), Lemma 4 and equation (21) states
the same entropy bound for every Renyi order
`alpha in (0,1) union (1,infinity)`, hence for `alpha=2`. S4 PDF p. 13,
Lemma 7 and its proof gives, for arbitrary finite `k`,

```text
r is majorized by w := p^(1) meet ... meet p^(k).         (7.1)
```

The proof of (7.1) is entropy-independent: the joint PMF is an aggregation of
each marginal, hence a common majorization lower bound. S5 PDF pp. 3--4,
Definitions 3 and 7, Remark 3, and equation (7) independently records the
aggregation implication and finite meet formula; its 2026 preprint status is
not hidden.

**Exact T132 specialization.** Let `phi_s` be reduction modulo `q_s`, let
`p^(s)` be the sorted normalized residue masses `R_(q_s,r)/N`, and let `r` be
the normalized joint-tuple histogram of

```text
(B mod q_1,...,B mod q_k).
```

Exact labels refine joint tuples, so, with `J=N^2 sum_u r_u^2`,

```text
C_m <= J.                                                (7.2)
```

Since `z -> sum z_i^2` is Schur-convex, (7.1) gives

```text
J <= G := N^2 sum_i w_i^2
  <= min_s E_(q_s)
  <= (1/k) sum_s E_(q_s).                                (7.3)
```

All constants are exactly one. The hypotheses are only finite nonnegative
masses, their full marginal profiles, zero-padding, sorting, and an arbitrary
joint coupling. There is no independence, support-uniformity, collision-decay,
or asymptotic-range hypothesis. Multiplicity is retained in every PMF entry.

**Strict-gain branch and survivor test.** C-MEET is called a survivor only on
an actual profile instance satisfying

```text
G < min_s E_(q_s).                                       (7.4)
```

Then (7.3) beats both trivial bounds strictly without assuming collision
decay. This branch is nonempty for literal residue projections. Give labels
`b=0,...,5` multiplicities

```text
(3,1,1,3,1,1),  N=10,  q_1=2, q_2=3.
```

The exact energy is `C=22`; the modulo-2 and modulo-3 energies are `50` and
`44`. Their sorted PMFs are `(1/2,1/2,0)` and `(3/5,1/5,1/5)`, whose meet is
`(1/2,3/10,1/5)`. Hence

```text
G = 100*(1/4+9/100+1/25) = 38 < 44 < 47,                (7.5)
```

where `47` is the average projected energy. CRT is used only to identify the
actual joint tuple; no product of marginal probabilities is taken. The replay
checks every count in (7.5).

**Parameter outcome.** For arbitrary `A,m,N`, C-MEET reaches the direct
factor-three target if the computed full profiles give

```text
G <= N^2/(3*A*m).                                        (7.6)
```

S4 does not force (7.6), and no such profile estimate is known here for pi.
Thus C-MEET survives as a finite deterministic discriminator, not as a
fixed-point theorem.

### 7.2 C-LS: weighted analytic large sieve

**Source statement.** S2 printed p. 119, equations (1.1), (1.3), and Theorem 1
equation (1.4), states: for arbitrary complex coefficients `a_n` on an
integer interval of length `H`, and distinct frequencies `x_r mod 1` with
minimum circle spacing `delta`,

```text
sum_r |sum_n a_n e(n*x_r)|^2
 < (H+delta^(-1)) sum_n |a_n|^2.                         (7.7)
```

The constant is one and there is no asymptotic restriction. For `q>=2`, put
`H=M=10^m`, coefficient `a_b=A_b`, and take all `q` frequencies `h/q`. Their
spacing is `1/q`; (3.8) gives

```text
q*E_q < (M+q)*C_m,
C_m > q*E_q/(M+q).                                       (7.8)
```

**Outcome.** Multiplicity is perfectly preserved, but (7.8) lower-bounds
`C_m`. It cannot improve either upper bound in (3.7). Combining frequencies
from several moduli requires deleting duplicates; it still gives an upper
frame bound with `C_m` on the right and supplies no joint fiber control.
C-LS is rejected by direction and is not a survivor.

### 7.3 Five screened, non-retained source mechanisms

1. S1 Theorem 1, formula (2), printed p. 77, bounds the cardinality of a set
   occupying at most `g(q)` classes modulo prime powers. Repeating one support
   point does not change `g(q)` but can make its weight arbitrarily large. It
   discards multiplicity and can only turn a support upper bound into the
   lower collision bound `C_m>=N^2/|support|`.
2. S3 Theorem 1, equation (1.7), preprint pp. 1--2, preserves arbitrary
   coefficients but bounds primitive square-denominator frequency sums by a
   constant times `sum|a_n|^2=C_m`. It again has the wrong direction, and its
   primitive frequencies are not full residue Parseval.
3. S5 confirms the lattice framework but provides no decimal-profile estimate;
   it is supporting, not a second collision candidate.
4. S6 Theorems A--B and Corollary 2.4 give fixed-order Gowers decay for the
   Thue--Morse and Rudin--Shapiro sequences. They have no arbitrary
   nonnegative weights or joint-modulus conclusion and duplicate T121's
   fixed-order automatic-sequence screen.
5. S7 Theorems A--B assume a q-multiplicative sequence with Gelfond/Fourier
   input and keep the Gowers order fixed. The literal block phases (4.5) are
   not shown q-multiplicative; importing the needed Fourier decay would assume
   the missing input. This is also the T121 F-AUT screen.

## 8. Candidate-by-candidate prior comparison

The comparator reports are vendored in `prior_evidence.tar.gz`. Source claims
inside the accepted literature reports are checked at their stated level;
their new deductions remain `proof sketch` unless they identify a checked
formal theorem. No prose note is used as a premise.

| Candidate | Comparator and exact locator | Comparison |
|---|---|---|
| C-MEET | T117 `prior-t117-REPORT.md`, lines 163--176 and 204--268 | T117's finite-field subset-product cancellation controls every word in a Legendre model. C-MEET uses no character sum or pointwise word discrepancy; it majorizes the joint histogram of the actual supplied marginal profiles. |
| C-MEET | T118 `prior-t118-REPORT.md`, lines 46--167 and 606--618 | T118 selects one private prime-power modulus and rejects unsupported multiplication of CRT character bounds. C-MEET neither selects a prescribed numerator nor multiplies marginals; it uses the actual joint coupling and full profiles. |
| C-MEET | T121 `prior-t121-REPORT.md`, lines 115--158 and 187--273 | T121's single-family Parseval/Walsh energy is the pre-screened duplicate. C-MEET starts after marginal energies are known and can strictly improve their minimum through Lorenz-profile crossing; it is not a standalone `E_q` estimate. |
| C-MEET | T124 `prior-t124-UNVERIFIED-REPORT.md`, lines 3--6 and 127--311 | The T124 note argues, unverified, for spectral mixing of all branching words on congruence quotients. C-MEET assumes no branching law or spectral decay and applies to any finite empirical coupling. No T124 deduction is imported. |
| C-MEET | T130 `prior-t130-REPORT.md`, lines 99--148, 264--291, 332--465, and 702--709 | T130 encodes literal equal blocks as exact prefix-integer S-unit equations; its standard counts fail at rank `N+O(log N)`, degeneracy, and multiplicity. C-MEET uses no prefix arithmetic or group rank: from complete residue profiles it bounds the actual joint coupling by a majorization meet. Thus it does not duplicate T130, and no T130 proof-sketch deduction is imported. |
| C-MEET | T131 `prior-t131-REPORT.md`, lines 88--176, 178--257, 259--343, and 345--447 | T131 rounds or orders balanced de Bruijn circulations and closes its realizations as T121 global-L2 or offline incidence constructions. C-MEET constructs no word, flow, Euler tour, or nesting; it tests a supplied empirical coupling for strict Lorenz-profile gain. It is distinct from T131 but still needs PI-MEET for the prescribed orbit. |
| C-LS | T117, same vendored locator | C-LS is a generic upper-frame inequality, not shifted subset-product cancellation. It is rejected before any Legendre-style word conversion. |
| C-LS | T118, same vendored locator | Both use modular exponential sums, but C-LS has arbitrary coefficients and no private-prime prescribed numerator. It also confirms T118's warning that marginal bounds do not create joint CRT control. |
| C-LS | T121, same vendored locator | Specializing C-LS to all characters of one modulus lands exactly on the residue Parseval quantity pre-screened as a T121 duplicate, and moreover has the wrong inequality direction. |
| C-LS | T124, same vendored locator | The unverified T124 mechanism is a lower spectral contraction for a branching walk. C-LS is an upper frame bound for arbitrary coefficients and supplies no contraction. |
| C-LS | T130, same vendored report and locators | T130's candidates count exact S-unit solutions or block support, whereas C-LS is a generic Fourier upper-frame inequality. Neither supplies the required collision upper bound, but their failed mechanisms are different; C-LS is rejected by (7.8) without using T130. |
| C-LS | T131, same vendored report and locators | T131's flow cards control incidence vectors by construction and ordering. C-LS assumes arbitrary coefficients and returns `qE_q<(M+q)C_m`, so it neither balances a flow nor controls a joint fiber and is rejected before any T131-style construction. |

These rows use T130/T131 only at their self-reported verification levels. They
replace the stale lease-only boundary and do not promote either report's
proof-sketch deductions to premises. This bounded audit makes no novelty claim.

## 9. Exclusion summary

The audit rejects:

1. support-only larger sieves, because multiplicity is invisible;
2. upper-frame large-sieve inequalities, because they lower-bound `C_m`;
3. products of CRT marginal collision probabilities without a joint coupling;
4. hypotheses already assuming residue-L2, Renyi-2, or Fourier decay;
5. powers-of-ten suffix projections, by the exact shallower identity (4.3);
6. finite-field subset-product cancellation duplicating T117;
7. private-prime prescribed-numerator sums duplicating T118;
8. single-modulus Parseval bounds duplicating T121;
9. branching spectral models conditionally resembling the unverified T124 note;
10. exact block-to-S-unit counting that duplicates T130;
11. balanced circulation, Euler ordering, or nested-word construction that
    duplicates T131.

C-MEET avoids items 1--11 at the finite-profile level. It is still withheld
from novelty and fixed-point classification because this is a bounded source
audit and the premise below is missing.

## 10. Separately labeled fixed-pi transfer premise

**PI-MEET (conjecture; unproved).** For every integer `A>=1`, there exists an
integer `m0>=1` such that for every integer `m>=m0`, there exist an integer
`N>=1` and a finite family of at least two coarse moduli
`Q=Q(A,m,N) subset {1,...,10^m-1}` for which the sorted residue profiles of the
literal multiset

```text
{B_(i,m)(pi): 0<=i<N}
```

have majorization meet `w=w(A,m,N,Q)` satisfying

```text
A*m*N^2*sum_j w_j^2 <= N^2.                              (PI-MEET)
```

This is the exact additional fixed-pi premise needed for C-MEET to imply the
T7 finite-prefix collision inequality, because (7.2)--(7.3) then give
`A*m*C_m(pi,N)<=N^2`. It is not a theorem of S4 or S5, and no evidence in this
audit establishes it. Using the same premise with `A` replaced by `3A` and
then (5.4) would be sufficient for the canonical near-return inequality; that
logical observation is not a fixed-pi conclusion.

For one direct single-scale canonical screen, the stronger computed condition
`sum_j w_j^2<=1/(3*A*m)` or the single-modulus conditions (6.2) suffice. None
is asserted for pi.

```text
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
NOVELTY_CLAIM: none
SUCCESSOR: none
VERDICT: hold as model
```
