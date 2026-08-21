# T113: effective-avoidance audit for decimal differences

Audit date: 2026-08-10 UTC.

```text
PRIMARY_SOURCE_COUNT: 3
PRIMARY_SOURCE_CAP: 8
SEARCHED_DOMAIN_COUNT: 3
PRIOR_FINGERPRINT_COUNT: 5
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

Claim labels are load-bearing. The three source statements identified in
`SOURCE_PINS.md` are `literature-checked`. Sections 4-7 are new elementary
`proof sketch` deductions, not machine-checked theorems. The bounded replay is
an `experiment`: it checks transcription and finite instances, not the
universal deductions. This report proves no statement about pi.

## 1. Immutable statement and normalized scope

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For real `x` and integers `n,N>=1`, put

```text
Q_x(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)x||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, the circle inequality
is strict, and the canonical assertion fixes `x=pi` with quantifiers

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N) <= N^2.
```

T113 changes the point. Its positive result is therefore only an A13 sibling.
It does not establish canonical C1, normality of pi, or any decimal-complexity
consequence for pi.

Normalized ambiguities:

1. `D_N={10^i-10^j:0<=i,j<N}` is a set over the integers. It contains zero,
   both signs of every nonzero magnitude, and no nonzero multiplicities.
2. Moshchevitin's `t_k` is a strictly increasing positive sequence, so T113
   orders the positive magnitudes of `D_N`; sign invariance of circle norm then
   handles both ordered orientations.
3. The source's word "increasing" for `k-h(k)` is read as nondecreasing. Its
   own floor-function example has flat integer steps, and its proof uses only
   monotonicity. Our `k-h(k)` is not claimed strictly increasing.
4. `log` in the calculations is the natural logarithm.
5. A nonempty or full-Hausdorff-dimension avoidance set is not silently treated
   as containing a computable member.
6. The schedule below uses integer `A,n>=1` and `N_A(n)=A*n` exactly.

## 2. Bounded three-domain source audit

Exactly three primary sources were inspected, one per required domain. This is
below the cap eight. No source was added to fill the cap.

| domain | source | exact role | result for this audit |
|---|---|---|---|
| restricted-denominator approximation | Moshchevitin (2007), Theorem 2 | variable `H`, moving-window and initial-sum avoidance theorem | load-bearing source; all hypotheses are instantiated in Section 6 |
| explicit fixed-point lacunary dynamics | Becher--Carton (2018/2019), Theorem 1 | named base-10 nested-necklace point with discrepancy `O((log N)^2/N)` | comparator: effective fixed point and aggregate pair control, not uniform difference avoidance |
| symbolic collision coding | Fishman--Merrill--Simmons (2018), definition (2.1) and Corollary 4.3 | nested totally de Bruijn expansions for alphabets of size at least four | comparator underlying T111's effective FMS point; T111's proof-sketch ingredients already imply all-difference avoidance on its prefix |

The agenda prefers 2020-2026 sources but expressly retains Moshchevitin's
indispensable variable-`H` source. The shortest nonduplicative corpus is older:
the two other sources are the exact accepted T90 and T111 mechanism pins. The
2025 material already audited by T105 and the five-source 2026-era T112 scout
are compared below; neither supplies a variable-threshold named-point theorem.
Adding a recent paper merely to fill a date preference would not test a new
hypothesis.

Exact URLs, versions, hashes, theorem locators, and derivative line locators
are in `SOURCE_PINS.md`. All three authoritative PDFs and line-addressable text
derivatives are delivered.

## 3. Prior-fingerprint comparison

Verification level is part of every comparison. Notes are navigation and
source-pinned exploration, not discharged formal premises.

| prior item | inspected pin and level | normalized fingerprint | T113 distinction |
|---|---|---|---|
| T90 | `REPORT.md`, SHA `730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0`; sources `literature-checked`, transfers `proof sketch` | named computable expanding-map point -> discrepancy -> aggregate `Q_x` upper bound | T113 asks for simultaneous avoidance of every nonzero decimal difference, which would give exact `Q_x=N`; discrepancy allows off-diagonal pairs |
| T105 | `REPORT.md`, SHA `ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f`; sources `literature-checked`, deductions `proof sketch`, replay `experiment` | exact `D_N` structure followed by energy/BSG, ambient Fourier decay, or modular geometric-sum tests | T113 reuses the elementary distinctness fingerprint but uses direct Peres--Schlag avoidance, not energy or cancellation; it selects an existential sibling point rather than evaluating a prescribed character at pi |
| T111 | `REPORT.md`, SHA `89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8`; accepted source-pinned note, deductions still `proof sketch` | totally de Bruijn odd-digit coding gives a named computable FMS point; its first `4^m` codes are distinct and odd, while a metric return forces cyclic adjacency | Those proof-sketch ingredients already imply `Q_x(m,N)=N` for every `N<=4^m`, although T111 displayed only the looser `Q_x<=(2m+1)N`. T113 claims no new symbolic sibling. Its distinct work is solely the direct variable-`H` instantiation, which yields an unnamed existential point |
| T112 (active revision state) | report blob SHA `06456a6f7fe521c44ecf57f972cb93506d6a6aeb03e6544e29e8c6a663c717eb`; source statements `literature-checked`, deductions `proof sketch`; reviewer requested revision | finite carry/local-limit and twisted finite-transducer operators calibrated to T64/T107 boundary and Fourier budgets | T113 has no random carry law, growing-state operator, or boundary-discrepancy transfer. T112 explicitly gives no fixed-pi result, and its operator-to-event constants were not accepted as reproducible |
| T109 (terminal rejected record) | report blob SHA `6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf`; source statements `literature-checked`, transports `proof sketch`; reviewer rejected the claimed necessity of its certificate tests | Markov-law, shadowing, and Wasserstein/Fourier-window robustness transport | T113 constructs an existential avoiding point directly. It does not transport a model estimate to pi, and it does not infer failure of a transfer from failure of a sufficient certificate |

Thus the closest combination is T105's elementary difference distinctness plus
T111's Moshchevitin pin. T111's separate FMS proof sketch already contains a
named symbolic route to exact diagonal-only prefixes: for `N=A*m`, `m>=16A`
gives `N<=m^2/16<=4^m`, so its distinct odd codes exclude every off-diagonal
metric return. T113 neither duplicates nor upgrades that route. T113's new
`proof sketch` work is narrowly the exact ordering, direct variable-`H`
instantiation, and threshold calculation for Moshchevitin's existential point.
It makes no novelty claim beyond this bounded local corpus.

## 4. Exact variable-threshold source theorem

Moshchevitin begins with a strictly increasing sequence of positive reals

```text
1 <= t_1 < t_2 < ... ,  t_k -> infinity
```

and defines, for `tau>1`,

```text
H(k,tau) = min{r in N: t_(k+r)/t_k >= tau}.                (4.1)
```

Theorem 2 fixes `0<eta<1`, a natural-number sequence `h(k)`, and a decreasing
positive sequence `delta(k)`. Its hypotheses are:

```text
(H0) k-h(k) is nondecreasing on the integers with k>h(k);

(H1) h(k) >= H(k-h(k), 1/delta(k-h(k))) whenever k>h(k);

(H2) sum_(v=k-h(k)+1)^(k-1) delta(v)
       <= (1-eta)*eta/4 whenever k>h(k);

(H3) sum_(v=1)^k delta(v)
       <= (1-eta)/16 whenever k<=h(k).                     (4.2)
```

The conclusion is exactly

```text
{x in [0,1]: ||t_k*x||_(R/Z) > delta(k) for every k>=1}
is nonempty.                                                   (4.3)
```

Locators: definition (1), printed p. 2, derivative lines 66-71; Theorem 2,
printed pp. 2-3, derivative lines 107-129. Section 6B, equation (19), printed
p. 8, derivative lines 538-546, states a full-dimension corollary under a
two-sided `exp(k^beta)` hypothesis. T113 does not invoke that corollary: its
literal upper bound has exponent coefficient `sqrt(2)*log(10)`, which cannot be
absorbed into the fixed multiplicative constant in printed equation (19).
Instead Sections 5-6 check Theorem 2 directly.

The source says only "nonempty" in Theorem 2. It does not state an algorithm,
a computable member, or a digit expansion for a member.

## 5. Complete ordering of decimal differences

For `i>=1` and `1<=s<=i`, define the triangular block index and value

```text
k(i,s) = i*(i-1)/2 + s,
t_(k(i,s)) = 10^i - 10^(i-s).                              (5.1)
```

This is the complete increasing enumeration of all positive differences
`10^i-10^j`, `i>j>=0`.

First, within a fixed `i`, increasing `s` decreases the subtracted power, so

```text
10^i-10^(i-1) < 10^i-10^(i-2) < ... < 10^i-1.             (5.2)
```

Second, adjacent blocks do not interleave:

```text
max(block i) = 10^i-1 < 9*10^i = min(block i+1).           (5.3)
```

Third, every positive difference has the displayed form with `s=i-j`.
Distinctness can also be read arithmetically: in

```text
10^i-10^j = 10^j*(10^(i-j)-1),
```

the last factor is divisible by neither 2 nor 5. Either valuation recovers
`j`, and then the value recovers `i`.

Consequently, for `N>=2`, the positive magnitudes from `D_N` are exactly

```text
t_1,...,t_K,  where K=binom(N,2)=N*(N-1)/2,                (5.4)
```

and the distinct nonzero signed set has size `2K=N(N-1)`. Including zero gives
the T105 cardinality `|D_N|=N(N-1)+1`. Every ordering and multiplicity used
below is now explicit.

For growth, if `i(i-1)/2 < k <= i(i+1)/2`, then

```text
9*10^(i-1) <= t_k < 10^i.                                  (5.5)
```

Writing `a=sqrt(2)*log(10)`, the triangular inequalities imply

```text
(9/(10*sqrt(10)))*exp(a*sqrt(k))
  <= t_k < 10*exp(a*sqrt(k)).                              (5.6)
```

Indeed `sqrt(2k)<i+1/2` gives the lower bound, while
`i<sqrt(2k)+1` gives the upper bound. These deliberately coarse global bounds
handle the near-unit ratios inside each triangular block.

## 6. Every theorem hypothesis with explicit constants

Set, for every integer `k>=1`,

```text
eta      = 1/2,
delta(k) = 1/(64*k^2),
f(k)     = 8*sqrt(k)*log(64*k),
h(k)     = ceil(f(k)).                                     (6.1)
```

All constants are fixed; no asymptotic comparison is being substituted for a
Theorem 2 hypothesis.

### 6.1 Basic sequence and threshold properties

Equations (5.1)-(5.3) show `1<=t_1<t_2<...` and `t_k` tends to infinity.
The sequence `h(k)` is natural-valued. The sequence `delta(k)` is positive and
strictly decreasing.

### 6.2 Hypothesis H0

For real `x>=1`, put `f(x)=8*sqrt(x)*log(64x)`. Then

```text
f'(x)  = (4*log(64x)+8)/sqrt(x),
f''(x) = -2*log(64x)/x^(3/2) < 0.                          (6.2)
```

If `k>h(k)`, then `sqrt(k)>8*log(64k)`. Hence

```text
f'(k) < (log(64k)+2)/(2*log(64k)) < 1.                    (6.3)
```

Concavity gives `f(k+1)-f(k)<1`, so
`h(k+1)-h(k)<=1`. Therefore

```text
(k+1-h(k+1)) >= k-h(k).                                   (6.4)
```

The same inequality shows that once `k>h(k)`, also `k+1>h(k+1)`. Thus the
relevant domain is a tail and (6.4) proves H0 in the source's nondecreasing
sense.

### 6.3 Hypothesis H1

Fix `k>h(k)` and put `m=k-h(k)>=1`. From (5.6),

```text
t_k/t_m
 > (9/(100*sqrt(10)))
     * exp(a*(sqrt(k)-sqrt(m))).                           (6.5)
```

Here `9/(100*sqrt(10))>1/64`, and

```text
sqrt(k)-sqrt(m)
 = h(k)/(sqrt(k)+sqrt(m))
 > h(k)/(2*sqrt(k))
 >= 4*log(64k).                                            (6.6)
```

Since `a=sqrt(2)*log(10)>1`, equations (6.5)-(6.6) give

```text
t_k/t_m > (1/64)*(64k)^4 > 64*m^2 = 1/delta(m).            (6.7)
```

Thus the candidate increment `h(k)` itself reaches the ratio in (4.1), and

```text
H(m,1/delta(m)) <= h(k).                                   (6.8)
```

This is H1 with room to spare.

### 6.4 Hypotheses H2 and H3

The elementary telescoping comparison

```text
sum_(v=1)^infinity 1/v^2 <
1 + sum_(v=2)^infinity 1/(v*(v-1)) = 2                    (6.9)
```

gives

```text
sum_(v=1)^infinity delta(v) < 1/32.                        (6.10)
```

For `eta=1/2`, the H2 budget is `1/16`, so every H2 window is below its
budget. The H3 budget is `1/32`, so every finite initial sum is strictly below
its budget. This checks both hypotheses, including the small indices where
`k<=h(k)`.

### 6.5 Exact source conclusion

Theorem 2 now gives at least one real `x in [0,1]` such that

```text
||t_k*x||_(R/Z) > 1/(64*k^2) for every integer k>=1.       (6.11)
```

This is an existential fixed-orbit sibling. Section 8 explains why it is not
an effective named-point construction.

## 7. Complete threshold-to-Q calculation

Fix integers `A>=1` and `n>=16A`, and prescribe

```text
N_A(n) = A*n,
K       = binom(N_A(n),2).                                 (7.1)
```

Then `N_A(n)>=A*n` with equality and `N_A(n)>=2`. From `K<N_A(n)^2/2`,

```text
delta(K) = 1/(64*K^2) > 1/(16*N_A(n)^4).                  (7.2)
```

The elementary inequality

```text
16*A^4*n^4 < 10^n for n>=16A                              (7.3)
```

is explicit: `A<=n/16` reduces the left side to at most `n^8/4096`; at
`n=16` this is below `10^16`, and the ratio
`((n+1)/n)^8/10` is below one thereafter. Combining (7.2)-(7.3) gives

```text
delta(K) > 10^(-n).                                        (7.4)
```

For every off-diagonal ordered pair `0<=i,j<N_A(n)`, its positive magnitude is
one of `t_1,...,t_K` by (5.4). Since `delta` decreases and circle norm is
unchanged by sign, (6.11) and (7.4) give

```text
||(10^i-10^j)*x||_(R/Z) > 10^(-n).                        (7.5)
```

No off-diagonal pair meets the strict counting inequality. Every diagonal pair
does because its distance is zero. Therefore, with order and the diagonal
retained,

```text
Q_x(n,N_A(n)) = N_A(n).                                    (7.6)
```

Finally,

```text
A*n*Q_x(n,N_A(n))
  = A*n*N_A(n)
  = N_A(n)^2.                                              (7.7)
```

Thus the theorem and new deductions establish the exact canonical-quantifier
inequality for at least one unnamed sibling point, with `n0(A)=16A` and a
prescribed linear witness. This remains a `proof sketch` artifact and says
nothing about pi.

## 8. First failed variable-H requirement: effective named point

The agenda asks whether the variable-threshold theorem effectively constructs
one named computable `x`. It does not. This failure is scoped to the
Moshchevitin route. It is not a claim that no named computable sibling exists:
the T111 note's FMS proof-sketch ingredients already give one by a different
symbolic mechanism, as recorded in Section 3.

An adequate effective named-point certificate would provide an algorithm that,
on input `r`, outputs a rational `q_r` with `|x-q_r|<=2^(-r)`, together with a
proved invariant ensuring that the nested finite choices extend to a point
satisfying every inequality in (6.11). Equivalently, a nested-rational-interval
algorithm would need computable diameters tending to zero and a decidable or
certified extendibility condition through all later forbidden neighborhoods.

Moshchevitin Theorem 2 concludes only that the set (4.3) is nonempty. It names
no member, gives no digit algorithm, no computable convergence modulus, and no
effective infinite-branch selector. Section 6B's Hausdorff-dimension conclusion
does not repair this: a full-dimensional set can omit every computable real.
Computability also does not follow merely because `t_k`, `h(k)`, and
`delta(k)` are computable; nonempty effectively presented closed sets need not
have computable members.

This is the first failed requirement of the audited variable-`H` mechanism.
No theorem hypothesis and no threshold comparison failed. Calling its
existential `x` computable, or identifying it with the FMS point, would be an
unsupported strengthening of the source.

## 9. Additional pi-specific premise

The exact additional premise needed to run this mechanism at pi is the
following unproved statement:

```text
PI-AVOID:
  for every integer k>=1,
  ||t_k*pi||_(R/Z) > 1/(64*k^2),
```

where `t_k` is the ordered sequence (5.1). Under `PI-AVOID`, Section 7 applies
verbatim with `x=pi`, `n0(A)=16A`, and `N_A(n)=A*n`; it would imply the
canonical inequality through the stronger diagonal-only identity. Neither the
three-source corpus nor any compared prior artifact proves `PI-AVOID`. It is a
strictly sufficient pi-specific premise, not an equivalent reformulation of
canonical C1, and no claim about pi is made.

The cheapest exact falsifier for `PI-AVOID` is one certified index `k` with
`||t_k*pi||<=1/(64*k^2)`. Failure to find such an index in a bounded search
would be only an `experiment`, never evidence for the universal premise.

## 10. Replay, boundary, and classification

From a directory containing only the delivered artifacts, run

```text
python3 verify_t113.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes, source theorem anchors,
caps, prior-fingerprint markers, exact difference ordering through bounded
instances, finite instances of the explicit `h/delta` inequalities, and the
threshold schedule. These checks are transcription and falsification aids
only. The universal argument is the displayed `proof sketch` in Sections 4-8.

No bounded successor is scheduled: the isolated variable-`H` issue is
effective selection from the avoidance construction, but T111 already supplies
a separate named symbolic sibling at proof-sketch level, and repeating the same
source without a genuine computable-choice theorem would add no evidence.

TERMINAL_VERDICT: hold as model
