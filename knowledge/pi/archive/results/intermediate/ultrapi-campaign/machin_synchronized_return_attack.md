# Synchronized Machin returns: an exact criterion and three denominator barriers

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No complete proof that every finite decimal word occurs in pi was obtained.
Canonical V1 remains a `conjecture`.

There is nevertheless a clean result about the proposed route.  Fix an integer
\(c\ge2\) multiplicatively independent of ten.  Producing unbounded
\(N_j\) and rational numbers \(A_j\) such that

\[
 (10^{N_j}-c)A_j\in\mathbb Z,
 \qquad |\pi-A_j|=o(10^{-N_j})                         \tag{1}
\]

is not merely sufficient for V1: it is **equivalent** to V1.  Thus the
synchronization target is logically exact, but it is not a weaker
intermediate statement.

Three proposed ways of engineering (1) were then audited.

1. A fixed \(c\) permits only bounded powers of 2 and 5 in a synchronized
   reduced denominator.  This rules out the full Hutton sequence by T63/T66,
   the direct \(1/2,1/3\) sequence, and infinitely many Taylor depths of every
   fixed denominator-safe split considered here.
2. Synchronizing the standard *natural common denominator* of a positive
   Machin truncation is impossible: its certified error times that denominator
   is always at least \(32/35\), while (1) requires this product to tend to
   zero.
3. Using only the fully reduced denominator leaves a logical escape through
   enormous cross-term cancellation.  For all four explicit Hutton/split
   identities, however, a private-prime theorem proves along an infinite
   depth subsequence that the reduced denominator times the actual error tends
   to infinity exponentially.  Exact finite replay finds the same failure at
   \(R=81\), by margins from \(10^{91}\) to \(10^{911}\).

The deductions are `proof sketch`; the companion exact replay is an
`experiment`.  The bounded source search is `literature-checked` as of the
date above.  Nothing here is a `candidate resolution`.

## 1. Exact normalization of the synchronized-return target

Let

\[
 K=\overline{\{10^n\pi\pmod1:n\ge0\}}\subset\mathbb T.
\]

The Furstenberg bridge already audited in
[`furstenberg_bbp_bridge.md`](furstenberg_bbp_bridge.md) gives, whenever
\(c\ge2\) is multiplicatively independent of ten,

\[
 \mathrm{V1}
 \quad\Longleftrightarrow\quad
 c\pi\in K
 \quad\Longleftrightarrow\quad
 \liminf_{N\to\infty}\|(10^N-c)\pi\|_{\mathbb T}=0.     \tag{2}
\]

The following rational version makes every quantifier explicit.

**Exact synchronization criterion (`proof sketch`).**  Put
\(Q_N=10^N-c\), which is positive for all sufficiently large \(N\).  The
last condition in (2) holds if and only if there are \(N_j\to\infty\) and
\(A_j\in\mathbb Q\) satisfying (1).  Equivalently, the reduced denominator of
\(A_j\) divides \(Q_{N_j}\) and its error is \(o(10^{-N_j})\).

Indeed, (1) gives

\[
 \|Q_{N_j}\pi\|_{\mathbb T}
 \le Q_{N_j}|\pi-A_j|=o(1).                              \tag{3}
\]

Conversely, along any subsequence on which the left side tends to zero, choose
\(z_j\in\mathbb Z\) nearest to \(Q_{N_j}\pi\) and set
\(A_j=z_j/Q_{N_j}\).  Then

\[
 { |\pi-A_j| \over 10^{-N_j}}
 ={10^{N_j}\over Q_{N_j}}
   \|Q_{N_j}\pi\|_{\mathbb T}\longrightarrow0.         \tag{4}
\]

This equivalence is useful for rejecting insufficient constructions.  It also
prevents a false progress claim: finding (1) would already be a proof of V1,
not a denominator lemma awaiting a routine transfer.

## 2. A fixed multiplier has bounded decimal-primary capacity

For \(p\in\{2,5\}\), once \(N\) is large enough that
\(v_p(10^N)>v_p(c)\), the two summands have unequal \(p\)-adic valuations and

\[
                       v_p(10^N-c)=v_p(c).                \tag{5}
\]

Consequently, if a reduced denominator \(q\mid Q_N\), then

\[
               v_2(q)\le v_2(c),\qquad v_5(q)\le v_5(c).\tag{6}
\]

This is already fatal to two previously tested families.

- T63 and T66 prove that the reduced Hutton lower denominator is odd and has
  exact 5-adic exponent \(\lfloor\log_5 T\rfloor\) at maximum Taylor exponent
  \(T\).  It therefore cannot divide \(10^N-c\) beyond finitely many depths for
  any fixed \(c\).
- The direct \(\arctan(1/2)+\arctan(1/3)\) shadow has exact two-adic
  preperiod \(R-2\) in that report's notation, as audited in
  [`euler_two_three_attack.md`](euler_two_three_attack.md).  Equation (6)
  likewise excludes all sufficiently deep truncations.

The denominator-safe identities avoid powers of 2, but a fixed identity still
has an infinite 5-adic obstruction.  Write it as

\[
 {\pi\over4}=\sum_{i=1}^J c_i\arctan x_i,
 \quad x_i={a_i\over b_i}\in(0,1),
 \quad \gcd(b_i,10)=1,                                  \tag{7}
\]

and suppose the linear shadow \(S=\sum_i c_ix_i\) is a 5-adic unit.  For
\(e\ge1\), let \(T_e=5^e+2\equiv3\pmod4\), and truncate each series through exponent
\(T_e\).  The only exponent at most \(T_e\) divisible by \(5^e\) is \(5^e\).
After multiplication by \(5^e\), all other terms vanish modulo 5, while
Fermat gives \(x_i^{5^e}\equiv x_i\pmod5\).  Hence

\[
 5^eL_{T_e+2}\equiv4S\not\equiv0\pmod5,
 \qquad v_5(\operatorname{den}L_{T_e+2})=e.              \tag{8}
\]

Here the subscript follows the convention below: \(L_R\) has first omitted
exponent \(R\), so its largest included exponent is \(R-2\).

All four displayed identities have 5-adic-unit \(S\).  Thus no one of
them can use these infinitely many depths in a fixed-\(c\) synchronization.
This does not exclude varying the identity with the depth and arranging new
5-adic cancellations; it identifies an additional condition such a
construction must satisfy.

## 3. Natural-denominator synchronization has an exact error barrier

Let \(R\equiv1\pmod4\), \(R\ge5\), put \(T=R-2\), and let \(L_R\) be the
positive identity's alternating lower truncation through exponent \(T\).
For \(0<x<1\), the first two omitted terms give

\[
 \arctan x-\sum_{\substack{1\le r\le T\\r\ {\rm odd}}}
 {\chi_4(r)x^r\over r}
 >{x^R\over R}-{x^{R+2}\over R+2}
 \ge {2x^R\over R(R+2)}.                                \tag{9}
\]

It follows that the actual positive error
\(\delta_R=\pi-L_R\) obeys

\[
 \delta_R\ge {8\over R(R+2)}\sum_i c_ix_i^R.            \tag{10}
\]

The standard safe natural denominator is

\[
 D_R=\operatorname{lcm}\{1,3,\ldots,T\}
               \prod_{i=1}^J b_i^T.                    \tag{11}
\]

Assume \(J\ge2\), as in every identity under test, and put
\(P=\prod_i b_i\).  Since \(a_i,c_i\ge1\) and \(b_i\ge2\), arithmetic--geometric
mean gives

\[
\begin{aligned}
 D_R\delta_R
 &\ge {8\over R(R+2)}P^T\sum_i b_i^{-(T+2)}\\
 &\ge {8J\over R(R+2)}
       P^{(T(J-1)-2)/J}\\
 &\ge {8\,2^{T-1}\over(T+2)(T+4)}
 \ge {32\over35}.                                      \tag{12}
\end{aligned}
\]

The last expression is increasing for \(T\ge3\).  Therefore, if one tries to
engineer the strong divisibility \(D_R\mid Q_N\), then

\[
                 10^N\delta_R\ge D_R\delta_R\ge32/35,   \tag{13}
\]

contradicting the little-oh requirement in (1).  This is an unconditional
obstruction to synchronizing all of the displayed term denominators and the
odd exponent lcm with one repunit-like number.

The reduced denominator \(q_R=\operatorname{den}(L_R)\) can be smaller than
\(D_R\).  With cancellation factor \(C_R=D_R/q_R\), (12) becomes

\[
 q_R\delta_R={D_R\delta_R\over C_R}.                    \tag{14}
\]

Thus a reduced-denominator construction is not ruled out by (12), but it
must create cancellation large enough to dominate the entire height/error
product in (12).  Merely making every angle smaller does not do this.

## 4. Private primes expose height leakage in the reduced denominator

There is a second exact obstruction that uses the *reduced* denominator.
Suppose a prime \(p\equiv3\pmod4\) divides exactly one argument denominator
\(b_j\), with \(\beta=v_p(b_j)\ge1\), and
\(p\nmid4c_ja_j\).  For odd \(e\), take \(T=p^e\equiv3\pmod4\).  The endpoint
term of component \(j\) has valuation

\[
                         -\beta T-e.                     \tag{15}
\]

Every earlier term in that component has denominator valuation at most
\(\beta(T-2)+e-1\), and every other component has at worst the exponent
denominator contribution \(e\).  The endpoint is therefore the unique term
of least \(p\)-adic valuation.  No cross-component cancellation is possible,
and

\[
                 v_p(\operatorname{den}L_{T+2})=\beta T+e.\tag{16}
\]

Let \(X=\max_i x_i\), attained with coefficient \(c_*\).  Combining (10)
and (16),

\[
 q_{T+2}\delta_{T+2}
 \ge {8c_*X^2\over(T+2)(T+4)}p^e(p^\beta X)^T.           \tag{17}
\]

Since \(p^e=T\), the right side tends to infinity exponentially whenever
\(p^\beta X>1\).  On this subsequence, not only does (1) fail: the rational
shadow becomes exponentially *worse* than the \(1/q\) scale.

Each fixed identity has such a certificate:

| identity | private component | \(p\) | \(X\) | \(pX\) |
|---|---:|---:|---:|---:|
| Hutton | \(1/7\) | 7 | \(1/3\) | \(7/3\) |
| first split | \(2/11\) | 11 | \(2/11\) | 2 |
| second split | \(3/79\) | 79 | \(1/11\) | \(79/11\) |
| third split | \(6/127\) | 127 | \(6/127\) | 6 |

This phenomenon explains why recursive splitting can improve decimal
accuracy while worsening approximation quality relative to the reduced
denominator.  A tiny leaf with a private, large denominator fixes the exact
Gaussian identity; a larger leaf controls the Archimedean Taylor error.

The theorem is for each fixed identity and its private-prime depth
subsequence.  A still-unexcluded construction could change the identity at
every step, deliberately share all large prime factors between leaves, and
force huge numerator cancellations.  No such construction was found.

## 5. Exact finite falsification

The checker recomputes the reduced fractions, rather than using only the safe
denominator (11).  At \(R=81\), the certified lower bound in (10) gives:

| identity | reduced denominator digits | digits of \(D_R/q_R\) | \(\lfloor\log_{10}(q_R\delta_R^{\rm lower})\rfloor\) |
|---|---:|---:|---:|
| Hutton | 133 | 5 | 91 |
| first split | 176 | 6 | 113 |
| second split | 387 | 4 | 300 |
| third split | 1022 | 6 | 911 |

Thus none of these four \(R=81\) shadows can meet even the necessary
finite-scale inequality \(10^N\delta_R<1\) if its denominator divides a
number \(10^N-c\): divisibility implies \(10^N>q_R\), while already
\(q_R\delta_R>10^{91}\) in the weakest row.  This is an `experiment` at one
finite scale, not an asymptotic theorem beyond the private-prime subsequences
proved above.

There is also an independent modular gate.  If \(p\nmid10\), \(p\mid q_R\),
and \(q_R\mid10^N-c\), then necessarily

\[
                         c\in\langle10\rangle\pmod p.     \tag{18}
\]

For the Furstenberg multiplier \(c=16\), this fails at the first split's
private prime \(p=11\) and the second split's \(p=79\).  It holds for
\(p=7,127\), so it is deliberately not presented as a universal obstruction.
Changing \(c\) can change (18), but the same one \(c\) must pass every prime
in an infinite proposed sequence.

## 6. Why Gaussian factorization does not yet repair the route

A positive rational angle decomposition is equivalent to a Gaussian product

\[
              \prod_i(b_i+ia_i)^{c_i}=M(1+i),\qquad M>0.\tag{19}
\]

It is tempting to factor \(Q_N(1+i)\) and use the Gaussian factors as Machin
arguments.  Equation (19), however, controls norms and angle addition; it does
not make the real parts \(b_i\), their Taylor powers \(b_i^T\), or the odd
exponent denominators divide \(Q_N\).  Requiring all of those divisibilities
falls under (13).  Requiring only the final reduced denominator to divide
\(Q_N\) demands precisely the exceptional cancellation isolated in (14), plus
the simultaneous discrete-log conditions (18).

The elementary split

\[
 \arctan x=\arctan u+\arctan{\,x-u\over1+xu}            \tag{20}
\]

has the same height leak: balancing the two child angles generally makes the
second denominator roughly the product of the parent and split denominators.
Iteration improves the real bracket but introduces private denominator
coordinates.  The exact computations above show that the resulting reduced
denominator is very close in digit length to (11), not smaller by the enormous
factor (14) would require.

Signed Machin identities could evade the positive-error lower bound (10) by
Archimedean cancellation.  They would then need a new, rigorous remainder
cancellation theorem *and* exact reduced-denominator synchronization.  No
checked identity or source supplies both.  Treating alternating numerical
cancellation as exact would be another unproved phase assumption.

## 7. Dated literature check

The search was restricted to primary sources and exact applicability.

- Furstenberg, [*Disjointness in Ergodic Theory, Minimal Sets, and a Problem
  in Diophantine Approximation*](https://doi.org/10.1007/BF01692494), Theorem
  IV.1, supplies the topological implication used in (2).  The locally pinned
  PDF and source audit are recorded in `furstenberg_bbp_bridge.md`.
- Gao--Yip, [*On the fractional parts of certain sequences of
  \(\xi\alpha^n\)*, arXiv:2408.02972v2](https://arxiv.org/abs/2408.02972v2),
  explicitly place fixed-pair questions among the difficult cases and prove
  interval-count results only under additional Diophantine hypotheses.  No
  theorem there proves a shrinking return to zero for
  \((10^N-c)\pi\).
- Rudnick--Zaharescu, [*The distribution of spacings between fractional parts
  of lacunary sequences*, arXiv:math/9912103](https://arxiv.org/abs/math/9912103),
  prove Poissonian spacing behavior for almost every multiplier.  This metric
  statement cannot be specialized to the fixed multiplier pi.
- DLMF [4.24.E3](https://dlmf.nist.gov/4.24#E3) is the analytic source for the
  alternating arctangent series and hence (9)--(10).
- The refinement literature already pinned in
  `machin_angle_splitting_attack.md` constructs rapidly convergent Machin
  identities, but supplies no repunit divisibility or selected reduced-height
  cancellation theorem.

Searches on 2026-08-12 UTC included `Diophantine approximation denominators
b^n-a fractional parts lacunary sequence`, `distribution fractional parts
alpha (b^n-c)`, and the exact Gao--Yip and Rudnick--Zaharescu records.  No
checked primary source proved (1) for pi.  This is a bounded negative
applicability finding, not a novelty claim.

## 8. Exact replay and sharp conclusion

The companion checker is
[`machin_synchronized_return_attack_check.py`](machin_synchronized_return_attack_check.py).
It uses integer arithmetic and `Fraction` throughout.  A clean run reports:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
fixed_c_primary_valuation_exact_checks=126
natural_denominator_lower_bound_exact_checks=112
fixed_identity_five_adic_exact_checks=12
private_prime_height_exact_checks=24
private name=Hutton p=7 denominator_digits=11 floor_log10_q_error_lower=5 v_p_q=8
private name=split-1 p=11 denominator_digits=24 floor_log10_q_error_lower=12 v_p_q=12
private name=split-2 p=79 denominator_digits=387 floor_log10_q_error_lower=300 v_p_q=80
private name=split-3 p=127 denominator_digits=1645 floor_log10_q_error_lower=1470 v_p_q=128
reduced_denominator_scale_exact_checks=8
scale name=Hutton R=81 q_digits=133 natural_over_reduced_digits=5 floor_log10_q_error_lower=91
scale name=split-1 R=81 q_digits=176 natural_over_reduced_digits=6 floor_log10_q_error_lower=113
scale name=split-2 R=81 q_digits=387 natural_over_reduced_digits=4 floor_log10_q_error_lower=300
scale name=split-3 R=81 q_digits=1022 natural_over_reduced_digits=6 floor_log10_q_error_lower=911
c16_private_prime_subgroup_exact_checks=4
all exact assertions passed
```

**Verdict.**  The synchronized-return idea is exact and would prove V1, but
the straightforward Machin implementations fail for structural reasons, not
for lack of Taylor accuracy.  A successful continuation must simultaneously

1. keep the reduced denominator's 2- and 5-parts bounded by one fixed \(c\);
2. make that reduced denominator divide \(10^N-c\), including every
   discrete-log compatibility;
3. obtain error \(o(10^{-N})\), which is stronger than \(o(1/q)\) when the
   synchronized denominator \(q\) is smaller than \(10^N\); and
4. create cancellations far beyond the natural-denominator and private-prime
   barriers above.

No current split tree, Gaussian factorization, or checked literature theorem
provides those four properties.  More convergence-rate work without a
reduced-height synchronization mechanism is a dead end for this route.
