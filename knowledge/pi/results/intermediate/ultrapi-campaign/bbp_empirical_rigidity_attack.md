# BBP empirical measures and the fixed-slice rigidity gap

Audit date: **2026-08-12 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local question has no external source URL; none is invented.

## Outcome and claim status

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained.  Canonical V1 remains a `conjecture`.

This branch does obtain an exact BBP-specific empirical relation and a sharper
sufficient lemma, both recorded as a `proof sketch`.

1. The diagonal decimal BBP recurrence is a summably small moving-coordinate
   copy of the actual \(\times10\) orbit of pi.  Its empirical measures and
   the actual decimal-orbit empirical measures have exactly the same weak-star
   limit set.  Therefore BBP unconditionally supplies probability,
   \(T_{10}\)-invariance, and support inside the decimal orbit closure.
2. The analogous BBP states shadow the \(\times16\) orbit, and synchronized
   two-coordinate BBP states shadow the genuine
   \((T_{10},T_{16})\)-orbit.  Their limit measures are invariant on the
   expected one- or two-circle systems.  None is automatically one circle
   measure invariant under both maps.
3. If one decimal BBP empirical limit is \(T_{10}\)-ergodic, nonatomic, and
   not mutually singular with its \(T_{16}\)-pushforward, then V1 follows.
   This uses only the ergodic-measure dichotomy and Furstenberg's topological
   theorem; positive entropy and Rudolph rigidity are not needed once these
   three hypotheses hold.
4. Exact BBP proves none of those three additional hypotheses.  Host and
   Hochman are almost-everywhere theorems and do not select the named point
   pi.  Rudolph applies only after one has produced a common invariant measure
   on one circle.  Graph and synchronous torus joinings do not satisfy that
   premise.
5. Schmidt's theorem gives one sharp separator: a number can be generic for
   Lebesgue measure under \(\times16\), generic for a nonatomic ergodic
   positive-entropy missing-digit measure under \(\times10\), and still omit
   decimal digit 9.  Its two decimal measures are necessarily singular under
   the \(\times16\) pushforward.  Thus the missing overlap and named-point
   selection are genuine, not technical bookkeeping.

All infinite deductions here are a `proof sketch`; the primary-source audit
is `literature-checked` within its dated scope; and the replay is an
`experiment`.  There are no `machine-checked` claims in this file.

## 1. Target and exact BBP coordinates

Put \(T_b(x)=bx\pmod1\), \(\alpha=\pi\pmod1\), and

\[
 K_\pi=\overline{\{T_{10}^n\alpha:n\ge0\}}.
\]

The previously audited Furstenberg bridge gives

\[
 \mathrm{V1}
 \iff K_\pi=\mathbb T
 \iff T_{16}\alpha\in K_\pi
 \iff\liminf_n\|(10^n-16)\pi\|_{\mathbb T}=0.          \tag{1}
\]

For the standard BBP coefficient and partial sum, write

\[
 a(k)={4\over8k+1}-{2\over8k+4}-{1\over8k+5}-{1\over8k+6},
 \qquad B_n=\sum_{k=0}^n{a(k)\over16^k}.              \tag{2}
\]

The exact rational simplification

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}                           \tag{3}
\]

is positive, and the audited BBP tail estimate is

\[
 0<\pi-B_n\le {16^{-n}\over15(n+1)^2}.                \tag{4}
\]

Define the actual decimal state, the diagonal BBP state, and its moving error
by

\[
 x_n=T_{10}^n\alpha,\qquad
 u_n=\{10^nB_n\},\qquad
 t_n=10^n(\pi-B_n).                                   \tag{5}
\]

Then, on the circle,

\[
 x_n=u_n+t_n,
 \qquad0<t_n\le{(5/8)^n\over15(n+1)^2}.               \tag{6}
\]

The diagonal BBP state obeys the exact nonautonomous recurrence

\[
 u_{n+1}=\left\{10u_n+\epsilon_{n+1}\right\},\qquad
 \epsilon_{n+1}=a(n+1)\left({5\over8}\right)^{n+1},  \tag{7}
\]

and the perturbation is the exact coboundary

\[
                        \epsilon_{n+1}=10t_n-t_{n+1}. \tag{8}
\]

Thus, if \(F_n(z)=10z+\epsilon_{n+1}\pmod1\) and
\(H_n(z)=z+t_n\pmod1\), then

\[
                         H_{n+1}\circ F_n=T_{10}\circ H_n. \tag{9}
\]

Equation (9) is an exact conjugacy with time-dependent coordinates, not a
mixing theorem.  It is the central reason the recurrence cannot be treated as
an independently randomized process.

## 2. Summable empirical shadowing

Let

\[
 \mu_N={1\over N}\sum_{n=0}^{N-1}\delta_{x_n},\qquad
 \eta_N={1\over N}\sum_{n=0}^{N-1}\delta_{u_n}.       \tag{10}
\]

Use the geodesic circle distance and its \(1\)-Wasserstein metric.  Pair the
\(n\)-th atom of \(\eta_N\) with the \(n\)-th atom of \(\mu_N\).  Equations
(6) and the geometric-series bound give

\[
 W_1(\eta_N,\mu_N)
 \le {1\over N}\sum_{n<N}t_n
 \le {1\over15N}\sum_{n\ge0}(5/8)^n
 ={8\over45N}.                                        \tag{11}
\]

Consequently the two empirical sequences have exactly the same weak-star
subsequential limits.  Every such limit \(\mu\) is a probability, and the
usual endpoint telescope gives, for continuous \(f\),

\[
 \int(f\circ T_{10}-f)\,d\mu_N
 ={f(x_N)-f(x_0)\over N}\longrightarrow0.             \tag{12}
\]

Hence

\[
 (T_{10})_*\mu=\mu,\qquad \mu(K_\pi)=1,qquad
 \operatorname{supp}\mu\subseteq K_\pi.              \tag{13}
\]

The support statement follows because every \(\mu_N\) is carried by the
closed set \(K_\pi\).  Nothing in (11)--(13) implies ergodicity,
nonatomicity, or positive entropy.  These three conclusions are not hidden in
the word “empirical.”

The pushforward shadows are just as exact.  Since \(T_{16}\) is
16-Lipschitz,

\[
 W_1((T_{16})_*\eta_N,(T_{16})_*\mu_N)
 \le {128\over45N}.                                   \tag{14}
\]

Thus BBP also identifies the limit of the graph empirical measures

\[
 G_N={1\over N}\sum_{n<N}\delta_{(u_n,T_{16}u_n)}.
\]

If \(\eta_{N_j}\Rightarrow\mu\), then

\[
 G_{N_j}\Rightarrow(\mathrm{id},T_{16})_*\mu.         \tag{15}
\]

This is a graph joining of the two \(T_{10}\)-systems \(\mu\) and
\((T_{16})_*\mu\), invariant under \(T_{10}\times T_{10}\).  It does not
say that its two marginals overlap or coincide.

## 3. Hexadecimal and synchronous BBP empiricals

Put

\[
 y_n=T_{16}^n\alpha,\qquad h_n=\{16^nB_n\},\qquad
 r_n=16^n(\pi-B_n).                                   \tag{16}
\]

Then

\[
 y_n=h_n+r_n,qquad0<r_n\le {1\over15(n+1)^2},
 \qquad h_{n+1}=\{16h_n+a(n+1)\}.                    \tag{17}
\]

Therefore the empirical measures of \((h_n)\) and of the actual
\(\times16\) orbit have the same limits, with the elementary bound

\[
 W_1\left({1\over N}\sum_{n<N}\delta_{h_n},
           {1\over N}\sum_{n<N}\delta_{y_n}\right)
 \le {2\over15N}.                                    \tag{18}
\]

Every limit is \(T_{16}\)-invariant.  Lagarias's unconditional BBP analysis
shows that the hexadecimal omega-limit set is infinite for irrational pi, but
it supplies no positive-entropy empirical limit; its density and uniform
distribution alternatives remain conditional.

Likewise define the synchronized BBP and actual pair empiricals

\[
 J_N={1\over N}\sum_{n<N}\delta_{(u_n,h_n)},\qquad
 \widetilde J_N={1\over N}\sum_{n<N}\delta_{(x_n,y_n)}. \tag{19}
\]

Under the sum product metric, (11) and (18) give

\[
                         W_1(J_N,\widetilde J_N)\le {14\over45N}. \tag{20}
\]

Every weak limit of \(\widetilde J_N\), hence of \(J_N\), is invariant under
\(T_{10}\times T_{16}\).  This is a probability on \(\mathbb T^2\), not a
probability on one circle invariant under both multipliers.  Rudolph's
Corollary 4.11 cannot be applied to it as though the two coordinates were one
measure.  Even product equidistribution of (19) would be a varying-exponent
statement and would not itself place \(16\pi\) in \(K_\pi\).

## 4. A sharp sufficient empirical lemma

**Proposition 4.1 (`proof sketch`).**  Suppose a subsequence of the BBP
empiricals \(\eta_N\) converges weakly to \(\mu\).  Assume:

1. \(\mu\) is ergodic for \(T_{10}\);
2. \(\mu\) is nonatomic; and
3. \(\mu\) and \(\nu=(T_{16})_*\mu\) are not mutually singular.

Then \(K_\pi=\mathbb T\), so V1 holds.

**Proof.**  Equation (13) gives \(T_{10}\)-invariance and support in
\(K_\pi\).  Commutation makes \(\nu\) another \(T_{10}\)-invariant ergodic
probability: it is a factor of the ergodic system \((\mathbb T,\mu,T_{10})\).
Distinct ergodic invariant probabilities for one map are mutually singular,
so hypothesis 3 forces

\[
                              (T_{16})_*\mu=\mu.        \tag{21}
\]

The support of \(\mu\) is now forward invariant under both \(T_{10}\) and
\(T_{16}\).  Nonatomicity makes the countable set of rational points null,
so the support contains an irrational point \(z\).  Furstenberg Theorem IV.1
makes \(\{10^a16^bz:a,b\ge0\}\) dense.  The full orbit lies in the closed
support, hence \(\operatorname{supp}\mu=\mathbb T\).  Since that support is
contained in \(K_\pi\), the latter is the full circle. \(\square\)

Positive \(T_{10}\)-entropy may replace nonatomicity, but it is stronger than
needed.  Under positive entropy, Rudolph Corollary 4.11 would additionally
identify \(\mu\) itself as Lebesgue.  Proposition 4.1 shows that for the V1
support conclusion, Furstenberg already finishes once (21) and one irrational
support point are available.

An all-depth decimal-cylinder affinity lower bound is one verifiable way to
state hypothesis 3.  It must use one depth-independent positive constant and
depths tending to infinity; finite-depth overlap is insufficient.  Boundary
safety is also needed when passing half-open decimal-cylinder masses through
weak convergence.  The previously checked T35/T39/T41 interfaces formalize
those exact qualifications.  The BBP identities (2)--(9) establish no such
affinity lower bound.

## 5. The exact coefficient-level missing estimate

For \(e(z)=\exp(2\pi iz)\), the Fourier coefficients of the BBP empirical are

\[
 \widehat\eta_N(q)={1\over N}\sum_{n<N}e(qu_n).        \tag{22}
\]

The equality \((T_{16})_*\mu=\mu\) would follow if, along one convergent
subsequence, one could prove for every fixed integer \(q\)

\[
 {1\over N}\sum_{n<N}
 \left(e(16qu_n)-e(qu_n)\right)\longrightarrow0.       \tag{23}
\]

Unlike (12), expression (23) does not telescope: the BBP recurrence advances
by multiplication by 10, while (23) compares multiplication by 16 at the
same time.  Substituting (7) merely rewrites the actual decimal orbit through
the summable coboundary (8).  Proving positive entropy similarly requires
growing-block distribution of \((u_n)\), which (11) identifies with the
unknown decimal block distribution of pi.

The exact rational denominator, all-depth two-adic identity, and local gcd
recurrences found in the separate BBP audits do not repair (23).  Their
full-denominator separator can change the remaining odd Archimedean quotient
while retaining all those derived data and a better-than-BBP approximation
rate.  That separator deliberately changes the four-pole coefficient
sequence.  It therefore proves the precise limited statement: any successful
coefficient-specific proof must control the actual selected Archimedean
quotient or (23), rather than only the currently derived denominator and
two-adic invariants.

## 6. Exact Host, Hochman, and Rudolph audit

### Decimal empirical limit

If a decimal empirical limit \(\mu\) is ergodic with positive
\(T_{10}\)-entropy, Hochman Theorem 1.1 with \((a,b)=(10,16)\) says that
\(\mu\)-almost every \(z\) equidistributes under \(T_{16}\).  It does not say
that the named seed pi belongs to this conull set, and even a dense
\(T_{16}\)-orbit of a point in \(K_\pi\) only recovers density of the union
\(\bigcup_tT_{16}^tK_\pi\).  It does not give the fixed inclusion
\(T_{16}\pi\in K_\pi\).

### Hexadecimal empirical limit

If a hexadecimal empirical limit \(\rho\) were invariant, ergodic, and of
positive \(T_{16}\)-entropy, Hochman with \((a,b)=(16,10)\) would make
\(\rho\)-almost every point decimal-normal.  To conclude this for pi one
still needs the additional assertion that pi lies in the theorem's conull
set.  Being a generic point for \(\rho\) under \(T_{16}\) does not supply
that assertion; Section 7 gives a direct counterexample.

### One-circle rigidity

Rudolph Corollary 4.11 does cover \((10,16)\): take coprime generators
\(u=2,v=5\) and exponent vectors \((1,1),(4,0)\), whose determinant is
\(-4\).  But it requires a probability on one circle invariant under both
maps and ergodic for their joint action.  Neither the graph measure (15) nor
the torus measure (19) is that object.  Proposition 4.1 reaches common
invariance only after the separate non-mutual-singularity hypothesis.

Thus the exact applicability order is:

\[
 \text{BBP shadow}
 \Longrightarrow T_{10}\text{-invariant empirical limit}
 \not\Longrightarrow
 \begin{matrix}\text{ergodic, nonatomic,}\
                 \text{or overlapping pushforward,}
 \end{matrix}
 \Longrightarrow\text{no rigidity conclusion}.       \tag{24}
\]

## 7. A single sharp separator

Schmidt's Theorem 2 supplies the relevant named-point separator.  Let
\(\Omega_9=\{0,\ldots,8\}^{\mathbb N}\) with uniform Bernoulli measure and
map a digit stream to the real number having the same digits after the
decimal point.  The coding is injective on all of \(\Omega_9\): at a first
difference in position \(j\), the leading gap is at least \(10^{-j}\), while
all later digits can compensate by at most

\[
 8\sum_{k>j}10^{-k}={8\over9}10^{-j}<10^{-j}.          \tag{25}
\]

In particular, eventually-8 streams cause no endpoint ambiguity; alternate
decimal expansions require an eventual tail of 9.

Apply Schmidt with \((r,s,t)=(16,10,9)\).  Since 16 and 10 are
multiplicatively independent, for almost every source stream the coded number
\(\beta\) is normal in base 16.  Almost every source stream is also normal in
base 9.  Choose \(\beta\) in the intersection.  Then:

1. \(\beta\) is generic for Lebesgue measure under \(T_{16}\), so its
   hexadecimal empirical limit is invariant, ergodic, and has maximal
   entropy \(\log16\).
2. Its decimal empirical measures converge to the uniform Bernoulli measure
   \(\mu_9\) on the missing-digit Cantor set \(K_9\).  This measure is
   nonatomic, \(T_{10}\)-ergodic, and has entropy \(\log9>0\).
3. The decimal digit 9 never occurs, so its decimal orbit closure is the
   proper set \(K_9\), and V1 fails for \(\beta\).
4. Consequently \(\mu_9\perp(T_{16})_*\mu_9\).  Indeed, if they were not
   mutually singular, ergodicity would make them equal; common invariance and
   positive entropy would make \(\mu_9\) Lebesgue by Rudolph, contradicting
   \(h_{\mu_9}(T_{10})=\log9\ne\log10\).

This one point disproves two tempting transfers.  A point can be generic for
an ergodic positive-entropy source measure and still lie outside Host's conull
cross-base-normal set.  It can also have an ergodic nonatomic
positive-entropy decimal empirical limit while the exact pushforward overlap
needed in Proposition 4.1 fails completely.

The separator is not pi and does not preserve the exact coefficient function
(3), which uniquely fixes the sum to pi.  Its role is to show that empirical
invariance, source-base genericity, positive entropy, and BBP-style summable
shadowing do not substitute for a coefficient-specific proof of (23) or
all-depth affinity.

## 8. Source audit and replay

Status of the bounded source checks below: `literature-checked` on
**2026-08-12 UTC**.

| source | exact checked use | local SHA-256 |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | exact BBP series (2), not a distribution theorem | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2), Theorems 3.1, 3.3, 4.1 | perturbed-radix shadowing and the boundary between unconditional infinite limit set and conditional density/uniform distribution | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Furstenberg, [*Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation*](https://doi.org/10.1007/BF01692494), Definition and Theorem IV.1 | non-lacunary joint orbit of an irrational is dense | `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358` |
| Hochman, [*A short proof of Host's equidistribution theorem*](https://arxiv.org/abs/2103.08938v2), Theorem 1.1 | invariant, ergodic, positive-entropy \(T_a\) measure gives the conclusion for measure-almost every point under independent \(T_b\) | `2fa94bec2580725a6b2d3e83761af1510f86061a6090528350c44ea785087d0b` |
| Rudolph, [*×2 and ×3 invariant measures and entropy*](https://doi.org/10.1017/S0143385700005629), Corollary 4.11 | positive-entropy common-invariant rigidity for the exponent-independent pair \((10,16)\) | `9016e14ea8a3125dbea8532c6f8b2230fb24a33fe5e8818db8bcf0f7a7b57c85` |
| Schmidt, [*On Normal Numbers*](https://doi.org/10.2140/pjm.1960.10.661), Theorem 2, printed p. 662 | the missing-decimal-digit Cantor measure gives base-16 normal points for \((r,s,t)=(16,10,9)\) | `28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67` |

Fresh searches for BBP empirical entropy, invariant measures, Host generic
points, and BBP joinings found no primary theorem supplying ergodicity,
nonatomicity, positive decimal entropy, pushforward overlap, or the named-pi
typicality missing above.  This is a bounded applicability result, not an
exhaustive absence or novelty claim.

The companion
[`bbp_empirical_rigidity_check.py`](bbp_empirical_rigidity_check.py) pins the
target and all six source PDFs, checks source markers, replays (3), (7), (8),
(17), and the summable bounds with exact rational arithmetic, and prints a
bounded cylinder-entropy/affinity table.  Every finite output is an
`experiment`; none is evidence for an infinite statement about pi.
Checker SHA-256:
`0b943566c03dc083be1321499b66e6f6cf1766ad7f11d87b657ebf52f6572953`.

## Bottom line

The exact four-pole BBP recurrence does produce invariant empirical limits
for the decimal orbit, but only because it is summably conjugate to that very
orbit.  It produces graph and synchronous joinings, but neither is the common
one-circle measure needed by rigidity.  Proposition 4.1 identifies a genuinely
sufficient and entropy-free finish: one ergodic nonatomic decimal empirical
limit with nonzero all-depth overlap with its \(\times16\) pushforward.  BBP
currently proves the ambient limit, invariance, and support, while all three
decisive hypotheses remain open.  Therefore the fixed return (1), and hence
V1, remain unproved.
