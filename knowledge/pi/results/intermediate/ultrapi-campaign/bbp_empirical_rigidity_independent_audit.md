# Independent audit: BBP empirical measures and fixed-slice rigidity

Audit date: **2026-08-12 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local question has no external source URL; none is invented.

Audited artifacts:

- [bbp_empirical_rigidity_attack.md](bbp_empirical_rigidity_attack.md),
  SHA-256
  `80fc0a6f9bd159dc36438a78ec10b35c76b433c2bae084750b3c34199d97534c`;
- [bbp_empirical_rigidity_check.py](bbp_empirical_rigidity_check.py),
  SHA-256
  `0b943566c03dc083be1321499b66e6f6cf1766ad7f11d87b657ebf52f6572953`.

Independent replay:

- [bbp_empirical_rigidity_independent_check.py](bbp_empirical_rigidity_independent_check.py),
  SHA-256
  `96482567af37c9676d0f4eb5ee9f1ef578e880d26cea3f43d9682a58429bd469`.

## Verdict

**PASS.**

The BBP recurrences, tail estimates, moving conjugacy, Wasserstein constants,
empirical-limit identifications, invariance and support deductions, ergodic
nonsingularity lemma, Fourier criterion, and Schmidt separator all rederive.
The cited versions of Furstenberg, Hochman, Rudolph, Schmidt, BBP, and Lagarias
have the hypotheses claimed in the report.  In particular, no endpoint,
subsequence, support, factor-ergodicity, or pushforward gap was found.

Two phrases merit editorial clarification but do not affect the result.

1. “V1 fails for \(\beta\)” in Section 7 means that the **analogue** of V1
   with \(\pi\) replaced by \(\beta\) fails; canonical V1 remains exclusively
   the statement about pi.
2. The point outside “Host's conull cross-base-normal set” is \(\beta\) viewed
   as a generic point for **Lebesgue measure under \(T_{16}\)**.  Viewed as a
   generic point for the missing-digit measure under \(T_{10}\), the same
   \(\beta\) is base-16 normal and is in Host's conclusion set.  The intended
   base-16-to-base-10 direction is clear from the preceding paragraph.

All infinite arguments here and in the audited report retain the label
`proof sketch`; the source applicability check is `literature-checked` as of
the audit date; and both finite replays are `experiment`.  No fixed-sixteen
return and no proof of V1 is present.  Canonical V1 remains a `conjecture`.

## 1. Exact BBP coordinates and tail

For

\[
 a(k)={4\over8k+1}-{2\over8k+4}-{1\over8k+5}-{1\over8k+6},
\]

common-denominator reduction gives exactly

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}.
\]

The numerator and denominator are positive for \(k\ge0\).  For \(k\ge1\),
direct expansion gives

\[
\begin{aligned}
 &(2k+1)(4k+3)(8k+1)(8k+5)
     -k^2(120k^2+151k+47)\\
 &\qquad=392k^4+873k^3+665k^2+194k+15>0.
\end{aligned}
\]

Thus \(0<a(k)<k^{-2}\).  With
\(B_n=\sum_{k=0}^na(k)16^{-k}\), the BBP identity and positivity imply

\[
 0<\pi-B_n
 <{1\over(n+1)^2}\sum_{k=n+1}^{\infty}16^{-k}
 ={16^{-n}\over15(n+1)^2}.
\]

The audited weak inequality is therefore valid.  Multiplication by \(10^n\)
gives

\[
 t_n=10^n(\pi-B_n)
 \le{(5/8)^n\over15(n+1)^2}.
\]

Writing \(u_n=\{10^nB_n\}\), exact rational arithmetic gives

\[
 u_{n+1}=\{10u_n+\epsilon_{n+1}\},\qquad
 \epsilon_{n+1}=a(n+1)(5/8)^{n+1}.
\]

Moreover,

\[
\begin{aligned}
 10t_n-t_{n+1}
 &=10^{n+1}\bigl((\pi-B_n)-(\pi-B_{n+1})\bigr)\\
 &=10^{n+1}{a(n+1)\over16^{n+1}}
 =\epsilon_{n+1}.
\end{aligned}
\]

Consequently, for \(F_n(z)=10z+\epsilon_{n+1}\pmod1\) and
\(H_n(z)=z+t_n\pmod1\),

\[
 H_{n+1}(F_nz)
 =10z+\epsilon_{n+1}+t_{n+1}
 =10z+10t_n
 =T_{10}(H_nz).
\]

This verifies the exact moving-coordinate conjugacy, including its sign and
index.  It is nonautonomous and supplies no mixing statement.

## 2. Wasserstein bounds and equality of empirical-limit sets

On the geodesic circle,

\[
 d_{\mathbb T}(u_n,x_n)\le t_n
\]

even if \(u_n+t_n\) crosses the endpoint.  Pairing corresponding atoms gives

\[
 W_1(\eta_N,\mu_N)
 \le {1\over N}\sum_{n<N}t_n
 \le {1\over15N}\sum_{n\ge0}(5/8)^n
 ={8\over45N}.
\]

Because this tends to zero, a subsequence of \((\eta_N)\) converges weakly if
and only if the matching subsequence of \((\mu_N)\) does, and their limits
are equal.  This proves equality of the complete sets of weak-star
subsequential limits, not merely the existence of one common limit.

The circle map \(T_{16}\) is 16-Lipschitz, so pushforward contraction with
the Lipschitz constant gives

\[
 W_1((T_{16})_*\eta_N,(T_{16})_*\mu_N)
 \le16W_1(\eta_N,\mu_N)
 \le {128\over45N}.
\]

For the hexadecimal coordinates,

\[
 r_n=16^n(\pi-B_n)\le {1\over15(n+1)^2},
\]

and \(\sum_{j\ge1}j^{-2}<2\).  Hence the corresponding average distance is
less than \(2/(15N)\).  Under the sum metric on \(\mathbb T^2\), the two
bounds add to

\[
 {8\over45N}+{2\over15N}={14\over45N}.
\]

All four constants in the report are therefore correct.

## 3. Invariance, support, graph measures, and synchronized measures

For every continuous \(f\), the actual decimal orbit satisfies the exact
endpoint telescope

\[
 {1\over N}\sum_{n=0}^{N-1}
 (f(T_{10}x_n)-f(x_n))={f(x_N)-f(x_0)\over N}.
\]

Boundedness of \(f\) makes the right side tend to zero.  Passing along any
weakly convergent subsequence proves \((T_{10})_*\mu=\mu\).  There is no
missing endpoint term and no need for convergence of the entire empirical
sequence.

Every \(\mu_N\) is carried by the closed orbit closure \(K_\pi\).  Portmanteau
for the closed set \(K_\pi\) gives \(\mu(K_\pi)=1\), and hence
\(\operatorname{supp}\mu\subseteq K_\pi\).  This direction of the closed-set
inequality is correct.

The graph empirical is exactly

\[
 G_N=(\mathrm{id},T_{16})_*\eta_N.
\]

Continuity of the graph map proves
\(G_{N_j}\Rightarrow(\mathrm{id},T_{16})_*\mu\).  Since \(T_{10}\) and
\(T_{16}\) commute, this graph measure is invariant under
\(T_{10}\times T_{10}\), with marginals \(\mu\) and
\((T_{16})_*\mu\).  It neither identifies nor overlaps those marginals.

Similarly, the actual synchronized pairs are an orbit of
\(T_{10}\times T_{16}\), so the same endpoint telescope on \(\mathbb T^2\)
proves invariance of every synchronized limit.  Such a measure lives on two
circles.  The report correctly refuses to treat it as one measure invariant
under both maps.

## 4. Ergodic, nonatomic, nonsingular-pushforward lemma

Let \(\mu\) be a decimal empirical limit with the three extra hypotheses in
Proposition 4.1, and put \(\nu=(T_{16})_*\mu\).

First, commutation gives \((T_{10})_*\nu=\nu\).  The factor map \(T_{16}\)
also preserves ergodicity: if \(A\) is \(T_{10}\)-invariant modulo \(\nu\),
then \(T_{16}^{-1}A\) is \(T_{10}\)-invariant modulo \(\mu\), so
\(\nu(A)=\mu(T_{16}^{-1}A)\) is zero or one.

Second, distinct ergodic invariant probabilities for the same continuous map
are mutually singular.  Indeed, if \(\mu\ne\nu\), choose continuous \(f\)
with \(\int f\,d\mu\ne\int f\,d\nu\).  By Birkhoff, the two full-measure sets
on which the time average of \(f\) equals the respective integral are
disjoint invariant measurable sets.  Thus \(\mu\perp\nu\).  The assumed
failure of mutual singularity therefore forces

\[
 (T_{16})_*\mu=\mu.
\]

For a continuous map \(T\), equality \(T_*\mu=\mu\) implies
\(T(\operatorname{supp}\mu)\subseteq\operatorname{supp}\mu\): the inverse
image of any neighborhood of \(Tx\) is a neighborhood of \(x\).  The support
is consequently forward invariant under both \(T_{10}\) and \(T_{16}\).

A nonatomic probability assigns zero mass to the countable rational points.
Since its support has full measure, it contains an irrational \(z\).
Furstenberg's Theorem IV.1 applies to the non-lacunary semigroup
\(\{10^a16^b:a,b\ge0\}\), so the joint forward orbit of \(z\) is dense.  That
orbit lies in the closed support, forcing

\[
 \operatorname{supp}\mu=\mathbb T\subseteq K_\pi.
\]

Thus \(K_\pi=\mathbb T\).  This proves the stated **sufficient** lemma.  The
BBP identities do not prove any of its three added hypotheses.

Positive \(T_{10}\)-entropy can replace nonatomicity here because an ergodic
atomic invariant probability is supported on a finite orbit and has zero
entropy.  The report correctly presents this only as a stronger substitute.

## 5. Fourier equivalence

For the convention \(\widehat\mu(q)=\int e(qx)\,d\mu(x)\),

\[
 \widehat{(T_{16})_*\mu}(q)=\widehat\mu(16q).
\]

If \(\eta_{N_j}\Rightarrow\mu\), then for every fixed integer \(q\),

\[
 {1\over N_j}\sum_{n<N_j}
 \bigl(e(16qu_n)-e(qu_n)\bigr)
 \longrightarrow\widehat\mu(16q)-\widehat\mu(q).
\]

Therefore vanishing of these limits for all \(q\) is equivalent to equality
of all Fourier coefficients of \((T_{16})_*\mu\) and \(\mu\).  Trigonometric
polynomial density then gives equality of the measures.  The quantifier must
use one common convergent subsequence and every fixed \(q\); the report does
so.  The comparison is same-time multiplication by 16 and has no endpoint
telescope analogous to the \(T_{10}\)-orbit identity.

## 6. Primary-source applicability

The following bounded checks are `literature-checked` on the audit date.

| primary source | audited implication | result |
|---|---|---|
| Bailey--Borwein--Plouffe, [Theorem 1](https://doi.org/10.1090/S0025-5718-97-00856-9) | the exact four-pole series for pi | PASS |
| Lagarias, [Theorems 3.1 and 3.3](https://arxiv.org/abs/math/0101055v2) | perturbed and actual radix orbits asymptotically shadow; finitely many limit points iff the represented number is rational | PASS |
| Furstenberg, [Theorem IV.1](https://doi.org/10.1007/BF01692494) | a non-lacunary multiplicative semigroup has dense orbit at every irrational circle point | PASS |
| Hochman, [Theorem 1.1](https://arxiv.org/abs/2103.08938v2) | an invariant, ergodic, positive-entropy \(T_a\) measure gives \(T_b\)-Lebesgue equidistribution for measure-almost every point when \(a,b\) are multiplicatively independent | PASS |
| Rudolph, [Corollary 4.11](https://doi.org/10.1017/S0143385700005629) | positive-entropy rigidity extends from coprime generators to exponent-independent products | PASS |
| Schmidt, [Theorem 2](https://doi.org/10.2140/pjm.1960.10.661) | the base-\(t\)-to-base-\(s\) Cantor coding is base-\(r\) normal almost everywhere when \(r\) and \(s\) are multiplicatively independent | PASS |

The pinned local PDFs have exactly the SHA-256 values recorded in the audited
report.  The independent checker extracts and checks the corresponding
theorem markers from those PDFs in a temporary directory.

Hochman's theorem is explicitly almost everywhere.  Neither membership in an
orbit closure nor genericity for a different transformation promotes the
named point pi into that conull set.  The report's application boundary is
correct.

Rudolph's corollary covers \(10\) and \(16\) by taking the coprime generators
\(u=2,v=5\), with exponent vectors

\[
 10=u^1v^1,\qquad16=u^4v^0,qquad
 \det\begin{pmatrix}1&1\\4&0\end{pmatrix}=-4\ne0.
\]

Its premise is a common one-circle invariant probability ergodic for the
joint action.  In Proposition 4.1, \(T_{10}\)-ergodicity would imply joint
ergodicity after common invariance is established.  The graph and synchronized
torus measures do not themselves meet this premise, exactly as the report
states.

## 7. Schmidt separator

Schmidt defines \(T_{s,t}\) by reading the base-\(t\) digits of a source point
as base-\(s\) digits, with \(1<t<s\).  Theorem 2 says that if \(r\) and \(s\)
are multiplicatively independent, then \(T_{s,t}\xi\) is base-\(r\) normal
for Lebesgue-almost every source \(\xi\).  The substitution

\[
 (r,s,t)=(16,10,9)
\]

meets every hypothesis.  Intersecting the theorem's full-measure source set
with the full-measure set of base-9-normal sources selects \(\xi\) such that
\(\beta=T_{10,9}\xi\) is base-16 normal and its decimal digit stream is the
same base-9-normal stream over \(\{0,\ldots,8\}\).

The decimal code is injective.  If two streams first differ at position
\(j\), the leading difference is at least \(10^{-j}\), while the maximum
possible cancellation from later digits is

\[
 8\sum_{k>j}10^{-k}={8\over9}10^{-j}<10^{-j}.
\]

Thus there is no endpoint ambiguity.  Base-9 normality makes the source shift
generic for uniform Bernoulli measure on nine symbols and makes its shift
orbit dense in the full nine-symbol shift.  Under the injective continuous
decimal coding, \(\beta\) is therefore \(T_{10}\)-generic for \(\mu_9\), and
its decimal orbit closure is exactly the proper missing-digit Cantor set
\(K_9\).

The conclusions in the report follow:

- base-16 normality makes \(\beta\) generic for Lebesgue measure under
  \(T_{16}\);
- \(\mu_9\) is nonatomic, \(T_{10}\)-ergodic, and has entropy \(\log9\);
- \(\beta\) omits decimal digit 9 despite its base-16 genericity.

Finally, \(\mu_9\perp(T_{16})_*\mu_9\).  If not, both are ergodic
\(T_{10}\)-invariant probabilities, so the dichotomy proved above makes them
equal.  Then \(\mu_9\) is common invariant, jointly ergodic because it is
already \(T_{10}\)-ergodic, and has positive \(T_{10}\)-entropy.  Rudolph's
corollary would make it Lebesgue, contradicting either its support on \(K_9\)
or \(h_{\mu_9}(T_{10})=\log9<\log10\).

This separator is existential and is not pi.  It validates only the stated
failure of the tempting empirical transfers.

## 8. Independent replay and scope

The independent checker:

- pins the canonical statement, audited report, audited checker, and all six
  primary-source PDFs;
- checks the coefficient identity and strict \(a(k)<k^{-2}\) majorant through
  depth 120 with exact rational arithmetic;
- checks 96 decimal and hexadecimal recurrences, coboundary identities, and
  moving-coordinate identities using a deeper exact rational surrogate;
- rederives \(8/45\), \(128/45\), \(2/15\), and \(14/45\);
- checks the positive decimal-code separation gaps and Rudolph exponent
  determinant; and
- confirms that the report explicitly retains V1 as a `conjecture` and
  disclaims a fixed return.

The primary checker and independent checker both return `PASS`.  Their finite
outputs remain `experiment`; they do not establish ergodicity,
nonatomicity, nonsingularity, entropy, fixed return, or V1.

## Bottom line

The report identifies a correct conditional route: an ergodic nonatomic
decimal empirical limit that is not mutually singular with its
\(T_{16}\)-pushforward would force full decimal orbit closure.  BBP supplies
the exact moving shadow, common subsequential limits, invariance, and support,
but none of the three decisive extra hypotheses.  The primary theorems do not
fill that gap, and Schmidt shows why genericity or positive entropy in one
base cannot be transferred to the named point in another base.  The audit
therefore passes without upgrading the claim: fixed-sixteen return and V1
remain unproved.
