# T79: post-T78 arithmetic-opportunity scout

Date: 2026-08-07 UTC.

Status: `proof sketch` literature-and-exact-arithmetic audit. This report proves
no normality, equidistribution, C1, C2, or canonical near-return estimate. The
only finite computations are the reproducible sanity checks in `verify_note.py`.

## 1. Scope and canonical statement

`canonical_statement.txt` is a byte-for-byte copy of the immutable local source;
its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

Thus the target remains the ordered, diagonal-inclusive count

\[
 Q_\pi(n,N)=\#\{(i,j):0\leq i,j<N,
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\},
\]

with quantifiers \(\forall A\ \exists n_0\ \forall n\geq n_0\ \exists N\).
Nothing below changes these quantifiers.

## 2. Exclusion and overlap table

| route or representation | disposition | reason |
|---|---|---|
| Bailey--Borwein--Plouffe base-16 series | previously covered | T63 audits its Theorem 1, equations (1.2)--(1.3); the agenda expressly excludes the standard BBP formula. |
| Zudilin recurrence/arctangent route | previously covered | T63 records the corrected source and T68 has a machine-checked, route-specific transient analysis. It is excluded by the agenda. |
| Bailey--Crandall PRNG route | previously covered | It is a named excluded route. Its 2002 theorem is cited below only as a scale yardstick, not imported as a route for pi. |
| Euler--Rabinowitz--Wagon factorial series and Chudnovsky-type factorial series | previously covered | The agenda excludes the factorial route. T78 is an unverified proof sketch, so this table uses only the agenda's exclusion, not a claim that T78 establishes it. |
| Abrarov--Quine two-term Machin-like family, specialized below | retained | Its source is a dated primary arXiv paper, it is neither the standard BBP identity nor the excluded Zudilin/factorial families, and its rational terms expose an exact base-10 transient and an odd prime-power modulus. |

There is one retained candidate and two retained primary sources, both byte-pinned
in `SOURCE_PINS.md`; this is within the limits of four candidates and eight sources.

## 3. Retained candidate: a k=4 rational Machin-like specialization

Abrarov and Quine, arXiv:1706.08835v3 (updated 2017-07-26), equation (3),
PDF p. 3, gives

\[
 {\pi\over4}=2^{k-1}\arctan(1/u_1)+\arctan(1/u_2). \tag{3.1}
\]

Their equation (5), the same page, gives the rational construction

\[
 u_2={2\over((u_1+i)/(u_1-i))^{2^{k-1}}-i}-i. \tag{3.2}
\]

Set \(k=4\) and \(u_1=10\). Exact rational complex arithmetic gives

\[
 ((10+i)/(10-i))^8=
 {-258800989811999+10825473963759840i\over10828567056280801},
 \qquad u_2=-{147153121\over1758719}. \tag{3.3}
\]

The tangent addition identity, with the signs fixed by
\(8\arctan(1/10)\in(\pi/4,\pi/2)\), therefore gives the exact,
nonfactorial representation

\[
 \boxed{\displaystyle
 \pi=32\sum_{r\geq0}{(-1)^r\over(2r+1)10^{2r+1}}
 -4\sum_{r\geq0}{(-1)^r1758719^{2r+1}\over
 (2r+1)147153121^{2r+1}}.} \tag{3.4}
\]

The arctangent series is used only for \(|x|<1\), which holds here. Direct
integer verification of (3.3), including the identity \(147153121>80\cdot1758719\),
is part of the replay script.

Put \(P=147153121\), \(B=1758719\), and, for \(K\geq1\),

\[
 S_K=\sum_{r=0}^{K-1}\left({32(-1)^r\over(2r+1)10^{2r+1}}
 -{4(-1)^rB^{2r+1}\over(2r+1)P^{2r+1}}\right)={p_K\over q_K},
 \quad \gcd(p_K,q_K)=1,\ q_K>0. \tag{3.5}
\]

## 4. Uniform truncation and rational orbit data

Both summands in (3.4) are alternating with decreasing absolute terms. Hence

\[
 |\pi-S_K|
 <{32\over(2K+1)10^{2K+1}}+
 {4\over(2K+1)80^{2K+1}}
 <{36\over(2K+1)10^{2K+1}}. \tag{4.1}
\]

For every \(0\leq i,j<N\),

\[
 |(10^i-10^j)(\pi-S_K)|<10^{N-1}|\pi-S_K|. \tag{4.2}
\]

Consequently the explicit uniform schedule

\[
 \boxed{N+n+4\leq2K} \tag{4.3}
\]

makes the right side of (4.2) smaller than \(10^{-(n+1)}\): use
\(36/(2K+1)\leq12\) and
\(N-1-(2K+1)\leq-n-5\). Thus all rational phase comparisons at
the canonical radius have a strict error margin; this is a transfer statement,
not a count estimate.

For exact denominator bookkeeping define the odd least common multiple

\[
 L_K=\operatorname{lcm}(1,3,\ldots,2K-1),\quad
 D_K=10^{2K-1}P^{2K-1}L_K,
\]

and the integer

\[
 A_K=\sum_{r=0}^{K-1}\left[
 {32(-1)^rD_K\over(2r+1)10^{2r+1}}
 -{4(-1)^rB^{2r+1}D_K\over(2r+1)P^{2r+1}}\right]. \tag{4.4}
\]

Every displayed quotient in (4.4) is integral. With \(G_K=\gcd(A_K,D_K)\),
the reduced fraction is exactly \(p_K=A_K/G_K\), \(q_K=D_K/G_K\). In
particular, with \(v_\ell(0)=\infty\),

\[
 v_2(q_K)=2K-1-\min(v_2(A_K),2K-1),\tag{4.5}
\]
\[
 v_5(q_K)=2K-1+v_5(L_K)-
 \min(v_5(A_K),2K-1+v_5(L_K)).\tag{4.6}
\]

These are reduced-denominator valuations, not common-denominator guesses.
Write \(a_K=v_2(q_K)\), \(b_K=v_5(q_K)\),
\(t_K=\max(a_K,b_K)\), and

\[
 m_K={q_K\over2^{a_K}5^{b_K}}. \tag{4.7}
\]

Then \(\gcd(m_K,10)=1\), and for \(j=t_K+s\)

\[
 {p_K10^j\over q_K}\pmod1=
 {p_K2^{t_K-a_K}5^{t_K-b_K}10^s\over m_K}\pmod1. \tag{4.8}
\]

The numerator in (4.8) is a unit modulo \(m_K\). Thus the post-transient
orbit has exact period

\[
 d_K=\operatorname{ord}_{m_K}(10), \tag{4.9}
\]

and its residues are distinct for \(0\leq s<d_K\). For the tail interval
\(t_K\leq j<N\), equality occurs exactly when \(d_K\mid i-j\). Its exact
ordered collision multiplicity is

\[
 \sum_{r=0}^{d_K-1}c_r^2,
 \qquad
 c_r=\max\left(0,1+\left\lfloor{N-t_K-1-r\over d_K}\right\rfloor\right). \tag{4.10}
\]

Formula (4.10) is equality, not an occupancy estimate. The script derives
(4.5)--(4.10) for \(1\leq K\leq8\), factors the resulting moduli, and obtains
the exact orders by modular exponentiation.

## 5. Prime-power size obstruction and the T10 comparison

For \(2K-1<P\), the second summand with \(r=K-1\) in (3.5) has
\(P\)-adic valuation \(-(2K-1)\). Every earlier second summand has valuation
at least \(-(2K-3)\), and every first summand has nonnegative \(P\)-adic
valuation. The minimum is unique, so

\[
 \boxed{v_P(q_K)=2K-1,\qquad m_K\geq P^{2K-1}.} \tag{5.1}
\]

This does not assume anything about digit occupancy. Under the uniform schedule
(4.3), \(K-1/2\geq(N+n+3)/2\), hence

\[
 \boxed{\sqrt{m_K}\geq P^{K-1/2}
 \geq P^{(N+n+3)/2}>N.} \tag{5.2}
\]

The named fixed-pi comparison is T10's direct long-lag Fourier frontier: it needs
nontrivial cancellation of length \(L\leq N\) phase sums after any rational transfer.
For comparison only, Bailey--Crandall's primary Theorem 4.6 (printed pp. 12--13)
has a square-root-modulus leading cost

\[
 B\left(A\sqrt{c^e}+L c^{-e/2}\right)\log(c^e). \tag{5.3}
\]

After harmlessly increasing its positive constants to \(A,B\geq1\), (5.2) makes
the first cost in (5.3) exceed \(N\geq L\). Moreover (4.7) is generally not a
pure power, so that theorem's hypotheses are not met in the first place. Therefore
the excluded Bailey--Crandall route is not revived here: even its optimistic
square-root-modulus scale cannot supply the T10 cancellation for this candidate.

For the direct rational tail the exact relevant sum is instead

\[
 E_{K,h}(L)=\sum_{s=0}^{L-1}
 \exp\left(2\pi i h\,{p_K2^{t_K-a_K}5^{t_K-b_K}10^s\over m_K}\right). \tag{5.4}
\]

Equations (4.8)--(4.10) give period and exact equality collisions, but no
nontrivial bound for (5.4); we do not label that absence an occupancy premise.
The quantitative obstruction is specifically (5.2)--(5.3), which closes the
only square-root-modulus rational-orbit interface comparable to the T10 scale.

## 6. Terminal classification

**Newly obstructed.** The retained nonfactorial candidate has an exact uniform
truncation schedule, reduced valuations, transient, coprime modulus, order, and
collision formula. But for every \(K\) in the explicitly stated range
\(2K-1<P\) and every \(n,N\) satisfying the simultaneous transfer schedule,
the modulus obeys \(\sqrt{m_K}>N\). Thus a rational-orbit method carrying a
positive square-root-modulus leading cost cannot deliver the length-\(\leq N\)
T10 Fourier cancellation. This is a displayed size obstruction, not an unknown
occupancy assertion. It does not rule out a qualitatively different estimate for
(5.4), and it makes no claim about the canonical question.

## 7. Reproduction

From a directory containing only this artifact set, run:

```bash
python3 verify_note.py
```

The command verifies the canonical and retained-source hashes; derives (3.3);
checks the exact partial denominators, valuations, transients, factorizations,
orders, and collision formula for \(1\leq K\leq8\); and checks the sample
uniform schedule and the prime-power lower bound. `SHA256SUMS` separately
covers the report and replay-script bytes. The script uses only Python's
standard library.
