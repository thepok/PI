# Hutton prefix sums: exact scale, actual denominator structure, and the logarithmic-prefix barrier

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.  This note uses the fields of
[`problems/TEMPLATE.md`](../../problems/TEMPLATE.md) inside the existing
problem record rather than creating a second problem statement.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained.  The
canonical V1 statement remains a `conjecture`.

This attack isolates the exact analytic theorem that a Hutton-prefix route
would require and obtains two pieces of actual-numerator structure:

1. If \(R=4K+3\), then every prime
   \(R/2<p\le R\), apart from \(2,3,5,7,17\), occurs **exactly once** in the
   reduced denominator of the lower Hutton approximant.  Its local numerator
   is the fixed residue
   
   \[
   pH_K\equiv(-1)^{(p-1)/2}{68\over21}\pmod p.             \tag{1}
   \]
   
   Consequently the post-transient modulus has a squarefree factor \(G_K\)
   with \(\log G_K=R/2+o(R)\).  In particular its prime support is not fixed.
2. The useful Hutton prefix has only
   
   \[
   N_K=4\log_{10}(3)K+O(\log K)
      =1.908485\ldots K+O(\log K)                         \tag{2}
   \]
   
   post-transient states, while \(\log m_K=\Theta(K)\).  Thus the problem is
   an incomplete Korobov sum of logarithmic length.  The strongest directly
   relevant published estimates found in the bounded search become
   nontrivial only at superlogarithmic lengths.  More decisively, on an
   infinite neighboring subsequence the same exact moduli admit the unit
   coefficient \(a=1\) for which the whole length-\(N_K\) sum is
   \(N_K-o(1)\).  No estimate uniform in the numerator can work at the needed
   scale.

There is also an exact conceptual separator.  Up to a bounded total error,
the exponential sums for the **actual** Hutton numerator over this prefix are
the corresponding initial Weyl sums for pi.  Cancellation \(o(N_K)\) for all
fixed nonzero Fourier modes is equivalent to base-10 normality of pi, not a
rational shortcut to it.  The weaker assertion that the Hutton brackets hit
every fixed cylinder is equivalent to V1 itself.

Equations (1)--(2), the cylinder criterion, the uniform-numerator obstruction,
the lifting calculation, and the equivalences are a `proof sketch`: the
elementary arguments are given in full but have not been formalized in Lean.
The source comparison is `literature-checked` as of the date above.  The
finite replay is an `experiment`.  Nothing here is a `candidate resolution`.

## 1. Normalized target and ambiguous quantifiers

Write

\[
 \pi=3+\sum_{j\ge0}d_j(\pi)10^{-(j+1)},
 \qquad d_j(\pi)\in\{0,\ldots,9\}.
\]

The canonical target is

\[
 \forall \ell\ge0\ \forall c\in\{0,\ldots,10^\ell-1\}\
 \exists j\ge0:\quad
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c.          \tag{V1}
\]

The code \(c\) is padded to length \(\ell\), so leading zeroes count;
occurrence is contiguous; and \(\ell=0\) is vacuous.  Pi is irrational, so
there is no terminating/nonterminating decimal ambiguity.

The phrase “the first \(CK\) powers hit every cylinder” has three different
quantifier readings.

1. For each fixed \(\ell\), one sufficiently large \(K\) hits all
   \(10^\ell\) cylinders.  This is enough for V1 after transfer through the
   bracket.
2. For every fixed \(\ell\), all sufficiently large \(K\) hit all cylinders.
   This is stronger.
3. The empirical discrepancy of the prefixes tends to zero.  This is much
   stronger: for the actual Hutton numerator it is equivalent to normality of
   pi.

The analysis below never substitutes (2) or (3) for (1) without saying so.

## 2. The exact transferable prefix

Put

\[
 T_q(M)=\sum_{n=0}^{M-1}{(-1)^n\over(2n+1)q^{2n+1}},
 \qquad
 H_K=8T_3(2K+2)+4T_7(2K+2).                              \tag{3}
\]

The adjacent alternating upper endpoint is \(U_K\), and the already checked
Hutton bracket has exact width

\[
 H_K\le\pi\le U_K,\qquad
 W_K=U_K-H_K
 ={8\over(4K+5)3^{4K+5}}+{4\over(4K+5)7^{4K+5}}.          \tag{4}
\]

Write \(H_K=p_K/q_K\) in lowest terms.  Since \(q_K\) is odd, define

\[
 b_K=v_5(q_K),\qquad m_K=q_K/5^{b_K},\qquad
 a_K\equiv2^{b_K}p_K\pmod {m_K},                          \tag{5}
\]

with \(0\le a_K<m_K\).  Then
\(\gcd(a_K,m_K)=\gcd(10,m_K)=1\), and the exact post-transient state
at offset \(s\) is

\[
 \{10^{b_K+s}H_K\}={r_{K,s}\over m_K},\qquad
 r_{K,s}\equiv a_K10^s\pmod {m_K}.                       \tag{6}
\]

For a word length \(\ell\), set \(\delta=10^{-\ell}\) and let

\[
 J_{K,\ell}=\max\{j\ge0:10^jW_K<\delta/2\}.               \tag{7}
\]

For large \(K\), the number of usable post-transient starts is

\[
 N_{K,\ell}=J_{K,\ell}-b_K+1.                             \tag{8}
\]

If for some \(0\le s<N_{K,\ell}\)

\[
 {r_{K,s}\over m_K}\in
 I_{\ell,c}:=[c\delta,c\delta+\delta/2),                  \tag{9}
\]

then the complete scaled bracket lies in the desired cylinder.  Indeed, with
\(j=b_K+s\) and \(z=\lfloor10^jH_K\rfloor\), equations (7)--(9) give

\[
 z+c\delta\le10^jH_K\le10^j\pi\le10^jU_K
 <z+(c+1)\delta.                                          \tag{10}
\]

Thus a hit in each of the \(10^\ell\) half-cylinders (9) is a clean sufficient
condition.  It retains a factor-two margin; no decimal-boundary heuristic is
being used.

From (4), with \(Q=4K+5\),

\[
 -\log_{10}W_K
 =Q\log_{10}3+\log_{10}(Q/8)
  -\log_{10}\!\left(1+{1\over2}(3/7)^Q\right).            \tag{11}
\]

Also \(b_K\le\lfloor\log_5(4K+3)\rfloor\).  Equations
(7)--(8) therefore give (2), with the additive constant depending on the
fixed \(\ell\).

## 3. The Fourier inequality that would suffice

Let \(D^*_{K,N}\) denote the star discrepancy of the first \(N\) points in
(6), and define the Korobov sums

\[
 S_{K,N}(h)=\sum_{s=0}^{N-1}
 \exp\!\left(2\pi i h{a_K10^s\over m_K}\right).           \tag{12}
\]

Any interval has counting error at most \(2ND^*_{K,N}\).  Hence

\[
 D^*_{K,N_{K,\ell}}<\delta/4                              \tag{13}
\]

would force a point in every interval (9).  A standard Erdős--Turán
inequality has the form

\[
 D^*_{K,N}\le C_{\rm ET}\left(
 {1\over H}+\sum_{h=1}^{H}{|S_{K,N}(h)|\over hN}\right).  \tag{14}
\]

Consequently, for fixed \(\ell\), it would suffice to take
\(H\asymp10^\ell\) and prove, for all \(1\le h\le H\),

\[
 |S_{K,N_{K,\ell}}(h)|\le
 {10^{-\ell}\over C(1+\log H)}N_{K,\ell}.                 \tag{15}
\]

The exact constant \(C\) is immaterial to the scale comparison: \(\ell\) is
fixed before \(K\to\infty\).  A proof that
\(S_{K,N_{K,\ell}}(h)=o(N_{K,\ell})\) for every fixed
\(h\ne0\) would imply (15).  Section 9 shows that this apparently natural
goal is exactly a normality theorem for pi.

## 4. Actual denominator and actual local numerator

Let \(R=4K+3\), the largest odd exponent in (3).  Fix a prime

\[
 R/2<p\le R,\qquad p\notin\{2,3,5,7,17\}.                 \tag{16}
\]

Among the odd indices \(r\le R\), only \(r=p\) is divisible by \(p\).
Every term of (3) except the \(r=p\) term is therefore \(p\)-integral.  The
exceptional term is

\[
 (-1)^{(p-1)/2}
 {4(2\cdot7^p+3^p)\over p3^p7^p}.                        \tag{17}
\]

By Fermat's theorem,

\[
 4(2\cdot7^p+3^p)\equiv4(14+3)=68\pmod p.                \tag{18}
\]

The residue is nonzero under (16), while \(3^p7^p\) is a unit.  Thus
\(v_p(H_K)=-1\): \(p\) occurs exactly once in \(q_K\).  Multiplying (17) by
\(p\) gives the more precise local-coordinate identity (1).  For \(p=17\),
the numerator in (18) vanishes and all terms are (17)-integral, explaining
the sole nontrivial exception in this interval.

Define

\[
 G_K=\prod_{\substack{R/2<p\le R\\p\ {m prime}\\
                 p\notin\{2,3,5,7,17\}}}p.               \tag{19}
\]

Then \(G_K\mid m_K\).  The prime number theorem in Chebyshev-function form
\(\vartheta(x)\sim x\) yields

\[
 \log G_K=\vartheta(R)-\vartheta(R/2)+O(1)=R/2+o(R).      \tag{20}
\]

On the other hand the natural common denominator divides
\(3^R7^R\operatorname{lcm}(1,3,\ldots,R)\), whose logarithm is \(O(R)\).
It follows that

\[
 \log m_K=\Theta(K),\qquad N_{K,\ell}=\Theta(\log m_K).   \tag{21}
\]

This is stronger than merely observing a complicated factorization in an
`experiment`: (19) is forced by the actual Hutton numerator.  It also shows
that estimates whose constants require a fixed set of denominator primes do
not apply to the full \(m_K\).

## 5. Quantitative comparison with known estimates

The exact sums in (12) are the Korobov-type sums
\(\sum_{s<N}e(ab^s/m)\) with \(b=10\).  The most directly relevant primary
source located was Vandehey,
[*Differencing Methods for Korobov-type Exponential Sums*](https://arxiv.org/abs/1606.07911)
(arXiv PDF retrieved 2026-08-12, SHA-256
`28f10a84ee2038d09af33f1509e74386d70c96baee158143b0924c80e3cc1b7c`).
It records the classical estimates and proves an improved fixed-prime-support
bound.  Its Theorem 7.2 also translates the sum estimates directly into digit
counts for rational expansions.

The scale comparison is as follows.  Here \(M\) denotes the relevant modulus
and \(N=\Theta(\log M)\) is the Hutton prefix length.

| Method | Scope actually covered | Length where the cited bound becomes nontrivial | Comparison with \(N=\Theta(\log M)\) |
|---|---|---:|---:|
| Classical general Korobov estimate | arbitrary \(M\), suitable order range | \(N\gg M^{1/2}\log M\) | exponentially too long |
| Korobov prime-power estimate | \(M=p^e\), fixed odd \(p\) | roughly \(N\ge\exp((\log M)^{2/3})\) | superpolynomially too long |
| Vandehey Theorem 1.4 / 7.2 | all prime factors in one fixed finite set \(P\) | \(N\ge\exp(\Theta(\log M/\log\log M))\) | superpolynomially too long; hypothesis also fails by (19) |
| Bourgain sum-product bounds | arbitrary modulus with order hypotheses | \(N>M^\gamma\) for a positive parameter tied to the saving | exponentially too long at every fixed \(\gamma>0\) |
| Complete-subgroup estimates | complete multiplicative subgroup, usually of size \(>p^\varepsilon\) | full subgroup rather than an ordered prefix | wrong summation set |

The relevant primary arbitrary-modulus source is Bourgain,
[*The sum-product theorem in \(\mathbb Z_q\) with \(q\) arbitrary*](https://doi.org/10.1007/s11854-008-0044-2).
For prime-field complete subgroups, see Bourgain--Glibichuk--Konyagin,
[*Estimates for the Number of Sums and Products and for Exponential Sums in
Fields of Prime Order*](https://doi.org/10.1112/S0024610706022721).
Neither source supplies an ordered-prefix theorem of logarithmic length for
the actual coefficient in (12).

Pólya--Vinogradov and Burgess are useful scale landmarks but are not direct
theorems about (12): they concern consecutive sums of multiplicative
characters, whereas (12) is an additive character evaluated along a
geometric progression.  Even an unjustifiably optimistic transfer of their
scales would require respectively
\(N\gg M^{1/2}\log M\) or \(N>M^{1/4+\varepsilon}\), still exponential in
\(K\).  The primary Burgess source is
[*On Character Sums and Primitive Roots*](https://www.mathnet.ru/eng/mat267).

Thus the comparison is not merely “no convenient theorem was found.”  Every
located theorem is outside the required asymptotic regime, and the closest
fixed-prime-support theorem fails a proved structural hypothesis of \(m_K\).

## 6. Exact complete cancellation does not localize

The large prime-power components look especially attractive because their
complete sums are excellent.  For \(e\ge3\),

\[
 \langle10\rangle\pmod {3^e}=\{x:x\equiv1\pmod9\},
 \qquad |\langle10\rangle|=3^{e-2}.                       \tag{22}
\]

Hence, for \(3\nmid h\),

\[
 \sum_{s=0}^{3^{e-2}-1}e\!\left({h10^s\over3^e}\right)
 =e(h/3^e)\sum_{t=0}^{3^{e-2}-1}e\!\left({ht\over3^{e-2}}\right)=0. \tag{23}
\]

Likewise \(10\) is a primitive root modulo \(7^f\), so the complete
\(7^f\)-orbit is the unit group and its fixed-unit additive sum is the
corresponding Ramanujan sum, zero for \(f\ge2\).  These exact cancellations
occur only after exponentially many states.

Fourier completion of the first \(N\) exponents introduces twisted complete
sums

\[
 G_r(h)=\sum_{s=0}^{d-1}e(h10^s/M)e(rs/d),                \tag{24}
\]

not just the untwisted \(G_0(h)\) in (23).  A square-root bound for all
\(G_r\), even if available, gives an incomplete bound on the order of
\(M^{1/2}\log M\), not \(O(\log M)\).  Exact complete cancellation therefore
does not locate an early cylinder.

There is an even sharper obstruction to every coefficient-uniform approach.
The neighboring-denominator calculation in the prior Hutton note says that,
for every large \(K\), one \(J\in\{K-1,K\}\) satisfies

\[
 e_J:=v_3(q_J)\ge4K+3-O(\log K).                          \tag{25}
\]

Combining \(3^{e_J}\mid m_J\) with (19)--(20) and (2) gives

\[
 {10^{N_{J,\ell}}\over m_J}\le \exp(-2K+o(K)).           \tag{26}
\]

Now keep this exact modulus but replace the actual numerator by the legal
unit coefficient \(a=1\).  The elementary chord bound
\(|e(x)-1|\le2\pi|x|\) yields

\[
 \left|\sum_{s=0}^{N-1}e(10^s/m_J)-N\right|
 \le {2\pi\over9}{10^N\over m_J}=o(1),                   \tag{27}
\]

for \(N=N_{J,\ell}\).  Thus the normalized magnitude tends to one, not zero.
The modulus, order, prime-power lifting, and complete-cycle census are all
the same as for the actual numerator.  Any successful theorem at this scale
must use the actual \(a_J\), not merely denominator quality or a bound uniform
over units.

## 7. What \(p\)-adic differencing can and cannot lower

For shifts \(t\ge1\), lifting the exponent gives the exact identities

\[
 v_3(10^t-1)=2+v_3(t),                                   \tag{28}
\]

and

\[
 v_7(10^t-1)=
 \begin{cases}
  0,&6\nmid t,\\
  1+v_7(t/6),&6\mid t.
 \end{cases}                                             \tag{29}
\]

One van der Corput difference replaces the phase \(a10^s\) by
\(a10^s(10^t-1)\).  If \(t\le N=O(K)\), equation (28) removes at most

\[
 2+\log_3N=O(\log K)                                     \tag{30}
\]

of the \(e=\Theta(K)\) three-primary exponent.  After \(k\) such differences,
the surviving exponent is at least

\[
 e-k(2+\log_3N).                                         \tag{31}
\]

Reducing it to \(O(1)\) requires

\[
 k\ge {e-O(1)\over2+\log_3N}=\Theta(K/\log K).            \tag{32}
\]

Repeated Cauchy--Schwarz at that depth raises the moment to \(2^k\); this is
the concrete loss behind the superlogarithmic ranges in known differencing
theorems.  The same obstruction appears at 7 via (29).  Other prime factors
may divide particular \(10^t-1\), but no shift \(t=O(K)\) removes the robust
three-primary component.  Since \(a_K\) is a unit, its exact value does not
improve the valuation calculation (28)--(32).

This does not prove that every conceivable \(p\)-adic method must fail.  It is
a sharp barrier for the natural repeated-differencing mechanism at the exact
Hutton prefix length.

## 8. Why CRT does not turn local cancellation into interval hits

Suppose \(m=AB\) with \((A,B)=1\).  CRT factors each term as

\[
 e_m(ha10^s)
 =e_A(haB^{-1}10^s)e_B(haA^{-1}10^s).                    \tag{33}
\]

A cancellation estimate for the first factor alone gives no estimate for
the product: the second factor is a structured twist, and in general a twist
can undo cancellation completely.  A joint bilinear or correlation theorem
would be required.

Equation (1) gives unusually explicit actual-numerator data at every prime
in \(G_K\).  It is genuine structure, not a random-numerator model.  But the
decimal interval in (9), when transported through CRT, is not a product of
independent local intervals, and the components in (33) all use the same
exponent \(s\).  Neither local equidistribution nor a product of complete
cycle counts proves the required joint prefix hit.

The exact adjacent formula for \(H_K-H_{K-1}\) has the same limitation.  It
shows that neighboring rational shadows agree throughout essentially the
entire older usable prefix.  It does not provide two independent samples;
each step of \(K\) reveals only about \(4\log_{10}3=1.908\ldots\) new decimal
positions.

## 9. The actual-numerator character sum is a pi Weyl sum

For every integer \(h\), the chord bound and (4) give

\[
 \begin{aligned}
 &\left|
 \sum_{s=0}^{N-1}e(h10^{b_K+s}H_K)
 -\sum_{s=0}^{N-1}e(h10^{b_K+s}\pi)
 \right|\\
 &\hspace{25mm}\le
 2\pi|h|W_K10^{b_K}{10^N-1\over9}.                       \tag{34}
 \end{aligned}
\]

For \(N=N_{K,\ell}\), the right side is \(O_h(10^{-\ell})\), uniformly in
\(K\), by (7).  By (6), the first sum in (34) is exactly (12).  Since
\(b_K=O(\log K)=o(N_{K,\ell})\), deleting the first \(b_K\) terms of the pi
Weyl sum has negligible normalized cost.

Moreover \(J_{K,\ell}=4\log_{10}(3)K+O(\log K)\), and the explicit ratio
of successive widths in (4) bounds
\(J_{K+1,\ell}-J_{K,\ell}\) by an absolute constant.  Therefore

\[
 \forall h\in\mathbb Z\setminus\{0\}:\quad
 S_{K,N_{K,\ell}}(h)=o(N_{K,\ell})                       \tag{35}
\]

holds if and only if the full pi Weyl sums satisfy

\[
 \sum_{j=0}^{n-1}e(h10^j\pi)=o(n)\quad(n\to\infty).       \tag{36}
\]

By Weyl's criterion, (36) is equivalent to uniform distribution of
\(\{10^j\pi\}\), hence to base-10 normality of pi.  Thus the discrepancy
strategy (13)--(15), applied at every large \(K\), asks for a famous stronger
open statement.

There is a parallel exact equivalence at the weaker block-hitting level.

- If a Hutton bracket satisfies (10), then pi has the word: this is the
  forward cylinder certificate.
- Conversely, suppose pi has the word \(c\) at position \(j\).  Irrationality
  puts \(10^j\pi\) strictly inside the corresponding rational cylinder.
  Since \(H_K,U_K\to\pi\), for all sufficiently large \(K\) the scaled bracket
  lies in that same cylinder, and \(j\le J_{K,\ell}\).

Hence “every word eventually has a localized Hutton bracket” is equivalent
to V1.  The rational family gives exact finite certificates once a hit is
known, but does not make the missing hit theorem easier by itself.

## 10. Exact replay and finite experiment

The companion checker is
[`hutton_prefix_sum_check.py`](hutton_prefix_sum_check.py), SHA-256
`ed2d0ad126b879d64cd24882b171e74485137f1dd40436beb464b0a81da24661`.
It uses only integers and `Fraction` arithmetic.  Run it from the repository
root:

```text
python3 work/ultrapi-resume/hutton_prefix_sum_check.py
```

The 2026-08-12 run checked:

```text
source sha256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
upper-half prime survival assertions: 13418
fixed local-residue assertions: 6707
post-transient state assertions: 37986
neighboring 3-primary assertions: 200
LTE assertions: 10000
uniform-a alignment rows (pair K, selected J, N, floor(log10 m_J)):
  10 10 18 69
  20 20 38 139
  40 40 75 278
  80 80 152 557
  120 120 228 839
  200 200 380 1393
lower-half cylinder experiment (K: ell -> starts/hits):
  20: 1->39/9 2->38/16 3->37/17
  40: 1->76/10 2->75/31 3->74/34
  80: 1->153/10 2->152/51 3->151/74
  120: 1->229/10 2->228/66 3->227/107
  200: 1->381/10 2->380/87 3->379/180
  300: 1->572/10 2->571/97 3->570/259
  400: 1->763/10 2->762/99 3->761/330
  600: 1->1145/10 2->1144/100 3->1143/445
all exact checks passed
```

In the last table, `ell->starts/hits` means the exact number of transferable
post-transient starts and the number of distinct **lower-half** cylinders
hit.  For example, the \(K=600\) rational bracket certifies all two-digit
cylinders in this deliberately conservative half-cylinder test, but only 445
of 1000 three-digit cylinders.  These are `experiment` data about finite
prefixes.  They neither extrapolate to arbitrary \(\ell\) nor establish V1.

## 11. Literature search log

| Date (UTC) | Primary source/query | Finding actually used |
|---|---|---|
| 2026-08-12 | Vandehey, arXiv `1606.07911`, “Korobov-type exponential sums” | Exact sum (12); classical square-root range; fixed-prime-support differencing range; rational digit-count application. |
| 2026-08-12 | Bourgain, DOI `10.1007/s11854-008-0044-2`, arbitrary-modulus sum-product | Nontrivial estimates require a positive-power length/order regime, not an ordered \(O(\log m)\) prefix. |
| 2026-08-12 | Bourgain--Glibichuk--Konyagin, DOI `10.1112/S0024610706022721`, subgroup exponential sums | Complete prime-field subgroups of positive-power size; no transfer to the ordered composite prefix. |
| 2026-08-12 | Burgess, *On Character Sums and Primitive Roots* | The \(M^{1/4+\varepsilon}\) landmark is for a different character sum and remains exponentially above the Hutton length. |
| 2026-08-12 | Local mathlib and AllMath search for Hutton/order/discrepancy lemmas | Exact rational/bracket/cylinder and adjacent-increment infrastructure exists; no localized actual-numerator exponential-sum theorem was found. |

This is a bounded dated search, not a novelty claim.  In particular, no claim
is made that (1) or the separator is absent from all prior literature.

## 12. What theorem is still missing

A Hutton-prefix proof must supply one of the following, with the **actual**
state \(a_K\) retained:

1. for every fixed \(\ell,c\), an unbounded family of \(K\) for which one
   \(s<N_{K,\ell}\) satisfies (9); or
2. a joint-CRT bound for (12) at \(N=\Theta(\log m_K)\) strong enough for
   (15), using the local residues (1) and controlling their correlation with
   the three-, seven-, and remaining primary components.

The first statement is equivalent to V1 after the exact bracket transfer.
The natural uniform-discrepancy version of the second is equivalent to
base-10 normality of pi.  Current complete-period, character-sum,
prime-power, CRT, and differencing tools do not bridge that scale, and the
uniform-coefficient counterexample (27) shows that denominator structure
alone cannot do so.

**Bottom line:** the Hutton construction supplies exceptionally clean
rational certificates and the exact prime residue (1), but its usable
orbit is only a logarithmic prefix.  A successful continuation would need a
new, pi-specific, actual-numerator localization theorem; V1 does not follow
from the work in this note.
