# Independent audit: restricted 0/1 denominators and the fixed return

Audit date: **2026-08-12 UTC**  
Audited report:
[`restricted_denominator_iyer_attack.md`](restricted_denominator_iyer_attack.md)  
Audited replay:
[`restricted_denominator_iyer_attack_check.py`](restricted_denominator_iyer_attack_check.py)

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: the target is Marcel's immutable local question and has no
external source URL.

## Verdict

**PASS after two exact corrections, an elementary strengthening, and a
primary-source route closure at Iyer's proved scale.**

The report is a sound route-specific `proof sketch`; its bounded source
audit is `literature-checked` as of the stated date, and its finite replays
are `experiment`.  It does not prove a decimal cylinder hit.  Canonical V1
remains a `conjecture`, and nothing audited here is a `candidate resolution`.

The corrections and strengthening were:

1. Below \(10^N\), the decimal 0/1 family has \(2^N-1\) positive members;
   up to and including \(10^N\), it has \(2^N\), not \(2^N-1\).
2. The specialized cofactor statement was sharpened, with its endpoint made
   explicit, from \(k\geq16(N-2)\) for \(N\geq5\) to
   \(k\geq80N-224\) for \(N\geq8\).  The former bound was correct but not
   the strongest consequence of the same long-division argument.
3. Schleischitz's published missing-digit Cantor-distance theorem was found
   and checked directly.  It gives
   \(k=\Omega(N^{\log_2 10})\), hence \(k/N^2\to\infty\), and therefore
   closes the proposed transfer of Iyer's guaranteed \(N^{-2}\) phase bound.

The report and its primary checker were amended accordingly.  A second,
independently written checker now replays the relevant arithmetic.

## 1. Primary-source audit of Iyer's theorem

I checked the open primary source directly, both as the arXiv v1 source
e-print and as its rendered PDF:

- Siddharth Iyer,
  [*Rational approximation with digit-restricted
  denominators*](https://arxiv.org/abs/2312.01076v1),
  arXiv:2312.01076v1;
- source e-print SHA-256
  `40bacfe7e518c18b116379b900d60053c2e0f64a19cd0049e9d76534c00be183`;
- PDF SHA-256
  `a312fd3c401f46360939dfa7ffff92a3d3f293693a9637fad2f2574e181821d8`.

Theorem 1.1 has exactly the quantifier shape used in the report: for every
real \(\gamma\),

\[
 \min_{1\leq q\leq X,\ q\in\mathfrak D_b}
       \|q\gamma\|_{\mathbb T}
 \leq \frac{C_b}{(\log X)^2}.                                    \tag{A1}
\]

The source's conventions say that Vinogradov constants throughout may
depend on the fixed base \(b\), but not on either cutoff \(X\) or real
parameter \(\gamma\).  The report's “sufficiently large cutoff” wording is
a safe weakening of the displayed theorem.  Its definition of
\(\mathfrak D_b\) is the finite positive subset-sum family
\(\sum_j\varepsilon_jb^j\), \(\varepsilon_j\in\{0,1\}\); it imposes no
units-digit condition and restricts the displayed integer \(q\), not the
denominator left after cancelling a rational \(a/q\).

Taking \(b=10\), \(\gamma=\pi\), and cutoffs tending to infinity gives
witnesses with phase tending to zero.  These witnesses must be unbounded:
for any fixed finite set of positive \(q\)'s, irrationality of pi makes the
minimum of \(\|q\pi\|\) strictly positive.  Choosing a nearest integer
\(a\) therefore gives, along an unbounded displayed-denominator sequence,

\[
 q\left|\pi-\frac aq\right|=\|q\pi\|\longrightarrow0.             \tag{A2}
\]

This verifies the report's claim and also its limitation: (A1) contains no
divisibility condition \(q\mid10^N-16\), no multiplicative-order or
discrete-log condition, no lower annulus for \(q\) relative to \(X\), and no
bound for a complementary quotient.  Iyer's Conjecture 7.1, not a theorem,
is where the source asks for positive-power decay on the full digit family.

The DOI metadata also matches the report: *Quarterly Journal of
Mathematics* **76** (2025), 381--394,
[DOI 10.1093/qmath/haaf007](https://doi.org/10.1093/qmath/haaf007).

## 2. Primary-source audit of the Cantor-distance theorem

I independently checked Johannes Schleischitz,
[*On intrinsic and extrinsic rational approximation to Cantor
sets*](https://arxiv.org/abs/1812.10689v4), arXiv:1812.10689v4:

- source e-print SHA-256
  `28896db4b7dd45b854279f645b08cb4800828d3b8e7df579ea7a299dc304a0c9`;
- PDF SHA-256
  `1bbac7bd2e4d178682b44ded08cd80c9b23883dcaa63423d0592da704a3467e0`.

Theorem 3.4, equation (11) in the PDF and source labels `bfr` / `eq:null`,
states that for the missing-digit Cantor set \(C_{b,W}\), with
\(\Delta=\log|W|/\log b\), every reduced rational \(p/q\notin C_{b,W}\)
satisfies

\[
 \operatorname{dist}\!\left(C_{b,W},\frac pq\right)
 >\frac{b^{-(2b)^\Delta q^\Delta}}{2q}.                           \tag{A3}
\]

This special case has no unmentioned “sufficiently large denominator”
condition.  It applies for every outside rational.  The general part of the
theorem has a Cantor-set-dependent constant, while (A3) is the explicit
missing-digit specialization used here.

Theorem 4.9, source label `pthm`, independently gives the same exponent in
prefix form.  If the first base-\(b\) digits \(c_0,\ldots,c_s\) of an
eventually periodic rational lie in \(W\), but a later digit lies outside
\(W\), then its reduced denominator \(q_0\) satisfies

\[
                              q_0\gg s^{1/\Delta}.                 \tag{A4}
\]

The implied constant may depend on the fixed missing-digit system.  The
indexing is important: \(c_0,\ldots,c_s\) is \(s+1\) digits, so an allowed
prefix of length \(N\) permits \(s=N-1\), not \(s=N\).

The journal metadata matches [DOI
10.1017/etds.2020.7](https://doi.org/10.1017/etds.2020.7): *Ergodic Theory
and Dynamical Systems* **41** (2021), no. 5, 1560--1589.

## 3. Rational decimal-Cantor denominator lemma

The lemma

\[
 x=p/q\in C_{01},\quad \gcd(p,q)=1
 \quad\Longrightarrow\quad v_2(q)=v_5(q)                           \tag{A5}
\]

is correct, including terminating and leading-zero cases.  If an allowed
eventually periodic expansion is written

\[
 x=0.a_1\cdots a_s\overline{b_1\cdots b_t}
   =\frac{U-A}{10^s(10^t-1)},
\]

then \(U\) and \(A\), padded to a common width, contain only 0 and 1.  At
their first unequal digit from the right, \((U-A)/10^r\equiv\pm1\pmod {10}\).
Thus the numerator has equal 2- and 5-adic valuations, while
\(10^t-1\) is coprime to ten.  Cancelling removes equal powers of 2 and 5.
The degenerate equality \(U=A\) forces \(x=0\), and an allowed terminating
expansion is obtained by repeating zero.  The same trailing-digit argument
proves \(v_2(d)=v_5(d)\) for every positive integer \(d\) written only with
decimal digits 0 and 1.

The independent replay checked 15,960 nonzero preperiod/period instances
through preperiod and period lengths six.  This is an `experiment`; the
argument above is the proof sketch.

## 4. General cofactor argument

The general claim is correct with all of its stated hypotheses.  Let
\(N>S_c=\max(v_2(c),v_5(c))\), let
\(10^N-c=kd\), where \(d\in\mathfrak D_{10}\) and \(k>c\), and suppose
\(v_2(c)\ne v_5(c)\).  Since \(v_p(10^N)>v_p(c)\) for \(p=2,5\),

\[
 v_p(10^N-c)=v_p(c).
\]

Writing \(h=v_2(d)=v_5(d)\) gives

\[
 v_2(k)-v_5(k)=v_2(c)-v_5(c)\ne0.                                \tag{A6}
\]

Moreover, \(10^N/k=d+c/k\) with \(0<c/k<1\), so the first \(N\) digits
of \(1/k\) are the zero-padded digits of \(d\).  For
\(k=2^a5^bm\), \(\gcd(m,10)=1\), the nonterminating part starts after at
most \(s=\max(a,b)\leq S_c\) places and has period
\(\operatorname{ord}_m(10)\).  The case \(m=1\), or a period of length at
most \(N-s\), would put all digits of \(1/k\) in \(\{0,1\}\), contradicting
(A5) and (A6).  Hence

\[
 \operatorname{ord}_m(10)>N-s,
 \qquad k\geq m\geq N-S_c+2.                                    \tag{A7}
\]

An independent finite enumeration checked (A6)--(A7) on 265 aligned cases
with \(1\leq c\leq50\) and the configured small depths.  Again, that
enumeration is only an `experiment`.

## 5. Specialized \(c=16\) strengthening

For \(N\geq5\), exact valuation gives
\(v_2(10^N-16)=4\) and \(v_5(10^N-16)=0\).  A decimal 0/1 divisor \(d\)
cannot end in zero, so it ends in 1; hence

\[
 k=16m,\qquad \gcd(m,10)=1.
\]

The exceptional possibility \(m=1\) would make
\(d=625\,10^{N-4}-1\), whose final digit is 9.  Therefore \(m>1\), and
(A7) first gives \(m\geq N-2\).

The strengthened count is also valid.  For \(4\leq i\leq N\), use the
least positive long-division remainder

\[
 r_i=10^i\bmod k=16s_i.
\]

For \(i<N\), the allowed next digit of \(1/k\) implies
\(\lfloor10r_i/k\rfloor\leq1\), hence \(5r_i<k\).  At the endpoint,
\(r_N=16\).  If \(N\geq8\), the preliminary \(m\geq N-2\) gives
\(m>5\), so the endpoint too satisfies \(5r_N<k\).  Thus all
\(N-3\) integers \(s_4,\ldots,s_N\) lie in
\(1\leq s<m/5\).

They are distinct.  A repeat \(r_i=r_j\) with \(4\leq i<j\leq N\)
would make deterministic long division cycle through the already observed,
allowed digit block from positions \(i+1\) through \(j\).  Together with
the allowed prefix, that would put \(1/k\) in \(C_{01}\), contradicting
\(v_2(k)=4\ne0=v_5(k)\).  Therefore

\[
 N-3\leq\left\lfloor\frac{m-1}{5}\right\rfloor,
 \qquad m\geq5N-14,
 \qquad \boxed{k\geq80N-224}.                                    \tag{A8}
\]

The endpoint and all strict inequalities are therefore sound.

## 6. Published cofactor bound and synchronized sufficiency

The application of (A3) is exact.  From \(10^N=kd+16\),

\[
 \frac1k=\frac d{10^N}+\frac{16}{k10^N}.                          \tag{A9}
\]

The rational \(d/10^N\) lies in \(C_{01}\), using its terminating
zero-padded expansion.  Meanwhile \(1/k\notin C_{01}\): it is in lowest
terms and \(v_2(k)=4\ne0=v_5(k)\), contradicting (A5) were it in the set.
Apply (A3) to \(1/k\), use (A9), and put
\(\Delta=\log2/\log10\).  Since \(10^\Delta=2\),

\[
 \frac{16}{k10^N}
 \geq\operatorname{dist}\!\left(C_{01},\frac1k\right)
 >\frac{10^{-20^\Delta k^\Delta}}{2k}.
\]

Taking base-ten logarithms and using \(1/\Delta=\log_2 10\) gives the
fully explicit bound

\[
 \boxed{
 k>\frac{(N-\log_{10}32)^{\log_2 10}}{20}.}                       \tag{A10}
\]

All hypotheses are met for every \(N\geq5\): the argument in Section 5
excludes \(k=16\), so \(k>16\), and \(N-\log_{10}32>0\).  Theorem 4.9 gives
the consistent qualitative check \(k\gg(N-1)^{\log_2 10}\): the first
\(N\) digits of the ordinary expansion of \(1/k\) are the padded digits of
\(d\), while \(1/k\notin C_{01}\).

It follows that \(k/N^2\to\infty\) along every unbounded aligned family.
There is also a clean all-depth consequence:

\[
                              k>N^2\qquad(N\geq5).                 \tag{A11}
\]

For \(5\leq N\leq7\), the preliminary bound
\(k\geq16(N-2)\) exceeds \(N^2\).  For \(8\leq N\leq25\), (A8) exceeds
\(N^2\).  For \(N\geq26\), the elementary inequalities
\(\log_2 10>3\) and \(\log_{10}32<2\) turn (A10) into
\[
 k>(N-2)^3/20>N^2.
\]
The last inequality holds at \(N=26\),
\(24^3=13824>13520=20\cdot26^2\), and
\((N-2)^3/N^2\) is strictly increasing for \(N>2\).  This checks every
endpoint and establishes (A11) without finite-search exhaustion.

The exact examples replay successfully:

\[
 10^{208}\equiv16\pmod {1011},\qquad
 10^{190}\equiv16\pmod {1101}.
\]

Both moduli use only digits 0 and 1.  Their cofactors have respectively
205 and 187 decimal digits and satisfy all long-division state checks and
(A8).  They correctly refute any proposed claim that the 0/1 language alone
forbids all aligned divisors.

The synchronized-Iyer implication is exact.  If

\[
 d_j\mid10^{N_j}-16,\qquad
 \|d_j\pi\|_{\mathbb T}\leq C N_j^{-2},\qquad
 k_j=(10^{N_j}-16)/d_j=o(N_j^2),                                 \tag{A12}
\]

then

\[
 \|(10^{N_j}-16)\pi\|_{\mathbb T}
 \leq k_j\|d_j\pi\|_{\mathbb T}
 \leq Ck_j/N_j^2\longrightarrow0.
\]

The independently audited Furstenberg bridge then makes (A12) sufficient
for V1.  But (A10) proves that the \(k_j=o(N_j^2)\) clause is impossible
for any unbounded aligned family.  Thus (A12) is a correct implication with
inconsistent arithmetic hypotheses, and the proposed transfer of Iyer's
guaranteed \(N^{-2}\) phase bound is closed.

This is only a route closure, not a proof of V1.  The exact divisor transfer
would still work if aligned denominators happened to satisfy

\[
                    k_N\|d_N\pi\|_{\mathbb T}\longrightarrow0,
\]

with phases much smaller than Iyer guarantees.  Neither (A10) nor
Schleischitz's theorem controls this fixed-pi phase, and no checked source
supplies the exceptional cancellation.

As a nearby-source check, Chow--Varj\'u--Yu's main 2026 theorems require
one-missing-digit sets, \(\#D=b-1\), apart from their explicit base-4 cases;
they do not cover \(D=\{0,1\}\) in base ten and do not supply fixed-pi phase
or divisibility.  The checked arXiv v2 pins are e-print SHA-256
`2d3ddb20cca49fc4e9c3c35b4270aa89d2b5865eab2713a0befda4d12ea41ab5`
and PDF SHA-256
`5bb31a65f491bd85a72864938f610cddf04e45bac6e6f635e508ff6cf70b67bf`.

## 7. Reproducibility

Commands rerun:

```text
python3 work/ultrapi-resume/restricted_denominator_iyer_attack_check.py
python3 work/ultrapi-resume/restricted_denominator_iyer_independent_check.py
python3 -m py_compile \
  work/ultrapi-resume/restricted_denominator_iyer_attack_check.py \
  work/ultrapi-resume/restricted_denominator_iyer_independent_check.py
```

Both replays returned `status: PASS`.  The primary replay checked 3,876
rational 0/1 cases, both large modular examples, the exact piecewise
quadratic certificate, and found zero \(k\leq N^2\) alignments for
\(5\leq N\leq200\).  The independent replay
checked 15,960 rational cases, 265 general-cofactor alignments, 262,099
0/1 candidates through \(N=17\), all 13 small alignments found there, and
both large modular examples; it independently replayed the piecewise
quadratic certificate.  The finite enumerations remain `experiment`; the
global bound (A10)--(A11) comes from the proof sketch and published theorem,
not from search exhaustion.

Final artifact SHA-256 values at audit time:

| artifact | SHA-256 |
|---|---|
| `restricted_denominator_iyer_attack.md` | `bcb9c6ea87f7b3924324aed357a159c735914f05dddc0f184a012d18c49ccbd2` |
| `restricted_denominator_iyer_attack_check.py` | `b4aecbfb824d0cc73a26a54806855b827517a3768b6203670dac40a0d5f18456` |
| `restricted_denominator_iyer_independent_check.py` | `1789ae5f83be97b3479f57008d3d0af23fc6f35cbeee3ae9504b79967ebadea1` |

## Bottom line

The route report passes independent audit after correction and strengthening.
Iyer supplies the correct Archimedean approximation scale on the wrong,
high-entropy denominator family.  Exact decimal arithmetic plus
Schleischitz's published Cantor-distance theorem force every synchronized
decimal-0/1 divisor to satisfy (A10), so \(k/N^2\to\infty\).  This closes
the transfer of Iyer's guaranteed \(N^{-2}\) phase scale.  It does not
exclude exceptionally smaller fixed-pi phases on aligned denominators, and
no checked source supplies those phases.  V1 remains a `conjecture`.
