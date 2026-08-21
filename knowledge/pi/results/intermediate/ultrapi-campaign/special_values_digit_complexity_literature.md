# Special values, E/G-functions, and decimal-language complexity of pi

Audit date: **2026-08-12 UTC**

Status: `literature-checked` bounded primary-source audit, with explicitly
marked `proof sketch` reductions

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Finding

The audit found one material theorem that genuinely specializes to \(\pi\):
Fischler--Rivoal's final 2026 paper proves an effective irrationality measure
for every real irrational simple zero of a non-polynomial rational-coefficient
E-function.  With \(f(z)=\sin z\) and \(\zeta=\pi\), it gives effective
constants \(c,d>0\) such that

\[
  \left|\pi-\frac ab\right|\geq \exp(-c b^d)
  \qquad(a\in\mathbb Z,\ b\geq1).                 \tag{1}
\]

This is unconditional and pi-specific.  It is also far below the decimal
truncation scale: for \(b=10^N\), its right side is
\(\exp(-c10^{dN})\), whereas every \(N\)-digit truncation has error less than
\(10^{-N}\).  The theorem sees neither the numerator's decimal language nor
the unit cylinder containing \(10^N\pi\), so it yields no word occurrence.

No inspected theorem through the audit date proves any of the following from
the fact that \(\pi\) is a G-value, a period/E-period, a logarithm of an
algebraic number, or a zero of an E-function:

| Requested threshold | Result for decimal \(\pi\) found in this audit |
|---|---|
| Positive base-10 factor entropy | None |
| Maximal base-10 factor entropy, hence disjunctivity | None |
| Escape from a prescribed proper finite-state/forbidden-word language, except by directly checking a finite occurrence | None |
| A language-sensitive lower bound for decimal truncation numerators | None |
| A scalar special-value measure | Yes: (1), but it is too weak and language-blind |

The nearest unconditional digit theorems control low factor complexity or
long exact repetitions for *other* E/G-values.  Their conclusions remain
linear in the block length and therefore have zero entropy.  The nearest
maximal-language result is Lagarias's conditional BBP dichotomy; its needed
dynamical hypothesis is unproved, and the checked source does not furnish a
base-10 BBP expansion for \(\pi\).

## 1. Exact symbolic threshold

Put \(\theta=\pi-3=0.d_1d_2\ldots\) and let

\[
 p_\pi(m)=\#\{d_jd_{j+1}\cdots d_{j+m-1}:j\geq1\}.
\]

The target is

\[
  p_\pi(m)=10^m\quad\text{for every }m\geq1.       \tag{2}
\]

The topological factor entropy of the digit word is

\[
  h_{10}(\pi)=\lim_{m\to\infty}\frac1m\log p_\pi(m),
\]

where the limit exists by submultiplicativity.  Positive entropy is not
enough: a decimal sequence over only two digits can have positive entropy and
omit the other eight digits.  In fact, every fixed-word survivor subshift in
the ten-symbol full shift contains a positive-entropy subshift.

`proof sketch`: maximal entropy *is* enough and is equivalent here to (2).
If a word of length \(L\) is absent, then
\(p_\pi(L)\leq10^L-1\).  Submultiplicativity gives

\[
  h_{10}(\pi)\leq \frac1L\log p_\pi(L)<\log 10.
\]

Conversely, (2) gives \(h_{10}(\pi)=\log10\).  Thus a special-value theorem
would have to reach **maximal**, not merely positive, entropy unless it sees
individual forbidden languages directly.

For a finite word \(w\), let \(A_w(N)\) be the set of integers
\(0\leq a<10^N\) whose zero-padded \(N\)-digit word avoids \(w\).  If \(w\)
never occurs, then

\[
 a_N:=\lfloor10^N\theta\rfloor\in A_w(N)
 \quad\text{and}\quad
 0\leq\theta-\frac{a_N}{10^N}<10^{-N}              \tag{3}
\]

for every \(N\).  This is the exact restricted-numerator condition a useful
arithmetic theorem must contradict.

## 2. E-function zeros: a direct theorem for pi, but at the wrong scale

The material direct specialization is in Fischler--Rivoal,
[*Transcendence of values of logarithms of E-functions*](https://www.imo.universite-paris-saclay.fr/~fischler/logE.pdf),
Math. Ann. **394** (2026), Article 12,
[DOI 10.1007/s00208-026-03374-z](https://doi.org/10.1007/s00208-026-03374-z).
In the paragraph immediately after Theorem 3, Article page 5, the authors
derive

\[
 \left|\zeta-\frac ab\right|\geq \frac1{\exp(c b^d)}               \tag{4}
\]

for every real irrational simple zero \(\zeta\) of a non-polynomial
E-function with rational coefficients.  The constants are effective.
The hypotheses match \(\pi\) exactly:

- \(\sin z\) is a strict E-function with rational coefficients;
- it is non-polynomial;
- \(\sin\pi=0\), \(\cos\pi=-1\neq0\), so \(\pi\) is a simple real zero;
- \(\pi\) is irrational.

The proof applies Theorem 3 at the moving rational point \(a/b\) to lower
bound \(|\sin(a/b)|\), then uses the mean value theorem.  This is stronger
applicability than treating \(\pi\) merely as \(-i\operatorname{Log}(-1)\),
but its scale is much weaker:

\[
  \exp(-c10^{dN})\ll 10^{-CN}\quad\text{for every fixed }C>0.       \tag{5}
\]

Consequently (4) is compatible with every truncation in (3).  It also allows
all numerators \(a\); it has no stronger conclusion when \(a\in A_w(N)\).

The same paper's Theorem 2, Article page 3, proves

\[
 \left|\ln f(\xi)-\frac ab\right|\geq\exp(-c b^d)                  \tag{6}
\]

when \(f\in\mathbb Q[[z]]\) is a strict E-function,
\(\xi\in\mathbb Q^*\), \(f(\xi)>0\), and \(\ln f(\xi)\) is
irrational.  This does **not** apply to
\(\operatorname{Log}(-1)=i\pi\): the positive-real hypothesis fails.
Corollary 1, Article page 2, gives qualitative transcendence for fixed
complex logarithms of E-values outside a finite exceptional set, but no
digit or rational-approximation conclusion.

A second zeros paper,
[*Zeros of E-functions and of exponential polynomials defined over
\(\overline{\mathbb Q}\)*](https://arxiv.org/abs/2503.20345), has no missing
quantitative bridge.  Theorem 1.2 (paper page 2) and Theorem 1.5 (page 3) are
unconditional factorization/multiplicity results.  Theorem 1.8 (page 4) is
conditional on Schanuel's conjecture and says that if an exponential
polynomial \(f\) over \(\overline{\mathbb Q}\) satisfies \(f(\pi)=0\), then
for some \(M\geq1\),

\[
 \frac{f(x)}{e^{2ix/M}-e^{2i\pi/M}}
\]

is again an exponential polynomial.  For \(f(x)=\sin x\), the conclusion is
already explicit with \(M=1\):

\[
 \frac{\sin x}{e^{2ix}-1}=\frac{e^{-ix}}{2i}.
\]

It classifies why functions vanish at \(\pi\); it neither locates \(\pi\)
inside a decimal cylinder nor builds a digit-sensitive vanishing function.

## 3. G-function values: exact pi representation, failed uniformity, weak language output

Fischler--Rivoal,
[*Rational approximation to values of G-functions, and their expansions in
integer bases*](https://www.imo.universite-paris-saclay.fr/~fischler/approxG.pdf),
Manuscripta Math. **155** (2018),
[DOI 10.1007/s00229-017-0933-8](https://doi.org/10.1007/s00229-017-0933-8),
with [erratum DOI 10.1007/s00229-017-0988-6](https://doi.org/10.1007/s00229-017-0988-6),
is the closest unconditional language theorem for G-values.

Theorem 2, published pages 581--582 / corrected-paper pages 3--4, fixes a
nonrational \(F\in\mathbb Q[[z]]\) and \(t\geq0\), and gives effective
constants such that, when \(b\) is sufficiently large relative to \(F\) and
\(a\), \(1\leq B\leq b^t\), and \(m\) exceeds its stated effective threshold,

\[
 \left|F(a/b)-\frac{n}{B b^m}\right|
 \geq \frac1{B b^m(|a|+1)^{c_4m}}.                  \tag{7}
\]

Corollary 1, published page 582 / paper page 4, simplifies this for large
\(b,m\) to \(b^{-m(1+\varepsilon)}\).  Theorem 3, published page 583 /
paper page 5, controls immediate repetitions: if \(b^s\) is sufficiently
large relative to the fixed \(F,\varepsilon,a\), then for every block length
\(t\geq1\),

\[
 \limsup_{n\to\infty}
 \frac{N_b(F(a/b^s),t,n)}n\leq\frac\varepsilon t,                 \tag{8}
\]

where \(N_b\) counts consecutive copies of the length-\(t\) block beginning
at digit \(n\).

There is an exact decimal-denominator G-function representation of \(\pi\).
Machin's identity gives

\[
 H(z)=16\arctan(2z)-4\arctan(10z/239),\qquad H(1/10)=\pi.         \tag{9}
\]

Here \(H\) is a fixed nonrational rational-coefficient G-function.  But (8)
applies to (9) only if \(10\) exceeds the effective threshold attached to
this particular \(H\) and \(\varepsilon\); the paper does not establish
that.  The obvious scaling does not repair the hypothesis.  For example,

\[
 H_r(z)=16\arctan(10^rz/5)-4\arctan(10^rz/239),
 \qquad H_r(10^{-r})=\pi,                                      \tag{10}
\]

but \(H_r\) changes with \(r\), while all threshold constants depend on
the fixed function.  The theorem contains no uniformity in this moving
family.

Even a successful threshold check would not prove a word occurrence.  The
decimal real whose digits are the binary Thue--Morse word uses only digits
0 and 1, so it omits digit 2 and has zero entropy.  Thue--Morse is cube-free,
so its analogue of \(N_{10}(\xi,t,n)\) is at most 2 for all \(t,n\), which is
strictly stronger than the asymptotic conclusion (8).  Thus repetition
control and forbidden-language escape are logically separate.

## 4. E-values at rational points: optimal irrationality exponent is still insufficient

Fischler--Rivoal,
[*Rational approximations to values of E-functions*](https://arxiv.org/abs/2312.12043),
arXiv:2312.12043v2 (10 July 2025), Theorem 1, paper page 2, proves that for
an E-function \(f\in\mathbb Q[[z]]\) and \(r\in\mathbb Q\), either
\(f(r)\in\mathbb Q\), or for every \(\varepsilon>0\),

\[
 \left|f(r)-\frac pq\right|\geq \frac{c(f,r,\varepsilon)}{q^{2+\varepsilon}}.
                                                                    \tag{11}
\]

Hence every irrational such value has irrationality exponent exactly 2.
Combined with Adamczewski's Theorem 1 below, this implies

\[
 p(f(r),b,n)-n\longrightarrow+\infty                              \tag{12}
\]

in every integer base.  No verified representation \(\pi=f(r)\) satisfying
these hypotheses is supplied by the paper or the other checked sources.  The
standard E-function relation is instead \(\sin(\pi)=0\), with \(\pi\) as the
input, not the value at a rational point.

Even if a new E-value representation put \(\pi\) under (11), (12) would not
give entropy: \(p(n)=n+o(n)\), or any other linear complexity, has entropy
zero and is compatible with omitted words.

The earlier
[*Values of E-functions are not Liouville numbers*](https://arxiv.org/abs/2301.01158),
J. Éc. polytech. Math. **11** (2024), Corollary 1, paper page 3, is weaker for
this purpose: it excludes Liouville behavior for E-values at algebraic points
but has the same missing representation and language gap.

## 5. Exponential-period and irrationality-exponent complexity results

Adamczewski,
[*On the expansion of some exponential periods in an integer
base*](https://arxiv.org/abs/1205.0961), Math. Ann. **346** (2010), Theorem 1,
printed page 110 / preprint page 3, proves that \(\mu(\xi)=2\) implies (12).
Corollary 2 applies it to \(e\) in every base and the following discussion
lists further exponential-function, trigonometric, and Bessel examples.
It does not include \(\pi\).

The paper itself records the obstruction particularly clearly in Remark 6,
printed page 115 / preprint page 9: even a proposed improvement would not
give a new complexity bound for \(\pi,\log2,\zeta(3)\), because their known
irrationality-exponent upper bounds exceed \((3+\sqrt5)/2\).  Remark 7 then
exhibits a number with \(\mu=2\) but only linear factor complexity.  Thus
optimal scalar irrationality exponent does not force entropy.

Bugeaud--Kim,
[*On b-ary expansions of \(\log(1+1/a)\) and
\(e\)*](https://arxiv.org/abs/1510.00282), Ann. Sc. Norm. Super. Pisa (2017),
Theorems 1.3--1.5, preprint pages 3--4, gives linear factor-complexity bounds
from irrationality exponents and explicit linear bounds for \(e\).  Its
logarithm applications concern \(\log(1+1/a)\) for sufficiently large positive
integers \(a\); they do not specialize to \(\operatorname{Log}(-1)=i\pi\).

The 2026 refinements remain far from \(\pi\) and far from exponential
complexity:

- Bugeaud--Kim,
  [arXiv:2510.02059v2](https://arxiv.org/abs/2510.02059), Theorem 1.4,
  paper page 3, gives explicit **linear** lower bounds for
  \(\liminf p(n)/n\) and \(\limsup p(n)/n\).  They are nontrivial only for
  \(\mu<2.246\ldots\) and \(\mu<2.324\ldots\), respectively.  The paper
  records \(\mu(\pi)\leq7.10321\).
- Bugeaud--Kaneko--Kim,
  [arXiv:2510.17177v3](https://arxiv.org/abs/2510.17177), Theorem 1.3,
  paper page 3, proves \(\limsup p(n)/n\geq4/3\) when \(\mu=2\), and a
  bound nontrivial for \(\mu<2.2\) when \(\mu>2\).  Even a future proof
  that \(\mu(\pi)=2\) would yield only a linear bound.

These results exclude certain extremely low-complexity words.  They do not
force positive entropy, much less the maximal entropy needed in Section 1.

## 6. Logarithms of algebraic numbers

The exact identity

\[
  \operatorname{Log}(-1)=i\pi                                      \tag{13}
\]

puts \(\pi\) within classical logarithm transcendence measures.  For example,
Cijsouw,
[*Transcendence measures of exponentials and logarithms of algebraic
numbers*](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf), Theorem 2,
printed page 164, supplies an effective degree--height lower bound for a
polynomial evaluated at a fixed logarithm of an algebraic number.  Taking
the algebraic number \(-1\) applies to \(i\pi\).

This is pointwise polynomial separation: a polynomial must first be supplied.
A missing word supplies only the membership (3), not a small polynomial in
\(\pi\).  Rivoal,
[*Convergents and irrationality measures of
logarithms*](https://doi.org/10.4171/RMI/519), Theorems 1--4, printed pages
933--936, obtains restricted-power-denominator measures for certain positive
real logarithms \(\log(1-a/b)\).  Those hypotheses exclude
\(\operatorname{Log}(-1)\), and the digit application controls long gaps or
nonzero-digit counts rather than prescribed blocks.  Full details and an
explicit separator are recorded in
[`logarithm_missing_word_attack.md`](logarithm_missing_word_attack.md).

No checked language-sensitive logarithm theorem converts (13) plus
\(a_N\in A_w(N)\) into exponential smallness.  The 2026 log-E theorem in
Section 2 supplies the direct zero estimate (1), but it does not close this
gap either.

## 7. BBP/G-series dynamics: the only route to full language is conditional

Lagarias,
[*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055),
gives the exact symbolic conclusion sought here, but conditionally.

- Definition 2.1 and Theorem 2.1, printed pages 4--5, identify digit-density
  (disjunctivity) with density of the orbit \(\{b^n\theta\}\), and normality
  with uniform distribution.
- Definition 4.1, printed page 9, defines BBP numbers
  \(\theta=\sum p(n)q(n)^{-1}b^{-n}\).
- Theorem 4.1, printed pages 9--10, says the **Weak Dichotomy Hypothesis**
  implies rational-or-digit-dense, while the **Strong Dichotomy Hypothesis**
  implies rational-or-normal.
- Theorem 5.2 characterizes when these series are G-series; Theorem 5.3,
  printed pages 14--15, supplies a rational-or-transcendental conclusion for
  a subclass.  That arithmetic conclusion does not prove the dynamical
  dichotomy.

The weak/strong dichotomies are hypotheses, not proved theorems about the
perturbed orbit.  Standard \(\pi\) BBP formulas use binary/hexadecimal-type
bases; no base-10 BBP representation satisfying Definition 4.1 was located
in the checked primary sources.  Even a binary or hexadecimal normality
conclusion would not imply decimal disjunctivity: bases 2 and 10 are
multiplicatively independent.

Thus this route accurately identifies the missing dynamics, but it does not
currently instantiate an unconditional decimal theorem for \(\pi\).

## 8. Period and E-period classifications do not add digit separation

Yoshinaga,
[*Periods and elementary real numbers*](https://arxiv.org/abs/0805.0349),
Theorem 18, printed page 9, proves that every real period is an elementary
real number in the sense defined there.  This is an effective computability
classification, not a lower bound on the factor language.  Computable
irrational digit sequences can be constructed inside fixed forbidden-word
subshifts, so computability cannot supply the missing implication.

The most recent source checked before the cutoff is Snodgrass,
[*Periods of E-operators*](https://arxiv.org/abs/2608.06005), submitted
6 August 2026.  Theorem 6.2 and Definition 6.5, paper pages 19--20, put a
rational structure on rapid-decay cohomology and define E-periods; Section 7
embeds E-values and exponential periods in this ring.  The paper provides no
rational-approximation, base-expansion, entropy, or finite-language theorem.
Classification into a broader period ring does not distinguish a number in a
forbidden-word subshift from one outside it.

## 9. Restricted-digit numerator search

The desired special-value estimate would have to distinguish the numerator
set \(A_w(N)\) in (3).  None of the inspected E/G/logarithm measures does:

- G-function Theorem 2 in Section 3 restricts denominators to \(B b^m\) but
  leaves the numerator arbitrary.
- The E-zero estimate (1) leaves numerator and denominator arbitrary and is
  vastly below the truncation scale.
- Classical logarithm measures restrict polynomial degree/height, not the
  automaton language of an integer coefficient.

The adjacent restricted-digit literature solves different quantifiers:

- Chow--Varjú--Yu,
  [*Counting rationals and Diophantine approximation in missing-digit Cantor
  sets*](https://arxiv.org/abs/2402.18395), arXiv:2402.18395v2 (16 January
  2026), Theorems 1.2, 1.4 and 1.8, paper pages 3--5, proves aggregate rational
  counts and metric/dimension statements for one-missing-digit Cantor sets.
  It does not decide whether the named point \(\pi-3\) belongs to such a set,
  and a general forbidden word is more flexible than a missing digit.
- Iyer,
  [*Rational approximation with digit-restricted
  denominators*](https://arxiv.org/abs/2312.01076), Theorems 1.1--1.2,
  paper page 3, proves existence results when the **denominator** uses digits
  0 and 1.  This is the opposite variable and direction from (3).
- Hauke--Kowalski,
  [*Rational approximation with chosen
  numerators*](https://arxiv.org/abs/2502.08335), Theorems 1.1--1.4,
  paper pages 1--3, gives probabilistic/metric and constructed-sequence
  approximation results with one numerator per prime denominator.  It is not
  a lower bound for the decimal-prefix numerators of a fixed special value.

No pointwise exponential-separation theorem for a named E-zero, G-value, or
algebraic logarithm against all \(a\in A_w(N)\) was found.

## 10. Strongest missing theorem

The strongest clean missing statement is a **pi-specific finite-state escape
theorem**:

> For every proper base-10 finite-state survivor language \(L\) (in
> particular, the language avoiding one nonempty word \(w\)), the decimal
> expansion of \(\pi-3\) is not an infinite path in \(L\).

For one forbidden word this is equivalently

\[
 \exists N\geq |w|:\quad
 10^N(\pi-3)\notin
 \bigcup_{a\in A_w(N)}[a,a+1).                         \tag{14}
\]

An entropy formulation of exactly the needed total strength is

\[
 h_{10}(\pi)=\log10.                                    \tag{15}
\]

By Section 1, (15) is equivalent to disjunctivity, not a weaker halfway
result.

For the special-value program, the missing bridge must use the actual cell
or numerator language at scale \(10^{-N}\).  A scalar estimate
\(|\theta-a/10^N|\geq10^{-CN}\) with \(C>1\), and a fortiori the rationally
shifted form of (1), is compatible
with (3).  Even endpoint separation of order \(10^{-N}\) needs sign/cell
information: membership in a unit cylinder does not force closeness to a
particular endpoint by a small fixed fraction.  What is absent is an
automaton-sensitive auxiliary form or orbit theorem that converts
\(a_N\in A_w(N)\) for all \(N\) into arithmetic smallness contradicting a
special relation such as \(\sin\pi=0\) or \(e^{i\pi}=-1\).

Proving \(\mu(\pi)=2\), improving (1) to an ordinary polynomial irrationality
measure, or establishing positive factor entropy would still not supply this
theorem.

## 11. Primary-source pins and search record

All links and theorem locators above were checked on **2026-08-12 UTC**.
This is a bounded primary-source search, not a claim to have exhausted all
mathematical literature.  Searches covered combinations of *E-function
value/zero*, *G-function integer-base expansion*, *exponential period digit
complexity*, *algebraic logarithm subword complexity*, *forbidden word*,
*restricted numerator/digits*, and 2025--2026 citation/version follow-ups.

Exact PDFs used in the audit:

| Source/version | SHA-256 |
|---|---|
| Fischler--Rivoal, log E-functions, final Math. Ann. 2026 PDF | `86669c0103d2a589c9a45970734a9ebac47c737382c015fa026b546960c0301d` |
| Fischler--Rivoal, corrected G-function PDF (2017 correction) | `4e6954c62da62ab760181f9204a7f0fec50afaea6089004b874723b6dedc4d40` |
| Fischler--Rivoal, rational E-value approximation, arXiv:2312.12043v2 | `d2d8ce8a517ff6836c3f52d2c6ba3a5ce64cdc564d2f3390e8a72524426e2fbc` |
| Fischler--Rivoal, non-Liouville E-values, arXiv:2301.01158v3 | `f2af77427bd3e314936fe0367e6dc039c3e1f3a8f19ba6bfb36da5932fc1af6e` |
| Fischler--Rivoal, zeros of E-functions, arXiv:2503.20345v1 | `74c98e4af3e6b7c7637aef0786d67c4516f4611ddcfed98a92ca44c63183b6df` |
| Adamczewski, arXiv:1205.0961v1 | `28ed9d10ddcadc20e103a0ff177c19d2d8c80b5b264441baa071ce5f13e4a7e3` |
| Bugeaud--Kim, arXiv:1510.00282 | `23187960a2037659cec4638c1f2b49bb2eb9393d162b5d13281a4c95e57f5d89` |
| Lagarias, arXiv:math/0101055v2 | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Bugeaud--Kim, arXiv:2510.02059v2 | `fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330` |
| Bugeaud--Kaneko--Kim, arXiv:2510.17177v3 | `c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01` |
| Yoshinaga, arXiv:0805.0349 | `699a03ef2e00b94666ac0b275d8cc1d29639e0b32b1b6d8df96bd289c49dac71` |
| Snodgrass, arXiv:2608.06005v1 | `cd487c9c9804f0439c6ee4aa32a13bf3a749d2176fb59edde78c22d0500482cb` |
| Chow--Varjú--Yu, arXiv:2402.18395v2 | `5bb31a65f491bd85a72864938f610cddf04e45bac6e6f635e508ff6cf70b67bf` |
| Iyer, arXiv:2312.01076v1 | `a312fd3c401f46360939dfa7ffff92a3d3f293693a9637fad2f2574e181821d8` |
| Hauke--Kowalski, arXiv:2502.08335v3 | `b5c7e346eb7683e24a4b0baeb7e02f749e837d3704f14151049da8de3d438b21` |

## Bottom line

The direct E-zero estimate (1) is real progress in applicability: it is an
unconditional contemporary theorem about \(\pi\) itself, not an analogy with
other constants.  Its quantitative scale and unrestricted numerator make it
incapable of deciding even one unobserved forbidden-word cylinder.  The
special-value literature currently stops at scalar separation, low-complexity
exclusion, repetition control, or conditional BBP dynamics.  The unresolved
step is the finite-state/cylinder-sensitive theorem in Section 10.
