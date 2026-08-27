# Independent audit: G-function value versus a proper decimal finite-type subshift

Audit date: **2026-08-13 UTC**  
Audit status: `literature-checked` bounded primary-source audit, local
`proof sketch` verification, and an independent `experiment` checker  
Canonical V1 status: `conjecture`  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Audited artifacts:

* [`gfunction_subshift_entropy_attack_20260813.md`](gfunction_subshift_entropy_attack_20260813.md),
  SHA-256
  `3fe1e0639411421cef5b28786190717e41bdde1d893fe15fb6bd7e0600efb3b9`;
* [`gfunction_subshift_entropy_attack_20260813_check.py`](gfunction_subshift_entropy_attack_20260813_check.py),
  SHA-256
  `c150a72f596794655ed00d911def69db88b92c578c69a463cb7ea05086baa6d7`.

## Verdict

**No fatal mathematical or source-applicability gap was found.**  The parent
report correctly proves the elementary implication

\[
 \text{one word missing}\quad\Longrightarrow\quad
 \text{the digit path lies in a proper positive-entropy SFT with }
 h<\log 10,                                                    \tag{1}
\]

and correctly concludes that no inspected G-function, E-function, Mahler,
D-finite, irrationality-measure, or low-complexity theorem supplies the
missing pointwise bridge for \(\pi\).

The most important distinction survives independent review:

> A finite automaton recognizing all legal prefixes of a subshift is not an
> automaton, Mahler equation, or differential equation selecting the one path
> formed by the digits of \(\pi\).

Bell--Chen's theorem actually confirms this separation.  The selected digit
series of \(\pi\) cannot be D-finite, because a D-finite series with digits in
a finite alphabet is rational, hence has an eventually periodic coefficient
word, which would make \(\pi\) rational.  Membership in a branching
finite-type language does not imply D-finiteness.

The independent audit found only two harmless precision points:

1. In the Thue--Morse construction, choose \(a<b\) explicitly if the phrase
   “no carries” is to be read literally.  The affine series identity works for
   either ordering, and the construction always permits \(a<b\).
2. The Hausdorff-dimension statement should be read for the decimal-coded
   survivor in \([0,1]\), or for the symbolic space with the usual decimal
   ultrametric.  With either standard interpretation, the displayed bounds
   are correct; the notation \(\dim_{\rm H}X_w\) alone does not specify the
   metric.

Neither point affects a theorem or the negative verdict.  The factor norm
\(30\cdot10^{2n}\) in the parent report can also be sharpened to
\(25\cdot10^{2n}\); its intentional slack does not change the
\(O(N^2)\) height or the failure against Cijsouw's measure.

This audit does **not** promote V1.  There is no `candidate resolution` and no
complete proof that every finite decimal word occurs in \(\pi\).

## 1. Exact SFT counts and entropy

Let \(w\) be a decimal word of length \(m\), and let \(R_w(N)\) be the number
of length-\(N\) words avoiding \(w\).  The prefix-matching automaton has
states \(0,\ldots,m-1\), recording the longest suffix that is a proper prefix
of \(w\).  Removing transitions that complete \(w\) gives exactly

\[
 R_w(N)=e_0^{\mathsf T}A_w^N\mathbf 1.                       \tag{2}
\]

Choose any digit \(c\) occurring in \(w\).  All words on the remaining nine
digits avoid \(w\), proving

\[
 9^N\le R_w(N).                                               \tag{3}
\]

For \(N=qm+r\), \(0\le r<m\), every avoiding word in particular avoids
\(w\) in each of the \(q\) disjoint aligned length-\(m\) blocks.  Thus

\[
 R_w(N)\le 10^r(10^m-1)^q.                                  \tag{4}
\]

This immediately gives

\[
 {R_w(N)\over10^N}
 \le(1-10^{-m})^{\lfloor N/m\rfloor}                         \tag{5}
\]

and

\[
 \log9\le h(X_w)\le {1\over m}\log(10^m-1)<\log10.          \tag{6}
\]

The strict deficit is exactly

\[
 \delta_m=-{1\over m}\log(1-10^{-m})>0.                     \tag{7}
\]

All steps are integer inequalities before taking logarithms; no spectral or
floating-point assumption is hidden in (2)--(7).

For the real-coded survivor, legal prefixes give a cover by \(R_w(N)\)
half-open decimal cylinders of diameter \(10^{-N}\), yielding

\[
 \dim_{\rm H}X_w\le {\log(10^m-1)\over m\log10}.             \tag{8}
\]

The full shift on the nine digits different from \(c\) embeds in the
survivor.  Its decimal self-similar set has dimension \(\log9/\log10\);
endpoint ambiguity is countable and does not change dimension.  Hence the
lower bound in the parent report is valid.

If \(p_\pi(n)\) is the factor-complexity function of the one selected digit
word, then \(p_\pi(n+k)\le p_\pi(n)p_\pi(k)\).  Consequently, one absent
length-\(m\) word gives

\[
 h_\pi\le {1\over m}\log p_\pi(m)
          \le {1\over m}\log(10^m-1)<\log10.                 \tag{9}
\]

Conversely, disjunctivity gives \(p_\pi(n)=10^n\) for every \(n\), while
\(h_\pi=\log10\) forces equality at every \(n\), since the entropy is the
infimum of \(n^{-1}\log p_\pi(n)\).  The claimed equivalence between V1 and
maximal factor entropy is therefore correct.

Status: local `proof sketch`; the independent checker verifies extensive
finite instances as `experiment`, not as a proof.

## 2. The D-finite and automaton separation

Let

\[
 D_\pi(z)=\sum_{n\ge1}d_nz^n.                               \tag{10}
\]

[Bell--Chen, Theorem 1.3](https://arxiv.org/abs/1606.04986)
states that a D-finite power series over a characteristic-zero field whose
coefficients lie in a finite set is rational.  Its hypotheses would apply to
(10) if D-finiteness were available.

For completeness, the final implication does not need a second deep theorem.
A rational power series satisfies a constant-coefficient recurrence from
some index onward.  A state consisting of the last finitely many
coefficients takes values in a finite set and deterministically selects the
next coefficient.  Some state therefore repeats, making the coefficient word
eventually periodic.  The associated decimal is rational.  Since \(\pi\) is
irrational,

\[
 D_\pi(z)\text{ is not D-finite and hence is not a G-function}.            \tag{11}
\]

[Bell--Chen--Nguyen--Zannier, Theorem 1.1](https://arxiv.org/abs/2306.02590)
is consistent and slightly redundant here: decimal coefficients have height
zero and denominator one, so its sublinear height/denominator assumptions
would again make a D-finite digit series rational.

[Bell--Coons--Rowland, Theorem 1](https://arxiv.org/abs/1210.2070)
states that a D-finite Mahler function is rational.  It applies to separate
the nonrational Thue--Morse generating function below from G-functions.  None
of these theorems reverses the implication: being one path in a regular
branching language does not make that path automatic, Mahler, or D-finite.
There are uncountably many paths in the embedded nine-shift and only
countably many finite automata.

Status: theorem statements and applicability are `literature-checked`; the
specialization (11) is a local `proof sketch`.

## 3. Thue--Morse separator

For Thue--Morse \(t_{2n}=t_n\), \(t_{2n+1}=1-t_n\), choose a digit \(c\)
occurring in \(w\) and choose \(a<b\) among the other nine digits.  Put

\[
 \tau_{10}=\sum_{n\ge0}t_n10^{-n-1},\qquad
 \eta_w={a\over9}+(b-a)\tau_{10}.                            \tag{12}
\]

Termwise,

\[
 \eta_w=\sum_{n\ge0}\bigl(a+(b-a)t_n\bigr)10^{-n-1}.         \tag{13}
\]

The coefficients in (13) are exactly \(a\) or \(b\), so no carry occurs.
Digit \(c\) never occurs and therefore neither does \(w\).  The selected
digit series is 2-automatic and satisfies the exact Mahler equation

\[
 T(z)=(1-z)T(z^2)+{z\over1-z^2}.                             \tag{14}
\]

[Bugeaud's theorem](https://www.numdam.org/item/AIF_2011__61_5_2065_0.pdf)
proves that \(\sum_{n\ge0}t_nb^{-n}\) has irrationality exponent two for
every integer \(b\ge2\); the same paper correctly attributes its
transcendence to Mahler.  Multiplication by a nonzero rational and addition
of a rational preserve both transcendence and irrationality exponent, so the
parent's conclusion for \(\eta_w\) is valid.

This is a genuine separator for arguments based only on word omission,
automatic/Mahler structure, transcendence, and scalar irrationality exponent.
It is not a counterexample to a future theorem special to G-values, and the
parent report explicitly preserves that boundary.

The use of limited powers to explain why Fischler--Rivoal's repetition
conclusion is insufficient rests on the classical overlap-freeness, hence
cube-freeness, of Thue--Morse.  This fact is not source-pinned in the parent
report, but it is not needed for the main separator (12)--(14) and is not a
fatal gap.

Status: (12)--(14) are a local `proof sketch`; the irrationality-exponent
claim is `literature-checked`; finite substitution and avoidance checks are
`experiment`.

## 4. The fixed G-function representation and the exact theorem boundary

Define

\[
 H(z)=16\arctan(2z)-4\arctan(10z/239).                       \tag{15}
\]

The rational tangent computation

\[
 \tan(2\arctan(1/5))={5\over12},\qquad
 \tan(4\arctan(1/5))={120\over119},
\]

and

\[
 \tan(4\arctan(1/5)-\arctan(1/239))=1                      \tag{16}
\]

gives Machin's identity after checking the angle lies in \((0,\pi/2)\).
Thus \(H(1/10)=\pi\).  Independently, the checker verifies the equivalent
Gaussian-rational phase identity

\[
 \left({5+i\over5-i}\right)^4{239-i\over239+i}=i.            \tag{17}
\]

The Taylor coefficients of each arctangent are rational with exponential
size and common-denominator bounds, and the function is D-finite.  The
evaluation point \(1/10\) lies strictly inside the nearest radius \(1/2\).
Moreover,

\[
 H'(z)={32\over1+4z^2}-{9560\over57121+100z^2}.              \tag{18}
\]

At \(z^2=-1/4\), the second denominator is \(57096\ne0\), so
the first simple poles cannot cancel.  Since the derivative of a rational
function has zero residues and no simple-pole term, \(H\) is nonrational.
The parent report's G-function hypotheses are therefore correct.

[Fischler--Rivoal, Theorem 2](https://www.imo.universite-paris-saclay.fr/~fischler/approxG.pdf)
requires

\[
 b>(c_1|a|)^{c_2},                                           \tag{19}
\]

where the effective constants depend on the fixed G-function; Theorem 3
requires \(b^s\) to be sufficiently large in terms of the fixed
\(F,\varepsilon,a\).  The source does not establish (19) for \(F=H,a=1,b=10\).
Replacing \(H\) by a rescaled family changes the fixed function and hence its
constants, so it is not a uniform workaround.  The parent report states this
boundary exactly.

Even if the threshold were verified, Theorem 3 bounds immediate powers
\(N_b(F(a/b^s),t,n)\); it does not assert that any prescribed word occurs.
That conclusion is strictly weaker than escape from every proper SFT.

Status: `literature-checked` applicability with local `proof sketch`
specialization.

## 5. Other cited complexity and special-value theorems

Every theorem statement used in the parent applicability table was checked
against its pinned primary PDF.

| Source | Audited statement | Verdict for this route |
|---|---|---|
| [Adamczewski--Bugeaud](https://arxiv.org/abs/math/0511674), Theorems 1--2 | Irrational algebraic base-\(b\) expansions have \(p(n)/n\to\infty\); irrational automatic numbers are transcendental. | Correctly stated.  \(\pi\) is transcendental and SFT survivors allow exponential complexity. |
| [Adamczewski](https://arxiv.org/abs/1205.0961), Theorem 1 | \(\mu(\xi)=2\) implies \(p(n)-n\to\infty\). | Correctly stated.  It is only a linear-scale conclusion and \(\mu(\pi)=2\) is not known. |
| [Bugeaud--Kaneko--Kim](https://arxiv.org/abs/2510.17177v3), Theorem 1.3 | If \(\mu=2\), then \(\limsup p(n)/n\ge4/3\); the displayed \(\mu>2\) bound is nontrivial only for \(\mu<2.2\). | Exact match.  It remains exponentially below \(10^n\). |
| [Zeilberger--Zudilin](https://arxiv.org/abs/1912.06345) | \(\mu(\pi)\le7.103205334137\ldots\). | Correct and far outside the cited near-two range. |
| [Fischler--Rivoal 2026](https://doi.org/10.1007/s00208-026-03374-z), paragraph after Theorem 3 | A real irrational simple zero \(\zeta\) of a non-polynomial rational-coefficient E-function obeys \(|\zeta-a/b|\ge\exp(-cb^d)\). | Applies to \(\sin\pi=0\).  At \(b=10^N\), the lower bound is much smaller than \(10^{-N}\) and ignores numerator language. |
| [Adamczewski--Faverjon](https://arxiv.org/abs/2604.08208), Theorems 1.1--1.2 and Corollary 5.2 | Liouville-type polynomial bounds for fixed Mahler values; no M-value is a Liouville or U-number. | Correct.  An arbitrary SFT path is not supplied as a Mahler value, and no forbidden language appears in the estimate. |
| [Nguyen](https://arxiv.org/abs/2605.30606v2), Theorems A--B | A sufficiently large refined Diophantine exponent / controlled approximate periodicity gives transcendence or measures. | Correct.  The recurrence is an input and does not follow from membership in a positive-entropy SFT. |

The E-function-zero estimate specializes genuinely to \(\pi\), but its scale
is

\[
 \exp(-c10^{dN})\ll10^{-N},                                  \tag{20}
\]

so it cannot contradict decimal truncation.  No direction of implication is
reversed in the parent report.  The statement that no pointwise
G/E-value-to-SFT exclusion theorem was located is explicitly a bounded-search
finding, not a novelty or exhaustiveness claim.

Status: `literature-checked`.

## 6. Auxiliary-polynomial ledger

Let \(A_w(n)\) be the avoiding length-\(n\) prefixes and
\(R_w(n)=|A_w(n)|\).  The all-candidate polynomial

\[
 B_n(X)=\prod_{a\in A_w(n)}(10^n(X-3)-a)                     \tag{21}
\]

has exactly

\[
 \deg B_n=R_w(n),\qquad
 \operatorname{lc}B_n=10^{nR_w(n)},\qquad
 \log H(B_n)\ge nR_w(n)\log10\ge n9^n\log10.                \tag{22}
\]

If the selected prefix is \(a_n=\lfloor10^n(\pi-3)\rfloor\),
then its factor lies in \((0,1)\), while every other factor has modulus less
than \(10^n\).  Therefore

\[
 0<|B_n(\pi)|<(10^n)^{R_w(n)-1},                             \tag{23}
\]

which is not a small integer-polynomial value.  Normalization loses
integrality and clearing denominators restores (22).  The parent's diagnosis
is exact.

For

\[
 P_N(X)=\prod_{n=1}^N F(10^nX-A_n),\quad
 F(Z)=Z(1-Z),\quad A_n=\lfloor10^n\pi\rfloor,                \tag{24}
\]

one has \(0<P_N(\pi)\le4^{-N}\) and \(\deg P_N=2N\).  With
\(t=10^n\), the factor coefficients are

\[
 -t^2,\qquad t(1+2A_n),\qquad -A_n(1+A_n).                   \tag{25}
\]

Because \(0\le A_n<4t\), their \(\ell^1\)-norm is maximized at
\(A_n=4t-1\) and equals

\[
 25t^2-5t\le25t^2.                                           \tag{26}
\]

Thus the parent's weaker bound \(30t^2\), and consequently

\[
 H(P_N)\le30^N10^{N(N+1)},                                  \tag{27}
\]

are valid.

[Cijsouw, Theorem 2](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf)
states, with \(S=D+\log H\), the transcendence measure

\[
 \exp[-C D^2S(1+\log D)^2]                                  \tag{28}
\]

for a fixed logarithm of an algebraic number.  For
\(i\pi=\operatorname{Log}(-1)\), the symmetrization

\[
 Q(Y)=P(-iY)P(iY)\in\mathbb Z[Y]                             \tag{29}
\]

satisfies

\[
 \deg Q\le2D,quad H(Q)\le(D+1)H(P)^2,quad
 Q(i\pi)=P(\pi)P(-\pi).                                     \tag{30}
\]

Together with the elementary upper bound on \(|P(-\pi)|\), this gives the
shape recorded in the parent report.  Substituting \(D=2N\) and
\(\log H(P_N)=O(N^2)\) yields only

\[
 |P_N(\pi)|>\exp[-O(N^4\log^2N)],                            \tag{31}
\]

fully compatible with \(P_N(\pi)\le4^{-N}\).  The checker verifies (29)--(30)
coefficientwise for independent integer polynomials.  No universal no-go for
all possible auxiliary constructions is claimed.

Status: Cijsouw's theorem is `literature-checked`; the transfer and ledgers
are local `proof sketch`; finite polynomial identities are `experiment`.

## 7. Primary-source pins reproduced

The following SHA-256 values were independently recomputed from the primary
PDFs on 2026-08-13 UTC.  The inherited Bugeaud pin was reproduced from the
Numdam PDF; a publisher mirror serves equivalent mathematical content with
different PDF bytes.

| Primary PDF | SHA-256 |
|---|---|
| [Fischler--Rivoal, corrected G-function PDF](https://www.imo.universite-paris-saclay.fr/~fischler/approxG.pdf) | `4e6954c62da62ab760181f9204a7f0fec50afaea6089004b874723b6dedc4d40` |
| [Adamczewski--Bugeaud, arXiv:math/0511674](https://arxiv.org/pdf/math/0511674) | `e3bd2934800e94dd27930d43d47abc44f760de7e90320d1d014b372b681be9a0` |
| [Adamczewski, arXiv:1205.0961](https://arxiv.org/pdf/1205.0961) | `28ed9d10ddcadc20e103a0ff177c19d2d8c80b5b264441baa071ce5f13e4a7e3` |
| [Bell--Chen, arXiv:1606.04986](https://arxiv.org/pdf/1606.04986) | `9550237fb012dea45349573f50ef19aa0adbbe9d4e68121255206756851da1db` |
| [Bell--Coons--Rowland, arXiv:1210.2070](https://arxiv.org/pdf/1210.2070) | `30481c3b4cf0ae925bb7bf11b908e00d3df0a77779090c615ebdfa82bd764aa0` |
| [Bell--Chen--Nguyen--Zannier, arXiv:2306.02590v1](https://arxiv.org/pdf/2306.02590v1) | `2d50018f9c9f255d3886814fb4875dacc7f3c7e936fc31ed0c2bab2bd8a4ac05` |
| [Bugeaud--Kaneko--Kim, arXiv:2510.17177v3](https://arxiv.org/pdf/2510.17177v3) | `c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01` |
| [Zeilberger--Zudilin, arXiv:1912.06345](https://arxiv.org/pdf/1912.06345) | `b922ee68a427ad5b74617bd2ac6b6a549824eb2d5a8c97eed0d34b2de984155f` |
| [Adamczewski, Mahler survey](https://adamczewski.perso.math.cnrs.fr/Mahler_selecta_new.pdf) | `2862813f5fc24f3a4e5d4af48603053c2657bb4722d9583c5af9f477a3ea55b0` |
| [Cijsouw 1974](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf) | `fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a` |
| [Bugeaud, Thue--Morse--Mahler](https://www.numdam.org/item/AIF_2011__61_5_2065_0.pdf) | `6d7607e8a70e8524630daa45001192113487d9af1f1588c96556283445c7460c` |
| [Adamczewski--Faverjon, arXiv:2604.08208v1](https://arxiv.org/pdf/2604.08208v1) | `c428a9a555b8d7abeb25f3e8a02c8f7880c640e7fe6a2f85c411ca1b68f1945c` |
| [Fischler--Rivoal, Math. Ann. 2026 author PDF](https://www.imo.universite-paris-saclay.fr/~fischler/logE.pdf) | `86669c0103d2a589c9a45970734a9ebac47c737382c015fa026b546960c0301d` |
| [Nguyen, arXiv:2605.30606v2](https://arxiv.org/pdf/2605.30606v2) | `2cfb651d65a9960bc0385a2658005752dd899bb4a8919b08d91c8319a18a87b2` |

Status: `literature-checked` source-pin audit.  It remains a bounded audit,
not a claim that all related literature has been exhausted.

## 8. Independent checker

The audit checker is
[`gfunction_subshift_entropy_attack_20260813_independent_check.py`](gfunction_subshift_entropy_attack_20260813_independent_check.py),
SHA-256
`6c0b96cf3f2b9f8bd611b17495d1c3c2471854e660808d1634f0f3d85117a804`.
It imports no code from the parent checker and uses only the Python standard
library.  Its successful run checks:

* 477 brute-force/automaton cross-checks in bases two and three;
* all 11,110 decimal forbidden words of lengths one through four;
* 433,290 exact integer bounds and 1,011,010 submultiplicativity inequalities;
* 8,190 distinct cylinders in embedded nine-shifts;
* all 11,110 corresponding mapped Thue--Morse survivors;
* 4,096 coefficients of the Mahler equation;
* the exact Gaussian-rational Machin identity;
* finite denominator divisibility for the coefficients of \(H\);
* a fully expanded independent-base language polynomial;
* the sharpened selected-tail factor bound through sixty scales;
* four coefficientwise Cijsouw symmetrizations.

These checks are labeled `experiment`.  They test the proof ledgers and catch
implementation errors; they do not infer an infinite theorem from finite data.

## 9. Final audit classification

| Parent component | Independent classification |
|---|---|
| Missing-word SFT, counts, entropy, dimension | valid local `proof sketch` |
| D-finite/automatic/Mahler category separation | `literature-checked` with valid local specialization |
| Thue--Morse survivor and scalar separator | valid `proof sketch`; cited number-theoretic claim `literature-checked` |
| Machin G-function representation | valid local `proof sketch` |
| Fischler--Rivoal and modern theorem boundaries | `literature-checked`, no hypothesis reversal found |
| Auxiliary-polynomial degree/height ledger | valid local `proof sketch`; direct scheme remains noncontradictory |
| Parent checker | PASS, correctly labeled `experiment` |
| Canonical V1 | remains a `conjecture` |

The audited report is therefore a sound obstruction report, not a solution.
The missing result remains a genuinely digit-sensitive theorem linking this
fixed special value to escape from every proper decimal finite-type subshift.
