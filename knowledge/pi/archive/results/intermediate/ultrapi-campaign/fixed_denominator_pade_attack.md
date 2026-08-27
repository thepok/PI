# Fixed-denominator Padé attack: exact anchors do not synchronize with accuracy

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No return, decimal-cylinder hit, or proof that every finite decimal word
occurs in pi was obtained. Canonical V1 remains a `conjecture`.

This branch gives one material exact finite observation and a corrected
audit of the classical Gauss--Lambert Padé route.  The Gauss continued
fraction for arctangent produces rational shadows of pi with geometric
analytic convergence.  A 2000 expository source says their reduced-
denominator approximation quality tends to \(0.9058\ldots<1\), but an
independent exact-rational replay found that the displayed number nearly
equals the depth-25 quality while later qualities fall below \(0.8\).
Consequently the asserted asymptotic is not audit-safe and cannot prove that
the most favorable exact anchor

\[
             \operatorname{den}(A_n)\mid10^N-16                 \tag{1}
\]

fails.  The valid conditional lemma is that any proved eventual quality bound
strictly below one would close this exact-divisibility transfer.  No such
reduced-denominator theorem was verified here, so this family remains open at
the asymptotic level.

A faster, recently documented Padé variant supplies a striking finite test.
Using Euler's identity and the depth-six Gauss convergents gives

\[
 A_6=4\{F_6(1/2)+F_6(1/3)\}
     ={774756220\over246612571},\qquad
 246612571=19\cdot641\cdot20249.                                \tag{2}
\]

The reduced denominator in (2) **does** divide a fixed-sixteen decimal
denominator:

\[
              246612571\mid10^{684842}-16.                      \tag{3}
\]

The exponent \(684842\) is the least positive solution. Yet an exact
alternating-series bracket proves

\[
                    |\pi-A_6|>{1\over11560000},                 \tag{4}
\]

so the transfer error at (3) exceeds \(10^{684834}\). The exact congruence
and the approximation occur at catastrophically different scales. A
separate high-precision `experiment` finds

\[
 \|(10^{684842}-16)\pi\|_{\mathbb T}
 =0.4582011106795978822479936067816677757\ldots,                 \tag{5}
\]

not a small return. Equation (5) is finite evidence only and is not used in
any deduction.

The bounded primary-source search is `literature-checked` as of the audit
date. Deductions in this report are `proof sketch`; the checker is an
`experiment`. Nothing here is machine-checked or a `candidate resolution`.

## 1. Exact target and quantifiers

The independently audited fixed-return bridge reduces V1 to

\[
 \boxed{\liminf_{N\to\infty}\|(10^N-16)\pi\|_{\mathbb T}=0.}     \tag{6}
\]

Equivalently, along an **unbounded** sequence of positive integers \(N_j\),
there must be integers \(a_j\) with

\[
 \left|\pi-{a_j\over10^{N_j}-16}\right|=o(10^{-N_j}).           \tag{7}
\]

The numerator is free, but the denominator is prescribed. Ordinary
irrationality measures address lower bounds over all denominators and do not
construct (7). Metric restricted-denominator theorems apply to almost every
real and cannot be specialized to the fixed point pi.

For a rational shadow \(A=P/D\) in lowest terms,

\[
 \|(10^N-16)\pi\|_{\mathbb T}
 \leq \|(10^N-16)A\|_{\mathbb T}
      +(10^N-16)|\pi-A|.                                      \tag{8}
\]

Padé accuracy pays only the second term. Divisibility \(D\mid10^N-16\)
pays the first term exactly. Both must occur at the same scale.

## 2. Classical Gauss--Lambert Padé convergents

For positive integers \(p\leq q\), Wang's 2026 equivalence transform of
Gauss's classical continued fraction is

\[
 \arctan{p\over q}
 =\cfrac{p}{q+\cfrac{p^2}{3q+\cfrac{(2p)^2}{5q+
                   \cfrac{(3p)^2}{7q+\cdots}}}}}.              \tag{9}
\]

If \(F_n(p/q)=P_n/Q_n\) denotes its depth-\(n\) convergent before
reduction, continuants give

\[
 \begin{aligned}
 P_n&=q(2n-1)P_{n-1}+(n-1)^2p^2P_{n-2},\\
 Q_n&=q(2n-1)Q_{n-1}+(n-1)^2p^2Q_{n-2}.                        \tag{10}
 \end{aligned}
\]

Wang proves the geometric error ratio

\[
 { |F_{n+1}(p/q)-\arctan(p/q)|
  \over |F_n(p/q)-\arctan(p/q)| }
 \longrightarrow
 r_{p,q}=\left({\sqrt{p^2+q^2}-q\over p}\right)^2<1.          \tag{11}
\]

For \(p=q=1\), four times these convergents begin

\[
 4,\ 3,\ {19\over6},\ {160\over51},\ {1744\over555},
 {644\over205},\ldots                                         \tag{12}
\]

and approximate pi. Their unreduced continuant denominators obey

\[
 Q_n=(2n-1)Q_{n-1}+(n-1)^2Q_{n-2},\quad Q_0=Q_1=1,             \tag{13}
\]

and have the exact exponential generating function

\[
             \sum_{n\ge0}{Q_nx^n\over n!}
              ={1\over\sqrt{1-2x-x^2}}.                        \tag{14}
\]

Beukers identifies the same rational sequence through positive integrals
and records the asymptotic approximation quality

\[
 -{\log|\pi-A_n|\over\log\operatorname{den}(A_n)}
          \longrightarrow 0.9058\ldots<1.                     \tag{15}
\]

but supplies no proof or formula for that decimal in the article.  Independent
exact rational Machin enclosures instead certify, for

\[
 M_n=-{\log|\pi-A_n|\over\log\operatorname{den}(A_n)},
\]

that \(0.905<M_{25}<0.906\), \(M_{100}<0.85\), and
\(M_{200},M_{1000}<0.8\).  These finite values do not logically disprove a
later return to the printed limit, but they make (15) unsafe as a research
premise.  Ekhad--Zeilberger report \(0.79119792\ldots\) for a related
denominator-clearing analysis; that is a useful lead, not a theorem about the
actual reduced qualities \(M_n\) or a lower-error estimate.

The underlying conditional accounting remains valid. Let
\(d_n=\operatorname{den}(A_n)\), suppose
\(d_n\mid10^{N_n}-16\), and suppose \(d_n\to\infty\). Necessarily

\[
                   10^{N_n}-16\ge d_n.                         \tag{16}
\]

If one separately proved \(M_n\le L+o(1)\) for some \(L<1\), choose
\(\eta>0\) with \(L+\eta<1\).  Then, for all large \(n\),

\[
 |\pi-A_n|>d_n^{-(L+\eta)}.
\]

Combining this with (16) yields

\[
 (10^{N_n}-16)|\pi-A_n|
 \ge d_n^{1-(L+\eta)}\longrightarrow\infty.                   \tag{17}
\]

Thus a proved eventual reduced-denominator quality below one would exclude
this transfer.  Neither (11) nor the finite checkpoints proves that premise:
(11) measures decay per depth, whereas the needed theorem concerns the
**reduced** denominator.  The independent audit therefore withdrew the
original unconditional family-closure claim.

The first 200 reduced denominators exhibit eligible 5-adic windows only at
depths \(1\!:\!4\), \(20\!:\!24\), and \(110\!:\!114\). This is an
`experiment`, not an asymptotic theorem. At depths \(20\!:\!24\), every
denominator is divisible by \(11\), but \(10^N\equiv(-1)^N\not\equiv5
\pmod {11}\), so none can divide \(10^N-16\). At depths \(110\!:\!114\),
the tested denominators have several analogous small-prime obstructions.
These finite obstructions are exact experiments, not evidence for the missing
asymptotic premise.

## 3. A faster Padé shadow with an exact but useless anchor

Euler's exact angle identity is

\[
            {\pi\over4}=\arctan{1\over2}+\arctan{1\over3}.     \tag{18}
\]

Using (9) at both arguments and equal depth six gives the exact rational in
(2). Direct continuant arithmetic verifies it. Its denominator is coprime
to ten, and the local discrete logs are

\[
\begin{array}{c|ccc}
p&19&641&20249\\ \hline
\min\{N>0:10^N\equiv16\pmod p\}&14&10&1472\\
\operatorname{ord}_p(10)&18&32&2531.
\end{array}                                                    \tag{19}
\]

The generalized Chinese remainder theorem applied to (19) gives

\[
 N\equiv684842\pmod{728928},                                  \tag{20}
\]

so (3) holds and \(684842\) is minimal.

This is the strongest congruence alignment found in this branch, but (4)
closes it immediately. To prove (4) without numerical pi, let

\[
 L=4\sum_{k=0}^{19}{(-1)^k\over2k+1}
       \left(2^{-(2k+1)}+3^{-(2k+1)}\right).                   \tag{21}
\]

Each arctangent series in (21) stops on a negative term, so the alternating
series theorem gives \(L<\pi\). Exact rational subtraction gives

\[
             L-A_6>{1\over11560000}.                           \tag{22}
\]

Thus \(A_6<L<\pi\), and hence

\[
 |\pi-A_6|=\pi-A_6>L-A_6>{1\over11560000},                     \tag{23}
\]

which proves (4) and also certifies that \(A_6<\pi\). The companion checker
uses (21)--(23); the explicit parity is kept here to prevent a hidden
alternating-series sign error.

Combining (3)--(4), the exact-anchor version of (8) has transfer term

\[
 (10^{684842}-16)|\pi-A_6|>10^{684834}.                        \tag{24}
\]

A lower bound this large on the transfer-error term says nothing by itself
about the true return; it shows that (8) cannot certify smallness through
this shadow. Direct pi evaluation gives (5), showing only that this one
finite exponent is not exceptional.

## 4. Why recent refinements do not alter the ledger

Two current papers were checked directly.

1. Wang proves the two-parameter family (9) and exact rate (11). It is a
   fixed-function Padé construction. It supplies no theorem arranging its
   reduced denominator inside \(10^N-16\), and faster analytic rate for
   larger \(q/p\) does not imply favorable reduced-denominator quality.
2. Farhi refines two-term Machin identities through the ordinary continued
   fraction of a ratio of two arctangent values. His rational shadows have
   error \(O(D_n^{-2})\), where \(D_n\) is a continued-fraction denominator.
   The unreduced common denominator is controlled by products of tangent
   denominators, but the paper supplies no equality theorem or divisibility/
   discrete-log control for the final reduced denominator.
   Already its displayed shadows \(1748/553\) and
   \(216791924/68976559\) fail fixed-sixteen divisibility: \(553\) contains
   an incompatible residue class, and the latter contains the same issue.

Hata-type Hermite--Padé integrals improve scalar irrationality measures by
carefully removing prime factors from common denominators. This is useful
for a lower bound on arbitrary rational approximation. It does not select
the multiplicative coset

\[
       \{d:d\mid10^N-16\text{ for some }N\},                   \tag{25}
\]

nor create the upper approximation (7). A finite irrationality measure is
logically compatible with both dense and nondense decimal orbits.

## 5. Checker and source record

Companion:
[`fixed_denominator_pade_attack_check.py`](fixed_denominator_pade_attack_check.py)

The checker uses exact integers and rationals to verify:

1. the initial Gauss--Lambert convergents and recurrence (10)--(13);
2. the finite 5-adic windows through depth 200 (`experiment` only);
3. the Euler depth-six rational (2) and its exact factorization;
4. the local orders/discrete logs, the CRT solution (20), and minimality;
5. the alternating rational bracket proving (4); and
6. the enormous mismatch (24).

The high-precision evaluation (5) was repeated at 80 and 140 guard digits
and agreed for 70 displayed digits. It remains an `experiment` and is not in
the proof checker.

The adversarial checker uses a separate continued-fraction evaluation and
exact rational Machin bounds for pi.  It reproduces the finite Euler/CRT/error
claims and certifies the quality checkpoints above.  The resulting audit is
[`fixed_denominator_pade_independent_audit.md`](fixed_denominator_pade_independent_audit.md),
with replay
[`fixed_denominator_pade_independent_check.py`](fixed_denominator_pade_independent_check.py).

Sources checked on **2026-08-12 UTC**:

| source | exact use | source pin |
|---|---|---|
| [Wang, *A Family of Continued Fraction Identities for Arctangent Values*, arXiv:2601.11892v3](https://arxiv.org/abs/2601.11892v3) | Theorem 1.2 and Proposition 4.2: (9) and (11) | PDF SHA-256 `26013cf9ef1595031a41cb4b67d7e7d393ae9dba33f1f0b833aafc2b1d508dc9` |
| [Farhi, *On refinements of two-term Machin-like formulas*, arXiv:2601.10300v1](https://arxiv.org/abs/2601.10300v1) | Corollary 2.6 and displayed Euler refinements; accuracy without fixed-denominator arithmetic | PDF SHA-256 `86cdd17355a4462db9ac18b6e7dcfe2559e14089ed02272247df6cd71ce7b90e` |
| [Beukers, *A rational approach to pi*, NAW 5/1 (2000), 372--379](https://www.nieuwarchief.nl/serie5/pdf/naw5-2000-01-4-372.pdf) | Integral interpretation and the printed, but currently audit-unsafe, \(0.9058\ldots\) reduced-quality assertion | PDF SHA-256 `7826ef90d8f0668a0952b0eed93887ada962d8e4fef2547193a8806d61985f6b` |
| [Ekhad--Zeilberger, *Searching for Apéry-Style Miracles*, arXiv:1405.4445v1](https://arxiv.org/abs/1405.4445v1) | Related `RAint` denominator-clearing value \(0.79119792\ldots\); not used as an actual reduced-quality limit | PDF SHA-256 `4b74fc949a5900a257a0badbe7d5519c563195f8c28c0c8159617b733b1b2ab8` |
| [Hata, *Rational approximations to pi and some other numbers*, Acta Arith. 63 (1993), 335--349](https://doi.org/10.4064/aa-63-4-335-349) | Representative Hermite--Padé/irrationality-measure construction and denominator-prime removal | PDF SHA-256 `c3294d1987dfd013ec4d13f93737233177817d50c9c102ea95033e986cd9e3df` |

Search phrases covered combinations of *prescribed denominator rational
approximation*, *restricted denominators pi*, *arctangent Padé denominator
recurrence*, *Hermite--Padé pi*, and *fixed denominator linear forms in
logarithms*. No primary theorem was found that creates a fixed-pi upper
approximation on \(10^N-16\).

## Bottom line

The classical Gauss--Lambert asymptotic exact-divisibility route is **not**
closed: its needed reduced-denominator quality limit was withdrawn after
adversarial replay.  The conditional lemma (16)--(17) remains valid, and the
finite quality checkpoints strongly suggest a bound below one, but finite
evidence is not a proof.  A faster Euler split really does hit the congruence
lattice once, at the exact exponent
\(684842\), but its Archimedean transfer-error term exceeds
\(10^{684834}\). Current Machin refinements and Hata-style integrals improve analytic
approximation without supplying the missing ordered denominator
synchronization. No fixed-sixteen return was proved; V1 remains a
`conjecture`.
