# Independent audit: fixed-denominator Padé attack

Audit date: **2026-08-12 UTC**  
Primary artifact:
[`fixed_denominator_pade_attack.md`](fixed_denominator_pade_attack.md)  
Corrected primary SHA-256:
`8be600862e2734b0fb2cd053a0948335e4f8c27bea4ca2df45029a4f004ca986`  
Primary checker:
[`fixed_denominator_pade_attack_check.py`](fixed_denominator_pade_attack_check.py)  
Primary checker SHA-256:
`bd8c7a0438d6d0b3e2c2b0d9f82c789a5b792effb5339641b6e8839307ae057d`  
Independent checker:
[`fixed_denominator_pade_independent_check.py`](fixed_denominator_pade_independent_check.py)

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

**PASS for the corrected scope.**

Correction history is part of this verdict.  The initially audited primary
artifact (SHA-256
`1c335f71b5ce589411220bd9cb633aea351f252f575e144b6b8599706ce0e30a`)
failed because it used Beukers' printed \(0.9058\ldots\) reduced-quality
limit as a theorem and thereby claimed that a whole exact-divisibility
transfer was closed.  The corrected artifact, whose hash is pinned above,
withdraws that inference, records the exact counter-checkpoints, keeps only
the valid conditional lemma, narrows the Farhi denominator claim, and
preserves the finite Euler/CRT result with its modulo-one warning.  All five
required corrections are present.

The discovery behind the correction remains important.  Beukers' 2000
article really does print that the qualities of the displayed
Gauss--Lambert approximants tend to \(0.9058\ldots\), and it defines quality
using a coprime numerator and denominator.  However, the article gives no
proof or formula for that number, and an exact replay of the same reduced
rational sequence behaves incompatibly with treating \(0.9058\ldots\) as a
verified asymptotic input:

\[
 M_n:={-\log|\pi-A_n|\over\log\operatorname{den}(A_n)},
 \qquad
 M_{25}=0.9058071158\ldots,
\]

but

\[
 M_{100}=0.8475527595\ldots,
 \quad M_{200}=0.7987630318\ldots,
 \quad M_{1000}=0.7968316080\ldots .                         \tag{A1}
\]

These are not ordinary floating-point evaluations of pi.  The independent
checker encloses pi between exact rational Machin-series bounds, encloses
each error, and verifies the rational-power certificates

\[
 0.905<M_{25}<0.906,
 \qquad M_{100}<0.85,
 \qquad M_{200}<0.8,
 \qquad M_{1000}<0.8.                                      \tag{A2}
\]

Finite values in (A2) do not, by themselves, logically disprove a later
return to a \(0.9058\ldots\) limit.  They do show that the number printed by
Beukers is nearly exactly the depth-25 value and that the source's bare
asymptotic assertion needs a proof or a correction before it can carry a
research claim.  A later Ekhad--Zeilberger calculation reports
\(0.79119792\ldots\) for the corresponding \(k=0\) arctangent integral via
its `RAint` denominator-clearing analysis.  That result points in the same
direction as (A1), but it is **not** a theorem that the actual reduced
qualities \(M_n\) have that limit, and it is **not** a lower-error theorem.
It therefore cannot simply be substituted into (15)--(17).

Consequently the inference (15) \(\Rightarrow\) (17), although logically
correct conditional on an eventual quality bound below one, is not presently
supported by a verified reduced-denominator asymptotic.  The corrected
primary report now says exactly this and no longer claims that the classical
family is closed.  No V1 claim follows.

The separate finite result passes: the Euler depth-six rational, its prime
factorization, all three local discrete logarithms and orders, the generalized
CRT class and its least positive representative \(684842\), the alternating
rational error bracket, and the enormous Archimedean transfer term all replay
exactly.  This finite result is a useful `experiment` plus exact arithmetic
`proof sketch`, but it neither gives nor rules out a true circle return.

## 1. Classical continued fraction: what passes

Wang's Theorem 1.2 states, for positive \(p\le q\),

\[
 \arctan{p\over q}
 =\cfrac{p}{q+\cfrac{p^2}{3q+\cfrac{(2p)^2}{5q+\cdots}}}.
\]

The continuant recurrence in the primary report follows from the standard
generalized-continued-fraction recurrence.  The independent checker evaluates
the same finite fractions from the bottom rather than calling the primary
routine.  For \(p=q=1\), both methods give

\[
 4,\ 3,\ {19\over6},\ {160\over51},\ {1744\over555},\ {644\over205}.
\]

The pre-reduction denominators begin

\[
 1,1,4,24,204,2220,29520,463680.
\]

The exponential generating function

\[
 F(x)=\sum_{n\ge0}{Q_nx^n\over n!}
     =(1-2x-x^2)^{-1/2}
\]

is consistent with the recurrence: differentiating gives
\((1-2x-x^2)F'=(1+x)F\), and coefficient extraction gives
\(Q_{k+1}=(2k+1)Q_k+k^2Q_{k-1}\).

Wang's Proposition 4.2 states the analytic error ratio

\[
 {|F_{n+1}(p/q)-\arctan(p/q)|\over
   |F_n(p/q)-\arctan(p/q)|}
 \longrightarrow
 \left({\sqrt{p^2+q^2}-q\over p}\right)^2.
\]

This is correctly quoted.  It is an error-per-depth statement and does not
determine growth of the **reduced** denominator.  The primary report itself
correctly warns about that distinction.

The finite 5-adic windows through depth 200 also replay:

\[
 1{:}4,\qquad20{:}24,\qquad110{:}114.
\]

The obstruction descriptions can be made fully explicit.  Every reduced
denominator at depths 20--24 is divisible by \(11\), while \(16\) is not in
the subgroup generated by \(10\pmod {11}\).  Every denominator at depths
110--114 is divisible by \(37\), while

\[
 \langle10\rangle\pmod {37}=\{1,10,26\}
\]

omits \(16\).  These are finite `experiment` results only.

## 2. Failure of the reduced-denominator premise

Beukers defines the quality \(M\) of a reduced rational \(p/q\) by

\[
 \left|\pi-{p\over q}\right|=q^{-M}.
\]

On the same page, the article lists exactly the first six fractions above,
states that they are the Gauss continued-fraction convergents, and then says
their qualities tend to \(0.9058\ldots\).  Thus the discrepancy is not
explained by an obvious switch from a reduced to an unreduced denominator or
by a different indexing convention.

The independent check proves (A2) as follows.  With an even number of terms,
the alternating series for each arctangent gives rational lower and upper
bounds.  Machin's exact identity

\[
 \pi=16\arctan(1/5)-4\arctan(1/239)
\]

therefore gives exact rational bounds \(L<\pi<U\).  For an approximant
outside this tiny interval, exact subtraction gives
\(e_n^-\le|\pi-A_n|\le e_n^+\).  The script then checks, using integers and
`Fraction` only,

\[
 (e_{25}^+)^{200}d_{25}^{181}<1,
 \quad (e_{25}^-)^{500}d_{25}^{453}>1,
\]

and

\[
 (e_{100}^-)^{20}d_{100}^{17}>1,
 \quad (e_{200}^-)^5d_{200}^4>1,
 \quad (e_{1000}^-)^5d_{1000}^4>1.
\]

Those are precisely the rational certificates in (A2).  No decimal value of
pi is trusted.

The conditional algebra after (15) is sound.  If one proves for this family
that \(M_n\le L+o(1)\) for some \(L<1\), then

\[
 d_n\mid10^{N_n}-16,\quad d_n\to\infty
 \quad\Longrightarrow\quad
 (10^{N_n}-16)|\pi-A_n|\to\infty.
\]

The initial audit failure was specifically the use of a source assertion in
place of a reliable theorem with that hypothesis.  The corrected artifact
does not make that inference.  Numerical evidence is not a proof, even when
it strongly suggests that a corrected exponent is below one.

## 3. Euler depth-six anchor: exact PASS

Euler's angle addition identity is exact:

\[
 \arctan(1/2)+\arctan(1/3)=\pi/4.
\]

Bottom-up evaluation of the two depth-six Gauss fractions gives

\[
 A_6={774756220\over246612571},
 \qquad246612571=19\cdot641\cdot20249,
\]

and trial division independently certifies that all three factors are prime.
Direct modular iteration gives

| modulus | first \(N>0\) with \(10^N\equiv16\) | order of \(10\) |
|---:|---:|---:|
| \(19\) | \(14\) | \(18\) |
| \(641\) | \(10\) | \(32\) |
| \(20249\) | \(1472\) | \(2531\) |

A separate progression-stepping generalized CRT replay yields

\[
 N\equiv684842\pmod{728928}.
\]

Because \(0<684842<728928\), this is the least positive solution, and direct
modular exponentiation verifies

\[
 246612571\mid10^{684842}-16.
\]

For the error direction, the 20-term sums for both
\(\arctan(1/2)\) and \(\arctan(1/3)\) end with negative terms.  Their sum is
therefore a strict lower bound for pi.  Exact subtraction independently
verifies

\[
 A_6<L<\pi,
 \qquad L-A_6>{1\over11560000}.
\]

It follows that

\[
 (10^{684842}-16)|\pi-A_6|>10^{684834}.
\]

This is a lower bound on one term in the triangle-inequality transfer.  It is
**not** a lower bound on
\(\|(10^{684842}-16)\pi\|_{\mathbb T}\), because the transfer term may have an
integer-sized part and cancel modulo one.  The primary report states this
distinction correctly.

As a separate check of the reported finite `experiment`, pi was evaluated at
more than \(684842\) decimal digits, giving fractional part

\[
 \{(10^{684842}-16)\pi\}
 =0.54179888932040211775200639321833222429\ldots
\]

and hence circle distance

\[
 0.45820111067959788224799360678166777570\ldots .
\]

This agrees with equation (5), but is not used in any proof.

## 4. Recent-source and scope audit

- Wang's Theorem 1.2 and Proposition 4.2 support the continued fraction and
  analytic error ratio.  They provide no reduced-denominator divisibility
  theorem.
- Farhi's Corollary 2.6 proves
  \(a_{-n}u_n+a_{-n+1}u_{n+1}=\pi/4+O(D_{n-1}^{-2})\).  The displayed
  examples are \(1748/553\) and \(216791924/68976559\).  Factoring gives
  \(553=7\cdot79\) and
  \(68976559=79\cdot873121\); \(16\notin\langle10\rangle\pmod {79}\), so
  both fail fixed-sixteen divisibility.  The paper does not prove that every
  later **reduced** denominator equals a product of tangent denominators;
  the safe general statement is that the unreduced common denominator
  divides such a product.  The corrected primary report uses this narrowed
  wording.
- Hata's paper uses Hermite--Padé forms and removes systematic prime factors
  to improve irrationality estimates.  No selection theorem for the
  multiplicative coset \(d\mid10^N-16\) occurs in the paper.  This supports
  the primary report's limited methodological comparison, not a universal
  no-go theorem.

The cited PDF hashes were independently reproduced:

| source | SHA-256 |
|---|---|
| Wang, arXiv:2601.11892v3 | `26013cf9ef1595031a41cb4b67d7e7d393ae9dba33f1f0b833aafc2b1d508dc9` |
| Farhi, arXiv:2601.10300v1 | `86cdd17355a4462db9ac18b6e7dcfe2559e14089ed02272247df6cd71ce7b90e` |
| Beukers, NAW 2000 | `7826ef90d8f0668a0952b0eed93887ada962d8e4fef2547193a8806d61985f6b` |
| Hata, Acta Arith. 1993 | `c3294d1987dfd013ec4d13f93737233177817d50c9c102ea95033e986cd9e3df` |
| Ekhad--Zeilberger, arXiv:1405.4445v1 | `4b74fc949a5900a257a0badbe7d5519c563195f8c28c0c8159617b733b1b2ab8` |

## 5. Correction disposition and retained scope

The corrected primary artifact implements every required change:

1. Equation (15) is retained only as an accurately attributed, explicitly
   audit-unsafe source assertion.  Deduction (17) is now conditional on a
   separately proved bound \(M_n\le L+o(1)\) with \(L<1\), and the
   bottom-line family-closure claim is withdrawn.
2. The exact finite certificates (A2) are recorded.  The
   \(0.79119792\ldots\) value is labeled a denominator-clearing lead rather
   than a theorem about the actual \(M_n\).
3. The valid conditional exact-divisibility lemma is retained without
   silently supplying its missing hypothesis.
4. The Farhi denominator wording is narrowed to unreduced denominator
   control, with no equality or reduced-divisibility claim.
5. The Euler depth-six finite result is retained together with the explicit
   warning that a huge Archimedean transfer term is not a true circle-return
   lower bound.

For this corrected scope, the branch supports the exact statement:

> One depth-six Euler/Gauss rational has reduced denominator dividing
> \(10^{684842}-16\), but its Archimedean approximation error is far too large
> for the triangle inequality to certify a return; direct high-precision
> evaluation also finds no return at that one exponent.

That is a finite `proof sketch` plus `experiment`, not a proof that this Padé
family can never work, not a fixed-sixteen return, and not a proof of V1.

## 6. Replay record

Commands run:

```text
python -m py_compile \
  work/ultrapi-resume/fixed_denominator_pade_attack_check.py \
  work/ultrapi-resume/fixed_denominator_pade_independent_check.py

python work/ultrapi-resume/fixed_denominator_pade_attack_check.py
PASS: Gauss recurrence, finite 5-adic windows, Euler depth-six fixed-sixteen anchor, and exact rational error mismatch

python work/ultrapi-resume/fixed_denominator_pade_independent_check.py
PASS (adversarial replay): finite Euler/CRT/error claims hold; exact quality checkpoints place M_25 in (0.905,0.906), M_100<0.85, and M_200,M_1000<0.8, so the quoted 0.9058 asymptotic is not certified
```

No Lean declaration was added.  Nothing in this audit is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.  Canonical V1 remains a
`conjecture`.
