# Gauss--Lambert Padé denominators: the exact missing gcd theorem

Audit date: **2026-08-12 UTC**
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No fixed-sixteen return and no decimal-cylinder hit was obtained. Canonical
V1 remains a `conjecture`.

This audit corrects the asymptotic ledger for the classical Gauss--Lambert
rational approximants to pi.  Their recurrence, exponential generating
functions, integral error, and a large canonical numerator--denominator gcd
can all be derived exactly.  Those facts rigorously explain the constant

\[
  \delta_0=
  {2\log(1+\sqrt2)\over
   1+\log(1+\sqrt2)+\tfrac12\log2}
  =0.7911979206687043762\ldots .                              \tag{1}
\]

But (1) is a **one-sided lower bound on approximation quality**, not an
established limit.  The actual reduced denominator contains an additional
factor

\[
 E_n={\gcd(4P_n,Q_n)\over
       2^{\lfloor n/2\rfloor}\operatorname{odd}
       (n!/\operatorname{lcm}(1,\ldots,n))}.                  \tag{2}
\]

The assertion that the reduced qualities have the limit in (1) is equivalent
to the new arithmetic statement

\[
                         \log E_n=o(n).                       \tag{3}
\]

No proof of (3) was found.  Even better for the present project, the weaker
bound

\[
 \limsup_{n\to\infty}{\log E_n\over n}
 <1-\log(1+\sqrt2)+\tfrac12\log2
 =0.4652000032604297\ldots                                   \tag{4}
\]

would force eventual reduced quality strictly below one and would exclude
this specific exact-divisibility transfer.  No checked source proves (4).

There is an exact reason that (3)--(4) are not a routine consequence of the
factorial normalization.  For every odd prime \(p\), the recurrence has the
prime-shift congruence

\[
 Q_{p+s}\equiv0,\qquad P_{p+s}\equiv P_pQ_s\pmod p.           \tag{5}
\]

Consequently, when \(p>n/2\), the otherwise unforced prime \(p\) enters the
gcd at depth \(n=p+s\) precisely when \(p\mid Q_s\).  At \(n=30\), for
example, \(23\mid Q_7=463680\), and the exceptional factor is
\(E_{30}=46\).  Thus the missing estimate asks for uniform aggregate control
of shifted large prime divisors of the earlier continuants; it is not supplied
by analytic Padé convergence or by the prime number theorem.

The exact deductions below are a `proof sketch`.  The bounded literature
search is `literature-checked` as of the audit date.  The companion exact
checker is an `experiment`.  Nothing here is machine-checked, a
`candidate resolution`, or a proof of V1.

## 1. Exact target and quantifiers

For \(n\ge0\), define integer sequences

\[
 \begin{array}{c|cc}
       &n=0&n=1\\ \hline
 P_n&0&1\\
 Q_n&1&1
 \end{array}
\]

and, for \(n\ge2\),

\[
 X_n=(2n-1)X_{n-1}+(n-1)^2X_{n-2}.                           \tag{6}
\]

The depth-\(n\) Gauss--Lambert shadow is

\[
 A_n={4P_n\over Q_n}={a_n\over d_n},\qquad
 d_n={Q_n\over g_n},\quad g_n:=\gcd(4P_n,Q_n),               \tag{7}
\]

where \(a_n/d_n\) is in lowest terms.  Its first values are

\[
 4, 3, {19\over6}, {160\over51}, {1744\over555},
 {644\over205},\ldots .                                     \tag{8}
\]

The quantity under audit is the actual reduced quality

\[
 M_n={-\log|\pi-A_n|\over\log d_n}.                           \tag{9}
\]

The word “denominator” in (9) always means \(d_n\), not the unreduced
continuant \(Q_n\), and any asymptotic assertion is over **all** positive
integer depths \(n\to\infty\).  Finite quality values cannot establish a
limit.

## 2. Closed forms and the exact integral error

Put

\[
 F(x)=\sum_{n\ge0}{Q_nx^n\over n!},\qquad
 G(x)=\sum_{n\ge0}{P_nx^n\over n!}.
\]

Multiplying (6) by \(x^n/n!\) and summing gives

\[
 F(x)={1\over\sqrt{1-2x-x^2}},\qquad
 G(x)=F(x)\int_0^xF(t)\,dt.                                 \tag{10}
\]

Two useful exact coefficient formulas follow:

\[
 Q_n=\sum_{0\le k\le n/2}
 {n!^2\over2^k k!^2(n-2k)!},                                \tag{11}
\]

and

\[
 P_n=\sum_{a+b=n-1}{n\choose a}Q_aQ_b.                       \tag{12}
\]

The continuant determinant is

\[
 P_nQ_{n-1}-P_{n-1}Q_n
     =(-1)^{n-1}((n-1)!)^2.                                 \tag{13}
\]

Now let

\[
 J_n=\int_0^1 {t^n(1-t)^n\over(1+t^2)^{n+1}}\,dt>0.          \tag{14}
\]

Summing the geometric series inside the integral gives

\[
 \sum_{n\ge0}{2^{n+2}n!J_n\over n!}x^n
 =4\int_0^1{dt\over1+t^2-2xt(1-t)}.
\]

Completing the square in the last denominator gives the exact analytic
identity near \(x=0\)

\[
 4\int_0^1{dt\over1+t^2-2xt(1-t)}
       =\pi F(-x)-4G(-x).                                   \tag{14a}
\]

Comparing exponential-generating-function coefficients in (14a) yields

\[
 2^{n+2}n!J_n=(-1)^n(Q_n\pi-4P_n).                           \tag{15}
\]

Therefore

\[
                     |\pi-A_n|={2^{n+2}n!J_n\over Q_n}.       \tag{16}
\]

Let \(\rho=\sqrt2-1=(1+\sqrt2)^{-1}\).  The function

\[
 h(t)={t(1-t)\over1+t^2}
\]

has its unique maximum on \([0,1]\) at \(t=\rho\), with
\(h(\rho)=\rho/2\).  The elementary maximum principle for positive
integrals gives

\[
                   \lim_{n\to\infty}J_n^{1/n}={\rho\over2}.  \tag{17}
\]

The unique dominant positive singularity in (10), or standard coefficient
bounds applied directly to (11), gives

\[
 \log Q_n=n\log n+{-1+\log(1+\sqrt2)}n+o(n).                \tag{18}
\]

Combining (16)--(18),

\[
 \lim_{n\to\infty}{-\log|\pi-A_n|\over n}
       =2\log(1+\sqrt2)=:A
       =1.762747174039086\ldots .                            \tag{19}
\]

This is the analytic part of the problem.  It is exact and contains no
reduced-denominator information.

## 3. The canonical common divisor

Let

\[
 L_n=\operatorname{lcm}(1,2,\ldots,n),\qquad
 H_n=2^{\lfloor n/2\rfloor}\operatorname{odd}(n!/L_n),       \tag{20}
\]

where \(\operatorname{odd}(m)=m/2^{v_2(m)}\).  Then

\[
                         H_n\mid g_n.                        \tag{21}
\]

Here is a coefficient proof of (21).

For an odd prime \(p\), (11) shows

\[
 v_p(Q_n)\ge v_p(n!).                                       \tag{22}
\]

In (10), integrating \(F\) introduces only a divisor
\(m\le n\).  More explicitly, the summand of (12) indexed by
\(a+b=n-1\) has valuation at least

\[
 \begin{split}
 &v_p\!\left({n!\over a!(b+1)!}\right)+v_p(Q_a)+v_p(Q_b)\\
 &\hspace{20mm}\ge v_p(n!)-v_p(b+1).
 \end{split}                                                 \tag{22a}
\]

Taking the worst possible \(b+1\le n\) gives

\[
 v_p(P_n)\ge v_p(n!)-\max_{m\le n}v_p(m)
             =v_p(n!)-v_p(L_n).                              \tag{23}
\]

Thus the odd part of \(n!/L_n\) divides both \(P_n\) and \(Q_n\).

For the prime two, (11) also gives

\[
 v_2(Q_n)\ge\lfloor n/2\rfloor.                              \tag{24}
\]

For completeness, write \(s_2(m)\) for the binary digit sum and set
\(b=n-2k\).  Legendre's formula says that the 2-adic valuation of the
\(k\)-th summand in (11), minus \(\lfloor n/2\rfloor\), is

\[
 \left\lceil{b\over2}\right\rceil
 +2s_2(k)+s_2(b)-2s_2(2k+b).                                \tag{24a}
\]

This is nonnegative because
\(s_2(2k+b)\le s_2(k)+s_2(b)\) and
\(s_2(b)\le\lceil b/2\rceil\).  Thus every summand, not merely their sum,
has the divisibility asserted in (24).

Formula (12) gives a particularly transparent companion bound.  Every term
has a factor \(Q_aQ_b\), where \(a+b=n-1\), so

\[
 v_2(P_n)\ge
 \min_{a+b=n-1}\{\lfloor a/2\rfloor+\lfloor b/2\rfloor\}
 \ge\lfloor n/2\rfloor-1.                                  \tag{25}
\]

Equations (22)--(25) prove (21), with spare powers of two on the numerator
side.

The prime number theorem in the equivalent form
\(\log L_n=n+o(n)\), together with Stirling's formula and
\(v_2(n!)=n+o(n)\), gives

\[
 \log H_n=n\log n-(2+\tfrac12\log2)n+o(n).                  \tag{26}
\]

Consequently

\[
 \log{Q_n\over H_n}
 =\{1+\log(1+\sqrt2)+\tfrac12\log2\}n+o(n)
 =Cn+o(n),                                                   \tag{27}
\]

where

\[
 C=2.2279471772995156799\ldots .                             \tag{28}
\]

Since \(d_n\le Q_n/H_n\), (19) and (27) yield the rigorous one-sided
statement

\[
                  \liminf_{n\to\infty}M_n\ge {A\over C}
                  =0.7911979206687043762\ldots .             \tag{29}
\]

This recovers exactly the \(k=0\) number printed by
Ekhad--Zeilberger.  Their number has the correct orientation for denominator
clearing: it is a guaranteed quality floor, not an upper bound and not, by
itself, the actual reduced-quality limit.

## 4. The exceptional gcd is the whole missing theorem

Define \(E_n\) by (2).  From (7),

\[
                d_n={Q_n\over H_nE_n}.                       \tag{30}
\]

Equations (19), (27), and (30) make the accounting exact:

\[
 M_n={An+o(n)\over Cn-\log E_n+o(n)}.                        \tag{31}
\]

Because \(A_n\to\pi\) and pi is irrational, the reduced denominators
\(d_n\) tend to infinity: otherwise a bounded-denominator subsequence would
take only finitely many rational values near pi.  Thus the logarithmic
denominator in (31) is eventually positive.  It follows from (31) that:

1. The limit \(M_n\to A/C\) holds **if and only if**
   \(\log E_n=o(n)\).
2. To obtain the weaker transfer-exclusion conclusion \(M_n\le L<1\)
   eventually, it suffices to prove (4).
3. A lower bound such as (29) has the wrong direction for excluding an exact
   divisibility transfer.

The exceptional factor is real, not a bookkeeping artifact.  Exact values
include

\[
 \begin{array}{c|rrrrrrrr}
 n&25&30&72&100&200&1000&1500&2000\\ \hline
 E_n&3&46&16473&5&9&1&5869947&203985322053.
 \end{array}                                                  \tag{32}
\]

The values fluctuate sharply.  Their small apparent exponential rate is an
`experiment`; it does not prove (3) or (4).

## 5. Exact prime-shift mechanism

The source of the fluctuations can already be seen modulo one odd prime.
Formula (11) implies

\[
                         Q_p\equiv0\pmod p.                  \tag{33}
\]

The recurrence then gives \(Q_{p+1}\equiv0\pmod p\), so
\(Q_{p+s}\equiv0\pmod p\) for every \(s\ge0\).  On the other hand,
(13), Wilson's theorem, and \(Q_p\equiv0\pmod p\) show
\(P_pQ_{p-1}\equiv1\pmod p\), hence
\(P_p\not\equiv0\pmod p\).  Since the coefficients of (6) at
index \(p+s\) reduce to the coefficients at index \(s\), the two initial
values at \(s=0,1\) give

\[
                         P_{p+s}\equiv P_pQ_s\pmod p.         \tag{34}
\]

For \(p>n/2\), write \(n=p+s\) with \(0\le s<p\).  Combining
(33)--(34),

\[
             p\mid g_n\quad\Longleftrightarrow\quad p\mid Q_s. \tag{35}
\]

Such a prime contributes nothing to the odd factorial/LCM exponent in
\(H_n\), so it enters \(E_n\).  For example,

\[
 Q_7=463680=23\cdot20160,qquad30=23+7,qquad23\mid E_{30}.   \tag{36}
\]

There is also a clean prime-power version of the periodic shift.  If
\(q=p^r\), (11) implies \(q\mid Q_q\); recurrence (6) then gives, for every
\(s\ge0\),

\[
 Q_{q+s}\equiv0,\qquad P_{q+s}\equiv P_qQ_s\pmod q.         \tag{35a}
\]

Unlike \(P_p\) modulo \(p\), the coefficient \(P_q\) need not be a unit
modulo \(q\), so (35a) is **not** promoted to an iff criterion for exact
\(p\)-adic valuations.  Higher-power effects do occur: exact arithmetic gives
\(17^2\mid E_{72}\).  Thus a proof of
(3), or merely (4), must control the total logarithmic weight of shifted
prime and prime-power divisors like (35), uniformly in \(n\).  The ordinary
singularity analysis of \(F\), the error integral, and denominator-clearing
divisibility do not address that distribution.

## 6. Exact checker and bounded experiment

Companion:
[`gauss_pade_reduced_denominator_check.py`](gauss_pade_reduced_denominator_check.py)

It independently verifies with exact integers:

1. the recurrence, first reduced shadows, formulas (11)--(13);
2. \(H_n\mid g_n\) for every \(1\le n\le1200\), plus the displayed
   high-depth checkpoints at 1500 and 2000;
3. all exceptional-factor checkpoints in (32), plus several others;
4. the prime-shift congruences (33)--(35) for every odd prime \(p\le199\),
   and (35a) for every prime power \(q\le199\); and
5. the exact logarithmic constants in (1) and (4).

On the finite range through 1200, the largest observed values of
\(\log E_n/n\) on three tails are below \(0.138\) for \(n\ge100\), below
\(0.056\) for \(n\ge500\), and below \(0.030\) for \(n\ge1000\).  These
are `experiment` results only.  In particular, they are not extrapolated to
(3) or (4).

## 7. Literature record

Sources checked on **2026-08-12 UTC**:

| source | exact use | source pin |
|---|---|---|
| [Beukers, *A rational approach to pi*, NAW 5/1 (2000), 372--379](https://www.nieuwarchief.nl/serie5/pdf/naw5-2000-01-4-372.pdf) | Defines reduced quality, gives the integral family and Gauss convergents, and prints the unsupported \(0.9058\ldots\) limit | PDF SHA-256 `7826ef90d8f0668a0952b0eed93887ada962d8e4fef2547193a8806d61985f6b` |
| [Ekhad--Zeilberger, *Searching for Apéry-Style Miracles*, arXiv:1405.4445v1](https://arxiv.org/abs/1405.4445v1) | Prints the \(k=0\) denominator-clearing value \(0.79119792\ldots\); its general automation discussion explicitly distinguishes reduced denominators and denominator multipliers | PDF SHA-256 `4b74fc949a5900a257a0badbe7d5519c563195f8c28c0c8159617b733b1b2ab8` |
| [Wang, *A Family of Continued Fraction Identities for Arctangent Values*, arXiv:2601.11892v3](https://arxiv.org/abs/2601.11892v3) | Gauss arctangent continued fraction and the geometric error ratio, agreeing with (19) | PDF SHA-256 `26013cf9ef1595031a41cb4b67d7e7d393ae9dba33f1f0b833aafc2b1d508dc9` |

The bounded search used combinations of *Gauss arctangent continued fraction
gcd*, *reduced denominator Padé approximants*, *arctangent integral
denominator asymptotic*, and the two printed decimals.  No primary source was
found that proves a subexponential bound for \(E_n\), the weaker threshold
(4), or an actual limit for the reduced qualities \(M_n\).  Beukers' printed
\(0.9058\ldots\) is nearly the exact depth-25 value and conflicts with later
exact checkpoints; it is not retained as an asymptotic premise.

## Bottom line

The analytic part of the Gauss--Lambert route is completely explicit.  A
canonical common divisor gives the rigorous quality floor
\(0.7911979206687\ldots\), correcting the direction of the earlier
denominator argument.  The actual asymptotic reduces exactly to the
exceptional gcd estimate (3), while the fixed-denominator application needs
only the still-unproved threshold (4).  Congruence (35) exhibits the genuine
shifted-prime obstruction.  This is meaningful route clarification, not a
fixed return or a proof that every finite decimal word occurs in pi.
