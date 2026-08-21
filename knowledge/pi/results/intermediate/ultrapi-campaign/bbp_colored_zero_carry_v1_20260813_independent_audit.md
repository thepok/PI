# Independent audit: colored zero-carry V1 criterion

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Audited frozen artifacts:

- [bbp_colored_zero_carry_v1_20260813.md](bbp_colored_zero_carry_v1_20260813.md),
  SHA-256
  `159ff0d1c94d9fb145790e0ca4f11db571d0af211ef2c588b094201122ff279a`;
- [bbp_colored_zero_carry_v1_20260813_check.py](bbp_colored_zero_carry_v1_20260813_check.py),
  SHA-256
  `7fbce9df0a4a92831ce7cadc5c0343546be71dd771331f7b5f7270fd4150d916`.

Independent replay:

- [bbp_colored_zero_carry_v1_20260813_independent_check.py](bbp_colored_zero_carry_v1_20260813_independent_check.py),
  SHA-256
  `46c3b807872b7e483c05e1eabe9c42bb7b4307abf2ff5022b6e4f9e51ed75433`.

## Verdict

**PASS, with two nonfatal completeness notes and no requested correction.**

The exact equivalence rederives with all quantifiers and both boundary colors:
decimal-disjunctivity is equivalent to arbitrarily late, arbitrarily long
zero-carry blocks in every split color, every residue color, or merely every
interior color.  The fixed-period eventual BBP transfer is valid.  The common
rational phase, split-color recurrence, fixed-modulus collapse, and sparse
uncolored counterexample are also exact.

Two implicit one-line details are worth recording:

1. In the irrationality-measure transfer, the displayed rational
   $(2m+1)/(2q_P10^n)$ need not be in lowest terms.  If a reduced-denominator
   formulation is used, its odd numerator cannot cancel the factor
   $2^{n+1}$, so the reduced denominator still tends to infinity; its
   irrationality lower bound is at least the one written with the unreduced
   denominator.  Thus the onset is legitimate and uniform in $m$.
2. The factorial-sparse decimal is irrational because it has infinitely many
   1s separated by unbounded zero gaps.  An eventually periodic decimal with
   infinitely many 1s has bounded gaps between them.  This supplies the
   routine step behind the report's assertion.

Neither point changes a formula or conclusion.  The exact derivations retain
the label `proof sketch`; bounded checks retain the label `experiment`; and
the inherited dated source work retains the label `literature-checked`.
Nothing in these artifacts is `machine-checked`, a `candidate resolution`, or
a `verified resolution`.  The colored condition is not established for pi,
and canonical V1 remains a `conjecture`.

## 1. Zero carries and split colors

Let $x$ be irrational, fix $P\geq1$, put $q=10^P-1$, and define

\[
 z_n=\left\lfloor q10^nx+\frac12\right\rfloor,
 \qquad e_n=q10^nx-z_n,
 \qquad \gamma_n=z_{n+1}-10z_n.
\]

Irrationality excludes every half-integer boundary, so
$-1/2<e_n<1/2$ and

\[
 e_{n+1}=10e_n-\gamma_n.                              \tag{A1}
\]

For every $H\geq1$,

\[
 \gamma_n=\cdots=\gamma_{n+H-1}=0
 \quad\Longleftrightarrow\quad
 |e_n|<{1\over2\,10^H}.                              \tag{A2}
\]

The forward implication follows from $e_{n+H}=10^He_n$.  Conversely, the
strict bound keeps $10^te_n$ inside the nearest-integer cell around
$10^tz_n$ for every $0\leq t\leq H$.  Hence
$z_{n+t}=10^tz_n$ and all $H$ displayed carries vanish.  The endpoint $t=H$
is why the denominator in (A2) is $10^H$, not $10^{H-1}$.

Write

\[
 10^nx=I_n+y_n,\qquad I_n\in\mathbb Z,\qquad0<y_n<1,
\]

and define the split color

\[
 c_{n,P}=\left\lfloor qy_n+\frac12\right\rfloor
 \in\{0,\ldots,q\}.                                  \tag{A3}
\]

Separating the integer part gives exactly

\[
 z_n=qI_n+c_{n,P},\qquad e_n=qy_n-c_{n,P},\qquad
 z_n\bmod q=c_{n,P}\bmod q.                          \tag{A4}
\]

For an interior residue $1\leq k\leq q-1$, the congruence in (A4) forces
the unique split color $c_{n,P}=k$.  Therefore

\[
 \begin{split}
 &z_n\equiv k\pmod q,\qquad
 \gamma_n=\cdots=\gamma_{n+H-1}=0\\
 &\hspace{25mm}\Longleftrightarrow
 \left|y_n-{k\over q}\right|<{1\over2q10^H}.         \tag{A5}
 \end{split}
\]

Residue zero has exactly the two one-sided realizations

\[
 c_{n,P}=0:\quad0<y_n<{1\over2q10^H},
 \qquad
 c_{n,P}=q:\quad0<1-y_n<{1\over2q10^H}.              \tag{A6}
\]

Thus ordinary residue zero genuinely forgets whether the orbit approaches
the all-zero or all-nine endpoint.  No other residue is merged.

## 2. Periodic cylinders and the exact V1 equivalence

For $1\leq k\leq q-1$, let $k_t$ be the representative in
$\{1,\ldots,q-1\}$ of $10^tk\pmod q$.  Since $10$ is a unit modulo $q$,
every $k_t$ remains interior and $k_P=k$.  Euclidean division gives

\[
 d_t={10k_t-k_{t+1}\over q}\in\{0,\ldots,9\}.        \tag{A7}
\]

These are precisely the repeated digits of the $P$-digit, leading-zero-padded
word for $k$:

\[
 {k\over10^P-1}=0.\overline{\operatorname{digits}_P(k)}.
\]

There is no terminating-expansion ambiguity because the reduced denominator
is greater than one and coprime to 10.

More precisely, write

\[
 10^Hk=Aq+k_H,qquad1\leq k_H\leq q-1.
\]

The point $k/q$ lies in its length-$H$ decimal cylinder with exact left and
right margins

\[
 {k_H\over q10^H},qquad {q-k_H\over q10^H}.          \tag{A8}
\]

Both are at least $1/(q10^H)$, twice the radius in (A5).  Consequently every
visit in (A5) begins with the first $H$ digits of the periodic word.  The two
visits in (A6) begin with $H$ zeroes or $H$ nines, respectively.

Now let:

- $\mathcal C_{\rm split}$ quantify over every exact color
  $c\in\{0,\ldots,q\}$;
- $\mathcal C_{\rm res}$ quantify over every residue
  $k\in\{0,\ldots,q-1\}$; and
- $\mathcal C_{\rm int}$ quantify only over
  $1\leq k\leq q-1$.

In each case the remaining quantifiers are

\[
 \forall P\geq1\ \forall H\geq1\ \forall N\geq0\
 \exists n\geq N,                                    \tag{A9}
\]

with the selected color and $H$ consecutive zero carries at $n$.

If $x$ is decimal-disjunctive, every word occurs arbitrarily late: an
occurrence of $0^Nw$ contains an occurrence of $w$ beginning at an index at
least $N$.  For an interior color $c$, request the first
$L=H+P+1$ digits of $c/q$.  A point in the same length-$L$ cylinder differs
from $c/q$ by less than $10^{-L}$, and

\[
 10^{-L}<{1\over2q10^H}                               \tag{A10}
\]

because $q<10^P$.  Equations (A2)--(A5) give the requested colored zero
block.  Requesting $L$ zeroes or $L$ nines gives the two boundary colors by
(A6).  Hence decimal-disjunctivity implies $\mathcal C_{\rm split}$, which
implies $\mathcal C_{\rm res}$, which implies $\mathcal C_{\rm int}$.

Conversely, take any nonempty word $w$ of length $m$ and fixed-width value
$a\in\{0,\ldots,10^m-1\}$.  Put $P=m+1$ and

\[
 d=\begin{cases}1,&a=0,\\0,&a>0,\end{cases}
 \qquad k=10a+d.                                      \tag{A11}
\]

Then $1\leq k\leq10^P-2=q-1$, including the leading-zero and all-nine
extremes.  Its padded $P$-digit word is $w$ followed by $d$.  Apply
$\mathcal C_{\rm int}$ with $H=P$.  Since $k_P=k$, the two margins in (A8)
are

\[
 {k\over q10^P},\qquad {q-k\over q10^P},
\]

both strictly larger than the radius $1/(2q10^P)$.  Thus $y_n$ begins with
$w$.  The empty word is vacuous.  This proves the exact chain

\[
 \boxed{
 x\text{ decimal-disjunctive}
 \iff\mathcal C_{\rm split}(x)
 \iff\mathcal C_{\rm res}(x)
 \iff\mathcal C_{\rm int}(x).}                      \tag{A12}
\]

The onset quantifier in (A9) is essential.  The proof preserves it in both
directions; no finite occurrence or bounded computation is substituted for
arbitrarily late occurrences.

## 3. Eventual sevenfold-BBP transfer

For $x=\pi$, the frozen report uses

\[
 \widehat z_{n,P}
 =\left\lfloor q_P10^nB_{7n}+\frac12\right\rfloor,
 \qquad
 \widehat\gamma_{n,P}
 =\widehat z_{n+1,P}-10\widehat z_{n,P}.              \tag{A13}
\]

The inherited irrationality-measure input $\mu(\pi)<8$ supplies, for fixed
$P$ and every nearest-integer boundary,

\[
 \left|q_P10^n\pi-\left(m+\frac12\right)\right|
 >{1\over2^8q_P^7 10^{7n}}                           \tag{A14}
\]

after an onset.  To make the denominator convention explicit, reducing
$(2m+1)/(2q_P10^n)$ cannot cancel its factor $2^{n+1}$ because $2m+1$ is odd.
The reduced denominator therefore tends to infinity.  If it is $Q'\leq
2q_P10^n$, then $(Q')^{-8}\geq(2q_P10^n)^{-8}$, so (A14) follows under either
the reduced or unreduced convention.

The positive BBP tail gives

\[
 0<q_P10^n(\pi-B_{7n})
 \leq {q_P10^n16^{-7n}\over15(7n+1)^2}.              \tag{A15}
\]

The ratio of (A15) to (A14) is at most

\[
 {2^8q_P^8\over15(7n+1)^2}
 \left({10^8\over16^7}\right)^n\longrightarrow0,    \tag{A16}
\]

since $10^8<16^7$.  Thus the segment between the rational shadow and the true
phase eventually crosses no nearest-integer boundary, uniformly over the
boundary index $m$.  For an onset $n_0(P)$,

\[
 \widehat z_{n,P}=z_{n,P},\qquad
 \widehat\gamma_{n,P}=\gamma_{n,P}\quad(n\geq n_0(P)). \tag{A17}
\]

The colored condition fixes $P$ before choosing $n$.  Replacing its requested
onset $N$ by $\max(N,n_0(P))$ places the start and every later transition of
the length-$H$ block beyond (A17).  Conversely, eventual equality transfers a
late rational block back to the true row in the same way.  Hence the
sevenfold-BBP statement in the report is exactly equivalent to V1; it is not
an assertion that either side holds.

## 4. The common rational phase and color recurrence

Use the exact raw BBP integers

\[
 B_{7n}={A_{7n}\over16^{7n}L_{7n}},\quad
 D_n=2^{27n}L_{7n},\quad
 R_n={L_{7n+7}\over L_{7n}},\quad
 \Lambda_n=2^{27}R_n,
\]

and

\[
 H_n=A_{7n+7}-16^7R_nA_{7n}.
\]

After removing the repunit multiplier, set

\[
 V_n=5^nA_{7n}=a_nD_n+r_n,qquad0\leq r_n<D_n,
 \qquad K_n=5^{n+1}H_n.                              \tag{A18}
\]

Then

\[
 {V_n\over D_n}=10^nB_{7n},qquad
 V_{n+1}=10\Lambda_nV_n+K_n,qquad
 D_{n+1}=\Lambda_nD_n.                               \tag{A19}
\]

Euclidean division of $10\Lambda_nr_n+K_n$ by $D_{n+1}$ gives

\[
 \begin{aligned}
 b_n&=\left\lfloor{10\Lambda_nr_n+K_n\over D_{n+1}}\right\rfloor,\\
 r_{n+1}&=10\Lambda_nr_n+K_n-b_nD_{n+1},\\
 a_{n+1}&=10a_n+b_n.
 \end{aligned}                                       \tag{A20}
\]

Thus $r_n/D_n$ is one exact $P$-independent rational state.  Its period-$P$
split color is

\[
 \widehat c_{n,P}
 =\left\lfloor {q_Pr_n\over D_n}+\frac12\right\rfloor
 \in\{0,\ldots,q_P\}.                               \tag{A21}
\]

Since $q_PV_n/D_n=q_Pa_n+q_Pr_n/D_n$, nearest-integer translation yields

\[
 \widehat z_{n,P}=q_Pa_n+\widehat c_{n,P},
 \qquad
 \widehat z_{n,P}\bmod q_P=\widehat c_{n,P}\bmod q_P. \tag{A22}
\]

Substituting (A20) at consecutive depths gives

\[
 \boxed{
 \widehat\gamma_{n,P}
 =q_Pb_n+\widehat c_{n+1,P}-10\widehat c_{n,P}.}      \tag{A23}
\]

Hence a zero carry is equivalent to
$q_Pb_n+\widehat c_{n+1,P}=10\widehat c_{n,P}$.  If a zero block starts at
an interior color $k$, reduction modulo $q_P$ gives

\[
 \widehat c_{n+t,P}\equiv10^tk\pmod {q_P},
 \qquad
 b_{n+t}={10\widehat c_{n+t,P}-\widehat c_{n+t+1,P}\over q_P}. \tag{A24}
\]

The right side is the periodic digit in (A7).  This verifies the report's
common-state formulation without assuming distribution of $r_n/D_n$.

## 5. Fixed-modulus collapse is exact

Let $q=10^P-1$ and $j=(q-1)/2$.  The coefficient denominator

\[
 d_j=(2j+1)(4j+3)(8j+1)(8j+5)
\]

contains $2j+1=q$.  Therefore

\[
 n\geq\left\lceil{q-1\over14}\right\rceil
 \quad\Longrightarrow\quad
 q\mid L_{7n}\mid D_n.                               \tag{A25}
\]

For

\[
 S_{n,P}=q_PV_n-D_n\widehat z_{n,P},
\]

one has $q_P\mid S_{n,P}$ after this coarse onset.  The formally true
congruence

\[
 D_n\widehat z_{n,P}\equiv-S_{n,P}\pmod {q_P}
\]

then reduces to $0\equiv0$ for every color.  Passing to modulus $q_PD_n$
retains the color only through

\[
 q_PV_n-S_{n,P}-D_nk\equiv0\pmod {q_PD_n}
 \quad\Longleftrightarrow\quad
 \widehat z_{n,P}\equiv k\pmod {q_P},                \tag{A26}
\]

which is just $D_n(\widehat z_{n,P}-k)$ and hence tautological.  The color is
the Archimedean cell selected by $r_n/D_n$, not a residue of $r_n$ modulo a
fixed $q_P$.

The independent replay supplies a new bounded illustration at $P=5$:

\[
 r_{119}\equiv r_{158}\equiv40620\pmod {99999},
\]

but the corresponding residue colors are $70938$ and $2841$.  This is an
`experiment`, not an asymptotic assertion.

## 6. The sparse uncolored counterexample

Consider

\[
 \xi=\sum_{j=2}^{\infty}10^{-j!}.
\]

Its nonterminating decimal expansion has 1s exactly at factorial positions
and zeroes elsewhere.  It is not eventually periodic: it has infinitely many
1s but their intervening zero gaps are unbounded.  Hence $\xi$ is irrational.
It is not decimal-disjunctive because digit 2 never occurs.

Fix arbitrary $P,H,N$, put $q=10^P-1$, and choose $j$ so that
$n=j!\geq N$ and $G=(j+1)!-j!$ satisfies

\[
 q{10\over9}10^{-G}<{1\over2\,10^H}.                 \tag{A27}
\]

Every term through $j!$ becomes integral after multiplication by $10^n$.
The later exponents are distinct integers beginning at $G$, so

\[
 0<\{10^n\xi\}
 =\sum_{\ell>j}10^{j!-\ell!}
 \leq\sum_{r=G}^{\infty}10^{-r}
 ={10\over9}10^{-G}.                                 \tag{A28}
\]

Equations (A2), (A3), and (A27)--(A28) give an $H$-zero block of split color
zero.  Since factorial gaps tend to infinity, this works for every
$P,H,N$.  Thus arbitrarily late, arbitrarily long **uncolored** zero blocks
for every period do not imply V1.  The all-residue quantifier cannot be
dropped.

## 7. Independent exact replay

The independent checker imports no primary code and first reruns the pinned
primary checker.  It then uses exact integers and `Fraction` to cover a
deliberately different finite family:

- 14,021 nonboundary rational-grid checks of the iff in (A2), for
  $1\leq H\leq7$;
- all 99,998 interior colors at the new exhaustive period $P=5$, including
  digit emission and three cylinder lengths per color;
- all 100,000 five-digit words under the append-one-digit reduction into
  period $P=6$;
- a direct-fraction reconstruction of the common BBP phase through depth 360,
  with 360 phase transitions and 720 colored transitions for the new periods
  $P=5,6$;
- the new $P=5$ fixed-residue collision above, and absorption witnesses for
  $P=5,6,7$;
- exact tail-to-boundary ratio checks for the sevenfold transfer at $P=5,6$,
  including the retained dyadic factor after rational reduction;
- a certified lower-boundary residue-zero block at positions 854--855 of the
  pinned pi prefix, with split colors $(0,0,0)$ at states 854--856, complementing
  the primary checker's upper-boundary color-9 block; and
- three new factorial-gap samples at periods $P=3,5,6$.

Replay from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_independent_check.py
```

The retained result is `status: PASS`, with
`asserts_colored_condition_for_pi: false` and `asserts_v1: false`.  Every
finite row has label `experiment`.

## Coordination record

This audit registered the descendant-area watch
`watch:ultrapi:colored-zero-carry-v1-independent-audit-20260813` on
`local:pi-digits` for agent `codex-ultrapi-colored-zero-carry-v1-audit`.
The initial poll was empty at cursor 56,925.  The final poll delivered the
unrelated rational-phase-separator events 56,930--56,931; the last processed
event, 56,931, was acknowledged.  Those observation events were treated only
as coordination signals and were not imported as evidence here.

## Claim boundary and handoff

The report supplies an exact `proof sketch` reformulation of V1, not a proof
of V1.  Its useful sharpening is that the missing property is fully colored:
one common rational BBP phase must enter every repunit torsion cell with
arbitrarily high accuracy at arbitrarily late depths.  Long visits to the
zero cell alone are insufficient, the residue-zero endpoint needs a split if
literal periodic words are discussed, and fixed moduli are eventually
absorbed by the raw denominator.

No theorem here proves the required all-color recurrence for pi.  Canonical
V1 remains a `conjecture`.
