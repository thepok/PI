# Hutton periodic orbit: an exponential period outside a linear shadow

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.  This note follows the fields of
[`problems/TEMPLATE.md`](../../problems/TEMPLATE.md) within the existing
problem record rather than creating a second problem statement.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained.  The
canonical V1 statement remains a `conjecture`.

The route does produce a sharp separator.  For the rational lower Hutton
truncations

\[
 H_K=8T_3(2K+2)+4T_7(2K+2),
 \qquad
 T_q(N)=\sum_{n=0}^{N-1}{(-1)^n\over(2n+1)q^{2n+1}},       \tag{1}
\]

the exact reduced denominator, decimal transient, post-transient modulus,
multiplicative order, and word-cylinder test are given below.  More strongly,
for every $K\ge1$, at least one of $H_{K-1},H_K$ has a three-primary
component forcing a decimal period

\[
 d\ \ge\ 3^{4K+3-\lfloor\log_3(16K+13)\rfloor-2}.         \tag{2}
\]

This is exponential in $K$.  In contrast, the adjacent exact Hutton bracket
can locate pi digits only through a scale

\[
 h_K\le (4K+5)\log_{10}3+\log_{10}{4K+5\over8}
      =1.90848\ldots K+O(\log K).                          \tag{3}
\]

A theorem saying that a word occurs *somewhere* in the full rational period
therefore gives an offset below an exponentially large $d$, not an offset
inside the linear shadow $h_K$.  Denominator and order data cannot repair
this: multiplying a reduced numerator by a power of 10 rotates the same
cycle, preserving the denominator, order, and full-cycle coverage while
moving the first occurrence.  The actual numerator would need a new
localized block-hitting theorem.

Equations (1)--(3), the exact orbit formula, and the separator construction
are `proof sketch`: complete elementary arguments are recorded but not
formalized in Lean.  The source statements are `literature-checked` as of the
date above.  The finite rational calculations are an `experiment`, replayed
exactly by the companion checker.  No item in this note is a candidate
resolution of V1.

## 1. Normalized target and the quantifiers this route would need

Write the nonterminating decimal expansion of pi as

\[
 \pi=3+\sum_{j\ge0}d_j(\pi)10^{-(j+1)},
 \qquad d_j(\pi)\in\{0,\ldots,9\}.
\]

The canonical statement is

\[
 \forall \ell\ge0\ \forall c\in\{0,\ldots,10^\ell-1\}\
 \exists j\ge0:\quad
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c.          \tag{V1}
\]

The integer $c$ is padded to length $\ell$, so leading zeroes are allowed;
$\ell=0$ is vacuous and occurrence is contiguous.

Three plausible readings of “the rational orbit contains every fixed word”
must not be conflated.

1. One fixed $H_K$ contains every finite word.  This is impossible: with
   preperiod $b_K$ and period $d_K$, its whole infinite expansion has at
   most $b_K+d_K$ distinct factors of any given length.  It therefore
   misses a word whenever $10^\ell>b_K+d_K$.  Its periodic part alone has
   at most $d_K$ cyclic factors.
2. For each $\ell$, sufficiently large $K$ have all $10^\ell$ words
   somewhere in their full periods.  Call this **global periodic coverage**.
   It is a meaningful finite-orbit conjecture, but it does not imply V1.
3. For every $\ell,c$, some $H_K$ has the word at a start $j$ for which
   the full rational bracket remains in the same decimal cylinder.  This is
   **localized transferable coverage**.  It does imply V1, but it is the
   missing assertion, not a consequence of the period.

The ambiguity is thus an order-of-quantifiers issue: global coverage gives an
offset $s_K<d_K$ *after* choosing $K$, while transfer needs that same
offset to satisfy a bound of size $O(K)$.

## 2. Literature and mathlib search

The search preceded the new denominator/order calculation.

- Borwein--Borwein--Galway, [*Finding and Excluding b-ary Machin-Type
  Individual Digit Formulae*](https://doi.org/10.4153/CJM-2004-041-2),
  printed equation (13), records
  
  \[
  \pi/4=2\arctan(1/3)+\arctan(1/7).
  \]
  
  The vendored PDF is
  `work/theory/pi-digits/library/t19/borwein-borwein-galway-2004-machin-exclusion.pdf`,
  SHA-256
  `51d47633a37a9d4b024ccabfd782fe0d0ade85f554a8a6fc3fe2773832ecc2cb`.
- The pinned mathlib checkout is commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`.  Its file
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean` contains
  `two_mul_arctan_inv_3_add_arctan_inv_7`; the file SHA-256 is
  `f2503a1e4710591b3dbadf5502e2dd14681b4f69c0498d1cb073ecd634c65238`.
  Searches for `orderOf`, `Nat.ModEq`, and decimal block
  predicates found general arithmetic ingredients, but no theorem asserting
  block coverage for these Hutton numerators.
- Lagarias, [*On the Normality of Arithmetical
  Constants*](https://arxiv.org/abs/math/0101055), Theorem 2.1, records both
  the digit-dense/orbit-dense equivalence and the eventual-periodicity
  characterization for rationals.  The vendored text SHA-256 is
  `d4dcb5c31735fa51bbe15f7bb5bdcaa7f2cb86582f09b08665c8ec91aa08a346`.
  It does not turn finite rational periodicity into digit-density.
- A bounded 2026-08-12 search of arXiv/AMS for `decimal repetend all blocks`,
  `powers modulo composite modulus discrepancy`, and `multiplicative
  subgroup interval` found general subgroup and short-character-sum work,
  including Chang's [*Short character sums for composite
  moduli*](https://arxiv.org/abs/1201.0299).  No located source supplied both
  (i) coverage for the actual reduced Hutton numerator/modulus and (ii) an
  occurrence before the approximation horizon.  Prime-field subgroup
  theorems cannot silently be substituted for this varying composite
  modulus.

This is a dated, bounded search, not a novelty claim.  The nearby local T79
report already warned that exact rational order does not itself provide a
special-numerator orbit estimate; the calculation below specializes and
sharpens that warning for the $3/7$ Hutton family.

## 3. Exact denominator, transient, order, and block criterion

Set

\[
 R=4K+3,\qquad
 \Lambda_R=\operatorname{lcm}\{1,3,5,\ldots,R\},\qquad
 D_K=3^R7^R\Lambda_R.                                    \tag{4}
\]

Define the integer

\[
 A_K=\sum_{\substack{1\le r\le R\\r\ {\mathrm{odd}}}}
 (-1)^{(r-1)/2}
 \left({8D_K\over r3^r}+{4D_K\over r7^r}\right).          \tag{5}
\]

Every quotient in (5) is integral, and direct collection of (1) gives

\[
 H_K={A_K\over D_K}={p_K\over q_K},\qquad
 g_K=\gcd(A_K,D_K),\quad p_K=A_K/g_K,\quad q_K=D_K/g_K.    \tag{6}
\]

Thus (6) is the exact reduced denominator formula, not merely a convenient
common denominator.  In particular $q_K$ is odd.  Put

\[
 b_K=v_5(q_K),\qquad m_K=q_K/5^{b_K}.                      \tag{7}
\]

Since the only factor 5 in $D_K$ comes from $\Lambda_R$,

\[
 0\le b_K\le v_5(\Lambda_R)=\lfloor\log_5R\rfloor,        \tag{8}
\]

and $\gcd(m_K,10)=1$.  After exactly $b_K$ decimal steps the reduced
state is

\[
 a_K\equiv2^{b_K}p_K\pmod {m_K},\qquad
 x_{K,s}={r_{K,s}\over m_K},\quad
 r_{K,s}\equiv a_K10^s\pmod {m_K},                        \tag{9}
\]

where $0\le r_{K,s}<m_K$.  Hence the exact post-transient period is

\[
 d_K=\operatorname{ord}_{m_K}(10).                        \tag{10}
\]

The residues in (9) are distinct for $0\le s<d_K$.  A padded length-
$\ell$ word encoded by $c<10^\ell$ starts at decimal position
$b_K+s$ exactly when

\[
 c\,m_K\le10^\ell r_{K,s}<(c+1)m_K.                      \tag{11}
\]

Equation (11), not the value of $d_K$ alone, is the residue-distribution
problem.  Since $m_K\mid10^{d_K}-1$, one always has the weak size bound

\[
 d_K\ge\lceil\log_{10}(m_K+1)\rceil.                     \tag{12}
\]

The prime-power orders are much sharper.  The lifting-the-exponent identity
gives

\[
 \operatorname{ord}_{3^e}(10)=
 \begin{cases}1,&e\le2,\\3^{e-2},&e\ge3,\end{cases}
 \qquad
 \operatorname{ord}_{7^f}(10)=6\,7^{f-1}\quad(f\ge1).     \tag{13}
\]

Therefore $d_K$ is divisible by the least common multiple of the applicable
orders in (13).  This proves separation and period size, not interval hits in
(11).

## 4. A new neighboring-denominator lower bound

The adjacent difference has an unexpectedly clean form.  For $K\ge1$ and
$R=4K+3$, the two newly added odd exponents are $R-2,R$, so exact
simplification gives

\[
 \begin{aligned}
 H_K-H_{K-1}
 &= {16(4R+1)\over R(R-2)3^R}
   +{8(24R+1)\over R(R-2)7^R}.                            \tag{14}
 \end{aligned}
\]

At the prime 3 the first summand is uniquely dominant.  Indeed
$24R+1\equiv1\pmod3$ and $v_3(4R+1)<R$, the latter following from
$3^R>4R+1$.  Thus

\[
 -v_3(H_K-H_{K-1})
 =E_{3,K}:=R+v_3(R)+v_3(R-2)-v_3(4R+1).                  \tag{15}
\]

At the prime 7 the second summand is uniquely dominant: $7^R>24R+1$
implies $v_7(24R+1)-R<0\le v_7(4R+1)$.  Hence

\[
 -v_7(H_K-H_{K-1})
 =E_{7,K}:=R+v_7(R)+v_7(R-2)-v_7(24R+1).                 \tag{16}
\]

The denominator of a difference of reduced rationals divides the least
common multiple of their denominators.  Equations (15)--(16) therefore imply
the exact pair bounds

\[
 \max\{v_3(q_{K-1}),v_3(q_K)\}\ge E_{3,K},\qquad
 \max\{v_7(q_{K-1}),v_7(q_K)\}\ge E_{7,K}.               \tag{17}
\]

Since $v_p(n)\le\lfloor\log_p n\rfloor$,

\[
 E_{3,K}\ge R-\lfloor\log_3(4R+1)\rfloor,\qquad
 E_{7,K}\ge R-\lfloor\log_7(24R+1)\rfloor.              \tag{18}
\]

Choose the member $J\in\{K-1,K\}$ realizing the first inequality in
(17).  Removing the 5-primary transient does not remove its 3-primary
factor.  Equations (13) and (18) give exactly (2).  Thus arbitrarily large
Hutton periods are not a heuristic: a neighboring member of every pair has
an exponentially large period.  Equations (14)--(18) do not assert that the
same member realizes both prime bounds, and no simultaneous claim is needed
for (2).

## 5. The approximation horizon is only linear

Let the adjacent odd Taylor truncation be

\[
 U_K=8T_3(2K+3)+4T_7(2K+3).
\]

Alternation, with positive Hutton coefficients, gives the exact bracket

\[
 H_K<\pi<U_K,\qquad
 W_K:=U_K-H_K
 ={8\over(4K+5)3^{4K+5}}+{4\over(4K+5)7^{4K+5}}.         \tag{19}
\]

Define the scale at which this bracket still has length below one after
decimal magnification:

\[
 h_K=\max\{j\ge0:10^jW_K<1\}.                            \tag{20}
\]

The first summand in (19) yields

\[
 h_K<\log_{10}{(4K+5)3^{4K+5}\over8},                    \tag{21}
\]

which is (3).  For a word $c<10^\ell$, an exact sufficient transfer
certificate at start $j$ is the existence of an integer $z$ such that

\[
 z+{c\over10^\ell}\le10^jH_K
 \quad\hbox{and}\quad
 10^jU_K<z+{c+1\over10^\ell}.                            \tag{22}
\]

Then the entire bracket, hence $10^j\pi$, lies in the desired decimal
cylinder.  A rational occurrence satisfying only (11) need not satisfy
(22): it may be near a cylinder boundary, and its cycle offset may be far
beyond $h_K$.  Indeed, fitting any length-$\ell$ cylinder already requires
$10^{j+\ell}W_K<1$, so (20) is a generous outer horizon rather than a
sufficient block certificate.

Combining (2) and (21), the available full period is exponential along a
neighboring subsequence, while the bracket horizon is linear.  Periodicity
therefore exposes mostly digits of $H_K$ that are not controlled digits of
pi.  Choosing $K$ “much larger than a target position” works only when the
position is chosen *before* $K$; global coverage chooses an unknown
position after $K$, with no $O(K)$ bound.

### Rotation separator

For any reduced post-transient state $a/m$, replacing $a$ by
$10^ta\pmod m$ cyclically rotates the same orbit.  It preserves $m$,
$\operatorname{ord}_m(10)$, and the multiset of cyclic words, but can move a
chosen occurrence by $t$ positions.  Consequently no argument using only
the denominator, order, or full-cycle word census can prove the localization
needed in (22).  A theorem must use the actual numerator $a_K$ and ordered
initial segment.

## 6. A quantifier-level separator independent of Hutton arithmetic

The localization gap is logically real, not merely a weakness of the current
estimates.  Consider

\[
 \beta=\sum_{n=2}^{\infty}10^{-n!}.                       \tag{23}
\]

Its decimal digits are 0 and 1 with unbounded gaps between the ones, so it is
irrational and omits the one-digit word 2.  Fix a precision $L$ and a word
length $\ell$.  Let $P_L=\lfloor10^L\beta\rfloor$, and choose a decimal de
Bruijn cycle $B_\ell$ of length $D=10^\ell$, interpreted as a $D$-digit
integer with leading zeroes allowed.  Define

\[
 r_{L,\ell}={P_L\over10^L}
       +{B_\ell\over10^L(10^D-1)}.                        \tag{24}
\]

Then

\[
 |r_{L,\ell}-\beta|<10^{-L},                              \tag{25}
\]

and the eventual decimal period of $r_{L,\ell}$ contains every length-
$\ell$ word.  The de Bruijn period cannot collapse to a shorter one, since
a cycle of shorter length has fewer than $10^\ell$ starting positions.
Thus an irrational number omitting 2 has arbitrarily accurate rational
shadows whose full periods cover every prescribed finite word length.

This separator does not reproduce the Hutton numerator or denominator.  Its
purpose is exact: even **arbitrarily accurate shadows plus global periodic
coverage at every word length** do not imply digit coverage for the limit.
Only a localized transfer statement such as (22) can do that.

## 7. Exact finite replay and falsification results

The companion checker is
[`hutton_periodic_orbit_check.py`](hutton_periodic_orbit_check.py), SHA-256
`c7d1484ccfa9df668e4fc00d26c2ebd790046d3025b31274cc3897655b3ff6e5`.
It uses only Python's standard library and exact integers/Fractions.  It verifies
(4)--(18) for $0\le K\le60$, exact orders and horizons for $0\le K\le8$,
and the block scans below.

For the first nine truncations it obtains:

| $K$ | bits of $q_K$ | $v_3(q_K)$ | $v_7(q_K)$ | $v_5(q_K)$ | $d_K=\operatorname{ord}_{m_K}(10)$ | $h_K$ |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 15 | 4 | 3 | 0 | 882 | 2 |
| 1 | 36 | 7 | 8 | 1 | 400241898 | 4 |
| 2 | 55 | 11 | 11 | 1 | 11119920652134 | 6 |
| 3 | 77 | 16 | 15 | 1 | 6487839865043017362 | 8 |
| 4 | 98 | 19 | 19 | 1 | 420587194931143686526374 | 10 |
| 5 | 120 | 23 | 23 | 1 | 899758400831441308292693160834 | 12 |
| 6 | 144 | 30 | 27 | 2 | 4724619665906687501107923982528243158 | 14 |
| 7 | 167 | 31 | 31 | 2 | 340314354535258700704803764461509354670740 | 16 |
| 8 | 187 | 35 | 36 | 2 | 463292731890601531602396586413671605640041301580 | 18 |

The complete $K=0$ cycle has 882 positions.  Its exact numbers of distinct
cyclic words of lengths 1, 2, 3, 4 are

\[
                         10,\quad100,\quad631,\quad882.    \tag{26}
\]

So the first Hutton orbit contains every two-digit word but misses 369 of the
1000 three-digit words.  This falsifies the naive assertion that Hutton's
denominator structure automatically makes each period universal.

For $1\le K\le8$, an exact scan of the first 150000 rational digits does
find all length-3 and length-4 words.  The first prefix lengths containing all
length-4 words are respectively

\[
 92461,\ 98103,\ 81030,\ 125672,\ 97982,\ 100440,\ 95831,\ 108134. \tag{27}
\]

They should be compared with the bracket horizons
$4,6,8,10,12,14,16,18$.  Thus every observed length-4 coverage certificate
lies far outside the part that these approximants rigorously transfer to pi.
This is an `experiment`, not an asymptotic theorem; its value is to falsify
the expected early-localization shortcut.

Run from the repository root:

```bash
python3 work/ultrapi-resume/hutton_periodic_orbit_check.py
```

The script prints `claim_status=experiment` and ends with
`all exact assertions passed`.

## 8. What would genuinely advance this route

Global periodic coverage, even if proved using character sums, is not the
missing bridge.  A useful new input must be one of the following, with the
actual Hutton numerator retained:

1. a uniform prefix discrepancy bound for
   $a_K,10a_K,\ldots,10^{C K}a_K\pmod {m_K}$ strong enough to hit every
   fixed decimal cylinder;
2. an exact coding theorem placing each word at an offset $s=O_\ell(K)$
   and away from both cylinder boundaries by more than $10^sW_K$; or
3. a different approximation whose proven shadow length reaches the orbit
   coverage scale.

Any of these would be materially stronger than multiplicative order.  None
was found in the cited search or proved here.  The current route therefore
ends at a `proof sketch` separator: **the Hutton periods are provably huge,
but the portion tied to pi is only linear and has no proved block census.**
