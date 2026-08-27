# Gauss--Lambert exceptional gcd: a large-prime zero-set reduction

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

The requested estimate

\[
 \log E_n=o(n)                                                     \tag{1}
\]

was **not** proved, and neither was the weaker transfer-killing bound

\[
 \limsup_{n\to\infty}{\log E_n\over n}
 <0.4652000032604297\ldots .                                      \tag{2}
\]

Canonical V1 remains a `conjecture`.

There is nevertheless a sharp arithmetic reduction.  For every \(n\ge1\),
write

\[
 U_n={Q_n\over n!},\qquad V_n={P_n\over n!},                       \tag{3}
\]

for the normalized Gauss--Lambert continuants, and let

\[
 E_n={\gcd(4P_n,Q_n)\over
  2^{\lfloor n/2\rfloor}\operatorname{odd}
       (n!/\operatorname{lcm}(1,\ldots,n))}.                       \tag{4}
\]

For every integer \(n\ge2\) and every odd prime \(\ell\), its exceptional
exponent satisfies the all-depth estimate

\[
 v_\ell(E_n)\le
 \lfloor\log_\ell n\rfloor+
 \lfloor\log_\ell(n-1)\rfloor-v_\ell(n).                         \tag{5}
\]

Consequently all odd primes \(\ell\le\sqrt n\) contribute only
\(O(\sqrt n\log n)=o(n)\) to \(\log E_n\).  Every possible linear
odd-prime contribution is therefore carried by primes
\(\sqrt n<\ell<n\), each with exponent at most two.

For such a prime, write

\[
                         n=a\ell+s,qquad 0\le s<\ell.             \tag{6}
\]

Then \(1\le a<\ell\), and there is an exact criterion

\[
 \boxed{\quad v_\ell(E_n)\ge1
       \quad\Longleftrightarrow\quad
       U_sV_a\equiv0\pmod\ell .\quad}                             \tag{7}
\]

Here \(U_s\) and \(V_a\) are \(\ell\)-integral because
\(s,a<\ell\).  Thus the desired odd-part estimate is equivalent to a
weighted, varying-prime zero-density statement for two explicit earlier
coefficients.  Fixed-prime automaticity does not supply that statement.

The derivation of (5)--(7) below is a `proof sketch`; it is not yet a Lean
formalization.  The bounded source search is `literature-checked` as of the
audit date.  The companion exact checker is an `experiment`.  Nothing in
this note is a `machine-checked`, `candidate resolution`, or
`verified resolution` of V1.

## 1. Exact setup and ambiguous quantifiers

The integer continuants are

\[
 P_0=0,\ P_1=1,\qquad Q_0=Q_1=1,
\]

and, for \(n\ge2\),

\[
 X_n=(2n-1)X_{n-1}+(n-1)^2X_{n-2}.                                \tag{8}
\]

The words “upper bound on \(E_n\)” can mean three different things, which
must not be conflated:

1. a finite checked bound over a specified range of depths;
2. an all-depth estimate with a nonzero exponential constant;
3. the asymptotic estimate (1), or at least the strict constant (2).

Only the first is computational.  Equations (5)--(7) are all-depth
arithmetic reductions, but they do not imply (1) or (2).

For an odd prime \(\ell\) and an integer \(n\ge1\), put

\[
 r_\ell(n)=\lfloor\log_\ell n\rfloor,
\]

so that \(v_\ell(\operatorname{lcm}(1,\ldots,n))=r_\ell(n)\).
All asymptotics in this note are over every integer \(n\to\infty\), not a
selected subsequence.

## 2. Normalization and the determinant bound

The exponential generating functions from the preceding denominator audit
give

\[
 F(x)=\sum_{n\ge0}U_nx^n=(1-2x-x^2)^{-1/2},                       \tag{9}
\]

and

\[
 V_n=\sum_{i+j=n-1}{U_iU_j\over j+1}\qquad(n\ge1).              \tag{10}
\]

The binomial form

\[
 U_n=\sum_{0\le k\le n/2}
      {1\over2^k}{n\choose2k}{2k\choose k}                      \tag{11}
\]

shows that \(U_n\) is integral at every odd prime.  Formula (10) shows

\[
 v_\ell(V_n)\ge-r_\ell(n)\qquad(n\ge1),                        \tag{12}
\]

because no denominator \(j+1\le n\) contains more than
\(r_\ell(n)\) copies of \(\ell\).

Let \(g_n=\gcd(4P_n,Q_n)\).  Since \(4\) is an \(\ell\)-adic unit,
normalizing the two arguments of the gcd gives the exact identity

\[
 v_\ell(E_n)=r_\ell(n)+
       \min\{v_\ell(U_n),v_\ell(V_n)\}\qquad(n\ge1).            \tag{13}
\]

The continuant determinant becomes especially simple after division by
\(n!(n-1)!\):

\[
 V_nU_{n-1}-V_{n-1}U_n={(-1)^{n-1}\over n}\qquad(n\ge1).       \tag{14}
\]

Set

\[
 m=\min\{v_\ell(U_n),v_\ell(V_n)\},\qquad
 r'=r_\ell(n-1).
\]

The first term on the left of (14) has valuation at least \(m\), while
the second has valuation at least \(m-r'\), by (11)--(12).  Therefore

\[
 -v_\ell(n)=v_\ell(1/n)\ge m-r'.                                \tag{15}
\]

Substitution in (13) proves (5).

Two useful consequences are immediate:

- if \(\ell>n\), then \(\ell\nmid E_n\); the case \(\ell=n\) also has
  exceptional exponent zero;
- if \(\sqrt n<\ell<n\), then \(r_\ell(n)=r_\ell(n-1)=1\), so
  \(v_\ell(E_n)\le2\).

For the remaining odd primes, the crude count of integers up to \(\sqrt n\)
already gives

\[
 \begin{split}
 \sum_{3\le\ell\le\sqrt n}v_\ell(E_n)\log\ell
 &\le2\sum_{3\le\ell\le\sqrt n}
          \lfloor\log_\ell n\rfloor\log\ell\\
 &\le2\sqrt n\log n=o(n).                                     \tag{16}
 \end{split}
\]

No prime number theorem is needed for (16).

## 3. A Lucas product for the normalized denominator

Let

\[
 D(x)=1-2x-x^2.
\]

In \(\mathbb F_\ell[[x]]\), Frobenius gives
\(D(x)^\ell=D(x^\ell)\).  Both sides below have constant coefficient one
and square to \(D(x)^{-1}\), hence

\[
 F(x)=D(x)^{(\ell-1)/2}F(x^\ell)\pmod\ell.                       \tag{17}
\]

The polynomial \(D(x)^{(\ell-1)/2}\) has degree \(\ell-1\).  Comparing
coefficients below degree \(\ell\), then comparing the general base-
\(\ell\) digit, gives

\[
 U_{c\ell+d}\equiv U_cU_d\pmod\ell
       \qquad(c\ge0,\ 0\le d<\ell).                           \tag{18}
\]

Iterating (18) gives the full Lucas product over all base-\(\ell\) digits.
The last coefficient of the polynomial in (17) also gives

\[
 U_{\ell-1}\equiv(-1)^{(\ell-1)/2}\not\equiv0\pmod\ell.        \tag{19}
\]

This is stronger than the earlier one-shift congruence for the raw
continuants: it resolves every normalized denominator coefficient modulo a
fixed odd prime into its base-\(\ell\) digits.  The result itself is not new:
as recorded in Section 7, (18) is a specialization of Noe's 2006 generalized
central-trinomial Lucas congruence, and (19) is also covered by his scaled
Holt congruence.  Equations (17)--(19) are a rediscovered direct derivation
for this particular sequence.

## 4. Exact criterion for every prime above \(\sqrt n\)

Suppose \(\sqrt n<\ell<n\), and use (6).  Formula (10) implies

\[
 \ell V_n=\sum_{i+j=n-1}{\ell U_iU_j\over j+1}.                  \tag{20}
\]

Modulo \(\ell\), every summand whose denominator is an \(\ell\)-adic unit
vanishes.  The surviving indices are exactly

\[
 j=c\ell-1,\qquad i=(a-c)\ell+s,qquad 1\le c\le a.             \tag{21}
\]

Because \(a<\ell\), equations (18)--(19) turn (20) into

\[
 \begin{split}
 \ell V_n
 &\equiv U_sU_{\ell-1}
       \sum_{c=1}^a{U_{a-c}U_{c-1}\over c}\\
 &\equiv U_sU_{\ell-1}V_a\pmod\ell.                            \tag{22}
 \end{split}
\]

Here \(V_n\) has valuation at least \(-1\), so \(\ell V_n\) has a
well-defined reduction modulo \(\ell\).  From (13), with
\(r_\ell(n)=1\) and \(v_\ell(U_n)\ge0\),

\[
 v_\ell(E_n)\ge1
 \quad\Longleftrightarrow\quad v_\ell(V_n)\ge0
 \quad\Longleftrightarrow\quad \ell V_n\equiv0\pmod\ell.       \tag{23}
\]

Combining (19), (22), and (23) proves (7).

There are two genuinely different sources of exceptional primes:

\[
 \ell\mid U_s\quad\text{or}\quad \ell\mid V_a.                \tag{24}
\]

Since \(s,a<\ell\), these can be rewritten without rational denominators as

\[
 \ell\mid Q_s\quad\text{or}\quad \ell\mid P_a.                \tag{25}
\]

The alternatives in (25) cannot simply be discarded as rare edge cases.

### 4.1 Earlier-denominator mechanism

If \(0\le s<\ell\) and \(\ell\mid Q_s\), then \(\ell\) enters
\(E_{a\ell+s}\) for every \(1\le a<\ell\).  (The premise excludes
\(s=0,1\), since \(Q_0=Q_1=1\), so these depths do satisfy \(\ell<n\).)
The old case \(a=1\) is only the first member of this family.  Exponent two
can occur: the exact checker finds

\[
 v_{73}(E_{107})=2,qquad v_{131}(E_{166})=2,                    \tag{26}
\]

with \(107=73+34\) and \(166=131+35\).  Therefore replacing the exponent
bound two by one is false.

### 4.2 Earlier-numerator block mechanism

If \(1\le a<\ell\) and \(\ell\mid P_a\), then the same prime enters every
depth in the complete block

\[
                 a\ell\le n\le(a+1)\ell-1.                     \tag{27}
\]

Indeed \(n<\ell^2\) throughout the block and the \(V_a\) factor in (7)
vanishes independently of \(s\).  For example,

\[
 P_3=19,qquad V_3={19\over6},                                 \tag{28}
\]

so \(19\mid E_n\) for every \(57\le n\le75\).  This block mechanism is
invisible if one studies only primes \(\ell>n/2\).

### 4.3 The entire earlier-numerator branch is subexponential

The block mechanism is genuine locally, but its aggregate logarithmic weight
is \(o(n)\).  This useful fact follows from a cutoff argument and needs no
distribution theorem for prime divisors.

For a fixed \(a\), every eligible prime in the \(V_a\) branch lies in

\[
 {n\over a+1}<\ell\le {n\over a}                                \tag{28a}
\]

and divides the fixed nonzero integer \(P_a\).  Consequently the sum of
\(\log\ell\) over those primes is at most \(\log P_a\).  The recurrence
(8), or the positive coefficient formulas, gives the coarse uniform bound

\[
                         \log P_a=O(a\log(a+2)).                 \tag{28b}
\]

Set \(A=\lfloor n^{1/3}\rfloor\).  For \(a\le A\), summing (28b) gives

\[
 \sum_{a\le A}\ \sum_{\substack{\ell:\ \lfloor n/\ell\rfloor=a\\
                                  \ell\mid P_a}}
       \log\ell
       =O(A^2\log A)=o(n).                                     \tag{28c}
\]

For \(a>A\), forget the divisibility condition completely.  Equation (28a)
puts every remaining prime below \(n/A\), and hence

\[
 \sum_{a>A}\ \sum_{\substack{\ell:\ \lfloor n/\ell\rfloor=a\\
                               \ell\mid P_a}}
       \log\ell
 \le {n\over A}\log n=o(n).                                   \tag{28d}
\]

Thus, if \(\mathcal Z_n^{(V)}\) denotes the primes selected by
\(\ell\mid V_{\lfloor n/\ell\rfloor}\), then

\[
                  \sum_{\ell\in\mathcal Z_n^{(V)}}\log\ell=o(n).
                                                                    \tag{28e}
\]

This removes one of the two alternatives in (24) from the exponential
scale.  A proof of (1) can now focus on the earlier-denominator branch.

## 5. The exact remaining odd-prime problem

For every integer \(n\ge2\), define the large-prime zero set

\[
 \mathcal Z_n=\left\{\ell:\begin{array}{l}
       \ell\text{ odd prime},\ \sqrt n<\ell<n,\\
       U_{n\bmod\ell}V_{\lfloor n/\ell\rfloor}
                    \equiv0\pmod\ell
       \end{array}\right\}.                                    \tag{29}
\]

Equations (5), (7), and (16) give the exact decomposition

\[
 \log\operatorname{odd}(E_n)
 =\sum_{\ell\in\mathcal Z_n}v_\ell(E_n)\log\ell+o(n),          \tag{30}
\]

where every displayed exponent is one or two.  In particular, if

\[
 W_n=\sum_{\ell\in\mathcal Z_n}\log\ell,                        \tag{31}
\]

then

\[
 W_n+o(n)\le\log\operatorname{odd}(E_n)
           \le2W_n+o(n).                                      \tag{32}
\]

Thus there is an exact equivalence

\[
 \boxed{\quad
 \log\operatorname{odd}(E_n)=o(n)
 \quad\Longleftrightarrow\quad W_n=o(n).
 \quad}                                                        \tag{33}
\]

This isolates the missing odd-primary input without hiding it inside a gcd.
It is a diagonal, varying-characteristic zero problem: both the prime
\(\ell\) and the tested indices \(n\bmod\ell\) and
\(\lfloor n/\ell\rfloor\) vary with \(n\).

More sharply, define

\[
 \mathcal Z_n^{(U)}=
 \{\ell:\ell\text{ odd prime},\ \sqrt n<\ell<n,\
               \ \ell\mid U_{n\bmod\ell}\}.                    \tag{33a}
\]

The estimate (28e) shows that (33) is equivalent to

\[
       \sum_{\ell\in\mathcal Z_n^{(U)}}\log\ell=o(n).           \tag{33b}
\]

Lucas's product gives one more exact constraint: every prime in
\(\mathcal Z_n^{(U)}\) divides \(U_n\).  If \(N_n\) is the positive reduced
numerator of \(U_n\), their product therefore divides \(N_n\).  Formula
(11) gives a common denominator \(2^{\lfloor n/2\rfloor}\), while (9) gives
\(\log U_n=n\log(1+\sqrt2)+o(n)\).  Hence

\[
 \sum_{\ell\in\mathcal Z_n^{(U)}}\log\ell
 \le\log N_n
 \le\left(\log(1+\sqrt2)+\tfrac12\log2\right)n+o(n).           \tag{33c}
\]

The constant in (33c) is \(1.2279471772\ldots\), so this fixed-integer
product bound is still much too weak for (2), let alone (33b).  It is the
precise point at which a new large-prime-factor or resultant estimate is
needed.

A completely unconditional but inadequate consequence is

\[
 \log\operatorname{odd}(E_n)
 \le2\sum_{\ell<n}\log\ell+o(n)=2n+o(n),                       \tag{34}
\]

where the last equality uses the prime number theorem.  The constant two is
far above the required \(0.4652000032\ldots\), and (34) says nothing about
the power of two in \(E_n\).

To prove (1) by this route, it is now enough, and for the odd part necessary,
to establish uniform cancellation in (29).  Merely proving that the zero set
for each **fixed** prime is automatic does not control the aggregate in
(31).

## 6. The separate two-adic edge

The determinant estimate (5) used odd-prime integrality of \(U_n\), so it
does not cover \(\ell=2\).  The exact checker gives the following
`experiment` through \(n=10{,}000\):

\[
 v_2(Q_n)-\lfloor n/2\rfloor=
 \begin{cases}
 0,&n\equiv0,1\pmod4,\\
 1,&n\equiv2\pmod4,\\
 v_2(n+1),&n\equiv3\pmod4.
 \end{cases}                                                    \tag{35}
\]

Equation (35) is a `conjecture`, not an all-depth result in this audit.  If
proved, it would immediately imply

\[
 v_2(E_n)\le v_2(Q_n)-\lfloor n/2\rfloor=O(\log n),              \tag{36}
\]

because \(\gcd(4P_n,Q_n)\mid Q_n\).  It would therefore remove the
two-adic contribution from the exponential scale.  No argument below relies
on (35).

The full target (1) has consequently been separated into two explicit tasks:

1. prove the elementary-looking valuation formula (35), or any
   \(v_2(E_n)=o(n)\) substitute;
2. prove the varying-prime zero-density estimate \(W_n=o(n)\).

Task 2 remains the deeper obstruction even if (35) is granted.

## 7. Literature and mathlib search

Search date: **2026-08-12 UTC**.  The search was deliberately aimed at
primary sources and at the exact logical gap in (33).

- Tony D. Noe,
  [*On the Divisibility of Generalized Central Trinomial Coefficients*,
  J. Integer Sequences 9 (2006), Article 06.2.7](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf),
  proves the base-prime digit product in his equation (13).  For his
  parameters \((a,b,c)=(1,2,2)\), equation (2) gives
  \(T_n=2^nU_n\); Fermat's theorem therefore turns his (13) exactly into the
  iterated form of (18).  His equation (14), specialized at \(k=0\) and
  discriminant \(-4\), also gives (19); equivalently, in the common two-
  parameter notation this is \(T_n(2,2)=2^nU_n\), OEIS A006139.  Thus the
  Lucas result in Section 3 is explicitly classified as rediscovered, not
  novel.  The official PDF
  fetched on the search date has SHA-256
  `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c`.
- Eric Rowland and Reem Yassawi,
  [*Automatic congruences for diagonals of rational functions*](https://arxiv.org/abs/1310.8635),
  gives finite-automaton methods modulo \(p^\alpha\) and Lucas products for
  broad classes of diagonal sequences.  It supports the fixed-prime context
  of (17)--(18), but it does not provide a uniform estimate as the prime and
  coefficient index vary together as in (29).
- Boris Adamczewski and Jason P. Bell,
  [*On vanishing coefficients of algebraic power series over fields of
  positive characteristic*](https://arxiv.org/abs/1205.4091), proves that the
  zero set of an algebraic power series over a **fixed** positive-
  characteristic field is automatic.  Again, this is not a bound for the
  cross-prime sum (31).
- The local mathlib search found Lucas's theorem for binomial coefficients in
  `Mathlib/Data/Nat/Choose/Lucas.lean` and shifted Legendre polynomial
  infrastructure in `Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean`.
  The latter does not directly formalize the ordinary Legendre value at zero
  implicit in (11).  The search found no existing Padé-continuant or
  varying-prime zero-density theorem that closes (31).

Queries included variants of “generalized central trinomial Lucas
congruence,” “automatic congruences diagonals rational functions,”
“vanishing coefficients algebraic power series positive characteristic,”
“zeros modulo p algebraic power series,” and “p-adic valuation coefficients
\((1-2x-x^2)^{-1/2}\).”  No checked primary source was found that proves
(1), (2), (33)'s right-hand side, or the all-depth two-adic formula (35).
Absence from this bounded search is not a novelty claim.

## 8. Reproduction

Run

```bash
python work/ultrapi-resume/gauss_exceptional_gcd_upper_bound_check.py
```

The expected output is

```text
PASS: normalized determinant/exponent bound, Lucas product, and exact large-prime zero criterion on 84219 pairs (1197 exceptional), including exponent-two and V_a-block witnesses
EXPERIMENT: v_2(Q_n)-floor(n/2) follows the stated mod-4 pattern through n=10000; no all-n proof is claimed
```

The checker verifies exact rational determinants, (13), (5), sampled Lucas
digits from the independent binomial sum, (7) for every eligible pair with
\(n\le1000\), the exponent-two examples, and the complete \(V_3\) block.
Its last line is explicitly finite evidence only.

## 9. Handoff

The useful breakthrough is not an upper bound of the desired strength.  It is
the reduction of all odd-primary exponential growth to the inspectable set
\(\mathcal Z_n^{(U)}\), together with proofs that small primes and the whole
\(P_a\)-block branch are harmless and that large-prime exponents never exceed
two.  Any continuation should attack (33b) directly rather than returning to
analytic Padé error estimates.  Until (33b) and the two-adic edge are
controlled, this route does not prove a decimal-cylinder hit and must not be
reported as a solution of V1.
