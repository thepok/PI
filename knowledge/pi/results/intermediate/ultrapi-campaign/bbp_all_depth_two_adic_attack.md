# BBP all-depth two-adic attack: a p-adic null identity closes the exact-anchor escape

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained.  Canonical V1 remains a `conjecture`.

This branch closes one concrete gap left by
[`fixed_multiplier_return_attack.md`](fixed_multiplier_return_attack.md).
For the standard BBP partial sum

\[
 B_N=\sum_{k=0}^{N}\frac1{16^k}
 \left(\frac4{8k+1}-\frac2{8k+4}
                 -\frac1{8k+5}-\frac1{8k+6}\right),
\tag{1}
\]

the earlier finite experiment suggested, but did not prove, that

\[
 \boxed{v_2(\operatorname{den}B_N)=4N-v_2(N+1)}
 \qquad(N\geq1).                                      \tag{2}
\]

Sections 2--4 give a self-contained p-adic `proof sketch` of (2).  Its new
ingredient is the exact two-adic null identity

\[
 \sum_{j\geq0}16^j
 \left(\frac1{8j+2}+\frac1{8j+3}
       +\frac2{8j+4}-\frac4{8j+7}\right)=0
 \quad\hbox{in }\mathbb Q_2.                           \tag{3}
\]

The identity is the reciprocal/reflected form of the BBP coefficient.  A
global two-adic logarithmic primitive evaluates to zero at both endpoints.
It implies (2) at **every** truncation depth, not just at even depths.

Consequently, for every fixed nonzero integer \(c\), all sufficiently large
depths and exponents can never satisfy the strongest rational synchronization

\[
                 (10^n-c)B_N\in\mathbb Z.               \tag{4}
\]

In particular, when \(c=16\), every \(N\geq2\) is excluded for every
\(n\geq5\).  This is a genuine method obstruction, not V1: it does not bound
the nonzero phase

\[
                 \|(10^n-16)B_N\|_{\mathbb T}.          \tag{5}
\]

The deductions in this note have status `proof sketch` and are not Lean
declarations.  The exact finite replay is an `experiment`.  The bounded
source audit is `literature-checked` as of the date above.  Nothing here is a
`candidate resolution`.

## 1. Exact target and quantifier audit

Write \(v_2(0)=+\infty\) and normalize \(v_2(2)=1\).  Let

\[
 K_{10}(\pi)=\overline{\{10^n\pi\bmod1:n\geq0\}}.
\]

The fixed-sixteen return is

\[
 16\pi\in K_{10}(\pi)
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0.   \tag{6}
\]

The Furstenberg bridge already audited in
[`furstenberg_bbp_bridge.md`](furstenberg_bbp_bridge.md) makes (6) equivalent
to V1.  Joint semigroup density only gives

\[
 \{10^m16^r\pi:m,r\geq0\}\ \hbox{dense in }\mathbb T,  \tag{7}
\]

where both exponents vary.  It does not fix \(r=0\), nor does it put the one
point \(16\pi\) in the decimal orbit closure.

For a reduced rational \(A=P/q\), the exact anchor

\[
                  (10^n-16)A\in\mathbb Z                \tag{8}
\]

is equivalent to \(q\mid10^n-16\).  Together with
\(|\pi-A|=o(10^{-n})\), it would imply (6).  Equation (2) rules out (8) for
deep BBP truncations; it does not rule out an approximate residue tending to
zero.

## 2. Reversal of the BBP coefficient

Put

\[
 a(X)=\frac4{8X+1}-\frac2{8X+4}
                 -\frac1{8X+5}-\frac1{8X+6}
     =\frac{120X^2+151X+47}
      {(2X+1)(4X+3)(8X+1)(8X+5)}.                       \tag{9}
\]

For every \(X\in\mathbb Z_2\), all four factors in the final denominator are
units.  Expanding their inverses around any residue class therefore shows
that \(a\) is a \(\mathbb Z_2\)-valued analytic function on
\(\mathbb Z_2\).  Reflection gives the exact identity

\[
 a(-1-j)=\frac1{8j+2}+\frac1{8j+3}
                 +\frac2{8j+4}-\frac4{8j+7}
 =\frac{120j^2+89j+16}
 {(2j+1)(4j+1)(8j+3)(8j+7)}.                            \tag{10}
\]

Although the split fractions in (10) have even denominators, their combined
denominator is odd.  Therefore

\[
                         F(X)=\sum_{j\geq0}16^j a(X-1-j)\tag{11}
\]

converges coefficientwise and uniformly on \(\mathbb Z_2\) to a
\(\mathbb Z_2\)-valued analytic function.  More explicitly, each
\(a(X-1-j)\) has a power-series expansion in \(\mathbb Z_2[[X]]\), and the
factor \(16^j\) sends every coefficient to zero two-adically, uniformly in
the coefficient index.

The decisive point is \(F(0)=0\), proved next.  This cancellation is why a
unique-minimum valuation argument at the final summand fails at odd depths.

## 3. The reflected coefficient is a two-adic null BBP series

Let

\[
 P(x)=x+x^2+2x^3-4x^6,
 \qquad g(x)=\frac{P(x)}{1-16x^8}.                       \tag{12}
\]

On the two-adic closed unit disc,

\[
 g(x)=\sum_{j\geq0}16^j
  (x^{8j+1}+x^{8j+2}+2x^{8j+3}-4x^{8j+6}).              \tag{13}
\]

Termwise formal integration from 0 to 1 is convergent block by block and is
exactly the left side of (3).  Indeed, after division by the four monomial
exponents, the four coefficient valuations in block \(j\) are respectively
\(4j-1,4j,4j-1,4j+2\), so they tend uniformly to \(+\infty\).  We now
evaluate the resulting primitive without assuming (3).

The rational factorizations

\[
\begin{aligned}
 P(x)&=-x(x-1)(2x^2+1)(2x^2+2x+1),\\
 1-16x^8
  &=-(2x^2-1)(2x^2+1)(2x^2-2x+1)(2x^2+2x+1)
\end{aligned}                                           \tag{14}
\]

give

\[
 g(x)=\frac{x(x-1)}{(2x^2-1)(2x^2-2x+1)}.               \tag{15}
\]

Work in \(\mathbb C_2\), choose \(i^2=-1\), and use

\[
                  \log(1+z)=\sum_{r\geq1}{(-1)^{r+1}z^r\over r}
                  \qquad(v_2(z)>0).                     \tag{16a}
\]

Every series below converges on \(x\in\mathbb Z_2\): \(2x^2\) is
two-adically small, \(x(x-1)\in2\mathbb Z_2\), and
\(v_2(1\pm i)=1/2\).  Define

\[
\begin{aligned}
 A(x)&=\frac1{2i}\bigl(
   \log(1+(i-1)x)-\log(1-(1+i)x)\bigr),\\
 G(x)&=-\frac18\log(1-2x^2)
       +\frac18\log(1+2x^2-2x)+\frac14 A(x).
\end{aligned}                                           \tag{16}
\]

The two factors in each logarithm lie in
\(1+\mathfrak m_{\mathbb C_2}\),
so logarithmic differentiation is legitimate throughout the disc.  Direct
differentiation gives

\[
 A'(x)=\frac1{2x^2-2x+1},
 \qquad G'(x)=g(x).                                     \tag{17}
\]

For completeness, the cancellation in (17) is

\[
\begin{aligned}
 A'(x)&={1\over2i}\left(
 {i-1\over1+(i-1)x}+{1+i\over1-(1+i)x}\right)
 ={1\over2x^2-2x+1},\\
 G'(x)&=-{x\over2(2x^2-1)}
       +{2x-1\over4(2x^2-2x+1)}
       +{1\over4(2x^2-2x+1)}\\
 &= {x(x-1)\over(2x^2-1)(2x^2-2x+1)}=g(x).
\end{aligned}                                           \tag{17a}
\]

At \(x=0\), every logarithm in (16) is zero.  At \(x=1\), the first two
logarithm arguments are \(-1\) and \(1\), while the arguments in \(A\) are
\(i\) and \(-i\).  The logarithm (16a) is a homomorphism on
\(1+\mathfrak m_{\mathbb C_2}\).  Since these arguments are roots of unity
of order dividing four, \(4\log\zeta=\log(\zeta^4)=0\), hence each logarithm
is zero.  Therefore

\[
       \int_0^1g(x)\,dx=G(1)-G(0)=0,                    \tag{18}
\]

where the integral denotes evaluation at 1 minus evaluation at 0 of the
global analytic primitive furnished by the uniformly convergent integrated
series (13); no path-integration assertion is being used.  Equations (10),
(13), and (18) prove (3), and therefore

\[
                             F(0)=0.                     \tag{19}
\]

No real value of pi enters (19).  Complexly, the corresponding logarithm
records an angular period; two-adically, the logarithm kills the relevant
roots of unity.  That is an arithmetic explanation of the cancellation, not
a bridge from a binary orbit to the decimal orbit.

## 4. Exact valuation at every depth

Modulo 2, all terms with \(j\geq1\) in (11) vanish coefficientwise.  From
(9), after writing \(X-1\) in place of \(X\),

\[
 a(X-1)=
 \frac{120X^2-89X+16}
 {(2X-1)(4X-1)(8X-7)(8X-3)}
 \equiv X\pmod2.                                       \tag{20}
\]

Every factor in the denominator of (20) is congruent to 1 modulo 2, while
the numerator is congruent to \(X\).  Thus \(F(X)\equiv X\pmod2\) as a
power series.  Since \(F(0)=0\), formal division by \(X\) gives an analytic
\(U(X)\in\mathbb Z_2[[X]]\) such that

\[
                         F(X)=XU(X),\qquad U(X)\equiv1\pmod2.\tag{21}
\]

For every \(m\in\mathbb Z_2\), \(U(m)\) is a two-adic unit.  Consequently

\[
                         v_2(F(m))=v_2(m)\qquad(m\geq1).\tag{22}
\]

Now put \(m=N+1\) and scale the BBP partial sum:

\[
\begin{aligned}
 S_N=16^NB_N
 &=\sum_{k=0}^{N}16^{N-k}a(k)\\
 &=\sum_{j=0}^{m-1}16^j a(m-1-j).
\end{aligned}                                           \tag{23}
\]

The omitted tail in \(F(m)\) begins at \(j=m\).  Since every value of \(a\)
at a two-adic integer is integral, every tail summand has valuation at least
\(4j\), and the non-Archimedean triangle inequality gives

\[
 v_2(F(m)-S_N)\geq4m>v_2(m).                            \tag{24}
\]

For \(m\geq1\), \(v_2(m)<4m\).  Thus (22) and (24) have unequal valuations,
and the equality case of the ultrametric inequality gives

\[
                         v_2(S_N)=v_2(N+1).              \tag{25}
\]

Since \(B_N=16^{-N}S_N\),

\[
 v_2(B_N)=v_2(N+1)-4N<0\qquad(N\geq1).                  \tag{26}
\]

For a rational in lowest terms, a negative two-adic valuation is minus the
two-adic valuation of its denominator.  Equation (26) is precisely (2).

## 5. Consequence for the fixed-sixteen return

For every fixed nonzero integer \(c\), once \(n>v_2(c)\), the terms
\(10^n\) and \(c\) have unequal valuations \(n\) and \(v_2(c)\).  The
equality case of the ultrametric inequality gives

\[
                         v_2(10^n-c)=v_2(c).             \tag{27}
\]

Equation (2) tends to infinity with \(N\).  Therefore the reduced denominator
of \(B_N\) cannot divide \(10^n-c\) for all sufficiently large \(N,n\).

For the requested multiplier \(c=16\), (27) is \(v_2(10^n-16)=4\) for
\(n\geq5\).  If \(N\geq2\) is even, \(v_2(N+1)=0\); if \(N\geq3\) is odd,
\(v_2(N+1)\leq N-1\).  Hence

\[
 v_2(\operatorname{den}B_N)=4N-v_2(N+1)\geq8
 \qquad(N\geq2).                                       \tag{28}
\]

Thus (4) is impossible for every \(N\geq2,n\geq5\).

This does **not** imply that (5) is bounded away from zero.  The BBP tail
still gives

\[
 \left|\|(10^n-16)\pi\|_{\mathbb T}
       -\|(10^n-16)B_N\|_{\mathbb T}\right|
 \leq(10^n-16)|\pi-B_N|.                               \tag{29}
\]

Choosing \(N\) large pays the right side, but the nonzero selected residue
on the left remains uncontrolled.  Controlling it along an unbounded
sequence at a transferable scale would prove (6), hence V1 itself.

## 6. Why logarithmic and trigonometric identities do not supply the missing phase

The calculation above exposes a general lattice mismatch.

- BBP and Machin identities arise from logarithms of algebraic numbers and
  angular relations modulo rational multiples of pi.
- The desired return asks for nearness of \((10^n-16)\pi\) to an **ordinary
  integer**, a period-one lattice condition.
- Replacing pi by a rapidly convergent rational or algebraic shadow pays only
  the Archimedean error.  It supplies no reason that the shadow lands near
  that integer lattice.
- Furstenberg density for the joint semigroup lets the exponent of 16 vary.
  It cannot be specialized to the fixed-sixteen return without exactly the
  invariance that is equivalent to V1.

The two-adic logarithm is powerful enough to determine the entire primary
denominator of (1), but it controls the wrong local coordinate for (5).

## 7. Dated primary-source audit

| Source | Checked statement | Scope here |
|---|---|---|
| [Bailey--Borwein--Plouffe, *On the Rapid Computation of Various Polylogarithmic Constants* (Math. Comp. 66, 1997), Theorem 1](https://doi.org/10.1090/S0025-5718-97-00856-9) | The exact series (1), with an integral proof. | Primary source for the BBP identity only; it makes no decimal-distribution claim.  A pinned local copy is `work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf`, SHA-256 `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`. |
| [Barsky--Muñoz--Pérez-Marco, *On the genesis of BBP formulas* (Acta Arith. 198, 2021), Theorem 5.2 and Proposition 5.3](https://arxiv.org/abs/1906.09629) | Derivation of the classical BBP formula from logarithms and an exact null BBP formula. | Supports the logarithmic provenance and the distinction between pi formulas and null formulas.  It does not state (2) or (3). |
| [Lagarias, *On the normality of arithmetical constants* (2001)](https://arxiv.org/abs/math/0101055) | BBP remainder dynamics and conditional dichotomy framework. | Confirms that BBP digit extraction does not furnish an unconditional orbit-density theorem. |

Fresh searches on 2026-08-12 UTC included the exact strings
`"4N-v_2(N+1)" BBP`, `2-adic BBP partial sums denominator formula`,
`p-adic BBP formula pi 2-adic null series`, and `denominator of partial sums
BBP formula valuation`.  No source stating (2) or (3) was located.  This is a
bounded search record, not a novelty claim.

## 8. Exact replay

Run:

```bash
.venv/bin/python work/ultrapi-resume/bbp_all_depth_two_adic_check.py
```

The checker verifies the immutable source hash, both polynomial
factorizations in (14), the reflected coefficient identity (10), the exact
finite denominator formula through depth 400, and the increasingly accurate
finite approximants to the null identity (3).  These finite checks have
status `experiment`; they do not replace the p-adic argument.

## Sharp conclusion

The standard BBP family has no odd-depth escape from its decimal-primary
denominator obstruction.  Its exact reduced denominator always contains

\[
                         2^{\,4N-v_2(N+1)}.
\]

Therefore no sufficiently deep BBP partial sum can be exactly anchored by
\(10^n-16\).  The only surviving BBP route is to prove decay of the nonzero
moving residue (5), and after tail transfer that statement is the fixed
return (6), hence V1.  No such decay was proved here, so V1 remains a
`conjecture`.
