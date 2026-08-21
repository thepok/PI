# Hutton multi-band local coordinates and the full radical of the denominator

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained.  The
canonical V1 statement remains a `conjecture`.

There is nevertheless a substantive exact extension of T61--T64.  If
$R=4K+3$, $H_K=P_K/Q_K$ is the reduced lower Hutton shadow, $p>7$ is
prime, and $p\le R<p^2$, then the complete $p$-singular block is governed by
one *shorter Hutton prefix*.  Put

\[
 A_n=\sum_{j=0}^{n-1}(-1)^j\left(
 {8\over(2j+1)3^{2j+1}}+{4\over(2j+1)7^{2j+1}}\right),
 \quad
 n=\left\lfloor{\lfloor R/p\rfloor+1\over2}\right\rfloor .       \tag{1}
\]

Then, in the localization at $p$,

\[
 \boxed{\quad pH_K\equiv\chi_4(p)A_n\pmod p.\quad}              \tag{2}
\]

Moreover $p$ occurs in $Q_K$ with exponent exactly one if and only if
$p\nmid\operatorname{num}(A_n)$; otherwise it does not occur in $Q_K$.
Here $\chi_4(m)=(-1)^{(m-1)/2}$ for odd $m$.

The first new band is completely explicit:

\[
 3p\le R<5p
 \quad\Longrightarrow\quad
 A_n=A_2={87112\over27783}
 ={2^3\cdot10889\over3^4\,7^3}.                         \tag{3}
\]

Thus every prime $p>7$ in $R/5<p\le R/3$ occurs exactly once in
$Q_K$, with the **single exact exception $p=10889$**.  At that exception
the prime is absent, not merely uncontrolled.

Iterating (2) has an asymptotic consequence.  If
$\operatorname{rad}(Q_K)$ is the squarefree kernel of the denominator,
then

\[
 \boxed{\quad \log\operatorname{rad}(Q_K)=R+o(R).\quad}           \tag{4}
\]

Equivalently, the denominator contains all but $o(R)$ of the Chebyshev
logarithmic weight of the primes at most $R$.  Formula (4) is the strongest
denominator-support conclusion found in this Hutton branch: no further
fixed-band iteration can improve its leading constant.

Equations (1)--(4), including the elementary local proof and the reduction
of (4) to the prime number theorem, are a `proof sketch`: they have not yet
been formalized and audited in Lean.  The accompanying exact replay is an
`experiment`.  This note is not a `candidate resolution`.

## 1. Normalized target and quantifier warning

The target remains

\[
 \forall\ell\ge0\ \forall c<10^\ell\ \exists j\ge0:\quad
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c,          \tag{V1}
\]

with $c$ padded to length $\ell$, contiguous occurrence, leading zeroes
allowed, and $\ell=0$ vacuous.  Pi is irrational, so the two-decimal-
expansion ambiguity does not arise.

The new result concerns denominator support for each $K$, followed by an
asymptotic as $K\to\infty$.  It gives neither a decimal-cylinder hit nor a
uniform estimate for the selected numerator $P_K$.  Those quantifiers are
not interchangeable with V1.

## 2. Exact singular-prefix identity

The lower Hutton rational is

\[
 H_K=\sum_{\substack{1\le r\le R\\r\ {\rm odd}}}
 \chi_4(r)\left({8\over r3^r}+{4\over r7^r}\right),
 \qquad R=4K+3.                                         \tag{5}
\]

Fix a prime $p>7$, with $p\le R<p^2$, and set
$q=\lfloor R/p\rfloor$.  The odd exponents in (5) divisible by $p$ are
exactly

\[
 r=cp,\qquad 1\le c\le q,\qquad c\text{ odd}.            \tag{6}
\]

The inequality $R<p^2$ gives $q<p$.  Therefore $v_p(cp)=1$ in (6),
while every nonsingular summand is $p$-integral.  In particular
$v_p(H_K)\ge-1$, so $pH_K$ has a well-defined residue modulo $p$.

For a singular exponent $cp$, Fermat's theorem and multiplicativity of
$\chi_4$ give

\[
\begin{aligned}
 p\,\chi_4(cp)\left({8\over cp3^{cp}}+{4\over cp7^{cp}}\right)
 &\equiv {\chi_4(p)\chi_4(c)\over c}
   \left({8\over3^c}+{4\over7^c}\right)\pmod p.          \tag{7}
\end{aligned}
\]

There are
$n=\lfloor(q+1)/2\rfloor$ odd integers $c\le q$.  Summing (7), while
the nonsingular terms vanish after multiplication by $p$, proves (2).
All denominators occurring in $A_n$ are $p$-units because their odd
linear factors are below $p$ and $p>7$.

Consequently

\[
\begin{array}{rcl}
 p\nmid\operatorname{num}(A_n)
 &\Longleftrightarrow& v_p(pH_K)=0
 \Longleftrightarrow v_p(H_K)=-1,\\[2mm]
 p\mid\operatorname{num}(A_n)
 &\Longleftrightarrow& v_p(pH_K)\ge1
 \Longleftrightarrow v_p(H_K)\ge0.                      \tag{8}
\end{array}
\]

Since $P_K,Q_K$ are coprime, (8) says that the exponent of $p$ in
$Q_K$ is respectively one or zero.  This proves the claimed if-and-only-if,
not just a sufficient survival criterion.

T64 is precisely the $n=1$ case, while T61 is its narrower upper-half
subband.  Here $A_1=68/21$, whose only prime numerator divisor above $7$
is $17$.

## 3. The band \(R/5<p\le R/3\)

The exact hypotheses

\[
 p>7,\qquad 3p\le R<5p                              \tag{9}
\]

imply $R<p^2$, because $5p<p^2$.  They also force
$q\in\{3,4\}$, hence $n=2$.  Direct rational arithmetic gives

\[
\begin{aligned}
 A_2
 &=\left({8\over3}+{4\over7}\right)
   -{1\over3}\left({8\over3^3}+{4\over7^3}\right)\\
 &={87112\over27783}
 ={2^3\cdot10889\over3^4\,7^3}.                       \tag{10}
\end{aligned}
\]

Trial division through $\sqrt{10889}<105$ verifies that $10889$ is
prime.  Thus (8) proves the exact theorem:

> If $p>7$ is prime, $3p\le4K+3<5p$, and $p\ne10889$, then
> $v_p(H_K)=-1$, so $p$ occurs exactly once in $Q_K$.  If instead
> $p=10889$, then $v_p(H_K)\ge0$, so $p$ is absent from $Q_K$.

The exceptional prime is genuinely admissible.  Taking
$R=3\cdot10889=32667=4\cdot8166+3$ satisfies (9); the exact singular
residue is zero.

For a direct two-pair Lean implementation, combining the terms at $p$ and
$3p$ over a common denominator produces the integer factor

\[
\begin{aligned}
 F_2(p)={}&24\,3^{2p}7^{3p}+12\,3^{3p}7^{2p}
          -8\,7^{3p}-4\,3^{3p},\\
 F_2(p)&\equiv87112\pmod p.                              \tag{11}
\end{aligned}
\]

Equation (11) is a compact route to the noncancellation lemma without first
formalizing the general $A_n$ identity.

## 4. Iterated fixed bands

For $n\ge1$, the interval

\[
 (2n-1)p\le R<(2n+1)p                                  \tag{12}
\]

has exactly the singular multipliers $1,3,\ldots,2n-1$.  Provided
$p>\max(7,2n+1)$, condition (12) also implies $R<p^2$, and (8) applies
with $A_n$.  The exceptional primes in this band are exactly the prime
divisors above $7$ of the fixed numerator of $A_n$.

The first five exact prefixes illustrate the pattern:

| \(n\) | band | \(\operatorname{num}(A_n)\) |
|---:|---|---|
| 1 | \(p\le R<3p\) | \(2^2\cdot17\) |
| 2 | \(3p\le R<5p\) | \(2^3\cdot10889\) |
| 3 | \(5p\le R<7p\) | \(2^2\cdot13\cdot1233899\) |
| 4 | \(7p\le R<9p\) | \(2^4\cdot12377338601\) |
| 5 | \(9p\le R<11p\) | \(2^2\cdot67\cdot15683\cdot26716073\) |

These factorizations are replayed exactly by the checker.  They show why a
naive claim that *every* sufficiently large prime below $R$ survives is
too strong at finite $R$: each new band has its own finite exceptional
set.  They also show why the exceptions disappear uniformly in any fixed
collection of bands once $R$ is large enough.

## 5. The radical squeeze

Every \(A_n\) is positive.  Indeed, in each base separately the alternating
terms decrease strictly in magnitude; grouping consecutive positive-negative
pairs leaves a positive sum, with a possible final positive term.  Thus none
of the fixed numerators below is zero.

Fix a band depth $L\ge1$, and put

\[
 M_L=\max_{1\le n\le L}|\operatorname{num}(A_n)|,
 \qquad X_L=\max(7,2L+1,M_L).                            \tag{13}
\]

Assume

\[
 R>(2L+1)X_L.                                           \tag{14}
\]

If $p$ is any prime with $R/(2L+1)<p\le R$, then $p>X_L$.  Hence
$p>7$, $p>2L+1$, $R<p^2$, and its index in (1) lies between $1$
and $L$.  Most importantly, $p>M_L$, so it cannot divide the nonzero
numerator of the relevant $A_n$.  Equation (8) proves that every such
prime occurs exactly once in $Q_K$.

Write $\vartheta(x)=\sum_{p\le x}\log p$.  It follows from (14) that

\[
 \log\operatorname{rad}(Q_K)\ge
 \vartheta(R)-\vartheta\!\left({R\over2L+1}\right).     \tag{15}
\]

For the reverse inequality, every summand denominator in (5) divides

\[
 3^R7^R\operatorname{lcm}\{r:1\le r\le R,\ r\text{ odd}\}. \tag{16}
\]

Thus, for $R\ge7$, every prime in the reduced denominator is at most
$R$, and

\[
 \log\operatorname{rad}(Q_K)\le\vartheta(R).             \tag{17}
\]

The prime number theorem $\vartheta(x)=x+o(x)$, applied with fixed $L$,
gives

\[
 1-{1\over2L+1}
 \le\liminf_{K\to\infty}{\log\operatorname{rad}(Q_K)\over R}
 \le\limsup_{K\to\infty}{\log\operatorname{rad}(Q_K)\over R}
 \le1.                                                   \tag{18}
\]

Since $L$ is arbitrary, letting $L\to\infty$ proves (4).  This order of
quantifiers is important: no uniform estimate on the rapidly growing
numerators $A_n$ is required.

In particular $Q_K\ge\exp((1+o(1))R)$.  The theorem concerns the radical;
it does not determine the much larger powers of $3$, $7$, or the other
small primes in $Q_K$.

## 6. Weighted global CRT consequence

The multi-band coordinates do combine globally, but the result exposes the
same selected-numerator barrier rather than removing it.

Fix $L$ and take $K$ large enough for (14).  Let

\[
 G=\prod_{R/(2L+1)<p\le R}p,\qquad Q_K=CG,               \tag{19}
\]

and let $n(p)$ be the index in (1).  Define

\[
 B=\operatorname{lcm}_{1\le n\le L}\operatorname{den}(A_n),
 \quad a_n=BA_n\in\mathbb Z,
 \quad S=\sum_{p\mid G}\chi_4(p)a_{n(p)}{G\over p}.     \tag{20}
\]

All primes in $G$ exceed $X_L$, so $\gcd(B,G)=1$.  Translating (2)
from $pH_K$ to the reduced numerator gives, prime by prime and hence by
the Chinese remainder theorem,

\[
 \boxed{\quad BP_K\equiv CS\pmod G.\quad}                \tag{21}
\]

Therefore an integer $T$ exists with an exact decomposition

\[
 H_K={P_K\over CG}
 =\underbrace{\sum_{p\mid G}{\chi_4(p)A_{n(p)}\over p}}_{\displaystyle\Delta_{K,L}}
   +{T\over BC}.                                         \tag{22}
\]

For fixed $L$, the prime number theorem in the two residue classes modulo
$4$, followed by partial summation, gives
$\Delta_{K,L}=o(1)$.  This is far too weak for decimal transfer.  At a
useful Hutton shift $s=\Theta(R)$, the perturbation in (22) is multiplied
by $10^s$; a grid-localization argument would need an exponentially small
bound of order $\exp(-cR)$, not merely $o(1)$ or a classical zero-free-
region saving.

There is also a sharp scale ceiling.  For the fixed $L$ modulus in (19),
the prime number theorem gives

\[
 \log G=\left(1-{1\over2L+1}\right)R+o(R).              \tag{23}
\]

Letting the fixed depth tend to infinity makes the leading coefficient
approach $1$, and the full radical squeeze (4) shows that this ceiling is
attained asymptotically.  Thus even the maximal prime-support modulus has

\[
 \log_{10}\operatorname{rad}(Q_K)\sim {R\over\log 10}
 =0.434294\ldots R,
\]

whereas the Hutton bracket transfers roughly

\[
 -\log_{10}W_K\sim R\log_{10}3
 =0.477121\ldots R                                      \tag{24}
\]

decimal shifts.  The gap is
$(\log3-1)R$ on the natural-log scale.  Thus prime support alone cannot
keep a non-wrapping skeleton over the full transferable prefix.  Any genuine
next step must control at least one of:

1. the actual weighted reciprocal phase $\Delta_{K,L}$ at exponential
   accuracy;
2. the large $3$- and $7$-primary coordinates and their correlation with
   the prime coordinate; or
3. the selected cofactor/numerator phase after the mandatory decimal
   transient.

No such estimate is proved here.

## 7. Exact replay

The checker is
[`hutton_multi_band_check.py`](hutton_multi_band_check.py).  It verifies:

- the source hash;
- 51,202 instances of the valuation if-and-only-if in (8);
- 102,404 direct local-coordinate/singular-block congruences;
- 7,449 instances in the one-fifth band;
- the exact $p=10889,R=32667$ zero-residue witness;
- the first five prefix-numerator factorizations;
- 60 weighted CRT congruence/decomposition assertions; and
- finite radical-support and ratio data.

Its complete output on 2026-08-12 UTC was:

```text
source sha256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
generic local-coordinate assertions: 102404
generic exact-valuation assertions: 51202
one-fifth-band assertions: 7449
observed cancelling (prefix index, prime) pairs: [(1, 17), (3, 13), (5, 67)]
one-fifth exceptional witness: p=10889 R=32667 K=8166 residue=0
weighted CRT/decomposition assertions: 60
fixed-depth thresholds (L, X_L, strict R threshold):
  1 68 204
  2 87112 435560
  3 64162748 449139236
  4 198037417616 1782336758544
  5 112288830326212 1235177133588332
  6 60523600449215608 786806805839802904
  7 346981844006868410804 5204727660103026162060
  8 459056974189868332544096 7803968561227761653249632
radical experiment (K, R, support size, log(rad Q)/R, theta(R)/R):
  20 83 21 0.860324656781 0.899578831938
  50 203 45 0.925469749216 0.928884267347
  100 403 78 0.933086817583 0.934806785773
  200 803 138 0.944460166318 0.945323363305
  400 1603 251 0.971316290413 0.971748696640
all exact checks passed
```

The ratios are an `experiment`; the proof of (4) is (13)--(18), not an
extrapolation from those rows.

## 8. Bounded literature and repository check

A bounded search on 2026-08-12 used the phrases “Hutton formula rational
partial sums denominator primes”, “arctangent Taylor partial sums denominator
prime divisibility p-adic”, and “denominators partial sums Gregory series
p-adic valuation”.  Nearby literature included work on generalized Gregory
series, arithmetic of other arctangent-sum sequences, and unbounded
denominators of hypergeometric series, but the search did not locate the
specific finite-prefix congruence (2) or radical asymptotic (4):

- Franc--Gannon--Mason, [*On unbounded denominators and hypergeometric
  series*](https://arxiv.org/abs/1708.04213);
- Wituła--Hetmaniok--Słota, [*Generalized Gregory's
  series*](https://www.sciencedirect.com/science/article/pii/S009630031400472X);
- Amdeberhan--Medina--Moll, [*Arithmetical properties of a sequence arising from an
  arctangent sum*](https://www.sciencedirect.com/science/article/pii/S0022314X07001424).

These are context, not sources for (2) or (4), and no novelty claim is made.
The repository search underlying this draft found the one-pair T61/T64
modules and the analogous two-singular-exponent mechanism in T50 for a
different Machin seed, but no pre-existing generic Hutton multi-band theorem.
The concurrently developed T65 module addresses the $n=2$ band; the generic
local identity and radical asymptotic here still require formalization before
any research claim is promoted.

## 9. Proposed Lean boundary

The smallest next verified unit is the $n=2$ band, not the entire
asymptotic theorem.  Exact declaration targets are:

1. a two-index regular block deleting the exponents $p$ and $3p$;
2. uniqueness of those two singular exponents under
   $3p\le4K+3<5p$;
3. the exact two-pair decomposition;
4. `huttonLowerBandCancellationFactor_cast_zmod`, with residue `87112`;
5. nondivisibility outside `p = 10889`;
6. `padicValRat_huttonLowerRat_oneFifthPrime = -1`;
7. denominator divisibility and exact multiplicity one; and
8. a finite one-fifth-band prime product dividing the reduced denominator.

The generic identity (2), the exceptional-prime if-and-only-if, and the
radical squeeze (4) are clean later targets, but they should not be hidden
inside one opaque tactic block.  No shared import or axiom-audit file was
edited by this attack.
