# Furstenberg--BBP bridge for the decimal orbit of pi

Audit date: 2026-08-12 UTC

Status: the source audit below is `literature-checked` within its dated and
bounded scope.  The elementary deductions are `proof sketch`; the replay
script is an `experiment`.  Canonical V1 remains a `conjecture`.  In
particular, this note does **not** prove that every finite decimal word occurs
in pi.

## 1. Provenance, normalized target, and quantifiers

The immutable source is `problems/local/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
It is a human-authored local root and has no external source URL.

Put \(\mathbb T=\mathbb R/\mathbb Z\), write \(\{z\}\) for fractional part
and \(\|z\|_{\mathbb T}\) for distance to the nearest integer, and let

\[
 T_b(x)=bx\pmod 1,\qquad \alpha=\pi\pmod1,
 \qquad K=K_{10}(\alpha)=
 \overline{\{T_{10}^n\alpha:n\in\mathbb Z_{\ge0}\}}.
\]

Let \((D_j)_{j\ge1}\) be the unique decimal digit sequence of the fractional
part of pi, so \(\{\pi\}=\sum_{j\ge1}D_j10^{-j}\) with
\(D_j\in\{0,\ldots,9\}\).  The exact canonical statement V1 is

\[
 \forall m\ge0\ \forall(d_1,\ldots,d_m)\in\{0,\ldots,9\}^m\
 \exists n\ge0:\quad
 (D_{n+1},\ldots,D_{n+m})=(d_1,\ldots,d_m).
\]

Thus the requested word occurs contiguously beginning at decimal position
\(n+1\).  Leading zeros in the requested word are allowed; for \(m=0\) the
statement is vacuous.  Since pi is irrational, there is no
terminating-expansion ambiguity.  Decimal cylinders form a basis for
\(\mathbb T\), so

\[
             \mathrm{V1}\quad\Longleftrightarrow\quad K=\mathbb T. \tag{1}
\]

The following quantifier distinctions are essential.

1. “\(K\) is \(\times16\)-invariant” below means the forward inclusion
   \(T_{16}K\subseteq K\), not merely that the two sets intersect.
2. The orbit closure is one-sided.  Membership of a point not already on the
   orbit means approximation along an unbounded subsequence.
3. Furstenberg density allows both exponents in \(10^m16^n\) to vary.  V1
   fixes the exponent of 16 to zero.
4. The natural BBP perturbed recurrence shadows the base-16 orbit.  A second,
   reweighted recurrence shadows the base-10 orbit.  These are not
   interchangeable.
5. Base-16 digit density or normality is not base-10 digit density or
   normality, because 10 and 16 are multiplicatively independent.

## 2. The topological bridge is exact, but it is already V1

Furstenberg's Theorem IV.1 states that a nonlacunary multiplicative semigroup
of integers sends every irrational circle point to a dense set.  The semigroup
\(\langle10,16\rangle\) is nonlacunary: \(10^a=16^b\) for positive integers
\(a,b\) is impossible by comparing 5-adic valuations.

The following general statement isolates exactly what would be sufficient.

**Proposition (`proof sketch`).**  Let \(b,c\ge2\) be multiplicatively
independent, let \(x\in\mathbb T\) be irrational, and put
\(K_b(x)=\overline{\{b^nx:n\ge0\}}\).  The following are equivalent:

\[
\begin{array}{ll}
\text{(a)}&K_b(x)=\mathbb T;\\
\text{(b)}&cx\in K_b(x);\\
\text{(c)}&cK_b(x)\subseteq K_b(x);\\
\text{(d)}&c^rx\in K_b(x)\text{ for some }r\ge1;\\
\text{(e)}&c^rK_b(x)\subseteq K_b(x)\text{ for some }r\ge1.
\end{array} \tag{2}
\]

For (b)\(\Rightarrow\)(c), take \(b^{n_j}x\to y\in K_b(x)\).  Commutation
gives \(b^{n_j}(cx)\to cy\); every term lies in \(K_b(x)\), which is closed.
Condition (d) gives invariance under \(c^r\) in the same way, and
\(\langle b,c^r\rangle\) is still nonlacunary.  Furstenberg then puts the
dense joint orbit inside \(K_b(x)\), proving (a).  The remaining implications
are immediate.

Moreover, multiplicative independence and irrationality rule out a finite
equality \(b^Nx=c^rx\pmod1\).  Thus

\[
 c^rx\in K_b(x)
 \quad\Longleftrightarrow\quad
 \liminf_{N\to\infty}\|(b^N-c^r)x\|_{\mathbb T}=0. \tag{3}
\]

Specializing \((b,c,x)=(10,16,\pi)\), equations (1)--(3) give

\[
 \boxed{
 \mathrm{V1}
 \Longleftrightarrow 16\pi\in K
 \Longleftrightarrow T_{16}K\subseteq K
 \Longleftrightarrow
 \liminf_{N\to\infty}\|(10^N-16)\pi\|_{\mathbb T}=0.} \tag{4}
\]

Consequently, proving even the single return \(16\pi\in K\) is not a weaker
intermediate theorem.  It is an exact reformulation of V1 after applying
Furstenberg.

## 3. What the hexadecimal BBP recurrence actually gives

Bailey--Borwein--Plouffe prove

\[
 \pi=\sum_{k=0}^{\infty}\frac{c_k}{16^k},\qquad
 c_k=\frac4{8k+1}-\frac2{8k+4}-\frac1{8k+5}-\frac1{8k+6}. \tag{5}
\]

Combining the four fractions gives the positive expression

\[
 c_k=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}. \tag{6}
\]

For \(k\ge1\), \(0<c_k\le k^{-2}\).  An explicit polynomial certificate is

\[
\begin{split}
 &(2k+1)(4k+3)(8k+1)(8k+5)\\
 &\quad-k^2(120k^2+151k+47)
 =392k^4+873k^3+665k^2+194k+15>0.
\end{split} \tag{7}
\]

Let \(A_N=\sum_{k=0}^Nc_k16^{-k}\).  Positivity and (7) imply

\[
 0<\pi-A_N
 \le \frac{16^{-N}}{15(N+1)^2}. \tag{8}
\]

The natural hexadecimal BBP state is

\[
 h_N=\{16^NA_N\},\qquad
 h_{N+1}=\{16h_N+c_{N+1}\}. \tag{9}
\]

With \(\rho_N=16^N(\pi-A_N)\), equation (8) gives
\(0<\rho_N\le1/(15(N+1)^2)\), and exactly

\[
             \{16^N\pi\}=\{h_N+\rho_N\}. \tag{10}
\]

Therefore \((h_N)\) and the hexadecimal remainder orbit of pi have the same
omega-limit set.  This is the elementary shadowing relation underlying
Lagarias, Theorem 3.1 (up to the harmless index and initial-state convention).
Lagarias, Theorem 3.3, applied to the actual radix orbit, and irrationality of
pi show unconditionally that this limit set is infinite.  Density requires the unproved Weak Dichotomy
Hypothesis; uniform distribution requires the unproved Strong Dichotomy
Hypothesis (Bailey--Crandall's Hypothesis A).  Even granting the stronger
conclusion would establish base-16 behavior only.

Nothing in (5), (9), or (10) places \(h_N\), \(16^N\pi\), or one of their
limit points in the decimal orbit closure \(K\).  The recurrence evolves in
the \(\times16\) time direction, whereas (4) requires a \(\times10\) return
to the one fixed point \(16\pi\).

## 4. Decimal reweighting exposes the missing statement exactly

The same BBP partial sums can be sampled in decimal time.  Put

\[
 u_N=\{10^NA_N\},\qquad t_N=10^N(\pi-A_N).
\]

Then

\[
\begin{aligned}
 u_{N+1}
   &=\left\{10u_N+c_{N+1}\left(\frac58\right)^{N+1}\right\},\\
 0<t_N&\le\frac{(5/8)^N}{15(N+1)^2},\\
 \{10^N\pi\}&=\{u_N+t_N\},\\
 c_{N+1}\left(\frac58\right)^{N+1}&=10t_N-t_{N+1}.
\end{aligned} \tag{11}
\]

Thus the perturbation is an exact time-dependent coboundary.  If
\(F_N(z)=10z+c_{N+1}(5/8)^{N+1}\) and \(H_N(z)=z+t_N\), then

\[
                 H_{N+1}\circ F_N=T_{10}\circ H_N. \tag{12}
\]

Generic mixing of the expanding map cannot be imported through (12): the
nonautonomous recurrence is the original decimal orbit written in moving
coordinates.

The rational reduction is exact.  For \(N\ge2\), the circle distance is
1-Lipschitz and (8) gives

\[
\left|
 \|(10^N-16)\pi\|_{\mathbb T}
 -\|(10^N-16)A_N\|_{\mathbb T}
\right|
\le \frac{(5/8)^N}{15(N+1)^2}. \tag{13}
\]

Combining (4) and (13),

\[
 \boxed{
 \mathrm{V1}
 \Longleftrightarrow
 \liminf_{N\to\infty}\|(10^N-16)A_N\|_{\mathbb T}=0.} \tag{14}
\]

Equation (14) is an explicit rational diagonal target, not a proof of it.  It
shows exactly why the BBP error estimate is insufficient: the estimate
transfers the unknown decimal return from pi to \(A_N\), but gives no
distribution theorem for the moving rational residue.

## 5. Candidate recurrence and commutation bridges tested

| Proposed input | Exact consequence | Does it yield (4)? |
|---|---|---|
| BBP identity and digit extraction | Computes \(h_N\) and hexadecimal digits; (10) shadows \(\{16^N\pi\}\). | No cross-base membership statement. |
| Lagarias's unconditional theorem | Same hexadecimal omega-limit set; it is infinite for irrational pi. | No; an infinite closed set can be proper. |
| Weak/Strong Dichotomy Hypothesis | Conditionally makes the hexadecimal orbit dense/equidistributed. | No general base-16-to-base-10 transfer; the hypotheses are also unproved. |
| Furstenberg's theorem | \(\{10^m16^n\pi:m,n\ge0\}\) is dense. | No; both \(m,n\) vary, while V1 fixes \(n=0\). |
| Hexadecimal recurrence \(16^{r_j}\pi\to\pi\) | Recurrence in the \(\times16\) direction. | No; multiplication by an unbounded \(10^{m_j}\) amplifies the return error unless a new synchronized rate is proved. |
| \(K\cap16^rK\ne\varnothing\) for many or all \(r\) | Some common point, possibly a rational fixed point such as 0. | No; inclusion of the whole set is required. |
| \(16^r\pi\in K\) for one fixed \(r\ge1\) | By (2), \(K=\mathbb T\). | Yes, but this is equivalent to V1. |
| Decimal BBP recurrence (11) | Shadows the decimal orbit with exponentially vanishing error. | Only if the unproved diagonal condition (14) is established. |

The tempting joint-orbit transfer has the quantifier form

\[
 \forall I\ne\varnothing\ \exists m,n\ge0:
       10^m16^n\pi\in I, \tag{15}
\]

whereas V1 asks

\[
 \forall I\ne\varnothing\ \exists m\ge0:
       10^m\pi\in I. \tag{16}
\]

Neither commutation nor compactness changes (15) into (16).  The missing
uniform way to remove the varying exponent \(n\) is precisely the invariance
in (4).

## 6. Explicit dynamical separator

Schmidt's Theorem 2 supplies a strong separator.  For a canonical base-9
expansion

\[
 \xi=0.d_1d_2\ldots\quad(d_j\in\{0,\ldots,8\}),
\]

define

\[
 \Phi(\xi)=\sum_{j\ge1}d_j10^{-j}.
\]

Because 16 and 10 are multiplicatively independent, Schmidt's theorem with
\((r,s,t)=(16,10,9)\) says that \(\Phi(\xi)\) is normal to base 16 for
Lebesgue-almost every \(\xi\).  Almost every \(\xi\) is also normal to base 9.
The map \(\Phi\) is injective away from the countable radix-endpoint
ambiguities: at the first differing digit, the leading difference exceeds
the maximum possible decimal tail difference.  Choose a point in the
full-measure intersection, away from those endpoints and outside the
countable preimage of the algebraic numbers; call its image \(\beta\).  Then
(`proof sketch`):

1. \(\beta\) is transcendental and normal to base 16.  Its \(\times16\)
   orbit is therefore equidistributed, dense, and recurrent.
2. The decimal digits of \(\beta\) contain every finite word over
   \(\{0,\ldots,8\}\), because the source digit sequence is base-9 normal,
   but they contain no digit 9.
3. Its decimal orbit closure is exactly
   \[
     C=\left\{\sum_{j\ge1}e_j10^{-j}:e_j\in\{0,\ldots,8\}\right\},
   \]
   a proper closed \(\times10\)-invariant set.
4. Furstenberg still makes the joint orbit
   \(\{10^m16^n\beta:m,n\ge0\}\) dense.
5. Since \(0\in C\) and \(16^r0=0\), one has
   \(C\cap16^rC\ne\varnothing\) for every \(r\ge1\).
6. Nevertheless \(16^r\beta\notin C\) for every \(r\ge1\); otherwise (2)
   would force \(C=\mathbb T\), a contradiction.

This one point simultaneously preserves every abstract dynamical conclusion
one might hope to get from the BBP route--even full hexadecimal normality,
hexadecimal recurrence, joint Furstenberg density, transcendence, and
nonempty intersections of every pair of image sets--while decimal V1 fails.

The generic perturbed-recurrence mechanism can also be retained with rational,
positive, exponentially decaying perturbations.  Let

\[
 a_n=\frac{\lfloor16^{3n}\beta\rfloor}{16^{3n}},\quad a_0=0,
 \qquad \epsilon_n=16^n(a_n-a_{n-1}).
\]

Then \(\epsilon_n\in\mathbb Q_{\ge0}\),
\(\epsilon_n<16^{3-2n}\to0\), and telescoping gives

\[
             \beta=\sum_{n\ge1}\epsilon_n16^{-n}. \tag{17}
\]

Lagarias's perturbed recurrence for (17) shadows the dense hexadecimal orbit
of \(\beta\), but the decimal digit 9 is still absent.  Thus recurrence
shadowing, rational forcing, positivity, and rapid decay do not bridge the
bases.

The separator does **not** preserve pi's exact four-pole coefficient function
\(c_k\): no different number can preserve the complete identity (5), because
that identity fixes its sum to pi.  Its logical force is narrower and exact:
no argument using only the abstract dynamical consequences of BBP can prove
\(\times16\)-invariance of the decimal closure.  A successful argument would
have to exploit new arithmetic information in the exact coefficients to prove
the diagonal return (14).

## 7. Source audit and dated search log

| ID | Primary source and exact checked locator | Local pin | What is used |
|---|---|---|---|
| F67 | H. Furstenberg, *Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation*, Theorem IV.1, printed/PDF p. 48. DOI: <https://doi.org/10.1007/BF01692494>. | `work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf`, SHA-256 `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358` | Nonlacunary semigroup orbit of an irrational is dense. |
| BBP97 | D. H. Bailey, P. B. Borwein, S. Plouffe, *On the Rapid Computation of Various Polylogarithmic Constants*, Theorem 1 and (1.2), report p. 3. DOI: <https://doi.org/10.1090/S0025-5718-97-00856-9>. | `work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf`, SHA-256 `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` | Exact base-16 series and digit-extraction algorithm, not distribution. |
| BC01 | D. H. Bailey, R. E. Crandall, *On the Random Character of Fundamental Constant Expansions*, Hypothesis A and Theorem 1.1. DOI: <https://doi.org/10.1080/10586458.2001.10504441>. | `work/theory/pi-lacunary-near-return-sparsity/library/t63/bailey-crandall-2001-bcrandom.pdf`, SHA-256 `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` | The pi normality conclusion is conditional and in base 16/2. |
| L01 | J. C. Lagarias, *On the Normality of Arithmetical Constants*, Theorems 3.1, 3.3, 4.1 and Section 6, arXiv:math/0101055v2. <https://arxiv.org/abs/math/0101055v2>. | `work/theory/pi-lacunary-near-return-sparsity/library/t63/lagarias-math0101055v2.pdf`, SHA-256 `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` | Perturbed and radix orbits have the same limit set; the dichotomy is conditional; the paper reports no known bridge to Furstenberg's measure conjecture. |
| S60 | W. M. Schmidt, *On Normal Numbers*, Theorem 2, printed/PDF p. 662. DOI: <https://doi.org/10.2140/pjm.1960.10.661>. | `work/theory/pi-digits/library/t12/schmidt-1960-on-normal-numbers.pdf`, SHA-256 `28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67` | Missing-decimal-digit Cantor points can be normal in multiplicatively independent base 16. |

Searches run on 2026-08-12 UTC included `BBP Furstenberg pi normality
multiplicatively independent bases dynamics`, `Lagarias normality arithmetical
constants BBP Furstenberg`, and the exact Furstenberg/BBP title and DOI
queries.  The bounded search recovered the primary sources above and no
primary theorem proving the fixed-pi cross-base inclusion (4).  This is a
bounded negative applicability finding, not a global novelty claim.

The exact algebra in (6), (7), (9), and (11) is replayed by
`work/ultrapi-resume/furstenberg_bbp_bridge_check.py`.  Passing that script is
an `experiment`, not a machine-checked theorem and not evidence for the
liminf in (14).

## 8. Verdict and usable next target

**Does V1 follow?  No.**  The topological route is logically sound, but its
needed premise

\[
              16\pi\in K
 \quad\text{or equivalently}\quad
 \liminf_N\|(10^N-16)A_N\|_{\mathbb T}=0
\]

is itself equivalent to V1.  The hexadecimal BBP recurrence supplies no such
membership; it shadows the wrong one-parameter orbit.  Joint semigroup
density, hexadecimal normality, recurrence, and nonempty image intersections
all survive the Schmidt separator while decimal disjunctivity fails.

The narrow noncircular research target left by this route is therefore an
exact, pi-specific estimate on the rational residues
\((10^N-16)A_N\pmod1\) that proves a zero liminf.  No checked primary source
provides that estimate, and the BBP tail bound alone merely transfers the
original problem to it.
