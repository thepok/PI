# Independent audit: cyclotomic language-product attack

Audit date: **2026-08-12 UTC**  
Audit status: `proof sketch` audit with exact finite checks and separately
labelled numerical `experiment` checks  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

## Verdict

**PASS at the stated `proof sketch` level, after two claim-precision
corrections.** I found no sign error, missing exponential factor, invalid
Perron--Frobenius hypothesis, or hidden degree/length compression in the
central separator. In particular:

- the language-product and cyclotomic identities are correct;
- spacing improves the factorwise lower exponent from \(N_n\log q\) to
  \(C_wN_n+O_w(\log q)\);
- the singular logarithmic potential is integrable and its finite-language
  averages have the stated exponentially small normalized error, apart from
  the displayed \(O(n/N_n)\) selected-point term;
- the sharp decay constant satisfies
  \(c_w(\pi-3)>-\log(-2\cos2)\), so a lower bound with leading constant below
  the old upper constant cannot be true for this product;
- the Gamma/reflection and Euler--Maclaurin calculation has the displayed
  sign and constant;
- the child/parent quotient has logarithm \(O_w(\log q)\), but clearing it
  restores two integer polynomials with \(N_n\) binomial factors and
  \(\Theta(qN_n)\) degree.

This is a correct separator for the particular auxiliary-product family. It
does not prove V1, does not rule out unrelated auxiliary constructions, and
does not upgrade any claim to `machine-checked`, `candidate resolution`,
or `verified resolution`. V1 remains a `conjecture`.

## Audited pins

- Canonical target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Corrected report SHA-256:
  `d51c696eb6914de24cfaecb3ad185a387c9d385423dfc8118bb9a528377e8ebf`
- Original companion checker SHA-256:
  `ba3c0be9ebc42af0c9ea7ffac681455bc954906e0db2a09823a3d8f42dbfe440`
- Independent checker SHA-256:
  `ac851c1012227de63c7f54008940fd07c80270b630a26187e649818f165e69aa`

## 1. Exact product and cyclotomic identities

For \(p=3q+a\), \(\alpha=\pi-3\), and \(z_q=e^{i/q}\),

\[
 1+z_q^p=1+e^{i(3+a/q)}=1-e^{i(a/q-\alpha)}.
\]

The last equality uses \(e^{i3}=-e^{-i\alpha}\), so the report's logarithmic
potential identity has the correct sign. The following factorization is also
exact:

\[
 1+Z^p=\frac{Z^{2p}-1}{Z^p-1}
      =\prod_{d\mid2p,\ d\nmid p}\Phi_d(Z).
\]

Hence every zero is on the unit circle, the Mahler measure is one, and the
interior Jensen average is zero because the constant coefficient is one and
there is no zero in \(|Z|<1\).

The common-factor formula

\[
 \gcd(Z^p+1,Z^r+1)=
 \begin{cases}
 Z^{(p,r)}+1,&p/(p,r),r/(p,r)\text{ both odd},\\
 1,&\text{otherwise}
 \end{cases}
\]

is correct over characteristic zero with monic gcd convention. The report's
resultant warning is therefore real: shared cyclotomic zeros make the full
product discriminant vanish. Statements about what a squarefree radical
would lose are qualitative separator language, not an additional theorem.

## 2. Spacing lower bound

The layer identity is valid because every distance lies strictly between
successive powers of ten; irrationality excludes equality at a boundary:

\[
 \sum_u\lfloor-\log_{10}|y_u-\alpha|\rfloor
 =\sum_{k\ge1}\#\{u:|y_u-\alpha|<10^{-k}\}.
\]

For \(k\le n\), an open interval of radius \(10^{-k}\) meets at most three
length-\(k\) decimal cylinders. A legal cylinder ending at state \(s\) has
exactly \((M^{n-k}{\bf1})_s\) completions. Primitivity then gives the uniform
bounds \(O_w(\lambda^{n-k})\) for the local count and
\(N_n\asymp_w\lambda^n\).

For \(k>n\), the interval contains at most one point of the \(q^{-1}\) grid.
For any fixed \(\nu>\mu(\pi)\), the eventual bound

\[
 |a/q-\alpha|=|(3q+a)/q-\pi|\ge q^{-\nu}
\]

leaves only \(O(\log q)\) such one-point layers. Summing the layers gives

\[
 -\sum_u\log|y_u-\alpha|=O_w(N_n+\log q).
\]

Since \(|y_u-\alpha|<1\) and

\[
 2\sin(1/2)|t|\le |1-e^{it}|\le |t|\qquad(|t|\le1),
\]

the stated joint product lower bound follows. The notation \(C_w\) suppresses
dependence on the one fixed scalar input for \(\pi\) (a chosen finite
irrationality-exponent bound); it is not purely graph data in a literal
parameter ledger. This does not affect the comparison of exponential scales.

## 3. Perron limit and logarithmic singularity

The avoidance graph is primitive for every nonempty word. Every proper-prefix
state is reachable from state zero. A digit different from both the first and
last digit of \(w\) can be read repeatedly without completing \(w\); after
\(|w|\) repetitions the automaton is at state zero, which also has a loop on
that digit. Thus Perron--Frobenius spectral convergence applies.

If \(v>0\) is a right Perron vector, the transition weights telescope along a
legal prefix ending in state \(s\):

\[
 \Pr_{\nu_w}[u]=\frac{v_s}{\lambda^{|u|}v_0}.
\]

This both verifies the transition formula and shows that \(\nu_w\) has no
atoms. Uniform legal words of length \(n\), restricted to their first
\(L=\lfloor n/2\rfloor\) digits, differ exponentially from this law by the
Perron spectral gap; changing the remaining digits changes the evaluated real
number by at most \(10^{-L}\). This gives exponential convergence for
Lipschitz test functions.

For the singular test function, a radius-\(10^{-k}\) interval has mass
\(O_w(\lambda^{-k})\) under both the finite and limiting measures. Truncating
the logarithm at depth proportional to \(n\) makes this tail exponentially
small. Below the \(10^{-n}\) grid scale there is at most one finite-measure
atom, and the scalar irrationality bound limits its total contribution to
\(O(n/N_n)\). These observations justify

\[
 \int F_\alpha\,d\mu_n
 =\int F_\alpha\,d\nu_w+O_w(\vartheta_w^n+n/N_n)
\]

for some \(0<\vartheta_w<1\), and hence the unnormalized asymptotic in the
report. They also establish finiteness of the integral.

On \(x\in[0,1]\), the maximum of
\(2|\sin((x-\alpha)/2)|\) occurs only at \(x=1\). For
\(\alpha=\pi-3\), its value is

\[
 2\sin((4-\pi)/2)=-2\cos2=\rho<1.
\]

Therefore \(F_\alpha\le\log\rho\), with equality only at a point of
\(\nu_w\)-measure zero. This proves the strict inequality
\(-\int F_\alpha\,d\nu_w> -\log\rho\); no unproved quantitative gap is being
smuggled into the comparison.

## 4. Full-grid Gamma/reflection and second-order term

Starting from

\[
 \prod_{a=0}^{q-1}|a-q\alpha|
 =\left|\frac{\Gamma(q-q\alpha)}{\Gamma(-q\alpha)}\right|
\]

and using

\[
 |\Gamma(-x)|^{-1}=\Gamma(x+1)|\sin(\pi x)|/\pi
\]

gives exactly the report's distance-product identity. Stirling then yields

\[
 \begin{aligned}
 \sum_{a=0}^{q-1}\log|a/q-\alpha|
 &=q\int_0^1\log|x-\alpha|\,dx
   +\log|2\sin(\pi q\alpha)|\\
 &\quad+\tfrac12\log\frac{\alpha}{1-\alpha}+O(q^{-1}).
 \end{aligned}
\]

The smooth even correction
\(H(t)=\log(2\sin(|t|/2)/|t|)\) extends smoothly through zero. The left-endpoint
Euler--Maclaurin formula contributes

\[
 q\int_0^1H(x-\alpha)\,dx
 +\frac{H(-\alpha)-H(1-\alpha)}2+O(q^{-1}).
\]

Adding the two formulas reproduces both the sign and the constant \(C(\alpha)\)
in the report. The lower bound on rational approximation to \(\pi\) gives
\(\log|\sin(\pi q\alpha)|\ge-O(\log q)\); the trivial upper bound completes
the displayed \(O(\log q)\) fluctuation statement.

## 5. Child/parent quotient and arithmetic ledger

If a legal parent has exponent \(p=3\cdot10^{n-1}+a\), its children have
exponents \(10p+d\). Repeating the exponent \(10p\) once per allowed child
therefore gives exactly \(N_n\) factors on both sides of the quotient.

The \(O_w(\log q)\) bound can be checked without assuming cancellation. Split
parent grid points into those within \(20/q\) of \(\alpha\) and the rest.
There are \(O(1)\) near parents because their mesh is \(10/q\); every
associated logarithm is \(O(\log q)\) by the fixed irrationality-exponent
bound. On the far set, all digit shifts have size at most \(9/q\), while

\[
 |F_\alpha'(x)|\ll |x-\alpha|^{-1}.
\]

Bounding the legal parents by the full \(10/q\)-grid reduces the total absolute
change to a harmonic sum

\[
 q^{-1}\sum_{a}|a/10^{n-1}-\alpha|^{-1}=O(\log q).
\]

Thus the quotient estimate is sound. The selected-parent expansion follows
from \(10x_{n-1}=d_n+x_n\) and
\(\log(2\sin(|t|/2))=\log|t|+O(t^2)\), with total remainder \(O(q^{-2})\).

For the arithmetic ledger, polynomial length must mean coefficient
\(\ell^1\)-length \(L(P)=\sum_j|[Z^j]P|\). Each product has nonnegative
coefficients, so evaluation at \(Z=1\) gives exactly \(L=2^{N_n}\), even when
subset-sum collisions reduce the number of distinct monomials. The degrees
are the sums of \(N_n\) exponents lying at scale \(q\), hence
\(\Theta(qN_n)\). Consequently
\(L({\cal E}-{\cal Q})\le2^{N_n+1}\), and clearing the quotient does not yield
a low-degree or low-length integer polynomial.

## 6. Corrections made during this audit

Two claim-precision ambiguities were corrected directly in the report:

1. “length \(2^{N_n}\)” now explicitly means coefficient \(\ell^1\)-length.
   It would generally be false if interpreted as the number of distinct
   monomials.
2. Equation (7), which contains an \(O(q^{-2})\) remainder, was removed from
   the list of literal exact identities and is now identified as an
   asymptotic `proof sketch` consequence.

No formula, asymptotic rate, or final verdict was changed.

## 7. Reproduction checks

The supplied checker ran successfully:

```text
PASS: exact cyclotomic, transfer-tree, shell, and distance-product identities
EXPERIMENT: -N^-1 log products at n=5: w=0: 1.2923808501, w=00: 1.4111144566, w=314: 1.4162801665, w=99: 1.4296542093
EXPERIMENT: unrestricted limiting rate: 1.4167013053
```

I also added and ran
[`cyclotomic_language_product_independent_check.py`](cyclotomic_language_product_independent_check.py).
Its exact tests independently cover:

- cyclotomic factorizations for \(1\le p\le60\);
- all gcd pairs \(1\le p,r\le50\);
- child/parent exponent multisets and exact degree differences for four words
  through \(n=4\);
- an expanded small polynomial check of coefficient \(\ell^1\)-length,
  including exponent collisions;
- the shell layer identity and three-cylinder bound for three words and three
  rational centers.

Its separately labelled numerical `experiment` checks stress the
Gamma/reflection identity at 100-digit precision, the second-order constant
for three centers and three grid sizes, and the child/parent cocycle through
\(n=6\). Its output was:

```text
PASS: independent exact cyclotomic, gcd, tree, degree/l1, and shell checks
EXPERIMENT PASS: Gamma/reflection, second-order sign, and cocycle scales
```

Both checker files also pass Python bytecode compilation. These finite and
numerical checks support the algebraic ledger only; they are not evidence for
V1.

## 8. Remaining boundary

The branch now identifies its missing input correctly. A generic joint lower
bound at scale \(\exp(-C_wN_n)\) is not enough: its best leading constant must
match the actual logarithmic potential, already strictly beyond the crude
upper constant. A crossing would require a language-sensitive,
\(\pi\)-specific second-order estimate controlling the selected path cocycle.
No such estimate is established here. That is the exact point where this
`proof sketch` branch stops.
