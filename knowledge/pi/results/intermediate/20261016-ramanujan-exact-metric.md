# Exact metric and image of the Ramanujan fivefold defect

Date: 2026-10-16. Claim label: `proof sketch`. Reproduction label:
`experiment`. No Lean verification or priority claim.

Base repository: `thepok/PI`, commit
`2ab024737878cd9f1567cc296ef53f051a5ff10b`.

## What is new, and what is assumed

The repository's reviewed Frobenius proof sketch supplies the interpolation
\(U_N=P(N)\), \(P\in12+25\mathbb Z_5\langle x\rangle\), and deduces the
lower bound \(v_5(U_M-U_N)\ge2+v_5(M-N)\). The result here determines the
valuation exactly, identifies a single residue class with extra contraction,
and computes the complete five-adic image. This is a new corollary within the
inspected repository; it is not a replacement proof of its global Frobenius
comparison, and no claim about novelty in the literature is made.

The all-cutoff statement below depends on the reviewed global interpolation
in the [Frobenius proof sketch](https://github.com/thepok/PI/blob/2ab024737878cd9f1567cc296ef53f051a5ff10b/knowledge/pi/results/intermediate/20260906-ramanujan-frobenius-proof-sketch.md).
The elementary part uses only the bounded polynomial reduction and a
coefficient certificate from the [defect note](https://github.com/thepok/PI/blob/2ab024737878cd9f1567cc296ef53f051a5ff10b/knowledge/pi/results/intermediate/20260906-ramanujan-fiveadic-defect.md).
Section 5 gives an independent-of-Frobenius bounded-loss version for the
actual rational sums, including explicit infinite families of cutoffs.

No implication for E, CW0, CW9, or V1 is established. The closed carry route
is not reopened: the new information is five-adic arithmetic of a specific
sequence, with no estimate for ordered real decimal residues.

## 1. Statement

Retain
\[
b_N=\frac{\binom{2N}{N}^3}{256^N},\qquad
S_N=\sum_{j=0}^{N-1}(6j+1)b_j,\qquad
U_N=\frac{S_{5N}-5S_N}{125N^3b_N}\quad(N\ge1).
\]

For distinct positive integers \(M,N\), put
\[
\epsilon(M,N)=
\begin{cases}
1,&M\equiv N\equiv3\pmod5,\\
0,&\text{otherwise}.
\end{cases}
\]

**Exact valuation.** Subject to the repository's reviewed global interpolation,
\[
\boxed{
v_5(U_M-U_N)=2+v_5(M-N)+\epsilon(M,N).
}
\tag{1}
\]
Thus its former lower bound is sharp except when both indices are 3 modulo
5, where there is exactly one additional factor of 5. In particular, all
\(U_N\) are distinct as rational numbers.

**Exact image.** Writing \(U(x)=P(x)\) for the continuous extension to
\(\mathbb Z_5\), the extension is injective and
\[
\boxed{
\begin{aligned}
U(\mathbb Z_5)={}&(12+125\mathbb Z_5)\cup(87+125\mathbb Z_5)\\
&\cup(62+125\mathbb Z_5)\cup(37+125\mathbb Z_5)\\
&\cup(362+625\mathbb Z_5).
\end{aligned}}
\tag{2}
\]
Each of the five input residue balls maps bijectively onto its displayed
output ball:

| Input \(x\bmod5\) | Output ball for \(U(x)\) | Exact valuation gain |
|---|---|---|
| 0 | \(12+125\mathbb Z_5\) | 2 |
| 1 | \(87+125\mathbb Z_5\) | 2 |
| 2 | \(62+125\mathbb Z_5\) | 2 |
| 3 | \(362+625\mathbb Z_5\) | 3 |
| 4 | \(37+125\mathbb Z_5\) | 2 |

The gain column compares two distinct inputs in that input ball.

Inside the already known ball \(12+25\mathbb Z_5\), exactly four of its
25 residue classes modulo 625 are missing:
\[
112,\ 237,\ 487,\ 612\pmod{625}.
\tag{3}
\]
Its image occupies Haar proportion \(21/25\) of that ball, or absolute
Haar measure \(21/625\) when \(\mathbb Z_5\) has measure 1.
This is the image of the continuous extension, equivalently the closure of
the values at positive integer cutoffs; the countable set of integer values
itself does not have that positive Haar measure.

## 2. The minimal coefficient certificate

Let \(A=\mathbb Z_5\langle x\rangle\) and
\[
(LQ)(x)=\frac{(2x+1)^3}{32}Q(x+1)-x^3Q(x).
\]
The repository constructs analytic forcing
\(f=(HB-5(6x+1))/125\) and a norm-nonincreasing quotient map in
\(A=L(A)\oplus\mathbb Z_5[x]_{\le2}\). The quotient component is \(P\).
Its coefficientwise residue modulo \(625\) is
\[
\boxed{P(x)\equiv512+100x+550x^2+425x^3\pmod{625A}.}
\tag{4}
\]

This is obtained from coefficientwise expansion, not interpolation from a
finite list of cutoffs. Explicit ascending coefficient representatives are
\[
\begin{aligned}
H\pmod{5^7}:&\quad
(1,3030,59200,38000,7500,47500,50000,46875),\\
B\pmod{5^7}:&\quad
(77005,49380,47225,2375,0,3125).
\end{aligned}
\]
Multiplying, subtracting \(5+30x\), and only then dividing by 125 gives
\[
f\equiv616+121x+42x^2+16x^3+150x^4+300x^5+150x^6\pmod{625A}.
\]
Direct multiplication verifies this polynomial is
\(L(512+100x+550x^2+425x^3)\) modulo 625. Applying the bounded quotient
map proves (4), whether or not the exact quadratic remainder vanishes.

The infinite-tail justification is inherited from the repository's
coefficientwise construction: with
\[
E(t)=125t/12+875t^2/24+625t^3/12+625t^4/24,
\]
the \(m\)-th summand in \(\log G\) has coefficient valuation at least
\(3m-v_5(m)-\lfloor\log_5(4m+1)\rfloor\); exponential and rational-factor
tails have the explicit bounds recorded in `symbolic.py`. The supplied
reproduction script checks the raw arithmetic identity; the infinite-tail
bounds, not the finite check alone, justify it in the Tate algebra.

For
\[
V(x)=\frac{P(x)-12}{25},
\]
(4) is equivalent to
\[
\boxed{V(x)=20+4x+22x^2+17x^3+25W(x),\quad W\in A.}
\tag{5}
\]

## 3. Proof of the exact metric

For every \(W\in A\) and distinct \(x,y\in\mathbb Z_5\), the divided
difference \((W(x)-W(y))/(x-y)\) belongs to \(\mathbb Z_5\). Indeed,
each monomial divided difference is integral, and convergence follows from
the restricted coefficients tending to zero. This controls the error term
in (5) after division by \(x-y\), even when the two inputs are very close.

Modulo 5,
\[
V(x)\equiv2x^3+2x^2+4x=2(x+2)^3-1.
\]
Cubing permutes \(\mathbb F_5\), and the five output residues, in input
order \(0,1,2,3,4\), are \(0,3,2,4,1\). Consequently, if
\(x\not\equiv y\pmod5\), then
\(v_5(V(x)-V(y))=0=v_5(x-y)\).

If \(x\equiv y\equiv a\pmod5\), the divided difference of (5) modulo
5 is
\[
4+22(x+y)+17(x^2+xy+y^2)\equiv(a+2)^2\pmod5.
\]
It is a unit unless \(a=3\), giving
\(v_5(V(x)-V(y))=v_5(x-y)\) on the other four balls.

For the remaining ball, write \(x=3+5u,y=3+5v\). The same divided
difference modulo 25 is
\[
\begin{aligned}
4+22(x+y)+17(x^2+xy+y^2)
&\equiv4+22\cdot6+17\cdot27\\
&\quad+5(22+9\cdot17)(u+v)\\
&\equiv20\pmod{25}.
\end{aligned}
\]
The coefficient of \(u+v\) is 875, divisible by 25. The divided difference
therefore has valuation exactly 1, uniformly over this entire ball. The
error \(25W\) cannot change it. This proves
\[
v_5(V(x)-V(y))=v_5(x-y)+\boldsymbol1_{x\equiv y\equiv3\ (5)}.
\tag{6}
\]
Multiplying by 25 yields (1) for the analytic extension and, using
\(U_N=P(N)\), for the actual cutoff values.

## 4. Proof of the image classification

For \(a\in\{0,1,2,4\}\), define
\[
F_a(t)=\frac{V(a+5t)-V(a)}5.
\]
The restricted series is integral. Formula (6) implies that \(F_a\)
preserves every five-adic distance. A distance-preserving map
\(\mathbb Z_5\to\mathbb Z_5\) induces an injection on each finite quotient
\(\mathbb Z/5^k\mathbb Z\), hence a bijection. Compactness or the inverse
limit then gives surjectivity on \(\mathbb Z_5\). Thus
\(V(a+5\mathbb Z_5)=V(a)+5\mathbb Z_5\).

For the exceptional ball use
\[
F_3(t)=\frac{V(3+5t)-V(3)}{25}.
\]
The numerator is in \(25A\): its linear coefficient is \(5V'(3)\),
with \(V'(3)\equiv20\pmod{25}\), and higher coefficients have at least
two powers of 5. Formula (6) again makes \(F_3\) distance-preserving
and surjective. Since (5) gives \(V(3)\equiv14\pmod{25}\),
\[
V(3+5\mathbb Z_5)=14+25\mathbb Z_5.
\]
Together with the five residues modulo 5, this proves (2). Different input
balls have different output residues modulo 5 for \(V\), so they do not
overlap. The missing classes and Haar measures follow directly.

## 5. What survives without accepting the Frobenius comparison

The repository's uniform degree-25 certificate \(P_{20}\) gives, for every
positive integer \(N\),
\[
v_5(U_N-P_{20}(N))\ge20-3e(N),\qquad
e(N)=v_5(N)+v_5\binom{2N}{N}.
\]
Its coefficients reduce to (4). Therefore the proof of the exact metric
applies to \(P_{20}\) itself. Put
\(\lambda(M,N)=2+v_5(M-N)+\epsilon(M,N)\). If
\[
\boxed{\lambda(M,N)<\min\{20-3e(M),20-3e(N)\},}
\tag{7}
\]
the two approximation errors are strictly smaller in five-adic size than
the polynomial difference. The ultrametric inequality then proves (1) for
the actual sums, without the global Frobenius comparison.

The strict inequality in (7) is essential. Equality of error and signal
valuation would permit cancellation.

For concrete infinite examples, Kummer's carry formula gives
\(e(5^k+1)=e(5^k+2)=0\) for \(k\ge1\), hence
\[
v_5(U_{5^k+2}-U_{5^k+1})=2\qquad(k\ge1).
\]
For \(k\ge2\), doubling the base-5 expansions of \(5^k+3\) and
\(5^k+8\) produces exactly one carry, while both indices are units.
Thus both have \(e=1\), their difference is 5, and
\[
v_5(U_{5^k+8}-U_{5^k+3})=4\qquad(k\ge2).
\]
These use the single uniform precision-20 certificate, not a sample at
finitely many values of \(k\).

## 6. Reproduction

From the repository root, the minimal certificate is reproduced by

```sh
python3 workflows/experiments/ramanujan_fiveadic_defect_20260906/symbolic.py --precision 4
```

The independent finite experiment is

```sh
python3 workflows/experiments/ramanujan_fiveadic_defect_20261016/exact_metric_check.py --max-n 1250 --precision 10
```

Observed output on 2026-10-16:

```text
PASS: cubic coefficient identity modulo 5^4 and divided differences
PASS: N=1..1250; working modulus 5^26; U output 5^10
PASS: 780625 exact pairwise valuations, including 31125 exceptional pairs
PASS: independent exact rational values for N=1..30
```

The first 25 residues \(U_N\pmod{625}\) were

```text
337,62,362,37,387,212,187,362,162,262,87,312,362,287,137,
587,437,362,412,12,462,562,362,537,512.
```

All arithmetic is exact. The modular calculation strips the full
denominator valuation before inversion and reserves a guard digit.
The check over pairs is an `experiment`; the all-input conclusion comes
from the coefficientwise identity and divided-difference argument.

## 7. Research boundary

The result strengthens an existing arithmetic intermediate statement. It
shows exactly how much information about the cutoff is preserved in the
normalized defect, and exposes a residue class where a plausible uniform
isometry conjecture would have failed. It neither controls carries in the
decimal expansion of pi nor supplies the missing target-signed input.

An explicit decimal avoider with all fractional digits in \(\{1,2\}\)
stays between \(1/9\) and \(2/9\) under decimal shifts. No premise in this
note rules out an analogous real orbit for a limit using only the displayed
five-adic information. Hence this note is not an admitted digit candidate
under `FRONTIER.md`, and it should not be described as progress on V1 itself.
