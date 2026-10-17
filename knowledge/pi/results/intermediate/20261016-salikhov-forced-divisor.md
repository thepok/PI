# A forced five-adic divisor and a sharp Salikhov branch

Research date: 2026-10-16; independently reproduced on 2026-10-17.
Labels: `proof sketch` and `experiment`.
No Lean verification or novelty claim is made. These are arithmetic results
about the coefficients of an exact representation of pi. They do not prove
E, CW0, CW9, or V1 and do not constitute an admitted decimal-target candidate.

## Result and relation to existing work

Use the normalization in the
[existing Salikhov note](20260906-salikhov-mod5-support.md):
\[
I_n=a_n+b_n\pi,\qquad
q_n=2^{2-\lfloor5n/2\rfloor}b_n\in\mathbb Z,\qquad
-\frac{a_n}{b_n}=\frac{P_n}{Q_n},\quad Q_n>0,\quad (P_n,Q_n)=1.
\]
The existing note proves \(b_n>0\). Write \(v_p\) for the usual valuation
on nonzero rational numbers, with \(v_p(p)=1\).

**Theorem 1 (`proof sketch`).** For every integer \(n\ge1\),
\[
\boxed{v_5(q_n)=v_5(b_n)\ge v_5(2n-1).} \tag{1}
\]
Thus the index congruence \(2n\equiv1\pmod{5^k}\) forces
\(5^k\mid q_n\), without constructing a separate automaton at each precision.

**Theorem 2 (`proof sketch`).** Let
\(N_k=(5^k+1)/2\), for \(k\ge1\). Then
\[
\boxed{\frac{b_{N_k}}{5^k}\equiv(-1)^k\pmod5,
\qquad \frac{q_{N_k}}{5^k}\equiv2^k\pmod5.} \tag{2}
\]
In particular \(v_5(q_{N_k})=k=\log_5(2N_k-1)\): (1) is sharp on
this explicit infinite family.

The [parallel arithmetic PR #9](https://github.com/thepok/PI/pull/9), at
commit `da92b6f6f8509b2c8bed88a6e60244cddfe00c88`, develops a different
growing-precision result using Cartier operators, including dense index
families. The proofs below are independent of that PR. Its binary family
has even indices; every \(N_k\) here is odd. The multiplier theorem alone
does not control companion cancellation. Theorem 3 below resolves that
cancellation on the special branch; ordered decimal residues remain open.

## Exact residue formula

The primary input is the integral and symmetric partial fractions in
[Zeilberger–Zudilin, arXiv:1912.06345v2, Part II](https://arxiv.org/html/1912.06345v2):
\[
\mathcal R_n(x)=\frac{5x^{2n}(x^4+6x^2+25)^{2n}}{(25-x^2)^{3n+1}},
\qquad
I_n=i(-1)^{n+1}\int_{-1-2i}^{-1+2i}\mathcal R_n(x)\,dx.
\]
In those partial fractions, the logarithmic coefficient satisfies
\(b_n=(-1)^n A_{n,0}/2\), while the residue of \(\mathcal R_n\)
at \(x=5\) is \(-A_{n,0}\). The paper's coefficient divisibility lemma
gives the stated integrality of \(q_n\).

Make the local substitution \(x^2=25(1+t)\) at \(x=5\), choosing
the square-root series with constant term 5. Put
\[
K(t)=32+56t+25t^2.
\]
Since \(x^4+6x^2+25=25K(t)\), direct cancellation gives
\[
\mathcal R_n(x)\,dx
=\frac{(-1)^{n+1}}2\,
t^{-3n-1}(1+t)^{n-1/2}K(t)^{2n}\,dt.
\]
Comparison of residues therefore proves the exact identity
\[
\boxed{4b_n=[t^{3n}](1+t)^{n-1/2}K(t)^{2n}.} \tag{3}
\]
This also holds at \(n=0\), giving \(b_0=1/4\). It is a formal
coefficient identity; no numerical evaluation of pi is involved.

## Proof of the index-forced divisor

Set
\[
r=n-\tfrac12,\quad m=3n,\quad
V(t)=(1+t)K(t)^2,\quad
W(t)=(1+t)^r K(t)^{2n-1}.
\]
All coefficients of \(W\) are in \(\mathbb Z_5\). Indeed,
\([t^j](1+t)^{-1/2}=(-1)^j\binom{2j}{j}/4^j\), and multiplication
by an integer power of \(1+t\) preserves integrality. Also \(K(0)=32\)
is a 5-adic unit, so integer powers, including negative powers, of \(K\)
have coefficients in \(\mathbb Z_5\).

Differentiation gives, for every \(j\ge1\),
\[
j[t^j]W
=r[t^{j-1}]V'(t)(1+t)^{r-1}K(t)^{2n-3}. \tag{4}
\]
The series on the right after the factor \(r\) is integral. This
identity can be checked by the product rule, so no ambiguous choice of
a fractional power of the non-unit-normalized polynomial \(V\) is needed.

If \(5\nmid2n-1\), (1) follows from the known integrality of \(q_n\).
Otherwise \(n\equiv3\pmod5\), and the three positive indices
\(m,m-1,m-2\) are respectively \(4,3,2\pmod5\). Division by any
of these indices in (4) is division by a 5-adic unit. Hence all three
coefficients \([t^{m-i}]W\), \(i=0,1,2\), have valuation at least
\(v_5(r)=v_5(2n-1)\). By (3),
\[
4b_n=32[t^m]W+56[t^{m-1}]W+25[t^{m-2}]W,
\]
so the same lower bound holds for \(b_n\). Multiplication by the
normalizing power of two proves (1).

## Proof that the special branch is sharp

Write \(M=5^k\), \(n=N_k=(M+1)/2\), \(r=M/2\),
\(m=(3M+3)/2\), and \(B=4b_n\). Then
\[
W=(1+t)^{M/2}K^M.
\]
Frobenius on the integral formal series \((1+t)^{1/2}\), together with
\(K\equiv2+t\pmod5\), gives
\[
W(t)\equiv F(t^M)\pmod5,\qquad
F(z)=(1+z)^{1/2}(2+z)=2+2z+O(z^2). \tag{5}
\]
In \(\mathbb F_5[[t]]\),
\[
\frac{V'}V\equiv L(t):=\frac1{1+t}+\frac2{2+t}.
\]
Its coefficients are
\[
\ell_j=[t^j]L=(-1)^j(1+2^{-j}),\qquad
(\ell_j)_{j\ge0}=(2,1,0,2,2,1,0,2,\ldots), \tag{6}
\]
with period four. Equation (4), equivalently \(W'=r(V'/V)W\), allows
division of the three relevant coefficients by \(r\) before reducing
modulo five. Since \(32/m\equiv3\), \(56/(m-1)\equiv2\), and
\(25/(m-2)\equiv0\),
\[
\frac Br\equiv
3[t^{m-1}]L(t)F(t^M)+2[t^{m-2}]L(t)F(t^M)\pmod5. \tag{7}
\]
Both \(m-1\) and \(m-2\) lie between \(M\) and \(2M-1\), since
\(M\ge5\). Only the first two coefficients in (5) contribute. Because
\(M\equiv1\pmod4\), (6) and (7) reduce to
\[
\frac Br\equiv\ell_{m-1}+4\ell_{m-3}
=\begin{cases}2&k\text{ odd},\\3&k\text{ even}\end{cases}\pmod5.
\]
Here \(m-1\equiv0\pmod4\) for odd \(k\), and
\(m-1\equiv2\pmod4\) for even \(k\); this follows from
\(5^k\equiv5\) or \(1\pmod8\). As \(b_n/M=(B/r)/8\), this is
the first congruence in (2).

For the second, write \(h=(M-1)/4\), so \(n=2h+1\) and
\(2-\lfloor5n/2\rfloor=-5h\). The binomial congruence
\(5^k=(1+4)^k\equiv1+4k\pmod{16}\) gives \(h\equiv k\pmod4\).
Consequently
\[
\frac{q_n}{M}\equiv2^{-k}(-1)^k=2^k\pmod5,
\]
which is nonzero. This proves the exact valuation in Theorem 2.

## Companion survival and the exact reduced denominator

**Theorem 3 (`proof sketch`).** For every \(k\ge1\),
\[
a_{N_k}\in\mathbb Z_5,\qquad
a_{N_k}\equiv1+2(-1)^k\pmod5. \tag{8}
\]
In particular \(v_5(a_{N_k})=0\). Theorem 2 and the exact
reduced-fraction identity
\[
v_5(Q_n)=\max\{0,v_5(b_n)-v_5(a_n)\} \tag{9}
\]
give \(\boxed{v_5(Q_{N_k})=k}\) for every \(k\).
The [complete companion proof](20261017-salikhov-companion-survival.md)
establishes (8) by an exact integration-by-parts identity and three finite
Cartier polynomial equalities whose two-state cycle proves the result at
every length. It also supplies an independent proof of (2) and the general
bound \(v_5(a_n)\ge v_5(2n-1)-\lfloor\log_5(4n)\rfloor\).
The residue proof above controls only the logarithmic term; the new
integration-by-parts argument is the additional input for the companion.

The exact finite `experiment` gives:

| \(k\) | \(N_k\) | \(v_5(b_{N_k})\) | \(b_{N_k}/5^k\bmod5\) | \(v_5(a_{N_k})\) | \(a_{N_k}\bmod5\) | \(v_5(Q_{N_k})\) |
|---|---|---|---|---|---|---|
| 1 | 3 | 1 | 4 | 0 | 4 | 1 |
| 2 | 13 | 2 | 1 | 0 | 3 | 2 |
| 3 | 63 | 3 | 4 | 0 | 4 | 3 |
| 4 | 313 | 4 | 1 | 0 | 3 | 4 |
| 5 | 1563 | 5 | 4 | 0 | 4 | 5 |
| 6 | 7813 | 6 | 1 | 0 | 3 | 6 |

The six cases validate the formula but do not establish its all-index
content; the linked algebraic proof does. There is no general scaling law
\(v_5(Q_{5n})=v_5(Q_n)+1\): already \(v_5(Q_{14})=v_5(Q_{70})=1\).

The existing linear bound for the normalized companion
\(c_n=2^{2-\lfloor5n/2\rfloor}a_n\) gives
\[
v_2(P_n)\ge\max\{0,2n+1-\lfloor\log_2(4n+1)\rfloor-v_2(q_n)\}.
\]
However, the existing theorem controlling \(v_2(q_n)\) applies to
certain even indices. It cannot be imported onto the odd \(N_k\)
without a new argument. Simultaneous surviving two-adic and five-adic
precision, even if established, would still leave the decimal-target gap.

## Exact decimal transfer and the missing ordered residue

This paragraph records the consumer boundary, not a new active candidate.
For a prescribed word of length \(\ell\ge1\) and numerical value
\(d\in\{0,\ldots,10^\ell-1\}\), including leading-zero words,
fix an integer shift \(s\ge0\) and put
\[
u_{n,s}=\frac{10^sP_n\bmod Q_n}{Q_n},\qquad
\Delta_{n,s}=10^s\left(\pi-\frac{P_n}{Q_n}\right).
\]
The numerator residue uses the representative in \(\{0,\ldots,Q_n-1\}\).
Exactly,
\[
\{10^s\pi\}=\{u_{n,s}+\Delta_{n,s}\}.
\]
For \(0\le\eta<10^{-\ell}\), either of the following sufficient
conditions gives a literal occurrence of the prescribed word after shift
\(s\):
\[
0\le\Delta_{n,s}\le\eta,\qquad
\frac d{10^\ell}\le u_{n,s}
<\frac{d+1}{10^\ell}-\eta; \tag{10a}
\]
\[
-\eta\le\Delta_{n,s}\le0,\qquad
\frac d{10^\ell}+\eta\le u_{n,s}
<\frac{d+1}{10^\ell}. \tag{10b}
\]
The sum stays inside the required half-open cylinder in \([0,1)\), so
these conditions already handle the potential wrap at zero or one.
Theorems 1–3 do not supply the **ordered**
residue in (10), a suitable shift, or the compatible error sign and size.

### Explicit word-avoider separating the stated arithmetic data

For \(x=4/9=0.444\ldots\), which avoids the digit 0, take any
\(k\ge1\), \(h\ge3\), and \(\sigma\in\{-1,1\}\). Choose a
positive odd integer \(u\) with
\[
9\cdot2^{h-2}u+\sigma\equiv5^k\pmod{5^{k+1}}.
\]
Such a choice exists because the coefficient of \(u\) is a unit
modulo \(5^{k+1}\), and the Chinese remainder theorem also allows
\(u\) to be odd. Define
\[
P=2^h u,\qquad Q=9\cdot2^{h-2}u+\sigma.
\]
Then \(Q\) is positive and odd, \(v_2(P)=h\), and \(v_5(Q)=k\).
Moreover \(4Q-9P=4\sigma\), so \((P,Q)=1\), and
\[
x-\frac PQ=\frac{4\sigma}{9Q}. \tag{11}
\]
For each prescribed \(k,h,\sigma\), increasing \(u\) in the same
odd residue class gives arbitrarily small absolute errors. Thus exact
five-adic denominator depth, arbitrarily deep two-adic numerator
divisibility, approximation from both signs, and convergence do not force
even the occurrence of digit 0.

This separator has error exactly \(4/(9Q)\). It does **not** reproduce
the denominator-relative approximation rate, the recurrence, or the
irrationality of pi. Its role is limited to the listed valuation and sign
data; no stronger separation claim is made.

## Reproduction, review, and source boundary

Run the [standard-library checker](../../../../workflows/experiments/salikhov_forced_divisor_20261016/root_branch.py):

```sh
python3 workflows/experiments/salikhov_forced_divisor_20261016/root_branch.py --terms 2000 --direct 12
python3 workflows/experiments/salikhov_forced_divisor_20261016/root_branch.py --terms 8000 --direct 12 --json workflows/experiments/salikhov_forced_divisor_20261016/certificate.json
```

The tracked [certificate](../../../../workflows/experiments/salikhov_forced_divisor_20261016/certificate.json)
records the exact finite range, all six special indices, normalized unit
residues, and any companion-congruence failures. The checker also verifies
the residue formula independently of the recurrence at \(n=0,\ldots,12\),
the short coefficient identities used in the proof, the scaling
counterexample, and 64 explicit avoider instances. It never evaluates pi
or reads its digits.

The recurrence is the primary
[published Maple output](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt).
That source uses \(E_n=-I_n/5\); its homogeneous recurrence is unchanged,
while its initial values must be multiplied by \(-5\). The exact starting
values used here are
\[
(a_0,b_0)=(0,1/4),\quad
(a_1,b_1)=(-11272/3,1196),\quad
(a_2,b_2)=(-6156093056/105,18662336).
\]
An independent check compared all four degree-nine recurrence polynomials
with the existing full-pair implementation and compared **both** sequences
with its endpoint/coefficient formula at \(n=0,\ldots,12\).

The residue substitution, integrality argument, three unit-index divisions,
Frobenius step, parity cases, and normalization in Theorems 1–2 were reviewed
independently of the finite computation. Their all-index content rests on
those algebraic arguments. The finite table is a validation of (8), whose
proof is supplied separately; all mathematical labels remain as stated
at the top of this note.
