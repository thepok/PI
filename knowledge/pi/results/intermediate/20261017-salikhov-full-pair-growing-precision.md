# Growing five-adic precision for the full Salikhov pair

Date: 2026-10-17. Labels: `proof sketch` and exact `experiment`.
No Lean verification or priority claim. This extends the
[growing multiplier precision theorem](20261016-salikhov-prime-power-absorption.md)
to its rational companion, using the exact endpoint
formula rather than extrapolating the modulo-five automaton.

## Result and scope

Use the normalization of the
[preceding Salikhov source note](20260906-salikhov-mod5-support.md):

\[
I_n=a_n+b_n\pi,\quad q_n=2^{2-\lfloor5n/2\rfloor}b_n\in\mathbb Z,
\quad c_n=2^{2-\lfloor5n/2\rfloor}a_n,
\]
\[
s_n=\lfloor\log_5(4n)\rfloor,\qquad v_n=5^{s_n}c_n\in\mathbb Z_5
\quad(n\ge1).
\]

Retain the explicit precision function from the multiplier theorem:

\[
h_a=\min\{h\ge1:4\cdot5^{h-1}\ge a-1\},\quad D_a=5h_a+100,
\]
\[
a_L=\max\bigl(\{a\ge2:4aD_a\le L\}\cup\{0\}\bigr).
\]

Define

\[
L(M)=\lfloor\log_5M\rfloor,\quad r(M)=\lfloor14L(M)/15\rfloor,
\qquad B(M)=a_{r(M)}.
\]

Then, uniformly in positive integers \(u,d,M\) with \(5\nmid d\),

\[
\boxed{
\#\{0\le j<M:\min(v_5(q_{u+dj}),v_5(v_{u+dj}))<B(M)\}
=O(M^{52/55}).
}
\tag{1}
\]

All implied constants are independent of the progression, including its
offset. The growing precision satisfies

\[
B(M)\sim\frac{7\log M}{150\log\log M}.
\tag{2}
\]

This controls the full normalized pair at common growing precision. It
does **not** control their valuation difference. For the reduced rational
approximant \(-a_n/b_n=P_n/Q_n\), \(Q_n>0\), the exact identity is still

\[
v_5(Q_n)=\max(0,s_n+v_5(q_n)-v_5(v_n)).
\tag{3}
\]

Neither noncancellation nor an ordered decimal residue follows from (1).
No E, CW0, CW9, or V1 conclusion is claimed. The result is a supporting
arithmetic theorem; it does not reopen a closed digit route.

## 1. A whole-numerator prefix controls every required partial fraction

Write

\[
C_{n,j}=[z^nw^{3n-j}]\frac{S_0(w)}{Q(z,w)},\quad
S_0=(2-w)^2,
\]

with the preceding denominator \(Q=D-zF\). In particular,
\(q_n=(-1)^n2^{1-\lfloor5n/2\rfloor}C_{n,0}\).

The [multiplier theorem, Section 6](20261016-salikhov-prime-power-absorption.md#6-growing-precision-and-uniform-arithmetic-progressions)
proves the following stronger fact than its final
scalar-output assertion. At precision \(a=a_r\), outside at most

\[
(100/91)^{D_a}(91/20)^r
\tag{4}
\]

low-digit words of length \(r\), the complete Cartier numerator is zero
modulo \(5^a\) after processing those digits of \((n,3n)\). Every later
section therefore remains zero.

If \(5^r\mid j\) and \(0\le j\le3n\), the first \(r\) digits of
\(3n-j\) and \(3n\) coincide. Their paired coefficient sections have
the same numerator after those \(r\) steps. Thus, for every good prefix,

\[
C_{n,j}\equiv0\pmod{5^a}
\qquad(0\le j\le3n,\ 5^r\mid j).
\tag{5}
\]

The carry after the prefix can differ; this is harmless because the
**whole** numerator is zero. Knowing only the terminal scalar output
\(q_n\equiv0\) would not justify (5).

The [exact companion endpoint formula](20260906-salikhov-mod5-support.md#full-rational-companion-and-local-pair) is

\[
a_n=(-1)^{n+1}\sum_{j=1}^{3n}\frac{C_{n,j}E_j}{j}
 +5\sum_{k=0}^{2n-1}\frac{D_{n,k}J_{4n-1-2k}}{4n-1-2k},
\tag{6}
\]

where

\[
D_{n,k}=[y^k]\frac{(1+6y+25y^2)^{2n}}{(1-25y)^{3n+1}},
\]
\[
E_j=i\left[((2+i)/2)^j-((2-i)/2)^j
             +((3+i)/4)^j-((3-i)/4)^j\right],
\qquad J_j=i\left[(-1+2i)^j-(-1-2i)^j\right].
\]

All \(C_{n,j}\), \(E_j\), and \(J_j\) are five-adically integral.
Assume

\[
s_n\ge r+a-1.
\tag{7}
\]

For a partial-fraction denominator \(j\) not divisible by \(5^r\),
the factor \(5^{s_n}/j\) already has valuation at least \(a\).
For \(5^r\mid j\), (5) supplies the required precision, since
\(v_5(j)\le s_n\). Hence the normalized first sum in (6) vanishes
modulo \(5^a\).

## 2. The polynomial endpoint contribution: a long window of Kummer borrows

The polynomial term cannot simply be omitted at higher precision. For
example, at \(n=1536\) it contributes 25 modulo 125 to \(v_n\).

For an odd \(j\) with \(1\le j\le4n-1\), put
\(k=(4n-1-j)/2\). Expand by the number \(u\) of quadratic numerator
terms and the number \(v\) of denominator terms. The exact coefficient
formula is

\[
D_{n,k}=\sum_{u,v\ge0}25^{u+v}
 \binom{2n}{u}\binom{2n-u}{(j+1)/2+u+v}
 6^{k-2u-v}\binom{3n+v}{v}.
\tag{8}
\]

Only terms with \(u\le2n\) and \(0\le k-2u-v\le2n-u\) are
included. This convention keeps every exponent nonnegative. Formula (8)
follows directly from the multinomial and negative-binomial expansions;
the second binomial was written using its complementary lower index.

Modulo \(5^a\), all terms with \(2(u+v)\ge a\) vanish. Set

\[
H=\min\{h\ge1:5^h>a\}.
\]

Suppose \(5^r\mid j\), with \(r>H\). Since \(j\) is odd,

\[
\frac{j+1}{2}\equiv\frac{5^r+1}{2}\pmod{5^r}.
\]

The residue on the right has base-five digits 3 at position zero and 2
at every position from 1 to \(r-1\). Adding
\(u+v\le\lfloor(a-1)/2\rfloor\) does not carry into position \(H\),
because

\[
\frac{5^H+1}{2}+u+v\le\frac{5^H+a}{2}<5^H.
\]

Consequently the lower index in (8) has digit 2 at every position
\(H,\ldots,r-1\), independently of \(j\), \(u\), and \(v\).

In subtracting this index from \(2n-u\), each position in that window
where \(2n-u\) has digit 0 or 1 causes an outgoing borrow, regardless
of the incoming borrow. The factorial valuation formula

\[
v_5\binom NK=\sum_{t\ge1}
 \left(\left\lfloor\frac N{5^t}\right\rfloor
 -\left\lfloor\frac K{5^t}\right\rfloor
 -\left\lfloor\frac{N-K}{5^t}\right\rfloor\right)
\]

counts these borrows. Thus the following finite digit condition suffices:

> For every \(0\le u\le\lfloor(a-1)/2\rfloor\), the digits of
> \(2n-u\) in positions \(H,\ldots,r-1\) include at least \(a\)
> entries from \(\{0,1\}\).

Under this condition, each surviving second binomial in (8) is divisible
by \(5^a\), so

\[
D_{n,(4n-1-j)/2}\equiv0\pmod{5^a}
\quad(5^r\mid j,\ j\text{ odd},\ 1\le j<4n).
\tag{9}
\]

If \(5^r\nmid j\), (7) makes the normalized endpoint factor
\(5^{s_n+1}/j\) divisible by \(5^{a+1}\). If \(5^r\mid j\), use
(9) and \(v_5(j)\le s_n\). The normalized polynomial sum in (6)
therefore also vanishes modulo \(5^a\).

## 3. Uniform counting on every progression coprime to five

Let \(L=\lfloor\log_5M\rfloor\), \(r=\lfloor14L/15\rfloor\), and
\(a=a_r\). The assertion is trivial when \(a=0\). In the asymptotic
range, \(a=O(L/\log L)\) and \(H=O(\log L)\).

There are three exceptional sets.

First, violation of (7) implies
\(4n<5^{r+a-1}\). Any positive increasing integral progression contains
at most \(5^{r+a-1}\) such values, uniformly in its offset and step.
This is \(M^{14/15+o(1)}\).

Second, every residue modulo \(5^r\) occurs in a progression of length
\(M\) and step coprime to five at most
\(\lceil M/5^r\rceil\le2M/5^r\) times. Multiplying (4) by this
factor bounds the failed Cartier prefixes by

\[
2M(100/91)^{D_a}(91/100)^r
=M^{\delta_*+o(1)},
\quad
\delta_*:=\frac1{15}+\frac{14}{15}\log_5(91/20)<\frac{52}{55}.
\tag{10}
\]

The strict inequality follows from the exact integer comparison
\(91^{154}<20^{154}5^{145}\).

Third, fix one \(u\) in the digit condition. Multiplication by two and
translation by \(-u\) permute residues modulo \(5^r\). With
\(R=r-H\), there are exactly

\[
5^H\sum_{i=0}^{a-1}\binom Ri 2^i3^{R-i}
\tag{11}
\]

bad residues, with the sum truncated at \(i=R\) if necessary. Since
\(a=o(R)\), the sum is \(3^{R+o(R)}\). For example, the standard
bound \(\sum_{i\le a}\binom Ri\le(eR/a)^a\), together with
\(a\log(R/a)=o(R)\), gives this directly. A union bound over at most
\(a\) values of \(u\), and the same residue multiplicity, gives

\[
M^{\,1-(14/15)(1-\log_5 3)+o(1)}.
\tag{12}
\]

The exact inequality \(3^{10}<5^7\) puts the fixed exponent below
\(18/25\). All three exponents are strictly below \(52/55\), so
their \(o(1)\) losses are absorbed by this fixed gap. This proves (1)
with one constant independent of \(u,d,M\). Formula (2) follows from
the already proved asymptotic for \(a_L\).

## 4. Consequences for the binary entropy family and both actual-pi signs

Let

\[
\mathcal G=\{2^km:k\ge2,\ m\text{ odd},\ s_2(3m)\le k\},
\qquad \gamma=\log_2\frac{1+\sqrt5}{2}.
\]

The [previous entropy theorem](20261016-salikhov-entropy-family.md)
gives \(\#(\mathcal G\cap[1,N])\asymp
N^\gamma\). Put

\[
\eta=\frac{11}{15}H_2(4/11)<\gamma,
\]

where \(H_2\) is binary entropy. Then

\[
\#\left\{n\in\mathcal G\cap[1,N]:
 \min(v_5(q_n),v_5(v_n))<B(\lfloor\sqrt N\rfloor)\right\}
=O(N^\eta).
\tag{13}
\]

For completeness, take \(L_2=\lfloor\log_2(3N)\rfloor\), split at
\(K=\lfloor4L_2/15\rfloor\) and \(J=\lfloor2L_2/5\rfloor\).
For \(k\le K\), the same Bernoulli tilt as in the entropy theorem,
with parameter \(4/11\), bounds all candidate binary words by a
geometric sum with terms \((11/7)^{L_2+1}(49/44)^k\). Its order is
\(N^\eta\). For \(K<k\le J\), the odd-multiplier progression has
length comparable to \(N/2^k\), exceeding \(\sqrt N\) eventually.
Use (1) at that length and monotonicity of \(B\), then sum
geometrically to obtain \(O(N^{52/75})\). The inequality
\(52/55<H_2(4/11)\) follows from \(11^{55}>4^{20}7^{35}2^{52}\), so this
is smaller than \(O(N^\eta)\). For \(k>J\), all indices together
number \(O(N^{3/5})\). Finally \(H_2(t)/(1+t)\) is strictly
increasing up to \(p=(3-\sqrt5)/2>4/11\), where its maximum is
\(\gamma\), proving \(\eta<\gamma\).

On the computable good blocks from the entropy theorem, with
\(\ell_k=\lfloor k/p\rfloor\), \(N_k=2^{k+\ell_k}\), each actual-pi
sign retains

\[
\#\{n\in\mathcal G_k^*:
 v_5(q_n),v_5(v_n)\ge B(2^{\ell_k}),\ \sigma(\pi-P_n/Q_n)>0\}
\gg\frac{N_k^\gamma}{\sqrt{\log N_k}}.
\tag{14}
\]

Apply (1) to the super-progression
\(n=2^k(1+2j)\), \(0\le j<2^{\ell_k}\), which contains the entire
block and has length exactly \(2^{\ell_k}\) and step \(2^{k+1}\).
This justifies the literal threshold \(B(2^{\ell_k})\), including its
jumps. Formula (1) deletes only \(O(2^{52\ell_k/55})\) indices,
whereas each fixed-margin sign
core has order \(2^{H_2(p)\ell_k}/\sqrt{\ell_k}\), and
\(52/55<H_2(4/11)<H_2(p)\). The
[preceding sign proof](20261016-salikhov-entropy-family.md#reserving-six-low-bits)
gives the strict lower limit \(p^5(1-2p)>1/1000\) for each sign's
fraction; its rational lower bound is \(243/163840>1/1000\).
Deleting \(o(\text{core})\) indices therefore preserves the same eventual
proportion \(1/1000\). Every retained index still has

\[
Q_n\text{ odd},\qquad
v_2(P_n)\ge2n-1-2\lfloor\log_2n\rfloor.
\]

The actual-pi signed asymptotic is inherited unchanged from the entropy
theorem; this new argument supplies only additional local precision.
The sign premise fails for the explicit replacement constant \(4/9\),
because \(4/9-P_n/Q_n\) is eventually negative. That separation still
does not turn an adaptive approximation sign into a prescribed decimal hit.

## Verification and the remaining cancellation issue

[joint_precision.py](../../../../workflows/experiments/salikhov_joint_precision_20261017/joint_precision.py)
evaluates the pair at an arbitrary positive index,
modulo a fixed \(5^a\). The partial-fraction coefficients use the tracked
bounded Cartier engine. Terms outside the relevant five-adic denominator
shells are omitted using their proven valuation. Formula (8) evaluates
the polynomial part with only \(u+v<a/2\). Factorial-unit products
compute binomial coefficients modulo \(5^a\) without constructing
factorials or full binomial coefficients of a large index.

The [recorded exact experiment](../../../../workflows/experiments/salikhov_joint_precision_20261017/certificate.json)
checks both coordinates against the
published rational recurrence modulo 125 through \(n=45\), and at
\(n=1072,1536,2000\). It separately compares the polynomial coefficient
formula with direct coefficient expansion for \(n\le15\), and modular
binomials with exact binomials for \(n<100\). The complete entropy-family
census through \(n=2000\) has 104 members:

| Valuation comparison | Count |
|---|---:|
| \(v_5(q_n)=v_5(v_n)\) | 75 |
| \(v_5(v_n)>v_5(q_n)\) | 27 |
| \(v_5(q_n)>v_5(v_n)\) | 2 |

The two last cases are \(n=1072\), with valuations \((4,2)\), and
\(n=1536\), with valuations \((3,1)\). Both have \(s_n=5\) and
\(v_5(Q_n)=7\). At \(n=1536\), the partial-fraction and polynomial
contributions to \(v_n\bmod125\) are respectively 95 and 25.

Thus the valuation difference takes both signs already on the arithmetic
family of interest. In particular, neither \(v_5(v_n)\ge v_5(q_n)\)
nor the reverse inequality can be silently added to (1). A growing
precision theorem for that difference, a nonzero reduced unit class,
other denominator primes, and ordered decimal residues remain open here.

The finite checks are `experiment`; the infinite argument above is a
`proof sketch`, conditional only on the explicitly cited preceding
coefficient, Cartier-absorption, binary, and signed-asymptotic results.

From the repository root, reproduce the certificate with:

```sh
python3 workflows/experiments/salikhov_joint_precision_20261017/joint_precision.py --check 45 --samples 1072 1536 2000 --json workflows/experiments/salikhov_joint_precision_20261017/certificate.json
```

The original integral and recurrence are from
[Zeilberger–Zudilin, arXiv:1912.06345v2](https://arxiv.org/html/1912.06345v2)
and their
[exact recurrence output](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt).
