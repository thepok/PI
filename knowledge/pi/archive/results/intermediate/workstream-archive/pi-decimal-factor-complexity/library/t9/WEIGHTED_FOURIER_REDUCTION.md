# T9: A weighted Fourier target for pi's lacunary near returns

Status: `proof sketch` (a self-contained paper proof of a conditional
implication; not machine-checked).

## Scope and immutable source

The canonical source is
`knowledge/pi/statements/pi-decimal-factor-complexity.txt`, SHA-256

```text
e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43
```

The canonical question A1 asks whether the factor complexity of the
fractional decimal digit stream of pi satisfies

\[
  (\forall C>0)(\exists n_0\geq 1)(\forall n\geq n_0)\quad
  p_\pi(n)>Cn.
\]

This note does **not** prove A1. It concerns the strictly stronger sufficient
sibling C2 defined in the accepted T8 artifact
`../knowledge_library/t8/PiLacunaryNearReturns.lean`, SHA-256

```text
324478887e8504d8086a9cedc6e640fe415491849e6391b63d1ec3fb10f596d8
```

Specifically, this note imports the following T8 conventions without changing
them:

- Lines 11--15: starts are zero-based, `Fin N` means the starts
  \(0,\ldots,N-1\), pairs are ordered, and diagonal pairs are included.
- Lines 35--38: circle distance is distance to the nearest integer.
- Lines 92--104: \(Q_\pi(n,N)\) counts exactly the ordered pairs
  \(0\leq i,j<N\) for which
  \[
    \left\|(10^j-10^i)\pi\right\|_{\mathbb R/\mathbb Z}<10^{-n}.
  \]
- Lines 178--186: C2 is exactly
  \[
  (\forall C\in\mathbb R)(C>0\Rightarrow
  (\exists n_0\in\mathbb N)(n_0\geq1\ \wedge
  (\forall n\in\mathbb N)(n\geq n_0\Rightarrow
  (\exists N\in\mathbb N)(N\geq1\ \wedge
  Q_\pi(n,N)<N^2/(Cn))))).
  \tag{C2}
  \]
  All quantities in the last inequality are coerced to reals.

T8 machine-checks only the implications C2 \(\Rightarrow\) C1
\(\Rightarrow\) A1. C2 itself is unproved for pi.

## Normalized T9 statement

For \(t\in\mathbb R\), put

\[
  e(t):=\exp(2\pi\mathrm{i}t),\qquad
  \|t\|_{\mathbb T}:=\inf_{k\in\mathbb Z}|t-k|,
  \qquad \mathbb T:=\mathbb R/\mathbb Z.
\]

For an integer \(h\) and \(N\in\mathbb N\), define the unnormalized
lacunary exponential sum

\[
  S_h(N):=\sum_{0\leq i<N}e(h10^i\pi)
  =\sum_{0\leq i<N}\exp(2\pi\mathrm{i}\,h10^i\pi).
  \tag{1}
\]

The two occurrences of \(\pi\) in the last expression have different roles:
the first is part of the Fourier phase \(2\pi\mathrm{i}\), while the second is
the number whose decimal orbit is sampled.

We will construct, for every \(n\geq1\) and \(H\geq1\), an explicit real,
even trigonometric polynomial

\[
  M_{n,H}(x)=\sum_{|h|\leq H}c_h e(hx)
\]

such that

\[
  \mathbf 1_{\{\|x\|_{\mathbb T}<10^{-n}\}}\leq M_{n,H}(x)
  \quad\hbox{for every }x\in\mathbb T.                 \tag{2}
\]

No endpoint convention is hidden in (2): the set on the left is open, while
the majorization established below also holds at its interior points. Values
on the boundary are irrelevant to the application because T8 uses a strict
inequality.

## Elementary Fejer majorant

All integrals below use normalized Haar measure on \(\mathbb T\), represented
by Lebesgue measure on any interval of length one. For \(0\leq r<1/2\), write

\[
  I_r:=\{x\in\mathbb T:\|x\|_{\mathbb T}\leq r\}.
\]

Thus \(I_r\) is represented by \([-r,r]\) and has measure \(2r\).

Fix \(H\geq1\). Define

\[
\begin{aligned}
  K_H(t)
  &:=\frac1{H+1}\left|\sum_{r=0}^{H}e(rt)\right|^2,\\
  \eta_H&:=\frac1{2(H+1)},\\
  m_H&:=\int_{I_{\eta_H}}K_H(t)\,dt.
\end{aligned}                                                   \tag{3}
\]

Expanding the square in (3) gives, with no convergence issue because all sums
are finite,

\[
\begin{aligned}
 K_H(t)
 &=\frac1{H+1}\sum_{r=0}^{H}\sum_{s=0}^{H}e((r-s)t)\\
 &=\sum_{|h|\leq H}\left(1-\frac{|h|}{H+1}\right)e(ht).          \tag{4}
\end{aligned}
\]

Indeed, for each integer \(h\) with \(|h|\leq H\), exactly
\(H+1-|h|\) pairs \((r,s)\in\{0,\ldots,H\}^2\) satisfy \(r-s=h\).
The definition in (3) also shows directly that

\[
  K_H(t)\geq0.                                                    \tag{5}
\]

### A lower bound for the normalizing mass

For \(0<|t|\leq\eta_H\), the finite geometric-series identity gives

\[
  K_H(t)=\frac1{H+1}
  \left(\frac{\sin(\pi(H+1)t)}{\sin(\pi t)}\right)^2.             \tag{6}
\]

We use only the elementary inequalities

\[
 |\sin u|\geq \frac{2|u|}{\pi}\quad(|u|\leq\pi/2),
 \qquad |\sin v|\leq |v|\quad(v\in\mathbb R).                   \tag{7}
\]

For completeness, the first inequality follows because \(\sin u\) is
concave on \([0,\pi/2]\) and therefore lies above the chord joining
\((0,0)\) to \((\pi/2,1)\), followed by oddness. The second follows from the
mean-value theorem and \(|\cos v|\leq1\).

Since \(0<|t|\leq\eta_H\leq1/4\), the denominator in (6) is nonzero.
Also \(\pi(H+1)|t|\leq\pi/2\), so (6) and (7) imply

\[
\begin{aligned}
 K_H(t)
 &\geq\frac1{H+1}
   \left(\frac{2(H+1)|t|}{\pi|t|}\right)^2
  =\frac{4(H+1)}{\pi^2}.                                        \tag{8}
\end{aligned}
\]

At \(t=0\), the definition gives \(K_H(0)=H+1\), so (8) also holds
there. The interval \(I_{\eta_H}\) has length
\(2\eta_H=1/(H+1)\). Integrating (8) therefore yields the explicit bound

\[
  m_H\geq\frac4{\pi^2}>0,
  \qquad \frac1{m_H}\leq\frac{\pi^2}{4}.                         \tag{9}
\]

### Definition and pointwise verification

Fix \(n\geq1\), and set

\[
  \delta_n:=10^{-n},\qquad a_{n,H}:=\delta_n+\eta_H.              \tag{10}
\]

Because \(\delta_n\leq1/10\) and \(\eta_H\leq1/4\), we have
\(a_{n,H}\leq7/20<1/2\). Hence all three arcs
\(I_{\delta_n},I_{\eta_H},I_{a_{n,H}}\) have the unambiguous interval
representatives used above. Define

\[
  M_{n,H}(x):=\frac1{m_H}\int_{I_{a_{n,H}}}K_H(x-y)\,dy.          \tag{11}
\]

This function is nonnegative by (5) and (9). Suppose
\(\|x\|_{\mathbb T}<\delta_n\). For every
\(t\in I_{\eta_H}\), the circle triangle inequality gives

\[
  \|x-t\|_{\mathbb T}
  \leq\|x\|_{\mathbb T}+\|t\|_{\mathbb T}
  <\delta_n+\eta_H=a_{n,H}.
\]

Thus \(x-I_{\eta_H}\subseteq I_{a_{n,H}}\). Restricting the nonnegative
integral in (11) to this translated arc and substituting \(t=x-y\) gives

\[
  M_{n,H}(x)
  \geq\frac1{m_H}\int_{x-I_{\eta_H}}K_H(x-y)\,dy
  =\frac1{m_H}\int_{I_{\eta_H}}K_H(t)\,dt
  =1.                                                            \tag{12}
\]

If \(\|x\|_{\mathbb T}\geq\delta_n\), the indicator in (2) is zero and
the nonnegativity of \(M_{n,H}\) proves (2). This verifies the pointwise
majorant everywhere on the circle.

## Exact coefficients and their bounds

Insert (4) into (11) and interchange a finite sum and the integral. For
\(|h|\leq H\), the coefficient of \(e(hx)\) is

\[
  c_h=\frac1{m_H}\left(1-\frac{|h|}{H+1}\right)
      \int_{-a_{n,H}}^{a_{n,H}}e(-hy)\,dy.                       \tag{13}
\]

Consequently

\[
  c_0=\frac{2a_{n,H}}{m_H},                                      \tag{14}
\]

and, for \(0<|h|\leq H\),

\[
  c_h=\frac1{m_H}\left(1-\frac{|h|}{H+1}\right)
      \frac{\sin(2\pi h a_{n,H})}{\pi h}.                       \tag{15}
\]

For \(|h|>H\), \(c_h=0\). Formulas (14)--(15) show that every \(c_h\) is
real and \(c_{-h}=c_h\), so \(M_{n,H}\) is a real, even trigonometric
polynomial of degree at most \(H\).

By (9), (10), and (14),

\[
\begin{aligned}
  c_0
  &\leq\frac{\pi^2}{4}(2\delta_n+2\eta_H)\\
  &=\frac{\pi^2}{2}10^{-n}+\frac{\pi^2}{4(H+1)}.                \tag{16}
\end{aligned}
\]

For nonzero \(h\), the two bounds
\(|\sin u|\leq|u|\) and \(|\sin u|\leq1\) give

\[
 \left|\frac{\sin(2\pi h a_{n,H})}{\pi h}\right|
 \leq \min\left(2a_{n,H},\frac1{\pi|h|}\right).                \tag{17}
\]

Using also \(0\leq1-|h|/(H+1)\leq1\), equations (9), (10), (15), and
(17) give, coefficient by coefficient,

\[
 |c_h|\leq\frac{\pi^2}{4}
 \min\left(2\cdot10^{-n}+\frac1{H+1},\frac1{\pi|h|}\right)
 \quad(0<|h|\leq H).                                            \tag{18}
\]

This completes the explicit construction and all coefficient bounds without
invoking an external majorant theorem.

## Ordered-pair summation identity

Let

\[
  x_i:=10^i\pi\pmod 1\qquad(0\leq i<N).
\]

T8's definition of \(Q_\pi\) is exactly

\[
 Q_\pi(n,N)=\sum_{0\leq i,j<N}
 \mathbf 1_{\{\|x_j-x_i\|_{\mathbb T}<10^{-n}\}}.               \tag{19}
\]

This is a sum over all \(N^2\) ordered pairs. In particular, it includes the
\(N\) diagonal pairs, each of which satisfies the strict near-return
condition because \(0<10^{-n}\).

Apply (2) to each term of (19) and then use the finite Fourier expansion:

\[
\begin{aligned}
 Q_\pi(n,N)
 &\leq\sum_{0\leq i,j<N}M_{n,H}(x_j-x_i)\\
 &=\sum_{|h|\leq H}c_h
   \sum_{0\leq i,j<N}e(h(x_j-x_i)).                              \tag{20}
\end{aligned}
\]

For each integer \(h\), the inner ordered-pair sum factors exactly as

\[
\begin{aligned}
 \sum_{0\leq i,j<N}e(h(x_j-x_i))
 &=\left(\sum_{0\leq j<N}e(hx_j)\right)
   \left(\sum_{0\leq i<N}e(-hx_i)\right)\\
 &=S_h(N)\,\overline{S_h(N)}\\
 &=|S_h(N)|^2.                                                    \tag{21}
\end{aligned}
\]

The second equality uses \(e(-t)=\overline{e(t)}\). Notice that (21) is for
ordered pairs; no factor of two has been inserted or removed. Since
\(S_0(N)=N\), \(c_{-h}=c_h\), and
\(|S_{-h}(N)|=|S_h(N)|\), equations (20)--(21) give first the exact identity
for the majorant sum and then an upper bound:

\[
\begin{aligned}
 \sum_{0\leq i,j<N}M_{n,H}(x_j-x_i)
 &=c_0N^2+2\sum_{h=1}^{H}c_h|S_h(N)|^2,                          \tag{22}\\
 Q_\pi(n,N)
 &\leq c_0N^2+2\sum_{h=1}^{H}|c_h|\,|S_h(N)|^2.                 \tag{23}
\end{aligned}
\]

The absolute values in (23) are necessary because the coefficients in (15)
need not be nonnegative.

Define the weighted energy

\[
 W_{n,H}(N):=\sum_{h=1}^{H}
 \min\left(2\cdot10^{-n}+\frac1{H+1},\frac1{\pi h}\right)
 |S_h(N)|^2.                                                      \tag{24}
\]

Combining (16), (18), and (23) proves the fully explicit bound

\[
 \boxed{
 Q_\pi(n,N)\leq
 \left(\frac{\pi^2}{2}10^{-n}+\frac{\pi^2}{4(H+1)}\right)N^2
 +\frac{\pi^2}{2}W_{n,H}(N)
 }
 \quad(n,H\geq1,\ N\geq0).                                     \tag{25}
\]

For \(N=0\), both sides are zero. C2 only uses \(N\geq1\).

## The weighted Fourier-energy hypothesis

For \(A>0\) and \(n\geq1\), let

\[
  H_A(n):=\lceil An\rceil.
\]

Because \(An>0\), this is a positive integer. Consider the following
pi-specific hypothesis:

**Weighted Fourier-energy hypothesis HFE(pi).** For every real \(A>0\) and
every real \(\varepsilon>0\), there is an integer \(n_*\geq1\) such that for
every integer \(n\geq n_*\), there is an integer \(N\geq1\) satisfying

\[
 W_{n,H_A(n)}(N)<\varepsilon\frac{N^2}{n}.                       \tag{26}
\]

In fully displayed quantifier order, HFE(pi) is

\[
 (\forall A\in\mathbb R)(A>0\Rightarrow
 (\forall\varepsilon\in\mathbb R)(\varepsilon>0\Rightarrow
 (\exists n_*\in\mathbb N)(n_*\geq1\ \wedge
 (\forall n\in\mathbb N)(n\geq n_*\Rightarrow
 (\exists N\in\mathbb N)(N\geq1\ \wedge (26)))))).            \tag{27}
\]

The sample size \(N\) in (26) may depend on \(A\), \(\varepsilon\), and
\(n\). This existential dependence is essential and agrees with C2; no
single \(N\) is asserted to work for all sufficiently large \(n\).

HFE(pi) is a natural cancellation target in the following limited sense. The
weights in (24) are exactly the coefficient bounds forced by the explicit
hard-interval majorant, \(H_A(n)\) gives linearly many frequencies, and (26)
asks their weighted energy to be \(o(N^2/n)\) along at least one finite sample
size at each sufficiently large \(n\). This description is motivational, not
evidence that pi satisfies the hypothesis.

## Quantified implication HFE(pi) => C2

Assume HFE(pi). We prove C2 with its quantifiers unchanged.

Let \(C\in\mathbb R\) satisfy \(C>0\). Choose explicitly

\[
  A:=\pi^2C+1>\pi^2C,
  \qquad \varepsilon:=\frac1{\pi^2C}>0.                          \tag{28}
\]

Apply HFE(pi) with these \(A\) and \(\varepsilon\), obtaining
\(n_*\geq1\) as in (27).

There is also an integer \(n_{\rm exp}\geq1\) such that

\[
  2\pi^2C\,n10^{-n}<1\qquad(n\geq n_{\rm exp}).                 \tag{29}
\]

Here is an elementary verification of this eventual assertion. Induction
gives \(n\leq5^n\) for every \(n\geq1\): it is true at \(n=1\), and
\(n+1\leq5n\leq5^{n+1}\). Hence \(n10^{-n}\leq2^{-n}\). Choose
\(n_{\rm exp}\) so large that \(2^{n_{\rm exp}}>2\pi^2C\); such an integer
exists because the powers of \(2\) are unbounded. For
\(n\geq n_{\rm exp}\), this gives (29).

Set

\[
  n_0:=\max(n_*,n_{\rm exp}).                                   \tag{30}
\]

Then \(n_0\geq1\). Let an arbitrary integer \(n\geq n_0\) be given. By
HFE(pi), there is an integer \(N\geq1\) such that

\[
 W_{n,H_A(n)}(N)<\frac1{\pi^2C}\frac{N^2}{n}.                   \tag{31}
\]

Put \(H=H_A(n)\). We bound the three terms on the right of (25).
First, (29) rearranges to

\[
  \frac{\pi^2}{2}10^{-n}N^2<\frac{N^2}{4Cn}.                    \tag{32}
\]

Second, \(H+1>An\), and \(A>\pi^2C\), so

\[
  \frac{\pi^2}{4(H+1)}N^2
  <\frac{\pi^2}{4An}N^2
  <\frac{N^2}{4Cn}.                                              \tag{33}
\]

Third, (31) gives

\[
  \frac{\pi^2}{2}W_{n,H}(N)
  <\frac{N^2}{2Cn}.                                              \tag{34}
\]

Substituting (32)--(34) into (25) yields

\[
  Q_\pi(n,N)
  <\left(\frac14+\frac14+\frac12\right)\frac{N^2}{Cn}
  =\frac{N^2}{Cn}.                                               \tag{35}
\]

We began with arbitrary \(C>0\), constructed \(n_0\geq1\), and for every
arbitrary \(n\geq n_0\) produced an \(N\geq1\) satisfying (35). Therefore
(27) implies exactly C2, including its eventual-\(n\) and existential-\(N\)
quantifiers.

## What remains unproved

HFE(pi) is **unproved for pi**. This note proves only the conditional
implication

\[
  \mathrm{HFE}(\pi)\Longrightarrow\mathrm{C2}.
\]

It does not establish HFE(pi), C2, C1, or canonical A1. In particular, T8's
machine-checked chain C2 \(\Rightarrow\) C1 \(\Rightarrow\) A1 cannot be
invoked unconditionally from this note.

## Source and dependency audit

No external majorant theorem is used. Equations (3)--(18) derive the
majorant, its pointwise property, and every coefficient bound directly from a
finite geometric sum and the elementary sine inequalities proved or justified
above.

Before choosing this construction, the local formal library was searched for
Fejer-kernel infrastructure. The related file
`TheoryLib/PiDigits/T27FiniteExponentialCylinderCoverage.lean`, SHA-256
`fd9c730e411dd7fb12b5b1a103c683238595c68bbea0f06af0250b4d13a8ee4e`,
defines a normalized Fejer kernel at lines 24--39 and proves elementary
nonnegativity and finite-sum identities at lines 83--145. It addresses a
different decimal-cylinder estimate and is not invoked here. The accepted T8
artifact identified above is the sole imported mathematical dependency.

## Ambiguities resolved

- This concerns sibling C2, not canonical A1 and not sibling C1.
- Starts are \(0,\ldots,N-1\), corresponding in T8 to the first \(N\)
  fractional-digit starts; the integer digit \(3\) is not a start.
- Pairs are ordered and include diagonals.
- Circle intervals and circle distance are modulo one.
- The near-return interval is open, exactly as in T8.
- \(H_A(n)=\lceil An\rceil\) is chosen after \(A\) and \(n\); the sample size
  \(N\) may depend on \(A,\varepsilon,n\).
- The finite Fourier identity is exact for the majorant sum. Only the first
  comparison from \(Q_\pi\) to that sum is an inequality.
