# BBP one-character return: an exact rational recurrence and a sharp Fourier alternative

Audit date: **2026-08-13 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Normalized statement and quantifier boundary

Canonical V1 asks: for every length \(m\ge0\) and every word
\((d_1,\ldots,d_m)\in\{0,\ldots,9\}^m\), there is a position \(n\ge0\) at which
the next \(m\) decimal digits of pi are exactly that word.  The occurrence is
contiguous, leading zeroes are allowed, and the empty word is vacuous.  Pi is
irrational, so its decimal expansion has no terminating-expansion ambiguity.

The source's “any sequence” also admitted two noncanonical readings: every
infinite word as a contiguous tail (false), and every infinite word as a
subsequence (equivalent to every digit recurring infinitely often, and
open).  This report addresses only finite contiguous words, V1.  Its fixed
return has quantifiers

\[
 \forall\epsilon>0\ \exists n\ge0:\quad
 \|(10^n-16)\pi\|_{\mathbb T}<\epsilon,
\]

not a finite cutoff, an almost-everywhere statement, or a two-parameter
Furstenberg orbit.

## Outcome and claim status

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained.  Canonical V1 remains a `conjecture`.

This branch replaces the earlier all-frequency BBP targets by one exact
pointwise character recurrence.  Its main conclusions have status `proof
sketch`.

1. If \(B_n\) is the \(n\)-th rational BBP partial sum and
   \(R_n=(10^n-16)B_n\), then V1 is equivalent to

   \[
      \limsup_{n\to\infty}\Re e(R_n)=1,
      \qquad e(x)=\exp(2\pi i x).                     \tag{1}
   \]

   Thus the exact remaining target is one pointwise Fourier character of one
   explicit rational sequence.  No Cesaro limit, all-frequency Weyl
   criterion, or moving CRT decomposition is needed for this equivalence.
2. The pair of roots of unity

   \[
      V_n=e(B_n),\qquad Z_n=e(R_n)
   \]

   starts at \(V_0=e(47/15)\), \(Z_0=1\), and obeys a closed
   coefficient-specific recurrence displayed in (12).  Therefore (1) is a
   finite-dimensional rational-forcing problem with no unevaluated pi in its
   definition.
3. Averaging over the full BBP triangle \((M,n)\), rather than a fixed row,
   produces no new coefficient-specific phase.  Exact reindexing turns the
   average into a tent-multiplicity weighting of the actual decimal phases,
   with total normalized BBP error \(O_h(\log K/K^2)\).  Across a fixed
   column the complete four-pole carry moves through an arc of only
   \(O_h(M^{-2})\); it reinforces the multiplicity instead of creating a
   transverse cancellation mechanism.
4. A 2026 theorem of Chen--Ye--Zheng applies to the limiting affine phase
   \(X_n=(10^n-16)\pi\).  It proves unconditionally that its limit set is
   infinite, that

   \[
                         \limsup_n\|X_n\|_{\mathbb T}\ge {1\over22}, \tag{2}
   \]

   and that every modulus \(M\) has a residue-class subsequence whose limit
   set is not contained in any circle interval of length \(<1/10\).  The BBP
   rational phases \(R_n\) have exactly the same conclusions.  The constants
   \(1/22\) and \(1/10\) are optimal only within that source theorem's
   respective \(L\)- and \(\lambda\)-length interfaces, not as global
   dispersion constants.  This is a genuine unconditional dispersion result,
   but it controls the **limsup**, whereas V1 needs the **liminf** to be zero.
5. If the return fails with a positive gap, an elementary Fejer argument
   forces one fixed low power \(Z_n^h\) to retain a quantitative negative
   Cesaro bias along a subsequence.  The exact power-of-ten shift identity
   propagates its magnitude along the entire frequency ray
   \(h,10h,10^2h,\ldots\).  This gives a sharp falsifiable alternative for the
   recurrence; it does not rule the alternative out.
6. The decimal Kempner--Fredholm number preserves rational roots of unity,
   transcendence, optimal irrationality exponent two, exponentially
   accurate rational diagonal shadows, positive rational forcing converging
   exponentially to \(144\kappa\), while its
   complete fixed-sixteen orbit stays more than \(2/9\) from zero.  Hence the
   remaining proof must use the exact four-pole coefficient sequence, not
   only the architecture of the recurrence.

The bounded source audit is `literature-checked` as of the displayed date.
The companion replay is an `experiment`.  Nothing in this report is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Normalized target and the diagonal BBP shadow

Put

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 b_k={a(k)\over16^k},\qquad
 B_n=\sum_{k=0}^n b_k.                              \tag{3}
\]

The exact positive BBP tail estimate is

\[
       0<\pi-B_n\le {16^{-n}\over15(n+1)^2}.         \tag{4}
\]

Let

\[
 q_n=10^n-16,\qquad
 X_n=q_n\pi,\qquad
 R_n=q_nB_n.                                        \tag{5}
\]

For \(n\ge2\), (4) gives

\[
  0<X_n-R_n=q_n(\pi-B_n)
  \le { (5/8)^n\over15(n+1)^2}=:\varepsilon_n.      \tag{6}
\]

The circle norm is \(1\)-Lipschitz, so

\[
 \left|\|X_n\|_{\mathbb T}-\|R_n\|_{\mathbb T}\right|
 \le\varepsilon_n\longrightarrow0.                 \tag{7}
\]

The audited Furstenberg bridge gives

\[
 \mathrm{V1}
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\|X_n\|_{\mathbb T}=0.
                                                               \tag{8}
\]

Combining (7)--(8) produces the fully rational diagonal criterion

\[
 \boxed{
 \mathrm{V1}
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\|R_n\|_{\mathbb T}=0.}       \tag{9}
\]

This resembles the diagonal statement already implicit in the BBP bridge,
but the next section makes it a closed one-character recurrence rather than
a family of moving reduced numerators.

## 2. Exact rational and root-of-unity recurrences

The two elementary identities

\[
       B_{n+1}=B_n+b_{n+1},\qquad
       q_{n+1}=10q_n+144                              \tag{10}
\]

give

\[
 \boxed{
 R_{n+1}=10R_n+G_{n+1},\qquad
 G_{n+1}=144B_n+q_{n+1}b_{n+1}.}                    \tag{11}
\]

Every entry in (11) is rational and is determined by (3).  In particular,

\[
 B_0={47\over15},\qquad q_0=-15,\qquad R_0=-47.
\]

Apply the circle character \(e(x)=\exp(2\pi ix)\), and set

\[
 V_n=e(B_n),\qquad Z_n=e(R_n).
\]

All \((V_n,Z_n)\) are roots of unity.  Equations (10)--(11) become the exact
two-coordinate recurrence

\[
 \boxed{
 \begin{aligned}
 V_{n+1}&=V_n e(b_{n+1}),\\
 Z_{n+1}&=Z_n^{10}V_n^{144}e(q_{n+1}b_{n+1}),
 \end{aligned}}
 \qquad V_0=e(47/15),\quad Z_0=1.                  \tag{12}
\]

For a real \(x\), with \(d=\|x\|_{\mathbb T}\in[0,1/2]\),

\[
                    1-\Re e(x)=2\sin^2(\pi d).      \tag{13}
\]

Consequently (9) is exactly the promised one-character criterion

\[
 \boxed{
 \mathrm{V1}
 \quad\Longleftrightarrow\quad
 \limsup_{n\to\infty}\Re Z_n=1.}                 \tag{14}
\]

Equation (14) is the genuinely narrower necessary-and-sufficient theorem
isolated by this branch.  The all-frequency average in the earlier weighted
quotient route would imply it, but (14) asks only whether one explicitly
generated root of unity returns pointwise to \(1\).

There is also an exact moving conjugacy.  From (6), write \(E_n=X_n-R_n\).
The actual affine phase satisfies

\[
 X_{n+1}=10X_n+144\pi,
\]

and subtraction of (11) gives

\[
 E_{n+1}=10E_n+144\pi-G_{n+1},\qquad E_n\to0.       \tag{15}
\]

Thus the rational recurrence is asymptotically conjugate to the actual
affine orbit by translations of size \(E_n\).  This identity validates the
transfer, but also prevents treating (12) as an independently randomized
root-of-unity process.

## 3. Full triangular averaging only introduces multiplicity

The fixed-row audit left open whether summing the cross-depth four-pole carry
before taking a limit could reveal cancellation.  It does not at any fixed
Fourier mode.  Let

\[
 L_M=\max\{n:10^n\le16^M\},\qquad
 \mathcal D_K=\{(M,n):5\le M\le K,\ M\le n\le L_M\},
 \qquad N_K=|\mathcal D_K|.                         \tag{15a}
\]

For fixed \(h\in\mathbb Z\), form the full triangular average

\[
 \mathcal A_K(h)={1\over N_K}
 \sum_{(M,n)\in\mathcal D_K}e\bigl(h(10^n-16)B_M\bigr).       \tag{15b}
\]

Define the exact first admissible depth

\[
 c(n)=\min\{M:10^n\le16^M\}
\]

and the column multiplicity

\[
 w_K(n)=\max\bigl(0,\ \min(n,K)-\max(5,c(n))+1\bigr).        \tag{15c}
\]

Changing the order of summation is now exact.  Applying the BBP tail bound
term by term gives

\[
\boxed{
 \left|\mathcal A_K(h)-{e(-16h\pi)\over N_K}
 \sum_{n=5}^{L_K}w_K(n)e(h10^n\pi)\right|
 \le {2\pi|h|\over15N_K}
 \sum_{M=5}^K{L_M-M+1\over(M+1)^2}.}              \tag{15d}
\]

Indeed, for every pair in the triangle,

\[
 0<(10^n-16)(\pi-B_M)
 \le {10^n16^{-M}\over15(M+1)^2}
 \le {1\over15(M+1)^2}.                           \tag{15e}
\]

The right side of (15d) is \(O_h(\log K/K^2)\).  One elementary verification
is enough: \(16^5>10^6\) gives
\(L_M\ge\lfloor6M/5\rfloor\), while \(16<10^2\) gives
\(L_M\le2M-1\).  Hence \(N_K\gg K^2\), whereas the numerator in (15d) is
\(O(\log K)\).

The cross-depth carry itself is coherent, not oscillatory.  Fix a column
\(n\) and two of its depths \(M_0<M_1\).  Positivity of the four-pole
coefficients gives the unwrapped bound

\[
 0<(10^n-16)(B_{M_1}-B_{M_0})
 <(10^n-16)(\pi-B_{M_0})
 \le {1\over15(M_0+1)^2}.                          \tag{15f}
\]

Thus all copies in a late column lie on a shrinking common arc.  At a fixed
mode \(h\), triangular averaging merely assigns the tent weights \(w_K(n)\) to
the same actual decimal phases; it does not manufacture independent samples.

The fixed-return quantifiers remain unchanged.  If there were
\(\delta>0\) and \(n_0\) with
\(\|(10^n-16)\pi\|_{\mathbb T}\ge\delta\) for every \(n\ge n_0\),
the Fejer argument in Section 5, averaged with the nonnegative weights
\(w_K\), would force a negative bias at one fixed mode \(1\le h<H\) along a
subsequence of triangles.  Consequently a triangular route must still rule
out exactly such a selected low-mode bias.  Equations (15d)--(15f) show that
the four-pole cross-depth carry supplies no extra cancellation for doing so.

## 4. A new primary theorem gives sharp dispersion in the wrong direction

The actual sequence in (5) is a constant-coefficient linear recurrence:

\[
 X_n=\pi10^n-16\pi,
 \qquad X_{n+2}-11X_{n+1}+10X_n=0.                 \tag{16}
\]

Let

\[
                        P(T)=(T-10)(T-1)=T^2-11T+10. \tag{17}
\]

Chen--Ye--Zheng, *Distribution modulo one of linear recurrent sequences*,
[arXiv:2604.14036v1](https://arxiv.org/abs/2604.14036v1), Theorem 1.3,
applies through its condition \((c')\): the coefficient of \(10^n\) is
\(\pi\notin\mathbb Q(10)\).  The theorem therefore makes the circle limit set
of \(X_n\) infinite and gives

\[
 \limsup_n\|X_n\|_{\mathbb T}\ge {1\over L(P)}={1\over22}.     \tag{18}
\]

Here is the source-exact hypothesis match.  On printed/PDF page 2 the paper
defines

\[
 L(A)=\sum_j|a_j|,\qquad
 \ell(A)=\inf_Q L(AQ),\qquad
 \lambda(A)=\min_D\ell(A/D),                         \tag{18a}
\]

where the multipliers in \(\ell\) have leading coefficient one or constant
coefficient one, and \(D\) ranges over integer-polynomial factors whose roots
are roots of unity or have modulus below one, with each root-of-unity root
simple.  Theorem 1.3 on the same page assumes an integer recurrence \(R\), a
representation \(x_k=\sum_iF_i(k)\alpha_i^k\) with distinct \(\alpha_i\), and
one of its listed conditions.  In the present application

\[
 R=P,\quad (\alpha_1,\alpha_2)=(10,1),\quad
 (F_1,F_2)=(\pi,-16\pi).                             \tag{18b}
\]

Condition \((c')\) is exactly the existence of an index \(i\) with
\(|\alpha_i|>1\) and \(F_i\notin\mathbb Q(\alpha_i)[x]\); it holds at \(i=1\)
because \(\mathbb Q(10)=\mathbb Q\) and pi is irrational.  The source then
asserts

\[
 \begin{gathered}
 E\text{ is infinite},\qquad
 \limsup_{k\to\infty}\|x_k\|\ge1/L(R),\\
 \forall M\in\mathbb Z_{\ge1}\ \exists l\in\mathbb Z_{\ge0}:\quad
 E_{M,l}\text{ is not contained in any interval of }\mathbb R/\mathbb Z
 \text{ of length }<1/\lambda(R),                    \tag{18c}
 \end{gathered}
\]

where \(E_{M,l}\) is the limit set of \((x_{kM+l})_{k\ge1}\).  This is the exact
progression quantifier: \(l\) is chosen after \(M\), and the theorem does not
give one \(l\) for all moduli.  Replacing \(l\) by its residue modulo \(M\) only
deletes or adds finitely many initial terms, so it leaves the limit set
unchanged.

Here \(L(P)\) is the sum of the absolute coefficients.  The constant is not
an artifact of a poor recurrence choice.  Suppose an integer polynomial

\[
                         U(T)=\sum_i u_iT^i                         \tag{19}
\]

annihilates \(X_n\).  Evaluating the relation at two consecutive indices
forces \(U(10)=U(1)=0\), hence \(P\mid U\).  Since \(U(1)=0\), the sum of its
positive coefficients and the absolute sum of its negative coefficients are
the same integer \(m=L(U)/2\).  The identity \(U(10)=0\) is an equality of
two multisets of \(m\) powers of ten.

If \(m\le9\), ordinary base-10 uniqueness makes the multisets identical.  If
\(m=10\), a noncanonical side can only consist of ten identical powers; after
one carry its value is a single power of ten.  Any other ten-term
representation of that value again has all ten terms equal.  Hence it is the
same multiset.  A nonzero relation requires \(m\ge11\), so

\[
                              L(U)\ge22.             \tag{20}
\]

The polynomial \(P\) attains equality.  Therefore \(1/22\) is the strongest
bound obtainable from Theorem 1.3's plain \(L\)-length conclusion for this
sequence.  This optimality statement is internal to that theorem interface;
it is not a globally optimal dispersion bound.

The same source has an arithmetic-progression conclusion in terms of the
overreduced length \(\lambda(P)\).  Here

\[
                              \lambda(P)=10.          \tag{21}
\]

Indeed, the allowed factors in Definition 1.2 are only \(1\) and \(T-1\), so
the two candidates are \(\ell(P)\) and \(\ell(T-10)\).  The Mahler measure of
both \(P\) and \(T-10\) is ten.  Every multiplier allowed in the definition of
reduced length has Mahler measure at least one, while coefficient length is
at least Mahler measure.  Both candidates are therefore at least ten.  The
constant-one polynomials

\[
 Q_d(T)=1+{T\over10}+\cdots+{T^d\over10^d}
\]

give

\[
                  (T-10)Q_d(T)={T^{d+1}\over10^d}-10,
 \qquad L((T-10)Q_d)=10+10^{-d}\downarrow10,        \tag{22}
\]

proving equality.  Thus, for every integer \(M\ge1\), the source theorem
provides a residue \(l\pmod M\) for which the limit set of
\((X_{kM+l})_k\) is not contained in any circle interval of length \(<1/10\).
Again, \(1/10\) is optimal only for this source theorem's \(\lambda\)-length
interface, not as a global progression-spread constant.

Changing the annihilating recurrence cannot improve this particular
\(\lambda\)-interface.  Every integer recurrence polynomial \(U\) for
\(X_n\) is divisible by \(T-10\).  An admissible factor removed in the
definition of \(\lambda(U)\) cannot contain the root \(10\), so the remaining
integer polynomial still has root \(10\), nonzero integer leading
coefficient, and Mahler measure at least \(10\).  Therefore
\(\lambda(U)\ge10\), while \(P\) attains equality.

Because \(X_n-R_n\to0\), all these limit-set, limsup, and progression-spread
conclusions transfer to the fully rational recurrence (11)--(12).  More
explicitly, for each fixed \(M\ge1\) and \(l\ge0\),

\[
 d_{\mathbb T}(X_{kM+l},R_{kM+l})\longrightarrow0.
\]

Two sequences in the compact circle whose termwise distance tends to zero
have identical subsequential limit sets: any convergent subsequence of one
forces the corresponding subsequence of the other to the same limit, and
the converse is symmetric.  Thus the residue-class limit sets themselves,
not merely their diameters, transfer exactly.
This is real progress on its orbit geometry.  It cannot be reversed into
(14): a set can be infinite and widely spread while remaining a positive
distance from the prescribed point \(0\pmod1\).

## 5. Missing return forces one fixed low Fourier bias

The one-character formulation permits a more local Fourier alternative than
all-frequency Weyl cancellation.  Define the normalized Fejer kernel

\[
 \Phi_H(x)={1\over H}\left|\sum_{j=0}^{H-1}e(jx)\right|^2
 =1+2\Re\sum_{h=1}^{H-1}\left(1-{h\over H}\right)e(hx).       \tag{23}
\]

If \(\|x\|_{\mathbb T}\ge\delta\), where
\(0<\delta\le1/2\), then

\[
                    \Phi_H(x)\le {1\over H\sin^2(\pi\delta)}. \tag{24}
\]

Assume (14) fails.  By (9), there are \(\delta>0\) and \(n_0\) such that
\(\|R_n\|_{\mathbb T}\ge\delta\) for every \(n\ge n_0\).  Choose

\[
 H=\left\lceil{2\over\sin^2(\pi\delta)}\right\rceil,
 \qquad U={1\over H\sin^2(\pi\delta)}\le {1\over2}.             \tag{25}
\]

For a block of \(N\) late indices put

\[
 A_N(h)={1\over N}\sum_{n=n_0}^{n_0+N-1}Z_n^h.                 \tag{26}
\]

Averaging (23)--(24) gives

\[
 1+2\Re\sum_{h=1}^{H-1}\left(1-{h\over H}\right)A_N(h)\le U. \tag{27}
\]

Since twice the sum of the positive weights in (27) is \(H-1\), at least
one \(1\le h<H\) obeys

\[
                  \Re A_N(h)\le-{1-U\over H-1}
                  \le-{1\over2(H-1)}.             \tag{28}
\]

There are only \(H-1\) choices.  Pigeonholing as \(N\to\infty\) proves the
fixed-mode alternative

\[
 \boxed{
 \text{failure of V1}\Longrightarrow
 \exists h\ge1\ \exists N_j\to\infty:
 \Re A_{N_j}(h)\le-{1\over2(H-1)}.}                \tag{29}
\]

This is not a normality requirement disguised as a conclusion: (29) says
that failure of one pointwise return forces a quantitative bias at one of a
finite list of modes.  Conversely, proving that the explicit recurrence
cannot realize the alternative for every possible gap \(\delta\) would prove
V1.

The bias cannot be killed merely by moving up a power-of-ten frequency ray.
For the actual phases,

\[
 q_{n+r}=10^rq_n+16(10^r-1),
\]

so

\[
 e(hX_{n+r})=e(16h(10^r-1)\pi)e(10^rhX_n).         \tag{30}
\]

After summing \(N\) terms, shifting the index range costs at most \(2r/N\).
For each fixed \(r\), any nonzero limiting magnitude at \(h\) therefore
persists at \(10^rh\).  Equation (7) transfers the same assertion to \(R_n\).
This recovers the exact frequency-ray obstruction of the four-pole audit in
the pointwise-return setting: the BBP recurrence propagates a possible bias;
it does not supply a zero-frequency endpoint that contradicts it.

## 6. A finite-irrationality-exponent transcendental separator

The recurrence architecture alone cannot prove (14), even if one adds the
optimal scalar irrationality exponent.  Put

\[
 \kappa=\sum_{j\ge0}10^{-2^j}
       =0.1101000100000001\ldots\quad\text{(base 10)}.          \tag{31}
\]

Kempner's theorem makes this decimal Fredholm value transcendental.  Shallit
computes its continued fraction as the specialization \(u=10\) of
\(B(u,\infty)=\sum_{j\ge0}u^{-2^j}\); his Theorems 8--9 show that all its
partial quotients belong to the finite set \(\{8,9,10,12\}\) after the initial
zero.  Hence \(\kappa\) is badly approximable and has irrationality exponent
exactly two.

Its decimal digits are only zero and one, and

\[
                         {11\over100}<\kappa<{1\over9}.         \tag{32}
\]

Every decimal tail \(\{10^n\kappa\}\) lies in \([0,1/9]\), while the first
three nonzero terms in (31), together with \(\kappa<1/9\), give

\[
                    \{16\kappa\}\in(19/25,7/9).                \tag{33}
\]

For \(x\in[0,1/9]\) and \(y\in(19/25,7/9)\), both arcs between \(x\) and
\(y\) have length greater than \(2/9\).  Consequently

\[
                 \|(10^n-16)\kappa\|_{\mathbb T}>{2\over9}
                 \qquad(n\ge0).                    \tag{34}
\]

This stronger separator has the same rational-shadow form.  For \(n\ge1\)
let

\[
 C_n={\lfloor10^{3n}\kappa\rfloor\over10^{3n}}
     =\sum_{2^j\le3n}10^{-2^j},
 \qquad S_n=(10^n-16)C_n.                          \tag{35}
\]

Then \(C_n\in\mathbb Q\), \(C_n\uparrow\kappa\), and comparison with a decimal
tail consisting entirely of ones gives

\[
       0<\kappa-C_n\le {10^{-3n}\over9},\qquad
       |(10^n-16)(\kappa-C_n)|<{10^{-2n}\over9}.    \tag{36}
\]

Exactly as in (11), with \(c_{n+1}=C_{n+1}-C_n\ge0\),

\[
 S_{n+1}=10S_n+H_{n+1},\qquad
 H_{n+1}=144C_n+(10^{n+1}-16)c_{n+1}\in\mathbb Q_{>0}.         \tag{37}
\]

Moreover, \(0\le c_{n+1}\le\kappa-C_n\) yields the explicit convergence

\[
 |H_{n+1}-144\kappa|
 \le16\,10^{-3n}+{10^{1-2n}\over9}\longrightarrow0.         \tag{38}
\]

Thus \(e(C_n)\) and \(e(S_n)\) are roots of unity, their diagonal rational
shadow error is exponentially small, their rational forcing is positive and
converges exponentially to an irrational constant, and their limit is both
transcendental and of irrationality exponent two.  Nevertheless,
(34)--(36) give a uniform nonreturning gap.

The separator deliberately does not satisfy the four-pole coefficient
formula (3).  Its force is exact: rationality, positivity, exponential
shadowing, root-of-unity dynamics, transcendence, and even optimal scalar
irrationality exponent are insufficient.  A successful proof of (14) must
exploit a further identity special to the actual \(a(k)\).

## 7. Exact replay

The companion
[`bbp_one_character_return_check.py`](bbp_one_character_return_check.py),
SHA-256
`4d4cf5933f0d9751ea84fffaf2a7f1e25c84769e50e3e77b1b4083982a660372`,
uses `Fraction` and integer arithmetic for every structural assertion.  It
pins the target and all five local source PDFs; checks the coefficient
inequality, (10)--(12), the linear recurrence, the exact triangular
reindexing and cross-depth carry, and the Kempner-shadow estimates; and
prints only a labeled finite diagonal diagnostic.

Run:

```bash
python -m py_compile work/ultrapi-resume/bbp_one_character_return_check.py
python work/ultrapi-resume/bbp_one_character_return_check.py --max-depth 160
```

Retained output:

```text
status: PASS
claim_label: experiment
source_sha256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
bbp_pdf_sha256: e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4
lagarias_pdf_sha256: a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9
chen_ye_zheng_pdf_sha256: a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d
shallit_pdf_sha256: 592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981
kempner_pdf_sha256: 99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014
coefficient_bounds: 160
scalar_recurrence_checks: 160
torus_recurrence_checks: 320
diagonal_phase_checks: 159
linear_recurrence_checks: 159
triangular_reindex_checks: 4
triangular_carry_checks: 3296
triangular_transfer_checks: 3640
largest_triangle_size: 2707
separator_shadow_checks: 160
separator_recurrence_checks: 159
finite_diagonal_record: n=5,distance=0.000159642895927
minimum_certified_separator_gap: 0.221555555555556
asserts_fixed_return: false
asserts_v1: false
all exact checks passed
```

The depth-five record is an `experiment`, not evidence for an infinite
return.  The printed separator gap is the finite rational lower certificate,
not a floating-point proof of (34).

## 8. Dated source and applicability audit

Status: `literature-checked` on **2026-08-13 UTC**, within this bounded
search.

The reproducible search log is:

| date | database and exact query | result used or boundary |
|---|---|---|
| 2026-08-12 UTC | Web/arXiv: `"linear recurrent sequence" fractional parts limit values zero recurrence 10^n pi` | Rechecked the closest source family and found no stronger fixed-return theorem; Chen--Ye--Zheng was then audited directly by identifier. |
| 2026-08-12 UTC | Web/arXiv: `"10^n alpha" modulo one limit point zero affine recurrence` | Returned generic or metric orbit results, not a fixed-\(\pi\) prescribed return. |
| 2026-08-12 UTC | Web/arXiv: `BBP formula decimal orbit Fourier cancellation carry recurrence` | Returned BBP computation material, not a distribution or cancellation theorem for the selected orbit. |
| 2026-08-12 UTC | Web/arXiv: `lacunary sequence fixed alpha prescribed point return modulo one` | Returned predominantly almost-everywhere lacunary results; none specializes to \(\pi\). |
| 2026-08-12 UTC; replayed 2026-08-13 UTC | arXiv direct version audit: `2604.14036v1` (abstract, HTML, PDF, and e-print source) | Verified Definition 1.2, Theorem 1.3, condition \((c')\), the progression quantifiers, and the pinned v1 source bytes. |
| 2026-08-12 UTC | Web/Waterloo: `Jeffrey Shallit Kempner number continued fraction bounded partial quotients irrationality exponent 2 sum 10^{-2^n}` | Located Shallit's primary PDF; Theorems 3 and 8--9 give the exact decimal specialization used in Section 6. |

| source | exact use | pin |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | Exact series (3), not a return or distribution theorem. | local PDF SHA-256 `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2), Theorems 2.1, 3.1, 3.3, 4.1 | Digit-density/orbit equivalence and perturbed-radix shadowing; density remains conditional in the BBP framework. | local PDF SHA-256 `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Chen--Ye--Zheng, [*Distribution modulo one of linear recurrent sequences*](https://arxiv.org/abs/2604.14036v1), Definition 1.2 and Theorem 1.3, printed/PDF p. 2 | Exact definitions (18a), hypothesis \((c')\), infinite limit set, recurrence-length limsup bound, and progression spread applied in (16)--(22). | [local PDF](library/chen-ye-zheng-2604.14036v1.pdf), SHA-256 `a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d`; e-print SHA-256 `8793096b3e8e45bd9646c460e37290f39bd11a57ba9c74c8239620f22f7a45ed` |
| Furstenberg, [*Disjointness in ergodic theory, minimal sets, and a problem in Diophantine approximation*](https://doi.org/10.1007/BF01692494), Theorem IV.1 | Supplies the already audited implication from one fixed independent return to decimal density. | local source pin recorded in the T69 audit |
| Kempner, [*On Transcendental Numbers*](https://doi.org/10.1090/S0002-9947-1916-1501054-4), printed p. 477 | Transcendence of the decimal value (31). | [existing T89 local PDF](../theory/pi-lacunary-near-return-sparsity/library/t89/kempner-1916.pdf), SHA-256 `99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014` |
| Shallit, [*Simple Continued Fractions for Some Irrational Numbers*](https://doi.org/10.1016/0022-314X(79)90040-4), Theorems 3 and 8--9, PDF pp. 5 and 7 | Irrationality and bounded partial quotients of \(\sum_{j\ge0}u^{-2^j}\) for integer \(u\ge3\), specialized to \(u=10\); bounded partial quotients give \(\mu(\kappa)=2\). | [local PDF](library/shallit-1979-simple-continued-fractions.pdf), SHA-256 `592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981` |

Fresh searches covered linear-recurrent fractional parts, holonomic rational
recurrences, fixed-frequency lacunary sums, and BBP carry dynamics.  The 2026
linear-recurrence theorem is the closest applicable new result found.  Its
output is (18) and progression spread, not a theorem placing zero in the
limit set.  Metric lacunary theorems average over the starting point and do
not select pi.  G-function digit theorems control rational approximation or
long repetitions, not the one-character limsup (14).

## Sharp handoff

The fixed return has been reduced to the following coefficient-only problem:

> Starting from \(V_0=e(47/15)\), \(Z_0=1\), prove that the exact rational
> root-of-unity recurrence (12) has
> \(\limsup_n\Re Z_n=1\).

The latest linear-recurrence theorem proves that the same orbit is infinite
and quantitatively dispersed, and the Fejer alternative says exactly what
failure would look like: a fixed low power \(Z_n^h\) retains a negative
Cesaro bias and that bias propagates along its power-of-ten ray.  Neither
result rules out that alternative.  The Kempner construction proves that
the generic recurrence architecture cannot do so even at irrationality
exponent two.  The unresolved input is
therefore a four-pole-specific cancellation or return identity for (12), not
another denominator valuation or an all-frequency normality theorem.
