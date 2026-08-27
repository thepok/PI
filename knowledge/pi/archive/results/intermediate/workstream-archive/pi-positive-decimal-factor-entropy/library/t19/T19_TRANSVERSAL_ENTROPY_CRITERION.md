# T19: a quantitative times-16 transversal criterion

Status: `proof sketch` (rigorous prose, not machine-checked)

## 1. Provenance and scope

- Agenda item: `T19`, serving goal `G7`.
- Canonical statement: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.
- Verified SHA-256 of that statement:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Original source URL: none. The canonical file says that the question was
  formulated locally on 2026-07-22.
- Existing verified interface used for comparison: T1's machine-checked
  canonical factor entropy definitions and limit theorem. The covering
  argument below is new prose and is not imported from an unverified note.

This note proves a general conditional statement for a nonempty closed
forward-times-10-invariant subset of the circle. It then applies that statement
to the decimal orbit closure of pi, still conditionally on an explicit
times-16 transversal rate. It does **not** prove that this rate holds for pi.

No result from the research literature is used in the proof. A scoped search
on 2026-07-23 located Furstenberg's qualitative times-2/times-3 work
([DOI 10.1007/BF01692494](https://doi.org/10.1007/BF01692494)), but neither a
qualitative nor a quantitative Furstenberg theorem is invoked here. In
particular, this note makes no literature or novelty claim about quantitative
transversal rates.

## 2. Normalized statement and ambiguities

Write

\[
  \mathbb T=\mathbb R/\mathbb Z,
  \qquad T_b(x)=b x\pmod 1,
\]

and equip `T` with circular distance

\[
  d_{\mathbb T}(x,y)=\min_{k\in\mathbb Z}|\widetilde x-\widetilde y-k|,
\]

where tildes are arbitrary real lifts. Let \(m\) be normalized Haar length,
so \(m(\mathbb T)=1\). All logarithms denoted by \(\log\) are natural.

The following conventions resolve all ambiguities needed here.

1. "Times-10-invariant" means forward invariant:
   \(T_{10}(K)\subseteq K\). Equality is not needed. The set \(K\) is always
   assumed nonempty and closed.
2. A subset \(S\subseteq\mathbb T\) is \(\varepsilon\)-dense when
   every \(y\in\mathbb T\) has some \(s\in S\) with
   \(d_{\mathbb T}(y,s)\leq\varepsilon\). If "dense" is instead defined with
   strict inequality, that stronger convention implies the convention used
   here with the same radius.
3. The phrase \(R_K(\varepsilon)=O(\log(1/\varepsilon))\) is not used until
   its constants and quantifiers are displayed in Section 7.
4. The phrase \(R_K(\varepsilon)=o(\log(1/\varepsilon))\) is not used until
   its exact quantifiers are displayed in Section 8.
5. Decimal cells are half-open in the unique representative interval
   \([0,1)\). Their *closed* circular hulls are used for covers. This separates
   digit assignment from topological closure and handles terminating decimal
   boundary points without choosing two decimal expansions.
6. An arbitrary closed forward-invariant \(K\) need not have a finite
   transversal time. Thus \(R_K(\varepsilon)\) is allowed to be \(+\infty\).

The normalized conditional theorem proved below is:

> **Theorem (conditional transversal criterion).** Let
> \(\varnothing\neq K\subseteq\mathbb T\) be closed and satisfy
> \(T_{10}(K)\subseteq K\). Then its decimal factor entropy \(h_{10}(K)\)
> exists. For every fixed \(A\geq0\), \(B\in\mathbb R\), and
> \(0<\varepsilon_0<1\), if for every
> \(0<\varepsilon<\varepsilon_0\), the time \(R_K(\varepsilon)\) is finite and
> \(R_K(\varepsilon)\leq A\log(1/\varepsilon)+B\), then
> \[
>   h_{10}(K)\geq\frac{1}{1+A\log16}>0.
> \]
> If instead \(R_K(\varepsilon)=o(\log(1/\varepsilon))\) in the exact sense
> of Section 8, then \(h_{10}(K)=1\).

## 3. Decimal cells, factor counts, and boundaries

For integers \(n\geq0\), put \(q_n=10^n\). For
\(a\in\{0,\ldots,q_n-1\}\), define the half-open circular decimal cell

\[
  C_{n,a}=\left\{x\in\mathbb T:
    \widetilde x\in[a/q_n,(a+1)/q_n)\right\},                 \tag{1}
\]

where \(\widetilde x\in[0,1)\) is the unique representative. These cells are
pairwise disjoint and their union is all of \(\mathbb T\). In particular,
\(0=1\) belongs to \(C_{n,0}\), not to \(C_{n,q_n-1}\).

Define the occupied labels and their count by

\[
  \mathcal A_n(K)=\{a:C_{n,a}\cap K\neq\varnothing\},
  \qquad P_K(n)=|\mathcal A_n(K)|.                           \tag{2}
\]

Because \(K\neq\varnothing\), and because (1) is a partition,

\[
  1\leq P_K(n)\leq 10^n.                                   \tag{3}
\]

Let

\[
  c_n(x)=\lfloor 10^n\widetilde x\rfloor.
\]

This is precisely the label of the unique half-open cell containing \(x\).
For all \(n,m\geq0\), including when \(x\) or an iterate is on a decimal
boundary, the floor convention gives the exact identity

\[
  c_{n+m}(x)
   =10^m c_n(x)+c_m(T_{10}^n x).                            \tag{4}
\]

Indeed, write \(10^n\widetilde x=c_n(x)+u\) with
\(u\in[0,1)\). Multiplication by \(10^m\) and taking the floor gives (4),
including the case \(u=0\).

If a label \(a=c_{n+m}(x)\) is occupied, then \(c_n(x)\) is an occupied
length-\(n\) label and, by forward invariance,
\(c_m(T_{10}^n x)\) is an occupied length-\(m\) label. The map

\[
  a\longmapsto\big(c_n(x),c_m(T_{10}^n x)\big)
\]

does not depend on the chosen \(x\in C_{n+m,a}\): by (4), it is just the
quotient-remainder decomposition of \(a\) modulo \(10^m\). That decomposition
is injective. Therefore

\[
  P_K(n+m)\leq P_K(n)P_K(m).                                \tag{5}
\]

Thus \(\log P_K(n)\) is subadditive. Fekete's lemma and (3) give the existing
limit

\[
  h_{10}(K)
  :=\lim_{n\to\infty}\frac{\log P_K(n)}{n\log10}
  =\inf_{n\geq1}\frac{\log P_K(n)}{n\log10},
  \qquad 0\leq h_{10}(K)\leq1.                              \tag{6}
\]

## 4. Finite times-16 transversal time

For an integer \(R\geq0\), set

\[
  U_R(K)=\bigcup_{j=0}^{R}T_{16}^j(K).                      \tag{7}
\]

For \(\varepsilon>0\), define

\[
 R_K(\varepsilon)=
 \begin{cases}
  \min\{R\in\mathbb N:U_R(K)\text{ is }\varepsilon\text{-dense}\},
       &\text{if this set is nonempty},\\
  +\infty,&\text{otherwise}.
 \end{cases}                                                \tag{8}
\]

The minimum in the first line exists by well-ordering. The adjective
"finite" refers to the finite union in (7); finiteness of the value in (8) is
always retained as a hypothesis when needed. Monotonicity is immediate:
if \(0<\varepsilon\leq\varepsilon'\) and
\(R_K(\varepsilon)<\infty\), then

\[
  R_K(\varepsilon')\leq R_K(\varepsilon).                  \tag{9}
\]

No later argument needs (9), but it records the direction of the scale
parameter explicitly.

## 5. Explicit image covers

Fix \(n\geq1\), and write \(\delta_n=10^{-n}\). Let

\[
  \overline C_{n,a}
   =\text{the image in }\mathbb T\text{ of }
     [a/10^n,(a+1)/10^n].                                  \tag{10}
\]

This is a closed circular arc, and it contains the half-open cell
\(C_{n,a}\), including its assigned left endpoint. If \(z_{n,a}\) is the
image of its real midpoint \((a+1/2)/10^n\), then

\[
  \overline C_{n,a}
   \subseteq \overline B_{\mathbb T}
      (z_{n,a},\delta_n/2).                                 \tag{11}
\]

Since all points of \(K\) lie in their uniquely assigned occupied cells,

\[
  K\subseteq
    \bigcup_{a\in\mathcal A_n(K)}\overline C_{n,a}
  \subseteq
    \bigcup_{a\in\mathcal A_n(K)}
       \overline B_{\mathbb T}(z_{n,a},10^{-n}/2).          \tag{12}
\]

For all \(x,y\in\mathbb T\), multiplication by 16 obeys

\[
  d_{\mathbb T}(T_{16}x,T_{16}y)
    \leq16d_{\mathbb T}(x,y).                              \tag{13}
\]

To check (13), choose an integer \(k\) minimizing the lift distance; after
multiplication the integer \(16k\) is an admissible competitor in the new
circular distance. Iterating (13) gives the explicit Lipschitz constant

\[
  \operatorname{Lip}(T_{16}^j)\leq16^j.                    \tag{14}
\]

Applying (14) to (12), for every integer \(j\geq0\),

\[
  T_{16}^j(K)\subseteq
   \bigcup_{a\in\mathcal A_n(K)}
    \overline B_{\mathbb T}
      (T_{16}^jz_{n,a},16^j10^{-n}/2).                     \tag{15}
\]

Formula (15) remains valid when its displayed radius is at least \(1/2\):
then the circular ball is simply all of \(\mathbb T\). Thus wrapping across
\(0=1\), or wrapping several times under a large power of 16, causes no
unrecorded splitting or extra cover count.

## 6. Density forces a covering lower bound

Assume that \(R=R_K(\varepsilon)<\infty\). By (8), for each
\(y\in\mathbb T\) there is an \(x\in U_R(K)\) with
\(d_{\mathbb T}(x,y)\leq\varepsilon\). Combining this fact with (15) and the
triangle inequality gives the explicit enlarged cover

\[
 \mathbb T\subseteq
 \bigcup_{j=0}^{R}\ \bigcup_{a\in\mathcal A_n(K)}
  \overline B_{\mathbb T}
   \left(T_{16}^jz_{n,a},\,\varepsilon+\frac{16^j10^{-n}}2\right). \tag{16}
\]

A closed circular ball of radius \(r\geq0\) has normalized length
\(\min(1,2r)\), which is at most \(2r\). Taking Haar length in (16), using
finite subadditivity, and retaining every cover multiplicity yields

\[
\begin{aligned}
 1
 &\leq \sum_{j=0}^{R}\sum_{a\in\mathcal A_n(K)}
    \left(2\varepsilon+16^j10^{-n}\right)\\
 &=P_K(n)\left(2(R+1)\varepsilon
       +10^{-n}\sum_{j=0}^{R}16^j\right)\\
 &=P_K(n)\left(2(R+1)\varepsilon
       +10^{-n}\frac{16^{R+1}-1}{15}\right).              \tag{17}
\end{aligned}
\]

Consequently, with the strictly positive denominator displayed in (17),

\[
 P_K(n)\geq
 \left(2(R+1)\varepsilon
       +10^{-n}\frac{16^{R+1}-1}{15}\right)^{-1}.          \tag{18}
\]

Equations (11), (14), (16), and (17) record respectively the initial radius,
the image Lipschitz constant, the enlarged density radius, and the exact
image-cover count. No assertion about pi has entered this chain.

## 7. Exact big-O quantifiers and positive entropy

Here the assertion

\[
  R_K(\varepsilon)=O(\log(1/\varepsilon))
  \quad(\varepsilon\downarrow0)                            \tag{19}
\]

means exactly that there exist constants

\[
  A\geq0,\qquad B\in\mathbb R,\qquad 0<\varepsilon_0<1     \tag{20}
\]

such that, for every real \(\varepsilon\) with
\(0<\varepsilon<\varepsilon_0\), the value
\(R_K(\varepsilon)\) is finite and

\[
  R_K(\varepsilon)\leq A\log(1/\varepsilon)+B.             \tag{21}
\]

For the remainder of this section, fix any one witness triple
\((A,B,\varepsilon_0)\) satisfying (20)--(21). The bound derived below holds
for every such fixed triple; in particular, the \(A\) in (29) is bound by
this choice and is not a canonical constant attached to big-O notation.

The additive constant is allowed to be negative. The existence of the
nonnegative left side in (21) automatically forces its right side to be
nonnegative at every scale where (21) is asserted.

Define the positive constants and scales

\[
  \lambda=\frac{\log10}{1+A\log16},
  \qquad \varepsilon_n=e^{-\lambda n},
  \qquad R_n=R_K(\varepsilon_n).                            \tag{22}
\]

For every sufficiently large integer \(n\), one has
\(0<\varepsilon_n<\varepsilon_0\), so (21) gives

\[
  R_n+1\leq A\lambda n+B+1.                                \tag{23}
\]

The first term in the parenthesis in (17) therefore satisfies

\[
  2(R_n+1)\varepsilon_n
   \leq2(A\lambda n+B+1)e^{-\lambda n}.                    \tag{24}
\]

For the geometric-sum term, (23) and monotonicity of real exponentiation give

\[
\begin{aligned}
 10^{-n}\frac{16^{R_n+1}-1}{15}
 &\leq \frac{10^{-n}16^{R_n+1}}{15}\\
 &\leq \frac{16^{B+1}}{15}
   \exp\!\left(-n\log10+A\lambda n\log16\right)\\
 &=\frac{16^{B+1}}{15}e^{-\lambda n}.                      \tag{25}
\end{aligned}
\]

The last equality follows from the exact identity

\[
  \log10-A\lambda\log16=\lambda,                           \tag{26}
\]

which is immediate from (22). Substituting (24) and (25) into (18) yields the
fully explicit lower bound

\[
 P_K(n)\geq
 \frac{e^{\lambda n}}
 {2(A\lambda n+B+1)+16^{B+1}/15}                           \tag{27}
\]

for every sufficiently large \(n\). The denominator in (27) is positive
because it bounds from above the positive denominator in (18). It is affine
in \(n\), so

\[
 \lim_{n\to\infty}
 \frac{\log(2(A\lambda n+B+1)+16^{B+1}/15)}{n}=0.           \tag{28}
\]

Taking logarithms in (27), dividing by \(n\log10\), and using the existing
limit (6) gives

\[
 \boxed{
 h_{10}(K)\geq\frac{\lambda}{\log10}
 =\frac1{1+A\log16}>0.}                                   \tag{29}
\]

This proves the positive-entropy conclusion with an explicit constant. The
constant \(B\) and threshold \(\varepsilon_0\) affect only how large \(n\)
must be, not the entropy exponent.

## 8. Exact little-o quantifiers and full entropy

Here

\[
 R_K(\varepsilon)=o(\log(1/\varepsilon))
 \quad(\varepsilon\downarrow0)                             \tag{30}
\]

means exactly:

> For every real \(\eta>0\), there is a real
> \(\varepsilon_\eta\in(0,1)\) such that, for every
> \(0<\varepsilon<\varepsilon_\eta\), the value
> \(R_K(\varepsilon)\) is finite and
> \[
>   R_K(\varepsilon)\leq\eta\log(1/\varepsilon).           \tag{31}
> \]

Take

\[
  \varepsilon_n=10^{-n},\qquad R_n=R_K(10^{-n}).            \tag{32}
\]

For every \(\eta>0\), (31) gives, for all sufficiently large \(n\),

\[
  0\leq\frac{R_n}{n}\leq\eta\log10.                       \tag{33}
\]

Since \(\eta\) is arbitrary,

\[
  \frac{R_n}{n}\longrightarrow0.                           \tag{34}
\]

Using (32) in (17) and factoring out \(10^{-n}\) gives

\[
 1\leq P_K(n)10^{-n}
 \left(2(R_n+1)+\frac{16^{R_n+1}-1}{15}\right).            \tag{35}
\]

For every integer \(R_n\geq0\), one has
\(R_n+1\leq16^{R_n+1}\). Therefore the parenthesis in (35)
has the explicit upper bound

\[
 2(R_n+1)+\frac{16^{R_n+1}-1}{15}
 \leq\frac{31}{15}16^{R_n+1}.                              \tag{36}
\]

Combining (35) and (36),

\[
 P_K(n)\geq
 10^n\frac{15}{31}\,16^{-(R_n+1)}.                         \tag{37}
\]

Taking logarithms, dividing by \(n\log10\), and using (34),

\[
 \liminf_{n\to\infty}\frac{\log P_K(n)}{n\log10}\geq1.  \tag{38}
\]

The universal upper bound \(P_K(n)\leq10^n\) from (3) gives the reverse
inequality. Hence

\[
  \boxed{h_{10}(K)=1.}                                     \tag{39}
\]

## 9. Boundary-robust specialization to the orbit closure of pi

Let

\[
 x_i=\{10^i\pi\}\in\mathbb T,\qquad
 O_\pi=\{x_i:i\geq0\},\qquad K_\pi=\overline{O_\pi}.       \tag{40}
\]

The set \(K_\pi\) is nonempty and closed. Continuity of \(T_{10}\) and the
identity \(T_{10}(x_i)=x_{i+1}\) imply

\[
  T_{10}(K_\pi)\subseteq K_\pi.                            \tag{41}
\]

Let \(S_n\) be the set of cell labels attained by \(O_\pi\):

\[
  S_n=\{a:\text{some }x_i\text{ lies in }C_{n,a}\}.        \tag{42}
\]

The floor-based decimal shift identity says that the label of \(x_i\) is the
ordered block \((d_{i+1},\ldots,d_{i+n})\). Thus, with the canonical factor
convention from the source statement,

\[
  |S_n|=p_\pi(n).                                           \tag{43}
\]

No orbit point \(x_i\) is a decimal boundary \(a/10^n\): such an equality
would make \(10^i\pi\), and hence \(\pi\), rational. Closure points can be
boundaries, so this observation alone does not justify equality between
\(P_{K_\pi}(n)\) and \(p_\pi(n)\).

The inclusion \(O_\pi\subseteq K_\pi\) immediately gives

\[
  p_\pi(n)=|S_n|\leq P_{K_\pi}(n).                         \tag{44}
\]

For the reverse comparison, take any
\(a\in\mathcal A_n(K_\pi)\) and choose
\(x\in K_\pi\cap C_{n,a}\).

- If \(x\) is in the circular interior of \(C_{n,a}\), some orbit point
  lies in that interior because \(O_\pi\) is dense in its closure. Hence
  \(a\in S_n\).
- Otherwise, the half-open convention forces \(x\) to be the assigned left
  endpoint \(a/10^n\). Every sufficiently small punctured neighborhood of
  this endpoint is contained in
  \(C_{n,a-1}\cup C_{n,a}\), with labels interpreted modulo \(10^n\).
  Since orbit points approach \(x\) and never equal the endpoint, either
  \(a-1\in S_n\) or \(a\in S_n\).

This includes the wraparound endpoint \(a=0\), where \(a-1\) means
\(10^n-1\). In set notation,

\[
  \mathcal A_n(K_\pi)\subseteq S_n\cup(S_n+1),              \tag{45}
\]

where addition is modulo \(10^n\). Therefore

\[
  \boxed{p_\pi(n)\leq P_{K_\pi}(n)\leq2p_\pi(n).}         \tag{46}
\]

Consequently

\[
  0\leq
  \frac{\log P_{K_\pi}(n)-\log p_\pi(n)}{n\log10}
  \leq\frac{\log2}{n\log10}\longrightarrow0.              \tag{47}
\]

Thus the entropy in (6) agrees with the canonical decimal factor entropy:

\[
  h_{10}(K_\pi)=h_{10}(\pi).                               \tag{48}
\]

The factor 2 in (46) is exactly where decimal-boundary closure points are
paid for; it disappears after entropy normalization but must not be omitted
from finite factor counts.

## 10. Conditional pi conclusions and nonclaims

The program's conjecture C6 states that there are \(A>0\), \(B\in\mathbb R\),
and \(\varepsilon_0>0\) such that each
\(0<\varepsilon<\varepsilon_0\) admits an integer
\(R\leq A\log(1/\varepsilon)+B\) for which \(U_R(K_\pi)\) is
\(\varepsilon\)-dense. Whenever such a witness exists, minimality in (8)
gives

\[
  R_{K_\pi}(\varepsilon)\leq R
  \leq A\log(1/\varepsilon)+B.                             \tag{49}
\]

Fix any particular witness triple \((A,B,\varepsilon_0)\) to C6 and replace
its threshold by

\[
  \varepsilon'_0=\min(\varepsilon_0,1/2).                  \tag{49a}
\]

Then \(0<\varepsilon'_0<1\), and the same witness property holds for every
\(0<\varepsilon<\varepsilon'_0\). Therefore (29), (48), and (49), applied to
this fixed witness triple, give

\[
  h_{10}(\pi)\geq\frac1{1+A\log16}>0.                      \tag{49b}
\]

Since every C6 witness has some finite \(A>0\), the closed conditional
implication is

\[
 \boxed{\text{C6}\quad\Longrightarrow\quad h_{10}(\pi)>0.} \tag{50}
\]

For each fixed C6 witness, (49b) retains the stronger explicit
witness-dependent constant. By the machine-checked T1 theorem
`DecimalFactorEntropy.pi_positive_entropy_iff_canonical_exponential_quantifiers`,
positivity in (50) is exactly the uniform eventual exponential conclusion C1.
This sentence is an implication from C6, not an assertion that either C6 or
C1 holds.

Likewise, (39) and (48) prove only

\[
 \boxed{
 R_{K_\pi}(\varepsilon)=o(\log(1/\varepsilon))
 \quad\Longrightarrow\quad h_{10}(\pi)=1.}                 \tag{51}
\]

The premise in (51) is strictly stronger than the displayed C6 rate and is
not established here. The note stops at the conditional full-entropy
statement (51); it does not assert disjunctivity for pi.

To be explicit, this note does not establish or assume any of the following:

- C6 or any quantitative Furstenberg theorem;
- C1 unconditionally;
- full entropy or disjunctivity for pi;
- occurrence of every decimal word in pi.

The proved prose chain is exactly (2) -> (12) -> (15) -> (16) -> (17) ->
(29)/(39), with the pi comparison supplied separately by (43)--(48).
