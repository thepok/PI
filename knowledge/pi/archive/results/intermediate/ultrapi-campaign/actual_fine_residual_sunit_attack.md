# Actual fine residual: affine closure and the S-unit boundary

Audit date: **2026-08-12 UTC**  
Literature-search cutoff: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local source contains no external source URL,
so none is invented here.  
Inputs: [the balanced selector note](machin_selector_multiscale.md),
[the actual numerator-phase note](actual_numerator_phase_attack.md), T38, T40,
T46, and the T48--T51 prime-band calculations.

## Outcome and claim status

No proof that every finite decimal word occurs in \(\pi\) was obtained. The
canonical target remains a `conjecture`.

The useful result is a sharp `proof sketch` closure of the last fine
residual. At balanced selector depth, its character is exactly

\[
 e\!\left({R_j\over F_j}\right)
 =e\!\left(q_j10^j\pi-q_js_j-{L_j\over h_j}\right),       \tag{1}
\]

where \(q_j\asymp\sqrt j\), \(s_j\) is T38's geometrically small Machin
error, and \(L_j/h_j\) is the explicit three-adic leading staircase. Thus
the allegedly residual Archimedean phase is a coordinate copy of the linked
fixed-\(\pi\) phase \(q_j10^j\pi\). The exact twelve-term forcing does give
an affine cross-index recurrence, but conjugating away that forcing gives
(1), not an algebraic \(S\)-unit orbit.

Three further exact findings delimit the route.

1. Within one fixed-denominator pulse, the residual obeys multiplication by
   ten modulo \(F_j\). This is an expanding decimal orbit, not a contraction.
2. Every certified prime-band residue gives an explicit local component of
   \(R_j\), and their CRT product reconstructs the single character in (1).
   There is no average over the primes.
3. The twelve forcing summands are units in a **changing** \(S_j\)-group,
   but their sum need not be an \(S_j\)-unit. More decisively,
   \(R_j/F_j\) is generally not an \(S(F_j)\)-unit at all: its numerator has
   unknown prime support. Enlarging \(S\) to include that support makes the
   group depend on the very actual residual one is trying to control.

There is one nontrivial positive cross-index result. The product of T48's
upper-half seed primes is a fixed shared factor for a block of
\(\lfloor j/2+O(1)\rfloor\) later indices, and the actual residual projected
to that factor obeys a pure multiplicative recurrence. Its logarithm is
\(6j+o(j)\), so this is much stronger than the generic depth-lift algebra.
The update is nevertheless a permutation, and the complementary CRT factor
still carries exactly the phase in (1); no contraction follows.

The bounded primary-source audit below is `literature-checked` as of the
displayed cutoff. It found no \(S\)-unit, Subspace-Theorem, or large-sieve
result that controls (1) at the forbidden-word scale. This label applies to
the recorded audit, not to V1 and not to a claim that all literature has been
exhausted.

The companion computation is an `experiment`. Finite checks are never used
as proof.

## 1. Normalized statement and quantifiers

The canonical V1 statement is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^m\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.              \tag{2}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed,
and \(m=0\) is vacuous. This is finite contiguous occurrence, not normality,
subsequence occurrence, or occurrence of every infinite tail.

The needed new estimate has unusually rigid quantifiers: one fixed word,
the one actual Machin numerator at every selected index, balanced depth
\(k_j=\lfloor a_j/2\rfloor\), natural shadow length
\(2j+|w|-1\), and signed cancellation at its actual phase. An average over
other numerators, other shifts, or other \(S\)-units cannot replace that
pointwise statement.

## 2. Exact residual and its fixed-\(\pi\) character

Put

\[
 y_j=10^jM_{3j},\qquad x_j=\{y_j\}={b_j\over Q_j},
 \qquad Q_j=F_jD_j,                               \tag{3}
\]

where \(b_j/Q_j\) is reduced and \(D_j\) is the complete three-primary
part. T52 gives

\[
 3^{a_j}\le12j+3<3^{a_j+1},\qquad D_j=3^{a_j-1}.
                                                               \tag{4}
\]

At balanced depth define

\[
 k_j=\lfloor a_j/2\rfloor,\qquad h_j=3^{k_j},
 \qquad q_j={D_j\over h_j}.                       \tag{5}
\]

Split the actual numerator as

\[
 b_j=F_jc_j+r_j,\qquad0\le c_j<D_j,\qquad0\le r_j<F_j.      \tag{6}
\]

Let \(L_j\in\{0,\ldots,h_j-1\}\) represent \(D_jy_j\) modulo
\(h_j\) in \(\mathbb Z_{(3)}\), and let
\(C_j\in\{0,\ldots,h_j-1\}\) represent \(c_j\) modulo \(h_j\).
The selector identity is

\[
 C_j+r_jF_j^{-1}\equiv L_j\pmod {h_j}.            \tag{7}
\]

Consequently

\[
 R_j:={F_j(C_j-L_j)+r_j\over h_j}\in\mathbb Z.   \tag{8}
\]

Writing

\[
 \beta_j=\{q_jx_j\},                              \tag{9}
\]

direct Euclidean division gives the exact real equality

\[
 \boxed{\beta_j={L_j\over h_j}+{R_j\over F_j}.}   \tag{10}
\]

Now let

\[
 s_j=10^j(\pi-M_{3j})                              \tag{11}
\]

be T38's sampled error. Then \(y_j=10^j\pi-s_j\). Since
\(q_jx_j\equiv q_jy_j\pmod1\), (10) yields, for every integer
frequency \(\ell\),

\[
 \boxed{
 e\!\left({\ell R_j\over F_j}\right)
 =e\!\left(\ell q_j10^j\pi-\ell q_js_j
             -{\ell L_j\over h_j}\right).}       \tag{12}
\]

This is the decisive closure. The right side has an explicit root of unity
and a geometrically small explicit correction, but its main factor is the
actual linked lacunary phase

\[
                         e(\ell q_j10^j\pi).       \tag{13}
\]

Thus an estimate excluding \(R_j/F_j\) from the relevant digital major arcs
would be an estimate about (13). Replacing the left side by CRT coordinates
does not make the multiplier of \(10^j\) algebraic and does not average the
fixed number \(\pi\).

## 3. Every known prime-band residue in residual coordinates

Let \(p\mid F_j\) be a certified prime occurring to exponent one, and set

\[
 u_{j,p}\equiv p y_j\pmod p.                       \tag{14}
\]

The congruence is read in the usual localization at \(p\). Additive CRT for
the reduced numerator gives

\[
 r_j(F_j/p)^{-1}\equiv D_ju_{j,p}\pmod p.          \tag{15}
\]

Reducing (8) modulo \(p\), using \(D_j=h_jq_j\), gives the residual form

\[
 \boxed{R_j(F_j/p)^{-1}\equiv q_ju_{j,p}\pmod p.} \tag{16}
\]

For a prime in the band

\[
 {12j+3\over2r+1}<p\le {12j+3\over2r-1}           \tag{17}
\]

which satisfies the exact endpoint and coefficient hypotheses from the
general prime-band calculation,

\[
 u_{j,p}\equiv10^j\chi_4(p)C_r\pmod p.            \tag{18}
\]

Therefore every such known local component is

\[
 \boxed{
 R_j(F_j/p)^{-1}
 \equiv q_j10^j\chi_4(p)C_r\pmod p.}              \tag{19}
\]

Let \(P_j\mid F_j\) be the squarefree product of all certified primes in
use and write \(F_j=F_{0,j}P_j\). With
\(e_m(z)=e(z/m)\), additive CRT turns (19) into

\[
 e\!\left({\ell R_j\over F_j}\right)
 =e_{F_{0,j}}(\ell z_{0,j})
   \prod_{p\mid P_j}
   e_p\!\left(\ell q_j10^j\chi_4(p)C_{r(p)}\right),          \tag{20}
\]

where \(z_{0,j}\equiv R_jP_j^{-1}\pmod {F_{0,j}}\). This is an
exact use of all known band residues, not a heuristic independence model.
The product in (20) is exactly the one unit-modulus character in (12).
There is no summation over \(p\), so neither orthogonality nor square-root
cancellation follows from multiplying the local factors.

## 4. Within-pulse recurrence: multiplication by ten, not contraction

Fix \(j\) and keep \(F_j,h_j,q_j\) fixed. For \(t\ge0\), put

\[
 \beta_{j,t}=\{q_j10^tx_j\},\qquad
 L_{j,t}\equiv10^tL_j\pmod {h_j},\qquad0\le L_{j,t}<h_j,    \tag{21}
\]

and define \(R_{j,t}\in\mathbb Z\) by

\[
 \beta_{j,t}={L_{j,t}\over h_j}+{R_{j,t}\over F_j}.         \tag{22}
\]

Let

\[
 v_{j,t}={10L_{j,t}-L_{j,t+1}\over h_j}\in\{0,\ldots,9\},
 \qquad
 \delta_{j,t}=\lfloor10\beta_{j,t}\rfloor\in\{0,\ldots,9\}.            \tag{23}
\]

Comparing (22) at two consecutive times gives

\[
 \boxed{
 R_{j,t+1}=10R_{j,t}+F_j(v_{j,t}-\delta_{j,t}),
 \qquad R_{j,t}\equiv10^tR_j\pmod {F_j}.}         \tag{24}
\]

In particular,

\[
 e\!\left({\ell R_{j,t}\over F_j}\right)
 =e\!\left({\ell10^tR_j\over F_j}\right).        \tag{25}
\]

The factor ten is not even a unit on the large 5-primary part of \(F_j\);
on every certified nonbase prime it is a unit but merely permutes a
multiplicative orbit. Formula (24) has no factor of absolute value smaller
than one. The integers \(\delta_{j,t}\) are decimal carries, so treating them
as a harmless error would delete the digit information being sought.

Equation (19) propagates correspondingly:

\[
 R_{j,t}(F_j/p)^{-1}
 \equiv10^tq_ju_{j,p}\pmod p.                     \tag{26}
\]

Thus the complete local information evolves coherently, but it still
reconstructs one selected orbit rather than an averaged family.

## 5. Cross-index recurrence with the exact twelve-term forcing

Define

\[
 T_q(n)={(-1)^n\over(2n+1)q^{2n+1}}.              \tag{27}
\]

T40's exact forcing is

\[
 \boxed{
 \begin{aligned}
 \Delta_j:=y_{j+1}-10y_j
 =10^{j+1}\bigg(&16\sum_{u=0}^{5}T_5(6j+2+u)\\
                 &-4\sum_{u=0}^{5}T_{239}(6j+3+u)\bigg).
 \end{aligned}}                                  \tag{28}
\]

For balanced depth,

\[
 \sigma_j={q_{j+1}\over q_j}\in\{1,3\}.          \tag{29}
\]

The sampled phases therefore satisfy

\[
 \beta_{j+1}=\{10\sigma_j\beta_j+q_{j+1}\Delta_j\}.         \tag{30}
\]

Set

\[
 \Omega_j={10\sigma_jL_j\over h_j}
            +q_{j+1}\Delta_j-{L_{j+1}\over h_{j+1}},         \tag{31}
\]

and let

\[
 m_j=\left\lfloor10\sigma_j\beta_j+q_{j+1}\Delta_j\right\rfloor.
                                                               \tag{32}
\]

Substitution of (10) into (30) gives the exact affine residual recurrence

\[
 \boxed{
 {R_{j+1}\over F_{j+1}}
 =10\sigma_j{R_j\over F_j}+\Omega_j-m_j.}         \tag{33}
\]

At character level,

\[
 e\!\left({\ell R_{j+1}\over F_{j+1}}\right)
 =e\!\left({10\sigma_j\ell R_j\over F_j}\right)e(\ell\Omega_j).         \tag{34}
\]

This is the strongest valid cross-index closure found in this attack. It is
not a multiplicative \(S\)-unit recurrence:

- the rational modulus changes from \(F_j\) to a generally nonnested
  \(F_{j+1}\);
- the update is additive and includes the actual Archimedean carry \(m_j\);
- \(\Omega_j\) is a sum of twelve rational terms plus roots of unity; and
- conjugating the additive forcing away recovers (12), whose coefficient is
  the transcendental number \(\pi\).

### 5.1 Strongest fixed/shared-factor specialization

There is a genuine actual-Machin consequence beyond the formal affine
identity (33). Put

\[
 B=12j+3,
 \qquad
 G_j=\prod_{\substack{B/2<p\le B\\p\ \mathrm{prime},\
 p\notin\{239,317\}}}p.
                                                               \tag{35a}
\]

T48 gives \(p\Vert F_j\) for every factor \(p\mid G_j\). Let \(T\ge0\)
satisfy

\[
                         24T+4\le B.              \tag{35b}
\]

For \(0\le u<T\), every odd linear denominator in \(\Delta_{j+u}\) lies
between

\[
                         B+12u+2\quad\hbox{and}\quad B+12u+14.              \tag{35c}
\]

It is larger than \(p\). It is also smaller than \(3p\): the largest one is
\(B+12T+2\), and (35b), together with \(2p>B\), gives

\[
 2(B+12T+2)\le3B<6p.
\]

The only multiple of \(p\) strictly between \(p\) and \(3p\) is \(2p\),
which is even, whereas every number in (35c) is odd. Thus
\(\Delta_{j+u}\) is \(p\)-integral. Since
\(v_p(y_{j+u})=-1\), the unequal-valuation rule applied to
\(y_{j+u+1}=10y_{j+u}+\Delta_{j+u}\) shows inductively that

\[
                         p\Vert F_{j+u}\qquad(0\le u\le T).                 \tag{35d}
\]

Hence \(G_j\) is a unitary divisor of every \(F_{j+u}\) in the block. Define
the additive-CRT projection of the residual by

\[
 A_{j+u}^{(G_j)}\equiv
 R_{j+u}\left(F_{j+u}/G_j\right)^{-1}\pmod {G_j}.             \tag{35e}
\]

This normalization is not the same as the single-prime normalization in
(16). For \(p\mid G_j\),

\[
 {F_i\over G_j}={F_i/p\over G_j/p}
 \quad\Longrightarrow\quad
 A_i^{(G_j)}\equiv {G_j\over p}\,
 R_i(F_i/p)^{-1}\pmod p.                         \tag{35e'}
\]

The factor \(G_j/p\) is independent of \(i\) and is a unit modulo \(p\).
It therefore appears on both sides of the local recurrence and cancels.
This is the exact CRT-normalization step needed below; identifying
\(A_i^{(G_j)}\bmod p\) directly with the single-prime coordinate would be
incorrect.

For a single shared prime, write

\[
 Z_{i,p}=R_i(F_i/p)^{-1}\pmod p,\qquad
 W_{i,p}=p\Delta_i\pmod p.                       \tag{35f}
\]

Whenever both seed valuations are \(-1\) and \(v_p(\Delta_i)\ge-1\), the
actual seed recurrence and (16) give the exact local formula

\[
 \boxed{
 Z_{i+1,p}\equiv
 10\sigma_i Z_{i,p}+q_{i+1}W_{i,p}\pmod p.}       \tag{35g}
\]

On the block (35b), \(W_{i,p}=0\). Combining (35g) over all
\(p\mid G_j\) by CRT gives

\[
 \boxed{
 A_{j+u+1}^{(G_j)}\equiv
 10\sigma_{j+u}A_{j+u}^{(G_j)}\pmod {G_j}.}       \tag{35h}
\]

Equivalently,

\[
 A_{j+t}^{(G_j)}\equiv
 10^tq_{j+t}q_j^{-1}A_j^{(G_j)}\pmod {G_j}
 \qquad(0\le t\le T).                            \tag{35i}
\]

The inverses exist because \(G_j\) is prime to \(30\). The prime number
theorem gives

\[
 \log G_j=\vartheta(B)-\vartheta(B/2)+O(1)=6j+o(j).            \tag{35j}
\]

Thus (35h) is a large, fixed-modulus, actual-Machin recurrence lasting
\(T=\lfloor(B-4)/24\rfloor=j/2+O(1)\) transitions. It is not tautological
and is the strongest exact fixed-factor formula obtained here.

It still does not contract. Multiplication by \(10\sigma_i\) is a
permutation of \(\mathbb Z/G_j\mathbb Z\), and the full phase factors as

\[
 e\!\left({R_i\over F_i}\right)
 =e_{G_j}\!\left(A_i^{(G_j)}\right)
  e_{F_i/G_j}(B_i^*)                               \tag{35k}
\]

for the complementary actual CRT coordinate \(B_i^*\). A bound for the
first factor alone cannot bound a sum of the products in (35k); the second
factor may align with it. In the actual Machin instantiation their product
is exactly (12), so declaring the complement “arbitrary” would be invalid,
while ignoring it would be circular.

### 5.2 Actual Machin content versus generic T56/T57 algebra

The distinction is important.

- T56's generic residual lift assumes integer identities at two selector
  depths and derives \(3R'=R+F(u-v)\). It keeps one arbitrary \(F\) and says
  nothing about a Machin seed, a Taylor window, or a factor shared by
  different indices.
- T57's generic fixed-depth decimal transport derives
  \(R'=10R+F(v-a)\) after its carry identities are supplied. It likewise
  keeps one arbitrary modulus and contains no prime-survival input.
- Equations (33) and (35g)--(35i) instantiate the actual rational seeds,
  the exact T40 forcing, T48 survival, balanced \(q_i\), and changing reduced
  denominators. In particular, (35d) is arithmetic information absent from
  the generic algebra.

What remains generic even after this instantiation is the absence of decay:
all three recurrences transport one selected residue by a unit (with explicit
impulses when present). None averages residue classes or estimates the
complementary character in (35k).

## 6. Why this is not a fixed-rank S-unit problem

Each individual term in (28) is a unit in the rational \(S_j\)-group with

\[
 \begin{aligned}
 S_j=\{2,5,239\}\ \cup\!!
 &\bigcup_{u=0}^{5}\{p:p\mid12j+5+2u\}\\
 {}\cup\!!
 &\bigcup_{u=0}^{5}\{p:p\mid12j+7+2u\}.          \tag{35}
 \end{aligned}
\]

Consequently \(\Delta_j\) has denominator supported on \(S_j\). A sum of
twelve \(S_j\)-units need not itself be an \(S_j\)-unit: cancellation can
introduce unrestricted numerator primes. Across a pulse, the relevant set is
\(\bigcup S_{j+u}\), which changes and grows with the pulse.

There is an even more direct failure for the actual residual. Reducedness of
\(b_j/Q_j\) gives \((r_j,F_j)=1\). Reducing (8) modulo \(F_j\) gives

\[
 h_jR_j\equiv r_j\pmod {F_j}.
\]

Since \((h_j,F_j)=1\),

\[
                         (R_j,F_j)=1.              \tag{36}
\]

Let \(S(F_j)\) be the prime divisors of \(F_j\). The rational number
\(R_j/F_j\) is an \(S(F_j)\)-unit only in the exceptional case
\(|R_j|=1\); every prime divisor of its numerator lies outside
\(S(F_j)\) by (36). To force membership one must enlarge \(S\) by the prime
support of the actual integer \(R_j\), which is neither controlled by the
denominator theorem nor fixed with \(j\).

The growing-band `proof sketch` supplies almost every prime above
\(B_j=o(j)\) up to \(12j+3\). By the prime number theorem, the denominator
support already contains

\[
                         (12+o(1)){j\over\log j}   \tag{37}
\]

distinct certified primes. Thus even before adding numerator primes, the
natural multiplicative rank tends to infinity. This is not merely a poor
constant in a fixed-\(S\) theorem; the group itself changes with the seed.

## 7. Primary-source applicability audit (`literature-checked`)

The searches used combinations of “S-unit equation”, “multiplicative group
rank”, “Subspace Theorem fractional parts”, “powers algebraic number”,
“restricted digits complexity”, and “large sieve separated phases”. Only
primary papers are used for the technical conclusions below.

### Evertse--Schlickewei--Schmidt: exact equations, changing rank

Primary source: J.-H. Evertse, H. P. Schlickewei, and W. M. Schmidt,
[*Linear equations in variables which lie in a multiplicative group*](https://arxiv.org/abs/math/0409604),
Annals of Mathematics 155 (2002), 807--836,
[journal page](https://annals.math.princeton.edu/2002/155-3/p04).

Exact locator: Theorem 1.1, equation (1.2), printed pages 809--810. For a
fixed subgroup \(\Gamma\subset(K^*)^n\) of finite rank \(r\), the number of
nondegenerate solutions of

\[
 a_1x_1+\cdots+a_nx_n=1
\]

is at most

\[
                    \exp((6n)^{3n}(r+1)).          \tag{38}
\]

Applicability: (38) counts exact solutions to one fixed linear equation in
one fixed finite-rank group. The Machin relation (33) changes its group,
coefficients, modulus, and carry with \(j\), while digital avoidance is an
inequality placing one phase in a union of exponentially many intervals.
Even a forced encoding with \(n=12\) would have rank at least the scale in
(37), so (38) grows like \(\exp(Cj/\log j)\), vastly larger than the one
row per index that would need to be excluded. It supplies no pointwise
Fourier cancellation.

### Corvaja--Zannier: algebraic fixed groups and near-integers

Primary source: P. Corvaja and U. Zannier,
[*On the rational approximations to the powers of an algebraic number*](https://arxiv.org/abs/math/0403522),
Acta Mathematica 193 (2004), 175--191.

Exact locators: Theorem 1 on printed page 177 and the Main Theorem,
equation (1.1), on printed page 179. The Main Theorem fixes a finitely
generated group \(\Gamma\subset\overline{\mathbb Q}^{\,*}\), an algebraic
\(\delta\ne0\), and controls exceptionally small distances
\(\|\delta qu\|\) for \(u\in\Gamma\), apart from pseudo-Pisot behavior.

Applicability fails twice. In (12), the fixed coefficient needed to put the
main orbit into that framework is \(\delta=\pi\), which is transcendental.
Moreover, avoidance of one finite word does not imply exponentially small
distance to the nearest integer. It places a point in a positive-entropy
subshift, a union of many ordinary decimal cylinders. The hypotheses of the
Main Theorem therefore do not encode the required digital major arcs.

### Adamczewski--Bugeaud: low complexity does not mean one missing word

Primary source: B. Adamczewski and Y. Bugeaud,
[*On the complexity of algebraic numbers I. Expansions in integer bases*](https://arxiv.org/abs/math/0511674),
Annals of Mathematics 165 (2007), 547--565.

Exact locator: Theorem 1 on printed page 550. If \(p(n)\) is the block
complexity of an irrational algebraic number, then

\[
                         \liminf_{n\to\infty}{p(n)\over n}=\infty.          \tag{39}
\]

Applicability: \(\pi\) is not algebraic, and a sequence avoiding one fixed
word still has exponential block complexity. Such a sequence satisfies
(39) by an enormous margin. The theorem separates automatic or linear
complexity, not the positive-entropy missing-word language relevant to V1.

### Montgomery--Vaughan: an average cannot select the actual phase

Primary source: H. L. Montgomery and R. C. Vaughan,
[*The large sieve*](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf),
Mathematika 20 (1973), 119--134,
[DOI 10.1112/S0025579300004708](https://doi.org/10.1112/S0025579300004708).

Exact locator: Theorem 1, equation (1.4), printed page 119. If
\(x_1,\ldots,x_R\) are \(\delta\)-separated modulo one and
\(S(x)=\sum_{n=M+1}^{M+N}a_ne(nx)\), then

\[
 \sum_{r=1}^{R}|S(x_r)|^2
 \le (N+\delta^{-1})\sum_{n=M+1}^{M+N}|a_n|^2.    \tag{40}
\]

Applicability: the residual problem has one selected point \(R_j/F_j\).
With one point, (40) gives no pointwise cancellation beyond Cauchy--Schwarz.
Averaging over all CRT lifts can show that most lifts behave well, while the
actual lift may be exceptional. Pooling different \(j\) also fails directly:
the digital coefficient vector and its length change with \(j\), and no
useful separation of the actual phases is known. The denominator-only Farey
guarantee is merely \(\delta\ge1/(F_iF_j)\) for two distinct fractions,
whose \(\delta^{-1}\) term is far beyond the natural decimal scale here.

## 8. Two proof-level separators and their exact limits

The first separator uses the full actual forcing. T38 gives

\[
                         \Delta_j=10s_j-s_{j+1}.   \tag{41}
\]

For any real \(\theta\), define

\[
 z_j(\theta)=\{10^j\theta-s_j\}.                  \tag{42}
\]

Then

\[
 z_{j+1}(\theta)=\{10z_j(\theta)+\Delta_j\}.      \tag{43}
\]

Taking \(\theta=1/3\), one has \(10^j\theta\equiv1/3\pmod1\), so
\(z_j(1/3)=1/3-s_j\) for all sufficiently large \(j\). It eventually
avoids the decimal cell \([0,1/10)\). Hence even the entire exact sequence
of twelve-term forcing values does not imply all-cell recurrence. This
separator does not preserve rational Machin denominators or their local
residues; that is its precise limit.

The second separator concerns denominator support. Suppose a modulus \(F\)
has

\[
 \log F\ge12j-o(j),\qquad\omega(F)=o(j).           \tag{44}
\]

Kanold's Jacobsthal bound \(J(F)\le2^{\omega(F)}\) supplies an integer
\(R\) coprime to \(F\) within \(J(F)\) of any prescribed location, in
particular a location making \(L/h+R/F\) arbitrarily close to \(1/9\).
Equations (44) give

\[
 {J(F)\over F}=\exp(-12j+o(j)).                    \tag{45}
\]

After fewer than \(2j\) multiplications by ten, this error is still
\(\exp(-(12-2\log10)j+o(j))\), eventually less than the distance from
\(1/9\) to the boundary of the digit-1 cell. Thus primitive residuals with
the same denominator-size and prime-support profile can follow an all-1
pulse under the exact within-pulse dynamics (24).

This second separator deliberately changes the actual local residues (19).
It proves that \(S\)-support, rank, reducedness, and multiplication by ten
cannot replace those residues. Conversely, once every actual local component
is imposed, CRT selects the one phase (20), and (12) identifies the missing
Archimedean assertion with the linked \(\pi\)-phase itself. The route has no
intermediate generic \(S\)-unit theorem left to invoke.

## 9. Exact finite audit (`experiment`)

[`actual_fine_residual_sunit_check.py`](actual_fine_residual_sunit_check.py)
uses only exact integers and `Fraction`. It checks:

- residual integrality, recombination (10), and the character form preceding
  (12);
- the within-pulse recurrence (24) and multiplication-by-ten congruence;
- all twelve forcing terms in (28) and their denominator support (35);
- the cross-index affine recurrence (33) and shared-prime formula (35g);
- T48 upper-half survival and the local residual formula (16), using
  \(C_1=3804/1195\); and
- fixed upper-half prime persistence (35d) and the shared-factor recurrence
  (35h) over every complete block available in the checked range, including
  the normalization factor \(G_j/p\) in (35e').

Retained run:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
j_range=2..80
balanced_seed_character_identities=79
within_pulse_residual_recurrences=1896
twelve_term_forcing_windows=79
forcing_denominator_support_checks=79
cross_index_residual_recurrences=79
shared_prime_affine_recurrences=6465
upper_half_local_residual_components=3069
shared_upper_prime_persistence_checks=43799
shared_crt_normalization_checks=87598
fixed_shared_factor_recurrences=1027
observed_forcing_support_rank=165
all exact checks passed
```

Reproduction:

```bash
python3 -m py_compile \
  work/ultrapi-resume/actual_fine_residual_sunit_check.py
python3 work/ultrapi-resume/actual_fine_residual_sunit_check.py \
  --max-j 80 --pulse-steps 24
```

Checker SHA-256:
`67831ce9d74e9eeaa40b24ad23bc5fca170862a9bbc6f54b07d1f8a47c2df0b7`.

The observed support rank is finite evidence only. It is not used for the
asymptotic rank statement (37), which comes from the prime-band argument and
the prime number theorem.

## 10. Precise remaining theorem

This attack rules out a generic fixed-rank \(S\)-unit or large-sieve
shortcut, but it does not rule out new arithmetic information special to
\(\pi\). A valid continuation must prove something not shared by the two
separators, for example:

1. a signed estimate for the digital Fourier reconstruction at
   \(e(q_j10^j\pi)\), uniformly at the linked balanced scales;
2. a theorem coupling the complete actual prime-band residue vector (19) to
   an Archimedean interval exclusion, rather than merely reconstructing it by
   CRT; or
3. a genuinely new distribution theorem for the sparse linked sequence
   \(q_j10^j\pi\), strong enough to force one valid forbidden-word shadow
   count below one.

An exact recurrence, a larger \(S\), more denominator factors, a fixed-rank
unit-equation count, or an average over alternative phases does not meet this
target.

## Bottom line

The actual fine residual is now closed both locally and across indices. Its
known prime-band components evolve by exact rational recurrences; on the
large fixed factor (35a) they even follow the pure actual-Machin orbit
(35h). Their complete CRT product is nevertheless the fixed-\(\pi\)
character (12). Available \(S\)-unit and
Subspace theorems concern fixed algebraic groups or near-integer inequalities;
the large sieve averages separated phases. None controls this one linked
transcendental phase against a positive-entropy forbidden-word automaton.
This is meaningful obstruction work at `proof sketch` and
`literature-checked` status, not a proof of V1, a `candidate resolution`, or
a `verified resolution`.
