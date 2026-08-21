# T32: joint T24 extraction at adjacent nodes of one T26 chain

## Status and scope

**OPEN WITH ONE NAMED MIXED-OVERLAP GAP.**

This note uses only the kernel-checked T24, T26, and T28 modules pinned in
`DEPENDENCIES.sha256`. It neither assumes nor concludes canonical A1. It gives
no unconditional existence assertion about a resonance chain for pi. Instead,
it fixes an object in the exact fixed-pi chain domain used by T26 and T28 and
tests what T24's two nodewise conclusions imply there. No synthetic phase is
introduced.

The canonical statement is the ordered, diagonal-inclusive fixed-pi question
in `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its checked SHA-256 is
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.

## 1. Normalized setup and quantifiers

Fix natural numbers

\[
  M,D,K,d,h,r
\]

with

\[
  1\le D,\qquad 1\le d,\qquad 1\le h,\qquad 1\le r,
  \tag{1}
\]

and fix

\[
 \mathcal C:
 \operatorname{GeometricResonanceChain}
   (\operatorname{initialCoefficient}(h,r),M,D,1,K,d,\{r\}).
 \tag{2}
\]

Here, exactly as in T26,

\[
 \operatorname{initialCoefficient}(h,r)
   =h(10^r-1)\pi.
 \tag{3}
\]

Thus (2) is a genuine fixed-pi T26 chain type, not a chain with freely chosen
real phases. Assume also the length request used by T26's nodewise inverse
theorem,

\[
 2\,\operatorname{densityDenominator}(D,d)^2\le K.
 \tag{4}
\]

Fix `k : Fin d`; equivalently, fix an integer \(k\) with

\[
 0\le k<d.
 \tag{5}
\]

The consecutive prefix nodes are \(k\) and \(k+1\). Define

\[
\begin{aligned}
 t&:=\mathcal C.\operatorname{shiftAt}(k),&
 U&:=10^t-1,\\
 \beta _0&:=\mathcal C.\operatorname{nodeCoefficient}(k),&
 \beta _1&:=\mathcal C.\operatorname{nodeCoefficient}(k+1),\\
 M_0&:=\mathcal C.\operatorname{nodeResidual}(k),&
 M_1&:=\mathcal C.\operatorname{nodeResidual}(k+1),\\
 D_0&:=\operatorname{densityDenominator}(D,k),&
 D_1&:=\operatorname{densityDenominator}(D,k+1),\\
 \tau _0&:=\frac1{8D_0^2},&
 \tau _1&:=\frac1{8D_1^2},\\
 \varepsilon _0&:=\frac{\arccos(\tau _0)}{2\pi},&
 \varepsilon _1&:=\frac{\arccos(\tau _1)}{2\pi}.
\end{aligned}
\tag{6}
\]

These are precisely T26's `nodeTau` and T24's `inverseError` at the two
nodes. T24's positivity argument, as used in T26, gives

\[
 D_0,D_1\ge1,\qquad 0<\tau _0,\tau _1<1,
 \qquad \varepsilon _0,\varepsilon _1>0.
 \tag{7}
\]

T28's `nodeCoefficient_succ` and
`nodeCoefficient_eq_multiplier_pi` give the exact identities

\[
 \beta _1=U\beta _0,
 \qquad
 \beta _0=C\pi,
 \qquad
 C:=\operatorname{nodeMultiplier}(h,r,\mathcal C.\mathrm{shifts},k).
 \tag{8}
\]

By (1) and the chain's shift lower bound, T28's positivity lemmas give

\[
 C\ge1,\qquad U\ge1.
 \tag{9}
\]

From T28's exact prefix identity
`take_succ_eq`, followed by `List.sum_append` and `Nat.sub_sub`,

\[
 M_1=M_0-t,
 \qquad\text{hence}\qquad M_1\le M_0.
 \tag{10}
\]

There are two possible readings of "one pair" which must not be conflated.
Here it means one common **index pair** \((j,s)\); the nearest integers
\(a_0,a_1\) at the two nodes may differ. The preperiod is \(j\ge0\), so the
pure-cycle case is exactly \(j=0\); the period always satisfies \(s\ge1\).

## 2. Common legal domain and exact T24 predicates

For \(j,s\in\mathbb N\), put

\[
 Q(j,s):=10^j(10^s-1).
 \tag{11}
\]

Define the common legal index-pair domain

\[
 \Omega_k:=\{(j,s)\in\mathbb N^2:
  1\le s,\ j+s<M_0,\ j+s<M_1\}.
 \tag{12}
\]

By (10), this is equivalently

\[
 \Omega_k=\{(j,s)\in\mathbb N^2:1\le s,\ j+s<M_1\},
 \tag{13}
\]

but both residual inequalities are retained in (12) so that every T28 range
can be checked literally.

For \(\ell\in\{0,1\}\), an integer \(a\), and \((j,s)\in\Omega_k\), define
the signed and absolute scaled errors

\[
 \xi_\ell(j,s,a):=Q(j,s)\beta_\ell-a,
 \qquad
 e_\ell(j,s,a):=|\xi_\ell(j,s,a)|.
 \tag{14}
\]

The two exact T24 good-pair predicates, restricted to their common domain,
are

\[
 \begin{aligned}
 G_0(j,s)&:\Longleftrightarrow
   (j,s)\in\Omega_k\ \land\
   \exists a_0\in\mathbb Z,
       e_0(j,s,a_0)<\varepsilon _0,\\
 G_1(j,s)&:\Longleftrightarrow
   (j,s)\in\Omega_k\ \land\
   \exists a_1\in\mathbb Z,
       e_1(j,s,a_1)<\varepsilon _1.
 \end{aligned}
 \tag{15}
\]

To check that (15) is exactly T24-shaped, T24 defines

\[
 \left|\beta_\ell-\frac{a_\ell}
 {10^j(10^s-1)}\right|
 <\frac{\varepsilon _\ell}{10^j(10^s-1)}.
 \tag{16}
\]

For \(s\ge1\), T28's `decimalDenominatorNat_pos` and
`decimalDenominatorNat_cast` say that the denominator in (16) is the positive
real cast of \(Q(j,s)\). Multiplication by this positive denominator makes
(16) equivalent, in both directions, to

\[
 |Q(j,s)\beta_\ell-a_\ell|<\varepsilon _\ell,
 \tag{17}
\]

which is precisely (15).

T24's `CycleApproximation` chooses \(j=0\), \(1\le s\), and \(s<M_\ell\).
Its `PositivePreperiodApproximation` chooses \(1\le j\), \(1\le s\), and
\(j+s<M_\ell\). Consequently, T26's
`GeometricResonanceChain.nodewise_inverse_necessaryOnly`, under (1)--(4),
gives separately at each node

\[
 \exists j_\ell,s_\ell\in\mathbb N,\ \exists a_\ell\in\mathbb Z:
 1\le s_\ell,\quad j_\ell+s_\ell<M_\ell,\quad
 e_\ell(j_\ell,s_\ell,a_\ell)<\varepsilon _\ell.
 \tag{18}
\]

The node-1 witness in (18) lies in \(\Omega_k\), by (10), so T24/T26 do
imply that \(G_1\) is nonempty. The node-0 witness need not satisfy
\(j_0+s_0<M_1\), and (18) does not make the two index pairs equal.

## 3. The one named mixed-overlap inequality

The following single inequality packages exactly the common-index and weighted
error information needed by T28.

**Joint weighted mixed-overlap inequality (JWMO).** There exist
\((j,s)\in\Omega_k\) and \(a_0,a_1\in\mathbb Z\) such that, with
\(Q=Q(j,s)\) and \(e_\ell=e_\ell(j,s,a_\ell)\),

\[
 \boxed{
 \max\!\left\{
   \frac{e_0}{\varepsilon _0},
   \frac{e_1}{\varepsilon _1},
   Qe_1+UQe_0
 \right\}<1.}
 \tag{JWMO}
\]

Because (7) makes both divisions legal, `(JWMO)` implies all three strict
inequalities

\[
 e_0<\varepsilon _0,
 \qquad e_1<\varepsilon _1,
 \qquad Qe_1+UQe_0<1.
 \tag{19}
\]

Thus its first two entries say exactly that the same \((j,s)\) satisfies both
predicates (15), while its third entry is T28's mixed error budget with
\(Q_0=Q_1=Q\). This is one explicit inequality, not two independently chosen
nodewise phases.

## 4. Conditional joint-extraction theorem

**Theorem.** In the fixed setup (1)--(10), `(JWMO)` implies

\[
 \operatorname{AdjacentPairCompatible}
   (\mathcal C,k,j,s,j,s,a_0,a_1).
 \tag{20}
\]

**Proof.** Expand T28's `AdjacentPairCompatible`. Its seven conjuncts become,
in order:

1. \(1\le s\);
2. \(j+s<M_0\);
3. \(1\le s\);
4. \(j+s<M_1\);
5. \(e_0<\operatorname{inverseError}(\operatorname{nodeTau}(D,k))
   =\varepsilon _0\);
6. \(e_1<\operatorname{inverseError}(\operatorname{nodeTau}(D,k+1))
   =\varepsilon _1\);
7. \(Qe_1+UQe_0<1\).

The first four are exactly membership in (12); the last three are (19).
This proves (20). \(\square\)

No further selection hypothesis is hidden in this theorem: both T28 node
indices are instantiated by the same \(j,s\), and both denominators are
literally \(Q(j,s)\).

## 5. Signed cancellation and T28 transport

For the witnesses in `(JWMO)`, the signed identity (8) gives

\[
\begin{aligned}
 z&:=Qa_1-UQa_0\\
  &=-Q(Q\beta _1-a_1)+UQ(Q\beta _0-a_0)\\
  &=-Q\xi_1+UQ\xi_0.
\end{aligned}
\tag{21}
\]

Here \(z\in\mathbb Z\), and the triangle inequality plus (19) gives the fully
signed-error bound

\[
 |z|\le Q|\xi_1|+UQ|\xi_0|
      =Qe_1+UQe_0<1.
 \tag{22}
\]

Therefore \(z=0\). This is exactly T28's `cross_node_cancellation` specialized
to equal index pairs:

\[
 Qa_1=UQa_0.
 \tag{23}
\]

Since \((j,s)\in\Omega_k\) implies \(s\ge1\), one has \(Q\ge1\), so integer
cancellation also gives

\[
 a_1=Ua_0.
 \tag{24}
\]

All preperiod and denominator ranges are explicit. Namely, (12) gives

\[
 j\ge0,\qquad 1\le s,
 \qquad j+s<M_1\le M_0.
 \tag{25}
\]

In particular \(M_1\ge2\), and

\[
 1\le Q=10^j(10^s-1)
   <10^{j+s}\le10^{M_1-1}.
 \tag{26}
\]

T28's selected denominator is, in this equal-pair specialization,

\[
 q:=\operatorname{selectedDenominator}(\mathcal C,k,j,s)
   =CUQ.
 \tag{27}
\]

Using (9) and (26),

\[
 1\le q<CU\,10^{M_1-1}.
 \tag{28}
\]

Finally T28's `compatible_pair_pi_error`, applied to (20), transports the pair
without an inequality loss:

\[
 \boxed{
 \left|\pi-\frac{a_1}{CUQ}\right|
   =\frac{e_0}{CQ}
   <\frac{\varepsilon _0}{CQ}.}
 \tag{29}
\]

Equations (23)--(24) also show directly that

\[
 \frac{a_1}{CUQ}=\frac{a_0}{CQ}.
 \tag{30}
\]

This completes every deterministic index, signed-error, cancellation, and
denominator step from `(JWMO)` to T28 compatibility and transport.

## 6. Exact endpoint

T24/T26 prove only the two separate existential statements (18). They do not
prove `(JWMO)`:

- the node-0 pair from (18) is not known to lie in the shorter common domain
  \(\Omega_k\);
- even if both restricted good-pair sets are nonempty, their intersection is
  not known to be nonempty;
- even for a common good pair, T24 gives only
  \(e_0<\varepsilon _0\) and \(e_1<\varepsilon _1\), whereas T28 additionally
  needs the weighted sum \(Qe_1+UQe_0<1\).

These are the three coordinates of the **single** displayed `(JWMO)`
inequality, not three untracked proof obligations. Once `(JWMO)` is assumed,
Sections 4--5 discharge every remaining clause by the kernel-checked T28
lemmas and explicit algebra. Neither T24 nor T26 contains a cardinality,
distribution, or cross-node phase-correlation estimate from which `(JWMO)`
can be derived. This note also gives no exact counterexample inside the
fixed-pi chain domain, so refutation would be unjustified.

**OPEN WITH ONE NAMED MIXED-OVERLAP GAP: the Joint weighted mixed-overlap
inequality `(JWMO)`.**
