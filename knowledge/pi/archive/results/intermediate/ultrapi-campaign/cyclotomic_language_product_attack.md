# Cyclotomic language-product and multiscale attack

Audit date: **2026-08-12 UTC**  
Status: local `proof sketch` separators with finite `experiment` checks  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

This branch sharpens the language-product construction, but it does **not**
prove V1.

Fix a decimal word \(w\), put \(q=10^n\), and let

\[
 {\cal A}_n(w)=\{3q+[u]_{10}:u\in\{0,\ldots,9\}^n
                         \text{ avoids }w\},\qquad N_n=|{\cal A}_n(w)|.
\]

The previous auxiliary polynomial was

\[
 {\cal E}_{n,w}(Z)=\prod_{p\in{\cal A}_n(w)}(1+Z^p)\in\mathbb Z[Z].       \tag{1}
\]

Its factors are cyclotomic, and their self-similar spacing gives much more
than the crude factorwise estimate.  Write

\[
 \alpha=\pi-3,\qquad z_n=e^{i/q},\qquad
 F_\alpha(x)=\log|1-e^{i(x-\alpha)}|.
\]

Then the exact logarithm is the finite-state logarithmic potential

\[
 \log|{\cal E}_{n,w}(z_n)|
 =\sum_{u\text{ avoids }w}F_\alpha([u]_{10}/q).                         \tag{2}
\]

Let \(\nu_w\) be the Perron--Frobenius Markov measure on infinite paths of
the word-avoidance automaton, pushed to \([0,1]\) by decimal evaluation.  If
the digits of \(\pi\) avoid \(w\), then a self-contained spacing argument
gives

\[
 \log|{\cal E}_{n,w}(z_n)|
   =N_n I_w(\alpha)+O_w(N_n\vartheta_w^n+n),
 \quad
 I_w(\alpha)=\int F_\alpha\,d\nu_w,\quad 0<\vartheta_w<1.                \tag{3}
\]

In particular,

\[
 \lim_{n\to\infty}-{1\over N_n}
       \log|{\cal E}_{n,w}(z_n)|=c_w(\alpha):=-I_w(\alpha).              \tag{4}
\]

This is the sharp constant-rate ledger.  It yields the requested rigorous
separator for this particular product.  Since

\[
 F_\alpha(x)\le \log\rho,\qquad
 \rho=-2\cos2=0.832293673\ldots<1,
\]

with strict inequality away from the single endpoint \(x=1\), the
non-atomic measure \(\nu_w\) satisfies

\[
 c_w(\alpha)>c_0:=-\log\rho=0.1835699279\ldots .                        \tag{5}
\]

Therefore any asymptotic lower bound for the **same actual product** of the
form

\[
 |{\cal E}_{n,w}(z_n)|\ge \exp(-C_wN_n+o(N_n))                          \tag{6}
\]

must have \(C_w\ge c_w(\alpha)>c_0\).  But comparison with the old upper
bound \(q^{-1}\rho^{N_n-1}\) would require \(C_w<c_0\).  Improving the old
factorwise lower bound to a spacing-, Jensen-, transfer-, or
Mahler-measure lower bound cannot cross: the best constant must reproduce
the product's actual logarithmic-potential constant, which is already on the
wrong side.

The actual prefix factor is visible exactly, but only below the exponential
scale.  For

\[
 p_n=\lfloor q\pi\rfloor,\qquad x_n=q\pi-p_n,
\]

its contribution is

\[
 \log|1+e^{ip_n/q}|
 =-\log q+\log x_n+O(q^{-2})=O(\log q).                                \tag{7}
\]

Thus the special selected path changes an \(O(N_n)\) bulk potential by an
\(O(\log q)\) singular term (and by subleading finite-state discrepancies).
A full-grid control calculation below gives the entire second-order term
exactly as \(\log|2\sin(\pi q\alpha)|+O(1)\).  The finite-state child/parent
ratio also cancels the bulk down to a path cocycle of size \(O_w(\log q)\),
but it is a quotient of two integer-polynomial values of the original
degree and height.  Clearing that quotient restores the full complexity.

The constructive outcome is therefore a sharp analytic description and a
constant-rate impossibility result for (1), not a contradiction.  V1 remains
a `conjecture`; this file is not a candidate resolution.

## 1. Normalized target and conditional setup

Write the canonical nonterminating decimal expansion

\[
 \pi=3+\sum_{j\ge1}d_j10^{-j},\qquad d_j\in\{0,\ldots,9\}.
\]

The target is

\[
 \forall m\ge1\ \forall w\in\{0,\ldots,9\}^m\ \exists k\ge1:
 d_kd_{k+1}\cdots d_{k+m-1}=w.                                       \tag{8}
\]

Leading zeroes are significant, occurrences start in the fractional
stream, and irrationality removes the terminating-decimal ambiguity.  This
branch fixes one nonempty \(w\) and assumes conditionally that it never
occurs.  Under that assumption, the length-\(n\) prefix of \(\alpha=\pi-3\)
belongs to the avoidance language for every \(n\).

For \(a=[u]_{10}\) and \(p=3q+a\), Euler's identity gives

\[
 1+e^{ip/q}
 =1+e^{i(3+a/q)}
 =1-e^{i(a/q-\alpha)}.                                                  \tag{9}
\]

Equation (2) follows immediately.  Unlike an expanded
Lindemann--Weierstrass form, (2) preserves the complete geometry of all
candidate nodes.

## 2. What the cyclotomic factorization really supplies

Every binomial in (1) has the exact factorization

\[
 1+Z^p={Z^{2p}-1\over Z^p-1}
      =\prod_{\substack{d\mid2p\\d\nmid p}}\Phi_d(Z).                   \tag{10}
\]

Consequently all zeros of \({\cal E}_{n,w}\) are roots of unity and

\[
 M({\cal E}_{n,w})=1,                                                   \tag{11}
\]

where \(M\) is Mahler measure.  For every \(0\le r<1\), Jensen's formula
also gives

\[
 {1\over2\pi}\int_0^{2\pi}
   \log|{\cal E}_{n,w}(re^{it})|\,dt=0,                                 \tag{12}
\]

because the constant term is one and all zeros lie on the unit circle.
This is an average identity, not a pointwise lower bound.  The very negative
value near \(z_n\) is compensated elsewhere on the circle.

The nearest root of \(1+Z^p\) to \(z_n\) is

\[
 \xi_p=e^{i\pi/p},\qquad
 \left|{1\over q}-{\pi\over p}\right|
 ={ |p-q\pi|\over pq}.                                                  \tag{13}
\]

As \(p\) runs through \([3q,4q)\), these roots occupy an arc of length
\(\Theta(q^{-1})\), adjacent roots have angular spacing
\(\Theta(q^{-2})\), and the selected root has distance
\(\Theta(x_nq^{-2})\) from \(z_n\).  Cyclotomicity therefore describes a
large root cluster at the evaluation point; it does not separate the point
from that cluster.

There is an additional resultant obstruction.  For \(g=(p,r)\),

\[
 \gcd(Z^p+1,Z^r+1)=
 \begin{cases}
   Z^g+1,&p/g\text{ and }r/g\text{ are both odd},\\
   1,&\text{otherwise}.
 \end{cases}                                                            \tag{14}
\]

Thus many binomials have common cyclotomic factors.  The discriminant of
the full product is then zero, while replacing the product by its squarefree
radical discards precisely the multiplicities responsible for its
exponential smallness.  Nonzero pairwise cyclotomic resultants constrain
distances among algebraic roots, not the distance from the transcendental
point \(e^{i/q}\) to the common root cluster.

Status of this section: `proof sketch`; (10) and (14) are checked exactly by
the companion program.

## 3. Exact transfer-matrix representation of the logarithm

Let the proper-prefix states of \(w\) be \(0,\ldots,m-1\).  For each digit
\(d\), let \(B_d\) be the zero-one matrix of legal KMP transitions and put

\[
 M=\sum_{d=0}^9B_d.                                                      \tag{15}
\]

The graph is primitive.  Every prefix state is reachable from state zero.
Choose a digit \(c\) different from both the first and last digits of \(w\).
Then reading \(c\) cannot complete \(w\), and reading it repeatedly for
\(m\) steps leaves no nonempty suffix which is a prefix of \(w\), so every
state reaches state zero; state zero itself has a \(c\)-loop.  Let
\(\lambda>1\)
be the Perron root and \(v>0\) a right Perron vector.  Define digit-labeled
Markov matrices by

\[
 (P_d)_{st}={(B_d)_{st}v_t\over\lambda v_s}.                             \tag{16}
\]

Their row sum is one.  The induced path measure, pushed forward by
\((d_j)\mapsto\sum d_j10^{-j}\), is \(\nu_w\).

There is also an exact finite Fourier formula.  Put

\[
 \Phi_n(k)=\sum_{u\text{ avoids }w}e^{ik[u]_{10}/10^n}.
\]

Then

\[
 \Phi_n(k)=e_0^{\mathsf T}
 \prod_{j=1}^n\left(\sum_{d=0}^9e^{ikd/10^j}B_d\right){\bf1}.            \tag{17}
\]

For \(0<r<1\), regularize the logarithmic singularity by

\[
 F_{\alpha,r}(x)=\log|1-re^{i(x-\alpha)}|
 =-\sum_{k\ge1}{r^k\over k}\cos(k(x-\alpha)).                           \tag{18}
\]

Absolute convergence and (17) give

\[
 \sum_{u}F_{\alpha,r}([u]_{10}/q)
 =-\sum_{k\ge1}{r^k\over k}
   \Re\!\left(e^{-ik\alpha}\Phi_n(k)\right).                            \tag{19}
\]

The limiting Fourier transform of \(\nu_w\) is similarly

\[
 \widehat\nu_w(k)=e_0^{\mathsf T}
 \prod_{j\ge1}\left(\sum_{d=0}^9e^{ikd/10^j}P_d\right){\bf1},           \tag{20}
\]

and \(I_w(\alpha)\) is the Abel limit obtained from (18)--(20).

Equations (17)--(20) are a genuine transfer-operator compression of the
**numerical logarithm**.  They are not a low-height integer auxiliary form:
the matrices contain scale-dependent complex phases, and taking a logarithm
has already discarded the integer-polynomial arithmetic needed by a
transcendence estimate.

Status: local `proof sketch`; the finite transfer identity is checked by the
companion program.

## 4. Spacing gives a joint lower bound of the correct scale

The scalar irrationality estimate used in the previous report bounded every
factor as if it could independently be as close to \(\pi\) as \(p_n/q\).
That loses almost all spacing information.  Distinct candidate nodes lie on
the \(q^{-1}\) grid, so at most a few can occupy each shrinking decimal
neighborhood of \(\alpha\).

For a legal word \(u\), put

\[
 y_u=[u]_{10}/q,\qquad
 K_u=\lfloor-\log_{10}|y_u-\alpha|\rfloor,
\]

and, for \(k\ge1\),

\[
 C_{n,k}=|\{u:|y_u-\alpha|<10^{-k}\}|.                                \tag{21}
\]

No equality occurs at a shell boundary because \(\alpha\) is irrational.
Layer counting gives the exact integer identity

\[
 \sum_uK_u=\sum_{k\ge1}C_{n,k},                                        \tag{22}
\]

and hence

\[
 (\log10)\sum_{k\ge1}C_{n,k}
 \le-\sum_u\log|y_u-\alpha|
 <(\log10)\left(N_n+\sum_{k\ge1}C_{n,k}\right).                         \tag{23}
\]

For \(k\le n\), the interval in (21) meets at most three decimal cylinders
of length \(k\).  If a cylinder ends in state \(s\), its exact number of
legal completions is

\[
 (M^{n-k}{\bf1})_s.                                                      \tag{24}
\]

Primitivity therefore supplies constants \(A_w,B_w>0\) such that

\[
 C_{n,k}\le A_w\lambda^{n-k},\qquad
 N_n\ge B_w\lambda^n.                                                    \tag{25}
\]

For \(k>n\), a shell contains at most one grid point.  A fixed valid upper
bound \(\nu>\mu(\pi)\) for the irrationality exponent gives, eventually,

\[
 |y_u-\alpha|\ge q^{-\nu};                                              \tag{26}
\]

thus at most \(O(\log q)\) nonempty one-point shells remain.  Summing (25)
in (23) proves

\[
 -\sum_u\log|y_u-\alpha|=O_w(N_n+\log q).                               \tag{27}
\]

Finally, for \(|t|\le1\),

\[
 2\sin(1/2)|t|\le |1-e^{it}|\le|t|.                                   \tag{28}
\]

Equations (23)--(28) give a joint lower bound

\[
 |{\cal E}_{n,w}(z_n)|\ge\exp(-C_wN_n-O_w(\log q))                      \tag{29}
\]

for some explicit graph-dependent \(C_w\).  This is exponentially stronger
than multiplying \(N_n\) scalar irrationality bounds, which paid
\(N_n\log q\).  It is nevertheless the natural size of the product, not an
arithmetic contradiction.

Status: `proof sketch`.  The shell identity and cylinder geometry are checked
exactly on finite instances; the use of finite irrationality exponent is the
same `literature-checked` scalar input recorded and source-pinned in
[`automaton_pade_attack.md`](automaton_pade_attack.md).

## 5. Sharp logarithmic-potential asymptotics

Let

\[
 \mu_n={1\over N_n}\sum_{u\text{ avoids }w}\delta_{[u]_{10}/10^n}.       \tag{30}
\]

Perron--Frobenius theory gives exponential convergence of \(\mu_n\) to
\(\nu_w\) against Lipschitz functions.  One direct proof couples the first
\(\lfloor n/2\rfloor\) digits: the distribution of those prefixes differs
exponentially from the Parry transition law, while changing the remaining
digits moves the real point by at most \(10^{-\lfloor n/2\rfloor}\).

The logarithmic singularity requires one extra check.  A radius \(10^{-k}\)
interval has \(\mu_n\)- and \(\nu_w\)-mass \(O_w(\lambda^{-k})\) by
(24)--(25).  Truncating \(F_\alpha\) at depth \(T\), applying exponential
Lipschitz convergence, and then using this cylinder bound gives uniform
integrability.  The possible grid point below scale \(10^{-n}\) contributes
only \(O(n/N_n)\) after normalization by (26).  Choosing \(T\) proportional
to \(n\) yields some \(0<\vartheta_w<1\) for which

\[
 \int F_\alpha\,d\mu_n
 =\int F_\alpha\,d\nu_w+O_w(\vartheta_w^n+n/N_n).                       \tag{31}
\]

This proves (3)--(4).  It also proves that \(I_w(\alpha)\) is finite.  Since
\(F_\alpha(x)\le\log\rho<0\) throughout \([0,1]\), with equality only at
\(x=1\), and \(\nu_w\) has no atoms, (5) follows.

The constant has a transparent multiscale interpretation.  Up to the bounded
smooth correction

\[
 H(t)=\log{2\sin(|t|/2)\over|t|},\qquad H(0)=0,                          \tag{32}
\]

the number \(-I_w(\alpha)\) is the logarithmic energy

\[
 \int_0^\infty
   \nu_w\{x:|x-\alpha|<e^{-t}\}\,dt.                                   \tag{33}
\]

Thus the sharp constant already contains the entire hierarchy of prefix
and sibling-cylinder masses around the selected path.  A transfer estimate
cannot replace it by a smaller constant without becoming false for the
product it is estimating.

Status: `proof sketch`.  This argument is self-contained finite-state
Perron--Frobenius theory plus the scalar bound (26); it has not been added to
the machine-checked track.

## 6. The actual selected factor is only an \(O(\log q)\) correction

Under the omitted-word assumption,

\[
 a_n=p_n-3q=\lfloor q\alpha\rfloor
\]

is one of the legal nodes.  With \(x_n=\{q\pi\}=\{q\alpha\}\), its factor is

\[
 |1+e^{ip_n/q}|=2\sin{x_n\over2q}.                                     \tag{34}
\]

The Taylor expansion at zero gives the exact-scale identity

\[
 \log|1+e^{ip_n/q}|
 =-\log q+\log x_n+O(q^{-2}).                                          \tag{35}
\]

For every fixed \(\nu>\mu(\pi)\), (26) implies

\[
 q^{1-\nu}\le x_n<1
\]

for all sufficiently large \(n\), and therefore

\[
 -\nu\log q+O(1)
 \le\log|1+e^{ip_n/q}|
 \le-\log q.                                                           \tag{36}
\]

This isolates the actual prefix's \(O(\log q)\) contribution.  It is
negligible compared with \(N_n\asymp\lambda^n\), but it is exactly where the
unknown decimal tail survives after the bulk potential is removed.

## 7. Full-grid control: the second-order term is exact

The unrestricted grid makes the bulk compensation fully explicit.  Let

\[
 P_q^{\rm all}=\prod_{a=0}^{q-1}|1-e^{i(a/q-\alpha)}|,
 \qquad 0<\alpha<1.
\]

The distance part has the exact Gamma identity

\[
 \prod_{a=0}^{q-1}|a/q-\alpha|
 =q^{-q}{\Gamma(q\alpha+1)\Gamma(q(1-\alpha))
             |\sin(\pi q\alpha)|\over\pi}.                             \tag{37}
\]

Apply Stirling's expansion to (37) and Euler--Maclaurin to the smooth
function \(H\) from (32).  With

\[
 I_{\rm all}(\alpha)=\int_0^1F_\alpha(x)\,dx,
\]

one obtains

\[
 \log P_q^{\rm all}
 =qI_{\rm all}(\alpha)+\log|2\sin(\pi q\alpha)|+C(\alpha)+O(q^{-1}),    \tag{38}
\]

where

\[
 C(\alpha)={1\over2}\log{\alpha\over1-\alpha}
       +{H(-\alpha)-H(1-\alpha)\over2}.                                \tag{39}
\]

For \(\alpha=\pi-3\), the scalar irrationality estimate gives

\[
 \log|\sin(\pi q\alpha)|=O(\log q)                                    \tag{40}
\]

from below, while it is bounded above.  Hence (38) is a genuine leading
\(q\) term plus an exact \(O(\log q)\) Diophantine fluctuation.  The selected
factor's \(-\log q+\log x_n\) is not an extra exponential saving: neighboring
grid factors compensate it, and their combined residue is the sine term in
(38).

Numerically,

\[
 -I_{\rm all}(\pi-3)=1.4167013053381887\ldots,                           \tag{41}
\]

far larger than \(c_0=0.1835699279\ldots\).  Formula (38), not the crude
\(\rho^q\) estimate, is the correct full-grid benchmark.

Status: (37)--(40) are a local `proof sketch`; the displayed decimal in
(41) is an `experiment`.

## 8. A child/parent ratio cancels the bulk but not the arithmetic cost

There is a natural hierarchical ratio which genuinely improves the analytic
ledger.  Let a legal length-\((n-1)\) prefix end in state \(s\), let \(D_s\)
be its allowed next digits, and put \(b_s=|D_s|\).  Split the full product by
last digit:

\[
 {\cal E}_{n,w}(Z)
 =\prod_{(p,s)\in{\cal A}_{n-1}(w)}
   \prod_{d\in D_s}(1+Z^{10p+d}).                                      \tag{42}
\]

Define the state-weighted parent comparison

\[
 {\cal Q}_{n,w}(Z)
 =\prod_{(p,s)\in{\cal A}_{n-1}(w)}(1+Z^{10p})^{b_s}
 =\prod_s{\cal E}_{n-1,w,s}(Z^{10})^{b_s}.                              \tag{43}
\]

Both (42) and (43) contain exactly \(N_n\) binomial factors.  With polynomial
length defined as the coefficient \(\ell^1\)-norm
\(L(P)=\sum_j|[Z^j]P|\), their nonnegative coefficients give
\(L({\cal E}_{n,w})=L({\cal Q}_{n,w})=2^{N_n}\), and both degrees are
\(\Theta(qN_n)\).  (The number of distinct monomials can be smaller because
different subset sums may collide.)  At \(z_n=e^{i/q}\), the shell estimate
applied to shifts \(d/q\) gives

\[
 \log\left|{{\cal E}_{n,w}(z_n)\over{\cal Q}_{n,w}(z_n)}\right|
 =O_w(\log q).                                                          \tag{44}
\]

The exceptional local term can be written explicitly.  Suppose the actual
length-\((n-1)\) prefix ends in state \(s\), its next digit is \(d_n\), and
\(10x_{n-1}=d_n+x_n\).  Its child cluster contributes to (44)

\[
 \log\left(
 {\prod_{d\in D_s}|d-d_n-x_n|
  \over(10x_{n-1})^{b_s}}
 \right)+O(q^{-2}).                                                      \tag{45}
\]

This is the promised selected-path multiscale cocycle.  It is built from the
unknown decimal digit \(d_n\) and tail \(x_n\); iterating it rewrites the
base-10 orbit rather than controlling it.

Most importantly, (44) is a quotient.  Clearing it leaves the two
integer-polynomial values (42)--(43), each with the original
\(\Theta(qN_n)\) degree and \(2^{N_n}\) length.  Taking their difference
gives length at most \(2^{N_n+1}\) and, without a new phase relation, only
the same \(\exp(-\Theta(N_n))\) upper scale.  A monomial phase alignment does
not change degree or length.  The analytic cancellation in (44) therefore
does not become a lower-height arithmetic form.

There is an even simpler obstruction to following one child.  For each
prefix \(v\), its subtree product factors exactly as

\[
 {\cal E}(v)=\prod_{d\in D_{s(v)}}{\cal E}(vd).                          \tag{46}
\]

Dividing away all nonselected children leaves the selected child product,
and repeating this operation ends at the single factor (34).  Selecting the
quotients requires the actual digits; clearing them restores every divided
subtree factor.  Hierarchy compresses the description of the candidate set,
not the integer degree of the disjunction.

Status: local `proof sketch`.  The exact tree factor counts in (42)--(43)
are checked by the companion program.  Bound (44) follows by splitting the
shifted logarithms into the shells of Section 4; it has not been
machine-checked.

## 9. Why no Mahler, Jensen, resultant, or transfer crossing remains

The audited refinements now have precise outcomes.

1. **Spacing** improves the naive lower exponent from
   \(N_n\log q\) to \(C_wN_n+O(\log q)\), but (4)--(6) prove that its sharp
   constant must be \(c_w(\alpha)>c_0\), so it cannot contradict the crude
   upper constant \(c_0\).
2. **Transfer operators** compute \(c_w(\alpha)\) and every Fourier
   regularization exactly, but they compute the logarithmic potential of all
   paths, not an integer auxiliary form selecting the \(\pi\) path.
3. **Mahler measure and Jensen** give the exact average zero in (11)--(12).
   They permit arbitrarily negative boundary values at clustered roots and
   supply no pointwise lower bound.
4. **Cyclotomic resultants** are often zero because of (14).  After common
   factors are removed, they separate algebraic roots from one another, not
   \(e^{i/q}\) from the root whose closeness is exactly the rational
   approximation \(p_n/q\to\pi\).
5. **Prefix/child and cross-scale ratios** reduce the analytic bulk to the
   \(O(\log q)\) cocycle (45), but their numerator and denominator retain the
   full integer degree and height.  Clearing a quotient reverses the
   compression.

A still conceivable proof would need a new \(\pi\)-specific arithmetic lower
bound which matches the leading constant \(c_w(\alpha)\) and then beats the
path-dependent \(O(\log q)\) term.  Existing scalar irrationality bounds see
only \(x_n\), while known exponential-polynomial bounds pay the expanded
degree and height.  Establishing control of the cocycle (45) for every
forbidden \(w\) would already be a digit-orbit theorem of essentially the
same strength as the target.

This is a separator for the present cyclotomic-product family, not a proof
that every imaginable auxiliary-form construction is impossible.

## 10. Finite checker and numerical scale

Companion:
[`cyclotomic_language_product_check.py`](cyclotomic_language_product_check.py)

It checks exactly on finite instances:

- the cyclotomic factorization (10);
- the common-root formula (14);
- KMP language enumeration and the finite Fourier transfer identity (17);
- the child/parent factor-count identity (42)--(43);
- the shell ledger (22) and the three-cylinder geometry;
- a rational full-grid distance-product identity.

It separately labels floating-point calculations as `experiment`.  The exact
run is:

```text
PASS: exact cyclotomic, transfer-tree, shell, and distance-product identities
EXPERIMENT: -N^-1 log products at n=5: w=0: 1.2923808501, w=00: 1.4111144566, w=314: 1.4162801665, w=99: 1.4296542093
EXPERIMENT: unrestricted limiting rate: 1.4167013053
```

All sampled rates are far above \(c_0=0.1835699279\ldots\), as predicted by
(5).  They illustrate the constant mismatch only; finite calculations are
not evidence for V1.

## 11. Claim status and exact missing input

- Equations (2), (9)--(10), (14), (17), (22), (34), (37), and the
  factor-count parts of (42)--(46) are exact mathematical identities, recorded
  here as a `proof sketch` because they are not in the verified Lean track.
- Equation (7) is the corresponding selected-factor asymptotic with an
  \(O(q^{-2})\) remainder; it is also a local `proof sketch`, not an exact
  identity in the literal sense.
- The Perron/log-potential limit (3)--(4), the spacing bound (29), and the
  cross-scale estimate (44) are local `proof sketch` results with their proof
  ingredients exposed above.
- The printed finite values are `experiment`.
- The scalar irrationality-exponent dependency is inherited from the dated,
  source-pinned `literature-checked` audit in
  [`automaton_pade_attack.md`](automaton_pade_attack.md).
- No statement here is `machine-checked`, a candidate resolution, or a
  verified resolution.

The exact missing input for this branch is no longer a generic joint product
lower bound.  Such a bound has now been obtained at the correct exponential
scale and shown unable to cross.  What would be needed is a
language-sensitive, \(\pi\)-specific **second-order** arithmetic estimate that
matches \(N_nI_w(\alpha)\) and controls the tail cocycle (45) sharply enough
to contradict membership of the actual digit path in the avoidance graph.
No such estimate is supplied by cyclotomic factorization, spacing,
resultants, Mahler measure, Jensen's formula, or the finite-state transfer
operator.  V1 does not follow.
