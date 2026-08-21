# T13: the many-anchor incidence route

Status: `proof sketch` (rigorous prose, not machine-checked).

Verdict: `INSUFFICIENT`.  The pinned inputs give the unconditional lower
bound (8.8) below, but it saturates the geometric neighborhood term in the
incidence inequality.  They give no positive lower bound for the upper box
dimension of the decimal-orbit closure.

## 0. Scope, provenance, and claim boundary

The canonical statement is vendored as `CANONICAL_STATEMENT.txt`, with
SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

It asks for a uniform ordered long-lag decimal block-collision estimate, with
quantifiers `for every 0<s<1, there exists C_s, for every m,N>=1`.  The
present anchor count is not that count.  It is a new sibling reduction related
to the canonical statement's near-return sibling A13.  Nothing below proves
or refutes C1, T8's all-scale spectral premise, or any statement called V1.

The external arithmetic statements used below are pinned in `SOURCE_PIN.md`.
The only inputs are:

1. Zeilberger--Zudilin's published upper bound for the irrationality measure
   of pi;
2. Banks's finite-type discrepancy lemma; and
3. for the exact-symbolic-constant fallback only, the Erdos--Turan inequality
   printed by Aistleitner--Hofer--Larcher.

The T9, T10, and T11 notes in the accumulated library have status `proof
sketch`.  No claim from them is used as a proved premise.  The machine-checked
T2 and T8 files are conditional upper-bound reductions, not lower-bound
existence theorems, and therefore do not increase the anchor count below.

No novelty claim is made.  In particular, the incidence lemma is elementary;
the point of this note is to determine exactly what the pinned arithmetic can
and cannot yield for this route.

## 1. Normalized definitions and ambiguities

Write

\[
  \mathbb T=\mathbb R/\mathbb Z,
  \qquad \|x\|_{\mathbb T}=\min_{k\in\mathbb Z}|x-k|.
\]

All balls and distances below use this circle metric.  Put

\[
 x_n=\{10^n\pi\}\quad(n\geq 0),\qquad
 X_\pi=\overline{\{x_n:n\geq0\}}\subset\mathbb T.       \tag{1.1}
\]

Thus `closure of the decimal orbit` means the closure of the fractional
parts, and the orbit starts at exponent zero.  For integers \(Q\geq1\) and
real \(\varepsilon>0\), call an integer \(q\) with \(1\leq q\leq Q\) an
\(\varepsilon\)-anchor when

\[
  \operatorname{dist}_{\mathbb T}(\{q\pi\},X_\pi)
     <\varepsilon,
\]

and define

\[
 I(Q,\varepsilon)=
 \#\{1\leq q\leq Q:q\hbox{ is an }\varepsilon
      \hbox{-anchor}\}.                                  \tag{1.2}
\]

The inequality is strict.  The anchor count is not ordered-pair valued.

Let \(N_X(r)\) be the least number of open circle balls of radius \(r\)
needed to cover a nonempty compact set \(X\).  Define

\[
 \overline{\dim}_{B}X=
 \limsup_{r\downarrow0}\frac{\log N_X(r)}{\log(1/r)}.     \tag{1.3}
\]

Changing open balls to closed balls, or radius to diameter, does not change
this dimension.  We retain radius throughout so that the constants in Section
4 are unambiguous.

For the rotation sample \(\{q\pi\}\), \(1\leq q\leq Q\), define its
nonwrapping interval discrepancy by

\[
 D_Q=\sup_{J\subset[0,1)}
 \left|Q^{-1}\#\{1\leq q\leq Q:\{q\pi\}\in J\}-|J|\right|, \tag{1.4}
\]

where \(J\) ranges over intervals, exactly as in Banks's definition.  Define
the circle-arc discrepancy \(\Delta_Q\) by the same supremum over connected
arcs of \(\mathbb T\).  A circle arc is either a nonwrapping interval or the
disjoint union of two such intervals.  Hence

\[
                         \Delta_Q\leq2D_Q.                \tag{1.5}
\]

This factor two is retained everywhere.  Paying discrepancy only once for an
arbitrary union of many arcs would be false.

## 2. Pinned irrationality input and finite type

Use the exact rational number

\[
                  U=7.103206.                             \tag{2.1}
\]

The retained Zeilberger--Zudilin publication displays the stronger numerical
upper bound
`7.10320533413700172750577342281...`; in particular, its result implies

\[
                         \mu(\pi)<U.                       \tag{2.2}
\]

Using the slightly larger terminating decimal avoids treating the source's
ellipsis as an exact real number.

The source's definition of irrationality measure implies the following.  For
every real \(\nu>U\), there is an integer \(H_\nu\geq1\) such that, for every
integer \(h\geq H_\nu\),

\[
                    \|h\pi\|_{\mathbb T}>h^{1-\nu}.       \tag{2.3}
\]

Indeed, apply the source inequality
\(|\pi-p/q|>q^{-\nu}\) to a nearest integer \(p\) to
\(q\pi\), then multiply by \(q\).

For later finite-scale use, set

\[
 c_\nu=\min\left(1,
   \min_{1\leq h<H_\nu}h^{\nu-1}\|h\pi\|_{\mathbb T}
                   \right)>0,                             \tag{2.4}
\]

with the inner minimum omitted when \(H_\nu=1\).  Its positivity uses the
irrationality of pi.  Equations (2.3)--(2.4) give, for every integer \(h\geq1\),

\[
              \|h\pi\|_{\mathbb T}\geq c_\nu h^{1-\nu}. \tag{2.5}
\]

Banks defines the Diophantine type of an irrational \(\gamma\) by

\[
 \tau(\gamma)=\sup\{t\in\mathbb R:
       \liminf_{n\to\infty} n^t\|n\gamma\|_{\mathbb T}=0\}.
                                                               \tag{2.6}
\]

**Lemma 2.1 (type supplied by the published bound).**

\[
                         \tau(\pi)\leq U-1.                \tag{2.7}
\]

**Proof.**  Fix \(t>U-1\), and choose \(\nu\) with
\(U<\nu<t+1\).  By (2.3), eventually

\[
 n^t\|n\pi\|_{\mathbb T}>n^{t+1-\nu}\longrightarrow\infty.
\]

Thus this \(t\) is not in the set in (2.6).  This holds for every
\(t>U-1\), proving (2.7).  QED.

## 3. The pinned rotation discrepancy exponent

Banks, Section 2.2, Lemma 2.1, states that if an irrational \(\gamma\) has
finite type \(\tau\), then for every real shift \(\delta\) and every
\(\eta>0\),

\[
 D_{\gamma,\delta}(Q)\ll_{\gamma,\eta}
        Q^{-1/(\tau+\eta)}.                               \tag{3.1}
\]

Its discrepancy is the all-interval discrepancy (1.4), and the implicit
constant is independent of \(Q\) and \(\delta\).  We only use \(\delta=0\).

Define the exact threshold

\[
 \theta_*={1\over U-1}={1\over6.103206}
          =0.163848311854458\ldots.                        \tag{3.2}
\]

**Proposition 3.1 (pinned discrepancy input).**  For every real
\(\theta\) satisfying

\[
                       0<\theta<\theta_*,                  \tag{3.3}
\]

there is a real constant \(C_\Delta=C_\Delta(\pi,\theta)\geq1\), chosen
before \(Q\), such that every integer \(Q\geq1\) satisfies

\[
                         \Delta_Q\leq C_\Delta Q^{-\theta}. \tag{3.4}
\]

**Proof.**  Choose \(\eta>0\) so small that
\(\theta<1/(U-1+\eta)\).  By (2.7),

\[
 {1\over\tau(\pi)+\eta}\geq {1\over U-1+\eta}>\theta.
\]

Apply (3.1), use \(Q^{-1/(\tau+\eta)}\leq Q^{-\theta}\) for \(Q\geq1\),
then use (1.5) and enlarge the constant to at least one.  QED.

The endpoint \(\theta=\theta_*\) is not claimed.  Both the strict published
irrationality-measure quantifier and Banks's \(+\eta\) leave an open endpoint.

### 3.1 Exact-symbolic-constant fallback from Erdos--Turan

For auditability, here is a weaker estimate derived directly from the exact
inequality in the retained Aistleitner--Hofer--Larcher PDF.  Their equation
(1.1), journal page 639, says for every positive integer \(H\)

\[
 D_Q^*(x_1,\ldots,x_Q)\leq {1\over H+1}
 +\sum_{h=1}^{H}{1\over h}
   \left|{1\over Q}\sum_{q=1}^{Q}e^{2\pi i h x_q}\right|. \tag{3.5}
\]

There is no suppressed multiplicative constant.  At \(x_q=\{q\pi\}\),
the finite geometric progression and
\(|\sin(\pi x)|\geq2\|x\|_{\mathbb T}\) give

\[
 \left|\sum_{q=1}^{Q}e^{2\pi i hq\pi}\right|
 \leq {1\over2\|h\pi\|_{\mathbb T}}
 \leq {h^{\nu-1}\over2c_\nu}.                            \tag{3.6}
\]

For \(H=\lfloor Q^{1/\nu}\rfloor\), using
\(\sum_{h=1}^{H}h^{\nu-2}\leq H^{\nu-1}\),

\[
 D_Q^*\leq\left(1+{1\over2c_\nu}\right)Q^{-1/\nu}.
                                                               \tag{3.7}
\]

Every circle arc has discrepancy at most \(2D_Q^*\).  Therefore

\[
 \Delta_Q\leq(2+c_\nu^{-1})Q^{-1/\nu}                    \tag{3.8}
\]

for every \(\nu>U\).  Taking \(\nu=8\) gives the exact symbolic exponent
\(1/8\), with the source-dependent finite constant \(2+c_8^{-1}\).
The source does not give a numerical onset \(H_8\), so this is not a
numerically effective constant.  Proposition 3.1 is stronger in exponent but
has Banks's implicit constant.

## 4. Incidence from a box cover, with constants

The following statement is independent of pi except for its discrepancy.

**Lemma 4.1 (cover-to-incidence).**  Let \(X\subset\mathbb T\) be nonempty
and compact.  If \(r>0\), \(\varepsilon>0\), and
\(r+\varepsilon<1/2\), then

\[
 {1\over Q}\#\{1\leq q\leq Q:
       \operatorname{dist}_{\mathbb T}(\{q\pi\},X)<\varepsilon\}
 \leq N_X(r)\bigl(2(r+\varepsilon)+\Delta_Q\bigr).       \tag{4.1}
\]

**Proof.**  Cover \(X\) by \(M=N_X(r)\) open radius-\(r\) balls with
centers \(y_1,\ldots,y_M\).  If a point is within \(\varepsilon\) of \(X\),
it belongs to one of the radius-\((r+\varepsilon)\) balls about the same
centers.  Each such ball is a circle arc of length \(2(r+\varepsilon)\).
By the definition of \(\Delta_Q\), the proportion of sample points in each
arc is at most its length plus \(\Delta_Q\).  The union bound gives (4.1).
Overlaps only make the union bound larger.  QED.

Taking \(X=X_\pi\), \(r=\varepsilon<1/4\), gives the exact inequality

\[
                {I(Q,\varepsilon)\over Q}
 \leq N_{X_\pi}(\varepsilon)(4\varepsilon+\Delta_Q).      \tag{4.2}
\]

The constants have the following origins: radius \(\varepsilon\) in the box
cover plus radius \(\varepsilon\) in the anchor definition gives radius
\(2\varepsilon\); its circle length is \(4\varepsilon\); discrepancy is paid
once for every covering ball.

## 5. The requested box-dimension inequality

Suppose

\[
                  \overline{\dim}_{B}X_\pi<d'<1.          \tag{5.1}
\]

By the definition (1.3), there are \(C_X\geq1\) and \(r_0>0\) such that

\[
                  N_{X_\pi}(r)\leq C_Xr^{-d'}
          \quad(0<r<r_0).                                \tag{5.2}
\]

In fact one can take \(C_X=1\) after shrinking \(r_0\), but retaining
\(C_X\) exposes every dependence.

Fix \(0<\theta<\theta_*\), choose \(C_\Delta\) as in Proposition 3.1,
and let \(a>0\).  Substituting \(\varepsilon=Q^{-a}\) into (4.2), for every
integer

\[
 Q>\max(4^{1/a},r_0^{-1/a}),                              \tag{5.3}
\]

we obtain

\[
 \boxed{
 {I(Q,Q^{-a})\over Q}
 \leq 4C_XQ^{-a(1-d')}
      +C_XC_\Delta Q^{ad'-\theta}.}                       \tag{5.4}
\]

Thus, with constants depending only on \(X_\pi,d',\pi,\theta\),

\[
 {I(Q,Q^{-a})\over Q}
 \ll Q^{-a(1-d')}+Q^{ad'-\theta}.                         \tag{5.5}
\]

This is the requested incidence-to-dimension chain.  There is no hidden
factor for wrapped intervals because it was already included in
\(C_\Delta\) through (1.5).

## 6. Conditional full dimension and its quantifiers

**Theorem 6.1 (conditional many-anchor criterion).**  For every real
\(\theta\) with \(0<\theta<\theta_*\), and every real \(a\) with
\(0<a<\theta\),

\[
 \left(\limsup_{Q\to\infty}{I(Q,Q^{-a})\over Q}>0\right)
 \quad\Longrightarrow\quad
             \overline{\dim}_{B}X_\pi=1.                 \tag{6.1}
\]

Equivalently, since a \(\theta\) can be chosen between \(a\) and
\(\theta_*\), for every real \(a\) with \(0<a<\theta_*\), positive upper
limiting anchor density at scale \(Q^{-a}\) forces full upper box dimension.

**Proof.**  Suppose instead that the dimension is \(d<1\), and choose
\(d'\) with \(d<d'<1\).  In (5.4),

\[
 a(1-d')>0,\qquad \theta-ad'>\theta-a>0.
\]

Both terms tend to zero, contradicting the positive limsup.  Since every
subset of the circle has upper box dimension at most one, the dimension must
equal one.  QED.

For comparison with weaker lower counts, (5.4) gives the following complete
dimension ladder.  If for some \(c>0\), \(\beta\geq0\), and all sufficiently
large \(Q\),

\[
                 {I(Q,Q^{-a})\over Q}\geq cQ^{-\beta},    \tag{6.2}
\]

then, provided \(\beta<\min(a,\theta)\),

\[
 \overline{\dim}_{B}X_\pi\geq
 \min\left(1-{\beta\over a},{\theta-\beta\over a}\right). \tag{6.3}
\]

Indeed, if the dimension were smaller than the right side, choose \(d'\)
strictly between them.  Then both terms in (5.4) would be
\(o(Q^{-\beta})\), contradicting (6.2).  This records exactly what polynomial
improvement an unconditional count would need.

## 7. Why full dimension implies every decimal word occurs

Full dimension does not imply density for an arbitrary closed subset of the
circle.  The conclusion here instead uses the special forbidden-word
structure of a decimal orbit.

Let \(w\) be a decimal word of length \(k\geq1\), including words with a
leading zero, and suppose that \(w\) never occurs in the unique decimal
expansion of pi.  If \(m=tk+s\), where \(t\geq0\) and \(0\leq s<k\), then
any length-\(m\) decimal word occurring in the orbit has none of its \(t\)
aligned length-\(k\) blocks equal to \(w\).  Therefore the number \(A_w(m)\)
of possible such prefixes obeys

\[
                         A_w(m)\leq(10^k-1)^t10^s.         \tag{7.1}
\]

Every orbit point \(x_n\) belongs to the half-open decimal cylinder specified
by its next \(m\) digits.  The union of the closures of the at most \(A_w(m)\)
relevant cylinders is closed and covers the orbit.  It consequently covers
the orbit closure \(X_\pi\).  Each closed cylinder is a circle interval of
length \(10^{-m}\).  It fits in an open ball of radius \(10^{-m}\), with
room at both endpoints.  Thus

\[
                 N_{X_\pi}(10^{-m})\leq A_w(m).           \tag{7.2}
\]

The ratio between consecutive decimal scales is fixed.  Using monotonicity
of covering numbers between those scales, (7.1)--(7.2) give

\[
 \overline{\dim}_{B}X_\pi
 \leq {\log(10^k-1)\over k\log 10}<1.                    \tag{7.3}
\]

The use of closed cylinders is essential: a sequence of irrational orbit
points can converge to a decimal-cylinder boundary, where terminating and
repeating-9 representations meet.  We do not assign a preferred expansion to
such a closure point.  We cover it by closure before taking the orbit closure,
so no boundary word is silently introduced.

Contraposing (7.3) proves

\[
 \overline{\dim}_{B}X_\pi=1
 \quad\Longrightarrow\quad
 \text{every finite decimal word occurs in pi}.           \tag{7.4}
\]

This elementary estimate is consistent with the machine-checked
forbidden-language entropy inequalities indexed in the accumulated T3
artifact, but no unproved note is needed for (7.4).

Combining (6.1) and (7.4) gives the requested conditional implication, not an
unconditional claim about the digits of pi.

## 8. Unconditional anchor lower bounds from the pinned machinery

### 8.1 Exact decimal-power anchors

For every \(n\geq0\),

\[
                 \{10^n\pi\}=x_n\in X_\pi.
\]

Consequently, for every \(Q\geq1\) and every \(\varepsilon>0\),

\[
 \boxed{I(Q,\varepsilon)\geq
        \lfloor\log_{10}Q\rfloor+1.}                     \tag{8.1}
\]

This includes \(q=1=10^0\).

### 8.2 A logarithmic packing of orbit centers

Fix any \(\nu>U\) and use \(c_\nu\) from (2.4).  For
\(0\leq i<j<K\), the integer \(h=10^j-10^i\) satisfies
\(1\leq h<10^K\).  Equation (2.5) gives

\[
 \|x_j-x_i\|_{\mathbb T}
   =\|h\pi\|_{\mathbb T}
   >c_\nu10^{-K(\nu-1)}.                                 \tag{8.2}
\]

For \(0<\varepsilon<1/4\), define

\[
 K_\nu(\varepsilon)=
 \max\left(0,
 \left\lfloor{\log_{10}(c_\nu/(2\varepsilon))\over\nu-1}
 \right\rfloor\right).                                  \tag{8.3}
\]

By (8.2), the open radius-\(\varepsilon\) balls around
\(x_0,\ldots,x_{K_\nu(\varepsilon)-1}\) are pairwise disjoint.  All of them
are contained in the \(\varepsilon\)-neighborhood of \(X_\pi\).  Each has
length \(2\varepsilon\), so the lower side of the definition of
\(\Delta_Q\), summed over these disjoint balls, gives the exact estimate

\[
 \boxed{
 {I(Q,\varepsilon)\over Q}\geq
 K_\nu(\varepsilon)(2\varepsilon-\Delta_Q).}              \tag{8.4}
\]

The right side is allowed to be negative; the useful specialization below is
positive.

### 8.3 Strongest lower count derived by this direct packing argument

Fix a real \(a\) with

\[
                         0<a<\theta_*.                    \tag{8.5}
\]

Choose \(\theta\) with \(a<\theta<\theta_*\).  Proposition 3.1 gives
\(\Delta_Q\leq C_\Delta Q^{-\theta}=o(Q^{-a})\).  Set
\(\varepsilon=Q^{-a}\) in (8.4).  Since

\[
 K_\nu(Q^{-a})={a\over\nu-1}\log_{10}Q+O_{\pi,\nu}(1),   \tag{8.6}
\]

we obtain, for every fixed \(\nu>U\),

\[
 \liminf_{Q\to\infty}
 {I(Q,Q^{-a})\over Q^{1-a}\log_{10}Q}
 \geq {2a\over\nu-1}.                                    \tag{8.7}
\]

Letting \(\nu\downarrow U\) is legitimate because (8.7) holds separately
for every \(\nu>U\).  Therefore the direct packing and discrepancy argument
produces

\[
 \boxed{
 \liminf_{Q\to\infty}
 {I(Q,Q^{-a})\over Q^{1-a}\log_{10}Q}
 \geq {2a\over U-1}>0
 \quad(0<a<\theta_*).}                                   \tag{8.8}
\]

In particular,

\[
                  I(Q,Q^{-a})\gg_{\pi,a}Q^{1-a}\log Q.   \tag{8.9}
\]

For \(a\geq\theta_*\), the pinned discrepancy theorem no longer makes its
error smaller than the target interval length.  The unconditional statement
retained for that range is the exact-anchor bound (8.1).  This is a limit of
the present machinery, not a claim that no stronger theorem is possible.

### 8.4 Near-return, residual, and three-gap audit

The machine-checked residual and spectral library files say that certain
upper bounds would imply C1.  They do not assert that any non-power integer is
an anchor, so they add no unconditional term to (8.8).

The accumulated note library contains no pinned three-distance theorem.  No
such theorem is silently imported here.  More importantly, the bare datum
that a finite rotation orbit has at most three gap lengths controls the number
of distinct lengths, not their sizes relative to a prescribed union of
shrinking balls.  That structural datum alone cannot improve (8.4).  The
finite-type discrepancy theorem already supplies the needed count throughout
the full range \(a<\theta_*\); beyond that range its error and the target
length are of the same or worse polynomial order.  Thus the three-gap route,
without new quantitative arithmetic, does not furnish another lower bound
that can enter the dimension ladder.

## 9. Exact saturation and the unconditional verdict

Normalize (8.9) by \(Q\):

\[
                  {I(Q,Q^{-a})\over Q}
                  \gg Q^{-a}\log Q.                      \tag{9.1}
\]

This has the boundary polynomial exponent \(\beta=a\).  The formal ladder
(6.3) assumes the strict inequality \(\beta<a\), so it cannot be invoked at
this endpoint.  Its first threshold closes at

\[
                         1-{\beta\over a}=0.              \tag{9.2}
\]

Equivalently, for every fixed \(d'>0\), the geometric term allowed by (5.4)
is

\[
                  Q^{-a(1-d')}=Q^{-a+ad'},                \tag{9.3}
\]

and

\[
                  Q^{-a}\log Q=o(Q^{-a+ad'}).             \tag{9.4}
\]

Thus the lower count is compatible with every arbitrarily small positive
cover exponent \(d'\).  The logarithm records the logarithmic packing of the
known orbit points, but it is subpolynomial and cannot force positive box
dimension.

The exact saturating step is the neighborhood-volume contribution

\[
                     N_{X_\pi}(\varepsilon)\varepsilon   \tag{9.5}
\]

in (4.2), not the discrepancy-error contribution.  A zero-dimensional set
may have a covering number growing like \(\log(1/\varepsilon)\), and then
(9.5) has exactly the size \(\varepsilon\log(1/\varepsilon)\) seen in (9.1).

Therefore the unconditional dimension conclusion delivered by this complete
incidence-and-packing chain is only

\[
 \boxed{\overline{\dim}_{B}X_\pi\geq0,}                  \tag{9.6}
\]

which is tautological.  This note does **not** claim a new nontrivial
dimension theorem for pi.

To cross the obstruction at one scale \(Q^{-a}\), it would suffice to prove
for some \(\delta>0\)

\[
                 I(Q,Q^{-a})\geq Q^{1-a+\delta-o(1)},     \tag{9.7}
\]

with the exponent also beating the discrepancy side of (6.3).  Equivalently,
one needs a power-sized packing of genuinely distinct decimal-orbit centers,
or new arithmetic that counts anchors beyond the natural volume of the
currently known logarithmic packing.  Existing exact powers, conditional
near-return reductions, and rotation discrepancy do not provide that input.

## 10. Quantifier and constant checklist

1. `X_pi` is the closure of `{10^n*pi mod 1 : n>=0}`.
2. `q` is an integer in the inclusive range `1<=q<=Q`.
3. The anchor distance is strict and uses the circle metric.
4. `I(Q,eps)` is a one-index count, not the ordered C1 pair count.
5. The exact safe irrationality exponent is `U=7.103206`; the displayed
   threshold is `theta_*=1/(U-1)`, and its endpoint is excluded.
6. For every `theta<theta_*`, `C_Delta` is chosen before every positive
   integer `Q`.
7. A cover ball has radius `eps`; anchor enlargement gives radius `2eps`,
   length `4eps`, producing the constant `4` in (5.4).
8. Wrapped-arc splitting contributes the factor `2` in (1.5), already
   absorbed into `C_Delta`.
9. In Theorem 6.1 the order is `for every theta`, `for every a<theta`, then
   the implication from a positive limsup.
10. The disjunctivity conclusion uses the forbidden-word bound (7.3), not the
    false general assertion that every full-dimensional closed set is dense.
11. The unconditional lower count (8.8) is valid only for `0<a<theta_*`;
    exact powers give (8.1) at every scale.
12. The verdict is `INSUFFICIENT`: the exact saturation is (9.5), and no C1,
    V1, normality, or unconditional disjunctivity claim is made.
