# T43: finite invariant cores as conditional certificates for C6

Status: `proof sketch` (rigorous prose, not machine-checked).

## 0. Provenance, scope, and claim status

- Canonical statement: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.
- Canonical SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Original external source URL: none. The canonical question is a locally
  formulated research question dated 2026-07-22.
- This note concerns the program conjecture C6, a conditional quantitative
  times-16 transversal statement supporting the canonical positive-entropy
  question. It does not prove the canonical question or C6.
- T20 is the `machine-checked` module
  `TheoryLib.PiPositiveDecimalFactorEntropy.T20T20TransversalEntropy`, module
  SHA-256
  `ac5ed1c3c9c74fae5ae5d2191e92a8895ad991c34e0d2e950dfc10b036a09a64`.
  Its canonical-source pin is separately the canonical SHA-256 above. The
  exact definitions and theorems used are `EpsilonDense`,
  `timesSixteenTransversal`, `piOrbitClosure`, `piOrbitClosure_nonempty`,
  `piOrbitClosure_isClosed`, `piOrbitClosure_forward_timesTen_invariant`, and
  `piC6_iff_literal_quantifiers`. The machine-checked justification for calling
  C6 sufficient for the canonical positive-entropy target is
  `piC6_implies_positive_decimal_factor_entropy`. All are in namespace
  `DecimalFactorEntropy.TransversalEntropy`.
- The T38 bundle is an `experiment`. It is not a premise below. In particular,
  none of its bounded tau probes is extrapolated, and no all-word tau table or
  assertion about pi is made.

All logarithms denoted by `log` or `ln` below are natural logarithms;
`log_10` is explicitly base 10.

**Acceptance index.** Provenance, source hash, and source URL are in Section 0;
the normalized targets and quantifier ambiguities are in Section 1; endpoint
conventions and invariance are in Sections 2-4; the explicit radius and word
length are in Sections 5-6; the conditional universal premise and linear time
bound are in Section 7; the endpoint-complete carry graph and its exact coding
are in Sections 8-9; the SCC condition and complete sufficiency proof are in
Section 10; exact outputs and nonclaims are in Section 11.

## 1. Normalized target and ambiguous quantifiers

The circle is

\[
  \mathbb T=\mathbb R/\mathbb Z
\]

with quotient map `q : R -> T` and its usual metric

\[
 d(q(s),q(t))=\min_{k\in\mathbb Z}|s-t-k|.
\]

For every integer `b >= 1`, write

\[
  T_b(q(t))=q(bt).
\]

Thus `T_10 T_16 = T_16 T_10` exactly.

The canonical positive-entropy target is:

> For the unique nonterminating decimal expansion of pi, do there exist one
> fixed real `eta>0` and one integer `N>=1` such that
> \[
> p_\pi(n)\ge 10^{\eta n}
> \]
> for every integer `n>=N`?

C6 is a separate conjectural sufficient condition, not the canonical target.
Positive entropy does not assert C6, full entropy, occurrence of every decimal
word, or decimal disjunctivity.

The C6 statement used here is the following literal conditional target:

> There exist real numbers `A > 0`, `B`, and `epsilon_0 > 0` such that, for
> every real `epsilon` with `0 < epsilon < epsilon_0`, there is an integer
> `R >= 0` satisfying
> \[
> R\le A\log(1/\epsilon)+B
> \]
> and
> \[
> \bigcup_{0\le j\le R}T_{16}^{j}K_\pi
> \]
> is closed-radius `epsilon`-dense in `T`.

Here closed-radius `epsilon`-dense means

\[
  (\forall y\in\mathbb T)(\exists z\in S)\ d(y,z)\le\epsilon.
  \tag{1.1}
\]

The quantifiers that must not be conflated are:

1. The word-dependent extinction time in Hypothesis 7.1 below may depend on
   the entire word, not merely its length.
2. The constants `L,C` in that hypothesis must be uniform over every nonempty
   decimal word.
3. The C6 witness time may depend on `epsilon`, but `A,B,epsilon_0` may not.
4. Finiteness of cores is a universal premise in Theorem 7.4, not a conclusion
   established for the cores of pi.
5. T38 gives only bounded symbolic computations and discharges none of these
   universal quantifiers.
6. In the canonical target, one fixed `eta>0` must work for every sufficiently
   large `n`; `eta` may not depend on `n`.
7. C6 is used only as a sufficient intermediate conjecture and is neither
   proved nor asserted equivalent to the canonical target here.

## 2. Decimal coding and endpoint-safe avoidance sets

**Definition 2.1 (decimal sequence space).** Let `D={0,...,9}` and
`Sigma=D^N`, with coordinates numbered `0,1,2,...`. For `a in Sigma`, define

\[
  \operatorname{val}(a)=\sum_{n=0}^{\infty}a_n10^{-n-1}\in[0,1]
\]

and

\[
  \kappa(a)=q(\operatorname{val}(a))\in\mathbb T.
\]

This deliberately permits both decimal expansions of a terminating point.
For example, `0.5000...` and `0.4999...` have the same image. Also
`0.9999...` and `0.0000...` both map to `0` on the circle.

**Definition 2.2 (word value and closed decimal cell).** For a nonempty word
`w=w_0...w_{m-1} in D^m`, where `m=|w|>=1`, set

\[
  [w]_{10}=\sum_{i=0}^{m-1}w_i10^{m-1-i}\in\{0,\ldots,10^m-1\}
\]

and define the closed circle cell

\[
  J_w=q\left(\left[\frac{[w]_{10}}{10^m},
                  \frac{[w]_{10}+1}{10^m}\right]\right).
  \tag{2.1}
\]

Leading zeroes are retained by the separately specified length `m`. The top
cell is the image of `[1-10^{-m},1]`, so its right endpoint is the circle point
`0`; no half-open convention is hidden in (2.1).

**Definition 2.3 (symbolic avoidance and its circle image).** Let

\[
 X_w=\{a\in\Sigma:(a_n,\ldots,a_{n+m-1})\ne w
                    \text{ for every }n\ge0\}
\]

and

\[
 K_w=\kappa(X_w)\subseteq\mathbb T.                 \tag{2.2}
\]

Thus membership in `K_w` is existential over decimal expansions: a circle
point belongs to `K_w` when at least one of its decimal expansions avoids `w`.
This convention is needed for closedness. Choosing a preferred half-open
decimal expansion instead can make the literal avoidance set nonclosed.

**Lemma 2.4 (closedness and invariance).** For every nonempty word `w`, the
set `K_w` is compact, hence closed, and

\[
 T_{10}(K_w)\subseteq K_w.                           \tag{2.3}
\]

**Proof.** The set `X_w` is the intersection, over all `n>=0`, of complements
of finite-coordinate cylinders, so it is closed in the compact product
`D^N`. The evaluation map `kappa` is continuous, hence its image `K_w` is
compact. If `sigma` is the left shift, direct summation gives
`T_10 kappa = kappa sigma` on the circle. Since `sigma(X_w) subset X_w`, (2.3)
follows. `square`

**Lemma 2.5 (a displayed block forces cell membership).** If a sequence
`a in Sigma` has `w` beginning at coordinate `n`, then

\[
 T_{10}^n\kappa(a)\in J_w.                           \tag{2.4}
\]

**Proof.** The value of the shifted sequence lies between
`[w]_10/10^m` and `([w]_10+1)/10^m`, inclusively. The inclusive upper endpoint
is necessary for a tail of all nines. Passing to the circle gives (2.4).
`square`

## 3. The largest closed forward-invariant core

**Definition 3.1 (finite preimage intersection).** For a nonempty word `w`
and an integer `R>=0`, put

\[
 H(w,R)=\bigcap_{j=0}^{R}T_{16}^{-j}(K_w).           \tag{3.1}
\]

The notation means that `x in H(w,R)` exactly when
`T_16^j x in K_w` for every integer `j` with `0<=j<=R`.

**Definition 3.2 (invariant core).** Define

\[
 \operatorname{Core}(w,R)
   =\{x\in H(w,R):(\forall n\ge0)\ T_{10}^n x\in H(w,R)\}.
                                                               \tag{3.2}
\]

Equivalently,

\[
 \operatorname{Core}(w,R)
   =\bigcap_{n=0}^{\infty}T_{10}^{-n}H(w,R).          \tag{3.3}
\]

**Lemma 3.3 (largest-subset property).** `Core(w,R)` is closed and satisfies

\[
 T_{10}(\operatorname{Core}(w,R))
   \subseteq\operatorname{Core}(w,R).                \tag{3.4}
\]

If `F subset H(w,R)` is closed and `T_10(F) subset F`, then

\[
 F\subseteq\operatorname{Core}(w,R).                 \tag{3.5}
\]

Hence (3.2) is exactly the largest closed forward-times-10-invariant subset of
the intersection (3.1).

**Proof.** Each set in (3.3) is closed, proving closedness. Dropping the first
condition in the sequence of conditions indexed by `n` proves (3.4). If
`x in F`, induction gives `T_10^n x in F subset H(w,R)` for every `n`, proving
(3.5). `square`

**Lemma 3.4 (commutation makes the core equal the intersection).** For every
nonempty `w` and every `R>=0`,

\[
 \operatorname{Core}(w,R)=H(w,R).                   \tag{3.6}
\]

**Proof.** If `x in H(w,R)`, then for `0<=j<=R`,

\[
 T_{16}^j(T_{10}x)=T_{10}(T_{16}^jx)\in K_w
\]

by commutation and Lemma 2.4. Thus `H(w,R)` is itself forward-times-10
invariant. Lemma 3.3 applied to `F=H(w,R)` gives `H subset Core`; the reverse
inclusion is in Definition 3.2. `square`

The expanded definition (3.2) is retained because it states the requested
largest-core construction without relying on the simplifying equality (3.6).

**Lemma 3.5 (time monotonicity).** If `0<=R<=R'`, then

\[
 \operatorname{Core}(w,R')\subseteq\operatorname{Core}(w,R).  \tag{3.7}
\]

**Proof.** The intersection defining `H(w,R')` has all the constraints of
`H(w,R)` and possibly more. Use (3.6). `square`

## 4. The pi orbit closure and failure of density

**Definition 4.1 (T20 orbit closure).** Let

\[
 K_\pi=\overline{\{q(10^n\pi):n\ge0\}}.             \tag{4.1}
\]

For `R>=0`, put

\[
 U_R=\bigcup_{j=0}^{R}T_{16}^jK_\pi.                \tag{4.2}
\]

T20 machine-checks that `K_pi` is nonempty, closed, and forward-times-10
invariant. Since the circle is compact and each `T_16^j` is continuous, `U_R`
is a nonempty compact set.

**Lemma 4.2 (literal negation of T20 density).** Let `epsilon>0`. If `U_R` is
not closed-radius `epsilon`-dense in the sense of (1.1), then there is
`y in T` such that

\[
 d(y,z)>\epsilon\quad\text{for every }z\in U_R.      \tag{4.3}
\]

Because `U_R` is compact, the minimum

\[
 \rho=d(y,U_R)=\min_{z\in U_R}d(y,z)                 \tag{4.4}
\]

exists and satisfies `rho>epsilon`.

**Proof.** Negate the two quantifiers and the weak inequality in (1.1). The
minimum assertion is compactness. `square`

## 5. An explicit decimal cell inside a metric hole

**Lemma 5.1 (decimal grid cell lemma, including wraparound).** Suppose
`0<epsilon<1/2`, let `U subset T` be nonempty and compact, and suppose some
`y in T` satisfies `d(y,U)>epsilon`. Set

\[
 m=\left\lceil\log_{10}(1/\epsilon)\right\rceil,
 \qquad h=10^{-m}.                                   \tag{5.1}
\]

Then `m>=1`, `h<=epsilon`, and there is a word `w in D^m` such that

\[
 J_w\cap U=\varnothing.                              \tag{5.2}
\]

Thus the requested displayed additive word-length constant is exactly

\[
 |w|=\left\lceil\log_{10}(1/\epsilon)\right\rceil+0. \tag{5.3}
\]

**Proof.** Write `rho=d(y,U)>epsilon`. The diameter of the circle in the stated
metric is `1/2`, so nonemptiness of `U` gives `rho<=1/2`. Choose explicitly

\[
 \eta=\frac{\epsilon+\rho}2.
\]

Then `epsilon<eta<rho` and `eta<1/2`. Choose a lift `t in R` of `y`, and let

\[
 k=\left\lfloor\frac{t-\eta}{h}\right\rfloor+1.
\]

The floor inequalities give

\[
 t-\eta<kh\le t-\eta+h.
\]

Consequently

\[
 (k+1)h\le t-\eta+2h
            \le t-\eta+2\epsilon<t+\eta,            \tag{5.4}
\]

where the last inequality is strict because `epsilon<eta`. Thus the entire
closed interval `[kh,(k+1)h]` lies in `(t-eta,t+eta)`.

Let `a` be the residue of `k` modulo `10^m`, chosen in
`{0,...,10^m-1}`, and let `w` be the unique length-`m` decimal word, with
leading zeroes if necessary, whose value is `a`. Translation by an integer
shows

\[
 q([kh,(k+1)h])=J_w.
\]

This also covers a cell crossing the chosen lift boundary: the top grid cell
maps from `[1-h,1]` and contains the circle point `0` as prescribed by (2.1).
Every point of `J_w` has circle distance less than `eta` from `y` by (5.4),
whereas every point of `U` has distance at least `rho>eta`. This proves (5.2).
`square`

The strict margin `rho>epsilon`, supplied by the closed-radius convention and
compactness, is why no extra decimal digit is needed.

## 6. Failure of density places `K_pi` inside a core

**Theorem 6.1 (finite-time hole-to-core implication).** Let `R>=0` and
`0<epsilon<1/2`. If `U_R` is not closed-radius `epsilon`-dense, then there is
a decimal word `w` satisfying

\[
 |w|=\left\lceil\log_{10}(1/\epsilon)\right\rceil   \tag{6.1}
\]

and

\[
 K_\pi\subseteq\operatorname{Core}(w,R).            \tag{6.2}
\]

**Proof.** Apply Lemmas 4.2 and 5.1 to obtain a word `w` whose closed cell
`J_w` is disjoint from `U_R`.

Fix `x in K_pi`, `0<=j<=R`, and `n>=0`. T20's forward invariance and
commutation give

\[
 T_{10}^nT_{16}^jx=T_{16}^jT_{10}^nx
       \in T_{16}^jK_\pi\subseteq U_R.               \tag{6.3}
\]

Hence every point in the forward-times-10 orbit of `T_16^j x` avoids `J_w`.
Choose any decimal expansion `a` of `T_16^j x`. If `a` contained `w` beginning
at coordinate `n`, Lemma 2.5 would put the left side of (6.3) in `J_w`, a
contradiction. Therefore `a in X_w`, so `T_16^j x in K_w`. This holds for
every `j` in the displayed finite range, proving `x in H(w,R)`. Finally use
Lemma 3.4. `square`

No property of pi beyond T20's machine-checked orbit-closure invariance has
been used in Theorem 6.1.

## 7. Conditional reduction from uniform finite cores to C6

**Hypothesis 7.1 (uniform linear finite-core premise).** There exist real
constants `L>=0` and `C` such that, for every nonempty finite decimal word
`w`, there is an integer `r_w>=0` satisfying

\[
 r_w\le L|w|+C                                        \tag{7.1}
\]

and

\[
 \operatorname{Core}(w,r_w)\text{ is finite}.        \tag{7.2}
\]

This hypothesis is not established here, by T20, or by T38.

**Definition 7.2 (common time at one word length).** For each integer `m>=1`,
choose witnesses `r_w` from Hypothesis 7.1 for the finite set `D^m` and set

\[
 R_m=\max_{w\in D^m}r_w.                              \tag{7.3}
\]

Then

\[
 R_m\le Lm+C,                                         \tag{7.4}
\]

and every `Core(w,R_m)` with `w in D^m` is finite by Lemma 3.5.

**Lemma 7.3 (irrationality obstruction).** `K_pi` is infinite.

**Proof.** If `K_pi` were finite, then its subset
`{q(10^n pi):n>=0}` would be finite. Thus there would be integers `0<=n<k`
with

\[
 q(10^n\pi)=q(10^k\pi).
\]

It follows that `(10^k-10^n)pi` is an integer, making `pi` rational. This
contradicts the irrationality of pi. `square`

**Theorem 7.4 (uniform finite cores imply C6, conditionally).** Under
Hypothesis 7.1, C6 holds with the explicit constants

\[
 A=\frac{L+1}{\log 10}>0,\qquad B=L+C,
 \qquad \epsilon_0=\frac12.                          \tag{7.5}
\]

**Proof.** Fix `epsilon` with `0<epsilon<1/2` and set

\[
 m=\left\lceil\log_{10}(1/\epsilon)\right\rceil.
\]

Then `m>=1`. We claim that `U_(R_m)` is closed-radius `epsilon`-dense. If not,
Theorem 6.1 supplies `w in D^m` with

\[
 K_\pi\subseteq\operatorname{Core}(w,R_m).
\]

The right side is finite by Definition 7.2, contradicting Lemma 7.3. This
proves the density assertion.

For the time bound, the elementary ceiling inequality gives

\[
 m<\log_{10}(1/\epsilon)+1
   =\frac{\log(1/\epsilon)}{\log 10}+1.               \tag{7.6}
\]

Since `L>=0` and `log(1/epsilon)>0`, (7.4)-(7.6) imply

\[
 \begin{aligned}
 R_m
 &\le Lm+C\\
 &\le \frac{L}{\log 10}\log(1/\epsilon)+L+C\\
 &\le \frac{L+1}{\log 10}\log(1/\epsilon)+(L+C)\\
 &=A\log(1/\epsilon)+B.
 \end{aligned}                                       \tag{7.7}
\]

These are exactly T20's literal C6 quantifiers. `square`

The conclusion of Theorem 7.4 remains conditional on every quantifier in
Hypothesis 7.1. In particular, Theorem 7.4 is not a pi-specific proof of C6.

## 8. Exact endpoint-complete carry/KMP graph for one core

This section gives a finite condition which, if checked for one fixed pair
`(w,R)`, is sufficient to prove that particular core finite. It does not claim
that the condition holds uniformly, or even for any unbounded family.

Fix for this entire section a nonempty word `w in D^m`, `m>=1`, and an integer
`R>=0`.

**Definition 8.1 (KMP states and transitions).** Let

\[
 Q_w=\{0,\ldots,m-1\}.
\]

State `r` records that the longest suffix of the digits already read which is
a prefix of `w` has length `r`. For `r in Q_w` and `d in D`, let

\[
 \ell(r,d)=\max\{0\le s\le m:
   w_0\cdots w_{s-1}\text{ is a suffix of }w_0\cdots w_{r-1}d\}.
\]

The transition `delta_w(r,d)` is defined and equals `ell(r,d)` when
`ell(r,d)<m`; it is undefined when `ell(r,d)=m`, because that digit completes
the forbidden word. The initial state is `0`.

The standard suffix induction says that an infinite digit stream labels an
infinite KMP path from `0` exactly when it lies in `X_w`.

**Definition 8.2 (endpoint-complete carry set).** Let

\[
 C_{16}=\{-1,0,1,\ldots,15,16\}.                     \tag{8.1}
\]

The values `-1` and `16` are essential for exact circle endpoints. For example,
the equality of `0.000...` with `0.999...` on the circle can require carry
`-1`, and multiplication of `0.999...=1` by `16` relative to `0.000...=0`
can require carry `16`. T38 used a narrower symbolic convention and explicitly
made no circle-endpoint claim; that convention is not substituted here.

**Definition 8.3 (chained simultaneous graph `G(w,R)`).** A vertex is

\[
 v=(r_0,\ldots,r_R;c_1,\ldots,c_R)
   \in Q_w^{R+1}\times C_{16}^{R}.                   \tag{8.2}
\]

Thus the graph has exactly

\[
 |V|=m^{R+1}18^R                                     \tag{8.3}
\]

vertices. Its start set is

\[
 S=\{(0,\ldots,0;c_1,\ldots,c_R):c_j\in C_{16}\},  \tag{8.4}
\]

which has `18^R` elements (and one element when `R=0`).

An edge carries a full digit label

\[
 \mathbf d=(d_0,\ldots,d_R)\in D^{R+1}.
\]

There is an edge

\[
 (r_0,\ldots,r_R;c_1,\ldots,c_R)
 \mathrel{\mathop{\longrightarrow}^{\mathbf d}}
 (r'_0,\ldots,r'_R;c'_1,\ldots,c'_R)                \tag{8.5}
\]

exactly when both of the following finite lists hold:

1. `delta_w(r_j,d_j)` is defined and
   \[
   r'_j=\delta_w(r_j,d_j)\quad(0\le j\le R);         \tag{8.6}
   \]
2. the right-to-left carry equations are
   \[
   16d_{j-1}+c'_j=d_j+10c_j\quad(1\le j\le R).      \tag{8.7}
   \]

Equation (8.7), not its reversal, is the correct equation for a graph read
most-significant digit first: `c'_j` is the carry supplied by the as-yet unread
tail to the right. Parallel edges with different full digit labels are retained.

**Definition 8.4 (path projection).** For an infinite path from `S`, write
`d_{j,n}` for component `j` of the label on its `n`-th edge. Project the path
to

\[
 \kappa(d_{0,0}d_{0,1}d_{0,2}\cdots)\in\mathbb T.   \tag{8.8}
\]

## 9. Exact coding theorem, including decimal endpoints

**Theorem 9.1 (the graph projects exactly onto the core).** The set of circle
points obtained from all infinite paths in `G(w,R)` beginning in `S` is exactly

\[
 \operatorname{Core}(w,R).                           \tag{9.1}
\]

The projection need not be injective, because terminating circle points can
have two decimal expansions.

**Proof, core to path.** Let `x in Core(w,R)=H(w,R)`. For every
`0<=j<=R`, choose `a^(j) in X_w` such that

\[
 \kappa(a^{(j)})=T_{16}^j x.                         \tag{9.2}
\]

These choices are available from Definition 2.3 and retain whichever endpoint
expansion actually avoids `w`.

For `n>=0`, define the value of the tail beginning at `n` by

\[
 A_{j,n}=\sum_{s=0}^{\infty}a^{(j)}_{n+s}10^{-s-1}
          \in[0,1].                                  \tag{9.3}
\]

For `1<=j<=R`, define

\[
 c_{j,n}=16A_{j-1,n}-A_{j,n}.                        \tag{9.4}
\]

Applying `T_10^n` to the circle equality in (9.2) shows that (9.4) is an
integer. Since both tail values lie in `[0,1]`,

\[
 -1\le c_{j,n}\le16,                                 \tag{9.5}
\]

so `c_{j,n} in C_16`. The identity

\[
 A_{j,n}=\frac{a^{(j)}_n+A_{j,n+1}}{10}
\]

turns (9.4) into

\[
 16a^{(j-1)}_n+c_{j,n+1}
   =a^{(j)}_n+10c_{j,n}.                              \tag{9.6}
\]

The avoiding streams provide all KMP transitions (8.6), and (9.6) provides all
carry transitions (8.7). At `n=0` all KMP states are `0` and all carries lie in
`C_16`, so the resulting infinite path starts in `S` and projects to `x`.

**Proof, path to core.** Conversely, take an infinite path from `S`. The KMP
invariant puts each component stream `a^(j)=(d_{j,n})_(n>=0)` in `X_w`.
For fixed `j>=1`, multiply (8.7) at time `n` by `10^{-n-1}` and sum from
`n=0` through `N-1`. The carry terms telescope to give

\[
 16\sum_{n<N}d_{j-1,n}10^{-n-1}
 -\sum_{n<N}d_{j,n}10^{-n-1}
 =c_{j,0}-c_{j,N}10^{-N}.                            \tag{9.7}
\]

The carry sequence is bounded by `16` in absolute value, so its final term
tends to zero. Letting `N` tend to infinity in (9.7) gives

\[
 16\operatorname{val}(a^{(j-1)})
 -\operatorname{val}(a^{(j)})=c_{j,0}\in\mathbb Z.  \tag{9.8}
\]

Therefore

\[
 \kappa(a^{(j)})=T_{16}\kappa(a^{(j-1)}).
\]

Induction on `j` shows that the path projection lies in every
`T_16^{-j}K_w`, hence in `H(w,R)=Core(w,R)`. This proves (9.1). `square`

The graph is finite for each fixed `(w,R)`, while its path set can still be
infinite or uncountable. Finiteness of the state set alone is therefore not a
finiteness certificate for the core.

## 10. An exact SCC certificate sufficient for one core to be finite

All definitions in this section are finite graph operations on `G(w,R)`.

**Definition 10.1 (reachable, live, and cyclic).** A vertex is reachable if a
finite path from `S` ends there. A reachable vertex is live if an infinite path
starts there. In a finite graph, this is equivalent to being able to reach a
directed cycle. Let `G_live` be the labelled multigraph induced by the live
vertices, retaining every edge whose source and target are live.

An SCC of `G_live` is cyclic if it contains a directed cycle; a self-loop
counts as a cycle. It is terminal if no edge of `G_live` leaves it for a
different SCC.

For an edge `e`, let `t(e)` be its target and let `d_0(e)` be the first
component of its full label, namely the digit of the path projection (8.8).

**Definition 10.2 (projected deterministic terminal-SCC condition).** Say that
`CF(w,R)` holds if both finite conditions below hold:

1. every cyclic SCC of `G_live` is terminal;
2. for every vertex `v` in every cyclic SCC, the finite set
   \[
   \{(t(e),d_0(e)):e\text{ is a live outgoing edge from }v\}
   \tag{10.1}
   \]
   has cardinality exactly one.

Parallel edges are allowed by (10.1) only when they have the same target and
the same projected input digit. A simpler but stronger check is to require
exactly one outgoing live edge from each such vertex, counting parallel
labelled edges separately.

An inspectable finite certificate for `CF(w,R)` consists of the explicit
vertex and edge tables from Definitions 8.1-8.3, the reachable and live vertex
lists, an SCC partition, the terminal flags in the condensation DAG, and the
singleton `(target,d_0)` value for each vertex in a cyclic SCC. Tarjan's
algorithm or any independently implemented SCC algorithm can check these
lists; no numerical approximation is involved.

**Theorem 10.3 (complete SCC sufficiency proof).** For every fixed nonempty
word `w` and every fixed `R>=0`,

\[
 CF(w,R)\quad\Longrightarrow\quad
 \operatorname{Core}(w,R)\text{ is finite}.          \tag{10.2}
\]

**Proof.** Let `M` be the number of live vertices and consider any infinite
path from `S`. Every vertex on the path is live, because its prefix shows
reachability and its suffix is an infinite continuation.

Before the path first enters a cyclic SCC, it cannot repeat a vertex: a segment
between two occurrences of the same vertex would be a directed cycle, placing
that vertex in a cyclic SCC. Hence the path enters a cyclic SCC after at most
`M` edges.

Once the path enters a cyclic SCC `C`, it cannot leave. Indeed, every target
used by its infinite suffix is live, while condition 1 says that no edge of
`G_live` leaves `C` for another SCC.

Inside `C`, condition 2 determines from the current vertex both the next
vertex and the next projected digit `d_0`. Repeating this observation
determines the entire projected input tail from the entry vertex. Distinct
parallel edges with the same pair in (10.1) do not create a new projected
input sequence.

There are finitely many start vertices and finitely many finite edge paths of
length at most `M`. Each possible entrance path has at most one projected
infinite continuation. Thus only finitely many projected decimal sequences
occur. Their images under `kappa` form a finite set. By Theorem 9.1 that image
is exactly `Core(w,R)`, proving (10.2). `square`

A crude fully explicit bound, if `E` is the number of live labelled edges, is

\[
 |\operatorname{Core}(w,R)|
 \le |S|\left(1+\sum_{n=1}^{M}E^n\right).            \tag{10.3}
\]

The condition `CF(w,R)` is sufficient, not claimed necessary.

**Boundary check 10.4 (why unlabelled simple cycles are insufficient).** Take
`R=0` and the one-digit forbidden word `w=9`. The graph has one KMP vertex and
nine parallel self-loops with projected labels `0,...,8`. Its unlabelled SCC
is a terminal one-vertex simple cycle, but its projected path set contains all
infinite streams over `{0,...,8}` and is infinite. Condition (10.1) correctly
fails because it sees nine distinct projected digits. This finite example is
only a check on the formulation of `CF`; it is not evidence for any universal
core-extinction claim.

## 11. Exact logical output and remaining frontier

The implications argued in this `proof sketch` are exactly:

1. For every `R>=0` and `0<epsilon<1/2`, failure of closed-radius
   `epsilon`-density of `U_R` implies the existence of a word of length
   `ceil(log_10(1/epsilon))+0` with
   `K_pi subset Core(w,R)`.
2. Hypothesis 7.1 implies C6 with the explicit constants (7.5), using the
   irrationality of pi.
3. For every fixed `(w,R)`, the finite graph condition `CF(w,R)` implies that
   `Core(w,R)` is finite.

What is not established is equally explicit:

1. No `CF(w,R)` certificate is claimed for all words of any unbounded length.
2. No uniform linear choice of extinction times is proved.
3. No T38 tau value is promoted from bounded experiment to an asymptotic
   statement.
4. C6, positive decimal factor entropy for pi, and decimal disjunctivity of pi
   all remain open in this note.

At `proof sketch` status, this note gives the displayed conditional
finite-certificate reduction. The unresolved research problem is to produce
uniform finite SCC certificates with the linear time bound in Hypothesis 7.1,
or to show that this proposed certificate family cannot do so.
