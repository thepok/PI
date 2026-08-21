# Fixed-return dynamics: dense dilate clouds can have disjoint slices

Audit date: **2026-08-12 UTC**
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No proof of the fixed return

\[
             \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0       \tag{1}
\]

was obtained.  Hence no decimal-cylinder hit and no proof that every finite
decimal word occurs in pi was obtained.  Canonical V1 remains a `conjecture`.

This branch produced two precise structural propositions, recorded only as a
`proof sketch`.

1. If $M$ is an infinite minimal closed set for multiplication by 10 on
   the circle, then the compact slices

   \[
                      M_t=16^tM\qquad(t\geq0)                         \tag{2}
   \]

   are pairwise disjoint, while their union is dense.  Every slice has the
   same Hausdorff dimension and the same topological entropy.  Thus joint
   Furstenberg density can be carried by a dense cloud of mutually disjoint
   fixed-$t$ slices.  Compactness, Baire category, dimension, or an
   intersection theorem cannot turn the varying exponent $t$ into $t=0$.

2. There is an explicit high-dimensional measure version.  Let $K_9$ be
   the decimal Cantor set using digits $0,\ldots,8$, and let $\mu$ be its
   uniform Bernoulli measure.  The measures

   \[
                         \mu_t=(\times16^t)_*\mu                         \tag{3}
   \]

   are pairwise mutually singular and all have times-10 entropy $\log 9$,
   yet

   \[
                  {1\over N}\sum_{t=0}^{N-1}\mu_t
                       \mathop{\longrightarrow}^{w^*}\lambda,          \tag{4}
   \]

   where $\lambda$ is Lebesgue measure.  Their supports all contain zero
   and have dimension

   \[
             {\log9\over\log10}>{19\over20}.                           \tag{5}
   \]

   Hence even very large dimension, nonempty support intersections, positive
   entropy, and Lebesgue equidistribution *after averaging the dilates* do not
   yield one fixed return.

These are method-closing obstructions, not a resolution.  They sharpen the
remaining pointwise requirement: an argument must attach multiplication by
16 to the **same decimal orbit closure of pi**, rather than to a dense union
or a weak average of its images.

The primary-source statements used below are `literature-checked` within the
dated scope in Section 8.  The companion replay is an `experiment`; it proves
nothing about pi.

Claim ledger for this file:

- Proposition 2.1 and the Section 4 measure separator: `proof sketch`;
- quoted source statements and the bounded applicability search:
  `literature-checked`;
- companion finite replay: `experiment`;
- V1 and the fixed return (1): `conjecture`;
- `machine-checked` claims: none.

## 1. Normalized target and quantifiers

Put

\[
 T_a(x)=ax\pmod1,\qquad
 \alpha=\pi\pmod1,\qquad
 K_\pi=\overline{\{T_{10}^n\alpha:n\geq0\}}.
\]

The already audited Furstenberg bridge gives

\[
 \mathrm{V1}
 \iff K_\pi=\mathbb T
 \iff T_{16}\alpha\in K_\pi
 \iff \liminf_n\|(10^n-16)\pi\|_{\mathbb T}=0.             \tag{6}
\]

The last return is along an unbounded subsequence.  It is not enough that

\[
 \overline{\bigcup_{t\geq0}T_{16}^tK_\pi}=\mathbb T,        \tag{7}
\]

because (7) lets $t$ vary with the target and scale.  Furstenberg's theorem
proves (7) unconditionally from the irrationality of pi.  Equation (6) asks
for the single point $16\alpha$ in the single slice $K_\pi$.

The ambiguous strengthenings audited below are:

- “the slices are dense in aggregate” does not mean any fixed slice is
  dense;
- “the slices have large dimension” does not mean a prescribed point lies
  in a prescribed slice;
- “the supports intersect” does not mean their invariant measures share a
  nonzero common component;
- weak convergence of an average of pushed measures does not give
  nonsingularity of any one pushed measure; and
- an almost-everywhere theorem for a positive-entropy invariant measure does
  not specialize to the named point pi.

## 2. A topological slice-separation proposition

The next statement is general and strictly stronger than a one-off
counterexample.  It is a `proof sketch`, not a machine-checked declaration.
Its only non-elementary input is the primary-source theorem cited explicitly
in the proof.

**Proposition 2.1 (`proof sketch`).**  Let $a,b\geq2$ be multiplicatively
independent.  Let $M\subset\mathbb T$ be an infinite compact set satisfying
$T_aM\subseteq M$ and minimal for the forward $T_a$-action: every forward
$T_a$-orbit in $M$ is dense in $M$.  Put $M_t=T_b^tM$.  Then:

1. every $M_t$ is an infinite compact $T_a$-minimal set;
2. $M_s\cap M_t=\varnothing$ whenever $s\ne t$; and
3. $\bigcup_{t\geq0}M_t$ is dense in $\mathbb T$.

**Proof.**  A rational point has a finite forward $T_a$-orbit.  If one lay in
$M$, minimality would identify $M$ with the closure of that finite orbit.
Thus every point of the infinite minimal set $M$ is irrational.

The map $T_b^t:M\to M_t$ is a continuous factor commuting with $T_a$.
The image of a minimal system under a factor is minimal.  It is infinite:
if $M_t$ were finite, then its inverse image under the degree-$b^t$ circle
map would be finite and would contain $M$.  This proves item 1.

Two forward-minimal compact sets for the same map which intersect must
coincide: the orbit closure of a point in the intersection equals each set.
Suppose $M_s=M_t$ with $s<t$, and put $r=t-s$.  Then

\[
                         T_b^rM_s=M_s.                           \tag{8}
\]

Choose an irrational $x\in M_s$.  The semigroup
$\{a^ub^{rv}:u,v\geq0\}$ is nonlacunary in Furstenberg's Definition IV.1:
if all its positive elements were powers of one integer, then $a$ and $b^r$
would be multiplicatively dependent, contrary to the hypothesis.
Furstenberg's Theorem IV.1 then makes

\[
              \{a^ub^{rv}x:u,v\geq0\}
\]

dense in the circle.  Equation (8) and $T_aM_s\subseteq M_s$ put this
whole orbit in the closed set $M_s$, so $M_s=\mathbb T$.  But the full
circle is not $T_a$-minimal, since it contains the proper invariant set
$\{0\}$.
This contradiction proves item 2.

Finally, for any $x\in M$, Furstenberg makes the full joint orbit

\[
              \{a^ub^tx:u,t\geq0\}
\]

dense.  For each fixed $t$, its $u$-orbit lies in $M_t$.  The joint
orbit is therefore contained in the union in item 3, proving density.  \(\square\)

The proposition tests the exact quantifier at issue in (7): a dense countable
union may consist of pairwise disjoint compact slices.

### Dimension and entropy do not repair the separation

For an integer $c\geq2$, $T_c$ is globally Lipschitz.  Refine the circle
into finitely many subarcs on which $T_c$ is injective and whose images avoid
the circle cut.  On each such subarc both the restricted map and its inverse
branch are Lipschitz; finite unions take the maximum Hausdorff dimension.
Thus

\[
                         \dim_H(T_cE)=\dim_H E.                   \tag{9}
\]

Likewise $T_b^t:M\to M_t$ is a finite-to-one factor with uniformly bounded
fibres.  Such a factor has zero relative measure entropy: conditional on an
image point there are at most $b^t$ possible full orbit names, so the
conditional entropy of an $N$-name is at most $t\log b$, which vanishes after
division by $N$.  Thus every invariant measure and its pushed measure have
the same entropy.  The variational principle, together with the ordinary
factor inequality in the reverse direction, gives

\[
                         h_{\rm top}(M_t,T_a)
                         =h_{\rm top}(M,T_a).                    \tag{10}
\]

Thus Proposition 2.1 remains a separator after retaining the exact dimension and
entropy of every slice.

## 3. An explicit positive-entropy minimal separator

The abstract proposition has a source-pinned explicit realization.  The
El Abdalaoui--Kasjan--Lemanczyk/Downarowicz--Kasjan construction audited in
the local T103 record gives a one-sided Toeplitz sequence $z_5$ on
$\{-1,0,1\}$.  Let $X_5$ be its compact one-sided shift-orbit closure.
Uniform recurrence makes $X_5$ minimal, and the source-audited language
estimate gives

\[
 h_{\rm top}(X_5)\geq
       \left({6\over\pi^2}-{1\over4}\right)\log2>0.              \tag{11}
\]

Replace the symbols by the decimal digits $0,1,2$, and define

\[
            \kappa(d)=\sum_{j\geq0}d_j10^{-j-1}.                 \tag{12}
\]

If two such streams first differ at position $j$, the leading difference
is at least $10^{-j-1}$, while the largest possible later difference is

\[
       2\sum_{k>j}10^{-k-1}={2\over9}10^{-j-1}.                  \tag{13}
\]

Hence $\kappa$ is injective and quantitatively bi-Lipschitz for the usual
decimal sequence metric.  It conjugates the shift to $T_{10}$.  For a
one-sided subshift in the metric $10^{-j}$, Hausdorff dimension is topological
entropy divided by $\log 10$; in particular (11) gives positive dimension.
Therefore

\[
                         M=\kappa(X_5)                           \tag{14}
\]

is an explicit infinite $T_{10}$-minimal compact set of positive entropy
and positive Hausdorff dimension, contained in $[0,2/9]$.  Applying Proposition
2.1 with $(a,b)=(10,16)$, the sets $16^tM$ are pairwise disjoint, retain
that positive dimension and entropy, and have dense union.

Within the `proof sketch`, this is an explicit counterexample to each general
assertion below:

| proposed general implication | counterexample property |
|---|---|
| dense joint $(10,16)$ orbit $\Rightarrow$ a fixed slice meets another | the slices $16^tM$ are pairwise disjoint |
| positive entropy of all slices $\Rightarrow$ one fixed inclusion | every slice has the positive lower bound inherited from (11) |
| positive Hausdorff dimension plus density $\Rightarrow$ fixed intersection | every slice has the same positive dimension, yet intersections are empty |
| minimality supplies a recurrent bridge between slices | minimality is what forces equality-or-disjointness, and equality is impossible |

The separator is not pi.  It proves that the stated dynamical data alone
cannot distinguish pi from a system in which the fixed return fails.

## 4. A dimension $>19/20$ singular-measure separator

The minimal separator makes the supports disjoint.  A complementary example
shows that even intersecting supports and Lebesgue average behavior are
insufficient.

Let

\[
 K_9=\left\{\sum_{j\geq1}d_j10^{-j}:d_j\in\{0,\ldots,8\}\right\}, \tag{15}
\]

The claims in this section are a `proof sketch`, not machine-checked.  For
the invariance claim, let $\Omega=\{0,\ldots,8\}^{\mathbb N}$, let $\beta$ be
the uniform product measure, and let

\[
 \kappa_9(d)=\sum_{j\geq1}d_j10^{-j}.
\]

Digits never equal 9, so $\kappa_9$ is a continuous injection and hence a
homeomorphism from $\Omega$ onto $K_9$.  It obeys
$\kappa_9\circ\sigma=T_{10}\circ\kappa_9$.  The one-sided Bernoulli shift
$(\Omega,\beta,\sigma)$ is invariant and ergodic.  Therefore
$\mu=(\kappa_9)_*\beta$ is $T_{10}$-invariant and ergodic, and the coding is a
measure-theoretic conjugacy.  In particular,

\[
                  h_\mu(T_{10})=\log9,\qquad
                  \dim_HK_9={\log9\over\log10}>{19\over20}.      \tag{16}
\]

The last strict inequality is the exact integer inequality

\[
                              9^{20}>10^{19}.                    \tag{17}
\]

Put $\mu_t=(T_{16}^t)_*\mu$.  Commutation makes every $\mu_t$
$T_{10}$-invariant and ergodic: it is a factor of the ergodic system
$(K_9,\mu,T_{10})$.  The factor map $T_{16}^t$ has at most $16^t$ points in
each circle fibre.  Conditional on the factor point, an entire $N$-step name
therefore has at most $16^t$ possible lifts, independent of $N$.  Its relative
entropy is zero, so this finite-to-one factor preserves entropy even though
the maps are noninvertible.  Hence

\[
                              h_{\mu_t}(T_{10})=\log9.            \tag{18}
\]

### Pairwise mutual singularity

Suppose $\mu_s=\mu_t=\nu$ for $s<t$, and put $r=t-s$.  Then

\[
                  (T_{16}^r)_*\nu=\nu.                          \tag{19}
\]

This identity uses only composition of pushforwards:

\[
 (T_{16}^r)_*\mu_s=(T_{16}^{r+s})_*\mu=\mu_t=\mu_s.
\]

No inverse map and no cancellation of $T_{16}^s$ is being used.  The measure
$\nu$ is $T_{10}$-ergodic and has positive $T_{10}$ entropy.  Consequently it
is also ergodic for the joint $(T_{10},T_{16}^r)$ action, since a jointly
invariant set is in particular $T_{10}$-invariant.  Rudolph's Corollary 4.11
applies with the coprime generators $u=2,v=5$,
$10=2^1 5^1$, and $16^r=2^{4r}5^0$, since the exponent determinant is

\[
                          1\cdot0-1\cdot4r=-4r\ne0.              \tag{20}
\]

The corollary says that a jointly invariant ergodic non-Lebesgue measure has
zero entropy for both generators; equivalently, positive entropy forces
$\nu$ to be Lebesgue measure.  This contradicts (18), because
Lebesgue times-10 entropy is $\log 10$, not $\log 9$.  Therefore the
measures $\mu_t$ are distinct.  Distinct ergodic invariant probabilities
for one map are mutually singular: Birkhoff averages of a set on which their
integrals differ give disjoint full-measure generic sets.  Hence

\[
                         \mu_s\perp\mu_t\qquad(s\ne t).          \tag{21}
\]

### Their Cesaro average is nevertheless Lebesgue

Hochman's Theorem 1.1, the general Host equidistribution theorem, applies to
$a=10,b=16$.  It says that for $\mu$-almost every $x$, the sequence
$16^tx$ equidistributes for Lebesgue measure.  For every continuous $f$,
dominated convergence therefore gives

\[
\begin{aligned}
 \int f\,d\left({1\over N}\sum_{t<N}\mu_t\right)
 &=\int {1\over N}\sum_{t<N}f(16^tx)\,d\mu(x)\\
 &\longrightarrow\int f\,d\lambda.
\end{aligned}                                                   \tag{22}
\]

This proves (4).  The supports $16^tK_9$ all contain zero and all retain
the dimension in (16).  Their union is dense by Furstenberg, because it
contains the joint orbit of any irrational point of $K_9$.

A $\mu$-generic point has decimal orbit closure $K_9$, so it permanently
omits digit 9.  Host nevertheless makes its times-16 orbit equidistributed.
This is the strongest direct separator found in this branch:

\[
 \boxed{\text{pairwise singular high-entropy slices can average to Lebesgue.}} \tag{23}
\]

Consequently neither averaged weak convergence nor support intersections
give the all-depth nonsingularity/affinity input needed by the existing
Rudolph--Johnson bootstrap.

## 5. Consequence for a hypothetical proper $K_\pi$

Assume the fixed return (1) fails.  By (6), $K_\pi$ is proper.  There are
then two entropy cases.

1. If $h_{\rm top}(K_\pi,T_{10})=0$, entropy and positive-dimension
   rigidity have no input.
2. If $h_{\rm top}(K_\pi,T_{10})>0$, the variational principle supplies a
   $T_{10}$-ergodic positive-entropy probability supported on $K_\pi$.
   Host describes almost every point for that measure under the *varying*
   $16^t$ orbit, but it neither says pi is generic for the measure nor puts
   $16\pi$ in $K_\pi$.  Section 4 shows that pushed measures may even be
   pairwise singular while their mean tends to Lebesgue.

Thus proving merely positive entropy for $K_\pi$ would be important, but it
would not prove the fixed return.  The measure route still needs a property
such as non-mutual-singularity of one ergodic measure and its times-16
pushforward at all generating depths.  That property is exactly what the
existing affinity reduction leaves unproved.

## 6. Euler's identity lives on the wrong character lattice

The special input

\[
                              e^{i\pi}=-1                         \tag{24}
\]

does not interact with the decimal circle through a continuous character.
This mismatch is exact.

Every continuous character of $\mathbb R/\mathbb Z$ has the form

\[
                         \chi_h(x)=e^{2\pi ihx},\qquad h\in\mathbb Z. \tag{25}
\]

The function $x\mapsto e^{ix}$ does not descend to this circle, because
$e^{i(x+1)}\ne e^{ix}$.  More generally $e^{icx}$ descends modulo one
exactly when $c\in2\pi\mathbb Z$.  Thus (24) has frequency
$1/(2\pi)$, outside the dual group in (25).

For $n\geq1$, put $q_n=10^n-16$.  It is even, so Euler gives the exact
but vacuous identity

\[
                              e^{iq_n\pi}=1.                      \tag{26}
\]

Equation (26) says $q_n\pi$ lies in the lattice $2\pi\mathbb Z$.  The
fixed return asks whether those same numbers approach the different lattice
$\mathbb Z$.  Indeed,

\[
 q_n\pi=\left(5\cdot10^{n-1}-8\right)2\pi,\qquad
 \|q_n\pi\|_{\mathbb T}
 =\left\|\left(5\cdot10^{n-1}-8\right)2\pi\right\|_{\mathbb T}. \tag{27}
\]

So Euler's identity rewrites the return as another lacunary orbit of $2\pi$;
it does not estimate it.

The actual circle character needed by (1) is

\[
 e^{2\pi iq_n\pi}=\left(e^{2\pi^2i}\right)^{q_n}.             \tag{28}
\]

No algebraic relation for $e^{2\pi^2i}$ follows from (24), and standard
Lindemann--Weierstrass theorems do not apply to the transcendental exponent
$2\pi^2i$.  Replacing (28) by exponentials of decimal truncations restores
the uncontrolled decimal tail, as audited separately in the sine and
algebraic-logarithm reports.

This character-lattice lemma does not prove that every future use of (24)
must fail.  It closes the direct Fourier transfer: any successful use must
create a genuinely new digit-sensitive auxiliary form, not substitute the
non-periodic function $e^{ix}$ for a circle character.

## 7. Counterexample audit

The conclusions above were checked against the following failure modes.

1. **Dropping irrationality.**  Modulo 11, multiplication by 10 has the
   minimal two-cycle $\{1,10\}$.  Its successive times-16 images are

   \[
   \{1,10\},\{5,6\},\{3,8\},\{4,7\},\{2,9\},                    \tag{29}
   \]

   which are disjoint and cover all nonzero residues, then repeat.  This
   finite analogue shows exactly where irrationality is needed to replace a
   finite joint orbit by circle density.
2. **Dropping minimality.**  The sets $16^tK_9$ all meet at zero.  Thus
   pairwise disjointness is a minimal-slice proposition, not a claim about every
   invariant compact set.
3. **Replacing measure overlap by support overlap.**  The supports in Section
   4 intersect, but the measures are mutually singular.
4. **Using finite cylinder overlap.**  Mutually singular measures can have
   positive common mass at every separately fixed finite decimal depth.  The
   companion replay exhibits this for finite truncations; it does not infer
   an all-depth lower bound.
5. **Treating almost-everywhere as named-point.**  Host's theorem applies to
   $\mu$-almost every point, not to pi merely because pi lies in the circle.

## 8. Source audit and 2025--2026 search

Status of this section: `literature-checked` on **2026-08-12 UTC** for the
bounded sources and searches listed here.

| source | exact checked use | local pin |
|---|---|---|
| H. Furstenberg, [*Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation*](https://doi.org/10.1007/BF01692494), Definition IV.1 and Theorem IV.1, printed pp. 47--48 | “Non-lacunary” means not all positive semigroup elements are powers of one integer; such a semigroup sends every irrational circle point to a dense orbit. | `work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf`, SHA-256 `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358` |
| M. Hochman, [*A short proof of Host's equidistribution theorem*](https://arxiv.org/abs/2103.08938v2), Theorem 1.1, preprint p. 2 | A positive-entropy invariant ergodic times-$a$ measure has almost every point equidistributed under multiplicatively independent times-$b$. | `work/theory/pi-digits/library/t44/hochman-2022-host-equidistribution-v2.pdf`, SHA-256 `2fa94bec2580725a6b2d3e83761af1510f86061a6090528350c44ea785087d0b` |
| D. Rudolph, [*×2 and ×3 invariant measures and entropy*](https://doi.org/10.1017/S0143385700005629), definition of the ergodic common-invariant class on printed p. 399 and Corollary 4.11 on p. 406 | Positive-entropy rigidity for exponent-independent combinations of two coprime generators; (20) checks the $(10,16^r)$ specialization. | `work/theory/pi-digits/library/t44/rudolph-1990-times2-times3.pdf`, SHA-256 `9016e14ea8a3125dbea8532c6f8b2230fb24a33fe5e8818db8bcf0f7a7b57c85` |
| El Abdalaoui--Kasjan--Lemanczyk, [*0-1 sequences of the Thue-Morse type and Sarnak's conjecture*](https://arxiv.org/abs/1304.3587v2), Section 6 | Explicit power-of-five Toeplitz point and coordinate recurrence. | `work/theory/pi-lacunary-near-return-sparsity/library/t103/akl-1304.3587v2.pdf`, SHA-256 `6d65ce118a10b38450fd0d38716a3624ec3a2dea56bb08c32771a88165b88ce3` |
| T. Downarowicz--S. Kasjan, [*Odometers and Toeplitz systems revisited in the context of Sarnak's conjecture*](https://arxiv.org/abs/1502.02307v1), Section 8 | The explicit Toeplitz example has the positive entropy lower bound used in (11). | `work/theory/pi-lacunary-near-return-sparsity/library/t103/downarowicz-kasjan-1502.02307.pdf`, SHA-256 `11f3315b34ec2d84a59c849860c2a2a90903348160e7a4316788840f2713e540` |

The dated 2025--2026 search checked *lacunary orbit fixed target*,
*multiplicative semigroup orbit closure dimension*, *Furstenberg pointwise
slice*, *lacunary shrinking target*, and *fixed recurrence normality*.

- Hauke--Shubin--Stefanescu--Zafeiropoulos,
  [arXiv:2604.02005v1](https://arxiv.org/abs/2604.02005v1), studies circle
  coverings by lacunary centers for Lebesgue-almost every random $x$, with
  extensions to measures having Fourier decay.  It contains no specialization
  to pi and no fixed-$x$ return theorem.
- Becher--Lew Deveali,
  [arXiv:2607.06773v1](https://arxiv.org/abs/2607.06773v1), constructs numbers
  in zero-dimensional sparse base-2 Cantor sets which are normal in every odd
  base.  This is a useful current separator between source-base sparsity and
  cross-base normality; its target bases are odd, so it does not apply to the
  pair $(10,16)$, and it says nothing about pi.
- Kaneko--Mance,
  [arXiv:2510.23380v1](https://arxiv.org/abs/2510.23380v1), determines Borel
  complexity for sets of normal vectors in certain fixed recurrences.  It
  classifies sets of parameters and expressly does not decide a named point
  such as pi.

No checked primary theorem supplied (1), a pi-specific entropy premise, or a
mechanism selecting the fixed slice $t=0$.  This is a bounded negative
applicability result, not a claim that all literature has been exhausted.

## 9. Replay

Run

```text
python3 work/ultrapi-resume/fixed_return_dynamics_check.py
```

The script checks all six local hashes, UTF-8/control-character and delimiter
integrity of this report, the exact mod-11 cosets (29), the identity (27) for
$1\leq n\leq80$, the pushforward exponent composition for
$0\leq s<t\leq10$, the determinant (20) for $1\leq r\leq80$, the exact
inequality (17), and a bounded finite-truncation cylinder-overlap table.
Expected top-level output is `"status": "PASS"`.
Every finite output is labeled `experiment`; it is neither a measure theorem
nor evidence for the fixed-pi liminf.

## Bottom line

The fixed-return theorem remains unproved.  The useful new finding is that
the most natural entropy/dimension rescue of Furstenberg's varying-exponent
orbit is structurally false in a strong form: fixed dilate slices can be
pairwise disjoint with dense union, and high-dimensional positive-entropy
pushforwards can be pairwise singular while averaging to Lebesgue.  Euler's
identity does not bridge the gap because it lives on the $2\pi\mathbb Z$
lattice rather than the character lattice of the decimal circle.

What would change the verdict is one genuinely pointwise input for pi, for
example a nonzero all-depth common component between a $T_{10}$-ergodic
measure supported on $K_\pi$ and its times-16 pushforward, or a
digit-sensitive estimate forcing $16\pi\in K_\pi$.  Neither is supplied by
the checked literature or by the exact identities above.
