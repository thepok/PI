# Balanced three-adic selector tower: exact aliases and the residual obstruction

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local source contains no external source URL,
so none is invented here.  
Inputs: [the three-adic selector note](machin_three_adic_coarse_correlation.md),
[the nested-resonance note](three_primary_resonance_attack.md),
[T52](../../TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean),
and [T53](../../TheoryLib/PiQuantitativeBlockHitting/T53T53MachinQuotientCarry.lean).

## Outcome and claim status

No proof that every finite decimal word occurs in \(\pi\) was obtained.  The
canonical target remains a `conjecture`.

This note pursues a genuinely growing, non-singleton selector depth

\[
                         k_j=\lfloor a_j/2\rfloor.             \tag{1}
\]

For every \(j\ge2\), it satisfies \(1\le k_j<a_j-1\); the forbidden
tautological choice \(k=a_j-1\) is never used.  The selected grid has
\(3^{a_j-1-k_j}\asymp\sqrt{D_j}\) points.

The exact result is a sharp separator, retained as a `proof sketch` because
it has not been formalized in Lean:

1. The depth-\(k\) selected grid is not a new ensemble.  It is exactly the
   coset \(x_j+q_{j,k}^{-1}\mathbb Z/\mathbb Z\) centered on the actual
   Machin point, where \(q_{j,k}=D_j/3^k\).
2. Successive depths give a ternary partition.  The selector chooses one
   child, and that child can contain **all** of the parent's avoiding points.
   Only the sum over all three children has cube-root cancellation.
3. The exact fine residual obeys multiplication by \(3^{-1}\bmod F_j\), not
   a contracting recurrence.  It selects a cube root of the parent Fourier
   phase; it does not average the three roots.
4. At the balanced depth, the stable harmonic staircase contains
   \(\Theta(3^{k_j})\), not \(O(1)\), surviving Taylor exponents.  The factor
   by which the grid shrinks is exactly the factor by which its resonant
   Fourier lattice becomes denser.
5. An explicit rational model preserves the actual stable leading-residue
   tower through the balanced depth, the exact \(D_j\) schedule, and a
   positive T46-size geometric coboundary, while retaining an all-1 prefix of
   length \(2j\).  It deliberately changes the actual fine phase.  Therefore
   the staircase and generic recurrence geometry are insufficient; a new
   theorem about the **actual Archimedean fine residual** is indispensable.

The companion checker is an `experiment`.  Finite evidence is never used as
proof.

## 1. Normalized target and all quantifiers

The canonical V1 statement is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^m\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.              \tag{2}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed,
and \(m=0\) is vacuous.  This is contiguous finite occurrence, not
subsequence occurrence and not normality.

Fix \(j\ge2\), and put

\[
 y_j=10^jM_{3j},\qquad x_j=\{y_j\}={b_j\over F_jD_j},
 \qquad D_j=3^{a_j-1},                             \tag{3}
\]

where

\[
 3^{a_j}\le12j+3<3^{a_j+1},\qquad (F_j,D_j)=1,
 \qquad0\le b_j<F_jD_j.                           \tag{4}
\]

T52 supplies the exact complete three-primary factor \(D_j\).  Split

\[
 b_j=F_jc_j+r_j,\qquad0\le c_j<D_j,\qquad0\le r_j<F_j,
 \qquad\theta_j={r_j\over F_j}.                   \tag{5}
\]

At a selector depth \(1\le k\le a_j-1\), define

\[
 d=3^k,qquad q={D_j\over d}.                     \tag{6}
\]

Let \(L_{j,k}\in\{0,\ldots,d-1\}\) be the canonical residue of
\(D_jy_j\) modulo \(d\) in \(\mathbb Z_{(3)}\), and define

\[
 T_{j,k}=r_jF_j^{-1}\pmod d,qquad
 C_{j,k}=L_{j,k}-T_{j,k}\pmod d,                 \tag{7}
\]

again using canonical integer representatives.  The selector lemma gives

\[
                         C_{j,k}=c_j\pmod d.       \tag{8}
\]

All later count formulas fix \(j,k\), a nonempty forbidden word \(w\), and
a finite prefix length \(n\).  The natural computational pulse is
\(n=2j+|w|-1\), but the algebraic identities hold for every \(n\ge0\).

## 2. The selector grid is an actual-centered coset

The absolute selector formula is

\[
 \mathcal G_{j,k}=
 \left\{{C_{j,k}+dt\over D_j}+{r_j\over F_jD_j}:
             0\le t<q\right\}.                   \tag{9}
\]

Since \(c_j=C_{j,k}+dt_0\) for a unique \(0\le t_0<q\), translation of
the index gives the more revealing identity

\[
 \boxed{\mathcal G_{j,k}=
 x_j+{1\over q}\mathbb Z/\mathbb Z.}             \tag{10}
\]

Thus the selector does not produce samples independent of the target.  It
produces a smaller coset which contains, and is naturally centered on, the
actual target point.  At \(k=a_j-1\), (10) is the singleton \(\{x_j\}\),
so proving its avoidance count is zero would merely restate the desired hit.
Equation (1) stays a factor of roughly two away from this singleton depth,
but the actual-centered dependence remains.

For a forbidden word \(w\), let \(A_w(n)\subset\{0,\ldots,10^n-1\}\) be
the decimal prefixes avoiding \(w\), let \(f_{w,n}\) be the corresponding
half-open cylinder indicator on the circle, and put

\[
 N_{j,k}(w,n)=\sum_{z\in\mathcal G_{j,k}}f_{w,n}(z).           \tag{11}
\]

Under a missing-word hypothesis at a scale where the Machin shadow is
valid, \(f_{w,n}(x_j)=1\), and therefore

\[
                         N_{j,k}(w,n)\ge1          \tag{12}
\]

at **every** selector depth.  This is the basic integrality barrier that a
multiscale contraction would have to overcome.

## 3. Boundary-safe finite Fourier formula

Put \(Q=F_jD_j\), \(M=10^n\), and define on \(\mathbb Z/Q\mathbb Z\)

\[
 g(a)=\mathbf1_{A_w(n)}\!\left(\left\lfloor{Ma\over Q}\right\rfloor\right),
 \qquad
 \widehat g(h)=\sum_{a=0}^{Q-1}g(a)e(-ha/Q).       \tag{13}
\]

The selected numerator coset is

\[
                    F_j(C_{j,k}+dt)+r_j,qquad0\le t<q.       \tag{14}
\]

Finite Fourier inversion and subgroup orthogonality give, with no endpoint
qualification,

\[
 \boxed{
 N_{j,k}(w,n)={1\over F_jd}\sum_{u=0}^{F_jd-1}
 \widehat g(qu)
 e\!\left({u(F_jC_{j,k}+r_j)\over F_jd}\right).} \tag{15}
\]

For comparison with the digit automaton, define

\[
 S_{w,n}(h)=\sum_{v\in A_w(n)}e(-hv/M).            \tag{16}
\]

Away from cylinder endpoints, the symmetric-limit Poisson form is

\[
 \boxed{
 \begin{aligned}
 N_{j,k}(w,n)={}&{q\,|A_w(n)|\over M}\\
 &+\lim_{H\to\infty}\sum_{0<|\ell|\le H}
 {1-e(-\ell q/M)\over2\pi i\ell}
 S_{w,n}(\ell q)e(\ell\beta_{j,k}),
 \end{aligned}}                                  \tag{17}
\]

where

\[
 \beta_{j,k}=\left\{qx_j\right\}
 ={C_{j,k}+\theta_j\over d}.                     \tag{18}
\]

Formula (15) remains exact at endpoints.  Formula (17) displays the exact
tradeoff: selecting depth \(d\) divides the zero mode and grid size by
\(d\), but also divides the resonant spacing by \(d\), making the lattice
\(d\) times denser.

## 4. Exact fine residual and its inverse-three recursion

The congruence defining \(C_{j,k}\) has an exact integral quotient.  Define

\[
 \boxed{
 R_{j,k}:={F_j(C_{j,k}-L_{j,k})+r_j\over3^k}\in\mathbb Z.}   \tag{19}
\]

Then the Fourier phase in (18) recombines exactly as

\[
 \boxed{
 \beta_{j,k}={L_{j,k}\over3^k}+{R_{j,k}\over F_j}.}         \tag{20}
\]

This is stronger and cleaner than treating the fine term as an unspecified
error: the first summand is the stable leading-unit staircase, while the
second is the actual Archimedean residual character.

Now lift from \(k\) to \(k+1\).  There are unique ternary digits
\(u_{j,k},v_{j,k}\in\{0,1,2\}\) such that

\[
 C_{j,k+1}=C_{j,k}+3^ku_{j,k},\qquad
 L_{j,k+1}=L_{j,k}+3^kv_{j,k}.                   \tag{21}
\]

Substitution into (19) gives the exact recurrence

\[
 \boxed{
 3R_{j,k+1}=R_{j,k}+F_j(u_{j,k}-v_{j,k}),
 \qquad
 R_{j,k+1}\equiv3^{-1}R_{j,k}\pmod {F_j}.}       \tag{22}
\]

Correspondingly,

\[
 \boxed{3\beta_{j,k+1}=\beta_{j,k}+u_{j,k},
 \qquad e(3\ell\beta_{j,k+1})=e(\ell\beta_{j,k}).}         \tag{23}
\]

Equations (22)--(23) are closure, not cancellation.  Multiplication by
\(3^{-1}\) merely permutes residues modulo \(F_j\).  It creates one chosen
cube root of the parent phase; it does not sum the three cube roots.  In
particular,

\[
 e(\ell R_{j,k+1}/F_j)
 =e(\ell(3^{-1}\bmod F_j)R_{j,k}/F_j)             \tag{24}
\]

is still one unit-modulus character.  No magnitude decreases.

This is the sharp answer to the proposed residual-phase route: the exact
fine residual is compatible across depth, but its compatibility is a
frequency permutation.  A cancellation theorem would have to be an
additional result about the actual orbit of \(R_{j,k}\) against the changing
digital coefficients in (17).

## 5. Ternary occupancy and Fourier alias recurrence

Let \(d=3^k\), \(q=D_j/d\), and suppose \(k<a_j-1\).  Put
\(q'=q/3\) and

\[
 \alpha_k={C_{j,k}\over D_j}+{r_j\over F_jD_j}.              \tag{25}
\]

The parent grid is the disjoint union

\[
 \mathcal G_{j,k}=\bigsqcup_{a=0}^2\mathcal G_{j,k}^{(a)},
 \quad
 \mathcal G_{j,k}^{(a)}=
 \left\{\alpha_k+{a+3t\over q}:0\le t<q'\right\}.          \tag{26}
\]

Equation (21) says that the actually selected child is precisely

\[
                    \mathcal G_{j,k+1}=\mathcal G_{j,k}^{(u_{j,k})}.          \tag{27}
\]

Therefore the direct occupancy recursion is only

\[
 N_{j,k}=N_{j,k}^{(0)}+N_{j,k}^{(1)}+N_{j,k}^{(2)},
 \qquad N_{j,k+1}=N_{j,k}^{(u_{j,k})}.            \tag{28}
\]

There is no inequality here.  The selected child may retain the entire
parent occupancy.

For a trigonometric polynomial \(f\) (and, by the same endpoint convention
as above, for the cylinder indicator), the child formula is

\[
 N_{j,k}^{(a)}=q'\sum_{\ell\in\mathbb Z}
 \widehat f(\ell q')e(\ell q'\alpha_k)e(\ell a/3).           \tag{29}
\]

The terms with \(3\mid\ell\) equal one third of the parent count.  Hence

\[
 \boxed{
 N_{j,k+1}={1\over3}N_{j,k}+
 q'\sum_{3\nmid\ell}\widehat f(\ell q')
 e(\ell q'\alpha_k)e(\ell u_{j,k}/3).}           \tag{30}
\]

Only after summing (29) over all three values of \(a\) do the
\(3\nmid\ell\) terms cancel.  The actual selector keeps exactly one value of
\(a\).  Re-centering every grid at \(x_j\) makes that value \(a=0\), which
clarifies the tautology: the filtration follows the child already known to
contain the actual point.

Under a missing-word hypothesis, once a parent has one avoiding point and
that point is \(x_j\), the selected child also has that point.  Thus
\(N_{j,k}=N_{j,k+1}=1\) is compatible with every exact identity above.  A
strict factor smaller than one cannot hold uniformly at sparse occupancy.

## 6. What balanced growth costs

Take (1), write \(d_j=3^{k_j}\), and put \(q_j=D_j/d_j\).  The two parities
of \(a_j\) give exactly

\[
 \begin{array}{c|c|c|c}
 a_j&d_j&q_j&D_j\\ \hline
 2s&3^s&3^{s-1}&d_jq_j=d_j^2/3\\
 2s+1&3^s&3^s&d_jq_j=d_j^2.
 \end{array}                                      \tag{31}
\]

Thus \(d_j\) and \(q_j\) are balanced at square-root scale and always obey

\[
                             d_jq_j=D_j.           \tag{32}
\]

The stable staircase formula is valid because
\(a_j\ge2k_j-1\).  But its renormalized cutoff is

\[
 h_{j,k_j}=
 \left\lfloor{12j+3\over3^{a_j-k_j+1}}\right\rfloor,
 \qquad {d_j\over3}\le h_{j,k_j}<d_j.            \tag{33}
\]

Consequently its number of surviving odd exponents lies between roughly
\(d_j/6\) and \(d_j/2\).  The fixed-depth claim "fewer than \(3^k\) terms"
is uniform only when \(k\) is fixed.  At balanced growing depth it is a
\(\Theta(d_j)\)-term arithmetic sum, not a bounded-state forcing.

For every fixed nonempty word, the automaton avoidance count has exponential
rate strictly below \(10\).  Since \(D_j\le4j+1\), the zero mode

\[
                  {q_j|A_w(2j+|w|-1)|\over10^{2j+|w|-1}}     \tag{34}
\]

tends to zero.  This does not imply the integer count is zero: (30) leaves
the selected nonzero aliases completely uncontrolled.  In summary:

- sample count and zero mode improve by \(d_j\);
- resonant frequencies become \(d_j\) times denser;
- the stable leading sum itself has \(\Theta(d_j)\) terms; and
- the actual child can retain 100% of the parent occupancy.

No scale gain survives without a signed estimate using the actual residual
phase.

## 7. Cross-index balanced recurrence

Let \(\Delta_j=y_{j+1}-10y_j>0\).  Since
\(x_{j+1}=\{10x_j+\Delta_j\}\), and since (31) implies

\[
 \sigma_j={q_{j+1}\over q_j}\in\{1,3\},          \tag{35}
\]

the balanced Fourier phase obeys

\[
 \boxed{
 \beta_{j+1,k_{j+1}}=
 \{10\sigma_j\beta_{j,k_j}+q_{j+1}\Delta_j\}.}  \tag{36}
\]

Equivalently,

\[
 e(\ell\beta_{j+1,k_{j+1}})=
 e(10\sigma_j\ell\beta_{j,k_j})
 e(\ell q_{j+1}\Delta_j).                        \tag{37}
\]

At an \(a=2s\to2s+1\) threshold, \(d_j\) stays fixed and \(q_j\) triples.
At an \(a=2s+1\to2s+2\) threshold, both \(D_j\) and \(d_j\) triple, so
\(q_j\) stays fixed: the new selector digit absorbs the denominator
tripling.  This closes the frequency bookkeeping but supplies no decay.
The combined phase in (37) is still the actual fixed-\(\pi\) lacunary phase
up to T38's small tail.

## 8. Stable-staircase separator preserving the actual tower

The following explicit model isolates what is missing.  It preserves the
**actual** stable leading residue at every depth through \(k_j\), but
deliberately replaces the actual fine residual.

Assume \(a_j\ge5\), put \(d_j=3^{k_j}\), and let
\(L_j=L_{j,k_j}\).  T52 implies \(3\nmid L_j\).  Choose the canonical unit

\[
 s_j\equiv-L_j^{-1}\pmod {d_j},\qquad1\le s_j<d_j,            \tag{38}
\]

and define

\[
 F_j^*=d_j10^{9j}+s_j,qquad
 \varepsilon_j={1\over D_jF_j^*},qquad
 z_j={1\over9}-\varepsilon_j.                    \tag{39}
\]

Because \(k_j\le a_j-3\), one has \(d_j\mid D_j/9\).  The fraction

\[
 z_j={D_jF_j^*/9-1\over D_jF_j^*}                \tag{40}
\]

is reduced: its numerator is \(-1\) modulo every prime factor of \(F_j^*\)
and modulo three.  Therefore its complete three-primary denominator is
exactly \(D_j\).  Moreover,

\[
 D_jz_j={D_j\over9}-{1\over F_j^*}
 \equiv-(F_j^*)^{-1}\equiv L_j\pmod {d_j}.        \tag{41}
\]

Reduction of (41) modulo every \(3^k\mid d_j\) shows that this model agrees
with the actual Machin leading-residue staircase at **all** depths
\(1\le k\le k_j\), not merely at the top balanced depth.

Since \(10^{-9}<\rho=10/625^3\),

\[
 0<\varepsilon_j<10^{-9j}<\rho^j,
 \qquad
 \varepsilon_j<{1\over9\,10^{2j}}.               \tag{42}
\]

Thus \(z_j\) starts with \(2j\) consecutive digit 1s and avoids digit zero
on the natural pulse.  Put

\[
                         \eta_j=10\varepsilon_j-\varepsilon_{j+1}.           \tag{43}
\]

The explicit size of \(F_j^*\) gives \(\varepsilon_{j+1}<2\cdot10^{-9}
\varepsilon_j\), so \(\eta_j>0\), and

\[
 z_{j+1}=\{10z_j+\eta_j\},\qquad
 \sum_{u=0}^{s-1}10^{s-1-u}\eta_{j+u}
 =10^s\varepsilon_j-\varepsilon_{j+s}
 <10^s\rho^j.                                    \tag{44}
\]

This separator preserves:

1. the exact \(D_j\) schedule;
2. the actual stable harmonic-staircase residue through balanced depth;
3. a positive rational coboundary and the T46 geometric pulse bound;
4. nested selected grids and closed frequencies; and
5. a surviving digit-zero-avoiding actual member at every scale.

It does **not** preserve \(r_j/F_j\), \(R_{j,k}/F_j\), or the exact Machin
forcing.  Therefore it does not refute a theorem using those actual values.
It proves precisely that the stable staircase, even as an entire growing
tower, cannot replace such a theorem.

## 9. Exact finite falsification (`experiment`)

[`machin_selector_multiscale_check.py`](machin_selector_multiscale_check.py)
uses incremental exact `Fraction` Machin seeds, integer modular arithmetic,
and exact decimal-prefix floors.  It checks:

- the stable leading residue, coarse/fine selector, and residual integrality
  at every depth \(1\le k\le k_j\);
- the exact inverse-three recurrence (22), phase recombination (20), and
  cube-root identity (23);
- the balanced ternary grid partition, actual membership, and cross-index
  phase recurrence;
- one- and two-digit avoidance at natural length, including which selected
  child receives each avoiding point; and
- the staircase-preserving separator (38)--(44).

Through \(j=240\), the balanced child was larger than one third of its
parent in 59 one-digit cases and 9,879 two-digit cases.  It retained the
parent's entire positive occupancy in 14 one-digit cases and 2,442 two-digit
cases; 11 and 1,833 of these, respectively, had the exact sparse pattern

\[
                              N_{j,k_j-1}=N_{j,k_j}=1.         \tag{45}
\]

For example, at \(j=7\), the digit-4 and digit-7 counts both satisfy (45).
For two-digit words, the first retained-parent examples occur at \(j=67\).
These are finite counterexamples to uniform per-depth averaging, not evidence
against a possible eventual theorem using additional actual arithmetic.

The largest observed occupancy/zero-mode ratios were

\[
 \begin{array}{c|c|c|c|c}
 |w|&j&w&q_j&N/(\text{zero mode})\\ \hline
 1&16&4&3&9.7077468625\ldots\\
 2&233&75&27&12.6059205937\ldots
 \end{array}                                      \tag{46}
\]

All ten one-digit selected-grid occupancies were zero after \(j=16\) in the
checked range.  Many two-digit occupancies survived or resurrected later,
especially when \(q_j\) tripled; finite disappearance or survival proves no
asymptotic statement.  The exact separator matched 622 actual staircase
residues and retained 221 all-1 prefixes for \(20\le j\le240\).

Reproducible commands:

```bash
python3 -m py_compile \
  work/ultrapi-resume/machin_selector_multiscale_check.py
python3 work/ultrapi-resume/machin_selector_multiscale_check.py --max-j 240
```

Checker SHA-256:
`293122cb1533dccb0b1c59ba1c79b56c5adf4abeb119bab5dc593c87d791c0a5`.

## 10. Precise continuation target

The balanced selector is useful bookkeeping, but it does not itself
contract.  A non-tautological continuation must prove at least one result
not shared by the separator:

- a signed estimate for the nondivisible-by-three residual aliases in (30),
  using the actual \(R_{j,k}/F_j\);
- an Archimedean exclusion showing that the actual residual phases cannot
  follow digital major arcs while \(k\) grows; or
- a cross-index estimate for the exact Machin \(\Delta_j\) which couples
  (37) to the word automaton and forces the actual selected child to be empty.

Merely iterating (22), bounding the harmonic staircase term count, summing
all three aliases, or taking \(k\) closer to \(a_j-1\) cannot suffice.  The
last maneuver tends to the singleton \(\{x_j\}\) and becomes tautological.

## Bottom line

At \(k_j=\lfloor a_j/2\rfloor\), the selector grid is genuinely smaller and
non-singleton, but it is exactly an actual-centered coset.  Its depth
recursion chooses one ternary alias; the residual phase is multiplied by
\(3^{-1}\) modulo \(F_j\), which is a permutation, not a contraction.  The
staircase has square-root many terms at this growing depth, while the Fourier
lattice is square-root denser.  Exact computation exhibits full and
singleton occupancy concentration, and the explicit model shows that even
the actual stable leading-residue tower plus generic Machin-scale forcing is
compatible with perpetual avoidance.  The unresolved datum is the actual
Archimedean fine residual.  No V1 resolution or completion notification
follows.
