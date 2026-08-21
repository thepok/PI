# T98: T95 exact-word charging versus literal T56/C7

Status: **proof sketch**. The imported declarations identified below are
machine-checked. Sections 5-6 give an independent complete paper proof of the
T95 charging estimate and its constant-explicit transport, but those sections
have not been machine-checked or independently reviewed.

## Provenance and scope

- Agenda item: `T98`, serving `G24`.
- Canonical source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Original source URL: none; this is the local formulation recorded on
  2026-07-22.
- Byte-exact delivered copy: `canonical_statement.txt`.
- Canonical SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.

The canonical question asks whether

\[
 \forall A\in\mathbb N_{\ge1}\ \exists n_0\ge1\ \forall n\ge n_0\
 \ \exists N\ge1:\quad A n Q_\pi(n,N)\le N^2,
\]

where `Q_pi` is ordered, diagonal-inclusive, uses strict circle distance, and
has `N` depending on `A,n`. T98 does not prove or assume this statement. T98 is
only a cross-program soundness audit of the T83 Review-B claim. It does not
reopen T67's terminal-ray comparator and makes no claim about fixed `pi`, the
canonical question, C1, or C2.

The only interpretation requiring resolution is the word "controls": direct
upper control of T61's Vaaler majorant is different from indirect upper control
of T56's near-return count. Section 4 shows that the former does not follow;
Section 6 proves the latter conditionally, with all constants displayed.

## Normalized interfaces and ambiguities

All divisions in exponents or bandwidths below are natural-number divisions.
Fix `n>=1` and write

\[
 L_n=10^{\lfloor n/2\rfloor},\qquad H_n=\lfloor10^n/2\rfloor.
\]

The relevant ambiguity list is:

1. The T56 statistic is metric strict near-return, not exact word equality.
2. T56 includes the diagonal in `Q_pi`; both residual sectors and both T95
   statistics exclude it.
3. Positive lag `r` is doubled in both programs to restore ordered pairs.
4. Lag `n` is long, not short, in both programs.
5. T61's frequency cutoff is strict. Its zero mode is separated from positive
   frequencies and the positive-frequency range is `1<=h<H_n`.
6. The Vaaler majorant is summed over the arithmetic-residual rectangle before
   imposing nearness. It is not a collision count.
7. The T95 note is unverified exploration. No assertion below uses its claimed
   theorem as a premise; Section 5 reproduces the argument independently.

## Source and declaration pins

The delivered `T98StatisticImports.lean` imports the definitions instead of
copying or redeclaring them. The audited source hashes are:

| Interface | Source SHA-256 |
|---|---|
| T83 literal audit | `013170204762b54fd9e8791f6723f189473ccbf03d4a4ec7b63ad657e44ea424` |
| T92 exact-word definitions | `d912120e6ebc122d82f889f1731be56eb756b312b66244ff22ee451317e7cd12` |
| T56 lag-sector source | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` |
| T61 Vaaler source | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` |
| T7 finite-cylinder source | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` |
| T1 exact-long source | `64ff2687e84edc22a843da65a54b3f801713455ff54df457f508cc5ef14a20b0` |
| T2 exact-to-residual source | `ffe231e2750445a8f2c0a342cb60e1259a2427e5bb0f8067bf1350ab62bdeba3` |
| T95 unverified note | `08baad91851c1d25ceaa82f86cbe8b728ca2c063f31f01f83c5fa96aea45d8cb` |

No external literature result or novelty claim is needed: this is an internal
interface audit. Searches were confined to the named local modules and their
imported machine-checked dependencies.

## 1. Literal T56/C7 statistic

### 1.1 Full near-return count and lag decomposition

At `L=L_n`, T56's source theorem
`sparse_Q_exact_lag_decomposition` states exactly

\[
 Q_\pi(n,L)=L+2\sum_{r=1}^{L-1}
  \#\left\{0\le j<L-r:
  \left\|10^j(10^r-1)\pi\right\|_{\mathbb R/\mathbb Z}<10^{-n}\right\}.
 \tag{1.1}
\]

Thus pairs are ordered, the diagonal contributes exactly `L`, the cutoff is
strict, every positive lag `1<=r<=L-1` is present, and the triangular boundary
is exactly `0<=j<L-r`.

Given real `mu,c` and natural `Q0`, let `ArithmeticExcluded(mu,c,Q0,n,j,r)`
be T25's existing arithmetic mask. The residual starts at lag `r` are exactly

\[
 \mathcal N_r=\{0\le j<L-r:
   \|10^j(10^r-1)\pi\|_{\mathbb R/\mathbb Z}<10^{-n},\
   \ \neg\operatorname{ArithmeticExcluded}(\mu,c,Q0,n,j,r)\}.
 \tag{1.2}
\]

The literal residual sectors are

\[
 S^{\rm res}_n=2\sum_{\substack{1\le r\le L-1\\r<n}}|\mathcal N_r|,
 \qquad
 T^{\rm res}_n=2\sum_{r=n}^{L-1}|\mathcal N_r|.             \tag{1.3}
\]

These are exactly `shortResidualPairCount mu c Q0 n L` and
`longResidualPairCount mu c Q0 n L`. The first range is equivalently
`0<r<n` and `r<L`; the second is `0<r`, `n<=r`, and `r<L`. Neither contains
the diagonal. Under the explicit premise

```text
EffectiveIrrationality Real.pi mu c Q0
```

the machine-checked T56 identity is

\[
 Q_\pi(n,L)=L+S^{\rm res}_n+T^{\rm res}_n.                 \tag{1.4}
\]

Without that premise there is an additional nonnegative excluded sector.
The unconditional checked short estimate is only
`S_res <= 2 L n`.

### 1.2 C7 and all frequencies

For arbitrary `L` and `H>=1`, T26 defines

\[
 \mathcal F_\pi(L,H)=
 \sum_{\substack{h\in\mathbb Z\\|h|<H}}
 \left(1-\frac{|h|}{H}\right)
 \left|\sum_{j=0}^{L-1}
   e^{2\pi i h\{10^j\pi\}}\right|^2.                       \tag{1.5}
\]

The signed integer range is strict, contains `h=0`, and contains both signs
for every `1<=|h|<H`. The weight is triangular and vanishes only at the
excluded endpoints `|h|=H`. Literal C7 is

\[
 \exists C>0\ \exists N\ge1\ \forall n\ge N:\quad
 \mathcal F_\pi(L_n,H_n)\le C H_n L_n.                    \tag{1.6}
\]

The constant precedes the cutoff and all later `n`. T27 machine-checks that
(1.6) is equivalent to an eventual `Q_pi(n,L_n)<=A L_n` bound. In the
count-to-energy direction, a pointwise constant `A` becomes the explicit
energy constant `17A`.

## 2. Literal T61 Vaaler interface

T61 uses the same `L_n,H_n`. Before imposing nearness, its residual start
domain is

\[
 D_r=\{0\le j<L_n-r:
       \neg\operatorname{ArithmeticExcluded}(\mu,c,Q0,n,j,r)\}. \tag{2.1}
\]

The lag range remains exactly `0<r<n` and `r<L_n`. The strict incidence half
count is

\[
 I_n=\sum_{\substack{1\le r\le L_n-1\\r<n}}|\mathcal N_r|,
 \qquad S^{\rm res}_n=2I_n.                                \tag{2.2}
\]

T61's periodic Vaaler majorant at bandwidth `H` has Fourier coefficients

\[
 \widehat V_H(0)=\frac2H,
 \quad
 \widehat V_H(h)=a_H(|h|)\quad(0<|h|<H),
 \quad
 \widehat V_H(h)=0\quad(|h|\ge H),                          \tag{2.3}
\]

where

\[
 a_H(h)=\frac1H\left(
 \frac{\sin(\pi h/H)}{\pi}
 +2(1-h/H)\cos(\pi h/H)\right).                            \tag{2.4}
\]

The coefficient can change sign; no absolute values replace it. Summing the
majorant over the complete masked rectangle gives

\[
 M_n=\frac{2}{H_n}\sum_r|D_r|
 +2\sum_{h=1}^{H_n-1}a_{H_n}(h)
   \sum_r\sum_{j\in D_r}
   \cos\!\left(2\pi h\,(10^j(10^r-1))\pi\right).           \tag{2.5}
\]

This is `structuredVaalerMajorantTotal`, exactly equal to
`completeStructuredVaalerExpression`. The endpoint convention is important:
the strict central indicator is zero at circle distance `1/(2H_n)=10^-n`,
while the majorant equals one there. The proved theorem direction is

\[
 \boxed{I_n\le M_n}.                                       \tag{2.6}
\]

An upper bound on `I_n`, whether supplied by exact-word charging or otherwise,
does not imply an upper bound on `M_n` from (2.6). T95 therefore does not
control the Vaaler majorant directly, and this audit never reverses (2.6).

## 3. Literal T95 arbitrary-word statistics

Fix an integer base `b>=2`, an alphabet `Sigma` with exactly `b` symbols, and
an integer `n>=1`. Put

\[
 k=\lfloor n/2\rfloor,\qquad L=b^k.                        \tag{3.1}
\]

Let `x` be one finite word of length at least `L+n-1`; longer words are legal.
For each of the exactly `L` starts `0<=i<L`, define the length-`n` factor
`U_i=x[i,i+n)`. The last permitted factor ends at `L+n-2`. Define

\[
 S_b(x,n,L)=\#\{(i,j):0\le i,j<L,\ 0<|i-j|<n,\ U_i=U_j\}, \tag{3.2}
\]

\[
 R_b(x,n,L)=\#\{(i,j):0\le i,j<L,\ |i-j|\ge n,\ U_i=U_j\}.\tag{3.3}
\]

Both counts are ordered and off-diagonal. Overlap is allowed in (3.2); lag
`n` is included in (3.3). Equivalently, in the positive-lag convention,

\[
 S_b=2\sum_{\substack{1\le r\le L-1\\r<n}}
   \#\{0\le i<L-r:U_i=U_{i+r}\},                           \tag{3.4}
\]

\[
 R_b=2\sum_{r=n}^{L-1}
   \#\{0\le i<L-r:U_i=U_{i+r}\}.                           \tag{3.5}
\]

Equations (3.4)-(3.5) are the conventions of the imported T92 binary
definitions; (3.4) is also T83's decimal `exactShortPairCount`. There are no
frequencies, Fourier weights, arithmetic masks, or boundary-majorant terms in
these exact-word counts.

### Clause-by-clause comparison

| Clause | T56/T61 | T95 exact word |
|---|---|---|
| Base and scale | base 10, `L_n=10^(n/2)` | base `b`, `L=b^(n/2)`; set `b=10` to align |
| Starts | `0<=j<L-r` at lag `r` | `0<=i<L-r` at lag `r` |
| Short lags | `0<r<n`, `r<L` | identical |
| Long lags | `n<=r<L` | identical |
| Orientation | positive-lag half doubled | positive-lag half doubled |
| Diagonal | present as `L` in full `Q_pi` | absent from `S_b,R_b` |
| Relation | strict circle distance plus residual mask | exact factor equality |
| Carry/neighbor cases | included by strict near return | excluded unless factors equal |
| Fourier range | signed `|h|<H_n`; Vaaler uses `1<=h<H_n` plus zero mode | none |
| Weight | Fejer `1-|h|/H_n`; Vaaler signed `a_H(h)` | unit counting weight |
| Endpoint | strict distance `<10^-n`; Vaaler has positive boundary slack | exact equality; lag `n` is long |
| Normalization | C7 is `F<=C H_n L_n`; count form is `Q<=A L_n` | charging has additive `C_b L` |

## 4. Why direct Vaaler transport fails

Exact equality is contained in same-cylinder collision, and the union of the
same, predecessor, and successor cylinder graphs contains every strict circle
near return. That global three-graph fact is different from a pointwise
comparison between exact equality and the Vaaler polynomial.

In particular, (2.6) has the form `incidence <= majorant`. From
`incidence <= exact-word expression` one cannot infer
`majorant <= exact-word expression`. The Vaaler boundary values make this
failure literal: at distance exactly `1/(2H)` the strict indicator is zero but
the majorant is one. No direct majorant implication is claimed below.

The legal route is instead the global machine-checked inequality

\[
 Q_\pi(n,L)\le3E_\pi(n,L),                                 \tag{4.1}
\]

where `E_pi` is the ordered, diagonal-inclusive exact decimal-cylinder
collision count. The factor three is exactly the equality, cyclic predecessor,
and cyclic successor code-graph cover; it is not a hidden asymptotic constant.

## 5. Independent reproduction of the T95 charging estimate

This section does not cite the T95 conclusion. It proves it from the literal
definitions (3.1)-(3.3).

Define

\[
 C_b=\frac{25}{6}\left(4+
       9\frac{b^2(b+1)}{(b-1)^3}\right).                  \tag{5.1}
\]

We prove, for every legal `b,n,L,x`,

\[
 \boxed{2S_b(x,n,L)\le3R_b(x,n,L)+2C_bL}.                 \tag{5.2}
\]

### Step 1: partition by exact factor labels

For each occurring length-`n` factor `u`, let

\[
 A_u=\{i\in\{0,\ldots,L-1\}:U_i=u\},\qquad m_u=|A_u|.
\]

Let `s_u` count unordered pairs in `A_u` at distance strictly between zero and
`n`, and let `r_u` count unordered pairs at distance at least `n`. Every
unordered distinct pair lies in exactly one class, including the boundary lag
`n` in `r_u`. Hence

\[
 s_u+r_u={m_u\choose2},\qquad
 S_b=2\sum_u s_u,\qquad R_b=2\sum_u r_u.                   \tag{5.3}
\]

The nonempty fibers partition the `L` starts, so at most `L` labels occur.

### Step 2: local occupancy bounds short pairs

Let

\[
 q_u=\max_{a\in\mathbb Z}|A_u\cap\{a,a+1,\ldots,a+n-1\}|. \tag{5.4}
\]

The maximum exists because `A_u` is finite and nonempty. Order `A_u`. For an
occurrence at `j`, all earlier occurrences at distance `<n`, together with
`j`, lie in the `n` consecutive positions `j-n+1,...,j`. Thus `j` has at most
`q_u-1` earlier short neighbors. Charging each unordered short pair to its
later endpoint gives

\[
 s_u\le m_u(q_u-1).                                       \tag{5.5}
\]

No overlap or boundary start was discarded.

### Step 3: coefficient-three charging for one label

Work in the reals and set `d_u=2s_u-3r_u`. By (5.3),

\[
 d_u=5s_u-3{m_u\choose2}.
\]

Using (5.5), then dropping only the nonpositive term `-(7/2)m_u`,

\[
\begin{aligned}
 d_u
 &\le5m_u(q_u-1)-\frac32m_u(m_u-1)\\
 &=5m_uq_u-\frac32m_u^2-\frac72m_u\\
 &\le5m_uq_u-\frac32m_u^2\\
 &\le\frac{25}{6}q_u^2.                                  \tag{5.6}
\end{aligned}
\]

The last inequality is exactly

\[
 \frac{25}{6}q_u^2-5m_uq_u+\frac32m_u^2
 =\frac{(5q_u-3m_u)^2}{6}\ge0.                            \tag{5.7}
\]

### Step 4: overlapping copies force a period

Let `p(u)` be the least positive period of `u`; period `n` always exists. If
equal copies start at `i<j<i+n`, then `d=j-i` satisfies
`u_t=u_(t+d)` for every `0<=t<n-d`, so every short occurrence gap is a period
and is at least `p(u)`.

Choose `q_u` occurrences in one interval of `n` consecutive start positions
and order them. Their span is at most `n-1`; each consecutive gap is at least
`p(u)`. Therefore

\[
 (q_u-1)p(u)\le n-1,
 \qquad q_u\le1+\left\lfloor\frac{n-1}{p(u)}\right\rfloor.\tag{5.8}
\]

No Fine-Wilf or other unquoted periodicity theorem is used.

### Step 5: sum squared occupancies

Assume first `n>=2` and put `k=floor(n/2)>=1`, so `L=b^k`. If `p(u)>k`, then
(5.8) gives `q_u<=2` for either parity of `n`. Since at most `L` labels occur,

\[
 \sum_{p(u)>k}q_u^2\le4L.                                 \tag{5.9}
\]

For fixed `1<=p<=k`, a length-`n` word with period `p` is determined by its
first `p` symbols, so at most `b^p` such words exist. Because `n-1<=2k` and
`p<=k`, (5.8) gives

\[
 q_u\le1+\frac{2k}{p}\le\frac{3k}{p}.                    \tag{5.10}
\]

With `d=k-p`,

\[
\begin{aligned}
 \sum_{p(u)\le k}q_u^2
 &\le9\sum_{p=1}^k b^p(k/p)^2\\
 &=9L\sum_{d=0}^{k-1}b^{-d}\left(1+\frac d{k-d}\right)^2\\
 &\le9L\sum_{d=0}^{\infty}\frac{(d+1)^2}{b^d}\\
 &=9L\frac{b^2(b+1)}{(b-1)^3}.                            \tag{5.11}
\end{aligned}
\]

Here `k-d>=1`, so `1+d/(k-d)<=d+1`. The final series identity follows from
twice differentiating the absolutely convergent geometric series, or directly
from

\[
 \sum_{d\ge0}(d+1)^2z^d=\frac{1+z}{(1-z)^3},\quad |z|<1,
\]

with `z=1/b`. Combining (5.9)-(5.11),

\[
 \sum_u q_u^2\le K_bL,
 \qquad K_b=4+9\frac{b^2(b+1)}{(b-1)^3}.                  \tag{5.12}
\]

### Step 6: restore orientations

By (5.3) and the definition of `d_u`,

\[
 2S_b-3R_b=2\sum_u d_u
 \le\frac{25}{3}\sum_u q_u^2
 \le\frac{25}{3}K_bL=2C_bL.
\]

This is (5.2). If `n=1`, then `k=0`, `L=1`, and there is only one start, so
`S_b=R_b=0`; the same result is immediate. Every legal `n` is covered.

## 6. Constant-explicit transport to the T83 Review-B claim

Set `b=10`. Formula (5.1) gives, without rounding,

\[
 C_{10}=\frac{25}{6}\left(4+\frac{1100}{81}\right)
       =\frac{17800}{243}.                                \tag{6.1}
\]

Apply (5.2) to the first `L_n+n-1` digits of the decimal expansion of `pi`.
Write `S_pi^=` and `R_pi^=` for (3.2)-(3.3). The ordered exact collision
count partitions exactly as

\[
 E_\pi(n,L_n)=L_n+S_\pi^=+R_\pi^=.                       \tag{6.2}
\]

From (5.2),

\[
 S_\pi^=\le\frac{17800}{243}L_n+\frac32R_\pi^=,
\]

and hence

\[
 E_\pi(n,L_n)
 \le\frac{18043}{243}L_n+\frac52R_\pi^=.                 \tag{6.3}
\]

The checked global carry/neighbor comparison (4.1) now gives

\[
 \boxed{Q_\pi(n,L_n)
 \le\frac{18043}{81}L_n+\frac{15}{2}R_\pi^=.}             \tag{6.4}
\]

The imported T2 theorem preserves both ordered orientations and, under the
explicit effective-irrationality premise, gives

\[
 R_\pi^=\le T_n^{\rm res}.                                \tag{6.5}
\]

We end with exactly one implication, scoped to the T83 Review-B claim. For
every real `mu,c`, natural `Q0`, real `K>0`, and natural `N>=1`:

\[
\boxed{\begin{gathered}
 \operatorname{EffectiveIrrationality}(\pi,\mu,c,Q0)\ \wedge\\
 \left(\forall n\ge N:\quad T_n^{\rm res}\le K L_n\right)
 \\\Longrightarrow\\
 \forall n\ge N:\quad
 \left\{\begin{aligned}
 Q_\pi(n,L_n)&\le
 \left(\frac{18043}{81}+\frac{15}{2}K\right)L_n,\\
 \mathcal F_\pi(L_n,H_n)&\le
 17\left(\frac{18043}{81}+\frac{15}{2}K\right)H_nL_n.
 \end{aligned}\right.
\end{gathered}}                                             \tag{6.6}
\]

The first conclusion follows from (6.4)-(6.5); the second is T27's checked
count-to-C7 implication with constant multiplier `17`. Thus the reproduced
T95 exact-word theorem can replace T61's signed-majorant premise in this
conditional route, but only by passing through the global three-cylinder
comparison. It does not upper-bound `structuredVaalerMajorantTotal`.

Neither effective irrationality nor the residual-long linear bound is proved
here. Consequently (6.6) is a conditional interface theorem, not a fixed-`pi`
result, not a proof of C7, and not a claim about canonical A1, C1, or C2.

## Replay and verification

From a directory containing only the delivered artifacts, run:

```sh
python3 verify_note.py
sha256sum -c SHA256SUMS
```

The replay checks the canonical hash, exact rational constants, the per-label
square identity on a bounded grid, the period-word count on bounded alphabets,
and exhaustive binary instances through `n=6`. Those finite checks are
**experiments**, not proof of the universal statements. The universal argument
is the numbered proof in Section 5.

To replay the import audit in the pinned Lean workspace, run:

```sh
lake env lean T98StatisticImports.lean
```

The import file adds no declaration and claims no new Lean theorem.

## Independent review

- Statement normalization: prepared in this artifact; not independently
  reviewed.
- Paper proof: not independently reviewed.
- Novelty/attribution: not applicable; no novelty claim is made.
