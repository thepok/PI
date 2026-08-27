# T95: universal Review-B exact-word charging

Claim label: **proof sketch**.  This note gives a complete numbered paper proof,
but the universal combinatorial argument has not been machine-checked or
independently reviewed.  The imported T83 and T92 declarations identified
below are machine-checked.

## 1. Provenance and immutable scope

Canonical source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
Original source URL: none; this is the local system formulation recorded on
2026-07-22.  The byte-exact delivered copy `canonical_statement.txt` has
SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The canonical question concerns the ordered, diagonal-inclusive strict
circle-near-return count for the fixed number `pi`.  T95 does **not** adjudicate
that question.  It adjudicates only Review B's separate exact-word sibling.

## 2. Literal T83/T92 imports and normalization

The delivered `T95StatisticImports.lean` literally imports, without copying or
redeclaring their statistics,

```lean
import TheoryLib.PiLacunaryNearReturnSparsity.T83T83LiteralStatisticAudit
import TheoryLib.PiLacunaryNearReturnSparsity.T92T92ConstantRunDiscriminator
```

The imported source hashes are respectively

```text
013170204762b54fd9e8791f6723f189473ccbf03d4a4ec7b63ad657e44ea424
d912120e6ebc122d82f889f1731be56eb756b312b66244ff22ee451317e7cd12
```

The exact interfaces used to fix the conventions are:

1. T83's `exactShortPairCount` counts equal length-`n` factors on a
   `Stream (Fin 10)` by summing positive lags in
   `Icc 1 (L-1)` filtered by `r<n`, then multiplying by two.
2. T92's `binaryExactShortPairCount` has the same domain and range convention
   on a `Stream (Fin 2)`.
3. T92's `binaryExactLongPairCount` sums positive lags in `Icc n (L-1)`,
   then multiplies by two.  Thus lag `n` is remote.
4. The factor two records both orientations.  No diagonal is present in
   either statistic.  Each lag `r` has exactly `L-r` possible starts before
   the equality filter is applied.

We now state the arbitrary-base sibling with exactly those conventions.  Fix
an integer `b>=2`, an alphabet `Sigma` of exactly `b` symbols, and an integer
`n>=1`.  Set

\[
 k=\lfloor n/2\rfloor,\qquad L=b^k.                       \tag{2.1}
\]

Let `x` be any finite word over `Sigma` of length at least `L+n-1`.  For each
of the **exactly `L` starts** `0<=i<L`, put

\[
 U_i=x[i,i+n).                                             \tag{2.2}
\]

The last allowed block ends at position `L+n-2`, so `L+n-1` is the exact
minimum word length (longer words are also legal).  Define

\[
 S_b(x,n,L)=\#\{(i,j):0\le i,j<L,\ 0<|i-j|<n,\ U_i=U_j\}, \tag{2.3}
\]

\[
 R_b(x,n,L)=\#\{(i,j):0\le i,j<L,\ |i-j|\ge n,\ U_i=U_j\}.\tag{2.4}
\]

Both counts are ordered and off-diagonal.  The short range is strict, overlap
is allowed, and the remote range includes lag `n`.  Equations (2.3)-(2.4)
specialize literally to T92's two definitions when `Sigma=Fin 2` and `x` is
extended to a binary stream; (2.3) likewise specializes to T83's decimal
exact-short definition when `Sigma=Fin 10`.  An alphabet merely equinumerous
with `Fin b` first requires the harmless relabeling bijection.  No claim
identifies these exact equalities with T56's carry-thickened strict near
returns.

## 3. The theorem and explicit constant

For every integer `b>=2`, define the finite positive real constant

\[
 \boxed{C_b={25\over6}\left(4+
       9{b^2(b+1)\over(b-1)^3}\right).}                   \tag{3.1}
\]

The numbered proof sketch derives, for every legal `n,L,x`,

\[
 \boxed{2S_b(x,n,L)\le3R_b(x,n,L)+2C_bL.}                 \tag{3.2}
\]

The constant depends only on the fixed base `b`, not on `n`, `L`, or `x`.
It is deliberately nonoptimal.  T92's constant-stream equality at `b=2`,
`n=7` shows only that any optimal `C_2` is at least `51/8`.

## 4. Numbered proof

### Step 1: exact partition by block labels

For each length-`n` word `u` over `Sigma`, let

\[
 A_u=\{i\in\{0,\ldots,L-1\}:U_i=u\},\qquad m_u=|A_u|.    \tag{4.1}
\]

Only nonempty `A_u` will be used.  They partition the `L` starts, so there are
at most `L` occurring labels.  Let `s_u` be the number of **unordered** pairs
from `A_u` at distance strictly between `0` and `n`, and let `r_u` be the
number at distance at least `n`.  Every unordered pair of distinct starts
falls into exactly one of these classes; in particular lag `n` is in `r_u`.
Therefore

\[
 s_u+r_u={m_u\choose2},                                   \tag{4.2}
\]

and restoring both orientations gives the exact identities

\[
 S_b=2\sum_u s_u,\qquad R_b=2\sum_u r_u.                  \tag{4.3}
\]

### Step 2: local occupancy controls short pairs

Define the maximum local occupancy of label `u` by

\[
q_u=\max_{a\in\mathbb Z}|A_u\cap\{a,a+1,\ldots,a+n-1\}|.\tag{4.4}
\]

This maximum is attained because the nonempty set `A_u` is finite; only
finitely many translated windows meet it.

Order `A_u` increasingly.  For each occurrence `j`, all earlier occurrences
at distance `<n`, together with `j`, lie in the `n` consecutive start
positions `j-n+1,...,j`.  Hence `j` has at most `q_u-1` earlier short
neighbors.  Summing once over the later endpoint of every unordered short
pair gives

\[
 s_u\le m_u(q_u-1).                                       \tag{4.5}
\]

This argument does not discard overlaps or boundary starts.

### Step 3: exact coefficient-three charging for one label

Embed the integer counts in the reals and put `d_u=2s_u-3r_u` (so subtraction
is not natural-number truncation).  From (4.2),

\[
 d_u=5s_u-3{m_u\choose2}.                                 \tag{4.6}
\]

Using (4.5), `m_u>=0`, and then completing a square,

\[
\begin{aligned}
 d_u
 &\le5m_u(q_u-1)-{3\over2}m_u(m_u-1)\\
 &=5m_uq_u-{3\over2}m_u^2-{7\over2}m_u\\
 &\le5m_uq_u-{3\over2}m_u^2\\
 &\le {25\over6}q_u^2,
\end{aligned}                                             \tag{4.7}
\]

because

\[
 {25\over6}q_u^2-5m_uq_u+{3\over2}m_u^2
 ={(5q_u-3m_u)^2\over6}\ge0.                             \tag{4.8}
\]

Remote repetitions are therefore not ignored: increasing total multiplicity
raises the negative quadratic term in (4.6).

### Step 4: overlap forces a period

For a length-`n` word `u`, call `p` a period when `1<=p<=n` and

\[
 u_t=u_{t+p}\quad(0\le t<n-p).                            \tag{4.9}
\]

The vacuous period `n` always exists; let `p(u)` be the least positive period.
If equal copies of `u` start at `i<j<i+n`, then, with `d=j-i`, equality of
the two complete factors gives

\[
 u_t=x_{i+t}=x_{j+t}=u_{t+d}\quad(0\le t<n-d).            \tag{4.10}
\]

Thus every short gap between two occurrences is a period of `u` and is at
least `p(u)`.

Choose `q_u` occurrences in an interval of `n` consecutive starts and order
them `i_1<...<i_{q_u}`.  Their span is at most `n-1`.  Every consecutive gap
is short and at least `p(u)`, so

\[
 (q_u-1)p(u)\le i_{q_u}-i_1\le n-1.                       \tag{4.11}
\]

Consequently

\[
 q_u\le1+\left\lfloor{n-1\over p(u)}\right\rfloor.       \tag{4.12}
\]

This is the only word-periodicity input; no Fine-Wilf theorem is assumed.

### Step 5: sum the squared occupancies

Assume first `n>=2`, so `k=floor(n/2)>=1`.  Split occurring labels according
to whether `p(u)>k` or `p(u)<=k`.

If `p(u)>k`, then (4.12) gives `q_u<=2` for both parities of `n`.  Since at
most `L` labels occur,

\[
 \sum_{p(u)>k}q_u^2\le4L.                                 \tag{4.13}
\]

For a fixed `1<=p<=k`, a length-`n` word having period `p` is determined by
its first `p` symbols, so at most `b^p` words have least period `p`.  Also
`n-1<=2k`; hence (4.12) and `p<=k` give

\[
 q_u\le1+{2k\over p}\le{3k\over p}.                      \tag{4.14}
\]

It follows, with `d=k-p` and `L=b^k`, that

\[
\begin{aligned}
 \sum_{p(u)\le k}q_u^2
 &\le9\sum_{p=1}^k b^p\left({k\over p}\right)^2\\
 &=9L\sum_{d=0}^{k-1}b^{-d}
       \left(1+{d\over k-d}\right)^2\\
 &\le9L\sum_{d=0}^{\infty}{(d+1)^2\over b^d}\\
 &=9L\,{b^2(b+1)\over(b-1)^3}.                           \tag{4.15}
\end{aligned}
\]

The inequality uses `1+d/(k-d)<=d+1`, since `k-d=p>=1`.  For completeness,
the last series identity follows for `|z|<1` by differentiating the absolutely
convergent geometric series twice:

\[
 \sum_{d\ge0}(d+1)^2z^d={1+z\over(1-z)^3},                \tag{4.16}
\]

then substituting `z=1/b`.

Combining (4.13) and (4.15),

\[
 \sum_u q_u^2\le K_bL,
 \qquad K_b=4+9{b^2(b+1)\over(b-1)^3}.                   \tag{4.17}
\]

### Step 6: restore ordered pairs and finish

Equations (4.3) and the definition of `d_u` give

\[
 2S_b-3R_b=2\sum_u d_u.                                   \tag{4.18}
\]

Using (4.7), (4.17), and `C_b=(25/6)K_b`,

\[
 2S_b-3R_b
 \le {25\over3}\sum_u q_u^2
 \le {25\over3}K_bL
 =2C_bL.                                                   \tag{4.19}
\]

This is (3.2).  If `n=1`, then `k=0`, `L=1`, and there is only one start, so
`S_b=R_b=0`; (3.2) is immediate.  Thus every legal `n` is covered.

## 5. Adjudication and scope

The proof sketch supports the universal alternative with the explicit finite
constant (3.1).  In particular, its bound in every fixed base is

\[
 {2S_b-3R_b\over L}\le2C_b,                               \tag{5.1}
\]

so no legal infinite counterfamily can have unbounded normalized excess.
Finite exhaustive checks in `verify_note.py` are sanity checks only and are
not used in the proof.

This adjudicates **only Review B's exact-word sibling**.  It implies nothing
about T56/C7, the canonical fixed-`pi` question, `pi`, C1, or C2.  In
particular, exact block equality is not substituted for T56's neighboring-
cylinder or carry-thickened strict near-return relation.
