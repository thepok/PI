# T7: uniform quantitative word cover for an iid decimal stream

Claim label: `proof sketch` (a complete proof note submitted for independent
skeptic review; not machine-checked).

This is an **iid sibling theorem**. It proves nothing about the decimal digits
of pi and does not prove canonical conjecture C1. Any such conclusion would
require a separate, verified transfer theorem relating pi's digits to the iid
probability space below. No such transfer theorem is assumed or supplied.

## Provenance

- Agenda item: T7, serving G7.
- Canonical local statement: `knowledge/pi/statements/pi-quantitative-block-hitting.txt`.
- Canonical statement SHA-256:
  `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`.
- Original source URL: none; the canonical file says that this local question
  was formulated by the system on 2026-07-22.
- Relation to the canonical statement: the quantifiers and full-containment
  deadline are retained, but the deterministic pi digit stream is replaced by
  an iid uniform random decimal stream. This replacement is a sibling variant,
  not a reduction of C1.

## Normalized statement and quantifiers

Let `D = {0,1,...,9}`. On the product probability space defined below, there
are explicit constants

```text
C_rand = 18,                 eta = 8/9
```

such that

\[
 \mathbb P\left(
   \forall k\in\mathbb Z_{\ge 1}\ \forall w=(w_0,\ldots,w_{k-1})\in D^k\
   \exists i\in\mathbb Z_{\ge 1}:\
   i+k-1\le 18k10^k\ \text{ and }\
   X_{i+j}=w_j\ (0\le j<k)
 \right)\ge \frac89.                                      \tag{T7}
\]

Thus one deterministic constant works simultaneously for every positive `k`
and every word. A word is a member of `D^k`, not a `k`-digit integer, so words
such as `(0,...,0)` and all other leading-zero words are included.

## Ambiguities fixed before the proof

- The coordinates are one-based: `X_1` is the first random fractional digit.
- The prefix deadline is an endpoint bound. The witness satisfies
  `i+k-1 <= 18*k*10^k`, so the entire occurrence, not just its start, lies in
  the indicated prefix.
- Starts are arbitrary integer positions and the tested windows inside a chunk
  overlap. The proof does not assume that overlapping windows are independent.
- Different words and their occurrence events need not be independent.
- The assertion is one event with `forall k >= 1`, not a separate
  positive-probability assertion for each `k`.
- The assigned chunks restrict which witnesses the proof searches for, but the
  theorem's conclusion merely asserts an ordinary contiguous occurrence.
- This is a positive-probability iid statement. It is neither a finite-`k`
  computation nor a statement about pi, normal numbers, or every stream.

## Probability space

Give `D` the discrete sigma-algebra and the uniform probability measure `u`,
where `u({a})=1/10` for every `a in D`. Set

\[
 (\Omega,\mathcal F,\mathbb P)
   =\prod_{n=1}^{\infty}(D,2^D,u),
 \qquad X_n(\omega)=\omega_n.
\]

The coordinate variables are jointly independent and uniform. Equivalently,
for every finite set `I` of coordinate indices and prescribed digits
`(a_n)_(n in I)`,

\[
 \mathbb P(X_n=a_n\text{ for every }n\in I)=10^{-|I|}.      \tag{1}
\]

All events below are finite unions and intersections of cylinder events,
followed at the end by one countable intersection over `k`; hence they are
measurable.

## Slabs and full-containment indexing

For `k >= 1`, put

\[
 m_k=10^k,\qquad \ell_k=m_k+k-1,
\]

and define cumulative endpoints

\[
 S_0=0,\qquad
 S_k=\sum_{j=1}^k 8j\ell_j.
\]

The level-`k` slab is the digit interval

\[
 B_k=\{S_{k-1}+1,\ldots,S_k\}.
\]

It is partitioned into `8k` consecutive chunks. For
`r in {0,...,8k-1}`, let

\[
 a_{k,r}=S_{k-1}+r\ell_k+1,
 \qquad
 B_{k,r}=\{a_{k,r},\ldots,a_{k,r}+\ell_k-1\}.
\]

Inside chunk `B_(k,r)`, test exactly the `m_k=10^k` starts

\[
 a_{k,r}+t,\qquad 0\le t<m_k.                              \tag{2}
\]

The last digit of the window at start `a_(k,r)+t` is
`a_(k,r)+t+k-1`. For the largest tested start, `t=m_k-1`, this
is

\[
 a_{k,r}+(m_k-1)+(k-1)=a_{k,r}+\ell_k-1,
\]

the final digit of the chunk. Thus every tested occurrence is fully contained
in its chunk. Starts crossing chunk boundaries are simply not used.

The chunks are pairwise disjoint, including chunks belonging to different
slabs. Consequently their coordinate sigma-algebras are mutually independent
by the product construction. Independence of the `8k` chunks within one slab
will be used below. The final union bound does not require independence between
different `k`-slabs, although that independence is also available.

The cumulative endpoint has the required deterministic bound. For `j >= 1`,
`j-1 <= 10^j`, so

\[
\begin{aligned}
 S_k
 &=8\sum_{j=1}^k j(10^j+j-1)\\
 &\le 16\sum_{j=1}^k j10^j\\
 &\le 16k\sum_{j=1}^k10^j\\
 &=\frac{160k(10^k-1)}9\\
 &<\frac{160}{9}k10^k
 <18k10^k.                                                   \tag{3}
\end{aligned}
\]

In particular, every occurrence found in one of the slabs `B_1,...,B_k`
ends no later than `S_k <= 18*k*10^k`.

## Fixed-word overlapping-pair calculation

Fix `k >= 1`, a word `w=(w_0,...,w_(k-1)) in D^k`, and one level-`k`
chunk beginning at coordinate `a`. For `0 <= t < m_k`, let

\[
 I_t=\mathbf 1\{X_{a+t+j}=w_j\text{ for every }0\le j<k\},
 \qquad Z=\sum_{t=0}^{m_k-1}I_t.
\]

By (1),

\[
 p:=\mathbb E I_t=10^{-k}=m_k^{-1},
 \qquad \mathbb E Z=m_kp=1.                                \tag{4}
\]

We now calculate every pair according to its shift rather than pretending the
overlapping indicators are independent. Let `0 <= t < s < m_k` and put
`d=s-t`.

If `d >= k`, the two windows use disjoint coordinate sets, so

\[
 \mathbb E(I_tI_s)=10^{-2k}=p^2.                            \tag{5}
\]

Suppose instead that `1 <= d < k`. Both occurrences are possible exactly when
the suffix and prefix forced on their overlap agree, namely

\[
 w_{d+j}=w_j\quad\text{for every }0\le j<k-d.               \tag{6}
\]

This is the border condition saying that the length-`k-d` prefix of `w`
equals its length-`k-d` suffix. Let `b_d(w)` be `1` when (6) holds and `0`
otherwise. If the condition fails, the joint event is empty. If it holds, the
union of the windows contains `k+d` distinct coordinates whose digits are all
prescribed consistently. Therefore (1) gives the exact formula

\[
 \mathbb E(I_tI_s)=b_d(w)10^{-(k+d)}\qquad(1\le d<k).       \tag{7}
\]

There are `m_k-d` ordered pairs with `t<s` and shift `d`. Equations (5)-(7)
therefore expose the complete covariance calculation:

\[
\begin{aligned}
 \operatorname{Var}(Z)
 &=m_kp(1-p)
   +2\sum_{d=1}^{k-1}(m_k-d)
       \left(b_d(w)10^{-(k+d)}-p^2\right).                 \tag{8}
\end{aligned}
\]

The shifts `d >= k` contribute zero covariance and hence do not appear in
(8). Uniformly over every border pattern, use `b_d(w) <= 1`, discard the
possibly negative terms, and use `m_k10^{-k}=1`:

\[
\begin{aligned}
 \operatorname{Var}(Z)
 &\le 1+2\sum_{d=1}^{k-1}m_k10^{-(k+d)}\\
 &=1+2\sum_{d=1}^{k-1}10^{-d}
 \le 1+\frac29=\frac{11}{9}.                               \tag{9}
\end{aligned}
\]

For `k=1` the sum is empty, so the same bound holds. Combining (4) and (9),

\[
 \mathbb E Z^2=\operatorname{Var}(Z)+(\mathbb E Z)^2
 \le \frac{20}{9}.                                        \tag{10}
\]

Finally, Cauchy-Schwarz applied to
`Z=Z*1_{Z>0}` gives

\[
 1=(\mathbb E Z)^2
 \le \mathbb E(Z^2)\,\mathbb P(Z>0),
\]

and hence the word-uniform one-chunk estimates

\[
 \mathbb P(Z>0)\ge\frac9{20},
 \qquad
 \mathbb P(Z=0)\le\frac{11}{20}.                           \tag{11}
\]

Highly bordered words therefore do not defeat the estimate; (7)-(9) already
use the worst possible border indicator at every overlapping shift.

## One slab, all words, and all lengths

For fixed `k` and `w`, absence of `w` from all tested starts in the level-`k`
slab is the intersection of `8k` events, one per chunk. These events depend on
disjoint coordinate sets, so chunk independence and (11) give

\[
 \mathbb P(w\text{ is missed by its level-}k\text{ slab})
 \le \left(\frac{11}{20}\right)^{8k}.                      \tag{12}
\]

There are exactly `|D^k|=10^k` words, including all leading-zero words. A
union bound over them shows that the level-`k` failure event `F_k` satisfies

\[
 \mathbb P(F_k)
 \le 10^k\left(\frac{11}{20}\right)^{8k}
 =\left[10\left(\frac{11}{20}\right)^8\right]^k.          \tag{13}
\]

The numerical estimate is exact and needs no simulation:

\[
 \left(\frac{11}{20}\right)^4
 =\frac{14641}{160000}<\frac1{10},
\]

so `(11/20)^8 < 1/100` and consequently

\[
 \mathbb P(F_k)\le 10^{-k}.                                \tag{14}
\]

Let

\[
 G=\bigcap_{k=1}^{\infty}F_k^c.
\]

This is the single event on which every level succeeds simultaneously. The
countable union bound, which does not assume cross-level independence, gives

\[
 \mathbb P(G^c)
 =\mathbb P\left(\bigcup_{k=1}^{\infty}F_k\right)
 \le\sum_{k=1}^{\infty}\mathbb P(F_k)
 \le\sum_{k=1}^{\infty}10^{-k}=\frac19.                    \tag{15}
\]

Therefore `P(G) >= 8/9`. On `G`, for every `k >= 1` and every `w in D^k`,
the word occurs at a tested start in `B_k`; its endpoint is at most `S_k`,
which is at most `18*k*10^k` by (3). This proves (T7) with the explicit integer
`C_rand=18 >= 1` and explicit `eta=8/9 > 0`.

## Acceptance audit surface

| Required point | Direct location in this note |
|---|---|
| Probability space | Product space and finite-cylinder formula (1) |
| Explicit constants | `C_rand=18`, `eta=8/9` in (T7) |
| Overlap-pair calculation | Border condition (6), exact joint law (7), variance identity (8) |
| Fixed-word second moment | Equations (4), (9), (10), and (11) |
| Slab and chunk independence | Disjoint definitions (2) and paragraph following them; used in (12) |
| Union over words and lengths | Equations (13)-(15) |
| Simultaneous all-`k` quantifier | The event `G=intersection_(k>=1) F_k^c` |
| Leading-zero coverage | Words are all of `D^k`; reiterated before (13) |
| Full-containment indexing | Endpoint calculation after (2), cumulative bound (3) |
| No simulation as proof | Every bound is symbolic; the only numerical check is an exact rational inequality |
| Separation from pi and C1 | Warning at the beginning and scope statement below |

## Scope, reuse, and non-claims

The reusable content is the exact border-sensitive pair formula (7), the
uniform second-moment estimate (9)-(11), and the independent-slab allocation.
No finite simulation appears. No novelty claim is made for these elementary
probabilistic ingredients. Most importantly, the iid measure assigns
probabilities to random streams, while pi supplies one fixed stream with no
proved connection to this measure. Positive iid probability neither identifies
pi as a successful stream nor supplies a transfer principle. Thus this sibling
theorem leaves C1 open.

## Literature and formalization log

- The accumulated T4 source audit was inspected before this proof. Its warning
  that overlapping windows cannot be treated as independent is addressed
  directly by (5)-(8). The present proof does not rely on the paper criticized
  there or on any external quantitative word-cover theorem.
- Accepted T1 fixes the canonical one-based endpoint condition
  `i+k-1 <= N` and its zero-based Lean translation `n+k <= N`. This note stays
  one-based throughout.
- No Lean theorem is claimed by this artifact. The argument is presented for
  direct mathematical skeptic review.
