# T145: coefficient classification of factorial-ratio carry cycles

Status: `proof sketch`. The universal classification is proved in Sections
2--6. The independent finite replay is an `experiment`; it checks formulas and
small instances but is not evidence for the universal theorem. This is an
A13/A14 related-model note. It makes no fixed-pi, canonical A1, C1, or C2
claim, and no literature-novelty claim.

```text
UNIVERSAL_CLASSIFICATION_COUNT: 1
COMPARATOR_COUNT: 3
SCOPED_VERDICT_COUNT: 1
```

## 1. Provenance, canonical scope, and normalized theorem

The immutable local source is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`; no external source URL
was supplied for this system-formulated question. Its byte-exact delivered
copy is `canonical_statement.txt`, with SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
The canonical question fixes pi, base 10, strict circle distance, ordered pairs
including the diagonal, and the quantifiers

```text
for every A >= 1 there exists n0 >= 1 such that
for every n >= n0 there exists N >= 1 with A*n*Q_pi(n,N) <= N^2.
```

Nothing in this note supplies these quantifiers. The theorem here concerns a
different, coefficient-level arithmetic model.

Fix two nonempty finite lists of positive integers

\[
  a=(a_1,\ldots,a_r),\qquad b=(b_1,\ldots,b_s),             \tag{1.1}
\]

with repetitions retained and

\[
  \sum_i a_i=\sum_j b_j.                                   \tag{1.2}
\]

Assume the balanced factorial ratio

\[
  R(n)={\prod_i(a_i n)!\over\prod_j(b_j n)!}                \tag{1.3}
\]

is an integer for every integer `n>=0`. For every prime `p`, Section 3
constructs a finite weighted base-`p` carry graph directly from the two lists.
The theorem proved below is

\[
 \boxed{\mu_-(p;a,b)=0,\qquad
 \mu_+(p;a,b)=0\ \Longleftrightarrow\
 \{a_i\}_i=\{b_j\}_j\text{ as multisets}.}                 \tag{1.4}
\]

The exact conventions are:

1. Input digits are read least-significant first.
2. A length-`t` word represents exactly one `0<=n<p^t`; high zero padding is
   allowed and terminal carry digits are charged after the word.
3. The full Cartesian carry space is defined, but a state or cycle is called
   accessible only if it is reachable from the all-zero initial state.
4. Distinct digits giving the same endpoints remain parallel labeled edges.
5. A cycle is a nonempty directed closed walk. Its weight excludes terminal
   weights, and its mean is edge-weight divided by positive length. Extremal
   means may equivalently be taken over accessible simple directed cycles.
6. Edge weights below measure `(p-1)*v_p(R(n))`. Dividing every weight and mean
   by `p-1` gives valuation units and does not change any zero classification.
7. Integrality means integrality for every `n>=0`, not merely tested values.

## 2. Landau step function derived from integrality

Define the one-periodic integer-valued step function

\[
  \Lambda(x)=\sum_i\lfloor a_i x\rfloor
             -\sum_j\lfloor b_j x\rfloor.                  \tag{2.1}
\]

Periodicity follows from (1.2). We require only the direction of Landau's
criterion that is proved next; no literature theorem is imported.

**Lemma 2.1 (integrality forces nonnegativity).** For every real `x`,
`Lambda(x)>=0`.

**Proof.** Counting multiples of powers of a prime `q` in a factorial gives

\[
 v_q(m!)=\sum_{h\ge1}\left\lfloor{m\over q^h}\right\rfloor.
                                                                    \tag{2.2}
\]

Consequently

\[
 v_q(R(n))=\sum_{h\ge1}\Lambda(n/q^h),                    \tag{2.3}
\]

where the sum is finite. Suppose `Lambda(x_0)<0`. By periodicity take
`0<=x_0<1`. A floor step function is right-continuous and has only finitely
many jumps on `[0,1]`, so `Lambda` is negative throughout some nonempty
right-hand interval `I` in `[0,1)`. Choose a sufficiently large prime
`q>max_i a_i,max_j b_j` and an integer `0<=n<q` with `n/q in I`; arbitrarily
large primes and the mesh `1/q` make this possible. For `h>=2`,

\[
 0\le n/q^h<1/q<1/\max(\{a_i\}\cup\{b_j\}),                \tag{2.4}
\]

so every floor in `Lambda(n/q^h)` is zero. Equation (2.3) then says
`v_q(R(n))=Lambda(n/q)<0`, contradicting that the positive rational `R(n)` is
an integer. This proves the lemma. `square`

This argument also covers a negative value at a discontinuity: the value of a
floor function is its post-jump value, hence persists immediately to the
right.

## 3. Independently reconstructed carry graph and weights

For a positive coefficient `c`, let

\[
  K_c=\{0,1,\ldots,c-1\}.                                  \tag{3.1}
\]

The complete state space is

\[
 K=\prod_{i=1}^r K_{a_i}\times\prod_{j=1}^s K_{b_j}.       \tag{3.2}
\]

Write a state as
`q=(alpha_1,...,alpha_r; beta_1,...,beta_s)`, and let `q_0` be
the all-zero state. For every digit `d in {0,...,p-1}`, define one labeled
edge `q --d/w--> q'` by

\[
 \alpha'_i=\left\lfloor{a_i d+\alpha_i\over p}\right\rfloor,
 \qquad
 \beta'_j=\left\lfloor{b_j d+\beta_j\over p}\right\rfloor. \tag{3.3}
\]

These values remain in (3.1): if `0<=kappa<c`, then
`0<=(cd+kappa)/p<c`. The emitted base-`p` output digit of `c n` is

\[
 e_c(q,d)=cd+\kappa_c-p\kappa'_c.                           \tag{3.4}
\]

Define the integer edge and terminal weights

\[
 w(q,d)=\sum_j e_{b_j}(q,d)-\sum_i e_{a_i}(q,d),            \tag{3.5}
\]

\[
 \tau(q)=\sum_j s_p(\beta_j)-\sum_i s_p(\alpha_i),         \tag{3.6}
\]

where `s_p` is base-`p` digit sum. Equations (3.2)--(3.6) specify every state,
all `p` labeled edges from every state, every weight, and all terminal terms;
no table or quotient from another item is used.

Let a length-`t` word have LSDF digits `d_0,...,d_(t-1)` and value
`k=sum_(u<t)d_u p^u`. Induction in (3.3) gives the exact state after `t`
digits:

\[
 \boxed{\alpha_i=\lfloor a_i k/p^t\rfloor,\qquad
        \beta_j=\lfloor b_j k/p^t\rfloor.}                 \tag{3.7}
\]

Indeed multiplication by `c` after `t` digits has processed `c k` modulo
`p^t`, leaving exactly `floor(c k/p^t)` as carry. Thus the accessible set is
precisely the set of vectors in (3.7) as `t>=0` and `0<=k<p^t` vary.

After `t` steps, (3.4) has emitted the low `t` digits of each product; its
unflushed high part is the final carry in (3.7). Summing the emitted digits and
then (3.6) therefore gives

\[
 \sum_{u=0}^{t-1}w(q_u,d_u)+\tau(q_t)
 =\sum_j s_p(b_jk)-\sum_i s_p(a_i k).                       \tag{3.8}
\]

The digit-sum form of (2.2),
`(p-1)v_p(m!)=m-s_p(m)`, and balance (1.2) now yield

\[
 \boxed{\sum_{u<t}w(q_u,d_u)+\tau(q_t)
       =(p-1)v_p(R(k)).}                                   \tag{3.9}
\]

This proves exactness for every finite word, including `t=0` and high-zero
padding.

## 4. Accessible potentials and the cycle identity

Define a state potential

\[
 \Phi(q)=\sum_i\alpha_i-\sum_j\beta_j.                     \tag{4.1}
\]

For an accessible state (3.7),

\[
 \boxed{\Phi(q)=\Lambda(k/p^t)\ge0}                        \tag{4.2}
\]

by Lemma 2.1. Expanding (3.5), and using balance to cancel all terms linear in
the input digit, gives the load-bearing edge identity

\[
 \boxed{w(q,d)=p\Phi(q')-\Phi(q).}                          \tag{4.3}
\]

For any accessible closed walk
`C=(q_0 --d_0--> q_1 --> ... --> q_l=q_0)` of positive length,
cyclic reindexing in (4.3) gives

\[
 \boxed{W(C)=(p-1)\sum_{u=0}^{l-1}\Phi(q_u)\ge0.}          \tag{4.4}
\]

Terminal weights do not occur in (4.4), exactly as stipulated in Section 1.
Every closed walk decomposes by successively cutting at repeated vertices into
simple directed cycles, and its mean is the length-weighted average of their
means. The finite graph therefore has attained minimum and maximum means over
simple cycles, equal to the extrema over all nonempty closed walks.

At the initial zero state, digit zero is a self-loop: (3.3) returns zero and
(4.3) gives weight zero. Equation (4.4) rules out every negative accessible
cycle. Hence

\[
 \boxed{\mu_-=0.}                                          \tag{4.5}
\]

Notice that individual edges can be negative. The assertion concerns complete
cycles, not edges or terminal-corrected finite paths.

## 5. Coefficient multiset detection

For each positive integer `c`, let

\[
 m_c=\#\{i:a_i=c\}-\#\{j:b_j=c\}.                          \tag{5.1}
\]

Then `Lambda(x)=sum_c m_c floor(c x)`.

**Lemma 5.1.** `Lambda` is identically zero if and only if the numerator and
denominator coefficient multisets agree.

**Proof.** Multiset equality plainly gives `Lambda=0`. Conversely, suppose
some `m_c` is nonzero and let `M` be the largest such coefficient. At
`x=1/M`, the jump of `floor(c x)` is zero for every `c<M`, while the jump of
`floor(Mx)` is one. No `c>M` has nonzero signed multiplicity by the choice of
`M`. Thus the jump of `Lambda` is `m_M!=0`, contradicting an identically zero
function. `square`

Assume now that the multisets differ. Lemmas 2.1 and 5.1 imply that
`Lambda(x)>0` somewhere. Right-continuity and finite discontinuity count give
a nonempty interval on which it is positive. For every fixed prime `p`, choose
`t` large enough that the grid `{k/p^t:0<=k<p^t}` meets that interval. By
(3.7), its grid point reaches a state `q` with

\[
 \Phi(q)=\Lambda(k/p^t)>0.                                 \tag{5.2}
\]

There is also a path from `q` back to the initial state using only zero digits:
for coefficient `c`, (3.3) becomes `kappa'=floor(kappa/p)`, so finitely many
zero steps flush every carry. Concatenate the access path to `q` with this
zero-flush path. It is an accessible closed walk containing `q`, and (4.4)
makes its total weight strictly positive. At least one simple cycle in its
decomposition has positive weight and positive mean. Therefore

\[
 \{a_i\}\ne\{b_j\}\quad\Longrightarrow\quad\mu_+>0.       \tag{5.3}
\]

If the multisets agree, `Lambda=0`, so every accessible `Phi` vanishes by
(4.2), every accessible edge has weight zero by (4.3), and `mu_+=0`. Together
with (5.3), this proves the second assertion of (1.4).

The proof identifies no additional arithmetic invariant: balance gives the
edge potential identity, all-`n` integrality gives nonnegative accessible
potentials, and coefficient multiset disagreement gives a positive accessible
potential.

## 6. Fully displayed convention check

Take

\[
 R(n)={(2n)!\over(n!)^2},\qquad p=2.                        \tag{6.1}
\]

This is integral because it is the central binomial coefficient. Denominator
multiplier-one carries are always zero, so write only the multiplier-two carry.
The complete accessible graph is

| state `alpha` | `Phi` | digit 0 | digit 1 | terminal `tau` |
|---:|---:|---|---|---:|
| 0 | 0 | `0 / 0` | `1 / 2` | 0 |
| 1 | 1 | `0 / -1` | `1 / 1` | -1 |

An edge entry is `next state / weight`. For example, the one-digit word `1`
has total `2+(-1)=1=(2-1)v_2(2!)`. The accessible simple cycle means are

\[
 0\quad(0\text{-loop}),\qquad
 1\quad(1\text{-loop}),\qquad
 {2-1\over2}={1\over2}\quad(0\to1\to0).                   \tag{6.2}
\]

Thus a negative edge coexists with minimum cycle mean zero, while coefficient
disagreement gives positive maximum mean exactly as (1.4) states.

## 7. Independent finite replay (`experiment`)

From a directory containing only the delivered files, run

```bash
python3 verify_t145.py
sha256sum -c SHA256SUMS
```

The script hash-checks the canonical and comparison inputs, reconstructs states,
edges, potentials, terminal weights, and reachable-state formulas, checks
Legendre valuations against path totals, checks all simple cycle means in
(6.2), and exhaustively sweeps small balanced coefficient partitions and four
primes. Its finite sweep is an `experiment`, not proof of (1.4). The proofs in
Sections 2--5 establish the universal statement.

## 8. Explicit T133, T141, and T143 comparison

The three complete comparator reports are delivered byte-for-byte so a skeptic
need not trust availability claims. Their statuses and mathematical claims are
not imported as premises.

| Item and exact delivered SHA-256 | Self-labeled level and mechanism | T145 boundary |
|---|---|---|
| T133, `53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40` | `prior-T133-REPORT.md` self-labels a `proof sketch`; it builds a specialized centered base-5 transducer for `U_n=(6n)!n!/(12^n(3n)!(2n)!)`, collapses six carry triples to three residual classes, and computes exact finite-block extrema. | T133 is unbalanced at the factorial-coefficient level and includes centering plus `12^n`. T145 uses none of its table or extrema; it derives the raw graph for every balanced integral coefficient pair and classifies all accessible cycle signs from the coefficient Landau potential. |
| T141, `e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356` | `prior-T141-REPORT.md` self-labels an unverified `proof sketch`; it argues for a general factorial-ratio carry graph, tropical extrema, accessible-cycle asymptotics, and one central-trinomial application. | T141 is motivation only. T145 independently reconstructs the graph, then adds the all-prime coefficient classification absent from T141: integrality forces every accessible Landau potential nonnegative, and multiset disagreement creates a positive cycle. No T141 assertion discharges a T145 step. |
| T143, `e20df633705a85a7e77c867fbe73535bb2e5cd1851178f4739d0fd8e5b6a1e1f` | `active-T143-REPORT.md` self-labels an unverified `proof sketch`; it starts with one fixed terminal-weighted transducer, minimizes it by terminal-normalized residual equivalence, forms a quotient, and argues that powers lift quotient cycles while preserving means. It was active when T145 was specified; the refreshed record made this report recoverable. | T145 neither minimizes nor quotients a supplied transducer. It retains the raw coefficient carry coordinates and uniformly decides the signs and zero cases of extremal accessible means. T143's fixed-machine equivalence algorithm and cycle-lifting argument are not used. |

The overlap is limited to elementary multiplication-carry notation and the
definition of cycle mean. T145's new proof object is the coefficient-derived
potential `Phi=Lambda(k/p^t)` and the identity (4.4), not a compressed machine.

## 9. Separately stated unproved pi-transfer hypothesis

**PI-DECIMAL-FACT-T145 (`conjecture`; entirely unproved).** There exists a
pi-specific, decimal-compatible sequence of rational approximants `X_m=P_m/Q_m`
in lowest terms, built by an exact identity from balanced integral factorial
ratios of the form (1.3), with all of the following data proved simultaneously:

1. **Reduced numerator and modulus survival:** complete reduction identifies
   `P_m` and `Q_m`, proves which carry-derived prime factors survive every sum
   and cancellation, and controls the residue of `P_m` modulo the surviving
   coprime part of `Q_m`.
2. **Decimal transient and multiplicative order:** writing
   `Q_m=2^u5^v q_m` with `gcd(q_m,10)=1`, the consumed transient
   `max(u,v)` and a lower bound for `ord_(q_m)(10)` hold at the required orbit
   length. Prime valuations or cycle means alone prove neither fact.
3. **Truncation:** an exact identity `pi=X_m+epsilon_m` has an error small
   enough after multiplication by every `10^i-10^j` in the selected prefix to
   preserve the strict decimal near-return comparison.
4. **Occupancy:** for that same reduced numerator, modulus, order, truncation,
   and prefix, the ordered, diagonal-inclusive rational orbit has the metric
   occupancy bound required by the T7 finite-cylinder interface; order alone
   is insufficient.
5. **T107 data, if that route is used:** the same representation additionally
   yields T107's separate decimal boundary loads and collected Fourier budgets
   on the required coherent triangular family of levels.

This hypothesis explicitly requires every reduction, modulus, order,
truncation, and occupancy datum to survive the carry model. No representation
or estimate in this note supplies any clause. The classification (1.4) concerns
prime valuations only and gives no fixed-pi result and no program-conjecture
result.

## 10. Claim boundary

The outcome is a rigorous prose proof at repository label `proof sketch`, not
a machine-checked theorem and not a literature or novelty determination. The
finite replay is only an `experiment`. The result classifies an A13/A14 sibling
model uniformly for every prime and every balanced integral coefficient pair;
it establishes nothing for fixed pi, canonical A1, C1, or C2.

SCOPED_VERDICT: DEVELOP
