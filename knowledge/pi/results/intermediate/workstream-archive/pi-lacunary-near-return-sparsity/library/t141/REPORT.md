# T141: factorial-ratio valuation extrema from multiplication carries

Status: `proof sketch`. Every universal assertion below is proved in the note.
`verify_t141.py` is an independent exact-arithmetic `experiment`; its finite
checks validate, but do not prove, the universal assertions. This is an A13/A14
related-model note. It makes no fixed-pi, canonical A1, C1, or C2 claim.
The T133 note is unverified motivation and changed comparison evidence only;
none of its mathematical claims is used as a premise.

## 1. Canonical scope and normalized statement

The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
The canonical question concerns the fixed number pi, base 10, strict metric
near returns, ordered pairs including the diagonal, and the quantifiers

```text
for every A >= 1, there exists n0 >= 1 such that
for every n >= n0, there exists N >= 1 with A*n*Q_pi(n,N) <= N^2.
```

Nothing proved here supplies those quantifiers. Fix instead:

* a prime `p`;
* nonempty finite lists `a=(a_1,...,a_r)` and `b=(b_1,...,b_s)` of positive
  integers, so `r,s>=1`;
* an integer `n>=0`.

Put

\[
 R(n)={\prod_{i=1}^r(a_i n)!\over\prod_{j=1}^s(b_j n)!},\qquad
 \Delta=\sum_i a_i-\sum_j b_j,
\]

and, with `s_p(m)` denoting the sum of the base-`p` digits of `m`,

\[
 D_p(n)=(p-1)v_p(R(n))-\Delta n.                    \tag{1.1}
\]

Here `v_p` is the additive valuation on nonzero rationals, so no integrality of
`R(n)` is assumed. Repeated entries in either list are distinct coordinates.

Ambiguities fixed here are: input is read least-significant digit first; exactly
`L` digits, including high zero padding, are read for `0<=n<p^L`; extrema
include `n=0`; terminal carry digits are part of the output; parallel digit
edges are retained; and only states reachable from the zero carry affect the
cycle theorem.

## 2. Digit-sum identity

Legendre's formula, derived by counting multiples of powers of `p`, is

\[
 v_p(m!)=\sum_{h\ge1}\left\lfloor {m\over p^h}\right\rfloor
        ={m-s_p(m)\over p-1}.                              \tag{2.1}
\]

Apply (2.1) separately to every factorial in `R(n)`. The linear terms are
`Delta*n`, and therefore cancel the centering in (1.1). Thus

\[
 \boxed{D_p(n)=\sum_{j=1}^s s_p(b_jn)-
                    \sum_{i=1}^r s_p(a_in).}               \tag{2.2}
\]

This proves the identity independently of T133. In particular, `D_p(n)` is an
integer even when `R(n)` is not.

## 3. Complete LSDF multiplication-carry transducer

For a positive multiplier `c`, its incoming carry lies in
`K_c={0,...,c-1}`. Indeed, from `0<=kappa<c` and `0<=d<p`,

\[
 0\le\left\lfloor{cd+\kappa\over p}\right\rfloor<c.        \tag{3.1}
\]

Take the complete finite state space

\[
 K=\prod_{i=1}^r K_{a_i}\times\prod_{j=1}^s K_{b_j}.       \tag{3.2}
\]

Write a state as `q=(alpha_1,...,alpha_r; beta_1,...,beta_s)`.
The initial state is the all-zero vector `q0`. For every state `q` and every
digit `d in {0,...,p-1}`, there is exactly one transition `q --d/w--> q'`,
where

\[
 \alpha'_i=\left\lfloor{a_i d+\alpha_i\over p}\right\rfloor,
 \qquad
 \beta'_j=\left\lfloor{b_j d+\beta_j\over p}\right\rfloor, \tag{3.3}
\]

and

\[
 w(q,d)=\sum_j(b_jd+\beta_j-p\beta'_j)
         -\sum_i(a_id+\alpha_i-p\alpha'_i).                \tag{3.4}
\]

Every state, all `p` transitions from every state, and the terminal weight

\[
 \tau(q)=\sum_j s_p(\beta_j)-\sum_i s_p(\alpha_i)           \tag{3.5}
\]

are now specified. Unreachable states may be removed without changing any
output from `q0`; let `S` be the resulting accessible state set.

To prove exactness, write `n=sum_(t=0)^(L-1) d_t p^t`. For any multiplier `c`,
let `kappa_0=0` and use (3.3). The `t`-th output digit of `cn` is

\[
 e_t=cd_t+\kappa_t-p\kappa_{t+1}.                          \tag{3.6}
\]

After `L` steps the unflushed high part is `kappa_L`, so

\[
 s_p(cn)=\sum_{t=0}^{L-1}e_t+s_p(\kappa_L).                \tag{3.7}
\]

Summing (3.7) with signs prescribed by (2.2) proves

\[
 \boxed{D_p(n)=\sum_{t=0}^{L-1}w(q_t,d_t)+\tau(q_L)}        \tag{3.8}
\]

for every `L>=0` and `0<=n<p^L`. This includes all centering and terminal-carry
terms.

## 4. Exact max-plus and min-plus formulas

Let `-infinity` and `+infinity` have their usual tropical meanings. Index rows
and columns by `S` and define

\[
 A^+_{uv}=\max\{w(u,d):T(u,d)=v\},\qquad
 A^-_{uv}=\min\{w(u,d):T(u,d)=v\},                         \tag{4.1}
\]

using `-infinity` or `+infinity` if the set is empty. Let `e^+` be zero at
`q0` and `-infinity` elsewhere, and let `e^-` be zero at `q0` and `+infinity`
elsewhere. With max-plus product `otimes_max` and min-plus product
`otimes_min`, (3.8) gives the exact formulas

\[
 \boxed{M_L:=\max_{0\le n<p^L}D_p(n)
   =e^+\otimes_{\max}(A^+)^{\otimes_{\max}L}
       \otimes_{\max}\tau,}                               \tag{4.2}
\]

\[
 \boxed{m_L:=\min_{0\le n<p^L}D_p(n)
   =e^-\otimes_{\min}(A^-)^{\otimes_{\min}L}
       \otimes_{\min}\tau.}                               \tag{4.3}
\]

Proof: tropical multiplication once selects one digit edge and adds its
weight. Induction on `L` therefore ranges over exactly all `p^L` digit words;
the final multiplication adds exactly (3.5). Parallel edges are combined by
the extrema in (4.1), which is valid because only their endpoint and weight
matter for all continuations.

Equivalently, define `H_0(q)=h_0(q)=tau(q)` and

\[
 H_{L+1}(q)=\max_d(w(q,d)+H_L(T(q,d))),\quad
 h_{L+1}(q)=\min_d(w(q,d)+h_L(T(q,d))).                    \tag{4.4}
\]

Then `M_L=H_L(q0)` and `m_L=h_L(q0)`. This is an exact dynamic program, not an
asymptotic approximation.

## 5. Accessible-cycle theorem and deviation criterion

Regard digit transitions on `S` as a directed weighted multigraph. For every
directed cycle `C`, count repeated vertices/edges with multiplicity and put
`mean(C)=weight(C)/length(C)`. Define

\[
 \mu_+=\max_C mean(C),\qquad \mu_-=\min_C mean(C),          \tag{5.1}
\]

where cycles are accessible from `q0` by the definition of `S`.
It is enough to take simple directed cycles: every closed walk decomposes into
simple cycles and its mean is a length-weighted average of their means. Thus
the extrema in (5.1) are over a finite nonempty set and are attained.

There is always a zero-weight loop at `q0`, supplied by input digit zero.
Consequently `mu_+>=0`, `mu_-<=0`, `M_L>=0`, and `m_L<=0`.

**Theorem.** There are constants depending only on `p,a,b` such that, for all
`L>=0`,

\[
 \boxed{M_L=\mu_+L+O(1),\qquad m_L=\mu_-L+O(1).}            \tag{5.2}
\]

**Upper and lower envelope proof.** Delete directed cycles successively from
any length-`L` path. Its remainder is a simple path of fewer than `|S|` edges.
Every deleted cycle has weight at most `mu_+` times its length and at least
`mu_-` times its length. There are finitely many simple paths and terminal
weights, so this gives `M_L<=mu_+L+C_+` and
`m_L>=mu_-L-C_-`.

Choose a cycle attaining `mu_+`, a path of `h` edges from `q0` to a vertex on
it, and let its length be `ell`. For each sufficiently large `L`, first take
between zero and `ell-1` copies of the zero loop at `q0`, then the access path,
then as many whole copies of the cycle as fit. Choose the zero-loop count so
that the total is exactly `L`; the endpoint is the chosen cycle vertex, where
the fixed terminal weight is applied. The omitted number of cycle edges is
less than `ell`, proving `M_L>=mu_+L-C'_+`. The same construction with a cycle
attaining `mu_-` proves `m_L<=mu_-L+C'_-`. Enlarging constants covers the
finitely many small `L`, proving (5.2). This argument explicitly uses only
accessible cycles and works even when the graph is not strongly connected.

It follows without extra assumptions that:

* all deviations `D_p(n)`, over all block lengths, are uniformly bounded iff
  `mu_+=mu_-=0`;
* the upper deviation is bounded iff `mu_+=0`, and otherwise its exact maximum
  grows linearly with positive slope `mu_+`;
* the lower deviation is bounded iff `mu_-=0`, and otherwise its exact minimum
  grows linearly with negative slope `mu_-`;
* deviations grow linearly in both signs iff `mu_+>0>mu_-`.

For the reverse implication in the first bullet, a nonzero accessible cycle
can be repeated after its access path, producing an unbounded output in its
sign. Thus no cancellation hidden in a terminal weight changes the criterion.

## 6. Fresh mandatory application

Take the central trinomial factorial ratio

\[
 R(n)={(3n)!\over(n!)^3},\qquad p=2.                       \tag{6.1}
\]

This model is fresh relative to the required T63, T68, T78--T80, T85, T124,
T126, and T133 boundary; no literature-novelty claim is made. A full-text
search of the supplied accepted library found no prior occurrence of this
ratio or the central-trinomial label. T133 contains `(3n)!` only inside the
different H1 ratio `(6n)!n!/(12^n(3n)!(2n)!)`. Prior note-level factorial
claims are unverified comparison memory, not premises here.

The factorization
`R(n)=binom(3n,n)binom(2n,n)` proves that `R(n)` is an integer. Here
`Delta=0`, so `D_2(n)=v_2(R(n))=3s_2(n)-s_2(3n)`. The three denominator
multiplier-1 carries are always zero. In the product-state notation of (3.2),
the complete accessible set is exactly
`{(0;0,0,0),(1;0,0,0),(2;0,0,0)}`; the table abbreviates these by their
multiplier-3 coordinate `0,1,2`.

| state | digit 0 | digit 1 | terminal |
|---|---|---|---|
| `0` | `0 / 0` | `1 / 2` | `0` |
| `1` | `0 / -1` | `2 / 3` | `-1` |
| `2` | `1 / 0` | `2 / 2` | `-1` |

An entry is `next state / edge weight`. This table displays all six
transitions and all three terminal weights. Its simple cycle means are

\[
 0,\quad 2,\quad {2-1\over2}={1\over2},\quad
 {3+0\over2}={3\over2},                                   \tag{6.2}
\]

from, respectively, the loops at 0 and 2 and the cycles `0-1-0` and
`1-2-1`. Hence `mu_-=0` and `mu_+=2`. Formula (5.2) says the minimum is
bounded and the maximum has slope 2. In fact (4.4) gives the exact refinement

\[
 \boxed{\min_{0\le n<2^L}v_2(R(n))=0\quad(L\ge0),}          \tag{6.3}
\]

\[
 \boxed{\max_{0\le n<2^L}v_2(R(n))=
   \begin{cases}0,&L=0,\\1,&L=1,\\2L,&L\ge2.\end{cases}}  \tag{6.4}
\]

For (6.3), valuations are nonnegative because (6.1) is a multinomial
coefficient, while `n=0` attains zero. For (6.4), direct substitution gives
the continuation maxima

| remaining digits `L` | state 0 | state 1 | state 2 |
|---|---:|---:|---:|
| `0` | `0` | `-1` | `-1` |
| `1` | `1` | `2` | `1` |
| `L>=2` | `2L` | `2L` | `2L-1` |

The rows `L=0,1,2` are direct. Substitution into all six transitions proves
the displayed `L+1` row for every `L>=2`, hence (6.4). The all-one word
attains the maximum for `L>=2`.

## 7. Proved p-primary screen and unproved transfer premises

The reciprocal

\[
 x_n={(n!)^3\over(3n)!}={1\over R(n)}                       \tag{7.1}
\]

is already in lowest terms because `R(n)` is a positive integer. Consequently
the exact proved 2-primary denominator screen is

\[
 \boxed{v_2(\operatorname{den}(x_n))=D_2(n)},               \tag{7.2}
\]

with block extrema (6.3)--(6.4). This says only which power of 2 divides the
reduced denominator. It does not determine the odd part, the result of lowest
terms after sums, multiplicative order, orbit occupancy, or approximation to
pi. In particular, no full-modulus conclusion follows from (7.2).

Here is one explicit sufficient transfer package, solely to expose what is
missing. Each premise is **unproved**. It posits integers `m,n,N>=1`, a model
index `k=k(m)>=0`, and a rational `X_m=P_m/Q_m` in lowest terms.

1. **PI-REP-T141 (representation):** there is an exact identity
   `pi=X_m+epsilon_m`, and the complete reduction of `Q_m` contains a specified
   factor inherited from `den(x_k)=R(k)`. Equation (7.2) would identify only
   the 2-primary exponent of that factor; cancellation in `X_m` must still be
   ruled out by this premise.
2. **PI-TRUNC-T141 (truncation):** for every integer `A>=1` and every
   sufficiently large `n`, one can choose `m,N` with `N>=A*n` and
   \[
   |\epsilon_m|\le {10^{-n}\over2(10^{N-1}-1)}              \tag{7.3}
   \]
   when `N>1` (for `N=1` the phase error is zero). Hence for `i,j<N`,
   `|(10^i-10^j)epsilon_m|<=10^(-n)/2`.
3. **PI-ORDER-T141 (multiplicative order):** writing
   `Q_m=2^u5^v q_m` with `gcd(q_m,10)=1`, complete reduction proves both the
   transient and a quantitative lower bound
   \[
   \operatorname{ord}_{q_m}(10)\ge N,                       \tag{7.4}
   \]
   or a stronger explicitly stated bound actually used to prove occupancy.
   The 2-primary screen (7.2) proves neither the factorization nor (7.4).
4. **PI-OCC-T141 (occupancy):** for those same choices, the ordered,
   diagonal-inclusive rational metric count obeys
   \[
   \#\{(i,j)<N:\|(10^i-10^j)X_m\|_{\mathbb R/\mathbb Z}
          <\tfrac32 10^{-n}\}\le {N^2\over A n}.            \tag{7.5}
   \]
   Multiplicative order alone does not imply this metric bound; distribution
   inside the rational orbit is an additional requirement.

Under (7.3), every canonical pi pair at strict radius `10^(-n)` belongs to the
set in (7.5), so (7.5) would give `A*n*Q_pi(n,N)<=N^2`. This one-line
implication explains the constants but does not discharge any premise. No
source or argument here supplies PI-REP, PI-TRUNC, PI-ORDER, or PI-OCC. They
are not asserted as plausible facts, and no fixed-pi, A1, C1, or C2 conclusion
is made.

## 8. Exact replay and evidence boundary

Run, in a directory containing only the delivered files,

```bash
python3 verify_t141.py
```

The script hash-checks the canonical statement, constructs every carry state,
transition and terminal weight from the formulas, checks the state cap
`3<=100000`, checks all six specialized transitions, computes exact rational
cycle means, replays tropical extrema, and for every `0<=n<1000000` compares
Legendre floors, digit sums, and transducer output. `raw_output.txt` is the
captured output of that command. These are finite `experiment` checks only;
the proofs in Sections 2--6 carry the universal statements.
