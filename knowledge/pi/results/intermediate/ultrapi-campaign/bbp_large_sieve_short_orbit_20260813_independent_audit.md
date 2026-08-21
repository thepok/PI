# Independent audit: BBP bounded-factor short-orbit mixing

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is Marcel's local, human-authored question and has no
external source URL; none is invented here.

Primary artifacts audited without editing:

- [bbp_large_sieve_short_orbit_20260813.md](bbp_large_sieve_short_orbit_20260813.md),
  SHA-256
  `23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d`;
- [bbp_large_sieve_short_orbit_20260813_check.py](bbp_large_sieve_short_orbit_20260813_check.py),
  SHA-256
  `fb0925503b7ffbb6ec06a83c0c4d84779f13c8d81a41be84c1436a26ee2ff8c7`.

## Audit result and claim boundary

**Result: PASS.**

The primary's two substantive conclusions remain supported, with status
`proof sketch`:

1. all but (o(M)) of the retained high-prime logarithmic mass has a
   locally cancelling proportional row; and
2. every projection onto at most a fixed number (k) of nonexceptional
   retained primes has a uniform power-saving bound.

The corrected primary explicitly handles the multiplicative-period issue:
it splits the row into complete common periods and one remainder, applies
Bourgain--Chang Corollary 4.2 to every complete period, applies Corollary 4.5
only to a sufficiently long proper remainder, and bounds a short remainder
trivially.  This is the required repair.  The independent period-crossing
witness below is retained as a regression check showing why the split is
necessary, not as a defect in the corrected primary.

No estimate is obtained for the product of all retained coordinates.  In
particular, this audit proves no fixed-sixteen return and no decimal-word
occurrence.  Canonical V1 remains a `conjecture`.  The independent replay is
an `experiment`; the direct source inspection below is
`literature-checked`.  Nothing here is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.

## 1. Exact normalized row

Retain the primary notation

\[
 T_M=\lfloor(\log_{10}16)M\rfloor-M+1
     =cM+O(1),\qquad c=\log_{10}16-1>0,             \tag{A1}
\]

and, for a retained prime (M<p\leq8M+5),

\[
 t_p=\operatorname {ord}_p(10),\qquad
 S_{M,p,h}=\sum_{j=0}^{T_M-1}e_p(\lambda_{M,p,h}10^j),
 \quad \lambda_{M,p,h}\ne0                         \tag{A2}
\]

for every fixed nonzero (h) and all sufficiently large (M).  The
coefficient is nonzero because the selected CRT coordinate is nonzero,
(p>|h|), and (16) and (10) are units modulo (p).

Equations (A1) and (M<p\leq8M+5) imply uniformly

\[
                         p\asymp T_M,qquad \sqrt p<T_M             \tag{A3}
\]

once (M) is large.  These are the scale facts required by Kerr's third
line.

## 2. Independent derivation of LS9--LS12

Kerr's Theorem 2 states, for (N\leq t_p), that in the range
(sqrt p<N<t_p),

\[
 \max_{(\lambda,p)=1}
 \left|\sum_{j=1}^{N}e_p(\lambda10^j)\right|
 \leq p^{1/4}t_p^{-1/96}N^{49/96+o(1)}.             \tag{A4}
\]

### Case (T_M<t_p)

Apply (A4) with (N=T_M).  Since (p\asymp T_M) and
(t_p>T_M),

\[
 |S_{M,p,h}|
 \ll T_M^{1/4-1/96+49/96+o(1)}
 =T_M^{3/4+o(1)}.                                  \tag{A5}
\]

The exponent identity is exact:
(1/4-1/96+49/96=3/4).

### Case (t_p\leq T_M)

Write (T_M=qt_p+r), (0\leq r<t_p).  One complete period is an
additive character sum over the multiplicative subgroup
(H=\langle10\rangle\subset\mathbb F_p^*).  If
(d=(p-1)/|H|), multiplicative-character orthogonality gives

\[
 \sum_{x\in H}e_p(ax)
 ={1\over d}\sum_{\chi^d=1}\sum_{x\ne0}\chi(x)e_p(ax).
\]

The principal inner sum is (-1), and every nonprincipal inner sum is a
Gauss sum of modulus (sqrt p).  Therefore

\[
                         \left|\sum_{x\in H}e_p(ax)\right|\leq\sqrt p. \tag{A6}
\]

All complete periods cost at most (T_M\sqrt p/t_p).  If
(r\leq T_M^{3/4}), the trivial bound handles the remainder.  Otherwise
(r>T_M^{3/4}>\sqrt p) eventually, and (A4), now with (N=r<t_p), gives

\[
 |S(r)|
 \leq p^{1/4}t_p^{-1/96}r^{49/96+o(1)}
 \leq p^{1/4}r^{1/2+o(1)}
 \ll T_M^{3/4+o(1)}.                               \tag{A7}
\]

Combining (A5)--(A7) proves the primary estimate

\[
 \boxed{
 { |S_{M,p,h}|\over T_M}
 \ll {\sqrt p\over t_p}+T_M^{-1/4+o(1)}.}          \tag{A8}
\]

No primitive-root assumption entered this derivation.  If
(t_p/\sqrt p\to\infty), both terms in (A8) tend to zero.

## 3. Erdős--Murty and exceptional logarithmic mass

The author-hosted scan of Erdős--Murty was retrieved and inspected directly.
Its SHA-256 is
`75da28d20c371a3700af9c8a67130f5a8642010e74bab6ae2627bfefa64909a8`.
Theorem 3 on printed page 88 states that, for the order (f(p)) of a fixed
integer (a>1), there exist (alpha,delta>0) such that

\[
 f(p)\geq\sqrt p\exp((\log p)^\delta)               \tag{A9}
\]

outside (O(x/(\log x)^{1+\alpha})) primes (p\leq x).
Taking (a=10) is valid for all retained primes because they exceed five.

At (x=8M+5), every exceptional retained prime has logarithm
(O(\log M)).  Hence their total logarithmic mass is at most

\[
 O\!\left({M\over(\log M)^{1+\alpha}}\right)O(\log M)
 =O\!\left({M\over(\log M)^\alpha}\right)=o(M).     \tag{A10}
\]

The frozen denominator result gives total retained high-prime mass
((5+o(1))M).  Deleting the exceptional set therefore leaves
((5+o(1))M) mass, and (A9) makes the first term of (A8) at most
(exp(-(log p)^\delta)).  This supports the primary local-mixing claim.

This is only a statement about projections.  Summing logarithmic mass does
not combine their additive characters.

## 4. Fixed-(k) Bourgain--Chang claim: audit of the corrected proof

Let (mathcal P_M) contain (1\leq\ell\leq k) nonexceptional retained
primes, where (k) is fixed, and put

\[
 Q=\prod_{p\in\mathcal P_M}p,qquad
 \Xi={\xi\over Q}\pmod1.                            \tag{A11}
\]

Reduction of the common numerator modulo (p\mid Q) gives

\[
 \xi\equiv\widehat\gamma_{M,p}(Q/p)\not\equiv0\pmod p,
\]

so ((\xi,Q)=1).  The shifted coefficient
(h\xi16^{-1}10^M) is likewise a unit for fixed (h\ne0) once
all selected primes exceed (|h|).

### Why the explicit period split is necessary

The source's Remark 4.6 explicitly calls (t<\operatorname{ord}_Q(10))
the incomplete-sum case in Corollary 4.5.  Its proof forms the set of the
first (t) powers; once a period is crossed, repetitions must be counted
separately.  The lower bounds on (T_M) and on every local order do not by
themselves verify

\[
                         T_M\leq\operatorname{ord}_Q(10).      \tag{A12}
\]

Nor does (A9) imply (A12): its lower bound is square-root scale, while
(T_M\asymp M).

This is not merely a remote quantifier issue.  On the actual (M=48)
support,

\[
 p=73,quad \widehat\gamma_{48,73}\equiv264/5,quad
 Q=73,quad T_M=10,quad\operatorname{ord}_{73}(10)=8.       \tag{A13}
\]

Both size inequalities for (delta_0=1/4) hold exactly:
(10^4>73) and (8^4>73), but the row contains one complete period plus
two further terms.  The independent replay finds 6,851 such singleton
period crossings through depth 600.  Finite counts are `experiment`, but
(A13) exactly falsifies the implication that the size hypotheses alone put
the whole row inside one period.  The corrected primary avoids that
implication by making the split explicit.

### Verification of the corrected fixed-(k) proof

Choose, for example, (delta_0=1/(8k)).  Since

\[
 Q\leq(8M+5)^k,qquad T_M\asymp M,qquad
 t_p\geq\sqrt p\exp((\log p)^\delta),               \tag{A14}
\]

we have, for every (p\mid Q) and all sufficiently large (M),

\[
                         T_M>Q^{\delta_0},qquad t_p>Q^{\delta_0}. \tag{A15}
\]

Let

\[
                         \tau=\operatorname{ord}_Q(10)
                              =\operatorname {lcm}_{p\mid Q}t_p,
 \qquad T_M=u\tau+r,quad0\leq r<\tau.              \tag{A16}
\]

The subgroup (H=\langle10\rangle\subset\mathbb Z_Q^*) projects to a
subgroup of size exactly (t_p>Q^{\delta_0}) modulo every (p\mid Q).
The squarefree (Q) has at most (k) prime factors, hence has "few prime
factors" in the exact source definition.  Bourgain--Chang Corollary 4.2
therefore supplies (eta_k>0) with

\[
 \left|\sum_{x\in H}e_Q(ax)\right|
 \leq |H|Q^{-\eta_k}\qquad((a,Q)=1).                \tag{A17}
\]

The (u) complete periods in (A16) contribute at most
(T_MQ^{-\eta_k}).  For the remainder:

- if (r\leq Q^{\delta_0}), use the trivial bound
  (r\leq Q^{\delta_0}\ll T_M^{1/8+o(1)});
- if (r>Q^{\delta_0}), then (r<\tau), so Corollary 4.5 applies to the
  proper incomplete remainder and gives (r^{1-\eta'_k}).

Because (Q>M) and (T_M\asymp M), these three terms yield, after reducing
the saving to absorb fixed constants,

\[
 \boxed{
 \left|\sum_{n=M}^{L_M}e(hA_n\Xi)\right|
 \ll_k T_M^{1-\varepsilon_k}}                       \tag{A18}
\]

for some (\varepsilon_k>0), uniformly over every chosen set of at most
(k) nonexceptional retained primes.  Thus primary equation LS19 is
supported as now written.  It remains a `proof sketch`.

## 5. Audit of the global barrier

For the full retained high-prime product (Q_M^>), the frozen mass formula
gives

\[
                         \log Q_M^>=(5+o(1))M.                 \tag{A19}
\]

Every factor is at most (8M+5), so (A19) gives
(omega(Q_M^>)\gg M/\log M).  The prime-counting upper bound gives the
reverse (O(M/\log M)); hence

\[
                         \omega(Q_M^>)\asymp M/\log M.         \tag{A20}
\]

For every fixed (delta_0>0), (A19), (T_M=\Theta(M)), and
(t_p\leq p-1=O(M)) imply

\[
 T_M<(Q_M^>)^{\delta_0},qquad
 t_p<(Q_M^>)^{\delta_0}                              \tag{A21}
\]

eventually.  The factor count is also unbounded.  Thus neither Corollary
4.2 nor 4.5 applies to the full product.

The synchronization obstruction is exact.  The orbit modulo the product
has period

\[
                         \operatorname {lcm}_{p\mid Q_M^>}t_p, \tag{A22}
\]

not (prod_pt_p).  On the actual (M=48) support, the selected primes
(53) and (79) both have order 13, so their paired orbit has 13 states,
while the Cartesian product of the two projections has 169.  Cancellation
of every bounded marginal does not estimate the synchronized product with
the remaining dyadic/cofactor character.

The primary's large-sieve and Burgess applicability boundaries are also
correct.  The ordinary additive large sieve needs a common coefficient
sequence and linear frequencies; absorbing the complementary CRT factors
would make the coefficients depend on the selected prime.  Burgess concerns
multiplicative characters on consecutive integers, whereas the local term is
an additive character on consecutive powers.  These observations are
method-specific no-go statements, not impossibility theorems.

## 6. Independent replay

The independent checker
[bbp_large_sieve_short_orbit_20260813_independent_check.py](bbp_large_sieve_short_orbit_20260813_independent_check.py),
SHA-256
`6bb233921592a5cd2e2868c53c8b3ce6e6de8e99624ea894bc206f4de3ec288c`,
imports no branch checker.  It rebuilds both the four-pole localization and
the six-band table, compares 352 local coordinates with the actual reduced
BBP rational at five depths, factors every (p-1) independently, verifies
CRT primitivity and common periods, and extends the finite scan through
depth 600.

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_independent_check.py \
  --max-depth 600
```

Retained output:

```text
status: PASS
verifies_explicit_fixed_factor_period_split: true
bounded_replay_label: experiment
analytic_claim_label: proof sketch
depth_range: [48, 600]
coordinate_formula_checks: 171170
actual_reduced_crt_checks: 352
multiplicative_order_checks: 124635
exact_period_checks: 124635
fixed_factor_hypothesis_checks: 2212
fixed_factor_rows_crossing_period: 0
singleton_rows_crossing_period: 6851
period_crossing_witness:
  M=48, p=73, T=10, ord=8, periods=1, remainder=2, coordinate=264/5
full_product_barrier_checks: 1106
minimum_log_high_product_over_depth: 4.618178146918716 at M=114
maximum_log_row_length_over_log_high_product: 0.01011246276808403 at M=48
actual_pair_diagonal_size: 13
actual_pair_cartesian_size: 169
kerr_LS9_exponent: 3/4
kerr_LS11_exponent: 3/4
asserts_full_product_cancellation: false
asserts_fixed_sixteen_return: false
asserts_v1: false
```

Every bounded count and magnitude is an `experiment`.  In particular, the
finite product ratios do not prove (A19), and the many period crossings do
not prove or disprove distribution.

## 7. Direct source and mathlib record

Status: bounded `literature-checked` inspection on **2026-08-13 UTC**.

| source | directly checked content | SHA-256 |
|---|---|---|
| Bryce Kerr, [*Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170), Theorem 2 | The third line is exactly (A4), with (N\leq t) globally and (sqrt p<N<t) in that line. | `9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd` |
| Pál Erdős and M. Ram Murty, [*On the Order of a (mod p)*](https://mast.queensu.ca/~murty/erdos-ram.pdf), Theorem 3, printed p. 88 | Gives (A9) outside (O(x/(\log x)^{1+\alpha})) primes for fixed (a). | `75da28d20c371a3700af9c8a67130f5a8642010e74bab6ae2627bfefa64909a8` |
| Jean Bourgain and Mei-Chu Chang, [*Exponential Sum Estimates over Subgroups and Almost Subgroups of \(\mathbb Z_q^*\)*](https://doi.org/10.1007/s00039-006-0558-7), Corollaries 4.2, 4.5 and Remark 4.6 | Corollary 4.2 gives (A17); 4.5 handles a long incomplete prefix; Remark 4.6 records the incomplete-period distinction used in the primary's explicit split. | `a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7` |

The repository/mathlib search confirms elementary multiplicative-order and
finite-character infrastructure but no formal Kerr, Erdős--Murty,
Bourgain--Chang, or unbounded-factor diagonal estimate.  No verified-track
declaration is added: the analytic results remain a `proof sketch`, and
formalizing finite instances would not prove a return.

## 8. Coordination record and handoff

This audit registered the descendant-area watch
`watch:local:pi-digits:independent-large-sieve-audit-20260813` on
`local:pi-digits` for agent `codex-independent-large-sieve-audit`.  Its
latest poll before writing was empty at cursor and delivered sequence
57,198, so no event was acknowledged.  Observation events were not used as
evidence.

The sharp remaining target is unchanged:

\[
 \sum_{n=M}^{L_M}W_{M,h}(n)
 \prod_{p\mid Q_M^>}e_p(h\widehat\gamma_{M,p}A_n)=o(T_M).     \tag{A23}
\]

The audited results control every fixed-dimensional projection of (A23)
using the primary's explicit period split, and show that almost all
logarithmic mass has good local order.  They do not control the unbounded
synchronized product.  No V1 implication is claimed.
