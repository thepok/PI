# BBP short orbit: bounded-factor mixing and the unbounded diagonal barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is Marcel's local question and has no external source
URL; none is invented here.

Frozen inputs:

- [bbp_mixed_coordinate_height_separator_20260813.md](bbp_mixed_coordinate_height_separator_20260813.md),
  SHA-256
  `950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820`;
- [bbp_high_prime_phase_compression_20260813.md](bbp_high_prime_phase_compression_20260813.md),
  SHA-256
  `47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564`;
- [bbp_odd_cofactor_short_orbit_experiment_20260813.md](bbp_odd_cofactor_short_orbit_experiment_20260813.md),
  corrected SHA-256
  `c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`. No fixed-sixteen return and no complete
proof that every finite decimal word occurs in pi is obtained here.

There is nevertheless a genuine positive analytic result, with label
`proof sketch`.

1. The proportional BBP row is long enough to mix one retained high-prime
   coordinate whenever the multiplicative order of ten is larger than
   square-root scale. Erdős--Murty prove that this order condition holds for
   all but a quantitatively sparse set of primes. Consequently all but
   \(o(M)\) of the retained high-prime logarithmic mass is locally mixing.
2. More strongly, for every **fixed** \(k\), every product of at most \(k\)
   nonexceptional retained high primes has a power-saving exponential-sum
   bound. This follows by splitting the row into complete common periods and
   one remainder, then applying Bourgain--Chang separately to the subgroup
   periods and to a sufficiently long proper remainder.
3. This does not extend to the actual product. Its number of prime factors
   tends to infinity, its size is \(\exp((5+o(1))M)\), and the row length is
   only \(\Theta(M)=\Theta(\log Q_M)\). Both positive-power hypotheses in
   Bourgain--Chang then fail. Local characters share the same exponent and
   form one diagonal orbit, so neither the ordinary large sieve nor local
   cancellation permits the synchronized complement to be discarded.

Thus the fact that every retained prime is \(O(M)\) does produce strong
bounded-dimensional mixing. The precise unresolved step is an
**unbounded-factor diagonal estimate for the actual selected phase**. The
finite companion replay has label `experiment`; the source applicability
audit is `literature-checked`. Nothing here is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.

## 1. Exact row and its prime-coordinate projections

Write the reduced BBP truncation as

\[
 B_M={P_M\over 2^{K_M}R_M},\qquad
 D_M=2^{K_M-4},\qquad
 A_n={10^n-16\over16}.
\]

Put

\[
 L_M=\lfloor(\log_{10}16)M\rfloor,\qquad
 T_M=L_M-M+1=(\log_{10}16-1)M+O(1).                \tag{LS1}
\]

The exact missing sum is

\[
 \mathcal S_{M,h}
 =\sum_{n=M}^{L_M}
 e\!\left({hA_nP_M\over D_MR_M}\right).             \tag{LS2}
\]

The frozen transfer result says that suitable decay of these rows would give
the fixed-sixteen return and hence V1. Equation (LS2) is only a normalized
target.

For every actually surviving high prime \(p>M\), let
\(\widehat\gamma_{M,p}\in\{1,\ldots,p-1\}\) be its frozen additive CRT
coordinate. The localization report gives

\[
 \widehat\gamma_{M,p}\equiv G_{M,p}\pmod p,          \tag{LS3}
\]

where \(G_{M,p}\) is one of the eight displayed rational constants and every
such prime satisfies

\[
                         M<p\le 8M+5.                \tag{LS4}
\]

For a set \(\mathcal P\) of retained high primes, put

\[
 Q=\prod_{p\in\mathcal P}p,\qquad
 \Xi_{M,\mathcal P}
 =\sum_{p\in\mathcal P}{\widehat\gamma_{M,p}\over p}
 \equiv{\xi_{M,\mathcal P}\over Q}\pmod1.           \tag{LS5}
\]

Reducing its numerator modulo a prime \(p\mid Q\) leaves
\(\widehat\gamma_{M,p}(Q/p)\not\equiv0\pmod p\). Hence

\[
                         (\xi_{M,\mathcal P},Q)=1.    \tag{LS6}
\]

This primitivity is important: the fixed-product theorem below applies to
the actual selected coordinate, not to a generic or averaged numerator.

## 2. A local order-sensitive estimate

Let

\[
 t_p=\operatorname {ord}_p(10),\qquad
 \mathcal S_{M,p,h}
 =\sum_{n=M}^{L_M}
 e_p(h\widehat\gamma_{M,p}A_n).                     \tag{LS7}
\]

Fix \(h\ne0\). For sufficiently large \(M\), \(p>|h|\). Since \(p>5\),
\(16\) is invertible modulo \(p\), and after writing \(n=M+j\),

\[
 |\mathcal S_{M,p,h}|
 =\left|\sum_{j=0}^{T_M-1}e_p(\lambda_{M,p,h}10^j)\right|,
 \quad
 \lambda_{M,p,h}\not\equiv0\pmod p.                \tag{LS8}
\]

The constant term \(-1\) in \(A_n=16^{-1}10^n-1\) has modulus one and
does not affect the absolute value.

Kerr's Theorem 2 applies uniformly in the nonzero coefficient. From
(LS1)--(LS4), \(p\asymp T_M\) and \(T_M>\sqrt p\) eventually. If
\(T_M<t_p\), the third line of that theorem gives

\[
 |\mathcal S_{M,p,h}|
 \le p^{1/4}t_p^{-1/96}T_M^{49/96+o(1)}
 \ll T_M^{3/4+o(1)}.                                \tag{LS9}
\]

There is also a useful bound when \(t_p\le T_M\). Break the row into complete
\(t_p\)-periods and a remainder of length \(r<t_p\). For a multiplicative
subgroup \(H\subset\mathbb F_p^*\), multiplicative-character expansion and
the ordinary Gauss bound give

\[
 \left|\sum_{x\in H}e_p(ax)\right|\le\sqrt p
 \quad(a\ne0).                                      \tag{LS10}
\]

The complete periods therefore cost at most \(T_M\sqrt p/t_p\). If
\(r\le T_M^{3/4}\), use the trivial remainder bound. If
\(r>T_M^{3/4}\), then \(r>\sqrt p\) eventually and Kerr's third line gives,
using \(t_p\ge r\),

\[
 |S(r)|\le p^{1/4}t_p^{-1/96}r^{49/96+o(1)}
 \ll T_M^{3/4+o(1)}.                                \tag{LS11}
\]

Combining both cases yields the order-sensitive statement

\[
 \boxed{
 { |\mathcal S_{M,p,h}|\over T_M}
 \ll {\sqrt p\over t_p}+T_M^{-1/4+o(1)}.}           \tag{LS12}
\]

In the case \(t_p>T_M\), (LS9) supplies the same conclusion directly.
Consequently any selected family with
\(t_p/\sqrt p\to\infty\) has local normalized sum tending to zero. This is
the strongest correct single-coordinate consequence found here; no
primitive-root assumption is needed.

## 3. Almost all retained high-prime mass is locally mixing

Erdős--Murty's Theorem 3, specialized to the fixed integer \(10\), states
that there are constants \(\alpha,\delta>0\) such that

\[
 \operatorname {ord}_p(10)
 \ge\sqrt p\exp((\log p)^\delta)                    \tag{LS13}
\]

for all but
\(O(x/(\log x)^{1+\alpha})\) primes \(p\le x\). Applying this with
\(x=8M+5\), the exceptional retained primes have total logarithmic mass at
most

\[
 O\!\left({M\over(\log M)^{1+\alpha}}\right)O(\log M)
 =O\!\left({M\over(\log M)^\alpha}\right)=o(M).     \tag{LS14}
\]

The frozen denominator audit gives total retained high-prime mass

\[
 \sum_{\substack{p>M\\p\mid R_M}}\log p=(5+o(1))M. \tag{LS15}
\]

Hence the primes satisfying (LS13) still carry \((5+o(1))M\) of logarithmic
mass. For each fixed nonzero \(h\), (LS12) gives cancellation on every one of
these local projections. Low multiplicative order is therefore not the
large-mass obstruction.

This conclusion uses the global exceptional-set theorem only as an upper
bound: restricting the exceptional primes to the moving support can only
decrease their number.

## 4. Every fixed number of good coordinates mixes jointly

The preceding local result can be upgraded without pretending that the
coordinates are independent.

Fix \(k\ge1\). For each \(M\), choose any nonempty set \(\mathcal P_M\) of
at most \(k\) retained primes satisfying (LS13), and let \(Q_M\) and
\(\xi_{M,\mathcal P_M}\) be as in (LS5). Then

\[
 Q_M\le(8M+5)^k.                                    \tag{LS16}
\]

Use the fixed parameter \(\delta_0=1/(8k)\). For all sufficiently large
\(M\), equations (LS1), (LS13), and (LS16) imply

\[
 T_M>Q_M^{\delta_0},\qquad
 \operatorname {ord}_p(10)>Q_M^{\delta_0}
 \quad(p\mid Q_M).                                  \tag{LS17}
\]

The squarefree modulus \(Q_M\) has at most the fixed number \(k\) of prime
factors, so it satisfies the source's "few prime factors" hypothesis.
Moreover, (LS6) shows that for fixed \(h\ne0\) the coefficient

\[
 h\xi_{M,\mathcal P_M}16^{-1}10^M\pmod {Q_M}        \tag{LS18}
\]

is primitive once every selected prime exceeds \(|h|\).

There is a period issue that must be handled explicitly. Put

\[
 \tau_M=\operatorname {ord}_{Q_M}(10)
       =\operatorname {lcm}_{p\mid Q_M}\operatorname {ord}_p(10),
 \qquad T_M=u_M\tau_M+r_M,\quad0\le r_M<\tau_M.    \tag{LS18a}
\]

The subgroup \(H_M=\langle10\rangle\subset\mathbb Z_{Q_M}^*\) projects
modulo every \(p\mid Q_M\) to a subgroup of size
\(\operatorname {ord}_p(10)>Q_M^{\delta_0}\). Bourgain--Chang Corollary
4.2 therefore bounds one complete period by
\(|H_M|Q_M^{-\eta_k}\) for some \(\eta_k>0\), and all \(u_M\) complete
periods cost at most \(T_MQ_M^{-\eta_k}\). If
\(r_M\le Q_M^{\delta_0}\), the trivial bound costs
\(O(T_M^{1/8+o(1)})\). If \(r_M>Q_M^{\delta_0}\), then
\(r_M<\tau_M\), so Corollary 4.5 applies to this proper incomplete
remainder. After reducing the saving exponent, there is an
\(\varepsilon_k>0\), independent of the selected primes and \(M\), such
that

\[
 \boxed{
 \left|\sum_{n=M}^{L_M}
 e\!\left(hA_n\Xi_{M,\mathcal P_M}\right)\right|
 \ll_k T_M^{1-\varepsilon_k}.}                      \tag{LS19}
\]

Thus the actual selected prime coordinates are jointly mixing on every
fixed-dimensional projection. This is stronger than separately applying
(LS12), and it already accounts for their common exponent.

Equation (LS19) remains a `proof sketch`: its primary-source hypotheses have
been checked and its elementary specialization is displayed, but it has not
been formalized in Lean.

## 5. Why fixed-dimensional mixing does not reach the actual phase

Let \(Q_M^>\) be the product of **all** retained primes above \(M\). From
(LS15),

\[
 Q_M^>=\exp((5+o(1))M),\qquad
 \omega(Q_M^>)\asymp {M\over\log M}.                \tag{LS20}
\]

The lower bound on \(\omega\) follows because each factor is at most
\(8M+5\); the matching upper order is the elementary prime-count bound.
Therefore the factor-count parameter in Bourgain--Chang is unbounded.
More decisively, for every fixed \(\delta_0>0\),

\[
 T_M=\Theta(M)< (Q_M^>)^{\delta_0},\qquad
 \operatorname {ord}_p(10)\le p-1=O(M)<(Q_M^>)^{\delta_0}   \tag{LS21}
\]

eventually. Both hypotheses in its Corollary 4.5 fail, regardless of how
large the orders are relative to the individual primes.

The obstruction is also exact at the character level. If
\(z_{p,n}=e_p(h\widehat\gamma_{M,p}A_n)\), the high-prime factor is

\[
                         \prod_{p\mid Q_M^>}z_{p,n}. \tag{LS22}
\]

It is sampled on the one diagonal map

\[
 n\longmapsto(10^n\bmod p)_{p\mid Q_M^>}.           \tag{LS23}
\]

Over a complete period, the image has cardinality

\[
 \operatorname {lcm}_{p\mid Q_M^>}t_p,              \tag{LS24}
\]

not \(\prod_pt_p\). The actual row uses only its first \(T_M=\Theta(M)\)
points. Local or bounded-product averages are marginals of this diagonal
orbit; they are not independent samples.

Finally, the full sum (LS2) is

\[
 \mathcal S_{M,h}
 =\sum_{n=M}^{L_M}W_{M,h}(n)
   \prod_{p\mid Q_M^>}z_{p,n},                      \tag{LS25}
\]

where \(W_{M,h}\) is the synchronized dyadic and remaining-cofactor
character. It always has modulus one. Neither (LS12) nor (LS19) estimates
(LS25), because deleting \(W_{M,h}\) changes the sum. The frozen mixed
separator shows concretely why this distinction cannot be dismissed.

## 6. Large-sieve and Burgess applicability

The ordinary additive large sieve controls a family of separated **linear**
frequencies with one common coefficient sequence. Applied locally, it can
average expressions such as
\(\sum_n c_n e_p(a_p n)\). Here the relevant phase is
\(e_p(a_p10^n)\), and if one absorbs all other CRT factors into \(c_n\), that
coefficient sequence depends on the chosen \(p\). There is no common family
to which the large-sieve inequality applies. Averaging the unweighted local
sums only reproves information about the marginals, not (LS25).

Kerr's fourth-moment theorem does average the correct power-generator sum
over all coefficients modulo one prime. Its pointwise Theorem 2 is already
strong enough for (LS12). The difficulty is therefore not a missing local
average.

Burgess estimates consecutive sums of multiplicative characters. Equation
(LS8) is instead an additive character evaluated on consecutive powers.
No exact transform found in the source audit changes one into the other, and
the synchronized product (LS25) remains even if a local Burgess-like saving
is postulated.

Bourgain--Chang is the closest composite-modulus theorem located. Section 4
shows it genuinely applies to every fixed number of selected factors;
(LS20)--(LS21) show exactly why it does not apply to their full product. This
is a method-specific no-go, not an impossibility theorem for every future
unbounded-factor estimate.

## 7. Exact finite falsification and replay

The independent companion
[bbp_large_sieve_short_orbit_20260813_check.py](bbp_large_sieve_short_orbit_20260813_check.py),
SHA-256
`fb0925503b7ffbb6ec06a83c0c4d84779f13c8d81a41be84c1436a26ee2ff8c7`,
imports no earlier checker. It uses exact integers and fractions for all
structural assertions; complex floating point is confined to explicitly
labelled magnitude diagnostics.

Two tempting uniform assertions fail immediately:

- at \(M=48\), the actual coordinate \(p=73\),
  \(G_{48,73}=264/5\), has \(t_p=8<T_M=10\), so not every retained prime
  has order exceeding the row length;
- at \(M=50\), \(p=101\), \(G_{50,101}=56\), and \(t_p=4\); its local
  normalized row magnitude is \(0.7951973\ldots\). Thus a uniform finite
  local saving without an order hypothesis is false.

There is also an actual-support diagonal witness. At \(M=48\), both
\(p=53\) and \(p=79\) have order \(13\). Their paired orbit has exactly
\(13\) states, while the Cartesian product of the two projections has
\(13^2=169\) states. This is an exact cardinality check, not a statistical
interpretation.

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_check.py
```

Retained output:

```text
status: PASS
bounded_replay_label: experiment
analytic_claim_label: proof sketch
depth_range: [48, 400]
high_prime_coordinate_checks: 57889
multiplicative_order_checks: 57889
exact_period_checks: 57889
order_at_most_row_length_rows: 3284
order_above_sqrt_prime_rows: 56263
fixed_factor_hypothesis_checks: 1412
first_order_gt_length_falsifier: (48, 73, 10, 8, Fraction(264, 5))
maximum_low_order_normalized_magnitude: 0.795197347556592 at M=50, p=101, T=11, ord=4, G=56
minimum_log_global_order_over_depth: 1.002540481904505 at M=319 (bit_length=462, coordinate_count=222)
actual_M48_pair: p=53,79; orders=13,13
actual_pair_diagonal_size: 13
actual_pair_cartesian_size: 169
exact_record_sha256: e65b35327209c5350dfedcf103f7e2b12f65aeef57a86d2027d545c1c3b8ac09
asserts_full_product_cancellation: false
asserts_fixed_sixteen_return: false
asserts_v1: false
```

Every bounded row is an `experiment`. The large global-order diagnostic is
not evidence for equidistribution of its first \(T_M\) states.

## 8. Dated literature and mathlib audit

Search date: **2026-08-13 UTC**.

- Bryce Kerr,
  [*Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170),
  Theorem 2, gives the three order-sensitive bounds used in
  (LS9)--(LS12). The locally pinned PDF is
  [kerr-1302.4170v1.pdf](../theory/pi-long-lag-block-collision-decay/library/t70/kerr-1302.4170v1.pdf),
  SHA-256
  `9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd`.
- Pál Erdős and M. Ram Murty,
  [*On the Order of a (mod p)*](https://mast.queensu.ca/~murty/erdos-ram.pdf),
  Theorem 3 on printed page 88, gives (LS13) with the stated exceptional-set
  size. The author-hosted PDF retrieved on the audit date has SHA-256
  `75da28d20c371a3700af9c8a67130f5a8642010e74bab6ae2627bfefa64909a8`.
- Jean Bourgain and Mei-Chu Chang,
  [*Exponential Sum Estimates over Subgroups and Almost Subgroups of
  \(\mathbb Z_q^*\), where \(q\) is Composite with Few Prime Factors*](https://doi.org/10.1007/s00039-006-0558-7),
  Corollaries 4.2 and 4.5 give (LS19) after the explicit period split above.
  Corollary 4.2 controls complete subgroup periods; Corollary 4.5 controls a
  proper incomplete remainder once its length exceeds \(q^\delta\). Both
  require bounded total prime-power factor count and projected subgroup
  orders exceeding \(q^\delta\). The pinned
  PDF is
  [bourgain-chang-2006.pdf](../theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf),
  SHA-256
  `a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7`.
- Konyagin--Shparlinski,
  [*On the Consecutive Powers of a Primitive Root: Gaps and Exponential
  Sums*](https://doi.org/10.1112/S0025579311002117), supplies the sharper
  primitive-root special case but is not needed after Kerr. The pinned PDF
  is
  [konyagin-shparlinski-2012.pdf](../theory/pi-lacunary-near-return-sparsity/library/t85/konyagin-shparlinski-2012.pdf),
  SHA-256
  `46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc`.
- Montgomery--Vaughan,
  [*The large sieve*](https://doi.org/10.1112/S0025579300004708), is the
  primary source checked for the ordinary separated-frequency inequality.
  Its common-coefficient, linear-frequency shape does not match (LS25).
- Burgess,
  [*On Character Sums and Primitive Roots*](https://www.mathnet.ru/eng/mat267),
  concerns multiplicative-character interval sums, not (LS8).

The search also covered `large sieve power generator primes`, `incomplete
exponential sums multiplicative order`, and `short orbit composite modulus`.
No primary theorem located allows both an unbounded number of prime factors
and a \(\Theta(\log q)\)-length ordered prefix with the actual BBP
coefficient. This is a bounded applicability statement, not an exhaustiveness
or novelty claim.

A repository/mathlib search found the elementary order divisibility lemmas
`orderOf_units_dvd_card_sub_one` and `orderOf_dvd_card_sub_one` in
`Mathlib/FieldTheory/Finite/Basic.lean`, plus finite additive-character
orthogonality. It found no formal Kerr, Erdős--Murty, Bourgain--Chang, or
unbounded-factor power-generator estimate. No verified-track declaration is
added in this branch.

## Sharp handoff

The proportional length \(T_M\asymp M\) and the bound \(p=O(M)\) are useful:
they prove cancellation after projection onto almost every individual high
prime, and even after projection onto any fixed number of good high primes.
This removes "perhaps the local orders are too small" as the main explanation
for the failure of the route.

The surviving target is genuinely global:

\[
 \boxed{
 \sum_{n=M}^{L_M}W_{M,h}(n)
 \prod_{p\mid Q_M^>}e_p(h\widehat\gamma_{M,p}A_n)
 =o(T_M).}                                           \tag{LS26}
\]

It has \(\Theta(M/\log M)\) synchronized prime factors, a modulus
\(\exp((5+o(1))M)\), and only \(\Theta(M)\) samples. Existing local,
fixed-factor, large-sieve, and Burgess estimates do not imply (LS26). A new
unbounded-factor diagonal theorem using the actual BBP coefficient and its
dyadic/cofactor correlation would be a genuine return implication. None is
proved here, so V1 remains a `conjecture`.

## Coordination record

This branch registered the descendant-area watch
`watch:local:pi-digits:large-sieve-short-orbit-20260813` on
`local:pi-digits` for agent `codex-large-sieve-short-orbit`. Its initial
poll was empty at cursor and delivered sequence 57,116, so no event was
acknowledged. Observation events were treated only as coordination signals,
not as mathematical evidence.
