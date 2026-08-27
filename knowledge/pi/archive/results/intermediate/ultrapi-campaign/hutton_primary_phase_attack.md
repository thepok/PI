# Hutton simultaneous primary phases: an almost-full modulus without phase steering

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here. This note continues the existing problem record using
the fields of [`problems/TEMPLATE.md`](../../problems/TEMPLATE.md).

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained. The
canonical V1 statement remains a `conjecture`.

This branch does establish a stronger exact arithmetic package than the
single-prime-power tests. For

\[
 R_a=3^a7^{a+1},\qquad K_a={R_a-3\over4},\qquad a\ge2,                 \tag{1}
\]

both large primary components of the reduced Hutton denominator are known
exactly and simultaneously:

\[
 \boxed{
 v_3(\operatorname{den}H_{K_a})=R_a+a,
 \qquad
 v_7(\operatorname{den}H_{K_a})=R_a+a+1.}                            \tag{2}
\]

Their leading units are also explicit to a growing precision. If

\[
 H_{K_a}=P_a/Q_a,\qquad b_a=v_5(Q_a),\qquad
 m_a=Q_a/5^{b_a},\qquad A_a\equiv2^{b_a}P_a\pmod {m_a},               \tag{3}
\]

and \(F_{0,a}=3^{R_a+a}7^{R_a+a+1}\), then the canonical additive-CRT
coordinate

\[
 \xi_a\equiv A_a(m_a/F_{0,a})^{-1}\pmod {F_{0,a}}                    \tag{4}
\]

satisfies

\[
\begin{aligned}
 \xi_a&\equiv-8\,10^{b_a}7^{R_a}\pmod {3^{a+2}},\\
 \xi_a&\equiv-4\,10^{b_a}3^{R_a}\pmod {7^{a+3}}.                    \tag{5}
\end{aligned}
\]

There is a second, asymptotically sharp compression. Adjoin to \(F_{0,a}\)
every prime \(p>\sqrt {R_a}\) which survives in \(Q_a\), and call the
resulting modulus \(F_a\). Then

\[
 Q_a=5^{b_a}F_aD_a,\qquad (F_a,D_a)=1,\qquad
 \boxed{D_a\le R_a^{\sqrt {R_a}}=\exp(O(\sqrt {R_a}\log R_a))}.       \tag{6}
\]

Thus the two primary powers and the high-prime coordinates determine all
but a subexponential complementary modulus. Equations (1)--(6), including
the elementary proofs below, are a `proof sketch`: they are not registered
Lean declarations. The finite replay is an `experiment`.

The attempted breakthrough fails at a precise point. The low-primary data
(5), even together with the *exact* primary denominator and exact decimal
period, admit a different numerator whose first essentially
\(R_a\log_{10}21\) primary-phase steps are arbitrarily close to one. Hence no
uniform short-sum estimate can follow from (2) and (5). Using the complete
actual coordinate removes that countermodel, but then the selected and
complementary phases obey the taut exact identity

\[
 e_{F_a}(\alpha_a10^s)e_{D_a}(\beta_a10^s)
       =e(10^{b_a+s}H_{K_a}),                                          \tag{7}
\]

which is the fixed pi phase up to the Hutton bracket. The smallness of
\(D_a\) does not prevent the one actual complementary state from following a
word-avoiding path. No unconditional cylinder hit, `candidate resolution`,
or `verified resolution` follows.

## 1. Normalized target and ambiguous quantifiers

Write the nonterminating decimal expansion of pi as

\[
 \pi=3+\sum_{j\ge0}d_j(\pi)10^{-(j+1)},
 \qquad d_j(\pi)\in\{0,\ldots,9\}.
\]

The exact target is

\[
 \forall\ell\ge0\ \forall c\in\{0,\ldots,10^\ell-1\}\ \exists j\ge0:
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c.                    \tag{V1}
\]

The code \(c\) is padded to length \(\ell\), so leading zeroes count;
occurrence is contiguous; and \(\ell=0\) is vacuous.

Three quantifiers in this attack must not be conflated.

1. Equations (2) and (5) hold for every integer \(a\ge2\).
2. Equation (6) says that, after the displayed local data are fixed, at most
   \(D_a=\exp(o(R_a))\) complementary residues remain possible.
3. V1 needs the **one residue actually selected by \(P_a\)** to enter each
   prescribed decimal cylinder at an offset where the Hutton bracket still
   transfers. Neither a small candidate count nor an average over candidates
   supplies that pointwise assertion.

The word “known coordinate” below means an exact modular formula or a finite
algorithm. It does not mean that its ordered short orbit has been proved
equidistributed.

## 2. Hutton notation

For every odd \(R\equiv3\pmod4\), put \(K=(R-3)/4\) and

\[
 H_K=\sum_{\substack{1\le r\le R\\r\ {\rm odd}}}
 \chi_4(r)\left({8\over r3^r}+{4\over r7^r}\right),                  \tag{8}
\]

where \(\chi_4(r)=(-1)^{(r-1)/2}\). The adjacent alternating-series bracket is

\[
 H_K<\pi<H_K+W_K,
 \qquad
 W_K={8\over(R+2)3^{R+2}}+{4\over(R+2)7^{R+2}}.                      \tag{9}
\]

The exact result T66 gives an odd reduced denominator and the full decimal
transient

\[
 b_K=v_5(\operatorname{den}H_K)=\lfloor\log_5R\rfloor.               \tag{10}
\]

The special radii in (1) satisfy \(R_a\equiv3\pmod4\), because the sum of
their exponents of numbers congruent to \(-1\pmod4\) is \(2a+1\).

## 3. A dominant-layer lemma

The simultaneous result rests on one elementary lemma.

> **Dominant-layer lemma.** Let \(p\) be an odd prime, \(R\) an odd positive
> integer, and \(u=v_p(R)\ge1\). If
> 
> \[
>             \lfloor\log_pR\rfloor\le p^u-2,                         \tag{11}
> \]
> 
> then every odd \(r<R\) satisfies
> 
> \[
>                         r+v_p(r)\le R-2.                             \tag{12}
> \]

To prove it, set \(d=R-r\), which is a positive even integer, and
\(t=v_p(r)\). If \(t<u\), then \(p^t\mid d\). For \(t=0\), parity gives
\(d\ge2=t+2\); for \(t\ge1\), \(d\ge p^t\ge t+2\). If \(t\ge u\), then
\(p^u\mid d\). Also \(p^t\le r<R\), so
\(t\le\lfloor\log_pR\rfloor\), and (11) gives

\[
 d\ge p^u\ge\lfloor\log_pR\rfloor+2\ge t+2.
\]

In every case \(t\le d-2\), which is (12).

For \(R_a=3^a7^{a+1}\), the two hypotheses follow without logarithmic
approximation. Since \(7<3^2\),

\[
 \lfloor\log_3R_a\rfloor\le3a+1\le3^a-2\qquad(a\ge2),                \tag{13}
\]

where the last inequality starts with equality at \(a=2\) and then follows
by induction. Since \(3<7\),

\[
 \lfloor\log_7R_a\rfloor\le2a\le7^{a+1}-2.                           \tag{14}
\]

Apply the lemma first with \((p,u)=(3,a)\), then with
\((p,u)=(7,a+1)\).

## 4. Exact simultaneous primary valuations and units

At the prime 3, the valuation of the base-3 summand indexed by \(r\) is
\(-r-v_3(r)\). Equation (12) puts every earlier base-3 summand at valuation
at least \(-(R_a-2)\), whereas the final summand has valuation
\(-(R_a+a)\). Every base-7 summand has 3-adic valuation only \(-v_3(r)\), so
it cannot tie the final base-3 term. The latter is uniquely minimal; hence

\[
                         v_3(H_{K_a})=-(R_a+a).                         \tag{15}
\]

The same argument with 3 and 7 interchanged gives

\[
                         v_7(H_{K_a})=-(R_a+a+1).                       \tag{16}
\]

Since \(H_{K_a}=P_a/Q_a\) is reduced, (15)--(16) prove (2).

There is useful leading-unit information. Put \(c=a+1\). The last base-3
term is

\[
 -{8\over R_a3^{R_a}}=-{8\over3^{R_a+a}7^c}.
\]

After multiplication by \(3^{R_a+a}\), every preceding base-3 term is
divisible by \(3^{a+2}\), by (12), and every base-7 term is even more
3-adically integral: its scaled valuation is
\(R_a+a-v_3(r)\ge a+2\). Therefore

\[
 3^{R_a+a}H_{K_a}\equiv-8\,7^{-c}\pmod {3^{a+2}}.                    \tag{17}
\]

Symmetrically,

\[
 7^{R_a+c}H_{K_a}\equiv-4\,3^{-a}\pmod {7^{c+2}}.                    \tag{18}
\]

Here the symmetric cross-base check is
\(R_a+c-v_7(r)\ge c+2\). Both inequalities follow, for example, from
\(v_p(r)\le\lfloor\log_pR_a\rfloor\le R_a-2\). Thus no cross-base term
has been omitted from either leading-unit congruence.

These are congruences of rationals whose denominators are units at the
displayed prime.

Now use (3)--(4). Modulo \(3^{R_a+a}\), the additive coordinate on the
3-primary factor is \(10^{b_a}\) times (17). Recombining it inside
\(F_{0,a}\) multiplies by the other primary factor \(7^{R_a+c}\). This gives

\[
 \xi_a\equiv-8\,10^{b_a}7^{R_a}\pmod {3^{a+2}}.
\]

The 7-primary calculation similarly gives the second line of (5). Thus (5)
is about the actual post-transient additive coordinate, not an unreduced
numerator silently substituted for it.

For comparison, the single-prime subsequences are immediate special cases
of the same dominant-layer mechanism. If \(R=3^e\) with odd \(e\), then
\(v_3(\operatorname{den}H_K)=R+e\) and
\(3^{R+e}H_K\equiv-8\pmod {3^{e+2}}\). If \(R=7^e\) with odd \(e\), then
\(v_7(\operatorname{den}H_K)=R+e\) and
\(7^{R+e}H_K\equiv-4\pmod {7^{e+2}}\). The family (1) is stronger because
it certifies both large primary factors at the same index.

## 5. High-prime enrichment leaves only a subexponential modulus

Every summand denominator in (8) divides

\[
 3^R7^R\Lambda_R,
 \qquad \Lambda_R=\operatorname{lcm}\{1,3,5,\ldots,R\}.              \tag{19}
\]

Consequently, for a prime \(p>\sqrt R\), its exponent in \(Q_a\) is at most
one. Define

\[
 \mathcal P_a=\{p>\sqrt {R_a}:p\mid Q_a\},\qquad
 F_a=F_{0,a}\prod_{p\in\mathcal P_a}p,
 \qquad D_a={m_a\over F_a}.                                           \tag{20}
\]

The general singular-prefix calculation in
[`hutton_multi_band_attack.md`](hutton_multi_band_attack.md) determines both
membership in \(\mathcal P_a\) and the local coordinate. Explicitly, for
\(p>7\), \(p\le R<p^2\), and

\[
 n=\left\lfloor{\lfloor R/p\rfloor+1\over2}\right\rfloor,
 \qquad
 A_n=\sum_{j=0}^{n-1}(-1)^j
 \left({8\over(2j+1)3^{2j+1}}+{4\over(2j+1)7^{2j+1}}\right),          \tag{21}
\]

one has

\[
                  pH_K\equiv\chi_4(p)A_n\pmod p.                     \tag{22}
\]

The prime survives exactly when the right side is nonzero.

This also gives the actual additive coordinate, not merely the survival
test. For a surviving \(p\in\mathcal P_a\), define its one-prime coordinate

\[
 \gamma_{a,p}\equiv A_a(m_a/p)^{-1}\pmod p.
\]

Since \(pH_{K_a}\equiv P_a(5^{b_a}m_a/p)^{-1}\pmod p\), (22) gives

\[
 \boxed{\gamma_{a,p}\equiv
 10^{b_a}\chi_4(p)A_n\pmod p.}                                      \tag{22a}
\]

The coordinate of the combined selected factor \(F_a\) restricts to this
\(p\)-coordinate after the usual additive-CRT recombination.

After the full 3- and 7-primary factors, the factor \(5^{b_a}\), and every
surviving high prime have been removed, every prime divisor of \(D_a\) is at
most \(\sqrt {R_a}\). Its exponent is at most
\(\lfloor\log_pR_a\rfloor\), by (19). Hence

\[
 D_a\le
 \prod_{p\le\sqrt {R_a}}p^{\lfloor\log_pR_a\rfloor}
 \le\prod_{p\le\sqrt {R_a}}R_a
 \le R_a^{\sqrt {R_a}},                                                \tag{23}
\]

which proves (6) without a prime-number theorem. In particular
\(\log D_a=o(R_a)\).

This is almost-full-modulus information. The main primary factor alone has

\[
 \log F_{0,a}=R_a\log21+O(a),                                         \tag{24}
\]

and the high-prime product adds essentially the radical contribution
studied in the multi-band report. Yet modulus size is not phase location.

## 6. The exact selected/complementary phase

Write \(m_a=F_aD_a\), and define the canonical additive coordinates

\[
 \alpha_a\equiv A_aD_a^{-1}\pmod {F_a},
 \qquad
 \beta_a\equiv A_aF_a^{-1}\pmod {D_a}.                               \tag{25}
\]

Then additive CRT gives, for every \(s\ge0\),

\[
\begin{aligned}
 e_{F_a}(\alpha_a10^s)e_{D_a}(\beta_a10^s)
 &=e_{m_a}(A_a10^s)\\
 &=e(10^{b_a+s}H_{K_a}),                                               \tag{26}
\end{aligned}
\]

which is (7). T58's bracket further gives

\[
 \left|e(10^{b_a+s}H_{K_a})-e(10^{b_a+s}\pi)\right|
 \le2\pi10^{b_a+s}W_{K_a}.                                           \tag{27}
\]

Thus, at every genuinely transferable offset, the complementary factor is
the selected inverse times the still-unknown fixed-pi phase, up to (27).
The fact that \(D_a=\exp(o(R_a))\) does not make this correlation small.

Equivalently, knowing \(\alpha_a\) leaves a shifted grid of \(D_a\) possible
full states. A fixed missing word has exponentially small avoidance measure
over \(\Theta(R_a)\) digits, but a deterministic shifted-grid count has one
boundary term per avoidance cylinder. The exact separator in
[`subexponential_candidate_avoidance.md`](subexponential_candidate_avoidance.md)
shows that a single reduced state can remain on a constant word-avoiding
itinerary even with a fixed complementary modulus and exponentially more
fine precision than (24). Therefore a probability-times-candidate-count
argument cannot promote (6) to a cylinder hit.

## 7. A stationary lift falsifies the low-primary short-sum route

The low congruences (5) might appear to force special cancellation in

\[
             \sum_{s<N}e_{F_{0,a}}(\xi_a10^s).                         \tag{28}
\]

They do not. Put

\[
 M_a=3^{a+2}7^{a+3},                                                    \tag{29}
\]

and let \(\widetilde\xi_a\in[0,M_a)\) be the least CRT lift of the two
residues in (5). Both residues are units, so
\((\widetilde\xi_a,F_{0,a})=1\). Thus
\(\widetilde\xi_a/F_{0,a}\) has the same exact primary denominator and the
same decimal period \(\operatorname{ord}_{F_{0,a}}(10)\) as the actual
primary coordinate, while retaining all the displayed low-unit data.

The period itself is explicit. LTE gives

\[
 \operatorname{ord}_{3^E}(10)=3^{E-2}\quad(E\ge2),\qquad
 \operatorname{ord}_{7^G}(10)=6\,7^{G-1}\quad(G\ge1),
\]

because \(v_3(10^n-1)=2+v_3(n)\),
\(\operatorname{ord}_7(10)=6\), and \(v_7(10^6-1)=1\). Hence

\[
 \boxed{\operatorname{ord}_{F_{0,a}}(10)
 =2\,3^{R_a+a-2}7^{R_a+a}.}                                       \tag{29a}
\]

Both the actual primary coordinate and the stationary lift are units at 3
and 7, so numerator cancellation cannot shorten this denominator or period.

For every integer \(N\ge1\) with
\(\widetilde\xi_a10^{N-1}<F_{0,a}\), the chord inequality gives the rigorous
lower bound

\[
 \left|{1\over N}\sum_{s=0}^{N-1}
 e_{F_{0,a}}(\widetilde\xi_a10^s)\right|
 \ge1-{2\pi M_a(10^N-1)\over9NF_{0,a}}.                               \tag{30}
\]

Since \(\log M_a=O(a)\) and (24) holds, the right side tends to one for
every

\[
 N\le(\log_{10}21-\delta)R_a,\qquad
 0<\delta<\log_{10}7.                                                  \tag{31}
\]

This range is much longer than the Hutton transfer scale
\(R_a\log_{10}3+O(\log R_a)\). Therefore even *simultaneous* exact primary
valuations, exact period, and \(O(a)\) leading primary digits are compatible
with essentially no cancellation over the whole relevant pulse.

The construction has a quantitative lesson. When the known primary
congruences have combined modulus \(10^{O(L_a)}\) with \(L_a=o(R_a)\), their
least nonnegative CRT lift remains stationary for
\(\log_{10}F_{0,a}-O(L_a)\) steps by the same chord estimate. Thus this class
of primary-residue proofs cannot force cancellation without
\(\Theta(R_a)\)-depth information about the actual coordinate. At that point
the needed input is an actual selected-numerator theorem, not a valuation
theorem.

## 8. Exact replay and falsification experiment

The companion checker is
[`hutton_primary_phase_check.py`](hutton_primary_phase_check.py). It uses
only integers and `Fraction` for all structural assertions. Run from the
repository root:

```text
python3 -m py_compile work/ultrapi-resume/hutton_primary_phase_check.py
python3 work/ultrapi-resume/hutton_primary_phase_check.py
```

The retained run checked the elementary family conditions for
\(2\le a\le20\), directly enumerated 1,429,278 earlier dominant-layer scores
and 12 associated maximum assertions in the first three family members, and
evaluated the first full rational sample
\(a=2\):

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
family_bound_checks=95
dominant_score_checks=1429278
dominant_bound_assertions=12
high_prime_primes=425
high_prime_classification_assertions=1275
high_prime_coordinate_checks=425
unresolved_factor_checks=12
exact_sample=a:2,c:3,R:3087,K:771,v3:3089,v7:3090,b:4,q_digits:5417,primary_digits:4086,selected_digits:5378,complement_digits:37,surviving_high_primes:425,horizon:1476,offsets:1473
stationary_separator=least_lift:1091638,low_modulus:1361367,log10_mean_chord_bound:-2609.466686
finite actual-phase means: N 3-primary 7-primary 3x7-primary primary+high-prime complement full
   308 0.099308843545 0.032454561685 0.076546692134 0.051195192320 0.050421559745 0.039051651600
   771 0.054262143659 0.026500426793 0.018173628808 0.026002365194 0.017126872638 0.027169395512
  1473 0.040199422931 0.004642658465 0.020299287215 0.012865023990 0.014177398939 0.011329286436
unresolved_factors=[(11, 3), (13, 3), (17, 2), (19, 2), (23, 2), (29, 2), (31, 2), (37, 2), (41, 2), (43, 2), (47, 2), (53, 2)]
all exact checks passed; complex means are experiments only
```

For this sample, \(Q_a\) has 5,417 decimal digits; the primary factor has
4,086; enriching it with 425 surviving high primes raises this to 5,378;
and the exact complement is only

\[
 D_a=3443846140271004739007417826008487767,                            \tag{32}
\]

a 37-digit number. The actual phase means show substantial finite
cancellation, including \(0.011329\ldots\) for the full rational state over
the 1,473 post-transient offsets inside the outer Hutton horizon. This is an
`experiment`, not an asymptotic estimate and not a proof about all words.
In contrast, the rigorously constructed stationary lift has the same low
primary certificates while its mean differs from one by less than
\(10^{-2609}\) at this sample scale. That exact comparison falsifies any
uniform inference from the low certificates.

## 9. Dated literature and mathlib applicability audit

Search cutoff: **2026-08-12 UTC**. Searches covered `incomplete exponential
sums powers prime powers`, `consecutive powers gaps`, and `geometric
progression length log modulus`. The first two retained primary sources are
pinned in the repository; the third was freshly checked at its versioned
arXiv source.

1. Bryce Kerr, [*Incomplete exponential sums over exponential
   functions*](https://arxiv.org/abs/1302.4170v1), Theorem 2, treats prime
   modulus \(p\), an element \(g\) of order \(t\), and \(N\le t\). Its first
   branch is
   \(p^{1/8}N^{71/96+o(1)}\). Even in its prime-field setting this beats the
   trivial \(N\) only after
   \(N>p^{12/25+o(1)}\), not at \(N=O(\log p)\). The pinned PDF is
   `work/theory/pi-lacunary-near-return-sparsity/library/t118/kerr-1302.4170v1.pdf`,
   SHA-256
   `9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd`.
2. Konyagin--Shparlinski,
   [*On the consecutive powers of a primitive root: gaps and exponential
   sums*](https://doi.org/10.1112/S0025579311002117), works over a prime
   field with a primitive root. Its interval-gap theorem is developed in the
   range \(p^{1/2}<N<p\). It neither treats the prime-power Hutton modulus nor
   the logarithmic-length pulse here. The pinned PDF is
   `work/theory/pi-lacunary-near-return-sparsity/library/t85/konyagin-shparlinski-2012.pdf`,
   SHA-256
   `46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc`.
3. The newly screened prime-power-family paper by Untrau,
   [*Equidistribution of exponential sums indexed by a subgroup of fixed
   cardinality*](https://arxiv.org/abs/2112.05441v1), varies the prime-power
   modulus and studies families of complete sums over a subgroup of fixed
   order. It does not give a pointwise estimate for one growing incomplete
   ordered prefix \(10^s\), \(s<N=O(\log q)\). The version-1 PDF was fetched
   on 2026-08-12 UTC with SHA-256
   edf36a7a2cc19f8787006cf8656bc218796cc887f3cf100087a5c71ded8cfc5f.

The source statements and this bounded applicability search are
`literature-checked`. The deductions in this report remain `proof sketch`.
No located theorem can contradict the stationary lift (30), so any applicable
result must impose actual-numerator information absent from the uniform
theorems.

The pinned mathlib commit remains
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Existing ingredients include
`padicValRat`, rational normalization, modular inverses, finite sums, and CRT.
No searched declaration provides the dominant-layer specialization, the
almost-full-modulus compression, or an actual Hutton phase estimate. No Lean
file was changed in this branch.

## 10. Exact missing theorem

The arithmetic progress is inspectable: one infinite Hutton subsequence has
both primary powers exactly certified, all high-prime coordinates available,
and only an \(\exp(o(R))\) complementary modulus. The route would close only
with a theorem using the **complete actual coordinate**, for example either:

1. a pointwise cylinder hit for the joint state in (26) at some
   \(s\le(\log_{10}3-\delta)R_a\); or
2. enough cancellation in the actual joint sums
   
   \[
   {1\over N_a}\sum_{s<N_a}e(h10^{b_a+s}H_{K_a}),
   \qquad N_a=\lfloor(\log_{10}3-\delta)R_a\rfloor,                   \tag{33}
   \]
   
   for every fixed nonzero integer \(h\), with a transfer through (27).

The second would imply a much stronger equidistribution statement and, by
(27), is already a fixed-pi lacunary Weyl-sum problem. An estimate for the
selected \(F_a\)-factor alone is insufficient because the \(D_a\)-factor is
its correlated partner in (26). More valuation precision below linear
primary depth is also insufficient by (30).

Therefore the honest terminal status is: simultaneous primary arithmetic
and almost-full denominator compression are proved at `proof sketch` level;
the selected real phase remains uncontrolled; V1 remains a `conjecture`.

## 11. Formalization map and independent review

No declaration in `ErdosLab/` or `TheoryLib/` was added by this branch. A
clean formalization could be split into mathematically named lemmas for:

1. the dominant-layer inequality (11)--(12);
2. the two exact valuations (15)--(16);
3. the scaled-unit congruences (17)--(18) and their additive-CRT translation
   (5); and
4. the elementary small-prime-complement bound (23).

The existing formal inputs are T58's Hutton bracket, T63's exact five-adic
valuation, and T66's proof that this is the full base-ten transient. Any
formal theorem supporting a research claim would have to be registered in
`audit/AxiomAudit.lean` and pass `scripts/check.ps1`; none of the new
`proof sketch` statements is represented as `machine-checked` here.

Independent adversarial review passed at the proof sketch label on
2026-08-12 UTC; see
[hutton_primary_phase_independent_audit.md](hutton_primary_phase_independent_audit.md).
The review independently rederived the scaled-unit and additive-coordinate
formulas, the support and size of \(D_a\), the exact primary period, and the
stationary separator. Its separately written exact replay is
[hutton_primary_phase_independent_check.py](hutton_primary_phase_independent_check.py).
This review does not upgrade any new statement to machine-checked and does
not alter the V1 status.
