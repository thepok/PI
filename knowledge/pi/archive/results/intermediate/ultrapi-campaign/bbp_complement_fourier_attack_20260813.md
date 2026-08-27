# BBP complementary Fourier coefficient: exact factorization, nine-block energy, and the persistence barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The target is Marcel's immutable local question and has no external source
URL; none is invented here.

Frozen inputs:

| input | SHA-256 |
|---|---|
| [three-primary twisted-sum report](bbp_three_primary_twisted_sum_20260813.md) | 0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12 |
| [independent twisted-sum audit](bbp_three_primary_twisted_sum_20260813_independent_audit.md) | 44aabae56bfafd647e6bb8a899a97030641630044c4b57df5a45c8e858863c81 |
| [large-sieve short-orbit report](bbp_large_sieve_short_orbit_20260813.md) | 23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d |
| [high-prime compression report](bbp_high_prime_phase_compression_20260813.md) | 47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564 |
| [cross-depth phase split](bbp_cross_depth_phase_compensation_20260813.md) | 3ff784ebad18c8dda7c63691ba99120f80299953361362f7d2f2f8cd26f89d3f |
| [three-primary epoch report](bbp_three_primary_epoch_20260813.md) | 5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7 |
| [three-primary decimation report](bbp_three_primary_decimation_20260813.md) | 29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0 |

All frozen inputs remained byte-for-byte unchanged in this branch.

## Outcome and claim boundary

Canonical V1 remains a *conjecture*. This branch proves no fixed-sixteen
return, no decay of the actual selected Fourier coefficient, no normality
statement, and no occurrence theorem for every finite decimal word in pi.

It does sharpen the exact obstruction, with label *proof sketch*, in four
ways.

1. On every last-pre-drop three-primary row, the complementary phase splits
   exactly into the selected dyadic carry, a rowwise constant 5-primary
   factor, a small-prime cofactor, a six-periodic high-prime grid factor, and
   the explicit reciprocal-prime lift.
2. The sparse three-primary transform admits a nine-block physical-space
   identity. Its selected complement Fourier energy is exactly a sum of
   squares of nine-point twisted block differences.
3. This energy identity is a sharp no-go for an energy-only argument. Even
   if every nontrivial complement block correlation cancels in the usual
   asymptotic sense, the selected energy tends to \(1/9\) of the total, and
   Cauchy--Schwarz gives only \(|S|/T\le1/3+o(1)\). The required saving is
   phase-sensitive, not support-sensitive.
4. Every one of the eight nonzero block correlations retains a dyadic
   Korobov component with \(\Theta(M)\) binary precision and high-prime
   logarithmic mass at least

\[
 \left(5-\frac{64\log 10}{405}+o(1)\right)M
 = (4.636134701\ldots+o(1))M.                       \tag{CF1}
\]

Thus neither one van der Corput step nor the exact sparse support reduces the
actual complement to a fixed-dimensional or complete sum.

The bounded exact replay has label *experiment*. The source applicability
audit in Section 7 has label *literature-checked*. This branch adds no Lean
declaration and makes no new *machine-checked*, *candidate resolution*, or
*verified resolution* claim.

## 1. Normalized target and quantifiers

Canonical V1 asks:

> For every integer \(P\ge1\) and every \(0\le k<10^P\), there is an
> integer \(n\ge0\) such that
> \(\lfloor10^P\{10^n\pi\}\rfloor=k\), with leading zeroes retained.

The quantifier is over every finite word and asks for one contiguous
occurrence. It does not assert infinitely many occurrences or normality.
This report studies only the stronger Fourier route on a special family of
BBP rows. Failure to prove that stronger estimate is not evidence against
V1.

For even \(e\ge4\), put

\[
 T=3^{e-2},\qquad H=T/9,\qquad
 M=M_e^-={5(3^e-1)\over8}-1={45T-13\over8}.        \tag{CF2}
\]

The interval \(M\le n<M+T\) is a complete isolated three-primary period and
is uniformly shadowed by the actual pi orbit with exponentially decreasing
BBP-tail error. Fix a harmonic \(h\ne0\). The main formulas below are
written for \(3\nmid h\); the fixed-\(v_3(h)\) extension is the repeated
version already audited in the frozen twisted-sum report.

## 2. Exact complement factorization

Write the reduced partial sum as

\[
 B_M={P_M\over2^{K_M}R_M},\qquad
 K_M=4M-v_2(M+1),\qquad (P_M,2R_M)=1,              \tag{CF3}
\]

put \(D_M=2^{K_M-4}\), and define

\[
 w_M\equiv P_MR_M^{-1}\pmod {D_M},\qquad
 c_M={P_M-R_Mw_M\over D_M}.                        \tag{CF4}
\]

Then \(w_M\) is odd, \((c_M,R_M)=1\), and exactly

\[
                         16B_M={w_M\over D_M}+{c_M\over R_M}. \tag{CF5}
\]

At the endpoint (CF2), factor

\[
 R_M=3^e5^{v_M}S_M^>C_{0,M},\qquad
 v_M=\lfloor\log_5(8M+5)\rfloor,                  \tag{CF6}
\]

where \(S_M^>\) is the squarefree product of the actual denominator primes
\(p>M\), and \(C_{0,M}\) contains the remaining prime powers other than 3
and 5. Define the additive CRT coordinates

\[
\begin{aligned}
 \beta_{3,M}&\equiv c_M(R_M/3^e)^{-1}\pmod {3^e},\\
 \beta_{5,M}&\equiv c_M(R_M/5^{v_M})^{-1}\pmod {5^{v_M}},\\
 \beta_{0,M}&\equiv c_M(R_M/C_{0,M})^{-1}\pmod {C_{0,M}},\\
 \widehat\gamma_{M,p}&\equiv c_M(R_M/p)^{-1}\pmod p
       \qquad(p\mid S_M^>).
\end{aligned}                                                   \tag{CF7}
\]

All displayed numerators are units at their own moduli. Additive CRT gives

\[
 {c_M\over R_M}\equiv
 {\beta_{3,M}\over3^e}+{\beta_{5,M}\over5^{v_M}}
 +{\beta_{0,M}\over C_{0,M}}
 +\sum_{p\mid S_M^>}{\widehat\gamma_{M,p}\over p}\pmod1.    \tag{CF8}
\]

For \(p>M\), the frozen localization identifies
\(\widehat\gamma_{M,p}\) with one of eight rational constants
\(G_{M,p}\) modulo \(p\). The reciprocal-residue lift is

\[
 \sum_{p\mid S_M^>}{\widehat\gamma_{M,p}\over p}
 \equiv {J_M\over105}+H_M\pmod1,\qquad
 H_M=\sum_{p\mid S_M^>}{G_{M,p}\over p}.          \tag{CF9}
\]

Here \(J_M\bmod105\) is the explicit residue-class count from the frozen
high-prime report. The reduced denominator of \(H_M\) is divisible by
\(S_M^>\): reduction modulo one selected prime leaves a nonzero local
coordinate times all other denominators. In particular,

\[
                     \log\operatorname {den}(H_M)\ge(5+o(1))M. \tag{CF10}
\]

Let

\[
 A_n={10^n-16\over16}=2^{n-4}5^n-1.               \tag{CF11}
\]

Since \(n\ge M\ge49>v_M\), one has
\(A_n\equiv-1\pmod {5^{v_M}}\). Equations (CF5)--(CF9) give the
complete phase split

\[
\boxed{
 (10^n-16)B_M\equiv
 {A_n\beta_{3,M}\over3^e}
 +{A_nw_M\over D_M}
 -{\beta_{5,M}\over5^{v_M}}
 +{A_n\beta_{0,M}\over C_{0,M}}
 +{A_nJ_M\over105}+A_nH_M\pmod1.}                \tag{CF12}
\]

This is the requested exact decomposition. The five-primary factor is one
rowwise constant. Moreover, from \(n=4\) onward,

\[
 A_n\pmod {105}=99,54,24,39,84,9                 \tag{CF13}
\]

with period six. Hence the \(J_M/105\) factor is an ordinary six-periodic
weight. The genuinely growing complement is the product of

\[
 \exp\!\left(2\pi ih{A_nw_M\over D_M}\right),\qquad
 \exp\!\left(2\pi ih{A_n\beta_{0,M}\over C_{0,M}}\right),\qquad
 \exp(2\pi ihA_nH_M).                              \tag{CF14}
\]

The terms in (CF14) are still synchronized by the same exponent \(n\).

## 3. Nine-block identity and selected Fourier energy

Write \(e_q(x)=\exp(2\pi ix/q)\), set

\[
 f(j)=e_{3^e}(h\beta_{3,M}A_{M+j}),\qquad
 W(j)=\text{the product of all five complementary factors in (CF12)},
                                                               \tag{CF15}
\]

and let

\[
 a\equiv h\beta_{3,M}16^{-1}10^M\pmod9.           \tag{CF16}
\]

Then \(a\) is a unit modulo nine. The binomial congruence used in the frozen
sparse-transform proof gives

\[
 10^{mH}\equiv1+m3^{e-2}\pmod {3^e}\qquad(0\le m<9). \tag{CF17}
\]

Consequently

\[
                         f(u+mH)=f(u)e_9(am).       \tag{CF18}
\]

The full complete-period sum therefore has the exact physical-space form

\[
\boxed{
 S_{M,h}:=\sum_{j=0}^{T-1}f(j)W(j)
 =\sum_{u=0}^{H-1}f(u)\,D_aW(u),\qquad
 D_aW(u)=\sum_{m=0}^{8}e_9(am)W(u+mH).}            \tag{CF19}
\]

For the unnormalized transform

\[
 \widehat W(k)=\sum_{j=0}^{T-1}W(j)e_T(-kj),        \tag{CF20}
\]

define its energy in one residue class modulo nine by

\[
                         E_b(W)=\sum_{k\equiv b\ (9)}|\widehat W(k)|^2.
                                                               \tag{CF21}
\]

Expanding the square and applying the \(H\)-term character orthogonality
relation gives the exact identity

\[
\boxed{
 E_b(W)=H\sum_{u=0}^{H-1}
 \left|\sum_{m=0}^{8}W(u+mH)e_9(-bm)\right|^2.}    \tag{CF22}
\]

The frozen primary transform is supported on frequencies
\(k\equiv a\pmod9\), so it pairs with complement frequencies
\(-k\equiv-a\pmod9\). Equations (CF19)--(CF22) and Cauchy--Schwarz give

\[
                         |S_{M,h}|^2\le E_{-a}(W). \tag{CF23}
\]

No asymptotic estimate has entered (CF18)--(CF23).

## 4. Why sparse support and ordinary complement mixing do not suffice

Expanding (CF22) at \(b=-a\) gives

\[
\begin{aligned}
 \sum_{u<H}|D_aW(u)|^2
 =9H+\sum_{\substack{0\le m,m'<9\\m\ne m'}}
 e_9(a(m-m'))
 \sum_{u<H}W(u+mH)\overline{W(u+m'H)}.             \tag{CF24}
\end{aligned}
\]

Suppose, optimistically, that every one of the 72 off-diagonal correlations
in (CF24) is \(o(H)\). Then

\[
 E_{-a}(W)={T^2\over9}+o(T^2),\qquad
 {\sqrt{E_{-a}(W)}\over T}={1\over3}+o(1).         \tag{CF25}
\]

Thus ordinary mixing of the complement does **not** evacuate the selected
frequency class. It leaves exactly the random-energy share \(1/9\).
Equation (CF23) then gives only a constant-factor improvement over the
trivial bound. To prove \(S_{M,h}=o(T)\), one must control the phases in the
inner product (CF19), not merely the Fourier support or energy of \(W\).

The bounded replay makes this distinction visible. All entries are
*experiment*.

| \(e\) | \(M\) | \(T\) | selected complement energy \(E_{-a}/T^2\) | energy bound \(\sqrt E/T\) | actual \(|S|/T\) |
|---:|---:|---:|---:|---:|---:|
| 4 | 49 | 9 | 0.0877736102 | 0.296266114 | 0.296266114 |
| 6 | 454 | 81 | 0.0652890348 | 0.255517191 | 0.052328659 |
| 8 | 4099 | 729 | 0.1229686043 | 0.350668796 | 0.019238483 |

The reference random-energy value is \(1/9=0.111111\ldots\). At the last
two rows, the selected energy is not small, while the phase-sensitive actual
pairing is much smaller. This directly falsifies the proposal that the new
sparse support alone eliminates the complementary modes.

Factorwise selected energies also remain broad:

| \(e\) | dyadic | small-prime | \(1/105\) grid | reciprocal lift | dyadic·small·lift | full complement |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 0.0293473 | 0.0389957 | 0 | 0.1206139 | 0.0877736 | 0.0877736 |
| 6 | 0.1588427 | 0.1107768 | 0.0122722 | 0.1150452 | 0.1316730 | 0.0652890 |
| 8 | 0.1206140 | 0.1230108 | 0.0122722 | 0.0991839 | 0.1215025 | 0.1229686 |

These finite values are diagnostics, not an asymptotic theorem.

## 5. Every block correlation retains the hard moduli

Fix distinct block indices and orient them as \(0\le s<s+r\le8\). Put

\[
 n_0=M+sH,\qquad d=rH,\qquad0\le u<H.              \tag{CF26}
\]

The five-primary factor cancels from
\(W(n_0+u+d)\overline{W(n_0+u)}\). For the dyadic factor, the exact
difference is

\[
 A_{n+d}-A_n={10^n(10^d-1)\over16}.               \tag{CF27}
\]

Every \(10^d-1\) is odd and \(w_M\) is odd. Put

\[
 L_{M,s,h}=K_M-(M+sH)-v_2(h).
\]

After cancelling the power of two common to the whole \(u\)-block, the
dyadic correlation has the two equivalent exact representations

\[
\boxed{
 e_{\,2^{L_{M,s,h}}}(\alpha_{M,r,s,h}10^u)
 =e_{\,2^{L_{M,s,h}-u}}(\alpha_{M,r,s,h}5^u)}     \tag{CF28}
\]

where \(\alpha_{M,r,s,h}\) is odd. The first representation has a fixed
modulus and nonunit base 10; the second has unit base 5 and a modulus that
changes with \(u\). It is therefore not a classical fixed-modulus,
unit-base Korobov sum. Its effective denominator exponent is nevertheless
uniformly deep. Since \(sH+u\le8H-1\),

\[
 L_{M,s,h}-u\ge
 \left(3-{64\over405}\right)M-O_h(\log M)
 ={1151\over405}M-O_h(\log M).                    \tag{CF29}
\]

Thus every term of a block correlation still carries about \(2.842M\)
binary digits of the actual selected dyadic coordinate. The relevant
analytic obstruction is the fixed-modulus/nonunit-base versus
unit-base/varying-modulus dichotomy, in addition to the merely logarithmic
block length.

For the high-prime part define the surviving squarefree modulus

\[
 Q_{M,r}=\prod_{\substack{p>M,\ p\mid R_M\\p\nmid10^{rH}-1}}p. \tag{CF30}
\]

For fixed nonzero \(h\) and sufficiently large \(M>|h|\), the correlation
coefficient is nonzero at every prime in (CF30). The annihilated primes have
product dividing \(10^{rH}-1\), so

\[
 \sum_{\substack{p>M,\ p\mid R_M\\p\mid10^{rH}-1}}\log p
 <rH\log10\le8H\log10
 ={64\log10\over405}M+O(1).                       \tag{CF31}
\]

The frozen high-prime denominator theorem gives total logarithmic mass
\((5+o(1))M\). Subtracting (CF31) proves (CF1), uniformly for
\(1\le r\le8\). Consequently each correlation contains a primitive odd
Korobov factor

\[
                         e_{Q_{M,r}}(\xi_{M,r,s,h}10^u),      \tag{CF32}
\]

with \((\xi_{M,r,s,h},Q_{M,r})=1\), length
\(H=\Theta(M)=\Theta(\log Q_{M,r})\), and an unbounded number of prime
factors. It is multiplied by (CF28) and by the remaining small-prime
coordinate. Local cancellation at one prime does not estimate this
synchronized product.

The replay checks (CF27)--(CF28) at every block pair and exponent for
\(e=4,6,8\). Its minimum observed surviving high-prime logarithmic mass,
divided by \(M\), is respectively

\[
                         4.59488648,\quad4.91704244,\quad4.95805733. \tag{CF33}
\]

These finite ratios are *experiment*; the all-depth lower bound is (CF1).

## 6. The harmless pieces and the exact remaining target

The constant 5-primary factor changes neither a Fourier magnitude nor a
normalized sum magnitude. The \(1/105\) grid factor is also finite
complexity. If

\[
 q_M(n)=e_{105}(hJ_MA_n),
\]

then \(q_M(n+6)=q_M(n)\), and its ordinary six-term Fourier expansion is

\[
 q_M(n)=\sum_{r=0}^{5}c_{M,r}e_6(rn),\qquad
 \sum_{r=0}^{5}|c_{M,r}|^2=1.                     \tag{CF34}
\]

Therefore the grid factor reduces the active problem to at most six fixed
rational twists. It does not create a growing modulus.

After stripping (CF34) and the constant factor, define

\[
 V_M(n)=
 e_{D_M}(hA_nw_M)
 e_{C_{0,M}}(hA_n\beta_{0,M})
 e(hA_nH_M).                                       \tag{CF35}
\]

The exact remaining *conjecture* on the endpoint family is the
phase-sensitive estimate

\[
\boxed{
 \sum_{u=0}^{H-1}f(u)
 \sum_{m=0}^{8}e_9(am)q_M(M+u+mH)V_M(M+u+mH)
 =o(H)}                                             \tag{CF36}
\]

for every fixed nonzero harmonic, along a common unbounded endpoint
subsequence. Equation (CF36) is equivalent to \(S_{M,h}=o(T)\) because
\(T=9H\); together with the frozen real shadow and Weyl bridge it would be a
genuine route to the fixed-sixteen return. No estimate of (CF36) is proved.

## 7. van der Corput and primary-literature applicability

### literature-checked

Search and direct-check date: **2026-08-13 UTC**.

The ordinary van der Corput correlation of the complete phase is

\[
 \sum_n e\!\left(h(10^{n+d}-10^n)B_M\right)
 =\sum_n e\!\left(h(10^d-1)10^nB_M\right).        \tag{CF37}
\]

Thus differencing preserves the geometric phase and only promotes the
coefficient. At the special lags \(d=rH\), the three-primary part collapses
to nine-block data, but Sections 4--5 show that the complement does not
collapse. At arbitrary lags, (CF37) is the same missing family already
recorded in the frozen weighted-differencing report.

- Joseph Vandehey,
  [*Differencing Methods for Korobov-type Exponential Sums*](https://arxiv.org/abs/1606.07911),
  studies sums \(\sum_{n<N}e_m(ab^n)\). The fixed-prime-support theorem
  assumes all factors of \(m\) lie in one fixed finite set and
  \((b,m)=1\); its nontrivial range is still of order
  \(\exp(\log m/\log_2\log m)\), far above the present
  \(H=\Theta(\log m)\). The actual high product has unbounded prime
  support. In (CF28), base 5 is coprime only after making the modulus vary
  with \(u\), while the fixed-modulus representation has nonunit base 10;
  neither meets the theorem's fixed-modulus coprime-base premise. Even a
  hypothetical estimate for that factor alone would leave the unbounded
  odd product (CF30).
- Jean Bourgain and Mei-Chu Chang,
  [*Exponential Sum Estimates over Subgroups and Almost Subgroups of
  \(\mathbb Z_q^*\), where \(q\) is Composite with Few Prime Factors*](https://doi.org/10.1007/s00039-006-0558-7),
  Corollary 4.5, requires a bounded total prime-power factor count,
  \(N>q^\delta\), and projected orders \(>q^\delta\). The active modulus
  (CF30) has \(\gg M/\log M\) factors and \(H=\Theta(\log q)\); the full
  modulus also contains the nonunit dyadic factor.
- Bryce Kerr,
  [*Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170),
  gives nontrivial prime-modulus estimates on almost every nonexceptional
  local high-prime projection once the order hypothesis from the frozen
  Erdős--Murty audit is imposed. Those hypotheses are genuinely satisfied
  locally. The theorem does not permit multiplication by the dyadic,
  small-prime, and all-other-prime weights in (CF35).
- Bailey--Borwein--Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9),
  supplies the four-pole series used to construct \(B_M\). It supplies no
  decimal distribution or complement-Fourier estimate.

No checked primary theorem gives a nontrivial estimate for (CF36), for the
selected coefficient in the frozen TS39, or for any one of the complete
weighted correlations in (CF24). This is a bounded applicability record,
not an exhaustive or novelty claim.

## 8. Standalone replay

The [checker](bbp_complement_fourier_attack_20260813_check.py), SHA-256
4edba7339272813f152dbb9fb2a4af1ef8d8bd8ab76d4a28d45e1eee8494ff4c,
imports no other branch checker. Exact integers and gmpy2.mpq are used for
the BBP rational, denominator factorization, all CRT coordinates, the
reciprocal lift, the static five-primary phase, the six-period grid, every
nine-block congruence, every dyadic correlation valuation, and every
high-prime annihilation budget at harmonic \(h=1\). It also checks the two
exact representations in (CF28), not only their valuations. Floating FFTs
are confined to the labelled finite energy diagnostics.

Run from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_complement_fourier_attack_20260813_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_complement_fourier_attack_20260813_check.py

The retained run reports:

    status=PASS
    bounded_claim_label=experiment
    analytic_claim_label=proof sketch
    literature_claim_label=literature-checked
    denominator_factor_checks=3163
    high_coordinate_checks=2496
    reciprocal_lift_checks=2496
    full_phase_decomposition_checks=819
    nine_block_primary_checks=819
    primary_fourier_support_checks=819
    nine_block_energy_checks=546
    selected_fourier_energy_checks=546
    active_high_correlation_checks=19947
    high_annihilation_budget_checks=24
    dyadic_correlation_valuation_checks=3276
    dyadic_fixed_modulus_identity_checks=3276
    five_correlation_cancellation_checks=3276
    exact_record_sha256=c2b4d4f305958430abad628fd8370e3bb00416491e22621cfa4293dc23178190
    asserts_selected_complement_bound=false
    asserts_full_phase_cancellation=false
    asserts_fixed_return=false
    asserts_v1=false

Every bounded row and floating transform has label *experiment*; none is an
all-depth proof.

## 9. Coordination record and sharp handoff

This branch registered the descendant-area watch
ultrapi-complement-fourier-20260813 on local:pi-digits for agent
codex-ultrapi-complement-fourier. Its initial poll was empty at cursor and
delivered sequence 57,341, so no event was acknowledged. Observation events
are coordination signals only and were not used as mathematical evidence.

The exact sparse primary transform is useful, but its benefit is now
calibrated correctly. It compresses the unresolved calculation to the
nine-block inner product (CF36); it does not make the complement low-energy.
Even ideal off-diagonal mixing leaves one ninth of the complement energy in
the selected class, and every block correlation retains both a very deep
dyadic component and at least \(e^{(4.636+o(1))M}\) of high-prime modulus.

The next viable analytic target is therefore not another marginal or energy
bound. It is a phase-sensitive estimate for the actual product (CF35),
uniform under the six harmless twists (CF34), or a direct estimate of
(CF36). No such estimate is obtained here, so canonical V1 remains a
*conjecture*.
