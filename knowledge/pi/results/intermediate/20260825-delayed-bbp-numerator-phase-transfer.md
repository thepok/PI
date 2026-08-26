# Delayed BBP transfer to actual numerator phases

Status: `machine-checked` (the exact T154--T155 arithmetic identities and
horizon-uniform phase-transfer bounds and the exact T159 top-band prime
projections, plus the exact T160 two-factor decimal resonance and its delayed
value/numerator-phase transfer bounds, and the exact T161 safe-block
unique-pole/projection/valuation statements, the exact T162 lower minus-band
projections, and the exact T163 even-depth dyadic lift statements listed
below); `proof sketch` (the
explicit `nu_k <= 4*k`
burn-in, its use to discharge the logarithmic hypothesis, the
coefficient-summed corollary, the predecessor/residue CRT identity, the
finite-local polynomial-division obstruction, the general reciprocal-profile
adaptation, the scalar Hausdorff/TP2 diagnostic, and the critical
truncation-overlap law, including its all-finite-product and moving-horizon
generalizations, plus the BA sharp-tail and terminal-prime analysis and the
BC/BD shadow boundaries below)

Date: 2026-08-25 UTC

This note records the independently audited positive part of the ChatGPT Pro
AY memo. It narrows a moving-natural-window Fourier sum for the decimal
pi-orbit to phases of the actual reduced BBP truncations. Its exact arithmetic
and phase-transfer core is now machine-checked in
[`T154`](../../../../TheoryLib/PiQuantitativeBlockHitting/T154T154DelayedBBPFivePrimary.lean)
and
[`T155`](../../../../TheoryLib/PiQuantitativeBlockHitting/T155T155DelayedBBPPhaseTransfer.lean).
The exact top-band subset of the later reciprocal-prime adaptation is checked
in
[`T159`](../../../../TheoryLib/PiQuantitativeBlockHitting/T159T159ExactBBPTopPrimeProjection.lean).
The exact two-factor decimal-resonance transfer is checked in
[`T160`](../../../../TheoryLib/PiQuantitativeBlockHitting/T160T160DelayedBBPDecimalResonance.lean).
The exact terminal-prime safe-block subset is checked in
[`T161`](../../../../TheoryLib/PiQuantitativeBlockHitting/T161T161SafeLaterBBPPrimeProjection.lean).
The exact lower minus-band projections are checked in
[`T162`](../../../../TheoryLib/PiQuantitativeBlockHitting/T162T162ExactBBPMinusPrimeProjection.lean),
and the even-depth dyadic conductor and immediate-lift localization in
[`T163`](../../../../TheoryLib/PiQuantitativeBlockHitting/T163T163EvenBBPDyadicLift.lean).
It is not the whole T139 consumer and proves no cancellation or V1
consequence. Later sections also retain the scoped proof-sketch conclusion of
the AY follow-up and the broader adaptation from the independently audited AZ
follow-up. Except for the explicitly identified T159, T160, and T161 subsets,
those later statements are not promoted to the verified core.

## Setup and logarithmic burn-in

Let

\[
B_m=\sum_{j=0}^{7m}\frac1{16^j}
\left(\frac4{8j+1}-\frac2{8j+4}-\frac1{8j+5}-\frac1{8j+6}\right),
\qquad
10^mB_m=\frac{P_m}{D_m}
\]

in lowest terms with `D_m > 0`, and put

\[
\rho=\frac{10}{16^7}=\frac5{2^{27}}.
\]

The machine-checked T106 tail bound and the strongest T141 valuation statement
give

\[
0<10^m(\pi-B_m)<\rho^m,
\qquad
5\nmid D_m,
\qquad
5^{m-\operatorname{Nat.log}_5(56m+5)}\mid P_m
\quad(m\ge2).
\]

For a decimal scale `q = 10^k`, define the exact integer burn-in

\[
\nu_k=\min\{n\in\mathbb N:5^n\ge224k\}.
\]

The following explicit simplification remains a `proof sketch`: `nu_k <= 4k`,
and for every `n >= nu_k`, with `m=n+k`,

\[
\operatorname{Nat.log}_5(56m+5)\le n,
\qquad 5^k\mid P_m.
\]

The informal derivation observes that, at `n=nu_k`,

\[
56(n+k)+5\le285k<1120k\le5^{n+1},
\]

and this strict inequality persists as `n` increases. T141 then gives the
claimed divisibility. T154 does not formalize this `nu_k` estimate; it assumes
the exact theorem-friendly logarithmic inequality. Thus, at `proof sketch`
level, the linear burn-in obtained from the simpler `5^ceil(m/2) | P_m`
corollary improves to `O(log k)`.

## Exact actual-numerator phase

Under the exact hypotheses

```text
2 <= n+k
Nat.log 5 (56*(n+k)+5) <= n,
```

T154 machine-checks `delayed_scaledBBPRat_five_arithmetic`, including
`5^k | P_(n+k)`, and
`scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator`. Set

\[
U_{n+k}=\frac{P_{n+k}}{5^k}\in\mathbb Z.
\]

T154's `delayed_bbpPartial_eq_num_div_two_pow_den` and T155's
`delayedBBPValue_eq_num_div_two_pow_den` and
`phase_delayedBBPValue_eq_delayedBBPNumeratorPhase` then machine-check the
exact identities

\[
\boxed{
10^nB_{n+k}=\frac{U_{n+k}}{2^kD_{n+k}},
\qquad
e(h10^nB_{n+k})
=e_{2^kD_{n+k}}(hU_{n+k}).}
\]

Here T154 machine-checks that `5` does not divide `D_(n+k)`, so the displayed
`2^k D_(n+k)` is a valid five-free denominator for the phase. It need not be
the reduced or minimal phase modulus: powers of two may still cancel against
`h U_(n+k)`. The additional reduced-coprimality observation is not promoted
beyond `proof sketch` here.

This identity uses the actual numerator and denominator of the sevenfold BBP
truncation, not merely a finite five-adic residue fiber. T141 removes the
five-primary factor from this presentation; it does not control the remaining
Archimedean phase.

## Horizon-uniform delayed natural-window transfer

Let `x_r = fract(10^r * pi)`. T155 first machine-checks the exact rescaling
`abs_piPoint_sub_delayedBBPValue` and the natural-window pointwise estimate
`norm_phase_pi_sub_delayedBBPValue_lt`. Its theorem
`norm_sum_phase_pi_sub_delayedBBPValue_lt` proves, for `N>=1` and every
integer `h` in the natural window

\[
|h|\le2\cdot10^k-1,
\]

the horizon-uniform comparison with the delayed real BBP values. Under the
pointwise exact burn-in hypotheses

```text
forall j < N,
  2 <= (n+j)+k /\ Nat.log 5 (56*((n+j)+k)+5) <= n+j,
```

`norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_lt` machine-checks the literal
actual-numerator-phase form

\[
\boxed{
\left|
\sum_{j=0}^{N-1}e(hx_{n+j})
-\sum_{j=0}^{N-1}
 e_{2^kD_{n+k+j}}(hU_{n+k+j})
\right|
<\frac{4\pi\rho^{n+k}}{1-\rho}.}
\]

The formal proof uses the pointwise T106 estimate

\[
|e(h10^{n+j}\pi)-e(h10^{n+j}B_{n+k+j})|
\le 2\pi\frac{|h|}{10^k}\rho^{n+k+j}
<4\pi\rho^{n+k+j};
\]

and sums the geometric tail. Its independence from `h` holds
only after imposing the displayed natural window; outside that window the
unsimplified estimate retains the factor `|h|/10^k`. Its independence from
the horizon `N` is genuine.

Specializing the exact logarithmic hypotheses from merely `n>=nu_k` still
uses the unformalized burn-in argument above and therefore remains a `proof
sketch`.

At `proof sketch` level, the triangle inequality consequently gives, for
arbitrary complex coefficients supported on
`0 < |h| <= 2q-1`,

\[
\left|
\sum_hc_h\sum_{j<N}e(hx_{n+j})
-\sum_hc_h\sum_{j<N}e_{2^kD_{n+k+j}}(hU_{n+k+j})
\right|
<\frac{4\pi\rho^{n+k}}{1-\rho}\sum_h|c_h|.
\]

This transfers a delayed signed natural-window sum, including a
target-centred coefficient vector, but does not by itself discharge the
initial segment, endpoint decomposition, or quantifiers of the complete T139
hit consumer.

## Exact predecessor/residue coupling

Status in this section: `proof sketch`; T154--T155 do not formalize this CRT
identity.

Write

\[
\frac{P_m}{D_m}=J_m+\frac{r_m}{D_m},
\qquad 0\le r_m<D_m.
\]

Since `5^k | P_m` and `5` does not divide `D_m`,

\[
J_m\equiv-r_mD_m^{-1}\pmod{5^k}.
\]

For `0 <= s < 2^k`, `0 <= t < 5^k`, and the natural-window lift
`h=5^k s+2^k t`, the matched predecessor/residue/successor characters collapse
exactly to the same actual numerator phase:

\[
e_{2^k}(s(J_m-w_2))
e_{5^k}(t(-r_mD_m^{-1}-w_5))
e_{10^k}\!\left(h\frac{r_m}{D_m}\right)
=e_{10^k}(-hw)e_{2^kD_m}(hU_m),
\]

where `w_2=w mod 2^k` and `w_5=w mod 5^k`. This is an arithmetic realization
of an ordinary natural-window frequency, not a new frequency algebra and not
a bypass of T139's primitive-ray reduction.

## Finite-local forcing reduction

Status in this section: `proof sketch`; this is the compact conclusion of the
independently audited AY follow-up and is not Lean-checked. It adds an exact
identity for the actual BBP sequence, but no positive cancellation estimate.

Put `R_m=10^m B_m=P_m/D_m`, let `E` be the forward shift, and write the exact
forcing and tail coboundary as

\[
F_m=R_{m+1}-10R_m=10\tau_m-\tau_{m+1}.
\]

For every `C(X)=sum_(r=0)^R c_r X^r` in `Z[X]`, set

\[
H=C(10),\qquad Q_C(X)=\frac{C(X)-C(10)}{X-10}\in\mathbb Z[X].
\]

Polynomial division by `X-10` gives the exact identities

\[
\boxed{C(E)R=C(10)R+Q_C(E)F},
\qquad
\boxed{Q_C(E)F=C(10)\tau-C(E)\tau}.
\]

Thus, for `q=10^k`, `m=n+k`, and `z_(n,k)=R_(n+k)/q`, the corresponding
finite product of delayed characters is simultaneously

\[
\prod_{r=0}^R e(c_r z_{n+r,k})
=e\!\left(\frac{H R_m+(Q_C(E)F)_m}{q}\right)
=e(H10^n\pi)
 e\!\left(-\frac{\sum_{r=0}^R c_r\tau_{m+r}}q\right).
\]

Because the tail is geometrically summable, this yields a finite-local
dichotomy. If `C(10)=0`, the products are a summable perturbation of `1`, so
their Cesaro averages tend to `1`, not `0`. If `C(10) != 0`, they remain a
summable perturbation of a nonzero fixed-pi character. At a T139
primitive-ray leaf whose earliest coefficient `c_0` is not divisible by ten,

\[
C(10)\equiv c_0\pmod {10};
\]

hence that surviving frequency is already decimal-primitive. For a general
nonzero `C(10)` divisible by ten, one must first perform the usual decimal-ray
reduction, including its finite endpoint terms; nonzero alone does not imply
primitive.

Consequently, the Archimedean forcing recurrence by itself cannot turn finite
character telescoping or finite-order van der Corput into the missing
cancellation: it gives either zero-frequency coherence or another nonzero
fixed-pi phase. Repeated differences of a single primitive character have
frequency `h * product_i (10^(r_i)-1)` and therefore stay primitive (with
`9^d` growth after `d` differences); this growth assertion is not being made
for arbitrary cross terms of a polynomial expansion.

This is incremental negative progress, not a closure of all finite BBP
arguments. It does not exclude finite arguments that also use exact nonlocal
relations among the actual numerators and denominators, cross-index
congruences, or the seven-term rational formula before it is collapsed to the
Archimedean recurrence. No primitive/off-diagonal estimate, T139 premise, or
V1 consequence is obtained.

## Reciprocal-prime profiles at the delayed phase

Status in this section: `machine-checked` only for the exact T159 top-band
subset stated next; `proof sketch` for the general quotient profiles,
middle bands, endpoint corrections, delayed CRT factorization, and all
cancellation discussion. This is the compact, independently audited part of
the ChatGPT Pro AZ follow-up. The general `p^2` localization,
height-protected survival, and simultaneous high-prime CRT skeleton are **not
new here**: they were already derived in
[`bbp_actual_odd_quotient_attack.md`](ultrapi-campaign/bbp_actual_odd_quotient_attack.md),
especially (27a)--(27b), and compressed further in
[`bbp_high_prime_phase_compression_20260813.md`](ultrapi-campaign/bbp_high_prime_phase_compression_20260813.md).
The new adaptation packages the clean sampled-depth localization into two
quotient profiles and connects it literally to the T154--T155 numerator
phase.

### Exact T159 top-band subset

Let `m,i,p in Nat`, assume that `p` is prime, `5<p`, and

```text
56*m+6 < 2*p.
```

For the first pole family additionally assume `p<=56*m+1` and `p=8*i+1`;
for the third pole family assume `p<=56*m+5` and `p=8*i+5`. In module
`Theory.PiDigits.T159ExactBBPTopPrimeProjection`, theorems
`bbpPartial_topPrimeProjection_one` and
`bbpPartial_topPrimeProjection_three` machine-check, respectively,

\[
 \operatorname{PrimeCongruent}_p
   \bigl(p\,\operatorname{bbpPartial}(7m),4\bigr).
\]

Here `PrimeCongruent p x y` means `x=y` or
`1<=padicValRat p (x-y)`. The scaled theorems
`scaledBBPRat_topPrimeProjection_one` and
`scaledBBPRat_topPrimeProjection_three` give the same exact residue for both
top pole families:

\[
 \boxed{\operatorname{PrimeCongruent}_p
   \bigl(p\,\operatorname{scaledBBPRat}(m),4\cdot10^m\bigr).}
\]

Finally, `scaledBBPRat_topPrime_val_eq_neg_one` and
`scaledBBPRat_topPrimeThree_val_eq_neg_one` prove, under the corresponding
hypotheses,

\[
 \boxed{\operatorname{padicValRat}_p
   (\operatorname{scaledBBPRat}(m))=-1.}
\]

The strict top band itself rules out a second multiple of `p`; T159 assumes
neither a general middle-band profile nor the clean-endpoint hypotheses used
below. It does not machine-check a delayed `U_m` CRT phase or any cancellation
estimate.

Keep the sampled notation above and write `X_m=56m`. For `L>=0`, define

\[
 C_+(L)=\sum_{\substack{r\ge0,\ s\in\{1,4,5,6\}\\8r+s\le L}}
 \frac{c_s}{16^r(8r+s)},
 \qquad (c_1,c_4,c_5,c_6)=(4,-2,-1,-1),
\]

and

\[
\begin{aligned}
 C_-(L)={}&-
 \sum_{\substack{r\ge0\\8r+2\le L}}\frac4{16^r(8r+2)}
 -\sum_{\substack{r\ge0\\8r+3\le L}}\frac2{16^r(8r+3)}\\
 &-\sum_{\substack{r\ge0\\8r+4\le L}}\frac2{16^r(8r+4)}
 +\sum_{\substack{r\ge0\\8r+7\le L}}\frac1{2\cdot16^r(8r+7)}.
\end{aligned}
\]

Fix `m in Nat` and a prime `p>5` satisfying

```text
p^2 > 56*m + 6,
p does not divide product_(t=1)^6 (56*m+t).
```

Put `L=floor(56*m/p)` and let `epsilon(p)=+` for `p=1 mod 4` and
`epsilon(p)=-` for `p=3 mod 4`. Reindexing the already recorded localization
gives the clean rational-value congruence

\[
 \boxed{p\,(10^mB_m)\equiv
 10^m C_{\varepsilon(p)}(L)\pmod p.}
\]

The congruence is in the `p`-local rationals after multiplication by `p`; it
is not a congruence of an arbitrarily chosen raw numerator. The first clean
hypothesis implies `L<p`, so all profile denominators are units modulo `p`.
If the second clean hypothesis is dropped, one explicit final pole term may
have to be added.
If `C_(epsilon(p))(L)` is nonzero modulo `p`, then `p` occurs to exponent one
in the reduced denominator `D_m`. Rational nonvanishing alone does not imply
this modular nonvanishing; the earlier height condition is still required
outside the already protected prime bands.

The Archimedean limits are

\[
 C_+(L)\longrightarrow\pi,
 \qquad C_-(L)\longrightarrow-\pi.
\]

The first is the ordinary BBP series. For the second, geometric summation
gives the proof-sketch identity

\[
 C_-(\infty)=\int_0^1
 \frac{-4x-2x^2-2x^3+\tfrac12x^6}{1-x^8/16}\,dx.
\]

Factoring numerator and denominator reduces the integrand to

\[
 -\frac{4x}{x^2-2x+2}+\frac2{x+\sqrt2}+\frac2{x-\sqrt2}.
\]

The antiderivative
`-2*log((x-1)^2+1)-4*arctan(x-1)+2*log|x^2-2|` has values `0` at `x=1`
and `pi` at `x=0`, proving `C_-(infinity)=-pi`. This real limit must not be
used as a modular phase approximation: reduction of a rational modulo `p`
uses its denominator inverse modulo `p`.

Now fix `k,n in Nat`, put `m=n+k`, and assume the exact T154 burn-in

```text
2 <= n+k,
Nat.log 5 (56*(n+k)+5) <= n.
```

Let `10^m B_m=P_m/D_m` be reduced and `U_m=P_m/5^k`. For every prime `p`
satisfying the clean hypotheses above and
`C_(epsilon(p))(floor(56*m/p)) != 0 mod p`, write `D_m=p*d_(m,p)`.
Then the new packaging specializes the exact T154 numerator phase to

\[
 \boxed{U_m(2^k d_{m,p})^{-1}\equiv
 10^n C_{\varepsilon(p)}(\lfloor56m/p\rfloor)\pmod p,}
\]

and, for every `h in Int`, CRT gives

\[
 e_{2^kD_m}(hU_m)=
 e_p\!\left(h10^nC_{\varepsilon(p)}(\lfloor56m/p\rfloor)\right)
 e_{2^kd_{m,p}}\!\left(hU_mp^{-1}\right).
\]

For a target left endpoint `A/10^k`, with arbitrary `A in Int`, the cleared
local numerator is `5^kU_m-A D_m`, so the `A D_m` term vanishes modulo every
such `p`. The same statement holds for the centre
`(A+1/2)/10^k` after clearing the factor two. Thus this particular local
prime component is target-independent. The valid conclusion is only that it
does not carry target dependence by itself: it may still contribute to a
target-signed estimate through its correlation with the complementary and
`q`-primary target characters and the target-dependent coefficient vector.
No independence or adversarial-correlation principle is available.

More generally, for `N>=1`, `|h|<=2*10^k-1`, and the displayed burn-in at
every `n+j` with `j<N`, T155 transfers the pi phase sum to these exact delayed
numerator phases with its horizon-independent error. The factorization above
may then be applied separately at every `m=n+j+k` and every prime satisfying
its stated local hypotheses. It does not supply a prime set stable in `j`, a
bound for the complementary characters, or cancellation of their product.

## Scalar forcing is a Hausdorff/TP2 diagnostic

Status in this section: `proof sketch`; no asymptotic determinant formula is
used. Put

\[
 F_m=10^{m+1}\sum_{r=1}^7 b_{7m+r},\qquad
 \rho=10/16^7,
\]

where `b_j` is the ordinary four-pole BBP summand. Since

\[
 \frac4{8j+1}-\frac2{8j+4}-\frac1{8j+5}-\frac1{8j+6}
 =\int_0^1x^{8j}(1-x)(x^2+2)(x^2+2x+2)\,dx,
\]

there is a positive measure `mu` on `[0,1]`, with support accumulating at
one, such that for every `m in Nat`

\[
 \boxed{F_m/\rho^m=\int_0^1t^m\,d\mu(t).}
\]

Consequently, for every `m,r in Nat`, the ordinary forward difference obeys

\[
 (-1)^r\Delta^r(F_m/\rho^m)>0.
\]

In particular `0<F_(m+1)<rho*F_m`, the sequence is strictly log-convex,
`F_mF_(m+2)>F_(m+1)^2`, and `F_(m+1)/F_m` increases to `rho`. If
`F_(m,r)=10^(m+1)b_(7m+r)`, then for every `m in Nat` and
`1<=r<s<=7`, the direct double-integral comparison gives the strict TP2 law

\[
 F_{m,r}F_{m+1,s}-F_{m+1,r}F_{m,s}>0.
\]

This is a negative diagnostic only for the scalar real forcing and its seven
positive slices: their `rho`-adapted differences are one-signed and their
relative weights are monotonically ordered. It does not rule out arbitrary
weighted or modular combinations, nonlinear characters, or the coupled
prime-skeleton/complement correlation above. In particular it proves no
signed primitive estimate, T139 premise, or V1 consequence.

## Sharp four-pole bounds and terminal-prime compensation

Status in this section: `machine-checked` only for the six explicitly named
T161 safe-block unique-pole, rational-projection, and valuation statements
below. The sharp summand/tail/forcing bounds, improved transfer, reduced
cofactor congruence, short-order example, compensation, negligibility, and
off-diagonal consequences remain `proof sketch`. This compactly records the
independently audited ChatGPT Pro BA follow-up. Its original status discussion
predates the current verified core: T157 now checks the actual five-adic
statements, T158 the forcing identity and pulse laws, T159 the exact top-prime
projections, T160 the two-factor decimal-resonance transfer, and T161 the
safe-block subset just described. Source:
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-ba/turns/0002/answer.md`.

For `r>=1`, let the positive four-pole BBP summand be

\[
 b_r=\frac{120r^2+151r+47}
 {(2r+1)(4r+3)(8r+1)(8r+5)16^r}.
\]

Direct polynomial comparison gives the sharp-order bounds

\[
 \boxed{\frac1{8r^2 16^r}<b_r<\frac{15}{64r^2 16^r}.}
\]

With `rho=10/16^7`, `K_m=7m+1`,
`tau_m=10^m(pi-B_m)`, and
`F_m=10^(m+1)*sum_(r=7m+1)^(7m+7)b_r`, this yields, for every `m>=0`,

\[
 \boxed{\frac{\rho^m}{128K_m^2}<\tau_m<
 \frac{\rho^m}{64K_m^2}},\qquad
 \boxed{\frac{5\rho^m}{64K_m^2}<F_m<
 \frac{5\rho^m}{32K_m^2}}.
\]

In particular `F_(m+1)<2*rho*((7m+1)/(7m+8))^2*F_m`. If
`q=10^k`, `m=n+k`, and

\[
 \Phi(x)=\sum_{0<|h|<2q}c_h e(hx),\qquad
 \Lambda(\Phi)=\sum_h|c_h|,
\]

then for every finite horizon `R>=1`, the same delayed comparison as T155 has
the sharper proof-sketch bound

\[
 \boxed{\left|\sum_{r=0}^{R-1}\Phi(10^{n+r}\pi)
 -\sum_{r=0}^{R-1}\Phi(10^{n+r}B_{m+r})\right|
 <\frac{\pi\Lambda(\Phi)}{16(1-\rho)}
 \frac{\rho^m}{(7m+1)^2}.}
\]

This improves only the transfer error; it does not estimate the transferred
sum.

The terminal-prime safe-block core is now `machine-checked` in
`Theory.PiDigits.T161SafeLaterBBPPrimeProjection`. Fix `m>=1`, put `K=7m`,
and take either

- `p=56m+1` and `m<=t<=4m-1`; or
- `p=56m+5` and `m<=t<=4m`.

Theorems `caseOne_unique_terminal_pole` and
`caseThree_unique_terminal_pole` prove, throughout the corresponding stated
range, that the terminal first-pole denominator `8*(7m)+1=p`, respectively
third-pole denominator `8*(7m)+5=p`, is the unique denominator divisible by
`p` among all four pole families through index `7t`.

If `p` is prime, theorems `scaledBBPRat_safeLaterProjection_one` and
`scaledBBPRat_safeLaterProjection_three` prove in their respective ranges

\[
 \boxed{\operatorname{PrimeCongruent}_p
   \left(p\,\operatorname{scaledBBPRat}(t),4\,10^t\right)}.
\]

Theorems `scaledBBPRat_safeLaterVal_one` and
`scaledBBPRat_safeLaterVal_three` then prove

\[
 \boxed{v_p(\operatorname{scaledBBPRat}(t))=-1}.
\]

For clarity, the first range is exactly `m<=t<=4m-1` with
`p=56m+1`; the second is exactly `m<=t<=4m` with `p=56m+5`.

The further reduced-pair unpacking remains `proof sketch`: writing the actual
reduced rational as `R_t=10^tB_t=P_t/D_t` and `D_t=p*d_t`, `p` not dividing
`d_t`, it gives

\[
 \boxed{P_t\equiv4\,10^t d_t\pmod p}.
\]

Thus the fresh local factor at decimal scale `q=10^k` is exactly
`e_p(4h*10^(t-k))`. Its order need not be comparable with the safe-block
length: the certified example

\[
 p=4649=56\cdot83+1,\qquad 10^7\equiv1\pmod{4649}
\]

already has order dividing seven inside a block of length about `3*83`.

More decisively, remove the literal terminal pole

\[
 S_t=\frac{\sigma10^t}{p16^K},\qquad R_t^\circ=R_t-S_t.
\]

Here the remaining proof sketch takes `sigma=4` in the first case and
`sigma=-1` in the second.

The reduced denominator of `R_t^circ` is prime to `p`, and the exact cofactor
decomposition contains `e_p(-4h*10^(t-k))`, cancelling the fresh local factor
`e_p(4h*10^(t-k))`. The complete phase is therefore exactly

\[
 e(hR_t/q)=e(hR_t^\circ/q)e(hS_t/q).
\]

For a natural-window polynomial of coefficient load `Lambda`, summing the
literal-pole removal over any safe prefix costs less than

\[
 \frac{16\pi\Lambda}{9p}(1000\rho)^m
 \quad\text{in the first case},\qquad
 \frac{40\pi\Lambda}{9p}(1000\rho)^m
 \quad\text{in the second},
\]

where `1000*rho<1/20000`. Iterating
`R_(t+1)^circ=10R_t^circ+F_t` inside the block gives a forcing twist
`G_(t,ell)=sum_(j<ell)10^(ell-1-j)F_(t+j)` satisfying

\[
 \left|e(-vG_{t,\ell}/q)-1\right|
 <\frac{5\pi}{8}\,
 \frac{10^{\ell-1}\rho^t}{(7t+1)^2(1-\rho/10)}
 \qquad(0<|v|<2q).
\]

The scoped negative consequence is that neither the fresh `p`-character nor
the positive literal forcing supplies an independent source of primitive
cancellation: the former is exactly cofactor-compensated, while the literal
pole and forcing phases are quantitatively negligible on their safe block.
What remains is a block-dependent, pole-removed, target-signed correlation of
the actual `R_t^circ`; no sign or cancellation estimate is known for it.
Because both the prime and the resulting core depend on the chosen block,
this is only a diagnostic reduction of the live arithmetic problem. It proves
no T139 premise, density, normality, or V1.

## Exact lower minus-band projections and even-depth dyadic lift

Status in this section: `machine-checked` in T162 and T163.

For `m>=1`, let `p` be prime and

```text
14*m+1 < p <= 28*m+3.
```

T162 gives the complete `p=8*a+3` and `p=8*a+7` lower minus-band split. For
`p=8*a+3`, the quiet condition `56*m+1 < 3*p` leaves only the fourth-family
pole at `2*a` and gives

\[
 \operatorname{PrimeCongruent}_p
   (p\,\operatorname{scaledBBPRat}(m),-2\,10^m);
\]

the complementary active condition `3*p <= 56*m+1` adds the first-family
`3*p` pole at `3*a+1` and changes the residue to
`-(8/3)*10^m`. For `p=8*a+7`, the analogous quiet/active threshold is
`56*m+5 < 3*p` versus `3*p <= 56*m+5`; the secondary pole is then the
third-family pole at `3*a+2`, with the same respective residues `-2*10^m`
and `-(8/3)*10^m`. In all four cases T162 also proves the exact valuation

\[
 \boxed{v_p(\operatorname{scaledBBPRat}(m))=-1.}
\]

At every even depth `m`, T163 proves

\[
 v_2(\operatorname{scaledBBPRat}(m))=-27m.
\]

For positive even `m`, the reduced denominator therefore contains exactly
`2^(27*m)` and the reduced numerator is odd. Define

\[
 g_m=\frac{2\,5^{m-1}}{2^{27m}}.
\]

T163 proves for every `m>=1`, without a parity assumption, that

\[
 0<10^m\pi-\operatorname{scaledBBPRat}(m)<g_m.
\]

Consequently, at positive even depth the actual sampled BBP rational is the
unique point `scaledBBPRat(m)+z*g_m`, `z in Int`, in the immediate interval
`(10^m*pi-g_m,10^m*pi]`. This is exact localization of the actual rational;
it supplies no cancellation or T139 estimate.

## Exact-denominator and full-odd shadow boundaries

Status in this section: `proof sketch`; the shadow constructions themselves
are not Lean-checked.

The audited BC construction gives, for each **fixed** decimal delay `k` and
every prescribed word-omitting decimal carrier, reduced shadows with the
exact actual denominator `D_m` at every sufficiently large depth. They also
copy the specified five-primary, two-primary delayed, and exponentially large
odd local phase factors. The quantifiers matter: the construction is
eventual for one fixed `k`; it does not produce one shadow simultaneously
valid for all delays. Its numerators are selected depth by depth and do not
satisfy the literal seven-new-term/four-pole BBP recurrence or preserve the
complete actual numerator residue.

The audited BD construction is stronger in a different direction. At every
sampled depth `m>=2` it copies the entire actual odd denominator `R_m` and the
complete class of the actual rational in `Q_p/Z_p` for every odd prime. A
single word-omitting carrier can therefore be shadowed through all depths,
so completing all odd-prime projections cannot by itself force T139. The
shadow denominator is `2^(27*m)*R_m`; by T163 this is the exact actual
denominator at positive even depths, but no such all-depth exact-denominator
claim is available at odd depths. The shadow deliberately retains dyadic
freedom and again does not obey the literal BBP recurrence. Thus the surviving
fixed-pi information is the cross-depth coupling of the dyadic and full-odd
characters through the actual four-pole recurrence and target signs, not
either primary sector separately.

The BE cubic lag identity is a correct base-16 diagnostic, not progress on
this decimal frontier. It rewrites phases of
`e(m*(16^s-1)*16^n*pi)` with positive coefficient differences of cubic size,
but T139/T154/T155 require phases on the decimal carrier `10^n*pi`. The named
consumer asserted in that memo is absent from current main, and no abstract
base-16-to-base-10 transfer is valid. No BE statement is promoted here.

## Critical truncation overlap and its consumer mismatch

Status in this section: `machine-checked` only for the three explicitly named
T160 two-factor statements below; the overlap identity, tail and critical
scale, log-uniform law, all-finite-product/moving-horizon generalization, and
gauge diagnostic remain `proof sketch`. This is the compact conclusion of the
independently audited ChatGPT Pro BB memo. It concerns the actual four-pole
BBP summand with the sevenfold truncation schedule `j<=7m`. Source:
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bb/answer.md`,
with the transfer audit in
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bb/turns/0002/answer.md`.

Put

\[
 Y_m=10^mB_m,\qquad
 \Delta_{m,r}=Y_{m+r}-10^rY_m.
\]

For every `m,r in Nat`, direct subtraction gives the exact overlap identity

\[
 \boxed{\Delta_{m,r}=10^{m+r}(B_{m+r}-B_m)
 =10^{m+r}\sum_{j=7m+1}^{7(m+r)}16^{-j}a_j,}
\]

where

\[
 a_j=\frac4{8j+1}-\frac2{8j+4}-\frac1{8j+5}-\frac1{8j+6}.
\]

Thus, for every `h in Int`,

\[
 e(hY_{m+r})e(-h10^rY_m)=e(h\Delta_{m,r}).
\]

Strict positivity holds for `r>=1`; for `r=0`, `Delta_(m,0)=0`. More
generally, for integer coefficients `c_nu` and nonnegative lags `r_nu`,

\[
 \sum_\nu c_\nu Y_{m+r_\nu}
 =\left(\sum_\nu c_\nu10^{r_\nu}\right)Y_m
  +\sum_\nu c_\nu\Delta_{m,r_\nu}.
\]

The tail bound makes the last term

\[
 O\!\left(\frac{\rho^m}{m}
   \sum_\nu |c_\nu|10^{r_\nu}\right),
 \qquad \rho=10/16^7.
\]

Accordingly, for every fixed `epsilon>0`, bounded-order stencils with
`max r_nu <= (Lambda-epsilon)m` and total coefficient `l1` mass
`sum |c_nu|=exp(o(m))` collapse to the single frequency
`sum c_nu*10^(r_nu)`, where

\[
 \Lambda=\log_{10}(16^7/10).
\]

Equivalently, the exact requirement is that the weighted `l1` mass
`sum |c_nu|*10^(r_nu)` be at most
`10^((Lambda-epsilon)m+o(m))`; allowing unbounded stencil order or larger
mass is not covered. This retires only those bounded/subcritical linear
stencils, not all possible overlap arguments.

The tail asymptotic

\[
 \boxed{m^2 16^{7m}(\pi-B_m)=\frac1{3136}+O(m^{-1})}
\]

was already recorded, in equivalent notation, in
[`bbp_rational_phase_density_separator_20260813.md`](ultrapi-campaign/bbp_rational_phase_density_separator_20260813.md),
equation (10). It is not new to this memo. Its new use is to identify the
critical overlap window. Fix `tau in Real`, and choose `m_0(tau)` so that
`Lambda*m+2*log_10(m)+tau>=1` for every `m>=m_0(tau)`. On that eventual
domain define

\[
 r_m(\tau)=\left\lfloor
 \Lambda m+2\log_{10}m+\tau\right\rfloor,
 \qquad
 \theta_m(\tau)=\left\{
 \Lambda m+2\log_{10}m+\tau\right\}.
\]

Then `r_m(tau)>=1` on this eventual domain, and

\[
 \boxed{\Delta_{m,r_m(\tau)}
 =\frac{10^{\tau-\theta_m(\tau)}}{3136}+O_\tau(m^{-1}),}
\]

uniformly when `tau` ranges over a fixed compact interval. The irrationality
of `Lambda` and partial summation show that
`theta_m(tau)` is uniformly distributed modulo one. Hence the empirical
distribution of the overlap defect is log-uniform on

\[
 \left[\frac{10^{\tau-1}}{3136},
       \frac{10^\tau}{3136}\right],
\]

and for every fixed `h in Int`,

(after assigning arbitrary nonnegative lags at the finitely many earlier
indices, which does not affect the limit),

\[
 \lim_{M\to\infty}\frac1{M-m_0(\tau)+1}
 \sum_{m=m_0(\tau)}^M e(h\Delta_{m,r_m(\tau)})
 =\frac1{\log 10}
   \int_{10^{\tau-1}/3136}^{10^\tau/3136}\frac{e(hx)}x\,dx.
\]

A fixed `O(1)` shift below the critical window means a fixed negative value
of `tau`; its limiting interval remains nondegenerate and the defect does
**not** vanish. Vanishing follows only when the lag lies an unbounded amount
below the critical window (or after a separate limit `tau -> -infinity`).

The follow-up audit also gives the following explicit one-sided form of the
already-known tail constant: for every integer `m>=1`,

\[
 \boxed{0<\frac1{3136}-m^2 16^{7m}(\pi-B_m)<\frac1{3430m}.}
\]

This sharpened error bound remains a `proof sketch`; it is not a new
asymptotic constant or a machine-checked result.

The fatal limitation is a consumer mismatch. At a nontrivial decimal scale
`q=10^k` with `k>=1`, the T154--T155 delayed phase is

\[
 e(hY_m/q)=e(h10^nB_{n+k}),\qquad m=n+k.
\]

T155's natural-window transfer assumes `|h|<=2q-1`; the live T139 primitive
consumer further has `0<|h|` and `10` not dividing `h`.

The overlap limit instead concerns `e(hY_m)`, which is the delayed phase at
frequency `qh`, already divisible by ten when `k>=1`. Its second overlap
frequency is `q*10^(r_m(tau))*h`: for `r_m(tau)>=1` it is divisible by ten and
has magnitude at least `10q`, far outside the primitive natural window.
T155's natural-window error bound therefore cannot transfer this mixed phase
to pi. Indeed, replacing each truncation value `Y_m` by the exact pi value
`10^m*pi` makes the analogue identically

\[
 e\!\left(h(10^{m+r}\pi-10^r10^m\pi)\right)=1.
\]

The log-uniform cancellation is therefore a truncation-overlap phenomenon,
not an actual-pi off-diagonal estimate. No extraction inequality bridging it
to the low primitive T155 phases is supplied, and the displayed frequency
mismatch prevents treating such a bridge as routine. This section proves no
T139 premise, cancellation for the required consumer, or V1 consequence; it
also does not retire overlap methods that use different coupled information.

The follow-up audit makes this incompatibility quantitative for every finite
decimal-resonant product. Write

\[
 V_{d,n}=10^nB_{n+d},\qquad
 \Phi_{d,n}(g)=e(gV_{d,n}),\qquad
 \rho=10/16^7.
\]

The exact two-factor core is now `machine-checked` in
`Theory.PiDigits.T160DelayedBBPDecimalResonance`. For every `h in Int` and
`n,r in Nat`, theorem `pi_decimal_resonant_phase_product` proves

\[
 \operatorname{phase}(h,10^{n+r}\pi)\,
 \operatorname{phase}(-10^rh,10^n\pi)=1.
\]

For `k0,k1,n,r in Nat`, if

\[
 |h|<2\,10^{k1},\qquad |-10^rh|<2\,10^{k0},
\]

theorem `norm_delayedBBP_resonant_product_sub_one_lt` proves

\[
 \left\|\Phi_{k1,n+r}(h)\Phi_{k0,n}(-10^rh)-1\right\|
 <4\pi\left(\rho^{n+r+k1}+\rho^{n+k0}\right).
\]

Under the additional burn-in hypotheses

\[
 2\le n+r+k1,\quad \log_5(56(n+r+k1)+5)\le n+r,
\]

\[
 2\le n+k0,\quad \log_5(56(n+k0)+5)\le n,
\]

theorem `norm_delayedBBPNumerator_resonant_product_sub_one_lt` gives the same
bound with both `Phi` factors replaced by the corresponding actual
`delayedBBPNumeratorPhase` values. These three declarations establish only a
preselected resonant pair inside both transfer windows; they provide no
cancellation or abundance of such pairs.

The following arbitrary finite-product strengthening remains `proof sketch`.

Fix `n>=0` and `s>=1`. For each `1<=nu<=s`, let
`r_nu,d_nu in Nat` and `g_nu in Int`, and assume

\[
 |g_\nu|<2\,10^{d_\nu},\qquad
 \sum_{\nu=1}^s g_\nu10^{r_\nu}=0.
\]

Then the pointwise T155 transfer bound and a telescoping product estimate give

\[
 \boxed{\left|\prod_{\nu=1}^s
 \Phi_{d_\nu,n+r_\nu}(g_\nu)-1\right|
 <4\pi\sum_{\nu=1}^s\rho^{n+r_\nu+d_\nu}
 \le 4\pi s\rho^n.}
\]

When every corresponding T154 burn-in hypothesis holds, these factors are
literally the actual delayed numerator/denominator phases. The same estimate
holds pointwise when all lags, delays, and frequencies move with `n` while
`s` stays fixed. Consequently, for every `M,H>=1`, their block average is
within `4*pi*s*rho^M` of `1`, uniformly in `H` and in those moving choices.
Thus every fully T155-admissible decimal-resonant product is exponentially
coherent, including at target-dependent later horizons.

For the two-factor critical defect at common delay `d`, put `m=n+d`. Its
nondegenerate scale is not the undelayed lag above but

\[
 r_{d,n}(\tau)=d+\left\lfloor
 \Lambda m+2\log_{10}m+\tau\right\rfloor.
\]

At this scale the earlier resonant frequency has magnitude
`|h|*10^(r_(d,n)(tau))`, which eventually violates
`|g|<2*10^d` for every fixed nonzero `h`. Conversely, if both resonant
frequencies satisfy their T155 windows, the magnified tail is exponentially
small and the defect phase tends to `1`. Hence a nondegenerate critical
truncation defect necessarily exits at least one verified transfer window;
increasing the BBP delay cannot rescue both criticality and transferability.

There is also an exact information-loss obstruction. For any real `beta`,
fixed nonzero integer `h`, delayed errors `epsilon_(d,n)`, and arbitrary
moving lags `r_n`, set

\[
 a_n^{(\beta)}=e\!\left(h(10^n\beta-\epsilon_{d,n})\right).
\]

Then

\[
 a_{n+r_n}^{(\beta)}
 \left(\overline{a_n^{(\beta)}}\right)^{10^{r_n}}
 =e\!\left(h(10^{r_n}\epsilon_{d,n}-\epsilon_{d,n+r_n})\right),
\]

independently of `beta`. The critical-defect data is therefore blind to the
lacunary carrier gauge `a_n -> a_n*e(h*10^n*gamma)`. This is not a separator
preserving the actual BBP numerator/denominator coupling; it proves only that
defect data alone cannot recover the carrier needed by an extraction theorem.
The genuine same-frequency correlation still contains the uncontrolled
factor `e(h*(10^r-1)*V_(d,n))`, so exact cross-index carrier arithmetic remains
the hard input.

For completeness, the critical log-uniform law gives, for fixed nonzero `h`,
a mean-square distance from the exact-pi resonant product `1` equal in the
limit to `2-2*Re(I_h(A_tau))`; as `tau -> +infinity` this tends to the
decorrelated value `2`, not the pointwise maximum squared distance `4`.
This reinforces non-transfer rather than proving cancellation for T139 or V1.

## Machine-checked quadratic transfer and actual local arithmetic

T164 replaces the coarse exponential transfer constant by an explicit
quadratic one.  With

\[
 \Lambda_t=(56t+9)(56t+10),\qquad \rho=10/16^7,
\]

the actual sampled BBP error now satisfies the machine-checked finite bounds

\[
 \frac{\rho^t}{4\Lambda_t}<10^t(\pi-B_{7t})
 <\frac{\rho^t}{\Lambda_t}.
\]

Consequently T164 gives both pointwise and horizon-uniform T155 transfers
with the additional factor `1/Lambda_(n+k)`, including the literal delayed
numerator phase under the existing per-index burn-in.  This sharpens a real
verified bridge but does not bound the rational carrier itself.

T165 and T166 add two exact pieces of actual carrier arithmetic.  At positive
even depth `t=n+k`, under the T154 burn-in, T165 proves

\[
 \gcd\!\left(|U_{k,n}|,2^kD_t\right)=1
\]

and proves no alias between distinct frequencies throughout
`|h|<2*10^k`.  It also transports every verified T159--T162 prime projection
from `p*scaledBBPRat t` to the literal delayed coordinate

\[
 \frac{pU_{k,n}}{2^kD_t}\pmod p.
\]

T166 uses the valuation `v_p(scaledBBPRat t)=-1` to write `D_t=pE` with
`p` not dividing `E`, and removes the pole.  The delayed local coordinate is
then exactly

\[
 \frac{U_{k,n}}{2^kE}\equiv c10^n\pmod p,
 \qquad c\in\{4,-2,-8/3\},
\]

for the corresponding verified upper- and lower-band projections.  These are
genuine fixed-pi numerator/denominator consequences, not same-fiber data.
They isolate an explicit local factor of the target phase while leaving the
same-index complementary CRT factor uncontrolled.  Thus they do not yet
prove temporal cancellation, a T139 premise, density, normality, or V1.

## Cross-index stable factors and the forcing-cell no-go

Status: `machine-checked` in T168 for literal forcing support, odd-prime
integrality, valuation persistence, and equality-aware prime-power transport;
`proof sketch` for the composite cocycle, dyadic isometry, forcing-cell law,
and their stated limitations. These are the compact, independently audited
conclusions of the BC and BD follow-ups.

Write

\[
 Q_m=\frac{P_m}{D_m},\qquad F_m=Q_{m+1}-10Q_m,
\]

in lowest terms.  Over a finite block `m,...,m+R`, let
`L_(m,R)` be the product of the odd denominators occurring in the literal
seven new four-pole rows at each transition.  Let `S_(m,R)` be the product of
the complete prime powers `p^e || D_m` with `p != 2,5` and
`p` not dividing `L_(m,R)`.  The recurrence and strict ultrametric inequality
then transport all these old prime powers simultaneously.  For every
`0<=j<=R`, each `p^e || S_(m,R)` still has

\[
 v_p(Q_{m+j})=-e,
 \qquad
 p^eQ_{m+j}\equiv10^jp^eQ_m\pmod {p^e}.
\]

The congruence must use the equality-or-positive-valuation convention at
`j=0`: its two sides are exactly equal, while the repository's
`padicValRat 0` convention does not support replacing that equality by a
positive valuation assertion.  For `j>=1`, positivity of the intervening BBP
forcing makes the difference nonzero and the displayed valuation bound is
valid.

Writing `D_t=S_(m,R) E_t` with coprime factors, the actual composite residue

\[
 a_t\equiv P_tE_t^{-1}\pmod {S_{m,R}}
\]

obeys `a_(t+1)=10*a_t (mod S_(m,R))`.  If `q=10^k`, set

\[
 \Phi_t^{(k)}(h)=e(hQ_t/q),\qquad
 \chi_t^{(k)}(h)=e_{S_{m,R}}(h q^{-1}a_t),\qquad
 \psi_t^{(k)}(h)=\Phi_t^{(k)}(h)/\chi_t^{(k)}(h).
\]

Then the exact stable/complementary cocycle is

\[
 \chi_{t+1}^{(k)}(h)=\chi_t^{(k)}(10h),\qquad
 \psi_{t+1}^{(k)}(h)=
 \psi_t^{(k)}(10h)e(hF_t/q).
\]

This is simultaneous prime-power transport through the actual forcing, not a
collection of independent one-prime marginals.  It remains a factorization,
not a cancellation estimate for either factor.

The independently audited BD turn-0003 memo
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bd/turns/0003/answer.md`
adds one narrow `proof sketch` consequence.  Assume the sharp forcing bound
used below,

\[
 0<F_t<\frac{5}{32}\frac{\rho^t}{(7t+1)^2},
 \qquad \rho=\frac{10}{16^7},
\]

which follows from the displayed sharp bound for `delta_t` and
`F_t=mu_(t+1) delta_t`.  For `q=10^k`, `0<|h|<2q`, and every `m,N in Nat`,
the exact recurrence gives

\[
 \Phi_{m+j+1}^{(k)}(h)\,
 \overline{\Phi_{m+j}^{(k)}(10h)}=e(hF_{m+j}/q).
\]

Using `1-cos(theta)<=theta^2/2` and summing the resulting geometric tail gives

\[
 \boxed{
 \operatorname{Re}\sum_{j=0}^{N-1}
 \Phi_{m+j+1}^{(k)}(h)
 \overline{\Phi_{m+j}^{(k)}(10h)}
 >N-\frac{25\pi^2}{128(1-\rho^2)}
 \frac{\rho^{2m}}{(7m+1)^4}.}
\]

Thus the matched adjacent branches on a decimal frequency ray are nearly
maximally coherent, uniformly in the horizon.  This narrowly retires an
argument that averages those matched branches as if they were independent.
It supplies no control of the full target-signed off-diagonal sum.  In
particular, the repository has no shifted T139/T148 primitive consumer to
which this display can be passed directly; the scalar forcing coordinate is
only a lossless representation, not finite-memory progress.  No cancellation
estimate, T139/T148 premise, or V1 consequence follows.

T168 machine-checks this transport one prime power at a time, simultaneously
over every lag in any block whose literal innovation supports avoid that
prime. Its `PrimePowerCongruent` predicate deliberately has an equality
branch, so lag zero is represented correctly. The composite product `S_(m,R)`
and the `chi/psi` factorization below remain `proof sketch` rather than hidden
inside generic CRT infrastructure.

There is also a finite dyadic local cancellation statement retaining the
actual odd denominator inside the two-local unit.  At positive even `m`, put

\[
 W_m=2^{27m}Q_m=\frac{P_m}{R_m},\qquad
 \Gamma_m=W_{m+2}-25\,2^{56}W_m,
\]

where `D_m=2^(27m)R_m` and `R_m` is odd.  The audited two-adic divided-
difference argument gives, for distinct positive even `m,n`,

\[
 v_2(\Gamma_m-\Gamma_n)=v_2(m-n).
\]

Consequently, for positive even `M` and `K>=1`, the finite residues
`Gamma_(M+2j) mod 2^K`, `0<=j<2^(K-1)`, permute the odd residue classes, and
their additive-character sum is the Ramanujan sum `c_(2^K)(s)`.  This is only
a statement about the dyadic local character.  Although `Gamma_m` contains
the actual numerator and odd denominator in its two-local value, it does not
give cancellation for the simultaneous odd CRT character or for the full
Archimedean T155 phase.

The BD forcing-cell law makes the failure of recurrence-preserving full-odd
shadows exact.  For `m>=2`, write `D_m=2^(kappa_m)R_m`, with `R_m` odd, and
define

\[
 \mu_m=\frac{5^{m-1}}{2^{27m}}=\frac{\rho^m}{5},
 \qquad \mathcal O_m=Q_m+\mu_m\mathbb Z,
 \qquad B=2^{28}.
\]

The class `O_m` preserves the complete negative odd-primary principal parts,
that is, the image of `Q_m` in `Q_p/Z_p` for every odd prime.  It does not
preserve arbitrary positive p-adic digits.  Since `10*mu_m=B*mu_(m+1)`, the
normalized literal forcing

\[
 \delta_m=F_m/\mu_{m+1}
\]

satisfies the exact cell recurrence

\[
 u_{m+1}=Bu_m+\delta_m-\beta_m,qquad
 \beta_m=\lfloor Bu_m+\delta_m\rfloor,
\]

for the normalized residue `u_m in [0,1)`.  The seven-row BBP formula gives

\[
 \frac{5\,2^{21}}{(7m+1)^2}<\delta_m<
 \frac{5\,2^{22}}{(7m+1)^2}.
\]

Because `4586^2>5*2^22`, one has `0<delta_m<1` for every `m>=655`.
Thus

\[
 \beta_m=\lceil Bu_m-u_{m+1}\rceil,
 \qquad
 \delta_m=\{u_{m+1}-Bu_m\}
\]

from that depth onward.  If another sequence has
`Qhat_m in O_m`, write `Qhat_m-Q_m=mu_m*z_m`.  Its forcing satisfies

\[
 \widehat F_m-F_m=\mu_{m+1}(z_{m+1}-Bz_m).
\]

Hence two forcings in the same open cell `(0,mu_(m+1))` are equal.  If, for
one fixed `C`, this holds at every `m>=M>=655` and additionally

\[
 |\widehat Q_m-10^m\pi|\le C\rho^m,
\]

then `z_(m+1)=B*z_m`, while the approximation and actual BBP tail keep `z_m`
uniformly bounded.  Therefore every `z_m` is zero.  This is a genuine
cross-index rigidity/no-go: no nontrivial full-odd `O(rho^m)` shadow can also
preserve positive subcell forcing indefinitely.

These results do not reduce the live consumer to a solved scalar problem.
The singleton skew product treated in BC is only one constant-mass,
endpoint-free sector of the full T139 primitive polynomial; all other
primitive rays and their target signs remain.  At odd depths the convenient
`2^(27m+k)` dyadic modulus is an unreduced common-modulus representation, not
the actual conductor.  The scalar rational history `u_m` itself losslessly
encodes the large odd modulus and residue, and no target-signed `O(N/q)` bound
is proved for it.  Thus neither the local Ramanujan cancellation, the forcing
cell selection, nor the rigidity theorem supplies a T139/T148 premise or a V1
consequence.

## Fixed-future high-dyadic fibre averaging

Status: `proof sketch`.  Source: the independently audited BC turn-0003 memo
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bc/turns/0003/answer.md`.

This construction freezes one future actual BBP rational and averages only
artificial high dyadic lifts.  Fix `k>=3`, `q=10^k`, a target `a<q`,

\[
 L=4800(k+1)q,\qquad n\ge4k+6\ \text{even},\qquad T=n+L,
\]

and write the reduced future rational as

\[
 Q_T=10^TB_T=\frac{P_T}{D_T}.
\]

The T154 burn-in and the even-depth denominator law give

\[
 P_T=5^LU_T,\qquad D_T=2^{27T}R_T,\qquad
 R_T\ \text{odd},\qquad 5\nmid R_T,\qquad \gcd(U_T,2R_T)=1.
\]

The condition `5∤R_T` is essential here: it follows because `P_T/D_T` is
reduced and `5^L∣P_T`.  Put

\[
 A_T=27T+L,\qquad d=A_T-k-1,\qquad
 \lambda_t=1+2^{k+1}R_T5^kt\quad(0\le t<2^d).
\]

To make the endpoint bookkeeping legitimate, define the lifted decimal orbit
for every `j>=0`, not only on the averaging block,

\[
 z_j^{(t)}=\operatorname{fract}\!\left(
   \lambda_t10^{n+j}B_T\right).
\]

Then `z_(j+1)^(t)=fract(10*z_j^(t))`.  For `0<=j<L`, its phase calculation
uses the reduced denominator

\[
 2^{27T+L-j}R_T
\]

and gives, for every decimal-primitive frequency `u`,

\[
e(uz_j^{(t)})=e(uz_j^{(0)})
\cdot e_{2^d}(tU_T5^ku10^j).
\]

The explicit parameters satisfy the no-wrap hypothesis

\[
 4q10^{L-1}<2^d.
\]

Consequently the equality `u*10^j=v*10^r` among primitive frequencies in the
natural support forces `(j,u)=(r,v)`.  Thus, for arbitrary complex arrays
`c_(j,u), b_(j,u)` and

\[
 S_c(t)=\sum_{j<L}\sum_u c_{j,u}e(uz_j^{(t)}),
\]

the correctly conjugated fibre identities are

\[
 2^{-d}\sum_{t<2^d}S_c(t)=0,
\]

\[
 2^{-d}\sum_{t<2^d}S_c(t)\overline{S_b(t)}
 =\sum_{j<L}\sum_u c_{j,u}\overline{b_{j,u}}.
\]

For the actual T139 primitive coefficients `p_(q,a)(u)`, the audited
coefficient calculation gives the target-uniform estimate

\[
 \sum_u|p_{q,a}(u)|^2<\frac{31}{q}.
\]

Writing

\[
 Z_{n,k,a}(t)=\sum_{j<L}\sum_u p_{q,a}(u)e(uz_j^{(t)}),
\]

one therefore has the exact artificial-fibre second moment

\[
 2^{-d}\sum_{t<2^d}|Z_{n,k,a}(t)|^2
 =L\sum_u|p_{q,a}(u)|^2<\frac{31L}{q}.
\]

Chebyshev with the displayed value of `L` yields

\[
 \#\left\{t<2^d:\operatorname{Re}Z_{n,k,a}(t)
       \ge-\frac{L}{12q}\right\}
 >\frac{307}{400}\,2^d.
\]

The generic boundary consumer and its universal endpoint budget imply that
every such good lifted orbit hits the target cylinder during the length-`L`
block.  The distinguished lift `t=0` is the actual fixed-future BBP carrier;
if it satisfies the same lower bound, the T164 transfer gives an actual late
pi-orbit hit.  At the first allowed start `n=4k+6`, bounding the preceding
prefix separately also gives the literal unshifted T148 premise.

The fatal gap is that a subset of density greater than `307/400` need not
contain the distinguished point `t=0`.  Both the good set and its modulus move
with `n`, while their coefficients retain the changing actual odd state.  A
proof that the actual lift avoids these moving exceptional sets would itself
be a new target-signed fixed-pi estimate; it is not supplied by the fibre
average.  Hence this establishes no unconditional actual-pi T139 estimate,
proves no unconditional T148 premise or V1, and does not currently justify
Lean formalization of the lift or martingale package.

The later audited
[`fixed-future fibre de-randomization no-go`](../negative/20260826-fixed-future-bbp-fibre-derandomization-no-go.md)
closes one proposed repair of this gap: fibre majority plus the existing
fixed-modulus dyadic isometry and a supposedly harmless complementary CRT
state cannot select `t=0`.  Direct distinguished-point estimates and the full
unpaired moving-conductor problem remain open.

## Narrowed live arithmetic target

After the transfer, the hard delayed rational sum is

\[
\boxed{
\sum_{0<|h|\le2q-1}c_{q,w}(h)
\sum_{j=0}^{N-1}
e_{2^kD_{n+k+j}}(hU_{n+k+j}).}
\]

The transfer error is exponentially small and uniform in `N`; no bound of the
required sign or size is known for this actual `(U_m,D_m)` sum. Progress now
requires joint/off-diagonal information about the varying reduced BBP
numerators, denominators, and seven-term forcing. No fixed-pi cancellation,
T139 premise, density, normality, or V1 follows from this note.

## Verification boundary

The strict verifier and exact axiom audit accept the following declarations:

- T154: `delayed_scaledBBPRat_five_arithmetic`,
  `scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator`, and
  `delayed_bbpPartial_eq_num_div_two_pow_den`;
- T155: `delayedBBPValue_eq_num_div_two_pow_den`,
  `phase_delayedBBPValue_eq_delayedBBPNumeratorPhase`,
  `abs_piPoint_sub_delayedBBPValue`,
  `norm_phase_pi_sub_delayedBBPValue_lt`,
  `norm_sum_phase_pi_sub_delayedBBPValue_lt`, and
  `norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_lt`;
- T159: `bbpPartial_topPrimeProjection_one`,
  `bbpPartial_topPrimeProjection_three`,
  `scaledBBPRat_topPrimeProjection_one`,
  `scaledBBPRat_topPrimeProjection_three`,
  `scaledBBPRat_topPrime_val_eq_neg_one`, and
  `scaledBBPRat_topPrimeThree_val_eq_neg_one`;
- T160: `pi_decimal_resonant_phase_product`,
  `norm_delayedBBP_resonant_product_sub_one_lt`, and
  `norm_delayedBBPNumerator_resonant_product_sub_one_lt`;
- T161: `caseOne_unique_terminal_pole`,
  `caseThree_unique_terminal_pole`,
  `scaledBBPRat_safeLaterProjection_one`,
  `scaledBBPRat_safeLaterProjection_three`,
  `scaledBBPRat_safeLaterVal_one`, and
  `scaledBBPRat_safeLaterVal_three`;
- T162: `caseThree_quiet_unique_poles`,
  `caseThree_active_unique_poles`, `caseSeven_quiet_unique_poles`,
  `caseSeven_active_unique_poles`,
  `scaledBBPRat_minusThreeProjection_of_quiet`,
  `scaledBBPRat_minusThreeProjection_of_secondary`,
  `scaledBBPRat_minusSevenProjection_of_quiet`,
  `scaledBBPRat_minusSevenProjection_of_secondary`,
  `scaledBBPRat_minusThreeVal_of_quiet`,
  `scaledBBPRat_minusThreeVal_of_secondary`,
  `scaledBBPRat_minusSevenVal_of_quiet`, and
  `scaledBBPRat_minusSevenVal_of_secondary`;
- T163: `bbpPartial_eq_sum_combined`, `scaledBBPRat_two_val_even`,
  `scaledBBPRat_even_two_primary`, `scaledBBPRat_even_tail_lt_spacing`, and
  `scaledBBPRat_even_unique_immediate_lift`;
- T164: `bbpCombinedTerm_quadratic_bounds`,
  `real_bbp_tail_quadratic_bounds`, `sampledBBPError_quadratic_bounds`, the
  two sharpened pointwise phase-transfer theorems, and the sharpened delayed
  value and numerator-phase horizon theorems;
- T165: actual even-depth delayed-numerator coprimality and natural-window
  no-alias, the generic delayed prime-projection transport, and its concrete
  T159--T162 upper-, safe-later-, and lower-band corollaries;
- T166: multiplicity-one denominator decomposition, generic and actual
  delayed local-coordinate transport, and the `4`, `-2`, and `-8/3`
  residue wrappers;
- T168: exact seven-row innovation support, odd-prime forcing integrality,
  one-step and finite-block negative-valuation persistence, and equality-aware
  prime-power transport through the actual scaled BBP recurrence.

The explicit `nu_k<=4*k` derivation, predecessor/residue CRT identity,
finite-local polynomial reduction, general reciprocal-profile adaptation, and
Hausdorff/TP2 diagnostic, critical truncation-overlap law, and arbitrary
finite-product/moving-horizon extensions, as well as the remaining BA
asymptotic-limit, short-order, compensation, negligibility, and off-diagonal
claims and the BC/BD shadow constructions are not among these
declarations and remain `proof sketch`. No theorem listed here proves
cancellation, a T139 premise, density, normality, or V1.
