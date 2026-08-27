# Independent audit: BBP complementary Fourier coefficient

Audit date: **2026-08-13 UTC**

## Verdict and claim boundary

**PASS on the frozen primary snapshot, with one important nonfatal
interpretive clarification and no fatal mathematical defect found.** The
factor \(16\) and every sign in (CF12), the support and complement classes in
(CF18)--(CF23), the one-ninth diagonal energy, both dyadic presentations in
(CF28), the coefficient \(1151/405\), and the annihilated-prime budget in
(CF30)--(CF31) were independently re-derived.

The all-depth identities retain label **proof sketch**. The independent
finite replay has label **experiment**. The direct source-applicability check
has label **literature-checked**. This audit adds no Lean declaration and no
**machine-checked** claim. It proves no decay of the selected complementary
coefficient, no fixed-sixteen return, and no decimal word theorem. Canonical
V1 remains a **conjecture**; this is neither a **candidate resolution** nor a
**verified resolution**.

The nonfatal clarification is precise. Prime annihilation in (CF30) is exact
for the original high-prime CRT factor, equivalently for the *recombined*
\(J_M/105+H_M\) factor. It is not generally true for the reciprocal lift
\(H_M\) in isolation: after the prime \(p\) cancels, a denominator dividing
105 can remain and is canceled by the matching \(J_M/105\) contribution.
Read in the recombined sense used to obtain (CF32), the primary argument is
correct.

## Frozen inputs

| input | SHA-256 |
|---|---|
| [canonical source](../../problems/local/pi-digits.txt) | 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825 |
| [primary report](bbp_complement_fourier_attack_20260813.md) | eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a |
| [primary checker](bbp_complement_fourier_attack_20260813_check.py) | 4edba7339272813f152dbb9fb2a4af1ef8d8bd8ab76d4a28d45e1eee8494ff4c |
| [high-prime report](bbp_high_prime_phase_compression_20260813.md) | 47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564 |
| [large-sieve report](bbp_large_sieve_short_orbit_20260813.md) | 23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d |
| [Bourgain--Chang PDF](../theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf) | a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7 |
| [Kerr PDF](../theory/pi-long-lag-block-collision-decay/library/t70/kerr-1302.4170v1.pdf) | 9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd |
| [independent checker](bbp_complement_fourier_attack_20260813_independent_check.py) | 0415e9902c539a0ca9a09015dd8bd7794c15b2db580cf4b80e10ea6cb7c2caa4 |

The canonical source is Marcel's immutable local question and records no
external source URL; none is invented. Its quantifiers range over every
finite decimal word, including words with leading zeroes, and ask for at
least one contiguous occurrence in pi. This audit did not edit either
primary artifact, any formal source, audit/AxiomAudit.lean, TheoryLib.lean,
or ultrapi.md.

## 1. Exact CRT decomposition and the factor 16

Write

\[
 B_M=\frac{P}{2^K R},\qquad D=2^{K-4},\qquad
 w\equiv PR^{-1}\pmod D,\qquad c=\frac{P-Rw}{D}.
\]

Then \(P=Rw+Dc\), so there is an equality in the rationals, not merely a
congruence,

\[
 16B_M=\frac{P}{DR}=\frac wD+\frac cR.
\]

Because \(P\) and \(R\) are odd, \(w\) is odd. Reduction of \(P=Rw+Dc\)
modulo a prime dividing \(R\) shows \((c,R)=1\). For pairwise coprime
factors \(q\mid R\), the coordinate

\[
 \beta_q\equiv c(R/q)^{-1}\pmod q
\]

satisfies \(\beta_q(R/q)\equiv c\pmod q\), while every other coordinate
vanishes modulo \(q\). This proves the additive CRT sum (CF8) with positive
signs.

For a high-prime coordinate \(G=a/b\), the residue
\(\gamma\equiv ab^{-1}\pmod p\) obeys

\[
 \frac\gamma p\equiv\frac{\kappa(p)}b+\frac a{bp}\pmod1,
 \qquad \kappa(p)p\equiv-a\pmod b.
\]

Summing these identities gives exactly \(J_M/105+H_M\), including the sign
of the grid lift. Finally

\[
 A_n=\frac{10^n-16}{16}\in\mathbb Z,\qquad
 (10^n-16)B_M=A_n(16B_M).
\]

For \(n>v_M\), \(A_n=2^{n-4}5^n-1\equiv-1\pmod{5^{v_M}}\). Therefore the
five-primary term is \(-\beta_{5,M}/5^{v_M}\), while the three-primary,
dyadic, small-prime, \(J_M/105\), and \(H_M\) terms all retain positive
\(A_n\). This is precisely (CF12); there is no missing factor 16 and no sign
error.

The independent checker reconstructs the actual reduced BBP rationals at
\(e=4,6\) with the standard-library Fraction type, factors their
denominators without importing a branch utility, checks
\(16B_M=w/D+c/R\), and checks (CF12) directly at twelve endpoint
exponents. These bounded checks are **experiment**.

## 2. Nine-block sign, support, and complement frequency

Let \(q=3^e\), \(T=3^{e-2}\), and \(H=T/9=3^{e-4}\). The binomial expansion
gives

\[
 10^{mH}\equiv1+m3^{e-2}\pmod{3^e}\qquad(0\le m<9).
\]

Since \(10^u\equiv1\pmod9\), for

\[
 f(j)=e_q(h\beta A_{M+j}),\qquad
 a\equiv h\beta16^{-1}10^M\pmod9,
\]

one obtains

\[
 \frac{f(u+mH)}{f(u)}
 =e_q\!\left(h\beta16^{-1}10^{M+u}m3^{e-2}\right)
 =e_9(am).
\]

The sign in (CF18) is therefore positive. With the report's convention

\[
 \widehat f(k)=\sum_j f(j)e_T(-kj),
\]

the block character is \(e_9((a-k)m)\). Thus the primary transform is
supported on \(k\equiv a\pmod9\), not on \(-a\). In

\[
 \sum_j f(j)W(j)=\frac1T\sum_k\widehat f(k)\widehat W(-k),
\]

the selected complementary class is consequently \(-a\pmod9\). This
confirms the signs in (CF18)--(CF23).

The energy identity can also be checked without invoking the primary
transform. Write \(j=u+mH\) and \(k=b+9\ell\). Summation over
\(0\le\ell<H\) kills unequal \(u\)'s and leaves

\[
 E_b(W)=H\sum_{u<H}
 \left|\sum_{m=0}^8W(u+mH)e_9(-bm)\right|^2.
\]

At \(b=-a\), the inner character is \(e_9(am)\), exactly \(D_aW(u)\).
Equation (CF19) and ordinary Cauchy--Schwarz now give directly

\[
 |S_{M,h}|^2
 \le H\sum_{u<H}|D_aW(u)|^2
 =E_{-a}(W),
\]

so (CF23) has the correct normalization as well as the correct sign.

## 3. Why diagonal energy is exactly one ninth

Because every complementary factor has modulus one, the nine diagonal
terms in each square contribute \(9H\) after summing over \(u\). If all 72
ordered off-diagonal block correlations are \(o(H)\), then

\[
 \sum_{u<H}|D_aW(u)|^2=9H+o(H).
\]

Multiplication by the outer \(H\) in (CF22) yields

\[
 E_{-a}(W)=9H^2+o(H^2)=\frac{T^2}{9}+o(T^2),
 \qquad \frac{\sqrt{E_{-a}(W)}}T=\frac13+o(1).
\]

Thus the primary report's energy-only no-go is exact. Ordinary mixing does
not imply evacuation of the selected class; it leaves the random share
\(1/9\). This argument supplies no phase-sensitive estimate for (CF36).

## 4. The two dyadic representations and \(1151/405\)

For \(n=n_0+u\), \(n_0=M+sH\), \(d=rH\), and \(h=2^v h_0\) with \(h_0\)
odd,

\[
 A_{n+d}-A_n=2^{n-4}5^n(10^d-1).
\]

The dyadic correlation starts with denominator \(2^{K-4}\). Canceling the
power \(2^{n_0-4+v}\), common to the whole \(u\)-block, gives

\[
 e_{2^L}(\alpha10^u),\qquad
 L=K-n_0-v,\qquad
 \alpha=h_0w5^{n_0}(10^d-1),
\]

and \(\alpha\) is odd. Canceling the additional \(2^u\) pointwise gives the
equivalent phase

\[
 e_{2^{L-u}}(\alpha5^u).
\]

Hence the first presentation has fixed modulus but nonunit base 10; the
second has unit base 5 but a modulus depending on \(u\). The primary report
correctly refuses to treat either as a classical fixed-modulus unit-base
Korobov sum.

At the endpoint,

\[
 M=\frac{45T-13}{8},\qquad H=\frac T9=\frac{8M+13}{405}.
\]

Using the report's deliberately loose but valid bound
\(sH+u\le8H-1\),

\[
\begin{aligned}
 L-u
 &\ge3M-8H+1-v_2(M+1)-v_2(h)\\
 &=\frac{1151}{405}M+\frac{301}{405}
   -v_2(M+1)-v_2(h).
\end{aligned}
\]

This implies (CF29). The coefficient
\(1151/405=2.8419753086\ldots\) is correct. The orientation \(s+r\le8\)
actually gives \(s\le7\), so a slightly stronger constant is available; the
stated weaker bound is not a defect.

## 5. Prime annihilation, surviving mass, factor count, and primitivity

For an original high-prime CRT coordinate \(\gamma_p/p\), the correlation
coefficient at lag \(d=rH\) contains

\[
 h\gamma_p\,10^{n_0+u}(10^{rH}-1)16^{-1}\pmod p.
\]

Every \(\gamma_p\) is a unit. For fixed \(h\ne0\), once \(M>|h|\), every
prime \(p>M\) is coprime to \(h\); it is also coprime to 10 and 16. Hence
the local coefficient vanishes exactly when
\(p\mid10^{rH}-1\). This proves the \(h\)-primitivity assertion and explains
why no extra prime divisor of \(h\) need be removed from \(Q_{M,r}\) after
the stated threshold.

The annihilated-prime product is squarefree and divides the repunit, so

\[
 \sum_{\substack{p>M,\ p\mid R_M\\p\mid10^{rH}-1}}\log p
 \le\log(10^{rH}-1)<rH\log10\le8H\log10.
\]

Since \(8H=(64M+104)/405\), subtracting this from the frozen high-prime
mass \((5+o(1))M\) gives

\[
 \log Q_{M,r}\ge
 \left(5-\frac{64\log10}{405}+o(1)\right)M
 =(4.636134701354027\ldots+o(1))M.
\]

This is uniform over the fixed set \(1\le r\le8\). Moreover every high
denominator prime lies below \(8M+5\). Therefore

\[
 \omega(Q_{M,r})
 \ge\frac{\log Q_{M,r}}{\log(8M+5)}
 \ge(4.636134701\ldots+o(1))\frac{M}{\log M}.
\]

Thus the assertion that the number of active prime factors is unbounded,
indeed \(\gg M/\log M\), follows from the stated inputs and is not merely a
finite observation. At each active prime the local coefficient is nonzero;
CRT therefore combines the active factors into
\(e_{Q_{M,r}}(\xi10^u)\) with \((\xi,Q_{M,r})=1\).

As noted in the verdict, this exact cancellation and recombination must be
applied to the original high-prime factor. In the lifted notation, the
\(J_M/105\) and \(H_M\) correlations must be recombined first. This does not
alter \(Q_{M,r}\), its mass, its factor count, or the primitive coefficient.

## 6. Primary-literature applicability

### literature-checked

Direct-check date: **2026-08-13 UTC**.

- Vandehey, [*Differencing Methods for Korobov-type Exponential
  Sums*](https://arxiv.org/abs/1606.07911), studies
  \(\sum_{n\le N}e_m(ab^n)\). The fixed-prime-support result requires the
  prime divisors of \(m\) to lie in one fixed finite set and requires
  \((b,m)=1\). Its advertised nontrivial scale is of order
  \(\exp(\log m/\log_2\log m)\), still much larger than the present
  \(\Theta(\log m)\) block. The fixed-modulus form in (CF28) has nonunit
  base 10; the unit-base form has varying modulus. The exclusion is correct.
- Bourgain--Chang,
  [*Exponential Sum Estimates over Subgroups and Almost Subgroups of
  \(\mathbb Z_q^*\), where \(q\) is Composite with Few Prime
  Factors*](https://doi.org/10.1007/s00039-006-0558-7), define “few prime
  factors” using a bounded number of prime factors, each \(>q^\varepsilon\).
  Corollary 4.5 also assumes \(t>q^\delta\) and every projected order
  \(>q^\delta\). Here \(\omega(Q_{M,r})\gg M/\log M\) and
  \(H=\Theta(\log Q_{M,r})\), so both the factor-count and polynomial-length
  hypotheses fail. In addition,
  \(\operatorname{ord}_p(10)\le p-1\le8M+4=o(Q_{M,r}^{\delta})\), so the
  projected-order premise fails for every fixed \(\delta>0\). The primary
  report's non-applicability conclusion is correct; the lower bound for
  \(\omega(Q_{M,r})\) is derived in Section 5.
- Kerr, [*Incomplete exponential sums over exponential
  functions*](https://arxiv.org/abs/1302.4170), Theorem 2, concerns one
  prime modulus and one unweighted sequence \(e_p(\lambda g^n)\), with
  \(N\le\operatorname{ord}_p(g)\) in its stated form. The frozen large-sieve
  audit handles complete cycles and the nonexceptional local-order input.
  Those local estimates do not permit multiplication by the dyadic,
  small-prime, and all-other-prime phases. Thus they do not estimate (CF35)
  or (CF36).
- Bailey--Borwein--Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic
  Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), supplies the
  four-pole identity behind \(B_M\), not a decimal-distribution theorem or a
  selected complementary Fourier bound.

No checked primary theorem supplies the synchronized, phase-sensitive
estimate required by (CF36). This is a bounded applicability record, not an
exhaustive search or a novelty claim.

## 7. Disjoint replay

The [independent checker](bbp_complement_fourier_attack_20260813_independent_check.py)
uses only the Python standard library. It imports neither the primary checker
nor NumPy nor gmpy2. It constructs the actual \(e=4,6\) BBP rows with exact
rationals; checks the CRT and reciprocal lift; checks the factor 16 and all
signs in (CF12); verifies the nine-block support and complement classes by
exact residue counts; verifies the one-ninth diagonal by integer counting;
embeds both sides of (CF28) into the original dyadic modulus; and checks every
lag's killed and active high-prime products for four fixed harmonics.

The primary checker was separately compiled and replayed. It returned
status=PASS and exact record
c2b4d4f305958430abad628fd8370e3bb00416491e22621cfa4293dc23178190.
The independent checker returned:

    status=PASS
    bounded_claim_label=experiment
    analytic_claim_label=proof sketch
    literature_claim_label=literature-checked
    denominator_factor_checks=456
    sixteen_scaling_checks=2
    local_lift_checks=354
    odd_crt_checks=2
    reciprocal_denominator_checks=354
    cf12_phase_checks=12
    cf18_sign_checks=450
    primary_support_class_checks=90
    cf22_kernel_sign_checks=810
    one_ninth_diagonal_checks=10
    cf28_two_representation_checks=1440
    active_high_coordinate_checks=11296
    killed_high_coordinate_checks=32
    annihilation_product_checks=16
    constant_checks=4
    epoch_4=M49,T9,H1,high47,high_bits345,J35
    epoch_6=M454,T81,H9,high307,high_bits3233,J27
    exact_record_sha256=845304289ec54327dfe80ea79e42413eee213b2fe4c6364927ee3e7eaf07ea38
    imports_primary_checker=false
    asserts_selected_complement_bound=false
    asserts_full_phase_cancellation=false
    asserts_fixed_return=false
    asserts_v1=false

Every bounded calculation remains **experiment**. The checker does not turn
the all-depth denominator asymptotic, the source theorems, or the missing
phase estimate into a finite computation.

## 8. Sharp conclusion

The frozen branch has correctly isolated a genuine obstruction. Sparse
three-primary support compresses the full sum to a nine-block pairing, but
ordinary complement mixing leaves one ninth of the energy in the selected
class. Every block correlation also retains a deep dyadic factor and a
primitive odd modulus with \(\gg M/\log M\) active prime factors. None of
these statements supplies cancellation of the synchronized product.

The next mathematical target remains the primary report's (CF36), or an
equivalent phase-sensitive estimate for the actual product (CF35), uniformly
under the six bounded grid twists. No such estimate is obtained here, so V1
remains a **conjecture**.
