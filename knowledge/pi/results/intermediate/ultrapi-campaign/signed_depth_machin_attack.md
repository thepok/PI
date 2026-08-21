# Signed, depth-varying Machin shadows: a fixed-prime synchronization squeeze

Audit date: **2026-08-12 UTC**

Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)

Target SHA-256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No complete proof that every finite decimal word occurs in pi was obtained.
Canonical V1 remains a *conjecture*.

There is a scoped advance on the last escape left by
[the synchronized-return audit](machin_synchronized_return_attack.md).
Signed coefficients and different Taylor depths really can create
Archimedean cancellation. They still cannot rescue a rational shadow when
one fixed prime survives linearly in its reduced denominator.

> **Fixed-prime synchronization squeeze (proof sketch).** Fix an integer
> \(c\ge2\) multiplicatively independent of ten and a prime \(p\nmid10c\).
> Suppose reduced rationals \(A_j=P_j/q_j\), heights \(H_j\to\infty\), and
> exponents \(N_j\) obey
>
> \[
> q_j\mid10^{N_j}-c,\qquad v_p(q_j)\ge\kappa H_j,\qquad
> \log q_j\le C H_j                                      \tag{1}
> \]
>
> for fixed \(\kappa,C>0\). Then
>
> \[
>                         |\pi-A_j|\ne o(10^{-N_j}).       \tag{2}
> \]

Yu's fixed-\(p\) logarithmic-form estimate makes (1) force
\(N_j\ge\exp(\kappa'H_j)\), while the known finite irrationality measure of
pi gives \(|\pi-A_j|\ge\exp(-C'H_j)\). Thus the ratio in (2) tends to
infinity, irrespective of signed-tail cancellation.

Two exact signed identities are audited:

\[
 {\pi\over4}=3\arctan {1\over3}-\arctan {2\over11},       \tag{3}
\]

\[
 {\pi\over4}=6\arctan {1\over7}
                   -\arctan {1457\over22049},
 \qquad22049=17\cdot1297.                                 \tag{4}
\]

At equal depths, the largest argument in (3) gives an explicit lower bound.
At unequal depths, exact rational brackets certify relative cancellation
below \(1/4000\) at \((6209,4001)\) in (3), and below \(1/1400\) at
\((125,89)\) in (4). Nevertheless every fully reduced finite shadow checked
has \(q|\pi-A|>1\), by margins reaching \(10^{2514}\).

There is also a necessary correction. At maximum Taylor exponent \(2059\),
the two top 11-adic layers in the \(2/11\) series cancel once: the formal
maximum denominator score is 2059, but the exact reduced 11-primary exponent
is 2058. Therefore “the endpoint always survives” is false outside selected
depths. Infinite score-separated families are proved below; arbitrary
schedules still leave an all-depth p-adic gap.

The deductions below have status *proof sketch* and are not formalized in
Lean. The exact finite replay is an *experiment*. The source audit is
*literature-checked* as of the date above. Nothing here is a
*candidate resolution*.

## 1. Exact target and synchronization criterion

For \(m\ge0\) and \(0\le a<10^m\), canonical V1 is

\[
 \forall m\ \forall a<10^m\ \exists s\ge0:\qquad
 \left\lfloor10^m\{10^s\pi\}\right\rfloor=a.             \tag{V1}
\]

Leading zeroes are allowed, \(m=0\) is vacuous, and occurrence is contiguous.
The earlier fixed-return audit proves, for every fixed \(c\ge2\)
multiplicatively independent of ten,

\[
 \mathrm{V1}\quad\Longleftrightarrow\quad
 \liminf_N\|(10^N-c)\pi\|_{\mathbb T}=0.                  \tag{5}
\]

It also proves that (5) is equivalent to the existence of \(N_j\to\infty\)
and \(A_j\in\mathbb Q\) such that

\[
 (10^{N_j}-c)A_j\in\mathbb Z,\qquad
 |\pi-A_j|=o(10^{-N_j}).                                  \tag{6}
\]

For \(A_j=P_j/q_j\) reduced, the integer condition is exactly
\(q_j\mid10^{N_j}-c\). This branch asks whether signed Machin identities and
independent depths can manufacture (6).

## 2. Exact signed identities and remainder bounds

The Gaussian products

\[
 (3+i)^3(11-2i)=250(1+i),                                 \tag{7}
\]

\[
 (7+i)^6(22049-1457i)=1953125000(1+i)                    \tag{8}
\]

are exact integer certificates. Division by conjugates gives (3)--(4)
modulo pi. All arguments are in \((0,1)\), and

\[
 3\arctan(1/3)<1<\pi/2,\qquad
 6\arctan(1/7)<6/7<1<\pi/2.
\]

The positive imaginary excess in each Gaussian product selects \(\pi/4\).
All argument denominators are coprime to ten, so the elementary unbounded
2- or 5-primary obstruction does not settle these formulas.

For \(R\equiv1\pmod4\), \(R\ge5\), define

\[
 L_R(x)=\sum_{\substack{1\le r\le R-2\\r\ {\rm odd}}}
             {\chi_4(r)x^r\over r},\qquad
 \rho_R(x)=\arctan x-L_R(x),                              \tag{9}
\]

where \(\chi_4(r)=(-1)^{(r-1)/2}\). The finite geometric identity for
\(1/(1+t^2)\), followed by integration, gives

\[
 \rho_R(x)=\int_0^x{t^{R-1}\over1+t^2}\,dt,\qquad
 {x^R\over R(1+x^2)}\le\rho_R(x)\le{x^R\over R}.          \tag{10}
\]

This integral is the safe way to audit signed remainders.

## 3. Equal depth: the largest argument wins

Using the same \(R\) in (3), put

\[
 A_R=4(3L_R(1/3)-L_R(2/11)).
\]

Then

\[
\begin{aligned}
 \pi-A_R
 &=4(3\rho_R(1/3)-\rho_R(2/11))\\
 &\ge {4\,3^{-R}\over R}
       \left({27\over10}-\left({6\over11}\right)^R\right)\\
 &\ge {474\over55}{3^{-R}\over R}>0.                    \tag{11}
\end{aligned}
\]

Thus the negative coefficient causes no equal-depth cancellation. More
generally, after collecting duplicate arguments, let \(X\) be the largest
argument with nonzero total coefficient \(C\), let \(Y<X\) be the next, and
let \(B\) be the sum of the other absolute coefficients. Equation (10) gives

\[
 \left|\sum_i c_i\rho_R(x_i)\right|
 \ge {|C|X^R\over R(1+X^2)}-{B Y^R\over R}.               \tag{12}
\]

The right side is eventually a positive multiple of \(X^R/R\). Signed
common-depth identities therefore have the same largest-angle height leak as
positive identities. Only genuinely different depths can help.

## 4. Different depths: genuine but insufficient cancellation

For (3), set

\[
 A_{R,S}=4(3L_R(1/3)-L_S(2/11)),\qquad
 E_{R,S}=4(3\rho_R(1/3)-\rho_S(2/11)).                    \tag{13}
\]

The leading scales balance near

\[
 {3\,3^{-R}\over R}\asymp{(2/11)^S\over S}.               \tag{14}
\]

Because \(\log3/\log(11/2)\) is irrational by unique factorization, the two
depth lattices are not periodically locked. Exact ten-term alternating
brackets give

\[
 {|E_{6209,4001}|\over
  4(3\rho_{6209}(1/3)+\rho_{4001}(2/11))}<{1\over4000}.   \tag{15}
\]

For (4), the corresponding shadow

\[
 B_{R,S}=4(6L_R(1/7)-L_S(1457/22049))
\]

satisfies

\[
 {|\pi-B_{125,89}|\over
  4(6\rho_{125}(1/7)+\rho_{89}(1457/22049))}<{1\over1400}.\tag{16}
\]

So signed depth variation clears a real obstacle. It still misses the
reduced-height scale dramatically:

| identity | \((R,S)\) | reduced denominator digits | certified \(\lfloor\log_{10}(q|E|)\rfloor\) |
|---|---:|---:|---:|
| (3) | \((89,57)\) | 131 | 85 |
| (3) | \((269,173)\) | 413 | 281 |
| (3) | \((449,289)\) | 700 | 481 |
| (3) | \((809,521)\) | 1261 | 871 |
| (4) | \((125,89)\) | 528 | 418 |
| (4) | \((421,301)\) | 1826 | 1466 |
| (4) | \((717,513)\) | 3124 | 2514 |

Each row is an *experiment* at a finite pair. Its error lower bound is an
exact rational alternating bracket, not floating-point evidence.

## 5. Proof of the fixed-prime squeeze

Assume (1). Divisibility gives

\[
 \kappa H_j\le v_p(q_j)\le v_p(10^{N_j}-c).               \tag{17}
\]

Yu's Theorem 1 on p-adic logarithmic forms, applied with fixed \(10,c,p\),
gives

\[
                         v_p(10^N-c)\le C_{p,c}\log N     \tag{18}
\]

for sufficiently large \(N\); multiplicative independence excludes the zero
form. Hence

\[
                         N_j\ge\exp(\kappa'H_j)            \tag{19}
\]

for a fixed \(\kappa'>0\).

Zeilberger--Zudilin prove \(\mu(\pi)<7.104<8\). By the definition of
irrationality measure, every sufficiently large reduced denominator obeys

\[
                         |\pi-P/q|\ge q^{-8}.              \tag{20}
\]

Since \(q_j\le e^{CH_j}\),

\[
\frac{|\pi-A_j|}{10^{-N_j}}
\ge\exp\left((\log10)e^{\kappa'H_j}-8CH_j\right)
\longrightarrow\infty.                                   \tag{21}
\]

This proves the squeeze. If \(p\mid c\), divisibility is already impossible
because \(v_p(10^N-c)=0\).

For a fixed finite Machin identity whose depths are at most \(H\), the
natural common denominator has logarithm \(O(H)\): fixed rational argument
denominators contribute fixed powers and
\(\log\operatorname{lcm}(1,3,\ldots,H)=O(H)\) by Chebyshev. Reduction only
decreases it. Thus the upper-height condition is automatic. The hard
condition is linear survival of a fixed prime.

This improves the earlier \(v_p(10^N-c)=O(\log N)\) warning. Even if signed
cancellation makes the real tail unexpectedly tiny, the finite irrationality
measure prevents it from becoming tiny on the exponentially separated
\(10^{-N}\) scale.

## 6. Two infinite score-separated families

### 6.1 The \(3,11\) identity

Let \(p=11\), let \(e\) be odd, and use largest included exponent

\[
                         T_e=p^e,\qquad S_e=T_e+2.         \tag{22}
\]

Then \(S_e\equiv1\pmod4\). The endpoint has valuation \(-T_e-e\).
Every earlier \(2/11\) term has denominator score at most \(T_e+e-3\);
a \(1/3\) prefix of first-omitted depth at most \(2T_e\) has 11-adic
denominator score at most \(e\). The minimum is unique, so

\[
 v_{11}(\operatorname{den}A_{R,S_e})=T_e+e
 \qquad(S_e\le R\le2T_e).                                 \tag{23}
\]

For \(c=16\), powers of ten modulo 11 are only 1 and 10, while
\(16\equiv5\pmod {11}\), so divisibility fails immediately. For every other
fixed multiplicatively independent \(c\), either a congruence fails,
\(11\mid c\), or the squeeze applies. This whole comparable-depth family is
excluded.

### 6.2 The \(7,22049\) identity

Let \(p=1297\), \(e\ge3\), and use

\[
                         T_e=p^e+2,\qquad S_e=p^e+4.       \tag{24}
\]

Here \(S_e\equiv1\pmod4\). The term at exponent \(p^e\), not the endpoint,
has score \(p^e+e\). The endpoint score is \(p^e+2\); every earlier term has
score at most \(p^e+e-3\); a \(1/7\) prefix below \(2p^e\) contributes
exponent-denominator score at most \(e\). Hence

\[
 v_{1297}(\operatorname{den}B_{R,S_e})=p^e+e
 \qquad(S_e\le R\le2p^e).                                 \tag{25}
\]

Again the fixed-prime squeeze excludes synchronization for every fixed
\(c\) independent of ten, regardless of real-tail cancellation.

These infinite families cover a broad comparable-depth window, not every
schedule. A construction may deliberately avoid score-separated depths.

## 7. A real p-adic cancellation at exponent 2059

One cannot promote (23)--(25) to all depths by endpoint rhetoric. In the
\(2/11\) prefix through \(T=2059\),

\[
 2057=11^2\cdot17,\qquad
 2057+v_{11}(2057)=2059+v_{11}(2059)=2059.                \tag{26}
\]

The two tied top terms, after factoring \(11^{-2059}\), equal

\[
 {2^{2057}\over17}-{4\,2^{2057}\over2059}
 ={2^{2057}\cdot1991\over17\cdot2059},\qquad
 1991=11\cdot181.                                         \tag{27}
\]

They gain one 11-adic order. Exact reduction gives

\[
                v_{11}(L_{2061}(2/11))=-2058,             \tag{28}
\]

not \(-2059\). This finite identity falsifies a blanket all-depth dominant
endpoint claim.

A complete fixed-identity obstruction still needs a theorem such as

\[
 v_p(\operatorname{den}A_{R,S})\ge\kappa\max(R,S)         \tag{29}
\]

on every Archimedean-balanced schedule after all tied layers and
cross-component cancellation. No proof or checked source here establishes
(29). Varying the Gaussian identity creates a second escape because no prime
need remain fixed.

As an exact finite illustration, the least compatible exponent residues for
\(10^N\equiv16\pmod {1297^k}\), \(k=1,\ldots,6\), are

\[
616,\ 1043896,\ 1971072760,\ 2288940937096,\
3282357482682376,\ 3806434174632201688.                  \tag{30}
\]

The growth pattern is not used as proof; Section 5 uses Yu's theorem.

## 8. Dated primary-source audit

- [DLMF 4.24.E3](https://dlmf.nist.gov/4.24#E3) records the arctangent series
  underlying (9)--(10).
- Yu, [*p-adic logarithmic forms and group varieties II*](https://doi.org/10.4064/aa-89-4-337-378),
  Theorem 1, supplies the explicit fixed-\(p\) order bound used in (18).
- Zeilberger--Zudilin,
  [*The Irrationality Measure of Pi is at most 7.103205334137...*](https://doi.org/10.2140/moscow.2020.9.407),
  supply (20).
- Matveev,
  [*An explicit lower bound for a homogeneous rational linear form in
  logarithms of algebraic numbers*](https://doi.org/10.1070/im1998v062n04ABEH000190),
  is a possible tool for leading-tail balance. It is not claimed to bound the
  full tails here; uniform remainders and exact-equality cases remain.
- [The recursive Machin audit](machin_angle_splitting_attack.md) records the
  relevant identity literature. It supplies no all-depth theorem (29), no
  divisor \(q\mid10^N-c\), and no decimal-cylinder hit.

Searches on 2026-08-12 UTC included *signed depth-varying Machin formula*,
*linear forms in logarithms rational powers*, and *p-adic logarithmic forms
valuation of \(a^n-b\)*. No primary source found supplies (6). This is a
bounded negative search result, not a novelty claim.

## 9. Exact replay

The companion checker is
[signed_depth_machin_attack_check.py](signed_depth_machin_attack_check.py).
It uses integer arithmetic and Fraction for every identity, tail bracket,
reduced denominator, valuation, and modular lift. A clean run ends with:

~~~text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
gaussian_signed_identity_exact_checks=7
common_depth_dominance_exact_checks=100
finite_balance name=three-eleven R=809 S=521 sign=-1 denominator_digits=1261 floor_log10_q_error_lower=871
finite_balance name=seven-22049 R=717 S=513 sign=-1 denominator_digits=3124 floor_log10_q_error_lower=2514
deep_tail_balance name=three-eleven R=6209 S=4001 signed_over_unsigned_midpoint=0.00024763817486505602569145751820523307471781521653264
deep_tail_balance name=seven-22049 R=125 S=89 signed_over_unsigned_midpoint=0.00069465085888065749461999617601590666429497266328596
top_layer_cancellation T=2059 formal_max_score=2059 actual_denominator_valuation=2058
infinite_score_separated_symbolic_checks=28
c16_p1297_lift_residues=616,1043896,1971072760,2288940937096,3282357482682376,3806434174632201688
all exact assertions passed
~~~

## Sharp conclusion

Signed, depth-varying Machin shadows demonstrably create strong cancellation.
The fixed-prime synchronization squeeze nevertheless closes every
fixed-identity family in which one prime survives with linear multiplicity
and the rational height remains exponential in truncation height. Two
infinite natural depth families satisfy that premise exactly.

The remaining route must either prove systematic p-adic cancellation making
every fixed-prime exponent sublinear on all selected depths, or vary the
Gaussian identity so no fixed prime survives while the fully reduced
denominator still divides one \(10^N-c\). No construction or theorem found
here does either. Faster signed convergence alone cannot prove V1.
