# BBP short-orbit return: exact CRT recurrence and the missing odd quotient

Audit date: **2026-08-12 UTC**

Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)

Target SHA-256:
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained. Canonical V1 remains a "conjecture".

This branch starts from the all-depth two-adic identity in
[bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md) and
determines its exact content for the transferable short orbit. The material
conclusions are:

1. Decay of the minimum over the first
   \(\lfloor(\log_{10}16)M\rfloor\) decimal powers at BBP depth \(M\) is
   equivalent to the fixed-sixteen return; it is not a weaker finite target.
2. After the forced factor \(16\) is removed, the phase has a closed affine
   recurrence. Its changing reduced odd denominator is governed exactly by
   the congruences \(10^n\equiv16\pmod {p^e}\).
3. The reflected two-adic BBP function is an isometry of \(\mathbb Z_2\).
   The null identity determines the full dyadic numerator coordinate, with
   eight bits more precision than the dyadic factor in the reduced phase.
4. The complementary odd quotient is exactly the omitted Archimedean phase.
   A sharp separator preserves the full actual reduced denominator, the full
   all-depth two-adic congruence, and a better-than-BBP approximation rate to a
   fixed transcendental limit, while its complete transferable short orbit
   remains a fixed distance from zero.

The exact identities and asymptotic separator have status "proof sketch"
because they are not Lean declarations. The finite replay is an "experiment".
The bounded source audit is "literature-checked" as of the displayed date.
Nothing here is a "candidate resolution".

## 1. Normalized statement and the exact short-orbit equivalence

Canonical V1 is

\[
 \forall L\in\mathbb N\;\forall w\in\{0,\ldots,9\}^{L}\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+L-1}(\pi))=w.                 \tag{1}
\]

Digits are after the decimal point, leading zeroes are allowed in \(w\), and
\(L=0\) is vacuous. The statement asks for finite contiguous occurrence, not
occurrence of every infinite tail and not subsequence occurrence.

For

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_M=\sum_{k=0}^{M}\frac{a(k)}{16^k},                \tag{2}
\]

the audited positive BBP tail bound is

\[
 0<\pi-B_M\leq\frac{16^{-M}}{15(M+1)^2}.             \tag{3}
\]

Put \(\lambda=\log_{10}16=1.204119\ldots\). Uniformly for
\(5\leq n\leq\lfloor\lambda M\rfloor\), the circle norm is 1-Lipschitz and

\[
 \left|
 \|(10^n-16)\pi\|_{\mathbb T}
 -\|(10^n-16)B_M\|_{\mathbb T}
 \right|
 \leq\frac{1}{15(M+1)^2}.                            \tag{4}
\]

Indeed \(10^n\leq16^M\) in this window, so (4) follows immediately from
(3). For \(M\geq5\), define

\[
 E_M=\min_{5\leq n\leq\lfloor\lambda M\rfloor}
              \|(10^n-16)B_M\|_{\mathbb T}.          \tag{5}
\]

Then

\[
 \boxed{
 E_M\longrightarrow0
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0.} \tag{6}
\]

For the reverse implication, fix one good exponent \(n\) for pi, then let
\(M\) grow until the window contains \(n\); (3) transfers that phase. For
the forward implication, choose minimizers \(n_M\). If an infinite
subsequence of \(n_M\) were bounded, a further constant subsequence and
(3) would imply \((10^n-16)\pi\in\mathbb Z\), contradicting irrationality
of pi. Hence a subsequence has \(n_M\to\infty\), and (4) transfers its
vanishing phase to pi. The separately audited Furstenberg bridge makes the
right side of (6) equivalent to V1. Thus proving short-orbit decay in (5)
would resolve the target rather than supply an intermediate density lemma.

## 2. Exact reduced odd modulus and numerator recurrence

Let \(r_M=v_2(M+1)\). The all-depth valuation theorem gives the unique
reduced form

\[
 B_M=\frac{P_M}{2^{K_M}R_M},\qquad
 K_M=4M-r_M,\qquad
 (P_M,2R_M)=1,\quad R_M\ {\rm odd}.                  \tag{7}
\]

For \(M\geq2\), put

\[
 D_M=2^{K_M-4},\qquad
 A_n=\frac{10^n-16}{16}=2^{n-4}5^n-1\quad(n\geq5).   \tag{8}
\]

Every \(A_n\) in this range is odd, and

\[
 A_{n+1}=10A_n+9.                                    \tag{9}
\]

Consequently

\[
 (10^n-16)B_M=\frac{A_nP_M}{D_MR_M}.                \tag{10}
\]

Write

\[
 g_{M,n}=(A_n,R_M),\qquad
 U_{M,n}=\frac{A_nP_M}{g_{M,n}},\qquad
 Q_{M,n}=D_M\frac{R_M}{g_{M,n}}.                    \tag{11}
\]

Equation (10) in lowest terms is \(U_{M,n}/Q_{M,n}\). Its reduced
numerator and modulus therefore obey

\[
 \boxed{
 U_{M,n+1}=
 \frac{10g_{M,n}U_{M,n}+9P_M}{g_{M,n+1}},\qquad
 Q_{M,n+1}=D_M\frac{R_M}{g_{M,n+1}}.}               \tag{12}
\]

Before the changing gcd reduction, the recurrence is closed. If

\[
 t_{M,n}\equiv A_nP_M\pmod {D_MR_M},\qquad
 0\leq t_{M,n}<D_MR_M,
\]

then

\[
 \boxed{
 t_{M,n+1}\equiv10t_{M,n}+9P_M\pmod {D_MR_M},}       \tag{13}
\]

and the phase in (10) is exactly

\[
 \frac{\min(t_{M,n},D_MR_M-t_{M,n})}{D_MR_M}.        \tag{14}
\]

For every odd prime power \(p^e\mid R_M\),

\[
 p^e\mid g_{M,n}
 \quad\Longleftrightarrow\quad
 10^n\equiv16\pmod {p^e}.                            \tag{15}
\]

Thus the moving odd cancellation is a family of discrete-log residue
classes. No factor 5 can enter \(g_{M,n}\). Whenever \(3\mid R_M\), the
factor 3 divides \(g_{M,n}\) for every \(n\); higher powers still depend on
\(n\). Even complete knowledge of all these local gcds leaves the least
absolute residue in (14) undetermined.

## 3. The null BBP function is a two-adic isometry

Let

\[
 F(X)=\sum_{j\geq0}16^j a(X-1-j).                   \tag{16}
\]

The all-depth report proves that this is a restricted analytic function on
\(\mathbb Z_2\), that \(F(0)=0\), and coefficientwise that

\[
 F(X)\equiv X\pmod2.                                \tag{17}
\]

Write \(F(X)=X+2G(X)\), where \(G\) is integral and analytic on the closed
two-adic unit disc. For \(x,y\in\mathbb Z_2\), analytic division of
\(G(x)-G(y)\) by \(x-y\) is integral, so

\[
 F(x)-F(y)=(x-y)(1+2H(x,y)),\qquad H(x,y)\in\mathbb Z_2. \tag{18}
\]

Therefore

\[
 \boxed{v_2(F(x)-F(y))=v_2(x-y)}                    \tag{19}
\]

and \(F\) induces a permutation of \(\mathbb Z/2^s\mathbb Z\) for every
\(s\geq1\). This is an unconditional deduction from the analytic identities;
it is not an Archimedean distribution result.

Set \(m=M+1\). The exact reflected-tail estimate is

\[
 v_2\!\left(F(m)-16^MB_M\right)\geq4m,              \tag{20}
\]

where

\[
 16^MB_M=2^{r_M}\frac{P_M}{R_M}.
\]

After division by \(2^{r_M}\), (20) yields the full congruence

\[
 \boxed{
 P_MR_M^{-1}\equiv
 \frac{F(M+1)}{2^{r_M}}
 \pmod {2^{\,4(M+1)-r_M}}.}                         \tag{21}
\]

Since

\[
 2^{4(M+1)-r_M}=256D_M,                             \tag{22}
\]

the null identity gives eight bits more precision than the dyadic factor
\(D_M\) in (10). In particular, if

\[
 0\leq w_M<D_M,\qquad
 w_M\equiv P_MR_M^{-1}\pmod {D_M},                  \tag{23}
\]

then the null identity determines the complete dyadic CRT coordinate \(w_M\)
and also the next eight two-adic bits.

## 4. Exact quotient identity: what the two-adic coordinate omits

Define

\[
 c_M=\frac{P_M-R_Mw_M}{D_M}\in\mathbb Z.            \tag{24}
\]

Then

\[
 \boxed{
 16B_M=\frac{P_M}{D_MR_M}
      =\frac{w_M}{D_M}+\frac{c_M}{R_M}.}             \tag{25}
\]

If \(x_M=\{16B_M\}\) and \(\bar c_M=c_M\bmod R_M\), this is equivalently

\[
 \boxed{
 \frac{\bar c_M}{R_M}
 =\left\{x_M-\frac{w_M}{D_M}\right\}.}              \tag{26}
\]

The complementary numerator is therefore the position of the actual
Archimedean target in a shifted \(R_M\)-grid. It is not an independent local
invariant. The extra eight bits in (21) determine only one residue class
\(c_M\bmod256\): dividing (21) after subtracting \(w_M\) gives

\[
 c_MR_M^{-1}\equiv
 \frac{1}{D_M}
 \left(\frac{F(M+1)}{2^{r_M}}-w_M\right)
 \pmod {256}.                                       \tag{27}
\]

Substituting (25) into (10) gives

\[
 (10^n-16)B_M
 =A_n\left(\frac{w_M}{D_M}+\frac{c_M}{R_M}\right).  \tag{28}
\]

For \(e(z)=\exp(2\pi iz)\), every Fourier mode factors as

\[
 e\!\left(h(10^n-16)B_M\right)
 =
 e\!\left(\frac{hA_nw_M}{D_M}\right)
 e\!\left(\frac{hA_nc_M}{R_M}\right).               \tag{29}
\]

The first factor and the residue \(c_M\bmod256\) are fixed by the two-adic
identity. The second factor contains the remaining quotient from (26), is
synchronized by the same \(A_n\), and has modulus one. An exponential-sum
estimate for the first factor alone gives no estimate for the product.

## 5. Full-identity, full-denominator separator

Let \(j(q)\) be the least length such that every interval of \(j(q)\)
consecutive integers contains an integer coprime to \(q\). Kanold proves

\[
 j(q)\leq2^{\omega(q)}.                              \tag{30}
\]

Every prime divisor of \(R_M\) is at most \(8M+5\), because all such primes
come from the linear denominators in (2). The prime number theorem gives

\[
 2^{\omega(R_M)}=\exp(o(M)).                         \tag{31}
\]

The needed divisor mass follows from two explicit disjoint prime bands. Put

\[
\begin{aligned}
 \mathcal P_{1,M}={}&
 \{p\ {\rm prime}:4M+3<p\leq8M+1,\ p\equiv1\pmod8\}\\
 &\cup\{p\ {\rm prime}:4M+3<p\leq8M+5,\ p\equiv5\pmod8\},\\
 \mathcal P_{2,M}={}&
 \{p\ {\rm prime}:(8M+5)/3<p\leq4M+3\}.
\end{aligned}                                        \tag{31a}
\]

For \(p\in\mathcal P_{1,M}\), exactly one linear denominator among all
terms \(0\leq k\leq M\) is divisible by \(p\): it is \(8k+1=p\) or
\(8k+5=p\). For \(p\in\mathcal P_{2,M}\), one has \(p>2M+1\) and
\(3p>8M+5\). Since all four linear denominators are odd, again only the
multiple \(p\) can occur, uniquely as \(4k+3=p\), \(8k+1=p\), or
\(8k+5=p\), according to the residue class of \(p\). At the three possible
roots, the coefficient numerator satisfies

\[
 \left.(120k^2+151k+47)\right|_{k=-3/4}=5/4,
 \quad
 \left.(120k^2+151k+47)\right|_{k=-1/8}=30,
 \quad
 \left.(120k^2+151k+47)\right|_{k=-5/8}=-1/2.       \tag{31b}
\]

The residue applicable to each prime is nonzero modulo that prime. Thus the
unique singular BBP summand has \(p\)-adic valuation \(-1\), all other
summands are \(p\)-integral, and

\[
 v_p(B_M)=-1,\qquad p\mid R_M                         \tag{31c}
\]

with multiplicity exactly one. The prime number theorem in progressions
modulo 8 and the ordinary prime number theorem give

\[
 \sum_{p\in\mathcal P_{1,M}}\log p=(2+o(1))M,
 \qquad
 \sum_{p\in\mathcal P_{2,M}}\log p=(4/3+o(1))M.     \tag{31d}
\]

Consequently

\[
 \log R_M\geq(10/3+o(1))M.                           \tag{32}
\]

Fix any real \(\beta\). Because 256 is invertible modulo the odd number
\(R_M\), there is a residue \(a_M\bmod R_M\) such that

\[
 (c_M+256t,R_M)=1
 \quad\Longleftrightarrow\quad
 (t+a_M,R_M)=1.                                     \tag{33}
\]

Apply (30) to an interval centered at

\[
 T_M=\frac{R_M(\beta-B_M)}{16}.
\]

There is an integer \(t_M\) such that

\[
 (c_M+256t_M,R_M)=1,\qquad
 |t_M-T_M|=O\!\left(2^{\omega(R_M)}\right).          \tag{34}
\]

Put

\[
 c'_M=c_M+256t_M,\qquad
 P'_M=R_Mw_M+D_Mc'_M,\qquad
 B'_M=\frac{P'_M}{16D_MR_M}.                        \tag{35}
\]

The scaling in (35) is exact:

\[
 \boxed{B'_M=B_M+\frac{16t_M}{R_M}.}                \tag{36}
\]

Because \(w_M\) is odd and \((c'_M,R_M)=1\), (35) is reduced and has the
same complete denominator \(2^{K_M}R_M\) as \(B_M\). Moreover,

\[
 16^M(B'_M-B_M)=\frac{2^{4(M+1)}t_M}{R_M},          \tag{37}
\]

whose two-adic valuation is at least \(4(M+1)\). Combining (20) and (37)
shows that \(B'_M\) satisfies the full null-identity congruence (20), not
merely its reduction modulo \(D_M\).

Equations (34) and (36) give

\[
 |B'_M-\beta|
 =O\!\left(\frac{2^{\omega(R_M)}}{R_M}\right)
 \leq\exp\!\left((-10/3+o(1))M\right)
 =o\!\left(\frac{16^{-M}}{M^2}\right).              \tag{38}
\]

The final little-oh uses \(10/3>\log16\). Uniformly for
\(5\leq n\leq\lfloor\lambda M\rfloor\),

\[
 |(10^n-16)(B'_M-\beta)|
 \leq\exp\!\left((\log16-10/3+o(1))M\right)
 =o(1).                                             \tag{39}
\]

Take first \(\beta=1/10\). For every \(n\geq1\),

\[
 \|(10^n-16)\beta\|_{\mathbb T}=2/5.                \tag{40}
\]

Therefore the rational shadows (35), despite preserving the full actual
denominator and full two-adic congruence, satisfy

\[
 \min_{5\leq n\leq\lfloor\lambda M\rfloor}
 \|(10^n-16)B'_M\|_{\mathbb T}\geq2/5-o(1).         \tag{41}
\]

To preserve a transcendental limit as well, take

\[
 \beta=\frac1{10}+\sum_{r\geq2}10^{-r!}.            \tag{42}
\]

This is Liouville-transcendental. Every decimal tail of (42) lies in
\([0,1/9]\), while \(\{16\beta\}\in(3/5,7/9)\), so

\[
 \|(10^n-16)\beta\|_{\mathbb T}>2/9
 \qquad(n\geq0).                                    \tag{43}
\]

The same construction then retains a positive short-orbit gap, a
transcendental limit, a better-than-BBP approximation rate, the actual full
denominators, and the full all-depth two-adic identity. It deliberately does
not preserve the exact four-pole coefficient recurrence, which uniquely
selects pi. Its conclusion is narrow and exact: all two-adic and denominator
information obtained so far leaves the Archimedean quotient in (26)
unselected.

## 6. Cross-depth and exponential-sum routes

The exact cross-depth change is

\[
 (10^n-16)B_{M+1}-(10^n-16)B_M
 =\frac{(10^n-16)a(M+1)}{16^{M+1}}.                 \tag{44}
\]

On the transferable triangle \(n\leq\lambda M\), this is \(O(M^{-2})\).
Adjacent depths stabilize the same decimal orbit; they are not independent
samples for a second pigeonhole argument. Equation (6) is the quantified
form of this circularity.

The reduced odd denominators are not nested. Exact computation gives the
first losses from \(R_{M-1}\) to \(R_M\) at

\[
 (M,\text{lost factor})
 =(5,3),(9,19),(19,13),(24,7),(29,7),\ldots .       \tag{45}
\]

This is an "experiment", not an asymptotic theorem, but it falsifies the
simplest common-modulus cross-depth recurrence. An unreduced common
denominator restores a recurrence only by retaining the same Euclidean
quotient (26).

A Fourier proof of a hit in (5) would need cancellation in the selected sum

\[
 \sum_{n\leq\lambda M}
 e\!\left(\frac{hA_nP_M}{D_MR_M}\right).            \tag{46}
\]

Formula (29) shows why estimates for powers of 5 modulo the dyadic factor,
or complete-subgroup estimates modulo selected odd primes, do not bound
(46): the omitted factor is the synchronized selected quotient. The
separator (33)--(43) realizes the same complete two-adic data, denominator,
and local-gcd cancellation pattern with a uniformly nonreturning full phase.
It intentionally changes the odd numerator coordinate \(c_M\bmod R_M\). A
successful exponential-sum estimate must use the
actual \(c_M\), not merely \(w_M\), \(R_M\), or the local discrete logs in
(15).

## 7. Exact finite replay

The script
[bbp_short_orbit_return_check.py](bbp_short_orbit_return_check.py), SHA-256
cb21ab170454f0260e5c12f15eb9403c9fa57e932153bf3403e8ea95c35bc550,
uses only Fraction, integers, gcds, and modular inverses. It verifies the
source hash, the reduced recurrence, the full \(256D_M\) two-adic coordinate,
the CRT quotient split, nonnesting witnesses, and finite instances of the
full-identity separator.

Run:

    python -m py_compile work/ultrapi-resume/bbp_short_orbit_return_check.py
    python work/ultrapi-resume/bbp_short_orbit_return_check.py --max-depth 120

Retained output:

    claim_status=experiment
    source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
    finite_two_adic_permutation_checks=1022
    dyadic_coordinate_checks=119
    crt_split_checks=119
    phase_reduction_checks=16420
    affine_recurrence_checks=16188
    separator_phase_checks=8327
    maximum_separator_grid_gap=8
    smallest_separator_distance=0.399999220486486
    first_odd_denominator_nonnesting_events=[(5, 3), (9, 19), (19, 13), (24, 7), (29, 7), (35, 19), (50, 3), (75, 121)]
    proportional_band_monotonicity_falsifier=M20:n20:0.001144132300430->M21:n23:0.072845332310798
    all exact checks passed

The finite permutation checks do not prove the all-depth isometry (19); the
analytic argument does. Finite separator rows do not prove the asymptotic
prime-product input. No finite calculation supplies evidence for V1.

## 8. Dated primary-source and applicability audit

| Source | Checked statement | Scope here |
|---|---|---|
| [Bailey--Borwein--Plouffe, On the Rapid Computation of Various Polylogarithmic Constants (1997), Theorem 1](https://doi.org/10.1090/S0025-5718-97-00856-9) | Exact series (2) and its base-16 digit-extraction origin. | It supplies no distribution theorem for (46). A pinned local PDF and hash are recorded in the all-depth report. |
| [Barsky--Muñoz--Pérez-Marco, On the genesis of BBP formulas (2021), Theorem 5.2 and Proposition 5.3](https://arxiv.org/abs/1906.09629) | Logarithmic derivation of the classical BBP formula and an exact null BBP formula. | Supports the p-adic/logarithmic provenance, not an Archimedean return. |
| [Kanold, Über eine zahlentheoretische Funktion von Jacobsthal, Math. Ann. 170 (1967), 314--326](https://eudml.org/doc/161543) | The explicit bound \(j(q)\leq2^{\omega(q)}\). | Used only to preserve the full odd denominator and full derived two-adic residue class in the separator. |
| [Lagarias, On the Normality of Arithmetical Constants (2001), Theorems 3.1, 3.3, 4.1](https://arxiv.org/abs/math/0101055v2) | BBP perturbed-remainder shadowing; stronger distribution remains conditional. | Confirms that BBP dynamics supplies no unconditional fixed-pi orbit estimate. |

The exact prime-band divisor argument is (31a)--(31c); (31d) uses the
classical PNT/AP input. No novelty is claimed for that input. Fresh searches
on 2026-08-12 UTC included
the phrases “exponential sums powers 5 modulo 2^k short orbit p-adic”,
“exponential sums g^n modulo prime power”, and “Jacobsthal function
2^omega(n) Kanold”. The closest exponential-sum results concern complete or
polynomially large subgroups, averages over moduli, or different polynomial
phases. No primary theorem located in this bounded search controls the one
selected critical-length product (46). This is an applicability record, not
a claim that the literature is exhausted.

## Sharp conclusion

The all-depth null identity has now been pushed to its full exact
short-orbit content. It gives an isometric two-adic coordinate and, together
with (12)--(15), a recurrence for every local cancellation. The remaining
quantity is not another valuation:

\[
 \frac{c_M\bmod R_M}{R_M}
 =\left\{\{16B_M\}-\frac{w_M}{D_M}\right\}.          \tag{47}
\]

It is the selected Archimedean quotient. The full-identity,
full-denominator separator proves that the derived two-adic structure,
denominator, and local-gcd data cannot select it. The exact BBP coefficient
recurrence does select one quotient, but
proving that its first \(O(M)\) affine iterates approach zero is (6), hence
the fixed return and V1 themselves. No such estimate was proved, so V1
remains a "conjecture".
