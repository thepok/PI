# Independent audit: BBP high-prime phase compression

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Audited frozen pair:

- [bbp_high_prime_phase_compression_20260813.md](bbp_high_prime_phase_compression_20260813.md),
  SHA-256
  `47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564`;
- [bbp_high_prime_phase_compression_20260813_check.py](bbp_high_prime_phase_compression_20260813_check.py),
  SHA-256
  `7df64d082de31da1d902fa0e6418b97a5101cd14f93e495d141631535f3925ed`.

## Verdict and claim status

**PASS.** No fatal mathematical, indexing, endpoint, support, or claim-scope
error was found.

Conditional on the frozen localization and denominator results cited by the
primary report, its new infinite arguments retain label `proof sketch`. The
primary and independent finite replays retain label `experiment`. Canonical
V1 remains a `conjecture`; this audit proves neither a fixed-sixteen return
nor a complete decimal digit result for pi.

Three scope qualifications are essential and are already respected by the
primary report:

1. The moving-grid statement has quantifiers

   \[
      \forall\varepsilon>0\ \exists A_\varepsilon\ \exists M_0\
      \forall M\geq M_0:\quad E_M\leq M^\varepsilon.          \tag{A1}
   \]

   It does not use one fixed cutoff parameter (A) simultaneously for all
   \(\varepsilon\).
2. The annihilation budget concerns logarithmic prime mass only. It gives no
   lower bound for the resulting real phase, because nonzero CRT components
   can cancel near an integer.
3. The precision barrier rules out direct replacement of the exact
   reciprocal-prime lift by a PNT/AP or Siegel--Walfisz asymptotic. It does
   not rule out exponential-sum estimates, exact computation, or a theorem
   exploiting correlation with the dyadic and residual-cofactor terms.

## 1. Rational lift, (J_M), and modulus 840

Let (g=a/b) be reduced, (p\nmid b), and let
(r=[ab^{-1}]_p). Write

\[
                         br-a=pq.                            \tag{A2}
\]

Modulo (b), this says (pq\equiv-apmod b), so
(q\equiv\kappa_{a,b}(p)pmod b). Therefore

\[
 \frac r p=\frac a{bp}+\frac q b
 \equiv\frac a{bp}+\frac{\kappa_{a,b}(p)}b\pmod1.            \tag{A3}
\]

Every denominator in the six high-prime rows divides 105. Summing (A3)
therefore gives exactly

\[
 \Xi_M^>\equiv\frac{J_M}{105}+H_M\pmod1.                     \tag{A4}
\]

The interval and support decisions require (p\bmod4) and (p\bmod8),
while (kappa) requires (p\bmod b) for (b\mid105). Their least common
multiple is

\[
                         \operatorname{lcm}(8,105)=840.       \tag{A5}
\]

Thus interval plus (p\bmod840) determines the complete local contribution
to (J_M\bmod105). The five nonintegral (kappa)-formulas in the primary
report follow directly from (-a\pmod b); the independent replay verifies
all of them over every reduced class modulo 840.

## 2. The multiplier modulo 105

For (n\geq4),

\[
             A_n=2^{n-4}5^n-1.                              \tag{A6}
\]

Modulo 5 this is always (-1), modulo 3 it is always 0, and the remaining
modulo-7 component has period six. CRT gives the exact cycle

\[
             99,54,24,39,84,9\pmod {105}.                    \tag{A7}
\]

Every entry is a multiple of 3, hence (A_nJ_M/105) lies on a
(1/35)-grid. When (n\equiv2pmod6), the gcd with 105 is 21, hence this
term lies on a (1/5)-grid. The independent checker verifies (A7) through
(n=1199), as an `experiment`; the CRT derivation proves the infinite
cycle as a `proof sketch`.

## 3. Prime bands, asymptotic constant, and endpoints

After applying the densities of the two reduced classes modulo 4, and the
combined density (1/2) of the two supported classes modulo 8 above (4M),
the seven bands have the exact weights

\[
 \frac{32}{105},\ -\frac4{15},\ \frac{16}{15},\
 \frac83,\ \frac{32}3,\ 16,\ 32                         \tag{A8}
\]

on the respective ideal intervals

\[
 (1,8/7),\ (8/7,4/3),\ (4/3,8/5),\ (8/5,2),
 (2,8/3),\ (8/3,4),\ (4,8).                              \tag{A9}
\]

For example,

\[
 \frac12\left(\frac{752}{15}-\frac{1040}{21}\right)
 =\frac{32}{105},\qquad
 \frac12\left(64-\frac{128}{3}\right)=\frac{32}{3}.       \tag{A10}
\]

Multiplying (A8) by the logarithms of the endpoint ratios in (A9) gives

\[
 \begin{aligned}
 C_>={}&32\log3-16\log(3/2)
 +\frac{32}{3}\log(4/3)+\frac83\log(5/4)\\
 &+\frac{16}{15}\log(6/5)-\frac4{15}\log(7/6)
 +\frac{32}{105}\log(8/7)\\
 ={}&32.525874511493811\ldots.                              \tag{A11}
 \end{aligned}
\]

This independently reproduces the primary constant. Its positivity is
rigorous: the first two terms are (16\log6), which alone dominate the
only negative later term.

Fixed-modulus PNT/AP plus partial summation supplies each band with error
(O(1/\log^2M)). Only finitely many bands and residue classes occur, so the
error is uniform over the displayed sum. Replacing the exact endpoints by
their proportional endpoints moves only (O(1)) candidate integers per
depth, each contributing (O(1/M)). The independent replay through depth
400 found at most four changed band assignments and at most two changed
support assignments at any depth, exactly matching this bounded-endpoint
argument. Hence

\[
                 H_M=\frac{C_>}{\log M}
                     +O\!\left(\frac1{\log^2M}\right)        \tag{A12}
\]

follows from the cited fixed-modulus input.

Once (0<H_M<1/210), the point (J_M/105+H_M) lies strictly within half a
grid cell of (J_M/105). Therefore

\[
 \operatorname{dist}_{\mathbb T}
 \left(\Xi_M^>,\frac1{105}\mathbb Z/\mathbb Z\right)=H_M.    \tag{A13}
\]

No hidden wraparound or adjacent-grid ambiguity remains in the geometric
step.

## 4. Moving cutoff and reduced denominator

Fix (A>4C_0), put

\[
 L_M=\left\lfloor\frac{\log M}{A}\right\rfloor,\quad
 Y_M=\frac{M}{L_M},\quad
 N_M=\left\lfloor\frac{8M+5}{Y_M}\right\rfloor.              \tag{A14}
\]

The frozen height argument gives, for every retained prime (p>Y_M), a
reduced localization (G_{M,p}=a_{M,p}/b_{M,p}) with

\[
 b_{M,p}\mid E_M,qquad
 E_M=2^{2N_M}\operatorname{lcm}(1,\ldots,N_M).                \tag{A15}
\]

Applying (A3) with (E_M/b_{M,p}) yields the exact moving-grid identity.
Since (N_M=O(\log M/A)) and
(\log\operatorname{lcm}(1,\ldots,N_M)=O(N_M)), there is an absolute
constant (K) such that

\[
                         \log E_M\leq\frac KA\log M+O(1).    \tag{A16}
\]

Given a fixed \(\varepsilon>0\), choose one fixed
(A_\varepsilon>\max(4C_0,K/\varepsilon)). This proves precisely (A1).
The selected prime set and grid depend on that choice.

Factor

\[
                  E_M=2^{u_M}5^{v_M}E'_M,qquad(E'_M,10)=1.  \tag{A17}
\]

For (n\geq\max(u_M+4,v_M)), (A_n\equiv-1) modulo both primary factors.
Modulo (E'_M), its dependence is that of (10^n), with period
(operatorname{ord}_{E'_M}(10)\leq E'_M). Because
(u_M,v_M=O(\log M/A)), every (n\geq M) is past the transient eventually.
The period claim and its quantifiers are therefore correct.

For large (M), (Y_M>N_M), so each retained (p) is coprime to every
local denominator and to (E_M). The height inequality makes the reduced
numerator (a_{M,p}) nonzero modulo (p). In

\[
                         H_M^\star=\sum_p\frac{a_{M,p}}{b_{M,p}p}, \tag{A18}
\]

the (p)-summand has (p)-adic valuation (-1), while every other summand
is (p)-integral. Thus (p) survives reduction in the denominator of the
whole sum. Multiplying over retained primes proves the divisibility claim
and, using the frozen support mass, the ((6+o(1))M) lower bound.

At deliberately small finite cutoffs, rational nonvanishing need not imply
nonvanishing modulo (p). The independent replay observed one such
candidate among 663. It excludes that candidate from the surviving-prime
product. This is consistent with the primary checker and does not affect the
eventual height-protected statement.

Finally, boundedness of the local sums and Mertens give

\[
 |H_M^\star|\ll
 \sum_{M/L_M<p\leq8M+5}\frac1p
 \ll\frac{\log\log M}{\log M}=o(1).                          \tag{A19}
\]

The small Archimedean size and exponentially large reduced denominator are
therefore compatible.

## 5. Annihilation budget

If (10^n\equiv16\pmod p), then (p\mid A_n) for every retained
(p>M>5). Distinct killed primes have squarefree product dividing
(|A_n|), so

\[
 \sum_{p\ \mathrm{killed}}\log p
 \leq\log|A_n|<n\log10\leq M\log16.                           \tag{A20}
\]

Subtracting this from the frozen total masses ((5+o(1))M) and
((6+o(1))M) proves the two stated residual-mass lower bounds. The estimate
is uniform in the proportional row because only the common upper bound on
(n) is used. It excludes annihilation of almost all logarithmic mass, but
the primary report correctly declines to infer a real phase lower bound.

## 6. Precision barrier and its exact reach

Replacing (H_M) by an approximation with uncertainty interval of length
(delta_M) produces an image interval of length
(|A_n|\delta_M) under multiplication modulo one. An interval of input
length (1/|A_n|) already covers the circle. Hence a phase conclusion based
only on uniform absolute approximation requires

\[
                         \delta_M=o(|A_n|^{-1})=o(10^{-n}).    \tag{A21}
\]

For (n\asymp M), this is exponential precision in (M). Fixed-modulus
PNT/AP and Siegel--Walfisz remainders, including arbitrary fixed powers of
(1/\log M), are (e^{-o(M)}), not (e^{-\Theta(M)}). They also leave
prime-count errors much larger than one and therefore do not determine
(J_M\bmod105). The stated no-go for direct asymptotic substitution is
valid. It is an information barrier for that method, not an impossibility
theorem for the exact phase.

## 7. Independent replay

The independent checker
[bbp_high_prime_phase_compression_20260813_independent_check.py](bbp_high_prime_phase_compression_20260813_independent_check.py)
has SHA-256
`49298d7adabe2cb7a7f6993998130789bf07d70da9069de56ff30ba7e3b2a5f9`.
It imports no primary or frozen checker. It reconstructs the pole
localizations, the rational lifts, reduced BBP coordinates at independent
depths, endpoint discrepancies, moving common denominators, eventual
periods, reduced-denominator products, and annihilation products.

Run:

```text
python -m py_compile \
  work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_independent_check.py
python \
  work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_independent_check.py
```

Retained output:

```text
status: PASS
audit_label: experiment
elementary_lift_checks: 2304
kappa_table_checks: 960
dependence_mod_840_checks: 960
period_mod_105_checks: 1196
high_prime_table_checks: 57889
aggregate_grid_checks: 353
actual_reduced_crt_checks: 315
maximum_band_discrepancies_per_depth: 4
maximum_support_discrepancies_per_depth: 2
geometric_grid_checks: 315
moving_denominator_checks: 663
moving_grid_checks: 3
moving_period_checks: 36
moving_reduced_denominator_checks: 662
annihilation_budget_checks: 198
derived_asymptotic_constant: 32.525874511493811
asserts_fixed_sixteen_return: false
asserts_v1: false
```

## Final assessment

The (1/105)-grid lift, the modulo-840 dependence, the multiplier period,
the positive reciprocal-prime constant, the moving (M^\varepsilon)-grid,
the reduced-denominator divisibility, and the logarithmic annihilation budget
all survive independent checking. The PNT precision discussion is valid at
its explicitly limited scope.

The primary artifact should remain `proof sketch`, not be promoted to
`machine-checked`, `candidate resolution`, or `verified resolution`. It is a
sound structural reduction and method-specific no-go, not a proof of V1.
