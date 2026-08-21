# BBP high-prime phase compression: a fixed grid, a reciprocal-prime lift, and a precision barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is Marcel's local question and has no external source
URL; none is invented here.

Frozen inputs:

- [bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
  SHA-256
  `d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`;
- [bbp_high_prime_coordinate_rigidity_20260813.md](bbp_high_prime_coordinate_rigidity_20260813.md),
  SHA-256
  `419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42`;
- [bbp_mixed_coordinate_height_separator_20260813.md](bbp_mixed_coordinate_height_separator_20260813.md),
  SHA-256
  `950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  No fixed-sixteen return and no
short-orbit estimate for pi is proved here.

This report expands the actual additive CRT phase at all denominator primes
(p>M).  Its new statements have label `proof sketch`; the exact finite
replay has label `experiment`.

The useful positive result is an exact compression.  The exponentially large
product of actual primes (p>M), of logarithmic mass ((5+o(1))M),
contributes modulo one as

\[
 \boxed{\Xi_M^{>}\equiv {J_M\over105}+H_M\pmod1,\qquad
 H_M=\sum_{\substack{p>M\\p\mid R_M}}{G_{M,p}\over p}.}       \tag{1}
\]

Here (J_M\bmod105) is an explicit weighted count of primes in fixed
residue classes modulo (840), and every (G_{M,p}) is one of the eight
frozen rational local coordinates.  Moreover

\[
 H_M={C_{>}\over\log M}+O\!\left({1\over\log^2M}\right),
 \qquad C_{>}=32.5258745114938\ldots>0.                         \tag{2}
\]

Thus the high-prime phase is not opaque CRT data: it is a (1/105)-grid
point plus one small, explicit signed reciprocal-prime sum.

The negative result is equally precise.  Multiplication by
(A_n=(10^n-16)/16) turns the second term into

\[
 A_nH_M=10^n{H_M\over16}-H_M,                                  \tag{3}
\]

so the missing information is the decimal shift of (H_M/16) at positions
(n\asymp M).  Fixed-modulus PNT or Siegel--Walfisz estimates determine
(H_M) only to (e^{-o(M)}) precision, whereas phase transfer at those
positions requires (e^{-\Theta(M)}) precision.  They also do not determine
the exact count residue (J_M\bmod105).  Hence direct substitution of PNT/AP
asymptotics into (1) cannot prove the required return.  This is a no-go for
that specific route, not for every possible use of prime structure.

Nothing below is `machine-checked`, a `candidate resolution`, or a
`verified resolution`.

## 1. Exact input phase

Write the reduced BBP partial sum as

\[
 B_M={P_M\over2^{K_M}R_M},\qquad (P_M,2R_M)=1,
\]

and use the complete dyadic coordinate (y_M=w_M/2^{K_M-4}) from the
frozen actual-quotient report.  Its exact odd decomposition is

\[
 16B_M=y_M+{c_M\over R_M}.                                    \tag{4}
\]

For each sufficiently large denominator prime (p>M), the exponent of (p)
in (R_M) is one.  Its additive CRT coordinate is

\[
 \widehat\gamma_{M,p}\equiv
 c_M(R_M/p)^{-1}\pmod p,qquad 0\leq\widehat\gamma_{M,p}<p.    \tag{5}
\]

The frozen localization proves
(\widehat\gamma_{M,p}\equiv G_{M,p}\pmod p), where the rational
number (G_{M,p}) is given by the following six interval rows.  A row is
used only when (p) belongs to the actual possible denominator support.

| interval for (p) | (p\equiv1\pmod4) | (p\equiv3\pmod4) |
|---|---:|---:|
| (p>(8M+5)/3) | (64) | (-32) |
| (2M+1<p\leq(8M+5)/3) | (64) | (-128/3) |
| ((8M+5)/5<p\leq2M+1) | (56) | (-152/3) |
| ((4M+3)/3<p\leq(8M+5)/5) | (264/5) | (-152/3) |
| ((8M+5)/7<p\leq(4M+3)/3) | (752/15) | (-152/3) |
| (M<p\leq(8M+5)/7) | (752/15) | (-1040/21) |

Every denominator in this table divides (105).  All primes
(M<p\leq4M+3) are in the possible support.  Above (4M+3), precisely the
classes (1,5\pmod8) occur up to their respective endpoints (8M+1) and
(8M+5).  For (M\geq48), every possible prime survives reduction and the
table is the actual coordinate.

Define

\[
 \Xi_M^{>}=
 \sum_{\substack{p>M\\p\mid R_M}}{\widehat\gamma_{M,p}\over p}.
                                                                    \tag{6}
\]

The frozen denominator audit gives

\[
 \sum_{\substack{p>M\\p\mid R_M}}\log p=(5+o(1))M.             \tag{7}
\]

## 2. The elementary rational-residue lift

Let (g=a/b) be reduced with (b>0), and let (p\nmid b).  Define

\[
 0\leq\kappa_{a,b}(p)<b,qquad
 \kappa_{a,b}(p)p\equiv-a\pmod b.                              \tag{8}
\]

If (r=[ab^{-1}]_p\in\{0,\ldots,p-1\}), then
(br-a) is divisible by (p).  Reducing its quotient modulo (b) gives
(8), and therefore

\[
 \boxed{{r\over p}\equiv
 {\kappa_{a,b}(p)\over b}+{a\over bp}\pmod1.}                  \tag{9}
\]

Apply (9) to every table entry (G_{M,p}=a_{M,p}/b_{M,p}).  Set

\[
\begin{aligned}
 J_M&\equiv
 \sum_{\substack{p>M\\p\mid R_M}}
 {105\over b_{M,p}}\kappa_{a_{M,p},b_{M,p}}(p)
 \pmod {105},\\
 H_M&=
 \sum_{\substack{p>M\\p\mid R_M}}{G_{M,p}\over p}.
\end{aligned}                                                    \tag{10}
\]

Summing (9) proves the exact decomposition (1).

This also identifies all local dependence.  The interval row and the sign
of (G_{M,p}) use (p\bmod4); support above (4M+3) uses (p\bmod8);
and (8) uses (p\bmod b_{M,p}), where (b_{M,p}\mid105).  Hence each
summand of (J_M) is determined by the interval and (p\bmod840).  In
particular, (J_M\bmod105) is an exact weighted sum of prime counts in
fixed progressions modulo (840), reduced modulo (105).  There is no
remaining modular inverse with a growing modulus in this part of the phase.

For example, the nonintegral rows use

\[
\begin{array}{c|c}
G=a/b&\kappa_{a,b}(p)\pmod b\\ \hline
-128/3,\,-152/3&2p^{-1}\pmod3\\
264/5&p^{-1}\pmod5\\
752/15&-2p^{-1}\pmod{15}\\
-1040/21&11p^{-1}\pmod{21}.
\end{array}                                                       \tag{11}
\]

## 3. The reciprocal lift has a positive explicit asymptotic

For fixed (0<\alpha<\beta) and (r\in\{1,3\}), fixed-modulus PNT/AP
and partial summation give

\[
 \sum_{\substack{\alpha M<p\leq\beta M\\p\equiv r\ (4)}}{1\over p}
 ={\log(\beta/\alpha)\over2\log M}
 +O\!\left({1\over\log^2M}\right).                            \tag{12}
\]

The additive constants in the table endpoints affect only the error.  The
positive first row extends from (8M/3) to (8M), while its negative class
stops at (4M).  Every later interval contains both reduced classes modulo
four.  Substitution in (10) gives (2), with

\[
\begin{aligned}
C_{>}={}&32\log3-16\log(3/2)
 +{32\over3}\log(4/3)+{8\over3}\log(5/4)\\
&+{16\over15}\log(6/5)-{4\over15}\log(7/6)
 +{32\over105}\log(8/7)\\
={}&32.5258745114938112501680455\ldots>0.             \tag{13}
\end{aligned}
\]

The positivity in (13) is not based on the decimal evaluation.  Its first
two terms equal (16\log6); every later term is positive except
(-(4/15)\log(7/6)), and
(16\log6>(4/15)\log(7/6)).  The error in (12) is uniform over the
present calculation because there are only the finitely many displayed
fixed endpoints and residue classes.  Moving an endpoint by the bounded
constants (1,3,5) changes a reciprocal sum by (O(1/M)), which is
absorbed by (O(1/\log^2M)).

Consequently (H_M>0) eventually and (H_M\to0).  Combining this with
(1), once (H_M<1/210), gives the geometric statement

\[
 \boxed{
 \operatorname {dist}_{\mathbb T}
 \left(\Xi_M^{>},{1\over105}\mathbb Z/\mathbb Z\right)
 ={C_{>}\over\log M}+O\!\left({1\over\log^2M}\right).}        \tag{14}
\]

Thus exact pairing of the high-prime coordinates does **not** collapse them
onto the fixed grid: the reciprocal lift is eventually nonzero and its
distance from the grid is asymptotically explicit.

## 4. Exact action of the return multiplier

For (n\geq4), put

\[
 A_n={10^n-16\over16}=2^{n-4}5^n-1.                            \tag{15}
\]

Equations (1) and (15) give

\[
 \boxed{
 A_n\Xi_M^{>}
 \equiv {A_nJ_M\over105}+10^n{H_M\over16}-H_M\pmod1.}        \tag{16}
\]

The grid factor is completely elementary.  Starting at (n=4), the
residues of (A_n\bmod105) are periodic with period six:

\[
 99,\ 54,\ 24,\ 39,\ 84,\ 9.                                 \tag{17}
\]

Every entry is divisible by three, so the first term of (16) lies on a
(1/35)-grid; when (n\equiv2\pmod6), it lies on a (1/5)-grid.
All genuinely long-modulus information from the primes (p>M) is therefore
concentrated in the decimal shift (10^nH_M/16\pmod1).

Using the cofactor (C_M^{>}=R_M/\prod_{p>M,p\mid R_M}p) and its additive
coordinate (\eta_M^{>}\bmod C_M^{>}), the complete actual phase becomes

\[
 (10^n-16)B_M\equiv
 A_n\left(
 y_M+{J_M\over105}+H_M+{\eta_M^{>}\over C_M^{>}}
 \right)\pmod1.                                                \tag{18}
\]

Equation (18) is an exact reparameterization.  It does not separate the
dyadic, reciprocal-prime, and cofactor terms after multiplication by the
same (A_n).

## 5. Compression at the moving cutoff

The same residue lift applies to the stronger frozen cutoff.  Choose the
constant (A) in that report, put

\[
 L_M=\left\lfloor{\log M\over A}\right\rfloor,qquad
 Y_M={M\over L_M},qquad
 N_M=\left\lfloor{8M+5\over Y_M}\right\rfloor,                 \tag{19}
\]

and retain every actual coordinate with (p>Y_M).  For sufficiently large
(M), its localization (G_{M,p}=a_{M,p}/b_{M,p}) is nonzero and the
frozen height calculation gives

\[
 b_{M,p}\mid E_M,qquad
 E_M=2^{2N_M}\operatorname {lcm}(1,\ldots,N_M).                 \tag{20}
\]

Define (J_M^\star\bmod E_M) by the analogue of (10), and put

\[
 H_M^\star=\sum_{\substack{p>Y_M\\p\mid R_M}}{G_{M,p}\over p}.
\]

Then exactly

\[
 \boxed{
 \Xi_M^\star\equiv{J_M^\star\over E_M}+H_M^\star\pmod1.}   \tag{21}
\]

The local sums (G_{M,p}) are bounded absolutely by a universal constant.
Mertens/PNT and (Y_M=M/L_M) therefore give

\[
 |H_M^\star|
 \ll\sum_{Y_M<p\leq8M+5}{1\over p}
 \ll{\log\log M\over\log M}=o(1).                            \tag{22}
\]

Also (N_M=O(\log M/A)), so Chebyshev's bound for
(\log\operatorname {lcm}(1,\ldots,N_M)) gives

\[
 \log E_M=O(\log M/A).                                       \tag{23}
\]

Since the height proof permits any sufficiently large fixed (A), for each
fixed (\varepsilon>0) it can be chosen so that (E_M\leq M^\varepsilon)
eventually.  More explicitly, write
(E_M=2^{u_M}5^{v_M}E'_M) with ((E'_M,10)=1).  Once
(n\geq\max(u_M+4,v_M)), the (2)- and (5)-primary residues of
(A_n) are both (-1), while its residue modulo (E'_M) has period
(\operatorname {ord}_{E'_M}(10)\leq\varphi(E'_M)\leq E'_M).
Because (u_M,v_M=O(\log M/A)), every exponent (n\geq M) is past this
transient for all sufficiently large (M).

For the same sufficiently large (M), every retained (p) is larger than
(N_M), so ((p,E_M)=1).  The height-protected nonvanishing of
(G_{M,p}\pmod p) then shows prime by prime that

\[
 \prod_{\substack{p>Y_M\\p\mid R_M}}p
 \ \mid\ \operatorname {den}(H_M^\star).                       \tag{23a}
\]

Thus the reduced denominator of the small lift itself still has logarithm
at least ((6+o(1))M); the compression is an additive structural identity,
not a low-height approximation.

Thus even the explicit coordinates on prime mass ((6+o(1))M) compress to
an arbitrarily small polynomial grid plus one (o(1)) reciprocal lift.
This is stronger structural information than the raw CRT sum, but the lift
still has an exponentially large exact denominator and is sampled at
decimal positions (n\asymp M).

## 6. A quantitative discrete-log annihilation budget

There is a second exact obstruction to a prime-by-prime attack.  Let

\[
 \mathcal K_{M,n}^{>}=
 \{p>M:p\mid R_M,\ 10^n\equiv16\pmod p\}.                       \tag{24}
\]

Every prime in this set divides the integer (A_n), and the primes are
distinct.  Hence

\[
 \sum_{p\in\mathcal K_{M,n}^{>}}\log p
 \leq\log|A_n|<n\log10.                                      \tag{25}
\]

Uniformly for every integer
(M\leq n\leq\lfloor(\log_{10}16)M\rfloor), equations (7) and (25)
imply, as (M\to\infty),

\[
 \sum_{\substack{p>M,\ p\mid R_M\\10^n\not\equiv16\ (p)}}
 \log p
 \geq(5-\log16+o(1))M
 = (2.227411\ldots+o(1))M.                                   \tag{26}
\]

At the moving cutoff the corresponding lower bound is
((6-\log16+o(1))M).  Thus no exponent in the proportional BBP row can
annihilate all, or even almost all, explicit prime coordinates through the
local condition (10^n\equiv16\pmod p).

This does not give a real lower bound for the phase: nonzero residues at
different primes may still combine close to an integer.  It does close the
more limited proposal that one short-row exponent could make the product
formula effective by forcing nearly every retained local determinant to
vanish.

## 7. Why PNT/AP and exact pairing stop here

Two precise barriers remain after the compression.

### 7.1 Count residues

The grid numerator (J_M\bmod105) is determined by exact prime counts in
classes modulo (840), **reduced modulo (105)**.  PNT/AP estimates those
counts with errors tending to infinity in absolute count.  Such estimates
do not determine their residues modulo (105).  Exact computation can find
one finite (J_M), but finite values give no asymptotic orbit theorem.

### 7.2 Archimedean precision

Suppose an analytic estimate replaces (H_M) by (widetilde H_M) with
absolute error at most (delta_M).  The induced phase uncertainty in (16)
is bounded only by

\[
 |A_n|\delta_M.                                                \tag{27}
\]

This is sharp as an information barrier: any real interval of length at
least (1/|A_n|) maps onto the whole circle under (x\mapsto A_nx\pmod1).
Therefore a uniform approximation alone must have

\[
 \delta_M=o(10^{-n})                                           \tag{28}
\]

to transfer an (o(1)) phase estimate at exponent (n).  Throughout the
proportional row, this is (e^{-\Theta(M)}) precision.

Fixed-modulus PNT/AP gives the first terms in (2), and Siegel--Walfisz can
make the remainder smaller than any fixed power of (1/\log M).  Both are
only (e^{-o(M)}).  Substitution into (27) is therefore vacuous.  Even
granting the exact (J_M), neither theorem controls the needed decimal
shift of the exact rational (H_M/16).

These statements rule out **direct asymptotic replacement** and **exact
fixed-grid pairing**.  They do not rule out a new theorem about exponential
sums of the exact reciprocal-prime rational, nor a theorem exploiting its
correlation with (y_M) and the residual cofactor in (18).

## 8. Exact finite replay

The independent companion
[bbp_high_prime_phase_compression_20260813_check.py](bbp_high_prime_phase_compression_20260813_check.py)
rebuilds every (G_{M,p}) from the four localized pole families.  It imports
no earlier checker.  It verifies:

- all six interval rows and 124,635 actual high-prime coordinates through
  depth 600;
- direct reconstruction of 281 additive CRT coordinates from the reduced
  BBP rational at four independent depths;
- the rational residue lift (9), aggregate (1/105)-grid identity (1), and
  dependence on interval plus (p\bmod840);
- the exact phase identity (16) and period (17);
- the common-denominator compression (20)--(21) at finite moving cutoffs;
- survival of every nonzero tested moving-cutoff prime in the reduced
  denominator of the reciprocal lift;
- the exact product-divisibility ledger behind (25).

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_check.py \
  --max-depth 600
```

Retained output:

```text
status: PASS
bounded_replay_label: experiment
asymptotic_decomposition_label: proof sketch
depth_range: [48, 600]
high_prime_table_checks: 124635
exact_residue_lift_checks: 124635
aggregate_1_over_105_grid_checks: 553
phase_factorization_checks: 9954
dependence_mod_840_checks: 124635
period_mod_105_checks: 396
actual_reduced_crt_checks: 281
moving_denominator_checks: 912
moving_grid_checks: 3
moving_reduced_denominator_checks: 910
annihilation_budget_checks: 226
asymptotic_constant_derivation_checks: 10
last_high_prime_count: 390
last_grid_numerator_mod_105: 68
last_harmonic_lift: 4.010910185003171
last_log_scaled_harmonic_lift: 25.657510306855265
predicted_asymptotic_constant: 32.525874511493811
maximum_observed_killed_log_mass_over_depth: 0.100416744562759
asserts_fixed_sixteen_return: false
asserts_v1: false
```

The slow finite approach to (13) is not evidence for or against the proof
sketch; (12), not numerical extrapolation, proves the asymptotic.

## 9. Dated literature and applicability audit

Search date: **2026-08-13 UTC**.

- [Bennett--Martin--O'Bryant--Rechnitzer, *Explicit bounds for primes in
  arithmetic progressions* (2018), Theorem 1.2](https://arxiv.org/abs/1802.00085v3)
  supplies a fixed-modulus estimate for the Chebyshev function in a reduced
  progression.  Partial summation gives (12).  It gives neither exact prime
  count residues modulo (105) nor decimal-shift information about (H_M).
- A targeted search for Siegel--Walfisz and reciprocal-prime AP estimates
  found standard arbitrary-log-power distribution statements, including
  [Carella, *Elementary Proof of the Siegel--Walfisz Theorem*
  (2020)](https://arxiv.org/abs/2004.02010).  No result located converts such
  (e^{-o(M)})-scale counting information into the (e^{-\Theta(M)})
  pointwise phase precision required by (28).  The proof above does not rely
  on this latter paper; the fixed-modulus Bennett et al. theorem suffices for
  (2).
- The BBP identity, fixed-return normalization, and prior searches for short
  power-generator estimates are inherited from the three frozen reports.
  No source found there or in this targeted search estimates the selected
  decimal shifts in (16) or the synchronized full phase (18).

The source applicability audit is `literature-checked`; it is not an
exhaustiveness or novelty claim.

## Sharp handoff

The high-prime coordinate sum now has an explicit ordinary lift: a small
fixed grid plus a signed reciprocal-prime rational with positive leading
constant.  This removes the apparent mystery of the local inverses and
shows exactly what fixed-modulus prime distribution can and cannot see.

The same result does not prove a return.  After multiplication by (A_n),
the surviving datum is the block of decimal digits of (H_M/16) around
position (n\asymp M), synchronized with the complete dyadic coordinate
and the remaining cofactor.  PNT/AP precision and exact residue-class
pairing both stop before that datum.  A viable continuation needs a new
pointwise exponential-sum or digit-shift estimate for the exact rational in
(18), not another asymptotic count of its prime support.
