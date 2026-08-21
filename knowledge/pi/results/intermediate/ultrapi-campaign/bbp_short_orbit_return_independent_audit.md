# Independent audit: BBP short-orbit return and odd-quotient separator

Audit date: **2026-08-12 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local question has no external source URL; none is invented.

Audited corrected artifacts:

- [bbp_short_orbit_return_attack.md](bbp_short_orbit_return_attack.md),
  SHA-256
  `eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d`;
- [bbp_short_orbit_return_check.py](bbp_short_orbit_return_check.py),
  SHA-256
  `cb21ab170454f0260e5c12f15eb9403c9fa57e932153bf3403e8ea95c35bc550`.

Independent replay:

- [bbp_short_orbit_return_independent_check.py](bbp_short_orbit_return_independent_check.py),
  SHA-256
  `c044e66b2fd64b9bb45ec15c57b11abc6370a181bbc32a38cbe2bb1a6aa13d5f`.

## Verdict

**PASS after four scoped corrections.**

The central mathematics rederives.  In particular, the triangular minimum is
equivalent to the fixed-sixteen return, the reduced affine recurrence and its
prime-power discrete-log rule are exact, the reflected function is a
two-adic isometry, the (256D_M) coordinate and complementary quotient split
are exact, and the Kanold lift really can preserve the complete reduced
denominator and every bit of the derived two-adic congruence while converging
to a uniformly nonreturning limit.

The pre-audit report, SHA-256
`30f4ff821b5dac3a2903f64f4d13dd9678f7344af14d286524330e42705ba23c`,
required four repairs. All four are present in the corrected artifact pinned
above.

1. \(E_M\) is now defined only for \(M\ge5\), avoiding the initial empty
   indexing sets without changing the limit.
2. The false attribution of “certified disjoint prime bands” to the
   fixed-multiplier audit is removed. The corrected report includes the exact
   two-band proof of the \(10M/3\) lower bound given in Section 6 below.
3. In (38), the input is only a lower bound for \(R_M\), so the corrected
   display uses the required upper bound:

   \[
    |B'_M-\beta|
    =O\!\left({2^{\omega(R_M)}\over R_M}\right)
    \le \exp\!\left((-10/3+o(1))M\right)
    =o\!\left({16^{-M}\over M^2}\right).              \tag{A0}
   \]

   The literal equality
   `= exp(-10M/3+o(M))` is not implied and is empirically not the actual
   denominator scale.
4. “Same complete p-adic data” is corrected to **same complete two-adic data
   derived here**, together with the same denominator and local cancellation
   pattern. The report now states that replacing \(c_M\) by
   \(c_M+256t_M\) generally changes \(c_M\bmod R_M\) and does not preserve
   the odd-prime numerator coordinates.

These are real provenance, quantifier, inequality, and scope corrections,
but none damages the separator once stated correctly.  All infinite
deductions remain a `proof sketch`; the finite replays remain an
`experiment`; and the bounded source check is `literature-checked` as of the
audit date.  No fixed return or V1 statement is proved.  Canonical V1 remains
a `conjecture`.

## 1. Triangular minimum if and only if fixed return

Write

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_M=\sum_{k=0}^M {a(k)\over16^k}.
\]

For (k\ge1), (a(k)>0), and direct expansion gives

\[
\begin{aligned}
 &(2k+1)(4k+3)(8k+1)(8k+5)
      -k^2(120k^2+151k+47)\\
 &\hspace{12mm}=392k^4+873k^3+665k^2+194k+15>0.
\end{aligned}
\]

Hence (a(k)<k^{-2}), and the positive BBP tail satisfies

\[
 0<\pi-B_M
 \le {1\over(M+1)^2}\sum_{k=M+1}^\infty16^{-k}
 ={16^{-M}\over15(M+1)^2}.                            \tag{A1}
\]

If (5\le n\le\lfloor M\log_{10}16\rfloor), then

\[
 |10^n-16|\,|\pi-B_M|\le {1\over15(M+1)^2}.          \tag{A2}
\]

Distance to the nearest integer is 1-Lipschitz, so (A2) is exactly the
uniform transfer estimate used in the report.

Now define (E_M) for (M\ge5).  If

\[
 \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0,
\]

then, for each tolerance, choose one sufficiently large good (n).  For all
sufficiently large (M), that fixed (n) lies in the triangle and (A2)
shows (E_M) is below the tolerance.  Thus (E_M\to0).

Conversely, choose a minimizer (n_M).  If infinitely many (n_M) were in
a bounded set, a constant subsequence plus (A1) would give
((10^n-16)\pi\in\mathbb Z) for one fixed (n\ge5), contradicting
irrationality of pi.  Therefore an unbounded subsequence of minimizers tends
to infinity, and (A2) transfers its phase to pi.  This proves

\[
 E_M\to0
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0. \tag{A3}
\]

The previously audited Furstenberg bridge makes the right side equivalent to
V1; it does not prove either side.  Thus the report correctly identifies the
short triangle as the original return bottleneck, not an easier finite
subproblem.

## 2. Reduced recurrence, gcds, and discrete logs

Assume the separately audited all-depth valuation formula and write

\[
 B_M={P_M\over2^{K_M}R_M},\qquad
 K_M=4M-v_2(M+1),\qquad (P_M,2R_M)=1,
\]

with (R_M) odd.  For (M\ge2), put

\[
 D_M=2^{K_M-4},\qquad
 A_n={10^n-16\over16}=2^{n-4}5^n-1\quad(n\ge5).
\]

The number (A_n) is odd and (A_{n+1}=10A_n+9).  Since the only possible
odd cancellation in

\[
 (10^n-16)B_M={A_nP_M\over D_MR_M}
\]

is (g_{M,n}=(A_n,R_M)), lowest terms are

\[
 U_{M,n}={A_nP_M\over g_{M,n}},\qquad
 Q_{M,n}=D_M{R_M\over g_{M,n}}.                       \tag{A4}
\]

Substitution of (A_{n+1}=10A_n+9) gives the displayed recurrence exactly:

\[
 U_{M,n+1}={10g_{M,n}U_{M,n}+9P_M\over g_{M,n+1}}.
\]

Before reduction, (t_{M,n}\equiv A_nP_M\pmod{D_MR_M}) therefore obeys

\[
 t_{M,n+1}\equiv10t_{M,n}+9P_M\pmod{D_MR_M}.          \tag{A5}
\]

For every (p^e\mid R_M), both (16) and (P_M) are units modulo (p),
so

\[
 p^e\mid g_{M,n}
 \quad\Longleftrightarrow\quad
 10^n\equiv16\pmod{p^e}.                              \tag{A6}
\]

Also (A_n\equiv-1\pmod5), so 5 never enters the gcd; and modulo 3 one has
(10^n\equiv16\equiv1), so a factor 3 in (R_M) always cancels once,
with higher powers still governed by (A6).  There is no ordinary-versus-
circle-norm mismatch: the least absolute residue of (t_{M,n}) divided by
(D_MR_M) is exactly the circle phase.

## 3. The two-adic isometry and all (256D_M) bits

The all-depth report proves in the restricted power-series ring that

\[
 F(X)=\sum_{j\ge0}16^j a(X-1-j),\qquad F(0)=0,
 \qquad F(X)\equiv X\pmod2.                           \tag{A7}
\]

The last congruence is coefficientwise.  Consequently
(F(X)=X+2G(X)) for (G\in\mathbb Z_2\langle X\rangle).  For
(x,y\in\mathbb Z_2), restricted analytic division gives

\[
 G(x)-G(y)=(x-y)H(x,y),\qquad H(x,y)\in\mathbb Z_2.
\]

Therefore

\[
 F(x)-F(y)=(x-y)(1+2H(x,y)),\qquad
 v_2(F(x)-F(y))=v_2(x-y).                             \tag{A8}
\]

Thus (F) really is an isometry and induces a permutation modulo every
power of 2.  This strengthens the earlier origin-based valuation without
introducing an Archimedean conclusion.

Set (m=M+1) and (r_M=v_2(m)).  Reversing the finite sum shows

\[
 16^MB_M=\sum_{j=0}^{M}16^j a(M-j)=2^{r_M}{P_M\over R_M}.
\]

The omitted terms of (F(m)) start at (j=m), and every (a(m-1-j)) is
two-adically integral.  Hence

\[
 v_2(F(m)-16^MB_M)\ge4m.                              \tag{A9}
\]

After division by (2^{r_M}), this yields

\[
 P_MR_M^{-1}\equiv {F(M+1)\over2^{r_M}}
       \pmod {2^{,4(M+1)-r_M}}.                      \tag{A10}
\]

Since

\[
 2^{4(M+1)-r_M}=2^8D_M=256D_M,                       \tag{A11}
\]

the report's “eight extra bits” count is exact.  In particular, the residue
(w_M=P_MR_M^{-1}\bmod D_M) and the next eight bits are fixed.  Dividing
((A10)-w_M) by (D_M) is legitimate and gives precisely

\[
 c_MR_M^{-1}\equiv
 {D_M}^{-1}\left({F(M+1)\over2^{r_M}}-w_M\right)
 \pmod{256},                                         \tag{A12}
\]

where (c_M=(P_M-R_Mw_M)/D_M).  This is full precision for the congruence
actually supplied by (A9); it is not a claim to know the odd coordinate
(c_M\bmod R_M).

## 4. Complementary quotient and Fourier factorization

The defining equation for (c_M) rearranges without approximation to

\[
 16B_M={w_M\over D_M}+{c_M\over R_M}.                 \tag{A13}
\]

Taking fractional parts after subtracting (w_M/D_M) gives

\[
 {c_M\bmod R_M\over R_M}
 =\left\{\{16B_M\}-{w_M\over D_M}\right\}.           \tag{A14}
\]

Thus the missing odd quotient is exactly the Archimedean position in a
shifted (R_M)-grid.  Multiplication by (A_n) gives the report's phase
split, and applying (e(h\cdot)) gives the product of a dyadic factor and an
odd-quotient factor.  Both are driven by the same (A_n), so cancellation in
the first exponential sum alone says nothing about their product.  The
ordinary identity (A13), its circle reduction (A14), and the Fourier
factorization all agree; no lattice has been changed silently.

## 5. Kanold lift, factor (256), and complete denominator

Let (j(q)) denote the Jacobsthal run length in the report's convention.
Kanold's Satz 4 gives

\[
 j(q)\le2^{\omega(q)}.                                \tag{A15}
\]

The primary scan was independently refetched during this audit; its bytes
have SHA-256
`dd75cd1ff949feff49b0e7ca9ca2379518e8f65e075ee99a7df4f247c80c97cb`,
matching the earlier source audit.  Coprimality depends only on
(\operatorname{rad}(q)), so the statement applies unchanged to prime
powers in (R_M).

Because 256 is a unit modulo (R_M), the condition
((c_M+256t,R_M)=1) is a translate of the condition that one ordinary
integer be coprime to (R_M).  Applying (A15) to a run adjacent to

\[
 T_M={R_M(\beta-B_M)\over16}
\]

therefore supplies an integer (t_M) with

\[
 (c_M+256t_M,R_M)=1,qquad
 |t_M-T_M|=O(2^{\omega(R_M)}).                        \tag{A16}
\]

With (c'_M=c_M+256t_M), define

\[
 P'_M=R_Mw_M+D_Mc'_M,qquad
 B'_M={P'_M\over16D_MR_M}.
\]

Since (P_M=R_Mw_M+D_Mc_M), the scaling is

\[
 B'_M-B_M={D_M(256t_M)\over16D_MR_M}
          ={16t_M\over R_M}.                          \tag{A17}
\]

The factor is (16), not (1/16) or 256.  Moreover, (w_M) is odd,
because it is the product of two odd units modulo the nontrivial power of 2
(D_M).  Hence (P'_M) is odd.  Modulo (R_M), it is (D_Mc'_M), a unit
by (A16).  Thus

\[
 (P'_M,16D_MR_M)=1,                                  \tag{A18}
\]

so (B'_M) has exactly the same complete reduced denominator
(2^{K_M}R_M) as (B_M).

Finally,

\[
 16^M(B'_M-B_M)={2^{4(M+1)}t_M\over R_M},             \tag{A19}
\]

whose two-adic valuation is at least (4(M+1)).  Combining (A19) with
(A9) proves that (B'_M) preserves the entire congruence (A10), including
the 256 extra bits.  It does not preserve (c_M\bmod R_M); changing that
coordinate is the separator's purpose.

## 6. Missing prime-band proof and corrected approximation exponent

Every prime divisor of (R_M) is at most (8M+5), because the odd
denominator of the sum can acquire primes only from the four displayed
linear factors.  Hence

\[
 \omega(R_M)\le\pi(8M+5)=o(M).                       \tag{A20}
\]

The frozen report does not support its lower bound for (R_M), but it can be
proved directly.  Use these disjoint sets:

\[
\begin{aligned}
 \mathcal P_{1,M}={}&
 \{p:4M+3<p\le8M+1,\ p\equiv1\pmod8\}\\
 &\cup\{p:4M+3<p\le8M+5,\ p\equiv5\pmod8\},\\
 \mathcal P_{2,M}={}&
 \{p:(8M+5)/3<p\le4M+3\}.
\end{aligned}                                         \tag{A21}
\]

For (p\in\mathcal P_{1,M}), exactly one denominator factor among all
(0\le k\le M) is divisible by (p): it is (8k+1=p) or (8k+5=p).
The other linear factors are below (p), and even (2p) exceeds the largest
factor.  At these roots the coefficient numerator has residues

\[
 (120k^2+151k+47)\big|_{k=-1/8}=30,qquad
 (120k^2+151k+47)\big|_{k=-5/8}=-1/2.                 \tag{A22}
\]

They are nonzero modulo every prime in the band.

For (p\in\mathcal P_{2,M}), one has (p>2M+1) and
(3p>8M+5).  Since every linear factor is odd, no multiple other than (p)
can occur.  According to the residue class, the unique factor is
(4k+3=p), (8k+1=p), or (8k+5=p).  The additional root residue is

\[
 (120k^2+151k+47)\big|_{k=-3/4}=5/4,                 \tag{A23}
\]

again nonzero in this band.  In both bands, the unique singular BBP summand
has (p)-adic valuation (-1), every other summand is (p)-integral, and
(16^{-k}) is a unit.  The unequal-valuation rule therefore gives

\[
 v_p(B_M)=-1,qquad p\mid R_M                         \tag{A24}
\]

with multiplicity exactly one.

The PNT in progressions modulo 8 applied to the first band and ordinary PNT
applied to the second now give

\[
\begin{aligned}
 \sum_{p\in\mathcal P_{1,M}}\log p&=(2+o(1))M,\\
 \sum_{p\in\mathcal P_{2,M}}\log p&=(4/3+o(1))M,
\end{aligned}
\]

and hence

\[
 \log R_M\ge(10/3+o(1))M.                            \tag{A25}
\]

This is the exact missing proof.  Combining (A16), (A17), (A20), and (A25)
gives only the upper bound (A0), which is sufficient because
(10/3>\log16).  Uniformly over
(5\le n\le\lfloor M\log_{10}16\rfloor),

\[
 |(10^n-16)(B'_M-\beta)|
 \le\exp((\log16-10/3+o(1))M)=o(1).                  \tag{A26}
\]

Thus the separator has the advertised stronger-than-BBP approximation rate
after the equality sign in the original display is corrected.

## 7. Rational and Liouville nonreturning limits

For \(\beta=1/10\) and every \(n\geq1\),

\[
 {10^n-16\over10}=10^{n-1}-{8\over5}
 \quad\Longrightarrow\quad
 \left\|{10^n-16\over10}\right\|_{\mathbb T}={2\over5}. \tag{A27}
\]

The reverse triangle inequality for the circle norm and (A26) therefore
give the uniform short-orbit gap (2/5-o(1)) for (B'_M).

The second proposed limit is exactly the classical Liouville constant

\[
 \beta=\sum_{r\ge1}10^{-r!}
      ={1\over10}+\sum_{r\ge2}10^{-r!}.               \tag{A28}
\]

Its non-eventually-periodic decimal expansion and factorial truncations give
the standard Liouville-transcendence proof.  Every shifted decimal tail
(x_n=\{10^n\beta\}) has only zero and one digits, so

\[
 0\le x_n\le1/9.                                      \tag{A29}
\]

Also (11/100<\beta<1/9), which implies

\[
 y=\{16\beta\}\in(3/5,7/9).                          \tag{A30}
\]

Set (d=y-x_n).  Equations (A29)--(A30) give

\[
 d>3/5-1/9=22/45>2/9,
 \qquad 1-d>1-7/9=2/9.
\]

Therefore, for every (n\ge0),

\[
 \|(10^n-16)\beta\|_{\mathbb T}
 =\|x_n-y\|_{\mathbb T}>2/9.                         \tag{A31}
\]

This checks both the strict constant and the endpoint (n=0).  Applying the
same lift and (A26) retains a positive gap while converging faster than the
BBP tail to a fixed transcendental limit.

## 8. Cross-depth and source applicability

The adjacent-depth identity is immediate:

\[
 (10^n-16)(B_{M+1}-B_M)
 ={(10^n-16)a(M+1)\over16^{M+1}}.                     \tag{A32}
\]

On the transferable triangle, (10^n\le16^M) and
(a(M+1)=O(M^{-2})), so (A32) is (O(M^{-2})).  Adjacent rows therefore
shadow the same decimal orbit; they are not independent samples.  The
nonnesting examples for (R_M) are exact finite falsifiers of a simpler
common-reduced-modulus recurrence but are only an `experiment`.

The source scopes were checked as follows.

- The pinned Bailey--Borwein--Plouffe PDF has SHA-256
  `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`
  and supplies the series, not decimal distribution.
- The pinned Barsky--Muñoz--Pérez-Marco PDF has SHA-256
  `64629d2323ad8e1a11b457b3572c1568993c29b37e3959e8e9d31fa03d06fa2f`
  and supports logarithmic/null-formula provenance, not the new two-adic
  denominator theorem or a return.
- Kanold supplies (A15), not the prime-band theorem or any information about
  the actual BBP quotient.
- The pinned Lagarias PDF has SHA-256
  `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9`.
  Its Theorem 4.1 explicitly makes the digit-density conclusion conditional
  on a weak or strong dichotomy hypothesis; it supplies no unconditional
  fixed-pi return.

The pre-audit source fault was the false cross-reference for the prime bands;
it is removed from the corrected report. The replacement proof (A21)--(A25)
is elementary apart from the stated classical PNT/AP input. No checked
source controls the selected (O(M))-term Fourier
sum for the actual quotient (c_M\bmod R_M).

## 9. Independent replay

The independent checker imports no branch code.  It rechecks the immutable
source hash, finite isometry shadows, the all-depth denominator formula, all
(256D_M) coordinate bits, the quotient split, the affine recurrence, every
prime-power form of (A6), 4,018 exact instances of the repaired prime bands,
the factor-16 separator lift and complete denominator, and finite rational
and Liouville gap shadows.

Run:

    python -m py_compile \
      work/ultrapi-resume/bbp_short_orbit_return_independent_check.py
    python work/ultrapi-resume/bbp_short_orbit_return_independent_check.py

Retained output:

    claim_status=experiment
    source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
    isometry_pair_checks=43435
    all_depth_valuation_checks=119
    full_256_coordinate_checks=119
    quotient_split_checks=119
    affine_recurrence_checks=16188
    prime_power_discrete_log_checks=842383
    clean_prime_band_survival_checks=4018
    separator_phase_checks=8210
    largest_finite_lift_distance=9
    liouville_shadow_checks=121
    all independent exact checks passed

These finite rows do not prove the analytic two-adic identity, Kanold's
theorem, the PNT/AP asymptotic, or any return for pi.

## Sharp independent conclusion

After the four stated amendments, this branch is a sound `proof sketch` of a
strong method separator.  It exposes the complete two-adic coordinate
available from the reflected BBP null identity and proves that the remaining
odd quotient can be varied, while retaining the actual full denominator and
all that two-adic precision, to approximate rational or transcendental
limits whose entire short orbit stays away from zero.

That separator does not preserve the exact four-pole BBP recurrence or the
actual odd numerator coordinate.  Consequently it does not refute a future
estimate using the true (c_M\bmod R_M); it proves only that the presently
derived denominator, two-adic, and local-gcd data cannot select that phase.
Obtaining decay for the actual first (O(M)) affine iterates is, by (A3), the
fixed-sixteen return and hence V1 itself.  No such decay is proved here, so
V1 remains a `conjecture`.
