# BBP high-prime coordinate rigidity: no cofactor tuning at transfer scale

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_short_orbit_return_attack.md](bbp_short_orbit_return_attack.md),
  SHA-256
  eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d;
- [bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
  SHA-256
  d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc;
- [T69T69FixedSixteenReturn.lean](../../TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean),
  SHA-256
  fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9.

## Outcome and claim boundary

No fixed-sixteen return and no occurrence theorem for the decimal digits of
pi is proved here. Canonical V1 remains a 'conjecture'.

This branch tests one concrete CRT/Dirichlet mechanism left by the actual
odd-quotient report: keep the complete dyadic coordinate and every explicit
large-prime coordinate, then tune only the remaining small-prime cofactor to
force the selected target. The mechanism fails for an exact reason.

The new result, labeled 'proof sketch', is:

> Once the complete dyadic coordinate and all actual odd-denominator prime
> coordinates above the BBP depth are fixed, the admissible rational shadows
> form a one-dimensional lattice of spacing \(1/(16C_M)\), where
> \(\log C_M\leq(1+o(1))M\). The BBP error window has radius
> \(16^{-M}/(15(M+1)^2)\). Since \(\log16>1\), that window eventually
> contains only the actual four-pole partial sum \(B_M\).

Thus the unexpanded cofactor is small in the wrong direction for tuning: it
has far too little resolution to create a different BBP-quality shadow.
This is genuine rigidity of the exact four-pole data, but it supplies no
estimate for the selected short orbit of the unique surviving point.

The exact finite replay is an 'experiment'. The BBP formula and the prime
number theorem input are inherited from the frozen 'literature-checked'
audit; no separate novelty claim is made. Nothing here is 'machine-checked',
a 'candidate resolution', or a 'verified resolution'.

## 1. Normalized fixed-return target

Write \(\|x\|_{\mathbb T}=\min_{m\in\mathbb Z}|x-m|\). The exact target is

\[
 \boxed{
 \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0.}              \tag{1}
\]

Equivalently, for every \(\varepsilon>0\) and every \(N\), there is
\(n\geq N\) for which the norm in (1) is below \(\varepsilon\).
Unboundedness of the witnesses is automatic. If witnesses for radii tending
to zero stayed in a bounded set, one exponent would recur and force
\((10^n-16)\pi\) to be an integer. This is impossible because pi is
irrational and \(10^n\ne16\).

The audited T69/Furstenberg bridge makes (1) equivalent to canonical V1. The
equivalence is only the target normalization; it proves neither side.

Use the exact four-pole BBP sum

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},
 \qquad
 B_M=\sum_{k=0}^{M}\frac{a(k)}{16^k}.                         \tag{2}
\]

The positive tail bound is

\[
 0<\pi-B_M\leq
 E_M:=\frac{16^{-M}}{15(M+1)^2}.                              \tag{3}
\]

The prior proportional-row transfer shows that controlling the short orbit
of these exact rational sums is neither stronger nor weaker than (1).

## 2. Exact cofactor lattice

Use the reduced form and complete dyadic coordinate from the frozen reports:

\[
 B_M=\frac{P_M}{2^{K_M}R_M},
 \qquad
 D_M=2^{K_M-4},
 \qquad
 (P_M,2R_M)=1,\quad R_M\text{ odd},                         \tag{4}
\]

and

\[
 0\leq w_M<D_M,\qquad
 w_M\equiv P_MR_M^{-1}\pmod {D_M},\qquad
 c_M=\frac{P_M-R_Mw_M}{D_M}.                                \tag{5}
\]

Then exactly

\[
 16B_M=\frac{w_M}{D_M}+\frac{c_M}{R_M}.                     \tag{6}
\]

Let

\[
 S_M=\prod_{\substack{p>M\\p\mid R_M}}p,
 \qquad C_M=\frac{R_M}{S_M}.                                \tag{7}
\]

For all sufficiently large \(M\), every \(p>M\) has \(p^2>8M+5\), so its
exponent in \(R_M\) is one. The actual-quotient report proves more: once
\(M\ge48\), every possible such denominator prime survives and its additive
coordinate is one of eight explicit rational localizations.

For \(p\mid S_M\), write the actual additive coordinate as

\[
 \gamma_{M,p}\equiv
 c_M(R_M/p)^{-1}\pmod p.                                    \tag{8}
\]

Now let \(c'_M\) be any integer having all the same coordinates (8). Since
\(R_M/p\) is a unit modulo \(p\), equality of coordinates is equivalent to

\[
 c'_M\equiv c_M\pmod p.
\]

The primes in \(S_M\) are distinct, so CRT gives

\[
 c'_M-c_M=S_Mt\qquad(t\in\mathbb Z).                         \tag{9}
\]

Keep the same ambient denominator and complete dyadic coordinate and define

\[
 X_M(c'_M)=
 \frac{R_Mw_M+D_Mc'_M}{16D_MR_M}.                            \tag{10}
\]

Equations (6), (7), and (9) give the exact identity

\[
 \boxed{X_M(c'_M)-B_M=\frac{t}{16C_M}.}                     \tag{11}
\]

Hence either \(X_M(c'_M)=B_M\), or

\[
 |X_M(c'_M)-B_M|\geq\frac1{16C_M}.                           \tag{12}
\]

This argument even permits cancellation in the unpreserved small-prime
part. It therefore applies a fortiori to the narrower class in which (10)
retains the complete reduced denominator.

## 3. The cofactor has only \(e^{(1+o(1))M}\) resolution

Put \(X=8M+5\). Every prime factor of \(R_M\) comes from one of the four
linear denominators in (2), hence is at most \(X\). After (7) removes all
primes above \(M\), the remaining prime support is at most \(M\).

For \(p>5\), no two of the four linear factors at one index can both be
divisible by \(p\); their pairwise resultants have prime factors at most
five. Therefore

\[
 v_p(C_M)\leq\lfloor\log_pX\rfloor\qquad(p>5).                \tag{13}
\]

For the fixed primes \(3\) and \(5\), the harmless bound is four times the
right side. Consequently

\[
\begin{aligned}
 \log C_M
 &\leq \vartheta(M)
   +\sum_{\ell\geq2}\vartheta(X^{1/\ell})+O(\log M)\\
 &=M+o(M).                                                    \tag{14}
\end{aligned}
\]

The first equality scale uses the prime number theorem
\(\vartheta(M)=M+o(M)\). The higher powers contribute \(o(M)\): an
elementary Chebyshev bound makes their sum
\(O(\sqrt M\log M)\), which is more than sufficient.

Combining (12)--(14), every distinct coordinate-preserving shadow is at
distance at least

\[
 \frac1{16C_M}=\exp(-(1+o(1))M).                              \tag{15}
\]

The moving-cutoff localization of the actual-quotient report gives an even
stronger variant. If every explicit coordinate for
\(p>M/L_M\), \(L_M\asymp\log M\), is retained, its remaining cofactor has
\(\log C_M^\star=o(M)\), and the spacing becomes \(\exp(-o(M))\). The
simpler cutoff \(p>M\) already suffices for the comparison below and avoids
any dependence on an unspecified finite onset.

## 4. BBP-quality uniqueness

Suppose a shadow (10) has all the coordinates (8) and also satisfies the
same certified error bound as the BBP sum:

\[
 |X_M(c'_M)-\pi|\leq E_M.                                  \tag{16}
\]

Together with (3), the triangle inequality gives

\[
 |X_M(c'_M)-B_M|\leq2E_M
 =\frac{2\,16^{-M}}{15(M+1)^2}.                              \tag{17}
\]

But (14) and \(\log16>1\) imply

\[
 2E_M<\frac1{16C_M}                                         \tag{18}
\]

for every sufficiently large \(M\). Equations (12), (17), and (18) force
\(t=0\). Thus

\[
 \boxed{X_M(c'_M)=B_M\quad\text{for all sufficiently large }M.} \tag{19}
\]

This is the promised rigidity. It uses the exact selected high-prime
coordinates rather than only denominator size. In particular, the earlier
full-denominator/two-adic separator cannot be upgraded into a distinct
BBP-quality approximation to pi while also retaining these coordinates.

## 5. Verdict on the CRT/Dirichlet mechanism

The tested mechanism was to regard the remaining cofactor coordinate as a
free CRT parameter, then use nearest-point, Dirichlet, or Jacobsthal input to
choose a value whose short power orbit approaches the selected target
\(16\pi\). Equations (11)--(19) show that there is eventually no nontrivial
parameter to choose inside the only interval from which BBP transfer is
valid. A general approximation theorem can select a nearby point on the
cofactor lattice, but its mesh is exponentially larger than the entire BBP
window.

This closes that tuning route; it does **not** close (1). The one admissible
point is the actual \(B_M\), and the still-missing estimate is precisely

\[
 \min_{M\leq n\leq\lfloor(\log_{10}16)M\rfloor}
 \|(10^n-16)B_M\|_{\mathbb T}\longrightarrow0
\quad\text{along some unbounded depths}.                         \tag{20}
\]

Neither the lattice uniqueness nor Dirichlet's theorem controls the selected
residue of this unique point. A viable continuation must estimate the
actual synchronized power-generator sum, not perturb its small-prime
cofactor.

## 6. Independent exact replay

The companion
[bbp_high_prime_coordinate_rigidity_20260813_check.py](bbp_high_prime_coordinate_rigidity_20260813_check.py)
has SHA-256
b80afdebbcb75b4c45a30a11fb3f8cf618119124d4354c637e559730bf3ef157.
It imports no earlier checker. It reconstructs (2) with Python Fraction,
factors the actual reduced odd denominator, rebuilds \(w_M,c_M,S_M,C_M\),
and checks:

- the exact reduced two-adic exponent at every sampled depth;
- the prime-power bound used in (13);
- preservation of every actual \(p>M\) additive coordinate under
  \(c_M\mapsto c_M+S_M\);
- the exact spacing identity (11); and
- the exact finite comparison \(2E_M<1/(16C_M)\).

Replay from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_check.py \
      --max-depth 180

The retained run reports:

    status: PASS
    claim_label: experiment
    depths_checked: 169
    exact_small_prime_exponent_bound_checks: 3879
    high_prime_coordinate_preservation_checks: 13488
    lattice_spacing_identity_checks: 169
    observed_permanent_uniqueness_onset: 12
    minimum_log_spacing_over_two_tail: 23.74023712965329
    last_log_cofactor_over_depth: 1.067310470830356
    asserts_fixed_sixteen_return: false
    asserts_v1: false

The onset and numerical ratios are only an 'experiment'; (14)--(19), not
the finite replay, prove the asymptotic 'proof sketch' statement.

## 7. Coordination record

This branch registered the descendant-area watch
watch:ultrapi:fixed-return-mechanism-search-20260813 on
local:pi-digits for agent codex-ultrapi-fixed-return-search. The initial
poll was empty at cursor 56,944. Observation events are coordination signals
only and are not imported as mathematical evidence. The final poll was also
empty at cursor and delivered sequence 56,944, so there was no event to
acknowledge.

## Sharp handoff

The explicit BBP prime coordinates have more resolution leverage than the
earlier separators showed: together with the dyadic coordinate and the
certified Archimedean window, even the clean range \(p>M\) uniquely selects
the exact rational partial sum. This rules out cofactor steering by CRT,
Dirichlet, or Jacobsthal at the transfer scale.

What remains is narrower but still open: prove a short-orbit estimate for the
one selected \(B_M\), or derive new cross-depth information about its actual
cofactor residue. No such estimate is obtained here, so the fixed return and
canonical V1 remain a 'conjecture'.
