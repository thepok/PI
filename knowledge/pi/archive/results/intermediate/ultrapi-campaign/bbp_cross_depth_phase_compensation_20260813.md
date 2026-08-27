# BBP cross-depth phase compensation: exact boundary events and a row-averaging no-go

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
- corrected
  [bbp_odd_cofactor_short_orbit_experiment_20260813.md](bbp_odd_cofactor_short_orbit_experiment_20260813.md),
  SHA-256
  `c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3`;
- [bbp_high_prime_phase_compression_20260813.md](bbp_high_prime_phase_compression_20260813.md),
  SHA-256
  `47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  No fixed-sixteen return is proved.

This branch sought a cross-depth telescope that combines the explicit
high-prime phase with the rowwise constant 5-primary phase.  It found exact
cross-depth identities, all labelled `proof sketch`, but their implication
is compensation rather than a return.

1. The reciprocal-prime lift $H_M$ has a completely local increment:
   $H_{M+1}-H_M$ is the sum of at most four new pole events and one possible
   boundary-prime removal.  In particular, it is $O(1/M)$ pointwise.
2. After the high-prime and 5-primary CRT splits, the complete phase is
   explicit.  Across two adjacent BBP depths, the dyadic and remaining
   cofactor parts compensate the high-prime plus static 5-primary increment
   exactly, leaving only the positive $O(M^{-2})$ BBP increment.  The finite
   replay observes that the compensated increment is often macroscopic.
3. For a fixed decimal exponent $n$, every admissible depth $M$ produces a
   point within $O(n^{-2})$ of the **same** actual orbit point
   $(10^n-16)\pi$.  Consequently, the apparently two-dimensional array of
   proportional BBP rows contains only $O(X)$ asymptotically distinct
   columns among $\Theta(X^2)$ entries up to depth $X$.
4. A double mean over depths and row exponents reduces, with normalized
   error tending to zero, to a triangularly weighted one-dimensional
   exponential sum along the original decimal orbit of pi.  Depth averaging
   therefore does not create an independent source of cancellation.
5. Pigeonhole gives close **pairs**, not proximity to the prescribed target
   zero.  An exact base-ten countermodel with a 5-primary denominator makes
   this logical gap explicit.

The companion finite replay has label `experiment`.  The dated source audit
has label `literature-checked`.  Nothing here is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.

## 1. Normalized phase and exact CRT coordinates

Use

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_M=\sum_{k=0}^M{a(k)\over16^k}.                    \tag{1}
\]

Write

\[
 B_M={P_M\over2^{K_M}R_M},\qquad
 D_M=2^{K_M-4},\qquad
 16B_M=y_M+{c_M\over R_M},                          \tag{2}
\]

where $R_M$ is odd, $y_M=w_M/D_M$, and $(c_M,R_M)=1$.  Put

\[
 A_n={10^n-16\over16}=2^{n-4}5^n-1\qquad(n\ge4),
 \qquad \Phi_{M,n}=(10^n-16)B_M.                   \tag{3}
\]

Then

\[
                         \Phi_{M,n}=A_n\left(y_M+{c_M\over R_M}\right).
                                                               \tag{4}
\]

For $M\ge48$, let

\[
 \mathcal Q_M^>=\{p>M:p\mid R_M\},\qquad
 S_M^>=\prod_{p\in\mathcal Q_M^>}p,
 \qquad C_M^>={R_M\over S_M^>}.                    \tag{5}
\]

Every selected prime has exponent one.  Its actual additive coordinate is

\[
 \widehat\gamma_{M,p}\equiv
 c_M(R_M/p)^{-1}\pmod p,qquad
 \Xi_M^>=\sum_{p\in\mathcal Q_M^>}
 {\widehat\gamma_{M,p}\over p}.                    \tag{6}
\]

The frozen high-prime report gives the exact lift

\[
 \Xi_M^>\equiv{J_M\over105}+H_M\pmod1,
 \qquad
 H_M=\sum_{p\in\mathcal Q_M^>}{G_{M,p}\over p},    \tag{7}
\]

where $J_M\bmod105$ is an explicit weighted prime-count residue and each
$G_{M,p}$ is one of the eight fixed rational localizations.

Let

\[
 \eta_M\equiv c_M(S_M^>)^{-1}\pmod {C_M^>},
 \qquad C_M^>=5^{e_M}C_{0,M},
 \qquad e_M=\lfloor\log_5(8M+5)\rfloor.             \tag{8}
\]

The corrected odd-cofactor report proves that this is the complete
5-primary exponent.  Split the remaining additive coordinate by

\[
 \beta_{5,M}\equiv\eta_MC_{0,M}^{-1}\pmod {5^{e_M}},
 \qquad
 \beta_{0,M}\equiv\eta_M(5^{e_M})^{-1}\pmod {C_{0,M}}.       \tag{9}
\]

For every exponent in the proportional row, $n\ge M\ge48$, so $A_n$ is an
integer and $A_n\equiv-1\pmod {5^{e_M}}$.  Equations (2), (6)--(9) give the
complete combined phase

\[
\boxed{
 \Phi_{M,n}\equiv
 A_ny_M+A_n\left({J_M\over105}+H_M\right)
 -{\beta_{5,M}\over5^{e_M}}
 +A_n{\beta_{0,M}\over C_{0,M}}\pmod1.}            \tag{10}
\]

This is an exact reparameterization, not a distribution theorem.  The
factor 5 appearing in the auxiliary denominator $105$ is not another
5-primary CRT coordinate: it cancels internally against the rational lift
$H_M$ in (7).  Treating $J_M/105$ and the true term
$\beta_{5,M}/5^{e_M}$ as independent 5-adic samples would double-count a
representation artifact.

## 2. Exact boundary-event formula for the high-prime lift

The rational localization $G_{M,p}$ is built from four multiplier families.
For an index $k\ge49$, a prime $p>k$, and the unique applicable odd
multiplier $m$, define the new-pole weight

\[
 \varepsilon_{k,p}=
 \begin{cases}
 -8/(m4^{m-1}),&2k+1=mp,\\
 -2^{6-m}/m,&4k+3=mp,\\
 64\chi_p/(m2^{(m-1)/2}),&8k+1=mp,\\
 -64\chi_p/(m2^{(m-1)/2}),&8k+5=mp,
 \end{cases}                                      \tag{11}
\]

where $\chi_p=(2/p)$.  The four cases are mutually exclusive for $p>5$;
their pairwise resultants have no larger prime factor.  Since
$p>k$ and every displayed pole is at most $8k+5$, one has
$m\in\{1,3,5,7\}$ and $|\varepsilon_{k,p}|\le64$.

Let $\mathcal N_k$ be the primes $p>k$ dividing one of the four new pole
values in (11).  Put $q=M+1$.  Only two things can change between $H_M$ and
$H_{M+1}$:

- a pole at the new index $k=M+1$ activates; or
- the moving cutoff passes the possible boundary prime $q$.

Termwise subtraction of the localization formula therefore gives

\[
\boxed{
 H_{M+1}-H_M=
 \sum_{p\in\mathcal N_{M+1}}{\varepsilon_{M+1,p}\over p}
 -\mathbf1_{\{q\ \mathrm{\,prime},\ q\mid R_M\}}
 {G_{M,q}\over q}.}                                \tag{12}
\]

There is at most one prime larger than $M+1$ in each new pole value, so the
first sum has at most four terms.  The six-row table for $p>M$ also gives
$|G_{M,q}|\le64$.  Hence the completely uniform pointwise estimate

\[
                         |H_{M+1}-H_M|\le{320\over M+1}.       \tag{13}
\]

Formula (12) is the requested cross-depth increment for $H_M$.  It is a
local event identity, but not a return mechanism.  Its individual signs
vary, and after multiplication by $A_n\asymp10^n$ the bound (13) is far too
large to control a phase modulo one.

## 3. The full phase telescope is exact compensation

The BBP sums themselves have the one-term recurrence

\[
                         B_{M+1}-B_M={a(M+1)\over16^{M+1}}.    \tag{14}
\]

Suppose $n$ belongs to both adjacent proportional rows, that is

\[
                  M+1\le n\le\lfloor(\log_{10}16)M\rfloor.   \tag{15}
\]

Then (14) gives the exact ordinary-real increment

\[
\boxed{
 \Phi_{M+1,n}-\Phi_{M,n}
 =(10^n-16){a(M+1)\over16^{M+1}}.}                 \tag{16}
\]

The positive BBP tail estimate

\[
             0<\pi-B_M\le{16^{-M}\over15(M+1)^2}              \tag{17}
\]

and $10^n\le16^M$ in (15) imply

\[
             0<\Phi_{M+1,n}-\Phi_{M,n}
             \le{1\over15(M+1)^2}.                \tag{18}
\]

Subtracting (10) at the two depths turns (16) into a simultaneous
compensation law:

\[
\begin{aligned}
\Delta_M\Bigg[
 A_ny_M+A_n\left({J_M\over105}+H_M\right)
 -{\beta_{5,M}\over5^{e_M}}
 +A_n{\beta_{0,M}\over C_{0,M}}
\Bigg]
\equiv{}&(10^n-16){a(M+1)\over16^{M+1}}
\pmod1.                                                       \tag{19}
\end{aligned}
\]

Thus the high-prime boundary events and the changing static 5-primary
offset are not independent increments.  Whatever macroscopic jump they
make is canceled by the dyadic and residual-cofactor terms up to the tiny
positive quantity (18).  Summing (16) gives, whenever a fixed $n$ is
admissible from $M_0$ through $M_1$,

\[
\boxed{
 0\le\Phi_{M_1,n}-\Phi_{M_0,n}
 <{1\over15(M_0+1)^2}.}                            \tag{20}
\]

This is a genuine telescope, but it collapses depths onto the already-open
decimal orbit rather than driving that orbit toward zero.

## 4. Every depth column shadows one actual orbit point

Put

\[
                         z_n=(10^n-16)\pi.                       \tag{21}
\]

For every admissible pair $M\le n\le\lfloor(\log_{10}16)M\rfloor$,
(17) gives

\[
                         |z_n-\Phi_{M,n}|
 \le{1\over15(M+1)^2}.                              \tag{22}
\]

For fixed $n$, the admissible depths satisfy
$\lceil n/\log_{10}16\rceil\le M\le n$.  Their minimum is comparable to
$n$, so (20)--(22) imply

\[
 \operatorname {diam}
 \{\Phi_{M,n}:M\le n\le\lfloor(\log_{10}16)M\rfloor\}
 =O(n^{-2}),                                        \tag{23}
\]

and the whole column converges to the single point $z_n$ as its index grows.
The $\Theta(n)$ rows containing exponent $n$ are therefore repeated
approximations to one orbit point, not $\Theta(n)$ new samples.

This also closes a tempting counting shortcut.  Let

\[
 \mathcal D_X=
 \{(M,n):48\le M\le X,\ M\le n\le
 \lfloor(\log_{10}16)M\rfloor\},                  \tag{24}
\]

and let $w_X(n)$ count the depths paired with $n$.  Then

\[
 |\mathcal D_X|={\log_{10}16-1\over2}X^2+O(X),
 \qquad \#\{n:w_X(n)>0\}=O(X).                    \tag{25}
\]

Writing $e(t)=e^{2\pi it}$, the Lipschitz bound for $e(t)$ and (22) yield,
for each fixed integer $h$,

\[
\boxed{
 \sum_{(M,n)\in\mathcal D_X}e(h\Phi_{M,n})
 =\sum_n w_X(n)e(hz_n)+O_h(\log X).}               \tag{26}
\]

Indeed, the total error is bounded by a constant times

\[
 \sum_{M\le X}
 {\lfloor(\log_{10}16)M\rfloor-M+1\over(M+1)^2}
 =O(\log X).                                       \tag{27}
\]

After division by $|\mathcal D_X|$, the two means differ by $o(1)$.  Proving
Haar cancellation for the double array would therefore amount to proving a
nontrivial triangularly weighted exponential-sum theorem for the original
selected orbit of pi.  The extra depth parameter supplies multiplicity, not
independence.

## 5. Why pair pigeonhole does not hit the target zero

A pigeonhole argument on many circle points guarantees a close pair.  It
does not guarantee that either member is close to the prescribed point
zero.  The orbit is not closed under the required subtraction:

\[
 z_n-z_m=(10^n-10^m)\pi,                            \tag{28}
\]

which is not another fixed-sixteen phase in general.

There is an exact base-ten countermodel that already contains a 5-primary
denominator.  Take $x=1/45$.  Since $10^n\equiv10\pmod {45}$ for every
$n\ge1$,

\[
 (10^n-16)x\equiv-{2\over15}\equiv{13\over15}\pmod1.          \tag{29}
\]

Every pair gap is zero, while every point remains at distance $2/15$ from
zero.  Thus no argument using only pair proximity, periodicity, or repeated
columns can establish the target return.  Additional information tying a
specific orbit member to zero is indispensable.

## 6. Smooth residual moduli and periods

The 5-primary split leaves $C_{0,M}$ coprime to ten.  Since
$(\beta_{0,M},C_{0,M})=1$, the exact period of its moving term is

\[
 \operatorname {ord}_{C_{0,M}}(10).                            \tag{30}
\]

The stronger square-root cutoff from the corrected odd-cofactor report
leaves a modulus $C_{0,M}^{\square}$ satisfying

\[
 P^+(C_{0,M}^{\square})\le\sqrt{8M+5},\qquad
 \log C_{0,M}^{\square}=O(\sqrt M\log M)=o(M).                 \tag{31}
\]

But (31) gives only

\[
 \operatorname {ord}_{C_{0,M}^{\square}}(10)
 \le C_{0,M}^{\square}=\exp(o(M)),                             \tag{32}
\]

and an $\exp(o(M))$ period can still be much longer than the $O(M)$ row.
Even when every individual prime-power period is at most $O(M)$, their least
common multiple can have the full size in (32).  Pigeonhole on that product
again supplies a pair, not the prescribed inhomogeneous target contributed
by the other three terms in (10).

The finite replay computes both the $p>M$ and square-root residual periods.
Every one tested through depth 360 exceeded its row length.  This has label
`experiment`, not an asymptotic lower bound.  Smoothness alone supplies no
theorem forcing the target into the first $(\log_{10}16-1)M+O(1)$ powers.

## 7. Exact finite replay and falsification record

The standalone
[bbp_cross_depth_phase_compensation_20260813_check.py](bbp_cross_depth_phase_compensation_20260813_check.py)
imports no branch checker.  It reconstructs the reduced BBP rational, every
actual $p>M$ coordinate, the $1/105$ lift, the true 5-primary split, both
residual periods, and the complete phase.  It verifies:

- 47,312 actual high-prime coordinates;
- 13,192 complete phase and static 5-primary identities;
- all new-pole and boundary-removal terms in (12);
- 12,806 adjacent compensation identities (16) and (19);
- every fixed-exponent column telescope (20);
- exact double-array weights and the error ledger behind (26);
- pair-versus-zero gaps and the exact countermodel (29).

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813_check.py \
  --max-depth 360
```

Retained output:

```text
status: PASS
bounded_claim_label: experiment
cross_depth_identities_label: proof sketch
depth_range: [48, 360]
actual_high_coordinate_checks: 47312
high_grid_lift_checks: 313
five_static_phase_checks: 13192
full_phase_decomposition_checks: 13192
boundary_event_checks: 540
boundary_prime_removal_checks: 57
harmonic_increment_sign_counts: positive=145,negative=142,zero=25
nonzero_grid_jumps: 188
maximum_depth_scaled_harmonic_increment: 66.016240594140825
adjacent_phase_telescope_checks: 12806
high_five_compensation_checks: 12806
macroscopic_high_five_jumps: 6090
maximum_high_five_jump: 0.499855002416626
column_telescope_checks: 386
maximum_normalized_adjacent_phase_increment: 0.216212074114337
maximum_normalized_column_diameter: 0.230321967800901
period_checks: 313
periods_longer_than_row: 313
log_order_over_log_modulus_range: [0.240002717422290, 0.421204118201472]
sqrt_period_checks: 313
sqrt_periods_longer_than_row: 313
sqrt_log_order_over_log_modulus_range: [0.570460448333894, 0.676858388242404]
total_double_array_points: 13192
distinct_exponent_columns: 386
transfer_error_ledger_upper_bound: 0.027712737088701
pair_gap_checks: 313
rows_pair_gap_strictly_smaller_than_zero_gap: 313
largest_zero_to_pair_gap_ratio: 878.410913178599344
strongest_pair_gap_example: (167, 2109, 2100, 2114)
pair_gap_record_sha256:
  2303859e663117acc2e094dca8fa676bab00311f38c6d4ee601b856474d1bfd9
pigeonhole_countermodel_checks: 100
asserts_fixed_sixteen_return: false
asserts_v1: false
```

The four fields of `strongest_pair_gap_example` are the depth, the bit length
of the distance-to-zero numerator, the bit length of the closest-pair
numerator, and the common denominator bit length.

The sign changes, period ratios, pair gaps, and macroscopic component jumps
are finite `experiment` only.  The exact identities (10), (12), (16), (20),
and (26), with their displayed bounds, are the `proof sketch` results.

## 8. Dated literature and mathlib applicability audit

Search date: **2026-08-13 UTC**.

- The frozen actual-quotient report already audits
  [Konyagin--Shparlinski, *On the consecutive powers of a primitive root:
  gaps and exponential sums* (2012)](https://doi.org/10.1112/S0025579311002117).
  Its prime-modulus primitive-root hypotheses do not hold for the changing
  composite $C_{0,M}$, and it does not include the synchronized high-prime,
  dyadic, and static target in (10).
- A targeted fresh search found
  [Bhakta--Shparlinski, *Exponential Sums with Sparse Polynomials and
  Distribution of the Power Generator*
  (2024)](https://arxiv.org/abs/2412.07989).  Its power-generator discrepancy
  theorems concern a different recurrence and are nontrivial only at lengths
  exceeding a fixed positive power of the prime modulus under stated order
  conditions.  Those hypotheses are not verified for the changing composite
  residual modulus here; the audit permits regimes in which the available
  $O(M)$ length is below every fixed positive power of that modulus.  The
  theorem also does not estimate the full synchronized phase (10).
- The inherited Lagarias/BBP literature explains why a pointwise orbit
  estimate would suffice, but supplies no estimate for (10) or (26).

A same-date mathlib search found general `orderOf`, cyclic-group, exponent,
and geometric-sum lemmas under `Mathlib/GroupTheory` and
`Mathlib/NumberTheory`.  It found no formalized short power-generator
discrepancy theorem applicable to (30).  No formal declaration is added in
this branch.

This applicability record is `literature-checked`; it is not an exhaustive
novelty claim.

## Sharp handoff

There is a rigorous cross-depth telescope, but it points in the wrong
direction for a breakthrough.  The explicit high-prime and static
5-primary phases do not evolve as independent samples.  Their boundary
jumps are forced to cancel against the dyadic and remaining cofactor phases,
leaving each depth column within $O(n^{-2})$ of one pre-existing decimal
orbit point of pi.

Consequently, averaging over depths merely reweights that one-dimensional
orbit, pair pigeonhole misses the prescribed target, and smooth residual
periods can still dwarf the available row.  A viable continuation still
needs a genuinely pointwise inhomogeneous estimate for one selected phase
in (10); boundary-event telescoping, period counting, or unanchored
pigeonhole alone cannot supply it.
