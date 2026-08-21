# BBP growing-band joint harmonics: exact diagonal collapse and one-sided barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL;
none is invented here.

Frozen inputs:

| input | SHA-256 |
|---|---|
| [Peres--Yang endpoint attack](peres_yang_bbp_endpoint_attack_20260813.md) | `3721a8e1a43fd3c4244ab8ffa11e0da0581e169d037cdf04f85e18ec1a539b60` |
| [full-phase endpoint experiment](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [three-primary twisted sum](bbp_three_primary_twisted_sum_20260813.md) | `0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12` |
| [complementary Fourier attack](bbp_complement_fourier_attack_20260813.md) | `eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a` |
| [independent Peres--Yang audit](peres_yang_bbp_endpoint_attack_20260813_independent_audit.md) | `8c138103b4b2afb3e2b6e559c147c9b1ed69495e3689c1d00fa9fe50cee062ff` |

## Outcome and claim boundary

No growing-band bound, endpoint gap law, fixed-sixteen return, or occurrence
theorem for every finite decimal word in pi is proved. Canonical V1 remains a
`conjecture`.

The branch gives four substantive conclusions, with label `proof sketch`.

1. The exact quantized sums in PYB15 do not retain the clean BBP
   primary/complement factorization. Cell rounding contributes a third
   unit-modulus factor which depends on the **full** BBP phase. At the needed
   harmonics (h\asymp K), that factor is not a small perturbation.
2. In the unquantized replacement, the joint family with primary coefficient
   (ha_e\bmod3^e) and complement (W_e^h) collapses exactly to the ordinary
   power sums of the full endpoint points. Artificial primary-coefficient
   averaging controls each horizontal slice, but the actual data lie on one
   diagonal and can be exceptional on every slice.
3. Bare energy and symmetric absolute-moment routes fail on the actual finite
   rows for structural, not precision, reasons. At (e=8,10,12), the
   positive centered cell peak already exceeds (L), so a symmetric
   certificate (\|F\|_\infty<L) is false even though every cell is occupied.
   At (e=12), the negative trough is only (K) above the forbidden value
   (-L). Any argument which approximates this near-boundary trough must
   therefore have one-sided error smaller than (K\asymp L/\log L), or use
   an exact nonvanishing/integrality mechanism. A remainder stated only as
   (o(L)) around the boundary does not resolve that margin.
4. On all six exact rows through (e=8), there is a small alternative
   coprime numerator with the **same complete reduced denominator** and the
   **same actual three-primary additive coordinate** as BBP. It retains the
   complete primary grid and primitive growing-band coefficients at every
   high denominator prime, yet its full row lies in a microscopic arc and
   misses every other equal cell. Thus primary nesting, modulus size,
   coprimality, local nonannihilation, and the power law (W^h) do not suffice
   without the actual joint complementary numerator.

The ten actual-row checks and six alternative-numerator checks have label
`experiment`. They are finite falsifiers, not evidence for an asymptotic
theorem. No Lean declaration, axiom audit, verification gate, or
`ultrapi.md` was changed by this branch.

## 1. Normalized target and growing bandwidth

Canonical V1 asks that for every (P\ge1) and every (0\le k<10^P), there
is an (n\ge0) such that

\[
             \left\lfloor10^P\{10^n\pi\}\right\rfloor=k,       \tag{GB1}
\]

with leading zeroes retained. It asks for one contiguous occurrence of every
finite word, not normality and not an occurrence of every infinite string.

On one BBP endpoint row, let (x_1,\ldots,x_L\in[0,1)) be the complete
phases. Put

\[
 K=\left\lfloor {L\over\log L}\right\rfloor,\qquad
 q_n=\lfloor Kx_n\rfloor,\qquad
 c_a=\#\{n:q_n=a\}.                                      \tag{GB2}
\]

With (\zeta_K=e^{2\pi i/K}) and

\[
 C_h=\sum_{n=1}^L\zeta_K^{hq_n},\qquad
 F_a=\sum_{h=1}^{K-1}C_h\zeta_K^{-ha},                   \tag{GB3}
\]

finite Fourier inversion is the exact identity

\[
                         \boxed{F_a=Kc_a-L.}               \tag{GB4}
\]

The half-open convention includes the leading-zero cell (a=0) without an
endpoint ambiguity. Every cell is occupied exactly when

\[
                         \min_a F_a>-L.                    \tag{GB5}
\]

At this bandwidth, one occupied point in the least populated cell gives only
the additive safety margin (F_a+L=K\asymp L/\log L). Since all-cell
coverage implies only (G\le2/K), the sharp constant-one target

\[
                         G\le(1+\varepsilon){\log L\over L}               \tag{GB5a}
\]

would use, for example,
(K\sim2L/((1+\varepsilon)\log L)). The finite table below retains
(K=\lfloor L/\log L\rfloor), where every audited row is occupied, to
falsify information-losing moment criteria. The factor of two does not alter
the growing-band obstruction, but it matters for a claimed sharp constant.

## 2. Quantization destroys the clean CRT product at high harmonics

Write (z_n=e(x_n)), where (e(t)=e^{2\pi it}), and put

\[
                       \theta_n=\{Kx_n\}\in[0,1).          \tag{GB6}
\]

Then exactly

\[
 \zeta_K^{q_n}=e(q_n/K)
 =z_n e(-\theta_n/K).                                    \tag{GB7}
\]

For a reduced endpoint denominator (D=3^eC), ((3,C)=1), the unquantized
BBP phase has the CRT split

\[
 z_n=e_{3^e}(aR_n)W_n,qquad R_n=10^n-16,                 \tag{GB8}
\]

where (a\) is the selected primary coefficient and (W_n) is the product
of all complementary coordinates. Equations (GB3), (GB7), and (GB8) give

\[
 \boxed{
 C_h=\sum_n e_{3^e}(haR_n)W_n^h
                  e(-h\theta_n/K).}                       \tag{GB9}
\]

The last factor depends on the full phase (x_n), hence on both sides of the
CRT split. Moreover,

\[
 \left|C_h-\sum_n z_n^h\right|
 \le L\min\left(2,{2\pi h\over K}\right).                \tag{GB10}
\]

For (h\asymp K), (GB10) is (O(L)), the same size as the forbidden trough
in (GB5). Summing such errors over the full band is worse. Therefore the
quantized certificate cannot be transferred to classical BBP exponential
sums by treating cell rounding as a small error.

A Selberg--Vaaler minorant avoids the discontinuous factor in (GB9), but it
still needs unquantized harmonics through (h\asymp K). Its interval main
term is only (L/K\asymp\log L). Even hypothetical square-root bounds

\[
                         |S_h|\ll\sqrt L\quad(h\le K)       \tag{GB11}
\]

do not survive a triangle sum: (\sum_{h\le K}|S_h|/h) can be of order
(\sqrt L\log K\), much larger than (\log L). A successful sharp argument
must retain cancellation among the harmonics, not merely bound them one at a
time.

## 3. Exact diagonal collapse of the joint harmonic family

For the unquantized sums define

\[
 S_h=\sum_n z_n^h
     =\sum_n e_{3^e}(haR_n)W_n^h.                         \tag{GB12}
\]

This displays both pieces requested by the growing-band proposal: the
primary coefficient is (ha\bmod3^e), and the complement is the power
(W^h). It also shows their exact limitation. For any coefficients
(\lambda_h),

\[
 \sum_h\lambda_hS_h
 =\sum_n P(z_n),\qquad P(z)=\sum_h\lambda_hz^h,            \tag{GB13}
\]

and the quadratic family is

\[
 \sum_h\lambda_h|S_h|^2
 =\sum_{m,n}\sum_h\lambda_h(z_m\overline z_n)^h.          \tag{GB14}
\]

Thus joint harmonic orthogonality recombines the CRT factors into the full
pair spacings. It does not yield a product of independent local savings.

To see the diagonal selection explicitly, set

\[
 \mathcal T(h,b)=\sum_n e_{3^e}(bR_n)W_n^h.               \tag{GB15}
\]

Ramanujan averaging over artificial (b\) controls a horizontal slice with
(h) fixed, as in the frozen selected-unit theorem. The BBP value is the
single diagonal point

\[
                           S_h=\mathcal T(h,ha).            \tag{GB16}
\]

An (O(1)) exceptional set on every horizontal slice permits all (K)
diagonal points to be exceptional. The formal obstruction is sharp: for the
artificial complement (W_n=\overline{e_{3^e}(aR_n)}), equation (GB16)
equals (L) for every (h). That complement is not asserted to be BBP; it
shows that two-parameter orthogonality alone has no diagonal selector.

The same issue blocks a direct dual-large-sieve repair. Applied after
(GB14), the ordinary large sieve needs separation of the **full** points
(z_n). The equal-cell labels deliberately collide, while distinctness of
the unquantized rational points gives only a full-denominator-scale spacing,
exponentially smaller than (1/K). Separation of the primary projection
cannot replace full separation because the complementary coordinate may
cancel it.

## 4. Why energy and symmetric higher moments miss the actual event

Parseval applied to (GB4) gives

\[
 E_K:=\sum_{h=1}^{K-1}|C_h|^2
 =K\sum_a c_a^2-L^2.                                    \tag{GB17}
\]

If one cell is empty, Cauchy--Schwarz gives

\[
                              E_K\ge {L^2\over K-1}.       \tag{GB18}
\]

The strict reverse is sufficient but already fails on eight of the ten
audited actual rows. Scalar energy is even less informative than that
threshold comparison suggests. At (L=93,K=20), the one-empty histogram

\[
                       (6^6,5^{11},1^2,0)                        \tag{GB18a}
\]

(exponent notation means repeated entries) has the exact same value
(E_K=1211) as the actual completely covered pre-drop histogram. More
generally, a bare even-moment argument controls
the symmetric quantity (\max_a|F_a|). It cannot prove (GB5) via
(\max|F|<L) once an occupied, overloaded cell has (F_a\ge L).

All entries below have label `experiment`. The shadow labels at (e=10,12)
are certified for the rational (B_M) phase, not merely for the pi centers.

| (e) | row | (L) | (K) | min/max (c_a) | (\min F_a) | (\max F_a) | energy test (GB18) | (\max|F|<L) |
|---:|:---:|---:|---:|:---:|---:|---:|:---:|:---:|
| 4 | pre | 11 | 4 | 2 / 3 | -3 | 1 | passes | passes |
| 4 | drop | 11 | 4 | 2 / 3 | -3 | 1 | passes | passes |
| 6 | pre | 93 | 20 | 2 / 7 | -53 | 47 | fails | passes |
| 6 | drop | 93 | 20 | 2 / 7 | -53 | 47 | fails | passes |
| 8 | pre | 837 | 124 | 2 / 14 | -589 | 899 | fails | **fails** |
| 8 | drop | 837 | 124 | 2 / 14 | -589 | 899 | fails | **fails** |
| 10 | pre | 7533 | 843 | 2 / 21 | -5847 | 10170 | fails | **fails** |
| 10 | drop | 7534 | 843 | 2 / 21 | -5848 | 10169 | fails | **fails** |
| 12 | pre | 67799 | 6094 | 1 / 28 | -61705 | 102833 | fails | **fails** |
| 12 | drop | 67799 | 6094 | 1 / 28 | -61705 | 102833 | fails | **fails** |

At (e=12), the forbidden value is (-67799) and the observed safety
margin is exactly

\[
                          -61705-(-67799)=6094=K.           \tag{GB19}
\]

This does not rule out a genuinely one-sided high-moment, exponential-moment,
or minorant argument. It identifies what a near-boundary approximation must
do: control the negative tail without paying for the larger positive tail,
at additive precision (o(L/\log L)), with an explicit error below the cell
margin, or through an exact nonvanishing argument. A much stronger uniform
bound (\max_a|F_a|=o(L)) would also suffice, but it is not what the
sharp-scale occupied histograms above exhibit. Fixed-order Gowers norms,
Parseval, and bare absolute moments do not provide the needed one-sided
information.

## 5. Same-denominator primary-preserving collapsed rows

The diagonal obstruction is not confined to the artificial conjugate in
Section 3. On an exact endpoint write

\[
 B_M={P\over D},\qquad D=3^eC,qquad(3,C)=1.               \tag{GB20}
\]

Choose the first nonnegative (t) for which

\[
                 P'=P\bmod3^e+t3^e,qquad (P',D)=1.        \tag{GB21}
\]

Then (P'/D) has the same reduced denominator as (B_M), and

\[
 P'C^{-1}\equiv PC^{-1}\pmod {3^e}.                       \tag{GB22}
\]

Consequently every three-primary phase in the row is exactly unchanged,
including its complete primary grid. The complementary numerator is changed.
Crucially, (GB21) preserves (P\bmod3^e), **not** (P\bmod D): it does
not preserve the full BBP numerator, and in general it changes all
unconstrained complementary CRT coordinates. This is precisely why the
construction is an information-scope falsifier rather than an alternative
formula for the BBP partial sum.
For the six exact rows, (P') is so small that the entire full phase lies in
one microscopic positive arc:

| (e) | row | (M) | (K) | primary period | (t) | (P') | complete row arc |
|---:|:---:|---:|---:|---:|---:|---:|:---:|
| 4 | pre | 49 | 4 | 9 | 7 | 617 | (<10^{-126}) |
| 4 | drop | 50 | 4 | 3 | 9 | 263 | (<10^{-129}) |
| 6 | pre | 454 | 20 | 81 | 4 | 3307 | (<10^{-1183}) |
| 6 | drop | 455 | 20 | 27 | 14 | 3547 | (<10^{-1185}) |
| 8 | pre | 4099 | 124 | 729 | 12 | 79039 | (<10^{-10676}) |
| 8 | drop | 4100 | 124 | 243 | 11 | 26171 | (<10^{-10682}) |

Every cell label is therefore zero, so (C_h=L) for every quantized
harmonic and all other cells are empty. Since (P') is coprime to the full
denominator and (h<K<M<p) at every high denominator prime (p>M), the
additive CRT multiplier (hP'(D/p)^{-1}\bmod p) is primitive at every such
prime. Many primitive local characters can still cancel globally through
CRT.

These are `experiment`s. They are not alternative BBP truncations and not
counterexamples to V1. Their exact scope is an information-scope no-go: any
successful theorem must use the actual complementary numerator, and the
frozen odd- and dyadic-preserving countermodels show that its actual odd and
dyadic coordinates must be used jointly. Modulus factorization, local
primitivity, and the relation (W^h) alone cannot select it.

## 6. Reproducible checker and frozen record

The standalone
[checker](bbp_growing_band_joint_harmonic_20260813_check.py), SHA-256
`edd7cdb4971b3969aaa05f3764036f7ad78cfecfe1a5362c9d5e1a00b981b30b`,
imports no branch checker. It reconstructs the exact (e=4,6,8) BBP rows,
uses directed MPFR 4.2.2 plus the positive BBP-tail bound at (e=10,12),
certifies that no shadow interval crosses any of the (K) cell boundaries,
and then computes every retained occupancy, trough, peak, and Parseval energy
in integer arithmetic. It also constructs and checks all six
same-denominator alternatives in (GB21)--(GB22).

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813_check.py
```

The retained record ends with:

```text
actual_row_count=10
countermodel_count=6
energy_certificate_failure_count=8
absolute_supnorm_failure_count=6
isospectral_empty_histogram=6^6,5^11,1^2,0
isospectral_empty_nonzero_dft_energy=1211
exact_record_sha256=cc2cdf5824f772cc8062205f661ea605e244f369100132f1820f70fd481648c6
asserts_growing_band_bound=false
asserts_endpoint_gap_law=false
asserts_fixed_return=false
asserts_v1=false
status=PASS
```

## 7. Sharp handoff

The proposed growing-band route is not dead, but its viable form is now much
narrower. A successful theorem must work with the unquantized full numerator
or an endpoint-safe one-sided minorant and prove a **signed** bound across
the coupled diagonal family

\[
                   \sum_{h\le K}\lambda_h
                   \sum_n e_{3^e}(haR_n)W_n^h,             \tag{GB23}
\]

uniformly in the target translation. It must either keep the lower side
uniformly away from (-L), prove exact nonvanishing at (-L), or resolve the
observed near-boundary regime with additive error below
(K\asymp L/\log L). It must use actual odd and dyadic complementary phases
jointly. Separate Ramanujan averages, local high-prime cancellation, a dual
large sieve without full-point spacing, fixed-order Gowers bounds, Parseval,
or symmetric absolute moments cannot supply (GB23).

No such one-sided selected-numerator theorem is obtained here. The endpoint
gap law and canonical V1 remain `conjecture`s.
