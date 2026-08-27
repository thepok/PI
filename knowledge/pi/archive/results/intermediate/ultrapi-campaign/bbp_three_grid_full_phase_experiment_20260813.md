# Full BBP phase on the recurring three-primary endpoint rows

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is Marcel's immutable local question and has no external source
URL; none is invented here.

Frozen inputs:

- [bbp_three_primary_epoch_20260813.md](bbp_three_primary_epoch_20260813.md),
  SHA-256
  `5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7`;
- [bbp_odd_cofactor_short_orbit_experiment_20260813.md](bbp_odd_cofactor_short_orbit_experiment_20260813.md),
  SHA-256
  `c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3`.

## Outcome and exact claim boundary

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained. Canonical V1 remains a `conjecture`.

This branch measures the **complete** rational phase

\[
             (10^n-16)B_M\pmod1,
 \qquad M\le n\le U_M:=\lfloor\log_{10}(16^M)\rfloor,       \tag{1}
\]

on the recurring last-pre-drop and first-drop rows of every sampled even
three-adic epoch. It does not replace (1) by its three-primary projection.
The finite findings have label `experiment`.

The principal empirical finding is unusually stable across six scales. If
\(L_M=U_M-M+1\) and \(G_M\) is the largest circular gap between the points
in (1), then on all twelve retained rows, from \(L=11\) through
\(L=610188\),

\[
                  0.899 < {L_MG_M\over\log L_M}<1.084.       \tag{2}
\]

At the largest epoch the certified interval is

\[
 G_M\in[2.052076752066646182,2.052076755050746759]10^{-5},   \tag{3}
\]

so the corresponding target mesh \(G_M/2\) is about
\(1.02604\cdot10^{-5}\). The first two Fourier magnitudes also fall, and an
exact ternary correlation with the three-grid index has random-scale size:
\(\sqrt L\,\rho_3\) remains between \(0.526\) and \(1.331\) from epochs
6 through 14.

These observations motivate precise gap and Fourier `conjecture`s below.
Finite data do not establish either asymptotic statement. In particular, the
distance to the prescribed target zero is not monotone: it improves sharply
at epoch 8, becomes worse at epoch 10, and improves again at epochs 12 and
14. The data therefore falsify any naive monotone-return inference.

There is also a clear no-go. Passing from the last pre-drop row to the first
drop row divides the isolated three-primary period by three, but barely
changes the full circular geometry. The exact adjacent-depth identity in
Section 6 explains this: the complementary CRT coordinates compensate the
three-primary reorganization. The two rows are not independent trials.

Nothing here is `machine-checked`, `literature-checked`, a
`candidate resolution`, or a `verified resolution`.

## 1. Rows, phases, and target mesh

For every even \(e\ge4\), put

\[
 A_e={3^e-1\over8},\qquad M_e^-=5A_e-1,\qquad M_e^+=5A_e.  \tag{4}
\]

The frozen epoch calculation gives reduced three-primary denominator
exponents

\[
                       E_e^-=e,\qquad E_e^+=e-1.             \tag{5}
\]

Let

\[
 X_e^\pm=\left\{\left\{(10^n-16)B_{M_e^\pm}\right\}:
       M_e^\pm\le n\le U_{M_e^\pm}\right\}.                 \tag{6}
\]

The measured quantities are:

- \(d_e^\pm=\min_{x\in X_e^\pm}\|x\|_{\mathbb T}\), the
  distance to the prescribed target zero;
- \(G_e^\pm\), the largest circular gap between consecutive points of
  \(X_e^\pm\);
- \(G_e^\pm/2\), the exact worst-target covering radius, called the target
  mesh here;
- \(\widehat\mu_e^\pm(h)=L^{-1}\sum_{x\in X_e^\pm}e^{2\pi ihx}\)
  for \(h=1,2\);
- the exact coarse correlation \(\rho_3\) from Section 3.

The target mesh matters directly: every target on the circle, zero included,
lies within \(G_e^\pm/2\) of one row point. Therefore

\[
                         d_e^\pm\le {G_e^\pm\over2}.         \tag{7}
\]

## 2. Exact row arithmetic and distinctness

For \(e=4,6,8\), the checker constructs

\[
 B_M=\sum_{k=0}^M{120k^2+151k+47\over
  (2k+1)(4k+3)(8k+1)(8k+5)16^k}={P_M\over D_M}             \tag{8}
\]

as a reduced `Fraction`. Every phase point is then the exact integer residue

\[
                  {((10^n-16)P_M\bmod D_M)\over D_M}.       \tag{9}
\]

The recurrence

\[
 R_{n+1}\equiv10R_n+144P_M\pmod {D_M}                      \tag{10}
\]

is checked against direct modular exponentiation at the last row exponent.

There are no repeated points in any of these rows, and the same all-depth
argument applies to the larger rows. This is a `proof sketch`, not a new
formal declaration. The exact dyadic denominator exponent is

\[
                         K_M=4M-v_2(M+1).                    \tag{11}
\]

If two phases with \(m<n\) were equal, reducedness would force
\(2^{K_M}\mid10^m(10^{n-m}-1)\). The right side has two-adic valuation
exactly \(m\), while every retained proportional row satisfies
\(m\le U_M<K_M\), a contradiction. Distinctness rules out collisions as the
source of a large gap; it supplies no discrepancy bound.

## 3. Exact correlation with the three-grid index

Write

\[
 \beta_M\equiv3^{E_M}B_M\pmod {3^{E_M}},\qquad
 T_M=3^{E_M-2},\qquad g_n={10^n-16\over3}.                   \tag{12}
\]

At all endpoint rows \(\beta_M\equiv2\pmod3\). Define the exact grid index
\(j_{M,n}\in\{0,\ldots,T_M-1\}\) by

\[
 \beta_Mg_n\equiv2+3j_{M,n}\pmod {3^{E_M-1}}.               \tag{13}
\]

Every retained row covers all \(T_M\) indices, and the visit counts differ
by at most one. To measure an exact, origin-fixed correlation, set

\[
 p_n=\left\lfloor3\{(10^n-16)B_M\}\right\rfloor,\qquad
 q_n=\left\lfloor{3j_{M,n}\over T_M}\right\rfloor,          \tag{14}
\]

and let \(c_r=\#\{n:p_n-q_n\equiv r\pmod3\}\). With
\(\omega=e^{2\pi i/3}\), define

\[
 \rho_3=\left|{c_0+c_1\omega+c_2\omega^2\over L_M}\right|,
 \quad
 \rho_3^2={c_0^2+c_1^2+c_2^2-c_0c_1-c_1c_2-c_2c_0\over L_M^2}.             \tag{15}
\]

Thus \(\rho_3^2\) is rational and is checked without floating-point
arithmetic. It is only a three-bin statistic; its decay would not by itself
control all Fourier modes or prove target hitting.

The endpoint units in (12) are independently recomputed in one modular pass.
The checker sums \(3^{14}B_M\) term by term modulo \(3^{14}\), then divides
by the certified power of three at each endpoint. For \(e=4,6,8\), these
values are independently compared with the exact reduced `Fraction`.

## 4. Rigorous large-depth shadow

Constructing the complete reduced rational \(B_M\) at \(M\approx3\) million
would obscure the experiment. For \(e=10,12,14\), the checker instead uses a
rigorous real enclosure.

With 50 guard digits and enough total precision for the largest row, MPFR
4.2.2 is run once with rounding down and once with rounding up. Both runs give
the same integer

\[
                             Q=\lfloor\pi10^N\rfloor.        \tag{16}
\]

Each circle phase \((10^n-16)\pi\) is represented by its next 50 certified
decimal digits. If \(\widetilde x_n\) is that rational center, then the
digit truncation and the frozen positive BBP-tail bound give

\[
 \left\|\widetilde x_n-(10^n-16)B_M\right\|_{\mathbb T}
 <\eta_M:={1\over10^{50}}+{1\over15(M+1)^2}.                 \tag{17}
\]

Consequently the retained intervals use the rigorous transfers

\[
 |d_M-\widetilde d_M|\le\eta_M,qquad
 |G_M-\widetilde G_M|\le2\eta_M,qquad
 \left||\widehat\mu_M(h)|-|\widehat{\widetilde\mu}_M(h)|\right|
 \le2\pi|h|\eta_M.                                         \tag{18}
\]

For \(e=10,12,14\), the respective \(\eta_M\) are below
\(4.90\cdot10^{-11}\), \(6.05\cdot10^{-13}\), and
\(7.47\cdot10^{-15}\). The checker also verifies that no phase enclosure
crosses a ternary boundary in (14), so the reported \(c_r\) and \(\rho_3\)
remain exact for \(B_M\), not merely for the pi centers.

Fourier centers are evaluated with correctly rounded 256-bit MPFR
operations. A deliberately loose operation-count envelope, plus the last
term in (18), is added outward. The record therefore contains intervals, not
ordinary binary floating-point estimates.

## 5. Retained experiment

All entries below are finite `experiment`. Exact or outward interval bounds
with more digits are in the checker output. The symbols \(-\) and \(+\)
mean last pre-drop and first drop, respectively.

| \(e\) | row | \(M\) | \(L\) | \(T\) | \(d_0\) | \(G\) | \(LG/\log L\) | \(|\widehat\mu(1)|\) | \(\rho_3\) | \(\sqrt L\rho_3\) |
|---:|:---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | - | 49 | 11 | 9 | 5.5733e-2 | 2.36173e-1 | 1.08341 | 6.2462e-2 | 3.6364e-1 | 1.2060 |
| 4 | + | 50 | 11 | 3 | 5.5733e-2 | 2.36174e-1 | 1.08341 | 1.5880e-1 | 3.2778e-1 | 1.0871 |
| 6 | - | 454 | 93 | 81 | 7.0067e-3 | 4.38657e-2 | 0.90004 | 4.5738e-2 | 1.1329e-1 | 1.0925 |
| 6 | + | 455 | 93 | 27 | 7.0067e-3 | 4.38657e-2 | 0.90004 | 3.8161e-2 | 1.3430e-1 | 1.2952 |
| 8 | - | 4099 | 837 | 729 | 8.8149e-6 | 8.59352e-3 | 1.06879 | 2.7138e-2 | 3.2522e-2 | 0.9409 |
| 8 | + | 4100 | 837 | 243 | 8.8149e-6 | 8.59352e-3 | 1.06879 | 2.5420e-2 | 2.5090e-2 | 0.7259 |
| 10 | - | 36904 | 7533 | 6561 | 7.17993e-5 | 1.28188e-3 | 1.08170 | 9.7219e-3 | 1.0169e-2 | 0.8826 |
| 10 | + | 36905 | 7534 | 2187 | 7.17993e-5 | 1.28188e-3 | 1.08183 | 9.6780e-3 | 1.1002e-2 | 0.9550 |
| 12 | - | 332149 | 67799 | 59049 | 6.64209e-6 | 1.75895e-4 | 1.07202 | 3.7384e-3 | 5.1113e-3 | 1.3309 |
| 12 | + | 332150 | 67799 | 19683 | 6.64209e-6 | 1.75895e-4 | 1.07202 | 3.7146e-3 | 2.3526e-3 | 0.6126 |
| 14 | - | 2989354 | 610187 | 531441 | 5.62966e-8 | 2.05208e-5 | 0.93995 | 8.8125e-4 | 1.1419e-3 | 0.8920 |
| 14 | + | 2989355 | 610188 | 177147 | 5.62966e-8 | 2.05208e-5 | 0.93995 | 8.7854e-4 | 6.7395e-4 | 0.5264 |

The largest-gap statistic is much more stable than the target-zero minimum.
That is exactly what a covering statement should look like: a proof of small
largest gap would hit every target and would not rely on a lucky zero sample.
The pre/drop comparison is equally important. At epochs 8 through 14 the
largest gaps agree to the displayed precision even though \(T\) changes by a
factor of three. The isolated grid is therefore not acting as an independent
source of full-phase samples.

## 6. Exact compensation no-go

Let \(M=M_e^-\), so \(M+1=M_e^+\). On every exponent common to the two
proportional rows,

\[
\boxed{
 (10^n-16)B_{M+1}-(10^n-16)B_M
 =(10^n-16){a(M+1)\over16^{M+1}}.}                 \tag{19}
\]

The positive BBP-tail estimate gives

\[
 0<(10^n-16)(B_{M+1}-B_M)
 \le {1\over15(M+1)^2}.                            \tag{20}
\]

Equations (19)--(20) have status `proof sketch` here; the same adjacent-depth
identity was already present elsewhere in the workspace, so no novelty is
claimed. They explain the experiment: the three-primary coordinate changes
its denominator exponent and period at the drop, while the complete phase
moves only \(O(M^{-2})\) on every shared exponent. The complementary CRT
phase must compensate the primary change. Treating the two endpoint rows as
independent random trials would therefore be mathematically false.

## 7. Precise working conjectures

The direct quantitative proposal is:

### `conjecture` (endpoint gap law)

There exist constants \(C>0\) and even \(e_0\) such that for both signs and
every even \(e\ge e_0\),

\[
                         G_e^\pm\le C{\log L_e^\pm\over L_e^\pm}.           \tag{21}
\]

This would be a genuine breakthrough: (7) and \(L_e^\pm\to\infty\) would
give a fixed-sixteen near return, and the existing T72 reduction would then
give canonical V1. The six sampled epochs support (21) but do not prove it.

A weaker qualitative route suggested by the same data is:

### `conjecture` (endpoint Fourier decay)

For every fixed nonzero integer \(h\),

\[
                       \widehat\mu_e^\pm(h)\longrightarrow0                \tag{22}
\]

along the even epochs; the observed scale is compatible with
\(O_h(L^{-1/2})\). If (22) held for every fixed \(h\), Weyl's criterion would
give weak convergence to circle measure. A compactness argument would then
force \(G_e^\pm\to0\), which is enough for the return even without the sharp
logarithmic rate in (21). Only \(h=1,2\) were checked here.

The exact statistic (15) suggests the subsidiary `conjecture`
\(\rho_3=O(L^{-1/2})\). It is useful as a falsification test for coarse
locking to the three-grid, but it is strictly weaker than (22).

## 8. Reproduction and frozen record

The standalone
[checker](bbp_three_grid_full_phase_experiment_20260813_check.py), SHA-256
`502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458`,
imports no branch checker. Run from the repository root:

```bash
python -m py_compile \
  work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_check.py
python \
  work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_check.py
```

The retained run used gmpy2 2.3.1 and MPFR 4.2.2. It checked six exact
`Fraction` rows, six directed-shadow rows, all exact endpoint units through
\(e=14\), complete three-grid coverage, ternary-bin stability, target
distances, gaps, meshes, and two Fourier coefficients. Every row also has an
independent residue-stream SHA-256. The aggregate exact record is

```text
exact_record_sha256:
  2ef85d90315e487fb006ce6b39ca17731d8b20d6f0e129de0faf9422f9501f3d
asserts_asymptotic_gap_bound=false
asserts_fourier_decay=false
asserts_fixed_return=false
asserts_v1=false
status=PASS
```

## 9. Coordination record and sharp handoff

This branch registered descendant-area watch
`watch:local:pi-digits:three-grid-joint-experiment-20260813` on
`local:pi-digits` for agent `codex-three-grid-joint-experiment`. Its initial,
pre-report, and final polls were empty at cursor and delivered sequence
57,288, so there was no event to acknowledge. Observation events would be
coordination signals only, never mathematical evidence.

The finite full phase looks much better distributed than its isolated
three-primary description alone suggests: its gap is consistently of
random-point scale, its first Fourier modes decrease, and its coarse
three-grid correlation is of square-root scale. The stable, directly
sufficient next target is (21), not the nonmonotone minimum distance to zero.

At the same time, the pre/drop identity shows why the visible improvement
cannot be multiplied by treating primary epochs as independent. A proof must
control the synchronized complementary phase—or prove (22) directly for the
actual selected rational rows. The present artifact supplies a sharply
falsifiable quantitative target, not a proof of it.
