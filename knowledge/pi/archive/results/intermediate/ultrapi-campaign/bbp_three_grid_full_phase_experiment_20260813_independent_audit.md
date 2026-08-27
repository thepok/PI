# Independent audit: full BBP phase on the three-primary endpoint rows

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local source, so no external source URL is
invented.

## Conclusion and claim boundary

The frozen finite calculation is reproducible.  Its twelve complete rows,
six exact BBP fractions, six directed pi shadows, endpoint units, full
three-grid visit counts, target distances, circular gaps, ternary
correlations, first two Fourier magnitudes, per-row residue digests, and
aggregate record all pass an independent reconstruction.  Every such result
retains label `experiment`.

The endpoint gap law and endpoint Fourier decay remain `conjecture`s.  No
fixed-sixteen return and no instance of canonical V1 is proved.  In
particular, this audit is not `machine-checked`, `literature-checked`, a
`candidate resolution`, or a `verified resolution`.

There is one nonfatal logical wording defect in Section 7 of the primary
report.  Equation (7) alone gives only a circular return to the single target
zero.  T72 does not turn that single return into V1.  The proposed largest-gap
law is nevertheless sufficient for V1 because it gives **uniform coverage of
every circle target**; after shifting all repunit colors by the fixed
\(16\pi\) phase and treating color zero from the positive side, it supplies
T72's full colored-return hypothesis.  Section 8 below gives the exact
corrected implication.  Thus the conjecture is a valid sufficient target,
but the primary sentence attributing the zero-return step directly to T72 is
overcompressed and should not be quoted as its proof.

## 1. Frozen objects

| object | SHA-256 |
|---|---|
| canonical local source | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| three-primary epoch report | `5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7` |
| odd-cofactor experiment | `c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3` |
| audited full-phase report | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| audited primary checker | `502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458` |
| independent checker | `a80e8ba9a4fa6fb49689ab773667f110296e866fdbb522a6e2695ade6fad3c6d` |
| T69 fixed-sixteen bridge | `fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9` |
| T72 colored-return bridge | `c5b59557d1d95a26c0c451d9cd8d62d073d3d7f918467e5b2b888233d2c83373` |

The report and primary-checker hashes match the requested frozen values.
The independent checker imports neither of their Python definitions.

## 2. Endpoint arithmetic

For even \(e\ge4\), direct integer evaluation of

\[
 A_e=(3^e-1)/8,\qquad M_e^-=5A_e-1,\qquad M_e^+=5A_e
\]

reproduces every retained row:

| \(e\) | row | \(M\) | \(U=\lfloor\log_{10}(16^M)\rfloor\) | \(L\) | \(E\) | \(T=3^{E-2}\) | \(\beta\) |
|---:|:---:|---:|---:|---:|---:|---:|---:|
| 4 | - | 49 | 59 | 11 | 4 | 9 | 38 |
| 4 | + | 50 | 60 | 11 | 3 | 3 | 23 |
| 6 | - | 454 | 546 | 93 | 6 | 81 | 524 |
| 6 | + | 455 | 547 | 93 | 5 | 27 | 185 |
| 8 | - | 4099 | 4935 | 837 | 8 | 729 | 4898 |
| 8 | + | 4100 | 4936 | 837 | 7 | 243 | 914 |
| 10 | - | 36904 | 44436 | 7533 | 10 | 6561 | 57386 |
| 10 | + | 36905 | 44438 | 7534 | 9 | 2187 | 18410 |
| 12 | - | 332149 | 399947 | 67799 | 12 | 59049 | 175484 |
| 12 | + | 332150 | 399948 | 67799 | 11 | 19683 | 175874 |
| 14 | - | 2989354 | 3599540 | 610187 | 14 | 531441 | 3364130 |
| 14 | + | 2989355 | 3599542 | 610188 | 13 | 177147 | 353021 |

The logarithmic upper bounds were checked by the exact inequalities
\(10^U\le16^M<10^{U+1}\), rather than trusted from a floating logarithm.

For \(e=4,6,8\), the independent replay forms each reduced `Fraction`
directly from

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}
\]

and hashes `numerator/denominator`.  The six fraction digests, in the table's
order, are

```text
5d587fa24114f1bb0babc1652053b227043167e948b4a685281df899ce28772b
21ce353eea81858edc07c3cf7a280c5a39c1cc9edf60791f5c2c9cbe569a9aa7
b99709e38f3846bdc08de616cb2efc049f70fe4b9f9ab998ea4c82016ddf54fc
4f833d093ed2b202042833908708c29734996f8978186982937fee3cccf65566
b9673780cbf68442704c8e3038b1edf2d42fa2dbfc369ab1c0e6f76e7be036ca
04ebea7334a2307d3a1599db01fe1b36a13e17498313b7a4ce835eb50b9b7081
```

Their reduced 3-denominator exponents are exactly \(E\) in the table.  A
second prefix pass computes \(3^{14}B_M\bmod3^{14}\) from the unreduced
coefficient polynomial, removing numerator and denominator 3-valuations
separately.  Dividing at each endpoint recovers the displayed \(\beta\)'s.
For the six small rows these agree with a third computation from the reduced
fractions.  Every endpoint has \(\beta\equiv2\pmod3\).

## 3. Exact phase streams and three-grid accounting

For a small row \(B_M=P_M/D_M\), the independently generated exact residue is

\[
 R_n=((10^n-16)P_M)\bmod D_M,
\]

with recurrence

\[
 R_{n+1}\equiv10R_n+144P_M\pmod {D_M}.
\]

The last recurrence value agrees with direct modular exponentiation on all
six rows.  Each of the twelve streams has the stated length and no repeated
center.  The exact two-adic test

\[
 U_M<4M-v_2(M+1)
\]

also passes at every row, so the frozen distinctness argument is applicable
to the true rational phases, not merely to their decimal centers.

Put \(q_n=(10^n-16)/3\).  Modulo \(3^{E-1}\),

\[
 q_{n+1}\equiv10q_n+48,
 \qquad \beta q_n\equiv2+3j_n.
\]

The independent replay constructs \(q_M\) by exponentiation modulo \(3^E\),
then advances it by this affine recurrence.  In all twelve rows every one of
the \(T=3^{E-2}\) indices occurs, and visit counts differ by at most one.
The exact ternary count triples are

```text
(5,5,1) (2,3,6)
(24,35,34) (37,33,23)
(262,293,282) (272,272,293)
(2545,2461,2527) (2477,2566,2491)
(22830,22469,22500) (22672,22496,22631)
(203860,203175,203152) (203122,203525,203541)
```

and reproduce the exact rational values of \(\rho_3^2\).

## 4. Directed pi shadow and tail transfer

The independent run requests ten decimal guard places beyond the 50 used for
phase centers, and uses substantially more binary precision than the primary
run.  MPFR 4.2.2 is evaluated once with rounding down and once with rounding
up.  The resulting floors of \(\pi10^N\) agree, certifying the complete
decimal prefix.  The analogous lower and upper integer calculations certify
the 50-digit prefix of \(\{16\pi\}\).

If

\[
 t_n=10^{-50}\lfloor10^{50}\{10^n\pi\}\rfloor,
 \qquad c=10^{-50}\lfloor10^{50}\{16\pi\}\rfloor,
\]

then the two discarded tails lie in \([0,10^{-50})\).  Their difference
therefore has absolute value strictly below \(10^{-50}\), not
\(2\cdot10^{-50}\).  This validates the first term of the primary error
ledger.

The coefficient identity was independently checked in both combined and
four-pole form.  For every \(k\ge1\),

\[
\begin{aligned}
 &(2k+1)(4k+3)(8k+1)(8k+5)
   -k^2(120k^2+151k+47)\\
 &\hspace{2cm}=392k^4+873k^3+665k^2+194k+15>0.
\end{aligned}
\]

Thus \(0<a(k)<1/k^2\).  Since \(n\le U_M\) gives \(10^n\le16^M\),

\[
 0<(10^n-16)(\pi-B_M)
 <\sum_{j\ge1}\frac1{(M+j)^2 16^j}
 \le\frac1{15(M+1)^2}.
\]

Combining the decimal and BBP-tail errors proves the stated circle bound

\[
 \eta_M=10^{-50}+\frac1{15(M+1)^2}.
\]

The independently obtained bounds are below \(4.90\cdot10^{-11}\),
\(6.05\cdot10^{-13}\), and \(7.47\cdot10^{-15}\) at the three large
epochs, as reported.

## 5. Gap, target, correlation, and Fourier interval checks

Moving every labeled circle point by at most \(\eta\) changes its distance to
a fixed target by at most \(\eta\).  The largest gap is twice the covering
radius, while covering radius is 1-Lipschitz under Hausdorff distance;
therefore the largest gap changes by at most \(2\eta\).  This establishes the
two first transfers in the primary equation (18) without assuming that the
perturbed points preserve their sorted order.

For every integer \(h\), the circle character is \(2\pi|h|\)-Lipschitz, so

\[
 \bigl|\,|\widehat\mu(h)|-|\widehat{\widetilde\mu}(h)|\,\bigr|
 \le2\pi|h|\eta.
\]

The primary 256-bit internal allowance is \(2^{-220}\) in the largest row.
This is conservative: at most \(2^{20}\) bounded summands are accumulated;
even charging every addition at the maximal partial-sum exponent and then
dividing by the count leaves an error far below \(2^{-220}\), while input,
angle, correctly rounded `sin_cos`, division, and norm errors are smaller
again.  An independent 448-bit evaluation of all 24 magnitudes lies strictly
inside every frozen primary interval.

For the ternary bins, the replay computes the exact distance of every decimal
center to \(0,1/3,2/3,1\).  In all six shadow rows that distance is strictly
larger than \(\eta_M\), so none of the true \(B_M\) phases can cross a bin
boundary.  The ternary counts and correlations are therefore exact for the
rational row.

The resulting outward intervals independently verify

\[
 0.899<\frac{L_MG_M}{\log L_M}<1.084
\]

on all twelve finite rows, and
\(0.526<\sqrt L\rho_3<1.331\) for \(e=6,8,10,12,14\).  They also verify the
reported nonmonotonic target behavior: improvement at \(e=8\), worsening at
\(e=10\), then improvement at \(e=12\) and \(e=14\).  These remain finite
`experiment`, not asymptotic evidence upgraded into a proof.

## 6. Adjacent-row compensation

For \(M=M_e^-\), subtraction of successive partial sums gives exactly

\[
 (10^n-16)(B_{M+1}-B_M)
 =(10^n-16)\frac{a(M+1)}{16^{M+1}}.
\]

On every common row exponent, the coefficient bound above yields the primary
\(1/(15(M+1)^2)\) upper bound (indeed a slightly sharper bound is immediate).
Hence the nearly identical full gaps at the pre-drop/drop pair cannot be
treated as independent trials merely because the isolated 3-primary period
falls by three.  The complementary coordinates must synchronize the full
phase.  This no-go interpretation is valid as a `proof sketch`; it supplies
no discrepancy estimate.

## 7. Record and resource replay

The primary checker was compiled and run from the repository root.  It
reported gmpy2 2.3.1, MPFR 4.2.2, all twelve rows, and

```text
exact_record_sha256=2ef85d90315e487fb006ce6b39ca17731d8b20d6f0e129de0faf9422f9501f3d
status=PASS
```

The observed primary resource use was 74.53 seconds wall time, 72.97 seconds
user CPU, and 138,428 KiB maximum resident memory.  The final frozen
independent checker, which uses 448-bit Fourier recomputation and extra pi
guard precision, used 123.34 seconds wall time, 120.35 seconds user CPU, and
139,352 KiB maximum resident memory.  Its output was

```text
claim_status=experiment
source_pins=5
exact_fraction_rows=6
directed_shadow_rows=6
complete_grid_rows=12
fourier_recomputations=24
exact_record_sha256=2ef85d90315e487fb006ce6b39ca17731d8b20d6f0e129de0faf9422f9501f3d
gap_conjecture_asserted=false
fourier_decay_asserted=false
fixed_sixteen_return_asserted=false
canonical_v1_asserted=false
status=PASS
```

The per-row stream SHA-256 values also agree exactly.  The record digest is a
reproducibility checksum, not mathematical evidence for either asymptotic
`conjecture`.

Reproduce the independent run with:

```bash
python -m py_compile \
  work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_independent_check.py
python \
  work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_independent_check.py
```

## 8. Correct implication of the endpoint gap conjecture

This section repairs the attribution noted in the conclusion.  Assume the
endpoint gap law for one sign; two signs are more than necessary.  Let
\(c=\{16\pi\}\), let \(t=k/(10^P-1)\) be a T72 repunit color, and prescribe
\(N\) and \(\varepsilon>0\).  Because \(M_e\to\infty\), \(G_e\to0\), and

\[
 \delta_e:=\sup_{M_e\le n\le U_{M_e}}
 (10^n-16)(\pi-B_{M_e})\le\frac1{15(M_e+1)^2}\to0,
\]

one can choose an even \(e\) with \(M_e\ge N\) and with
\(G_e/2+\delta_e\) smaller than any prescribed positive margin.

If \(0<t<1\), select from the full endpoint row a phase within \(G_e/2\)
of the circle target \(t-c\), and require

\[
 G_e/2+\delta_e<\min(\varepsilon,t,1-t).
\]

After adding \(c\), the corresponding true point
\(\{10^n\pi\}\) is circle-close to \(t\); the margin prevents wraparound, so
its ordinary real distance to \(t\) is below \(\varepsilon\).

For the endpoint color \(t=0\), put

\[
 r=\min(\varepsilon/4,1/4)>0
\]

and select a phase close to \(r-c\), with total error below \(r\).  The real
fractional part then lies strictly between \(0\) and \(2r<\varepsilon\).
This supplies the endpoint-safe ordinary distance that T72 requires.

Thus the endpoint gap `conjecture` would imply every quantifier in
`ColoredRepunitReturns Real.pi`: every period, color, lateness threshold, and
positive tolerance.  T72's `canonicalV1_iff_coloredRepunitReturns` would then
give canonical V1.  This route uses the largest gap's all-target coverage,
not equation (7) alone.

For comparison, equation (7) alone would give T69's single
`FixedSixteenReturn` in circle distance.  T69 needs its separate joint-orbit
density premise to continue to V1; that is a different bridge from T72.

The Fourier-decay `conjecture` is also logically adequate if it holds for
every fixed nonzero integer frequency: Weyl's criterion gives weak
convergence of each endpoint empirical measure to Haar measure.  If largest
gaps failed to tend to zero, compactness of their centers would leave a fixed
positive-length arc empty along a subsequence, contradicting weak convergence
to a measure positive on every open arc.  Only \(h=1,2\) were measured, so no
premise of that argument is proved here.

## 9. Coordination record

This audit registered descendant-area watch
`ultrapi-three-grid-full-phase-audit-20260813` on `local:pi-digits` for agent
`codex-three-grid-full-phase-audit`.  Its initial poll was empty at cursor and
delivered sequence 57,331, so there was no event to acknowledge.  Observation
events are coordination signals only and never promote an `experiment`,
`conjecture`, or `proof sketch`.

The useful next analytic target remains control of the synchronized
complementary phase strong enough to prove all-target gap decay or every-mode
Fourier decay.  The present branch measures that target precisely but does
not prove it.
