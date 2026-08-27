# Independent audit: Peres--Yang at the BBP endpoints

Audit date: **2026-08-13 UTC**

Audit verdict: **PASS_WITH_SCOPE_CLARIFICATIONS**.  I found no fatal defect in
the almost-everywhere upper endpoint-window corollary, the equal-cell DFT
identity, or the bounded $M=454$ replay.  The corollary is an a.e. **upper
limsup** statement only.  It says nothing about the named point pi, and the
finite countermodels are not BBP truncations.  Canonical V1 remains a
`conjecture`.

The analytic endpoint corollary retains label `proof sketch`, the bounded
replay retains label `experiment`, and this dated primary-source applicability
check has label `literature-checked`.  Nothing audited here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Frozen audit surface

| artifact | SHA-256 |
|---|---|
| [canonical target](../../problems/local/pi-digits.txt) | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| [primary report](peres_yang_bbp_endpoint_attack_20260813.md) | `3721a8e1a43fd3c4244ab8ffa11e0da0581e169d037cdf04f85e18ec1a539b60` |
| [primary checker](peres_yang_bbp_endpoint_attack_20260813_check.py) | `121fad4ba825591d701b4156c6a570962e0609173b875d9b9fe5246afb0a8bcb` |
| [fresh literature audit](fresh_special_value_fractal_literature_20260813.md) | `0852d12d67609fffae963f49369643b2378e319852f0e13eabf716581725abfe` |
| [endpoint recursion](bbp_endpoint_gap_recursion_20260813.md) | `6a4a8b77164acf76316e8effa197843d0b76629c9a596fa4b342742746d41c1d` |
| [full-phase experiment](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [three-primary decimation](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [complement Fourier attack](bbp_complement_fourier_attack_20260813.md) | `eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a` |
| Peres--Yang arXiv:2606.28860v1 PDF | `bbfbd8b3cbcb0e4523873142eea72326f8d729c4cb2eeb58104741828688ac24` |
| local PDF text extraction | `9591c2cc7b37e2c643301df0aad7e9f3a96218605ecd70cd0fa88483603c30d7` |
| [independent checker](peres_yang_bbp_endpoint_attack_20260813_independent_check.py) | `6a44ffd9c30b22302e90df4c14a3049feba66b9d3f1621ac88fa80cc2afb0d48` |

The Peres--Yang PDF is the pinned local copy of
[*Maximal Gaps for Dilated Lacunary Integer Sequences*](https://arxiv.org/abs/2606.28860v1).
I checked Theorem 1.2, Lemma 5.1, Propositions 4.3, 5.2 and 5.7, and the proofs
on paper pages 15--21 directly against that copy.

## 2. Independent derivation of the endpoint-window corollary

### 2.1 Exact row geometry and shifts

For even $e$, let

\[
 A_e=\frac{3^e-1}{8},\qquad M_e^-=5A_e-1,\qquad M_e^+=5A_e,
\]

and put

\[
 U(M)=\lfloor M\log_{10}16\rfloor,\qquad
 L_e^\sigma=U(M_e^\sigma)-M_e^\sigma+1.
\]

Since $A_{e+2}=9A_e+1$,

\[
 M_{e+2}^-=9M_e^-+13,\qquad
 M_{e+2}^+=9M_e^++5.
\]

Writing $\alpha=\log_{10}16$, it follows that

\[
 L_e^\sigma=(\alpha-1)M_e^\sigma+O(1),\qquad
 \frac{L_{e+2}^\sigma}{L_e^\sigma}\longrightarrow9.       \tag{A1}
\]

Thus each sign separately gives a genuinely geometric sequence of sample
lengths.  For a fixed $x$, set

\[
 z_e^\sigma=\{10^{M_e^\sigma}x\}.
\]

Then the late row is exactly

\[
 \{10^n x:M_e^\sigma\le n\le U(M_e^\sigma)\}
 =\{10^jz_e^\sigma:0\le j<L_e^\sigma\}.             \tag{A2}
\]

This uses the Peres--Yang divisibility chain
$a_{j+1}=10^j$.  The index-zero term is handled simply by this one-place
reindexing.  The map $x\mapsto10^{M_e^\sigma}x\pmod1$ preserves Haar
measure, although it is not invertible.  Consequently, for every measurable
bad set $E_L$ of starting phases,

\[
 \lambda\{x:z_e^\sigma\in E_{L_e^\sigma}\}
 =\lambda(E_{L_e^\sigma}).                            \tag{A3}
\]

No common starting phase across rows is being asserted or needed.

### 2.2 The finite bad-set estimate is summable on these rows

Fix $\tau>1$, $\rho>0$, and choose
$0<\beta<\tau-1$.  Apply Section 5.1 of Peres--Yang with

\[
 s=\tau\frac{\log N}{N},\qquad R_N=(\log N)^4.
\]

The mesh contains $O_{\rho,\tau}(N/\log N)$ intervals.  For its regular
members, Proposition 5.2 and a union bound give

\[
 O_{\rho,\tau}\!\left(\frac N{\log N}\right)
 \left(
 N^{-\tau/(\beta+1+4/R_N)+o(1)}+O(N^{-4})
 \right).                                             \tag{A4}
\]

Because $\tau>\beta+1$, the first term in (A4) is $N^{-\delta+o(1)}$
for some fixed $\delta>0$.  Lemma 5.1 leaves only $O_\rho(R_N^2)$
nonregular mesh intervals.  Proposition 4.3, with
$\Gamma\le1$ and the paper's choice $\varepsilon=1$, bounds their total
contribution by

\[
 O_\rho(R_N^2)
 \left(N^{-\tau/(\beta+5)+o(1)}+O(N^{-4})\right).      \tag{A5}
\]

This is a polylogarithm times a fixed negative power of $N$.  The required
condition $s=o(R_N^{-1})$ also holds because
$(\log N)^5/N\to0$.  Equations (A4)--(A5) are therefore summable whenever
$N$ runs through either sequence $L_e^-$ or $L_e^+$, by (A1).

The geometric-sequence interpolation used by Peres--Yang to recover every
integer $N$ is not needed here: the desired events themselves occur only at
the endpoint lengths.  Combining the finite estimate with (A3) and applying
the first Borel--Cantelli lemma gives, for each fixed sign,

\[
 G_e^\sigma(x)\le
 (1+\rho)\tau\frac{\log L_e^\sigma}{L_e^\sigma}
 \quad\text{eventually for a.e. fixed }x.             \tag{A6}
\]

There are only two signs.  Intersect their full-measure sets and then
intersect over countable sequences $\rho\downarrow0$ and
$\tau\downarrow1$.  This proves precisely

\[
 \boxed{
 \limsup_{e\to\infty\atop e\ {\text{ even}}}
 \frac{L_e^\sigma G_e^\sigma(x)}{\log L_e^\sigma}\le1
 \quad(\sigma\in\{-,+\})
 }
 \quad\text{for a.e. fixed }x.                       \tag{A7}
\]

No independence between endpoint rows is used: summability and the first
Borel--Cantelli lemma suffice.

### 2.3 Mixed-radix independence is not in the upper proof

The source separation is unambiguous.

- The sharp upper/no-hit proof is Section 5.1.  Proposition 5.2 uses
  one-point and two-point integration over the survivor set,
  Paley--Zygmund, interval regularity, a mesh union bound, and then
  Borel--Cantelli.
- The mixed-radix expansion (5.7)--(5.8) starts only in Section 5.2.
  Its independent digit windows are used in Proposition 5.7 and then in
  Section 5.3 for the sharp **lower** gap bound.

Thus the primary report is correct that independent mixed-radix digits are
not an omitted hypothesis in (A7).  Lebesgue averaging over the starting
point is the decisive upper-bound input.

### 2.4 Scope clarification

The phrase “endpoint-window law” in the primary report must be read as the
upper-limsup formula displayed there.  This audit does not derive a matching
endpoint lower bound.  More importantly, the exceptional null set in (A7)
is not proved to omit pi.  Nor can (A7) be applied to the changing rowwise
rationals $B_{M_e^\sigma}$: those are a triangular array of selected points,
not one Lebesgue-typical fixed $x$.

## 3. Independent audit of the equal-cell DFT certificate

For $K\ge2$, let $q_n=\lfloor Kx_n\rfloor$, let
$c_a=\#\{n:q_n=a\}$, and let

\[
 C_h=\sum_n\zeta_K^{hq_n},\qquad \zeta_K=e^{2\pi i/K}.
\]

Character orthogonality gives, without approximation,

\[
 \sum_{h=0}^{K-1}C_h\zeta_K^{-ha}
 =\sum_n\sum_{h=0}^{K-1}\zeta_K^{h(q_n-a)}
 =Kc_a.                                               \tag{A8}
\]

Since $C_0=L$, (A8) is the primary report's identity

\[
 Kc_a=L+\sum_{h=1}^{K-1}C_h\zeta_K^{-ha}.            \tag{A9}
\]

The right side is real and integral.  Hence cell $a$ is empty exactly when
the nonzero-frequency signed sum equals (-L); all cells are occupied exactly
when its minimum is strictly greater than (-L).  If every half-open
$K$-cell is occupied, consecutive selected points can cross at most two
cell widths, so the circular gap is at most (2/K).

For a constant-one gap upper bound one would choose, for example,
$K\sim2L/((1+\varepsilon)\log L)$, not merely fix the implicit constant in
$K\asymp L/\log L$ to one.  Thus the primary phrase “$K\asymp
L/\log L$” is correct but suppresses this harmless factor-of-two choice.

Parseval independently yields

\[
 \sum_{h=1}^{K-1}|C_h|^2
 =K\sum_{a=0}^{K-1}c_a^2-L^2.                       \tag{A10}
\]

If one cell is empty, (A9) and Cauchy--Schwarz force

\[
 \sum_{h=1}^{K-1}|C_h|^2\ge\frac{L^2}{K-1}.          \tag{A11}
\]

This is a sufficient low-energy certificate in the reverse strict
direction, but scalar energy above that threshold does not determine
coverage.  The independent replay strengthens the primary example.  At
$L=93,K=20$:

- the actual covered histogram has energy (1211);
- the threshold is (8649/19);
- a balanced empty histogram has energy (491); and
- the one-empty histogram
  ((6^6,5^{11},1^2,0)) has **the same energy (1211)** as the actual
  covered histogram.

Here exponent notation denotes repeated entries.  Thus even identical
scalar nonzero DFT energy can occur with and without an empty cell.  The
phase-sensitive trough in (A9), rather than global energy alone, is the
correct deterministic target.

## 4. Disjoint $M=454$ replay

The independent checker imports no primary or branch checker.  It builds the
BBP prefix from the four classical fractions, rather than reusing the
primary checker's combined summand, and obtains the following exact data.

- $e=6$, pre-drop depth $M=454$, upper exponent 546, row length
  $L=93$, and three-primary period 81.
- The reduced denominator has 1,733 decimal digits, dyadic exponent
  $1816=4M-v_2(M+1)$, and exact three-adic exponent 6.
- The 93 residues are distinct and their exact circular gap lies strictly
  between (43/1000) and (44/1000).
- The exact 20-cell histogram is
  ((6,4,7,3,5,3,4,7,3,7,2,5,5,7,3,2,3,4,6,7)), so every cell is hit.
  The minimum signed nonzero DFT trough is (-53>-93), in agreement with
  (A9).  High-precision roots of unity only replay this exact integer
  histogram; the proof of (A9) is the algebra above.

The three numerator falsifiers were also reconstructed directly.

1. Numerator (1), with the same reduced denominator, places the row in an
   arc shorter than (10^{-1186}) and retains all 81 three-primary values.
2. The unique odd representative of the actual numerator modulo the complete
   odd denominator preserves every odd CRT coordinate.  Its row lies in an
   arc shorter than (83/1000), has circular gap greater than (917/1000),
   and retains all 81 three-primary values.
3. Preserving the complete dyadic numerator residue, the first lift coprime
   to the odd denominator is lift (3).  Its row lies in an arc shorter than
   (10^{-639}).

Each replacement is coprime to the same denominator, and the claimed CRT
coordinate is checked by congruence before its row is evaluated.  These are
finite `experiment`s showing that either marginal coordinate can coexist
with a nearly collapsed orbit.  They are not alternative values of the BBP
partial sum, not approximants to pi, and not counterexamples to V1.

## 5. Rational-grid and fixed-π boundary

From the reduced form

\[
 B_M=\frac{P_M}{2^{K_M}5^{v_M}R'_M},\qquad (10,R'_M)=1,
\]

multiplication by $10^M$, once $M>v_M$, leaves starting denominator

\[
 Q_M=2^{K_M-M}R'_M.                                  \tag{A12}
\]

After $j$ more decimal iterates the dyadic image grid alone has at least
(2^{K_M-M-j}) points.  At the last row exponent this is

\[
 2^{K_M-U(M)}
 =2^{(4-\log_{10}16)M-O(\log M)}.                   \tag{A13}
\]

This supports the primary report's grid-size comparison.  It does not select
the one residue $P_M$.  An exceptional-proportion estimate, even when
discretized on this exponentially fine grid, is not an emptiness theorem for
the exceptional set.  The bounded CRT examples demonstrate that neither the
odd nor dyadic marginal selects the actual joint numerator.

The notation $L_M$ in the primary report's (PYB11) should be read as
$U(M)-M+1$; this is only a notation clarification.  No deterministic
estimate for the selected $P_M$, no fixed return
$\|(10^n-16)\pi\|_{\mathbb T}\to0$ along a subsequence, and no V1 result is
present.

## 6. Artifact hygiene and replay

The independent checker verified all seven relative links in the primary
report, found no forbidden control bytes there, checked every frozen input
hash, and checked identifying statements in the pinned Peres--Yang text.
The primary and independent checkers both compile and pass.  The independent
checker itself contains no control bytes.

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_independent_check.py
```

The retained independent record ends with:

```text
actual_nonzero_dft_energy=1211
empty_energy_threshold=8649/19
balanced_empty_nonzero_dft_energy=491
isospectral_empty_nonzero_dft_energy=1211
isospectral_empty_cell_count=1
unit_numerator_gap_gt=1-10^-1186
odd_crt_preserving_gap_gt=917/1000
dyadic_preserving_first_coprime_lift=3
dyadic_preserving_gap_gt=1-10^-639
asserts_ae_endpoint_law=false
asserts_endpoint_gap_law=false
asserts_fixed_pi_return=false
asserts_v1=false
independent_record_sha256=aad0c3e1eddfcab8077d50822e4cc3819ace9295c5e974edaf4be649d23d6633
status=PASS
```

No Lean file, axiom audit, verification gate, primary artifact, or
`ultrapi.md` was changed by this audit.

## 7. Final audit conclusion

The frozen report correctly extracts a sharp a.e. upper endpoint-window
statement from Peres--Yang's finite estimates, including both endpoint signs
and the triangular late-window shifts.  Its use of Borel--Cantelli is valid
without row independence, and its upper proof does not use independent
mixed-radix digits.  The exact DFT certificate is correct; scalar Parseval
energy loses precisely the signed-cell information needed for coverage.

The surviving gap is unchanged: a new deterministic estimate must control
the actual joint BBP numerator, either through fixed-h full-product decay or
through the growing-band signed DFT trough.  No such estimate was proved, so
the audit supplies no fixed-π or V1 upgrade.
