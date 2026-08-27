# Peres--Yang at the BBP endpoints: metric late-window theorem and the selected-numerator barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL;
none is invented here.

Frozen inputs:

| artifact | SHA-256 |
|---|---|
| [fresh 2026 literature audit](fresh_special_value_fractal_literature_20260813.md) | `0852d12d67609fffae963f49369643b2378e319852f0e13eabf716581725abfe` |
| [endpoint-gap recursion](bbp_endpoint_gap_recursion_20260813.md) | `6a4a8b77164acf76316e8effa197843d0b76629c9a596fa4b342742746d41c1d` |
| [full-phase endpoint experiment](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [three-primary decimation](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [complementary Fourier attack](bbp_complement_fourier_attack_20260813.md) | `eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a` |

The pinned primary source is Peres--Yang,
[*Maximal Gaps for Dilated Lacunary Integer Sequences*](https://arxiv.org/abs/2606.28860v1),
arXiv:2606.28860v1, PDF SHA-256
`bbfbd8b3cbcb0e4523873142eea72326f8d729c4cb2eeb58104741828688ac24`.

## Outcome and exact claim boundary

No deterministic no-hit estimate for the actual BBP endpoint numerators was
proved.  The endpoint maximal-gap law and canonical V1 remain
`conjecture`s.  There is no fixed-sixteen return, no Fourier-decay theorem,
and no upgrade to a `candidate resolution` or `verified resolution`.

There are nevertheless three substantive conclusions.

1. A direct corollary of the finite estimates in Peres--Yang gives the sharp
   endpoint-window law

   \[
       \limsup_{e\to\infty\atop e\ \text{ even}}
       {L_e^\sigma G_e^\sigma(x)\over\log L_e^\sigma}\le1
                                                               \tag{PYB1}
   \]

   simultaneously for both endpoint signs and Lebesgue-almost every **fixed**
   circle point \(x\).  This late-window triangular-array corollary has label
   `proof sketch`.  It matches the exact endpoint geometry more closely than
   merely quoting their first-\(N\) theorem.  It still does not include the
   named point \(x=\pi\).
2. The relevant upper-bound proof does **not** use independent mixed-radix
   digits.  It averages over the starting point with Lebesgue measure,
   applies Paley--Zygmund on survivor sets, takes a union bound over target
   intervals, and finally uses Borel--Cantelli.  Independent mixed-radix
   digits enter their sharp **lower** bound in Proposition 5.7, not the sharp
   upper/no-hit estimate needed here.  The fixed-BBP obstruction is therefore
   a point-selection problem, not a missing claim that the BBP decimal digits
   are probabilistically independent.
3. There is an exact deterministic equal-cell Fourier certificate for the
   endpoint gap.  At the Peres--Yang scale it requires a phase-sensitive
   negative-trough bound across \(K_e\asymp L_e/\log L_e\) modes.  Parseval
   energy cannot replace it.  The actual BBP complementary-phase obstruction
   persists uniformly throughout this growing bandwidth.  This isolates a
   stricter target than fixed-harmonic decay and explains why the existing
   energy and marginal-coordinate estimates do not prove the endpoint law.

The elementary implications below have label `proof sketch`.  The bounded
row replay and its counterexamples have label `experiment`.  The source
applicability record has label `literature-checked`.

## 1. Exact endpoint rows

For even \(e\ge4\), put

\[
 A_e={3^e-1\over8},\qquad M_e^-=5A_e-1,\qquad M_e^+=5A_e,
 \qquad U(M)=\lfloor\log_{10}(16^M)\rfloor,              \tag{PYB2}
\]

and

\[
 L_e^\sigma=U(M_e^\sigma)-M_e^\sigma+1.                 \tag{PYB3}
\]

For a fixed circle point \(x\), define the late decimal window

\[
 Y_e^\sigma(x)=
 \{\{10^n x\}:M_e^\sigma\le n\le U(M_e^\sigma)\},       \tag{PYB4}
\]

and let \(G_e^\sigma(x)\) be its largest circular gap.  Replacing the points
by \(\{(10^n-16)x\}\) is a common translation and leaves the gap unchanged.
The rational BBP row is obtained by replacing \(x\) rowwise by
\(B_{M_e^\sigma}\); that is a different rational on every row.

Writing \(\alpha=\log_{10}16\), one has

\[
 L_e^\sigma=(\alpha-1)M_e^\sigma+O(1),\qquad
 {L_{e+2}^\sigma\over L_e^\sigma}\longrightarrow9.      \tag{PYB5}
\]

Thus the endpoint lengths themselves form a geometric sequence up to a
bounded rounding error.

## 2. Where Peres--Yang use measure, and where Borel--Cantelli enters

The sharp upper bound in their Section 5.1 has the following exact anatomy.

1. For an interval \(J\) of length \(s=\tau\log N/N\), they split the
   indices into main blocks and logarithmic buffers.  The survivor set
   \(\Omega_{u-1}(J)\) is a set of **starting points** \(x\), not a set of
   exponent indices.
2. Lemma 2.1 and Lemma 2.2 integrate over
   \(x\in\Omega_{u-1}(J)\).  In Proposition 5.2, Paley--Zygmund then removes
   a fixed Lebesgue proportion of each active survivor set.  For an
   \(R_N\)-regular interval this gives, uniformly in \(J\),

   \[
    \lambda\{x:10^j x\notin J\ (0\le j<N)\}
    \le N^{-\tau/(\beta+1+4/R_N)+o(1)}+O(N^{-4}),          \tag{PYB6}
   \]

   after shifting their index convention by one.
3. A mesh has \(O(N/\log N)\) regular intervals.  Lemma 5.1 leaves only
   \(O(R_N^2)\) nonregular intervals, and Proposition 4.3 supplies a weaker
   but still negative-power estimate for each of those.
4. If \(\tau>1\), choose \(0<\beta<\tau-1\).  The union bound for regular
   intervals then has a negative power of \(N\); the nonregular contribution
   is a polylogarithm times another negative power.  Along a geometric
   sequence these probabilities are summable.  Borel--Cantelli, on paper
   page 17 for the sharp upper bound, converts this summability into an
   eventual statement for almost every starting point.

The independent mixed-radix digits introduced by (5.7)--(5.8) on paper page
17 are used in Proposition 5.7 and Section 5.3 to prove the matching **lower**
gap bound.  They are not an input to (PYB6) or to the upper bound.  For the
present goal, replacing “independent digits” would attack the wrong step.

### Endpoint-window metric corollary

Fix \(\tau>1\), \(\rho>0\), and one endpoint sign.  In (PYB4), put

\[
                    z_e=\{10^{M_e^\sigma}x\}.               \tag{PYB7}
\]

Then \(Y_e^\sigma(x)=\{10^jz_e:0\le j<L_e^\sigma\}\).  The map
\(x\mapsto10^{M_e^\sigma}x\pmod1\) preserves Lebesgue measure.  Applying the
finite regular/nonregular bounds above with \(N=L_e^\sigma\), and using
(PYB5), makes

\[
 \sum_{e\ \text{ even}}
 \lambda\left\{x:G_e^\sigma(x)>
 (1+\rho)\tau{\log L_e^\sigma\over L_e^\sigma}\right\}<\infty.       \tag{PYB8}
\]

Borel--Cantelli proves the corresponding eventual bound.  Intersecting the
full-measure sets for both signs and for countable sequences
\(\rho\downarrow0\), \(\tau\downarrow1\) gives (PYB1).

No independence between different endpoint rows is used in (PYB8).  The
failure at \(\pi\) is exactly that a full-measure conclusion does not certify
one named point.

## 3. Why averaging over the rational numerator grid does not select BBP

Write one reduced BBP endpoint sum as

\[
 B_M={P_M\over2^{K_M}5^{v_M}R'_M},\qquad
 K_M=4M-v_2(M+1),\qquad (10,R'_M)=1.              \tag{PYB9}
\]

Since \(M>v_M\), the starting phase \(z_M=\{10^MB_M\}\) has reduced
denominator

\[
                         Q_M=2^{K_M-M}R'_M.         \tag{PYB10}
\]

After another \(j\) decimal iterates, the dyadic image grid alone still has
at least

\[
 2^{K_M-M-j}\ge
 2^{K_M-M-(L_M-1)}
 =2^{(4-\log_{10}16)M-O(\log M)}                  \tag{PYB11}
\]

points.  Thus uniform averaging over all numerator residues modulo \(Q_M\)
can discretize the Lebesgue one- and two-point estimates with exponentially
small mesh error.  This recovers an “almost all numerators” analogue of the
metric architecture; it does not identify \(P_M\).

At the target scale \(s\asymp\log L/L\), even the independent avoidance
model has probability \(\exp(-Ls)=L^{-O(1)}\).  In contrast,
\(Q_M\ge2^{3M-O(\log M)}\).  A polynomial exceptional-proportion estimate
is therefore many exponential orders of magnitude too weak to prove that
the exceptional numerator set contains no residue, and a fortiori too weak
to exclude its one selected BBP residue.

The distinction is not merely a limitation of that comparison.  The exact
bounded replay at the pre-drop endpoint \(e=6,M=454\) gives three explicit
falsifiers.

- Keeping the **same 1,733-digit reduced denominator** and replacing the
  numerator by the unit 1 puts the entire row in an arc shorter than
  \(10^{-1186}\), while its isolated three-primary coordinate still traverses
  the full 81-point grid.
- Let \(R_M\) be the complete odd denominator in (PYB9), including all
  three-primary, small-prime, and high-prime factors.  The unique odd
  representative

  \[
       \widetilde P_o\equiv P_M\pmod {R_M},
       \qquad0<\widetilde P_o<2R_M                         \tag{PYB12}
  \]

  preserves **every actual odd additive CRT numerator coordinate**.  It
  changes only the dyadic coordinate.  Its complete row lies in an arc
  shorter than \(83/1000\), hence has gap greater than \(917/1000\), while
  retaining the full 81-point three-primary grid.
- Conversely, preserve the complete actual dyadic residue
  \(\widetilde P_2\equiv P_M\pmod {2^{K_M}}\) and take the first lift coprime
  to \(R_M\).  It occurs at lift index 3 and puts the complete row in an arc
  shorter than \(10^{-639}\).

These are finite `experiment`s, not alternative BBP truncations and not
counterexamples to V1.  They show exactly what the CRT theorem must retain:
the actual dyadic coordinate and all actual odd coordinates **jointly**.
Fixing both determines the full numerator modulo the reduced denominator,
so there is no remaining averaging parameter.  Marginal CRT mixing cannot
replace the selected-numerator estimate.

## 4. An exact deterministic no-hit Fourier certificate

Let \(X=\{x_1,\ldots,x_L\}\subset\mathbb T\) be one endpoint row.  Choose an
integer \(K\ge2\), partition the circle into the equal half-open cells, and
put

\[
 q_n=\lfloor Kx_n\rfloor\in\mathbb Z/K\mathbb Z,
 \qquad c_a=\#\{n:q_n=a\}.                         \tag{PYB13}
\]

For \(\zeta_K=e^{2\pi i/K}\), define the quantized endpoint sums

\[
                         C_h=\sum_{n=1}^L\zeta_K^{hq_n}.    \tag{PYB14}
\]

Finite Fourier inversion is the exact identity

\[
 \boxed{
 Kc_a=L+\sum_{h=1}^{K-1}C_h\zeta_K^{-ha}.}        \tag{PYB15}
\]

The right side is a real integer.  Therefore a cell is empty if and only if
the signed nonzero-frequency sum in (PYB15) equals \(-L\).  In particular,

\[
 \boxed{
 \min_{a\bmod K}\Re\sum_{h=1}^{K-1}C_h\zeta_K^{-ha}>-L}   \tag{PYB16}
\]

is a deterministic all-cell no-hit certificate.  If every cell is occupied,
then every circular gap is at most \(2/K\).  Taking
\(K\asymp L/\log L\) makes (PYB16) strong enough for the endpoint maximal-gap
conjecture.

Equation (PYB16) is deliberately phase-sensitive.  Parseval gives only

\[
 E_K:=\sum_{h=1}^{K-1}|C_h|^2
     =K\sum_{a=0}^{K-1}c_a^2-L^2.                 \tag{PYB17}
\]

If one cell is empty, Cauchy--Schwarz implies

\[
                             E_K\ge {L^2\over K-1}.          \tag{PYB18}
\]

Thus the strict reverse inequality is a sufficient energy certificate, but
it is far too strong at the random-covering scale and its converse is false.
On the exact \(M=454\) row, \(L=93\), \(K=20\), all cells are hit and the
minimum count is 2, yet

\[
 E_{20}=1211>{93^2\over19}.                        \tag{PYB19}
\]

A balanced 20-cell histogram with the same total and one empty cell has
energy 491.  The energy ranges overlap.  This finite `experiment` is a
direct equal-cell version of the frozen complement-energy warning: global
second moments do not decide the extreme negative trough needed for no-hit.

For classical, unquantized exponential sums, a smooth or Selberg-minorant
version of (PYB16) requires harmonics through
\(|h|\asymp K\asymp L/\log L\).  This exposes a quantifier not present in
the fixed-h endpoint Fourier `conjecture`.  The frozen CF36 analysis remains
hard uniformly in this entire range: here \(|h|<M\) eventually, so no high
prime \(p>M\) divides \(h\), while \(v_2(h)=O(\log M)\).  Consequently its
deep dyadic factor and its \((4.636+o(1))M\) surviving high-prime logarithmic
mass persist throughout the Peres--Yang bandwidth.  A local estimate at one
prime, a fixed number of primes, one fixed harmonic, or one selected energy
class does not imply (PYB16).

For the weaker qualitative goal \(G_e\to0\), decay of every fixed classical
harmonic along one common endpoint subsequence would still suffice by Weyl
compactness.  No such full selected-product estimate is proved either.

## 5. Standalone bounded replay

The [checker](peres_yang_bbp_endpoint_attack_20260813_check.py), SHA-256
`121fad4ba825591d701b4156c6a570962e0609173b875d9b9fe5246afb0a8bcb`,
imports no branch checker.  It reconstructs \(B_{454}\) as an exact reduced
`Fraction`, verifies its dyadic and three-primary denominator data, computes
the exact 93-point row and gap, checks (PYB15) numerically from exact cell
labels, checks (PYB17)--(PYB19) in integer arithmetic, and constructs the
three exact same-denominator numerator falsifiers above.

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_check.py
```

The retained output ends with:

```text
actual_nonzero_dft_energy=1211
empty_energy_threshold=8649/19
balanced_empty_nonzero_dft_energy=491
same_denominator_unit_row_arc_upper_lt=10^-1186
same_denominator_unit_row_full_three_grid=true
odd_crt_preserving_row_arc_upper_lt=83/1000
odd_crt_preserving_row_gap_lower_gt=917/1000
odd_crt_preserving_row_full_three_grid=true
dyadic_preserving_first_coprime_lift=3
dyadic_preserving_row_arc_upper_lt=10^-639
finest_row_dyadic_exponent=1270
asserts_endpoint_gap_law=false
asserts_fixed_return=false
asserts_v1=false
exact_record_sha256=6f326295c5eceba841392479f32e95651b261580fc77084a0370fd1a819a32bd
status=PASS
```

All bounded findings have label `experiment`; the floating DFT is only a
replay of the exact integer histogram and supports no asymptotic claim.

## 6. Literature applicability and sharp handoff

### `literature-checked`

Peres--Yang's Theorem 1.2 proves the sharp maximal-gap law for almost every
fixed dilation parameter in an integer divisibility chain.  Proposition 5.2
and the proof on paper pages 15--17 provide the upper/no-hit machinery used
in (PYB8).  Proposition 5.7 and Section 5.3 provide the independent-digit
lower-bound machinery and are not used in the present upper corollary.  No
statement in the paper selects \(\pi\), a BBP numerator, or a changing
rational triangular array.

No new primary source was needed beyond the frozen literature audit.  No
Lean file, axiom audit, verification gate, or `ultrapi.md` was changed by
this branch.

The precise surviving route is now:

\[
 \boxed{
 \text{control the actual joint BBP numerator strongly enough either for
 fixed-h full-product decay, or for the growing-band signed trough (PYB16).}}
                                                               \tag{PYB20}
\]

Peres--Yang proves that the endpoint geometry and \(\log L/L\) scale are
correct for almost every starting point, including the same sparse sequence
of late windows.  The exact denominator grid can reproduce that averaging,
but cannot select its one numerator.  The bounded CRT falsifiers show that
neither marginal half of that numerator suffices, and the exact DFT identity
shows why energy-only replacement loses the no-hit information.  No estimate
of (PYB20) is obtained, so V1 remains a `conjecture`.
